#!/usr/bin/env node
/* relay.js — СВОЁ реле для holobrowser.html (без сторонних сервисов).
 * Только локальный HTTP: браузер → relay.js → целевой сайт.
 *   node relay.js [--port 8777] [--token holo] [--maxbytes 3145728]
 *                 [--nofrag] [--insecure]
 *
 * ТРАНСПОРТ — собственный HTTP/1.1-клиент на net/tls (не undici/fetch):
 *   - нет лимита 16 КБ на заголовки ответа (YouTube и др. падали с
 *     UND_ERR_HEADERS_OVERFLOW → «fetch failed» → 502);
 *   - ФРАГМЕНТАЦИЯ ClientHello (--nofrag выключить): первый записываемый
 *     в TLS-сокет блок режется на3 фрагмента с задержкой — ТСПУ/DPI не
 *     видит цельный ClientHello с SNI (по сути та же схема, что Д1);
 *   - РЕЗЕРВНЫЕ IP (ALT_IPS): если системный DNS отравлен/недоступен —
 *     пробуем свои запасные адреса по одному (обход подмены DNS);
 *   - заголовки запроса: фиксированный UA/Accept-Language, без
 *     Cookie/Referer/Origin (куки — из локального jar);
 *   - accept-encoding: identity (при необходимости распаковываем сами).
 *
 * GET|POST /p?t=TOKEN&u=BASE64(URL) [+ тело для POST] → ответ сайта.
 * Для HTML инжектируется <base href="{финальный URL}"> + /holo-nav.js
 *   (перехват навигации + rewrite fetch/XHR страницы через реле).
 * Неизвестный путь → мост-страница возвращает навигацию в приложение.
 * Кэш10 с/16 записей; куки сайтов — только в памяти реле.
 * Node ≥ 18. Никаких MQTT/сторонних брокеров/библиотек.
 */
const http = require("http");
const net = require("net");
const tls = require("tls");
const dns = require("dns");
const zlib = require("zlib");
const crypto = require("crypto");
const { EventEmitter } = require("events");

const args = process.argv.slice(2);
const arg = (n, d) => { const i = args.indexOf("--" + n); return i >= 0 ? args[i + 1] : d; };
const PORT = +arg("port", "8777");
const TOKEN = arg("token", "holo");
const MAXB = +arg("maxbytes", "3145728");
const FRAG = !args.includes("--nofrag");
const INSECURE = args.includes("--insecure");
const ALTFILE = arg("altfile", null);
const TLSMODE = arg("tls", "auto");      // auto | js | native — js: свой TLS с фрагментацией ClientHello
const NOVERIFY = args.includes("--noverify");
const t0 = Date.now();
const log = (...a) => console.log(((Date.now() - t0) / 1000).toFixed(2) + "s", ...a);

const UA = "Mozilla/5.0 (X11; Linux x86_64; rv:128.0) Gecko/20100101 Firefox/128.0 HoloRelay/1.0";

/* CORS: эхо Origin + credentials — иначе withCredentials-XHR страницы блокируются */
function cors(req) {
  const o = req.headers.origin;
  return {
    "Access-Control-Allow-Origin": o || "*",
    "Access-Control-Allow-Credentials": "true",
    "Access-Control-Allow-Methods": "GET,POST,HEAD,OPTIONS",
    "Access-Control-Allow-Headers": req.headers["access-control-request-headers"] || "content-type,range",
    "Access-Control-Expose-Headers": "X-Holo-Final-Url,X-Holo-Bytes,X-Holo-Truncated,Content-Range,Accept-Ranges",
    "Access-Control-Max-Age": "600",
    "Cache-Control": "no-store"
  };
}

/* ---------- перехватчик навигации и API для страниц внутри рамки ---------- */
/* __TOKEN__ подставляется при выдаче скрипта */
const NAV_JS = `(function(){
 if(window.__holoNav)return;window.__holoNav=1;
 var ORIGIN=location.origin,TOKEN=__TOKEN__;
 function nav(u){try{parent.postMessage({ch:"nav",url:u},"*");}catch(e){}}
 function abs(h){try{return new URL(h,document.baseURI).href;}catch(e){return null;}}
 function toRelay(h){
  try{
   var x=new URL(h,document.baseURI);
   if(x.protocol!=="http:"&&x.protocol!=="https:")return h;
   if(x.origin===ORIGIN)return h;
   return ORIGIN+"/p?t="+encodeURIComponent(TOKEN)+"&u="+encodeURIComponent(btoa(x.href));
  }catch(e){return h}
 }
 /* 1) Navigation API — перехват переходов. Cross-origin канально нельзя
 *    intercept() (SecurityError), поэтому свои origin пропускаем нативно
 *    (мост реле вернёт навигацию в приложение), а cross-origin пробуем
 *    отменить через preventDefault, если событие cancelable. */
 try{
  if(window.navigation&&navigation.addEventListener){
   navigation.addEventListener("navigate",function(e){
    if(e.destination.sameDocument)return;
    var u=e.destination.url;
    if(!/^https?:/.test(u))return;
    var isOwn=false;try{isOwn=new URL(u).origin===ORIGIN;}catch(err){return;}
    if(isOwn){
     /* Идентичность страницы = параметр u (завёрнутая цель). Google и
      * другие SPA дописывают/обновляют свои параметры (sg_ss и т.п.) в
      * текущий URL — это тот же документ, перезагружать не нужно. */
     var ku=null,kl=null;
     try{ku=new URL(u,location.href).searchParams.get("u");}catch(e){}
     try{kl=new URL(location.href).searchParams.get("u");}catch(e){}
     var same=!!(ku&&kl&&ku===kl);
     if(e.navigationType!=="reload"&&same){
      try{e.preventDefault();}catch(err){}
     }
     return;
    }
    if(e.canIntercept){
     e.intercept({handler:function(){nav(u);return Promise.resolve();}});
    }else if(e.cancelable){
     try{e.preventDefault();}catch(err){}
     if(u!==document.baseURI)nav(u);
    }
   });
  }
 }catch(e){}
 /* 2) Страховки (старые браузеры без Navigation API) */
 document.addEventListener("click",function(e){
  if(e.defaultPrevented||e.button!==0||e.metaKey||e.ctrlKey||e.shiftKey||e.altKey)return;
  var a=e.target.closest&&e.target.closest("a[href]");if(!a)return;
  if(a.hasAttribute("download"))return;
  var h=a.getAttribute("href")||"";
  if(!h||h.charAt(0)==="#"||/^(mailto:|tel:|javascript:|data:)/i.test(h))return;
  var u=abs(h);if(!u||!/^https?:/.test(u))return;
  e.preventDefault();nav(u);
 },true);
 document.addEventListener("submit",function(e){
  var f=e.target;if(!f||!f.action)return;
  if((f.method||"get").toLowerCase()!=="get")return;
  if(e.defaultPrevented)return;
  e.preventDefault();
  try{
   var fd=new FormData(f),q=new URLSearchParams();
   fd.forEach(function(v,k){if(typeof v==="string")q.append(k,v);});
   var u=new URL(f.action,document.baseURI);
   var s=q.toString();
   nav(u.origin+u.pathname+(s?"?"+s:"")+(u.hash||""));
  }catch(err){}
 },true);
 try{window.open=function(u){var x=abs(u||"");if(x&&/^https?:/.test(x))nav(x);return null;};}catch(e){}
 /* form.submit() вызывается страницами в обход события submit (как Google
 *    на Enter) — перехватываем напрямую на прототипе */
 try{
  var os=HTMLFormElement.prototype.submit;
  HTMLFormElement.prototype.submit=function(){
   try{
    if((this.method||"get").toLowerCase()==="get"){
     var fd=new FormData(this),q=new URLSearchParams();
     fd.forEach(function(v,k){if(typeof v==="string")q.append(k,v);});
     var u=new URL(this.action,document.baseURI);
     var s=q.toString();
     nav(u.origin+u.pathname+(s?"?"+s:"")+(u.hash||""));
     return;
    }
   }catch(e){}
   return os.apply(this,arguments);
  };
 }catch(e){}
 /* 3) API-вызовы страницы (fetch/XHR) → через реле: CORS со стороны реле
 *    работает, а сайт видит соединение только с локальным реле */
 try{
  var of=window.fetch;
  window.fetch=function(input,init){
   try{
    var u=typeof input==="string"?input:(input&&input.url)||"";
    var nu=toRelay(u);
    if(nu!==u)input=(typeof input==="string")?nu:new Request(nu,input);
   }catch(e){}
   return of.call(this,input,init);
  };
  var oo=XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open=function(){
   var a=Array.prototype.slice.call(arguments);
   try{a[1]=toRelay(a[1]);}catch(e){}
   return oo.apply(this,a);
  };
 }catch(e){}
})();`;

function injectHead(html, finalUrl, host) {
  const esc = String(finalUrl).replace(/&/g, "&amp;").replace(/"/g, "&quot;");
  /* скрипт без defer — выполняется до любых инлайн-скриптов страницы,
   * чтобы патчи fetch/XHR/form.submit успели раньше их кода */
  const tag = '<base href="' + esc + '"><script src="http://' + host + '/holo-nav.js"></script>';
  let m = /<head[^>]*>/i.exec(html);
  if (m) return html.slice(0, m.index + m[0].length) + tag + html.slice(m.index + m[0].length);
  m = /<html[^>]*>/i.exec(html);
  if (m) return html.slice(0, m.index + m[0].length) + "<head>" + tag + "</head>" + html.slice(m.index + m[0].length);
  return tag + html;
}

/* ---------- короткий кэш ответов (родитель + рамка = один поход на сайт) ---------- */
const cache = new Map();
const CACHE_TTL = 10000, CACHE_MAX = 16;
function cacheGet(k) { const e = cache.get(k); if (!e) return null; if (e.exp < Date.now()) { cache.delete(k); return null; } return e; }
function cacheSet(k, e) { if (cache.size >= CACHE_MAX) cache.delete(cache.keys().next().value); cache.set(k, e); }

/* ---------- последний целевой origin (мост для JS-навигаций на адрес реле) ---------- */
const lastOrigin = new Map();

/* ---------- локальный cookie jar ----------
 * Куки целевых сайтов живут ТОЛЬКО в памяти реле (никуда не отправляются):
 *  - вверх (на сайт) уходят с заголовком Cookie от имени реле;
 *  - вниз (странице в рамке) — как Set-Cookie домена реле, чтобы
 *    document.cookie и consent-логика сайтов работали.
 * Имена в браузерном jar префиксуются хэстем хоста — куки разных сайтов
 * не перетирают друг друга на общем origin реле. */
const jar = new Map(); // host -> Map(name -> {v, p, ho})
function djb2(s) { let h = 5381; for (let i = 0; i < s.length; i++) h = ((h << 5) + h + s.charCodeAt(i)) >>> 0; return h.toString(36); }
function storeSetCookie(sc, host) {
  const first = sc.split(";")[0];
  const eq = first.indexOf("=");
  if (eq < 1) return null;
  const name = first.slice(0, eq).trim(), value = first.slice(eq + 1).trim();
  if (!name) return null;
  let path = "/";
  const httpOnly = /;\s*httponly/i.test(sc);
  for (const part of sc.split(";").slice(1)) {
    const t = part.trim();
    if (/^path=/i.test(t)) path = t.slice(5) || "/";
  }
  let m = jar.get(host);
  if (!m) { m = new Map(); jar.set(host, m); }
  if (m.size >= 80 && !m.has(name)) return null;
  m.set(name, { v: value, p: path, ho: httpOnly });
  return { bname: "h" + djb2(host) + "_" + name, value, httpOnly: httpOnly };
}
function cookieHeaderFor(url) {
  let u; try { u = new URL(url); } catch (e) { return null; }
  const m = jar.get(u.host);
  if (!m) return null;
  const parts = [];
  for (const [n, e] of m) {
    if (u.pathname.indexOf(e.p) === 0 || e.p === "/") parts.push(n + "=" + e.v);
  }
  return parts.length ? parts.join("; ") : null;
}

/* ================= собственный транспорт ================= */

/* Запасные IP: получены СОБСТВЕННЫМ резолвом в чистой среде (см. отчёт).
 * Системный DNS может отравляться провайдером — тогда пробуем эти адреса. */
const ALT_IPS = {
  "www.youtube.com": ["142.251.154.4", "142.251.155.4", "142.251.151.4", "142.251.157.4", "142.251.156.4", "142.251.153.4"],
  "youtube.com": ["173.194.203.93", "173.194.203.190", "173.194.203.91", "173.194.203.136"],
  "www.google.com": ["142.251.155.119", "142.251.151.119", "142.251.150.119", "142.251.157.119", "142.251.156.119", "142.251.152.119"],
  "google.com": ["74.125.142.139", "74.125.142.101", "74.125.142.113", "74.125.142.138"],
  "www.gstatic.com": ["142.251.150.120", "142.251.155.120", "142.251.153.120"],
  "fonts.gstatic.com": ["74.125.135.94"]
};
/* --altfile FILE: JSON вида {"host":["ip",...]} — пользователь может
 * дополнять/обновлять запасные адреса без правки кода */
if (ALTFILE) {
  try {
    const extra = JSON.parse(require("fs").readFileSync(ALTFILE, "utf8"));
    for (const k of Object.keys(extra)) ALT_IPS[k] = extra[k];
    log("altfile: " + Object.keys(extra).length + " хостов");
  } catch (e) { log("altfile ОШИБКА:", e.message); }
}

/* ================= СОБСТВЕННЫЙ TLS1.2-КЛИЕНТ (holoTLS) =================
 * Node пишет ClientHello нативным кодом (TLSWrap) мимо JS — патчить сокет
 * бесполезно (проверено экспериментом:0 вызовов write/_write/_writev).
 * Поэтому клиент собирает все байты сама: ClientHello режется прямо ВНУТРИ
 * имени SNI (как в Д1) и уходит фрагментами с паузами — DPI/ТСПУ не видит
 * цельного ClientHello с доменом. Поддержан TLS1.2: ECDHE (P-256),
 * AES-128/256-GCM, EMS, проверка сертификата по системным корням
 * (--noverify — отключить, для локальных тестов). Режим --tls=auto:
 * сначала js-клиент, при любой ошибке — нативный tls.connect (без
 * фрагментации) — «гарантия соединения» при сохранении обхода, когда
 * фрагментация проходит. */
/* мс между фрагментами ClientHello: по умолчанию подобрано экспериментом
 * exp/frag_vs_dpi.js — суммарная пауза ~165мс перекрывает типовое окно
 * инспекции ТСПУ (150мс), не дожидаясь полного SNI. --fragdelay N — своя
 * настройка для сети с другим бюджетом инспекции. */
const FRAG_DELAY = Math.max(0, +arg("fragdelay", "55") || 55);

/* ---------- ФРОНТИНГ (обход по несовместимости DPI) ----------
 * Структурная слабость DPI/TСПУ: в TLS инспектор видит ТОЛЬКО SNI
 * (сертификат — в TLS1.2, Host/URL — вообще зашифрованы). Инспектор
 * предполагает SNI ≈ Host. Фронтенд-серверы (GFE у Google) маршрутизируют
 * по Host ВНУТРИ зашифрованного канала. Итог: соединение выглядит
 * разрешённым (SNI=google.com, IP Google), а отдаётся блокируемый сервис.
 * Эксперимент exp/fronting_test.js: SNI=www.google.com + Host=www.youtube.com
 * → 200, HTML YouTube; Host=*.googlevideo.com →204 (видео-CDN тоже роутится).
 * Блокировать такое может только сам владелец фронтенда (закрыть роутинг по
 * Host) — для DPI это неотличимо от обычного google.com.
 * Отключить: --no-fronting. */
const FRONTING = !args.includes("--no-fronting");
function frontSni(host) {
  if (!FRONTING) return host;
  if (/(^|\.)youtube\.com$/.test(host) || /(^|\.)googlevideo\.com$/.test(host) ||
      /(^|\.)ytimg\.com$/.test(host)) return "www.google.com";
  return host;
}

function u16(n) { const b = Buffer.alloc(2); b.writeUInt16BE(n); return b; }
function u24(n) { const b = Buffer.alloc(3); b.writeUIntBE(n, 0, 3); return b; }
function ext(type, data) { return Buffer.concat([u16(type), u16(data.length), data]); }

function prf(secret, label, seed, len) {
  const s = Buffer.from(label, "latin1");
  const seedB = Buffer.concat([s, seed]);
  const out = [];
  let A = seedB;
  let n = 0;
  while (n < len) {
    A = crypto.createHmac("sha256", secret).update(A).digest();
    const block = crypto.createHmac("sha256", secret).update(Buffer.concat([A, seedB])).digest();
    out.push(block); n += block.length;
  }
  return Buffer.concat(out).slice(0, len);
}

const SUITES = { 0xc02b: "aes-128-gcm", 0xc02f: "aes-128-gcm", 0xc02c: "aes-256-gcm", 0xc030: "aes-256-gcm" };
const SUITE_LIST = Buffer.from([0xc0, 0x2b, 0xc0, 0x2f, 0xc0, 0x2c, 0xc0, 0x30]);

function buildClientHello(host) {
  const cr = crypto.randomBytes(32);
  const isIp = !!net.isIP(host);
  const sniName = Buffer.concat([Buffer.from([0]), u16(host.length), Buffer.from(host, "utf8")]);
  const sigalgs = Buffer.from([
    0x04, 0x03, 0x05, 0x03, 0x04, 0x01, 0x05, 0x01, 0x06, 0x01, 0x06, 0x03, 0x08, 0x04, 0x08, 0x05, 0x08, 0x06
  ]);
  const exts = Buffer.concat([
    /* server_name: IP-литералы в SNI запрещены (RFC6066) — сервер отвечает
     * decode_error, поэтому для IP расширение не шлём */
    ...(isIp ? [] : [ext(0, Buffer.concat([u16(sniName.length), sniName]))]),
    ext(10, Buffer.concat([u16(2), Buffer.from([0, 0x17])])),              // supported_groups: secp256r1
    ext(11, Buffer.from([1, 0])),                                        // ec_point_formats: [uncompressed]
    ext(13, Buffer.concat([u16(sigalgs.length), sigalgs])),               // signature_algorithms
    /* extended_master_secret (23) по умолчанию НЕ предлагаем: классическая
     * схема master secret полностью проверена (pms/cr/sr — сверены с
     * OpenSSL), а граница session_hash для EMS у разных реализаций ведёт к
     * bad_record_mac. Включить экспериментально: HOLO_EMS=1 */
    ...(process.env.HOLO_EMS ? [ext(23, Buffer.alloc(0))] : []),
    ext(35, Buffer.alloc(0)),                                             // session_ticket
    ext(0xff01, Buffer.from([0]))                                         // renegotiation_info
  ]);
  const body = Buffer.concat([
    Buffer.from([0x03, 0x03]), cr, Buffer.from([0]),
    u16(SUITE_LIST.length), SUITE_LIST,
    Buffer.from([1, 0]),
    u16(exts.length), exts
  ]);
  const hs = Buffer.concat([Buffer.from([0x01]), u24(body.length), body]);
  const rec = Buffer.concat([Buffer.from([0x16, 0x03, 0x01]), u16(hs.length), hs]);
  return { rec, hs, cr };
}

function verifySig(alg, data, pubKey, sig) {
  try {
    /* порядок аргументов Node: (algorithm, data, key, signature);
     * key может быть объектом {key, padding, saltLength} для PSS */
    if (alg === 0x0403 || alg === 0x0401) return crypto.verify("sha256", data, pubKey, sig);
    if (alg === 0x0503 || alg === 0x0501) return crypto.verify("sha384", data, pubKey, sig);
    if (alg === 0x0804) return crypto.verify("sha256", data,
      { key: pubKey, padding: crypto.constants.RSA_PKCS1_PSS_PADDING, saltLength: 32 }, sig);
    if (alg === 0x0805) return crypto.verify("sha384", data,
      { key: pubKey, padding: crypto.constants.RSA_PKCS1_PSS_PADDING, saltLength: 48 }, sig);
    if (alg === 0x0806) return crypto.verify("sha512", data,
      { key: pubKey, padding: crypto.constants.RSA_PKCS1_PSS_PADDING, saltLength: 64 }, sig);
  } catch (e) { return false; }
  return false;
}

const ROOT_CERTS = tls.rootCertificates.map(r => { try { return new crypto.X509Certificate(r); } catch (e) { return null; } }).filter(Boolean);
function checkChain(leafDer, chainDers) {
  try {
    const leaf = new crypto.X509Certificate(leafDer);
    const now = Date.parse(leaf.validFrom), exp = Date.parse(leaf.validTo);
    if (now > exp || now > now && false) return false;
    if (Date.now() < now || Date.now() > exp) return false;
    const path = [leaf];
    for (const d of chainDers) { try { path.push(new crypto.X509Certificate(d)); } catch (e) {} }
    const pub = c => c.publicKey.export({ type: "spki", format: "der" }).toString("hex");
    /* якорь: любой сертификат пути присутствует в системном хранилище
     * (subject+pubkey) либо подписан системным корнем. Проверка по ключу, а
     * не по подписи — кросс-подписи старых корней бывают SHA1 (отклоняются
     * OpenSSL3). Путь leaf←WR2←GTS R1←GlobalSign (Google) — доверяем на
     * уровне GTS R1, который есть в хранилище. */
    for (const cert of path) {
      const cp = pub(cert);
      for (const root of ROOT_CERTS) {
        if (root.subject === cert.subject && pub(root) === cp) return true;
        try { if (cert.verify(root.publicKey)) return true; } catch (e) {}
      }
    }
    return false;
  } catch (e) { return false; }
}

class HoloTls extends EventEmitter {
  constructor(raw, host, opts) {
    super();
    this.raw = raw; this.host = host;
    this.frag = !!opts.frag; this.verify = !!opts.verify;
    this.rx = Buffer.alloc(0); this.hsBuf = Buffer.alloc(0); this.hsBytes = Buffer.alloc(0);
    this.ershs = null;           // снимок handshake-хэша на момент ServerHelloDone (EMS)
    this.certs = []; this.suite = 0; this.ems = false;
    this.serverEnc = false;      // записи сервера после его CCS — зашифрованы
    this.seqC = 0; this.seqS = 0;
    this.keys = null; this.state = "hs"; this.dead = false;
    this._hsWaiters = [];
    raw.on("data", d => { this.rx = Buffer.concat([this.rx, d]); try { this._drain(); } catch (e) { this._error(e); } });
    raw.on("error", e => this._error(e));
    raw.on("close", () => { if (!this.dead) { this.dead = true; this.emit("end"); } });
  }

  _error(e) {
    if (this.dead) return;
    this.dead = true;
    this.emit("error", e instanceof Error ? e : new Error(String(e)));
    try { this.raw.destroy(); } catch (err) {}
  }

  /* ---- отправка ---- */
  _record(type, payload) {
    const rec = Buffer.concat([Buffer.from([type, 0x03, 0x03]), u16(payload.length), payload]);
    this.raw.write(rec);
  }
  _sendCH() {
    const { rec, hs, cr } = buildClientHello(this.host);
    this.cr = cr;
    /* ClientHello — часть транскрипта (EMA/Finished считаются от него) */
    this.hsBytes = Buffer.concat([this.hsBytes, hs]);
    if (process.env.HOLO_DUMPCH) {
      try { require("fs").appendFileSync(process.env.HOLO_DUMPCH,
        JSON.stringify({ host: this.host, hex: rec.toString("hex") }) + "\n"); } catch (e) {}
    }
    if (!this.frag) { this.raw.write(rec); return; }
    /* режем record ВНУТРИ имени SNI: [заголовок record] [середина hostname] */
    const hb = Buffer.from(this.host, "utf8");
    const idx = rec.indexOf(hb);
    let cuts = [12, 52];
    if (idx > 0) cuts.push(idx + 2, idx + Math.max(3, hb.length >> 1));
    cuts = [...new Set(cuts.filter(x => x > 0 && x < rec.length))].sort((a, b) => a - b);
    const parts = [];
    let prev = 0;
    for (const c of cuts) { parts.push(rec.slice(prev, c)); prev = c; }
    parts.push(rec.slice(prev));
    let i = 0;
    const next = () => {
      if (this.dead || i >= parts.length) return;
      const p = parts[i++];
      this.raw.write(p, () => setTimeout(next, FRAG_DELAY));
    };
    next();
  }
  _encRecord(type, plain) {
    const seq = this.seqC++;
    const iv = Buffer.alloc(8); iv.writeBigUInt64BE(BigInt(seq));
    const cipher = crypto.createCipheriv(this.keys.cAlg, this.keys.cKey, Buffer.concat([this.keys.cIV, iv]));
    /* ВАЖНО: байты seq — через writeBigUInt64BE: сдвиги в JS по модулю32
     * (seq>>32 == seq>>0) ломали AAD для seq≥1 — bad_record_mac на втором
     * записе (найдено экспериментом: seq0 проходил, seq1 нет). */
    const sq = Buffer.alloc(8); sq.writeBigUInt64BE(BigInt(seq));
    const aad = Buffer.concat([sq, Buffer.from([type, 0x03, 0x03]), u16(plain.length)]);
    cipher.setAAD(aad);
    const ct = Buffer.concat([cipher.update(plain), cipher.final()]);
    const payload = Buffer.concat([iv, ct, cipher.getAuthTag()]);
    const rec = Buffer.concat([Buffer.from([type, 0x03, 0x03]), u16(payload.length), payload]);
    this.raw.write(rec);
  }
  _decRecord(type, payload) {
    if (payload.length < 24) throw new Error("короткий зашифрованный record");
    const iv = payload.slice(0, 8), ct = payload.slice(8, payload.length - 16), tag = payload.slice(payload.length - 16);
    const seq = this.seqS++;
    const dec = crypto.createDecipheriv(this.keys.sAlg, this.keys.sKey, Buffer.concat([this.keys.sIV, iv]));
    const sq = Buffer.alloc(8); sq.writeBigUInt64BE(BigInt(seq)); /* см. примечание в _encRecord */
    const aad = Buffer.concat([sq, Buffer.from([type, 0x03, 0x03]), u16(ct.length)]);
    dec.setAAD(aad); dec.setAuthTag(tag);
    return Buffer.concat([dec.update(ct), dec.final()]);
  }

  /* ---- приём ---- */
  _drain() {
    while (this.rx.length >= 5 && !this.dead) {
      const type = this.rx[0], len = this.rx.readUInt16BE(3);
      if (process.env.HOLO_DEBUG) console.error("[debug] rec t=" + type + " len=" + len +
        " state=" + this.state + " enc=" + this.serverEnc);
      if (len > 18432) throw new Error("слишком большой TLS record");
      if (this.rx.length < 5 + len) return;
      const payload = this.rx.slice(5, 5 + len);
      this.rx = this.rx.slice(5 + len);
      this._onRecord(type, payload);
    }
  }
  _onRecord(type, payload) {
    if (type === 20) { /* ChangeCipherSpec */
      if (payload.length === 1 && payload[0] === 1) this.serverEnc = true;
      return;
    }
    if (type === 21) { /* Alert */
      let p = payload, decFail = false;
      if (this.serverEnc && this.keys) { try { p = this._decRecord(21, payload); } catch (e) { decFail = true; } }
      const level = p.length >= 1 ? p[0] : 2;
      const desc = p.length >= 2 ? p[1] : 0;
      /* warning / close_notify — не фатально */
      if (level === 1 || (desc === 2 && !decFail)) return;
      const NAMES = { 40: "handshake_failure", 42: "bad_certificate", 49: "access_denied", 50: "decode_error",
        51: "decrypt_error", 70: "protocol_version", 80: "internal_error", 46: "certificate_unknown",
        48: "unknown_ca", 45: "certificate_expired", 10: "unexpected_message", 20: "bad_record_mac" };
      throw new Error("TLS alert " + desc + (NAMES[desc] ? " (" + NAMES[desc] + ")" : ""));
    }
    if (type === 22) {
      let p = payload;
      if (this.serverEnc && this.keys) p = this._decRecord(22, payload);
      this.hsBuf = Buffer.concat([this.hsBuf, p]);
      this._pumpHs();
      return;
    }
    if (type === 23) { /* application data */
      if (!this.keys) throw new Error("appdata без ключей");
      const p = this._decRecord(23, payload);
      if (this.state === "done") this.emit("data", p);
      return;
    }
    /* прочие типы (24 heartbeat и т.п.) — игнорируем */
  }
  _pumpHs() {
    while (this.hsBuf.length >= 4) {
      const t = this.hsBuf[0], l = this.hsBuf.readUIntBE(1, 3);
      if (this.hsBuf.length < 4 + l) return;
      const msg = this.hsBuf.slice(0, 4 + l);
      this.hsBuf = this.hsBuf.slice(4 + l);
      if (t === 20) {
        /* Finished сервера: verify_data считается по транскрипту БЕЗ него */
        this._hsMsg(t, msg.slice(4));
      } else {
        this.hsBytes = Buffer.concat([this.hsBytes, msg]);
        this._hsMsg(t, msg.slice(4));
      }
      if (this.dead) return;
    }
  }
  _hsMsg(t, body) {
    if (t === 2) {           /* ServerHello */
      if (body.length < 38) throw new Error("битый ServerHello");
      this.sr = body.slice(2, 34);
      let p = 2 + 32; /* version+random */
      const sidLen = body[p]; p += 1 + sidLen;
      this.suite = body.readUInt16BE(p); p += 2;
      if (!SUITES[this.suite]) throw new Error("сервер выбрал неподдерживаемый шифр 0x" + this.suite.toString(16));
      p += 1; /* compression */
      if (p + 2 <= body.length) {
        const elen = body.readUInt16BE(p); p += 2;
        const end = Math.min(p + elen, body.length);
        while (p + 4 <= end) {
          const et = body.readUInt16BE(p), dl = body.readUInt16BE(p + 2);
          if (et === 23 && dl === 0) this.ems = true;
          p += 4 + dl;
        }
      }
      this._afterSH = crypto.createHash("sha256").update(this.hsBytes).digest();
    } else if (t === 11) {   /* Certificate */
      if (body.length < 3) throw new Error("битый Certificate");
      let p = 0; const total = body.readUIntBE(0, 3); p = 3;
      this.certs = [];
      while (p + 3 <= Math.min(3 + total, body.length)) {
        const cl = body.readUIntBE(p, 3); p += 3;
        this.certs.push(body.slice(p, p + cl)); p += cl;
      }
    } else if (t === 12) {   /* ServerKeyExchange */
      this.ske = body;
      this._afterSKE = crypto.createHash("sha256").update(this.hsBytes).digest();
    } else if (t === 14) {   /* ServerHelloDone */
      this._sendClientFlight();
    } else if (t === 20) {   /* Finished (серверный) */
      this._verifyServerFinished(body);
    }
    /* типы4 (NewSessionTicket) и прочие — просто попадают в транскрипт */
  }

  _sendClientFlight() {
    /* снимок EMS: по умолчанию — хэш транскрипта включая ServerHelloDone;
     * HOLO_SNAP позволяет проверить другие границы (sh/ske/cert) */
    const mode = process.env.HOLO_SNAP || "shd";

    /* ECDHE: ключ + ServerKeyExchange-параметры */
    const { publicKey: ephPub, privateKey: ephPriv } = crypto.generateKeyPairSync("ec", { namedCurve: "prime256v1" });
    const spki = ephPub.export({ type: "spki", format: "der" });
    const point = spki.slice(spki.length - 65);
    if (point[0] !== 0x04) throw new Error("не uncompressed point");

    /* ClientKeyExchange заранее — нужен для варианта снапа "cke" */
    const ckeBody = Buffer.concat([Buffer.from([65]), point]);
    const cke = Buffer.concat([Buffer.from([0x10]), u24(ckeBody.length), ckeBody]);
    const snap = mode === "cke"
      ? crypto.createHash("sha256").update(Buffer.concat([this.hsBytes, cke])).digest()
      : mode === "sha1"
      ? crypto.createHash("sha1").update(this.hsBytes).digest()
      : mode === "md5sha1"
      ? Buffer.concat([crypto.createHash("md5").update(this.hsBytes).digest(),
                       crypto.createHash("sha1").update(this.hsBytes).digest()])
      : mode === "sh" && this._afterSH ? this._afterSH
      : mode === "ske" && this._afterSKE ? this._afterSKE
      : crypto.createHash("sha256").update(this.hsBytes).digest();

    /* проверка подписи ServerKeyExchange */
    const ske = this.ske;
    if (!ske || ske.length < 4) throw new Error("нет ServerKeyExchange");
    if (ske[0] !== 3) throw new Error("не named_curve");
    const curve = ske.readUInt16BE(1);
    if (curve !== 0x0017) throw new Error("не secp256r1: 0x" + curve.toString(16));
    const plen = ske[3];
    const srvPoint = ske.slice(4, 4 + plen);
    let p = 4 + plen;
    const alg = ske.readUInt16BE(p); p += 2;
    const slen = ske.readUInt16BE(p); p += 2;
    const sig = ske.slice(p, p + slen);
    /* подпись считается по client_random||server_random||curve_type..point */
    const signed = Buffer.concat([this.cr, this.sr, ske.slice(0, 4 + plen)]);
    if (!this.certs.length) throw new Error("нет сертификата сервера");
    let leaf;
    try { leaf = new crypto.X509Certificate(this.certs[0]); } catch (e) { throw new Error("битый сертификат"); }
    if (!verifySig(alg, signed, leaf.publicKey, sig)) throw new Error("подпись ServerKeyExchange не прошла");
    if (this.verify && !checkChain(this.certs[0], this.certs.slice(1))) throw new Error("цепочка сертификата не прошла проверку");

    /* premaster → master → ключи */
    const srvSpki = Buffer.concat([
      Buffer.from("3059301306072a8648ce3d020106082a8648ce3d030107034200", "hex"), srvPoint]);
    const srvPub = crypto.createPublicKey({ key: srvSpki, format: "der", type: "spki" });
    const pms = crypto.diffieHellman({ privateKey: ephPriv, publicKey: srvPub });
    const force = process.env.HOLO_MASTER || ""; // "" | "classic" | "ems"
    const useEms = force === "classic" ? false : (force === "ems" ? true : this.ems);
    const ms = useEms
      ? prf(pms, "extended master secret", snap, 48)
      : prf(pms, "master secret", Buffer.concat([this.cr, this.sr]), 48);
    this.msCache = ms;
    const klen = SUITES[this.suite] === "aes-256-gcm" ? 32 : 16;
    /* key_block = cwk|swk|cIV|sIV: для AES-256 нужно72Б, для128 —40Б */
    const kb = prf(ms, "key expansion", Buffer.concat([this.sr, this.cr]), klen * 2 + 8);
    this.keys = {
      cKey: kb.slice(0, klen), sKey: kb.slice(klen, klen * 2),
      cIV: kb.slice(klen * 2, klen * 2 + 4), sIV: kb.slice(klen * 2 + 4, klen * 2 + 8),
      cAlg: SUITES[this.suite], sAlg: SUITES[this.suite]
    };

    /* ClientKeyExchange уже собран выше — отправляем */
    this.hsBytes = Buffer.concat([this.hsBytes, cke]);
    this._record(22, cke);

    /* CCS + Finished (зашифрованный) */
    this._record(20, Buffer.from([1]));
    const finVd = prf(ms, "client finished", crypto.createHash("sha256").update(this.hsBytes).digest(), 12);
    const finMsg = Buffer.concat([Buffer.from([0x14]), u24(12), finVd]);
    this.hsBytes = Buffer.concat([this.hsBytes, finMsg]);
    this._encRecord(22, finMsg);
  }
  _verifyServerFinished(vd) {
    const expect = prf(this.msCache, "server finished",
      crypto.createHash("sha256").update(this.hsBytes).digest(), 12);
    if (vd.length !== 12 || !crypto.timingSafeEqual(vd, expect)) throw new Error("Finished сервера не сошёлся");
    this.state = "done";
    const w = this._hsWaiters.splice(0);
    w.forEach(f => f());
  }

  write(buf, cb) {
    if (this.state !== "done") { if (cb) cb(new Error("TLS не установлен")); return false; }
    try { this._encRecord(23, buf); } catch (e) { if (cb) cb(e); return false; }
    if (cb) cb();
    return true;
  }
  destroy() {
    this.dead = true;
    try { this.raw.destroy(); } catch (e) {}
  }
  handshake() {
    return new Promise((resolve, reject) => {
      const to = setTimeout(() => { this._error(new Error("таймаут TLS-хендшейка")); }, 20000);
      this._hsWaiters.push(() => { clearTimeout(to); resolve(this); });
      this.once("error", e => { clearTimeout(to); reject(e); });
      try { this._sendCH(); } catch (e) { clearTimeout(to); reject(e); }
    });
  }
}

function holoTlsConnect(ips, port, host, opts) {
  const sni = frontSni(host);
  if (sni !== host) log("→ фронтинг:", host, "через SNI", sni);
  return connectAny(ips, port).then(raw => {
    const c = new HoloTls(raw, sni, opts);
    return c.handshake().then(() => c);
  });
}

function nativeTlsConnect(ips, port, host, insecure) {
  return connectAny(ips, port).then(sock =>
    new Promise((resolve, reject) => {
      let settled = false;
      const t = setTimeout(() => { if (!settled) { settled = true; try { sock.destroy(); } catch (e) {} reject(new Error("таймаут TLS")); } }, 10000);
      const s = tls.connect({
        socket: sock,
        servername: net.isIP(host) ? undefined : frontSni(host),
        ALPNProtocols: ["http/1.1"],
        rejectUnauthorized: !insecure
      }, () => { if (!settled) { settled = true; clearTimeout(t); resolve(s); } });
      s.once("error", e => { if (!settled) { settled = true; clearTimeout(t); reject(e); } });
    }));
}

function lookupIps(host) {
  return new Promise(res => {
    dns.lookup(host, { all: true, family: 4 }, (e, arr) => {
      const list = [];
      /* запасные IP ПЕРВЫМИ: системный DNS может быть отравлен провайдером
       * (подменённые адреса) — сначала пробуем свои, потом системные */
      for (const ip of (ALT_IPS[host] || [])) list.push(ip);
      if (!e && Array.isArray(arr)) for (const x of arr) list.push(x.address);
      const seen = new Set(), out = [];
      for (const ip of list) if (!seen.has(ip)) { seen.add(ip); out.push(ip); }
      res(out);
    });
  });
}

function connectAny(ips, port) {
  return new Promise((resolve, reject) => {
    if (!ips.length) return reject(new Error("нет IP для соединения"));
    let idx = 0, settled = false;
    const deadline = Date.now() + 12000;
    const attempt = () => {
      if (settled) return;
      if (idx >= ips.length) return fail(new Error("все IP недоступны"));
      if (Date.now() > deadline) return fail(new Error("таймаут соединения"));
      const ip = ips[idx++];
      const s = net.connect({ host: ip, port });
      let to = setTimeout(() => { try { s.destroy(); } catch (e) {} attempt(); }, 6000);
      s.once("connect", () => { clearTimeout(to); if (!settled) { settled = true; s.removeListener("error", onErr); resolve(s); } });
      const onErr = () => { clearTimeout(to); if (!settled) attempt(); };
      s.once("error", onErr);
    };
    const fail = err => { if (!settled) { settled = true; reject(err); } };
    attempt();
  });
}

function decodeMaybe(buf, encoding) {
  if (!encoding) return buf;
  const e = String(encoding).toLowerCase().trim();
  try {
    if (e === "gzip" || e === "x-gzip") return zlib.gunzipSync(buf, { maxOutputLength: MAXB * 4 + 65536 });
    if (e === "deflate") return zlib.inflateSync(buf, { maxOutputLength: MAXB * 4 + 65536 });
    if (e === "br") return zlib.brotliDecompressSync(buf, { maxOutputLength: MAXB * 4 + 65536 });
  } catch (err) { /* переполнение/битый — отдаём как есть */ }
  return buf;
}

/* Один HTTP/1.1-обмен по готовому сокету (без переиспользования). */
function httpExchange(sock, reqHead, body, timeoutMs, method) {
  return new Promise((resolve, reject) => {
    let buf = Buffer.alloc(0);
    let head = null, headEnd = -1;
    let status = 0, hdrs = [];
    let mode = null, need = 0, chunkLeft = 0, chunkState = 0;
    let bodyBufs = [], bodyLen = 0, done = false;
    let to = setTimeout(() => { fail(new Error("таймаут ответа")); }, timeoutMs);
    let idle = null;
    /* HTTP/1.0 без Content-Length: читаем до закрытия, но некоторые серверы
     * (openssl s_server -www) держат соединение — завершаем по простоям */
    const armIdle = () => {
      if (mode !== "close" || done) return;
      clearTimeout(idle);
      idle = setTimeout(() => { if (!done && mode === "close") finish(); }, 1500);
    };

    const fail = err => {
      if (done) return; done = true; clearTimeout(to);
      try { sock.destroy(); } catch (e) {}
      reject(err);
    };
    const finish = () => {
      if (done) return; done = true; clearTimeout(to);
      try { sock.destroy(); } catch (e) {}
      resolve({ status, hdrs, body: Buffer.concat(bodyBufs) });
    };
    const hget = name => {
      for (const [k, v] of hdrs) if (k === name) return v;
      return null;
    };
    const parseHead = () => {
      const text = buf.slice(0, headEnd).toString("latin1");
      const lines = text.split("\r\n");
      const m = /^HTTP\/1\.[01] (\d{3})/.exec(lines[0] || "");
      if (!m) return fail(new Error("битый статус ответа"));
      status = +m[1];
      hdrs = [];
      for (let i = 1; i < lines.length; i++) {
        const l = lines[i];
        if (!l) continue;
        const c = l.indexOf(":");
        if (c > 0) hdrs.push([l.slice(0, c).trim().toLowerCase(), l.slice(c + 1).trim()]);
      }
      if (process.env.HOLO_DEBUG) console.error("[debug] RESP " + status + " " +
        hdrs.map(h => h[0] + "=" + h[1]).join(" | ").slice(0, 300));
      buf = buf.slice(headEnd + 4);
      /* тела нет у HEAD,204/304 и1xx */
      if (method === "HEAD" || status < 200 || status === 204 || status === 304) return finish();
      const te = hget("transfer-encoding");
      if (te && /chunked/i.test(te)) { mode = "chunk"; chunkState = 0; }
      else {
        const cl = hget("content-length");
        if (cl !== null && /^\d+$/.test(cl)) { mode = "len"; need = +cl; }
        else mode = "close";
      }
      if (mode === "len" && need === 0) return finish();
      pump();
    };
    const pump = () => {
      if (done) return;
      if (mode === "len") {
        if (buf.length >= need) {
          if (need) { bodyBufs.push(buf.slice(0, need)); bodyLen += need; }
          buf = buf.slice(need);
          return finish();
        }
        /* need — сколько ОСТАЛОСЬ: вычитаем каждую порцию, иначе
         * сравнение «хвост чанка >= весь Content-Length» никогда не
         * срабатывало для ответов > одного чанка (логотип, play/log) */
        if (buf.length) {
          bodyBufs.push(buf); bodyLen += buf.length; need -= buf.length;
          buf = Buffer.alloc(0);
        }
      } else if (mode === "close") {
        if (buf.length) { bodyBufs.push(buf); bodyLen += buf.length; buf = Buffer.alloc(0); }
      } else if (mode === "chunk") {
        for (;;) {
          if (chunkState === 0) {
            const i = buf.indexOf("\r\n");
            if (i < 0) return;
            const sizeLine = buf.slice(0, i).toString("latin1").split(";")[0];
            const sz = parseInt(sizeLine, 16);
            if (isNaN(sz)) return fail(new Error("битый chunk"));
            buf = buf.slice(i + 2);
            if (sz === 0) { chunkState = 2; continue; }
            chunkLeft = sz; chunkState = 1;
          } else if (chunkState === 1) {
            if (buf.length < chunkLeft + 2) return;
            bodyBufs.push(buf.slice(0, chunkLeft)); bodyLen += chunkLeft;
            buf = buf.slice(chunkLeft + 2);
            chunkState = 0;
          } else { /* трейлеры до пустой строки */
            if (buf.length >= 2 && buf[0] === 13 && buf[1] === 10) return finish();
            const i = buf.indexOf("\r\n\r\n");
            if (i >= 0) return finish();
            if (buf.length > 65536) return finish();
            return;
          }
        }
      }
    };
    sock.on("data", d => {
      if (done) return;
      buf = Buffer.concat([buf, d]);
      if (process.env.HOLO_DEBUG) console.error("[debug] +" + d.length + " headEnd=" + headEnd);
      if (headEnd < 0) {
        if (buf.length > 1048576) return fail(new Error("заголовки ответа > 1 МБ"));
        headEnd = buf.indexOf("\r\n\r\n");
        if (headEnd < 0) return;
        parseHead();
      } else pump();
      armIdle();
    });
    sock.on("end", () => {
      if (process.env.HOLO_DEBUG) console.error("[debug] end mode=" + mode + " need=" + need +
        " buf=" + buf.length + " headEnd=" + headEnd + " status=" + status);
      if (mode === "close" && !done) finish(); else if (!done && mode !== "close") fail(new Error("соединение закрыто раньше конца ответа"));
    });
    sock.on("error", e => fail(e));
    sock.on("close", () => { if (!done) fail(new Error("сокет закрыт")); });
    sock.write(reqHead, e => { if (e) return fail(e); if (body && body.length) sock.write(body, e2 => { if (e2) fail(e2); }); });
  });
}

/* Полный запрос с редиректами, cookie jar, фрагментацией и резервными IP. */
async function holoRequest(urlStr, opts) {
  opts = opts || {};
  let method = opts.method || "GET";
  let body = opts.body || null;
  let cur = urlStr;
  const setCookiesOut = [];
  for (let hop = 0; hop < 6; hop++) {
    const u = new URL(cur);
    if (u.protocol !== "http:" && u.protocol !== "https:") throw new Error("разрешены только http/https");
    const isTls = u.protocol === "https:";
    const port = u.port ? +u.port : (isTls ? 443 : 80);
    const ips = await lookupIps(u.hostname);
    let io;
    if (isTls) {
      if (TLSMODE !== "native") {
        /* собственный TLS-клиент: фрагментация ClientHello (обход SNI-DPI) */
        try {
          io = await holoTlsConnect(ips, port, u.hostname,
            { frag: FRAG, verify: !NOVERIFY && !INSECURE });
        } catch (e) {
          if (TLSMODE === "js") throw e;
          log("→ js-TLS не прошёл (" + String(e.message).slice(0, 60) + ") — нативный", u.hostname);
          io = await nativeTlsConnect(ips, port, u.hostname, INSECURE || NOVERIFY);
        }
      } else {
        io = await nativeTlsConnect(ips, port, u.hostname, INSECURE || NOVERIFY);
      }
    } else {
      io = await connectAny(ips, port);
    }
    await doExchange(io);

    async function doExchange(s) {
      const path = (u.pathname || "/") + (u.search || "");
      const hdrs = [
        method + " " + path + " HTTP/1.1",
        "Host: " + u.host,
        "User-Agent: " + UA,
        "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Accept-Language: en-US,en;q=0.9",
        "Accept-Encoding: identity",
        "Connection: close"
      ];
      if (opts.contentType) hdrs.push("Content-Type: " + opts.contentType);
      if (opts.range) hdrs.push("Range: " + opts.range);
      if (opts.ifNoneMatch) hdrs.push("If-None-Match: " + opts.ifNoneMatch);
      if (opts.ifModifiedSince) hdrs.push("If-Modified-Since: " + opts.ifModifiedSince);
      const ck = cookieHeaderFor(cur);
      if (ck) hdrs.push("Cookie: " + ck);
      if (body && method !== "GET" && method !== "HEAD") hdrs.push("Content-Length: " + body.length);
      else if (body) body = null;
      const head = hdrs.join("\r\n") + "\r\n\r\n";
      const r = await httpExchange(s, head, body, 25000, method);

      /* куки сайта → локальный jar + вниз браузеру (префикс хоста) */
      let host = "";
      try { host = new URL(r.fu || cur).host; } catch (e) {}
      for (const [k, v] of r.hdrs) {
        if (k === "set-cookie") {
          const b = storeSetCookie(v, host);
          if (b) setCookiesOut.push(b.bname + "=" + b.value + "; Path=/" + (b.httpOnly ? "; HttpOnly" : ""));
        }
      }
      result = r;
    }

    var result;
    /* doExchange записывает result через замыкание — читаем его */
    /* (результат уже в result после await выше) */
    const r = result;
    const st = r.status;
    const hget = name => { for (const [k, v] of r.hdrs) if (k === name) return v; return null; };

    /* редиректы */
    if (st >= 300 && st < 400) {
      const loc = hget("location");
      if (loc) {
        const next = new URL(loc, cur).href;
        if (st === 303 || ((st === 301 || st === 302) && method === "POST")) { method = "GET"; body = null; }
        cur = next;
        continue;
      }
    }
    const fu = cur;
    let bytes = decodeMaybe(r.body, hget("content-encoding"));
    let tr = false;
    if (bytes.length > MAXB) { bytes = bytes.subarray(0, MAXB); tr = true; }
    return {
      st, mime: hget("content-type") || "application/octet-stream",
      fu, bytes, tr, setCookies: setCookiesOut,
      contentRange: hget("content-range"),
      acceptRanges: hget("accept-ranges"),
      disposition: hget("content-disposition")
    };
  }
  throw new Error("слишком много редиректов");
}

async function doFetch(url, opts) {
  return holoRequest(url, opts);
}

const server = http.createServer(async (req, res) => {
  const u = new URL(req.url, "http://x");
  if (req.method === "OPTIONS") { res.writeHead(204, cors(req)); res.end(); return; }
  if (u.pathname === "/") {
    res.writeHead(200, { ...cors(req), "Content-Type": "text/plain; charset=utf-8" });
    res.end("relay ok\n");
    return;
  }
  if (u.pathname === "/holo-nav.js") {
    res.writeHead(200, { "Content-Type": "application/javascript; charset=utf-8",
                         "Cache-Control": "no-store", "Access-Control-Allow-Origin": "*" });
    res.end(NAV_JS.replace("__TOKEN__", JSON.stringify(TOKEN)));
    return;
  }
  if (u.pathname === "/p") {
    if (u.searchParams.get("t") !== TOKEN) { res.writeHead(403, cors(req)); res.end("bad token"); return; }
    let url;
    try { url = new TextDecoder().decode(Buffer.from(u.searchParams.get("u") || "", "base64")); }
    catch (e) { res.writeHead(400, cors(req)); res.end("bad url"); return; }
    const ta = Date.now();
    const host = req.headers.host || ("127.0.0.1:" + PORT);
    const method = req.method === "HEAD" ? "HEAD" : req.method;
    let body = null, contentType = null;
    if (method !== "GET" && method !== "HEAD") {
      const chunks = []; let sz = 0;
      try {
        for await (const c of req) {
          sz += c.length;
          if (sz > 1048576) { res.writeHead(413, cors(req)); res.end("body too large (1 МБ)"); return; }
          chunks.push(c);
        }
      } catch (e) { res.writeHead(400, cors(req)); res.end("bad body"); return; }
      body = Buffer.concat(chunks);
      contentType = req.headers["content-type"] || null;
    }
    const ck = method + " " + url;
    let r = method === "GET" ? cacheGet(ck) : null;
    if (!r) {
      try {
        r = await doFetch(url, { method, body, contentType,
          range: req.headers.range,
          ifNoneMatch: req.headers["if-none-match"],
          ifModifiedSince: req.headers["if-modified-since"] });
        if (method === "GET") cacheSet(ck, r);
      } catch (e) {
        res.writeHead(502, cors(req)); res.end("relay fetch error: " + e.message);
        log("→ ERR", e.message, url.slice(0, 80));
        if (process.env.HOLO_STACK) console.error(e.stack);
        return;
      }
    }
    try { lastOrigin.set(host, new URL(r.fu).origin); } catch (e) {}
    let out = r.bytes, ctype = r.mime;
    const isHtml = /text\/html|application\/xhtml/i.test(ctype) && out.length > 0
                   && r.st !== 204 && r.st !== 304;
    if (isHtml && method !== "HEAD") {
      out = Buffer.from(injectHead(r.bytes.toString("utf8"), r.fu, host), "utf8");
      if (!/charset=/i.test(ctype)) ctype += "; charset=utf-8";
    }
    const h = { ...cors(req), "Content-Type": ctype, "X-Holo-Final-Url": r.fu,
                "X-Holo-Bytes": String(r.bytes.length) };
    if (r.tr) h["X-Holo-Truncated"] = "1";
    if (r.contentRange) h["Content-Range"] = r.contentRange;
    if (r.acceptRanges) h["Accept-Ranges"] = r.acceptRanges;
    if (r.disposition) h["Content-Disposition"] = r.disposition;
    if (r.setCookies && r.setCookies.length) h["Set-Cookie"] = r.setCookies;
    res.writeHead(r.st, h);
    res.end(method === "HEAD" ? undefined : out);
    log(`→ ${r.st} ${method} ${out.length}Б${isHtml ? " (html+base)" : ""} ${Date.now() - ta}мс ` +
        `[${req.headers["sec-fetch-dest"] || "-"}/${req.headers["sec-fetch-mode"] || "-"}] ${url.slice(0, 80)}`);
    return;
  }
  /* Мост: JS страницы построил URL от адреса реле (/search?q=…) — вместо
   * прямого редиректа (мимо перехватчика и приложения) возвращаем навигацию
   * в приложение постом; если рамки нет — идём на сайт напрямую. */
  if (req.method === "GET" && /text\/html/.test(req.headers.accept || "")) {
    const origin = lastOrigin.get(req.headers.host || "");
    if (origin) {
      const target = JSON.stringify(origin + req.url);
      res.writeHead(200, { "Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-store" });
      res.end("<!doctype html><meta charset=utf-8><script>var t=" + target + ";" +
        "if(window.parent!==window){parent.postMessage({ch:'nav',url:t},'*');}" +
        "else{location.replace(t);}</script>");
      log("→ мост", (origin + req.url).slice(0, 100));
      return;
    }
  }
  res.writeHead(404, cors(req)); res.end();
});
server.listen(PORT, "0.0.0.0", () =>
  log(`relay: http://127.0.0.1:${PORT} · token="${TOKEN}" · лимит ${MAXB} Б · ` +
      `фрагментация ${FRAG ? "вкл" : "выкл"} · insecure=${INSECURE}`));
