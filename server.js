'use strict';

/* ============================================================
   KAYRO PATCH API  (Render)

   POST /patch   multipart/form-data, campo "video"
                 -> devuelve el MP4 parcheado como descarga
                 -> despues de entregarlo, borra todo del disco
   GET  /health  -> { ok: true }

   Variables de entorno (todas opcionales):
     API_KEY         si la pones, hay que mandar el header x-api-key
     ALLOWED_ORIGIN  dominios permitidos (CORS), separados por coma. Por defecto *
     MAX_MB          tamano maximo del video en MB. Por defecto 150
     MAX_PENDING     videos en proceso/cola a la vez. Por defecto 5
   ============================================================ */

const express = require('express');
const multer  = require('multer');
const fs      = require('fs');
const os      = require('os');
const path    = require('path');
const crypto  = require('crypto');
const { patchVideo } = require('./patcher');

const PORT        = Number(process.env.PORT) || 3000;
const API_KEY     = process.env.API_KEY || '';
const ORIGINS     = (process.env.ALLOWED_ORIGIN || '*')
  .split(',').map(s => s.trim()).filter(Boolean);
const MAX_MB      = Number(process.env.MAX_MB) || 150;
const MAX_PENDING = Number(process.env.MAX_PENDING) || 5;
const ORPHAN_MIN  = 15;

/* ---------- carpeta temporal (se vacia al arrancar y al apagar) ---------- */

const TMP = path.join(os.tmpdir(), 'kayro-patch');
fs.rmSync(TMP, { recursive: true, force: true });
fs.mkdirSync(TMP, { recursive: true });

function wipeAll(){
  try{ fs.rmSync(TMP, { recursive: true, force: true }); }catch(_){}
}

process.on('SIGTERM', () => { wipeAll(); process.exit(0); });
process.on('SIGINT',  () => { wipeAll(); process.exit(0); });

// Borra archivos huerfanos (por si algo se corto a la mitad)
setInterval(() => {
  const limit = Date.now() - ORPHAN_MIN * 60 * 1000;

  fs.readdir(TMP, (e, list) => {
    if(e) return;

    for(const f of list){
      const p = path.join(TMP, f);

      fs.stat(p, (err, st) => {
        if(!err && st.mtimeMs < limit)
          fs.rm(p, { force: true }, () => {});
      });
    }
  });
}, 5 * 60 * 1000).unref();

/* ---------- errores ---------- */

const ERR = {
  NO_FILE:         [400, 'No video received. Send it as multipart field "video".',
                         'No se recibió ningún video. Envíalo en el campo "video".'],
  CODEC:           [422, 'Only H.264 videos are supported.',
                         'Solo se aceptan videos H.264.'],
  RESOLUTION:      [422, 'The video is above 1080p.',
                         'El video supera 1080p.'],
  FPS:             [422, 'The video is above 120 fps.',
                         'El video supera 120 fps.'],
  ALREADY_PATCHED: [409, 'This video is already patched.',
                         'Este video ya está parcheado.'],
  BROKEN:          [422, 'The MP4 is broken or not supported.',
                         'El MP4 está roto o no es compatible.'],
  TOO_LARGE:       [413, 'The file is larger than ' + MAX_MB + ' MB.',
                         'El archivo supera ' + MAX_MB + ' MB.'],
  BUSY:            [503, 'Server is busy, try again in a minute.',
                         'Servidor ocupado, intenta de nuevo en un minuto.'],
  UNAUTHORIZED:    [401, 'Invalid or missing API key.',
                         'API key inválida o ausente.'],
  SERVER:          [500, 'Unexpected error.',
                         'Error inesperado.']
};

function sendErr(res, code, detail){
  if(res.headersSent) return;

  const [status, en, es] = ERR[code] || ERR.SERVER;

  res.status(status).json({
    ok: false,
    error: code,
    message: en,
    message_es: es,
    detail: detail || undefined
  });
}

/* ---------- cola: un video a la vez (cuida la RAM de Render) ---------- */

let running = 0;
const waiting = [];

function pending(){
  return running + waiting.length;
}

function enqueue(fn){
  return new Promise((resolve, reject) => {
    const run = async () => {
      running++;

      try{
        resolve(await fn());
      }catch(e){
        reject(e);
      }finally{
        running--;

        const next = waiting.shift();
        if(next) next();
      }
    };

    if(running < 1) run();
    else waiting.push(run);
  });
}

/* ---------- utilidades ---------- */

// multer entrega el nombre como latin1; lo regresamos a UTF-8 (acentos, ñ, emojis)
function fixName(n){
  n = String(n || 'video.mp4');

  return /[^\u0000-\u00ff]/.test(n)
    ? n
    : Buffer.from(n, 'latin1').toString('utf8');
}

function auth(req, res, next){
  if(!API_KEY) return next();

  const got  = Buffer.from(String(req.get('x-api-key') || ''));
  const want = Buffer.from(API_KEY);

  if(got.length === want.length && crypto.timingSafeEqual(got, want))
    return next();

  sendErr(res, 'UNAUTHORIZED');
}

/* ---------- app ---------- */

const app = express();
app.disable('x-powered-by');

// CORS
app.use((req, res, next) => {
  const origin = req.get('origin');

  if(ORIGINS.includes('*')){
    res.set('Access-Control-Allow-Origin', '*');
  }else if(origin && ORIGINS.includes(origin)){
    res.set('Access-Control-Allow-Origin', origin);
    res.set('Vary', 'Origin');
  }

  res.set({
    'Access-Control-Allow-Methods': 'POST, GET, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type, x-api-key',
    'Access-Control-Expose-Headers': 'Content-Disposition',
    'Cache-Control': 'no-store'
  });

  if(req.method === 'OPTIONS') return res.sendStatus(204);

  next();
});

app.get('/', (req, res) => res.json({ ok: true, service: 'kayro-patch-api' }));
app.get('/health', (req, res) => res.json({ ok: true }));

const upload = multer({
  storage: multer.diskStorage({
    destination: TMP,
    filename: (req, file, cb) =>
      cb(null, crypto.randomBytes(12).toString('hex') + '.in')
  }),
  limits: { fileSize: MAX_MB * 1024 * 1024, files: 1 }
}).single('video');

app.post(
  '/patch',
  auth,
  (req, res, next) => {
    upload(req, res, err => {
      if(!err) return next();

      sendErr(
        res,
        err.code === 'LIMIT_FILE_SIZE' ? 'TOO_LARGE' : 'NO_FILE',
        err.message
      );
    });
  },
  async (req, res) => {
    const file = req.file;

    if(!file) return sendErr(res, 'NO_FILE');

    const inPath  = file.path;
    const outPath = inPath.replace(/\.in$/, '.out.mp4');

    const rm = p => fs.rm(p, { force: true }, () => {});

    // Se dispara al terminar la entrega, al fallar o si el cliente se desconecta:
    // en todos los casos se borra el original y el parcheado.
    res.on('close', () => { rm(inPath); rm(outPath); });

    if(pending() >= MAX_PENDING) return sendErr(res, 'BUSY');

    try{
      const { filename } = await enqueue(async () => {
        const buf = await fs.promises.readFile(inPath);
        const r   = await patchVideo(buf, fixName(file.originalname));

        await fs.promises.writeFile(outPath, r.output);

        return { filename: r.filename };   // solo el nombre: libera el buffer de RAM
      });

      rm(inPath);   // el original ya no hace falta

      res.download(outPath, filename, err => {
        if(err && !res.headersSent) sendErr(res, 'SERVER');
      });

    }catch(e){
      if(e && e.name === 'KayroPatchError')
        return sendErr(res, e.code, e.message);

      console.error('Unexpected error:', e && e.message);
      sendErr(res, 'SERVER');
    }
  }
);

app.use((req, res) => res.status(404).json({ ok: false, error: 'NOT_FOUND' }));

const server = app.listen(PORT, '0.0.0.0', () =>
  console.log('Kayro Patch API listening on :' + PORT)
);

server.requestTimeout   = 20 * 60 * 1000;  // subidas lentas de videos grandes
server.keepAliveTimeout = 65 * 1000;       // mayor que el del proxy de Render
