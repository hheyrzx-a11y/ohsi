/* =========================================================
   KAYRO STUDIO — HQ PATCH API  (server.js)
   Solo API (sin HTML). Recibe un MP4 H.264/AVC, lo parcha con
   patch.js (KAYRO_STUDIO_HQ), le pone la etiqueta de metadatos
   "BYPASS BY KAYRO STUDIO", lo entrega y después borra todo.
   Sin recompresión: el contenido de video queda intacto.
   ========================================================= */
"use strict";

const http = require("http");
const fs = require("fs");
const fsp = fs.promises;
const os = require("os");
const path = require("path");
const crypto = require("crypto");

const express = require("express");
const cors = require("cors");
const Busboy = require("busboy");

const KAYRO_STUDIO_HQ = require("./patch.js"); // <- tu parche, sin tocar

/* =====================================================
   CONFIG
   ===================================================== */

const PORT = Number(process.env.PORT) || 3000;
const VERSION = "1.0.0";

const MAX_MB = 150;                       // máximo de subida
const MAX_BYTES = MAX_MB * 1024 * 1024;
const MULTIPART_OVERHEAD = 1024 * 1024;   // margen para los bordes del multipart

const MAX_LONG_SIDE = 1920;               // 1080p: 1920x1080 (o vertical 1080x1920)
const MAX_SHORT_SIDE = 1080;
const MAX_FPS = 120;
const FPS_TOLERANCE = 0.5;                // 120 fps medidos pueden dar 120.02, etc.

const TAG_TEXT = "BYPASS BY KAYRO STUDIO";

// El parche trabaja en memoria (~2x el tamaño del video). Con 1 a la vez
// un video de 150 MB cabe en los 512 MB de Render. Súbelo solo si tu plan tiene más RAM.
const PATCH_CONCURRENCY = Math.max(1, Number(process.env.PATCH_CONCURRENCY) || 1);
const MAX_ACTIVE = Math.max(1, Number(process.env.MAX_ACTIVE) || 4); // peticiones /patch a la vez
const MAX_JOBS = 2000;

const TMP_DIR = process.env.TMP_DIR || path.join(os.tmpdir(), "kayro-hq");
const CORS_ORIGIN = process.env.CORS_ORIGIN || "*";

/* =====================================================
   ERRORES
   ===================================================== */

class HttpError extends Error {
  constructor(status, code, message, detalle = null, closeConn = false) {
    super(message);
    this.status = status;
    this.code = code;
    this.detalle = detalle;
    this.closeConn = closeConn;
  }
}

/* =====================================================
   LECTOR MP4 MÍNIMO (validación + etiqueta)
   ===================================================== */

const CONTAINERS = new Set(["moov", "trak", "mdia", "minf", "stbl"]);

const CODEC_NAMES = {
  hvc1: "H.265/HEVC",
  hev1: "H.265/HEVC",
  av01: "AV1",
  vp09: "VP9",
  mp4v: "MPEG-4 Visual",
  s263: "H.263",
  apcn: "ProRes",
  apch: "ProRes"
};

function readBoxes(buf, start, end) {
  const out = [];
  let p = start;
  while (p + 8 <= end) {
    let size = buf.readUInt32BE(p);
    const type = buf.toString("latin1", p + 4, p + 8);
    let header = 8;
    if (size === 1) {
      if (p + 16 > end) break;
      size = Number(buf.readBigUInt64BE(p + 8));
      header = 16;
    } else if (size === 0) {
      size = end - p;
    }
    if (size < header || p + size > end) break;
    out.push({ type, start: p, end: p + size, header });
    p += size;
  }
  return out;
}

const subBoxes = (buf, box) => readBoxes(buf, box.start + box.header, box.end);

function pick(buf, box, ...route) {
  let cur = box;
  for (const type of route) {
    cur = cur && subBoxes(buf, cur).find((b) => b.type === type);
    if (!cur) return null;
  }
  return cur;
}

/** Recorre las cajas de primer nivel leyendo solo las cabeceras (no carga el archivo). */
async function scanTopLevel(fh, fileSize) {
  const boxes = [];
  const head = Buffer.alloc(16);
  let pos = 0;
  while (pos + 8 <= fileSize) {
    const { bytesRead } = await fh.read(head, 0, 16, pos);
    if (bytesRead < 8) break;
    let size = head.readUInt32BE(0);
    const type = head.toString("latin1", 4, 8);
    let header = 8;
    if (size === 1) {
      if (bytesRead < 16) break;
      size = Number(head.readBigUInt64BE(8));
      header = 16;
    } else if (size === 0) {
      size = fileSize - pos;
    }
    if (size < header) break;
    if (pos + size > fileSize) {
      boxes.push({ type, start: pos, end: pos + size, header, truncated: true });
      break;
    }
    boxes.push({ type, start: pos, end: pos + size, header });
    pos += size;
  }
  return boxes;
}

function analyzeMoov(buf, moovHeader) {
  const root = { type: "moov", start: 0, end: buf.length, header: moovHeader };
  const videos = [];

  for (const trak of subBoxes(buf, root).filter((b) => b.type === "trak")) {
    const hdlr = pick(buf, trak, "mdia", "hdlr");
    if (!hdlr) continue;
    const h = hdlr.start + hdlr.header + 8;
    if (buf.toString("latin1", h, h + 4) !== "vide") continue;

    const mdhd = pick(buf, trak, "mdia", "mdhd");
    const stbl = pick(buf, trak, "mdia", "minf", "stbl");
    const stsd = stbl && pick(buf, stbl, "stsd");
    const stts = stbl && pick(buf, stbl, "stts");
    if (!mdhd || !stsd || !stts) continue;

    // Primera entrada de muestra (VisualSampleEntry)
    const entry = stsd.start + stsd.header + 8;
    if (entry + 36 > stsd.end) continue;
    const codec = buf.toString("latin1", entry + 4, entry + 8);
    const width = buf.readUInt16BE(entry + 32);
    const height = buf.readUInt16BE(entry + 34);

    // Timescale (mdhd v0 / v1)
    const mdhdBase = mdhd.start + mdhd.header;
    const version = buf[mdhdBase];
    const timescale = buf.readUInt32BE(mdhdBase + (version === 1 ? 20 : 12));

    // fps reales = muestras / duración (usando stts)
    const n = buf.readUInt32BE(stts.start + stts.header + 4);
    let p = stts.start + stts.header + 8;
    let samples = 0;
    let ticks = 0;
    for (let i = 0; i < n && p + 8 <= stts.end; i++, p += 8) {
      const c = buf.readUInt32BE(p);
      const d = buf.readUInt32BE(p + 4);
      samples += c;
      ticks += c * d;
    }
    const fps = ticks > 0 && timescale > 0 ? (samples * timescale) / ticks : 0;
    const duration = timescale > 0 ? ticks / timescale : 0;

    videos.push({ codec, width, height, fps, duration, samples });
  }

  if (!videos.length) {
    throw new HttpError(
      415,
      "SIN_VIDEO",
      "El archivo no tiene una pista de video. Sube un video MP4 en H.264/AVC."
    );
  }

  const avc = videos.find((v) => v.codec === "avc1" || v.codec === "avc3");
  if (!avc) {
    const raw = videos[0].codec.trim();
    const nombre = CODEC_NAMES[raw] || raw;
    throw new HttpError(
      415,
      "NO_ES_H264",
      `Este video no está en H.264/AVC (códec detectado: ${nombre}). Tienes que subir un video MP4 en H.264/AVC.`,
      { codecDetectado: nombre }
    );
  }

  const w = avc.width;
  const h = avc.height;
  if (!w || !h) {
    throw new HttpError(422, "RESOLUCION_DESCONOCIDA", "No se pudo leer la resolución del video.");
  }
  if (Math.max(w, h) > MAX_LONG_SIDE || Math.min(w, h) > MAX_SHORT_SIDE) {
    throw new HttpError(
      422,
      "RESOLUCION_NO_PERMITIDA",
      `El video es de ${w}x${h}. Solo se aceptan videos de hasta 1080p (1920x1080).`,
      { ancho: w, alto: h, maximo: "1920x1080" }
    );
  }

  const fps = Math.round(avc.fps * 100) / 100;
  if (!avc.fps) {
    throw new HttpError(422, "FPS_DESCONOCIDOS", "No se pudieron leer los fps del video.");
  }
  if (avc.fps > MAX_FPS + FPS_TOLERANCE) {
    throw new HttpError(
      422,
      "FPS_NO_PERMITIDOS",
      `El video va a ${fps} fps. Solo se aceptan videos de hasta ${MAX_FPS} fps.`,
      { fps, maximo: MAX_FPS }
    );
  }

  return { codec: "H.264/AVC", width: w, height: h, fps, duration: Math.round(avc.duration * 100) / 100 };
}

async function probeMp4(file) {
  const fh = await fsp.open(file, "r");
  try {
    const { size } = await fh.stat();
    const top = await scanTopLevel(fh, size);

    if (!top.length || top[0].type !== "ftyp") {
      throw new HttpError(415, "NO_ES_MP4", "El archivo no es un MP4 válido. Sube un video .mp4 en H.264/AVC.");
    }
    if (top.some((b) => b.truncated)) {
      throw new HttpError(422, "MP4_INCOMPLETO", "El MP4 está incompleto o dañado.");
    }
    if (top.some((b) => b.type === "moof")) {
      throw new HttpError(422, "MP4_FRAGMENTADO", "Este MP4 es fragmentado (fMP4) y no es compatible con el parche.");
    }
    const moov = top.find((b) => b.type === "moov");
    if (!moov) {
      throw new HttpError(422, "MP4_SIN_MOOV", "El MP4 está dañado o incompleto (no tiene índice moov).");
    }
    const mdats = top.filter((b) => b.type === "mdat").length;
    if (mdats !== 1) {
      throw new HttpError(422, "MP4_NO_COMPATIBLE", "El MP4 no tiene la estructura que necesita el parche (debe tener un solo bloque de datos).");
    }

    const len = moov.end - moov.start;
    const buf = Buffer.alloc(len);
    const { bytesRead } = await fh.read(buf, 0, len, moov.start);
    if (bytesRead !== len) {
      throw new HttpError(422, "MP4_INCOMPLETO", "El MP4 está incompleto o dañado.");
    }
    return analyzeMoov(buf, moov.header);
  } finally {
    await fh.close();
  }
}

/* ---------- Etiqueta de metadatos (udta > meta > ilst) ---------- */

function mkBox(type, ...parts) {
  const payload = Buffer.concat(parts);
  const box = Buffer.alloc(8 + payload.length);
  box.writeUInt32BE(box.length, 0);
  box.write(type, 4, 4, "latin1");
  payload.copy(box, 8);
  return box;
}

function textItem(type, text) {
  const flags = Buffer.alloc(8); // tipo 1 = UTF-8, locale 0
  flags.writeUInt32BE(1, 0);
  return mkBox(type, mkBox("data", flags, Buffer.from(text, "utf8")));
}

function buildTagBox() {
  const hdlr = mkBox(
    "hdlr",
    Buffer.alloc(8),
    Buffer.from("mdir", "latin1"),
    Buffer.from("appl", "latin1"),
    Buffer.alloc(9)
  );
  const ilst = mkBox(
    "ilst",
    textItem("\u00A9nam", TAG_TEXT), // título
    textItem("\u00A9cmt", TAG_TEXT), // comentario
    textItem("\u00A9too", TAG_TEXT)  // encoder
  );
  return mkBox("udta", mkBox("meta", Buffer.alloc(4), hdlr, ilst));
}

function shiftChunkOffsets(moovBuf, delta) {
  const walk = (start, end) => {
    for (const b of readBoxes(moovBuf, start, end)) {
      if (b.type === "stco") {
        const base = b.start + b.header;
        const n = moovBuf.readUInt32BE(base + 4);
        let p = base + 8;
        if (p + n * 4 > b.end) throw new Error("stco dañado");
        for (let i = 0; i < n; i++, p += 4) {
          const v = moovBuf.readUInt32BE(p) + delta;
          if (v > 0xffffffff) throw new Error("Offset fuera de rango (stco)");
          moovBuf.writeUInt32BE(v, p);
        }
      } else if (b.type === "co64") {
        const base = b.start + b.header;
        const n = moovBuf.readUInt32BE(base + 4);
        let p = base + 8;
        if (p + n * 8 > b.end) throw new Error("co64 dañado");
        for (let i = 0; i < n; i++, p += 8) {
          moovBuf.writeBigUInt64BE(moovBuf.readBigUInt64BE(p) + BigInt(delta), p);
        }
      } else if (CONTAINERS.has(b.type)) {
        walk(b.start + b.header, b.end);
      }
    }
  };
  walk(8, moovBuf.length);
}

/**
 * Añade la etiqueta al final de moov y corrige los offsets.
 * Devuelve 3 trozos [antes de moov, moov nuevo, después de moov] sin copiar el video.
 */
function addTag(buf) {
  const moov = readBoxes(buf, 0, buf.length).find((b) => b.type === "moov");
  if (!moov || moov.header !== 8) throw new Error("moov no encontrado tras el parche");

  const udta = buildTagBox();
  const oldLen = moov.end - moov.start;
  const newMoov = Buffer.alloc(oldLen + udta.length);
  buf.copy(newMoov, 0, moov.start, moov.end);
  udta.copy(newMoov, oldLen);
  newMoov.writeUInt32BE(newMoov.length, 0);
  shiftChunkOffsets(newMoov, udta.length);

  return [buf.subarray(0, moov.start), newMoov, buf.subarray(moov.end)];
}

/* =====================================================
   TRABAJOS + PROGRESO EN TIEMPO REAL (SSE)
   ===================================================== */

const JOB_ID_RE = /^[A-Za-z0-9_-]{8,64}$/;
const jobs = new Map();

class Job {
  constructor(id) {
    this.id = id;
    this.clients = new Set();
    this.started = false;
    this.expires = Date.now() + 10 * 60 * 1000; // placeholder si nadie sube nada
    this.state = {
      jobId: id,
      stage: "esperando",
      percent: 0,
      message: "Esperando el video…",
      finished: false
    };
  }

  emit(event) {
    const payload = `event: ${event}\ndata: ${JSON.stringify(this.state)}\n\n`;
    for (const c of this.clients) c.write(payload);
  }

  update(stage, percent, message, extra) {
    if (this.state.finished) return;
    const pct = Math.max(this.state.percent, Math.min(99, Math.floor(percent)));
    if (stage === this.state.stage && pct === this.state.percent && message === this.state.message) return;
    this.state = { ...this.state, ...extra, stage, percent: pct, message };
    this.emit("progress");
  }

  finish() {
    if (this.state.finished) return;
    this.state = {
      ...this.state,
      stage: "listo",
      percent: 100,
      message: "Listo: video entregado y borrado del servidor.",
      finished: true
    };
    this.emit("done");
    this.closeClients();
  }

  fail(err) {
    if (this.state.finished) return;
    this.state = {
      ...this.state,
      stage: "error",
      message: err.message,
      error: err.code || "ERROR",
      finished: true
    };
    this.emit("failed");
    this.closeClients();
  }

  closeClients() {
    for (const c of this.clients) c.end();
    this.clients.clear();
    this.expires = Date.now() + 2 * 60 * 1000; // el estado final queda 2 min por si alguien se conecta tarde
  }
}

function getJob(id) {
  let job = jobs.get(id);
  if (!job) {
    job = new Job(id);
    jobs.set(id, job);
  }
  return job;
}

/* ---------- Cupo para el parche (usa mucha RAM) ---------- */

let slotsBusy = 0;
const slotQueue = [];

function acquirePatchSlot(job) {
  if (slotsBusy < PATCH_CONCURRENCY) {
    slotsBusy++;
    return Promise.resolve();
  }
  job.update("en_cola", 50, "En cola: hay otros videos procesándose…");
  return new Promise((resolve) => slotQueue.push(resolve));
}

function releasePatchSlot() {
  const next = slotQueue.shift();
  if (next) next();
  else slotsBusy--;
}

/* =====================================================
   SUBIDA (multipart -> disco, con progreso)
   ===================================================== */

function receiveUpload(req, job, inPath, declaredLength) {
  return new Promise((resolve, reject) => {
    let settled = false;
    const done = (err, value) => {
      if (settled) return;
      settled = true;
      if (err) reject(err);
      else resolve(value);
    };

    let received = 0;
    req.on("data", (chunk) => {
      received += chunk.length;
      if (received > MAX_BYTES + MULTIPART_OVERHEAD) {
        req.destroy(); // alguien manda más de lo permitido sin avisar
        return;
      }
      if (declaredLength > 0) {
        job.update(
          "subiendo",
          (45 * received) / declaredLength,
          "Recibiendo el video…",
          { receivedBytes: received, totalBytes: declaredLength }
        );
      }
    });

    let bb;
    try {
      bb = Busboy({
        headers: req.headers,
        limits: { files: 1, fileSize: MAX_BYTES, fields: 5, fieldSize: 1024, parts: 10 }
      });
    } catch (e) {
      return done(new HttpError(400, "FORMATO_INVALIDO", 'Envía el video como multipart/form-data en el campo "video".'));
    }

    let fileSeen = false;
    let originalName = "video.mp4";
    let out = null;
    let written = null;

    bb.on("file", (field, stream, info) => {
      if (fileSeen) {
        stream.resume();
        return;
      }
      fileSeen = true;

      const name = String(info.filename || "");
      const okExt = /\.mp4$/i.test(name);
      const okMime = /^video\/mp4$/i.test(info.mimeType || "");
      if (!okExt && !okMime) {
        stream.resume();
        return done(new HttpError(415, "NO_ES_MP4", "Solo se aceptan archivos .mp4 en H.264/AVC."));
      }
      if (name) originalName = path.basename(name);

      out = fs.createWriteStream(inPath);
      written = new Promise((r) => out.once("close", r));
      out.once("error", () => done(new HttpError(500, "ERROR_DISCO", "No se pudo guardar el video en el servidor.")));

      stream.on("limit", () => {
        stream.unpipe(out);
        out.destroy();
        stream.resume();
        done(new HttpError(413, "ARCHIVO_MUY_GRANDE", `El video supera el máximo de ${MAX_MB} MB.`));
      });
      stream.pipe(out);
    });

    bb.on("error", () => done(new HttpError(400, "FORMATO_INVALIDO", "No se pudo leer el formulario enviado.")));

    bb.on("close", async () => {
      if (settled) return;
      if (!fileSeen) {
        return done(new HttpError(400, "SIN_ARCHIVO", 'No se recibió ningún video. Envíalo en el campo "video".'));
      }
      await written;
      if (settled) return;
      if (!out.bytesWritten) {
        return done(new HttpError(400, "ARCHIVO_VACIO", "El archivo está vacío."));
      }
      done(null, { filename: originalName, size: out.bytesWritten });
    });

    req.once("close", () => {
      if (!req.complete) done(new HttpError(499, "SUBIDA_CANCELADA", "La subida se canceló antes de terminar."));
    });

    req.pipe(bb);
  });
}

/* =====================================================
   PARCHE
   ===================================================== */

async function runPatch(job, inPath, outPath, originalName) {
  job.update("parchando", 50, "Leyendo el video…");
  let data = await fsp.readFile(inPath);
  await fsp.rm(inPath, { force: true }); // ya está en memoria: libera disco

  job.update("parchando", 55, "Aplicando el parche KAYRO STUDIO HQ…");
  await new Promise((r) => setImmediate(r)); // deja salir el progreso antes del trabajo pesado

  let patched;
  let filename;
  try {
    const r = KAYRO_STUDIO_HQ.patchHQWithInfo({ name: originalName }, data);
    patched = Buffer.from(r.output.buffer, r.output.byteOffset, r.output.byteLength);
    filename = r.filename;
  } catch (e) {
    console.error("[parche] falló:", e.message);
    throw new HttpError(422, "PARCHE_FALLO", `No se pudo parchar este MP4 (${e.message}).`);
  } finally {
    data = null;
  }

  job.update("etiquetando", 60, `Escribiendo la etiqueta ${TAG_TEXT}…`);
  let parts;
  try {
    parts = addTag(patched);
  } catch (e) {
    console.error("[etiqueta] falló:", e.message);
    throw new HttpError(500, "ETIQUETA_FALLO", "No se pudo escribir la etiqueta en el video.");
  }

  await fsp.writeFile(outPath, parts[0]);
  await fsp.appendFile(outPath, parts[1]);
  await fsp.appendFile(outPath, parts[2]);
  return filename;
}

/* =====================================================
   APP
   ===================================================== */

const app = express();
app.disable("x-powered-by");
app.use(
  cors({
    origin: CORS_ORIGIN,
    methods: ["GET", "POST", "OPTIONS"],
    exposedHeaders: ["X-Job-Id", "Content-Disposition", "Content-Length"]
  })
);

app.get("/", (req, res) => {
  res.json({
    ok: true,
    servicio: "KAYRO STUDIO HQ Patch API",
    version: VERSION,
    limites: {
      formato: "MP4",
      codec: "H.264/AVC",
      resolucionMaxima: "1920x1080",
      fpsMaximos: MAX_FPS,
      pesoMaximoMB: MAX_MB
    },
    endpoints: {
      "POST /patch": 'multipart/form-data, campo "video". Opcional: ?jobId=<id> para seguir el progreso. Responde con el MP4 parcheado.',
      "GET /progress/:jobId": "Progreso en tiempo real (Server-Sent Events).",
      "GET /status/:jobId": "Estado actual en JSON (alternativa sin SSE).",
      "GET /health": "Comprobación de estado."
    }
  });
});

app.get("/health", (req, res) => res.json({ ok: true }));

/* ---------- Progreso ---------- */

app.get("/progress/:jobId", (req, res) => {
  const id = req.params.jobId;
  if (!JOB_ID_RE.test(id)) {
    return res.status(400).json({ ok: false, error: "JOBID_INVALIDO", mensaje: "jobId inválido." });
  }
  if (!jobs.has(id) && jobs.size >= MAX_JOBS) {
    return res.status(503).json({ ok: false, error: "SERVIDOR_OCUPADO", mensaje: "Intenta de nuevo en un momento." });
  }

  const job = getJob(id);
  res.writeHead(200, {
    "Content-Type": "text/event-stream; charset=utf-8",
    "Cache-Control": "no-cache, no-transform",
    Connection: "keep-alive",
    "X-Accel-Buffering": "no"
  });
  res.write("retry: 2000\n\n");

  const s = job.state;
  const event = !s.finished ? "progress" : s.stage === "listo" ? "done" : "failed";
  res.write(`event: ${event}\ndata: ${JSON.stringify(s)}\n\n`);

  if (s.finished) return res.end();
  job.clients.add(res);
  req.on("close", () => job.clients.delete(res));
});

app.get("/status/:jobId", (req, res) => {
  const job = jobs.get(req.params.jobId);
  if (!job) {
    return res.status(404).json({ ok: false, error: "JOB_NO_ENCONTRADO", mensaje: "No existe ese jobId." });
  }
  res.json({ ok: true, ...job.state });
});

/* ---------- Parchar ---------- */

let active = 0;

function sendError(res, job, err) {
  const e = err instanceof HttpError ? err : new HttpError(500, "ERROR_INTERNO", "Ocurrió un error procesando el video.");
  if (!(err instanceof HttpError)) console.error("[error]", err);
  job.fail(e);
  if (res.headersSent) {
    res.destroy();
    return;
  }
  if (e.closeConn) res.setHeader("Connection", "close");
  res.status(e.status).json({
    ok: false,
    jobId: job.id,
    error: e.code,
    mensaje: e.message,
    ...(e.detalle ? { detalle: e.detalle } : {})
  });
}

app.post("/patch", async (req, res) => {
  let jobId = req.query.jobId;
  if (jobId === undefined) jobId = crypto.randomUUID();
  if (typeof jobId !== "string" || !JOB_ID_RE.test(jobId)) {
    return res.status(400).json({
      ok: false,
      error: "JOBID_INVALIDO",
      mensaje: "jobId inválido. Usa de 8 a 64 caracteres: letras, números, guion o guion bajo."
    });
  }
  const existing = jobs.get(jobId);
  if (existing && existing.started) {
    return res.status(409).json({ ok: false, error: "JOBID_EN_USO", mensaje: "Ese jobId ya está en uso. Genera otro." });
  }
  if (active >= MAX_ACTIVE || (!existing && jobs.size >= MAX_JOBS)) {
    res.set("Retry-After", "15");
    return res.status(503).json({
      ok: false,
      error: "SERVIDOR_OCUPADO",
      mensaje: "Hay muchos videos procesándose. Intenta de nuevo en un momento."
    });
  }

  const job = getJob(jobId);
  job.started = true;
  job.expires = null;
  active++;
  res.setHeader("X-Job-Id", jobId);

  const inPath = path.join(TMP_DIR, `${jobId}.in.mp4`);
  const outPath = path.join(TMP_DIR, `${jobId}.out.mp4`);
  let closed = false;
  let rs = null;

  res.once("finish", () => job.finish());

  // Pase lo que pase (entregado, error o cliente desconectado): borrar todo.
  res.once("close", () => {
    closed = true;
    active--;
    if (rs) rs.destroy();
    if (!job.state.finished) {
      job.fail(new HttpError(499, "CONEXION_CERRADA", "La conexión se cerró antes de terminar."));
    }
    Promise.all([fsp.rm(inPath, { force: true }), fsp.rm(outPath, { force: true })]).catch(() => {});
  });

  try {
    if (!req.is("multipart/form-data")) {
      throw new HttpError(400, "FORMATO_INVALIDO", 'Envía el video como multipart/form-data en el campo "video".');
    }
    const declared = Number(req.headers["content-length"]) || 0;
    if (declared > MAX_BYTES + MULTIPART_OVERHEAD) {
      throw new HttpError(413, "ARCHIVO_MUY_GRANDE", `El video supera el máximo de ${MAX_MB} MB.`, null, true);
    }

    // 1) Recibir
    job.update("subiendo", 0, "Recibiendo el video…");
    const up = await receiveUpload(req, job, inPath, declared);

    // 2) Revisar (H.264/AVC, 1080p, 120 fps)
    job.update("validando", 45, "Revisando que sea H.264/AVC, hasta 1080p y 120 fps…");
    const info = await probeMp4(inPath);
    job.update("validando", 50, `Video válido: ${info.codec} ${info.width}x${info.height} a ${info.fps} fps.`);

    // 3) Parchar + etiquetar
    await acquirePatchSlot(job);
    let filename;
    try {
      if (closed) return;
      filename = await runPatch(job, inPath, outPath, up.filename);
    } finally {
      releasePatchSlot();
    }
    if (closed) return;

    // 4) Entregar (al terminar, 'close' borra los archivos)
    const stat = await fsp.stat(outPath);
    const asciiName = filename.replace(/[^A-Za-z0-9._-]/g, "_");
    const utf8Name = encodeURIComponent(filename).replace(/['()*]/g, (c) => "%" + c.charCodeAt(0).toString(16).toUpperCase());

    res.status(200);
    res.setHeader("Content-Type", "video/mp4");
    res.setHeader("Content-Length", stat.size);
    res.setHeader("Content-Disposition", `attachment; filename="${asciiName}"; filename*=UTF-8''${utf8Name}`);
    res.setHeader("Cache-Control", "no-store");

    job.update("entregando", 65, "Entregando el video parcheado…");
    let sent = 0;
    rs = fs.createReadStream(outPath);
    rs.on("data", (c) => {
      sent += c.length;
      job.update("entregando", 65 + 35 * (sent / stat.size), "Entregando el video parcheado…", {
        sentBytes: sent,
        totalBytes: stat.size
      });
    });
    rs.on("error", (e) => {
      console.error("[entrega] falló:", e.message);
      res.destroy();
    });
    rs.pipe(res);
  } catch (err) {
    if (closed) return;
    req.unpipe();
    if (!(err instanceof HttpError && err.closeConn)) req.resume(); // vacía lo que falte para que el cliente reciba el error
    sendError(res, job, err);
  }
});

/* ---------- 404 / errores ---------- */

app.use((req, res) => {
  res.status(404).json({ ok: false, error: "NO_ENCONTRADO", mensaje: "Ruta no encontrada." });
});

app.use((err, req, res, next) => {
  console.error("[express]", err);
  if (res.headersSent) return res.destroy();
  res.status(500).json({ ok: false, error: "ERROR_INTERNO", mensaje: "Error interno del servidor." });
});

/* =====================================================
   ARRANQUE
   ===================================================== */

function start() {
  // Al arrancar, borra cualquier resto de ejecuciones anteriores.
  fs.rmSync(TMP_DIR, { recursive: true, force: true });
  fs.mkdirSync(TMP_DIR, { recursive: true });

  const server = http.createServer(app);
  server.requestTimeout = 30 * 60 * 1000; // subidas lentas de hasta 150 MB
  server.headersTimeout = 65 * 1000;
  server.keepAliveTimeout = 65 * 1000;     // mayor que el del proxy de Render

  const timers = [
    // latido para que el proxy no corte el SSE + limpieza de trabajos viejos
    setInterval(() => {
      const now = Date.now();
      for (const [id, job] of jobs) {
        for (const c of job.clients) c.write(": ping\n\n");
        if (job.expires && now > job.expires) {
          job.closeClients();
          jobs.delete(id);
        }
      }
    }, 15 * 1000),

    // red de seguridad: borra archivos temporales con más de 30 min
    setInterval(async () => {
      try {
        const now = Date.now();
        for (const f of await fsp.readdir(TMP_DIR)) {
          const p = path.join(TMP_DIR, f);
          const st = await fsp.stat(p).catch(() => null);
          if (st && now - st.mtimeMs > 30 * 60 * 1000) await fsp.rm(p, { force: true });
        }
      } catch (_) {}
    }, 5 * 60 * 1000)
  ];
  timers.forEach((t) => t.unref());

  server.listen(PORT, "0.0.0.0", () => {
    console.log(`KAYRO STUDIO HQ Patch API v${VERSION} escuchando en el puerto ${PORT}`);
  });

  process.on("SIGTERM", () => {
    server.close();
    fs.rmSync(TMP_DIR, { recursive: true, force: true });
    process.exit(0);
  });

  return server;
}

process.on("unhandledRejection", (e) => console.error("[unhandledRejection]", e));

if (require.main === module) {
  start();
}

module.exports = { app, start, probeMp4, addTag, runPatch, Job, HttpError };
