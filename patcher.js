'use strict';

/* ============================================================
   KAYRO STUDIO ENHANCE MP4 PATCH ENGINE v2.0
   ============================================================ */

const VERSION = '2.0-api';
const ENCODER_TAG = 'kayro method';

// Limites de la API (H.264 solamente)
const MAX_LONG_SIDE  = 1920;  // lado largo maximo (1920x1080 o 1080x1920)
const MAX_SHORT_SIDE = 1080;  // lado corto maximo
const MAX_FPS        = 120;
const FPS_TOLERANCE  = 0.5;   // 120.5 como maximo por redondeos de timescale
const ATOM_TOO = new Uint8Array([0xa9,0x74,0x6f,0x6f]);
const UNKNOWN_DURATION = new Uint8Array([
  0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff
]);

const CONTAINERS = new Set([
  'moov','trak','mdia','minf','stbl','edts'
]);

const MAX_TABLE_ENTRIES = 0x2faf080;

function makeError(msg,code){
  const e = new Error(msg);
  e.name = 'KayroPatchError';
  e.code = code || 'BROKEN';
  return e;
}

function fail(msg,code){
  throw makeError(msg,code);
}

function readU32(buf,o){
  return (
    ((buf[o]<<24) |
    (buf[o+1]<<16) |
    (buf[o+2]<<8) |
    buf[o+3]) >>> 0
  );
}

function readU64(buf,o){
  const hi = readU32(buf,o);
  const lo = readU32(buf,o+4);
  const n = hi * 4294967296 + lo;

  if(!Number.isSafeInteger(n))
    fail('MP4 out of bounds.');

  return n;
}

function u32ToBytes(n){
  const b = new Uint8Array(4);
  new DataView(b.buffer).setUint32(0,n>>>0,false);
  return b;
}

function u64ToBytes(n){
  if(!Number.isSafeInteger(n) || n < 0)
    fail('Invalid 64-bit.');

  const b = new Uint8Array(8);
  const hi = Math.floor(n/4294967296);
  const lo = n - hi * 4294967296;
  const dv = new DataView(b.buffer);

  dv.setUint32(0,hi>>>0,false);
  dv.setUint32(4,lo>>>0,false);

  return b;
}

function strToBytes(s){
  const b = new Uint8Array(s.length);

  for(let i=0;i<s.length;i++)
    b[i] = s.charCodeAt(i) & 0xff;

  return b;
}

function concatBytes(arr){
  let len = 0;

  for(const x of arr)
    len += x.length;

  const out = new Uint8Array(len);
  let o = 0;

  for(const x of arr){
    out.set(x,o);
    o += x.length;
  }

  return out;
}

function copyBytes(b){
  return new Uint8Array(b);
}

function toUint8(x){
  return x instanceof Uint8Array
    ? x
    : new Uint8Array(x);
}

function indexOfBytes(hay,needle){
  const n = strToBytes(needle);

  outer:
  for(let i=0;i+n.length<=hay.length;i++){
    for(let j=0;j<n.length;j++){
      if(hay[i+j]!==n[j])
        continue outer;
    }

    return i;
  }

  return -1;
}

function asciiType(buf,o){
  return String.fromCharCode(
    buf[o+4],
    buf[o+5],
    buf[o+6],
    buf[o+7]
  );
}

/* ============================================================
   MP4 BOX
   ============================================================ */

function Box(type,payload,children){
  this.type = type;
  this.payload = payload || new Uint8Array(0);
  this.children = children || null;
}

Box.prototype.find = function(t){
  if(!this.children)
    return null;

  for(const c of this.children){
    if(c.type === t)
      return c;
  }

  return null;
};

Box.prototype.findAll = function(t){
  return this.children
    ? this.children.filter(c=>c.type===t)
    : [];
};

Box.prototype.path = function(...args){
  let c = this;

  for(const a of args){
    if(!c)
      return null;

    c = c.find(a);
  }

  return c;
};

Box.prototype.clone = function(){
  return this.children
    ? new Box(
        this.type,
        null,
        this.children.map(c=>c.clone())
      )
    : new Box(
        this.type,
        copyBytes(this.payload)
      );
};

Box.prototype.serialize = function(){
  const body = this.children
    ? concatBytes(this.children.map(c=>c.serialize()))
    : this.payload;

  if(body.length + 8 > 0xffffffff){
    return concatBytes([
      u32ToBytes(1),
      strToBytes(this.type),
      u64ToBytes(body.length + 16),
      body
    ]);
  }

  return concatBytes([
    u32ToBytes(body.length + 8),
    strToBytes(this.type),
    body
  ]);
};

/* ============================================================
   PARSE CONTAINERS
   ============================================================ */

function parseContainerChildren(buf,start,end){
  const out = [];
  let o = start;

  while(o + 8 <= end){
    let size = readU32(buf,o);
    let hs = 8;

    if(size === 1){
      if(o + 16 > end)
        break;

      size = readU64(buf,o+8);
      hs = 16;

    }else if(size === 0){
      size = end - o;
    }

    if(size < hs || o + size > end)
      break;

    const t = asciiType(buf,o);

    if(CONTAINERS.has(t)){
      out.push(
        new Box(
          t,
          null,
          parseContainerChildren(
            buf,
            o + hs,
            o + size
          )
        )
      );
    }else{
      out.push(
        new Box(
          t,
          buf.subarray(o + hs,o + size)
        )
      );
    }

    o += size;
  }

  return out;
}

const makeBoxStr = (t,p) =>
  concatBytes([
    u32ToBytes(p.length + 8),
    strToBytes(t),
    p
  ]);

const makeBoxBytes = (t,p) =>
  concatBytes([
    u32ToBytes(p.length + 8),
    t,
    p
  ]);

/* ============================================================
   BOX SCANNER
   ============================================================ */

function scanBoxes(buf,start,end,where){
  const out = [];
  let o = start;

  while(o < end){
    if(o + 8 > end)
      fail('Malformed layout.');

    let size = readU32(buf,o);
    let hs = 8;

    if(size === 1){
      if(o + 16 > end)
        fail('Truncated header.');

      size = readU64(buf,o+8);
      hs = 16;

    }else if(size === 0){
      size = end - o;
    }

    if(
      !Number.isSafeInteger(size) ||
      size < hs ||
      o + size > end
    ){
      fail('Malformed box size.');
    }

    out.push({
      type: asciiType(buf,o),
      start: o,
      end: o + size,
      header: hs
    });

    o += size;
  }

  return out;
}

function scanTopLevel(buf){
  return scanBoxes(
    buf,
    0,
    buf.length,
    'top-level'
  );
}

/* ============================================================
   ENCODER TAG / METADATA
   ============================================================ */

function makeEncoderAtom(tag){
  const payload = concatBytes([
    u32ToBytes(1),
    u32ToBytes(0),
    strToBytes(tag)
  ]);

  return makeBoxBytes(
    ATOM_TOO,
    makeBoxStr('data',payload)
  );
}

function makeMetaBox(tag){
  const hdlr = concatBytes([
    u32ToBytes(0),
    u32ToBytes(0),
    strToBytes('mdir'),
    new Uint8Array(12),
    new Uint8Array(1)
  ]);

  return makeBoxStr(
    'meta',
    concatBytes([
      u32ToBytes(0),
      makeBoxStr('hdlr',hdlr),
      makeBoxStr(
        'ilst',
        makeEncoderAtom(tag)
      )
    ])
  );
}

function rewriteIlst(buf,tag){
  const out = [];

  for(
    const b of scanBoxes(
      buf,
      0,
      buf.length,
      'ilst'
    )
  ){
    if(b.type !== '©too'){
      out.push(
        copyBytes(
          buf.subarray(
            b.start,
            b.end
          )
        )
      );
    }
  }

  if(tag)
    out.push(makeEncoderAtom(tag));

  return concatBytes(out);
}

function rewriteMeta(buf,tag){
  if(buf.length < 4)
    fail('Malformed meta.');

  const out = [
    copyBytes(buf.subarray(0,4))
  ];

  let placed = false;

  for(
    const b of scanBoxes(
      buf,
      4,
      buf.length,
      'meta'
    )
  ){
    if(b.type === 'ilst'){
      const inner = buf.subarray(
        b.start + b.header,
        b.end
      );

      out.push(
        makeBoxStr(
          'ilst',
          rewriteIlst(
            inner,
            placed ? null : tag
          )
        )
      );

      placed = placed || !!tag;

    }else{
      out.push(
        copyBytes(
          buf.subarray(
            b.start,
            b.end
          )
        )
      );
    }
  }

  if(!placed && tag){
    out.push(
      makeBoxStr(
        'ilst',
        makeEncoderAtom(tag)
      )
    );
  }

  return makeBoxStr(
    'meta',
    concatBytes(out)
  );
}

function rewriteUdta(buf,tag){
  const out = [];
  let placed = false;

  for(
    const b of scanBoxes(
      buf,
      0,
      buf.length,
      'udta'
    )
  ){
    if(b.type === 'meta'){
      const inner = buf.subarray(
        b.start + b.header,
        b.end
      );

      out.push(
        rewriteMeta(
          inner,
          placed ? null : tag
        )
      );

      placed = placed || !!tag;

    }else{
      out.push(
        copyBytes(
          buf.subarray(
            b.start,
            b.end
          )
        )
      );
    }
  }

  if(!placed && tag)
    out.push(makeMetaBox(tag));

  return concatBytes(out);
}

function ensureEncoderTag(moov,tag){
  const udtas = moov.findAll('udta');

  if(udtas.length){
    let placed = false;

    for(const u of udtas){
      const t = placed ? null : tag;

      placed = placed || !!t;

      if(u.children)
        fail('Unexpected udta tree.');

      u.payload = rewriteUdta(
        u.payload,
        t
      );
    }

  }else{
    moov.children.push(
      new Box(
        'udta',
        makeMetaBox(tag)
      )
    );
  }
}

function hasEncoderTag(moov,tag){
  return moov
    .findAll('udta')
    .some(
      u =>
        !u.children &&
        indexOfBytes(u.payload,tag) >= 0
    );
}

/* ============================================================
   MVHD DURATION PATCH
   ============================================================ */

function isUnknownDuration(p){
  if(
    !p ||
    p.length < 0x20 ||
    p[0] !== 1
  )
    return false;

  for(let i=0;i<8;i++){
    if(p[0x18+i] !== 0xff)
      return false;
  }

  return true;
}

function patchMvhd(p){
  if(!p || p.length < 4)
    fail('Malformed mvhd.');

  if(p[0] === 1){
    if(p.length < 0x70)
      fail('Malformed mvhd-1.');

    const out = copyBytes(p);

    out.set(
      UNKNOWN_DURATION,
      0x18
    );

    return out;
  }

  if(p[0] !== 0)
    fail('Unsupported mvhd version.');

  if(p.length < 0x64)
    fail('Malformed mvhd-0.');

  return concatBytes([
    new Uint8Array([
      1,
      p[1],
      p[2],
      p[3]
    ]),
    u32ToBytes(0),
    copyBytes(p.subarray(4,8)),
    u32ToBytes(0),
    copyBytes(p.subarray(8,12)),
    copyBytes(p.subarray(12,16)),
    copyBytes(UNKNOWN_DURATION),
    copyBytes(p.subarray(20,100))
  ]);
}

/* ============================================================
   SAMPLE TABLES
   ============================================================ */

function validateTableEntries(
  buf,
  header,
  entry,
  name
){
  if(!buf || buf.length < 8)
    fail('Truncated table.');

  const n = readU32(buf,4);

  if(n > MAX_TABLE_ENTRIES)
    fail('Table too large.');

  if(header + n * entry > buf.length)
    fail('Truncated table.');

  return n;
}

function readStts(buf){
  const n = validateTableEntries(
    buf,
    8,
    8,
    'stts'
  );

  const out = [];

  for(let i=0;i<n;i++){
    out.push([
      readU32(buf,8+i*8),
      readU32(buf,12+i*8)
    ]);
  }

  return out;
}

function readStsz(buf){
  if(!buf || buf.length < 12)
    fail('Truncated stsz.');

  const def = readU32(buf,4);
  const n = readU32(buf,8);

  if(n > MAX_TABLE_ENTRIES)
    fail('stsz too large.');

  if(
    !def &&
    12 + n * 4 > buf.length
  ){
    fail('Truncated stsz.');
  }

  const out = new Array(n);

  for(let i=0;i<n;i++){
    out[i] = def ||
      readU32(buf,12+i*4);
  }

  return out;
}

function readStsc(buf){
  const n = validateTableEntries(
    buf,
    8,
    12,
    'stsc'
  );

  const out = [];

  for(let i=0;i<n;i++){
    const r = [
      readU32(buf,8+i*12),
      readU32(buf,12+i*12),
      readU32(buf,16+i*12)
    ];

    if(
      r[0] < 1 ||
      r[1] < 1 ||
      r[2] < 1 ||
      (
        i > 0 &&
        r[0] <= out[i-1][0]
      )
    ){
      fail('Invalid chunk mapping.');
    }

    out.push(r);
  }

  return out;
}

function readChunkOffsets(box){
  const p = box.payload;

  const n = validateTableEntries(
    p,
    8,
    box.type === 'co64' ? 8 : 4,
    box.type
  );

  const out = new Array(n);

  for(let i=0;i<n;i++){
    out[i] =
      box.type === 'co64'
        ? readU64(p,8+i*8)
        : readU32(p,8+i*4);
  }

  return out;
}

function writeChunkOffsets(box,list){
  let max = 0;

  for(const v of list){
    if(v > max)
      max = v;
  }

  if(max > 0xffffffff){
    box.type = 'co64';

    const p = new Uint8Array(
      8 + list.length * 8
    );

    new DataView(
      p.buffer
    ).setUint32(
      4,
      list.length >>> 0,
      false
    );

    for(let i=0;i<list.length;i++){
      p.set(
        u64ToBytes(list[i]),
        8+i*8
      );
    }

    box.payload = p;

  }else{
    box.type = 'stco';

    const p = new Uint8Array(
      8 + list.length * 4
    );

    new DataView(
      p.buffer
    ).setUint32(
      4,
      list.length >>> 0,
      false
    );

    for(let i=0;i<list.length;i++){
      p.set(
        u32ToBytes(list[i]),
        8+i*4
      );
    }

    box.payload = p;
  }
}

/* ============================================================
   TRACK HELPERS
   ============================================================ */

const findStbl =
  trak =>
    trak.path(
      'mdia',
      'minf',
      'stbl'
    );

const findOffsetsBox =
  trak => {
    const s = findStbl(trak);

    return s
      ? (s.find('stco') || s.find('co64'))
      : null;
  };

const readHandlerType =
  trak => {
    const h = trak.path(
      'mdia',
      'hdlr'
    );

    if(!h || h.payload.length < 12)
      return '';

    return String.fromCharCode(
      h.payload[8],
      h.payload[9],
      h.payload[10],
      h.payload[11]
    );
  };

const findInStbl =
  (t,n) => {
    const s = findStbl(t);
    return s ? s.find(n) : null;
  };

const readCodecType =
  trak => {
    const s =
      findInStbl(trak,'stsd');

    if(
      !s ||
      s.payload.length < 16
    )
      return '';

    const p = s.payload;
    const n = readU32(p,4);
    const sz = readU32(p,8);

    if(
      n < 1 ||
      sz < 8 ||
      8 + sz > p.length
    )
      return '';

    return String.fromCharCode(
      p[12],
      p[13],
      p[14],
      p[15]
    );
  };

const readStsdEntryCount =
  trak => {
    const s =
      findInStbl(trak,'stsd');

    return s &&
      s.payload.length >= 8
      ? readU32(s.payload,4)
      : 0;
  };

/* ============================================================
   VIDEO INFO (ancho, alto, fps)
   ============================================================ */

function readVideoInfo(t){
  const stsd = findInStbl(t.trak,'stsd');
  const mdhd = t.trak.path('mdia','mdhd');
  const stts = findInStbl(t.trak,'stts');

  if(!stsd || stsd.payload.length < 44 || !mdhd || !stts)
    fail('Could not read video info.','BROKEN');

  const sp = stsd.payload;
  const width  = (sp[40] << 8) | sp[41];
  const height = (sp[42] << 8) | sp[43];

  const mp = mdhd.payload;
  const timescale =
    mp[0] === 1
      ? readU32(mp,20)
      : readU32(mp,12);

  let ticks = 0;

  for(const e of readStts(stts.payload))
    ticks += e[0] * e[1];

  if(!width || !height || !timescale || !ticks)
    fail('Could not read video info.','BROKEN');

  return {
    width,
    height,
    fps: t.count / (ticks / timescale)
  };
}

/* ============================================================
   TRACK ANALYSIS
   ============================================================ */

function analyzeTrack(trak){
  const stbl = findStbl(trak);

  if(!stbl)
    return null;

  const stsz = stbl.find('stsz');
  const stsc = stbl.find('stsc');
  const stts = stbl.find('stts');
  const off = findOffsetsBox(trak);

  if(!stsz || !stsc || !stts || !off)
    return null;

  const sizes = readStsz(stsz.payload);
  const count = sizes.length;
  const chunks = readChunkOffsets(off);
  const runs = readStsc(stsc.payload);

  if(
    !count ||
    !chunks.length ||
    !runs.length
  )
    return null;

  const perChunk = [];

  for(let i=0;i<runs.length;i++){
    const first = runs[i][0];
    const last =
      i + 1 < runs.length
        ? runs[i+1][0] - 1
        : chunks.length;

    if(
      first > last ||
      last > chunks.length
    )
      return null;

    for(
      let c=first;
      c<=last;
      c++
    ){
      perChunk.push(
        runs[i][1]
      );
    }
  }

  if(
    perChunk.length !== chunks.length
  )
    return null;

  if(
    perChunk.reduce(
      (a,b)=>a+b,
      0
    ) !== count
  )
    return null;

  const offsets = new Array(count);
  let k = 0;

  for(let i=0;i<chunks.length;i++){
    let p = chunks[i];

    for(
      let j=0;
      j<perChunk[i];
      j++
    ){
      offsets[k] = p;
      p += sizes[k];
      k++;
    }
  }

  if(
    readStts(stts.payload)
      .reduce(
        (a,e)=>a+e[0],
        0
      ) !== count
  )
    return null;

  return {
    trak,
    stsz,
    off,
    sizes,
    offsets,
    runs,
    count,
    handler: readHandlerType(trak),
    codec: readCodecType(trak)
  };
}

/* ============================================================
   MP4 PARSER
   ============================================================ */

function parseFile(buf){
  if(!buf.length)
    fail('Empty file.');

  const top =
    scanTopLevel(buf);

  const ftyp =
    top.filter(
      b => b.type === 'ftyp'
    );

  const moov =
    top.filter(
      b => b.type === 'moov'
    );

  const mdat =
    top.filter(
      b => b.type === 'mdat'
    );

  if(
    ftyp.length !== 1 ||
    moov.length !== 1 ||
    mdat.length !== 1
  )
    fail('Invalid MP4.');

  if(
    top.some(
      b => b.type === 'moof'
    )
  )
    fail(
      'Fragmented MP4/MOV files are not supported.'
    );

  const M =
    new Box(
      'moov',
      null,
      parseContainerChildren(
        buf,
        moov[0].start + moov[0].header,
        moov[0].end
      )
    );

  const traks =
    M.findAll('trak');

  if(!traks.length)
    fail('No tracks found.');

  const mvhd = M.find('mvhd');

  if(
    !mvhd ||
    mvhd.payload.length < 4
  )
    fail('Missing mvhd.');

  if(
    isUnknownDuration(
      mvhd.payload
    )
  )
    fail('Already patched.','ALREADY_PATCHED');

  if(
    mvhd.payload[0] !== 0 &&
    mvhd.payload[0] !== 1
  )
    fail(
      'Unsupported mvhd version.'
    );

  const tables =
    traks.map(analyzeTrack);

  if(
    tables.some(
      t => t === null
    )
  )
    fail('Could not map tables.');

  for(const t of tables){
    if(
      readStsdEntryCount(t.trak) !== 1 ||
      t.runs.some(
        r => r[2] !== 1
      )
    ){
      fail(
        'Multiple codec descriptions not supported.'
      );
    }
  }

  const videos =
    tables.filter(
      t => t.handler === 'vide'
    );

  if(videos.length !== 1)
    fail(
      'Expected exactly one video track.'
    );

  const video = videos[0];

  const isAvc =
    video.codec === 'avc1' ||
    video.codec === 'avc3';

  const isHevc =
    video.codec === 'hvc1' ||
    video.codec === 'hev1' ||
    video.codec === 'hvc2' ||
    video.codec === 'hev2';

  if(!isAvc)
    fail(
      isHevc
        ? 'HEVC/H.265 is not supported. Only H.264.'
        : 'Unsupported codec. Only H.264.',
      'CODEC'
    );

  const info = readVideoInfo(video);

  if(
    Math.max(info.width,info.height) > MAX_LONG_SIDE ||
    Math.min(info.width,info.height) > MAX_SHORT_SIDE
  )
    fail(
      'Resolution ' + info.width + 'x' + info.height +
      ' is above 1080p.',
      'RESOLUTION'
    );

  if(info.fps > MAX_FPS + FPS_TOLERANCE)
    fail(
      'Frame rate ' + info.fps.toFixed(2) +
      ' fps is above ' + MAX_FPS + '.',
      'FPS'
    );

  const audio =
    tables.filter(
      t =>
        t.handler === 'soun' &&
        t.codec === 'mp4a'
    );

  if(!audio.length)
    fail(
      'No AAC track found.'
    );

  return {
    top,
    ftypBox: ftyp[0],
    moovBox: moov[0],
    mdatBox: mdat[0],
    moov: M,
    mvhd,
    traks,
    tables,
    video,
    sourceAudio: audio[0],
    isAvc,
    isHevc
  };
}

/* ============================================================
   APPLY PATCH
   ============================================================ */

function applyPatch(src,P){
  const {
    top,
    moovBox,
    mdatBox,
    moov
  } = P;

  const mvhd =
    moov.find('mvhd');

  mvhd.payload =
    patchMvhd(
      mvhd.payload
    );

  ensureEncoderTag(
    moov,
    ENCODER_TAG
  );

  if(
    moovBox.start < mdatBox.start
  ){
    const tracks =
      moov
        .findAll('trak')
        .filter(
          t => findOffsetsBox(t)
        );

    const saved =
      tracks.map(
        t =>
          readChunkOffsets(
            findOffsetsBox(t)
          )
      );

    for(let i=0;i<4;i++){
      const delta =
        moov.serialize().length -
        (moovBox.end - moovBox.start);

      let typeChanged = false;

      tracks.forEach(
        (t,j)=>{
          const b =
            findOffsetsBox(t);

          const before =
            b.type;

          writeChunkOffsets(
            b,
            saved[j].map(
              v => v + delta
            )
          );

          if(
            b.type !== before
          )
            typeChanged = true;
        }
      );

      if(!typeChanged)
        break;
    }
  }

  const newMoov =
    moov.serialize();

  const out = [];

  for(const b of top){
    out.push(
      b.start === moovBox.start
        ? newMoov
        : src.subarray(
            b.start,
            b.end
          )
    );
  }

  return concatBytes(out);
}

/* ============================================================
   VALIDATE PATCHED OUTPUT
   ============================================================ */

function validatePatchedOutput(buf){
  const top =
    scanTopLevel(buf);

  if(
    !top.length ||
    top[top.length-1].end !== buf.length
  )
    fail('Incomplete.');

  const moov =
    top.filter(
      b => b.type === 'moov'
    );

  const mdat =
    top.filter(
      b => b.type === 'mdat'
    );

  if(
    moov.length !== 1 ||
    mdat.length !== 1
  )
    fail('Validation failed.');

  const M =
    new Box(
      'moov',
      null,
      parseContainerChildren(
        buf,
        moov[0].start + moov[0].header,
        moov[0].end
      )
    );

  if(
    !hasEncoderTag(
      M,
      ENCODER_TAG
    )
  )
    fail('No encoder tag.');

  const mvhd =
    M.find('mvhd');

  if(
    !mvhd ||
    !isUnknownDuration(
      mvhd.payload
    )
  )
    fail('Duration not unknown.');

  const lo =
    mdat[0].start +
    mdat[0].header;

  const hi =
    mdat[0].end;

  for(const t of M.findAll('trak')){
    const o =
      findOffsetsBox(t);

    if(!o)
      continue;

    for(
      const v of readChunkOffsets(o)
    ){
      if(
        v < lo ||
        v >= hi
      )
        fail(
          'Offset outside media data.'
        );
    }
  }
}

/* ============================================================
   PUBLIC PATCH API
   ============================================================ */

function patchVideoRaw(fileBuffer){
  const buf =
    toUint8(fileBuffer);

  const P =
    parseFile(buf);

  const out =
    applyPatch(
      buf,
      P
    );

  validatePatchedOutput(out);

  return out;
}

async function patchVideoFile(
  fileBuffer,
  originalName = 'video.mp4'
){
  try{
    const output =
      patchVideoRaw(
        fileBuffer
      );

    const on =
      (originalName || 'video.mp4')
        .replace(
          /\.[^/.]+$/,
          ''
        );

    return {
      output,
      filename:
        on + ' - Patched.mp4',

      stats: {
        strategy:
          'mvhd-sentinel + ©too-encoder-tag + stco-realign',
        version: VERSION,
        encoderTag: ENCODER_TAG
      }
    };

  }catch(error){
    console.error(
      'Patcher error:',
      error.message
    );

    throw error;
  }
}

function checkCompatibility(input){
  try{
    const P =
      parseFile(
        toUint8(input)
      );

    return {
      compatible: true,
      reason: '',
      codec: P.video.codec,
      isAvc: P.isAvc,
      isHevc: P.isHevc,
      sampleCount: P.video.count,
      audioTrackCount:
        P.tables.filter(
          t => t.handler === 'soun'
        ).length
    };

  }catch(e){
    return {
      compatible: false,
      reason:
        e && e.message
          ? e.message
          : 'Not supported.',
      codec: '',
      isAvc: false,
      isHevc: false,
      sampleCount: 0,
      audioTrackCount: 0
    };
  }
}

/* ============================================================
   EXPORT
   ============================================================ */

module.exports = {
  patchVideo: patchVideoFile,
  patchVideoRaw,
  checkCompatibility,
  VERSION,
  ENCODER_TAG
};
