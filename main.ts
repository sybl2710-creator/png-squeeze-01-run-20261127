import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS: Record<number, number> = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
const CHUNKS = ['IHDR', 'PLTE', 'tRNS', 'IDAT', 'IEND'];

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes: Uint8Array, start = 0, end = bytes.length): number {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

const ascii = (s: string) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function pngOf(chunks: [string, Uint8Array][]): Uint8Array {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width: number, height: number, colourType: number): Uint8Array {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

function paeth(a: number, b: number, c: number): number {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function filterRow(type: number, cur: Uint8Array, prev: Uint8Array | null, bpp: number, out: Uint8Array) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row: Uint8Array): number {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

function decodePng(bytes: Uint8Array, expect: { width: number; height: number } | null = null): { ok: boolean; why?: string; width?: number; height?: number; colourType?: number; rgba?: Uint8Array } {
  if (!(bytes instanceof Uint8Array)) return { ok: false, why: 'it is not bytes' };
  if (bytes.length < SIGNATURE.length || SIGNATURE.some((b, i) => bytes[i] !== b)) return { ok: false, why: 'it does not start with the PNG signature' };
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = SIGNATURE.length;
  let header: any = null;
  let palette: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idat: Uint8Array[] = [];
  let idatDone = false;
  let ended = false;
  while (at < bytes.length) {
    if (ended) return { ok: false, why: 'it holds bytes after IEND' };
    if (at + 12 > bytes.length) return { ok: false, why: `a chunk at byte ${at} is cut short` };
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) return { ok: false, why: `the chunk at byte ${at} claims ${len} bytes the file does not hold` };
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (!/^[A-Za-z]{4}$/.test(type)) return { ok: false, why: `the chunk at byte ${at} has no chunk type` };
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) return { ok: false, why: `the ${type} chunk at byte ${at} fails its CRC` };
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (!CHUNKS.includes(type)) return { ok: false, why: `it holds a ${type} chunk` };
    if (header === null && type !== 'IHDR') return { ok: false, why: `its first chunk is ${type}, not IHDR` };
    if (type !== 'IDAT' && idat.length > 0) idatDone = true;
    if (type === 'IHDR') {
      if (header !== null) return { ok: false, why: 'it holds IHDR twice' };
      if (len !== 13) return { ok: false, why: 'its IHDR is not 13 bytes' };
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], compression: data[10], filter: data[11], interlace: data[12] };
      if (header.width === 0 || header.height === 0) return { ok: false, why: 'its width or height is 0' };
      if (expect !== null && (header.width !== expect.width || header.height !== expect.height)) return { ok: false, why: 'dimension mismatch' };
      if (header.depth !== 8) return { ok: false, why: 'depth not 8' };
      if (!(header.colourType in CHANNELS)) return { ok: false, why: 'invalid colour type' };
      if (header.compression !== 0 || header.filter !== 0) return { ok: false, why: 'compression/filter method not 0' };
      if (header.interlace !== 0) return { ok: false, why: 'interlaced' };
    } else if (type === 'PLTE') {
      if (palette !== null) return { ok: false, why: 'PLTE twice' };
      if (header.colourType !== 3) return { ok: false, why: 'PLTE with wrong colour type' };
      if (idat.length > 0) return { ok: false, why: 'PLTE follows IDAT' };
      if (len === 0 || len % 3 !== 0 || len > 768) return { ok: false, why: 'invalid PLTE length' };
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) return { ok: false, why: 'tRNS twice' };
      if (idat.length > 0) return { ok: false, why: 'tRNS follows IDAT' };
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null) return { ok: false, why: 'tRNS before PLTE' };
        if (len > palette.length / 3) return { ok: false, why: 'tRNS longer than palette' };
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) return { ok: false, why: 'invalid tRNS length' };
      } else return { ok: false, why: 'invalid colour type for tRNS' };
      trns = data;
    } else if (type === 'IDAT') {
      if (idatDone) return { ok: false, why: 'IDAT chunks not in a row' };
      if (header.colourType === 3 && palette === null) return { ok: false, why: 'IDAT before PLTE' };
      idat.push(data);
    } else {
      if (len !== 0) return { ok: false, why: 'IEND not empty' };
      ended = true;
    }
  }
  if (!ended) return { ok: false, why: 'no IEND' };
  if (idat.length === 0) return { ok: false, why: 'no IDAT' };
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  let raw: Uint8Array;
  try {
    raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  } catch (err) {
    return { ok: false, why: 'inflate failed' };
  }
  if (raw.length !== expected) return { ok: false, why: 'inflated size mismatch' };

  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) return { ok: false, why: 'invalid filter type' };
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }

  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette!.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette![e * 3];
      lut[e * 4 + 1] = palette![e * 3 + 1];
      lut[e * 4 + 2] = palette![e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) return { ok: false, why: 'palette index out of bounds' };
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { ok: true, width, height, colourType, rgba };
}

function wordsOf(rgba: Uint8Array): Uint32Array {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}

function analyse(rgba: Uint8Array) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true;
  let grey = true;
  const counts = new Map<number, number>();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]] as [number, number, number, number], word: c, count: counts.get(c)! };
  });
  return { opaque, grey, colours };
}

function transparentKey(rgba: Uint8Array, grey: boolean): number {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return -1;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return -1;
  }
  if (key === -1) return -1;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return -1;
  }
  return key;
}

function samplesOf(rgba: Uint8Array, ct: number): Uint8Array {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

function paletteOrder(colours: any[], order: string) {
  const lum = (c: any) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

function paletteForm(rgba: Uint8Array, colours: any[], order: string) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i])!;
  return { plte, trns, indices };
}

function filtered(samples: Uint8Array, width: number, height: number, bpp: number, choice: number | string): Uint8Array {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride));
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
    } else {
      let bestType = 0;
      let bestSum = Infinity;
      for (let t = 0; t < 5; t++) {
        filterRow(t, cur, prev, bpp, trial[t]);
        const s = signedSum(trial[t]);
        if (s < bestSum) {
          bestSum = s;
          bestType = t;
        }
      }
      raw[at] = bestType;
      filterRow(bestType, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
    }
  }
  return raw;
}

function formsOf(rgba: Uint8Array) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms: any[] = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', [0, 'minsum']],
      ['luminance', [0, 'minsum']],
    ]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (grey) {
      // also try palette for grey images if colours <= 256
      const pCount = paletteForm(rgba, colours, 'count');
      forms.push({ colourType: 3, bpp: 1, samples: pCount.indices, plte: pCount.plte, trns: pCount.trns, filters: [0, 'minsum'] });
    } else {
      return forms;
    }
  }
  const key = opaque ? -1 : transparentKey(rgba, grey);
  let ct: number;
  let trns: Uint8Array | null = null;
  if (grey) {
    ct = opaque || key !== -1 ? 0 : 4;
    if (key !== -1) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== -1 ? 2 : 6;
    if (key !== -1) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = CHANNELS[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [0, 4, 'minsum'] });
  return forms;
}

const chunkBytes = (form: any) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

const LEN_BASE=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LEN_XN  =[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE=[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_XN=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];

const LEN_SYM=new Uint8Array(259), LEN_XV=new Uint16Array(259), LEN_EB=new Uint8Array(259);
for(let c=0;c<29;c++){const base=LEN_BASE[c],cnt=1<<LEN_XN[c];for(let k=0;k<cnt;k++){const l=base+k;if(l>258)break;if(c===27&&l===258)continue;LEN_SYM[l]=c;LEN_XV[l]=k;LEN_EB[l]=LEN_XN[c];}}
const DIST_SYM=new Uint8Array(32769), DIST_XV=new Uint16Array(32769), DIST_EB=new Uint8Array(32769);
for(let c=0;c<30;c++){const base=DIST_BASE[c],cnt=1<<DIST_XN[c];for(let k=0;k<cnt;k++){const d=base+k;if(d>32768)break;DIST_SYM[d]=c;DIST_XV[d]=k;DIST_EB[d]=DIST_XN[c];}}
const ORDER=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];

function buildLengths(freq, maxBits){
  const n=freq.length, out=new Uint8Array(n), syms=[];
  for(let s=0;s<n;s++) if(freq[s]>0) syms.push(s);
  const m=syms.length;
  if(m===0) return out;
  if(m===1){ out[syms[0]]=1; return out; }
  const maxN=2*m;
  const wt=new Float64Array(maxN), par=new Int32Array(maxN).fill(-1);
  const heap=new Int32Array(maxN+1); let hn=0;
  const less=(a,b)=> wt[a]<wt[b] || (wt[a]===wt[b] && a<b);
  for(let k=0;k<m;k++){wt[k]=freq[syms[k]];heap[hn]=k;let i=hn++;while(i>0){const p=(i-1)>>1;if(less(heap[i],heap[p])){const t=heap[i];heap[i]=heap[p];heap[p]=t;i=p;}else break;}}
  let next=m;
  while(hn>1){
    let top=heap[0];hn--;heap[0]=heap[hn];{let i=0;for(;;){let l=2*i+1;if(l>=hn)break;let r=l+1,s=l;if(r<hn&&less(heap[r],heap[l]))s=r;if(less(heap[s],heap[i])){const t=heap[i];heap[i]=heap[s];heap[s]=t;i=s;}else break;}}
    const a=top;
    top=heap[0];hn--;heap[0]=heap[hn];{let i=0;for(;;){let l=2*i+1;if(l>=hn)break;let r=l+1,s=l;if(r<hn&&less(heap[r],heap[l]))s=r;if(less(heap[s],heap[i])){const t=heap[i];heap[i]=heap[s];heap[s]=t;i=s;}else break;}}
    const b=top;
    wt[next]=wt[a]+wt[b];par[a]=next;par[b]=next;
    heap[hn]=next;{let i=hn++;while(i>0){const p=(i-1)>>1;if(less(heap[i],heap[p])){const t=heap[i];heap[i]=heap[p];heap[p]=t;i=p;}else break;}}
    next++;
  }
  const blCount=new Int32Array(64); let maxDepth=0;
  for(let k=0;k<m;k++){let d=0,x=k;while(par[x]!==-1){x=par[x];d++;}if(d>maxDepth)maxDepth=d;blCount[d]++;}
  if(maxDepth>maxBits){
    let overflow=0;
    for(let b=maxBits+1;b<=maxDepth;b++){overflow+=blCount[b];blCount[b]=0;}
    blCount[maxBits]+=overflow;
    while(overflow>0){
      let b=maxBits-1;
      while(b>0&&blCount[b]===0)b--;
      blCount[b]--;blCount[b+1]+=2;blCount[maxBits]--;overflow-=2;
    }
  }
  const order=syms.slice().sort((x,y)=>freq[x]-freq[y]||x-y);
  let idx=0;
  for(let b=maxBits;b>=1;b--){let cnt=blCount[b];while(cnt-->0){out[order[idx++]]=b;}}
  return out;
}

function revBits(c,l){let r=0;for(let k=0;k<l;k++){r=(r<<1)|(c&1);c>>=1;}return r;}
function canonCodes(lengths){
  const n=lengths.length;
  const bl=new Int32Array(16);
  for(let i=0;i<n;i++){const l=lengths[i];if(l)bl[l]++;}
  const nextc=new Int32Array(17); let code=0;
  for(let b=1;b<=15;b++){code=(code+bl[b-1])<<1;nextc[b]=code;}
  const codes=new Uint16Array(n);
  for(let i=0;i<n;i++){const l=lengths[i];if(l)codes[i]=revBits(nextc[l]++,l);}
  return codes;
}

class BW{
  constructor(){this.buf=new Uint8Array(1<<18);this.len=0;this.acc=0;this.cnt=0;}
  ensure(n){if(this.len+n>this.buf.length){let nb=new Uint8Array(Math.max(this.buf.length*2,this.len+n));nb.set(this.buf.subarray(0,this.len));this.buf=nb;}}
  bits(v,n){this.acc|=(v<<this.cnt);this.cnt+=n;while(this.cnt>=8){this.ensure(1);this.buf[this.len++]=this.acc&255;this.acc>>>=8;this.cnt-=8;}}
  flush(){if(this.cnt>0){this.ensure(1);this.buf[this.len++]=this.acc&255;this.acc=0;this.cnt=0;}}
}

const HASH_BITS=16, HASH_SIZE=1<<HASH_BITS;
let PREV=new Int32Array(0);
function buildChains(data){
  const n=data.length;
  if(PREV.length<n) PREV=new Int32Array(n);
  const prev=PREV;
  const head=new Int32Array(HASH_SIZE).fill(-1);
  const last=n-2;
  for(let i=0;i<last;i++){
    const v=(data[i]<<16)|(data[i+1]<<8)|data[i+2];
    const h=Math.imul(v,0x9E3779B1)>>>(32-HASH_BITS);
    prev[i]=head[h];head[h]=i;
  }
  if(n>=2) prev[n-2]=-1, prev[n-1]=-1;
  return prev;
}

const INF=1<<28;

function precomputeMatches(data,bs,be,prev,mlen,mdist,recOff,recLen,recDist){
  const nb=be-bs;
  let pool=0;
  const CHAIN=64, NICE=128;
  const CUT=32, CUTCH=8;
  const u32=(data.byteOffset&3)===0?new Uint32Array(data.buffer,data.byteOffset,data.length>>>2):null;
  for(let i=0;i<nb;i++){
    const g=bs+i;
    recOff[i]=pool;
    let maxLen=be-g; if(maxLen>258)maxLen=258;
    if(maxLen<3){continue;}
    let best=2, chain=CHAIN;
    const dlim=g-32768;
    let j=prev[g];
    while(j>=0&&j>dlim&&chain>0){
      chain--;
      if(data[j+best]!==data[g+best]){j=prev[j];continue;}
      let m=0;
      while(m+4<=maxLen && data[j+m]===data[g+m] && data[j+m+1]===data[g+m+1] && data[j+m+2]===data[g+m+2] && data[j+m+3]===data[g+m+3]) m+=4;
      while(m<maxLen&&data[j+m]===data[g+m])m++;
      if(m>best){
        best=m;
        recLen[pool]=m;recDist[pool]=g-j;pool++;
        if(best===maxLen)break;
        if(best>=NICE)break;
        if(best>=CUT&&chain>CUTCH)chain=CUTCH;
      }
      j=prev[j];
    }
    mlen[i]=best>=3?best:0;
    mdist[i]=pool>recOff[i]?recDist[pool-1]:0;
  }
  recOff[nb]=pool;
  return pool;
}

function dpPass(nb,data,bs,mlen,recOff,recLen,recDist,litBits,lenBits,distBits,clen,cdist,CAND){
  const dp=DP; // Int32Array(nb+1)
  dp[nb]=0;
  for(let i=nb-1;i>=0;i--){
    const b=data[bs+i];
    let bestCost=dp[i+1]+litBits[b];
    let bestLen=0,bestDist=0;
    const ml=mlen[i];
    if(ml>=3){
      const start=recOff[i], end=recOff[i+1];
      let lo=2;
      for(let r=start;r<end;r++){
        const hi=recLen[r];
        if(hi<=lo) continue;
        const dc=distBits[recDist[r]];
        const d=recDist[r];
        for(let L=lo+1;L<=hi;L++){
          const c=dp[i+L]+lenBits[L]+dc;
          if(c<bestCost){bestCost=c;bestLen=L;bestDist=d;}
        }
        lo=hi;
      }
    }
    dp[i]=bestCost;clen[i]=bestLen;cdist[i]=bestDist;
  }
}

function collectFreq(data,bs,be,clen,cdist,freqLL,freqD){
  freqLL.fill(0);freqD.fill(0);
  const nb=be-bs;
  let i=0;
  while(i<nb){
    const L=clen[i];
    if(L===0){freqLL[data[bs+i]]++;i++;}
    else{freqLL[257+LEN_SYM[L]]++;freqD[DIST_SYM[cdist[i]]]++;i+=L;}
  }
  freqLL[256]++;
}

function costsFromLengths(litLen,distLen,litBits,lenBits,distBits){
  for(let b=0;b<256;b++)litBits[b]=litLen[b]||15;
  for(let l=3;l<=258;l++)lenBits[l]=(litLen[257+LEN_SYM[l]]||15)+LEN_EB[l];
  for(let d=1;d<=32768;d++)distBits[d]=(distLen[DIST_SYM[d]]||15)+DIST_EB[d];
}

function fixedCosts(litBits,lenBits,distBits){
  for(let b=0;b<256;b++)litBits[b]=b<144?8:9;
  for(let l=3;l<=258;l++){const sym=257+LEN_SYM[l];lenBits[l]=(sym<=279?7:8)+LEN_EB[l];}
  for(let d=1;d<=32768;d++)distBits[d]=5+DIST_EB[d];
}

function rleLengths(seq,out){
  let o=0,i=0;
  while(i<seq.length){
    const v=seq[i];let run=1;while(i+run<seq.length&&seq[i+run]===v)run++;
    if(v===0){
      let r=run;
      while(r>=11){const t=r>138?138:r;out[o++]=18;out[o++]=t-11;r-=t;}
      while(r>=3){const t=r>10?10:r;out[o++]=17;out[o++]=t-3;r-=t;}
      while(r>0){out[o++]=0;out[o++]=0;r--;}
    }else{
      out[o++]=v;out[o++]=0;let r=run-1;
      while(r>=3){const t=r>6?6:r;out[o++]=16;out[o++]=t-3;r-=t;}
      while(r>0){out[o++]=v;out[o++]=0;r--;}
    }
    i+=run;
  }
  return o;
}

function adler32(data){let a=1,b=0;const n=data.length;let i=0;while(i<n){const end=i+5552<n?i+5552:n;for(;i<end;i++){a+=data[i];b+=a;}a%=65521;b%=65521;}return ((b<<16)|a)>>>0;}

const CAND=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
let DP=new Int32Array(0);

function deflateOptimal(data, opts={}){
  const BLOCK=opts.block||131072;
  const n=data.length;
  const prev=buildChains(data);
  const w=new BW();
  const freqLL=new Int32Array(286),freqD=new Int32Array(30);
  const litBits=new Int32Array(256),lenBits=new Int32Array(259),distBits=new Int32Array(32769);
  let litLen=new Uint8Array(286), distLen=new Uint8Array(30);
  const maxBlk=Math.min(n,BLOCK);
  if(DP.length<maxBlk+1) DP=new Int32Array(maxBlk+1);
  const mlen=new Uint16Array(maxBlk), mdist=new Uint16Array(maxBlk);
  const recOff=new Int32Array(maxBlk+1);
  const poolCap=maxBlk*3+64;
  const recLen=new Uint16Array(poolCap), recDist=new Uint16Array(poolCap);
  const clen=new Uint16Array(maxBlk), cdist=new Uint16Array(maxBlk);
  const seq=new Uint8Array(316);
  const toks=new Uint8Array(1200);
  const litCode=new Uint16Array(286), distCode=new Uint16Array(30);
  let bs=0;
  while(bs<n){
    const be=bs+BLOCK<n?bs+BLOCK:n;
    const nb=be-bs;
    const final=be===n;
    const PASSES=3;
    precomputeMatches(data,bs,be,prev,mlen,mdist,recOff,recLen,recDist);
    fixedCosts(litBits,lenBits,distBits);
    dpPass(nb,data,bs,mlen,recOff,recLen,recDist,litBits,lenBits,distBits,clen,cdist,CAND);
    for(let pass=1;pass<PASSES;pass++){
      collectFreq(data,bs,be,clen,cdist,freqLL,freqD);
      litLen=buildLengths(freqLL,15); distLen=buildLengths(freqD,15);
      if(!distLen.some(x=>x>0)) distLen[0]=1;
      costsFromLengths(litLen,distLen,litBits,lenBits,distBits);
      dpPass(nb,data,bs,mlen,recOff,recLen,recDist,litBits,lenBits,distBits,clen,cdist,CAND);
    }
    collectFreq(data,bs,be,clen,cdist,freqLL,freqD);
    litLen=buildLengths(freqLL,15); distLen=buildLengths(freqD,15);
    if(!distLen.some(x=>x>0)) distLen[0]=1;
    for(let i=0;i<286;i++)litCode[i]=0;
    canonInto(litLen,litCode); canonInto(distLen,distCode);
    let countLL=286; while(countLL>257&&litLen[countLL-1]===0)countLL--;
    let countD=30; while(countD>1&&distLen[countD-1]===0)countD--;
    for(let i=0;i<countLL;i++)seq[i]=litLen[i];
    for(let i=0;i<countD;i++)seq[countLL+i]=distLen[i];
    const nt=rleLengths(seq.subarray(0,countLL+countD),toks);
    const freqCL=new Int32Array(19);
    for(let i=0;i<nt;i+=2)freqCL[toks[i]]++;
    const clLen=buildLengths(freqCL,7);
    const clCode=new Uint16Array(19); canonInto(clLen,clCode);
    let hclen=19; while(hclen>4&&clLen[ORDER[hclen-1]]===0)hclen--;
    w.bits(final?1:0,1);w.bits(2,2);
    w.bits(countLL-257,5);w.bits(countD-1,5);w.bits(hclen-4,4);
    for(let i=0;i<hclen;i++)w.bits(clLen[ORDER[i]],3);
    for(let i=0;i<nt;i+=2){const s=toks[i];w.bits(clCode[s],clLen[s]);if(s===16)w.bits(toks[i+1],2);else if(s===17)w.bits(toks[i+1],3);else if(s===18)w.bits(toks[i+1],7);}
    let i=0;
    while(i<nb){
      const L=clen[i];
      if(L===0){const b=data[bs+i];w.bits(litCode[b],litLen[b]);i++;}
      else{
        const ls=LEN_SYM[L];
        w.bits(litCode[257+ls],litLen[257+ls]);
        if(LEN_EB[L])w.bits(LEN_XV[L],LEN_EB[L]);
        const d=cdist[i],ds=DIST_SYM[d];
        w.bits(distCode[ds],distLen[ds]);
        if(DIST_EB[d])w.bits(DIST_XV[d],DIST_EB[d]);
        i+=L;
      }
    }
    w.bits(litCode[256],litLen[256]);
    bs=be;
  }
  w.flush();
  const ad=adler32(data);
  const out=new Uint8Array(2+w.len+4);
  out[0]=0x78;out[1]=0x9c;
  out.set(w.buf.subarray(0,w.len),2);
  out[2+w.len]=(ad>>>24)&255;out[3+w.len]=(ad>>>16)&255;out[4+w.len]=(ad>>>8)&255;out[5+w.len]=ad&255;
  return out;
}

function canonInto(lengths,codes){
  const n=lengths.length;
  const bl=new Int32Array(16);
  for(let i=0;i<n;i++){const l=lengths[i];if(l)bl[l]++;}
  let code=0;
  const nextc=new Int32Array(17);
  for(let b=1;b<=15;b++){code=(code+bl[b-1])<<1;nextc[b]=code;}
  for(let i=0;i<n;i++){const l=lengths[i];if(l)codes[i]=revBits(nextc[l]++,l);else codes[i]=0;}
}


function compressAndPack(rgba: Uint8Array, width: number, height: number): Uint8Array {
  let best: { form: any; zlib: Uint8Array; data: Uint8Array; bytes: number } | null = null;
  for (const form of formsOf(rgba)) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, { level: 9, memLevel: 9 });
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) {
        best = { form, zlib: new Uint8Array(zlib.buffer, zlib.byteOffset, zlib.length), data, bytes };
      }
    }
  }
  const { form, data } = best!;
  let zlib = best!.zlib;
  const optimal = deflateOptimal(data);
  if (optimal.length < zlib.length) zlib = optimal;
  const chunks: [string, Uint8Array][] = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', zlib]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(I).sort()) {
  const inputBytes = readFileSync(join(I, id, 'image.png'));
  const decoded = decodePng(new Uint8Array(inputBytes));
  if (!decoded.ok) throw new Error(`${id}/image.png: ${decoded.why}`);
  mkdirSync(join(O, id), { recursive: true });
  const packed = compressAndPack(decoded.rgba!, decoded.width!, decoded.height!);
  writeFileSync(join(O, id, 'image.png'), packed);
}
