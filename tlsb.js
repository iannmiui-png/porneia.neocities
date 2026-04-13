// ── Manual PNG Decoder (avoids canvas premultiplied alpha corruption) ──
async function decodePNGRaw(base64) {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);

  let offset = 8;
  let width = 0, height = 0, channels = 4;
  const idatChunks = [];

  while (offset < bytes.length) {
    const dv = new DataView(bytes.buffer, offset, 8);
    const len = dv.getUint32(0);
    const type = String.fromCharCode(bytes[offset+4], bytes[offset+5], bytes[offset+6], bytes[offset+7]);
    const chunkData = bytes.slice(offset + 8, offset + 8 + len);

    if (type === 'IHDR') {
      const hdr = new DataView(chunkData.buffer, chunkData.byteOffset, chunkData.length);
      width = hdr.getUint32(0);
      height = hdr.getUint32(4);
      const colorType = chunkData[9];
      channels = colorType === 6 ? 4 : colorType === 2 ? 3 : colorType === 4 ? 2 : 1;
    } else if (type === 'IDAT') {
      idatChunks.push(chunkData);
    } else if (type === 'IEND') {
      break;
    }
    offset += 12 + len;
  }

  const totalLen = idatChunks.reduce((s, c) => s + c.length, 0);
  const compressed = new Uint8Array(totalLen);
  let pos = 0;
  for (const chunk of idatChunks) { compressed.set(chunk, pos); pos += chunk.length; }

  // Decompress zlib via DecompressionStream('deflate')
  const ds = new DecompressionStream('deflate');
  const writer = ds.writable.getWriter();
  writer.write(compressed);
  writer.close();

  const reader = ds.readable.getReader();
  const decompChunks = [];
  let totalDecomp = 0;
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    decompChunks.push(value);
    totalDecomp += value.length;
  }
  const decompressed = new Uint8Array(totalDecomp);
  pos = 0;
  for (const chunk of decompChunks) { decompressed.set(chunk, pos); pos += chunk.length; }

  // Reconstruct scanlines with PNG filters
  const stride = width * channels;
  const raw = new Uint8Array(width * height * channels);
  let srcPos = 0;

  for (let y = 0; y < height; y++) {
    const filterType = decompressed[srcPos++];
    const dstOff = y * stride;

    for (let x = 0; x < stride; x++) {
      const cur = decompressed[srcPos++];
      const a = x >= channels ? raw[dstOff + x - channels] : 0;
      const b = y > 0 ? raw[dstOff - stride + x] : 0;
      const c = (x >= channels && y > 0) ? raw[dstOff - stride + x - channels] : 0;
      let val;
      switch (filterType) {
        case 0: val = cur; break;
        case 1: val = (cur + a) & 0xFF; break;
        case 2: val = (cur + b) & 0xFF; break;
        case 3: val = (cur + ((a + b) >> 1)) & 0xFF; break;
        case 4: {
          const p = a + b - c;
          const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
          val = (cur + ((pa <= pb && pa <= pc) ? a : (pb <= pc) ? b : c)) & 0xFF;
          break;
        }
        default: val = cur;
      }
      raw[dstOff + x] = val;
    }
  }

  return raw;
}

// ── TernLSB Decoder ──
function decodeTernLSB(rawBytes) {
  const INSTRUCTIONS = '+-,.<>[]';
  const SAVE_MARKER_LEN = 4;

  let termIdx = -1;
  const codeChars = [];
  for (let i = 0; i < rawBytes.length; i++) {
    const mod = rawBytes[i] % 9;
    if (mod === 8) { termIdx = i; break; }
    codeChars.push(INSTRUCTIONS[mod]);
  }
  const code = codeChars.join('');

  let saveLines = null;
  if (termIdx >= 0) {
    let pos = termIdx + 1;
    if (pos + SAVE_MARKER_LEN <= rawBytes.length) {
      let hasMarker = true;
      for (let k = 0; k < SAVE_MARKER_LEN; k++) {
        if (rawBytes[pos + k] % 9 !== 8) { hasMarker = false; break; }
      }
      if (hasMarker) {
        pos += SAVE_MARKER_LEN;
        const chars = [];
        while (pos + 3 <= rawBytes.length) {
          const d0 = rawBytes[pos] % 9;
          const d1 = rawBytes[pos + 1] % 9;
          const d2 = rawBytes[pos + 2] % 9;
          const v = d0 + d1 * 9 + d2 * 81;
          if (v === 0) break;
          chars.push(String.fromCharCode(v));
          pos += 3;
        }
        if (chars.length > 0) {
          const text = chars.join('');
          saveLines = text.split('\n');
          if (saveLines.length && saveLines[saveLines.length - 1] === '') saveLines.pop();
        }
      }
    }
  }

  return { code, saveLines };
}

// ── Compiled BF (RLE + bracket match) ──
function compileBF(code) {
  const ops = [];
  const len = code.length;
  let i = 0;
  while (i < len) {
    const ch = code[i];
    if (ch === '+' || ch === '-' || ch === '>' || ch === '<') {
      let count = 1;
      while (i + count < len && code[i + count] === ch) count++;
      ops.push({ op: ch, arg: count });
      i += count;
    } else {
      ops.push({ op: ch, arg: 0 });
      i++;
    }
  }
  const stack = [];
  for (let j = 0; j < ops.length; j++) {
    if (ops[j].op === '[') stack.push(j);
    else if (ops[j].op === ']') {
      const open = stack.pop();
      ops[open].arg = j;
      ops[j].arg = open;
    }
  }
  return ops;
}

// ── Async BF Runner ──
class BFRunner {
  constructor(ops, saveLines) {
    this.ops = ops;
    this.tape = new Uint8Array(1000000);
    this.ptr = 0;
    this.pc = 0;
    this.outputBuf = '';
    this.inputQueue = [];
    this.inputResolve = null;
    this.saveLines = saveLines;
    this.saveLineIdx = 0;
    this.usedSaveLines = 0;
    this.steps = 0;
    this.running = false;
    this.finished = false;
  }

  feedInput(line) {
    for (const ch of line) this.inputQueue.push(ch.charCodeAt(0));
    this.inputQueue.push(10);
    if (this.inputResolve) { const r = this.inputResolve; this.inputResolve = null; r(); }
  }

  async getInputChar() {
    // Load next save line only when queue is empty (matches Python ternlsb.py)
    if (this.inputQueue.length === 0 && this.saveLines && this.saveLineIdx < this.saveLines.length) {
      const line = this.saveLines[this.saveLineIdx++];
      this.usedSaveLines++;
      for (const ch of line) this.inputQueue.push(ch.charCodeAt(0));
      this.inputQueue.push(10);
    }
    if (this.inputQueue.length > 0) return this.inputQueue.shift();

    return new Promise(resolve => {
      this.inputResolve = () => resolve(this.inputQueue.shift());
      cmdInput.disabled = false;
      cmdInput.placeholder = 'Enter command…';
      cmdInput.focus();
    });
  }

  async run() {
    this.running = true;
    const ops = this.ops;
    const tape = this.tape;
    const BATCH = 500000;

    while (this.pc < ops.length && this.running) {
      let batchLeft = BATCH;
      while (batchLeft > 0 && this.pc < ops.length) {
        const instr = ops[this.pc];
        switch (instr.op) {
          case '+': tape[this.ptr] = (tape[this.ptr] + instr.arg) & 0xFF; break;
          case '-': tape[this.ptr] = (tape[this.ptr] - instr.arg) & 0xFF; break;
          case '>': this.ptr += instr.arg; break;
          case '<': this.ptr -= instr.arg; break;
          case '.': this.outputBuf += String.fromCharCode(tape[this.ptr]); break;
          case ',':
            if (this.outputBuf) { flushOutput(this.outputBuf); this.outputBuf = ''; }
            updateStatus(this.steps, this.usedSaveLines, this.saveLines ? this.saveLines.length : 0);
            tape[this.ptr] = await this.getInputChar();
            break;
          case '[': if (tape[this.ptr] === 0) this.pc = instr.arg; break;
          case ']': if (tape[this.ptr] !== 0) this.pc = instr.arg; break;
        }
        this.pc++;
        this.steps++;
        batchLeft--;
      }
      if (this.outputBuf) { flushOutput(this.outputBuf); this.outputBuf = ''; }
      updateStatus(this.steps, this.usedSaveLines, this.saveLines ? this.saveLines.length : 0);
      await new Promise(r => setTimeout(r, 0));
    }

    this.finished = true;
    this.running = false;
    if (this.outputBuf) { flushOutput(this.outputBuf); this.outputBuf = ''; }
    updateStatus(this.steps, this.usedSaveLines, this.saveLines ? this.saveLines.length : 0, true);
  }
}

// ── DOM ──
const outputWrap = document.getElementById('output-wrap');
const cmdInput = document.getElementById('cmd');
const loadStatus = document.getElementById('load-status');
const stepCount = document.getElementById('step-count');
const saveInfo = document.getElementById('save-info');

function flushOutput(text) {
  const span = document.createElement('span');
  span.className = 'game-text';
  span.textContent = text;
  outputWrap.appendChild(span);
  outputWrap.scrollTop = outputWrap.scrollHeight;
}

function showInputEcho(text) {
  const span = document.createElement('span');
  span.className = 'input-echo';
  span.textContent = text + '\n';
  outputWrap.appendChild(span);
  outputWrap.scrollTop = outputWrap.scrollHeight;
}

function updateStatus(steps, usedSave, totalSave, done) {
  stepCount.textContent = 'Steps: ' + steps.toLocaleString();
  if (totalSave > 0) saveInfo.textContent = 'Save: ' + usedSave + '/' + totalSave + ' inputs';
  if (done) {
    loadStatus.textContent = 'Program finished.';
    cmdInput.disabled = false;
    cmdInput.placeholder = 'game over';
  }
}

let runner = null;

cmdInput.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && runner && !runner.finished) {
    const val = cmdInput.value;
    cmdInput.value = '';
    showInputEcho(val);
    cmdInput.disabled = true;
    cmdInput.placeholder = 'running…';
    runner.feedInput(val);
  }
});

async function runBFProgram(jsFile, onFinish) {
  loadStatus.textContent = 'Loading PNG data…';
  await new Promise(r => setTimeout(r, 50));

  let png_b64;
  try {
    const resp = await fetch(jsFile);
    const text = await resp.text();
    const m = text.match(/PNG_BASE64\s*=\s*"(.+?)"/s);
    png_b64 = m ? m[1] : text.trim();
  } catch(e) {
    loadStatus.textContent = 'Error loading ' + jsFile + ': ' + e.message;
    return;
  }

  loadStatus.textContent = 'Decoding PNG (manual decoder, no canvas)…';
  await new Promise(r => setTimeout(r, 50));

  let rawBytes;
  try {
    rawBytes = await decodePNGRaw(png_b64);
  } catch(e) {
    loadStatus.textContent = 'PNG decode error: ' + e.message;
    console.error(e);
    return;
  }

  loadStatus.textContent = 'Extracting BF + save…';
  await new Promise(r => setTimeout(r, 50));

  const { code, saveLines } = decodeTernLSB(rawBytes);

  loadStatus.textContent = 'Compiling ' + code.length.toLocaleString() + ' BF instructions…';
  await new Promise(r => setTimeout(r, 50));

  const ops = compileBF(code);

  const saveMsg = saveLines ? saveLines.length + ' save inputs' : 'no save';
  loadStatus.textContent = 'Running (' + ops.length.toLocaleString() + ' ops, ' + saveMsg + ')…';
  saveInfo.textContent = saveLines ? 'Save: 0/' + saveLines.length + ' inputs' : '';
  await new Promise(r => setTimeout(r, 50));

  runner = new BFRunner(ops, saveLines);
  runner.run().then(() => {
    if (typeof onFinish === 'function') onFinish();
  });
}

// Start with 99point_b64.js, then run sophie.js after it finishes
runBFProgram('99point_b64.js', function() {
  runBFProgram('sophie.js');
});