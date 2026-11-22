// Tiny stack VM: runs every /input/<id>/ program (program.bin + input.bin) and
// writes /output/<id>/stdout.bin + exit.txt. Node 22, erasable TypeScript only,
// no dependencies, no clock, no randomness: fully deterministic.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode [pops, pushes, immediate bytes], indexed by opcode byte; -1 = unknown.
const PO = new Int8Array(256).fill(-1);
const PU = new Int8Array(256);
const IM = new Int8Array(256);
for (const s of '0,0,0,0;1,0,1,1;2,0,1,4;3,1,0,0;4,1,2,0;5,2,2,0;6,2,3,0;7,3,3,0;16,2,1,0;17,2,1,0;18,2,1,0;19,2,1,0;20,2,1,0;21,2,1,0;22,2,1,0;23,1,1,0;24,2,1,0;25,2,1,0;26,2,1,0;27,1,1,0;28,2,1,0;29,2,1,0;30,2,1,0;32,2,1,0;33,2,1,0;34,2,1,0;48,0,0,2;49,1,0,2;50,1,0,2;51,0,0,2;52,0,0,0;64,1,1,0;65,2,0,0;80,1,0,0;81,1,0,0;82,0,1,0;83,1,0,0'.split(';')) {
  const v = s.split(',').map(Number);
  PO[v[0]] = v[1];
  PU[v[0]] = v[2];
  IM[v[0]] = v[3];
}

function run(p: Uint8Array, inp: Uint8Array): { o: Uint8Array; c: number } {
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, st = 0, ol = 0, ip = 0;
  const end = (c: number) => ({ o: out.slice(0, ol), c });
  for (;;) {
    if (st === 1e6) return end(10); // step limit
    if (pc < 0 || pc >= p.length) return end(9); // pc outside program
    const op = p[pc];
    if (PO[op] < 0) return end(5); // unknown opcode
    const im = IM[op];
    if (pc + im >= p.length) return end(9); // immediate cut off
    st++;
    const nx = pc + 1 + im;
    if (sp < PO[op]) return end(2); // stack underflow
    if (sp - PO[op] + PU[op] > 256) return end(3); // stack overflow
    pc = nx;
    switch (op) {
      case 0: return end(0); // HALT
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = -D[sp - 1] | 0; break; // NEG
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 16) r = (a + b) | 0; // ADD, wraps
        else if (op === 17) r = (a - b) | 0; // SUB, wraps
        else if (op === 18) r = Math.imul(a, b); // MUL, low 32 bits
        else if (op === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; } // DIV
        else if (op === 20) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; } // MOD
        else if (op === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 22) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 24) r = a & b; // AND
        else if (op === 25) r = a | b; // OR
        else if (op === 26) r = a ^ b; // XOR
        else if (op === 28) r = a << b; // SHL, low 5 bits of b
        else if (op === 29) r = a >> b; // SHR, arithmetic
        else if (op === 30) r = (a >>> b) | 0; // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP, JZ, JNZ
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: { // PRINT
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN
      case 83: return end(D[--sp] & 255); // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  if (!statSync(dir).isDirectory()) continue; // skip stray files in /input
  // One bad instance must never kill the other 39: fall back to empty output, exit 1.
  let r: { o: Uint8Array; c: number } = { o: new Uint8Array(0), c: 1 };
  try {
    r = run(readFileSync(join(dir, 'program.bin')), readFileSync(join(dir, 'input.bin')));
  } catch { /* keep the fallback */ }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}
