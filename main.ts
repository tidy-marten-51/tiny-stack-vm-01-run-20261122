// Tiny stack VM, make.fun ISA v1 (kit program/generator/subject/ISA.md).
// Runs /input/<id>/program.bin on input.bin, writes /output/<id>/stdout.bin
// and exit.txt. Pure and deterministic: no clock, network or env variation.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const STACK = 256, CALLS = 64, MEM = 256, STEPS = 1_000_000, OUTMAX = 65_536;
const enc = new TextEncoder();

// Opcode -> [immediate bytes, pops, pushes]; absent byte = unknown (trap 5).
const OPS = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x17: [0, 1, 1], 0x1b: [0, 1, 1],
  0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0], 0x33: [2, 0, 0],
  0x34: [0, 0, 0], 0x40: [0, 1, 1], 0x41: [0, 2, 0],
  0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};
for (let o = 0x10; o <= 0x22; o++)
  if (o !== 0x17 && o !== 0x1b && o !== 0x1f) OPS[o] = [0, 2, 1];

/** Run one program; returns [stdout bytes, exit code]. */
function run(prog, input) {
  const n = prog.length;
  const D = new Int32Array(STACK); // data stack
  const C = new Int32Array(CALLS); // return addresses
  const M = new Int32Array(MEM); // memory, all zero
  const out = new Uint8Array(OUTMAX);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (e) => [out.subarray(0, ol), e];
  for (;;) {
    // Trap order: step limit, pc range, unknown opcode, truncated
    // immediate, stack needs, then the op's own traps.
    if (steps === STEPS) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const spec = OPS[op];
    if (spec === undefined) return done(5);
    if (pc + spec[0] >= n) return done(9);
    steps++;
    const nx = pc + 1 + spec[0];
    if (sp < spec[1]) return done(2);
    if (sp - spec[1] + spec[2] > STACK) return done(3);
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8 sign-extends
      case 0x02: // PUSH32, little-endian
        D[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG wraps
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits, exact
          case 0x13: // DIV truncates toward zero; INT_MIN / -1 is INT_MIN
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD takes the sign of a; x % -1 is 0
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned quotient read back signed
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned remainder read back signed
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // shift counts masked to 5 bits
          case 0x1d: r = a >> (b & 31); break; // arithmetic shift
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical shift
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // unsigned compare
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (cp === CALLS) return done(7);
        C[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a >= MEM) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE pops v, then addr
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= MEM) return done(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: { // PRINT as decimal ASCII, no newline
        const t = enc.encode(String(D[sp - 1]));
        if (ol + t.length > OUTMAX) return done(11); // writes none of its bytes
        sp--;
        out.set(t, ol);
        ol += t.length;
        break;
      }
      case 0x51:
        if (ol + 1 > OUTMAX) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break; // IN, -1 past end
      case 0x53: return done(D[--sp] & 255); // EXIT takes the low byte
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const dir = join(IN, id);
  let prog, input;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { prog = Buffer.alloc(0); }
  try { input = readFileSync(join(dir, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const [stdout, exit] = run(prog, input);
  const od = join(OUT, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), stdout);
  writeFileSync(join(od, 'exit.txt'), exit + '\n');
}
