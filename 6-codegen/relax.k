// Branch relaxation: which jumps can be the two-byte short form, decided by the emitter.
//
// NASM gives a jump written without a size its near form at `-O1`, the level every build here
// assembles at: six bytes for a conditional jump, five for `jmp`. Its multipass optimizer (`-Ox`)
// would shorten them, but on this compiler's own 2.9 MB of text it took 690 seconds and 2.7 GB
// where `-O1` takes four seconds. The short form reaches 128 bytes either way, and three jumps
// in five are that close to their target.
//
// So the emitter decides. Once a function's text is written, every line gets an upper bound on its
// length (`boundAt`). Every jump starts short, and any jump whose target the bounds put out of
// reach is made near, repeating until nothing changes. Lengthening a jump only lengthens
// distances, so this ends, and every jump still short is in reach by the bounds. The true
// distance is never more than the bounded one, since each line's bound is at least what NASM
// writes for it. A short jump is written `jcc short .L`.
//
// The bounds are exact for nearly every line this compiler writes (on its own text they total
// 0.1% more than NASM's bytes) and short jumps come out within a few of what exact lengths give.
// A line the table does not know (a directive, a macro, an instruction it lacks, which only an
// `asm` block writes) leaves the function's jumps as they are. Should a bound ever fall short,
// NASM refuses the short jump as out of range: an assembly error, never wrong code.
#include <stdlib::{chars, heap, map, mem, option, string, vec}>

pub var gRelaxOff: bool = false;     // `--no-relax`: every jump the near form, as NASM -O1 writes it

// What a line of a function's text is.
local LK_LABEL: long = 1;
local LK_JUMP: long = 2;

// A register: its width in bits, and what it costs as an operand.
local RG_REX: long = 1024;         // r8-r15, xmm8-xmm15, spl/bpl/sil/dil: a REX prefix
local RG_BPLIKE: long = 2048;      // rbp/r13 as a base: a displacement byte even for 0
local RG_SPLIKE: long = 4096;      // rsp/r12 as a base: a SIB byte
local RG_WIDTH: long = 1023;
// Which register it is, plus one, in units of RG_ID: the back end's number for it (`REG_RAX` 0 to
// `REG_R15` 13, `xmm8` to `xmm14` 14 to 20, as regalloc.k counts them; asm.k checks that the two
// agree), and 21 for the `xmm` registers nothing is allocated to. `rsp` and `rbp` have none: no
// value is kept in either, and every function puts both back.
local RG_ID: long = 65536;

// What a function's text may change, as a set of those numbers (`Relax.regs`): every register a
// line names, read or written, and those an instruction writes without naming them. All of them
// is the answer for a function this file cannot read through.
pub RX_ALL: long = 4194303;
local RX_RAX: long = 1;
local RX_RCX: long = 4;
local RX_RDX: long = 8;
local RX_RDI: long = 16;
local RX_RSI: long = 32;
local RX_R11: long = 512;

// A mnemonic's class, and for the ones of one length, the length (`class * 32 + bytes`).
local MC_FIXED: long = 1;          // no operands: ret, cqo, syscall...
local MC_JCC: long = 2;
local MC_JMP: long = 3;
local MC_CALL: long = 4;
local MC_PUSHPOP: long = 5;
local MC_ALU: long = 6;            // add sub and or xor cmp adc sbb: an imm8 when it fits
local MC_SHIFT: long = 7;
local MC_SSE: long = 8;            // a mandatory prefix and a two-byte opcode
local MC_TWOBYTE: long = 9;        // 0F xx: setcc, cmovcc, movzx, movsx, bt...
local MC_MOV: long = 10;
local MC_ONE: long = 11;           // a one-byte opcode and a ModRM: lea, movsxd, neg, idiv...
local MC_IMUL: long = 12;
local MC_TEST: long = 13;
local MC_REP: long = 14;
local MC_LOCK: long = 15;

// Registers and mnemonics are keyed by their bytes packed into a long (`pk`), in open-addressed
// tables of 512 slots built when the compiler is compiled. A lookup is a multiply, a shift and a
// probe or two; a `HashMap` costs a call and a hash per operand, and with one this file made the
// compiler run 17% more instructions compiling itself. The two mnemonics longer than eight bytes
// are looked up by name.
pub struct PackTab { keys: [long; 512], vals: [long; 512] }
local gRelaxRegs: PackTab = relaxRegs();
local gMnemonics: PackTab = mnemonicClasses();
local gLongMnemonics: HashMap<str, long> = longMnemonics();

local tabSlot k:long -> long { return ((k * -7046029254386353131) >> 50) & 511; }
local tabPut inout t:PackTab k:long v:long -> void {
    i: long = tabSlot(k);
    while (t.keys[i] != 0) { i = (i + 1) & 511; }
    t.keys[i] = k;
    t.vals[i] = v;
}
local regFind k:long -> long {
    i: long = tabSlot(k);
    loop {
        x: long = gRelaxRegs.keys[i];
        if (x == k) { return gRelaxRegs.vals[i]; }
        if (x == 0) { return -1; }
        i = (i + 1) & 511;
    }
}
local mnemonicFind k:long -> long {
    i: long = tabSlot(k);
    loop {
        x: long = gMnemonics.keys[i];
        if (x == k) { return gMnemonics.vals[i]; }
        if (x == 0) { return -1; }
        i = (i + 1) & 511;
    }
}

local relaxRegs -> PackTab {
    m: PackTab = PackTab { };
    tabPut(&m, pk("rax"), 64 + RG_ID * 1); tabPut(&m, pk("eax"), 32 + RG_ID * 1); tabPut(&m, pk("ax"), 16 + RG_ID * 1); tabPut(&m, pk("al"), 8 + RG_ID * 1);
    tabPut(&m, pk("ah"), 8 + RG_ID * 1); tabPut(&m, pk("rcx"), 64 + RG_ID * 3); tabPut(&m, pk("ecx"), 32 + RG_ID * 3); tabPut(&m, pk("cx"), 16 + RG_ID * 3);
    tabPut(&m, pk("cl"), 8 + RG_ID * 3); tabPut(&m, pk("ch"), 8 + RG_ID * 3); tabPut(&m, pk("rdx"), 64 + RG_ID * 4); tabPut(&m, pk("edx"), 32 + RG_ID * 4);
    tabPut(&m, pk("dx"), 16 + RG_ID * 4); tabPut(&m, pk("dl"), 8 + RG_ID * 4); tabPut(&m, pk("dh"), 8 + RG_ID * 4); tabPut(&m, pk("rbx"), 64 + RG_ID * 2);
    tabPut(&m, pk("ebx"), 32 + RG_ID * 2); tabPut(&m, pk("bx"), 16 + RG_ID * 2); tabPut(&m, pk("bl"), 8 + RG_ID * 2); tabPut(&m, pk("bh"), 8 + RG_ID * 2);
    tabPut(&m, pk("rsp"), 64 + RG_SPLIKE); tabPut(&m, pk("esp"), 32 + RG_SPLIKE); tabPut(&m, pk("sp"), 16); tabPut(&m, pk("spl"), 8 + RG_REX);
    tabPut(&m, pk("rbp"), 64 + RG_BPLIKE); tabPut(&m, pk("ebp"), 32 + RG_BPLIKE); tabPut(&m, pk("bp"), 16); tabPut(&m, pk("bpl"), 8 + RG_REX);
    tabPut(&m, pk("rsi"), 64 + RG_ID * 6); tabPut(&m, pk("esi"), 32 + RG_ID * 6); tabPut(&m, pk("si"), 16 + RG_ID * 6); tabPut(&m, pk("sil"), 8 + RG_REX + RG_ID * 6);
    tabPut(&m, pk("rdi"), 64 + RG_ID * 5); tabPut(&m, pk("edi"), 32 + RG_ID * 5); tabPut(&m, pk("di"), 16 + RG_ID * 5); tabPut(&m, pk("dil"), 8 + RG_REX + RG_ID * 5);
    tabPut(&m, pk("r8"), 64 + RG_REX + RG_ID * 7); tabPut(&m, pk("r8d"), 32 + RG_REX + RG_ID * 7); tabPut(&m, pk("r8w"), 16 + RG_REX + RG_ID * 7); tabPut(&m, pk("r8b"), 8 + RG_REX + RG_ID * 7);
    tabPut(&m, pk("r9"), 64 + RG_REX + RG_ID * 8); tabPut(&m, pk("r9d"), 32 + RG_REX + RG_ID * 8); tabPut(&m, pk("r9w"), 16 + RG_REX + RG_ID * 8); tabPut(&m, pk("r9b"), 8 + RG_REX + RG_ID * 8);
    tabPut(&m, pk("r10"), 64 + RG_REX + RG_ID * 9); tabPut(&m, pk("r10d"), 32 + RG_REX + RG_ID * 9); tabPut(&m, pk("r10w"), 16 + RG_REX + RG_ID * 9); tabPut(&m, pk("r10b"), 8 + RG_REX + RG_ID * 9);
    tabPut(&m, pk("r11"), 64 + RG_REX + RG_ID * 10); tabPut(&m, pk("r11d"), 32 + RG_REX + RG_ID * 10); tabPut(&m, pk("r11w"), 16 + RG_REX + RG_ID * 10); tabPut(&m, pk("r11b"), 8 + RG_REX + RG_ID * 10);
    tabPut(&m, pk("r12"), 64 + RG_REX + RG_SPLIKE + RG_ID * 11); tabPut(&m, pk("r12d"), 32 + RG_REX + RG_SPLIKE + RG_ID * 11); tabPut(&m, pk("r12w"), 16 + RG_REX + RG_SPLIKE + RG_ID * 11); tabPut(&m, pk("r12b"), 8 + RG_REX + RG_SPLIKE + RG_ID * 11);
    tabPut(&m, pk("r13"), 64 + RG_REX + RG_BPLIKE + RG_ID * 12); tabPut(&m, pk("r13d"), 32 + RG_REX + RG_BPLIKE + RG_ID * 12); tabPut(&m, pk("r13w"), 16 + RG_REX + RG_BPLIKE + RG_ID * 12); tabPut(&m, pk("r13b"), 8 + RG_REX + RG_BPLIKE + RG_ID * 12);
    tabPut(&m, pk("r14"), 64 + RG_REX + RG_ID * 13); tabPut(&m, pk("r14d"), 32 + RG_REX + RG_ID * 13); tabPut(&m, pk("r14w"), 16 + RG_REX + RG_ID * 13); tabPut(&m, pk("r14b"), 8 + RG_REX + RG_ID * 13);
    tabPut(&m, pk("r15"), 64 + RG_REX + RG_ID * 14); tabPut(&m, pk("r15d"), 32 + RG_REX + RG_ID * 14); tabPut(&m, pk("r15w"), 16 + RG_REX + RG_ID * 14); tabPut(&m, pk("r15b"), 8 + RG_REX + RG_ID * 14);
    tabPut(&m, pk("xmm0"), 128 + RG_ID * 22); tabPut(&m, pk("xmm1"), 128 + RG_ID * 22); tabPut(&m, pk("xmm2"), 128 + RG_ID * 22); tabPut(&m, pk("xmm3"), 128 + RG_ID * 22);
    tabPut(&m, pk("xmm4"), 128 + RG_ID * 22); tabPut(&m, pk("xmm5"), 128 + RG_ID * 22); tabPut(&m, pk("xmm6"), 128 + RG_ID * 22); tabPut(&m, pk("xmm7"), 128 + RG_ID * 22);
    tabPut(&m, pk("xmm8"), 128 + RG_REX + RG_ID * 15); tabPut(&m, pk("xmm9"), 128 + RG_REX + RG_ID * 16); tabPut(&m, pk("xmm10"), 128 + RG_REX + RG_ID * 17); tabPut(&m, pk("xmm11"), 128 + RG_REX + RG_ID * 18);
    tabPut(&m, pk("xmm12"), 128 + RG_REX + RG_ID * 19); tabPut(&m, pk("xmm13"), 128 + RG_REX + RG_ID * 20); tabPut(&m, pk("xmm14"), 128 + RG_REX + RG_ID * 21); tabPut(&m, pk("xmm15"), 128 + RG_REX + RG_ID * 22);
    return m;
}

local mnemonicClasses -> PackTab {
    m: PackTab = PackTab { };
    tabPut(&m, pk("ret"), MC_FIXED * 32 + 1); tabPut(&m, pk("cqo"), MC_FIXED * 32 + 2); tabPut(&m, pk("cdq"), MC_FIXED * 32 + 1);
    tabPut(&m, pk("cdqe"), MC_FIXED * 32 + 2); tabPut(&m, pk("syscall"), MC_FIXED * 32 + 2); tabPut(&m, pk("leave"), MC_FIXED * 32 + 1);
    tabPut(&m, pk("nop"), MC_FIXED * 32 + 1); tabPut(&m, pk("ud2"), MC_FIXED * 32 + 2); tabPut(&m, pk("int3"), MC_FIXED * 32 + 1);
    tabPut(&m, pk("hlt"), MC_FIXED * 32 + 1); tabPut(&m, pk("pause"), MC_FIXED * 32 + 2); tabPut(&m, pk("jo"), MC_JCC * 32);
    tabPut(&m, pk("jno"), MC_JCC * 32); tabPut(&m, pk("jb"), MC_JCC * 32); tabPut(&m, pk("jnae"), MC_JCC * 32);
    tabPut(&m, pk("jc"), MC_JCC * 32); tabPut(&m, pk("jnb"), MC_JCC * 32); tabPut(&m, pk("jae"), MC_JCC * 32);
    tabPut(&m, pk("jnc"), MC_JCC * 32); tabPut(&m, pk("jz"), MC_JCC * 32); tabPut(&m, pk("je"), MC_JCC * 32); tabPut(&m, pk("jnz"), MC_JCC * 32);
    tabPut(&m, pk("jne"), MC_JCC * 32); tabPut(&m, pk("jbe"), MC_JCC * 32); tabPut(&m, pk("jna"), MC_JCC * 32);
    tabPut(&m, pk("jnbe"), MC_JCC * 32); tabPut(&m, pk("ja"), MC_JCC * 32); tabPut(&m, pk("js"), MC_JCC * 32);
    tabPut(&m, pk("jns"), MC_JCC * 32); tabPut(&m, pk("jp"), MC_JCC * 32); tabPut(&m, pk("jpe"), MC_JCC * 32);
    tabPut(&m, pk("jnp"), MC_JCC * 32); tabPut(&m, pk("jpo"), MC_JCC * 32); tabPut(&m, pk("jl"), MC_JCC * 32);
    tabPut(&m, pk("jnge"), MC_JCC * 32); tabPut(&m, pk("jnl"), MC_JCC * 32); tabPut(&m, pk("jge"), MC_JCC * 32);
    tabPut(&m, pk("jle"), MC_JCC * 32); tabPut(&m, pk("jng"), MC_JCC * 32); tabPut(&m, pk("jnle"), MC_JCC * 32);
    tabPut(&m, pk("jg"), MC_JCC * 32); tabPut(&m, pk("seto"), MC_TWOBYTE * 32); tabPut(&m, pk("setno"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setb"), MC_TWOBYTE * 32); tabPut(&m, pk("setnae"), MC_TWOBYTE * 32); tabPut(&m, pk("setc"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setnb"), MC_TWOBYTE * 32); tabPut(&m, pk("setae"), MC_TWOBYTE * 32); tabPut(&m, pk("setnc"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setz"), MC_TWOBYTE * 32); tabPut(&m, pk("sete"), MC_TWOBYTE * 32); tabPut(&m, pk("setnz"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setne"), MC_TWOBYTE * 32); tabPut(&m, pk("setbe"), MC_TWOBYTE * 32); tabPut(&m, pk("setna"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setnbe"), MC_TWOBYTE * 32); tabPut(&m, pk("seta"), MC_TWOBYTE * 32); tabPut(&m, pk("sets"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setns"), MC_TWOBYTE * 32); tabPut(&m, pk("setp"), MC_TWOBYTE * 32); tabPut(&m, pk("setpe"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setnp"), MC_TWOBYTE * 32); tabPut(&m, pk("setpo"), MC_TWOBYTE * 32); tabPut(&m, pk("setl"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setnge"), MC_TWOBYTE * 32); tabPut(&m, pk("setnl"), MC_TWOBYTE * 32); tabPut(&m, pk("setge"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setle"), MC_TWOBYTE * 32); tabPut(&m, pk("setng"), MC_TWOBYTE * 32); tabPut(&m, pk("setnle"), MC_TWOBYTE * 32);
    tabPut(&m, pk("setg"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovo"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovno"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovb"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovnae"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovc"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovnb"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovae"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovnc"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovz"), MC_TWOBYTE * 32); tabPut(&m, pk("cmove"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovnz"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovne"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovbe"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovna"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovnbe"), MC_TWOBYTE * 32); tabPut(&m, pk("cmova"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovs"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovns"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovp"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovpe"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovnp"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovpo"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovl"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovnge"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovnl"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovge"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovle"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovng"), MC_TWOBYTE * 32); tabPut(&m, pk("cmovnle"), MC_TWOBYTE * 32);
    tabPut(&m, pk("cmovg"), MC_TWOBYTE * 32); tabPut(&m, pk("jmp"), MC_JMP * 32); tabPut(&m, pk("call"), MC_CALL * 32);
    tabPut(&m, pk("push"), MC_PUSHPOP * 32); tabPut(&m, pk("pop"), MC_PUSHPOP * 32); tabPut(&m, pk("add"), MC_ALU * 32);
    tabPut(&m, pk("sub"), MC_ALU * 32); tabPut(&m, pk("and"), MC_ALU * 32); tabPut(&m, pk("or"), MC_ALU * 32);
    tabPut(&m, pk("xor"), MC_ALU * 32); tabPut(&m, pk("cmp"), MC_ALU * 32); tabPut(&m, pk("adc"), MC_ALU * 32);
    tabPut(&m, pk("sbb"), MC_ALU * 32); tabPut(&m, pk("shl"), MC_SHIFT * 32); tabPut(&m, pk("shr"), MC_SHIFT * 32);
    tabPut(&m, pk("sar"), MC_SHIFT * 32); tabPut(&m, pk("sal"), MC_SHIFT * 32); tabPut(&m, pk("rol"), MC_SHIFT * 32);
    tabPut(&m, pk("ror"), MC_SHIFT * 32); tabPut(&m, pk("movsd"), MC_SSE * 32); tabPut(&m, pk("movss"), MC_SSE * 32);
    tabPut(&m, pk("addsd"), MC_SSE * 32); tabPut(&m, pk("subsd"), MC_SSE * 32); tabPut(&m, pk("mulsd"), MC_SSE * 32);
    tabPut(&m, pk("divsd"), MC_SSE * 32); tabPut(&m, pk("addss"), MC_SSE * 32); tabPut(&m, pk("subss"), MC_SSE * 32);
    tabPut(&m, pk("mulss"), MC_SSE * 32); tabPut(&m, pk("divss"), MC_SSE * 32); tabPut(&m, pk("cvtsi2sd"), MC_SSE * 32);
    tabPut(&m, pk("cvtsi2ss"), MC_SSE * 32); 
    tabPut(&m, pk("cvtsd2ss"), MC_SSE * 32); tabPut(&m, pk("cvtss2sd"), MC_SSE * 32); tabPut(&m, pk("sqrtsd"), MC_SSE * 32);
    tabPut(&m, pk("sqrtss"), MC_SSE * 32); tabPut(&m, pk("ucomisd"), MC_SSE * 32); tabPut(&m, pk("ucomiss"), MC_SSE * 32);
    tabPut(&m, pk("comisd"), MC_SSE * 32); tabPut(&m, pk("comiss"), MC_SSE * 32); tabPut(&m, pk("movq"), MC_SSE * 32);
    tabPut(&m, pk("movd"), MC_SSE * 32); tabPut(&m, pk("xorpd"), MC_SSE * 32); tabPut(&m, pk("xorps"), MC_SSE * 32);
    tabPut(&m, pk("andpd"), MC_SSE * 32); tabPut(&m, pk("andps"), MC_SSE * 32); tabPut(&m, pk("pxor"), MC_SSE * 32);
    tabPut(&m, pk("movapd"), MC_SSE * 32); tabPut(&m, pk("movaps"), MC_SSE * 32); tabPut(&m, pk("movzx"), MC_TWOBYTE * 32);
    tabPut(&m, pk("movsx"), MC_TWOBYTE * 32); tabPut(&m, pk("bt"), MC_TWOBYTE * 32); tabPut(&m, pk("bsr"), MC_TWOBYTE * 32);
    tabPut(&m, pk("bsf"), MC_TWOBYTE * 32); tabPut(&m, pk("xadd"), MC_TWOBYTE * 32); tabPut(&m, pk("cmpxchg"), MC_TWOBYTE * 32);
    tabPut(&m, pk("mov"), MC_MOV * 32); tabPut(&m, pk("lea"), MC_ONE * 32); tabPut(&m, pk("movsxd"), MC_ONE * 32);
    tabPut(&m, pk("idiv"), MC_ONE * 32); tabPut(&m, pk("div"), MC_ONE * 32); tabPut(&m, pk("mul"), MC_ONE * 32);
    tabPut(&m, pk("neg"), MC_ONE * 32); tabPut(&m, pk("not"), MC_ONE * 32); tabPut(&m, pk("inc"), MC_ONE * 32);
    tabPut(&m, pk("dec"), MC_ONE * 32); tabPut(&m, pk("xchg"), MC_ONE * 32); tabPut(&m, pk("imul"), MC_IMUL * 32);
    tabPut(&m, pk("test"), MC_TEST * 32); tabPut(&m, pk("rep"), MC_REP * 32); tabPut(&m, pk("lock"), MC_LOCK * 32);
    return m;
}

local longMnemonics -> HashMap<str, long> {
    m: HashMap<str, long>;
    m.put("cvttsd2si", MC_SSE * 32); m.put("cvttss2si", MC_SSE * 32);
    return m;
}

// Up to eight bytes of `b` from `i` as one long, the first in the low byte. This is how a
// mnemonic, a register or a keyword is looked up without hashing a string. Every name of at most
// eight bytes, none of them zero, gets a key of its own.
local packAt b:[u8] i:long n:long -> long {
    k: long = 0;
    for j in 0..n { k = k | ((b[i + j] as long) << (8 * j)); }
    return k;
}
local pk s:str -> long { return packAt(s as [u8], 0, s.len); }

local K_ALIGN: long = pk("align");
local K_MOVQ: long = pk("movq");
local K_MOVSQ: long = pk("movsq");
local K_STOSQ: long = pk("stosq");
local K_MOVSB: long = pk("movsb");
local K_STOSB: long = pk("stosb");
local K_BYTE: long = pk("byte");
local K_WORD: long = pk("word");
local K_DWORD: long = pk("dword");
local K_QWORD: long = pk("qword");
local K_STRICT: long = pk("strict");

// The registers an instruction of the table writes without naming them (`implicitRegs`): every
// one of its mnemonics is either here or writes only what its operands name. `rep` is read with
// whichever string instruction follows it, and each of those moves `rdi` and counts in `rcx`;
// `movs` also moves `rsi`. `leave`, `push`, `pop`, `call` and `ret` move only `rsp` and `rbp`.
local K_SYSCALL: long = pk("syscall");
local K_CQO: long = pk("cqo");
local K_CDQ: long = pk("cdq");
local K_CDQE: long = pk("cdqe");
local K_DIV: long = pk("div");
local K_IDIV: long = pk("idiv");
local K_MUL: long = pk("mul");
local K_IMUL: long = pk("imul");
local K_CMPXCHG: long = pk("cmpxchg");
local implicitRegs k:long operands:long -> long {
    if (k == K_SYSCALL) { return RX_RAX | RX_RCX | RX_R11; }      // the kernel's rcx and r11
    if (k == K_CQO || k == K_CDQ) { return RX_RDX; }
    if (k == K_CDQE || k == K_CMPXCHG) { return RX_RAX; }
    if (k == K_DIV || k == K_IDIV || k == K_MUL) { return RX_RAX | RX_RDX; }
    if (k == K_IMUL && operands == 1) { return RX_RAX | RX_RDX; }
    return 0;
}

// What each byte is to the scans here, as one lookup rather than a chain of comparisons: a
// letter, a digit, or another character a name may hold (`_ . $ @ ?`). The table is built when
// the compiler is compiled, as the register and mnemonic tables are.
local CH_ALPHA: long = 1;
local CH_DIGIT: long = 2;
local CH_NAME: long = 4;
pub struct CharTab { c: [long; 256] }
local gChars: CharTab = charTab();
local charTab -> CharTab {
    t: CharTab = CharTab { };
    for c in 0..256 {
        k: long = 0;
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) { k = CH_ALPHA; }
        if (c >= '0' && c <= '9') { k = CH_DIGIT; }
        if (c == '_' || c == '.' || c == '$' || c == '@' || c == '?') { k = CH_NAME; }
        t.c[c] = k;
    }
    return t;
}
local identChar c:long -> bool { return (gChars.c[c & 255] & (CH_ALPHA | CH_DIGIT | CH_NAME)) != 0; }
local alnumC c:long -> bool { return (gChars.c[c & 255] & (CH_ALPHA | CH_DIGIT)) != 0; }
local alphaC c:long -> bool { return (gChars.c[c & 255] & CH_ALPHA) != 0; }
local digitC c:long -> bool { return (gChars.c[c & 255] & CH_DIGIT) != 0; }
// Bytes [i, j) are a name: identifier characters, not starting with a digit.
local identAt b:[u8] i:long j:long -> bool {
    if (i >= j || digitC(b[i] as long)) { return false; }
    for k in i..j { if (!identChar(b[k] as long)) { return false; } }
    return true;
}

// The register spelled by bytes [i, j), as `relaxRegs` packs it, or -1.
local regAt b:[u8] i:long j:long -> long {
    n: long = j - i;
    if (n < 2 || n > 5) { return -1; }
    return regFind(packAt(b, i, n));
}

// The set (RX_*) a register's name stands for, or 0: what lets asm.k check that RG_ID counts the
// registers as regalloc.k numbers them.
pub relaxRegSet name:str -> long {
    r: long = regAt(name as [u8], 0, name.len);
    if (r < 0 || r / RG_ID == 0) { return 0; }
    return 1 << (r / RG_ID - 1);
}

// The class of the mnemonic spelled by bytes [i, j), as `mnemonicClasses` packs it, or -1.
local classAt b:[u8] i:long j:long -> long {
    n: long = j - i;
    if (n < 2) { return -1; }
    if (n <= 8) {
        return mnemonicFind(packAt(b, i, n));
    }
    hit2: Option<long> = gLongMnemonics.find(b[i..j] as str);
    match hit2 { Some(c) { return c; } None { } }
    return -1;
}

local skipSpaces b:[u8] i0:long j:long -> long {
    i: long = i0;
    while (i < j && (b[i] == ' ' || b[i] == '\t')) { i = i + 1; }
    return i;
}
local trimEnd b:[u8] i:long j0:long -> long {
    j: long = j0;
    while (j > i && (b[j - 1] == ' ' || b[j - 1] == '\t')) { j = j - 1; }
    return j;
}

// One function's text: its labels and jumps in order, each with the bytes the instructions before
// it take (since the last one, by the bounds), and the jumps' decisions.
pub struct Relax {
    eKind: Vec<long>,                   // LK_LABEL or LK_JUMP
    eGap: Vec<long>,                    // bytes of instructions between the last entry and this one
    eLen: Vec<long>,                    // a jump's near length
    eMn: Vec<long>, eEnd: Vec<long>,    // a jump: where its mnemonic ends, and its line (trimmed)
    eTarget: Vec<long>,                 // a jump: its label's entry, or -1
    eShort: Vec<bool>,
    eAt: Vec<long>,                     // where each entry starts, by the bounds
    labels: HashMap<str, long>,         // a label of this function -> its entry
    eLabel: Vec<long>,                  // a label: where its name starts
    // The function being read: where its text starts, its jumps so far, the bytes since the last
    // entry, whether a line has been seen yet, and whether it is to be left as written.
    from: long, jumps: long, gap: long, first: bool, dead: bool,
    copy: String,
    cache: long, cacheUsed: long,       // `cachedBound`: CACHE_SLOTS (hash, bound) pairs, malloc'd once
    // What the operands of the line being bounded come to: how many there are, the first
    // register's width, whether there is a 64-bit general register or `qword` among them, a 16-bit
    // one or `word`, a register that needs REX, a memory operand (and its SIB, displacement and
    // segment bytes), an immediate (and whether it is a number, and its value), and the width a
    // size keyword gives. `num` is the last number read.
    shN: long, shRegW: long, shW64: bool, shW16: bool, shRex: bool, shMem: bool, shMemLen: long,
    shImm: bool, shImmNum: bool, shImmVal: long, shKw: long, num: long,
    nShort: long, nNear: long, nKept: long,
    // The registers the function's text may change (RX_*): what its lines name, what they write
    // without naming it, and what the functions it calls may change, `calls` saying that for each
    // label the emitter has finished (a label it does not hold is RX_ALL). `shRegs` is the line
    // being bounded's share, `lineRegs` the last line's. With `wantRegs` off nobody asks, and
    // `blind` stops the reading once the answer can only be RX_ALL. Lines read `aside` are on a
    // way out that never returns (the emitter's cold text ending in such a call): they are bounded
    // like any other, but what they change is not the function's.
    shRegs: long, lineRegs: long, regs: long, blind: bool, wantRegs: bool, aside: bool,
    calls: HashMap<str, long>
}

local CACHE_SLOTS: long = 65536;

methods Relax for Default {
    new -> Relax {
        return Relax { eKind: vec![], eGap: vec![], eLen: vec![], eMn: vec![], eEnd: vec![], eTarget: vec![],
                       eShort: vec![], eAt: vec![], labels: map![], eLabel: vec![], from: 0, jumps: 0, gap: 0, first: true, dead: true,
                       copy: String.new(), cache: 0, cacheUsed: 0,
                       shN: 0, shRegW: 0, shW64: false, shW16: false, shRex: false, shMem: false, shMemLen: 0,
                       shImm: false, shImmNum: false, shImmVal: 0, shKw: 0, num: 0,
                       nShort: 0, nNear: 0, nKept: 0,
                       shRegs: 0, lineRegs: 0, regs: RX_ALL, blind: true, wantRegs: false, aside: false, calls: map![] };
    }
}

methods Relax {
    // A decimal or `0x` number in bytes [i, j), with an optional sign, into `num`; false for
    // anything else. A value of more than eighteen digits may not fit in a `long`, and a bound
    // only needs to know that it is large, so it reads as 2^62 with its sign kept.
    numberAt &self b:[u8] i0:long j:long -> bool {
        i: long = i0;
        neg: bool = false;
        if (i < j && b[i] == '-') { neg = true; i = i + 1; }
        else if (i < j && b[i] == '+') { i = i + 1; }
        if (i >= j || !digitC(b[i] as long)) { return false; }
        x: long = 0;
        if (b[i] == '0' && i + 1 < j && (b[i + 1] == 'x' || b[i + 1] == 'X')) {
            i = i + 2;
            if (i >= j || j - i > 15) { return false; }
            while (i < j) {
                d: long = hexVal(b[i] as long);
                if (d < 0) { return false; }
                x = x * 16 + d;
                i = i + 1;
            }
        } else {
            if (j - i > 20) { return false; }
            for k in i..j { if (!digitC(b[k] as long)) { return false; } }
            if (j - i > 18) { x = 4611686018427387904; }
            else { for k in i..j { x = x * 10 + (b[k] - '0') as long; } }
        }
        if (neg) { self.num = 0 - x; } else { self.num = x; }
        return true;
    }

    // A register an operand names, into the line's set.
    noteReg &self r:long -> void {
        id: long = r / RG_ID - 1;
        if (id >= 0) { self.shRegs = self.shRegs | (1 << id); }
    }

    // The inside of `[...]` in bytes [i, j): a base, an index (`r*8`), numbers and symbols, `rel`,
    // and an `fs:` or `gs:` prefix.
    memoryAt &self b:[u8] i0:long j0:long -> bool {
        i: long = skipSpaces(b, i0, j0);
        j: long = trimEnd(b, i, j0);
        seg: long = 0;
        if (j - i >= 3 && (b[i] == 'f' || b[i] == 'g') && b[i + 1] == 's' && b[i + 2] == ':') {
            seg = 1;
            i = skipSpaces(b, i + 3, j);
        }
        self.shMem = true;
        if (j - i >= 4 && b[i] == 'r' && b[i + 1] == 'e' && b[i + 2] == 'l' && b[i + 3] == ' ') {
            // `rel sym`, `rel sym + 8`: a 32-bit displacement and nothing else.
            for k in i + 4..j {
                c: long = b[k] as long;
                if (!identChar(c) && c != ' ' && c != '+' && c != '-') { return false; }
            }
            self.shMemLen = seg + 4;
            return true;
        }
        base: long = -1;
        index: long = -1;
        disp: long = 0;
        sym: bool = false;
        sign: long = 1;
        while (i < j) {
            c: u8 = b[i];
            if (c == ' ') { i = i + 1; continue; }
            if (c == '+') { sign = 1; i = i + 1; continue; }
            if (c == '-') { sign = -1; i = i + 1; continue; }
            k: long = i;
            star: long = -1;
            while (k < j && b[k] != ' ' && b[k] != '+' && b[k] != '-') {
                if (b[k] == '*') { star = k; }
                k = k + 1;
            }
            if (star >= 0) {
                r: long = regAt(b, i, star);
                if (r < 0 || sign < 0 || index >= 0) { return false; }
                index = r;
                self.noteReg(r);
            } else {
                r: long = regAt(b, i, k);
                if (r >= 0) {
                    self.noteReg(r);
                    if (sign < 0) { return false; }
                    if (base < 0) { base = r; }
                    else if (index < 0) { index = r; }
                    else { return false; }
                } else if (self.numberAt(b, i, k)) { disp = disp + sign * self.num; }
                else if (identAt(b, i, k)) { sym = true; }
                else { return false; }
            }
            i = k;
        }
        if (base >= 0 && (base & RG_REX) != 0) { self.shRex = true; }
        if (index >= 0 && (index & RG_REX) != 0) { self.shRex = true; }
        if (base < 0) { self.shMemLen = seg + 1 + 4; return true; }   // [disp32]: a SIB byte in 64-bit mode
        sib: long = 0;
        if (index >= 0 || (base & RG_SPLIKE) != 0) { sib = 1; }
        d: long = 4;
        if (!sym) {
            if (disp == 0 && (base & RG_BPLIKE) == 0) { d = 0; }
            else if (disp >= -128 && disp <= 127) { d = 1; }
        }
        self.shMemLen = seg + sib + d;
        return true;
    }

    // One operand, bytes [i, j): any size keywords, then a memory operand, a register, a number or
    // a symbol.
    operandAt &self b:[u8] i0:long j0:long -> bool {
        i: long = skipSpaces(b, i0, j0);
        j: long = trimEnd(b, i, j0);
        going: bool = true;
        while (going) {
            going = false;
            e: long = i;
            while (e < j && alphaC(b[e] as long)) { e = e + 1; }
            if (e < j && b[e] == ' ' && e - i >= 4 && e - i <= 6) {
                k: long = packAt(b, i, e - i);
                w: long = 0;
                if (k == K_BYTE) { w = 8; } else if (k == K_WORD) { w = 16; } else if (k == K_DWORD) { w = 32; }
                else if (k == K_QWORD) { w = 64; } else if (k == K_STRICT) { w = -1; }
                if (w != 0) {
                    if (w > 0) { self.shKw = w; }
                    i = skipSpaces(b, e, j);
                    going = true;
                }
            }
        }
        if (i >= j) { return false; }
        if (b[i] == '[') {
            if (b[j - 1] != ']' || self.shMem) { return false; }
            return self.memoryAt(b, i + 1, j - 1);
        }
        r: long = regAt(b, i, j);
        if (r >= 0) {
            self.noteReg(r);
            w: long = r & RG_WIDTH;
            if (self.shRegW == 0) { self.shRegW = w; }
            if (w == 64) { self.shW64 = true; }
            if (w == 16) { self.shW16 = true; }
            if ((r & RG_REX) != 0) { self.shRex = true; }
            return true;
        }
        if (self.shImm) { return false; }
        if (self.numberAt(b, i, j)) { self.shImm = true; self.shImmNum = true; self.shImmVal = self.num; return true; }
        if (identAt(b, i, j)) { self.shImm = true; return true; }
        return false;
    }

    // The operands in bytes [i, j), separated by commas outside brackets.
    operandsAt &self b:[u8] i0:long j:long -> bool {
        self.shN = 0; self.shRegW = 0; self.shW64 = false; self.shW16 = false; self.shRex = false;
        self.shMem = false; self.shMemLen = 0; self.shImm = false; self.shImmNum = false; self.shImmVal = 0; self.shKw = 0;
        i: long = skipSpaces(b, i0, j);
        while (i < j) {
            k: long = i;
            depth: long = 0;
            while (k < j) {
                c: u8 = b[k];
                if (c == '[') { depth = depth + 1; }
                else if (c == ']') { depth = depth - 1; }
                else if (c == ',' && depth == 0) { break; }
                k = k + 1;
            }
            if (!self.operandAt(b, i, k)) { return false; }
            self.shN = self.shN + 1;
            if (self.shN > 3) { return false; }
            i = k + 1;
        }
        return true;
    }

    // An upper bound on the bytes NASM at `-O1` writes for bytes [i, j) of the text (one line,
    // trimmed, its comment gone), or -1 for a line this does not know to be bounded: a directive,
    // a macro, an instruction outside the table. A jump to a label is bounded by its near form.
    boundAt &self b:[u8] i:long j:long -> long {
        self.shRegs = 0;
        if (i >= j) { return 0; }
        m: long = i;
        while (m < j && alnumC(b[m] as long)) { m = m + 1; }
        if (m == i || (m < j && b[m] != ' ')) { return -1; }
        if (m - i == 5 && packAt(b, i, 5) == K_ALIGN) {
            a: long = skipSpaces(b, m, j);
            if (!self.numberAt(b, a, j) || self.num < 1 || self.num > 4096) { return -1; }
            return self.num - 1;
        }
        c: long = classAt(b, i, m);
        if (c < 0) { return -1; }
        cls: long = c / 32;
        pre: long = 0;
        mnKey: long = 0;
        if (m - i <= 8) { mnKey = packAt(b, i, m - i); }
        if (cls == MC_REP) {
            a: long = skipSpaces(b, m, j);
            if (j - a != 5) { return -1; }
            k: long = packAt(b, a, 5);
            self.shRegs = RX_RDI | RX_RSI | RX_RCX;
            if (k == K_MOVSQ || k == K_STOSQ) { return 3; }
            if (k == K_MOVSB || k == K_STOSB) { return 2; }
            return -1;
        }
        if (cls == MC_LOCK) {
            a: long = skipSpaces(b, m, j);
            m = a;
            while (m < j && alnumC(b[m] as long)) { m = m + 1; }
            if (m == a || (m < j && b[m] != ' ')) { return -1; }
            c = classAt(b, a, m);
            if (c < 0) { return -1; }
            cls = c / 32;
            mnKey = 0;
            if (m - a <= 8) { mnKey = packAt(b, a, m - a); }
            if (cls != MC_ALU && cls != MC_TWOBYTE && cls != MC_ONE) { return -1; }
            pre = 1;
        }
        if (cls == MC_FIXED) {
            if (skipSpaces(b, m, j) != j) { return -1; }
            self.shRegs = implicitRegs(mnKey, 0);
            return c % 32;
        }
        if (!self.operandsAt(b, m, j)) { return -1; }
        self.shRegs = self.shRegs | implicitRegs(mnKey, self.shN);
        if (cls == MC_JCC || cls == MC_JMP || cls == MC_CALL) {
            if (self.shN != 1) { return -1; }
            if (self.shImm) { if (cls == MC_JCC) { return 6; } return 5; }
            if (cls == MC_JCC) { return -1; }
            rx: long = 0;
            if (self.shRex) { rx = 1; }
            if (self.shMem) { return rx + 2 + self.shMemLen; }
            return rx + 2;
        }
        if (cls == MC_PUSHPOP && self.shN == 1 && !self.shMem) {
            if (self.shImm) {
                if (self.shImmNum && self.shImmVal >= -128 && self.shImmVal <= 127) { return 2; }
                return 5;
            }
            if (self.shRex) { return 2; }
            return 1;
        }
        if (self.shN == 0) { return -1; }
        w64: bool = self.shW64 || self.shKw == 64 || mnKey == K_MOVQ;
        if (self.shW16 || self.shKw == 16) { pre = pre + 1; }
        if (cls == MC_SSE) { pre = pre + 1; }
        rex: long = 0;
        if (w64 || self.shRex) { rex = 1; }
        opc: long = 1;
        if (cls == MC_SSE || cls == MC_TWOBYTE || (cls == MC_IMUL && self.shN == 2)) { opc = 2; }
        modrm: long = 1;
        il: long = 0;
        if (self.shImm) {
            small: bool = self.shImmNum && self.shImmVal >= -128 && self.shImmVal <= 127;
            if (cls == MC_MOV && !self.shMem) {
                // `mov r, imm` is B8+r and the immediate: all eight bytes of it for a 64-bit
                // register at -O1, unless `dword` asks for the sign-extended form (C7, a ModRM,
                // four bytes).
                if (self.shKw == 32 && w64) { il = 4; }
                else if (w64) { modrm = 0; il = 8; }
                else { modrm = 0; il = self.shRegW / 8; }
            } else if (cls == MC_MOV) {
                il = 4;
                if (self.shKw == 8) { il = 1; }
                if (self.shKw == 16) { il = 2; }
            } else if (cls == MC_ALU || cls == MC_IMUL || cls == MC_PUSHPOP) {
                il = 4;
                if (small || self.shRegW == 8 || self.shKw == 8) { il = 1; }
            } else if (cls == MC_SHIFT) {
                il = 1;
                if (self.shImmNum && self.shImmVal == 1) { il = 0; }
            } else if (cls == MC_TEST) {
                il = 4;
                if (self.shRegW == 8 || self.shKw == 8) { il = 1; }
            } else { il = 4; }
        }
        return pre + rex + opc + modrm + self.shMemLen + il;
    }

    // The bound of bytes [s, t) (a trimmed instruction line), and the registers it may change
    // (`lineRegs`), from the cache when that line was seen before. This compiler's text is 570,000
    // lines of which 40,000 differ, and a thousand distinct lines make up seven in ten of them. The
    // key is a 64-bit hash of the bytes and their length; beside the bound and the registers, the
    // entry holds 29 bits mixed from the line's first and last eight bytes (a line shorter than
    // that whole, and its length), which a line must match as well. Two lines taken for one would
    // hand one the other's registers, which could be wrong code rather than a short jump NASM
    // refuses: they would have to agree in all 64 bits of the hash and in those 29.
    cachedBound &self b:[u8] s:long t:long -> long {
        // FNV-1a over the line, eight bytes at a time (an unaligned load inside the line), then the
        // tail as the eight bytes that end the line (overlapping what was read, the same for the
        // same line), or a byte at a time for a line shorter than eight; then the length, and a last
        // mix so every bit of the key depends on all.
        h: long = -3750763034362895579;           // FNV-1a's offset basis
        k: long = s;
        w0: long = 0;
        wl: long = t - s;
        unsafe {
            at: long = b.ptr as long;
            if (t - s >= 8) {
                w0 = ((at + s) as *long)[0];
                wl = ((at + t - 8) as *long)[0];
            }
            while (k + 8 <= t) {
                h = (h ^ ((at + k) as *long)[0]) * 1099511628211;
                k = k + 8;
            }
            if (k < t && t - s >= 8) {
                h = (h ^ wl) * 1099511628211;
                k = t;
            }
        }
        if (k < t) { w0 = packAt(b, k, t - k); }
        while (k < t) { h = (h ^ (b[k] as long)) * 1099511628211; k = k + 1; }
        h = (h ^ (t - s)) * 1099511628211;
        h = (h ^ ((h >> 29) & 34359738367)) * -7046029254386353131;
        if (h == 0) { h = 1; }
        chk: long = (((w0 * -4417276706812531889) ^ (wl * -7046029254386353131)) >> 35) & 536870911;
        slot: long = ((h * -7046029254386353131) >> 40) & (CACHE_SLOTS - 1);
        unsafe {
            p: *long = self.cache as *long;
            loop {
                x: long = p[2 * slot];
                if (x == h) {
                    v: long = p[2 * slot + 1];
                    if (((v >> 35) & 536870911) == chk) {
                        self.lineRegs = (v >> 13) & RX_ALL;
                        return (v & 8191) - 1;
                    }
                }
                if (x == 0) { break; }
                slot = (slot + 1) & (CACHE_SLOTS - 1);
            }
            bd: long = self.boundAt(b, s, t);
            self.lineRegs = self.shRegs;
            if (self.cacheUsed < CACHE_SLOTS / 2 && bd < 8191) {
                p[2 * slot] = h;
                p[2 * slot + 1] = (chk << 35) | (self.shRegs << 13) | (bd + 1);
                self.cacheUsed = self.cacheUsed + 1;
            }
            return bd;
        }
    }

    // A function's text begins at `from` in the output, with its own label as the first line. The
    // emitter then passes on each line as it writes it (`line`, or `text` for lines it did not
    // compose), and `finish` sizes the jumps once the function is whole. Only labels and jumps are
    // kept, each with the bytes of the instructions between it and the previous one, so nothing is
    // read twice. A function is left as written when a line is not one `boundAt` knows, holds a
    // quote, or is a second label that is not local (it would open a scope of its own, and the
    // local names after it would belong to that). The same lines say which registers it may
    // change (`regs`), and a function left as written may change any.
    //
    // `--no-relax` leaves every jump near (`dead` from the start) but still reads the lines for
    // their registers, unless nobody asked for them (`wantRegs`).
    begin &self from:long -> void {
        self.eKind.clear(); self.eGap.clear(); self.eLen.clear(); self.eMn.clear(); self.eEnd.clear();
        self.eTarget.clear(); self.eShort.clear(); self.eAt.clear(); self.eLabel.clear();
        self.from = from;
        self.jumps = 0;
        self.gap = 0;
        self.first = true;
        self.dead = gRelaxOff;
        self.blind = !self.wantRegs;
        self.regs = 0;
        if (self.blind) { self.regs = RX_ALL; }
        // The bound cache, made once, here rather than on the path every line takes.
        if (self.cache == 0 && !(self.dead && self.blind)) {
            unsafe {
                self.cache = malloc(CACHE_SLOTS * 16);
                memset(self.cache, 0, CACHE_SLOTS * 16);
            }
        }
    }

    // One line the emitter wrote, bytes [s, t) of `out`: no comment, quote, newline or surrounding
    // blanks in it, so it is classified as it stands.
    line &self inout out:String s:long t:long -> void {
        if ((self.dead && self.blind) || t <= s) { return; }
        b: [u8] = "" as [u8];
        unsafe { b = out.view() as [u8]; }
        self.classify(b, s, t);
    }

    // Text that may hold anything (an `asm` block's line, the cold paths), read line by line. A
    // comment is dropped, and a quote leaves the function as written.
    text &self inout out:String from:long to:long -> void {
        if (self.dead && self.blind) { return; }
        b: [u8] = "" as [u8];
        unsafe { b = out.view() as [u8]; }
        n: long = to;
        i: long = from;
        while (i < n && !(self.dead && self.blind)) {
            e: long = i;
            t: long = -1;
            while (e < n) {
                c: u8 = b[e];
                if (c == '\n' || c == ';' || c == '\'' || c == '"' || c == '`') { break; }
                e = e + 1;
            }
            t = e;
            if (e < n && b[e] != '\n') {
                if (b[e] != ';') { self.kill(); return; }
                while (e < n && b[e] != '\n') { e = e + 1; }
            }
            s: long = i;
            while (s < t && (b[s] == ' ' || b[s] == '\t')) { s = s + 1; }
            while (t > s && (b[t - 1] == ' ' || b[t - 1] == '\t')) { t = t - 1; }
            if (t > s) { self.classify(b, s, t); }
            i = e + 1;
        }
    }

    kill &self -> void {
        if (!self.dead) { self.nKept = self.nKept + 1; }
        self.dead = true;
        self.blind = true;
        self.regs = RX_ALL;
    }

    // A trimmed line [s, t): a label, a jump to one, or an instruction whose bound adds to the gap.
    classify &self b:[u8] s:long t:long -> void {
        if (b[t - 1] == ':' && t - s > 1 && identAt(b, s, t - 1)) {
            if (!self.first && b[s] != '.') { self.kill(); return; }
            if (!self.dead) {
                self.eLabel.push(s);
                self.pushEntry(LK_LABEL, self.gap, 0, 0, t - 1);
                self.gap = 0;
            }
            self.first = false;
            return;
        }
        // Every conditional jump and `jmp` starts with `j`, and nothing else in the table does.
        // One that leaves the function, to a label not local to it or through a register or
        // memory, may reach code that changes any register.
        jl: long = 0;
        m: long = s;
        if (b[s] == 'j') {
            while (m < t && alnumC(b[m] as long)) { m = m + 1; }
            if (m < t && b[m] == ' ') {
                c: long = classAt(b, s, m) / 32;
                o: long = skipSpaces(b, m, t);
                if ((c == MC_JCC || c == MC_JMP) && identAt(b, o, t) && regAt(b, o, t) < 0) {
                    jl = 5;
                    if (c == MC_JCC) { jl = 6; }
                    if (b[o] != '.') { self.regs = RX_ALL; }
                } else if (c == MC_JMP) { self.regs = RX_ALL; }
            }
        }
        if (jl > 0) {
            if (!self.dead) {
                self.eLabel.push(-1);
                self.pushEntry(LK_JUMP, self.gap, jl, m, t);
                self.gap = 0;
                self.jumps = self.jumps + 1;
            }
        } else {
            bd: long = self.cachedBound(b, s, t);
            if (bd < 0) { self.kill(); return; }
            if (!self.dead) { self.gap = self.gap + bd; }
            if (!self.aside) { self.regs = self.regs | self.lineRegs; }
            // A call may change whatever its callee may: what `calls` holds for its label, and
            // anything for a label it does not hold or a callee in a register or memory.
            if (!self.blind && !self.aside && t - s > 5 && b[s] == 'c' && b[s + 1] == 'a' && b[s + 2] == 'l' && b[s + 3] == 'l' && b[s + 4] == ' ') {
                o: long = skipSpaces(b, s + 5, t);
                callee: long = RX_ALL;
                if (identAt(b, o, t) && regAt(b, o, t) < 0) {
                    hit: Option<long> = self.calls.find(b[o..t] as str);
                    match hit { Some(v) { callee = v; } None { } }
                }
                self.regs = self.regs | callee;
            }
        }
        self.first = false;
    }

    // The function is whole: rewrite short every jump the bounds show to be in reach of its target.
    finish &self inout out:String -> void {
        if (self.dead || self.jumps == 0) { return; }
        text: str = "";
        unsafe { text = out.view(); }
        b: [u8] = text as [u8];
        from: long = self.from;
        n: long = b.len;
        jumps: long = self.jumps;
        ne: long = self.eKind.len();
        if (self.labels.cap() > 512) { self.labels = map![]; } else { self.labels.clear(); }
        for k in 0..ne {
            if (self.eKind.get(k) != LK_LABEL) { continue; }
            ls: long = self.eLabel.get(k);
            self.labels.put(strSlice(text, ls, self.eEnd.get(k) - ls), k);
        }
        // Each jump's target, and every jump short to begin with.
        for k in 0..ne {
            if (self.eKind.get(k) != LK_JUMP) { continue; }
            o: long = skipSpaces(b, self.eMn.get(k), self.eEnd.get(k));
            hit: Option<long> = self.labels.find(strSlice(text, o, self.eEnd.get(k) - o));
            match hit { Some(x) { self.eTarget.set(k, x); self.eShort.set(k, true); } None { } }
        }
        self.labels.clear();
        changed: bool = true;
        while (changed) {
            changed = false;
            pos: long = 0;
            for k in 0..ne {
                pos = pos + self.eGap.get(k);
                self.eAt.set(k, pos);
                if (self.eKind.get(k) == LK_JUMP) {
                    if (self.eShort.get(k)) { pos = pos + 2; } else { pos = pos + self.eLen.get(k); }
                }
            }
            for k in 0..ne {
                if (!self.eShort.get(k)) { continue; }
                d: long = self.eAt.get(self.eTarget.get(k)) - (self.eAt.get(k) + 2);
                if (d < -128 || d > 127) { self.eShort.set(k, false); changed = true; }
            }
        }
        shorts: long = 0;
        for k in 0..ne { if (self.eShort.get(k)) { shorts = shorts + 1; } }
        self.nShort = self.nShort + shorts;
        self.nNear = self.nNear + jumps - shorts;
        if (shorts == 0) { return; }
        // The text is written again from a copy, with `short` after each short jump's mnemonic.
        self.copy.clear();
        self.copy.pushStr(strSlice(text, from, n - from));
        held: str = "";
        unsafe { held = self.copy.view(); }
        out.truncate(from);
        last: long = 0;
        for k in 0..ne {
            if (!self.eShort.get(k)) { continue; }
            ma: long = self.eMn.get(k) - from;
            out.pushStr(strSlice(held, last, ma - last));
            out.pushStr(" short");
            last = ma;
        }
        out.pushStr(strSlice(held, last, held.len - last));
    }

    pushEntry &self kind:long gap:long len:long mn:long end:long -> void {
        self.eKind.push(kind); self.eGap.push(gap); self.eLen.push(len); self.eMn.push(mn); self.eEnd.push(end);
        self.eTarget.push(-1); self.eShort.push(false); self.eAt.push(0);
    }
}
