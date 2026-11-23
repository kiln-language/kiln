# ipracheck.py ASM TRACE: hold the compiler's interprocedural register sets (`--trace-ipra`) to the
# assembly it wrote. Each function's set is worked out again here from its lines alone, with a
# table of implicit register writes of this file's own (from the instruction set reference, not
# from relax.k), and every set the compiler recorded must hold every register found here.
# Prints each function where it does not, and a summary; exits 1 on any.
import re, sys

GPR = {}
for r, al in [("rax", "eax ax al ah"), ("rbx", "ebx bx bl bh"), ("rcx", "ecx cx cl ch"), ("rdx", "edx dx dl dh"),
              ("rsi", "esi si sil"), ("rdi", "edi di dil"), ("rbp", "ebp bp bpl"), ("rsp", "esp sp spl")]:
    GPR[r] = r
    for a in al.split():
        GPR[a] = r
for i in range(8, 16):
    for suf in ("", "d", "w", "b"):
        GPR["r%d%s" % (i, suf)] = "r%d" % i
def canon(tok):
    if tok in GPR:
        return GPR[tok]
    m = re.fullmatch(r"[xyz]mm(\d+)", tok)
    if m:
        k = int(m.group(1))
        return "xmm%d" % k if 8 <= k <= 14 else "xmm*"
    return None

CALLEE = {"r12", "r13", "r14", "r15", "rbp", "rsp", "xmm12", "xmm13", "xmm14"}
FULL = {"rax", "rbx", "rcx", "rdx", "rdi", "rsi", "r8", "r9", "r10", "r11", "xmm8", "xmm9", "xmm10", "xmm11", "xmm*"}
ALWAYS = {"rax", "rdx", "xmm*"}

# Registers an instruction writes without naming them (Intel SDM vol. 2). A string instruction
# with `rep` also counts down rcx.
IMPLICIT = {
    "mul": {"rax", "rdx"}, "div": {"rax", "rdx"}, "idiv": {"rax", "rdx"},
    "cbw": {"rax"}, "cwde": {"rax"}, "cdqe": {"rax"}, "cwd": {"rdx"}, "cdq": {"rdx"}, "cqo": {"rdx"},
    "cmpxchg": {"rax"}, "cmpxchg8b": {"rax", "rdx"}, "cmpxchg16b": {"rax", "rdx"},
    "cpuid": {"rax", "rbx", "rcx", "rdx"}, "rdtsc": {"rax", "rdx"}, "rdtscp": {"rax", "rdx", "rcx"},
    "rdpmc": {"rax", "rdx"}, "rdmsr": {"rax", "rdx"}, "xgetbv": {"rax", "rdx"},
    "syscall": {"rax", "rcx", "r11"},
    "lodsb": {"rax", "rsi"}, "lodsw": {"rax", "rsi"}, "lodsd": {"rax", "rsi"}, "lodsq": {"rax", "rsi"},
    "stosb": {"rdi"}, "stosw": {"rdi"}, "stosd": {"rdi"}, "stosq": {"rdi"},
    "movsb": {"rsi", "rdi"}, "movsw": {"rsi", "rdi"}, "movsq": {"rsi", "rdi"},
    "scasb": {"rdi"}, "scasw": {"rdi"}, "scasd": {"rdi"}, "scasq": {"rdi"},
    "cmpsb": {"rsi", "rdi"}, "cmpsw": {"rsi", "rdi"}, "cmpsq": {"rsi", "rdi"},
    "loop": {"rcx"}, "loope": {"rcx"}, "loopne": {"rcx"}, "xlatb": {"rax"}, "lahf": {"rax"},
    "in": {"rax"}, "vzeroall": {"xmm8", "xmm9", "xmm10", "xmm11", "xmm*"},
}
# Instructions whose register effects are their operands (and rsp, rbp, flags) and nothing else.
PLAIN = set("""mov movzx movsx movsxd lea add sub and or xor cmp test adc sbb neg not inc dec xadd xchg
shl shr sar sal rol ror rcl rcr shld shrd bt bts btr btc bsf bsr tzcnt lzcnt popcnt bswap imul
push pop ret leave enter nop pause hlt ud2 int3 lfence mfence sfence
movsd movss movq movd movaps movapd movups movupd movdqa movdqu addsd subsd mulsd divsd addss subss
mulss divss sqrtsd sqrtss minsd maxsd minss maxss ucomisd ucomiss comisd comiss xorpd xorps andpd
andps andnpd andnps orpd orps pxor por pand cvtsi2sd cvtsi2ss cvtsd2ss cvtss2sd cvttsd2si cvttss2si
cvtsd2si cvtss2si roundsd roundss""".split())
TOK = re.compile(r"[A-Za-z_.$@?][A-Za-z0-9_.$@?]*")

def own_regs(mn, ops, prefix):
    """The registers one line may change, or None for one this file does not know."""
    regs = set()
    if mn in ("rep", "repe", "repz", "repne", "repnz"):
        inner = ops.split()
        if not inner or inner[0] not in IMPLICIT:
            return None
        return IMPLICIT[inner[0]] | {"rcx"}
    if mn == "lock":
        inner = ops.split(None, 1)
        if not inner:
            return None
        return own_regs(inner[0], inner[1] if len(inner) > 1 else "", "lock")
    if not (mn in PLAIN or mn in IMPLICIT or re.fullmatch(r"j[a-z]+|set[a-z]+|cmov[a-z]+", mn)):
        return None
    for t in TOK.findall(ops):
        c = canon(t)
        if c:
            regs.add(c)
    regs |= IMPLICIT.get(mn, set())
    if mn == "imul" and "," not in ops:
        regs |= {"rax", "rdx"}
    return regs

def blocks_reaching_ret(lines, noret):
    """Which lines lie on a path to a `ret`: the text cut into blocks at labels and after every
    jump, `ret` and call that never returns; a block reaches a return when it holds one, or falls
    or jumps into a block that does. A jump out of the function counts as a return."""
    starts = [0]
    label_at = {}
    for i, (mn, ops) in enumerate(lines):
        if mn == ":":
            label_at[ops] = i
            if i != starts[-1]:
                starts.append(i)
        elif mn == "ret" or mn.startswith("j") or (mn == "call" and ops in noret):
            if i + 1 < len(lines):
                starts.append(i + 1)
    starts = sorted(set(starts))
    blk_of = {}
    for b, s0 in enumerate(starts):
        e0 = starts[b + 1] if b + 1 < len(starts) else len(lines)
        for i in range(s0, e0):
            blk_of[i] = b
    nb = len(starts)
    succ = [[] for _ in range(nb)]
    rets = [False] * nb
    for b, s0 in enumerate(starts):
        e0 = starts[b + 1] if b + 1 < len(starts) else len(lines)
        falls = True
        for i in range(s0, e0):
            mn, ops = lines[i]
            if mn == "ret":
                rets[b] = True; falls = False
            elif mn.startswith("j"):
                o = ops.replace("short ", "").strip()
                if o in label_at:
                    succ[b].append(blk_of[label_at[o]])
                else:
                    rets[b] = True          # leaves the function
                if mn == "jmp":
                    falls = False
            elif mn == "call" and ops in noret:
                falls = False
        if falls and b + 1 < nb:
            succ[b].append(b + 1)
    reach = list(rets)
    changed = True
    while changed:
        changed = False
        for b in range(nb):
            if not reach[b] and any(reach[c] for c in succ[b]):
                reach[b] = True; changed = True
    return [reach[blk_of[i]] for i in range(len(lines))]

def parse(path):
    """Each function's lines, as (mnemonic, operands), a label as (":", name)."""
    fns = {}; order = []; cur = None; text = False
    for ln in open(path):
        ln = ln.rstrip("\n")
        s = ln.split(";")[0].strip()
        if not s:
            continue
        if s.startswith("section "):
            text = s.split()[1].startswith(".text"); cur = None; continue
        if not text or s.startswith(("global ", "extern ", "align ", "default ")):
            continue
        if s.endswith(":") and not ln[:1].isspace() and not s.startswith("."):
            cur = {"name": s[:-1], "lines": []}
            fns[cur["name"]] = cur; order.append(cur["name"]); continue
        if cur is None:
            continue
        if s.endswith(":"):
            cur["lines"].append((":", s[:-1])); continue
        parts = s.split(None, 1)
        cur["lines"].append((parts[0], parts[1].strip() if len(parts) > 1 else ""))
    return fns, order

def summarize(f, noret):
    """What a function's lines on a path to a return change on their own, and whom they call."""
    f["own"] = set(); f["calls"] = []; f["full"] = False
    live = blocks_reaching_ret(f["lines"], noret)
    for (mn, ops), keep in zip(f["lines"], live):
        if mn == ":" or not keep:
            continue
        if mn == "call" or mn.startswith("j"):
            o = ops.replace("short ", "").strip()
            if mn == "call" or not o.startswith("."):
                if canon(o) or "[" in o or not TOK.fullmatch(o):
                    f["full"] = True
                else:
                    f["calls"].append(o)
            continue
        r = own_regs(mn, ops, "")
        if r is None:
            f["full"] = True
        else:
            f["own"] |= r

def main():
    asm, trace = sys.argv[1], sys.argv[2]
    rec = {}; noret = set()
    for ln in open(trace):
        p = ln.split()
        if not p:
            continue
        if p[0] == "ipra":
            rec[p[1]] = set(p[2:])
        elif p[0] == "ipra-noreturn":
            noret.add(p[1])
    fns, order = parse(asm)
    for n in order:
        summarize(fns[n], noret)
    # The least sets that satisfy own | callees, found by going round until nothing grows.
    mask = {n: set() for n in order}
    changed = True
    while changed:
        changed = False
        for n in order:
            f = fns[n]
            m = set(FULL) if f["full"] else (f["own"] | ALWAYS)
            if not f["full"]:
                for c in f["calls"]:
                    if c in noret:
                        continue
                    m |= mask[c] if c in mask else FULL
            m = {r for r in m if r not in CALLEE}
            if m != mask[n]:
                mask[n] = m; changed = True
    bad = 0; checked = 0; tighter = 0
    for n in order:
        if n not in rec:
            continue
        checked += 1
        miss = mask[n] - rec[n]
        if miss:
            bad += 1
            if bad <= 30:
                print("%s: written but not in its set: %s" % (n, " ".join(sorted(miss))))
        elif rec[n] != mask[n]:
            tighter += 1
    print("ipracheck: %d functions checked, %d with a register missing from their set, %d whose set is wider than their text needs" % (checked, bad, tighter))
    sys.exit(1 if bad else 0)

main()
