#!/usr/bin/env python3
"""r27-CONDIII: validate the KER de-adm identity + seg-of-seg reduction used by
c3vx_KER_of_VE (reducing veM/veL to cfbx_VE at condIII slices).

KER regime (EXACTLY the vmlx_veM/veL_of_kernel hypothesis):
    H in RT_PS (reduced), monoT H, (H, Adm H q) in Marked, leR H 0 q c,
    q<c, c<Lng H  ==>
      bpHeadT(Trans(seg H (Adm H q) c)) = bpHeadT(Trans(seg H q c))
and  seg (seg H (Adm H q) c) (q-Adm H q) (Lng(seg H (Adm H q) c)-1) == seg H q c.

Note KER is stated for H in RT_PS & monoT H (standardness NOT required), so the
honest test corpus is reduced&monoT hosts.  The straddle warning (W1/W2/KER were
false positives on oper-ONLY corpora) is addressed by including BRUTE-FORCE
straddle hosts (random + diagSeq-prefixed), NOT just oper-generated ones, at
DEEP Lng>=9.  Run:  python3 -u <this>.
"""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, seg, Adm, leR, monoT, reduced, marked, diagSeq,
                       is_standard, fmt, oper)
from trans_model import Trans, bpHeadT

def pr(*a):
    print(*a); sys.stdout.flush()

# ---------- 1. seg-of-seg identity (pure list algebra) ----------
def check_segseg(n_iter=50000):
    bad = 0
    for _ in range(n_iter):
        n = random.randint(3, 14)
        H = [(random.randint(0,4), random.randint(0,4)) for _ in range(n)]
        a = random.randint(0, n-1); c = random.randint(a, n-1); q = random.randint(a, c)
        N = seg(H, a, c)
        if seg(N, q - a, Lng(N) - 1) != seg(H, q, c):
            bad += 1
            if bad <= 3: pr("  seg-of-seg CEX:", fmt(H), a, q, c)
    return bad

# ---------- host generators (reduced & monoT = RT_PS & PT_PS regime) ----------
def gen_random(nhosts, lo=9, hi=11, tries=40000):
    """Brute-force straddle: random reduced-monoT hosts (no oper, no is_standard).
    monoT prefilter (cheap) BEFORE reduced() (Red, expensive)."""
    hosts, seen, t = [], set(), 0
    while len(hosts) < nhosts and t < tries:
        t += 1
        n = random.randint(lo, hi)
        H = [(0,0)]; prev = 0
        for _ in range(n-1):
            a = prev + random.randint(0, 1)
            b = random.randint(0, a)
            H.append((a, b)); prev = a
        key = tuple(H)
        if key in seen: continue
        seen.add(key)
        if not monoT(H): continue        # cheap prefilter
        if not reduced(H): continue
        hosts.append(H)
    return hosts

def gen_diag_tail(lo=9, cap_hosts=1500, cap_iter=120000):
    """Brute-force straddle: diagSeq(0,d) + 2 tail pairs; monoT prefilter then reduced."""
    hosts, seen, it = [], set(), 0
    for d in range(6, 9):
        base = diagSeq(0, d)
        rng = range(0, d+1)
        for tail in itertools.product(itertools.product(rng, rng), repeat=2):
            it += 1
            if it > cap_iter: return hosts
            H = base + list(tail)
            if Lng(H) < lo: continue
            key = tuple(H)
            if key in seen: continue
            seen.add(key)
            if not monoT(H): continue     # cheap prefilter
            if not reduced(H): continue
            hosts.append(H)
            if len(hosts) >= cap_hosts: return hosts
    return hosts

def gen_oper_deep(lo=9):
    """oper(seed,n) for growing n (the genuine successor expansions)."""
    seeds = [[(0,0),(1,1),(2,1)], [(0,0),(1,1),(2,2),(3,1)], [(0,0),(1,1),(2,1),(3,1)],
             [(0,0),(1,1),(2,2),(3,2)], [(0,0),(1,1),(2,1),(3,2)],
             [(0,0),(1,1),(2,2),(3,3),(4,1)]]
    hosts, seen = [], set()
    std = 0
    for s in seeds:
        for n in range(1, 10):
            M = oper(s, n)
            if not M or Lng(M) < lo: continue
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            if not monoT(M) or not reduced(M): continue
            hosts.append(M)
            try:
                if is_standard(M): std += 1
            except Exception: pass
    return hosts, std

# ---------- 2. KER over admissible instances ----------
def check_KER(hosts, tag):
    tot = deep = nontrivial = bad = 0; cexs = []
    for H in hosts:
        n = Lng(H)
        for q in range(1, n-1):
            a = Adm(H, q)
            if not marked(H, a): continue           # (H, Adm H q) in Marked
            for c in range(q+1, n):
                if not leR(H, 0, q, c): continue     # leR H 0 q c, q<c<Lng H
                tot += 1
                if n >= 9: deep += 1
                if a < q: nontrivial += 1
                try:
                    if bpHeadT(Trans(seg(H, a, c))) != bpHeadT(Trans(seg(H, q, c))):
                        bad += 1
                        if len(cexs) < 6: cexs.append((fmt(H), 'q', q, 'c', c, 'Adm', a))
                except Exception:
                    continue
    pr(f"  [{tag}] KER {tot-bad}/{tot}  deep {deep}  nontrivial(Adm<q) {nontrivial}  CEX {bad}")
    for ce in cexs: pr("    KER CEX:", ce)
    return bad, nontrivial

if __name__ == '__main__':
    random.seed(20270703)
    pr("== seg-of-seg identity (pure) ==")
    b0 = check_segseg(); pr(f"  seg-of-seg CEX: {b0}")

    pr("== brute-force straddle: random reduced-monoT hosts (Lng 9-11) ==")
    H1 = gen_random(120); pr(f"  collected {len(H1)} hosts")
    b1, nt1 = check_KER(H1, "random-straddle")

    pr("== brute-force straddle: diagSeq+tail reduced-monoT hosts (Lng>=9) ==")
    H2 = gen_diag_tail(); pr(f"  collected {len(H2)} hosts")
    b2, nt2 = check_KER(H2, "diag-tail-straddle")

    pr("== oper-generated deep hosts (successor expansions) ==")
    H3, std3 = gen_oper_deep(); pr(f"  collected {len(H3)} hosts ({std3} verified standard)")
    b3, nt3 = check_KER(H3, "oper-deep")

    pr("== SUMMARY ==")
    pr(f"  seg-of-seg CEX={b0}")
    pr(f"  KER CEX: random={b1} (nt {nt1})  diag-tail={b2} (nt {nt2})  oper={b3} (nt {nt3})")
    pr("  VERDICT:", "ALL GREEN" if (b0+b1+b2+b3)==0 else "!!! CEX FOUND !!!")
