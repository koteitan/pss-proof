#!/usr/bin/env python3
"""r26: pin down the PROOF bridge sub-facts for c6nx (nadm-j0 condVI)."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, P, monoT, seg, diagSeq, parent, oper, fmt
import red_model as rm
from _r15_vx_lib import (Trans, Mark, gen_pool, mono_hosts, guarded, SKIP,
                         condVI, internals, flatBT)
from trans_model import (Dpt, ZB, adm, Adm, Pred, reduced, bpHeadV, bpHeadT)

def transJ0(M): return parent(M, 0, Lng(M)-1)
def transJm1(M): return Adm(M, transJ0(M))

def le0(M, a, b):
    # (nextrel0 M)^* a b within range
    if a == b and a < Lng(M): return True
    seen = {a}; frontier = [a]
    while frontier:
        x = frontier.pop()
        for y in range(x+1, Lng(M)):
            if parent(M, 0, y) == x and y not in seen:
                if y == b: return True
                seen.add(y); frontier.append(y)
    return b in seen

def run(hosts, label):
    st = dict(hosts=0, jm1eq=0, le0=0, v_eq_u=0, v_lt_u=0, v_le_u=0,
              PredMono=0, PredJ1pos=0, runnadm=0)
    bad = []
    for M0 in hosts:
        M = list(M0)
        info = internals(M)
        if info is None: continue
        j0 = transJ0(M); jm1 = transJm1(M); u = entry(M, 1, j0); v = info['v']
        st['hosts'] += 1
        PM = Pred(M)
        jm1P = transJm1(PM) if Lng(PM) >= 2 else -1
        st['jm1eq'] += (jm1 == jm1P)
        st['le0'] += le0(M, jm1, j0)
        st['v_eq_u'] += (v == u)
        st['v_lt_u'] += (v < u)
        st['v_le_u'] += (v <= u)
        st['PredMono'] += (Lng(PM) >= 2 and monoT(PM))
        st['PredJ1pos'] += (Lng(PM)-1 > 0)
        # run (jm1, j0] all non-adm?
        runnadm = all(not adm(M, s) for s in range(jm1+1, j0+1))
        st['runnadm'] += runnadm
        if jm1 != jm1P or v > u:
            bad.append((fmt(M), f"j0={j0} jm1={jm1} jm1P={jm1P} u={u} v={v}"
                        f" le0={le0(M,jm1,j0)} runnadm={runnadm}"))
    h = st['hosts']
    print(f"\n=== {label}: {h} hosts ===")
    for k in ('jm1eq','le0','runnadm','v_eq_u','v_lt_u','v_le_u','PredMono','PredJ1pos'):
        print(f"  {k:11s}: {st[k]}/{h}")
    for b in bad[:12]: print("  BAD:", b)

pool = gen_pool(maxlen=12, maxn=6, maxseed=4, cap=20000, oper_budget=5)
hosts = mono_hosts(pool)
nadm = [M for M in hosts if Lng(M) >= 4 and Lng(M)-1 > 1 and reduced(M)
        and guarded(condVI, M, budget=5) is not SKIP and condVI(M)
        and not adm(M, transJ0(M))]
run(nadm, "ST_PS oper-closure deep")

def gen_brute(maxlen, maxval):
    out = []
    for L in range(4, maxlen+1):
        cols = [(a, b) for a in range(maxval+1) for b in range(maxval+1)]
        for rest in itertools.product(cols, repeat=L-1):
            M = [(0, 0)] + list(rest)
            if monoT(M) and reduced(M): out.append(tuple(M))
    return out
brute = gen_brute(6, 3)
bnadm = [M for M in brute if Lng(M)-1 > 1
         and guarded(condVI, M, budget=5) is not SKIP and condVI(M)
         and not adm(M, transJ0(M))]
run(bnadm, "BRUTE reduced-monoT")
