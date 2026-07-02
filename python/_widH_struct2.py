#!/usr/bin/env python3
"""widH over DT_PS (reduced + monoT + descending(Br) + REACHABLE).
Check if the j0p-landing failures vanish on the genuine DT_PS / reachable set."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm, oper, diagSeq, seg, P, IncrFirst, funpow)
from trans_model import Trans, reduced

def RightNodes(t):
    ps = t[1]
    if not ps: return []
    v, body = ps[-1][1], ps[-1][2]
    return [v] + RightNodes(body)

def cdom(a, b):
    a00,a10 = a[0][0], a[0][1]; b00,b10 = b[0][0], b[0][1]
    return (a00 > b00) or (a00==b00 and a10 >= b10)
def descending(brs):
    return all(cdom(brs[i], brs[i+1]) for i in range(len(brs)-1))

# reachable set: BFS via oper from small diag seeds (approx DT_PS)
def reachable_set(maxlen, steps, maxn):
    seen = set()
    frontier = []
    for a in range(3):
        for b in range(a+1, a+4):
            M = tuple(diagSeq(a,b))
            seen.add(M); frontier.append(list(M))
    out = set(seen)
    for _ in range(steps):
        nf = []
        for M in frontier:
            for n in range(maxn+1):
                try:
                    N = oper(M, n)
                    if Lng(N) <= maxlen and N:
                        T = tuple(N)
                        if T not in out:
                            out.add(T); nf.append(N)
                except Exception:
                    pass
        frontier = nf
        if not frontier: break
    return [list(t) for t in out]

def is_DT(M):
    try:
        return monoT(M) and reduced(M) and descending(Br(M))
    except Exception:
        return False

def analyze(seqs, label):
    rows=[]; fails=[]
    for M in seqs:
        try:
            if Br(M)==[] or Lng(M)-1<=1: continue
            J1=Lng(Br(M))-1; j0p=Joints(M)[J1]; j1p=FirstNodes(M)[J1]
            e1j1=entry(M,1,j1p); e1j0=entry(M,1,j0p); e0j1=entry(M,0,j1p)
            C=(j0p==0) or (e0j1==e1j1)
            if not C: continue
            rn=RightNodes(Trans(M))
            if len(rn)<2: continue
            rn1=rn[1]; widH=e1j1<=rn1
            rows.append(widH)
            if not widH: fails.append((M,e1j1,e1j0,rn1))
        except Exception: continue
    print(f"[{label}] C-sat={len(rows)} widH_fail={len(fails)}")
    for f in fails[:12]: print("   FAIL",f)
    return fails

# (1) all reduced monoT DESCENDING (DT_PS, possibly non-reachable)
def gen_dt(maxlen, maxval):
    res=[]
    for n in range(4,maxlen+1):
        for seq in itertools.product([(a,b) for a in range(maxval+1) for b in range(maxval+1)], repeat=n):
            M=list(seq)
            if M[0] not in [(0,0),(1,1)]: continue
            if is_DT(M): res.append(M)
    return res

dt = gen_dt(6,3)
fails_dt = analyze(dt, "DT_PS reduced+monoT+descending (maxlen6,maxval3)")

# (2) reachable
reach = reachable_set(8, 6, 5)
reach = [M for M in reach if is_DT(M)]
print("reachable DT count:", len(reach))
fails_re = analyze(reach, "REACHABLE DT_PS")
