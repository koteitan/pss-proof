#!/usr/bin/env python3
r"""r26-VE1CORE: (1) confirm the VE'(1) counterexample rigorously,
(2) characterize the TRUE sub-domain, (3) test the ACTUAL W2 statement on
brute-force straddle hosts H (not oper-only)."""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, seg, parent, hasParent,
                       Adm, fmt, TrMax, Br)
from trans_model import (Trans, Mark, Pred, bpHeadT, bpHeadV, reduced, adm,
                         condI, condIII, condV, condVI, PB)

def pr(*a): print(*a, flush=True)

def condII(M):
    j1=Lng(M)-1; p=parent(M,0,j1)
    return entry(M,1,j1)==0 and not adm(M,p)
def condIV(M):
    j1=Lng(M)-1; p=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,p)>=entry(M,1,j1) and not adm(M,p)

def rmreduced(M): return rm.Red(list(M)) == list(M)

def ve1(S):
    j1 = Lng(S) - 1
    Sp = seg(S, 1, j1)
    return bpHeadT(Trans(list(S))) == bpHeadT(Trans(list(Sp)))

def transcond(S):
    for nm, f in [('I',condI),('II',condII),('III',condIII),
                  ('IV',condIV),('V',condV),('VI',condVI)]:
        try:
            if f(S): return nm
        except Exception:
            pass
    return '?'

# ---------- (1) confirm minimal CEX ----------
pr("=== (1) CEX confirmation ===")
CEX = [(0,0),(1,1),(2,2),(1,0)]
pr("S =", fmt(CEX))
pr("  monoT      :", monoT(CEX))
pr("  zeroT      :", zeroT(CEX))
pr("  reduced(RedCondAB):", reduced(CEX))
pr("  reduced(Red==M)   :", rmreduced(CEX))
pr("  adm S 1    :", adm(CEX,1), " (need False)")
pr("  1<Lng-1    :", 1 < Lng(CEX)-1)
pr("  Trans S       :", Trans(list(CEX)))
Sp = seg(CEX,1,Lng(CEX)-1)
pr("  seg S 1 (L-1) :", fmt(Sp))
pr("  Trans (seg)   :", Trans(list(Sp)))
pr("  bpHeadT Trans S   :", bpHeadT(Trans(list(CEX))))
pr("  bpHeadT Trans seg :", bpHeadT(Trans(list(Sp))))
pr("  VE1 holds  :", ve1(CEX), " <== FALSE means genuine counterexample")

# ---------- (2) characterize TRUE vs FALSE over brute ¬adm-1 hosts ----------
pr("\n=== (2) characterization over brute reduced monoT ¬adm-1 hosts ===")
def brute_hosts(n, K):
    out=[]
    for pairs in itertools.product(itertools.product(range(K+1),range(K+1)),repeat=n):
        S=list(pairs)
        if Lng(S)<3 or zeroT(S) or not monoT(S): continue
        if adm(S,1): continue
        if not (1 < Lng(S)-1): continue
        if not reduced(S): continue
        out.append(S)
    return out

hosts=[]
for n,K in [(3,4),(4,3),(4,4),(5,3)]:
    hs=brute_hosts(n,K)
    hosts += hs
    pr(f"  brute n={n} K={K}: {len(hs)} hosts")
# dedup
seen=set(); uh=[]
for S in hosts:
    k=tuple(S)
    if k not in seen: seen.add(k); uh.append(S)
pr(f"  total unique = {len(uh)}")

# candidate extra conditions:
def jp(S): return parent(S,0,Lng(S)-1)
def cand(name, S):
    j1=Lng(S)-1; p=jp(S)
    if name=='admJp':      return adm(S, p)
    if name=='jp_ge2':     return p >= 2
    if name=='not_II_IV':  return transcond(S) not in ('II','IV')
    if name=='admJp_or_condVVI': return adm(S,p) or transcond(S) in ('V','VI')
    if name=='TransS_princ_body_single':
        b=bpHeadT(Trans(list(S))); return len(b[1])<=1
    return None

names=['admJp','jp_ge2','not_II_IV','admJp_or_condVVI']
stats={nm:[0,0,0,0] for nm in names}   # TT, TF(cond true,ve false), FT, FF
tab=[]
t0=time.time()
for S in uh:
    if time.time()-t0>120:
        pr("  (time budget hit; partial)"); break
    try:
        v=ve1(S)
    except Exception as e:
        continue
    tc=transcond(S); p=jp(S)
    tab.append((fmt(S), v, tc, p, adm(S,p)))
    for nm in names:
        c=cand(nm,S)
        if c and v: stats[nm][0]+=1
        elif c and not v: stats[nm][1]+=1
        elif (not c) and v: stats[nm][2]+=1
        else: stats[nm][3]+=1
pr("  condition  [cond&VE  cond&~VE  ~cond&VE  ~cond&~VE]  (want cond<=>VE: cols2,3 ==0)")
for nm in names:
    a,b,c,d=stats[nm]
    ok = (b==0 and c==0)
    pr(f"    {nm:26s} [{a:4d} {b:4d} {c:4d} {d:4d}]  {'EXACT' if ok else ''}")
# show a few TRUE and FALSE with their transcond
tf=[t for t in tab if t[1]]; ff=[t for t in tab if not t[1]]
pr(f"  #VE1 TRUE={len(tf)}  #VE1 FALSE={len(ff)}")
pr("  sample FALSE (S, transcond, jp, admJp):")
for t in ff[:14]: pr("     ", t[0], t[2], 'jp=',t[3], 'admJp=',t[4])
pr("  sample TRUE:")
for t in tf[:8]: pr("     ", t[0], t[2], 'jp=',t[3], 'admJp=',t[4])

pr("\ndone")
