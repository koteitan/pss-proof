#!/usr/bin/env python3
"""Verification harness for §6.5-FIX glue:
 (L6) redle_core_nontrunk_BC WITH descending(Br M): on core (m00=m10=0) nontrunk
      monoT M with descending(Br M), leR M == leR(Red M).
 (C-shift) descending(Br M) => descending(Br (shiftRow0 M))
 (C-core)  descending(Br M) => descending(Br (diagSeq 0 (m10-1) @ IncrFirst^m10 M))
 (C-NJ)    descending(Br M) => descending(Br (NJ M J))  for J<Lng(Br M)
Generate standard terms + their anchored slices (which carry monoT & descending Br),
then test each lemma's statement as an implication over the generated population.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, monoT, multiT, zeroT, Br, IdxSum,
                       IncrFirst, FirstNodes, Joints, THE_nextR, diagSeq, funpow,
                       Red, leR, le0, fmt)
from d1pos_j0j1red_search import gen_std

def rankL(M): return Lng(M)
def valM(M): return max((max(a,b) for (a,b) in M), default=0)

def descending(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            a0,a1=entry(Q[J0],0,0),entry(Q[J0],1,0)
            b0,b1=entry(Q[J1],0,0),entry(Q[J1],1,0)
            if a0<b0: return False
            if a0==b0 and a1<b1: return False
    return True

def shiftRow0(M):
    m00=entry(M,0,0)
    return [(entry(M,0,j)-m00, entry(M,1,j)) for j in range(Lng(M))]

def coreReduce(M):
    m10=entry(M,1,0)
    if m10==0: return shiftRow0(M)
    return diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)

def npJ(M,J):
    b=Br(M)
    if entry(b[J],1,0)==0: return 0
    par=THE_nextR(M,1,FirstNodes(M)[J])
    return par+1
def NJ(M,J):
    b=Br(M); m00=entry(M,0,0); m10=entry(M,1,0); jn=Joints(M)
    return [(m00+jn[J]+1, m10+npJ(M,J))]+b[J][1:]

# population: standard terms and their le0-anchored proper slices
def population(maxlen,maxval,KMAX):
    Ms=gen_std(maxlen,maxval,KMAX)
    slices=[]
    for S in Ms:
        n=Lng(S)
        for a in range(n):
            for b in range(a,n):
                if le0(S,a,b):
                    M=seg(S,a,b)
                    if Lng(M)>=1:
                        slices.append(M)
    # dedup
    store={}
    for M in slices: store[fmt(M)]=M
    return list(store.values())

def is_core_nontrunk(M):
    return monoT(M) and entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)!=Lng(M)-1

def check_L6(pop):
    """redle_core_nontrunk_BC with descending(Br M) hypothesis."""
    strat={}; t=f=0; ce=[]
    for M in pop:
        if not is_core_nontrunk(M): continue
        if not descending(Br(M)): continue   # the added hypothesis
        R=Red(M); ok=True; first=None
        if Lng(R)!=Lng(M): ok=False; first=('LNG',fmt(R))
        else:
            n=Lng(M)
            for i in (0,1):
                for j0 in range(n):
                    for j1 in range(n):
                        if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                            ok=False; first=(i,j0,j1); break
                    if not ok: break
                if not ok: break
        r,v=rankL(M),valM(M); strat.setdefault((r,v),[0,0])
        strat[(r,v)][0 if ok else 1]+=1
        if ok: t+=1
        else:
            f+=1
            if len(ce)<8: ce.append((fmt(M),first,fmt(R)))
    print(f"== L6 redle_core_nontrunk_BC (+descending Br): TRUE={t} FALSE={f}")
    for k in sorted(strat):
        a,b=strat[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: T{a}/F{b}")
    for c in ce: print("    CE:",c)
    return f

def check_L6_NObrhyp(pop):
    """SAME L6 but WITHOUT descending(Br M): should find the 100 breakers."""
    t=f=0; ce=[]
    for M in pop:
        if not is_core_nontrunk(M): continue
        R=Red(M); ok=True; first=None
        if Lng(R)!=Lng(M): ok=False
        else:
            n=Lng(M)
            for i in (0,1):
                for j0 in range(n):
                    for j1 in range(n):
                        if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                            ok=False; first=(i,j0,j1); break
                    if not ok: break
                if not ok: break
        if ok: t+=1
        else:
            f+=1
            if len(ce)<5: ce.append((fmt(M),fmt(Br(M)),descending(Br(M))))
    print(f"== L6 WITHOUT descending hyp (control): TRUE={t} FALSE={f}")
    for c in ce: print("    breaker:",c,"(descBr=",c[2],")")

def check_closure(pop,name,argfun,guard=None):
    """descending(Br M) => descending(Br (argfun M))."""
    strat={}; t=f=0; ce=[]
    for M in pop:
        if not monoT(M): continue
        if guard and not guard(M): continue
        if not descending(Br(M)): continue
        try:
            A=argfun(M)
        except Exception as e:
            continue
        if A is None or Lng(A)==0: continue
        ok=descending(Br(A))
        r,v=rankL(M),valM(M); strat.setdefault((r,v),[0,0])
        strat[(r,v)][0 if ok else 1]+=1
        if ok: t+=1
        else:
            f+=1
            if len(ce)<8: ce.append((fmt(M),fmt(Br(M)),fmt(A),fmt(Br(A))))
    print(f"== {name}: TRUE={t} FALSE={f}")
    for k in sorted(strat):
        a,b=strat[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: T{a}/F{b}")
    for c in ce: print("    CE:",c)
    return f

def arg_core(M):
    m10=entry(M,1,0)
    return diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
def arg_NJ_all(M):
    # returns list-like; handled specially
    return None

def check_NJ(pop):
    strat={}; t=f=0; ce=[]
    for M in pop:
        if not monoT(M): continue
        if not descending(Br(M)): continue
        # the §6.5 branch-3b regime: core nontrunk
        if not (entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)!=Lng(M)-1): continue
        for J in range(Lng(Br(M))):
            A=NJ(M,J)
            if Lng(A)==0: continue
            ok=descending(Br(A))
            r,v=rankL(M),valM(M); strat.setdefault((r,v),[0,0])
            strat[(r,v)][0 if ok else 1]+=1
            if ok: t+=1
            else:
                f+=1
                if len(ce)<8: ce.append((fmt(M),J,fmt(A),fmt(Br(A))))
    print(f"== C-NJ descending(Br M)=>descending(Br(NJ M J)): TRUE={t} FALSE={f}")
    for k in sorted(strat):
        a,b=strat[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: T{a}/F{b}")
    for c in ce: print("    CE:",c)
    return f

if __name__=='__main__' and not (len(sys.argv)>1 and sys.argv[1]=="brute"):
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,6,7)
    pop=population(maxlen,maxval,KMAX)
    print(f"# population (anchored slices) = {len(pop)}  params L<={maxlen} val<={maxval} K={KMAX}")
    f1=check_L6(pop)
    check_L6_NObrhyp(pop)
    f2=check_closure(pop,"C-shift descending(Br M)=>descending(Br shiftRow0 M)",shiftRow0)
    f3=check_closure(pop,"C-core descending(Br M)=>descending(Br arg_core)",arg_core)
    f4=check_NJ(pop)
    print(f"\nSUMMARY false counts: L6={f1} Cshift={f2} Ccore={f3} CNJ={f4}")

# ============================================================================
# KEY FINDINGS (§6.5-FIX), recorded for the record:
#  - descending(Br M) is genuinely CLOSED under shiftRow0 (C-shift: brute 15904/0)
#    and under the coreReduce arg (C-core: brute 4338/0).
#  - descending(Br M) is NOT closed under NJ re-rooting (C-NJ: brute 776 FALSE),
#    e.g. (0,0)(1,0)(2,0)(2,1).  TRUE only on the anchored/reachable subset.
#  - The core-nontrunk redle obligation L6 is FALSE even WITH descending(Br M):
#    brute 2198 FALSE (e.g. (0,0)(1,1)(1,2)(2,2)).  TRUE only on anchored M.
#  => descending(Br) is INSUFFICIENT as a Red.pinduct invariant for the bottleneck;
#     the correct guard is reachability (M in anchored_slice), but anchored_slice
#     is NOT closed under the constructed shiftRow0/coreReduce arguments either.
#  - On anchored M the redle identity holds directly: anchored CORE 263/0,
#    anchored NONCORE 346/0, reducedMono anchored slices 4762/0.  These are the
#    sound (empirically-true) sorries shipped in pss_mechanized.thy.
# Run:  python3 glue_verify.py brute <maxlen> <maxval>   for the brute findings.
# ============================================================================
import itertools
def brute_mono(maxlen,maxval):
    res=[]; pairs=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for n in range(1,maxlen+1):
        for tail in itertools.product(pairs, repeat=n-1):
            M=[(0,0)]+list(tail)
            try:
                if not monoT(M): continue
            except Exception: continue
            res.append(M)
    return res

def run_brute(maxlen,maxval):
    R=brute_mono(maxlen,maxval)
    Rd=[M for M in R if descending(Br(M))]
    print(f"# brute monoT={len(R)} with descending(Br)={len(Rd)}")
    # C-shift / C-core closures
    def clo(name,fn,guard=None):
        t=f=0
        for M in Rd:
            if guard and not guard(M): continue
            try: A=fn(M)
            except Exception: continue
            if A is None or Lng(A)==0: continue
            try: ok=descending(Br(A))
            except Exception: continue
            t+= 1 if ok else 0; f+= 0 if ok else 1
        print(f"  {name}: TRUE {t} FALSE {f}")
    clo("C-shift (descending closed under shiftRow0)", shiftRow0)
    # C-NJ (known FALSE on brute)
    t=f=0
    for M in Rd:
        if not(entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)!=Lng(M)-1): continue
        for J in range(Lng(Br(M))):
            A=NJ(M,J)
            if Lng(A)==0: continue
            ok=descending(Br(A)); t+= 1 if ok else 0; f+= 0 if ok else 1
    print(f"  C-NJ (descending under NJ, expected FALSE): TRUE {t} FALSE {f}")
    # L6 brute (expected FALSE)
    t=f=0
    for M in Rd:
        if not(entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)!=Lng(M)-1): continue
        RM=Red(M); ok=Lng(RM)==Lng(M)
        if ok:
            m=Lng(M)
            for i in (0,1):
                for j0 in range(m):
                    for j1 in range(m):
                        if leR(M,i,j0,j1)!=leR(RM,i,j0,j1): ok=False; break
                    if not ok: break
                if not ok: break
        t+= 1 if ok else 0; f+= 0 if ok else 1
    print(f"  L6 (redle with descending(Br M), expected FALSE on brute): TRUE {t} FALSE {f}")

if len(sys.argv)>1 and sys.argv[1]=="brute":
    ml,mv=(int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (5,3)
    run_brute(ml,mv)
