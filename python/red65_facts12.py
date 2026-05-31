#!/usr/bin/env python3
"""§6.5-B verification, CORRECTED domain.

KEY: standard monoT terms always have m10=entry(M,1,0)=0, so the m10>0 mono
branch (where N, jN, the dead branch, and facts 1/2/3 live) NEVER fires on a
top-level standard input -- only on RECURSIVE sub-call arguments inside Red.

So we (1) instrument Red over all standard inputs (gen_std) and collect every
m10>0 mono sub-call argument M' actually reached; (2) ALSO directly enumerate
m10>0 mono terms (the article's M in PT_PS with m10>0, faithfully: monoT M and
m10>0); and test facts 1/2/3 on BOTH populations, rank-stratified."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, P, TrMax, Br,
                       FirstNodes, Joints, THE_nextR, diagSeq, IncrFirst,
                       funpow, seg, is_standard, fmt, leR, Red, reduced)
from d1pos_j0j1red_search import gen_std

def rankL(M): return Lng(M)
def valM(M): return max((max(a,b) for (a,b) in M), default=0)
def Nof(M):
    m10=entry(M,1,0)
    return Red(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M))

# ---- collect every m10>0 mono sub-call argument reached by Red ----
reached=[]
def Red_collect(M, depth=0):
    if depth>300: raise RuntimeError("deep")
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M): out+=Red_collect(blk,depth+1)
        return out
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1: return diagSeq(m10,m10+j1)
        out=diagSeq(0,j1p); b=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(b)):
            br10=entry(b[J],1,0)
            np=0 if br10==0 else THE_nextR(M,1,fn[J])+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
            out+=funpow(IncrFirst,eJ,Red_collect(NJ,depth+1))
        return out
    if m10==0:
        core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
        return Red_collect(core,depth+1)
    # m10>0 mono branch: THIS M is a fact-1/2/3 witness
    reached.append(M)
    N=Red_collect(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),depth+1)
    jN=Lng(N)-1; sg=seg(N,m10,jN)
    if m10<=jN and len(sg)>0 and monoT(sg):
        return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
    return M

def gen_mono_m10pos(maxlen, maxval):
    """Directly enumerate monoT terms with m10>0 (faithful 'M in PT_PS, m10>0':
    we relax standardness since m10>0 monoT terms are exactly the recursion
    arguments and are never themselves standard). Build by brute pairseq enum."""
    import itertools
    cells=list(itertools.product(range(maxval+1), repeat=2))
    out=[]
    for L in range(2,maxlen+1):
        for tup in itertools.product(cells, repeat=L):
            M=list(tup)
            if entry(M,1,0)>0 and monoT(M):
                out.append(M)
    return out

def strat_add(strat,M,ok):
    r,v=rankL(M),valM(M); strat.setdefault((r,v),[0,0])
    strat[(r,v)][0 if ok else 1]+=1

def print_strat(strat,labels=('true','false')):
    print(f"  rank(=Lng) x val : [{labels[0]}/{labels[1]}/total]")
    for k in sorted(strat):
        t,f=strat[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: {t}/{f}/{t+f}")

def fact1(M):
    return Lng(Nof(M))==Lng(M)+entry(M,1,0)
def fact2(M):
    m10=entry(M,1,0); N=Nof(M); LM=Lng(M); LN=Lng(N)
    for i in (0,1):
        for j in range(LM):
            for jp in range(LM):
                lhs=leR(M,i,j,jp)
                if j+m10<LN and jp+m10<LN: rhs=leR(N,i,j+m10,jp+m10)
                else: rhs=None
                if rhs is None:
                    if lhs: return False,(i,j,jp,'OOB')
                    continue
                if lhs!=rhs: return False,(i,j,jp,lhs,rhs)
    return True,None
def fact3(M):
    m10=entry(M,1,0); N=Nof(M); jN=Lng(N)-1; sg=seg(N,m10,jN)
    return (m10<=jN) and len(sg)>0 and monoT(sg), (m10,jN,fmt(sg),fmt(N))

def run_on(pop, name):
    print(f"\n##### population [{name}]  size={len(pop)} #####")
    s1={};t1=f1=0;ce1=[]
    s2={};t2=f2=0;ce2=[]
    s3={};al=dd=0;ce3=[]
    for M in pop:
        o1=fact1(M); strat_add(s1,M,o1)
        if o1: t1+=1
        else:
            f1+=1
            if len(ce1)<6: ce1.append((fmt(M),entry(M,1,0),Lng(M),Lng(Nof(M))))
        o2,c2=fact2(M); strat_add(s2,M,o2)
        if o2: t2+=1
        else:
            f2+=1
            if len(ce2)<6: ce2.append((fmt(M),c2,fmt(Nof(M))))
        o3,c3=fact3(M); strat_add(s3,M,o3)
        if o3: al+=1
        else:
            dd+=1
            if len(ce3)<8: ce3.append((fmt(M),c3))
    print(f"FACT1 Lng(N)=Lng(M)+m10:  TRUE={t1} FALSE={f1} TOTAL={t1+f1}")
    print_strat(s1)
    for c in ce1: print("  F1-CE:",c)
    print(f"FACT2 ancestor index-shift: TRUE={t2} FALSE={f2} TOTAL={t2+f2}")
    print_strat(s2)
    for c in ce2: print("  F2-CE:",c)
    print(f"FACT3 dead-branch alive(cond holds)/dead: alive={al} dead={dd} TOTAL={al+dd}")
    print_strat(s3, labels=('alive','dead'))
    for c in ce3: print("  F3-DEAD-CE:",c)

def main():
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,5,7)
    Ms=gen_std(maxlen,maxval,KMAX)
    print(f"# gen_std standard inputs: {len(Ms)} (maxlen={maxlen} maxval={maxval} KMAX={KMAX})")
    for M in Ms:
        try: Red_collect(M)
        except RuntimeError: pass
    # dedup reached
    seen={}; uniq=[]
    for M in reached:
        k=fmt(M)
        if k not in seen: seen[k]=1; uniq.append(M)
    print(f"# m10>0 mono sub-call args reached (dedup): {len(uniq)} (raw {len(reached)})")
    run_on(uniq, "A: m10>0 mono sub-call args reached by Red over standard inputs")

    # direct brute enum of m10>0 mono terms (smaller maxlen to keep tractable)
    bl,bv=(int(sys.argv[4]),int(sys.argv[5])) if len(sys.argv)>5 else (6,5)
    direct=gen_mono_m10pos(bl,bv)
    print(f"\n# direct brute m10>0 monoT terms (maxlen={bl} maxval={bv}): {len(direct)}")
    run_on(direct, "B: direct brute-enumerated m10>0 monoT terms")

if __name__=='__main__':
    main()
