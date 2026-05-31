#!/usr/bin/env python3
"""Standalone direct-brute facts 1/2/3 on m10>0 monoT terms, flushing."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, diagSeq, IncrFirst, funpow, seg, leR, Red, fmt)

def Nof(M):
    m10=entry(M,1,0)
    return Red(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M))
def rankL(M): return Lng(M)
def valM(M): return max((max(a,b) for (a,b) in M), default=0)

def fact1(M): return Lng(Nof(M))==Lng(M)+entry(M,1,0)
def fact2(M):
    m10=entry(M,1,0); N=Nof(M); LM=Lng(M); LN=Lng(N)
    for i in (0,1):
        for j in range(LM):
            for jp in range(LM):
                lhs=leR(M,i,j,jp)
                rhs=leR(N,i,j+m10,jp+m10) if (j+m10<LN and jp+m10<LN) else None
                if rhs is None:
                    if lhs: return False
                    continue
                if lhs!=rhs: return False
    return True
def fact3(M):
    m10=entry(M,1,0); N=Nof(M); jN=Lng(N)-1; sg=seg(N,m10,jN)
    return (m10<=jN) and len(sg)>0 and monoT(sg)

if __name__=='__main__':
    maxlen,maxval=(int(sys.argv[1]),int(sys.argv[2])) if len(sys.argv)>2 else (3,6)
    cells=list(itertools.product(range(maxval+1), repeat=2))
    s1={};s2={};s3={}; t1=f1=t2=f2=al=dd=0; n=0
    ce1=[];ce2=[];ce3=[]
    for L in range(2,maxlen+1):
        for tup in itertools.product(cells, repeat=L):
            M=list(tup)
            if entry(M,1,0)==0 or not monoT(M): continue
            n+=1
            r,v=rankL(M),valM(M)
            o1=fact1(M); s1.setdefault((r,v),[0,0]); s1[(r,v)][0 if o1 else 1]+=1
            if o1: t1+=1
            else:
                f1+=1
                if len(ce1)<6: ce1.append((fmt(M),entry(M,1,0),Lng(M),Lng(Nof(M))))
            o2=fact2(M); s2.setdefault((r,v),[0,0]); s2[(r,v)][0 if o2 else 1]+=1
            if o2: t2+=1
            else:
                f2+=1
                if len(ce2)<6: ce2.append(fmt(M))
            o3=fact3(M); s3.setdefault((r,v),[0,0]); s3[(r,v)][0 if o3 else 1]+=1
            if o3: al+=1
            else:
                dd+=1
                if len(ce3)<6: ce3.append((fmt(M),fmt(Nof(M))))
            if n%2000==0:
                print(f"... n={n} f1={f1} f2={f2} dead={dd}", flush=True)
    print(f"\n=== direct m10>0 monoT (maxlen={maxlen} maxval={maxval}) population={n} ===", flush=True)
    def pstr(s,lab):
        print(f"  by (Lng,val) [{lab}]:")
        for k in sorted(s):
            a,b=s[k]; print(f"    L={k[0]:2d} val={k[1]:2d}: {a}/{b}/{a+b}")
    print(f"FACT1 Lng(N)=Lng(M)+m10: TRUE={t1} FALSE={f1} TOTAL={t1+f1}", flush=True); pstr(s1,'true/false')
    for c in ce1: print("  F1-CE:",c)
    print(f"FACT2 ancestor index-shift: TRUE={t2} FALSE={f2} TOTAL={t2+f2}", flush=True); pstr(s2,'true/false')
    for c in ce2: print("  F2-CE:",c)
    print(f"FACT3 dead-branch alive/dead: alive={al} dead={dd} TOTAL={al+dd}", flush=True); pstr(s3,'alive/dead')
    for c in ce3: print("  F3-DEAD-CE:",c)
