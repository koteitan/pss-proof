#!/usr/bin/env python3
"""Audit for m_6_5_Red_oper_final and its two bricks:
  (1) oper-rebase commutation: oper(rebase(N,c,m),n) == rebase(oper(N,n),c,m)
  (2) row0 floor: all fst of oper(N,n) >= c = entry(N,0,0)
  (3) Red_oper: oper(Red(N),n) == Red(oper(N,n))
over anchored mono slices N (sources: standard expansions + reduced mono).
Result 2026-06-11: 1824/1824 each, 0 fail."""
import itertools
from red_model import Red, Lng, entry, monoT, zeroT, le0, oper, diagSeq, seg

def rebase(M, c, m): return [(a - c + m, b) for (a,b) in M]

def gen_standard(maxv=3, steps=4, ns=(1,2,3), maxlen=9):
    seen=set(); fr=[]
    for v in range(maxv+1):
        M=diagSeq(0,v); fr.append(M); seen.add(tuple(M))
    out=list(fr)
    for _ in range(steps):
        nf=[]
        for M in fr:
            for n in ns:
                M2=oper(M,n); t=tuple(M2)
                if t not in seen and 0<len(M2)<=maxlen: seen.add(t); nf.append(M2); out.append(M2)
        fr=nf
    return out

def gen_reduced_mono(maxlen=4,maxe=3):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    out=[]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            M=list(M)
            if monoT(M) and Red(M)==M: out.append(M)
    return out

def main():
    c1=c2=c3=0; seen=set()
    for S in gen_standard()+gen_reduced_mono():
        nS=Lng(S)
        for a in range(nS):
            for b in range(a,nS):
                if not le0(S,a,b): continue
                N=seg(S,a,b); t=tuple(N)
                if t in seen: continue
                seen.add(t)
                if not monoT(N): continue
                c=entry(N,0,0); m=entry(N,1,0)
                for n in (1,2,3):
                    Nn=oper(N,n)
                    assert oper(rebase(N,c,m),n)==rebase(Nn,c,m), ('commute',N,n)
                    c1+=1
                    assert all(p[0]>=c for p in Nn), ('rowmin',N,n)
                    c2+=1
                    assert oper(Red(N),n)==Red(Nn), ('Red_oper',N,n)
                    c3+=1
    print('commute:',c1,'rowmin:',c2,'Red_oper:',c3,'all 0 fail')

if __name__=='__main__': main()
