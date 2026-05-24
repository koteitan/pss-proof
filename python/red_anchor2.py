#!/usr/bin/env python3
"""Test the 5 corollaries on ANCHORED slices (le0(S,a,b)) for two source classes:
  (1) standard S  (expansion of diagonals = ST_PS by definition; no yaBMS needed)
  (2) reduced+mono S  (enumerated, Red S == S and monoT S)
These cover the two M-domains seen at §7 use-sites (ST_PS∩PT_PS and RT_PS∩PT_PS)."""
import os, itertools
from red_model import (Red, fmt, Lng, entry, P, monoT, zeroT, leR, le0, oper, diagSeq, seg)

def c_le(M):
    R=Red(M);n=Lng(M)
    return all(leR(M,i,a,b)==leR(R,i,a,b) for i in(0,1) for a in range(n) for b in range(n))
def c_monoT(M): return monoT(M)==monoT(Red(M))
def c_P(M): return P(Red(M))==[Red(b) for b in P(M)]
def c_idem(M): return Red(Red(M))==Red(M)
def c_oper(M): return all(oper(Red(M),n)==Red(oper(M,n)) for n in (1,2,3))
CORS={"Red_le":c_le,"Red_monoT":c_monoT,"P_Red":c_P,"Red_idem":c_idem,"Red_oper":c_oper}

def gen_standard(maxv=3, steps=5, ns=(1,2,3,4), maxlen=11):
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
    return out  # ST_PS by construction

def gen_reduced_mono(maxlen=4,maxe=2):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    out=[]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            M=list(M)
            if monoT(M) and Red(M)==M: out.append(M)
    return out

def test(sources,label):
    counts={k:[0,0,None] for k in CORS}; seen=set()
    for S in sources:
        n=Lng(S)
        for a in range(n):
            for b in range(a,n):
                if not le0(S,a,b): continue
                N=seg(S,a,b); t=tuple(N)
                if t in seen: continue
                seen.add(t)
                for k,f in CORS.items():
                    counts[k][0]+=1
                    try: ok=f(N)
                    except Exception: ok=False
                    if not ok:
                        counts[k][1]+=1
                        if counts[k][2] is None: counts[k][2]=f"{fmt(N)} (slice of {fmt(S)})"
    print(f"\n== {label}: {len(sources)} sources, {len(seen)} distinct anchored slices ==")
    for k,(t,fl,ex) in counts.items():
        print(f"  {k:10s} tested={t:5d} FAIL={fl:4d} sound={fl==0}  {('ex='+ex) if ex else ''}")

def main():
    os.chdir(os.path.dirname(__file__))
    stds=gen_standard()
    test(stds,"anchored slices of STANDARD")
    rms=gen_reduced_mono()
    test(rms,"anchored slices of REDUCED+MONO")

if __name__=="__main__": main()
