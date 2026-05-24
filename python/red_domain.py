#!/usr/bin/env python3
"""Test whether the §6.5 corollaries hold on the class of sequences §7 actually
feeds them: slices of standard / reduced sequences (the N's).
Candidate domains:
  H_std  = contiguous slices of standard seqs
  H_red  = contiguous slices of reduced seqs
each also tested 'mod row0 additive shift' (le/Red_le is row0-shift invariant)."""
import itertools, os
from red_model import (Red, fmt, Lng, entry, P, multiT, monoT, zeroT, leR, oper,
    IncrFirst, diagSeq, is_standard, reduced, Pred)

# ---- the 5 propositions ----
def c_Red_le(M):
    R=Red(M); n=Lng(M)
    return all(leR(M,i,a,b)==leR(R,i,a,b) for i in(0,1) for a in range(n) for b in range(n))
def c_Red_monoT(M): return monoT(M)==monoT(Red(M))
def c_P_Red(M): return P(Red(M))==[Red(b) for b in P(M)]
def c_Red_idem(M): return Red(Red(M))==Red(M)
def c_Red_oper(M):
    return all(oper(Red(M),n)==Red(oper(M,n)) for n in (1,2,3))
CORS={"Red_le":c_Red_le,"Red_monoT":c_Red_monoT,"P_Red":c_P_Red,"Red_idem":c_Red_idem,"Red_oper":c_Red_oper}

def norm0(M):
    m=min(a for a,b in M); return tuple((a-m,b) for a,b in M)

def gen_standard(maxv=3, steps=4, ns=(1,2,3,4), maxlen=9):
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
    return [M for M in out if is_standard(M)]

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)

def slice_set(seqs, mod0):
    H=set()
    for S in seqs:
        n=len(S)
        for a in range(n):
            for b in range(a,n):
                sl=S[a:b+1]
                H.add(norm0(sl) if mod0 else tuple(sl))
    return H

def main():
    os.chdir(os.path.dirname(__file__))
    stds=gen_standard()
    reds=[M for M in enum(4,2) if reduced(M)]
    print(f"standard={len(stds)}  reduced(enum≤4,≤2)={len(reds)}")
    domains={
      "slice_of_standard":      slice_set(stds, False),
      "slice_of_standard_mod0": slice_set(stds, True),
      "slice_of_reduced":       slice_set(reds, False),
      "slice_of_reduced_mod0":  slice_set(reds, True),
    }
    for dn,H in domains.items():
        print(f"\n== domain {dn}  (|H|={len(H)}) ==")
        for cn,cf in CORS.items():
            inH=passC=failC=0; ex=None
            for M in enum(4,2):
                key=norm0(M) if dn.endswith("mod0") else tuple(M)
                if key not in H: continue
                inH+=1
                try: ok=cf(M)
                except Exception: ok=False
                if ok: passC+=1
                else:
                    failC+=1
                    if ex is None: ex=fmt(M)
            print(f"  {cn:10s} inH={inH:5d} pass={passC:5d} FAIL={failC:4d} sound={failC==0} {('ex='+ex) if ex else ''}")

if __name__=="__main__": main()
