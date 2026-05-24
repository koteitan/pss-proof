#!/usr/bin/env python3
"""Empirically audit §6.7 (standard form) closure propositions, on ENUMERATED
standard sequences (filtered by yaBMS, complete in the small range):

  std_P_block   : M standard ⟹ every block of P M is standard           (1364)
  std_prefix    : M standard, j1'≤Lng-1 ⟹ seg M 0 j1' standard          (1394)
  std_slice_Br  : M standard, j0'<j1'≤Lng-1, (0,j0')≤_M(0,j1') ⟹
                  seg M j0' j1' is mono and Br(seg) is descending        (1422)
"""
import itertools, os
from red_model import (fmt, Lng, entry, P, monoT, le0, Br, seg, is_standard)

def descending(Q):
    for a in range(len(Q)):
        for b in range(a,len(Q)):
            if entry(Q[a],0,0) < entry(Q[b],0,0): return False
            if entry(Q[a],0,0)==entry(Q[b],0,0) and entry(Q[a],1,0) < entry(Q[b],1,0): return False
    return True

def std_P_block(M):
    return all(is_standard(b) for b in P(M))
def std_prefix(M):
    n=Lng(M)
    return all(is_standard(seg(M,0,b)) for b in range(n))
def std_slice_Br(M):
    n=Lng(M); ok=True
    for a in range(n):
        for b in range(a+1,n):
            if le0(M,a,b):
                N=seg(M,a,b)
                if not monoT(N): return False
                if not descending(Br(N)): return False
    return ok
PROPS={"std_P_block":std_P_block,"std_prefix":std_prefix,"std_slice_Br":std_slice_Br}

def enum_std(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    out=[]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            M=list(M)
            if is_standard(M): out.append(M)
    return out

def main():
    os.chdir(os.path.dirname(__file__))
    stds=enum_std(4,2)
    print(f"enumerated standard sequences (Lng<=4, e<=2): {len(stds)}")
    res={k:[0,0,None] for k in PROPS}
    for M in stds:
        for k,f in PROPS.items():
            try: ok=f(M)
            except Exception: ok=False
            res[k][0]+=1
            if not ok:
                res[k][1]+=1
                if res[k][2] is None: res[k][2]=fmt(M)
    for k,(p,fl,ex) in res.items():
        tag="OK(standard)" if fl==0 else f"FALSE (ex={ex})"
        print(f"  {k:14s} tested={p:4d} FAIL={fl:3d}  {tag}")

if __name__=="__main__": main()
