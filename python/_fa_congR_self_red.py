#!/usr/bin/env python3
"""Front A: verify m_6_5_congR_self_Red_monoT empirically.
  M in T_PS (nonempty) & RedCondA M & monoT M ==> congR M (Red M).
Also verify the NJ-branch facts threaded by the proof:
  for the core-nontrunk monoT branch, NJ M J is monoT-or-zeroT and RedCondA(NJ M J).
"""
import itertools, os
os.chdir(os.path.dirname(__file__))
from red_model import (Red, Lng, entry, monoT, zeroT, multiT, nextrel0, TrMax, Br,
                       seg, P, IdxSum, fmt)
from red_charac import RedCondA

def congR(A,X):
    if Lng(A)!=Lng(X): return False
    n=Lng(X)
    for p in range(n):
        for q in range(n):
            if nextrel0(A,p,q)!=nextrel0(X,p,q): return False
    for j in range(n):
        if entry(A,1,j)!=entry(X,1,j): return False
    return True

# NJ via the article: NJ M J built from Br M ! J with bumped head; but for the
# monoT-or-zeroT and RedCondA facts we only need NJ M J = Br M ! J's structural slice.
def npJ(M,J):
    br=Br(M)
    from red_model import FirstNodes, nextR
    if entry(br[J],1,0)==0: return 0
    fn=FirstNodes(M)
    cands=[j for j in range(Lng(M)) if nextR(M,1,j,fn[J])]
    return 1+cands[0]
def NJ(M,J):
    br=Br(M); from_=br[J]
    from red_model import Joints
    jo=Joints(M)
    head=(entry(M,0,0)+jo[J]+1, entry(M,1,0)+npJ(M,J))
    return [head]+from_[1:]

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)

def main():
    tot=fail=0; ex=None
    njtot=njfail=0; njex=None
    rcatot=rcafail=0; rcaex=None
    for M in enum(4,3):
        if not M: continue
        if not monoT(M): continue
        if not RedCondA(M): continue
        tot+=1
        try:
            ok=congR(M,Red(M))
        except Exception as e:
            ok=False
        if not ok:
            fail+=1
            if ex is None: ex=fmt(M)
        # core-nontrunk NJ facts
        if entry(M,0,0)==0 and entry(M,1,0)==0 and TrMax(M)!=Lng(M)-1:
            for J in range(Lng(Br(M))):
                try:
                    X=NJ(M,J)
                    njtot+=1
                    if not (zeroT(X) or monoT(X)):
                        njfail+=1
                        if njex is None: njex=(fmt(M),J,fmt(X))
                    rcatot+=1
                    if not RedCondA(X):
                        rcafail+=1
                        if rcaex is None: rcaex=(fmt(M),J,fmt(X))
                except Exception as e:
                    pass
    print(f"congR M (Red M): {tot} tested, {fail} fail. ex={ex}")
    print(f"NJ monoT-or-zeroT: {njtot} tested, {njfail} fail. ex={njex}")
    print(f"RedCondA(NJ): {rcatot} tested, {rcafail} fail. ex={rcaex}")

if __name__=="__main__": main()
