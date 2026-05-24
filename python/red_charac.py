#!/usr/bin/env python3
"""Find a structural predicate C that characterizes Red_le PASS, and test
whether C is closed under Red's recursive calls."""
import itertools
from red_model import (Red, red_le_holds, fmt, Lng, entry, P, Pcut, multiT, monoT,
    zeroT, le0, leR, nextR, nextrel0, nextrel1, TrMax, Br, FirstNodes, Joints,
    diagSeq, IncrFirst, funpow, seg)

def hasParent(M,i,j1):
    return sum(1 for j0 in range(Lng(M)) if nextR(M,i,j0,j1))==1
def parent(M,i,j1):
    for j0 in range(Lng(M)):
        if nextR(M,i,j0,j1): return j0
    return None

def RedCondA(M):
    for i in (0,1):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1):
                p=parent(M,i,j1)
                if entry(M,i,p)+1!=entry(M,i,j1): return False
    return True

def RedCondB(M):
    for j1 in range(Lng(M)):
        if (not hasParent(M,0,j1)):
            if entry(M,0,j1)!=entry(M,1,j1): return False
    return True

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            yield list(M)

PREDS={
  "RedCondB": RedCondB,
  "RedCondA": RedCondA,
  "A&B": lambda M: RedCondA(M) and RedCondB(M),
}

def main():
    maxlen=4; maxe=2
    rows={k:{"pass_C":0,"fail_C":0,"pass_notC":0,"fail_notC":0} for k in PREDS}
    allM=list(enum(maxlen,maxe))
    passset=[]
    for M in allM:
        r,_=red_le_holds(M)
        p=(r is True)
        if p: passset.append(M)
        for k,f in PREDS.items():
            c=f(M)
            key=("pass" if p else "fail")+("_C" if c else "_notC")
            rows[k][key]+=1
    print(f"total={len(allM)} pass={len(passset)}")
    for k,d in rows.items():
        # sound means fail_C==0 (C => pass). exact means pass_notC==0 too.
        print(f"{k:10s} pass&C={d['pass_C']:5d} fail&C={d['fail_C']:5d}  pass&!C={d['pass_notC']:5d} fail&!C={d['fail_notC']:5d}  sound(C=>pass)={d['fail_C']==0} exact={d['fail_C']==0 and d['pass_notC']==0}")

if __name__=="__main__":
    import os; os.chdir(os.path.dirname(__file__)); main()
