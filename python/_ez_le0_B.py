#!/usr/bin/env python3
"""Does le0 N z j1 (alone) imply Ez? And does the row-0 +1 ramp on [z,j1] hold
whenever z is interior on the row-0 trunk to j1?  TASK B reflection sharpening."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,le0,le1,nextrel1,idx1,hasParent,parent,oper,diagSeq,nextrel0)

def gen_closure(depth,umax,vmax,maxlen,max_n):
    seen=set(); frontier=[]
    for u in range(0,umax+1):
        for v in range(u,vmax+1):
            d=tuple(map(tuple,diagSeq(u,v)))
            if d not in seen and len(d)<=maxlen:
                seen.add(d); frontier.append([list(x) for x in d])
    allM=list(frontier)
    for _ in range(depth):
        newf=[]
        for M in frontier:
            for n in range(1,max_n+1):
                N=oper([tuple(x) for x in M],n); t=tuple(map(tuple,N))
                if t not in seen and 1<len(t)<=maxlen:
                    seen.add(t); newf.append([list(x) for x in N]); allM.append([list(x) for x in N])
        frontier=newf
        if not frontier: break
    return allM

def check(allM):
    # le0 N z j1 ==> Ez ?
    tot=0; fail=[]
    # consecutive step on row0 trunk: le0 N z j1 ==> for z<=x<j1, entry0(x+1)=entry0(x)+1 ?
    stot=0; sfail=[]
    for M in allM:
        n=Lng(M)
        if n<2: continue
        j1=n-1
        for z in range(0,j1):
            if not le0(M,z,j1): continue
            tot+=1
            Ez=(entry(M,0,j1)==entry(M,0,z)+(j1-z))
            if not Ez: fail.append((tuple(map(tuple,M)),z,j1,entry(M,0,j1),entry(M,0,z)+(j1-z)))
    return tot,fail

if __name__=='__main__':
    for cfg in [(5,3,6,14,4),(5,2,5,16,5)]:
        allM=gen_closure(*cfg)
        tot,fail=check(allM)
        print(f"cfg{cfg}: closure={len(allM)}  le0 z j1 => Ez : {tot} cases, {len(fail)} fails")
        for f in fail[:6]: print("    FAIL",f)
