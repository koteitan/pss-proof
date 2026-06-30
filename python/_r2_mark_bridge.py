#!/usr/bin/env python3
"""Map the §8.7 R2 equal-head q,qb to §7.4 Mark / branch-Trans components and
find which DONE order relation makes q <= qb hold.

For each equal-head case-34 sample, with last principal D_x q and previous D_x qb:
  - identify branches J1, J1-1 (and first-node basepoints)
  - compute Trans of those branches, bpHeadT
  - compute Mark M at column indices, see if q/qb = bpHeadT(Mark ...) or Trans(branch)
  - test relations: leBT(q,qb), MarkedB nesting between the corresponding Mark/Trans
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, monoT, Br, FirstNodes, Joints, P, reduced as red_reduced
from trans_model import (Trans, Pred, reduced, Mark, bpHeadT, bpHeadV, flatBT,
                         scb_decomps, PB)
from fast_pss import diagSeq, oper

ZB=('T',[])
def lessBT(a,b):
    pa,pb=a[1],b[1]
    if not pa: return bool(pb)
    if not pb: return False
    return lessBP(pa[0],pb[0]) or (pa[0]==pb[0] and lessBT(('T',pa[1:]),('T',pb[1:])))
def lessBP(p,q):
    u,a=p[1],p[2]; v,b=q[1],q[2]; return u<v or (u==v and lessBT(a,b))
def leBT(a,b): return lessBT(a,b) or a==b
def markedB(t,c):
    return len(scb_decomps(t, flatBT(c)))>0

def gen(ms,mn,ml,r):
    seen=set();fr=[]
    for a in range(ms+1):
        for b in range(a,ms+1):
            s=tuple(diagSeq(a,b))
            if s and s not in seen: seen.add(s);fr.append(list(s))
    for _ in range(r):
        nf=[]
        for M in fr:
            for n in range(1,mn+1):
                Mp=oper(M,n)
                if 1<=Lng(Mp)<=ml:
                    t=tuple(Mp)
                    if t not in seen: seen.add(t);nf.append(Mp)
        fr=nf
        if not fr:break
    return [list(t) for t in seen]

def main():
    Ms=gen(4,4,11,4)
    n=0
    cnt={'q_is_TransBrJ1':0,'qb_is_TransBrJ1m1':0,
         'q_is_MarkFN_J1':0,'qb_is_MarkFN_J1m1':0,
         'markedB_qb_q':0,'markedB_q_qb':0,'leBT_q_qb':0,
         'q_is_bpHeadT_TransBrJ1':0,'qb_is_bpHeadT_TransBrJ1m1':0}
    ex=[]
    for M in Ms:
        if Lng(M)<1 or not red_reduced(M) or not monoT(M) or Br(M)==[]: continue
        if not (Lng(M)-1>1): continue
        try: tM=Trans(M);tP=Trans(Pred(M))
        except: continue
        if tM==ZB or tP==ZB or len(tM[1])!=1 or len(tP[1])!=1: continue
        psM=tM[1][0][2][1]; psP=tP[1][0][2][1]
        if len(psM)<2 or len(psP)<1 or psM[:-1]!=psP[:-1]: continue
        last=psM[-1];prev=psM[-2];lp=psP[-1]
        x,q=last[1],last[2]; xp=lp[1]; hd,qb=prev[1],prev[2]
        if x!=xp or x!=hd: continue
        n+=1
        BrM=Br(M); FN=FirstNodes(M); J1=len(BrM)-1
        # branch Trans
        try:
            tbrJ1=Trans(BrM[J1]); tbrJ1m1=Trans(BrM[J1-1])
        except: tbrJ1=tbrJ1m1=None
        # last principal D_x q should equal Trans(last branch) (a single principal)
        Dxq=('T',[last]); Dxqb=('T',[prev])
        if tbrJ1==Dxq: cnt['q_is_TransBrJ1']+=1
        if tbrJ1m1==Dxqb: cnt['qb_is_TransBrJ1m1']+=1
        if tbrJ1 is not None and bpHeadT(tbrJ1)==q: cnt['q_is_bpHeadT_TransBrJ1']+=1
        if tbrJ1m1 is not None and bpHeadT(tbrJ1m1)==qb: cnt['qb_is_bpHeadT_TransBrJ1m1']+=1
        # Mark at first-node basepoints
        try:
            mkJ1=Mark(M, FN[J1]); mkJ1m1=Mark(M, FN[J1-1])
        except: mkJ1=mkJ1m1=None
        if mkJ1==Dxq: cnt['q_is_MarkFN_J1']+=1
        if mkJ1m1==Dxqb: cnt['qb_is_MarkFN_J1m1']+=1
        # order/nesting relations on the principals
        if markedB(Dxqb,Dxq): cnt['markedB_qb_q']+=1
        if markedB(Dxq,Dxqb): cnt['markedB_q_qb']+=1
        if leBT(q,qb): cnt['leBT_q_qb']+=1
        if len(ex)<4:
            ex.append({'M':M,'x':x,'q':q,'qb':qb,
                       'TransBrJ1':tbrJ1,'TransBrJ1m1':tbrJ1m1,
                       'MarkFN_J1':mkJ1,'MarkFN_J1m1':mkJ1m1,
                       'FN':FN,'J1':J1})
    print(f"equal-head case34 samples: {n}")
    for k,v in cnt.items(): print(f"  {k}: {v}")
    print("EXAMPLES:")
    for e in ex:
        print("  M=",e['M'])
        print("    x,q,qb =",e['x'],e['q'],e['qb'],"  FN=",e['FN'],"J1=",e['J1'])
        print("    Trans(BrJ1)=",e['TransBrJ1'],"  Trans(BrJ1-1)=",e['TransBrJ1m1'])
        print("    Mark(M,FN[J1])=",e['MarkFN_J1'],"  Mark(M,FN[J1-1])=",e['MarkFN_J1m1'])

if __name__=='__main__': main()
