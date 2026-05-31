#!/usr/bin/env python3
"""Extended dead-branch[20]/[19] reachability over gen_std standard inputs
(reaches higher rank/val than brute all_pairseqs). Instruments Red over the
input AND all recursive sub-calls. Rank-stratified by Lng of the *top* input.
Reports m10>0 reached vs dead taken, both summing."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, zeroT, multiT, monoT, P, TrMax, Br,
                       FirstNodes, Joints, THE_nextR, diagSeq, IncrFirst,
                       funpow, seg, fmt)
from d1pos_j0j1red_search import gen_std

stats={'m10pos':0,'dead':0,'examples':[]}
def Red_inst(M, depth=0):
    if depth>300: raise RuntimeError("deep "+fmt(M))
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M): out+=Red_inst(blk,depth+1)
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
            out+=funpow(IncrFirst,eJ,Red_inst(NJ,depth+1))
        return out
    if m10==0:
        core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
        return Red_inst(core,depth+1)
    stats['m10pos']+=1
    N=Red_inst(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),depth+1)
    jN=Lng(N)-1; sg=seg(N,m10,jN)
    if m10<=jN and len(sg)>0 and monoT(sg):
        return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
    stats['dead']+=1
    if len(stats['examples'])<10: stats['examples'].append((fmt(M),fmt(N),m10,jN))
    return M

if __name__=='__main__':
    maxlen,maxval,KMAX=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (12,5,7)
    Ms=gen_std(maxlen,maxval,KMAX)
    perL={}
    for M in Ms:
        r=Lng(M)
        before_m=stats['m10pos']; before_d=stats['dead']
        try: Red_inst(M)
        except RuntimeError as e: print("DEEP",fmt(M),e)
        perL.setdefault(r,[0,0])
        perL[r][0]+=stats['m10pos']-before_m
        perL[r][1]+=stats['dead']-before_d
    print(f"# gen_std maxlen={maxlen} maxval={maxval} KMAX={KMAX}; standard inputs={len(Ms)}")
    print(f"m10>0 reached: {stats['m10pos']}   dead taken: {stats['dead']}   alive: {stats['m10pos']-stats['dead']}")
    print("rank(=Lng of top input) x [m10pos / dead / alive]:")
    for r in sorted(perL):
        m,d=perL[r]; print(f"  L={r:2d}: m10pos={m}  dead={d}  alive={m-d}")
    if stats['dead']:
        print("DEAD COUNTEREXAMPLES (M,N,m10,jN):")
        for e in stats['examples']: print("  ",e)
    else:
        print("=> dead-branch UNREACHABLE on all gen_std standard inputs + sub-calls")
