#!/usr/bin/env python3
"""r44 diagnostic: WHY does qlt (q < whole) hold?  Mechanism split."""
import sys, time, signal, random
from collections import deque
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, oper, diagSeq, monoT, Br, entry
import trans_model as tm
import buchholz as bu
sys.setrecursionlimit(200000); random.seed(7)
_torig=tm.Trans; _tmemo={}
def Trans(M, depth=0):
    k=tuple(M); r=_tmemo.get(k)
    if r is None: r=_torig(M,depth); _tmemo[k]=r
    return r
tm.Trans=Trans
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s,f:(_ for _ in()).throw(TO()))
seeds=[diagSeq(u,u+d) for u in range(0,8) for d in range(1,9)]
seen=set(); q=deque(seeds); t0=time.time()
while q and time.time()-t0<40 and len(seen)<250000:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if Lng(M)<=36:
        for nn in range(1,7):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and len(M2)<=40 and tuple(M2) not in seen: q.append(M2)
vis=list(seen); random.shuffle(vis)
R=dict(app=0, qz=0, psne_qltps=0, psne_notqltps=0, pse=0, pse_xgthead=0,
       hd_ge=0, notbrle=0)
ex_notprefix=[]  # ps!=[], q not< Trm ps  (prefix does NOT dominate)
checked=set(); tC=time.time()
for E in vis:
    if time.time()-tC>160: break
    for kk in range(3,len(E)+1):
        M=list(E[:kk]); km=tuple(M)
        if km in checked: continue
        checked.add(km)
        if not(monoT(M) and Br(M)!=[]) or len(M)-1<=1: continue
        v0=entry(M,1,0)
        signal.alarm(6)
        try: TM=Trans(M); signal.alarm(0)
        except (TO,Exception): signal.alarm(0); break
        if len(TM[1])!=1 or TM[1][0][1]!=v0 or not TM[1][0][2][1]: continue
        lM=bucOf(TM[1][0][2]); ps=lM[:-1]; x,qq=lM[-1][1],lM[-1][2]
        if not (v0<=x): continue
        R['app']+=1
        if qq==[]:
            R['qz']+=1; continue
        # qq != []
        hq = qq[0][1]   # head of q's first principal
        if x >= hq: R['hd_ge']+=1
        if ps:
            if bu.lt_term(qq, ps): R['psne_qltps']+=1
            else:
                R['psne_notqltps']+=1
                if len(ex_notprefix)<8: ex_notprefix.append((len(M),M,v0,x,qq,ps))
        else:
            R['pse']+=1
            if bu.lt_term(qq, [('D',x,qq)]): R['pse_xgthead']+=1
print("APPLICABLE(v0<=x) =%d" % R['app'])
print(" q=0_B (trivial)          : %d" % R['qz'])
print(" q!=0_B                    : %d" % (R['app']-R['qz']))
print("   ps!=[] & q<Trm ps (prefix dominates): %d" % R['psne_qltps'])
print("   ps!=[] & q NOT< Trm ps             : %d" % R['psne_notqltps'])
print("   ps=[]  (whole=Dpt x q)             : %d" % R['pse'])
print("      of which q<Dpt x q (x-head wins): %d" % R['pse_xgthead'])
print(" [aux] q!=0_B & x>=head(q)  : %d / %d" % (R['hd_ge'], R['app']-R['qz']))
if ex_notprefix:
    print("== ps!=[] & q NOT< Trm ps  (prefix does NOT dominate qlt):")
    for L,M,v0,x,qq,ps in ex_notprefix:
        print("  Lng=%d v0=%d x=%d q=%s ps=%s" % (L,v0,x,qq,ps))
