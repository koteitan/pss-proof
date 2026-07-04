import sys, os, time, signal
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
import _r28_c4dx_producer as V
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg,
                       Br, FirstNodes, Joints, nextR, TrMax, fmt)
from trans_model import (ZB, Dpt, PB, bpHeadV, flatBT, _c2, Pred)
def leBT(a,b): return a==b or V.lessBT(a,b)
class St:
    def __init__(s): s.ok=0; s.bad=0; s.cex=[]
    def rec(s,g,i):
        if g: s.ok+=1
        else:
            s.bad+=1
            if len(s.cex)<5: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"
KEYS=('HB','BRNE','FNLAST','JLAST','JLT','DIAG','GT','LT','PIN','JPGE','LVLj1','LVLj0','LEFT','COVER')
R={'hosts':0,'to':0,'deep':0}
for k in KEYS: R[k]=St(); R[k+'D']=St()
def check(M):
    j1=Lng(M)-1; v1=entry(M,1,j1); j0=parent(M,0,j1)
    if j0 is None: return
    deep = Lng(M)>=9
    jm1=V.transJm1(M); t2=V.transT2(M); Rn=V.Red(seg(M,jm1,j1))
    R['hosts']+=1
    if deep: R['deep']+=1
    def rc(k,ok):
        R[k].rec(ok,(fmt(M),))
        if deep: R[k+'D'].rec(ok,(fmt(M),))
    rc('HB', all(leBT(Dpt(v1,ZB),c) for c in PB(t2)))
    vj0=entry(M,1,j0); rc('JPGE', vj0>=v1)
    brn=Br(Rn); rc('BRNE', len(brn)>=1)
    if len(brn)>=1:
        last=len(brn)-1; fn=FirstNodes(Rn); jj=Joints(Rn); tm=TrMax(Rn)
        rc('FNLAST', fn[last]==j1-jm1); rc('JLAST', jj[last]==j0-jm1)
        rc('JLT', 0<jj[last]<tm)
        e0=entry(Rn,0,fn[last]); e1=entry(Rn,1,fn[last])
        rc('DIAG', e0==e1); rc('GT', e0>e1); rc('LT', e0<e1)
        rc('COVER', e0>=e1)  # DIAG or GT covers everything?
        rc('LVLj1', entry(Rn,1,j1-jm1)==v1); rc('LVLj0', entry(Rn,1,j0-jm1)==vj0)
    c2=_c2(M,j1,j0,bpHeadV(V.Mark(Pred(M),jm1)),t2)
    rc('PIN', flatBT(V.Trans(seg(M,jm1,j1)))==flatBT(c2))
    Pt2=PB(t2)
    if Pt2: rc('LEFT', bpHeadV(Pt2[-1])==entry(M,1,j0))
pools=[]
for seed,mlen,cap,ns,um,vx in ((202,12,700,(1,2),2,6),(303,13,700,(1,2),2,7),
        (505,14,800,(1,2),3,8),(707,14,800,(1,2),4,8),(811,15,800,(1,2,3),4,9)):
    pools.append(('oper s%d'%seed, V.gen_oper(mlen,cap,seed,ns,um,vx)))
for seed,mlen,cap in ((41,10,400),(43,11,350),(47,12,300)):
    pools.append(('strad s%d'%seed, V.gen_straddle(mlen,cap,seed)))
for tag,pool in pools:
    nh=0; t1=time.time()
    for M in pool:
        if time.time()-t1>60: break
        j1=Lng(M)-1
        if j1<=1 or not monoT(M) or zeroT(M) or not hasParent(M,1,j1): continue
        if not V.reduced(M) or not V.condIV(M): continue
        nh+=1; signal.alarm(20)
        try: check(M)
        except (V.TO,RecursionError,ValueError,IndexError): R['to']+=1
        finally: signal.alarm(0)
    print(f'[{tag}] pool={len(pool)} condIV={nh} ({time.time()-t1:.0f}s)',flush=True)
print('hosts=%d deep=%d to=%d'%(R['hosts'],R['deep'],R['to']),flush=True)
for k in KEYS: print(f'{k:7s} all {str(R[k]):>10s}  deep {str(R[k+"D"]):>9s}  CEX {R[k].cex[:2]}',flush=True)
