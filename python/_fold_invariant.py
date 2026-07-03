import sys,os,functools,subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm)
import red_model as rm
from trans_model import (Trans,Mark,Adm,ZB,PB,bpHeadT,reduced)

def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))

def base_shape(TX):
    # TX = ('T',[('D',e10,body)]) single top-D; body's last P-block = single Dpt(vm1,leaf); leaf==spineLeaf(TX)
    if not TX[1] or len(TX[1])!=1: return (False,"head not single-D (len=%d)"%len(TX[1]))
    body=TX[1][0][2]; pb=PB(body)
    if not pb: return (False,"body empty")
    last=pb[-1]
    if len(last[1])!=1: return (False,"last P-block not single-D")
    leaf=last[1][0][2]; sl=spineLeaf(TX)
    return (leaf==sl, "leaf==spineLeaf? %s"%(leaf==sl))

def sf(T):
    if T==ZB:return '0'
    if not T[1]: return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)]]
print("FOLD-INVARIANT probe: does base-spine-shape hold for Trans(Y @ take k B), k=0..|B|?")
allok=True
for M in seeds:
  for q in range(2,6):
    Mq=oper(M,q); Msq=oper(M,q+1)
    if Lng(Msq)>13: continue
    jm1=transJm1(Mq); Lq=Lng(Mq)
    if not (jm1<Lq-1): continue
    Y=seg(Mq,jm1,Lq-1); YB=seg(Msq,jm1,Lng(Msq)-1)
    if YB[:len(Y)]!=Y: continue
    B=YB[len(Y):]
    try:
        line=[]
        for k in range(0,len(B)+1):
            X=Y+B[:k]
            TX=Trans(X)
            ok,why=base_shape(TX)
            line.append((k,ok))
            if not ok: allok=False
        kbad=[k for k,ok in line if not ok]
        tag="OK" if not kbad else "BAD@%s"%kbad
        print("  M=%s q=%d |B|=%d : %s  (TransY=%s, TransYB=%s)"%(rm.fmt(M),q,len(B),tag,sf(Trans(Y)),sf(Trans(YB))))
    except Exception as e:
        print("  M=%s q=%d ERR %s"%(rm.fmt(M),q,e))
print("ALL fold-intermediates keep base-spine-shape:",allok)
