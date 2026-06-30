import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm)
import red_model as rm
from trans_model import (Trans,Mark,Adm,ZB,PB,bpHeadT,reduced)

def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def sf(T):
    if T is None or T==ZB or not T[1]: return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)]]
print("3b LEAF RECURRENCE: L_k = spineLeaf(Trans(Y @ take k B)), per-column op action")
for M in seeds:
  for q in range(2,5):
    Mq=oper(M,q); Msq=oper(M,q+1)
    if Lng(Msq)>13: continue
    jm1=transJm1(Mq); Lq=Lng(Mq)
    if not (jm1<Lq-1): continue
    Y=seg(Mq,jm1,Lq-1); YB=seg(Msq,jm1,Lng(Msq)-1)
    if YB[:len(Y)]!=Y: continue
    B=YB[len(Y):]; w=len(B)
    try:
        Ls=[spineLeaf(Trans(Y+B[:k])) for k in range(0,w+1)]
        # also the full head bpHeadT(Trans Y) = target C(L_0)
        tgt=bpHeadT(Trans(Y))
        print("  M=%s q=%d w=%d:"%(rm.fmt(M),q,w))
        print("     L_0..L_w = %s"%(" -> ".join(sf(L) for L in Ls)))
        print("     target bpHeadT(Trans Y)=%s ; L_w==target? %s"%(sf(tgt), Ls[-1]==tgt))
        # per-step: is L_k = D0(prevhead, L_{k-1})-like? show the increment
        for k in range(1,w+1):
            # what wraps L_{k-1} to get L_k?
            print("       step%d: %s  ==>  %s"%(k, sf(Ls[k-1]), sf(Ls[k])))
    except Exception as e:
        print("  M=%s q=%d ERR %s"%(rm.fmt(M),q,e))
