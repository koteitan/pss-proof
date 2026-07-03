import sys,functools,os,subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,oper,seg,leR,adm)
import red_model as rm
from trans_model import (Trans,Adm,ZB,PB,bpHeadT,bpHeadV)
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],[(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)]]
print("Slice-Y surgery FORM: Trans(Y@B)=Dpt e10(body); body vs bpHeadT(Trans Y); endpoint")
for M in seeds:
  print("\n=== M=%s ==="%rm.fmt(M))
  for q in range(2,5):
    Mq=oper(M,q);Msq=oper(M,q+1)
    if Lng(Msq)>13:continue
    jm1=transJm1(Mq)
    if not jm1<Lng(Mq):continue
    Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1)
    tY=Trans(Y);tYB=Trans(YB)
    e10Y=tY[1][0][1] if tY[1] else None
    e10=tYB[1][0][1] if tYB[1] else None
    body=bpHeadT(tYB); bhY=bpHeadT(tY)
    print("  q=%d Y=%s B=%s"%(q,rm.fmt(Y),rm.fmt(YB[len(Y):])))
    print("     Trans Y    = %s  (e10=%s, bpHeadT=%s, spineLeaf=%s)"%(sf(tY),e10Y,sf(bhY),sf(spineLeaf(tY)) if spineLeaf(tY) else '-'))
    print("     Trans(Y@B) = %s  (e10=%s, body=%s)"%(sf(tYB),e10,sf(body)))
    print("     endpoint spineLeaf(Trans YB)=%s == bpHeadT(Trans Y)=%s : %s"%(sf(spineLeaf(tYB)),sf(bhY),spineLeaf(tYB)==bhY))
    # surgery form Trans(Y@B)=Dpt e10(t2 +B Dpt vm1 (bhY))?
    # read body as t2 +B Dpt vm1 (slot): last principal of body
    pbb=PB(body)
    if pbb:
        last=pbb[-1];vm1=last[1][0][1];slot=bpHeadT(last);t2=('T',[p for p in body[1][:-1]])
        form=(tYB==('T',[('D',e10,('T',t2[1]+[('D',vm1,bhY)]))]))
        print("     FORM Trans(Y@B)=Dpt %s (t2=%s +B Dpt %s (bpHeadT TrY)) : %s"%(e10,sf(t2),vm1,form))
