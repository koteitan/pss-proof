import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm)
import red_model as rm
from trans_model import (Trans,Mark,Adm,ZB,PB,bpHeadT,reduced)

def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,0),(4,1),(4,1)]]
print("3b MECHANISM: is op_k identity <=> transC1_k==transC2_k <=> entry1(B!k)=0 ?")
print("  transC1_k = Mark(Y@take k B) jm1 ; transC2_k = Mark(Y@take(Suc k)B) jm1")
allmatch=True
for M in seeds:
  for q in range(2,5):
    Mq=oper(M,q); Msq=oper(M,q+1)
    if Lng(Msq)>14: continue
    jm1=transJm1(Mq); Lq=Lng(Mq)
    if not (jm1<Lq-1): continue
    Y=seg(Mq,jm1,Lq-1); YB=seg(Msq,jm1,Lng(Msq)-1)
    if YB[:len(Y)]!=Y: continue
    B=YB[len(Y):]; w=len(B)
    # NOTE jm1 for the HOST (Y@take(Suc k)B) is its own transJm1, NOT Mq's jm1.
    # The netfold op uses transC1/2 of the host (Y@take m B)@[B!m] at ITS transJm1.
    try:
        rows=[]
        for k in range(0,w):
            host=Y+B[:k+1]            # (Y @ take k B) @ [B!k]
            prev=Y+B[:k]
            hjm = transJm1(host) if Lng(host)>1 else 0
            # transC1 = Mark(Pred host) (host-jm1) ; transC2 = Mark(host) (host-jm1)
            c1=Mark(prev,hjm); c2=Mark(host,hjm)
            e1=B[k][1]
            same=(c1==c2)
            rows.append((k,e1,same))
            if (e1==0) != same:
                allmatch=False
        tag=" ".join("k%d:e1=%d,c1==c2=%s"%(k,e1,s) for k,e1,s in rows)
        ok=all((e1==0)==s for _,e1,s in rows)
        print("  M=%s q=%d : %s  RULE-HOLDS=%s"%(rm.fmt(M),q,tag,ok))
    except Exception as e:
        print("  M=%s q=%d ERR %s"%(rm.fmt(M),q,e))
print("\nRULE (entry1(B!k)=0  <=>  transC1_k==transC2_k) holds everywhere:",allmatch)
