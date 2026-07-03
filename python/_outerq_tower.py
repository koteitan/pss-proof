import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,parent,oper,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def sf(T):
    if T is None or T==ZB or not T[1]: return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))

# slice_q = seg(M[q], jm1_q, end).  T_q = bpHeadT(Trans(slice_q)).
# QUESTION (non-circularity): is T_q = f(T_{q-1}) where f is structural (append/deepen),
# AND is endpoint spineLeaf(Trans(slice_q)) = bpHeadT(Trans(slice_{q-1})) = T_{q-1} self-similar?
seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(4,1),(4,1)]]
for M in seeds:
  print("\n=== seed M=%s ==="%rm.fmt(M))
  prevT=None
  for q in range(2,7):
    Mq=oper(M,q)
    if Lng(Mq)>16: print("  q=%d skip"%q); continue
    jm=transJm1(Mq)
    if not (jm<Lng(Mq)-1): continue
    sl=seg(Mq,jm,Lng(Mq)-1)
    try:
        T=bpHeadT(Trans(sl)); leaf=spineLeaf(Trans(sl))
    except Exception as e:
        print("  q=%d ERR %s"%(q,e)); continue
    # check endpoint self-similarity: leaf(q) == T_{q-1} ?
    selfsim = (prevT is not None and leaf==prevT)
    # check append-regime recurrence: T_q == T_{q-1} @ [Dpt vm1 T_{q-1}] ?
    note=""
    if prevT is not None:
        # append: T_q principals = T_{q-1} principals + 1 new whose body == T_{q-1}
        if len(T[1])==len(prevT[1])+1 and T[1][:-1]==prevT[1] and T[1][-1][2]==prevT:
            note="APPEND: T_q=T_{q-1}@[D%s(T_{q-1})]"%T[1][-1][1]
        elif T[1][:-1]==prevT[1][:-1] and len(T[1])==len(prevT[1]):
            note="DEEPEN: last principal body grew"
        else:
            note="OTHER"
    print("  q=%d jm=%d Lng=%d  T_q=%s  leaf=%s  selfsim(leaf==T_{q-1})=%s  %s"%(
          q,jm,Lng(Mq),sf(T),sf(leaf),selfsim,note))
    prevT=T
