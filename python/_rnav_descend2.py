import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,parent,oper,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,Dpt,addBT

def rnav(t):
    return t[1][-1][2] if t[1] else ZB

def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,0),(4,1),(4,1)]]

for M in seeds:
  print("\n=== seed M=%s ==="%rm.fmt(M))
  M2=oper(M,2)
  if Lng(M2)<2: continue
  jm1=transJm1(M2)
  prevAcc=None
  for q in range(2,7):
    Mq=oper(M,q)
    if Lng(Mq)>13: continue
    if not (jm1<Lng(Mq)-1) or jm1>=Lng(Mq): continue
    try:
        acc0=Mark(Mq,jm1)
    except Exception as e:
        print("  q=%d ERR %s"%(q,e)); continue
    rn = rnav(acc0)
    if prevAcc is not None:
        cand1 = addBT(bpHeadT(prevAcc), prevAcc)
        # cand2: prepend a single Dpt(c,ZB) using c = first principal value of bpHeadT(prevAcc)
        bh = bpHeadT(prevAcc)
        c = bh[1][0][1] if bh[1] else None
        cand2 = addBT(Dpt(c,ZB), prevAcc) if c is not None else None
        print("  q=%d: rnav(acc0_q)=%s"%(q,rn))
        print("        cand1 addBT(bpHeadT(prev),prev) == rnav? %s"%(cand1==rn))
        print("        cand2 addBT(Dpt(c,0),prev) == rnav?       %s  (c=%s)"%(cand2==rn,c))
        if cand1!=rn:
            print("        cand1=%s"%(cand1,))
            print("        rn   =%s"%(rn,))
    prevAcc=acc0
