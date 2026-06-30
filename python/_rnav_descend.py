import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,parent,oper,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT

def rnav(t):
    return t[1][-1][2] if t[1] else ZB

def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))

def sf(T,depth=0):
    if depth>8: return '...'
    if T is None or T==ZB or not T[1]: return '0'
    return '('+','.join('D%s.%s'%(p[1],sf(p[2],depth+1)) for p in T[1])+')' if len(T[1])>1 else 'D%s.%s'%(T[1][0][1],sf(T[1][0][2],depth+1))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,0),(4,1),(4,1)]]

print("CONJECTURE TEST: rnav(Mark(M[q],jm1)) == bpHeadT(Mark(M[q-1],jm1))  [same jm1 across q]")
ntested=0; nmatch=0
for M in seeds:
  print("\n=== seed M=%s ==="%rm.fmt(M))
  # fix jm1 from q=2 base (must remain valid/admissible meaningfully across q)
  M2=oper(M,2)
  if Lng(M2)<2: continue
  jm1=transJm1(M2)
  prevAcc=None
  for q in range(2,8):
    Mq=oper(M,q)
    if Lng(Mq)>13: print("  q=%d skip(len)"%q,flush=True); continue
    if not (jm1<Lng(Mq)-1) or jm1>=Lng(Mq):
        print("  q=%d skip(jm1 oob, Lng=%d)"%(q,Lng(Mq))); continue
    try:
        acc0=Mark(Mq,jm1)
    except Exception as e:
        print("  q=%d ERR %s"%(q,e),flush=True); continue
    rn = rnav(acc0)
    bh = bpHeadT(acc0)
    if prevAcc is not None:
        prevbh = bpHeadT(prevAcc)
        match = (rn==prevbh)
        ntested+=1; nmatch+= (1 if match else 0)
        print("  q=%d  acc0=%s"%(q,sf(acc0)))
        print("        rnav(acc0_q)      = %s"%sf(rn))
        print("        bpHeadT(acc0_q-1) = %s   MATCH=%s"%(sf(prevbh),match))
    else:
        print("  q=%d  acc0=%s  (base, no compare)"%(q,sf(acc0)))
    prevAcc=acc0

print("\nTOTAL tested=%d matched=%d"%(ntested,nmatch))
