import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,parent,oper,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,bpHeadV,Dpt,addBT

def rnav(t):
    return t[1][-1][2] if t[1] else ZB

def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))

seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,0),(4,1),(4,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,2),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(2,0),(3,1),(3,1)],
      ]

for M in seeds:
  print("\n=== seed M=%s ==="%rm.fmt(M))
  M2=oper(M,2)
  if Lng(M2)<2: continue
  jm1=transJm1(M2)
  prevAcc=None
  Wprev=None
  for q in range(2,8):
    Mq=oper(M,q)
    if Lng(Mq)>16: continue
    if not (jm1<Lng(Mq)-1) or jm1>=Lng(Mq): continue
    try:
        acc0=Mark(Mq,jm1)
    except Exception as e:
        print("  q=%d ERR %s"%(q,e)); continue
    z = rnav(acc0)  # = bpHeadT(acc0) since acc0 single-principal
    u = bpHeadV(acc0)
    if prevAcc is not None:
        zprev = rnav(prevAcc); uprev = bpHeadV(prevAcc)
        # z should = addBT(W, Dpt(uprev,zprev)) for some W (q-indep?). Recover W:
        lastp = z[1][-1] if z[1] else None
        oklast = (lastp is not None and lastp[1]==uprev and lastp[2]==zprev)
        W = ('T', z[1][:-1]) if oklast else None
        same_as_prev_W = (W==Wprev) if (W is not None and Wprev is not None) else None
        print("  q=%d: u=%d  lastprincipal-matches(uprev,zprev)=%s  W=%s  W==prevW:%s"%(
            q,u,oklast,W,same_as_prev_W))
        Wprev = W if W is not None else Wprev
    else:
        print("  q=%d: u=%d (base)"%(q,u))
    prevAcc=acc0
