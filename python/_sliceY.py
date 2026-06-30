import sys,functools,os,subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm)
import red_model as rm
from trans_model import (Trans,Mark,Adm,ZB,PB,bpHeadT,reduced)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def isMarked(M,m): return adm(M,m) and leR(M,0,m,Lng(M)-1)
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
gpar_seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
            [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
            [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)]]
print("SLICE-Y endpoint: Y=seg(M[q]) jm1 end, YB=seg(M[Suc q]) jm1 end, jm1=transJm1(M[q])")
for M in gpar_seeds:
  print("\n=== gpar seed M=%s ==="%rm.fmt(M))
  for q in range(2,5):
    Mq=oper(M,q); Msq=oper(M,q+1)
    if Lng(Msq)>13: print("  q=%d skip(len %d)"%(q,Lng(Msq)));continue
    jm1=transJm1(Mq)
    Lq=Lng(Mq)
    info="jm1=%d Lng(M[q])=%d interior=%s"%(jm1,Lq, 0<jm1<Lq-1)
    if not (jm1 < Lq):
        print("  q=%d %s -> jm1 at/over boundary, slice empty"%(q,info));continue
    Y=seg(Mq,jm1,Lq-1)
    YB=seg(Msq,jm1,Lng(Msq)-1)
    # confirm Y is a prefix of YB
    isprefix=(YB[:len(Y)]==Y)
    mkq=isMarked(Mq,jm1); mksq=isMarked(Msq,jm1)
    try:
        tY=Trans(Y); tYB=Trans(YB)
    except Exception as e:
        print("  q=%d %s ERR %s"%(q,info,e));continue
    sl=spineLeaf(tYB); bh=bpHeadT(tY); eq=(sl==bh)
    print("  q=%d %s | Y=%s B=%s Yprefix=%s Mkd(q,sq)=%s,%s"%(q,info,rm.fmt(Y),rm.fmt(YB[len(Y):]),isprefix,mkq,mksq))
    print("      ENDPOINT spineLeaf(Trans YB)=%s  bpHeadT(Trans Y)=%s  EQUAL=%s"%(sf(sl) if sl else None,sf(bh),eq))
