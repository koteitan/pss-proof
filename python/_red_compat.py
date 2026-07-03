import sys,functools,os,subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,oper,seg,Red,TrMax,Br)
import red_model as rm
from trans_model import (Trans,Adm,ZB,PB,bpHeadT,reduced,condV,condVI,condI,condIII)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def kind(M):
    try: return 'I' if condI(M) else 'III' if condIII(M) else 'V' if condV(M) else 'VI' if condVI(M) else 'o'
    except: return '?'
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
seeds=[[(0,0),(1,1),(2,0),(3,1),(3,1)],
       [(0,0),(1,1),(2,0),(3,1),(3,1),(3,1)],
       [(0,0),(1,1),(2,1),(3,0),(4,1),(4,1)]]
print("(a) Red(Y@B)=Red(Y)@B'' across families/q; reduced-slice structure:")
for M in seeds:
  print(" M=%s"%rm.fmt(M))
  rslices=set()
  for q in range(2,5):
    Mq=oper(M,q);Msq=oper(M,q+1);jm1=transJm1(Mq)
    if Lng(Msq)>13 or not jm1<Lng(Mq):continue
    Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1)
    rY=Red(Y);rYB=Red(YB)
    compat=(rYB[:len(rY)]==rY)
    rslices.add((tuple(rY),tuple(rYB)))
    print("   q=%d: Red(Y)=%s Red(Y@B)=%s compat=%s std(RedY)=%s std(RedYB)=%s"%(q,rm.fmt(rY),rm.fmt(rYB),compat,is_std(tuple(rY)),is_std(tuple(rYB))))
  # the reduced slice is q-invariant? + its kind + endpoint on the REDUCED level
  if len(rslices)==1:
    rY,rYB=list(rslices)[0]; rY=list(rY);rYB=list(rYB)
    print("   reduced-slice q-INVARIANT: RedY=%s RedYB=%s kind(RedYB)=%s"%(rm.fmt(rY),rm.fmt(rYB),kind(rYB)))
    ep=(spineLeaf(Trans(rYB))==bpHeadT(Trans(rY)))
    print("   reduced-slice endpoint spineLeaf(Trans RedYB)=%s == bpHeadT(Trans RedY)=%s : %s"%(sf(spineLeaf(Trans(rYB))),sf(bpHeadT(Trans(rY))),ep))
