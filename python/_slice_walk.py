import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg)
import red_model as rm
from trans_model import (Trans,Adm,ZB,PB,bpHeadT,reduced,condV,condVI,condI,condIII)
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def kind(M):
    try: return 'I' if condI(M) else 'III' if condIII(M) else 'V' if condV(M) else 'VI' if condVI(M) else 'o'
    except: return '?'
# slice instance
M=[(0,0),(1,1),(2,0),(3,1),(3,1)]; q=2
Mq=oper(M,q);Msq=oper(M,q+1);jm1=transJm1(Mq)
Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1);B=YB[len(Y):]
print("Y=%s  B=%s  YB=%s"%(rm.fmt(Y),rm.fmt(B),rm.fmt(YB)))
print("per-column walk Trans(Y @ take m B):")
for m in range(len(B)+1):
    cur=Y+B[:m]
    t=Trans(cur)
    extra=""
    if m>0:
        host=Y+B[:m]
        extra=" host-last-col-kind=%s reduced=%s monoT=%s"%(kind(host),reduced(host),monoT(host))
    print("  m=%d  Trans(Y@take %d B)=%s  spineLeaf=%s%s"%(m,m,sf(t),sf(spineLeaf(t)) if spineLeaf(t) else '-',extra))
# the slice itself: is Y standard? is it condV/VI? what does Red do to it?
print("\nslice Y=%s : reduced=%s monoT=%s kind=%s Red(Y)=%s"%(rm.fmt(Y),reduced(Y),monoT(Y),kind(Y),rm.fmt(rm.Red(Y))))
print("slice YB=%s : reduced=%s monoT=%s kind=%s"%(rm.fmt(YB),reduced(YB),monoT(YB),kind(YB)))
