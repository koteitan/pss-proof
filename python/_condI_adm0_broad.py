import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import Lng,entry,parent,oper,seg,Red
try:
    from red_model import is_standard
except Exception:
    is_standard=None
from trans_model import (Trans,Adm,ZB,bpHeadT,reduced)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))
def transJ1(M): return Lng(M)-1
def transV(M): return entry(M,1,0)
def Dpt(v,t): return ('T',[('D',v,t)])
def addB(s,t): return ('T', s[1]+t[1])
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))

seen=set(); ok=0; bad=0; nonadm=0; samples=[]
import itertools
hosts=[]
# generate standard hosts up to size 5, rows up to 3
cols=[(a,b) for a in range(4) for b in range(4)]
for n in range(3,6):
    for combo in itertools.product(cols,repeat=n):
        M=list(combo)
        if M[0]!=(0,0): continue
        if is_standard and not is_standard(M): continue
        hosts.append(M)
print("candidate hosts:",len(hosts))
cnt=0
for M in hosts:
    for q in (1,2,3):
        try:
            Mq=oper(M,q);Msq=oper(M,q+1)
        except Exception: continue
        j0q=transJ0(Mq)
        if j0q is None: continue
        jm1=transJm1(Mq)
        if jm1 is None or jm1<0 or jm1>=Lng(Mq)-1: continue
        Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1)
        if YB[:len(Y)]!=Y: continue
        B=YB[len(Y):]
        rY=Red(Y); rYB=Red(YB)
        if not rY or rYB[:len(rY)]!=rY: continue
        Bpp=rYB[len(rY):]
        if not Bpp: continue
        key=(tuple(rY),Bpp[0])
        if key in seen: continue
        seen.add(key)
        M0=rY+[Bpp[0]]
        if Lng(M0)-1<=1: continue  # need j1>1
        if transJ0(M0) is None: continue
        jm1p=transJm1(M0)
        if jm1p is None: continue
        cnt+=1
        e10=transV(M0); j1=transJ1(M0); e1j1=entry(M0,1,j1)
        TX=Trans(rY); TM=Trans(M0)
        want=Dpt(e10, addB(bpHeadT(TX), Dpt(e1j1,ZB)))
        adm0 = (jm1p==0)
        val = (TM==want)
        condI = (e1j1==0)   # condI hallmark in this reduced regime
        if adm0 and val and condI: ok+=1
        else:
            bad+=1
            if not adm0: nonadm+=1
            if len(samples)<12: samples.append((rm.fmt(rY),rm.fmt([Bpp[0]]),jm1p,e1j1,adm0,val,sf(TX),sf(TM),sf(want)))
print("distinct reduced-slice col0 openings tested:",cnt)
print("OK (Adm0 & condI & value):",ok,"  BAD:",bad,"  (of which non-Adm0:",nonadm,")")
print("--- counterexamples / deviations (first 12) ---")
for s in samples: print("  rY=%s col0=%s jm1p=%d e1j1=%d adm0=%s val=%s | TX=%s TM=%s want=%s"%s)
