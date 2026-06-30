import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,oper,seg,Red)
import red_model as rm
from trans_model import (Trans,Adm,ZB,PB,bpHeadT,reduced)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))
def transJ1(M): return Lng(M)-1
def transV(M): return entry(M,1,0)
def transCondI(M):  # entry M 1 j1 == 0 branch? use the standard: condI <=> ... approximate via entry
    j1=transJ1(M); return entry(M,1,j1)==0  # condI's hallmark for our slice: row1 last =0
def Dpt(v,t): return ('T',[('D',v,t)])
def addB(s,t): return ('T', s[1]+t[1])
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))

# host families: standard reduced-slice generator + a few real hosts
def check(RedY):
    # build col0 = the FIRST appended column of B'' (sibling-append). For a reduced slice,
    # col0 increments the trunk: (entry RedY 0 last +1, entry RedY 1 last +? ) -- but we
    # actually take it from the REAL surgery. Here: probe whether RedY@[any sibling col] is Adm0+condI.
    # Use the canonical reduced-slice continuation: next oper column.
    pass

print("=== reduced-slice col0 from REAL hosts ===")
M=[(0,0),(1,1),(2,0),(3,1),(3,1)]
for q in (2,3,4):
    Mq=oper(M,q);Msq=oper(M,q+1);jm1=transJm1(Mq)
    Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1);B=YB[len(Y):]
    rY=Red(Y); rYB=Red(YB)
    if rYB[:len(rY)]!=rY: 
        print("q=%d: rcompat fails, skip"%q); continue
    Bpp=rYB[len(rY):]
    if not Bpp: print("q=%d: empty B''"%q); continue
    M0=rY+[Bpp[0]]   # RedY @ [col0]
    print("q=%d RedY=%s col0=%s  M'=RedY@[col0]=%s"%(q,rm.fmt(rY),rm.fmt([Bpp[0]]),rm.fmt(M0)))
    jm1p=transJm1(M0)
    print("   transJm1(M')=%d  (Adm0 <=> ==0)   transCondI(M')[row1 last==0]=%s"%(jm1p,transCondI(M0)))
    TX=Trans(rY); TM=Trans(M0)
    e10=transV(M0); j1=transJ1(M0); e1j1=entry(M0,1,j1)
    want=Dpt(e10, addB(bpHeadT(TX), Dpt(e1j1,ZB)))
    print("   Trans(RedY)=%s  bpHeadT=%s"%(sf(TX),sf(bpHeadT(TX))))
    print("   Trans(M')  =%s"%sf(TM))
    print("   Dpt e10(bpHeadT(Trans RedY) +B Dpt e1j1 0) =%s   e10=%d e1j1=%d"%(sf(want),e10,e1j1))
    print("   *** Trans(M')==want ? %s   (Adm0-condI-append base holds)"%(TM==want))
