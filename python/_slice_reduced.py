import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,oper,seg,Red)
import red_model as rm
from trans_model import (Trans,Adm,ZB,PB,bpHeadT,reduced)
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
M=[(0,0),(1,1),(2,0),(3,1),(3,1)]
for q in (2,3):
    Mq=oper(M,q);Msq=oper(M,q+1);jm1=transJm1(Mq)
    Y=seg(Mq,jm1,Lng(Mq)-1);YB=seg(Msq,jm1,Lng(Msq)-1);B=YB[len(Y):]
    rY=Red(Y); rYB=Red(YB)
    print("q=%d Y=%s B=%s"%(q,rm.fmt(Y),rm.fmt(B)))
    print("   Red(Y)   = %s  reduced=%s"%(rm.fmt(rY),reduced(rY)))
    print("   Red(Y@B) = %s  reduced=%s"%(rm.fmt(rYB),reduced(rYB)))
    print("   Red(Y) prefix of Red(Y@B)? %s"%(rYB[:len(rY)]==rY))
    if rYB[:len(rY)]==rY:
        print("      => Red(Y@B) = Red(Y) @ %s"%rm.fmt(rYB[len(rY):]))
    # all slice hosts reduced? (m_8_5_surgery_of_geom_endpoint needs RT_PS)
    hosts_red=[reduced(Y+B[:m+1]) for m in range(len(B))]
    print("   slice hosts (Y@take m B) reduced? %s"%hosts_red)
    # reduced hosts?
    print("   Red(Y) standard-ish: monoT=%s"%monoT(rY))
