import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import oper,Lng,entry,parent,TrMax,monoT,Br
from trans_model import Trans,ZB,PB,bpHeadT,condI,condIII,condV,condVI,reduced
def k(M):
    return 'I' if condI(M) else 'III' if condIII(M) else 'V' if condV(M) else 'VI' if condVI(M) else 'o'
M=[(0,0),(1,1),(2,0),(3,1),(3,1)]
for q in range(1,5):
    Mq=oper(M,q)
    if Lng(Mq)>12:continue
    j1=Lng(Mq)-1
    print("q=%d M[q]=%s kind=%s | last col=(%d,%d) j1=%d parent0=%d TrMax=%d par>TrMax=%s Br!=[]=%s"%(
      q,''.join('(%d,%d)'%c for c in Mq),k(Mq),Mq[-1][0],Mq[-1][1],j1,parent(Mq,0,j1),TrMax(Mq),parent(Mq,0,j1)>TrMax(Mq),Br(Mq)!=[]))
