import sys, time, signal
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, Br, entry
from trans_model import Trans, Pred
import buchholz as bu
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s,f:(_ for _ in ()).throw(TO()))
def safe(f,*a,b=4):
    signal.alarm(b)
    try: r=f(*a); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
seen=set(); q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
hosts=[]; t0=time.time()
while q and time.time()-t0<30:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k); hosts.append(list(M))
    if Lng(M)<=45:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
key=[M for M in hosts if monoT(M) and Br(M)!=[] and Lng(M)-1>1]
key.sort(key=lambda M:-Lng(M))
R={'a':0,'c1':0,'c2':0,'c3':0,'all':0,'da':0,'dall':0}; Rfail=[]; tR=time.time()
for M in key:
    if time.time()-tR>150 or R['a']>=400: break
    v0=entry(M,1,0)
    TM=safe(Trans,M); TPM=safe(Trans,Pred(M))
    if TM is None or TPM is None: continue
    if len(TM[1])!=1 or len(TPM[1])!=1: continue
    if TM[1][0][1]!=v0 or TPM[1][0][1]!=v0: continue
    lM=bucOf(TM[1][0][2]); lPM=bucOf(TPM[1][0][2])
    if not lM: continue
    ps=lM[:-1]; x,qq=lM[-1][1],lM[-1][2]
    if lPM[:len(ps)]!=ps: continue
    deep=Lng(M)>=12; R['a']+=1
    c1=bu.in_OT([('D',x,qq)]); c2=(bu.le_term([('D',x,qq)],[ps[-1]]) if ps else True)
    body=ps+[('D',x,qq)]; c3=bu.G_lt(v0,body,body)
    if c1:R['c1']+=1
    if c2:R['c2']+=1
    if c3:R['c3']+=1
    if c1 and c2 and c3: R['all']+=1
    else: Rfail.append((M,c1,c2,c3))
    if deep:
        R['da']+=1
        if c1 and c2 and c3: R['dall']+=1
print("RESID applic=%d maxLng=%d"%(R['a'], max((Lng(M) for M in key),default=0)))
print(" c1(newOT)=%d c2(dstep)=%d c3(gbt)=%d ALL=%d  deep(>=12) ALL=%d/%d"
      %(R['c1'],R['c2'],R['c3'],R['all'],R['dall'],R['da']))
for M,c1,c2,c3 in Rfail[:10]: print("  RFAIL c1=%s c2=%s c3=%s Lng=%d M=%s"%(c1,c2,c3,Lng(M),M))
