import sys, time, signal
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg, Br, entry
from trans_model import Trans, Pred
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s,f:(_ for _ in ()).throw(TO()))
def safe(f,*a,b=4):
    signal.alarm(b)
    try: r=f(*a); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
# corpus
seen=set(); q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
hosts=[]; t0=time.time()
while q and time.time()-t0<25:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k); hosts.append(list(M))
    if Lng(M)<=45:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
# prioritize deep keystone hosts for resid
key=[M for M in hosts if monoT(M) and Br(M)!=[] and Lng(M)-1>1]
key.sort(key=lambda M:-Lng(M))
R={'a':0,'c1':0,'c2':0,'c3':0,'all':0,'da':0,'dall':0}; Rfail=[]
tR=time.time()
for M in key:
    if time.time()-tR>50 or R['a']>=250: break
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
# Q*/pcompPrefix on multiT (fast, no Trans)
multi_seeds=[list(m) for m in seen if multiT(list(m))]
seen2=set(); q2=deque(multi_seeds)
Qtot=Qok=Ptot=Pok=Pdeep=Pdeepok=0; Qfail=[]; t1=time.time()
while q2 and time.time()-t1<45:
    M=q2.popleft(); k=tuple(M)
    if k in seen2: continue
    seen2.add(k); comps=P(M)
    if multiT(M) and len(comps)>=2 and seg(M,Pcut(M),Lng(M)-1)!=[(0,0)]:
        Ptot+=1
        if is_prefix(comps[-1],comps[-2]): Pok+=1
        if Lng(M)>=12:
            Pdeep+=1
            if is_prefix(comps[-1],comps[-2]): Pdeepok+=1
        Qtot+=1
        if all(is_prefix(comps[j+1],comps[j]) for j in range(len(comps)-1)): Qok+=1
        else: Qfail.append((M,[len(c) for c in comps]))
    if Lng(M)<=48:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen2: q2.append(M2)
print("=== RESID (deep keystone) applic=%d ==="%R['a'])
print(" c1(newOT)=%d c2(dstep)=%d c3(gbt)=%d ALL=%d  deep(>=12) ALL=%d/%d"
      %(R['c1'],R['c2'],R['c3'],R['all'],R['dall'],R['da']))
for M,c1,c2,c3 in Rfail[:8]: print("  RFAIL c1=%s c2=%s c3=%s M=%s"%(c1,c2,c3,M))
print("=== pcompPrefix(last pair) %d/%d deep %d/%d ==="%(Pok,Ptot,Pdeepok,Pdeep))
print("=== Q*(ALL consec nested) %d/%d ==="%(Qok,Qtot))
for M,ls in Qfail[:8]: print("  QFAIL lens=%s M=%s"%(ls,M[:16]))
