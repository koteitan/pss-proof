import sys, time
from collections import deque, Counter
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
from trans_model import Trans
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
seen=set()
q=deque(diagSeq(u,u+d) for u in range(0,7) for d in range(1,7))
multi=[]; t0=time.time()
while q and time.time()-t0<120:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): multi.append(list(M))
    if Lng(M)<=55:
        for nn in range(1,6):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
# analyze
tot=md_ok=cp_ok=eqcomp=0; deep=deep_ok=0; noneq=[]; fails=[]
for M in multi:
    c=Pcut(M); bJ=seg(M,c,Lng(M)-1); comps=P(M)
    if len(comps)<2 or bJ==[(0,0)]: continue
    bJm1=comps[-2]
    try:
        pre=seg(M,0,c-1); TA=Trans(pre); TB=Trans(bJ); TBm1=Trans(bJm1)
    except Exception: continue
    asl=bucOf(TA); bsl=bucOf(TB)
    if not asl or not bsl: continue
    tot+=1
    md=bu.le_term([bsl[0]],[asl[-1]]); cp=bu.le_term(bucOf(TB),bucOf(TBm1))
    if md: md_ok+=1
    else: fails.append(('md',M))
    if cp: cp_ok+=1
    else: fails.append(('cp',M))
    if bJ==bJm1: eqcomp+=1
    else: noneq.append((M,bJ,bJm1,cp))
    if Lng(M)>=12:
        deep+=1
        if md and cp: deep_ok+=1
print("seen=%d multiT=%d nontriv-junction=%d"%(len(seen),len(multi),tot))
print("  multiD=%d/%d comple=%d/%d eqcomp=%d/%d"%(md_ok,tot,cp_ok,tot,eqcomp,tot))
print("  deep(>=12) both-pass=%d/%d"%(deep_ok,deep))
print("  NON-equal consecutive components: %d"%len(noneq))
for M,bJ,bJm1,cp in noneq[:12]:
    print("    cp=%s last=%s 2nd=%s Lng=%d"%(cp,bJ,bJm1,len(M)))
for f in fails[:8]: print("  FAIL",f)
