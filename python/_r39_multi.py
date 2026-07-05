import sys, time, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg
import red_model as rm
from trans_model import Trans
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
rng=random.Random(3); seen=set()
# wider seed set including asymmetric diagonals + deeper oper
starts=[diagSeq(u,u+d) for u in range(0,7) for d in range(1,7)]
nontriv=[]; total_multi=0
t0=time.time()
frontier=list(starts)
while frontier and time.time()-t0<70:
    M=frontier.pop()
    for nn in range(1,6):
        try: M2=oper(M,nn)
        except Exception: continue
        if M2==M or Lng(M2)>60: continue
        k=tuple(M2)
        if k in seen: continue
        seen.add(k)
        frontier.append(M2)
        if multiT(M2):
            total_multi+=1
            c=Pcut(M2); last=seg(M2,c,Lng(M2)-1)
            if last!=[(0,0)]:
                nontriv.append(list(M2))
print("seen=%d total_multi=%d nontriv_last=%d"%(len(seen),total_multi,len(nontriv)))
# validate multiD/comple on the nontrivial ones
ok_md=ok_cp=tot=headeq=0; fails=[]
for M in nontriv[:200]:
    c=Pcut(M); pre=seg(M,0,c-1); bJ=seg(M,c,Lng(M)-1)
    comps=P(M)
    if len(comps)<2: continue
    bJm1=comps[-2]
    try:
        TA=Trans(pre); TB=Trans(bJ); TBm1=Trans(bJm1)
    except Exception: continue
    asl=bucOf(TA); bsl=bucOf(TB)
    if not asl or not bsl: continue
    tot+=1
    md=bu.le_term([bsl[0]],[asl[-1]]); cp=bu.le_term(bucOf(TB),bucOf(TBm1))
    if md: ok_md+=1
    else: fails.append(('md',M))
    if cp: ok_cp+=1
    else: fails.append(('cp',M))
    if bsl[0][1]==asl[-1][1]: headeq+=1
print("nontriv-multiD: tot=%d md=%d comple=%d headeq=%d"%(tot,ok_md,ok_cp,headeq))
for M in nontriv[:8]:
    print("  nontriv Lng=%d P=%d last=%s M=%s"%(Lng(M),len(P(M)),seg(M,Pcut(M),Lng(M)-1),M))
for f in fails[:8]: print("  FAIL",f)
