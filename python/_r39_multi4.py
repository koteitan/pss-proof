import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, monoT, zeroT, P, seg, oper, diagSeq
from trans_model import Trans, reduced
import buchholz as bu
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def bucOf(t): return [('D',p[1],bucOf(p[2])) for p in t[1]]
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
# build periodic hosts by repeating a monoT block
blocks=[[(0,0),(1,0)],[(0,0),(1,0),(1,0)],[(0,0),(1,0),(1,0),(1,0)],
        [(0,0),(1,1),(2,0)],[(0,0),(1,0),(2,0)],[(0,0),(1,1),(2,1)]]
hosts=[]
for B in blocks:
    for k in (2,3,4,5):
        hosts.append(B*k)
# also try oper-generated periodic ones explicitly reachable
extra=[[(0,0),(1,0),(0,0),(1,0)],
       [(0,0),(1,0),(1,0),(0,0),(1,0),(1,0),(0,0),(1,0),(1,0),(0,0),(1,0),(1,0)]]
hosts+=extra
tot=md_ok=cp_ok=eqcomp=stpsN=0; fails=[]
for M in hosts:
    if not (multiT(M) and reduced(M)):
        # skip non-standard-looking
        pass
    c_valid = True
    try:
        c=Pcut(M)
    except Exception:
        continue
    pre=seg(M,0,c-1); bJ=seg(M,c,Lng(M)-1)
    comps=P(M)
    if len(comps)<2 or bJ==[(0,0)]: continue
    bJm1=comps[-2]
    try:
        TA=Trans(pre); TB=Trans(bJ); TBm1=Trans(bJm1)
    except Exception as e:
        print("  Trans-err",M,e); continue
    asl=bucOf(TA); bsl=bucOf(TB)
    if not asl or not bsl: continue
    tot+=1
    md=bu.le_term([bsl[0]],[asl[-1]]); cp=bu.le_term(bucOf(TB),bucOf(TBm1))
    if md: md_ok+=1
    else: fails.append(('md',M))
    if cp: cp_ok+=1
    else: fails.append(('cp',M,'Tlast',bucOf(TB),'T2nd',bucOf(TBm1)))
    if bJ==bJm1: eqcomp+=1
    else: print("  NONEQ comps: last=%s  2nd=%s  M=%s"%(bJ,bJm1,M))
print("checked=%d  multiD=%d  comple=%d  eqcomp(last==2nd)=%d"%(tot,md_ok,cp_ok,eqcomp))
for f in fails[:10]: print("  FAIL",f)
