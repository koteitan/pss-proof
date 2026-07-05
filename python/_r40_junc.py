import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from fast_pss import Lng, entry, le0, oper, diagSeq, nextrel0

def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0
def monoT(M): return (not zeroT(M)) and le0(M,0,Lng(M)-1)
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def Pcut(M):
    n=Lng(M)
    for j in range(1,n):
        if le0(M,j,n-1): return j
    raise ValueError
def P(M):
    out=[]
    while multiT(M) and Lng(M)>1:
        c=Pcut(M); out.append(M[c:]); M=M[:c]
    out.append(M); out.reverse()
    return out
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
def chain(cs): return all(is_prefix(cs[i+1],cs[i]) for i in range(len(cs)-1))

seeds=[tuple(diagSeq(u,u+d)) for u in range(0,10) for d in range(1,11)]
seen=set(); q=deque(seeds)
# For the ACTUAL recursion N=M[n]: c=last(P M).  Check junction first(P(c[n])) prefix c_{m-2}
# ONLY when it matters (len(P M)>=2, Lng c>1).  Record when junction FAILS but P(N) is
# still a prefix-chain (=> my inductive decomposition of P(N) is wrong somewhere).
junc_fail=[]; junc_fail_but_Nchain=[]
tot_lastc_lng_gt1=0; cond2_last=0
t0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 150.0
NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 55
while q and time.time()-t0<LIM:
    M=q.popleft()
    if M in seen: continue
    seen.add(M)
    Ml=list(M)
    if multiT(Ml):
        comps=P(Ml)
        if len(comps)>=2:
            c=comps[-1]; prev=comps[-2]
            if Lng(c)>1:
                tot_lastc_lng_gt1+=1
                L=Lng(c)
                is_cond1 = nextrel0(c,0,L-1) and entry(c,1,L-1)==0
                if not is_cond1: cond2_last+=1
                for nn in (1,2,3,5):
                    cn=oper(c,nn)
                    if Lng(cn)<=1: continue
                    Pcn=P(cn)
                    f=Pcn[0]
                    if not is_prefix(f,prev):
                        # does the actual N=M[n] still have a prefix-chain P?
                        N=oper(Ml,nn); PN=P(N)
                        rec_ok = (PN == comps[:-1]+Pcn)   # is my recursion formula right?
                        junc_fail.append((Ml,c,nn,f,prev,is_cond1,chain(PN),rec_ok))
                        break
    if Lng(Ml)<=NMAX:
        for nn in range(1,7):
            M2=tuple(oper(Ml,nn))
            if M2!=M and M2 not in seen: q.append(M2)

print("visited=%d  last-comp Lng>1 hosts=%d  (cond2 among them=%d)"%(len(seen),tot_lastc_lng_gt1,cond2_last))
print("JUNCTION FAIL (first(P(c[n])) not prefix of c_{m-2}), c=LAST comp: %d"%len(junc_fail))
for Ml,c,nn,f,prev,is1,Nchain,recok in junc_fail[:30]:
    print("  c=%s n=%d first=%s prev=%s cond1=%s  P(N)chain=%s recFormulaOK=%s"%(c,nn,f,prev,is1,Nchain,recok))
    print("      host=%s"%Ml)
