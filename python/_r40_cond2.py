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
    raise ValueError("no Pcut")
def P(M):
    out=[]
    while multiT(M) and Lng(M)>1:
        c=Pcut(M); out.append(M[c:]); M=M[:c]
    out.append(M); out.reverse()
    return out
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
def cond1(c):  # m_6_2_nonmulti_oper_1 branch: P(c[n]) = replicate n (Pred c)
    L=Lng(c)
    if L<=1: return False
    return nextrel0(c,0,L-1) and entry(c,1,L-1)==0

# enumerate ST_PS; for every multiT M with len(P M)>=2, look at EACH component
# c = P M ! J (J from 0..len-1).  If c is mono (Lng>1), record whether cond1 or cond2,
# and check the junction fact: first(P(c[n])) prefix of the PRECEDING component P M!(J-1).
seeds=[tuple(diagSeq(u,u+d)) for u in range(0,10) for d in range(1,11)]
seen=set(); q=deque(seeds)
c1=c2=0
cond2_lng_gt1=[]        # mono P-component c with Lng>1 that is cond2  (the danger case)
junc_bad=[]             # first(P(c[n])) NOT prefix of preceding component
t0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 150.0
NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 55
while q and time.time()-t0<LIM:
    M=q.popleft()
    if M in seen: continue
    seen.add(M)
    Ml=list(M)
    if multiT(Ml):
        comps=P(Ml)
        for J in range(len(comps)):
            c=comps[J]
            if Lng(c)>1 and not zeroT(c):  # a length>1 (mono) component
                if cond1(c):
                    c1+=1
                else:
                    c2+=1
                    if len(cond2_lng_gt1)<40: cond2_lng_gt1.append((Ml,J,c))
                # junction check for J>0: first(P(c[n])) prefix of comps[J-1]?
                if J>0:
                    for nn in (1,2,3):
                        cn=oper(c,nn)
                        Pcn=P(cn)
                        f=Pcn[0]
                        if not is_prefix(f,comps[J-1]):
                            junc_bad.append((Ml,J,c,nn,f,comps[J-1]))
                            break
    if Lng(Ml)<=NMAX:
        for nn in range(1,7):
            M2=tuple(oper(Ml,nn))
            if M2!=M and M2 not in seen: q.append(M2)

print("visited=%d  mono(Lng>1) P-components: cond1=%d  cond2=%d"%(len(seen),c1,c2))
print("=== cond2 mono components with Lng>1 (the DANGER case for the chain junction) ===")
print("count(sampled)=%d"%len(cond2_lng_gt1))
for M,J,c in cond2_lng_gt1[:25]:
    print("  J=%d c=%s  (host M=%s)"%(J,c,M))
print("=== junction violations: first(P(c[n])) NOT prefix of preceding component ===")
print("count=%d"%len(junc_bad))
for M,J,c,nn,f,prev in junc_bad[:25]:
    print("  J=%d n=%d c=%s first(P(c[n]))=%s prev=%s host=%s"%(J,nn,c,f,prev,M))
