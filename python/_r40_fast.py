import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from fast_pss import Lng, entry, le0, oper, diagSeq

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

# ST_PS = oper-closure of diagSeq(u,v), u<=v (u>0 included).  DEEP BFS.
seeds=[tuple(diagSeq(u,u+d)) for u in range(0,10) for d in range(1,11)]
seen=set(); q=deque(seeds)
tot=pref=eqc=deep=deep_pref=0
noPref=[]; chain_tot=chain_ok=0; chain_bad=[]
maxLngP=0; maxLngN=0
t0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 300.0
NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 70
while q and time.time()-t0<LIM:
    M=q.popleft()
    if M in seen: continue
    seen.add(M)
    Ml=list(M)
    if multiT(Ml):
        comps=P(Ml); c=Pcut(Ml); bJ=Ml[c:]
        if len(comps)>=2:
            chain_tot+=1
            allok=all(is_prefix(comps[J+1],comps[J]) for J in range(len(comps)-1))
            if allok: chain_ok+=1
            else: chain_bad.append((Ml,comps))
            if bJ!=[(0,0)]:
                bJm1=comps[-2]; tot+=1
                p=is_prefix(bJ,bJm1)
                if p: pref+=1
                else: noPref.append((Ml,bJ,bJm1,c))
                if bJ==bJm1: eqc+=1
                maxLngP=max(maxLngP,len(comps)); maxLngN=max(maxLngN,len(Ml))
                if Lng(Ml)>=14:
                    deep+=1
                    if p: deep_pref+=1
    if Lng(Ml)<=NMAX:
        for nn in range(1,7):
            M2=tuple(oper(Ml,nn))
            if M2!=M and M2 not in seen: q.append(M2)

print("=== r40 FAST validation over TRUE ST_PS (oper-closure diagSeq u in 0..9) ===")
print("visited=%d  time=%.0fs"%(len(seen),time.time()-t0))
print("TARGET: nontriv-junction hosts=%d  prefix=%d (eq=%d proper=%d)  maxLngN=%d maxLngP=%d"
      %(tot,pref,eqc,pref-eqc,maxLngN,maxLngP))
print("DEEP Lng(N)>=14: prefix %d / %d"%(deep_pref,deep))
print("TARGET NO-PREFIX (CEX): %d"%len(noPref))
for M,bJ,bJm1,c in noPref[:25]:
    print("  Pcut=%d last=%s 2nd=%s M=%s"%(c,bJ,bJm1,M))
print("STRONGER full prefix-chain: %d / %d   VIOLATIONS=%d"%(chain_ok,chain_tot,len(chain_bad)))
for M,comps in chain_bad[:25]:
    print("  M=%s comps=%s"%(M,comps))
