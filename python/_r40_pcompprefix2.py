import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg, Pcut, multiT, entry, le0

def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a

# ===== Phase 1: collect multiT seeds along oper-orbits from diagSeq (u>0 incl) =====
seeds=[diagSeq(u,u+d) for u in range(0,8) for d in range(1,9)]
seen=set(); q=deque(seeds); multi_seeds=[]
t0=time.time()
while q and time.time()-t0<60:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M): multi_seeds.append(list(M))
    if Lng(M)<=40:
        for nn in range(1,7):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)
print("phase1: visited=%d multi_seeds=%d"%(len(seen),len(multi_seeds)))

# ===== Phase 2: BFS from multi_seeds, deeper, check target + inductive invariant =====
tot=pref=eqc=0
deep=deep_pref=0
noPref=[]
# inductive invariant: is EVERY consecutive pair (c_{J+1} prefix of c_J) nested?
chain_tot=chain_ok=0
chain_bad=[]
seen2=set(); q2=deque(multi_seeds)
t1=time.time()
while q2 and time.time()-t1<180:
    M=q2.popleft(); k=tuple(M)
    if k in seen2: continue
    seen2.add(k)
    if multiT(M):
        comps=P(M); c=Pcut(M); bJ=M[c:]
        if len(comps)>=2 and bJ!=[(0,0)]:
            bJm1=comps[-2]; tot+=1
            p=is_prefix(bJ,bJm1)
            if p: pref+=1
            else: noPref.append((list(M),bJ,bJm1,c))
            if bJ==bJm1: eqc+=1
            if Lng(M)>=14:
                deep+=1
                if p: deep_pref+=1
        # stronger invariant: whole P-list is a prefix chain (c_{J+1} prefix of c_J)
        if len(comps)>=2:
            chain_tot+=1
            allok=all(is_prefix(comps[J+1],comps[J]) for J in range(len(comps)-1))
            if allok: chain_ok+=1
            else: chain_bad.append((list(M),comps))
    if Lng(M)<=44:
        for nn in range(1,7):
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen2: q2.append(M2)

print("=== TARGET (last comp prefix of 2nd-last) ===")
print("nontriv-junction hosts=%d  prefix=%d  (eq=%d proper=%d)"%(tot,pref,eqc,pref-eqc))
print("DEEP Lng(N)>=14: prefix %d / %d"%(deep_pref,deep))
print("NO-PREFIX (target CEX): %d"%len(noPref))
for M,bJ,bJm1,c in noPref[:20]:
    print("  Pcut=%d last=%s 2nd=%s M=%s"%(c,bJ,bJm1,M))
print("=== STRONGER: whole P-list prefix-chain (c_{J+1} prefix of c_J) ===")
print("multi hosts (len P>=2)=%d  full-chain-nested=%d"%(chain_tot,chain_ok))
print("chain-VIOLATIONS: %d"%len(chain_bad))
for M,comps in chain_bad[:20]:
    print("  M=%s comps=%s"%(M,comps))
