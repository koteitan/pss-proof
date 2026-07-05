import sys, time
from collections import deque
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import Lng, oper, diagSeq, monoT, zeroT, P, seg, Pcut, multiT, entry, le0

def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a

# ===== Phase 1: BFS the oper-closure of diagSeq seeds (INCLUDING u>0) =====
# ST_PS = union_k SkT_PS k, SkT_PS 0 = {diagSeq u v | u<=v},
#         SkT_PS (k+1) = {M[n] | M in SkT_PS k, n>=1}.  So oper-closure from
#         diagSeq seeds is EXACTLY ST_PS.  Deep BFS, intermediate Lng>=14.
seeds=[diagSeq(u,u+d) for u in range(0,8) for d in range(1,9)]
seen=set(); q=deque(seeds)
tot=pref=eqc=0
deep=deep_pref=0          # Lng(N)>=14
deepP=deepP_pref=0        # Lng(P N)>=14 (many components -> deep P-structure)
noPref=[]
# branch stats: classify by whether bJ is proper-prefix / equal / neither
eq_deep=pp_deep=0
maxlenP=0
t0=time.time()
NMAX=60          # cap on Lng(N) to keep BFS finite
NRANGE=range(1,7)   # oper multipliers
while q and time.time()-t0<240:
    M=q.popleft(); k=tuple(M)
    if k in seen: continue
    seen.add(k)
    if multiT(M):
        comps=P(M); c=Pcut(M); bJ=M[c:]
        if len(comps)>=2 and bJ!=[(0,0)]:
            bJm1=comps[-2]; tot+=1
            p=is_prefix(bJ,bJm1)
            if p: pref+=1
            else: noPref.append((list(M),bJ,bJm1,c))
            if bJ==bJm1: eqc+=1
            LP=len(comps); maxlenP=max(maxlenP,LP)
            if Lng(M)>=14:
                deep+=1
                if p: deep_pref+=1
                if p and bJ==bJm1: eq_deep+=1
                if p and bJ!=bJm1: pp_deep+=1
            if LP>=14:
                deepP+=1
                if p: deepP_pref+=1
    if Lng(M)<=NMAX:
        for nn in NRANGE:
            try: M2=oper(M,nn)
            except Exception: continue
            if M2!=M and tuple(M2) not in seen: q.append(M2)

print("=== r40 pcompPrefix deep validation over TRUE ST_PS (oper-closure of diagSeq, u in 0..7) ===")
print("visited states=%d  nontriv-junction multiT hosts=%d"%(len(seen),tot))
print("bJ prefix-of bJm1 = %d / %d   (equality=%d, proper-prefix=%d)"%(pref,tot,eqc,pref-eqc))
print("DEEP Lng(N)>=14:  prefix %d / %d   (eq=%d, proper=%d)"%(deep_pref,deep,eq_deep,pp_deep))
print("DEEP Lng(P N)>=14: prefix %d / %d   maxLng(P N)=%d"%(deepP_pref,deepP,maxlenP))
print("NO-PREFIX cases: %d"%len(noPref))
for M,bJ,bJm1,c in noPref[:20]:
    print("  Pcut=%d last=%s 2nd=%s Lng=%d M=%s"%(c,bJ,bJm1,len(M),M))
