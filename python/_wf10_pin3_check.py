#!/usr/bin/env python3
"""Pin-mechanism: within a fixed kind, is RightNodes(c) the SAME suffix of
RightNodes(t) for both decompositions? Verify:
  (A) within kind0: all decomps have len(RightNodes c)=2 and RN(c)=[v,0] => c suffix-seg of t fixed by:
      RN(c) = last 2 of RN(t)?  NO - need the kind cond to select among suffixes.
  Strategy that the formal proof will use:
    cut len(s) is determined by: c = flatBP p where RightNodes(Trm[p]) (=suffix of RightNodes t)
    has the kind-specific shape. We show j1_i (=len RN(c)-1) is UNIQUE given the kind,
    hence the suffix RN(c) = drop (len RN t - len RN c) (RN t) is unique, hence v0=RN(c)!0 unique,
    hence (article) the cut s ends right before the (j0=len RN t - len RN c)-th spine node = unique.
We test: within each kind, for all decomps of t, (len RN c) is constant AND
  len(s) is a strictly-monotone function of (len RN c) [longer RN c <-> earlier cut].
Also: print, for each t, the map  len(RN c) -> len(s)  over ALL decomps (any kind),
  to confirm len(RN c) ALONE determines len(s).
"""
import itertools
LP, CM, RP, Zsym = 'LP', 'CM', 'RP', 'Zsym'
def Dsym(u): return ('Dsym', u)
def Trm(ps): return ('Trm', tuple(ps))
def DB(v, a): return ('D', v, a)
def flatBP(p):
    _, u, a = p; return [Dsym(u)] + flatBT(a)
def flatBT(t):
    _, ps = t
    if len(ps)==0: return [Zsym]
    if len(ps)==1: return flatBP(ps[0])
    head=ps[0]; rest=ps[1:]; mid=[]
    for r in rest: mid += [CM] + flatBP(r)
    return [LP] + (flatBP(head)+mid) + [RP]
def RightNodes_T(t):
    _, ps = t
    if len(ps)==0: return []
    _, u, a = ps[-1]; return [u] + RightNodes_T(a)
def dfree_BT(t):
    return all(dfree_BP(p) for p in t[1])
def dfree_BP(p):
    _, v, a = p; return v!='INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)
def enum_terms(depth, idxs, mp):
    if depth==0: return [Trm([])]
    sub=enum_terms(depth-1,idxs,mp)
    princ=[DB(v,a) for v in idxs for a in sub]
    terms=[Trm([])]
    for k in range(1,mp+1):
        for combo in itertools.product(princ,repeat=k):
            terms.append(Trm(list(combo)))
    return terms
IDXS=[0,1,2]; DEPTH=2; MAXP=2
ALL=enum_terms(DEPTH,IDXS,MAXP)
ALL_PRINC=[]
for t in ALL:
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
for t in enum_terms(DEPTH+1,IDXS,1):
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
PMAP={}
for p in ALL_PRINC:
    if dfree_BP(p): PMAP.setdefault(tuple(flatBP(p)),p)
def isPTB(c): return tuple(c) in PMAP
def getp(c): return PMAP.get(tuple(c))
def scb(t,s,c,b):
    if flatBT(t)!=s+c+b: return False
    if t!=Trm([]) and not isPTB(c): return False
    return all(x==RP for x in b)
def decomps(t):
    ft=flatBT(t); n=len(ft); out=[]
    for i in range(n+1):
        for k in range(n-i+1):
            s=ft[:i]; c=ft[i:i+k]; b=ft[i+k:]
            if scb(t,s,c,b): out.append((s,c,b))
    return out
def RNc(c):
    p=getp(c)
    return RightNodes_T(Trm([p])) if p is not None else None

TB=[t for t in ALL if in_TB(t) and t!=Trm([])]
# Q: does (len RN c) ALONE determine len(s)? i.e. is map injective over decomps
fail_func=0
fail_suffix=0; sfx_chk=0
for t in TB:
    ds=decomps(t)
    if not ds: continue
    rnt=RightNodes_T(t)
    m={}
    for (s,c,b) in ds:
        r=RNc(c)
        if r is None: continue
        L=len(r)
        # suffix claim: r == rnt[len(rnt)-L:]
        sfx_chk+=1
        if rnt[len(rnt)-L:]!=r:
            fail_suffix+=1
            if fail_suffix<=8: print("SFXFAIL t=",t," rnt=",rnt," rnc=",r," len(s)=",len(s))
        if L in m and m[L]!=len(s):
            fail_func+=1
            if fail_func<=8: print("FUNCFAIL t=",t," L=",L," lens=",m[L],len(s))
        m[L]=len(s)
print(f"len(RN c) -> len(s) functional: {fail_func} violations")
print(f"RN c == suffix of RN t: {fail_suffix}/{sfx_chk} violations")
