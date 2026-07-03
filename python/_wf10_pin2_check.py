#!/usr/bin/env python3
"""Does length s pinning hold for ANY two scb_decomps (not just same-kind)?
i.e. is the cut determined purely by (principal c=flatBP p) + (b all-RP)?
Also: characterise the cut as: the start of the LAST principal-flat-prefix
whose remaining tail is all-RP. Test that the cut = len(ft) - (len(c)+len(b))
is forced by: c@b is the maximal balanced suffix starting at a principal boundary.
"""
import itertools

LP, CM, RP, Zsym = 'LP', 'CM', 'RP', 'Zsym'
def Dsym(u): return ('Dsym', u)
def Trm(ps): return ('Trm', tuple(ps))
def DB(v, a): return ('D', v, a)
def flatBP(p):
    _, u, a = p
    return [Dsym(u)] + flatBT(a)
def flatBT(t):
    _, ps = t
    if len(ps) == 0: return [Zsym]
    if len(ps) == 1: return flatBP(ps[0])
    head = ps[0]; rest = ps[1:]
    mid = []
    for r in rest: mid += [CM] + flatBP(r)
    return [LP] + (flatBP(head) + mid) + [RP]
def dfree_BT(t):
    _, ps = t; return all(dfree_BP(p) for p in ps)
def dfree_BP(p):
    _, v, a = p; return v != 'INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)
def enum_terms(depth, idxs, max_princ):
    if depth == 0: return [Trm([])]
    sub = enum_terms(depth-1, idxs, max_princ)
    princ = [DB(v,a) for v in idxs for a in sub]
    terms = [Trm([])]
    for k in range(1, max_princ+1):
        for combo in itertools.product(princ, repeat=k):
            terms.append(Trm(list(combo)))
    return terms

IDXS=[0,1,2]; DEPTH=2; MAXP=2
ALL_TERMS = enum_terms(DEPTH, IDXS, MAXP)
ALL_PRINC=[]
for t in ALL_TERMS:
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
for t in enum_terms(DEPTH+1, IDXS, 1):
    for p in t[1]:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
PRINC_SET = set(tuple(flatBP(p)) for p in ALL_PRINC if dfree_BP(p))
def isPTB_str(c): return tuple(c) in PRINC_SET
def scb_decomp(t,s,c,b):
    if flatBT(t)!=s+c+b: return False
    if t!=Trm([]) and not isPTB_str(c): return False
    return all(x==RP for x in b)
def all_decomps(t):
    ft=flatBT(t); n=len(ft); out=[]
    for i in range(n+1):
        for k in range(n-i+1):
            s=ft[:i]; c=ft[i:i+k]; b=ft[i+k:]
            if scb_decomp(t,s,c,b): out.append((s,c,b))
    return out

TB=[t for t in ALL_TERMS if in_TB(t) and t!=Trm([])]
# Q1: does len(s) pin across ALL scb_decomps (any kind)?
fail_any=0; tot=0; multi=0
for t in TB:
    ds=all_decomps(t)
    if not ds: continue
    tot+=1
    lens=set(len(s) for (s,c,b) in ds)
    if len(lens)>1:
        fail_any+=1
        if fail_any<=10:
            print("MULTI-CUT t=",t)
            for (s,c,b) in sorted(ds,key=lambda x:len(x[0])):
                print("   len(s)=",len(s)," c=",c," b=",b)
print(f"Q1 ANY-kind pinning: {fail_any}/{tot} terms have multiple distinct cuts")
