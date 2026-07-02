#!/usr/bin/env python3
"""Diagnose: for failing condIII/V hosts, what IS the relation between
Trans(M[m]) and the operB fundamental sequence?  Print actual terms, and
search for j s.t. Trans(M[m]) = promote_leaf(operB(Trans M)(numBT j), v)."""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
import trans_model as tm, red_model as rm, buchholz as B
ZB = tm.ZB
def conv(t): return [('D', p[1], conv(p[2])) for p in t[1]]
def bp_to_tm(p): return ('D', p[1], ('T', [bp_to_tm(q) for q in p[2]]))
def deepest_leaf_idx(bt):
    ps=bt[1]
    if not ps: return None
    _,w,body=ps[-1]
    return w if body[1]==[] else deepest_leaf_idx(body)
def promote_leaf(bt,newv):
    ps=bt[1]; _,w,body=ps[-1]
    if body[1]==[]: return ('T', ps[:-1]+[('D',newv,ZB)])
    return ('T', ps[:-1]+[('D',w,promote_leaf(body,newv))])

HOSTS = [
  [(0,0),(1,1),(2,1)],
  [(0,0),(1,1),(2,1),(2,1)],
  [(0,0),(1,1),(2,1),(3,1)],
  [(0,0),(1,1),(2,2),(3,1)],
  [(0,0),(1,1),(1,1),(1,1)],
  [(0,0),(1,1),(2,2),(2,2)],
]
for M in HOSTS:
    TM=tm.Trans(M); TMb=conv(TM); v=rm.entry(M,1,rm.Lng(M)-1)
    print(f"M={M}  v={v}  Trans M = {B.fmt(TMb)}")
    for j in range(0,5):
        Rj=B.bracket(TMb,B.nat(j))
        print(f"    operB(numBT {j}) = {B.fmt(Rj)}")
    for m in range(2,4):
        Mm=rm.oper(M,m); TMm=conv(tm.Trans(Mm))
        print(f"    Trans(M[{m}]) = {B.fmt(TMm)}   leaf={deepest_leaf_idx(tm.Trans(Mm))}")
        # search j: promote_leaf(operB(numBT j), v) == Trans(M[m])
        match=[]
        for j in range(0,m+3):
            Rj=B.bracket(TMb,B.nat(j))
            Rt=('T',[bp_to_tm(p) for p in Rj])
            if Rt[1] and conv(promote_leaf(Rt,v))==TMm: match.append(('prom',j))
            if Rj==TMm: match.append(('eq',j))
            if B.le_term(TMm,Rj): match.append(('le',j))
        print(f"        matches: {match}")
    print()
