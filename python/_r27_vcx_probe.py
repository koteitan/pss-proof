#!/usr/bin/env python3
r"""r27 VECLOSE probe: in the collapse residual (j1'=j1 STEP regime, TrMax+2<Lng,
0<m, m>=transJm1), study
  (a) whether transJm1 is really always 0 (rule out transJm1=TrMax),
  (b) whether the boundary m == transJ0(Q) is ever hit,
  (c) at boundary: entry Q 1 j0 < entry Q 1 j1 ? entry Q 1 j1 > 0 ?
      entry Q 1 j0 <= entry Q 0 j0 (row1<=row0) ? condV Q ?
  (d) generally: does entry M 1 j <= entry M 0 j hold on all reduced monoT hosts?
DEEP: brute straddle up to Lng 8 maxval 2/3.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper, seg,
                       Br, Joints, FirstNodes, TrMax, Red, Adm, fmt, adm)
from trans_model import Trans, Mark, Pred, bpHeadT, reduced, addBT, Dpt, ZB

def descending(br):
    n = len(br)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0, a1 = entry(br[J0], 0, 0), entry(br[J0], 1, 0)
            b0, b1 = entry(br[J1], 0, 0), entry(br[J1], 1, 0)
            if not (a0 >= b0 and (a0 != b0 or a1 >= b1)):
                return False
    return True

def regime(M, m):
    br = Br(M)
    if not br: return False
    j1 = Lng(M) - 1; J1 = len(br) - 1
    j0p = Joints(M)[J1]; j1p = FirstNodes(M)[J1]
    if m > j1 - 1: return False
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p) and descending(br))

def host(M):
    if Lng(M) < 3 or zeroT(M) or not monoT(M): return False
    if not reduced(M): return False
    return Br(M) != []

def cfbx_j1p(M):
    br = Br(M); return FirstNodes(M)[len(br) - 1]
def transJ0(M):  return parent(M, 0, Lng(M) - 1)
def transJm1(M): return Adm(M, transJ0(M))

def gen_brute(maxlen, maxval):
    pool = []
    cols = [(a, b) for a in range(maxval + 1) for b in range(maxval + 1)]
    for L in range(3, maxlen + 1):
        for tail in itertools.product(cols, repeat=L - 1):
            M = [(0, 0)] + list(tail)
            if zeroT(M) or not monoT(M): continue
            if not reduced(M): continue
            if Br(M) == []: continue
            pool.append(M)
    return pool

def main():
    pool = gen_brute(6, 3) + gen_brute(7, 2)
    c = {'coll_rows':0, 'coll_tjm1pos':0, 'boundary(m==j0)':0,
         'bnd_e1j0<e1j1':0, 'bnd_e1j0>=e1j1_BAD':0,
         'bnd_e1j1>0':0, 'bnd_e1j1==0_BAD':0,
         'bnd_condV_Q':0, 'bnd_condV_false':0,
         'row1<=row0_all':0, 'row1>row0_BAD':0}
    bad_ex=[]; bnd_ex=[]
    # (d) global row1<=row0 check
    for M in pool:
        if not host(M): continue
        ok=True
        for j in range(Lng(M)):
            if entry(M,1,j) > entry(M,0,j): ok=False; break
        if ok: c['row1<=row0_all']+=1
        else:
            c['row1>row0_BAD']+=1
            if len(bad_ex)<5: bad_ex.append(fmt(M))
    # collapse residual study
    for M in pool:
        if not host(M): continue
        j1=Lng(M)-1; Tr=TrMax(M)
        if not (Tr+2<Lng(M)): continue
        if cfbx_j1p(M)!=j1: continue
        j0=transJ0(M)
        for m in range(1, min(j0, j1-1)+1):
            if not regime(M,m): continue
            tj=transJm1(M)
            if m<tj: continue   # deepen
            c['coll_rows']+=1
            if tj!=0: c['coll_tjm1pos']+=1
            if m==j0:
                c['boundary(m==j0)']+=1
                e1j0=entry(M,1,j0); e1j1=entry(M,1,j1); e0j0=entry(M,0,j0)
                if e1j0<e1j1: c['bnd_e1j0<e1j1']+=1
                else:
                    c['bnd_e1j0>=e1j1_BAD']+=1
                    if len(bnd_ex)<8: bnd_ex.append((fmt(M),m,f'e1j0={e1j0} e1j1={e1j1}'))
                if e1j1>0: c['bnd_e1j1>0']+=1
                else: c['bnd_e1j1==0_BAD']+=1
                condV = (e1j1>0 and e1j0+1==e1j1 and j0+1<j1)
                if condV: c['bnd_condV_Q']+=1
                else: c['bnd_condV_false']+=1
    print("counts:", c, flush=True)
    print("row1>row0 examples:", bad_ex, flush=True)
    print("boundary e1j0>=e1j1 examples:", bnd_ex, flush=True)

if __name__=='__main__':
    main()
