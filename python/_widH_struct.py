#!/usr/bin/env python3
"""Understand widH: under C, is RightNodes(Trans M)!1 pinned to e1 j1'?
Tabulate which keystone disjunct lands (e1 j1' vs e1 j0') under condition C,
crossed with j1eq / Admpos."""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
from red_model import (Lng, entry, monoT, TrMax, Br, FirstNodes, Joints,
                       parent, Adm, adm)
from trans_model import Trans, reduced

def RightNodes(t):
    ps = t[1]
    if not ps: return []
    v, body = ps[-1][1], ps[-1][2]
    return [v] + RightNodes(body)

def gen_seqs(maxlen, maxval):
    # generate reduced monoT pairseqs with Br != [] and Lng-1>1
    res = []
    for n in range(4, maxlen+1):
        for seq in itertools.product(
                [(a,b) for a in range(maxval+1) for b in range(maxval+1)], repeat=n):
            M = list(seq)
            if M[0] != (0,0) and M[0] != (1,1): continue
            try:
                if not monoT(M): continue
                if not reduced(M): continue
            except Exception:
                continue
            if Br(M) == []: continue
            if Lng(M)-1 <= 1: continue
            res.append(M)
    return res

def analyze(seqs):
    rows = []
    for M in seqs:
        try:
            J1 = Lng(Br(M))-1
            j0p = Joints(M)[J1]
            j1p = FirstNodes(M)[J1]
            e1j1 = entry(M,1,j1p); e1j0 = entry(M,1,j0p)
            e0j1 = entry(M,0,j1p)
            C = (j0p == 0) or (e0j1 == e1j1)
            if not C: continue
            t = Trans(M)
            rn = RightNodes(t)
            if len(rn) < 2: continue
            rn1 = rn[1]
            j1 = Lng(M)-1
            j1eq = (j1p == j1)
            tj0 = parent(M,0,j1)
            admpos = Adm(M, tj0) > 0
            lands = 'j1p' if rn1==e1j1 else ('j0p' if rn1==e1j0 else '???')
            widH = e1j1 <= rn1
            rows.append((M, j1eq, admpos, e1j1, e1j0, rn1, lands, widH,
                         (j0p==0), (e0j1==e1j1)))
        except Exception as ex:
            continue
    return rows

seqs = gen_seqs(6, 3)
rows = analyze(seqs)
print("total C-satisfying:", len(rows))
fails = [r for r in rows if not r[7]]
print("widH FAILS:", len(fails))
for r in fails[:20]:
    print("  FAIL", r[0], "j1eq",r[1],"admpos",r[2],"e1j1",r[3],"e1j0",r[4],"rn1",r[5],r[6])

# breakdown of landing
from collections import Counter
print("landing counts:", Counter(r[6] for r in rows))
# when lands on j0p (the dangerous case), what are j1eq/admpos/C-disjunct?
j0land = [r for r in rows if r[6]=='j0p']
print("lands on j0p:", len(j0land))
print("  of those e1j1<=e1j0:", sum(1 for r in j0land if r[3]<=r[4]))
print("  j1eq distribution:", Counter(r[1] for r in j0land))
print("  C1(j0=0) distribution:", Counter(r[8] for r in j0land))
print("  C2(e0j1=e1j1) distribution:", Counter(r[9] for r in j0land))
for r in j0land[:15]:
    print("   J0LAND", r[0], "j1eq",r[1],"admpos",r[2],"e1j1",r[3],"e1j0",r[4],"C1",r[8],"C2",r[9])
