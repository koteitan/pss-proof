#!/usr/bin/env python3
# Directly verify the reach-conditioned WRAP'/KER counterexample.
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       le0, marked, nextrel0)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt

def show(M):
    print(f"--- H={rm.fmt(M)} reduced={reduced(M)} monoT={monoT(M)} ---")
    n=Lng(M)
    q,c=1,3
    am=Adm(M,q)
    print(f" Lng={n} q={q} c={c} Adm(H,{q})={am} adm(H,{q})={adm(M,q)}")
    print(f" marked(H,Adm)={marked(M,am)}  le0(H,{q},{c})={le0(M,q,c)}  (=reach guard)")
    sq=seg(M,q,c); sa=seg(M,am,c)
    print(f" seg H {q} {c}={rm.fmt(sq)}  monoT={monoT(sq)}  reduced={reduced(sq)}")
    print(f" seg H {am} {c}={rm.fmt(sa)}  monoT={monoT(sa)}  reduced={reduced(sa)}")
    Tq=Trans(sq); Ta=Trans(sa)
    print(f" Trans(seg H {q} {c}) = {Tq}")
    print(f"   bpHeadT = {bpHeadT(Tq)}")
    print(f" Trans(seg H {am} {c}) = {Ta}")
    print(f"   bpHeadT = {bpHeadT(Ta)}")
    # WRAP'(r=1): Trans(seg H 1 3) =?= Dpt(entry H 1 1)(bpHeadT(Trans(seg H 0 3)))
    rhs = Dpt(entry(M,1,q), bpHeadT(Ta))
    print(f" WRAP'(r={q}): Trans(seg H {q} {c}) == Dpt(entry H 1 {q})(bpHeadT(Trans(seg H {am} {c})))?")
    print(f"   LHS={Tq}")
    print(f"   RHS={rhs}")
    print(f"   WRAP' HOLDS = {Tq==rhs}")
    print(f" KER: bpHeadT(seg Adm)==bpHeadT(seg q)?  {bpHeadT(Ta)==bpHeadT(Tq)}")
    # also W1': single principal shape of seg H 1 3
    w1 = Dpt(entry(M,1,q), bpHeadT(Tq))
    print(f" W1'(single-principal seg H {q} {c}): {Tq==w1}")
    print()

for M in [
    [(0,0),(1,1),(2,2),(2,0)],
    [(0,0),(1,1),(2,2),(2,1)],
    [(0,0),(1,1),(2,2),(1,0)],  # r25 CEX (reach FALSE -> excluded)
]:
    show(M)
