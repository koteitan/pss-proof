#!/usr/bin/env python3
"""Numeric audit for lean/8/8.4-Trans-fseq-condIII-IV.lean (suffix _e34).

Checks, on a genuine ST_PS pool (diagSeq seeds closed under oper):

  (A) hasParent(M,1,j1) is NOT implied by condIII/condIV  -> justifies exposing
      `Exch84_condIIIIV_noParent` as a separate named Prop.
  (B) A32 settlement: the PRINTED conclusion (1)  Trans(M[n]) <= Trans(M)[n-1]
      is TRUE, and the "reverse strict" Trans(M)[n-1] < Trans(M[n]) that
      d13x_exchange13_condIII's note claims to prove is FALSE
      -> the d13x_T hypothesis bundle is vacuous (cf. pss_wip.thy:78648,
         "the r21b-CONDIV-M refutation was of the WRONG single-letter d13x_T form").
  (C) The conclusions actually ported (w84x_exchange13_core):
        (1') Trans(M[n]) <  Trans(M)[n]
        (3)  Trans(M)[n-1] < Trans(M[n+1])
  (D) `Exch84_condIIIIV_noParent` on the no-parent leg, with witness k = m.

Everything runs under the CORRECTED operB (footnote [30] read per A23).
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r56_operBfix_lib as fx  # patches vx.operB / vx.xseq  (A23-corrected)
from _r56_operBfix_lib import operB
from _r15_vx_lib import gen_pool, mono_hosts, Trans, numBT, lessBT, guarded, SKIP, condIV
from red_model import Lng, oper, hasParent, fmt
from trans_model import condIII


def leBT(a, b):
    return lessBT(a, b) or a == b


def main():
    pool = gen_pool(maxlen=6, maxn=3, maxseed=2, cap=400)
    hosts = mono_hosts(pool)
    sel = [M for M in hosts
           if Lng(M) - 1 > 1 and (condIII(M) or condIV(M))]
    print("pool=%d  mono ST_PS hosts=%d  condIII/IV hosts (j1>1)=%d"
          % (len(pool), len(hosts), len(sel)))

    # ---- (A) hasParent is a genuine extra hypothesis -------------------------
    nohp = [M for M in sel if not hasParent(M, 1, Lng(M) - 1)]
    print("\n(A) hasParent(M,1,j1) FAILURES among condIII/IV hosts: %d/%d"
          % (len(nohp), len(sel)))
    for M in nohp[:4]:
        print("      no-parent host:", fmt(M))

    # ---- (B)/(C)/(D) --------------------------------------------------------
    tally = {t: dict(tot=0, printed1=0, rev1=0, corr1=0, concl3=0, nohp_km=0)
             for t in ("HP", "NOHP")}
    for M in sel:
        tag = "HP" if hasParent(M, 1, Lng(M) - 1) else "NOHP"
        TM = guarded(Trans, M, budget=8)
        if TM is SKIP or TM is None:
            continue
        for n in range(1, 4):
            Mn = guarded(oper, M, n, budget=6)
            Mn1 = guarded(oper, M, n + 1, budget=6)
            if Mn is SKIP or Mn is None or Mn1 is SKIP or Mn1 is None:
                continue
            TMn = guarded(Trans, Mn, budget=8)
            TMn1 = guarded(Trans, Mn1, budget=8)
            if TMn is SKIP or TMn is None or TMn1 is SKIP or TMn1 is None:
                continue
            Xn1, Xn = operB(TM, numBT(n - 1)), operB(TM, numBT(n))
            t = tally[tag]
            t["tot"] += 1
            t["printed1"] += leBT(TMn, Xn1)          # article (1)  [A32 retracted]
            t["rev1"] += lessBT(Xn1, TMn)            # d13x note's claim
            t["corr1"] += lessBT(TMn, Xn)            # ported (1')
            t["concl3"] += lessBT(Xn1, TMn1)         # article (3)
            if n > 1:
                t["nohp_km"] += leBT(TMn, Xn)        # Prop witness k = m

    for tag in ("HP", "NOHP"):
        t = tally[tag]
        if not t["tot"]:
            continue
        print("\n[%s]  instances=%d" % (tag, t["tot"]))
        print("  (B) printed (1)   Trans(M[n]) <= Trans(M)[n-1] : %d/%d"
              % (t["printed1"], t["tot"]))
        print("  (B) d13x reverse  Trans(M)[n-1] <  Trans(M[n])  : %d/%d   <-- expect 0"
              % (t["rev1"], t["tot"]))
        print("  (C) ported (1')   Trans(M[n]) <  Trans(M)[n]    : %d/%d"
              % (t["corr1"], t["tot"]))
        print("  (C) article (3)   Trans(M)[n-1] < Trans(M[n+1]) : %d/%d"
              % (t["concl3"], t["tot"]))
        print("  (D) Prop witness  Trans(M[m]) <= Trans(M)[m]    : %d"
              % t["nohp_km"])


if __name__ == "__main__":
    main()
