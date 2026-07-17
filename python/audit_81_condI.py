#!/usr/bin/env python3
"""Adversarial numeric audit for lean/8/8.1-Trans-fseq-condI.lean.

Targets (public claims re-stated 1:1 from the Lean source):

  * `CondI_masterCF`      <- Isabelle `scx_condI_j0pos_masterCF` (wip 83639).
        The ONE Prop this file exposes.  If it were FALSE the whole
        green-modulo file would rest on a false hypothesis, so it is checked
        conclusion-first, not just for satisfiability.
  * `condI_exchange1`     <- Isabelle `y3g_condI_exchange1_rtps` (scratch 14693)
  * `condI_descent`       <- Isabelle `y3g_condI_descent_rtps`   (scratch 14760)
  * `Trans_fseq_condI`    <- article p_8_1_Trans_fseq_condI (paper 1769)
  * `exchI_holds`         <- `FseqDesc_exchI` of 8.7-fseq-descend

Also re-checks the two ALREADY-EXPOSED bricks this file reuses from the built
8.7-fseq-descend, since the exchange now depends on them:

  * `FseqDesc_operI_j0zero_trans_mult`
        <- Isabelle `operI_j0zero_trans_mult` (wip 36977)
  * `FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1`
        <- Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause1` (wip 19436)

Semantics: python/red_model.py + python/trans_model.py (canonical models) and
the operB/numBT of python/_r15_vx_lib.py (A23-corrected footnote [30] rule).

Pool: diagSeq closed under `oper`, plus row-0 ancestor slices Red(seg(...))
and the Pred-closure -- the established idiom (random pair sequences are
almost never reduced, so this is the only way to exercise M in RT_PS & PT_PS).

Each claim reports (a) how many pool instances exercise it NON-VACUOUSLY and
(b) how many of those falsify the conclusion.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import red_model as rm
import trans_model as tm
import _r15_vx_lib as vx

Lng, entry, oper, Pred, Red, seg, diagSeq = (
    rm.Lng, rm.entry, rm.oper, rm.Pred, rm.Red, rm.seg, rm.diagSeq)
monoT, parent, hasParent = rm.monoT, rm.parent, rm.hasParent
Mark, adm, Adm, reduced = tm.Mark, tm.adm, tm.Adm, tm.reduced
condI = tm.condI
ZB, Dpt, addBT, flatBT, flatBP, unflatBT = (
    tm.ZB, tm.Dpt, tm.addBT, tm.flatBT, tm.flatBP, tm.unflatBT)
operB, numBT, multBT = vx.operB, vx.numBT, vx.multBT

# Red / Trans are the hot spots (Red on every ancestor slice; Trans on every
# iterate).  Both are pure functions of the sequence, so memoise on the tuple.
_RED, _TRANS = {}, {}


def Red(M):
    k = tuple(M)
    r = _RED.get(k)
    if r is None:
        r = _RED[k] = rm.Red(list(M))
    return list(r)


def Trans(M):
    k = tuple(M)
    r = _TRANS.get(k)
    if r is None:
        r = _TRANS[k] = tm.Trans(list(M))
    return r


def RTPS(M):
    return bool(M) and reduced(M)


def lessBT(a, b):
    return _lessBPList(a[1], b[1])


def _lessBP(p, q):
    return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))


def _lessBPList(a, b):
    if not a and not b:
        return False
    if not a:
        return True
    if not b:
        return False
    return _lessBP(a[0], b[0]) or (a[0] == b[0] and _lessBPList(a[1:], b[1:]))


# ------------------------------------------------- pool (established idiom)
def standard_pool(umax=4, vmax=7, nmax=5, gens=5, lenCap=16):
    pool, seen = [], set()
    for u in range(umax + 1):
        for v in range(u, vmax + 1):
            M = diagSeq(u, v)
            t = tuple(M)
            if t not in seen:
                seen.add(t)
                pool.append(M)
    frontier = list(pool)
    for _ in range(gens):
        nxt = []
        for M in frontier:
            for n in range(1, nmax + 1):
                N = oper(M, n)
                if Lng(N) > lenCap:
                    continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t)
                    pool.append(N)
                    nxt.append(N)
        frontier = nxt
    return pool


def rtps_mono_pool(base, lenCap=13):
    cand, seen = [], set()

    def push(M):
        if not M or Lng(M) > lenCap:
            return
        t = tuple(M)
        if t in seen:
            return
        seen.add(t)
        cand.append(M)

    for M in base:
        push(M)
        L = Lng(M)
        for j1 in range(1, L):
            for j0 in range(j1):
                if not rm.le0(M, j0, j1):
                    continue
                push(Red(seg(M, j0, j1)))
    i = 0
    while i < len(cand):
        M = cand[i]
        i += 1
        if Lng(M) > 1:
            push(Pred(M))
    return [M for M in cand if RTPS(M) and monoT(M)]


# ------------------------------------------------------------- claim table
class Claim:
    def __init__(self, name, src):
        self.name, self.src, self.hit, self.bad = name, src, 0, 0
        self.cex = []

    def check(self, ok, M, extra=""):
        self.hit += 1
        if not ok:
            self.bad += 1
            if len(self.cex) < 3:
                self.cex.append((M, extra))

    def report(self):
        flag = "OK   " if self.bad == 0 else "FAIL "
        if self.hit == 0:
            flag = "VAC  "
        print(f"  {flag} {self.name:38s} {self.hit:6d} exercised, "
              f"{self.bad:4d} counterexamples   [{self.src}]")
        for M, extra in self.cex:
            print(f"        CEX {M}  {extra}")


# --------------------------- masterCF witness search (D_u(t0 + D_v(t1+D_0 0)))
def _succ_shape(body):
    """body = t0 +_B D_v (t1 +_B D_0 0)?  -> (u_free) returns (t0, v, t1) or None."""
    ps = body[1]
    if not ps:
        return None
    last = ps[-1]                       # ('D', v, inner)
    v, inner = last[1], last[2]
    ips = inner[1]
    if not ips:
        return None
    if ips[-1] != ('D', 0, ZB):
        return None
    t0 = ('T', list(ps[:-1]))
    t1 = ('T', list(ips[:-1]))
    return (t0, v, t1)


def masterCF_witnesses(M, kmax=4):
    """All (s,b,u,v,t0,t1) meeting dM; returns list of (witness, lhs_ok)."""
    t = Trans(M)
    out = []
    for i, p in enumerate(t[1]):
        # every top-level principal is an scb position with b = "" only when it
        # is the last one; the general scb positions are found by flat search.
        pass
    # enumerate every principal occurrence at any depth, via flat scan
    f = flatBT(t)
    n = len(f)
    for i in range(n):
        if not (isinstance(f[i], tuple) and f[i][0] == 'D'):
            continue
        # try to parse a full principal code starting at i
        for j in range(i + 2, n + 1):
            c = f[i:j]
            if not tm.isPTB_str(c):
                continue
            b = f[j:]
            if not all(x == ')' for x in b):
                continue
            s = f[:i]
            core = unflatBT(c)          # ('T',[('D',u,body)])
            if len(core[1]) != 1:
                continue
            u, body = core[1][0][1], core[1][0][2]
            sh = _succ_shape(body)
            if sh is None:
                continue
            t0, v, t1 = sh
            ok = True
            for k in range(1, kmax + 1):
                lhs = Trans(oper(M, k + 1))
                rhs = unflatBT(list(s) + flatBT(
                    Dpt(u, addBT(t0, multBT(Dpt(v, t1), k + 1)))) + list(b))
                if lhs != rhs:
                    ok = False
                    break
            out.append(((s, b, u, v, t0, t1), ok))
            break
    return out


# ------------------------------------------------------------------- main
def main():
    umax = int(os.environ.get("A81_UMAX", 4))
    vmax = int(os.environ.get("A81_VMAX", 7))
    lenCap = int(os.environ.get("A81_LENCAP", 13))
    base = standard_pool(umax=umax, vmax=vmax)
    pool = rtps_mono_pool(base, lenCap=lenCap)
    print(f"standard pool (diagSeq closed under oper): {len(base)} forms")
    print(f"RT_PS & PT_PS pool (+ancestor slices, +Pred-closure): {len(pool)}")

    c_master = Claim("CondI_masterCF", "wip 83639")
    c_exch = Claim("condI_exchange1", "scratch 14693")
    c_desc = Claim("condI_descent", "scratch 14760")
    c_exchI = Claim("exchI_holds / FseqDesc_exchI", "8.7-fseq-descend:71")
    c_mul = Claim("FseqDesc_operI_j0zero_trans_mult", "wip 36977")
    c_a0 = Claim("FseqDesc_..._Adm0_clause1", "wip 19436")

    n_hyp = n_j0pos = n_j0zero = 0
    for M in pool:
        if not (Lng(M) - 1 > 1 and condI(M)):
            continue
        j1 = Lng(M) - 1
        if not hasParent(M, 0, j1):
            continue
        n_hyp += 1
        j0 = parent(M, 0, j1)
        if j0 > 0:
            n_j0pos += 1
        else:
            n_j0zero += 1

        # ---- CondI_masterCF (j0 > 0 only)
        if j0 > 0:
            ws = masterCF_witnesses(M)
            good = [w for w, ok in ws if ok]
            c_master.check(len(good) > 0, M,
                           f"{len(ws)} shape-matching scb positions, "
                           f"{len(good)} with valid lhsCF")

        # ---- exchange (1) and descent (2), all n >= 1
        for n in range(1, 6):
            lhs = Trans(oper(M, n))
            rhs = operB(Trans(M), numBT(n - 1))
            c_exch.check(lhs == rhs, M, f"n={n}: {lhs} vs {rhs}")
            c_desc.check(lessBT(lhs, Trans(M)), M, f"n={n}")
            if n > 1 and j0 > 0:
                c_exchI.check(lhs == rhs, M, f"m={n}")

        # ---- the two reused bricks
        if j0 == 0:
            for k in range(0, 5):
                lhs = Trans(oper(M, k + 1))
                rhs = multBT(Trans(Pred(M)), k + 1)
                c_mul.check(lhs == rhs, M, f"k={k}")
        jm1 = Adm(M, j0)
        if jm1 == 0:
            t1s = [t for t in _all_bodies(M)]
            c_a0.check(len(t1s) == 1, M, f"{len(t1s)} witnesses")

    print(f"\nhypothesis set (RT&PT & Lng-1>1 & condI & hasParent): {n_hyp}")
    print(f"  of which j0 > 0 (the FseqDesc_exchI / masterCF regime): {n_j0pos}")
    print(f"  of which j0 = 0 (the copy-additivity regime)          : {n_j0zero}")
    print()
    for c in (c_master, c_exch, c_desc, c_exchI, c_mul, c_a0):
        c.report()
    bad = sum(c.bad for c in (c_master, c_exch, c_desc, c_exchI, c_mul, c_a0))
    vac = [c.name for c in (c_master, c_exch, c_desc, c_exchI) if c.hit == 0]
    print()
    if bad:
        print(f"RESULT: {bad} COUNTEREXAMPLE(S) -- a claim is WRONG.")
        return 1
    if vac:
        print(f"RESULT: VACUOUS claims (0 instances): {vac}")
        return 1
    print("RESULT: no counterexample, no vacuous claim.")
    return 0


def _all_bodies(M):
    """t1 with Trans(Pred M) = D_{M_{1,0}} t1 and Trans M = D_{M_{1,0}}(t1 + D_{M_{1,j1}} 0)."""
    j1 = Lng(M) - 1
    e10 = entry(M, 1, 0)
    tp, tM = Trans(Pred(M)), Trans(M)
    out = []
    if len(tp[1]) == 1 and tp[1][0][1] == e10:
        t1 = tp[1][0][2]
        if tM == Dpt(e10, addBT(t1, Dpt(entry(M, 1, j1), ZB))):
            out.append(t1)
    return out


if __name__ == "__main__":
    sys.exit(main())
