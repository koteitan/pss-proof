#!/usr/bin/env python3
"""Adversarial numeric audit for the §8.2 subexpr-component-Pred campaign.

Targets (public claims re-stated 1:1 from the Lean sources):

  lean/8/8.2-subexpr-wid.lean
    * `wid M`  (def, article-side conclusion of Isabelle `m_8_2_wid`,
      layerB/pss_wip.thy:29605)
    * `ft_transport` (29392), `jt_transport` (29460)
  lean/8/8.2-subexpr-final.lean
    * `wid_holds`                      <- `m_8_2_wid` (29605)
    * `subexpr_component_Pred`         <- `m_8_2_subexpr_component_Pred` (29702)
    * `subexpr_component_Pred_faithful`<- `p_8_2_subexpr_component_Pred`
                                          (isabelle/pss_paper.thy:1523)
    * green-modulo bricks `SXP_wid_cpU`, `SXP_wid_baseU`,
      `SXP_wid_of_predwid`, `SXP_subexpr_component_Pred_of_wid`,
      `SXP_subexpr_component_Pred_Adm0_full`
  lean/8/8.2-subexpr-adm0.lean
    * `subexpr_component_Pred_Adm0`    <- `m_8_2_subexpr_component_Pred_Adm0`
                                          (20828)
  lean/8/8.2-subexpr-adm0-full.lean
    * `subexpr_component_Pred_Adm0_full`
                                       <- `m_8_2_subexpr_component_Pred_Adm0_full`
                                          (27019)

Semantics is python/red_model.py + python/trans_model.py (the canonical
models).  `Red` returns a LIST OF TUPLES; every comparison below stays inside
that representation.  BT terms are ('T', [('D', v, t), ...]); 0_B = ('T', []).

The pool is built the established way (python/strongmono_audit.py,
python/d1pos_*.py): diagSeq closed under `oper`, then every row-0 ancestor
slice `Red(seg(M, j0, j1))`, then the `Pred`-closure of those (the §8.2
induction descends along `Pred`).  Random pair sequences are almost never
reduced, so this is the only way to exercise `M in RT_PS & PT_PS`.

Every claim is reported with (a) how many pool instances satisfy its
hypotheses -- i.e. exercise it NON-VACUOUSLY -- and (b) how many of those
falsify the conclusion.  A single counterexample would mean a wrong statement
got proved in Lean.

FINDINGS (2026-07-17 run, 14618-form pool, maxlen 15, max entry 19):

  * NO COUNTEREXAMPLE to any claim.  `wid` / the 4-clause keystone /
    `..._Adm0_full` / all four green-modulo `SXP_*` bricks / `ft_transport` /
    `jt_transport` all hold on every instance that exercises them.
  * `subexpr_component_Pred_Adm0` (8.2-subexpr-adm0.lean:40) is VACUOUS: its
    hypotheses `hgB` (e0(j1')=e1(j1') | adm j0'), `he0gt` (e1(j1')<e0(j1'))
    and `hnadmj0` (~adm j0') are mutually inconsistent -- he0gt refutes gB's
    left disjunct and hnadmj0 refutes its right one.  0 instances of 14618.
    This is FAITHFUL to Isabelle (m_8_2_subexpr_component_Pred_Adm0, wip
    20828, carries the same assumption set; it is only ever applied on the
    condA branch of m_8_2_subexpr_component_Pred_Adm0_nogB, wip 23862, which
    is itself the contradictory context).  Not a soundness bug -- a dead
    public name, superseded by `subexpr_component_Pred_Adm0_full`.
  * Clause (2) of the keystone never fires: its non-existential guard set
    (j1'=j1 & e1(j1')<e0(j1') & ~adm j0') has 0 hits.  Clause (1) fires
    exactly on the Adm0 branch; (3)/(4) carry everything else.
  * `SXP_wid_cpU` is the thinnest brick: only 18 non-vacuous instances (its
    hypothesis `FirstNodes(M)_{J1} = Lng M - 1` with `Br (Pred M) != []` and
    `transJm1 M > 0` is rare).  The Lean docstring's "empirically 291/291"
    came from a differently-built pool; on this one the sample is small.
    No violation, but the confidence is correspondingly weaker.
  * Model cross-checks that passed on all 14618 forms: Lean `Joints`
    (`parent`, headD 0) agrees with red_model's THE_nextR spelling; Lean
    `reduced` (Red-fixpoint) agrees with trans_model's RedCondA/B spelling.
"""
import sys, os
from functools import lru_cache

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
import trans_model as tm

# --------------------------------------------------------------- speed-ups
# Pure memoisation of the row-0 / row-1 reachability matrices.  No semantic
# change: red_model resolves le0/le1 from module globals at call time.
@lru_cache(maxsize=1 << 20)
def _reach0(Mt):
    return rm.reach(list(Mt), rm.nextrel0)


@lru_cache(maxsize=1 << 20)
def _reach1(Mt):
    return rm.reach(list(Mt), rm.nextrel1)


def _le0_cached(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n):
        return False
    return _reach0(tuple(M))[j0][j1]


def _le1_cached(M, j0, j1):
    n = len(M)
    if not (j0 < n and j1 < n):
        return False
    return _reach1(tuple(M))[j0][j1]


rm.le0 = _le0_cached
rm.le1 = _le1_cached

_trans_cache = {}
_mark_cache = {}
_orig_Trans = tm.Trans
_orig_Mark = tm.Mark


def _Trans_memo(M, depth=0):
    k = tuple(M)
    v = _trans_cache.get(k)
    if v is None:
        v = _orig_Trans(M, depth)
        _trans_cache[k] = v
    return v


def _Mark_memo(M, m, depth=0):
    k = (tuple(M), m)
    v = _mark_cache.get(k)
    if v is None:
        v = _orig_Mark(M, m, depth)
        _mark_cache[k] = v
    return v


tm.Trans = _Trans_memo
tm.Mark = _Mark_memo

Lng, entry, seg = rm.Lng, rm.entry, rm.seg
diagSeq, oper, Pred = rm.diagSeq, rm.oper, rm.Pred
ZB, Dpt, addBT = tm.ZB, tm.Dpt, tm.addBT


@lru_cache(maxsize=1 << 20)
def _Red_t(Mt):
    return tuple(rm.Red(list(Mt)))


def Red(M):
    return list(_Red_t(tuple(M)))


@lru_cache(maxsize=1 << 20)
def _reduced_t(Mt):
    return bool(Mt) and _Red_t(Mt) == Mt


def reduced(M):
    """Lean `reduced M = !M.isEmpty && (Red M == M)` (PSS/Red.lean:104)."""
    return _reduced_t(tuple(M))


def RTPS(M):
    """Lean `RTPS M : Prop := reduced M = true` (PSS/Red.lean:108)."""
    return reduced(M)


@lru_cache(maxsize=1 << 20)
def _monoT_t(Mt):
    return rm.monoT(list(Mt))


def monoT(M):
    return _monoT_t(tuple(M))


@lru_cache(maxsize=1 << 20)
def _TrMax_t(Mt):
    return rm.TrMax(list(Mt))


def TrMax(M):
    return _TrMax_t(tuple(M))


@lru_cache(maxsize=1 << 20)
def _Br_t(Mt):
    return tuple(tuple(C) for C in rm.Br(list(Mt)))


def Br(M):
    return [list(C) for C in _Br_t(tuple(M))]


@lru_cache(maxsize=1 << 20)
def _FirstNodes_t(Mt):
    return tuple(rm.FirstNodes(list(Mt)))


def FirstNodes(M):
    return list(_FirstNodes_t(tuple(M)))


# ------------------------------------------- Lean-faithful Joints / adm / Adm
# WARNING: red_model.Joints uses THE_nextR (None when the parent is not
# unique); Lean `Joints` (PSS/Mono.lean:64) uses `parent M 0 (FirstNodes M)[J]`
# = `(parents M 0 j).headD 0`.  We evaluate the Lean spelling and cross-check
# it against red_model's below (claim J).
def parent_lean(M, i, j1):
    for j0 in range(Lng(M)):
        if rm.nextR(M, i, j0, j1):
            return j0
    return 0


@lru_cache(maxsize=1 << 20)
def _Joints_lean_t(Mt):
    M = list(Mt)
    fn = FirstNodes(M)
    return tuple(parent_lean(M, 0, getD(fn, J, 0)) for J in range(len(Br(M))))


def Joints(M):
    return list(_Joints_lean_t(tuple(M)))


def adm(M, j):
    """Lean `adm` (PSS/Adm.lean:17) == trans_model.adm."""
    return tm.adm(M, j)


def Adm(M, j):
    return tm.Adm(M, j)


def transJ0(M):
    """Lean `transJ0 M = lastParent M = parent M 0 (Lng M - 1)`."""
    return parent_lean(M, 0, Lng(M) - 1)


def transJm1(M):
    """Lean `transJm1 M = Adm M (transJ0 M)`."""
    return Adm(M, transJ0(M))


def transC1(M):
    return tm.Mark(Pred(M), transJm1(M))


def transT2(M):
    return tm.bpHeadT(transC1(M))


def getD(l, n, d):
    return l[n] if n < len(l) else d


def ent(M, i, j):
    """Lean `entry` (PSS/Defs.lean:33): out-of-range index yields 0.
    red_model.entry raises instead, so the claim layer uses this spelling
    (indices such as `FirstNodes M ! (Lng (Br M) - 1)` DO leave the range when
    `Br M = []`)."""
    if j >= Lng(M):
        return 0
    return M[j][0] if i == 0 else M[j][1]


def RightNodes(t):
    """Lean `RightNodes` (PSS/Scb.lean:39): head indices of the trailing
    principal chain."""
    ps = t[1]
    if not ps:
        return []
    p = ps[-1]
    return [p[1]] + RightNodes(p[2])


def Trans(M):
    return tm.Trans(M)


def fmt(M):
    return "".join(f"({a},{b})" for (a, b) in M)


# ------------------------------------------------------------- the geometry
def geom(M):
    """(J1, j0', j1', e10) with J1 = Lng(Br M) - 1 in Lean's NAT arithmetic."""
    br = Br(M)
    J1 = len(br) - 1 if br else 0          # Lean: (Br M).length - 1, NAT
    j1p = getD(FirstNodes(M), J1, 0)
    j0p = getD(Joints(M), J1, 0)
    return J1, j0p, j1p, ent(M, 1, 0)


# --------------------------------------------------------- the wid predicate
def wid(M):
    """Lean `wid` (8.2-subexpr-wid.lean:57)."""
    _, j0p, j1p, _ = geom(M)
    w = getD(RightNodes(Trans(M)), 1, 0)
    return w == ent(M, 1, j1p) or w == ent(M, 1, j0p)


# ---------------------------------------------------- the 4-clause keystone
def _split_principal(t, v):
    """t == Dprin v body ?  -> body, else None."""
    if len(t[1]) != 1:
        return None
    (_, w, body) = t[1][0]
    return body if w == v else None


def _split_last(body, head):
    """body == addBT a (Dprin head x) ?  -> (a_principals, x), else None.
    addBT a (Dpt head x) = ('T', a[1] + [('D', head, x)]), so the split at the
    last principal is unique -- this is what makes the EX-UNIQUE claims
    decidable."""
    ps = body[1]
    if not ps:
        return None
    if ps[-1][1] != head:
        return None
    return ps[:-1], ps[-1][2]


def clause1(M):
    """(1): j1'=j1 & (TrMax=0 | j0'<TrMax) & (e0(j1')=e1(j1') | adm j0')
    & EX! t1. Trans(Pred M)=D_{e10} t1 & Trans M=D_{e10}(t1 +B D_{e1(j1')} 0B)"""
    _, j0p, j1p, e10 = geom(M)
    if j1p != Lng(M) - 1:
        return False
    if not (TrMax(M) == 0 or j0p < TrMax(M)):
        return False
    if not (ent(M, 0, j1p) == ent(M, 1, j1p) or adm(M, j0p)):
        return False
    t1 = _split_principal(Trans(Pred(M)), e10)
    if t1 is None:
        return False                       # no witness -> EX! false
    return Trans(M) == Dpt(e10, addBT(t1, Dpt(ent(M, 1, j1p), ZB)))


def clause2(M):
    """(2): j1'=j1 & e1(j1')<e0(j1') & ~adm j0'
    & EX! (t1,t2). Trans(Pred M)=D_{e10} t1
                 & Trans M=D_{e10}(t1 +B D_{e1(j0')} t2)"""
    _, j0p, j1p, e10 = geom(M)
    if j1p != Lng(M) - 1:
        return False
    if not (ent(M, 1, j1p) < ent(M, 0, j1p)):
        return False
    if adm(M, j0p):
        return False
    t1 = _split_principal(Trans(Pred(M)), e10)
    if t1 is None:
        return False
    bodyM = _split_principal(Trans(M), e10)
    if bodyM is None:
        return False
    sp = _split_last(bodyM, ent(M, 1, j0p))
    if sp is None:
        return False
    pre, _t2 = sp
    return list(pre) == list(t1[1])


def _clause34(M, head):
    """(3)/(4): EX! (a,b,c). Trans(Pred M)=D_{e10}(a +B D_head b)
                           & Trans M     =D_{e10}(a +B D_head c)"""
    _, _, _, e10 = geom(M)
    bodyP = _split_principal(Trans(Pred(M)), e10)
    if bodyP is None:
        return False
    spP = _split_last(bodyP, head)
    if spP is None:
        return False
    a, _b = spP
    bodyM = _split_principal(Trans(M), e10)
    if bodyM is None:
        return False
    spM = _split_last(bodyM, head)
    if spM is None:
        return False
    a2, _c = spM
    return list(a2) == list(a)


def clause3(M):
    _, _, j1p, _ = geom(M)
    return _clause34(M, ent(M, 1, j1p))


def clause4(M):
    _, j0p, _, _ = geom(M)
    return _clause34(M, ent(M, 1, j0p))


def keystone(M):
    """The 4-clause disjunction shared by `subexpr_component_Pred`,
    `subexpr_component_Pred_faithful`, `subexpr_component_Pred_Adm0`,
    `subexpr_component_Pred_Adm0_full`, `SXP_subexpr_component_Pred_of_wid`."""
    return clause1(M) or clause2(M) or clause3(M) or clause4(M)


def which_clauses(M):
    return [i for i, f in enumerate((clause1, clause2, clause3, clause4), 1)
            if f(M)]


# ----------------------------------------------------------- pool building
def standard_pool(umax=4, vmax=7, nmax=5, gens=5, lenCap=16):
    """diagSeq closed under `oper` -- REAL standard forms (the established
    idiom; random pair sequences are almost never reduced)."""
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


def rtps_mono_pool(base, lenCap=15):
    """M in RT_PS & PT_PS reachable from the standard pool:
      - the standard forms themselves,
      - every row-0 ancestor slice Red(seg(M, j0, j1)) (strongmono_audit
        proves these are reduced & mono),
      - the Pred-closure of both (the §8.2 induction descends along Pred).
    """
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
    # Pred-closure
    i = 0
    while i < len(cand):
        M = cand[i]
        i += 1
        if Lng(M) > 1:
            push(Pred(M))
    return [M for M in cand if RTPS(M) and monoT(M)]


# ---------------------------------------------------------------- reporting
class Claim:
    def __init__(self, name, src):
        self.name, self.src = name, src
        self.hit = 0          # hypotheses hold -> non-vacuously exercised
        self.bad = 0          # conclusion fails -> COUNTEREXAMPLE
        self.cex = []

    def check(self, hyp, concl, M, extra=""):
        if not hyp:
            return
        self.hit += 1
        if not concl:
            self.bad += 1
            if len(self.cex) < 5:
                self.cex.append((fmt(M), extra))

    def line(self):
        st = "OK " if self.bad == 0 else "FAIL"
        return (f"  [{st}] {self.name:44s} {self.hit:6d} non-vacuous, "
                f"{self.bad} counterexample(s)   ({self.src})")


def main():
    base = standard_pool()
    blens = [Lng(M) for M in base]
    bents = [x for M in base for p in M for x in p]
    print(f"standard pool (diagSeq closed under oper): {len(base)} forms, "
          f"maxlen {max(blens)}, max entry {max(bents)}", flush=True)

    pool = rtps_mono_pool(base)
    lens = [Lng(M) for M in pool]
    ents = [x for M in pool for p in M for x in p]
    print(f"RT_PS & PT_PS pool: {len(pool)} forms, maxlen {max(lens)}, "
          f"max entry {max(ents)}", flush=True)

    C = {}

    def mk(k, name, src):
        C[k] = Claim(name, src)
        return C[k]

    mk('wid', 'wid / wid_holds', '8.2-subexpr-wid:57, -final:263 <- wip 29605')
    mk('key', 'subexpr_component_Pred (+_faithful)',
       '8.2-subexpr-final:284,345 <- wip 29702 / paper 1523')
    mk('a0f', 'subexpr_component_Pred_Adm0_full',
       '8.2-subexpr-adm0-full:44 <- wip 27019')
    mk('a0v', 'subexpr_component_Pred_Adm0 [hyps satisfiable?]',
       '8.2-subexpr-adm0:40 <- wip 20828')
    mk('cpU', 'SXP_wid_cpU', '8.2-subexpr-final:184 <- wip 29605 assms')
    mk('bsU', 'SXP_wid_baseU', '8.2-subexpr-final:194 <- wip 29605 assms')
    mk('stp', 'SXP_wid_of_predwid', '8.2-subexpr-final:114 <- wip 29038')
    mk('ofw', 'SXP_subexpr_component_Pred_of_wid',
       '8.2-subexpr-final:133 <- wip 28627')
    mk('ft', 'ft_transport', '8.2-subexpr-wid:232 <- wip 29392')
    mk('jt', 'jt_transport', '8.2-subexpr-wid:268 <- wip 29460')
    mk('jnt', 'Joints: Lean `parent` == red_model THE_nextR',
       'PSS/Mono.lean:64 vs red_model.py:119')
    mk('rdc', 'reduced: Red-fixpoint == RedCondA/B (m_6_6)',
       'PSS/Red.lean:104 vs trans_model.py:111')

    # degeneracy counters
    deg_rn_short = 0
    adm0_n = admpos_n = 0
    clause_hist = {1: 0, 2: 0, 3: 0, 4: 0}
    guard_hist = {1: 0, 2: 0}
    multi_clause = 0

    for M in pool:
        # model cross-checks (every pool member, no extra hypotheses)
        C['rdc'].check(True, tm.reduced(M) == reduced(M), M)
        jl, jr = Joints(M), rm.Joints(M)
        C['jnt'].check(True, jl == jr, M, f"lean={jl} red_model={jr}")

        br = Br(M)
        main_hyp = (RTPS(M) and monoT(M) and br != [] and 1 < Lng(M) - 1)
        _, j0p, j1p, _ = geom(M)

        # ---- wid / wid_holds -------------------------------------------
        if main_hyp and len(RightNodes(Trans(M))) < 2:
            deg_rn_short += 1
        C['wid'].check(main_hyp, wid(M), M,
                       f"RN1={getD(RightNodes(Trans(M)), 1, 0)} "
                       f"e1(j1')={ent(M, 1, j1p)} e1(j0')={ent(M, 1, j0p)}")

        # ---- keystone ---------------------------------------------------
        ks = keystone(M) if main_hyp else False
        C['key'].check(main_hyp, ks, M)
        if main_hyp:
            cs = which_clauses(M)
            for c in cs:
                clause_hist[c] += 1
            if len(cs) > 1:
                multi_clause += 1
            # clause (1)/(2) NON-existential guards, to tell "guard never holds"
            # apart from "guard holds but the EX! witness is missing"
            if (j1p == Lng(M) - 1
                    and (TrMax(M) == 0 or j0p < TrMax(M))
                    and (ent(M, 0, j1p) == ent(M, 1, j1p) or adm(M, j0p))):
                guard_hist[1] += 1
            if (j1p == Lng(M) - 1 and ent(M, 1, j1p) < ent(M, 0, j1p)
                    and not adm(M, j0p)):
                guard_hist[2] += 1

        # ---- Adm0 branch ------------------------------------------------
        if main_hyp:
            if transJm1(M) == 0:
                adm0_n += 1
            else:
                admpos_n += 1
        C['a0f'].check(main_hyp and transJm1(M) == 0, ks, M)

        # ---- Adm0 (guarded, wip 20828): are the hypotheses satisfiable? --
        gB = (ent(M, 0, j1p) == ent(M, 1, j1p) or adm(M, j0p))
        a0_hyp = (main_hyp and transJm1(M) == 0 and gB
                  and transT2(M) != ZB
                  and ent(M, 1, j1p) < ent(M, 0, j1p)
                  and not adm(M, j0p))
        C['a0v'].check(a0_hyp, ks, M)

        # ---- SXP_wid_cpU -------------------------------------------------
        if Lng(M) > 1:
            PM = Pred(M)
            brP = Br(PM)
            J1P = len(brP) - 1 if brP else 0
            cpU_hyp = (main_hyp and transJm1(M) > 0 and brP != []
                       and j1p == Lng(M) - 1)
            cpU_cc = (getD(RightNodes(Trans(PM)), 1, 0)
                      == ent(PM, 1, getD(Joints(PM), J1P, 0)))
            C['cpU'].check(cpU_hyp, cpU_cc, M)

            # ---- SXP_wid_baseU ------------------------------------------
            bsU_hyp = (main_hyp and transJm1(M) > 0
                       and (brP == [] or not (1 < Lng(PM) - 1)))
            C['bsU'].check(bsU_hyp, wid(M), M)

            # ---- SXP_wid_of_predwid (wip 29038) -------------------------
            predwid_raw = (getD(RightNodes(Trans(PM)), 1, 0)
                           == ent(PM, 1, getD(FirstNodes(PM), J1P, 0))
                           or getD(RightNodes(Trans(PM)), 1, 0)
                           == ent(PM, 1, getD(Joints(PM), J1P, 0)))
            jt_prem = (ent(PM, 1, getD(Joints(PM), J1P, 0))
                       == ent(M, 1, j0p))
            ft_prem = (j1p == Lng(M) - 1
                       or ent(PM, 1, getD(FirstNodes(PM), J1P, 0))
                       == ent(M, 1, j1p))
            cp_prem = (j1p != Lng(M) - 1
                       or getD(RightNodes(Trans(PM)), 1, 0)
                       == ent(PM, 1, getD(Joints(PM), J1P, 0)))
            stp_hyp = (RTPS(M) and monoT(M) and 1 < Lng(M) - 1
                       and transJm1(M) > 0 and Trans(PM) != ZB
                       and predwid_raw and jt_prem and ft_prem and cp_prem)
            C['stp'].check(stp_hyp, wid(M), M)

            # ---- ft_transport / jt_transport ----------------------------
            C['ft'].check(main_hyp and brP != [] and j1p != Lng(M) - 1,
                          ent(PM, 1, getD(FirstNodes(PM), J1P, 0))
                          == ent(M, 1, j1p), M)
            C['jt'].check(main_hyp and 1 < Lng(M) - 1 and transJm1(M) > 0
                          and brP != [], jt_prem, M)

        # ---- SXP_subexpr_component_Pred_of_wid ---------------------------
        C['ofw'].check(main_hyp and wid(M), ks, M)

    print()
    print("claims (hypotheses = the Lean statement's, verbatim):", flush=True)
    order = ['wid', 'key', 'a0f', 'a0v', 'cpU', 'bsU', 'stp', 'ofw',
             'ft', 'jt', 'jnt', 'rdc']
    for k in order:
        print(C[k].line(), flush=True)

    print()
    print(f"  main hypothesis (RT_PS & PT_PS & Br M != [] & Lng M - 1 > 1) "
          f"holds on {C['wid'].hit} pool forms", flush=True)
    print(f"    Adm0 branch (transJm1 M = 0): {adm0_n};  "
          f"Admpos branch (transJm1 M > 0): {admpos_n}", flush=True)
    print(f"    clause hits: (1)={clause_hist[1]} (2)={clause_hist[2]} "
          f"(3)={clause_hist[3]} (4)={clause_hist[4]}; "
          f"{multi_clause} forms satisfy >1 clause", flush=True)
    print(f"    clause (1)/(2) non-EX! guards hold: (1)={guard_hist[1]} "
          f"(2)={guard_hist[2]}  -- clause (2)'s guard set "
          f"(j1'=j1 & e1(j1')<e0(j1') & ~adm j0') is", flush=True)
    print(f"    unreached on this pool, so clause (2) of the keystone is "
          f"never the one that fires;", flush=True)
    print(f"    the disjunction is carried by (1) on Adm0 and by (3)/(4) "
          f"elsewhere.", flush=True)
    print(f"    forms where RightNodes(Trans M) has length < 2 "
          f"(getD default 0 -- `wid` degenerate): {deg_rn_short}", flush=True)

    bad = [k for k in order if C[k].bad]
    for k in bad:
        print(f"\n!!! COUNTEREXAMPLES for {C[k].name} ({C[k].src}):",
              flush=True)
        for s, extra in C[k].cex:
            print(f"      M = {s}   {extra}", flush=True)

    print()
    if C['a0v'].hit == 0:
        print("  NOTE  subexpr_component_Pred_Adm0 (8.2-subexpr-adm0.lean:40, "
              "<- wip 20828) was", flush=True)
        print("        exercised 0 times: its hypotheses are mutually "
              "inconsistent.  gB says", flush=True)
        print("        (e0(j1')=e1(j1') | adm j0'), he0gt says "
              "e1(j1')<e0(j1') (refuting the left", flush=True)
        print("        disjunct) and hnadmj0 says ~adm j0' (refuting the "
              "right one).  The theorem is", flush=True)
        print("        VACUOUS -- provable from the hypotheses alone, no §8.2 "
              "content.  Faithful to", flush=True)
        print("        Isabelle (m_8_2_subexpr_component_Pred_Adm0 carries the "
              "same gB/e0gt/nadmj0", flush=True)
        print("        assumption set), and superseded by "
              "subexpr_component_Pred_Adm0_full (wip 27019),", flush=True)
        print("        which the campaign actually wires in.  Not a soundness "
              "bug; a dead public name.", flush=True)

    ok = not bad
    print(f"\nAUDIT {'OK' if ok else 'FAILED'}", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
