#!/usr/bin/env python3
"""Adversarial numeric audit of the §8.5 exchV tower residuals.

Targets (public claims re-stated 1:1 from the Lean sources):

  lean/8/8.5-exchV-props.lean
    * `ExchVres_adm_M_tower`   (def, residual of `ExchV_scbdec_adm_forms`
      <- Isabelle `m_8_5_scbdec_adm_forms` conclusion (5), layerB/pss_wip.thy:57556)
    * `ExchVres_nadm_M_tower`  (def, residual of `ExchV_nf3x`
      <- Isabelle `nfx_M_tower`, layerB/pss_wip.thy:64348)
  lean/8/8.5-exchV-props2.lean
    * `ExchV_M_tower` (def) — the unified residual, and the claim that the two
      branches differ by exactly one in the `X = s0 ++ [D_e]` exponent
      (`exchV_tail M k = k` on adm, `= k+1` (k>0) on non-adm).

Semantics is python/red_model.py + python/trans_model.py (the canonical
models).  `Red` returns a LIST OF TUPLES; every comparison below stays inside
that representation.  BT terms are ('T', [('D', v, t), ...]); 0_B = ('T', []).

The pool is built the established way (python/audit_82_subexpr.py,
python/strongmono_audit.py): diagSeq closed under `oper`, then every row-0
ancestor slice `Red(seg(M, j0, j1))`, then the `Pred`-closure of those.
Random pair sequences are almost never reduced, so this is the only way to
exercise `M in RT_PS & PT_PS`.

FINDINGS (2026-07-17).  Two independently-built pools, both agreeing:

  (A) this script's defaults (diagSeq closed under oper, gens=4, + Red-slices
      + Pred-closure): 8094 forms -> 28 adm condition-(V) hosts.
  (B) a deeper oper closure (gens=5, nmax=5, lenCap=16, no slices):
      5780 forms -> 80 adm condition-(V) hosts.

  * `ExchVres_adm_M_tower` holds on EVERY adm condition-(V) host either pool
    reaches (28/28 on (A), 80/80 on (B); k = 0..3).  No counterexample.
    It is TRUE and NON-VACUOUS.
  * The non-adm formula, evaluated on those same adm hosts, FAILS on all of
    them (28/28 on (A), 80/80 on (B)).
    The two towers are therefore GENUINELY DIFFERENT statements: the non-adm
    exponent is one MORE than the adm one.  Consequence for the port:
    `ExchVres_nadm_M_tower` is NOT `ExchVres_adm_M_tower` with the `adm`
    hypothesis weakened away -- any "unification by dropping the branch
    hypothesis" is refuted.  (This matches isabelle/memo.md:130 on the
    article's m_n = n-1 vs n index, and matches the Isabelle blueprint:
    `nfx_M_tower`'s hypothesis `L1v` has core `D_u(t2 + D_e(t2 + D_e 0))`
    whereas the adm `s85b_L1_decomp_adm` has core `D_e(t2 + D_e 0)` -- one
    level apart, so `L1v` is FALSE on the adm branch.)
  * NON-ADM condition-(V) hosts do NOT occur in either pool (0 of 8094 / 0 of
    5780).  isabelle/memo.md records that Isabelle round r16-E1 found
    them only at `Lng >= 9`; reaching them needs a differently-seeded pool.
    So `ExchVres_nadm_M_tower` is EMPIRICALLY UNVALIDATED here -- reported
    honestly as `nadm: 0` rather than as a pass.

Second section: a PROP-VISIBILITY audit of python/audit_8_7_termination.py.
That script filters named Props by a hard-coded prefix list (`PROP_PREFIXES`),
so any `def X : Prop` whose name does not match is invisible: it is neither
counted as OPEN nor seen as a dependency of a discharger.  A theorem
`foo_holds (hres : InvisibleProp) : VisibleProp` therefore registers as an
UNCONDITIONAL discharger and the audit reports `VisibleProp` CLOSED.  This
section re-walks the same closure with the prefix filter removed and reports
every Prop that is open-but-invisible.

    python3 python/audit_85_exchV_towers.py
"""
import os
import re
import sys
import time
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)

import red_model as rm
import trans_model as tm

Lng, entry, seg, oper, diagSeq = rm.Lng, rm.entry, rm.seg, rm.oper, rm.diagSeq
ZB, Dpt, addBT, flatBT, flatBP = tm.ZB, tm.Dpt, tm.addBT, tm.flatBT, tm.flatBP


# --------------------------------------------------------------- speed-ups
# Pure memoisation of the reachability matrices / Trans / Red.  No semantic
# change: red_model resolves le0/le1 from module globals at call time.
@lru_cache(maxsize=1 << 20)
def _reach0(Mt):
    return rm.reach(list(Mt), rm.nextrel0)


@lru_cache(maxsize=1 << 20)
def _reach1(Mt):
    return rm.reach(list(Mt), rm.nextrel1)


rm.le0 = lambda M, a, b: a < len(M) and b < len(M) and _reach0(tuple(M))[a][b]
rm.le1 = lambda M, a, b: a < len(M) and b < len(M) and _reach1(tuple(M))[a][b]

_trans_cache = {}
_orig_Trans = tm.Trans


def _Trans_memo(M, depth=0):
    k = tuple(M)
    v = _trans_cache.get(k)
    if v is None:
        v = _orig_Trans(M, depth)
        _trans_cache[k] = v
    return v


tm.Trans = _Trans_memo
Trans = _Trans_memo


@lru_cache(maxsize=1 << 20)
def _Red_t(Mt):
    return tuple(rm.Red(list(Mt)))


def reduced(M):
    """Lean `reduced M = !M.isEmpty && (Red M == M)` (PSS/Red.lean:104)."""
    return bool(M) and _Red_t(tuple(M)) == tuple(M)


# ------------------------------------------- Lean/PSS/Trans.lean accessors
def transJ1(M):
    return Lng(M) - 1


def transJ0(M):
    return rm.parent(M, 0, Lng(M) - 1)


def transJm1(M):
    return tm.Adm(M, transJ0(M))


def transC1(M):
    return tm.Mark(tm.Pred(M), transJm1(M))


def transT2(M):
    return tm.bpHeadT(transC1(M))


# ------------------- lean/8/8.5-Trans-fseq-condV.lean:74 / :77 (s85b_W / e5x_bodyM)
def s85b_W(u, t, c, k):
    r = Dpt(u, c)
    for _ in range(k):
        r = Dpt(u, addBT(t, r))
    return r


def e5x_bodyM(t, e, k):
    return t if k == 0 else addBT(t, s85b_W(e, t, t, k))


# ----------------------------------------------------------- pool building
def standard_pool(umax=4, vmax=7, nmax=5, gens=4, lenCap=16):
    """diagSeq closed under `oper`, + row-0 ancestor Red-slices, + Pred-closure."""
    pool, seen = [], set()

    def add(M):
        t = tuple(M)
        if t and t not in seen:
            seen.add(t)
            pool.append(list(M))
            return True
        return False

    for u in range(umax + 1):
        for v in range(u, vmax + 1):
            add(diagSeq(u, v))
    frontier = list(pool)
    for _ in range(gens):
        nxt = []
        for M in frontier:
            for n in range(1, nmax + 1):
                N = oper(M, n)
                if Lng(N) > lenCap:
                    continue
                if add(N):
                    nxt.append(N)
        frontier = nxt
    for M in list(pool):
        n = Lng(M)
        for a in range(n):
            for b in range(a, n):
                add(list(_Red_t(tuple(seg(M, a, b)))))
    for M in list(pool):
        X = M
        while Lng(X) > 1:
            X = tm.Pred(X)
            add(X)
    return pool


# ----------------------------------------------------------- the two towers
def inner_pair(M):
    """(s0,b0,s1,b1) pinned by the two scb_decomp hypotheses, or None."""
    t2 = transT2(M)
    v1 = entry(M, 1, transJ1(M))
    jm1 = transJm1(M)
    d0 = tm.scb_decomps(addBT(t2, Dpt(v1, ZB)), flatBT(Dpt(v1, ZB)))
    d1 = tm.scb_decomps(Trans(oper(M, 1)), flatBT(Dpt(entry(M, 1, jm1), t2)))
    if len(d0) != 1 or len(d1) != 1:
        return None
    return d0[0][0], d0[0][1], d1[0][0], d1[0][1]


def tower_rhs(M, s0, b0, s1, b1, k, admbranch):
    t2 = transT2(M)
    e = entry(M, 1, transJ0(M))
    u = entry(M, 1, transJm1(M))
    if admbranch:
        X = s0 + [('D', e)]
        return s1 + [('D', e)] + X * k + flatBT(t2) + b0 * k + b1
    return s1 + flatBP(('D', u, e5x_bodyM(t2, e, k))) + b1


def check(M, admbranch, kmax=3):
    r = inner_pair(M)
    if r is None:
        return "skip", None
    s0, b0, s1, b1 = r
    for k in range(kmax + 1):
        if flatBT(Trans(oper(M, k + 1))) != tower_rhs(M, s0, b0, s1, b1, k, admbranch):
            return "FAIL", (k, M)
    return "ok", None


def run_towers():
    t0 = time.time()
    pool = standard_pool()
    print(f"standard pool (diagSeq closed under oper, + Red-slices, + Pred): "
          f"{len(pool)} forms  [{time.time() - t0:.1f}s]")
    hosts = [M for M in pool
             if Lng(M) > 1 and reduced(M) and rm.monoT(M) and tm.condV(M)]
    admh = [M for M in hosts if tm.adm(M, transJ0(M))]
    nadmh = [M for M in hosts if not tm.adm(M, transJ0(M))]
    print(f"condV & monoT & reduced hosts: {len(hosts)}  "
          f"(adm {len(admh)}, non-adm {len(nadmh)})")
    if not nadmh:
        print("  !! NO non-adm condition-(V) host in this pool -- "
              "`ExchVres_nadm_M_tower` is NOT exercised (see module docstring).")

    def tally(name, hs, ab):
        ok = fail = skip = 0
        cex = None
        for M in hs:
            st, info = check(M, ab)
            if st == "ok":
                ok += 1
            elif st == "skip":
                skip += 1
            else:
                fail += 1
                cex = cex or info
        tag = "" if not cex else f"   first CEX: k={cex[0]} M={cex[1]}"
        print(f"  {name:52s} ok={ok:4d} FAIL={fail:4d} skip={skip:3d}{tag}")
        return fail

    print("\n== the two tower residuals ==")
    bad = 0
    bad += tally("ExchVres_adm_M_tower  on adm hosts", admh, True)
    bad += tally("ExchVres_nadm_M_tower on non-adm hosts", nadmh, False)

    print("\n== are the two towers the same statement? ==")
    ok = fail = 0
    for M in admh:
        st, _ = check(M, False)
        if st == "ok":
            ok += 1
        elif st == "FAIL":
            fail += 1
    print(f"  non-adm formula evaluated on adm hosts: ok={ok} FAIL={fail}")
    if admh and fail == len(admh):
        print("  => REFUTED on every host: the towers differ (the non-adm exponent")
        print("     is one MORE).  `ExchVres_nadm_M_tower` cannot be obtained from")
        print("     `ExchVres_adm_M_tower` by weakening the branch hypothesis.")
    elif admh and fail == 0:
        print("  !! the two agree everywhere -- the index-shift claim in")
        print("     lean/8/8.5-exchV-props2.lean would be WRONG.  Investigate.")
        bad += 1
    return bad


# --------------------------------------- Prop-visibility audit of the 8.7 audit
IMPORT_RE = re.compile(r"^import\s+(.+?)\s*$", re.M)
DECL_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s:({\[]+)", re.M)
EXTERNAL = ("Mathlib", "Init", "Std", "Lean", "Batteries", "Aesop", "Qq", "Plausible")
# the hard-coded filter in python/audit_8_7_termination.py
PROP_PREFIXES = ("FseqDesc_", "OTdisp_", "ExchV_", "Exch84_", "CondI_", "CondII_",
                 "CondVI", "TransPreservesOT", "OT_B_wf", "RankSuccD1posLeg")


def _module_to_path(mod):
    if mod.split(".")[0] in EXTERNAL:
        return None
    raw = re.findall(r"«([^»]*)»|([A-Za-z_][A-Za-z0-9_']*)", mod)
    parts = [a or b for a, b in raw]
    cand = os.path.join(REPO, "lean", *parts) + ".lean"
    return cand if os.path.exists(cand) else None


def _closure(root):
    seen, order, stack = set(), [], [root]
    while stack:
        f = stack.pop()
        if f in seen or not os.path.exists(f):
            continue
        seen.add(f)
        order.append(f)
        src = open(f, encoding="utf-8").read()
        head = re.split(r"^(/-|namespace )", src, maxsplit=1, flags=re.M)[0]
        for mod in IMPORT_RE.findall(head):
            p = _module_to_path(mod)
            if p:
                stack.append(p)
    return order


def _decls(path):
    out = {}
    src = open(path, encoding="utf-8").read()
    for m in DECL_RE.finditer(src):
        name = m.group(2)
        tail = src[m.start():m.start() + 1200]
        cut = min((tail.find(t) for t in (":= by", ":=\n", " :=", "\nend ") if t in tail),
                  default=len(tail))
        out[name] = " ".join(tail[:cut].split())
    return out


def run_visibility(root_rel="lean/8/8.7-termination.lean"):
    root = os.path.join(REPO, root_rel)
    if not os.path.exists(root):
        print(f"\n(skipping visibility audit: {root_rel} not found)")
        return 0
    files = _closure(root)
    where = {}
    for f in files:
        for name, stmt in _decls(f).items():
            where.setdefault(name, []).append((os.path.relpath(f, REPO), stmt))
    props = {n: hits[0][0] for n, hits in where.items()
             if re.match(r"def \S+\s*:\s*Prop\b", hits[0][1])}
    dischargers = {}
    for f in files:
        for name, stmt in _decls(f).items():
            if not stmt.startswith(("theorem", "lemma")):
                continue
            m = re.search(r":\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*$", stmt)
            if not m or m.group(1) not in props:
                continue
            target = m.group(1)
            binders = stmt[:m.start()]
            deps = frozenset(p for p in props if p != target
                             and re.search(rf"\b{re.escape(p)}\b", binders))
            dischargers.setdefault(target, []).append((name, deps))
    closed = {}
    changed = True
    while changed:
        changed = False
        for p, ds in dischargers.items():
            if p in closed:
                continue
            for name, deps in ds:
                if deps <= closed.keys():
                    closed[p] = name
                    changed = True
                    break
    open_ = sorted(set(props) - set(closed))
    print(f"\n== Prop-visibility audit of python/audit_8_7_termination.py ==")
    print(f"  closure of {root_rel}: {len(files)} files, "
          f"{len(props)} `def _ : Prop` total")
    invisible_open = [p for p in open_ if not p.startswith(PROP_PREFIXES)]
    # which VISIBLE Props are reported CLOSED only because an INVISIBLE dep is unseen?
    fake_closed = []
    for p, ds in dischargers.items():
        if p not in props or not p.startswith(PROP_PREFIXES):
            continue
        real = [(n, d) for n, d in ds if d <= closed.keys()]
        if real:
            continue
        # every discharger needs something not closed -> genuinely open, skip
    for p in sorted(props):
        if not p.startswith(PROP_PREFIXES):
            continue
        for name, deps in dischargers.get(p, []):
            hidden = {d for d in deps if not d.startswith(PROP_PREFIXES)}
            if hidden and not (deps <= closed.keys()):
                fake_closed.append((p, name, sorted(hidden)))
    print(f"  OPEN Props INVISIBLE to the prefix filter ({len(invisible_open)}):")
    for p in invisible_open:
        print(f"      {p:42s} {props[p]}")
    if fake_closed:
        print("  Props the prefix filter reports CLOSED although their discharger"
              "\n  still needs an invisible Prop:")
        for p, name, hidden in fake_closed:
            print(f"      {p:42s} <- {name}  needs {', '.join(hidden)}")
    print(f"\n  => true open-leaf count is UNDERSTATED by {len(invisible_open)}"
          " by audit_8_7_termination.py.")
    return 0


def main():
    bad = run_towers()
    run_visibility()
    print("\n== VERDICT ==")
    if bad:
        print("  COUNTEREXAMPLE FOUND -- a wrong statement is in the Lean tree.")
    else:
        print("  No counterexample to any exercised claim.")
        print("  Unexercised: ExchVres_nadm_M_tower (no non-adm condV host in pool).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
