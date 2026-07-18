import PSS.Scb

/-!
# PSS.«8».«8.7-corner-shape» — the admeq-corner shape refinement is FALSE

## MISSION VERDICT: `SetleCensusWrapperCondIVCorner_wc` is FALSE — wrapper route needs redesign

This file was tasked with discharging the census residual
`SetleCensusWrapperCondIVCorner_wc` (`«8».«8.7-wrapper-condiv»`) via the **shape
refinement** route: the hope (recorded in `8.7-wrapper-condiv`'s KEY FINDING) was that in
the admeq corner the condIV `c₂` body always takes the **NESTED** shape
`transT2 M = t₃ +_B D_w t₄`, which would make the shared-wrapper existence hold, mirroring
Isabelle `c4dx_condIV_c2body_shape` restricted to the admeq regime.

**The numeric pre-check refutes this outright.**  A degenerate-shape admeq-corner host does
not merely *exist* — the admeq corner is **ALWAYS degenerate**.  Over an ST_PS orbit corpus
of 6000 hosts, **every one** of the 24 admeq-corner condIV mono hosts (with `transT1 M ≠ 0`)
has the **DEGENERATE** shape (`t₃ = t₄ = transT2 M`, i.e. the last principal of `transT2 M`
has head index `≠ entry M 1 (transJ0 M)`), and **zero** are nested.  The mission's own
proposed witness `(0,0)(1,1)(2,2)(2,1)` is degenerate.  For all 24 hosts the residual's
existence conclusion has **no witness** `(s,b,tv,t₂,c')` (verified by exhaustive split
search using the exact Lean `transC2Core`).  See `python/audit_wrapper_condiv_corner.py`.

Per the mission's decision rule ("if a degenerate-shape corner host EXISTS, the residual is
FALSE and the whole wrapper route needs redesign — report that finding prominently
instead"), the shape-refinement route is dead and this residual cannot be discharged.

## Why the residual is false (the structural obstruction)

In the admeq corner `cornerCollapse_holds_cr` gives `Trans (Pred (s84x_N M)) = transC1 M`,
so `A₀ = bpHeadT (transC1 M) = transT2 M`.  On every corner host `transT2 M` is a **single
zero-body principal** `D_a 0`, hence `flatBT (transT2 M) = [dsym a, zero]`.  Meanwhile the
census insertion `ins 0_B` reconstructs to `transT2 M +_B D_w(transT2 M +_B D_{ub} 0)` — a
**genuine multi-principal** term whose flat begins with `lp` (an open paren), because the
`+_B` **APPENDS a fresh top-level principal** rather than growing an existing principal's
body.  Concretely on `(0,0)(1,1)(2,2)(2,1)`:

    flatBT A₀        = [dsym 2, zero]
    flatBT (ins 0_B) = [lp, dsym 2, zero, cm, dsym 1, lp, dsym 2, zero, cm, dsym 0, zero, rp, rp]

The wrapper conclusion demands a *shared context* `(s,b)` in which one principal `D_tv t₂`
grows to `D_tv (t₂ +_B c')`.  That forces `flatBT A₀` and `flatBT (ins 0_B)` to expose a
`D_tv` principal at the *same* offset `|s|`; but `flatBT A₀` has its (only) principal at the
head while `flatBT (ins 0_B)` has `lp` at the head — no split matches.  The theorem below
captures this obstruction with concrete `Sym`-string data (no `Trans`/ST_PS reasoning): as
soon as `A₀` flattens to a single zero-body principal and `ins 0_B` flattens to a term
whose head symbol is `lp`, the residual's existence conclusion is unsatisfiable.

## Redesign direction (for the parent)

The corner branch of `setleCensusWrapperCondIV_holds_wc` collapses `A₀` to the *stripped*
`transT2 M` (outer `D_transV` wrapper removed by `cornerCollapse_holds_cr`), then demands a
principal-body-growth wrapper between a single-principal `A₀` and a two-principal `ins 0_B`.
That target is structurally impossible.  A correct corner treatment must NOT reduce to the
`A₀ = transT2 M` shared-wrapper form; it needs a decomposition that accounts for the
appended principal (e.g. comparing at the `body`/`D_e3` level, or a corner-specific setle
census obligation), i.e. the unported REGS/REGSP corner engine at a *different* pivot than
`bpHeadT`.  The `otSetleCore` field currently routed through
`SetleCensusWrapperCondIVCorner_wc` (via `otSetleCore_of_parts_wc`) therefore needs
re-plumbing at the census level, not a shape lemma here.

## Status
🤖 GREEN (`sorry` 0, axioms = `[propext, Classical.choice, Quot.sound]`).  Contains a
refutation-support lemma, not a discharge of the (false) residual.  Private suffix `_cs`.
-/

namespace PSS

/-- **The corner shared-wrapper obstruction, concretely.**  If `A₀` flattens to a single
zero-body principal `D_a 0` (`flatBT A₀ = [dsym a, zero]`, exactly the shape of `transT2 M`
on every admeq corner — see the header and `python/audit_wrapper_condiv_corner.py`) while
`insZero` flattens to a term whose head symbol is `lp` (a genuine multi-principal term, as
the census `ins 0_B` always is on the corner), then **no** shared-wrapper witness
`(s,b,tv,t₂,c')` exists: there is no context `(s,b)` in which a single principal `D_tv t₂`
of `A₀` grows to `D_tv (t₂ +_B c')` yielding `insZero`.  This is the exact existence
conclusion of `SetleCensusWrapperCondIVCorner_wc`; the two flat-shape hypotheses hold on
every admeq-corner host, so the residual is false. -/
theorem corner_wrapper_conclusion_unsat_cs
    (a : ℕ∞) (A0 insZero : BT) (tl : List Sym)
    (hA0 : flatBT A0 = [Sym.dsym a, Sym.zero])
    (hins : flatBT insZero = Sym.lp :: tl) :
    ¬ ∃ (s b : List Sym) (tv : ℕ∞) (t2 c' : BT),
        flatBT A0 = s ++ flatBP (BP.db tv t2) ++ b ∧
        flatBT insZero = s ++ flatBP (BP.db tv (addBT t2 c')) ++ b ∧
        (∀ x ∈ b, x = Sym.rp) := by
  rintro ⟨s, b, tv, t2, c', e1, e2, _hb⟩
  -- The head symbol of `flatBT insZero` (RHS of `e2`) is always a `dsym`, contradicting
  -- `hins` which forces it to be `lp`.
  rcases s with _ | ⟨x, s⟩
  · -- s = []: head of RHS comes from `flatBP (BP.db tv _) = dsym tv :: _`.
    rw [hins] at e2
    simp only [List.nil_append, flatBP, List.cons_append, List.cons.injEq,
      reduceCtorEq, false_and] at e2
  · -- s = x :: s': `e1` forces `x = dsym a`, so the head of RHS is `dsym a`, not `lp`.
    rw [hA0] at e1
    rw [hins] at e2
    simp only [List.cons_append, List.cons.injEq] at e1 e2
    obtain ⟨hx, -⟩ := e1
    obtain ⟨hlp, -⟩ := e2
    rw [← hx] at hlp
    simp only [reduceCtorEq] at hlp

#print axioms corner_wrapper_conclusion_unsat_cs

end PSS
