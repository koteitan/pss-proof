import «7».«7.1-lessBT-linear-order»
import «8».«8.7-otint-transport-prims»

/-!
# §8.7 `ox8`–`ox10` spine-descent engine — atom (b) of `otSetleCore` (`SETLE1`)

The KK-driven right-spine peel that discharges the census `SETLE1` slot
`ox10_SETLE1_ltJ` (`isabelle/layerC/pss_scratch.thy`:10995).  This file ports the
**pure structural engine** — the `ox8` right-spine sub-body operator, the `ox9_holeD`
hole relation, and the KK-route `ox10_engine` — bottom-up and green.  The withdrawn
`ox9_ok`/`ox9_lexP`/`ox9_MAIN` route (`pss_scratch.thy`:10121–10505, refuted by
`ox10_cex_not_ok`) is NOT ported: the live `ox10_engine` produces its per-level
ancestor bound from `ox9_holeD_lessBT` (MONO, unconditional) + `KK` + transitivity,
so it needs neither `ox9_ok` nor `ox9_MAIN`.

## 移植元 (isabelle/layerC/pss_scratch.thy)

- `ox8_lastT` (fun, :8313), `ox8_rsub` (fun, :8316) — right-spine last-body / iterate.
- `ox9_holeD` (inductive, :10149) — deepest-right principal replacement at spine depth.
- `ox9_holeD_0E`/`_SucE` (:10154/:10159), `ox9_holeD_ne` (:10165) — eliminators.
- `ox9_lessBT_zero` (:10173), `ox9_snoc_lessBT` (:10186), `ox9_holeD_lessBT` (:10189).
- `ox9_rsub_Suc` (:10542), `ox9_holeD_lastT` (:10553), `ox9_holeD_rsub` (:10565).
- `ox10_engine` (:10863) — THE engine (KK route).
- `ox10_SETLE1_ltJ` (:10995) — census top (out of reach here; needs `ox5_body_driver_census`,
  `oi5_IIIIV_pkg`, `ox6_holeH`, `ox9_holeD_of_flat3`, `m_7_2_scb_unique_sb`, `d4vx_ins_flat`).

## 依存（ビルド済みのみ import）
- `«8».«8.7-otint-transport-prims»` — `b1x_setle`（透過的に `PSS.Buchholz`: `BT`/`BP`/
  `Dprin`/`BZero`/`lessBT`/`lessBP`/`leBT`/`GBT`/`GBP`/`gatherB*`）。
- `«7».«7.1-lessBT-linear-order»` — `lessBT_linear_trans`。
- `b1x_GBT_trans`（Isabelle wip:50234）は Lean 側 public twin が無い（`GBT_trans_b4`/`_bc`
  は private）。本ファイルで suffix `_ox` にて再証明。

## 状態
GREEN。`ox8`/`ox9_holeD` 構造機械 ＋ `b1x_GBT_trans` 再証明 ＋ THE engine
`ox10_engine_ox` を無条件着地（`sorry` 0, axioms = propext/Classical.choice/Quot.sound）。
`ox10_setle_from_engine_ox` が engine を `k=0` で回して census `SETLE1` の結論形
`b1x_setle (Gᵤ A₁) ({X₁} ∪ Gᵤ X₁)` を出す。census top `ox10_SETLE1_ltJ` は named
residual `Ox10SETLE1Residual_ox`（engine の 5 入力）へ縮小、`ox10_SETLE1_of_residual_ox`
で放電。

### `Ox10SETLE1Residual_ox` の 5 入力の由来（本ファイル未移植 = needs）
- `holeH`  = `ox5_body_driver_census`(:4974) ＋ `ox6_holeH`(:5081)。
- `hdA`/`hdX` = `ox9_holeD_of_flat3`(:10507) ＋ `d4vx_ins_flat`(§8.7-transport-prims)
  ＋ `oi5_IIIIV_pkg` ＋ `m_7_2_scb_unique_sb`（surgery の flat 三つ組）。
- `pAlt`  = `ublt`（`ub < v₁`, transCondIII/IV の `v₁ > 0`）。
- `KK`    = spine bound `ox8_body_rspine_lessBT`(:8539)（census 幾何、A0/head-guard 不要）。

private suffix `_ox`。
-/

namespace PSS

/-! ## §ox8: the right-spine last-body operator and its iterate -/

/-- Isabelle `ox8_lastT` (pss_scratch.thy:8313): the body of the LAST top-level
    principal (`0`-term maps to `0`). -/
def ox8_lastT : BT → BT
  | .trm ps => match ps.reverse with
               | [] => BZero
               | .db _ b :: _ => b

/-- Isabelle `ox8_rsub` (pss_scratch.thy:8316): the `k`-th right-spine sub-body. -/
def ox8_rsub : BT → ℕ → BT
  | t, 0 => t
  | t, (k+1) => ox8_rsub (ox8_lastT t) k

@[simp] theorem ox8_rsub_zero_ox (t : BT) : ox8_rsub t 0 = t := rfl

@[simp] theorem ox8_rsub_succ_ox (t : BT) (k : ℕ) :
    ox8_rsub t (k+1) = ox8_rsub (ox8_lastT t) k := rfl

/-- The last-body reads the tail principal off a `snoc` list. -/
@[simp] theorem ox8_lastT_snoc_ox (ps : List BP) (w : ℕ∞) (b : BT) :
    ox8_lastT (.trm (ps ++ [.db w b])) = b := by
  simp only [ox8_lastT, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]

/-! ## §ox9: the hole relation `ox9_holeD` -/

/-- Isabelle `ox9_holeD` (pss_scratch.thy:10149): `t'` is `t` with its deepest-right
    principal `p` replaced by `q`, the hole sitting at right-spine depth `e`. -/
inductive ox9_holeD : ℕ → BP → BP → BT → BT → Prop where
  | hD0 (ps : List BP) (p q : BP) :
      ox9_holeD 0 p q (.trm (ps ++ [p])) (.trm (ps ++ [q]))
  | hDS (k : ℕ) (ps : List BP) (w : ℕ∞) (p q : BP) (b b' : BT)
      (hb : ox9_holeD k p q b b') :
      ox9_holeD (k+1) p q (.trm (ps ++ [.db w b])) (.trm (ps ++ [.db w b']))

/-- Isabelle `ox9_holeD_0E` (pss_scratch.thy:10154). -/
theorem ox9_holeD_0E_ox {p q : BP} {t t' : BT} (h : ox9_holeD 0 p q t t') :
    ∃ ps, t = .trm (ps ++ [p]) ∧ t' = .trm (ps ++ [q]) := by
  cases h with
  | hD0 ps p q => exact ⟨ps, rfl, rfl⟩

/-- Isabelle `ox9_holeD_SucE` (pss_scratch.thy:10159). -/
theorem ox9_holeD_SucE_ox {e : ℕ} {p q : BP} {t t' : BT} (h : ox9_holeD (e+1) p q t t') :
    ∃ (ps : List BP) (w : ℕ∞) (b b' : BT),
      t = .trm (ps ++ [.db w b]) ∧ t' = .trm (ps ++ [.db w b']) ∧ ox9_holeD e p q b b' := by
  cases h with
  | hDS k ps w p q b b' hb => exact ⟨ps, w, b, b', rfl, rfl, hb⟩

/-- Isabelle `ox9_holeD_ne` (pss_scratch.thy:10165). -/
theorem ox9_holeD_ne_ox {e : ℕ} {p q : BP} {t t' : BT} (h : ox9_holeD e p q t t') :
    t ≠ BZero := by
  cases h with
  | hD0 ps p q => simp [BZero]
  | hDS k ps w p q b b' hb => simp [BZero]

/-! ## §ox9: elementary `lessBT` / `lessBP` facts -/

/-- Isabelle `ox9_lessBT_zero` (pss_scratch.thy:10173): nothing is `< 0`. -/
theorem ox9_lessBT_zero_ox (t : BT) : lessBT t BZero = false := by
  rcases t with ⟨ps⟩
  cases ps <;> simp [lessBT, lessBPList, BZero]

/-- Isabelle `ox9_snoc_lessBT` (pss_scratch.thy:10186): surgery at a shared position
    strictly lowers, at the tree level. -/
theorem ox9_snoc_lessBT_ox {p q : BP} :
    ∀ (ps : List BP), lessBP q p = true →
      lessBT (.trm (ps ++ [q])) (.trm (ps ++ [p])) = true
  | [], h => by simp [lessBT, lessBPList, h]
  | a :: as, h => by
      have ih := ox9_snoc_lessBT_ox as h
      simp only [lessBT] at ih ⊢
      simp only [List.cons_append, lessBPList, beq_self_eq_true, Bool.true_and]
      rw [ih]; simp

/-- Isabelle `ox9_holeD_lessBT` (pss_scratch.thy:10189): a hole surgery `q < p`
    lowers the whole tree. -/
theorem ox9_holeD_lessBT_ox {e : ℕ} {p q : BP} {t t' : BT}
    (h : ox9_holeD e p q t t') : lessBP q p = true → lessBT t' t = true := by
  induction h with
  | hD0 ps p q => intro hpq; exact ox9_snoc_lessBT_ox ps hpq
  | hDS k ps w p q b b' hb ih =>
      intro hpq
      have hb' : lessBT b' b = true := ih hpq
      have hlp : lessBP (.db w b') (.db w b) = true := by simp [lessBP, hb']
      exact ox9_snoc_lessBT_ox ps hlp

/-! ## §ox9: reading the hole off the right-spine iterate -/

/-- Isabelle `ox9_rsub_Suc` (pss_scratch.thy:10542). -/
theorem ox9_rsub_Suc_ox (t : BT) (k : ℕ) :
    ox8_rsub t (k+1) = ox8_lastT (ox8_rsub t k) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
      rw [ox8_rsub_succ_ox t (k+1), ih (ox8_lastT t), ← ox8_rsub_succ_ox t k]

/-- Isabelle `ox9_holeD_lastT` (pss_scratch.thy:10553). -/
theorem ox9_holeD_lastT_ox {e : ℕ} {p q : BP} {t t' : BT}
    (h : ox9_holeD (e+1) p q t t') :
    ox9_holeD e p q (ox8_lastT t) (ox8_lastT t') := by
  obtain ⟨ps, w, b, b', ht, ht', hb⟩ := ox9_holeD_SucE_ox h
  subst ht ht'
  simpa using hb

/-- Isabelle `ox9_holeD_rsub` (pss_scratch.thy:10565). -/
theorem ox9_holeD_rsub_ox {p q : BP} (k : ℕ) : ∀ {dR : ℕ} {t t' : BT},
    ox9_holeD dR p q t t' → k ≤ dR →
    ox9_holeD (dR - k) p q (ox8_rsub t k) (ox8_rsub t' k) := by
  induction k with
  | zero => intro dR t t' h _; simpa using h
  | succ k ih =>
      intro dR t t' h hle
      cases dR with
      | zero => exact absurd hle (Nat.not_succ_le_zero k)
      | succ e =>
          have step : ox9_holeD e p q (ox8_lastT t) (ox8_lastT t') :=
            ox9_holeD_lastT_ox h
          have hle' : k ≤ e := Nat.le_of_succ_le_succ hle
          have hres := ih step hle'
          simpa [Nat.succ_sub_succ] using hres

/-! ## §G-part membership: `Gᵤ` snoc-split, the `Dᵥ` clause, and G-transitivity -/

private theorem mem_GBT_iff_ox {u : ℕ∞} {t x : BT} : x ∈ GBT u t ↔ x ∈ gatherBT u t := by
  simp [GBT, Set.mem_setOf_eq]

private theorem mem_GBP_iff_ox {u : ℕ∞} {p : BP} {x : BT} :
    x ∈ GBP u p ↔ x ∈ gatherBP u p := by
  simp [GBP, Set.mem_setOf_eq]

private theorem gatherBPList_append_ox (u : ℕ∞) (as bs : List BP) :
    gatherBPList u (as ++ bs) = gatherBPList u as ++ gatherBPList u bs := by
  induction as with
  | nil => simp [gatherBPList]
  | cons a as ih => simp [gatherBPList, List.cons_append, ih, List.append_assoc]

/-- Clause (G2): `x ∈ Gᵤ (Dᵥ b) ⟺ u ≤ v ∧ (x = b ∨ x ∈ Gᵤ b)`. -/
theorem mem_GBP_db_ox {u w : ℕ∞} {b x : BT} :
    x ∈ GBP u (.db w b) ↔ u ≤ w ∧ (x = b ∨ x ∈ GBT u b) := by
  rw [mem_GBP_iff_ox, mem_GBT_iff_ox]
  by_cases h : u ≤ w
  · simp [gatherBP, h]
  · simp [gatherBP, h]

/-- `Gᵤ` of a `snoc` splits into the prefix's `Gᵤ` and the tail principal's `Gᵤ`. -/
theorem mem_GBT_snoc_ox {u : ℕ∞} {ps : List BP} {p : BP} {x : BT} :
    x ∈ GBT u (.trm (ps ++ [p])) ↔ x ∈ GBT u (.trm ps) ∨ x ∈ GBP u p := by
  rw [mem_GBT_iff_ox, mem_GBT_iff_ox, mem_GBP_iff_ox]
  simp only [gatherBT, gatherBPList_append_ox, gatherBPList, List.append_nil,
    List.mem_append]

/-- The prefix's `Gᵤ` sits inside the whole `snoc` term's `Gᵤ`. -/
theorem GBT_prefix_ox {u : ℕ∞} {ps : List BP} {p : BP} :
    GBT u (.trm ps) ⊆ GBT u (.trm (ps ++ [p])) := by
  intro x hx
  exact mem_GBT_snoc_ox.mpr (Or.inl hx)

mutual
  private theorem gatherBT_trans_mem_ox (u : ℕ∞) (y : BT) :
      ∀ t x : BT, x ∈ gatherBT u t → y ∈ gatherBT u x → y ∈ gatherBT u t
    | .trm ps, x, hx, hy => gatherBPList_trans_mem_ox u y ps x hx hy
  private theorem gatherBP_trans_mem_ox (u : ℕ∞) (y : BT) :
      ∀ p : BP, ∀ x : BT, x ∈ gatherBP u p → y ∈ gatherBT u x → y ∈ gatherBP u p
    | .db v b, x, hx, hy => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr hy
          · exact Or.inr (gatherBT_trans_mem_ox u y b x hx hy)
        · simp [gatherBP, huv] at hx
  private theorem gatherBPList_trans_mem_ox (u : ℕ∞) (y : BT) :
      ∀ ps : List BP, ∀ x : BT,
        x ∈ gatherBPList u ps → y ∈ gatherBT u x → y ∈ gatherBPList u ps
    | [], x, hx, _ => by simp [gatherBPList] at hx
    | p :: ps, x, hx, hy => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_trans_mem_ox u y p x hx hy)
        · exact Or.inr (gatherBPList_trans_mem_ox u y ps x hx hy)
end

/-- Isabelle `b1x_GBT_trans` (layerB/pss_wip.thy:50234): `x ∈ Gᵤ t → Gᵤ x ⊆ Gᵤ t`.
    (Lean public twin was absent; `GBT_trans_b4`/`_bc` are private — re-proved here.) -/
theorem GBT_trans_ox {u : ℕ∞} {x t : BT} (hx : x ∈ GBT u t) : GBT u x ⊆ GBT u t := by
  intro y hy
  have hout := gatherBT_trans_mem_ox u y t x
    (by simpa [GBT] using hx) (by simpa [GBT] using hy)
  simpa [GBT] using hout

/-! ## §ox10: the engine, driven by `KK` alone -/

private theorem snoc_inj_ox {α : Type _} {ps ps' : List α} {a b : α}
    (h : ps ++ [a] = ps' ++ [b]) : ps = ps' ∧ a = b := by
  have hrev := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.cons.injEq] at hrev
  refine ⟨?_, hrev.1⟩
  have h2 := congrArg List.reverse hrev.2
  simpa using h2

private theorem leBT_refl_ox (x : BT) : leBT x x = true := by simp [leBT]

/-- Isabelle `ox10_engine` (pss_scratch.thy:10863): the right-spine peel, driven by
    the spine bound `KK` alone (the withdrawn `ox9_ok`/`ox9_MAIN` route is not needed —
    the per-level ancestor bound is `ox9_holeD_lessBT` (MONO) + `KK` + transitivity). -/
theorem ox10_engine_ox
    {u v1 : ℕ∞} {WB A1 X1 : BT} {pA pX : BP} {dR : ℕ}
    (holeH : b1x_setle (GBP u pA) (insert X1 (GBT u X1)))
    (hdA : ox9_holeD dR (.db v1 BZero) pA WB A1)
    (hdX : ox9_holeD dR (.db v1 BZero) pX WB X1)
    (pAlt : lessBP pA (.db v1 BZero) = true)
    (KK : ∀ j, 1 ≤ j → j ≤ dR → lessBT (ox8_rsub WB j) X1 = true) :
    ∀ (m k : ℕ), dR - k = m → k ≤ dR → GBT u (ox8_rsub X1 k) ⊆ GBT u X1 →
      b1x_setle (GBT u (ox8_rsub A1 k)) (insert X1 (GBT u X1)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro k hmk hkle subX
    have hdAk : ox9_holeD (dR - k) (.db v1 BZero) pA (ox8_rsub WB k) (ox8_rsub A1 k) :=
      ox9_holeD_rsub_ox k hdA hkle
    have hdXk : ox9_holeD (dR - k) (.db v1 BZero) pX (ox8_rsub WB k) (ox8_rsub X1 k) :=
      ox9_holeD_rsub_ox k hdX hkle
    cases hd : dR - k with
    | zero =>
        rw [hd] at hdAk hdXk
        obtain ⟨ps, hWBk, hA1k⟩ := ox9_holeD_0E_ox hdAk
        obtain ⟨ps', hWBk', hX1k⟩ := ox9_holeD_0E_ox hdXk
        have hpp : ps = ps' := by
          have hL : ps ++ [(.db v1 BZero : BP)] = ps' ++ [.db v1 BZero] := by
            have := hWBk.symm.trans hWBk'
            simpa only [BT.trm.injEq] using this
          exact (snoc_inj_ox hL).1
        have qsub : GBT u (.trm ps) ⊆ GBT u X1 := by
          intro z hz
          have h1 : z ∈ GBT u (.trm (ps' ++ [pX])) := by
            rw [← hpp]; exact mem_GBT_snoc_ox.mpr (Or.inl hz)
          rw [← hX1k] at h1
          exact subX h1
        rw [hA1k]
        intro x hx
        rcases mem_GBT_snoc_ox.mp hx with hxps | hxpA
        · exact ⟨x, Set.mem_insert_iff.mpr (Or.inr (qsub hxps)), leBT_refl_ox x⟩
        · exact holeH x hxpA
    | succ e =>
        rw [hd] at hdAk hdXk
        obtain ⟨ps, w, LB, LA, hWBk, hA1k, _hdLB⟩ := ox9_holeD_SucE_ox hdAk
        obtain ⟨ps', w', LB', LX, hWBk', hX1k, _hdLX⟩ := ox9_holeD_SucE_ox hdXk
        have hL : ps ++ [(.db w LB : BP)] = ps' ++ [.db w' LB'] := by
          have := hWBk.symm.trans hWBk'
          simpa only [BT.trm.injEq] using this
        obtain ⟨hpp, hdbeq⟩ := snoc_inj_ox hL
        have hww : w = w' := (by simpa only [BP.db.injEq] using hdbeq : w = w' ∧ LB = LB').1
        have rA : ox8_rsub A1 (k+1) = LA := by
          rw [ox9_rsub_Suc_ox, hA1k, ox8_lastT_snoc_ox]
        have rX : ox8_rsub X1 (k+1) = LX := by
          rw [ox9_rsub_Suc_ox, hX1k, ox8_lastT_snoc_ox]
        have kSle : k + 1 ≤ dR := by omega
        have leLA : leBT LA X1 = true := by
          have hdLA : ox9_holeD (dR - (k+1)) (.db v1 BZero) pA
                        (ox8_rsub WB (k+1)) (ox8_rsub A1 (k+1)) :=
            ox9_holeD_rsub_ox (k+1) hdA kSle
          have mono : lessBT (ox8_rsub A1 (k+1)) (ox8_rsub WB (k+1)) = true :=
            ox9_holeD_lessBT_ox hdLA pAlt
          have kk : lessBT (ox8_rsub WB (k+1)) X1 = true := KK (k+1) (by omega) kSle
          have hlt : lessBT (ox8_rsub A1 (k+1)) X1 = true :=
            lessBT_linear_trans _ _ _ mono kk
          rw [rA] at hlt
          simp [leBT, hlt]
        have qsub : GBT u (.trm ps) ⊆ GBT u X1 := by
          intro z hz
          have h1 : z ∈ GBT u (.trm (ps' ++ [.db w' LX])) := by
            rw [← hpp]; exact mem_GBT_snoc_ox.mpr (Or.inl hz)
          rw [← hX1k] at h1
          exact subX h1
        rw [hA1k]
        intro x hx
        rcases mem_GBT_snoc_ox.mp hx with hxps | hxpA
        · exact ⟨x, Set.mem_insert_iff.mpr (Or.inr (qsub hxps)), leBT_refl_ox x⟩
        · rw [mem_GBP_db_ox] at hxpA
          obtain ⟨uw, xcase⟩ := hxpA
          have LXin : LX ∈ GBT u X1 := by
            have huw' : u ≤ w' := hww ▸ uw
            have hmem : LX ∈ GBP u (.db w' LX) := mem_GBP_db_ox.mpr ⟨huw', Or.inl rfl⟩
            have h1 : LX ∈ GBT u (.trm (ps' ++ [.db w' LX])) :=
              mem_GBT_snoc_ox.mpr (Or.inr hmem)
            rw [← hX1k] at h1
            exact subX h1
          have subX' : GBT u (ox8_rsub X1 (k+1)) ⊆ GBT u X1 := by
            rw [rX]; exact GBT_trans_ox LXin
          rcases xcase with rfl | hxLA
          · exact ⟨X1, Set.mem_insert_iff.mpr (Or.inl rfl), leLA⟩
          · have mlt : dR - (k+1) < m := by omega
            have IHres : b1x_setle (GBT u (ox8_rsub A1 (k+1))) (insert X1 (GBT u X1)) :=
              IH (dR - (k+1)) mlt (k+1) rfl kSle subX'
            rw [rA] at IHres
            exact IHres x hxLA

/-- Running the engine from the top (`k = 0`) yields the census `SETLE1` conclusion
    shape (`ox10_SETLE1_ltJ`'s goal, pss_scratch.thy:11015): the whole `Gᵤ A₁` is
    `⊴`-bounded by `{X₁} ∪ Gᵤ X₁`.  This is `ox10_engine_ox` at `k = 0`. -/
theorem ox10_setle_from_engine_ox
    {u v1 : ℕ∞} {WB A1 X1 : BT} {pA pX : BP} {dR : ℕ}
    (holeH : b1x_setle (GBP u pA) (insert X1 (GBT u X1)))
    (hdA : ox9_holeD dR (.db v1 BZero) pA WB A1)
    (hdX : ox9_holeD dR (.db v1 BZero) pX WB X1)
    (pAlt : lessBP pA (.db v1 BZero) = true)
    (KK : ∀ j, 1 ≤ j → j ≤ dR → lessBT (ox8_rsub WB j) X1 = true) :
    b1x_setle (GBT u A1) (insert X1 (GBT u X1)) :=
  ox10_engine_ox holeH hdA hdX pAlt KK (dR - 0) 0 rfl (Nat.zero_le dR) (fun _ h => h)

/-- The remainder that separates the engine from the full census `ox10_SETLE1_ltJ`
    (pss_scratch.thy:10995): the census layer must supply the engine's five inputs
    for the specific surgery triple `WB = bpHeadT (Trans (s84x_N N))`,
    `A₁ = d4vx_ins s₀ ub b₀ (bpHeadT (Trans (Pred (s84x_N N))))`, `X₁ = d4vx_ins s₀ ub b₀ 0`.
    Each conjunct's census provenance (NOT ported here) is listed in the header `needs`. -/
def Ox10SETLE1Residual_ox (u v1 : ℕ∞) (WB A1 X1 : BT) (pA pX : BP) (dR : ℕ) : Prop :=
  b1x_setle (GBP u pA) (insert X1 (GBT u X1)) ∧
  ox9_holeD dR (.db v1 BZero) pA WB A1 ∧
  ox9_holeD dR (.db v1 BZero) pX WB X1 ∧
  lessBP pA (.db v1 BZero) = true ∧
  (∀ j, 1 ≤ j → j ≤ dR → lessBT (ox8_rsub WB j) X1 = true)

/-- The census `SETLE1` conclusion follows from the named residual by the engine. -/
theorem ox10_SETLE1_of_residual_ox {u v1 : ℕ∞} {WB A1 X1 : BT} {pA pX : BP} {dR : ℕ}
    (h : Ox10SETLE1Residual_ox u v1 WB A1 X1 pA pX dR) :
    b1x_setle (GBT u A1) (insert X1 (GBT u X1)) := by
  obtain ⟨holeH, hdA, hdX, pAlt, KK⟩ := h
  exact ox10_setle_from_engine_ox holeH hdA hdX pAlt KK

#print axioms ox8_lastT_snoc_ox
#print axioms ox9_holeD_0E_ox
#print axioms ox9_holeD_SucE_ox
#print axioms ox9_holeD_ne_ox
#print axioms ox9_lessBT_zero_ox
#print axioms ox9_snoc_lessBT_ox
#print axioms ox9_holeD_lessBT_ox
#print axioms ox9_rsub_Suc_ox
#print axioms ox9_holeD_lastT_ox
#print axioms ox9_holeD_rsub_ox
#print axioms mem_GBP_db_ox
#print axioms mem_GBT_snoc_ox
#print axioms GBT_prefix_ox
#print axioms GBT_trans_ox
#print axioms ox10_engine_ox
#print axioms ox10_setle_from_engine_ox
#print axioms ox10_SETLE1_of_residual_ox

end PSS
