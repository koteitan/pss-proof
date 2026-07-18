import «8».«8.7-otint-ox-engine»
import «7».«7.4-RightAnces-RightNodes»

/-!
# §8.7 `KKraw` — the raw census right-spine bound (`ox8_body_rspine_lessBT`)

Discharges the census leaf `KKraw` consumed as the last NEED of the BUILT
`«8».«8.7-otint-ox-close»` (`ox10_SETLE1_close_oc`).  移植元: the `ox8` chain of
`isabelle/layerC/pss_scratch.thy` (:8310–8600).

## What is fully proved here

- **The abstract descent engine** `ox8_rsub_lessBT_of_OTP_kk` (Isabelle
  `ox8_rsub_lessBT_of_OTP`, :8389): if `D_u t` is an `OT` principal (clause (OT2):
  `Gᵤ t < t`) and `u` is below every right-spine head down to level `k-1`, then the
  `k`-th right-spine sub-body of `t` is strictly `< t`.  Built bottom-up from
  `ox8_lastT_GBT` / `ox8_rsub_GBT` (`GBT_trans_ox` closes the chain), the `RightNodes`
  chain (`ox8_RightNodes_cons` / `ox8_rsub_head_RN`), and the `dfree` chain.
- **The census keystone** `ox8_body_rspine_lessBT_kk` (Isabelle `ox8_body_rspine_lessBT`,
  :8539): with the census-geometry inputs (`isOT_BP (D_{e₃} body)`, `e₃ < v₁`,
  `RightNodes body ≥ v₁`, `dfree body`) — each a separate census NEED — every right-spine
  sub-body of `body = bpHeadT (Trans (s84x_N M))` is `< body`.

## The `ox10_SETLE1_close_oc` interface

`ox8_KKraw_kk` assembles the exact `KKraw` field of `ox10_SETLE1_close_oc`
(target `ins 0_B`, not `body`) from the keystone plus the named residual
`SpineSurgeryTransport_kk` — the surgery TRANSPORT that the Isabelle STATUS §(7) flags as
the one remaining census gap (verdict-invariant on STEP-0's 11306/11306, faithful proof =
a separate `align3`-peel file).  `ins 0_B < body`, so the transport is genuinely needed
(`< body` alone is strictly weaker).

## 状態
GREEN.  Abstract engine + census keystone fully proved (axioms clean).  `KKraw` interface
green-modulo the named residuals: the 4 census-geometry inputs (`ox8_OTP_e3_body` /
`oi5_regime` / `ox7_RightNodes_body_ge_v1`) and `SpineSurgeryTransport_kk`.  private suffix `_kk`.
-/

namespace PSS

/-! ## §ox8: last-principal head, and the right-spine `Gᵤ`-descent engine -/

/-- Isabelle `ox8_lastV` (pss_scratch.thy:8311): the head word of the LAST top-level
    principal of `t` (`0` for `t = 0`).  (The body `ox8_lastT` lives in the built
    `«8».«8.7-otint-ox-engine»`.) -/
def ox8_lastV : BT → ℕ∞
  | .trm ps => match ps.reverse with
               | [] => 0
               | .db v _ :: _ => v

@[simp] theorem ox8_lastV_snoc_kk (ps : List BP) (v : ℕ∞) (b : BT) :
    ox8_lastV (.trm (ps ++ [.db v b])) = v := by
  simp only [ox8_lastV, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]

#print axioms ox8_lastV_snoc_kk

/-- A nonzero Buchholz term splits as a `snoc`. -/
private theorem bt_ne_zero_snoc_kk {t : BT} (ne : t ≠ BZero) :
    ∃ (ps : List BP) (v : ℕ∞) (b : BT), t = .trm (ps ++ [.db v b]) := by
  obtain ⟨qs⟩ := t
  have hqs : qs ≠ [] := by
    intro h; subst h; exact ne rfl
  rcases hrev : qs.reverse with _ | ⟨p, rs⟩
  · exact absurd (by rw [← List.reverse_reverse qs, hrev]; rfl) hqs
  · obtain ⟨v, b⟩ := p
    refine ⟨rs.reverse, v, b, ?_⟩
    have hq : qs = rs.reverse ++ [.db v b] := by
      rw [← List.reverse_reverse qs, hrev]; simp
    rw [hq]

/-- Isabelle `ox8_lastT_GBT` (pss_scratch.thy:8323): the last principal's body lies in
    `Gᵤ t` as soon as `u ≤ ox8_lastV t` (clause (G2)). -/
private theorem ox8_lastT_GBT_kk {u : ℕ∞} {t : BT} (ne : t ≠ BZero)
    (uh : u ≤ ox8_lastV t) : ox8_lastT t ∈ GBT u t := by
  obtain ⟨ps, v, b, rfl⟩ := bt_ne_zero_snoc_kk ne
  rw [ox8_lastV_snoc_kk] at uh
  rw [ox8_lastT_snoc_ox]
  have hb : b ∈ GBP u (.db v b) := mem_GBP_db_ox.mpr ⟨uh, Or.inl rfl⟩
  exact mem_GBT_snoc_ox.mpr (Or.inr hb)

/-- Isabelle `ox8_rsub_GBT` (pss_scratch.thy:8345): every right-spine sub-body
    `ox8_rsub t k` (`k ≥ 1`) lies in `Gᵤ t`, provided the spine is alive and its heads
    stay `≥ u` down to level `k-1` (`GBT_trans_ox` closes the chain). -/
private theorem ox8_rsub_GBT_kk {u : ℕ∞} : ∀ (k : ℕ) (t : BT), 1 ≤ k →
    (∀ j, j < k → ox8_rsub t j ≠ BZero ∧ u ≤ ox8_lastV (ox8_rsub t j)) →
    ox8_rsub t k ∈ GBT u t := by
  intro k
  induction k with
  | zero => intro t h _; exact absurd h (by norm_num)
  | succ k ih =>
    intro t _ prem
    have h0 := prem 0 (Nat.succ_pos k)
    have tne : t ≠ BZero := by simpa using h0.1
    have htv : u ≤ ox8_lastV t := by simpa using h0.2
    have step : ox8_lastT t ∈ GBT u t := ox8_lastT_GBT_kk tne htv
    rw [ox8_rsub_succ_ox]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simpa using step
    · have prem' : ∀ j, j < k →
          ox8_rsub (ox8_lastT t) j ≠ BZero ∧ u ≤ ox8_lastV (ox8_rsub (ox8_lastT t) j) := by
        intro j hj
        have := prem (j+1) (by omega)
        simpa [ox8_rsub_succ_ox] using this
      have IH := ih (ox8_lastT t) hkpos prem'
      exact GBT_trans_ox step IH

/-- The (OT2) clause of `isOT_BP (Dᵤ t)`: `Gᵤ t < t`. -/
private theorem otp_G_kk {u : ℕ∞} {t x : BT}
    (otp : isOT_BP (.db u t) = true) (hx : x ∈ GBT u t) : lessBT x t = true := by
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at otp
  exact otp.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

/-- Isabelle `ox8_rsub_lessBT_of_OTP` (pss_scratch.thy:8389): THE descent engine.
    If `Dᵤ t` is an `OT` principal (clause (OT2): `Gᵤ t < t`) and `u` is below every
    right-spine head of `t` down to level `k-1`, then the `k`-th right-spine sub-body of
    `t` is strictly below `t`. -/
theorem ox8_rsub_lessBT_of_OTP_kk {u : ℕ∞} {t : BT} {k : ℕ}
    (otp : isOT_BP (.db u t) = true) (kge : 1 ≤ k)
    (alive : ∀ j, j < k → ox8_rsub t j ≠ BZero ∧ u ≤ ox8_lastV (ox8_rsub t j)) :
    lessBT (ox8_rsub t k) t = true :=
  otp_G_kk otp (ox8_rsub_GBT_kk k t kge alive)

#print axioms ox8_rsub_lessBT_of_OTP_kk

/-! ## `RightNodes` reads exactly the `ox8_rsub` chain -/

/-- `rightNodesList` reads only the last principal of a `snoc` list. -/
private theorem rightNodesList_snoc_kk (ps : List BP) (p : BP) :
    rightNodesList (ps ++ [p]) = rightNodesBP p := by
  induction ps with
  | nil => rfl
  | cons a as ih =>
      cases as with
      | nil => rfl
      | cons a' as' => simpa [rightNodesList] using ih

/-- Isabelle `ox8_RightNodes_cons` (pss_scratch.thy:8419): `RightNodes` walks the same
    right-spine chain the engine iterates. -/
private theorem ox8_RightNodes_cons_kk {t : BT} (ne : t ≠ BZero) :
    RightNodes t = (ox8_lastV t).toNat :: RightNodes (ox8_lastT t) := by
  obtain ⟨ps, v, b, rfl⟩ := bt_ne_zero_snoc_kk ne
  rw [ox8_lastV_snoc_kk, ox8_lastT_snoc_ox]
  show rightNodesList (ps ++ [.db v b]) = v.toNat :: RightNodes b
  rw [rightNodesList_snoc_kk]
  rfl

/-- Isabelle `ox8_rsub_head_RN` (pss_scratch.thy:8441): the `k`-th right-spine head is a
    `RightNodes` entry of `t`. -/
private theorem ox8_rsub_head_RN_kk : ∀ (k : ℕ) (t : BT),
    (∀ j, j ≤ k → ox8_rsub t j ≠ BZero) →
    (ox8_lastV (ox8_rsub t k)).toNat ∈ RightNodes t := by
  intro k
  induction k with
  | zero =>
      intro t prem
      have tne : t ≠ BZero := by simpa using prem 0 (le_refl 0)
      rw [ox8_RightNodes_cons_kk tne]
      simp
  | succ k ih =>
      intro t prem
      have tne : t ≠ BZero := by simpa using prem 0 (Nat.zero_le _)
      have prem' : ∀ j, j ≤ k → ox8_rsub (ox8_lastT t) j ≠ BZero := by
        intro j hj
        have := prem (j+1) (by omega)
        simpa [ox8_rsub_succ_ox] using this
      have IH := ih (ox8_lastT t) prem'
      rw [ox8_rsub_succ_ox, ox8_RightNodes_cons_kk tne]
      exact List.mem_cons_of_mem _ IH

/-! ## `d`-freeness along the spine -/

/-- The last principal of a `dfree` `snoc` list is `dfree`. -/
private theorem dfree_BPList_snoc_last_kk (ps : List BP) (q : BP)
    (h : dfree_BPList (ps ++ [q]) = true) : dfree_BP q = true := by
  induction ps with
  | nil => simpa [dfree_BPList] using h
  | cons a as ih =>
      simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h
      exact ih h.2

/-- Isabelle `ox8_dfree_lastT` (pss_scratch.thy:8471). -/
private theorem ox8_dfree_lastT_kk {t : BT} (df : dfree_BT t = true) :
    dfree_BT (ox8_lastT t) = true := by
  rcases eq_or_ne t BZero with rfl | ne
  · simp [ox8_lastT, BZero, dfree_BT, dfree_BPList]
  · obtain ⟨ps, v, b, rfl⟩ := bt_ne_zero_snoc_kk ne
    rw [ox8_lastT_snoc_ox]
    simp only [dfree_BT] at df
    have hq : dfree_BP (.db v b) = true := dfree_BPList_snoc_last_kk ps (.db v b) df
    simp only [dfree_BP, Bool.and_eq_true] at hq
    exact hq.2

/-- Isabelle `ox8_dfree_rsub` (pss_scratch.thy:8488). -/
private theorem ox8_dfree_rsub_kk : ∀ (k : ℕ) (t : BT),
    dfree_BT t = true → dfree_BT (ox8_rsub t k) = true := by
  intro k
  induction k with
  | zero => intro t df; simpa using df
  | succ k ih =>
      intro t df
      rw [ox8_rsub_succ_ox]
      exact ih (ox8_lastT t) (ox8_dfree_lastT_kk df)

/-- Isabelle `ox8_dfree_lastV` (pss_scratch.thy:8497): a `dfree` term's last head is
    finite. -/
private theorem ox8_dfree_lastV_kk {t : BT} (df : dfree_BT t = true) (ne : t ≠ BZero) :
    ox8_lastV t ≠ ⊤ := by
  obtain ⟨ps, v, b, rfl⟩ := bt_ne_zero_snoc_kk ne
  rw [ox8_lastV_snoc_kk]
  simp only [dfree_BT] at df
  have hq : dfree_BP (.db v b) = true := dfree_BPList_snoc_last_kk ps (.db v b) df
  simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne] at hq
  exact hq.1

/-! ## CENSUS KEYSTONE: every right-spine sub-body of `body` is `< body` -/

/-- Isabelle `ox8_body_rspine_lessBT` (pss_scratch.thy:8539): the census form of the
    right-spine descent (self-maximality of the census spine) — **fully proved** here.

    Given the census-geometry inputs (each a separate NEED supplied by the census layer):
    * `otp : isOT_BP (D_{e₃} body)` — Isabelle `ox8_OTP_e3_body` (:8517), from `oi5_IIIIV_pkg`'s
      kind-1 scb block plus `m_8_7_OT_scb_recursive` (`«8».«8.7-OT-scb-recursive»`).
    * `e3lt : e₃ < v₁` — Isabelle `oi5_regime`(1).
    * `RNge : ∀ x ∈ RightNodes body, v₁ ≤ x` — Isabelle `ox7_RightNodes_body_ge_v1`.
    * `dfb : dfree_BT body` — Isabelle `oi5_regime`(3) (`body ∈ T_B`).

    then EVERY right-spine sub-body `ox8_rsub body k` (`k ≥ 1`, alive) is strictly below
    `body`.  `e₃` is below the WHOLE right spine (`e₃ < v₁ ≤` every spine head, via
    `ox8_rsub_head_RN`), so `ox8_rsub_lessBT_of_OTP` bounds every sub-body by `body`. -/
theorem ox8_body_rspine_lessBT_kk {e3 v1 : ℕ} {body : BT} {k : ℕ}
    (otp : isOT_BP (.db (e3 : ℕ∞) body) = true)
    (e3lt : e3 < v1)
    (RNge : ∀ x ∈ RightNodes body, v1 ≤ x)
    (dfb : dfree_BT body = true)
    (kge : 1 ≤ k)
    (alive : ∀ j, j < k → ox8_rsub body j ≠ BZero) :
    lessBT (ox8_rsub body k) body = true := by
  apply ox8_rsub_lessBT_of_OTP_kk otp kge
  intro j hj
  refine ⟨alive j hj, ?_⟩
  -- `e₃ ≤ ox8_lastV (ox8_rsub body j)`: the spine head is a `RightNodes` entry `≥ v₁ > e₃`.
  have prem : ∀ i, i ≤ j → ox8_rsub body i ≠ BZero := fun i hi => alive i (by omega)
  have mem : (ox8_lastV (ox8_rsub body j)).toNat ∈ RightNodes body :=
    ox8_rsub_head_RN_kk j body prem
  have ge : v1 ≤ (ox8_lastV (ox8_rsub body j)).toNat := RNge _ mem
  have dfj : dfree_BT (ox8_rsub body j) = true := ox8_dfree_rsub_kk j body dfb
  have fin : ox8_lastV (ox8_rsub body j) ≠ ⊤ := ox8_dfree_lastV_kk dfj (alive j hj)
  have hcoe : ((ox8_lastV (ox8_rsub body j)).toNat : ℕ∞) = ox8_lastV (ox8_rsub body j) :=
    ENat.coe_toNat fin
  have he3i : e3 ≤ (ox8_lastV (ox8_rsub body j)).toNat := by omega
  calc (e3 : ℕ∞) ≤ ((ox8_lastV (ox8_rsub body j)).toNat : ℕ∞) := by exact_mod_cast he3i
    _ = ox8_lastV (ox8_rsub body j) := hcoe

#print axioms ox8_body_rspine_lessBT_kk

/-! ## The `KKraw` interface consumed by the BUILT `ox10_SETLE1_close_oc` -/

/-- The surgery TRANSPORT residual (Isabelle STATUS §(7), pss_scratch.thy:8560+): the
    census `spineH` compares the peel bodies of the SURGERED trees, so it needs each
    right-spine sub-body below the LOWERED body `ins 0_B` (`< body` is the leaf-version
    the `Gᵤ`-descent produces, and `ins 0_B < body` since the deepest-right leaf head is
    lowered `v₁ ⤳ v₁-1`).  Empirically verdict-invariant (STEP-0, 11306/11306); its
    faithful proof (the `align3` peel keeping the two sides aligned at shared `(qs,w,sc,bc)`,
    Isabelle `ox7_align3_track`) is a separate future file. -/
def SpineSurgeryTransport_kk (body ins0 : BT) : Prop :=
  ∀ k, 1 ≤ k → lessBT (ox8_rsub body k) body = true → lessBT (ox8_rsub body k) ins0 = true

/-- The `KKraw` hypothesis of the BUILT `ox10_SETLE1_close_oc`
    (`«8».«8.7-otint-ox-close»`), assembled from the census keystone
    `ox8_body_rspine_lessBT_kk` (fully proved) plus the named surgery-transport residual
    `SpineSurgeryTransport_kk` (Isabelle STATUS §(7), the one remaining census gap).

    With `ins0 := ins 0_B`, the conclusion is exactly the `KKraw` field of
    `ox10_SETLE1_close_oc`:
    `∀ k, 1 ≤ k → (∀ j < k, ox8_rsub body j ≠ 0_B) → lessBT (ox8_rsub body k) (ins 0_B)`. -/
theorem ox8_KKraw_kk {e3 v1 : ℕ} {body ins0 : BT}
    (otp : isOT_BP (.db (e3 : ℕ∞) body) = true)
    (e3lt : e3 < v1)
    (RNge : ∀ x ∈ RightNodes body, v1 ≤ x)
    (dfb : dfree_BT body = true)
    (transp : SpineSurgeryTransport_kk body ins0) :
    ∀ k, 1 ≤ k → (∀ j, j < k → ox8_rsub body j ≠ BZero) →
      lessBT (ox8_rsub body k) ins0 = true := by
  intro k hk alive
  exact transp k hk (ox8_body_rspine_lessBT_kk otp e3lt RNge dfb hk alive)

#print axioms ox8_KKraw_kk

end PSS
