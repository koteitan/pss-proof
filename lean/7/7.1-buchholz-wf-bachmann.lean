import «7».«7.1-buchholz-fseq-closed»
import «7».«7.1-buchholz-fseq-lt»
import «7».«7.1-lessBT-linear-order»
import PSS.Buchholz

/-!
# [Buc1] 2.2 キャンペーン — Bachmann（共終性）性質（foundation 2/2）

- 原文: [Buc1] §2–§3。原文 §7.1 の基本列 `operB`（訂正 A23 後）。
  **意味論版 [Buc1] Lemma 2.2（順序数への評価写像 `o`, `ψ_v`, `Ω_u`）は移植対象外**
  （我々の設定では表現不能）。ここで移植するのは Buchholz–Schütte の
  distinguished-sets 経路＝`wf {(a,b). a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b}` の
  **cardinal-free** 証明のうち、Bachmann 性質の部分。
- Isabelle: `isabelle/layerC/pss_scratch.thy` の y4 ブロック 12493–13677。
  `y4_xseq_Dpt` 12493 / `y4_xseq_TBv` 12502 / `y4_xseq_lt` 12509 / `y4_xseq_mono` 12538 /
  `y4_xseq_le_mono` 12558 / `y4_leBT_addBT_self` 12568 / `y4_leBT_addBT_mono_right` 12578 /
  `y4_prefix_split` 12587 / `y4_descP_suffix` 12640 / `y4_OT_suffix` 12643 /
  `y4_GBT_suffix` 12647 / `y4_inner` 12661 / `y4_xseq_cof` 12883 / `y4_N_mono` 12912 /
  `y4_N_mono_le` 13034 / `y4_descP_all_le_hd` 13060 / `y4_TBv_of_head` 13084 /
  `y4_leBT_min` 13102 / `y4_bump` 13128 / `y4_operB_domzero_const` 13154 /
  `y4_le_replicate` 13221 / `y4_dfree_suffix` 13242 / `y4_bachmann` 13261。
- 依存: `PSS.Buchholz`（`operB`/`xseq`/`domTag`/`GBT`/`descP`）、
  `7.1-buchholz-fseq-lt`（`addBT_lt_right_bf`/`TBv_lt_head_bf`/`leBT_single_index_bf`/
  `descP_last_head_bf`/`domTag_snoc_bf`/`domTagBP_below_head_bf`）、
  `7.1-buchholz-fseq-closed`（`buchholz_fseq_closed_general`）、
  `7.1-lessBT-linear-order`（`lessBT_linear_trans`/`lessBT_linear_trichotomy`）。
- 状態: ✅ 証明済（sorry 0、**名前付き仮定 0＝green-modulo ではない**）。
  `operB` の単調性・下界性（Isabelle の `b1x_mono` / `b1x_lowerbound`、
  layerB/pss_wip.thy 50059 / 50147）と `GBT` の三性質（同 50212/50234/50257）、
  `wfj_G_OT_T` は built tree では `private` なので、公開補題
  （`addBT_lt_right_bf` / `TBv_lt_head_bf` / `leBT_single_index_bf` /
  `descP_last_head_bf` / `domTag_snoc_bf` / `domTagBP_below_head_bf`）から
  **接尾辞 `_b4` で再証明**した（仮定に取らず定理化）。

**Isabelle の `domB c = TBv (enat u)` は Lean では tag 形 `domTag c = .below u` で書く。**
両者は `BDom.toSet` の単射性（下の `domB_below_iff_b4` 等）で同値。set 形の Isabelle
文面をそのまま読みたい場合はこの橋を使う。
-/

namespace PSS

/-! ## 0. 順序の基本補題 -/

private theorem leBT_refl_b4 (a : BT) : leBT a a = true := by
  simp [leBT]

private theorem leBT_of_less_b4 {a b : BT} (h : lessBT a b = true) :
    leBT a b = true := by
  simp [leBT, h]

private theorem less_of_leBT_ne_b4 {a b : BT} (h : leBT a b = true) (hne : a ≠ b) :
    lessBT a b = true := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact h'
  · exact absurd (eq_of_beq h') hne

private theorem leBT_trans_b4 {a b c : BT} (hab : leBT a b = true)
    (hbc : leBT b c = true) : leBT a c = true := by
  rcases Bool.or_eq_true_iff.mp hab with h₁ | h₁
  · rcases Bool.or_eq_true_iff.mp hbc with h₂ | h₂
    · exact leBT_of_less_b4 (lessBT_linear_trans a b c h₁ h₂)
    · exact leBT_of_less_b4 (by rw [← eq_of_beq h₂]; exact h₁)
  · rw [eq_of_beq h₁]; exact hbc

private theorem le_less_trans_b4 {a b c : BT} (hab : leBT a b = true)
    (hbc : lessBT b c = true) : lessBT a c = true := by
  rcases Bool.or_eq_true_iff.mp hab with h₁ | h₁
  · exact lessBT_linear_trans a b c h₁ hbc
  · rw [eq_of_beq h₁]; exact hbc

private theorem less_le_trans_b4 {a b c : BT} (hab : lessBT a b = true)
    (hbc : leBT b c = true) : lessBT a c = true := by
  rcases Bool.or_eq_true_iff.mp hbc with h₁ | h₁
  · exact lessBT_linear_trans a b c hab h₁
  · rw [← eq_of_beq h₁]; exact hab

/-! ## 1. `BDom.toSet` の単射性（Isabelle の集合形 ↔ Lean の tag 形） -/

private theorem BZero_mem_TBv_b4 (v : ℕ∞) : BZero ∈ TBv v := by
  simp [TBv, BZero]

/-- `1 = D₀0`：全ての `TBv` に属し、`NatSet` にも属し、`0` ではない。 -/
private theorem one_mem_TBv_b4 (v : ℕ∞) : Dprin 0 BZero ∈ TBv v := by
  simp [TBv, Dprin, BZero]

private theorem one_ne_BZero_b4 : Dprin 0 BZero ≠ BZero := by
  simp [Dprin, BZero]

/-- `D₀(D₀0)`：全ての `TBv` に属すが `NatSet` には属さない。 -/
private theorem w2_mem_TBv_b4 (v : ℕ∞) : Dprin 0 (Dprin 0 BZero) ∈ TBv v := by
  simp [TBv, Dprin, BZero]

private theorem w2_not_mem_NatSet_b4 : Dprin 0 (Dprin 0 BZero) ∉ NatSet := by
  rintro ⟨n, hn⟩
  match n, hn with
  | 0, hn => simp [numBT, Dprin, BZero] at hn
  | 1, hn => simp [numBT, Dprin, BZero] at hn
  | (n + 2), hn => simp [numBT, List.replicate, Dprin, BZero] at hn

private theorem Dsucc_not_mem_NatSet_b4 (u : ℕ) :
    Dprin ((u + 1 : ℕ) : ℕ∞) BZero ∉ NatSet := by
  rintro ⟨n, hn⟩
  match n, hn with
  | 0, hn => simp [numBT, Dprin, BZero] at hn
  | 1, hn =>
      simp only [numBT, List.replicate, Dprin, BT.trm.injEq, List.cons.injEq,
        BP.db.injEq] at hn
      exact absurd hn.1.1.symm (by exact_mod_cast Nat.succ_ne_zero u)
  | (n + 2), hn => simp [numBT, List.replicate, Dprin, BZero] at hn

private theorem Dprin_mem_TBv_self_b4 (u : ℕ) :
    Dprin (u : ℕ∞) BZero ∈ TBv (u : ℕ∞) := by
  simp [TBv, Dprin, BZero]

private theorem Dprin_not_mem_TBv_lt_b4 {u v : ℕ} (h : v < u) :
    Dprin (u : ℕ∞) BZero ∉ TBv (v : ℕ∞) := by
  simp only [TBv, Dprin, Set.mem_setOf_eq, List.all_cons, List.all_nil,
    Bool.and_true, decide_eq_true_eq, not_le]
  exact_mod_cast h

private theorem TBv_inj_b4 {u v : ℕ} (h : TBv (u : ℕ∞) = TBv (v : ℕ∞)) : u = v := by
  by_contra hne
  rcases Nat.lt_or_ge u v with hlt | hge
  · exact Dprin_not_mem_TBv_lt_b4 hlt (h ▸ Dprin_mem_TBv_self_b4 v)
  · have hlt : v < u := lt_of_le_of_ne hge (Ne.symm hne)
    exact Dprin_not_mem_TBv_lt_b4 hlt (h ▸ Dprin_mem_TBv_self_b4 u)

private theorem BZero_mem_NatSet_b4 : BZero ∈ NatSet := ⟨0, rfl⟩

private theorem one_mem_NatSet_b4 : Dprin 0 BZero ∈ NatSet :=
  ⟨1, by simp [numBT, Dprin, BZero, List.replicate]⟩

/-- `BDom` のタグは、その表す集合で決まる。 -/
private theorem BDom_toSet_inj_b4 {d e : BDom} (h : d.toSet = e.toSet) : d = e := by
  cases d with
  | empty =>
      cases e with
      | empty => rfl
      | zeroOnly =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ (rfl : BZero ∈ ({BZero} : Set BT))
          exact absurd this (by simp [BDom.toSet])
      | naturals =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ BZero_mem_NatSet_b4
          exact absurd this (by simp [BDom.toSet])
      | below u =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ BZero_mem_TBv_b4 (u : ℕ∞)
          exact absurd this (by simp [BDom.toSet])
  | zeroOnly =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.zeroOnly).toSet := rfl
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly => rfl
      | naturals =>
          have : Dprin 0 BZero ∈ (BDom.zeroOnly).toSet := h ▸ one_mem_NatSet_b4
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b4)
      | below u =>
          have : Dprin 0 BZero ∈ (BDom.zeroOnly).toSet := h ▸ one_mem_TBv_b4 (u : ℕ∞)
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b4)
  | naturals =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.naturals).toSet := BZero_mem_NatSet_b4
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly =>
          have : Dprin 0 BZero ∈ (BDom.naturals).toSet := one_mem_NatSet_b4
          rw [h] at this
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b4)
      | naturals => rfl
      | below u =>
          have : Dprin 0 (Dprin 0 BZero) ∈ (BDom.naturals).toSet :=
            h ▸ w2_mem_TBv_b4 (u : ℕ∞)
          exact absurd this w2_not_mem_NatSet_b4
  | below u =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.below u).toSet := BZero_mem_TBv_b4 (u : ℕ∞)
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly =>
          have : Dprin 0 BZero ∈ (BDom.below u).toSet := one_mem_TBv_b4 (u : ℕ∞)
          rw [h] at this
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b4)
      | naturals =>
          have : Dprin 0 (Dprin 0 BZero) ∈ (BDom.below u).toSet :=
            w2_mem_TBv_b4 (u : ℕ∞)
          rw [h] at this
          exact absurd this w2_not_mem_NatSet_b4
      | below v =>
          exact congrArg BDom.below (TBv_inj_b4 (by simpa [BDom.toSet] using h))

/-- Isabelle の `domB a = TBv (enat u)` を tag 形へ。 -/
private theorem domB_below_iff_b4 (a : BT) (u : ℕ) :
    domB a = TBv (u : ℕ∞) ↔ domTag a = .below u := by
  constructor
  · intro h; exact BDom_toSet_inj_b4 (d := domTag a) (e := .below u) h
  · intro h; simp [domB, h, BDom.toSet]

/-- Isabelle の `domB a = NatSet` を tag 形へ。 -/
private theorem domB_nat_iff_b4 (a : BT) :
    domB a = NatSet ↔ domTag a = .naturals := by
  constructor
  · intro h; exact BDom_toSet_inj_b4 (d := domTag a) (e := .naturals) h
  · intro h; simp [domB, h, BDom.toSet]

/-- Isabelle の `domB a = {Trm []}` を tag 形へ。 -/
private theorem domB_zero_iff_b4 (a : BT) :
    domB a = {BZero} ↔ domTag a = .zeroOnly := by
  constructor
  · intro h; exact BDom_toSet_inj_b4 (d := domTag a) (e := .zeroOnly) h
  · intro h; simp [domB, h, BDom.toSet]

/-! ## 2. `operB` / `xseq` / `domTag` の展開（Isabelle の `b1x_*` / `bwl_*` 相当）

すべて `bOperCore` の定義的簡約。built tree では `private` なので再証明する。 -/

/-- Isabelle `b1x_xseq_0` (layerB/pss_wip.thy:28152)。 -/
private theorem xseq_zero_b4 (b : BT) (u : ℕ∞) :
    xseq b u 0 = Dprin u BZero := by
  simp [xseq, bOperCore]

/-- Isabelle `b1x_xseq_Suc` (layerB/pss_wip.thy:28155)。 -/
private theorem xseq_succ_b4 (b : BT) (u : ℕ∞) (i : ℕ) :
    xseq b u (i + 1) = Dprin u (operB b (xseq b u i)) := by
  simp [xseq, bOperCore, operB]

/-- Isabelle `b1x_operB_D0` (layerB/pss_wip.thy:28163)。 -/
private theorem operB_D0_b4 (z : BT) : operB (Dprin 0 BZero) z = BZero := by
  simp [operB, bOperCore, Dprin, BZero]

/-- Isabelle `b1x_operB_Dsucc` (layerB/pss_wip.thy:28170)。 -/
private theorem operB_Dsucc_b4 {v : ℕ∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) (z : BT) :
    operB (Dprin v BZero) z = z := by
  simp [operB, bOperCore, Dprin, BZero, hv0, hvtop]

/-- Isabelle `b1x_operB_case_i` (layerB/pss_wip.thy:28179)。 -/
private theorem operB_case_i_b4 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdb : domTag b = .zeroOnly) (z : BT) :
    operB (Dprin v b) z = multBT (Dprin v (operB b BZero)) (numNat z + 1) := by
  simp [operB, bOperCore, Dprin, hb, hdb]

/-- Isabelle `bwl_operB_case_ii`：訂正 A23 後の塔分岐。 -/
private theorem operB_case_ii_b4 {v : ℕ∞} {b : BT} {u : ℕ} (hb : b ≠ BZero)
    (hdb : domTag b = .below u) (hvu : v ≤ (u : ℕ∞)) (z : BT) :
    operB (Dprin v b) z = Dprin v (operB b (xseq b (u : ℕ∞) (numNat z))) := by
  simp [operB, bOperCore, Dprin, hb, hdb, hvu, xseq]

/-- Isabelle `b1x_operB_case_iii` (layerB/pss_wip.thy:28185)。 -/
private theorem operB_case_iii_b4 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdz : domTag b ≠ .zeroOnly)
    (hk : ∀ u : ℕ, domTag b = .below u → ¬ (v ≤ (u : ℕ∞))) (z : BT) :
    operB (Dprin v b) z = Dprin v (operB b z) := by
  cases hdb : domTag b with
  | empty => simp [operB, bOperCore, Dprin, hb, hdb]
  | zeroOnly => exact absurd hdb hdz
  | naturals => simp [operB, bOperCore, Dprin, hb, hdb]
  | below u => simp [operB, bOperCore, Dprin, hb, hdb, hk u hdb]

/-- Isabelle `b1x_operB_multi` (layerB/pss_wip.thy:28196)。 -/
private theorem operB_multi_b4 (p q : BP) (ps : List BP) (z : BT) :
    operB (.trm (p :: q :: ps)) z =
      addBT (.trm [p]) (operB (.trm (q :: ps)) z) := by
  simp [operB, bOperCore]

/-- Isabelle `domB_last_component`：multi 項の `dom` は末尾 principal の `dom`。 -/
private theorem domTag_cons_cons_b4 (p q : BP) (ps : List BP) :
    domTag (.trm (p :: q :: ps)) = domTag (.trm (q :: ps)) := by
  simp [domTag, domTagList]

/-- Isabelle `b1x_domB_Dsucc` (layerB/pss_wip.thy:28216)。 -/
private theorem domTag_Dsucc_b4 {v : ℕ∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    domTag (Dprin v BZero) = .below (v.toNat - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero, hv0, hvtop]

/-- Isabelle `bwl_domB_case_i`。 -/
private theorem domTag_case_i_b4 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdb : domTag b = .zeroOnly) : domTag (Dprin v b) = .naturals := by
  simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]

/-- Isabelle `bwl_domB_case_ii`。 -/
private theorem domTag_case_ii_b4 {v : ℕ∞} {b : BT} {u : ℕ} (hb : b ≠ BZero)
    (hdb : domTag b = .below u) (hvu : v ≤ (u : ℕ∞)) :
    domTag (Dprin v b) = .naturals := by
  simp [domTag, domTagList, domTagBP, Dprin, hb, hdb, hvu]

/-- Isabelle `b1x_domB_case_iii` (layerB/pss_wip.thy:28205)。 -/
private theorem domTag_case_iii_b4 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdz : domTag b ≠ .zeroOnly)
    (hk : ∀ u : ℕ, domTag b = .below u → ¬ (v ≤ (u : ℕ∞))) :
    domTag (Dprin v b) = domTag b := by
  cases hdb : domTag b with
  | empty => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]
  | zeroOnly => exact absurd hdb hdz
  | naturals => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]
  | below u => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb, hk u hdb]

/-- Isabelle `bwl_numNat_numBT`。 -/
private theorem numNat_numBT_b4 (n : ℕ) : numNat (numBT n) = n := by
  simp [numNat, numBT]

/-- Isabelle `b1x_mult_single` (layerB/pss_wip.thy:28225)。 -/
private theorem multBT_single_b4 (q : BP) (n : ℕ) :
    multBT (.trm [q]) n = .trm (List.replicate n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [multBT, ih]
      simp [addBT, List.replicate_succ']

/-! ## 3. `operB` の単調性・下界性と `GBT` の基本性質

Isabelle `b1x_mono` (layerB/pss_wip.thy:50059) / `b1x_lowerbound` (同 50147) /
`b1x_GBT_size` (同 50212) / `b1x_GBT_trans` (同 50234) / `b1x_GBT_antitone` (同 50257)。
built tree の `7.1-buchholz-fseq-closed` に同内容の `private` 版があるが、
`private` は参照できないので公開補題（`addBT_lt_right_bf` 等）から再証明する。 -/

/-- Isabelle `b1x_mono`：`dom a = T_w` 上で `a[·]` は狭義単調。 -/
private theorem operB_mono_below_b4 (a z₁ z₂ : BT) (w : ℕ)
    (htag : domTag a = .below w)
    (hz₁ : z₁ ∈ TBv (w : ℕ∞)) (hz₂ : z₂ ∈ TBv (w : ℕ∞))
    (hzlt : lessBT z₁ z₂ = true) :
    lessBT (operB a z₁) (operB a z₂) = true := by
  generalize hn : btWeight a = n
  induction n using Nat.strong_induction_on generalizing a w z₁ z₂ with
  | h n ih =>
      rcases a with ⟨xs⟩
      cases xs with
      | nil => simp [domTag, domTagList] at htag
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, b⟩
              by_cases hb : b = BZero
              · subst b
                by_cases hv₀ : v = 0
                · subst v
                  simp [domTag, domTagList, domTagBP, BZero] at htag
                · by_cases hvtop : v = ⊤
                  · subst v
                    simp [domTag, domTagList, domTagBP, BZero, hv₀] at htag
                  · simpa [operB, bOperCore, BZero, hv₀, hvtop] using hzlt
              · cases hdb : domTag b with
                | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | below u =>
                    by_cases hvu : v ≤ (u : ℕ∞)
                    · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag
                    · have huw : u = w := by
                        simpa [domTag, domTagList, domTagBP, hb, hdb, hvu] using htag
                      subst w
                      have hbn : btWeight b < n := by
                        rw [← hn]
                        simp [btWeight, bpListWeight, bpWeight]
                        omega
                      have hrec := ih (btWeight b) hbn b z₁ z₂ u hdb hz₁ hz₂ hzlt rfl
                      simpa [operB, bOperCore, Dprin, hb, hdb, hvu,
                        lessBT, lessBPList, lessBP, hrec]
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < n := by
                rw [← hn]
                simp [btWeight, bpListWeight]
              have htagtail : domTag (.trm (q :: qs)) = .below w := by
                simpa [domTag, domTagList] using htag
              have hrec := ih (btWeight (.trm (q :: qs))) htailn
                (.trm (q :: qs)) z₁ z₂ w htagtail hz₁ hz₂ hzlt rfl
              have hadd := addBT_lt_right_bf (.trm [p])
                (operB (.trm (q :: qs)) z₁)
                (operB (.trm (q :: qs)) z₂) hrec
              simpa [operB, bOperCore, addBT] using hadd

private theorem OT_tag_below_head_b4 (p : BP) (ps : List BP) (w : ℕ)
    (hot : isOT_BT (.trm (p :: ps)) = true)
    (htag : domTag (.trm (p :: ps)) = .below w) :
    ∃ h c, p = .db h c ∧ (w : ℕ∞) < h := by
  let ys := p :: ps
  have hne : ys ≠ [] := by simp [ys]
  cases hlast : ys.getLast hne with
  | db hl cl =>
      have hotsplit : isOT_BPList ys = true ∧ descP ys = true := by
        simpa [ys, isOT_BT] using hot
      have htaglp : domTagBP (.db hl cl) = .below w := by
        rw [← domTag_snoc_bf ys.dropLast (.db hl cl)]
        have hdecomp : ys.dropLast ++ [.db hl cl] = ys := by
          rw [← hlast]
          exact List.dropLast_append_getLast hne
        rw [hdecomp]
        simpa [ys] using htag
      have hwhl : (w : ℕ∞) < hl := domTagBP_below_head_bf htaglp
      rcases p with ⟨hp, cp⟩
      have hle : leBT (.trm [.db hl cl]) (.trm [.db hp cp]) = true := by
        have hle₀ := descP_last_head_bf (.db hp cp) ps hotsplit.2
        simpa [ys, hlast] using hle₀
      have hhlp : hl ≤ hp := leBT_single_index_bf hl hp cl cp hle
      exact ⟨hp, cp, rfl, hwhl.trans_le hhlp⟩

/-- Isabelle `b1x_lowerbound`：`dom a = T_w` かつ `z ∈ T_w` なら `z ≤ a[z]`。 -/
private theorem operB_lowerbound_below_b4 (a z : BT) (w : ℕ)
    (hot : isOT_BT a = true) (htag : domTag a = .below w)
    (hz : z ∈ TBv (w : ℕ∞)) : leBT z (operB a z) = true := by
  rcases a with ⟨xs⟩
  cases xs with
  | nil => simp [domTag, domTagList] at htag
  | cons p ps =>
      cases ps with
      | nil =>
          rcases p with ⟨v, b⟩
          by_cases hb : b = BZero
          · subst b
            by_cases hv₀ : v = 0
            · subst v
              simp [domTag, domTagList, domTagBP, BZero] at htag
            · by_cases hvtop : v = ⊤
              · subst v
                simp [domTag, domTagList, domTagBP, BZero, hv₀] at htag
              · simpa [operB, bOperCore, BZero, hv₀, hvtop] using
                  leBT_refl_b4 z
          · cases hdb : domTag b with
            | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | below u =>
                by_cases hvu : v ≤ (u : ℕ∞)
                · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag
                · have huw : u = w := by
                    simpa [domTag, domTagList, domTagBP, hb, hdb, hvu] using htag
                  subst w
                  have huv : (u : ℕ∞) < v := lt_of_not_ge hvu
                  apply leBT_of_less_b4
                  simpa [operB, bOperCore, Dprin, hb, hdb, hvu] using
                    (TBv_lt_head_bf (z := z) (c := operB b z)
                      (rest := []) hz huv)
      | cons q qs =>
          obtain ⟨h, c, hp, hwh⟩ :=
            OT_tag_below_head_b4 p (q :: qs) w hot htag
          subst p
          rcases hopen : operB (.trm (q :: qs)) z with ⟨rs⟩
          apply leBT_of_less_b4
          have hlt := TBv_lt_head_bf (z := z) (c := c) (rest := rs) hz hwh
          have hop : operB (.trm (.db h c :: q :: qs)) z =
              addBT (.trm [.db h c]) (operB (.trm (q :: qs)) z) := by
            simp [operB, bOperCore]
          rw [hop, hopen]
          simpa [addBT] using hlt

/-! `GBT` の三性質。`gatherBT` 上の相互再帰で示す。 -/

mutual
  private theorem mem_gatherBT_weight_b4 (u : ℕ∞) (x : BT) :
      ∀ t : BT, x ∈ gatherBT u t → btWeight x < btWeight t
    | .trm ps, hx => by
        have hlt := mem_gatherBPList_weight_b4 u x ps (by
          simpa [gatherBT] using hx)
        simp only [btWeight]
        omega

  private theorem mem_gatherBP_weight_b4 (u : ℕ∞) (x : BT) :
      ∀ p : BP, x ∈ gatherBP u p → btWeight x < bpWeight p
    | .db v b, hx => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [bpWeight]
          · have hlt := mem_gatherBT_weight_b4 u x b hx
            simp only [bpWeight]
            omega
        · simp [gatherBP, huv] at hx

  private theorem mem_gatherBPList_weight_b4 (u : ℕ∞) (x : BT) :
      ∀ ps : List BP, x ∈ gatherBPList u ps → btWeight x < bpListWeight ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx
        rcases hx with hx | hx
        · have hlt := mem_gatherBP_weight_b4 u x p hx
          simp only [bpListWeight]
          omega
        · have hlt := mem_gatherBPList_weight_b4 u x ps hx
          simp only [bpListWeight]
          omega
end

/-- Isabelle `b1x_GBT_size`（Lean では `size` の代わりに `btWeight`）。 -/
private theorem GBT_weight_lt_b4 {u : ℕ∞} {x t : BT}
    (hx : x ∈ GBT u t) : btWeight x < btWeight t := by
  apply mem_gatherBT_weight_b4 u x t
  simpa [GBT] using hx

mutual
  private theorem gatherBT_trans_mem_b4 (u : ℕ∞) (y : BT) :
      ∀ t x : BT, x ∈ gatherBT u t → y ∈ gatherBT u x →
        y ∈ gatherBT u t
    | .trm ps, x, hx, hy =>
        gatherBPList_trans_mem_b4 u y ps x hx hy

  private theorem gatherBP_trans_mem_b4 (u : ℕ∞) (y : BT) :
      ∀ p : BP, ∀ x : BT, x ∈ gatherBP u p → y ∈ gatherBT u x →
        y ∈ gatherBP u p
    | .db v b, x, hx, hy => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true,
            List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr hy
          · exact Or.inr (gatherBT_trans_mem_b4 u y b x hx hy)
        · simp [gatherBP, huv] at hx

  private theorem gatherBPList_trans_mem_b4 (u : ℕ∞) (y : BT) :
      ∀ ps : List BP, ∀ x : BT,
        x ∈ gatherBPList u ps → y ∈ gatherBT u x →
          y ∈ gatherBPList u ps
    | [], x, hx, _ => by simp [gatherBPList] at hx
    | p :: ps, x, hx, hy => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_trans_mem_b4 u y p x hx hy)
        · exact Or.inr (gatherBPList_trans_mem_b4 u y ps x hx hy)
end

/-- Isabelle `b1x_GBT_trans`。 -/
private theorem GBT_trans_b4 {u : ℕ∞} {x t : BT}
    (hx : x ∈ GBT u t) : GBT u x ⊆ GBT u t := by
  intro y hy
  have hout := gatherBT_trans_mem_b4 u y t x
    (by simpa [GBT] using hx) (by simpa [GBT] using hy)
  simpa [GBT] using hout

mutual
  private theorem gatherBT_antitone_mem_b4 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ t : BT, x ∈ gatherBT v t → x ∈ gatherBT u t
    | .trm ps, hx => gatherBPList_antitone_mem_b4 huv x ps hx

  private theorem gatherBP_antitone_mem_b4 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ p : BP, x ∈ gatherBP v p → x ∈ gatherBP u p
    | .db w b, hx => by
        have hvw : v ≤ w := by
          by_contra hn
          simp [gatherBP, hn] at hx
        have huw : u ≤ w := huv.trans hvw
        simp only [gatherBP, hvw, huw, decide_true, if_true,
          List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (gatherBT_antitone_mem_b4 huv x b hx)

  private theorem gatherBPList_antitone_mem_b4 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ ps : List BP,
        x ∈ gatherBPList v ps → x ∈ gatherBPList u ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_antitone_mem_b4 huv x p hx)
        · exact Or.inr (gatherBPList_antitone_mem_b4 huv x ps hx)
end

/-- Isabelle `b1x_GBT_antitone`。 -/
private theorem GBT_antitone_b4 {u v : ℕ∞} (huv : u ≤ v) (t : BT) :
    GBT v t ⊆ GBT u t := by
  intro x hx
  have hout := gatherBT_antitone_mem_b4 huv x t (by simpa [GBT] using hx)
  simpa [GBT] using hout

/-! ## 4. y4 ブロック (1) — 塔 `xseq` の狭義単調性

Isabelle: `isabelle/layerC/pss_scratch.thy` 12493–12566。 -/

/-- Isabelle `b1x_Dpt_TBv` (layerB/pss_wip.thy:28261)。 -/
private theorem Dpt_TBv_b4 (u : ℕ∞) (t : BT) : Dprin u t ∈ TBv u := by
  simp [TBv, Dprin]

private theorem BZero_lt_Dprin_b4 (v : ℕ∞) (t : BT) :
    lessBT BZero (Dprin v t) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- 同一指標の principal は本体の順序を反映する。 -/
private theorem Dprin_lt_Dprin_b4 {a b : BT} (v : ℕ∞) (h : lessBT a b = true) :
    lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- Isabelle `y4_xseq_Dpt` (pss_scratch.thy:12493)。 -/
theorem y4_xseq_Dpt (c : BT) (u : ℕ) (n : ℕ) :
    ∃ t, xseq c (u : ℕ∞) n = Dprin (u : ℕ∞) t := by
  cases n with
  | zero => exact ⟨BZero, xseq_zero_b4 c (u : ℕ∞)⟩
  | succ j => exact ⟨operB c (xseq c (u : ℕ∞) j), xseq_succ_b4 c (u : ℕ∞) j⟩

/-- Isabelle `y4_xseq_TBv` (pss_scratch.thy:12502)。 -/
theorem y4_xseq_TBv (c : BT) (u : ℕ) (n : ℕ) :
    xseq c (u : ℕ∞) n ∈ TBv (u : ℕ∞) := by
  obtain ⟨t, ht⟩ := y4_xseq_Dpt c u n
  rw [ht]
  exact Dpt_TBv_b4 (u : ℕ∞) t

/-- Isabelle `y4_xseq_lt` (pss_scratch.thy:12509)：塔は 1 段ごとに狭義増加。 -/
theorem y4_xseq_lt (c : BT) (u : ℕ) (n : ℕ)
    (ot : isOT_BT c = true) (dc : domTag c = .below u) :
    lessBT (xseq c (u : ℕ∞) n) (xseq c (u : ℕ∞) (n + 1)) = true := by
  induction n with
  | zero =>
      have x0 : xseq c (u : ℕ∞) 0 = Dprin (u : ℕ∞) BZero := xseq_zero_b4 c (u : ℕ∞)
      have x1 : xseq c (u : ℕ∞) 1 = Dprin (u : ℕ∞) (operB c (xseq c (u : ℕ∞) 0)) :=
        xseq_succ_b4 c (u : ℕ∞) 0
      have zin : xseq c (u : ℕ∞) 0 ∈ TBv (u : ℕ∞) := y4_xseq_TBv c u 0
      have le : leBT (xseq c (u : ℕ∞) 0) (operB c (xseq c (u : ℕ∞) 0)) = true :=
        operB_lowerbound_below_b4 c (xseq c (u : ℕ∞) 0) u ot dc zin
      have z0ne : lessBT BZero (xseq c (u : ℕ∞) 0) = true := by
        rw [x0]; exact BZero_lt_Dprin_b4 (u : ℕ∞) BZero
      have ne : lessBT BZero (operB c (xseq c (u : ℕ∞) 0)) = true :=
        less_le_trans_b4 z0ne le
      rw [x0, x1]
      exact Dprin_lt_Dprin_b4 (u : ℕ∞) ne
  | succ n ih =>
      have e1 : xseq c (u : ℕ∞) (n + 1) =
          Dprin (u : ℕ∞) (operB c (xseq c (u : ℕ∞) n)) := xseq_succ_b4 c (u : ℕ∞) n
      have e2 : xseq c (u : ℕ∞) (n + 1 + 1) =
          Dprin (u : ℕ∞) (operB c (xseq c (u : ℕ∞) (n + 1))) :=
        xseq_succ_b4 c (u : ℕ∞) (n + 1)
      have z1 : xseq c (u : ℕ∞) n ∈ TBv (u : ℕ∞) := y4_xseq_TBv c u n
      have z2 : xseq c (u : ℕ∞) (n + 1) ∈ TBv (u : ℕ∞) := y4_xseq_TBv c u (n + 1)
      have blt : lessBT (operB c (xseq c (u : ℕ∞) n))
          (operB c (xseq c (u : ℕ∞) (n + 1))) = true :=
        operB_mono_below_b4 c _ _ u dc z1 z2 ih
      rw [e1, e2]
      exact Dprin_lt_Dprin_b4 (u : ℕ∞) blt

/-- Isabelle `y4_xseq_mono` (pss_scratch.thy:12538)。 -/
theorem y4_xseq_mono (c : BT) (u : ℕ) (m n : ℕ)
    (ot : isOT_BT c = true) (dc : domTag c = .below u) (mn : m < n) :
    lessBT (xseq c (u : ℕ∞) m) (xseq c (u : ℕ∞) n) = true := by
  induction n with
  | zero => exact absurd mn (Nat.not_lt_zero m)
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp mn with hmn | hmn
      · exact lessBT_linear_trans _ _ _ (ih hmn) (y4_xseq_lt c u n ot dc)
      · subst hmn; exact y4_xseq_lt c u m ot dc

/-- Isabelle `y4_xseq_le_mono` (pss_scratch.thy:12558)。 -/
theorem y4_xseq_le_mono (c : BT) (u : ℕ) (m n : ℕ)
    (ot : isOT_BT c = true) (dc : domTag c = .below u) (mn : m ≤ n) :
    leBT (xseq c (u : ℕ∞) m) (xseq c (u : ℕ∞) n) = true := by
  rcases Nat.eq_or_lt_of_le mn with rfl | hlt
  · exact leBT_refl_b4 _
  · exact leBT_of_less_b4 (y4_xseq_mono c u m n ot dc hlt)

/-! ## 5. y4 ブロック (2) — `addBT` の順序補題と prefix split

Isabelle: `isabelle/layerC/pss_scratch.thy` 12568–12659。 -/

private theorem lessBPList_append_self_b4 (as bs : List BP) (hbs : bs ≠ []) :
    lessBPList as (as ++ bs) = true := by
  induction as with
  | nil =>
      cases bs with
      | nil => exact absurd rfl hbs
      | cons b bs => simp [lessBPList]
  | cons a as ih => simp [lessBPList, ih]

/-- Isabelle `lessBT_addBT_self` (layerB/pss_wip.thy:2431)。 -/
private theorem lessBT_addBT_self_b4 (t c : BT) (hc : c ≠ BZero) :
    lessBT t (addBT t c) = true := by
  rcases t with ⟨as⟩
  rcases c with ⟨bs⟩
  have hbs : bs ≠ [] := by rintro rfl; exact hc rfl
  simpa [addBT, lessBT] using lessBPList_append_self_b4 as bs hbs

/-- Isabelle `y4_leBT_addBT_self` (pss_scratch.thy:12568)。 -/
theorem y4_leBT_addBT_self (t c : BT) : leBT t (addBT t c) = true := by
  by_cases hc : c = BZero
  · subst c
    have : addBT t BZero = t := by rcases t with ⟨as⟩; simp [addBT, BZero]
    rw [this]; exact leBT_refl_b4 t
  · exact leBT_of_less_b4 (lessBT_addBT_self_b4 t c hc)

/-- Isabelle `y4_leBT_addBT_mono_right` (pss_scratch.thy:12578)。 -/
theorem y4_leBT_addBT_mono_right {a b : BT} (t : BT) (h : leBT a b = true) :
    leBT (addBT t a) (addBT t b) = true := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact leBT_of_less_b4 (addBT_lt_right_bf t a b h')
  · rw [eq_of_beq h']; exact leBT_refl_b4 _

private theorem lessBPList_nil_right_b4 (xs : List BP) : lessBPList xs [] = false := by
  cases xs <;> simp [lessBPList]

/-- Isabelle `y4_prefix_split` (pss_scratch.thy:12587)：`(a₀,…,a_k)` 未満の項は、
前部 `(a₀,…,a_{k-1})` 以下か、その前部を先頭 principal `< a_k` の非空ブロックで
延長したもの。多項の Bachmann 性を単項の場合へ帰着させる要。

Isabelle の `∃rs. ys = ps @ rs ∧ rs ≠ [] ∧ lessBP (hd rs) q` は、`hd` の
`Inhabited BP` 要求を避けるため、非空ブロックを `r :: rs` と分解した同値形で書く。 -/
theorem y4_prefix_split {ys ps : List BP} {q : BP}
    (h : lessBT (.trm ys) (.trm (ps ++ [q])) = true) :
    leBT (.trm ys) (.trm ps) = true ∨
      (∃ r rs, ys = ps ++ r :: rs ∧ lessBP r q = true) := by
  induction ps generalizing ys with
  | nil =>
      cases ys with
      | nil => exact Or.inl (by simp [leBT])
      | cons r rs' =>
          have h' : (lessBP r q || (r == q && lessBPList rs' [])) = true := by
            simpa [lessBT, lessBPList] using h
          rw [lessBPList_nil_right_b4 rs'] at h'
          simp only [Bool.and_false, Bool.or_false] at h'
          exact Or.inr ⟨r, rs', by simp, h'⟩
  | cons p ps' ih =>
      cases ys with
      | nil => exact Or.inl (by simp [leBT, lessBT, lessBPList])
      | cons r rs' =>
          have h' : (lessBP r p || (r == p && lessBPList rs' (ps' ++ [q]))) = true := by
            simpa [lessBT, lessBPList] using h
          rcases Bool.or_eq_true_iff.mp h' with hlt | hand
          · exact Or.inl (by simp [leBT, lessBT, lessBPList, hlt])
          · rcases Bool.and_eq_true_iff.mp hand with ⟨hrp, hrec⟩
            have rp : r = p := eq_of_beq hrp
            subst rp
            have hrec' : lessBT (.trm rs') (.trm (ps' ++ [q])) = true := by
              simpa [lessBT] using hrec
            rcases ih hrec' with hle | ⟨r2, rs2, hseq, hslt⟩
            · refine Or.inl ?_
              rcases Bool.or_eq_true_iff.mp hle with hlt2 | heq2
              · have hlp : lessBPList rs' ps' = true := by simpa [lessBT] using hlt2
                simp [leBT, lessBT, lessBPList, hlp]
              · have hrs : rs' = ps' := by simpa using eq_of_beq heq2
                subst hrs
                exact leBT_refl_b4 _
            · exact Or.inr ⟨r2, rs2, by simp [hseq], hslt⟩

/-- Isabelle `y4_descP_suffix` (pss_scratch.thy:12640)。 -/
theorem y4_descP_suffix {ps rs : List BP} (h : descP (ps ++ rs) = true) :
    descP rs = true := by
  induction ps with
  | nil => simpa using h
  | cons p ps ih =>
      apply ih
      rw [List.cons_append] at h
      cases hps : ps ++ rs with
      | nil => rfl
      | cons q qs =>
          rw [hps] at h
          simp only [descP, Bool.and_eq_true] at h
          exact h.2

private theorem isOT_BPList_suffix_b4 (ps rs : List BP)
    (h : isOT_BPList (ps ++ rs) = true) : isOT_BPList rs = true := by
  induction ps with
  | nil => simpa using h
  | cons p ps ih =>
      apply ih
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at h
      exact h.2

/-- Isabelle `y4_OT_suffix` (pss_scratch.thy:12643)。 -/
theorem y4_OT_suffix {ps rs : List BP} (h : isOT_BT (.trm (ps ++ rs)) = true) :
    isOT_BT (.trm rs) = true := by
  simp only [isOT_BT, Bool.and_eq_true] at h ⊢
  exact ⟨isOT_BPList_suffix_b4 ps rs h.1, y4_descP_suffix h.2⟩

/-- Isabelle `y4_GBT_suffix` (pss_scratch.thy:12647)。 -/
theorem y4_GBT_suffix (u : ℕ∞) (rs ps : List BP) :
    GBT u (.trm rs) ⊆ GBT u (.trm (ps ++ rs)) := by
  intro x hx
  induction ps with
  | nil => simpa using hx
  | cons p ps ih =>
      have hin : (gatherBPList u (ps ++ rs)).contains x = true := by
        simpa [GBT, gatherBT] using ih
      simp only [GBT, gatherBT, List.cons_append, gatherBPList,
        Set.mem_setOf_eq, List.contains_append, Bool.or_eq_true]
      exact Or.inr hin

private theorem dfree_BPList_suffix_b4 (ps rs : List BP)
    (h : dfree_BPList (ps ++ rs) = true) : dfree_BPList rs = true := by
  induction ps with
  | nil => simpa using h
  | cons p ps ih =>
      apply ih
      simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h
      exact h.2

/-- Isabelle `y4_dfree_suffix` (pss_scratch.thy:13242)。 -/
theorem y4_dfree_suffix {ps rs : List BP} (h : dfree_BT (.trm (ps ++ rs)) = true) :
    dfree_BT (.trm rs) = true := by
  simp only [dfree_BT] at h ⊢
  exact dfree_BPList_suffix_b4 ps rs h

/-! ## 6. y4 ブロック (5) — Bachmann 帰納のための補助群

Isabelle: `isabelle/layerC/pss_scratch.thy` 13060–13260。 -/

private theorem BZero_lt_of_ne_b4 {a : BT} (hne : a ≠ BZero) :
    lessBT BZero a = true := by
  rcases a with ⟨ps⟩
  cases ps with
  | nil => exact (hne rfl).elim
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-- Isabelle `y4_descP_all_le_hd` (pss_scratch.thy:13060)：`descP` リストでは
全ての principal が先頭以下。 -/
theorem y4_descP_all_le_hd {p p1 : BP} {ps : List BP}
    (h : descP (p1 :: ps) = true) (hp : p ∈ p1 :: ps) :
    leBT (.trm [p]) (.trm [p1]) = true := by
  induction ps generalizing p1 with
  | nil =>
      have hpe : p = p1 := by simpa using hp
      subst hpe; exact leBT_refl_b4 _
  | cons q qs ih =>
      simp only [descP, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact leBT_refl_b4 _
      · exact leBT_trans_b4 (ih h.2 hp') h.1

/-- Isabelle `y4_TBv_of_head` (pss_scratch.thy:13084)：先頭指標が `≤ m` の `OT` 項は
`T_m` に属す（`descP` により全指標が先頭以下だから）。 -/
theorem y4_TBv_of_head {w : ℕ∞} {e : BT} {rs : List BP} {m : ℕ}
    (ot : isOT_BT (.trm (.db w e :: rs)) = true) (wm : w ≤ (m : ℕ∞)) :
    (.trm (.db w e :: rs) : BT) ∈ TBv (m : ℕ∞) := by
  have dsc : descP (.db w e :: rs) = true :=
    (Bool.and_eq_true_iff.mp (by simpa [isOT_BT] using ot)).2
  simp only [TBv, Set.mem_setOf_eq, List.all_eq_true]
  intro p hp
  rcases p with ⟨u, t⟩
  have hle : leBT (.trm [.db u t]) (.trm [.db w e]) = true :=
    y4_descP_all_le_hd dsc hp
  have huw : u ≤ w := leBT_single_index_bf u w t e hle
  simp only [decide_eq_true_eq]
  exact huw.trans wm

/-- Isabelle `y4_leBT_min` (pss_scratch.thy:13102)：`1 = D₀0` は最小の principal。 -/
theorem y4_leBT_min (p : BP) : leBT (Dprin 0 BZero) (.trm [p]) = true := by
  rcases p with ⟨w, e⟩
  by_cases hw : w = 0
  · subst hw
    by_cases he : e = BZero
    · subst he; exact leBT_refl_b4 _
    · exact leBT_of_less_b4
        (by simp [Dprin, lessBT, lessBPList, lessBP, BZero_lt_of_ne_b4 he])
  · have h0w : (0 : ℕ∞) < w := pos_iff_ne_zero.mpr hw
    exact leBT_of_less_b4 (by simp [Dprin, lessBT, lessBPList, lessBP, h0w])

private theorem descP_snoc_min_b4 (zs : List BP) (h : descP zs = true) :
    descP (zs ++ [.db 0 BZero]) = true := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
      cases zs with
      | nil =>
          have := y4_leBT_min z
          simp [descP, Dprin] at this ⊢
          exact this
      | cons q qs =>
          simp only [descP, Bool.and_eq_true] at h
          have hrec := ih h.2
          simp only [List.cons_append, descP, Bool.and_eq_true]
          exact ⟨h.1, by simpa using hrec⟩

private theorem isOT_BPList_append_b4 (as bs : List BP)
    (ha : isOT_BPList as = true) (hb : isOT_BPList bs = true) :
    isOT_BPList (as ++ bs) = true := by
  induction as with
  | nil => simpa using hb
  | cons a as ih =>
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ih ha.2⟩

private theorem dfree_BPList_append_b4 (as bs : List BP)
    (ha : dfree_BPList as = true) (hb : dfree_BPList bs = true) :
    dfree_BPList (as ++ bs) = true := by
  induction as with
  | nil => simpa using hb
  | cons a as ih =>
      simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ih ha.2⟩

/-- Isabelle `y4_bump` (pss_scratch.thy:13128)：`T_m` の witness に `1` を足しても
`OT`・`D_ω`-free・`T_m` のままで、狭義に増える。Bachmann 帰納の等号場合を吸収する。 -/
theorem y4_bump {z : BT} {m : ℕ} (ot : isOT_BT z = true) (df : dfree_BT z = true)
    (tv : z ∈ TBv (m : ℕ∞)) :
    isOT_BT (addBT z (Dprin 0 BZero)) = true ∧
      dfree_BT (addBT z (Dprin 0 BZero)) = true ∧
      addBT z (Dprin 0 BZero) ∈ TBv (m : ℕ∞) ∧
      lessBT z (addBT z (Dprin 0 BZero)) = true := by
  rcases z with ⟨zs⟩
  have hsplit : isOT_BPList zs = true ∧ descP zs = true := by
    simpa [isOT_BT] using ot
  have hadd : addBT (.trm zs) (Dprin 0 BZero) = .trm (zs ++ [.db 0 BZero]) := by
    simp [addBT, Dprin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hadd]
    simp only [isOT_BT, Bool.and_eq_true]
    exact ⟨isOT_BPList_append_b4 zs _ hsplit.1 (by simp [isOT_BPList, isOT_BP,
        isOT_BT, BZero, descP, gatherBT, gatherBPList]),
      descP_snoc_min_b4 zs hsplit.2⟩
  · rw [hadd]
    simp only [dfree_BT]
    exact dfree_BPList_append_b4 zs _ (by simpa [dfree_BT] using df)
      (by simp [dfree_BPList, dfree_BP, dfree_BT, BZero])
  · rw [hadd]
    have hz : ∀ p ∈ zs, (match p with | .db u _ => decide (u ≤ (m : ℕ∞))) = true := by
      simpa [TBv, List.all_eq_true] using tv
    simp only [TBv, Set.mem_setOf_eq, List.all_eq_true, List.mem_append]
    rintro p (hp | hp)
    · exact hz p hp
    · have : p = .db 0 BZero := by simpa using hp
      subst this; simp
  · exact lessBT_addBT_self_b4 _ _ (by simp [Dprin, BZero])

/-- Isabelle `y4_operB_domzero_const` (pss_scratch.thy:13154)：`dom = {0}` の上では
括弧は引数を無視する（末尾 principal が `D₀0` で、単に削除されるだけ）。 -/
theorem y4_operB_domzero_const {c : BT} (h : domTag c = .zeroOnly) (z : BT) :
    operB c z = operB c BZero := by
  generalize hn : btWeight c = n
  induction n using Nat.strong_induction_on generalizing c z with
  | h n ih =>
      rcases c with ⟨cs⟩
      cases cs with
      | nil => simp [domTag, domTagList] at h
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, b⟩
              by_cases hb : b = BZero
              · subst b
                by_cases hv0 : v = 0
                · subst v
                  simp [operB, bOperCore, BZero]
                · by_cases hvtop : v = ⊤
                  · subst v
                    simp [domTag, domTagList, domTagBP, BZero, hv0] at h
                  · simp [domTag, domTagList, domTagBP, BZero, hv0, hvtop] at h
              · cases hdb : domTag b with
                | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at h
                | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at h
                | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at h
                | below u =>
                    by_cases hvu : v ≤ (u : ℕ∞)
                    · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at h
                    · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at h
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < n := by
                rw [← hn]; simp [btWeight, bpListWeight]
              have htagtail : domTag (.trm (q :: qs)) = .zeroOnly := by
                simpa [domTag, domTagList] using h
              have hrec := ih (btWeight (.trm (q :: qs))) htailn htagtail z rfl
              simp only [operB, bOperCore] at hrec ⊢
              rw [hrec]

/-- Isabelle `y4_le_replicate` (pss_scratch.thy:13221)：`descP` ブロックは、その先頭の
定数ブロック（同じ長さ）以下。([].4)(i) の等号吸収器。 -/
theorem y4_le_replicate {rs : List BP} {q : BP}
    (h : ∀ p ∈ rs, leBT (.trm [p]) (.trm [q]) = true) :
    leBT (.trm rs) (.trm (List.replicate rs.length q)) = true := by
  induction rs with
  | nil => simp [leBT]
  | cons r rs' ih =>
      have hd : leBT (.trm [r]) (.trm [q]) = true := h r (by simp)
      have ih' := ih (fun p hp => h p (by simp [hp]))
      simp only [List.length_cons, List.replicate_succ]
      by_cases hrq : r = q
      · subst hrq
        rcases Bool.or_eq_true_iff.mp ih' with hlt | heq
        · have hlp : lessBPList rs' (List.replicate rs'.length r) = true := by
            simpa [lessBT] using hlt
          simp [leBT, lessBT, lessBPList, hlp]
        · have hrs : rs' = List.replicate rs'.length r := by simpa using eq_of_beq heq
          rw [← hrs]; exact leBT_refl_b4 _
      · have hne : ¬ ((.trm [r] : BT) == .trm [q]) = true := by
          simp [hrq]
        have hlt : lessBP r q = true := by
          rcases Bool.or_eq_true_iff.mp hd with h' | h'
          · simpa [lessBT, lessBPList, lessBPList_nil_right_b4] using h'
          · exact absurd h' hne
        simp [leBT, lessBT, lessBPList, hlt]

/-! ## 7. y4 ブロック (4) — `ℕ` 添字基本列の狭義増加

Isabelle: `isabelle/layerC/pss_scratch.thy` 12912–13058。
[Buc1-Hydra] 3.3 の `<` 版。([].4)(ii) は `y4_xseq_lt`、([].4)(i) は数項ブロックの
前部成長。`D_ω`-freeness が `D_ω0` 枝を潰す。 -/

private theorem isOT_Dprin_body_b4 {v : ℕ∞} {b : BT}
    (h : isOT_BT (Dprin v b) = true) : isOT_BT b = true := by
  simp only [Dprin, isOT_BT, isOT_BPList, isOT_BP, descP, Bool.and_true,
    Bool.and_eq_true] at h
  tauto

private theorem isOT_Dprin_G_b4 {v : ℕ∞} {b : BT}
    (h : isOT_BT (Dprin v b) = true) : ∀ x ∈ GBT v b, lessBT x b = true := by
  intro x hx
  have hall : (gatherBT v b).all (fun y => lessBT y b) = true := by
    simp only [Dprin, isOT_BT, isOT_BPList, isOT_BP, descP, Bool.and_true,
      Bool.and_eq_true] at h
    tauto
  have hmem : x ∈ gatherBT v b := by simpa [GBT] using hx
  exact (List.all_eq_true.mp hall) x hmem

private theorem dfree_Dprin_body_b4 {v : ℕ∞} {b : BT}
    (h : dfree_BT (Dprin v b) = true) : dfree_BT b = true := by
  simp only [Dprin, dfree_BT, dfree_BPList, dfree_BP, Bool.and_true,
    Bool.and_eq_true] at h
  tauto

private theorem dfree_Dprin_idx_b4 {v : ℕ∞} {b : BT}
    (h : dfree_BT (Dprin v b) = true) : v ≠ ⊤ := by
  simp only [Dprin, dfree_BT, dfree_BPList, dfree_BP, Bool.and_true,
    Bool.and_eq_true, bne_iff_ne] at h
  tauto

private theorem isOT_tail_b4 {p : BP} {ps : List BP}
    (h : isOT_BT (.trm (p :: ps)) = true) : isOT_BT (.trm ps) = true := by
  have := y4_OT_suffix (ps := [p]) (rs := ps) (by simpa using h)
  simpa using this

private theorem dfree_tail_b4 {p : BP} {ps : List BP}
    (h : dfree_BT (.trm (p :: ps)) = true) : dfree_BT (.trm ps) = true := by
  have := y4_dfree_suffix (ps := [p]) (rs := ps) (by simpa using h)
  simpa using this

/-- Isabelle `y4_N_mono` (pss_scratch.thy:12912)。 -/
theorem y4_N_mono (a : BT) (n : ℕ) (ot : isOT_BT a = true) (df : dfree_BT a = true)
    (da : domTag a = .naturals) :
    lessBT (operB a (numBT n)) (operB a (numBT (n + 1))) = true := by
  generalize hn : btWeight a = N
  induction N using Nat.strong_induction_on generalizing a with
  | h N ih =>
      rcases a with ⟨xs⟩
      cases xs with
      | nil => simp [domTag, domTagList] at da
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, bb⟩
              by_cases hb : bb = BZero
              · subst bb
                by_cases hv0 : v = 0
                · subst v; simp [domTag, domTagList, domTagBP, BZero] at da
                · by_cases hvtop : v = ⊤
                  · subst v
                    exact absurd rfl (dfree_Dprin_idx_b4 (b := BZero)
                      (by simpa [Dprin] using df))
                  · simp [domTag, domTagList, domTagBP, BZero, hv0, hvtop] at da
              · have otbb : isOT_BT bb = true :=
                  isOT_Dprin_body_b4 (by simpa [Dprin] using ot)
                have dfbb : dfree_BT bb = true :=
                  dfree_Dprin_body_b4 (by simpa [Dprin] using df)
                have szbb : btWeight bb < N := by
                  rw [← hn]; simp [btWeight, bpListWeight, bpWeight]; omega
                cases hdb : domTag bb with
                | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at da
                | zeroOnly =>
                    have opn : operB (.trm [.db v bb]) (numBT n)
                        = .trm (List.replicate (n + 1) (.db v (operB bb BZero))) := by
                      rw [show (BT.trm [BP.db v bb]) = Dprin v bb from rfl,
                        operB_case_i_b4 hb hdb, numNat_numBT_b4]
                      exact multBT_single_b4 _ _
                    have opsn : operB (.trm [.db v bb]) (numBT (n + 1))
                        = .trm (List.replicate (n + 2) (.db v (operB bb BZero))) := by
                      rw [show (BT.trm [BP.db v bb]) = Dprin v bb from rfl,
                        operB_case_i_b4 hb hdb, numNat_numBT_b4]
                      exact multBT_single_b4 _ _
                    rw [opn, opsn, show List.replicate (n + 2) (BP.db v (operB bb BZero))
                      = List.replicate (n + 1) (.db v (operB bb BZero))
                        ++ [.db v (operB bb BZero)] from List.replicate_succ']
                    have hlt := lessBT_addBT_self_b4
                      (.trm (List.replicate (n + 1) (BP.db v (operB bb BZero))))
                      (.trm [.db v (operB bb BZero)]) (by simp [BZero])
                    simpa [addBT] using hlt
                | naturals =>
                    have hk : ∀ u : ℕ, domTag bb = .below u → ¬ (v ≤ (u : ℕ∞)) := by
                      intro u hu; rw [hdb] at hu; exact absurd hu (by simp)
                    have op : ∀ z : BT, operB (.trm [.db v bb]) z = Dprin v (operB bb z) := by
                      intro z
                      rw [show (BT.trm [BP.db v bb]) = Dprin v bb from rfl]
                      exact operB_case_iii_b4 hb (by rw [hdb]; simp) hk z
                    rw [op, op]
                    exact Dprin_lt_Dprin_b4 v (ih (btWeight bb) szbb bb otbb dfbb hdb rfl)
                | below u =>
                    by_cases hvu : v ≤ (u : ℕ∞)
                    · have op : ∀ z : BT, operB (.trm [.db v bb]) z
                          = Dprin v (operB bb (xseq bb (u : ℕ∞) (numNat z))) := by
                        intro z
                        rw [show (BT.trm [BP.db v bb]) = Dprin v bb from rfl]
                        exact operB_case_ii_b4 hb hdb hvu z
                      rw [op, op, numNat_numBT_b4, numNat_numBT_b4]
                      exact Dprin_lt_Dprin_b4 v (operB_mono_below_b4 bb _ _ u hdb
                        (y4_xseq_TBv bb u n) (y4_xseq_TBv bb u (n + 1))
                        (y4_xseq_lt bb u n otbb hdb))
                    · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at da
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < N := by
                rw [← hn]; simp [btWeight, bpListWeight]
              have htagtail : domTag (.trm (q :: qs)) = .naturals := by
                simpa [domTag, domTagList] using da
              have hrec := ih (btWeight (.trm (q :: qs))) htailn (.trm (q :: qs))
                (isOT_tail_b4 ot) (dfree_tail_b4 df) htagtail rfl
              have hadd := addBT_lt_right_bf (.trm [p]) _ _ hrec
              simpa [operB, bOperCore, addBT] using hadd

/-- Isabelle `y4_N_mono_le` (pss_scratch.thy:13034)。 -/
theorem y4_N_mono_le {a : BT} {m n : ℕ} (ot : isOT_BT a = true) (df : dfree_BT a = true)
    (da : domTag a = .naturals) (mn : m ≤ n) :
    leBT (operB a (numBT m)) (operB a (numBT n)) = true := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp mn
      subst hm; exact leBT_refl_b4 _
  | succ n ih =>
      by_cases hmn : m = n + 1
      · subst hmn; exact leBT_refl_b4 _
      · have hle : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne mn hmn)
        exact leBT_of_less_b4 (le_less_trans_b4 (ih hle) (y4_N_mono a n ot df da))

/-! ## 8. y4 ブロック (3) — 崩壊する共終性（case ([].4)(ii)）

Isabelle: `isabelle/layerC/pss_scratch.thy` 12661–12910。

**多項の場合の分解について**: Isabelle は `butlast`/`last` で末尾 principal へ
帰着させ、`y4_prefix_split` を使う。Lean の `bOperCore` は再帰が**先頭** principal を
剥がす形（`operB (p::q::ps) z = [p] +B operB (q::ps) z`）なので、こちらでは先頭剥がし＋
末尾への再帰で同じ帰着を行う（両者は同値。`y4_prefix_split` は原文忠実性のため
上で単体移植済み）。 -/

private theorem BZero_le_b4 (a : BT) : leBT BZero a = true := by
  by_cases h : a = BZero
  · subst h; exact leBT_refl_b4 _
  · exact leBT_of_less_b4 (BZero_lt_of_ne_b4 h)

private theorem lessBT_BZero_right_b4 (a : BT) : lessBT a BZero = false := by
  rcases a with ⟨as⟩
  simpa [lessBT, BZero] using lessBPList_nil_right_b4 as

private theorem lessBT_cons_single_b4 {r : BP} {rs : List BP} {p : BP}
    (h : lessBT (.trm (r :: rs)) (.trm [p]) = true) : lessBP r p = true := by
  have h' : (lessBP r p || (r == p && lessBPList rs [])) = true := by
    simpa [lessBT, lessBPList] using h
  rw [lessBPList_nil_right_b4 rs] at h'
  simpa using h'

private theorem lessBT_cons_of_head_b4 {r p : BP} (rs xs : List BP)
    (h : lessBP r p = true) : lessBT (.trm (r :: rs)) (.trm (p :: xs)) = true := by
  simp [lessBT, lessBPList, h]

private theorem lessBP_db_b4 {w1 w : ℕ∞} {y1 bb : BT}
    (h : lessBP (.db w1 y1) (.db w bb) = true) :
    w1 < w ∨ (w1 = w ∧ lessBT y1 bb = true) := by
  simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨eq_of_beq h1, h2⟩

private theorem lessBP_db_of_lt_b4 {w1 w : ℕ∞} {y1 bb : BT} (h : w1 < w) :
    lessBP (.db w1 y1) (.db w bb) = true := by simp [lessBP, h]

private theorem lessBP_db_of_body_b4 {w : ℕ∞} {y1 bb : BT} (h : lessBT y1 bb = true) :
    lessBP (.db w y1) (.db w bb) = true := by simp [lessBP, h]

private theorem GBT_head_body_b4 {u w1 : ℕ∞} {y1 : BT} {rs : List BP}
    (h : u ≤ w1) : y1 ∈ GBT u (.trm (.db w1 y1 :: rs)) := by
  simp [GBT, gatherBT, gatherBPList, gatherBP, h]

private theorem isOT_head_body_b4 {w1 : ℕ∞} {y1 : BT} {rs : List BP}
    (h : isOT_BT (.trm (.db w1 y1 :: rs)) = true) : isOT_BT y1 = true := by
  simp only [isOT_BT, isOT_BPList, isOT_BP, Bool.and_eq_true] at h
  tauto

private theorem isOT_head_G_b4 {w1 : ℕ∞} {y1 : BT} {rs : List BP}
    (h : isOT_BT (.trm (.db w1 y1 :: rs)) = true) :
    ∀ x ∈ GBT w1 y1, lessBT x y1 = true := by
  intro x hx
  have hall : (gatherBT w1 y1).all (fun t => lessBT t y1) = true := by
    simp only [isOT_BT, isOT_BPList, isOT_BP, Bool.and_eq_true] at h
    tauto
  exact (List.all_eq_true.mp hall) x (by simpa [GBT] using hx)

private theorem domTag_Dsucc_inv_b4 {w : ℕ∞} {u : ℕ}
    (h : domTag (Dprin w BZero) = .below u) : w = ((u + 1 : ℕ) : ℕ∞) := by
  by_cases hw0 : w = 0
  · subst hw0; simp [domTag, domTagList, domTagBP, Dprin, BZero] at h
  · by_cases hwtop : w = ⊤
    · subst hwtop; simp [domTag, domTagList, domTagBP, Dprin, BZero] at h
    · have h' : w.toNat - 1 = u := by
        simpa [domTag, domTagList, domTagBP, Dprin, BZero, hw0, hwtop] using h
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hwtop
      subst hk
      have hk0 : k ≠ 0 := by rintro rfl; exact hw0 (by simp)
      simp only [ENat.toNat_coe] at h'
      have : k = u + 1 := by omega
      rw [this]

/-- Isabelle `y4_inner` (pss_scratch.thy:12661)：塔のホスト `c₀` の下位文脈 `c'` に沿って、
`G_u`-escape が既に塔 `(xₙ)` で抑えられている `OT` 項 `y < c'` は `y ≤ c'[D_u xₙ]` を満たす。

`OT` の `G` 条件が不可欠な箇所（これが無いと `y = D₀(D₅0) < D₁0` が反例になる）。 -/
theorem y4_inner {c0 : BT} {u : ℕ} (ot0 : isOT_BT c0 = true) (dc0 : domTag c0 = .below u) :
    ∀ (c' y : BT), isOT_BT c' = true → domTag c' = .below u → isOT_BT y = true →
      lessBT y c' = true →
      (∀ x ∈ GBT (u : ℕ∞) y, ∃ n, leBT x (operB c0 (xseq c0 (u : ℕ∞) n)) = true) →
      (∃ n, leBT y (operB c' (xseq c0 (u : ℕ∞) n)) = true) := by
  intro c'
  generalize hn : btWeight c' = N
  induction N using Nat.strong_induction_on generalizing c' with
  | h N ih =>
      intro y otc dcc oty ylt GB
      rcases c' with ⟨cs⟩
      cases cs with
      | nil => simp [domTag, domTagList] at dcc
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨w, bb⟩
              by_cases hb : bb = BZero
              · subst bb
                have hw : w = ((u + 1 : ℕ) : ℕ∞) :=
                  domTag_Dsucc_inv_b4 (by simpa [Dprin] using dcc)
                subst hw
                have oper : ∀ z : BT,
                    operB (.trm [.db ((u + 1 : ℕ) : ℕ∞) BZero]) z = z := by
                  intro z
                  rw [show (BT.trm [BP.db ((u + 1 : ℕ) : ℕ∞) BZero])
                    = Dprin ((u + 1 : ℕ) : ℕ∞) BZero from rfl]
                  exact operB_Dsucc_b4 (by simp) (ENat.coe_ne_top (u + 1)) z
                rcases y with ⟨ys⟩
                cases ys with
                | nil => exact ⟨0, by rw [oper]; exact BZero_le_b4 _⟩
                | cons r rs =>
                    rcases r with ⟨w1, y1⟩
                    have hlt : lessBP (.db w1 y1) (.db ((u + 1 : ℕ) : ℕ∞) BZero) = true :=
                      lessBT_cons_single_b4 ylt
                    have hw1 : w1 < ((u + 1 : ℕ) : ℕ∞) := by
                      rcases lessBP_db_b4 hlt with h | ⟨_, h2⟩
                      · exact h
                      · exact absurd h2 (by simp [lessBT_BZero_right_b4])
                    have hw1le : w1 ≤ (u : ℕ∞) := by
                      rcases eq_or_ne w1 ⊤ with rfl | hne
                      · exact absurd hw1 (by simp)
                      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
                        subst hk
                        have hklt : k < u + 1 := by exact_mod_cast hw1
                        exact_mod_cast Nat.lt_succ_iff.mp hklt
                    by_cases hw1eq : w1 = (u : ℕ∞)
                    · subst hw1eq
                      obtain ⟨m, hm⟩ := GB y1 (GBT_head_body_b4 (le_refl _))
                      have clt := operB_mono_below_b4 c0 _ _ u dc0
                        (y4_xseq_TBv c0 u m) (y4_xseq_TBv c0 u (m + 1))
                        (y4_xseq_lt c0 u m ot0 dc0)
                      have lt : lessBT y1 (operB c0 (xseq c0 (u : ℕ∞) (m + 1))) = true :=
                        le_less_trans_b4 hm clt
                      refine ⟨m + 1 + 1, ?_⟩
                      rw [oper, xseq_succ_b4]
                      exact leBT_of_less_b4 (by
                        simpa [Dprin] using
                          lessBT_cons_of_head_b4 rs [] (lessBP_db_of_body_b4 lt))
                    · have hw1s : w1 < (u : ℕ∞) := lt_of_le_of_ne hw1le hw1eq
                      refine ⟨0, ?_⟩
                      rw [oper, xseq_zero_b4]
                      exact leBT_of_less_b4 (by
                        simpa [Dprin] using
                          lessBT_cons_of_head_b4 rs [] (lessBP_db_of_lt_b4 hw1s))
              · have hstruct : domTag bb = .below u ∧ (u : ℕ∞) < w := by
                  cases hdb : domTag bb with
                  | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at dcc
                  | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at dcc
                  | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at dcc
                  | below u' =>
                      by_cases hwu : w ≤ (u' : ℕ∞)
                      · simp [domTag, domTagList, domTagBP, hb, hdb, hwu] at dcc
                      · have hu' : u' = u := by
                          simpa [domTag, domTagList, domTagBP, hb, hdb, hwu] using dcc
                        subst hu'
                        exact ⟨rfl, lt_of_not_ge hwu⟩
                obtain ⟨dbb, wgt⟩ := hstruct
                have oper : ∀ z : BT, operB (.trm [.db w bb]) z = Dprin w (operB bb z) := by
                  intro z
                  rw [show (BT.trm [BP.db w bb]) = Dprin w bb from rfl]
                  refine operB_case_iii_b4 hb (by rw [dbb]; simp) ?_ z
                  intro u2 hu2
                  rw [dbb] at hu2
                  have hu2' : u = u2 := by simpa using hu2
                  subst hu2'
                  exact not_le.mpr wgt
                have otbb : isOT_BT bb = true :=
                  isOT_Dprin_body_b4 (by simpa [Dprin] using otc)
                have szbb : btWeight bb < N := by
                  rw [← hn]; simp [btWeight, bpListWeight, bpWeight]; omega
                rcases y with ⟨ys⟩
                cases ys with
                | nil => exact ⟨0, by rw [oper]; exact BZero_le_b4 _⟩
                | cons r rs =>
                    rcases r with ⟨w1, y1⟩
                    have hlt : lessBP (.db w1 y1) (.db w bb) = true :=
                      lessBT_cons_single_b4 ylt
                    rcases lessBP_db_b4 hlt with hws | ⟨hw1eq, y1lt⟩
                    · refine ⟨0, ?_⟩
                      rw [oper]
                      exact leBT_of_less_b4 (by
                        simpa [Dprin] using
                          lessBT_cons_of_head_b4 rs [] (lessBP_db_of_lt_b4 hws))
                    · subst hw1eq
                      have oty1 : isOT_BT y1 = true := isOT_head_body_b4 oty
                      have y1G : y1 ∈ GBT (u : ℕ∞) (.trm (.db w1 y1 :: rs)) :=
                        GBT_head_body_b4 (le_of_lt wgt)
                      have GB1 : ∀ x ∈ GBT (u : ℕ∞) y1,
                          ∃ n, leBT x (operB c0 (xseq c0 (u : ℕ∞) n)) = true :=
                        fun x hx => GB x (GBT_trans_b4 y1G hx)
                      obtain ⟨n, hnn⟩ :=
                        ih (btWeight bb) szbb bb rfl y1 otbb dbb oty1 y1lt GB1
                      have blt := operB_mono_below_b4 bb _ _ u dbb
                        (y4_xseq_TBv c0 u n) (y4_xseq_TBv c0 u (n + 1))
                        (y4_xseq_lt c0 u n ot0 dc0)
                      have y1lt2 : lessBT y1 (operB bb (xseq c0 (u : ℕ∞) (n + 1))) = true :=
                        le_less_trans_b4 hnn blt
                      refine ⟨n + 1, ?_⟩
                      rw [oper]
                      exact leBT_of_less_b4 (by
                        simpa [Dprin] using
                          lessBT_cons_of_head_b4 rs [] (lessBP_db_of_body_b4 y1lt2))
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < N := by
                rw [← hn]; simp [btWeight, bpListWeight]
              have htagtail : domTag (.trm (q :: qs)) = .below u := by
                simpa [domTag, domTagList] using dcc
              have ottail : isOT_BT (.trm (q :: qs)) = true := isOT_tail_b4 otc
              rcases y with ⟨ys⟩
              cases ys with
              | nil => exact ⟨0, BZero_le_b4 _⟩
              | cons r rs =>
                  have hstep : lessBP r p = true ∨
                      (r = p ∧ lessBT (.trm rs) (.trm (q :: qs)) = true) := by
                    have h' : (lessBP r p || (r == p && lessBPList rs (q :: qs))) = true := by
                      simpa [lessBT, lessBPList] using ylt
                    rcases Bool.or_eq_true_iff.mp h' with h'' | h''
                    · exact Or.inl h''
                    · rcases Bool.and_eq_true_iff.mp h'' with ⟨h1, h2⟩
                      exact Or.inr ⟨eq_of_beq h1, by simpa [lessBT] using h2⟩
                  rcases hstep with hlt | ⟨rp, hrec⟩
                  · refine ⟨0, ?_⟩
                    rcases hop : operB (.trm (q :: qs)) (xseq c0 (u : ℕ∞) 0) with ⟨xs2⟩
                    rw [operB_multi_b4, hop]
                    exact leBT_of_less_b4 (by
                      simpa [addBT] using lessBT_cons_of_head_b4 rs xs2 hlt)
                  · subst rp
                    have otrs : isOT_BT (.trm rs) = true := isOT_tail_b4 oty
                    have Gsub : GBT (u : ℕ∞) (.trm rs) ⊆ GBT (u : ℕ∞) (.trm (r :: rs)) := by
                      simpa using y4_GBT_suffix (u : ℕ∞) rs [r]
                    obtain ⟨n, hnn⟩ := ih (btWeight (.trm (q :: qs))) htailn
                      (.trm (q :: qs)) rfl (.trm rs) ottail htagtail otrs hrec
                      (fun x hx => GB x (Gsub hx))
                    refine ⟨n, ?_⟩
                    rw [operB_multi_b4]
                    simpa [addBT] using y4_leBT_addBT_mono_right (.trm [r]) hnn

/-! ### 外側の帰納 = ([].4)(ii) の残差、解消

Isabelle `y4_xseq_cof` (pss_scratch.thy:12883)。`OT` ホスト `c`（`dom c = T_u`）に対し、
`G_u`-escape が `c` 未満に留まる `OT` 項 `e < c` は塔で捕まる。`G` 仮定は `OT` の
principal `D_v e` がまさに供給するもの（`G_v e < e < c` と `v ≤ u` で `G_u ⊆ G_v`）。 -/

/-! Isabelle `wfj_G_OT_T`：`OT` 項の `G` 元はまた `OT`。 -/

mutual
  private theorem gatherBT_OT_mem_b4 (u : ℕ∞) (x : BT) :
      ∀ t : BT, isOT_BT t = true → x ∈ gatherBT u t → isOT_BT x = true
    | .trm ps, h, hx => by
        have hl : isOT_BPList ps = true := by
          simp only [isOT_BT, Bool.and_eq_true] at h; exact h.1
        exact gatherBPList_OT_mem_b4 u x ps hl (by simpa [gatherBT] using hx)

  private theorem gatherBP_OT_mem_b4 (u : ℕ∞) (x : BT) :
      ∀ p : BP, isOT_BP p = true → x ∈ gatherBP u p → isOT_BT x = true
    | .db v b, h, hx => by
        have hb : isOT_BT b = true := by
          simp only [isOT_BP, Bool.and_eq_true] at h; exact h.1
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hb
          · exact gatherBT_OT_mem_b4 u x b hb hx
        · simp [gatherBP, huv] at hx

  private theorem gatherBPList_OT_mem_b4 (u : ℕ∞) (x : BT) :
      ∀ ps : List BP, isOT_BPList ps = true → x ∈ gatherBPList u ps → isOT_BT x = true
    | [], _, hx => by simp [gatherBPList] at hx
    | p :: ps, h, hx => by
        simp only [isOT_BPList, Bool.and_eq_true] at h
        simp only [gatherBPList, List.mem_append] at hx
        rcases hx with hx | hx
        · exact gatherBP_OT_mem_b4 u x p h.1 hx
        · exact gatherBPList_OT_mem_b4 u x ps h.2 hx
end

private theorem GBT_OT_b4 {u : ℕ∞} {x t : BT} (hot : isOT_BT t = true)
    (hx : x ∈ GBT u t) : isOT_BT x = true :=
  gatherBT_OT_mem_b4 u x t hot (by simpa [GBT] using hx)

/-- Isabelle `y4_xseq_cof` (pss_scratch.thy:12883)。 -/
theorem y4_xseq_cof {c : BT} {u : ℕ} (ot : isOT_BT c = true) (dc : domTag c = .below u) :
    ∀ e : BT, isOT_BT e = true → lessBT e c = true →
      (∀ x ∈ GBT (u : ℕ∞) e, lessBT x c = true) →
      ∃ n, leBT e (operB c (xseq c (u : ℕ∞) n)) = true := by
  intro e
  generalize hn : btWeight e = N
  induction N using Nat.strong_induction_on generalizing e with
  | h N ih =>
      intro ote elt eG
      have GB : ∀ x ∈ GBT (u : ℕ∞) e,
          ∃ n, leBT x (operB c (xseq c (u : ℕ∞) n)) = true := by
        intro x xin
        have szx : btWeight x < N := by rw [← hn]; exact GBT_weight_lt_b4 xin
        exact ih (btWeight x) szx x rfl (GBT_OT_b4 ote xin) (eG x xin)
          (fun z hz => eG z (GBT_trans_b4 xin hz))
      exact y4_inner ot dc c e ot dc ote elt GB

/-! ## 9. y4 ブロック (6) — **Bachmann（共終性）性質**

Isabelle `y4_bachmann` (pss_scratch.thy:13261)：`OT`・`D_ω`-free な `a`, `b` に対し
`b < a ⟹ ∃z ∈ dom(a). b ≤ a[z]`。`btWeight a` の強帰納で `operB` の再帰を辿る:

* 多項: 先頭剥がし（Isabelle は `y4_prefix_split` で末尾へ帰着；上記 §8 の注参照）;
* `a = 1`: `b < 1` は `b = 0 = a[0]` を強制;
* `a = D_{m+1}0`（`dom = T_m`, `a[z] = z`）: witness は `b` 自身（`y4_TBv_of_head`）;
* ([].4)(i): 等号場合は数項ブロックが吸収（`y4_le_replicate`）;
* ([].4)(ii): `y4_xseq_cof` — 崩壊する共終性;
* ([].4)(iii): 本体への IH。等号場合は基本列添字の bump が吸収
  （`ℕ` 上は `y4_N_mono`、`T_m` 上は `y4_bump` ＋ 単調性）。 -/

private theorem le_of_lt_succ_enat_b4 {w : ℕ∞} {u : ℕ}
    (h : w < ((u + 1 : ℕ) : ℕ∞)) : w ≤ (u : ℕ∞) := by
  rcases eq_or_ne w ⊤ with rfl | hne
  · exact absurd h (by simp)
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    subst hk
    have hklt : k < u + 1 := by exact_mod_cast h
    exact_mod_cast Nat.lt_succ_iff.mp hklt

/-- Isabelle `y4_bachmann` (pss_scratch.thy:13261)。 -/
theorem y4_bachmann (a : BT) : ∀ b : BT,
    isOT_BT a = true → dfree_BT a = true → isOT_BT b = true → dfree_BT b = true →
    lessBT b a = true →
    ((domTag a = .zeroOnly ∨ domTag a = .naturals) →
        ∃ n, leBT b (operB a (numBT n)) = true) ∧
    (∀ m : ℕ, domTag a = .below m →
        ∃ z, z ∈ domB a ∧ isOT_BT z = true ∧ dfree_BT z = true ∧
          leBT b (operB a z) = true) := by
  generalize hn : btWeight a = N
  induction N using Nat.strong_induction_on generalizing a with
  | h N ih =>
      intro b ota dfa otb dfb hba
      rcases a with ⟨xs⟩
      cases xs with
      | nil =>
          rw [show (BT.trm [] : BT) = BZero from rfl, lessBT_BZero_right_b4 b] at hba
          exact absurd hba (by simp)
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, c⟩
              have otc : isOT_BT c = true := isOT_Dprin_body_b4 (by simpa [Dprin] using ota)
              have dfc : dfree_BT c = true := dfree_Dprin_body_b4 (by simpa [Dprin] using dfa)
              have vinf : v ≠ ⊤ := dfree_Dprin_idx_b4 (by simpa [Dprin] using dfa)
              have szc : btWeight c < N := by
                rw [← hn]; simp [btWeight, bpListWeight, bpWeight]; omega
              by_cases hc0 : c = BZero
              · subst c
                by_cases hv0 : v = 0
                · subst v
                  have da : domTag (.trm [BP.db 0 BZero]) = .zeroOnly := by
                    simp [domTag, domTagList, domTagBP, BZero]
                  have op : ∀ z : BT, operB (.trm [BP.db 0 BZero]) z = BZero := by
                    intro z; exact operB_D0_b4 z
                  have b0 : b = BZero := by
                    rcases b with ⟨bs⟩
                    cases bs with
                    | nil => rfl
                    | cons r rs =>
                        rcases r with ⟨w, e⟩
                        rcases lessBP_db_b4 (lessBT_cons_single_b4 hba) with h | ⟨_, h2⟩
                        · exact absurd h (by simp)
                        · exact absurd h2 (by simp [lessBT_BZero_right_b4])
                  refine ⟨fun _ => ⟨0, ?_⟩, fun m hm => ?_⟩
                  · rw [op, b0]; exact leBT_refl_b4 _
                  · rw [da] at hm; exact absurd hm (by simp)
                · have da : domTag (.trm [BP.db v BZero]) = .below (v.toNat - 1) := by
                    rw [show (BT.trm [BP.db v BZero]) = Dprin v BZero from rfl]
                    exact domTag_Dsucc_b4 hv0 vinf
                  have op : ∀ z : BT, operB (.trm [BP.db v BZero]) z = z := by
                    intro z
                    rw [show (BT.trm [BP.db v BZero]) = Dprin v BZero from rfl]
                    exact operB_Dsucc_b4 hv0 vinf z
                  refine ⟨fun hDA => ?_, fun m hm => ?_⟩
                  · rw [da] at hDA; rcases hDA with h | h <;> exact absurd h (by simp)
                  · have hv : v = ((m + 1 : ℕ) : ℕ∞) :=
                      domTag_Dsucc_inv_b4 (by simpa [Dprin] using hm)
                    have btv : b ∈ TBv (m : ℕ∞) := by
                      rcases b with ⟨bs⟩
                      cases bs with
                      | nil => exact BZero_mem_TBv_b4 _
                      | cons r rs =>
                          rcases r with ⟨w, e⟩
                          rw [hv] at hba
                          have hlt := lessBT_cons_single_b4 hba
                          have hw : w < ((m + 1 : ℕ) : ℕ∞) := by
                            rcases lessBP_db_b4 hlt with h | ⟨_, h2⟩
                            · exact h
                            · exact absurd h2 (by simp [lessBT_BZero_right_b4])
                          exact y4_TBv_of_head otb (le_of_lt_succ_enat_b4 hw)
                    refine ⟨b, ?_, otb, dfb, ?_⟩
                    · rw [domB, hm]; exact btv
                    · rw [op]; exact leBT_refl_b4 _
              · have HS : (∀ bs : List BP, b = .trm bs → bs = [] ∨
                    ∃ w e rs, bs = .db w e :: rs ∧
                      (w < v ∨ (w = v ∧ lessBT e c = true))) := by
                  intro bs hbs
                  cases bs with
                  | nil => exact Or.inl rfl
                  | cons r rs =>
                      rcases r with ⟨w, e⟩
                      subst hbs
                      exact Or.inr ⟨w, e, rs, rfl,
                        lessBP_db_b4 (lessBT_cons_single_b4 hba)⟩
                by_cases hdz : domTag c = .zeroOnly
                · -- ([].4)(i)
                  have da : domTag (.trm [BP.db v c]) = .naturals := by
                    rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl]
                    exact domTag_case_i_b4 hc0 hdz
                  have opn : ∀ n : ℕ, operB (.trm [BP.db v c]) (numBT n)
                      = .trm (List.replicate (n + 1) (BP.db v (operB c BZero))) := by
                    intro n
                    rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl,
                      operB_case_i_b4 hc0 hdz, numNat_numBT_b4]
                    exact multBT_single_b4 _ _
                  refine ⟨fun _ => ?_, fun m hm => ?_⟩
                  · rcases b with ⟨bs⟩
                    rcases HS bs rfl with rfl | ⟨w, e, rs', hbs, hdisj⟩
                    · exact ⟨0, by rw [opn]; exact BZero_le_b4 _⟩
                    · subst hbs
                      rcases hdisj with hwv | ⟨hwv, helt⟩
                      · refine ⟨0, ?_⟩
                        rw [opn]
                        exact leBT_of_less_b4 (by
                          simpa [List.replicate] using
                            lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_lt_b4 hwv))
                      · subst hwv
                        have ote : isOT_BT e = true := isOT_head_body_b4 otb
                        have dfe : dfree_BT e = true := by
                          have := dfb
                          simp only [dfree_BT, dfree_BPList, dfree_BP,
                            Bool.and_eq_true] at this
                          tauto
                        obtain ⟨n', hn'⟩ := (ih (btWeight c) szc c rfl e otc dfc ote dfe
                          helt).1 (Or.inl hdz)
                        have ee : leBT e (operB c BZero) = true := by
                          rwa [y4_operB_domzero_const hdz (numBT n')] at hn'
                        by_cases heq : e = operB c BZero
                        · have dsc : descP (BP.db w e :: rs') = true :=
                            (Bool.and_eq_true_iff.mp (by simpa [isOT_BT] using otb)).2
                          have allle : ∀ x ∈ rs',
                              leBT (.trm [x]) (.trm [BP.db w (operB c BZero)]) = true := by
                            intro x hx
                            have := y4_descP_all_le_hd dsc (List.mem_cons_of_mem _ hx)
                            rwa [heq] at this
                          refine ⟨rs'.length, ?_⟩
                          rw [opn, List.replicate_succ, heq]
                          have := y4_leBT_addBT_mono_right
                            (.trm [BP.db w (operB c BZero)]) (y4_le_replicate allle)
                          simpa [addBT] using this
                        · have hlt : lessBT e (operB c BZero) = true :=
                            less_of_leBT_ne_b4 ee heq
                          refine ⟨0, ?_⟩
                          rw [opn]
                          exact leBT_of_less_b4 (by
                            simpa [List.replicate] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_body_b4 hlt))
                  · rw [da] at hm; exact absurd hm (by simp)
                · by_cases hkii : ∃ u' : ℕ, domTag c = .below u' ∧ v ≤ (u' : ℕ∞)
                  · -- ([].4)(ii)
                    obtain ⟨u', du, hvu⟩ := hkii
                    have da : domTag (.trm [BP.db v c]) = .naturals := by
                      rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl]
                      exact domTag_case_ii_b4 hc0 du hvu
                    have opn : ∀ n : ℕ, operB (.trm [BP.db v c]) (numBT n)
                        = Dprin v (operB c (xseq c (u' : ℕ∞) n)) := by
                      intro n
                      rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl,
                        operB_case_ii_b4 hc0 du hvu, numNat_numBT_b4]
                    refine ⟨fun _ => ?_, fun m hm => ?_⟩
                    · rcases b with ⟨bs⟩
                      rcases HS bs rfl with rfl | ⟨w, e, rs', hbs, hdisj⟩
                      · exact ⟨0, by rw [opn]; exact BZero_le_b4 _⟩
                      · subst hbs
                        rcases hdisj with hwv | ⟨hwv, helt⟩
                        · refine ⟨0, ?_⟩
                          rw [opn]
                          exact leBT_of_less_b4 (by
                            simpa [Dprin] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_lt_b4 hwv))
                        · subst hwv
                          have ote : isOT_BT e = true := isOT_head_body_b4 otb
                          have Gv : ∀ x ∈ GBT w e, lessBT x e = true := isOT_head_G_b4 otb
                          have G : ∀ x ∈ GBT (u' : ℕ∞) e, lessBT x c = true := by
                            intro x hx
                            exact lessBT_linear_trans _ _ _
                              (Gv x (GBT_antitone_b4 hvu e hx)) helt
                          obtain ⟨n, hnn⟩ := y4_xseq_cof otc du e ote helt G
                          have clt := operB_mono_below_b4 c _ _ u' du
                            (y4_xseq_TBv c u' n) (y4_xseq_TBv c u' (n + 1))
                            (y4_xseq_lt c u' n otc du)
                          have lt : lessBT e (operB c (xseq c (u' : ℕ∞) (n + 1))) = true :=
                            le_less_trans_b4 hnn clt
                          refine ⟨n + 1, ?_⟩
                          rw [opn]
                          exact leBT_of_less_b4 (by
                            simpa [Dprin] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_body_b4 lt))
                    · rw [da] at hm; exact absurd hm (by simp)
                  · -- ([].4)(iii)
                    have hk : ∀ u2 : ℕ, domTag c = .below u2 → ¬ (v ≤ (u2 : ℕ∞)) := by
                      intro u2 hu2 hle; exact hkii ⟨u2, hu2, hle⟩
                    have da : domTag (.trm [BP.db v c]) = domTag c := by
                      rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl]
                      exact domTag_case_iii_b4 hc0 hdz hk
                    have op : ∀ z : BT, operB (.trm [BP.db v c]) z = Dprin v (operB c z) := by
                      intro z
                      rw [show (BT.trm [BP.db v c]) = Dprin v c from rfl]
                      exact operB_case_iii_b4 hc0 hdz hk z
                    refine ⟨fun hDA => ?_, fun m hm => ?_⟩
                    · have dcN : domTag c = .naturals := by
                        rw [da] at hDA
                        rcases hDA with h | h
                        · exact absurd h hdz
                        · exact h
                      rcases b with ⟨bs⟩
                      rcases HS bs rfl with rfl | ⟨w, e, rs', hbs, hdisj⟩
                      · exact ⟨0, by rw [op]; exact BZero_le_b4 _⟩
                      · subst hbs
                        rcases hdisj with hwv | ⟨hwv, helt⟩
                        · refine ⟨0, ?_⟩
                          rw [op]
                          exact leBT_of_less_b4 (by
                            simpa [Dprin] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_lt_b4 hwv))
                        · subst hwv
                          have ote : isOT_BT e = true := isOT_head_body_b4 otb
                          have dfe : dfree_BT e = true := by
                            have := dfb
                            simp only [dfree_BT, dfree_BPList, dfree_BP,
                              Bool.and_eq_true] at this
                            tauto
                          obtain ⟨n, hnn⟩ := (ih (btWeight c) szc c rfl e otc dfc ote dfe
                            helt).1 (Or.inr dcN)
                          have lt : lessBT e (operB c (numBT (n + 1))) = true :=
                            le_less_trans_b4 hnn (y4_N_mono c n otc dfc dcN)
                          refine ⟨n + 1, ?_⟩
                          rw [op]
                          exact leBT_of_less_b4 (by
                            simpa [Dprin] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_body_b4 lt))
                    · have dcm : domTag c = .below m := by rw [← da]; exact hm
                      rcases b with ⟨bs⟩
                      rcases HS bs rfl with rfl | ⟨w, e, rs', hbs, hdisj⟩
                      · exact ⟨BZero, by rw [domB, hm]; exact BZero_mem_TBv_b4 _,
                          by simp [isOT_BT, isOT_BPList, descP, BZero],
                          by simp [dfree_BT, dfree_BPList, BZero],
                          by rw [op]; exact BZero_le_b4 _⟩
                      · subst hbs
                        rcases hdisj with hwv | ⟨hwv, helt⟩
                        · refine ⟨BZero, by rw [domB, hm]; exact BZero_mem_TBv_b4 _,
                            by simp [isOT_BT, isOT_BPList, descP, BZero],
                            by simp [dfree_BT, dfree_BPList, BZero], ?_⟩
                          rw [op]
                          exact leBT_of_less_b4 (by
                            simpa [Dprin] using
                              lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_lt_b4 hwv))
                        · subst hwv
                          have ote : isOT_BT e = true := isOT_head_body_b4 otb
                          have dfe : dfree_BT e = true := by
                            have := dfb
                            simp only [dfree_BT, dfree_BPList, dfree_BP,
                              Bool.and_eq_true] at this
                            tauto
                          obtain ⟨z, zin, otz, dfz, lez⟩ :=
                            (ih (btWeight c) szc c rfl e otc dfc ote dfe helt).2 m dcm
                          have ztv : z ∈ TBv (m : ℕ∞) := by
                            rw [domB, dcm] at zin; exact zin
                          obtain ⟨otz', dfz', ztv', zlt⟩ := y4_bump otz dfz ztv
                          have hmono := operB_mono_below_b4 c z
                            (addBT z (Dprin 0 BZero)) m dcm ztv ztv' zlt
                          have lt : lessBT e (operB c (addBT z (Dprin 0 BZero))) = true :=
                            le_less_trans_b4 lez hmono
                          refine ⟨addBT z (Dprin 0 BZero), ?_, otz', dfz', ?_⟩
                          · rw [domB, hm]; exact ztv'
                          · rw [op]
                            exact leBT_of_less_b4 (by
                              simpa [Dprin] using
                                lessBT_cons_of_head_b4 rs' [] (lessBP_db_of_body_b4 lt))
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < N := by
                rw [← hn]; simp [btWeight, bpListWeight]
              have dtail : domTag (.trm (q :: qs)) = domTag (.trm (p :: q :: qs)) :=
                (domTag_cons_cons_b4 p q qs).symm
              have ottail : isOT_BT (.trm (q :: qs)) = true := isOT_tail_b4 ota
              have dftail : dfree_BT (.trm (q :: qs)) = true := dfree_tail_b4 dfa
              rcases b with ⟨bs⟩
              cases bs with
              | nil =>
                  exact ⟨fun _ => ⟨0, BZero_le_b4 _⟩, fun m hm =>
                    ⟨BZero, by rw [domB, hm]; exact BZero_mem_TBv_b4 _,
                      by simp [isOT_BT, isOT_BPList, descP, BZero],
                      by simp [dfree_BT, dfree_BPList, BZero], BZero_le_b4 _⟩⟩
              | cons r rs =>
                  have hstep : lessBP r p = true ∨
                      (r = p ∧ lessBT (.trm rs) (.trm (q :: qs)) = true) := by
                    have h' : (lessBP r p || (r == p && lessBPList rs (q :: qs))) = true := by
                      simpa [lessBT, lessBPList] using hba
                    rcases Bool.or_eq_true_iff.mp h' with h'' | h''
                    · exact Or.inl h''
                    · rcases Bool.and_eq_true_iff.mp h'' with ⟨h1, h2⟩
                      exact Or.inr ⟨eq_of_beq h1, by simpa [lessBT] using h2⟩
                  rcases hstep with hlt | ⟨rp, hrec⟩
                  · have any : ∀ z : BT,
                        leBT (.trm (r :: rs)) (operB (.trm (p :: q :: qs)) z) = true := by
                      intro z
                      rcases hop : operB (.trm (q :: qs)) z with ⟨xs2⟩
                      rw [operB_multi_b4, hop]
                      exact leBT_of_less_b4 (by
                        simpa [addBT] using lessBT_cons_of_head_b4 rs xs2 hlt)
                    exact ⟨fun _ => ⟨0, any _⟩, fun m hm =>
                      ⟨BZero, by rw [domB, hm]; exact BZero_mem_TBv_b4 _,
                        by simp [isOT_BT, isOT_BPList, descP, BZero],
                        by simp [dfree_BT, dfree_BPList, BZero], any _⟩⟩
                  · subst rp
                    have otrs : isOT_BT (.trm rs) = true := isOT_tail_b4 otb
                    have dfrs : dfree_BT (.trm rs) = true := dfree_tail_b4 dfb
                    have IH := ih (btWeight (.trm (q :: qs))) htailn (.trm (q :: qs)) rfl
                      (.trm rs) ottail dftail otrs dfrs hrec
                    refine ⟨fun hDA => ?_, fun m hm => ?_⟩
                    · obtain ⟨n, hnn⟩ := IH.1 (by rw [dtail]; exact hDA)
                      refine ⟨n, ?_⟩
                      rw [operB_multi_b4]
                      simpa [addBT] using y4_leBT_addBT_mono_right (.trm [r]) hnn
                    · obtain ⟨z, zin, otz, dfz, lez⟩ := IH.2 m (by rw [dtail]; exact hm)
                      refine ⟨z, ?_, otz, dfz, ?_⟩
                      · rw [domB, hm]
                        rw [domB, dtail, hm] at zin
                        exact zin
                      · rw [operB_multi_b4]
                        simpa [addBT] using y4_leBT_addBT_mono_right (.trm [r]) lez

/-- `y4_bachmann` の Isabelle 逐語形（`domB` の**集合**表示）。上の tag 形との橋は
`domB_zero_iff_b4` / `domB_nat_iff_b4` / `domB_below_iff_b4`（`BDom.toSet` の単射性）。
Isabelle: `y4_bachmann` (pss_scratch.thy:13261) の文面そのもの。 -/
theorem y4_bachmann_domB (a b : BT)
    (ota : isOT_BT a = true) (dfa : dfree_BT a = true)
    (otb : isOT_BT b = true) (dfb : dfree_BT b = true) (hba : lessBT b a = true) :
    ((domB a = {BZero} ∨ domB a = NatSet) → ∃ n, leBT b (operB a (numBT n)) = true) ∧
    (∀ m : ℕ, domB a = TBv (m : ℕ∞) →
        ∃ z, z ∈ domB a ∧ isOT_BT z = true ∧ dfree_BT z = true ∧
          leBT b (operB a z) = true) := by
  obtain ⟨c1, c2⟩ := y4_bachmann a b ota dfa otb dfb hba
  refine ⟨fun hDA => c1 ?_, fun m hm => c2 m ((domB_below_iff_b4 a m).mp hm)⟩
  rcases hDA with h | h
  · exact Or.inl ((domB_zero_iff_b4 a).mp h)
  · exact Or.inr ((domB_nat_iff_b4 a).mp h)

#print axioms y4_xseq_Dpt
#print axioms y4_xseq_TBv
#print axioms y4_xseq_lt
#print axioms y4_xseq_mono
#print axioms y4_xseq_le_mono
#print axioms y4_leBT_addBT_self
#print axioms y4_leBT_addBT_mono_right
#print axioms y4_prefix_split
#print axioms y4_descP_suffix
#print axioms y4_OT_suffix
#print axioms y4_GBT_suffix
#print axioms y4_dfree_suffix
#print axioms y4_descP_all_le_hd
#print axioms y4_TBv_of_head
#print axioms y4_leBT_min
#print axioms y4_bump
#print axioms y4_operB_domzero_const
#print axioms y4_le_replicate
#print axioms y4_N_mono
#print axioms y4_N_mono_le
#print axioms y4_inner
#print axioms y4_xseq_cof
#print axioms y4_bachmann
#print axioms y4_bachmann_domB

end PSS
