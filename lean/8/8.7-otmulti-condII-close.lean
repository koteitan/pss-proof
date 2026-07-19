import «8».«8.7-otmulti-narrow»
import «8».«8.7-fseq-descend-props2»
import «8».«8.2-condIIIV-close»
import «8».«8.3-condII-Boundary-close»

/-!
# §8.7 OT 柱 — 条件 (II) 脚 `OTmulti_interior_condII_on` の無条件クローズ

- 原文: `tmp/content.md` 6122（§8.7）。`«8».«8.7-otmulti-narrow»` は露出 `Prop`
  `OTmulti_interior_intCond_nc1`（複項 host の末尾 mono 成分の内部 OT ステップ＋
  `Trans L` 以下の順序）を、条件 (III)/(IV)/(V) を無条件供給で落として
  **条件 (II) だけ**の narrower Prop `OTmulti_interior_condII_on`
  （`8.7-otmulti-narrow`:137）に還元済み。本ファイルはその最後の脚を**無条件**に閉じる。
  訂正: なし。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。

## 攻め筋（Isabelle `opx_OTmulti` の condII 枝、`layerB/pss_wip.thy`:115556）

末尾 mono 成分 `L` が条件 (II)（`entry L 1 lastIdx = 0` かつ `¬ adm L lastParent`）の
とき、基本列翻訳 `Trans (oper L m)` が `OT_B` に留まり、かつ `Trans L` 以下であること。

* **等式**: `CondII_masterCF` は今や無条件（`condII_masterCF_of_condIIIV`
  ＋ `condIIIVterminalSlice_holds`、`8.2-condIIIV-close`＋`8.3-condII-Boundary-close`）
  ゆえ、その交換脚 `FseqDesc_exchII`（`8.7-fseq-descend-props2`:101 の
  `FseqDesc_exchII_of_CondII`）が **等式** `∃ k, Trans (oper L m) = operB (Trans L) (numBT k)`
  を与える（要 `1 < Lng L - 1`）。
* **OT 所属**: `OT_B` は `operB _ (numBT _)` で閉じる
  （`OT_B_operB_numBT_oc`＝`8.7-otmulti-notcondI`:85 private twin の複製）。
* **順序**: `mono` から `zeroT L = false`（`1 < Lng L`）ゆえ `Trans L ≠ 0_B`
  （`Trans_preserves_zeroT`）。[Buc1] Lemma 3.2(a)（`buchholz_fseq_lt`:
  `operB (Trans L) (numBT k) <_B Trans L`）と等式を連結して `leBT`。

## `1 < Lng L = 2` の隅は**空虚**（数値検証済み）

narrower Prop は `1 < Lng L` しか与えないが `FseqDesc_exchII` は `1 < Lng L - 1`
（`Lng L ≥ 3`）を課す。ギャップは `Lng L = 2`。**この隅では条件 (II) が偽**なので空虚:
`Lng L = 2` では `lastParent L = parent L 0 1 = 0`（親候補は `nextrel0` の `j0 < j1 = 1`
条項ゆえ `0` のみ、`parent_row0_one_zero_oc`）、`adm L 0 = true`（無条件、`adm_zero`）、
よって `transCondII L = (…) && !adm L 0 = (…) && false = false`。仮定 `transCondII L = true`
と矛盾（`python/trans_model.py` で `Lng = 2` の全 host に対し condII が 0 件を確認）。

- 依存（ビルド済みのみ import）: `«8».«8.7-otmulti-narrow»`
  （`OTmulti_interior_condII_on` の def、透過的に `OTmulti_interior_intCond_nc1`・
  `FseqDesc_exchII`・`buchholz_fseq_lt`・`Trans_preserves_zeroT`・`STPS_RTPS`・
  `RTPS_TPS`・`adm_zero`・`buchholz_fseq_closed`）、`«8».«8.7-fseq-descend-props2»`
  （`FseqDesc_exchII_of_CondII`）、`«8».«8.2-condIIIV-close»`
  （`condIIIVterminalSlice_holds`）、`«8».«8.3-condII-Boundary-close»`
  （`condII_masterCF_of_condIIIV`）。
- private helper suffix: `_oc`。
-/

namespace PSS

/-! ## 1. `OT_B` の `operB _ (numBT _)` 閉性（`8.7-otmulti-notcondI` private twin の複製） -/

/-- `0_B ∈ OT_B`。 -/
private theorem BZero_OT_B_oc : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- `operB 0_B z = 0_B`。Isabelle `b1x_operB_zero`。 -/
private theorem operB_BZero_oc (z : BT) : operB BZero z = BZero := by
  simp [operB, BZero, bOperCore]

/-- Isabelle `e4x_OT_B_operB_numBT` (`layerB/pss_wip.thy`:61390): 零脚を
`operB_BZero_oc` で埋めて `buchholz_fseq_closed` を無条件化。 -/
private theorem OT_B_operB_numBT_oc {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz, operB_BZero_oc]; exact BZero_OT_B_oc
  · exact buchholz_fseq_closed a n ha hz

/-! ## 2. `Lng L = 2` の隅の空虚性 -/

/-- 行 0 における `1` の親は（存在するとしても）常に `0`。`nextrel0` の `j0 < j1`
条項ゆえ親候補は `0` のみで、`headD` が空でも `0` を返す。`hasParent` 不要
（`parent_one_zero_fd` は `hasParent` を要求するので使えない）。 -/
private theorem parent_row0_one_zero_oc (M : PS) : parent M 0 1 = 0 := by
  have hcand : ∀ a, a ∈ parents M 0 1 → a = 0 := by
    intro a hmem
    have hmem' : a < Lng M ∧ nextR M 0 a 1 = true := by
      simpa [parents, List.mem_filter] using hmem
    have hnext := hmem'.2
    rw [nextR, if_pos rfl] at hnext
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnext
    have ha1 : a < 1 := hnext.1.1.2
    omega
  unfold parent
  cases h : parents M 0 1 with
  | nil => rfl
  | cons a as =>
      have ha0 : a = 0 := hcand a (by rw [h]; simp)
      simp [List.headD, ha0]

/-! ## 3. 主結果 — 条件 (II) 脚の無条件クローズ -/

/-- **`OTmulti_interior_condII_on` を無条件に閉じる**。等式 `FseqDesc_exchII`
（`CondII_masterCF` 無条件）＋ `OT_B` の `operB` 閉性＋ [Buc1] Lemma 3.2(a) を
`Lng L ≥ 3` の場で合流させ、`Lng L = 2` の隅は条件 (II) の偽性で空虚化する。 -/
theorem otMultiInteriorCondII_holds : OTmulti_interior_condII_on := by
  intro L m hLST hLmono hLgt hm hLpred hTL hcond
  have hLR : RTPS L := STPS_RTPS L hLST
  have hLT : TPS L := RTPS_TPS L hLR
  -- `Trans L ≠ 0_B`（mono ゆえ非零項、[Buc1] Lemma 3.2(a) の前提）
  have hnotzT : zeroT L = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  have hTne : Trans L ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT L hLT).2 h
    rw [hnotzT] at hz
    exact Bool.noConfusion hz
  -- ガード: `1 < Lng L - 1`（`Lng L = 2` の隅を条件 (II) の偽性で排除）
  have hj1gt : 1 < Lng L - 1 := by
    by_contra hcon
    have hL2 : Lng L = 2 := by omega
    have hlp : lastParent L = 0 := by
      unfold lastParent lastIdx
      rw [hL2]
      exact parent_row0_one_zero_oc L
    have hcII_false : transCondII L = false := by
      unfold transCondII
      rw [hlp, adm_zero L]
      simp
    rw [hcond] at hcII_false
    exact Bool.noConfusion hcII_false
  -- `Lng L ≥ 3`: 交換等式 → 両連言
  have hCF : CondII_masterCF := condII_masterCF_of_condIIIV condIIIVterminalSlice_holds
  have hexch : FseqDesc_exchII := FseqDesc_exchII_of_CondII hCF
  obtain ⟨k, hke⟩ := hexch L m hLST hLmono hj1gt hcond hm
  refine ⟨?_, ?_⟩
  · -- OT 所属
    rw [hke]
    exact OT_B_operB_numBT_oc hTL k
  · -- 順序
    rw [hke]
    have hlt : lessBT (operB (Trans L) (numBT k)) (Trans L) = true :=
      buchholz_fseq_lt (Trans L) k hTL hTne
    simp [leBT, hlt]

#print axioms otMultiInteriorCondII_holds

end PSS
