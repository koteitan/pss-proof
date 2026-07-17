import «7».«7.1-buchholz-fseq-lt»
import «7».«7.1-buchholz-fseq-closed»
import PSS.Buchholz

/-!
# §8.7 補題（順序数項の末尾項の零化可能性）

- 原文: `tmp/content.md` 5971（§8.7）。逐語形は `p_8_7_OT_tail_annihilable`
  (isabelle/pss_paper.thy:2284)。
- Isabelle: 移植元は `y3t_toplevel_OT_tail_annihilate`
  (isabelle/layerC/pss_scratch.thy:19355)。これは layerB の
  `m_8_7_toplevel_OT_tail_annihilate` (isabelle/layerB/pss_wip.thy:27288) を
  sorry 付き引用 `buc1_2_2_OT_B_wf` から解放した版で、`(OT_B, <)` の整礎性
  `y4_buc1_2_2_OT_B_wf` (同 layerC:13700) を帰納関係に使う。
- 訂正: A26（layerB/pss_wip.thy:26788）は **撤回済み**（A23 の operB 誤読に
  由来する A25 系の産物。`8.6-trailing-principal-annihilable` の冒頭注記と同じ）。
  従って原文の主張は真であり、ここでは Isabelle と同じ **top-level 値レベル形**
  （末尾 principal `D_u t'` を前置 `q` の上で `[0]` 反復により `D_u 0` へ落とす）
  を移植する。scb 形（`p_8_7_OT_tail_annihilable` 逐語形）は Isabelle 側も
  機械化していないため対象外。
- 依存（ビルド済みのみ import）: `PSS.Buchholz`（`BT`/`OT_B`/`lessBT`/`operB`/
  `bOperCore`/`domTag`/`domB`/`Dprin`/`addBT`/`BZero`/`numBT`/`multBT`/`TBv`/
  `NatSet`）、`7.1-buchholz-fseq-lt`（`buchholz_fseq_descent` ＝ [Buc1] 3.2(a)）、
  `7.1-buchholz-fseq-closed`（`buchholz_fseq_closed_general` ＝ [Buc1] 3.3）。
  ※ `7.1-buchholz-wf-Buc2body` は **未ビルド**なので import しない
  （`([].5)` 分配則は本ファイル内で `bOperCore_list_snoc_ota` として再証明した）。
- 状態: ✅ green（sorry 0）。名前付き仮定は **`OT_B_wf` の 1 つのみ**
  （Isabelle の `wf {(a,b). a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b}`
  ＝ `y4_buc1_2_2_OT_B_wf`。Lean 側の [Buc1] 2.2 キャンペーン
  `7.1-buchholz-wf-W` / `7.1-buchholz-wf-bachmann` は土台のみ着地済で
  頂点定理が未着地のため、仮定として括り出す）。

**Isabelle より強い点**: layerB / layerC の版は 1 ステップ降下 `step`
（`operB (q +_B D_u r) [0] = q +_B D_u r'`、`r' ∈ OT_B`、`r' < r`）を
**仮定に取る**（layerB の注記は「これを一般に落とすには operB の OT_B 上の
全域性＝[Buc1] 3.2 が要る」と述べている）。Lean では `operB` は
`bOperCore` の整礎再帰で **定義上全域** なので、この `step` は
`operB_Dprin_step_ota` として **無条件に証明できる**。よって公開定理
`toplevel_OT_tail_annihilate` は `step` を持たない。忠実な engine 形は
`toplevel_OT_tail_annihilate_of_step` として併置する。
-/

namespace PSS

/-! ## 0. 名前付き仮定 — `(OT_B, <)` の整礎性（[Buc1] 補題 2.2）

Isabelle: `y4_buc1_2_2_OT_B_wf : wf {(a, b). a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b}`
(isabelle/layerC/pss_scratch.thy:13700)。Isabelle の `(x,y) ∈ r` は「`x` が小さい」
なので、Lean の `WellFounded r` の引数順（第 1 引数が小さい）と一致する。 -/

/-- [Buc1] 補題 2.2 ＝ Isabelle `y4_buc1_2_2_OT_B_wf`。 -/
def OT_B_wf : Prop :=
  WellFounded (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true)

/-! ## 1. `([].5)` 分配則 — 末尾 principal への `operB` の局所化 -/

private theorem zero_addBT_ota (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩
  rfl

/-- `bOperCore` は principal リストの **末尾** にだけ効く。 -/
private theorem bOperCore_list_snoc_ota (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      exact (zero_addBT_ota _).symm
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih]
          rcases (bOperCore (.princ p z)) with ⟨cs⟩
          simp [addBT]

/-- `operB (D_v r) z` を `bOperCore` の `.princ` 節まで開く。
`bOperCore` は整礎再帰なので `rfl` では潰れず、`bOperCore.eq_def` が要る。 -/
private theorem operB_Dprin_eq_princ_ota (v : ℕ∞) (r z : BT) :
    operB (Dprin v r) z = bOperCore (.princ (.db v r) z) := by
  show bOperCore (.term (.trm [.db v r]) z) = bOperCore (.princ (.db v r) z)
  conv_lhs => rw [bOperCore.eq_def]
  show bOperCore (.list [.db v r] z) = bOperCore (.princ (.db v r) z)
  conv_lhs => rw [bOperCore.eq_def]

/-- Isabelle `operB_dist_trailing_single` / `bwo_addBT_operB` に対応する
`([].5)` 分配則（末尾が principal `D_v r` の形なので `≠ 0_B` 条件は不要）。 -/
private theorem operB_addBT_Dprin_ota (q : BT) (v : ℕ∞) (r z : BT) :
    operB (addBT q (Dprin v r)) z = addBT q (operB (Dprin v r) z) := by
  rcases q with ⟨qs⟩
  rw [operB_Dprin_eq_princ_ota]
  show bOperCore (.term (.trm (qs ++ [.db v r])) z) =
    addBT (.trm qs) (bOperCore (.princ (.db v r) z))
  conv_lhs => rw [bOperCore.eq_def]
  show bOperCore (.list (qs ++ [.db v r]) z) =
    addBT (.trm qs) (bOperCore (.princ (.db v r) z))
  exact bOperCore_list_snoc_ota qs (.db v r) z

/-! ## 2. `[0]` の 1 ステップは末尾 principal の**本体**を降下させる

これが Isabelle 版が仮定に取っていた `step`。`operB` が Lean では全域関数
なので、`bOperCore` の `.princ` 節を `domTag r` で場合分けするだけで落ちる。 -/

private theorem numNat_numBT_zero_ota : numNat (numBT 0) = 0 := rfl

/-- `x_0 = D_w 0`（訂正 A23 後の補助列の基点）。 -/
private theorem bOperCore_xseq_zero_ota (b : BT) (v : ℕ∞) :
    bOperCore (.xseq b v 0) = Dprin v BZero := by
  conv_lhs => rw [bOperCore.eq_def]

private theorem isOT_Dprin_zero_ota (w : ℕ) :
    isOT_BT (Dprin (w : ℕ∞) BZero) = true := by
  simp [Dprin, BZero, isOT_BT, isOT_BPList, isOT_BP, isOT_BPList,
    descP, gatherBT, gatherBPList]

private theorem dfree_Dprin_zero_ota (w : ℕ) :
    dfree_BT (Dprin (w : ℕ∞) BZero) = true := by
  simp [Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP, ENat.coe_ne_top]

private theorem Dprin_zero_mem_TBv_ota (w : ℕ) :
    Dprin (w : ℕ∞) BZero ∈ TBv (w : ℕ∞) := by
  simp [Dprin, BZero, TBv]

private theorem isOT_numBT_zero_ota : isOT_BT (numBT 0) = true := rfl

private theorem dfree_numBT_zero_ota : dfree_BT (numBT 0) = true := rfl

private theorem numBT_zero_mem_NatSet_ota : numBT 0 ∈ NatSet := ⟨0, rfl⟩

/-- 引数 `z` が [Buc1] 3.2(a)/3.3 の受理域に入っていれば、`D_u (r[z])` の形の
1 ステップは `step` の結論をそのまま与える。 -/
private theorem step_of_arg_ota {u : ℕ} {r z : BT}
    (hr : r ∈ OT_B) (hne : r ≠ BZero)
    (hz : z ∈ domB r ∨ z ∈ NatSet)
    (hzOT : isOT_BT z = true) (hzDF : dfree_BT z = true)
    (heq : operB (Dprin (u : ℕ∞) r) (numBT 0) =
      Dprin (u : ℕ∞) (operB r z)) :
    ∃ r', operB (Dprin (u : ℕ∞) r) (numBT 0) = Dprin (u : ℕ∞) r'
        ∧ r' ∈ OT_B ∧ lessBT r' r = true := by
  refine ⟨operB r z, heq, ?_, ?_⟩
  · have hc := buchholz_fseq_closed_general r z hr.1 hr.2 hne hz hzOT hzDF
    exact ⟨hc.1, hc.2⟩
  · exact buchholz_fseq_descent r z hr.1 hne hz

/-- **Isabelle 版が仮定に取っていた `step` の無条件証明**（Lean の `operB` は
全域なので [Buc1] 3.2 の全域性は不要）。 -/
private theorem operB_Dprin_step_ota {u : ℕ} {r : BT}
    (hr : r ∈ OT_B) (hne : r ≠ BZero) :
    ∃ r', operB (Dprin (u : ℕ∞) r) (numBT 0) = Dprin (u : ℕ∞) r'
        ∧ r' ∈ OT_B ∧ lessBT r' r = true := by
  have hrq : (r == BZero) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hne (eq_of_beq h)
  cases hdt : domTag r with
  | zeroOnly =>
      -- `dom r = {0}`: `D_u r [0] = (D_u (r[0])) · 1 = D_u (r[0_B])`
      refine step_of_arg_ota (z := BZero) hr hne ?_ rfl rfl ?_
      · exact Or.inl (by simp [domB, hdt, BDom.toSet])
      · rw [operB_Dprin_eq_princ_ota]
        conv_lhs => rw [bOperCore.eq_def]
        simp only [hrq, Bool.false_eq_true, if_false, hdt,
          numNat_numBT_zero_ota]
        show multBT (Dprin (u : ℕ∞) (operB r BZero)) 1 =
          Dprin (u : ℕ∞) (operB r BZero)
        simp [multBT]
  | naturals =>
      -- catch-all 枝: `D_u r [0] = D_u (r[0])`
      refine step_of_arg_ota (z := numBT 0) hr hne
        (Or.inr numBT_zero_mem_NatSet_ota)
        isOT_numBT_zero_ota dfree_numBT_zero_ota ?_
      rw [operB_Dprin_eq_princ_ota]
      conv_lhs => rw [bOperCore.eq_def]
      simp only [hrq, Bool.false_eq_true, if_false, hdt]
      rfl
  | empty =>
      -- catch-all 枝（`r ≠ 0_B` なので実際には起こらないが分岐は同形）
      refine step_of_arg_ota (z := numBT 0) hr hne
        (Or.inr numBT_zero_mem_NatSet_ota)
        isOT_numBT_zero_ota dfree_numBT_zero_ota ?_
      rw [operB_Dprin_eq_princ_ota]
      conv_lhs => rw [bOperCore.eq_def]
      simp only [hrq, Bool.false_eq_true, if_false, hdt]
      rfl
  | below w =>
      by_cases hle : (u : ℕ∞) ≤ (w : ℕ∞)
      · -- kind-1 枝: `D_u r [0] = D_u (r[x_0])`, `x_0 = D_w 0`
        refine step_of_arg_ota (z := Dprin (w : ℕ∞) BZero) hr hne ?_
          (isOT_Dprin_zero_ota w) (dfree_Dprin_zero_ota w) ?_
        · exact Or.inl (by
            simpa [domB, hdt, BDom.toSet] using Dprin_zero_mem_TBv_ota w)
        · rw [operB_Dprin_eq_princ_ota]
          conv_lhs => rw [bOperCore.eq_def]
          simp only [hrq, Bool.false_eq_true, if_false, hdt, hle,
            decide_true, if_true, numNat_numBT_zero_ota]
          rw [bOperCore_xseq_zero_ota]
          rfl
      · -- floor 枝: `D_u r [0] = D_u (r[0])`
        refine step_of_arg_ota (z := numBT 0) hr hne
          (Or.inr numBT_zero_mem_NatSet_ota)
          isOT_numBT_zero_ota dfree_numBT_zero_ota ?_
        rw [operB_Dprin_eq_princ_ota]
        conv_lhs => rw [bOperCore.eq_def]
        simp only [hrq, Bool.false_eq_true, if_false, hdt, hle,
          decide_false, if_false]
        rfl

/-! ## 3. 本体 — `(OT_B, <)` 上の整礎帰納 -/

/-- **Isabelle `y3t_toplevel_OT_tail_annihilate` の逐語形**
(isabelle/layerC/pss_scratch.thy:19355) ＝ layerB
`m_8_7_toplevel_OT_tail_annihilate` (isabelle/layerB/pss_wip.thy:27288)。
1 ステップ降下 `step` を仮定に取る engine 形。 -/
theorem toplevel_OT_tail_annihilate_of_step (hwf : OT_B_wf)
    {q : BT} {u : ℕ} {t' : BT} (t'OT : t' ∈ OT_B)
    (step : ∀ r : BT, r ∈ OT_B → r ≠ BZero →
      ∃ r', operB (addBT q (Dprin (u : ℕ∞) r)) (numBT 0)
              = addBT q (Dprin (u : ℕ∞) r')
          ∧ r' ∈ OT_B ∧ lessBT r' r = true) :
    ∃ k, ((fun a => operB a (numBT 0))^[k])
            (addBT q (Dprin (u : ℕ∞) t'))
          = addBT q (Dprin (u : ℕ∞) BZero) := by
  have hwf' : WellFounded
      (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) := hwf
  revert t'OT
  induction t' using hwf'.induction with
  | _ t' ih =>
    intro t'OT
    by_cases h0 : t' = BZero
    · exact ⟨0, by rw [h0]; rfl⟩
    · obtain ⟨t'', hst, ht''OT, ht''lt⟩ := step t' t'OT h0
      obtain ⟨k, hk⟩ := ih t'' ⟨ht''OT, t'OT, ht''lt⟩ ht''OT
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply, hst]
      exact hk

/-- 補題（順序数項の末尾項の零化可能性）(§8.7, 原文 5971) の
**top-level 値レベル形**（訂正 A26 は撤回済み ⇒ 原文の主張）。

Isabelle: `y3t_toplevel_OT_tail_annihilate` の `step` 仮定を
`operB_Dprin_step_ota` で **落とした強化版**。名前付き仮定は `OT_B_wf`
（[Buc1] 補題 2.2）のみ。 -/
theorem toplevel_OT_tail_annihilate (hwf : OT_B_wf)
    (q : BT) (u : ℕ) {t' : BT} (t'OT : t' ∈ OT_B) :
    ∃ k, ((fun a => operB a (numBT 0))^[k])
            (addBT q (Dprin (u : ℕ∞) t'))
          = addBT q (Dprin (u : ℕ∞) BZero) := by
  refine toplevel_OT_tail_annihilate_of_step hwf t'OT ?_
  intro r hr hne
  obtain ⟨r', heq, hr'OT, hr'lt⟩ := operB_Dprin_step_ota (u := u) hr hne
  refine ⟨r', ?_, hr'OT, hr'lt⟩
  rw [operB_addBT_Dprin_ota, heq]

#print axioms toplevel_OT_tail_annihilate_of_step
#print axioms toplevel_OT_tail_annihilate

end PSS
