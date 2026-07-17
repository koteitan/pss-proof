import «6».«6.5-Red-Pred-commute»
import «6».«6.6-reduced-leftend»
import «7».«7.3-Trans-preserves-zeroT»
import «8».«8.2-subexpr-wid»

/-!
# §8.2 keystone: `subexpr_component_Pred_of_wid`（w-identification 条件形）

- 原文: `tmp/content.md` L3360 付近（§8.2 補題「部分表現の単項成分と `Pred` の関係」）。
  faithful な原文主張は `isabelle/pss_paper.thy:1523`
  (`p_8_2_subexpr_component_Pred`)。
- Isabelle: `m_8_2_subexpr_component_Pred_of_wid`
  （`isabelle/layerB/pss_wip.thy:28627`, ~28836 まで）を逐語移植。
- 公開: `Adm0_full_hyp`, `Admpos_of_wid_hyp`（green-modulo の名前付き仮定 Prop）,
  `subexpr_component_Pred_of_wid`。

## 構造（Isabelle と同一）

`transJm1 M = 0`（Adm0）／`transJm1 M > 0`（Admpos）で場合分けするだけの dispatcher:

- Adm0 枝 → `m_8_2_subexpr_component_Pred_Adm0_full`（wip 27019）を無条件で適用。
- Admpos 枝 → `m_8_2_subexpr_component_Pred_Admpos_of_wid`（wip 27174）を適用。
  その仮定 `t₁ = Trans (Pred M) ≠ 0_B` は本ファイル内部で導出する（Isabelle と同じ）:
  `j₁ = Lng M - 1 > 1` ⟹ `Lng (Pred M) = Lng M - 1 > 1` ⟹ `¬ zeroT (Pred M)`
  ⟹ `Trans (Pred M) ≠ 0_B`（`m_7_3_Trans_zeroT` = Lean `Trans_preserves_zeroT`）。

## green-modulo

`Adm0_full`（wip 27019）と `Admpos_of_wid`（wip 27174）は本 wave の並行 agent の
スコープで、まだ Lean 側に未 built。したがって両者を**名前付き仮定 Prop**
（`Adm0_full_hyp` / `Admpos_of_wid_hyp`）として受け、dispatch を条件付きで証明する。
親 wave がそれぞれの実補題で放電すれば無条件形になる（両 Prop の結論は
`8.2-subexpr-adm0` の公開定理と字面一致の 4 clause 選言）。

## 依存

- `RTPS_TPS`（6.6-reduced-leftend）, `Pred_TPS` / `length_Pred`（6.5-Red-Pred-commute）,
  `Trans_preserves_zeroT`（7.3-Trans-preserves-zeroT）= Isabelle `m_7_3_Trans_zeroT`,
  `wid` / `wid_iff`（8.2-subexpr-wid）。
- Isabelle 側の `Pred_RT_PS` は本移植では不要（`Trans_preserves_zeroT` が `RT_PS` では
  なく `T_PS` 仮定で足りるため。`Pred_TPS` のみ使用）。

## 状態

✅ 本ファイル単独で green（sorry 0）。スコープ = dispatcher 全体（green-modulo
`Adm0_full_hyp` / `Admpos_of_wid_hyp`）。

私的補助の suffix は `_ow`。
-/

namespace PSS

/-! ## green-modulo の名前付き仮定 Prop -/

/-- Isabelle `m_8_2_subexpr_component_Pred_Adm0_full`（wip 27019）の主張。
Adm0（`transJm1 M = 0`）枝を無条件（ガード仮定なし）で放電する補題。並行 agent の
スコープのため、本ファイルでは名前付き仮定として受ける。 -/
def Adm0_full_hyp : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → Br M ≠ [] → 1 < Lng M - 1 →
    transJm1 M = 0 →
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
      ∧ (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
            = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
      ∧ ∃! t₁ : BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t₁ (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero)))
    ∨ ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      ∧ adm M ((Joints M).getD ((Br M).length - 1) 0) = false
      ∧ ∃! t12 : BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t12.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t12.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2)))

/-- Isabelle `m_8_2_subexpr_component_Pred_Admpos_of_wid`（wip 27174）の主張。
Admpos（`transJm1 M > 0`）枝を w-identification `wid M` と `Trans (Pred M) ≠ 0_B`
から放電する補題。並行 agent のスコープのため、本ファイルでは名前付き仮定として
受ける。（Isabelle 同様 `Br M ≠ []` は要求しない。） -/
def Admpos_of_wid_hyp : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 →
    0 < transJm1 M → Trans (Pred M) ≠ BZero → wid M →
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
      ∧ (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
            = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
      ∧ ∃! t₁ : BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t₁ (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero)))
    ∨ ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      ∧ adm M ((Joints M).getD ((Br M).length - 1) 0) = false
      ∧ ∃! t12 : BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t12.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t12.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2)))

/-! ## 私的補助層（suffix `_ow`） -/

/-- Isabelle の `Lpred`/`nzPred`/`t1ne`（wip 28700 付近）に対応。
`j₁ = Lng M - 1 > 1` から `Lng (Pred M) = Lng M - 1 > 1`、よって `¬ zeroT (Pred M)`、
`m_7_3_Trans_zeroT`（Lean `Trans_preserves_zeroT`）で `Trans (Pred M) ≠ 0_B`。 -/
private theorem t1ne_of_j1gt_ow (M : PS) (hM : TPS M) (hj1gt : 1 < Lng M - 1) :
    Trans (Pred M) ≠ BZero := by
  have hL : 1 < Lng M := by omega
  have hLpred : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have hne1 : ¬ (Lng (Pred M) = 1) := by omega
  have hzf : zeroT (Pred M) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne1
  intro hzero
  have hz : zeroT (Pred M) = true :=
    (Trans_preserves_zeroT (Pred M) (Pred_TPS M hM)).mpr hzero
  rw [hzf] at hz
  exact Bool.false_ne_true hz

/-! ## 公開定理: w-id 条件形の §8.2 keystone
（Isabelle `m_8_2_subexpr_component_Pred_of_wid`, layerB 28627）

`j₁ = Lng M - 1`, `J₁ = Lng(Br M) - 1`, `j₀' = Joints(M)_{J₁}`,
`j₁' = FirstNodes(M)_{J₁}` について、`wid M`（w-identification 残差）の下で
原文 §8.2 補題の 4 clause のいずれかが成り立つ。 -/

theorem subexpr_component_Pred_of_wid
    (hAdm0full : Adm0_full_hyp) (hAdmpos : Admpos_of_wid_hyp)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1)
    (hwid : wid M) :
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
      ∧ (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
            = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
      ∧ ∃! t₁ : BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t₁ (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero)))
    ∨ ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      ∧ adm M ((Joints M).getD ((Br M).length - 1) 0) = false
      ∧ ∃! t12 : BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t12.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t12.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2)))
    ∨ (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t123.2.2))) := by
  rcases Nat.eq_zero_or_pos (transJm1 M) with hAdm0 | hAdmposM
  · -- Adm0 枝: 無条件版をそのまま適用
    exact hAdm0full M hR hmono hBrne hj1gt hAdm0
  · -- Admpos 枝: `t₁ = Trans (Pred M) ≠ 0_B` を内部導出してから適用
    have hM : TPS M := RTPS_TPS M hR
    have ht1ne : Trans (Pred M) ≠ BZero := t1ne_of_j1gt_ow M hM hj1gt
    exact hAdmpos M hR hmono hj1gt hAdmposM ht1ne hwid

/-! ## 公理監査 -/

#print axioms subexpr_component_Pred_of_wid

end PSS
