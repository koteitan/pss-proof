import «8».«8.2-subexpr-adm0»
import «8».«8.2-subexpr-gB»
import «8».«8.2-subexpr-clause34»
import «8».«8.2-subexpr-wid»

/-!
# §8.2 部分表現の単項成分と `Pred` — Adm0 完全版 ＋ Admpos 枝（wid 経由）

- 原文: `tmp/content.md` §8.2 補題「部分表現の単項成分と `Pred` の関係」
  （4 clause の場合分け）。`Adm_M(j₀) = 0` 枝の**ガード完全放電版**と、
  `Adm_M(j₀) > 0` 枝の wid 還元版。
- Isabelle 対応（`isabelle/layerB/pss_wip.thy`）:
  - `subexpr_component_Pred_Adm0_full`     ← `m_8_2_subexpr_component_Pred_Adm0_full`
    (27019、~27173 まで)
  - `subexpr_component_Pred_Admpos_of_wid` ← `m_8_2_subexpr_component_Pred_Admpos_of_wid`
    (27174、~27394 まで)
- 依存（すべて built 済の公開定理）:
  - `8.2-subexpr-adm0`: `subexpr_component_Pred_Adm0_nogB` は `8.2-subexpr-gB` 側。
    本ファイルは `subexpr_component_Pred_Adm0_nogB`（gB を condA 枝で内部放電済み、
    ガード `t₂≠0`/`e0gt`/`¬adm j₀` は仮定のまま）を ¬condA 枝で使う。
  - `8.2-subexpr-adm0-cores`: `subexpr_component_Pred_Adm0_clause1_keystone`。
  - `8.2-subexpr-adm0-ctx`: `j1eq_Adm0` / `j0eq_Adm0` / `gA_Adm0` / `notVI_Adm0` /
    `condII_or_condIV` / `nadmj0_notAVI` / `t2ne_notAVI` / `e0gt_condIV` /
    `e0gt_e1zero`。
  - `8.2-subexpr-gB`: `gB_Adm0_condA`。
  - `8.2-subexpr-clause34`: `subexpr_component_Pred_clause34_of_witness`。
  - `8.2-subexpr-wid`: `wid` / `wid_iff`。
- 方針:
  - **Adm0_full**: Isabelle と同じく `(I)∨(III)∨(V)` で場合分け。condA 枝は
    `gB_Adm0_condA` で gB を放電して keystone → clause (1)。¬condA 枝では
    `notVI_Adm0` と併せて `t2ne_notAVI` / `nadmj0_notAVI` /
    (`condII_or_condIV` → `e0gt_e1zero` または `e0gt_condIV`) で 3 ガードを放電し、
    `subexpr_component_Pred_Adm0_nogB` に渡す（nogB は内部で同じ condA split を
    行い、この枝では ¬condA 側に落ちる）。ガードの添字表示は `j1eq_Adm0` /
    `j0eq_Adm0` で `j₁'`/`j₀'` 表示へ移送。
  - **Admpos_of_wid**: Isabelle の STEP 1 = `trans_admpos_body_split_wfin`
    (`layerB/pss_wip.thy:26699`、下請けは `trans_admpos_body_split` 26573 の外科機構)
    は Lean 未移植（並列 scope）。よって**その結論式そのものを名前付き Prop
    `TransAdmposBodySplitWfin` として定義し、green-modulo で仮定に取る**。
    残りは Isabelle 逐語: witness の有限頭 `w' = RightNodes(Trans M)₁` を
    `wid M` で 2 基点のいずれかに同定し、`clause34_of_witness` で 4-clause に包む。
- 状態: ✅ sorry 0（本ファイル単独で green）。ただし `Admpos_of_wid` は
  `TransAdmposBodySplitWfin` を仮定に取る green-modulo 形（親 wave が放電）。
-/

namespace PSS

/-! ## Adm0 枝: ガード完全放電版
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_full`, layerB 27019）

`j₁ = Lng M - 1`, `J₁ = Lng(Br M) - 1`, `j₀' = Joints(M)_{J₁}`,
`j₁' = FirstNodes(M)_{J₁}` について、`M ∈ RT_PS ∩ PT_PS`・`Br M ≠ []`・`j₁ > 1`・
`transJm1 M = 0` のみから原文 §8.2 補題の 4 clause 選言が従う（外部ガードなし）。 -/

theorem subexpr_component_Pred_Adm0_full (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
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
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  -- 幾何ブリッジ（Adm0 で放電済み）
  have hj1eq := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hj0eq := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hnotVI := notVI_Adm0 M hR hmono hBrne hj1gt hAdm0
  by_cases hcond : (transCondI M || transCondIII M || transCondV M) = true
  · -- condA 枝: gB を `gB_Adm0_condA` で放電し keystone → clause (1)
    left
    have hgA := gA_Adm0 M hR hmono hBrne hj1gt hAdm0
    have hgB := gB_Adm0_condA M hR hmono hBrne hj1gt hAdm0 hcond
    exact subexpr_component_Pred_Adm0_clause1_keystone M hR hmono hj1gt hAdm0
      hcond hj1eq hgA hgB
  · -- ¬condA 枝: 3 ガードを ctx 層で放電して nogB に渡す
    have hnotA : ¬(transCondI M = true ∨ transCondIII M = true
        ∨ transCondV M = true) := by
      intro h
      apply hcond
      rcases h with h | h | h <;> simp [h]
    -- ガード (a): t₂ ≠ 0
    have ht2ne : transT2 M ≠ BZero :=
      t2ne_notAVI M hR hmono hL hj1gt hnotA hnotVI
    -- ガード (b): ¬ adm M j₀'
    have hnadmj0J : adm M (transJ0 M) = false :=
      nadmj0_notAVI M hR hmono hL hnotA hnotVI
    have hnadmj0 : adm M ((Joints M).getD ((Br M).length - 1) 0) = false := by
      rw [hj0eq]; exact hnadmj0J
    -- ガード (c): M_{1,j₁} < M_{0,j₁}（cond (II)/(IV) の 2 部分ケース）
    have he0gtj1 : entry M 1 (Lng M - 1) < entry M 0 (Lng M - 1) := by
      rcases condII_or_condIV M hR hmono hL hnotA hnotVI with hII | hIV
      · -- (II): M_{1,j₁} = 0
        have he1z : entry M 1 (Lng M - 1) = 0 := by
          simp only [transCondII, Bool.and_eq_true, beq_iff_eq] at hII
          simpa [lastIdx] using hII.1
        exact e0gt_e1zero M hM hmono hL he1z
      · -- (IV): 行 0 の親ステップ ＋ 行 0/行 1 支配
        exact e0gt_condIV M hR hmono hL hIV
    have he0gt : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
        < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
      rw [hj1eq]; exact he0gtj1
    exact subexpr_component_Pred_Adm0_nogB M hR hmono hBrne hj1gt hAdm0
      ht2ne he0gt hnadmj0

/-! ## Admpos 枝の下請け（green-modulo の名前付き仮定）

Isabelle `trans_admpos_body_split_wfin`（`layerB/pss_wip.thy:26699`）の結論式。
`Trans M` が d-free であることから、`trans_admpos_body_split` (26573) が与える
共通接頭辞分解の末尾 principal の頭 `w` は有限で、`RightNodes (Trans M)₁` に一致する
（さらに `RightAnces M₁` にも一致）。Lean 側は下請けの外科機構
（`trans_surgery_localized` / `scb_outer_surgery_split` /
`trans_admpos_outer_principal`）が未移植のため、本ファイルではこの結論を
名前付き Prop として仮定に取る。 -/

def TransAdmposBodySplitWfin : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → 0 < transJm1 M →
    Trans (Pred M) ≠ BZero →
    ∃ pre u2 u3 : BT,
      Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
          (addBT pre (Dprin (((RightNodes (Trans M)).getD 1 0 : ℕ) : ℕ∞) u2))
      ∧ Trans M = Dprin (entry M 1 0 : ℕ∞)
          (addBT pre (Dprin (((RightNodes (Trans M)).getD 1 0 : ℕ) : ℕ∞) u3))
      ∧ (RightNodes (Trans M)).getD 1 0 = (RightAnces M).getD 1 0

/-! ## Admpos 枝: wid への還元
（Isabelle `m_8_2_subexpr_component_Pred_Admpos_of_wid`, layerB 27174）

`transJm1 M > 0`（Admpos）レジームでは、w-identification 残差 `wid M`
（`RightNodes(Trans M)₁ ∈ {M_{1,j₁'}, M_{1,j₀'}}`）を仮定すれば、
keystone の 4-clause 選言（実際には clause (3)/(4)）が従う。 -/

theorem subexpr_component_Pred_Admpos_of_wid (M : PS)
    (hsplit : TransAdmposBodySplitWfin)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (ht1ne : Trans (Pred M) ≠ BZero) (hwid : wid M) :
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
  -- STEP 1: 有限頭 `w' = RightNodes (Trans M)₁` を持つ共通接頭辞分解
  obtain ⟨pre, u2, u3, witP, witM, -⟩ :=
    hsplit M hR hmono hj1gt hAdmpos ht1ne
  -- w-id: 有限頭は 2 基点の行 1 成分のいずれか
  have wsplit := (wid_iff M).mp hwid
  -- clause (3)/(4) として包む
  exact subexpr_component_Pred_clause34_of_witness M
    ((RightNodes (Trans M)).getD 1 0) pre u2 u3 wsplit witP witM

/-! ## 公理監査 -/

#print axioms subexpr_component_Pred_Adm0_full
#print axioms subexpr_component_Pred_Admpos_of_wid

end PSS
