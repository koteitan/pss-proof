import «8».«8.2-subexpr-setup»
import «8».«8.2-subexpr-adm0-cores»
import «8».«8.2-subexpr-adm0-ctx»

/-!
# §8.2 部分表現の単項成分と `Pred` — Adm0 assembly

- 原文: `tmp/content.md` L3360 付近（§8.2 補題「部分表現の単項成分と Pred の関係」、
  4 clause の場合分けの `Adm`-zero（`transJm1 M = 0`）枝の組み立て）。
- Isabelle: `m_8_2_subexpr_component_Pred_Adm0`
  （`isabelle/layerB/pss_wip.thy:20828`、~20961 まで）。
- 公開定理: `subexpr_component_Pred_Adm0`。
- 依存（全て built 済 C-1 層の公開定理）:
  - `8.2-subexpr-adm0-ctx`: `j1eq_Adm0`（wip 20639）/ `j0eq_Adm0`（20657）/
    `gA_Adm0`（20727）/ `notVI_Adm0`（20763）。
  - `8.2-subexpr-adm0-cores`: `subexpr_component_Pred_Adm0_clause1_keystone`
    （20532）/ `subexpr_component_Pred_Adm0_clause2_core`（20167）/
    `subexpr_component_Pred_Adm0_clause4_core`（20290）。
- 方針: Isabelle の組み立てを逐語移植。幾何ブリッジ（`j₁' = j₁`, `j₀' = transJ0 M`,
  ガード `gA`, `¬(VI)`）を Adm0 で放電した後、`(I)∨(III)∨(V)` で場合分け:
  - 成立 → keystone で clause (1)。
  - 不成立 → `leftDj₀`（`t₂` の最終 principal の頭 = `M_{1,j₀}`）で場合分けし、
    成立なら clause (4) core、不成立なら clause (2) core（＋ガード `j1eq`/`e0gt`/
    `nadmj0` の束ね）。core の `transJ0 M` 表示は `j0eq_Adm0` の逆書き換えで
    `j₀' = Joints(M)_{J₁}` 表示に戻す。
- ガード仮定 `hgB`/`ht2ne`/`he0gt`/`hnadmj0` は Isabelle と同じく仮定のまま受ける
  （最終 assembly wave が ctx 層の `gB_condIorIII`/`t2ne_notAVI`/`e0gt_condIV`/
  `e0gt_e1zero`/`nadmj0_notAVI` で放電する）。
- 状態: ✅ sorry 0（本ファイル単独で green）。
-/

namespace PSS

/-! ## 公開定理: Adm0 枝の 4 clause 組み立て
（Isabelle `m_8_2_subexpr_component_Pred_Adm0`, layerB 20828）

`j₁ = Lng M - 1`, `J₁ = Lng(Br M) - 1`, `j₀' = Joints(M)_{J₁}`,
`j₁' = FirstNodes(M)_{J₁}` について、Adm0（`transJm1 M = 0`）＋ガード仮定の下で
原文 §8.2 補題の 4 clause のいずれかが成り立つ。 -/

theorem subexpr_component_Pred_Adm0 (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1)
    (hAdm0 : transJm1 M = 0)
    (hgB : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
        ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
    (ht2ne : transT2 M ≠ BZero)
    (he0gt : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
        < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0))
    (hnadmj0 : adm M ((Joints M).getD ((Br M).length - 1) 0) = false) :
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
  -- 幾何ブリッジ（すべて Adm0 で放電済み）
  have hj1eq := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hj0eq := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hgA := gA_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hnVI := notVI_Adm0 M hR hmono hBrne hj1gt hAdm0
  -- transC2 のサブケースで場合分け
  cases hcond : (transCondI M || transCondIII M || transCondV M) with
  | true =>
      -- clause (1): keystone のパッケージそのもの
      exact Or.inl (subexpr_component_Pred_Adm0_clause1_keystone M hR hmono
        hj1gt hAdm0 hcond hj1eq hgA hgB)
  | false =>
      -- ¬(I∨III∨V), ¬VI, t₂ ≠ 0: leftDj₀ で分岐
      by_cases hleft : bpHeadV ((PB (transT2 M)).getD
          ((PB (transT2 M)).length - 1) BZero) = (entry M 1 (transJ0 M) : ℕ∞)
      · -- clause (4)
        have cl4 := subexpr_component_Pred_Adm0_clause4_core M hR hmono
          hj1gt hAdm0 hcond hnVI ht2ne hleft
        rw [← hj0eq] at cl4
        exact Or.inr (Or.inr (Or.inr cl4))
      · -- clause (2)
        have cl2 := subexpr_component_Pred_Adm0_clause2_core M hR hmono
          hj1gt hAdm0 hcond hnVI ht2ne hleft
        rw [← hj0eq] at cl2
        exact Or.inr (Or.inl ⟨hj1eq, he0gt, hnadmj0, cl2⟩)

/-! ## 公理監査 -/

#print axioms subexpr_component_Pred_Adm0

end PSS
