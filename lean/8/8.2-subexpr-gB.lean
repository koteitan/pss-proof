import «8».«8.2-subexpr-adm0-cores»
import «8».«8.2-subexpr-adm0-ctx»

/-!
# §8.2 部分表現の単項成分と `Pred` — Adm0 枝の gB 放電＋gB-free 組み立て

- 原文: `tmp/content.md` L3360 付近（§8.2 補題「部分表現の単項成分と Pred の関係」）。
  「`M` が条件 (I) か (III) を満たすならば `j'₀` は `M` 許容である /
  `M` が条件 (V) を満たすならば `M_{0,j'₁} = M_{1,j'₁}`」の段。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `m_8_2_gB_Adm0_condA` (23704) → `gB_Adm0_condA`
  - `m_8_2_subexpr_component_Pred_Adm0_nogB` (23780) → `subexpr_component_Pred_Adm0_nogB`
    （Isabelle は condA 枝を `m_8_2_subexpr_component_Pred_Adm0` (20828) 経由で
    閉じるが、その組み立ては本 wave の sibling scope なので、ここでは Isabelle
    20828 の condA 枝（clause1 keystone 呼び）を直接インライン化する。
    ¬condA 枝は Isabelle 23865–23914 と同一（clause2/clause4 core 呼び）。）
- 依存（全て built 済の公開定理）:
  `subexpr_component_Pred_Adm0_clause1_keystone` /
  `subexpr_component_Pred_Adm0_clause2_core` /
  `subexpr_component_Pred_Adm0_clause4_core`（8.2-subexpr-adm0-cores）,
  `j1eq_Adm0` / `j0eq_Adm0` / `gA_Adm0` / `notVI_Adm0` / `parent_le_TrMax_Adm0` /
  `gB_condIorIII`（8.2-subexpr-adm0-ctx）,
  `RTPS_condAB`（6.6-reduced-iff-condAB）, `RTPS_mono_head_eq`（6.6-reduced-leftend）,
  `trunk_entries_offset` / `RedCondA_apply`（6.5-Red-le-core）,
  `mono_hasParent_row0`（6.6-P-condAB）— いずれも上記 2 import の推移閉包内。
- Isabelle の `M ∈ RT_PS` / `M ∈ PT_PS` は sibling 8.x file の慣例どおり
  `(hR : RTPS M) (hmono : monoT M = true)` に開いて受ける。
  `defines` の `j₁ = Lng M - 1` / `J₁ = Lng (Br M) - 1` / `j₀' = Joints M ! J₁` /
  `j₁' = FirstNodes M ! J₁` は展開して直書きする（`!` → `.getD`）。
- 状態: ✅ 本 wave で完成。`python3 python/check_lean.py lean/8/8.2-subexpr-gB.lean`
  が rc=0（エラー 0・未証明ゼロ）。公開 2 定理とも公理は
  `[propext, Classical.choice, Quot.sound]` のみ。
-/

namespace PSS

/-! ## 公開定理 1/2: clause-(1) ガード gB の condA 無条件放電
（Isabelle `m_8_2_gB_Adm0_condA`, layerB 23704）

cond-I/III は `adm M j'₀` を直接主張（`gB_condIorIII`＋`j0eq_Adm0`）。
cond-V は幹の対角性で第 1 disjunct を強制:
`j'₁ = j₁ = Lng M - 1`（`j1eq_Adm0`）、`jp = parent M 0 j₁ ≤ TrMax M`
（`parent_le_TrMax_Adm0`）、幹は対角（`trunk_entries_offset`＋根の対角性
`RTPS_mono_head_eq`）なので `M_{0,jp} = M_{1,jp}`、行 0 の親ステップ
（`RedCondA_apply`）と cond-V の行 1 ステップで
`M_{0,j₁} = M_{0,jp}+1 = M_{1,jp}+1 = M_{1,j₁}`。 -/

theorem gB_Adm0_condA (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hcond : (transCondI M || transCondIII M || transCondV M) = true) :
    entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
        = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true := by
  have hM : TPS M := RTPS_TPS M hR
  have hj1eq := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hj0eq := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  by_cases hV : transCondV M = true
  · -- cond-V: 第 1 disjunct `M_{0,j'₁} = M_{1,j'₁}`
    left
    rw [hj1eq]
    have hA := (RTPS_condAB M hR).1
    -- `jp ≤ TrMax M`
    have hjpTr : parent M 0 (Lng M - 1) ≤ TrMax M :=
      parent_le_TrMax_Adm0 M hR hmono hAdm0
    -- 根は対角: `M_{0,0} = M_{1,0}`
    have hhead : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
    -- 幹は対角オフセット
    have hoff := trunk_entries_offset M hM hA (parent M 0 (Lng M - 1)) hjpTr
    -- 行 0 の親ステップ（RedCondA）
    have hp0 : hasParent M 0 (Lng M - 1) = true :=
      mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
    have hrcA0 : entry M 0 (parent M 0 (Lng M - 1)) + 1
        = entry M 0 (Lng M - 1) :=
      RedCondA_apply M hA 0 (Lng M - 1) (by omega) (by omega) hp0
    -- cond-V の行 1 ステップ
    have hVs := hV
    simp only [transCondV, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hVs
    have hVstep : entry M 1 (parent M 0 (Lng M - 1)) + 1
        = entry M 1 (Lng M - 1) := by
      have := hVs.1.2
      simpa [lastParent, lastIdx] using this
    omega
  · -- cond-I/III: 第 2 disjunct `adm M j'₀`
    right
    have hcond' : transCondI M = true ∨ transCondIII M = true := by
      simp only [Bool.or_eq_true] at hcond
      rcases hcond with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hV
    have hadm : adm M (parent M 0 (Lng M - 1)) = true :=
      gB_condIorIII M hcond'
    rw [hj0eq]
    simpa [transJ0, lastParent, lastIdx] using hadm

/-! ## 公開定理 2/2: Adm0 枝、gB-free の 4-clause 組み立て
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_nogB`, layerB 23780）

clause-(1) の gB ガードは condA 枝で `gB_Adm0_condA` により内部放電される。
残るガードは clause-(2) 系の `t₂ ≠ 0` / `M_{0,j'₁} > M_{1,j'₁}` / `¬ adm M j'₀`
のみ（cond-II/IV 部分ケースの経験的ガード、Isabelle と同一）。
condA 枝 = clause (1)（keystone）、¬condA 枝 = leftDj₀ で clause (4)/(2)。 -/

theorem subexpr_component_Pred_Adm0_nogB (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
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
  have hj1eq := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hj0eq := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  have hnotVI := notVI_Adm0 M hR hmono hBrne hj1gt hAdm0
  by_cases hcond : (transCondI M || transCondIII M || transCondV M) = true
  · -- condA 枝: gB を内部放電して clause (1)（keystone）
    left
    have hgA := gA_Adm0 M hR hmono hBrne hj1gt hAdm0
    have hgB := gB_Adm0_condA M hR hmono hBrne hj1gt hAdm0 hcond
    exact subexpr_component_Pred_Adm0_clause1_keystone M hR hmono hj1gt hAdm0
      hcond hj1eq hgA hgB
  · -- ¬condA 枝: leftDj₀ で clause (4)/(2) の split
    have hcondF : (transCondI M || transCondIII M || transCondV M) = false :=
      Bool.eq_false_of_not_eq_true hcond
    by_cases hleft :
        bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
          = (entry M 1 (transJ0 M) : ℕ∞)
    · -- clause (4)
      right; right; right
      rw [hj0eq]
      exact subexpr_component_Pred_Adm0_clause4_core M hR hmono hj1gt hAdm0
        hcondF hnotVI ht2ne hleft
    · -- clause (2)
      right; left
      refine ⟨hj1eq, he0gt, hnadmj0, ?_⟩
      rw [hj0eq]
      exact subexpr_component_Pred_Adm0_clause2_core M hR hmono hj1gt hAdm0
        hcondF hnotVI ht2ne hleft

/-! ## 公理監査 -/

#print axioms gB_Adm0_condA
#print axioms subexpr_component_Pred_Adm0_nogB

end PSS
