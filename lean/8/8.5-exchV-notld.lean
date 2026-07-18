import «8».«8.5-exchV-nadm-c2l1»
import «8».«8.5-exchV-props»
import «8».«8.2-strongmono-props»
import «8».«8.5-Joints-FirstNodes-basic»
import «7».«7.3-Trans-IncrFirst-Red»

/-!
# §8.5 ExchV 非許容枝 `notLD`（`NadmC2L1NotLD` の放電）

## 目的

`8.5-exchV-nadm-c2l1` の最終残差 `NadmC2L1NotLD`（Isabelle `atx_notLD`）を放電する。
`NadmC2L1NotLD` は非許容条件(V)ホスト `M` について「前線 `t₂` の末尾 principal 頭は
`M₁,ⱼ₀` でない」:

    (bpHeadV ((PB t₂).getD ((PB t₂).length - 1) 0) == (M₁,ⱼ₀ : ℕ∞)) = false   (t₂ = transT2 M)

を主張する。house pattern で `nadmC2L1NotLD_holds : NadmC2L1NotLD`。

## 原文 / Isabelle 対応

- Isabelle blueprint（`isabelle/layerB/pss_wip.thy`）:
  * `atx_notLD`(86198) ← `atx_condV_nadm_t2_components`(86068)
    ← `m_8_5_Joints_FirstNodes_basic_condV`(60636)
       ＋ `m_8_2_subexpr_component_strongmono_uncond`(強単項成分の下界)。
  * `atx_condV_nadm_t2_components`（原文 補題「条件(V)の下での Joints/FirstNodes/t₂
    の基本性質」(3)）: `N = seg M j₋₁ j₁`, `RN = Red N` は強単項（`DT_PS`）なので、
    `Joints_FirstNodes_basic_condV` が最終枝の DIAG（行0=行1）と `FirstNodes ! last
    = j₁-j₋₁` を与え、`subexpr_component_strongmono` の (2) 枝が発火して
    `Trans RN = D_{RN₁,₀} t'` の各単項成分 `p` が `D_{RN₁,ⱼ₁₋ⱼ₋₁} 0` 以上になる。
    `Trans RN = Trans N = Mark M j₋₁ = c₂ = D_{M₁,ⱼ₋₁}(t₂ +_B D_{M₁,ⱼ₁} 0)` で body を
    ピン留めすると `t' = t₂ +_B D_{M₁,ⱼ₁} 0`、よって `t₂` の全成分が `D_{M₁,ⱼ₁} 0` 以上。
  * `atx_notLD`: 末尾 principal は `t₂` の成分の一つなので頭 `v ≥ M₁,ⱼ₁ = M₁,ⱼ₀ + 1
    > M₁,ⱼ₀`（条件(V)）。よって `v ≠ M₁,ⱼ₀`。

## Lean 対応（ビルド済ツールボックス）

| Isabelle | Lean |
|---|---|
| `s85b_condV_setup` | `condV_setup_holds`（`8.5-exchV-props`） |
| `m_8_5_scbdec_c1_shape` | `c1_shape_holds`（同上） |
| `s85b_condV_bridge(3)(4)` | `condV_bridge_hp_jm2`（推移的、`8.5-exchV-M-tower-close`） |
| `m_8_5_Joints_FirstNodes_basic_condV` | `Joints_FirstNodes_basic`（`8.5-Joints-FirstNodes-basic`） |
| `m_8_2_subexpr_component_strongmono_uncond` | `subexpr_component_strongmono` ＋ `sxsm_factA_uncond_holds`/`sxsm_factB_holds`（`8.2-strongmono-props`） |
| `m_8_2_standard_slice_Red_strongmono` | `standard_slice_Red_strongmono` |
| `m_6_5_Lng_Red` | `Lng_Red_invariance` |
| `m_6_6_ancestor_slice_Red_IncrFirst` | `ancestor_slice_Red_IncrFirst` |
| `entry_funpow_IncrFirst1` | `entry_IncrFirstN_one` |
| `rcpb_nextR_seg`/`entry_seg` | `entry_seg` |
| `m_7_4_Mark_Trans_repr` | `Mark_Trans_repr` |
| `m_7_3_Mark_rightmost2` | `m_7_3_Mark_rightmost2` |
| `m_7_3_Trans_Red` | `Trans_Red` |
| `nadm_Adm_lt`/`le0_trans`/`adm_row1_ancestry` | private below / `adm_row1_ancestry`/`row1_implies_row0` |
| `leBT_Dpt0_iff`/`PB_addBT_app` | private `leBT_Dprin0_iff_nl`/`PB_addBT_app_nl` |

## 依存（すべて committed 緑, main d96fb0b）

«8».«8.5-exchV-nadm-c2l1»（`NadmC2L1NotLD`／推移的に `condV_bridge_hp_jm2`／
`s84x_jm2`／`adm_row1_ancestry`／`mono_hasParent_row0`／`nextR0_leR`／`Adm_adm`／
`ancestor_basic_1`／`parent_exists_3`）, «8».«8.5-exchV-props»（`condV_setup_holds`／
`c1_shape_holds`）, «8».«8.2-strongmono-props»（`subexpr_component_strongmono`／
`sxsm_factA_uncond_holds`／`sxsm_factB_holds`）, «8».«8.5-Joints-FirstNodes-basic»
（`Joints_FirstNodes_basic`／`standard_slice_Red_strongmono`／`Lng_Red_invariance`／
`ancestor_slice_Red_IncrFirst`／`entry_IncrFirstN_one`／`entry_seg`／`length_seg`／
`Mark_Trans_repr`）, «7».«7.3-Trans-IncrFirst-Red»（`Trans_Red`）,
`PSS/Trans.lean`／`PSS/Buchholz.lean`／`PSS/Adm.lean`.

## 状態

GREEN（sorry 0, axioms = [propext, Classical.choice, Quot.sound]）。`NadmC2L1NotLD` を
無条件に discharge。§8.5 ExchV 非許容枝 `c₂(L₁)` の唯一の残差が閉じる。

## private 接尾辞: `_nl`
-/

namespace PSS

/-! ## 小道具（Isabelle の私的補題 / 他ファイルの private の複製） -/

/-- Isabelle `nadm_Adm_lt`。`adm M j = false` なら `Adm M j < j`。 -/
private theorem nadm_Adm_lt_nl (M : PS) (j : ℕ) (hna : adm M j = false) :
    Adm M j < j := by
  have hle : Adm M j ≤ j := Adm_le M j
  rcases Nat.lt_or_ge (Adm M j) j with h | h
  · exact h
  · exfalso
    have heq : Adm M j = j := by omega
    have hadm : adm M (Adm M j) = true := Adm_adm M j
    rw [heq, hna] at hadm
    exact Bool.noConfusion hadm

/-- Isabelle `le0_trans` の値特徴付け構成（`8.5-Joints-FirstNodes-basic` の
`le0_trans_jfb` と同一証明。当該は private なので再掲）。 -/
private theorem le0_trans_nl (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hbc : leR M 0 b c = true)
    (halt : a < b) (hblt : b < c) (hcL : c < Lng M) :
    leR M 0 a c = true := by
  apply parent_exists_3 M a c hM (by omega) hcL
  intro j haj hjc
  by_cases hjb : j ≤ b
  · exact ancestor_basic_1 M a j b hM haj hjb hab
  · have h1 : entry M 0 a < entry M 0 b :=
      ancestor_basic_1 M a b b hM halt le_rfl hab
    have h2 : entry M 0 b < entry M 0 j :=
      ancestor_basic_1 M b j c hM (by omega) hjc hbc
    omega

/-- `Dprin` の単射性（`.trm [.db v a]` の構造）。 -/
private theorem Dprin_inj_nl {u v : ℕ∞} {a b : BT} (h : Dprin u a = Dprin v b) :
    u = v ∧ a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact ⟨h.1, h.2⟩

/-- Isabelle `PB_addBT_app`。 -/
private theorem PB_addBT_app_nl (a b : BT) : PB (addBT a b) = PB a ++ PB b := by
  rcases a with ⟨as⟩; rcases b with ⟨bs⟩
  simp [PB, addBT, untrm]

/-- `PB t` の要素は principal 項。 -/
private theorem PB_mem_Dprin_nl {t r : BT} (hr : r ∈ PB t) : ∃ v c, r = Dprin v c := by
  simp only [PB, List.mem_map] at hr
  obtain ⟨p, -, rfl⟩ := hr
  rcases p with ⟨v, c⟩
  exact ⟨v, c, rfl⟩

/-- `t ≠ 0_B` なら `PB t` は非空。 -/
private theorem PB_ne_nil_of_ne_BZero_nl (t : BT) (h : t ≠ BZero) : PB t ≠ [] := by
  cases t with
  | trm as =>
    simp only [PB, untrm, ne_eq, List.map_eq_nil_iff]
    intro has
    subst has
    exact h rfl

/-- `bpHeadV (D_v c) = v`（定義計算）。 -/
private theorem bpHeadV_Dprin_nl (v : ℕ∞) (c : BT) : bpHeadV (Dprin v c) = v := rfl

private theorem lessBT_BZero_iff_nl (c : BT) : lessBT BZero c = true ↔ c ≠ BZero := by
  rcases c with ⟨cs⟩
  cases cs with
  | nil => simp [BZero, lessBT, lessBPList]
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-- Isabelle `leBT_Dpt0_iff`: `D_u 0 ≤_B D_v c ⟺ u ≤ v`。 -/
private theorem leBT_Dprin0_iff_nl (u v : ℕ∞) (c : BT) :
    leBT (Dprin u BZero) (Dprin v c) = true ↔ u ≤ v := by
  rw [leBT]
  simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
    Bool.false_eq_true, and_false, or_false, decide_eq_true_eq, beq_iff_eq,
    BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true]
  constructor
  · rintro ((hlt | ⟨heq, -⟩) | ⟨heq, -⟩)
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · exact le_of_eq heq
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (Or.inl hlt)
    · by_cases hc : c = BZero
      · exact Or.inr ⟨heq, hc.symm⟩
      · exact Or.inl (Or.inr ⟨heq, (lessBT_BZero_iff_nl c).mpr hc⟩)

/-! ## `t₂` 成分の下界（Isabelle `atx_condV_nadm_t2_components`, pss_wip.thy:86068）

原文 補題「条件(V)の下での `Joints`/`FirstNodes`/`t₂` の基本性質」(3)。前線 `t₂` の
各単項成分は `D_{M₁,ⱼ₁} 0`（`j₁ = Lng M - 1`）以上。 -/

private theorem t2_component_bound_nl (M : PS) (hST : STPS M)
    (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false) :
    ∀ c ∈ PB (transT2 M),
      leBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) c = true := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  -- setup / c1 shape
  obtain ⟨hJ1pos, hT1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨hVshape, _, _, _⟩ := c1_shape_holds M hR hM hmono hJ1pos hT1ne
  -- ranges from condition (V) (Isabelle `wnx_setup`)
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hlen : 1 < Lng M := by omega
  -- `transJm1 M = Adm M (transJ0 M)` (defeq) → non-adm strict descent
  have hjm1lt : transJm1 M < transJ0 M := nadm_Adm_lt_nl M (transJ0 M) hnadm
  have hmm1ltj1 : transJm1 M < Lng M - 1 := by omega
  -- ancestry `leR M 0 j₋₁ j₁`
  have hp0M : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextj0 : nextR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0M
  have hlej0j1 : leR M 0 (transJ0 M) (Lng M - 1) = true := nextR0_leR M _ _ hnextj0
  have hle1a : leR M 1 (transJm1 M) (transJ0 M) = true :=
    adm_row1_ancestry M (transJ0 M) hM (by omega)
  have hle0a : leR M 0 (transJm1 M) (transJ0 M) = true :=
    row1_implies_row0 M _ _ hM hle1a
  have leM : leR M 0 (transJm1 M) (Lng M - 1) = true :=
    le0_trans_nl M (transJm1 M) (transJ0 M) (Lng M - 1) hM hle0a hlej0j1 hjm1lt
      (by omega) (by omega)
  -- the reduced slice `RN = Red (seg M j₋₁ j₁)`
  have hj1le : Lng M - 1 ≤ Lng M - 1 := le_refl _
  have hND : DTPS (Red (seg M (transJm1 M) (Lng M - 1))) :=
    standard_slice_Red_strongmono M (transJm1 M) (Lng M - 1) hST hmm1ltj1 hj1le leM
  have hLNval : Lng (seg M (transJm1 M) (Lng M - 1)) = Lng M - transJm1 M := by
    rw [length_seg]; omega
  have hsegpos : 0 < Lng (seg M (transJm1 M) (Lng M - 1)) := by rw [hLNval]; omega
  have hsegT : TPS (seg M (transJm1 M) (Lng M - 1)) :=
    List.ne_nil_of_length_pos hsegpos
  -- Joints/FirstNodes basic (condV variant: derive nextR & gap from (V))
  have hbridge := condV_bridge_hp_jm2 M hM hmono hcond
  have hp1 : hasParent M 1 (Lng M - 1) = true := hbridge.1
  have hjm2eq : s84x_jm2 M = transJ0 M := hbridge.2
  have hnx1 : nextR M 1 (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    have h := hasParent_next_fseq M 1 (Lng M - 1) hp1
    rw [show parent M 1 (Lng M - 1) = transJ0 M from hjm2eq] at h
    exact h
  have hnadm' : adm M (parent M 0 (Lng M - 1)) = false := hnadm
  have hgap : parent M 0 (Lng M - 1) < Lng M - 1 - 1 := by
    show transJ0 M < Lng M - 1 - 1; omega
  obtain ⟨hBrge, _hG2, hFN, hDIAG⟩ := Joints_FirstNodes_basic M hST hmono hnx1 hnadm' hgap
  have key : Adm M (parent M 0 (Lng M - 1)) = transJm1 M := rfl
  rw [key] at hBrge hFN hDIAG
  have hBrne : Br (Red (seg M (transJm1 M) (Lng M - 1))) ≠ [] := by
    intro he; rw [he] at hBrge; simp at hBrge
  -- unconditional strong-monomiality component bound
  obtain ⟨t', ⟨hlead, hfactB, _, _⟩, _⟩ :=
    subexpr_component_strongmono sxsm_factA_uncond_holds sxsm_factB_holds
      (Red (seg M (transJm1 M) (Lng M - 1))) hND hBrne
  -- guard = second disjunct via DIAG at the last first-node
  have hguard :
      (Joints (Red (seg M (transJm1 M) (Lng M - 1)))).getD
          ((Br (Red (seg M (transJm1 M) (Lng M - 1)))).length - 1) 0 = 0 ∨
        entry (Red (seg M (transJm1 M) (Lng M - 1))) 0
            ((FirstNodes (Red (seg M (transJm1 M) (Lng M - 1)))).getD
              ((Br (Red (seg M (transJm1 M) (Lng M - 1)))).length - 1) 0) =
          entry (Red (seg M (transJm1 M) (Lng M - 1))) 1
            ((FirstNodes (Red (seg M (transJm1 M) (Lng M - 1)))).getD
              ((Br (Red (seg M (transJm1 M) (Lng M - 1)))).length - 1) 0) := by
    refine Or.inr ?_
    rw [hFN]; exact hDIAG
  have hcomp0 := hfactB hguard
  -- IncrFirst bridge: row-1 entries of `RN` transfer to host `M`
  have hfacts := ancestor_slice_Red_IncrFirst M (transJm1 M) (Lng M - 1) hR hmm1ltj1 hj1le leM
  have hsegeq : seg M (transJm1 M) (Lng M - 1)
      = IncrFirstN (entry M 0 (transJm1 M) - entry M 1 (transJm1 M))
          (Red (seg M (transJm1 M) (Lng M - 1))) := hfacts.2.2
  have e1RN : ∀ p, p < Lng (seg M (transJm1 M) (Lng M - 1)) →
      entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 p = entry M 1 (transJm1 M + p) := by
    intro p hp
    have hb : entry (seg M (transJm1 M) (Lng M - 1)) 1 p = entry M 1 (transJm1 M + p) :=
      entry_seg M (transJm1 M) (Lng M - 1) 1 p hp
    have ha : entry (seg M (transJm1 M) (Lng M - 1)) 1 p
        = entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 p := by
      conv_lhs => rw [hsegeq]
      rw [entry_IncrFirstN_one]
    rw [← ha]; exact hb
  have hlastlt : Lng M - 1 - transJm1 M < Lng (seg M (transJm1 M) (Lng M - 1)) := by
    rw [hLNval]; omega
  have e1last : entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 (Lng M - 1 - transJm1 M)
      = entry M 1 (Lng M - 1) := by
    have heq : transJm1 M + (Lng M - 1 - transJm1 M) = Lng M - 1 := by omega
    rw [e1RN _ hlastlt, heq]
  have e1zero : entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 0 = entry M 1 (transJm1 M) := by
    have h := e1RN 0 hsegpos
    rwa [Nat.add_zero] at h
  -- combined component bound (against `M₁,ⱼ₁`)
  have hcomp : ∀ p ∈ PB t',
      leBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) p = true := by
    intro p hp
    have hb := hcomp0 p hp
    rw [hFN, e1last] at hb
    exact hb
  -- pin the body: `t' = t₂ +_B D_{M₁,ⱼ₁} 0`
  have hmarked : Marked M (transJm1 M) := by
    refine ⟨hM, ?_, leM⟩
    show adm M (Adm M (transJ0 M)) = true
    exact Adm_adm M (transJ0 M)
  have hMkTrans : Mark M (transJm1 M) = Trans (seg M (transJm1 M) (Lng M - 1)) :=
    Mark_Trans_repr M (transJm1 M) hmarked hR hmm1ltj1
  have hMkC2 : Mark M (transJm1 M) = transC2 M :=
    m_7_3_Mark_rightmost2 M hR hmono hJ1pos hT1ne
  have hTRedN : Trans (seg M (transJm1 M) (Lng M - 1))
      = Trans (Red (seg M (transJm1 M) (Lng M - 1))) := Trans_Red _ hsegT
  have hguardC2 : (transCondI M || transCondIII M || transCondV M) = true := by
    rw [hcond]; simp
  -- abstract reduction of `transC2Core` on the condV regime (avoids whnf on `transV`/`transT2`)
  have hcore : ∀ (v : ℕ∞) (t₂ : BT),
      transC2Core M v t₂ = Dprin v (addBT t₂ (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    intro v t₂
    simp only [transC2Core, lastIdx]
    rw [if_pos hguardC2]
  have hc2form : transC2 M
      = Dprin (transV M) (addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) :=
    hcore (transV M) (transT2 M)
  have hpin : Dprin (entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 0 : ℕ∞) t'
      = Dprin (transV M) (addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    rw [← hlead, ← hTRedN, ← hMkTrans, hMkC2, hc2form]
  have hteq : t' = addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) :=
    (Dprin_inj_nl hpin).2
  -- `t₂`'s components sit inside `t'`'s
  intro c hc
  have hc' : c ∈ PB t' := by
    rw [hteq, PB_addBT_app_nl]
    exact List.mem_append_left _ hc
  exact hcomp c hc'

/-! ## `notLD` 残差の放電（Isabelle `atx_notLD`, pss_wip.thy:86198） -/

/-- Isabelle `atx_notLD`（pss_wip.thy:86198）。前線 `t₂` の末尾 principal 頭は
`M₁,ⱼ₀` でない。末尾 principal は `t₂` の成分の一つなので、その頭は
`t2_component_bound_nl` により `M₁,ⱼ₁ = M₁,ⱼ₀ + 1 > M₁,ⱼ₀`（条件(V)）以上、
よって `M₁,ⱼ₀` に等しくない。 -/
theorem nadmC2L1NotLD_holds : NadmC2L1NotLD := by
  intro M hST hmono hcond hnadm ht2ne
  have hcomp := t2_component_bound_nl M hST hmono hcond hnadm
  -- last principal of `PB t₂` is a member
  have hpne : PB (transT2 M) ≠ [] := PB_ne_nil_of_ne_BZero_nl (transT2 M) ht2ne
  have hidx : (PB (transT2 M)).length - 1 < (PB (transT2 M)).length := by
    have := List.length_pos_of_ne_nil hpne; omega
  have hg : (PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero
      = (PB (transT2 M))[(PB (transT2 M)).length - 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
  have hmem : (PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero ∈ PB (transT2 M) := by
    rw [hg]; exact List.getElem_mem hidx
  -- bound the last principal's head from below by `M₁,ⱼ₁`
  have hlb := hcomp _ hmem
  obtain ⟨v, c, hpJ⟩ := PB_mem_Dprin_nl hmem
  rw [hpJ] at hlb
  have hvge : (entry M 1 (Lng M - 1) : ℕ∞) ≤ v := (leBT_Dprin0_iff_nl _ _ _).mp hlb
  -- condition (V): `M₁,ⱼ₀ + 1 = M₁,ⱼ₁`
  have hsucc : entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.2
  have hlt : entry M 1 (transJ0 M) < entry M 1 (Lng M - 1) := by omega
  have hltc : (entry M 1 (transJ0 M) : ℕ∞) < v := by
    have h1 : (entry M 1 (transJ0 M) : ℕ∞) < (entry M 1 (Lng M - 1) : ℕ∞) := by
      exact_mod_cast hlt
    exact lt_of_lt_of_le h1 hvge
  -- so the head `≠ M₁,ⱼ₀`
  rw [hpJ, bpHeadV_Dprin_nl, beq_eq_false_iff_ne]
  exact (ne_of_lt hltc).symm

#print axioms nadmC2L1NotLD_holds

end PSS
