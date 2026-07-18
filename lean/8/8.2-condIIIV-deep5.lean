import «8».«8.2-condIIIV-deep6»
import «8».«8.2-strongmono-slice»

/-!
# §8.2 条件(II)/(IV) VE34 deep5 残差の底（VE2 非幹前置体制 `VE2RegPrefixReg` の上部構造）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。`8.2-condIIIV-deep6` の
  `condIIIVterminalSlice_of_deep5` は `condIIIVts` フィールド（`CondIIIVterminalSlice`）を
  **五つの体制別残差** `{VE2RegPrefixReg, VE3Base, VE3Step, VE4Base, VE4Step}` に還元した。
  本ファイルはその筆頭 `VE2RegPrefixReg`（VE2 非幹脚の前置体制、Isabelle `vg2x_cfbx_reg`）の
  **上部構造を無条件で** 討伐する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`、`vg2x_cfbx_reg` 92971）の証明構造:
  前置辞 `N = seg M 0 (FirstNodes M ! LastStep - 1)`（`m₁ = FirstNodes M ! LastStep - 1`）に対し
  `VEReg (Joints M ! (Br.length-1)) N` を示す。本ファイルは以下を **無条件で** 供給する:
  - `N ∈ DT_PS`（Isabelle `vg2x_N_DT`）: 強単項切片 `strongmono_slice` を、幹対角の上に
    ある切片端 `0 < b ≤ Lng M - 1`（`b = FirstNodes M ! LastStep - 1`、下限は幹閉包
    `FirstNodes_TrMax_Joints`＋ガード `0 < j₀' < TrMax`、上限は枝左端有界 `FN_lt_d5`）に
    適用して得る。これで `RTPS N`／`monoT N`／`descendingB (Br N)` が落ちる。
  - joint 単調性 `jle : Joints M ! (Br.length-1) ≤ Joints M ! (LastStep-1)`（`FirstNodes_Joints_mono`）。
  - 二分岐（`Joints M ! (Br.length-1) < / = Joints M ! (LastStep-1)`）で `VEReg` の選言を組む。
  深い部分（Isabelle `vg2x_prefix_geom`/`vg2x_prefix_joints` の枝数・最終 joint 移送、
  `vg2x_eqdiag_M` の `ROW10` 依存の対角化）は名前付き残差 `VE2PrefixLastJoint`／
  `VE2PrefixEqdiag` に露出する。
- 帰結: `condIIIVts` フィールドを **`{VE2PrefixLastJoint, VE2PrefixEqdiag, VE3Base, VE3Step,
  VE4Base, VE4Step}`** から供給する（`condIIIVterminalSlice_of_deep4`）。VE2 非幹脚は
  DT 所属・joint 単調・選言組立を無条件討伐し、残る二残差は純粋な前置幾何＋対角化
  （いずれも本ファイルの射程外＝Isabelle の別 surgery ブロック）。
- 依存 module: `8.2-condIIIV-deep6`（`VE2RegPrefixReg`／`condIIIVterminalSlice_of_deep5`／
  `VE3Base`/`VE3Step`/`VE4Base`/`VE4Step`／`VEReg`／`VEj1p`／`LastStep`／`Br`/`Joints`/
  `FirstNodes`/`TrMax`/`entry`/`seg` を推移的に）、`8.2-strongmono-slice`（`strongmono_slice`）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`VE2RegPrefixReg` の上部構造を **無条件討伐**、残差は
  前置幾何 `VE2PrefixLastJoint`（枝数・最終 joint 移送）と `VE2PrefixEqdiag`（`ROW10` 対角化）。
-/

namespace PSS

/-! ## 私的補助（suffix `_d5`）

枝左端有界 `FN_lt_d5`（Isabelle `a1_FN_lt`）。入口 `FN_lt_v34` の再掲。 -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める。 -/
private theorem leR0_bounds_d5 (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, pss_mechanized 33186）。 -/
private theorem FN_lt_d5 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_d5 M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-! ## 前置幾何の名前付き残差（Isabelle `vg2x_prefix_*` / `vg2x_eqdiag_M`）

`N = seg M 0 (FirstNodes M ! LastStep - 1)` の枝構造は Isabelle の `vg2x_prefix_geom`
（枝数 `Lng (Br N) = LastStep M`）／`vg2x_prefix_joints`（最終 joint の移送）で確立される。
本ファイルはその二事実（`Br N ≠ []` と最終 joint 移送）を一つの残差 `VE2PrefixLastJoint` に
束ねる。対角化（`vg2x_eqdiag_M`、`ROW10` 依存）は `VE2PrefixEqdiag` に露出する。 -/

/-- **前置枝・最終 joint 残差**（Isabelle `vg2x_prefix_LngBr` 92673 + `vg2x_prefix_joints`
92780）: `0 < LastStep M` の非幹脚で、前置辞 `N = seg M 0 (FirstNodes M ! LastStep - 1)` の
枝は非空、かつその最終 joint は `M` の `LastStep-1` 番目の joint に一致する。 -/
def VE2PrefixLastJoint : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] → 0 < LastStep M →
    Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) ≠ [] ∧
    (Joints (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).getD
        ((Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length - 1) 0
      = (Joints M).getD (LastStep M - 1) 0

/-- **前置対角化残差**（Isabelle `vg2x_eqdiag_M` 92870、`ROW10` 依存）: `0 < LastStep M` の
非幹脚で、最終枝ガード（行1 < 行0）と最終 joint の一致 `Joints M ! (LastStep-1) =
Joints M ! (Br.length-1)` の下で、前置辞 `N` の最終枝左端は対角（行0 = 行1）。
`vg2x_prefix_entry`（entry 移送）も本残差に吸収する。 -/
def VE2PrefixEqdiag : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] → 0 < LastStep M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    (Joints M).getD (LastStep M - 1) 0 = (Joints M).getD ((Br M).length - 1) 0 →
    entry (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) 0
        ((FirstNodes (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).getD
          ((Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length - 1) 0)
      = entry (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) 1
        ((FirstNodes (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).getD
          ((Br (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))).length - 1) 0)

/-! ## `VE2RegPrefixReg` の上部構造（Isabelle `vg2x_cfbx_reg`, 92971）

前置幾何残差 `{VE2PrefixLastJoint, VE2PrefixEqdiag}` から、VE2 非幹脚の前置体制
`VE2RegPrefixReg`（`8.2-condIIIV-deep6`）を **無条件で** 供給する。DT 所属
（`strongmono_slice`）・joint 単調（`FirstNodes_Joints_mono`）・選言組立は本ファイルで討伐。 -/

/-- **Isabelle `vg2x_cfbx_reg` (layerB 92971) の上部構造**: 前置幾何残差
`{VE2PrefixLastJoint, VE2PrefixEqdiag}` から `VE2RegPrefixReg` を放出する。 -/
theorem VE2RegPrefixReg_of_geom
    (hLJ : VE2PrefixLastJoint) (hEq : VE2PrefixEqdiag) : VE2RegPrefixReg := by
  intro M hMD hBrne hj0pos hj0lt hguard hLS0
  obtain ⟨hR, hmono, _hdesc⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hKL : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  -- FirstNodes bounds at K = LastStep M
  have hTF := FirstNodes_TrMax_Joints M (LastStep M) hM hmono hKL
  have hFNlt : (FirstNodes M).getD (LastStep M) 0 < Lng M := FN_lt_d5 M (LastStep M) hM hmono hKL
  have hbLe : (FirstNodes M).getD (LastStep M) 0 - 1 ≤ Lng M - 1 := by omega
  have hb0 : 0 < (FirstNodes M).getD (LastStep M) 0 - 1 := by
    -- b ≥ TrMax M, and TrMax M ≥ 2 from the guard 0 < j₀' < TrMax
    omega
  -- N ∈ DT_PS via strongmono_slice (Isabelle vg2x_N_DT)
  have hND : DTPS (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) :=
    strongmono_slice M 0 ((FirstNodes M).getD (LastStep M) 0 - 1) hMD hb0 hbLe (Nat.zero_le _)
  obtain ⟨hNR, hNmono, hNdesc⟩ := (DTPS_iff _).mp hND
  -- geometry residuals: Br N ≠ [] and last-joint transport
  obtain ⟨hBrNne, hJtrans⟩ := hLJ M hMD hBrne hLS0
  -- joint monotonicity: Joints M!(Br-1) ≤ Joints M!(LastStep-1)
  have hKm1J1 : LastStep M - 1 < (Br M).length - 1 := by omega
  have hJ1lt : (Br M).length - 1 < (Br M).length := by omega
  have hjle : (Joints M).getD ((Br M).length - 1) 0 ≤ (Joints M).getD (LastStep M - 1) 0 :=
    (FirstNodes_Joints_mono M (LastStep M - 1) ((Br M).length - 1) hM hmono hKm1J1 hJ1lt).2.1
  -- assemble VEReg
  refine ⟨hNR, hNmono, hBrNne, ?_⟩
  by_cases hlt : (Joints M).getD ((Br M).length - 1) 0 < (Joints M).getD (LastStep M - 1) 0
  · -- left disjunct
    left
    rw [hJtrans]
    exact hlt
  · -- right disjunct (equal joints)
    right
    have heqJ : (Joints M).getD (LastStep M - 1) 0 = (Joints M).getD ((Br M).length - 1) 0 := by omega
    refine ⟨?_, ?_, hNdesc⟩
    · rw [hJtrans]; exact heqJ.symm
    · show entry (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) 0
            (VEj1p (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))
          = entry (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) 1
            (VEj1p (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))
      unfold VEj1p
      exact hEq M hMD hBrne hLS0 hguard heqJ

/-! ## 四残差版キャップストーン

`VE2RegPrefixReg_of_geom` を `8.2-condIIIV-deep6` の五残差版キャップストーン
`condIIIVterminalSlice_of_deep5` に差し込み、`condIIIVts` フィールドの無条件形
`CondIIIVterminalSlice` を **六つの残差** `{VE2PrefixLastJoint, VE2PrefixEqdiag, VE3Base,
VE3Step, VE4Base, VE4Step}` から供給する（VE2 非幹脚の DT 所属・joint 単調・選言組立は
本ファイルで無条件討伐済み、残る VE2 二残差は純幾何＋対角化）。 -/

/-- **六残差版キャップストーン**: `condIIIVts` フィールドを
`{VE2PrefixLastJoint, VE2PrefixEqdiag, VE3Base, VE3Step, VE4Base, VE4Step}` から供給する。 -/
theorem condIIIVterminalSlice_of_deep4
    (hLJ : VE2PrefixLastJoint) (hEq : VE2PrefixEqdiag)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deep5
    (VE2RegPrefixReg_of_geom hLJ hEq) hV3b hV3s hV4b hV4s

/-- 六残差から condII 停止性フィールド `CondII_masterCF`（`8.3-TransCondII-engine`）を
供給する（`8.2-condIIIV-deep6` の `condII_masterCF_of_deep5` へ橋渡し）。 -/
theorem condII_masterCF_of_deep4
    (hLJ : VE2PrefixLastJoint) (hEq : VE2PrefixEqdiag)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondII_masterCF :=
  condII_masterCF_of_deep5
    (VE2RegPrefixReg_of_geom hLJ hEq) hV3b hV3s hV4b hV4s

/-! ## 転記の数値検証（前置幾何残差の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`（`oper` 展開の標準形）は `DT_PS`・
`Br ≠ []`・`0 < LastStep`（`LastStep = 1`、枝数 2、非幹脚の同一 joint 二枝構造）に属し、
非幹脚 `VE2PrefixLastJoint`/`VE2PrefixEqdiag` の量化域が非空であることを保証する。 -/

-- 非幹脚（`0 < LastStep`）の witness が DT_PS ホストに属する（残差の量化域が非空）。
#guard decide (DTPS [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ∧
  Br [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ≠ [] ∧
  0 < LastStep [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)]) = true

#print axioms VE2RegPrefixReg_of_geom
#print axioms condIIIVterminalSlice_of_deep4
#print axioms condII_masterCF_of_deep4

end PSS
