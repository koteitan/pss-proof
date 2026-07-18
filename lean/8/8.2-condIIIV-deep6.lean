import «8».«8.2-condIIIV-VE234»
import «8».«8.2-condV-VE-close»

/-!
# §8.2 条件(II)/(IV) VE34 の六体制別残差の底（VE2 の二脚）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。キャップストーン
  `8.2-condIIIV-VE234` の `condIIIVterminalSlice_of_deep6` は `condIIIVts` フィールド
  （`CondIIIVterminalSlice`）を**六つの体制別残差**
  `{VE2TrunkLeg, VE2RegLeg, VE3Base, VE3Step, VE4Base, VE4Step}` に還元した。本ファイルは
  その中で **最も浅い二脚（VE2 の二脚）** を攻める。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）:
  - **VE2 純幹脚**（`LastStep M = 0`）: `vg2x_VE2_trunk` (93069)。`m₁ = FirstNodes M ! 0 - 1
    = TrMax M`。`seg M 0 (TrMax M)` は全幹の対角列で、その終切片値は幹の閉形式
    `crg_slice_value_of_trunk` (91399) で固定される。本ファイルはこれを **無条件で** 閉じる
    （`VE2TrunkLeg_holds`）。幹の対角性は `trunk_entries_offset`＋`RTPS_mono_head_eq`、
    `Trans` は `diagSeq_Trans`。
  - **VE2 非幹脚**（`0 < LastStep M`）: `vg2x_VE2_reg` (93037)。`vgx_VE2_of_reg` (91332) は
    条件(V) の VE 閉形式 `vcx_VE_all` (77076、Lean 側 `vcx_VE_all` は**無条件で公開済み**) を
    `N = seg M 0 m₁` に適用し、`seg_of_seg` で終切片を移送する。本ファイルはその **移送部分を
    無条件で** 供給する（`VE2RegLeg_of_prefixReg`）。深い部分（`N = seg M 0 m₁` が条件(V) の
    体制 `VEReg j₀' N` に属すること＝Isabelle `vg2x_cfbx_reg` の前置枝構造 `vg2x_prefix_*`／
    `vg2x_N_DT`／`vgx_LastStep_lt_of_guard` の連鎖）は名前付き残差 `VE2RegPrefixReg` に露出する。
- 帰結: `condIIIVts` フィールドを**六残差から五残差**
  `{VE2RegPrefixReg, VE3Base, VE3Step, VE4Base, VE4Step}` へ絞る（VE2 純幹脚は無条件討伐、
  VE2 非幹脚は前置体制残差 modulo で供給）。
- 依存 module: `8.2-condIIIV-VE234`（六残差 Prop・`condIIIVterminalSlice_of_deep6`・
  `VE2goal`/`VE2TrunkLeg`/`VE2RegLeg`/`VE3Base`/… を推移的に）、`8.2-condV-VE-close`
  （`vcx_VE_all`／`VEReg`／`VEeq`）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。VE2 純幹脚 `VE2TrunkLeg_holds` を **無条件討伐**、
  VE2 非幹脚 `VE2RegLeg_of_prefixReg` を前置体制残差 `VE2RegPrefixReg` modulo で供給。
  残差は五つ（VE2 の前置体制＋VE3/VE4 の BASE/STEP、いずれも本ファイルの射程外＝
  §7.4 頭シフト readback surgery、または `vg2x_prefix_*` 前置枝構造）。
-/

namespace PSS

/-! ## 幹の対角切片（Isabelle `crg_slice_value_of_trunk` の底、91399）

`M ∈ RT_PS` の幹（`j ≤ TrMax M`）は対角列: `entry M c j = entry M 1 0 + j`
（`trunk_entries_offset`＋`RTPS_mono_head_eq`）。ゆえに幹の切片 `seg M a (TrMax M)`
（`a ≤ TrMax M`）は対角列 `diagSeq (u+a) (u+TrMax M)`（`u = entry M 1 0`）。 -/

/-- 幹の切片は対角列。Isabelle `crg_slice_value_of_trunk` の `Xeq`/`segeq` に対応する。 -/
private theorem trunk_seg_diagSeq_d6 (M : PS) (a : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hhead : entry M 0 0 = entry M 1 0)
    (ha : a ≤ TrMax M) :
    seg M a (TrMax M) = diagSeq (entry M 1 0 + a) (entry M 1 0 + TrMax M) := by
  apply List.ext_getElem
  · -- 長さ一致
    show Lng (seg M a (TrMax M)) = Lng (diagSeq (entry M 1 0 + a) (entry M 1 0 + TrMax M))
    rw [length_seg]
    simp only [diagSeq, List.length_map, List.length_range']
    omega
  · intro i hiS _
    have hiL : i < Lng (seg M a (TrMax M)) := hiS
    have hilt : i < TrMax M + 1 - a := by
      have := hiL; rw [length_seg] at this; omega
    have hai : a + i ≤ TrMax M := by omega
    have hoff := trunk_entries_offset M hM hA (a + i) hai
    have he0 : entry (seg M a (TrMax M)) 0 i = entry M 1 0 + (a + i) := by
      rw [entry_seg M a (TrMax M) 0 i hiL, hoff.1, hhead]
    have he1 : entry (seg M a (TrMax M)) 1 i = entry M 1 0 + (a + i) := by
      rw [entry_seg M a (TrMax M) 1 i hiL, hoff.2]
    have hSi : (seg M a (TrMax M))[i] =
        (entry (seg M a (TrMax M)) 0 i, entry (seg M a (TrMax M)) 1 i) := by
      have h0 : entry (seg M a (TrMax M)) 0 i = (seg M a (TrMax M))[i].1 := by
        simp [entry, List.getElem?_eq_getElem hiL]
      have h1 : entry (seg M a (TrMax M)) 1 i = (seg M a (TrMax M))[i].2 := by
        simp [entry, List.getElem?_eq_getElem hiL]
      rw [h0, h1]
    rw [hSi, he0, he1]
    simp only [diagSeq, List.getElem_map, List.getElem_range', Prod.mk.injEq]
    omega

/-- 幹の切片 `seg M a (TrMax M)`（`a < TrMax M`）の `Trans` の頭内部項は
`D_{u+TrMax M} 0`（`u = entry M 1 0`）。切片の左端 `a` に依らず一定。 -/
private theorem bpHeadT_trunk_seg_d6 (M : PS) (a : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hhead : entry M 0 0 = entry M 1 0)
    (ha : a < TrMax M) :
    bpHeadT (Trans (seg M a (TrMax M)))
      = Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero := by
  rw [trunk_seg_diagSeq_d6 M a hM hA hhead (le_of_lt ha)]
  rw [diagSeq_Trans (entry M 1 0 + a) (entry M 1 0 + TrMax M) (by omega)]
  rfl

/-! ## VE2 純幹脚（Isabelle `vg2x_VE2_trunk`, 93069）

`LastStep M = 0` では `m₁ = FirstNodes M ! 0 - 1 = TrMax M`。両切片
`seg M j₀' (TrMax M)` と `seg M 0 (TrMax M)` はどちらも幹の対角切片なので、
その `bpHeadT (Trans …)` は共通の `D_{u+TrMax M} 0` に等しい。 -/

/-- **Isabelle `vg2x_VE2_trunk` (layerB 93069) の逐語移植（無条件）**: 純幹接頭辞
（`LastStep M = 0`）での VE2 値方程式。 -/
theorem VE2TrunkLeg_holds : VE2TrunkLeg := by
  intro M hMD hBrne hj0pos hj0lt _hguard hLS0
  obtain ⟨hR, hmono, _hdesc⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  have hA : RedCondA M = true := (RTPS_condAB M hR).1
  have hhead : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  -- `m₁ = FirstNodes M ! 0 - 1 = TrMax M`
  have hm1 : (FirstNodes M).getD (LastStep M) 0 - 1 = TrMax M := by
    rw [hLS0, FirstNodes_getD M 0 hBrpos]
    have hs0 : (IdxSum (Br M)).getD 0 0 = 0 := by
      rw [idxSum_getD (Br M) 0 (Nat.zero_le _)]; simp
    omega
  have hTrpos : 0 < TrMax M := lt_trans hj0pos hj0lt
  unfold VE2goal
  rw [hm1,
    bpHeadT_trunk_seg_d6 M ((Joints M).getD ((Br M).length - 1) 0) hM hA hhead hj0lt,
    bpHeadT_trunk_seg_d6 M 0 hM hA hhead hTrpos]

/-! ## VE2 非幹脚の値移送（Isabelle `vgx_VE2_of_reg`, 91332）

`0 < LastStep M` では `m₁ = FirstNodes M ! (LastStep M) - 1`。`N = seg M 0 m₁` が
条件(V) の体制 `VEReg j₀' N` に属せば、条件(V) の VE 閉形式 `vcx_VE_all`（無条件）が
`VEeq j₀' N`＝`bpHeadT (Trans (seg N j₀' (Lng N - 1))) = bpHeadT (Trans N)` を与える。
`Lng N - 1 = m₁` かつ `seg N j₀' (Lng N - 1) = seg M j₀' m₁`（`seg_of_seg`）なので、
これはちょうど VE2goal M。前置体制 `VEReg j₀' N` の確立（Isabelle `vg2x_cfbx_reg`）は
本ファイルの射程外で名前付き残差に露出する。 -/

/-- **VE2 非幹前置体制残差**（Isabelle `vg2x_cfbx_reg` 92971 の結論）: `0 < LastStep M`
の非幹脚で、接頭辞 `N = seg M 0 (FirstNodes M ! LastStep M - 1)` が最終 joint `j₀'` を
`m`-パラメータとする条件(V) の体制 `VEReg` に属する。Isabelle では前置枝構造
`vg2x_prefix_LngBr`/`vg2x_prefix_joints`/`vg2x_prefix_entry`/`vg2x_N_DT`/
`vgx_LastStep_lt_of_guard`/`vg2x_eqdiag_M` の連鎖で確立される。 -/
def VE2RegPrefixReg : Prop :=
  ∀ M : PS, DTPS M → Br M ≠ [] →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
    0 < LastStep M →
    VEReg ((Joints M).getD ((Br M).length - 1) 0)
      (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))

/-- **Isabelle `vgx_VE2_of_reg` (layerB 91332) の逐語移植**: 前置体制残差
`VE2RegPrefixReg` から VE2 非幹脚 `VE2RegLeg` を放出する。条件(V) の VE 閉形式
`vcx_VE_all`（無条件）を `N = seg M 0 m₁` に適用し、`seg_of_seg` で終切片を移送する。 -/
theorem VE2RegLeg_of_prefixReg (hreg : VE2RegPrefixReg) : VE2RegLeg := by
  intro M hMD hBrne hj0pos hj0lt hguard hLS0
  unfold VE2goal
  set m₁ := (FirstNodes M).getD (LastStep M) 0 - 1 with hm1def
  set j₀' := (Joints M).getD ((Br M).length - 1) 0 with hj0def
  set N := seg M 0 m₁ with hNdef
  have hVEReg : VEReg j₀' N := hreg M hMD hBrne hj0pos hj0lt hguard hLS0
  have hVE : VEeq j₀' N := vcx_VE_all j₀' N hVEReg
  -- `Lng N - 1 = m₁`
  have hLN1 : Lng N - 1 = m₁ := by
    rw [hNdef, length_seg]; omega
  -- `seg N j₀' (Lng N - 1) = seg M j₀' m₁`
  have hcomp : seg N j₀' (Lng N - 1) = seg M j₀' m₁ := by
    rw [hLN1, hNdef, seg_of_seg_68 M 0 m₁ j₀' m₁ (Nat.zero_le _) (by omega)]
    simp
  unfold VEeq at hVE
  rw [hcomp] at hVE
  -- VE2goal M = `bpHeadT (Trans (seg M j₀' m₁)) = bpHeadT (Trans N)`
  exact hVE

/-! ## 五残差版キャップストーン

VE2 の純幹脚は無条件討伐（`VE2TrunkLeg_holds`）、非幹脚は前置体制残差
`VE2RegPrefixReg` modulo で供給（`VE2RegLeg_of_prefixReg`）。これらを
`8.2-condIIIV-VE234` の六残差版キャップストーン `condIIIVterminalSlice_of_deep6` に
差し込み、`condIIIVts` フィールドの無条件形 `CondIIIVterminalSlice` を**五つの残差**
`{VE2RegPrefixReg, VE3Base, VE3Step, VE4Base, VE4Step}` ちょうどに絞る。 -/

/-- **五残差版キャップストーン**: `condIIIVts` フィールド（`CondIIIVterminalSlice`）を
五残差 `{VE2RegPrefixReg, VE3Base, VE3Step, VE4Base, VE4Step}` から供給する。VE2 の二脚は
本ファイルで討伐（純幹）／前置体制残差へ還元（非幹）済み。 -/
theorem condIIIVterminalSlice_of_deep5
    (hV2r : VE2RegPrefixReg)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deep6
    VE2TrunkLeg_holds (VE2RegLeg_of_prefixReg hV2r)
    hV3b hV3s hV4b hV4s

/-- 五残差から condII 停止性フィールド `CondII_masterCF`（`8.3-TransCondII-engine`）を
供給する（`8.2-condIIIV-VE234` の `condII_masterCF_of_deep6` へ橋渡し）。 -/
theorem condII_masterCF_of_deep5
    (hV2r : VE2RegPrefixReg)
    (hV3b : VE3Base) (hV3s : VE3Step)
    (hV4b : VE4Base) (hV4s : VE4Step) :
    CondII_masterCF :=
  condII_masterCF_of_deep6
    VE2TrunkLeg_holds (VE2RegLeg_of_prefixReg hV2r)
    hV3b hV3s hV4b hV4s

/-! ## 転記の数値検証（VE2 純幹脚の regime が非空）

標準 witness `M = (0,0)(1,1)(2,2)(2,0)` は `DT_PS`・`Br ≠ []`・`LastStep = 0`
（純幹脚 `VE2TrunkLeg` の量化域）に属し、かつ最終 joint `j₀' = 1` が `0 < 1 < 2 = TrMax`
（`hj0pos`/`hj0lt`）を満たす。 -/

-- VE2 純幹脚の regime（`LastStep = 0` かつガード regime）が非空。
#guard decide (DTPS [(0,0),(1,1),(2,2),(2,0)] ∧ Br [(0,0),(1,1),(2,2),(2,0)] ≠ [] ∧
  LastStep [(0,0),(1,1),(2,2),(2,0)] = 0 ∧
  0 < (Joints [(0,0),(1,1),(2,2),(2,0)]).getD ((Br [(0,0),(1,1),(2,2),(2,0)]).length - 1) 0 ∧
  (Joints [(0,0),(1,1),(2,2),(2,0)]).getD ((Br [(0,0),(1,1),(2,2),(2,0)]).length - 1) 0
    < TrMax [(0,0),(1,1),(2,2),(2,0)]) = true

#print axioms VE2TrunkLeg_holds
#print axioms VE2RegLeg_of_prefixReg
#print axioms condIIIVterminalSlice_of_deep5
#print axioms condII_masterCF_of_deep5

end PSS
