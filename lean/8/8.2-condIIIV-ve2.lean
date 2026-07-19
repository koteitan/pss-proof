import «8».«8.2-condIIIV-deep4»
import «8».«8.2-condIIIV-capstone»

/-!
# §8.2 条件(II)/(IV) VE2 大域残差 `VE2Residual` の無条件討伐（最終の底 `EqdiagMlevel`）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分の VE2
  値方程式（一本目 `VE2goal`）。§8.2 の deep 連鎖
  （`8.2-condIIIV-VE234` → `-deep6` → `-deep5` → `-deep4`）は VE2 大域残差 `VE2Residual`
  （`8.2-condIIIV-VE34-assembly`）を、純幹脚 `VE2TrunkLeg_holds`（無条件）と非幹脚
  `VE2RegLeg`（`VE2RegPrefixReg` modulo）に分け、`VE2RegPrefixReg` を前置幾何
  `{VE2PrefixLastJoint（無条件）, VE2PrefixEqdiag}`、さらに `VE2PrefixEqdiag` を **ただ一本の
  M レベル残差 `EqdiagMlevel`**（`8.2-condIIIV-deep4`、Isabelle `vg2x_eqdiag_M` 92870 の結論）
  に還元した。本ファイルはその **最終残差 `EqdiagMlevel` を無条件で討伐**し、連鎖を合成して
  **`VE2Residual` を無条件で** 供給する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植）。
- Isabelle（`isabelle/layerB/pss_wip.thy`, `vg2x_eqdiag_M` 92870）の証明構造:
  最終枝ガード（`entry M 1 j₁' < entry M 0 j₁'`）と等 joint（`Joints M!(J₀-1) = Joints M!J₁`）の
  下で、`LastStep-1` 番目の枝頭が対角（行0 = 行1）であることを示す。
  - **HD0eq**: 等 joint から `RedCondA` の枝頭エッジ（`headEdge`, 各枝で
    `entry M 0 (Joints!J) + 1 = entry M 0 (FirstNodes!J)`）で row-0 first-node が一致。
  - **notInS**: `LastStep = Min S`（非対角枝の最小性、`vgx_LastStep_elsecase` の全域版
    `LastStep_find_min`）から `LastStep-1 ∉ S`、ゆえに枝頭で `row0 ≤ row1`（geComp）。
  - **ROW10**: 簡約形の係数不等式 `entry M 1 j ≤ entry M 0 j`（`reduced_coeff`, 6.6、
    **頭が (0,0) であることに依らず** `RedCondB` の「row-0 親なし ⟹ row0 = row1」だけで従う）
    から枝頭で `row1 ≤ row0`（leComp）。両者で `row0 = row1`（eqdiag）。
  - 枝頭↔成分の移送は `entry_FirstNodes_eq_component_mr`（6.5）。
- 依存 module: `8.2-condIIIV-deep4`（`EqdiagMlevel`／`VE2PrefixLastJoint_holds`／
  `VE2PrefixEqdiag_of_Mlevel`／`VE2RegPrefixReg_of_geom`／`VE2RegLeg_of_prefixReg`／
  `VE2TrunkLeg_holds`／`VE2Residual_of_legs`／`VE2Residual`／`LastStep`／`Br`/`Joints`/
  `FirstNodes`/`TrMax`/`entry`/`seg` と §6 公開補題 `reduced_coeff`/
  `entry_FirstNodes_eq_component_mr`/`RTPS_condAB`/`RedCondA_apply`/`Joints_nextR_FirstNodes`/
  `parent_eq_of_nextR0`/`mono_slice_next`/`FirstNodes_getD`/`Joints_getD`/`LastStep_lt_Lng_Br`
  を推移的に）、`8.2-condIIIV-capstone`（`condIIIVterminalSlice_of_assembly_cw`／
  `TspinAssemblyIH_tc`：consumer chain の bonus）。
- 状態: ✅ 完了（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  `EqdiagMlevel` を **無条件討伐** → 連鎖合成で **`VE2Residual` 無条件**。bonus として
  §8.2 命題の無条件形 `CondIIIVterminalSlice`（termination `condIIIVts` フィールド）を
  **STEP の単一残差 `TspinAssemblyIH_tc` のみ modulo** で供給（VE2 gap を閉塞）。
- Private suffix: `_v2`。
-/

namespace PSS

/-! ## 私的補助（suffix `_v2`）

`8.2-condIIIV-census-slice` の private 補題（`a1_FN_hasParent_cs2`/`a1_FN_lt_cs2`/
`headEdge_cs2`/`LastStep_find_min_cs2`）の再掲。いずれも公開 §6/§8.2 補題のみに依存する
（`TrMax_bound`/`mono_slice_next`/`FirstNodes_getD`/`Joints_nextR_FirstNodes`/
`RedCondA_apply`/`Joints_getD`/`LastStep` の定義）。 -/

/-- Isabelle `a1_FN_hasParent`: 枝 first node は row-0 に親を持つ。 -/
private theorem a1_FN_hasParent_v2 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    hasParent M 0 ((FirstNodes M).getD J 0) = true := by
  have htb := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hbr : Br M = [] := by simp [Br, heq]
    rw [hbr] at hJ; simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]; omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  exact hn.1

/-- Isabelle `a1_FN_lt`: 枝 first node は範囲内 `< Lng M`。 -/
private theorem a1_FN_lt_v2 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnx
  have h := hn0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- Isabelle `bgx_headedge`: 各枝 `J` で頭 joint の row-0 値 + 1 = first node の row-0 値。 -/
private theorem headEdge_v2 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (J : ℕ) (hJ : J < (Br M).length) :
    entry M 0 ((Joints M).getD J 0) + 1 = entry M 0 ((FirstNodes M).getD J 0) := by
  have hM : TPS M := RTPS_TPS M hR
  have hcondA : RedCondA M = true := (RTPS_condAB M hR).1
  have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    a1_FN_hasParent_v2 M J hM hmono hJ
  have hlt : (FirstNodes M).getD J 0 < Lng M := a1_FN_lt_v2 M J hM hmono hJ
  have hedge := RedCondA_apply M hcondA 0 ((FirstNodes M).getD J 0) (by omega) hlt hhas
  rw [Joints_getD M J hJ]
  exact hedge

/-- Isabelle `vgx_LastStep_elsecase` の全域版最小性: 非対角ガード下で `k < LastStep M` の
枝 `k` は `S`-述語（枝頭 row-0 が最終枝と一致し、かつ row-1 < row-0）を満たさない。 -/
private theorem LastStep_find_min_v2 (M : PS) (hBrne : Br M ≠ [])
    (hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0)
    (k : ℕ) (hk : k < LastStep M) :
    ¬ (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0
       ∧ entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0) := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  rintro ⟨heq0, hlt0⟩
  have hpk : (decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0)
             && decide (entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨heq0, hlt0⟩
  have hLSval : LastStep M
      = ((List.range (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD
            ((Br M).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval] at hk
  cases hfind : (List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
  | none =>
      simp only [hfind, Option.getD_none] at hk
      have hkmem : k ∈ List.range (Br M).length := List.mem_range.mpr (by omega)
      exact (List.find?_eq_none.mp hfind) k hkmem hpk
  | some c =>
      simp only [hfind, Option.getD_some] at hk
      have hf' : (List.range' 0 (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) = some c := by
        simpa using hfind
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 k (Nat.zero_le k) hk
      rw [hpk] at hmin
      simp at hmin

/-! ## `EqdiagMlevel` の無条件討伐（Isabelle `vg2x_eqdiag_M`, 92870）

最終枝ガード（`entry M 1 j₁' < entry M 0 j₁'`）と等 joint（`Joints M!(J₀-1) = Joints M!J₁`）の
下で、`J₀-1 = LastStep-1` 番目の枝頭が対角（行0 = 行1）。HD0eq（等 joint ⟹ row-0 first-node
一致）＋ notInS（`LastStep = Min S` から `LastStep-1 ∉ S`）＋ ROW10（`reduced_coeff`）で閉じる。 -/

/-- **Isabelle `vg2x_eqdiag_M` (layerB 92870) の逐語移植（無条件）**: `8.2-condIIIV-deep4` の
最終 VE2 残差 `EqdiagMlevel` を討伐する。`ROW10` は簡約係数 `reduced_coeff`（頭 (0,0) 非依存）
で内部供給し、`LastStep = Min S` の最小性は `LastStep_find_min_v2` で運ぶ。 -/
theorem eqdiagMlevel_holds : EqdiagMlevel := by
  intro M hMD hBrne hLS0 hguard heqJ
  obtain ⟨hR, hmono, _hdesc⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hKL : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  have hK1lt : LastStep M - 1 < (Br M).length := by omega
  have hJ1lt : (Br M).length - 1 < (Br M).length := by omega
  -- 枝頭エッジ（row-0 first node = joint row-0 + 1）
  have hedgeK1 := headEdge_v2 M hR hmono (LastStep M - 1) hK1lt
  have hedgeJ1 := headEdge_v2 M hR hmono ((Br M).length - 1) hJ1lt
  -- HD0eq: 等 joint から row-0 first node 一致
  have hjoint : entry M 0 ((Joints M).getD (LastStep M - 1) 0)
              = entry M 0 ((Joints M).getD ((Br M).length - 1) 0) := by rw [heqJ]
  have hHD0 : entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0)
            = entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) := by omega
  -- 枝頭↔成分の移送
  have h0J1 := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1lt
  have h1J1 := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 1 hM hJ1lt
  have h0K1 := entry_FirstNodes_eq_component_mr M (LastStep M - 1) 0 hM hK1lt
  have h1K1 := entry_FirstNodes_eq_component_mr M (LastStep M - 1) 1 hM hK1lt
  -- 最終枝頭ガード（成分レベル）と非対角性
  have hgtComp : entry ((Br M).getD ((Br M).length - 1) []) 1 0
               < entry ((Br M).getD ((Br M).length - 1) []) 0 0 := by
    rw [← h0J1, ← h1J1]; exact hguard
  have hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
           ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0 := by omega
  -- notInS: LastStep-1 は最小クラスタ S に属さない
  have hnotInS := LastStep_find_min_v2 M hBrne hnd (LastStep M - 1) (by omega)
  -- compHD0: 成分レベルの row-0 一致
  have hcompHD0 : entry ((Br M).getD ((Br M).length - 1) []) 0 0
                = entry ((Br M).getD (LastStep M - 1) []) 0 0 := by
    rw [← h0J1, ← h0K1]; exact hHD0.symm
  -- geComp: notInS から枝頭で row0 ≤ row1
  have hgeComp : entry ((Br M).getD (LastStep M - 1) []) 0 0
               ≤ entry ((Br M).getD (LastStep M - 1) []) 1 0 := by
    by_contra hlt
    exact hnotInS ⟨hcompHD0, by omega⟩
  -- leComp: ROW10（reduced_coeff）から枝頭で row1 ≤ row0
  have hrow10 : entry M 1 ((FirstNodes M).getD (LastStep M - 1) 0)
              ≤ entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0) :=
    reduced_coeff M hR ((FirstNodes M).getD (LastStep M - 1) 0)
      (a1_FN_lt_v2 M (LastStep M - 1) hM hmono hK1lt)
  have hleComp : entry ((Br M).getD (LastStep M - 1) []) 1 0
               ≤ entry ((Br M).getD (LastStep M - 1) []) 0 0 := by
    rw [← h0K1, ← h1K1]; exact hrow10
  -- 目標: entry M 0 (FN!(LastStep-1)) = entry M 1 (FN!(LastStep-1))
  rw [h0K1, h1K1]; omega

/-! ## `VE2Residual` の無条件討伐（deep 連鎖の合成）

`EqdiagMlevel`（本ファイル）→ `VE2PrefixEqdiag`（`VE2PrefixEqdiag_of_Mlevel`, deep4）
→ `VE2RegPrefixReg`（`VE2RegPrefixReg_of_geom` に `VE2PrefixLastJoint_holds` と併せて, deep5）
→ `VE2RegLeg`（`VE2RegLeg_of_prefixReg`, deep6）→ `VE2Residual`（`VE2Residual_of_legs` に
`VE2TrunkLeg_holds` と併せて, VE234）。すべて無条件。 -/

/-- **VE2 大域残差 `VE2Residual`（`8.2-condIIIV-VE34-assembly`）の無条件討伐**。 -/
theorem ve2Residual_holds : VE2Residual :=
  VE2Residual_of_legs VE2TrunkLeg_holds
    (VE2RegLeg_of_prefixReg
      (VE2RegPrefixReg_of_geom VE2PrefixLastJoint_holds
        (VE2PrefixEqdiag_of_Mlevel eqdiagMlevel_holds)))

/-! ## Bonus — consumer chain: §8.2 condIIIV 終切片フィールドを STEP 残差一本 modulo で供給

`8.2-condIIIV-capstone` の `condIIIVterminalSlice_of_assembly_cw` は
`TspinAssemblyIH_tc → VE2Residual → CondIIIVterminalSlice` だった。VE2 gap を本ファイルの
`ve2Residual_holds` で閉塞し、§8.2 命題の無条件形 `CondIIIVterminalSlice`（termination の
`condIIIVts` フィールド）を **STEP の単一残差 `TspinAssemblyIH_tc` のみ** modulo で供給する。 -/

/-- **§8.2 condIIIV 終切片フィールドを STEP 残差 `TspinAssemblyIH_tc` 一本で供給**（VE2 gap 閉塞）。 -/
theorem condIIIVterminalSlice_of_assembly_ve2
    (hAsm : TspinAssemblyIH_tc) : CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_assembly_cw hAsm ve2Residual_holds

/-! ## 転記の数値検証（`EqdiagMlevel` の量化域が非空・結論が成立）

length-5 の全数走査（`python`/kimina `decide`）で domain 12 例・結論失敗 0 例・非零頭 0 例。
以下は最小 witness `M = (0,0)(1,1)(1,1)(1,0)`（`DT_PS`・`Br ≠ []`・`0 < LastStep`・等 joint）で
`EqdiagMlevel` の含意（domain ⟹ 対角）が `decide` で成立することの回帰テスト。 -/

-- witness が `EqdiagMlevel` の domain に属する（量化域が非空）。
#guard decide (DTPS [(0,0),(1,1),(1,1),(1,0)] ∧ Br [(0,0),(1,1),(1,1),(1,0)] ≠ [] ∧
  0 < LastStep [(0,0),(1,1),(1,1),(1,0)] ∧
  entry [(0,0),(1,1),(1,1),(1,0)] 1
      ((FirstNodes [(0,0),(1,1),(1,1),(1,0)]).getD ((Br [(0,0),(1,1),(1,1),(1,0)]).length - 1) 0)
    < entry [(0,0),(1,1),(1,1),(1,0)] 0
      ((FirstNodes [(0,0),(1,1),(1,1),(1,0)]).getD ((Br [(0,0),(1,1),(1,1),(1,0)]).length - 1) 0) ∧
  (Joints [(0,0),(1,1),(1,1),(1,0)]).getD (LastStep [(0,0),(1,1),(1,1),(1,0)] - 1) 0
    = (Joints [(0,0),(1,1),(1,1),(1,0)]).getD ((Br [(0,0),(1,1),(1,1),(1,0)]).length - 1) 0) = true

-- witness で対角結論（`entry M 0 (FN!(LastStep-1)) = entry M 1 (FN!(LastStep-1))`）が成立。
#guard decide (entry [(0,0),(1,1),(1,1),(1,0)] 0
      ((FirstNodes [(0,0),(1,1),(1,1),(1,0)]).getD (LastStep [(0,0),(1,1),(1,1),(1,0)] - 1) 0)
    = entry [(0,0),(1,1),(1,1),(1,0)] 1
      ((FirstNodes [(0,0),(1,1),(1,1),(1,0)]).getD (LastStep [(0,0),(1,1),(1,1),(1,0)] - 1) 0)) = true

#print axioms eqdiagMlevel_holds
#print axioms ve2Residual_holds
#print axioms condIIIVterminalSlice_of_assembly_ve2

end PSS
