import «8».«8.2-condIIIV-deep4»

/-!
# §8.2 条件(II)/(IV) VE34 deep3 残差の底（M レベル対角化残差 `EqdiagMlevel` の無条件討伐）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分。
  `8.2-condIIIV-deep4` の `condIIIVterminalSlice_of_deep3` は `condIIIVts` フィールド
  （`CondIIIVterminalSlice`）を **五つの残差** `{EqdiagMlevel, VE3Base, VE3Step, VE4Base,
  VE4Step}` に還元した。本ファイルは筆頭の M レベル対角化残差 `EqdiagMlevel`
  （Isabelle `vg2x_eqdiag_M` 92870 の結論、`ROW10`＋`LastStep`=Min 特徴付けを吸収した形）を
  **無条件で討伐** する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）:
  - `vg2x_eqdiag_M` (92870): 等 joint の下で `LastStep-1` 番目の枝頭は対角。証明の三本柱:
    ① `HD0eq`（等 joint ⇒ 等 row-0 枝左端値、`RedCondA`: 親+1=枝左端）
    ② `LastStep = Min S` ゆえ `LastStep-1 ∉ S`（`vgx_LastStep_elsecase`）。Lean の全域的
       `LastStep`（`find?`＋既定値 `J₁`）では、非対角ガード下で `find?` の最小性
       （`List.find?_range'_eq_some` / `List.find?_eq_none`）に帰着する。
    ③ `ROW10`（枝頭 row-1 ≤ row-0 の不変量）。Isabelle では名前付き仮説だが、一般の
       `vg3x_row1_le_row0`（簡約列で全列 row-1 ≤ row-0）から落ちる。Lean では既存の公開
       補題 **`reduced_coeff`**（`RTPS M ⇒ entry M 1 j ≤ entry M 0 j`, §6.6）が同値。
  - `②` の `LastStep-1 ∉ S`：`HD0eq` を成分レベルに落とすと `S` の第一条件（同 row-0 枝頭）が
    成立するので、`LastStep-1 < LastStep = min S` が第三条件（row-1 < row-0）を否定し、
    `row-0 ≤ row-1`。`③` の逆向き `row-1 ≤ row-0` と合わせて等号。
- 帰結: `condIIIVts` フィールドを **四つの残差** `{VE3Base, VE3Step, VE4Base, VE4Step}` へ
  絞る（`condIIIVterminalSlice_of_deep2`）。VE2 系（純幹脚・非幹前置体制・前置幾何・M レベル
  対角化）は本 wave までに **すべて無条件討伐** され、残るは VE3/VE4 の BASE/STEP
  （§7.4 頭シフト readback surgery）のみ。
- 依存 module: `8.2-condIIIV-deep4`（`EqdiagMlevel`／`condIIIVterminalSlice_of_deep3`／
  `condII_masterCF_of_deep3`／`VE3Base`/…／`LastStep`／`Br`/`Joints`/`FirstNodes`／
  `reduced_coeff`／`RedCondA_apply`／`entry_FirstNodes_eq_component_mr`／
  `Joints_nextR_FirstNodes`／`parent_eq_of_nextR0`／`row0_parent_unique`／
  `hasParent_iff_unique_fseq` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`EqdiagMlevel` を無条件討伐、残差は
  `{VE3Base, VE3Step, VE4Base, VE4Step}`。
- Private suffix: `_d3`。
-/

namespace PSS

/-! ## 私的補助（suffix `_d3`）

枝左端有界 `FN_lt_d3`（Isabelle `a1_FN_lt`）と、枝 row-0 一段 `branch_row0_step_d3`
（Isabelle `raJ1'`／`raKm1'`：`RedCondA` の枝左端への適用）。 -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（入口 `leR0_bounds_d4v` の再掲）。 -/
private theorem leR0_bounds_d3 (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, `FN_lt_d4v` の再掲）。 -/
private theorem FN_lt_d3 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_d3 M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- **Isabelle `raJ1'`／`raKm1'` の逐語移植**: 枝 `J` の左端は親 (=joint) から row-0 で
一段だけ伸びる。`RedCondA`（親+1=枝左端）を枝左端 `FirstNodes M ! J` に適用する。 -/
private theorem branch_row0_step_d3 (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hA : RedCondA M = true) (hJ : J < (Br M).length) :
    entry M 0 ((Joints M).getD J 0) + 1 = entry M 0 ((FirstNodes M).getD J 0) := by
  have hnx : nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true :=
    Joints_nextR_FirstNodes M J hM hmono hJ
  have hFNlt : (FirstNodes M).getD J 0 < Lng M := FN_lt_d3 M J hM hmono hJ
  have hpar : parent M 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 M _ _ hnx
  have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    (hasParent_iff_unique_fseq M 0 _).mpr
      ⟨(Joints M).getD J 0, hnx, fun q hq => row0_parent_unique M q _ _ hq hnx⟩
  have hstep := RedCondA_apply M hA 0 ((FirstNodes M).getD J 0) (by omega) hFNlt hhas
  rw [hpar] at hstep
  exact hstep

/-! ## `LastStep` の最小性（Isabelle `vgx_LastStep_elsecase` の全域版）

非対角ガード（最終枝頭 row-0 ≠ row-1）の下では Lean の全域的 `LastStep` は
`find?`＋既定値 `J₁` の枝に落ちる。`find?` の最小性（`List.find?_range'_eq_some` の
第三成分、あるいは `find? = none` なら全域で述語が偽）から、`k < LastStep M` の任意の枝
`k` では `S` の述語（同 row-0 枝頭 ∧ row-1 < row-0）が成立しない。 -/

/-- **Isabelle `notInS`（`vg2x_eqdiag_M` 内）の全域版**: 非対角ガード下で `k < LastStep M`
の枝 `k` は `S`-述語を満たさない。 -/
private theorem LastStep_find_min_d3 (M : PS) (hBrne : Br M ≠ [])
    (hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0)
    (k : ℕ) (hk : k < LastStep M) :
    ¬ (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0
       ∧ entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0) := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  rintro ⟨heq0, hlt0⟩
  -- 述語 `pred k` は真
  have hpk : (decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0)
             && decide (entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨heq0, hlt0⟩
  -- `LastStep M` を `find?` の枝に落とす
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

三本柱: `HD0eq`（`branch_row0_step_d3`＋eqJoint）／`LastStep` 最小性
（`LastStep_find_min_d3`）／`ROW10`（`reduced_coeff`）。 -/

/-- **M レベル対角化残差の無条件討伐**（deep4 `EqdiagMlevel`）。

`0 < LastStep M` の非幹脚で、最終枝ガード（row-1 < row-0）と等 joint
`Joints M ! (LastStep-1) = Joints M ! (Br.length-1)` の下で、`M` の `LastStep-1` 番目の
枝頭は対角（row-0 = row-1）。 -/
theorem EqdiagMlevel_holds : EqdiagMlevel := by
  intro M hMD hBrne hLS0 hguard heqJ
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, _hB⟩ := RTPS_condAB M hR
  have hKL : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  -- 添字境界
  have hKm1lt : LastStep M - 1 < (Br M).length := by omega
  have hJ1lt : (Br M).length - 1 < (Br M).length := by omega
  have hKm1ltLS : LastStep M - 1 < LastStep M := by omega
  -- ガードの成分形 ⇒ 非対角
  have hg0J1 : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      = entry ((Br M).getD ((Br M).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1lt
  have hg1J1 : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      = entry ((Br M).getD ((Br M).length - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 1 hM hJ1lt
  have hguardC : entry ((Br M).getD ((Br M).length - 1) []) 1 0
      < entry ((Br M).getD ((Br M).length - 1) []) 0 0 := by
    rw [← hg0J1, ← hg1J1]; exact hguard
  have hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
      ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0 := by omega
  -- HD0eq: entry M 0 (FN!(Km1)) = entry M 0 (FN!(J1))
  have hstepKm1 := branch_row0_step_d3 M (LastStep M - 1) hM hmono hA hKm1lt
  have hstepJ1 := branch_row0_step_d3 M ((Br M).length - 1) hM hmono hA hJ1lt
  have hjeq : entry M 0 ((Joints M).getD (LastStep M - 1) 0)
      = entry M 0 ((Joints M).getD ((Br M).length - 1) 0) := by rw [heqJ]
  have hHD0eq : entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0)
      = entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) := by omega
  -- 成分形
  have hc0Km1 : entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0)
      = entry ((Br M).getD (LastStep M - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr M (LastStep M - 1) 0 hM hKm1lt
  have hc1Km1 : entry M 1 ((FirstNodes M).getD (LastStep M - 1) 0)
      = entry ((Br M).getD (LastStep M - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr M (LastStep M - 1) 1 hM hKm1lt
  -- S の第一条件（同 row-0 枝頭）
  have hfirst : entry ((Br M).getD ((Br M).length - 1) []) 0 0
      = entry ((Br M).getD (LastStep M - 1) []) 0 0 := by
    rw [← hg0J1, ← hc0Km1]; exact hHD0eq.symm
  -- LastStep 最小性 ⇒ Km1 は S 述語を満たさない ⇒ row-0 ≤ row-1
  have hfail := LastStep_find_min_d3 M hBrne hnd (LastStep M - 1) hKm1ltLS
  have hnotlt : ¬ (entry ((Br M).getD (LastStep M - 1) []) 1 0
      < entry ((Br M).getD (LastStep M - 1) []) 0 0) := fun hlt => hfail ⟨hfirst, hlt⟩
  have hge : entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0)
      ≤ entry M 1 ((FirstNodes M).getD (LastStep M - 1) 0) := by
    rw [hc0Km1, hc1Km1]; omega
  -- ROW10（reduced_coeff）
  have hFNlt : (FirstNodes M).getD (LastStep M - 1) 0 < Lng M :=
    FN_lt_d3 M (LastStep M - 1) hM hmono hKm1lt
  have hrow10 : entry M 1 ((FirstNodes M).getD (LastStep M - 1) 0)
      ≤ entry M 0 ((FirstNodes M).getD (LastStep M - 1) 0) :=
    reduced_coeff M hR ((FirstNodes M).getD (LastStep M - 1) 0) hFNlt
  omega

/-! ## 四残差版キャップストーン

`EqdiagMlevel` を無条件討伐し、`8.2-condIIIV-deep4` の五残差版キャップストーン
`condIIIVterminalSlice_of_deep3` に差し込む。これで `condIIIVts` フィールドの無条件形
`CondIIIVterminalSlice` を **四つの残差** `{VE3Base, VE3Step, VE4Base, VE4Step}` ちょうどに
絞る。VE2 系（純幹脚・非幹前置体制・前置幾何・M レベル対角化）はすべて無条件討伐済み。 -/

/-- **四残差版キャップストーン**: `condIIIVts` フィールドを
`{VE3Base, VE3Step, VE4Base, VE4Step}` から供給する。 -/
theorem condIIIVterminalSlice_of_deep2
    (hV3b : VE3Base) (hV3s : VE3Step) (hV4b : VE4Base) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deep3 EqdiagMlevel_holds hV3b hV3s hV4b hV4s

/-- 四残差から condII 停止性フィールド `CondII_masterCF`（`8.3-TransCondII-engine`）を
供給する（`8.2-condIIIV-deep4` の `condII_masterCF_of_deep3` へ橋渡し）。 -/
theorem condII_masterCF_of_deep2
    (hV3b : VE3Base) (hV3s : VE3Step) (hV4b : VE4Base) (hV4s : VE4Step) :
    CondII_masterCF :=
  condII_masterCF_of_deep3 EqdiagMlevel_holds hV3b hV3s hV4b hV4s

/-! ## 転記の数値検証（対角化討伐の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)` は `DT_PS`・`Br ≠ []`・`0 < LastStep`
（deep4/deep5 と共通の非幹脚ホスト）に属し、`EqdiagMlevel_holds` の量化域が非空である
ことを保証する。 -/

#guard decide (DTPS [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ∧
  Br [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)] ≠ [] ∧
  0 < LastStep [(0,0),(1,1),(2,2),(1,1),(2,2),(1,1),(2,2)]) = true

#print axioms EqdiagMlevel_holds
#print axioms condIIIVterminalSlice_of_deep2
#print axioms condII_masterCF_of_deep2

end PSS
