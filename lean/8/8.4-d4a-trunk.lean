import «8».«8.4-d4a-target»
import «8».«8.4-regsp-strictlt»
import «8».«8.3-condII-TrunkLeg»
import «8».«8.2-condIIIV-terminal-slice-Trans»
import «8».«8.2-condV-VE-close»
import «8».«8.2-subexpr-component-Pred»
import «8».«8.2-standard-slice-Red-strongmono»

/-!
# §8.4 交換パッケージ `d4a` — 簡約host 終切片値 leaf `NestScbD4aReducedValue` の discharge

- 対象: `NestScbD4aReducedValue`（«8».«8.4-d4a-target»:75 で def・narrowing 済の最終残差）。
  簡約host `R = Red (seg M j₋₃ (Lng M - 2))` の相対 offset `m = j₋₂ - j₋₃` における
  終切片値
  `Trans (seg R m (Lng R - 1)) = D_{R₁,ₘ} (bpHeadT (Trans R))`。
  Isabelle `w84x_slice_value_of_reg` (regime, layerB/pss_wip.thy:78815, `cfbx_reg`=VEReg 消費)
  / `crg_slice_value_of_trunk` (trunk, layerB/pss_wip.thy:91399, 対角閉形式) の出力。

## 移植構造（2 分岐 = Isabelle `crg_d4a_all` の `Br (Red (Pred (s84x_N M)))` dispatch）

頭形は公開 `slice_Trans_principal_head`（«8».«8.2-condIIIV-terminal-slice-Trans»）が両枝
共通に `D_{R₁,ₘ} (bpHeadT (Trans (seg R m ..)))` を与える。残るは **body 保存**
`bpHeadT (Trans (seg R m ..)) = bpHeadT (Trans R)`（= `VEeq m R`）を、`Br R` の空/非空で
供給する:

* **trunk 枝 `Br R = []`**（Isabelle `crg_slice_value_of_trunk`）: 全幹の簡約列は対角
  `diagSeq u w`（`wnx_trunk_diagSeq`＋`baseU_Br_empty_TrMax`）で、その `Trans` は明示的な
  2 段塔 `D_u (D_w 0_B)`（`diagSeq_Trans`）。末尾切片も対角 `diagSeq (u+m) w`
  （`segdrop_diagSeq_dk`）なので値は `D_{u+m} (D_w 0_B) = D_{R₁,ₘ} (bpHeadT (Trans R))` と
  直接計算される（本ファイルの `crg_slice_value_of_trunk_dk`、値を丸ごと閉じる）。

* **regime 枝 `Br R ≠ []`**（Isabelle `w84x_slice_value_of_reg`）: `m = 0` では切片が `R`
  自身なので body 保存は自明（`VE_index0`）。`m > 0` では `Regsp_slx37_regSP_holds`
  （«8».«8.4-regsp-strictlt»、無条件）が `VEReg m (Red (Pred (s84x_N M)))` を与え、
  `Red (Pred (s84x_N M)) = R`（`Red_Pred`＋`Pred_Red_terminal_slice`）で `VEReg m R` へ移し、
  `vcx_VE_all`（«8».«8.2-condV-VE-close»、無条件 VE campaign）で `VEeq m R` を得る。

到達性 `leR M 0 j₋₃ (Lng M - 2)`（`standard_slice_Red_strongmono` の入力）と
`Lng R - 1 = (Lng M - 2) - j₋₃`（`wnx_seg_transport_W3`）は «8».«8.4-d4a-target» と同じ
公開資産の連鎖で完全に組む。

## 状態

- 🎉 `nestScbD4aReducedValue_holds : NestScbD4aReducedValue`（sorry 0、無条件、
  axioms = propext/Classical.choice/Quot.sound）。
- 合成: `nestScbD4aTransport_dk : NestScbD4aTransport_ns`
  （`nestScbD4aTransport_holds ∘ nestScbD4aTargetValue_holds`、無条件）。
- Private helper suffix: `_dk`。
-/

namespace PSS

/-! ## 1. 対角列の私的補題（«8».«8.3-condII-TrunkLeg» private `_tl` の twin） -/

/-- 対角列の長さ。 -/
private theorem length_diagSeq_dk (u v : ℕ) : Lng (diagSeq u v) = v + 1 - u := by
  simp [diagSeq]

/-- 対角列の成分は `u + j`（両段共通）。 -/
private theorem entry_diagSeq_dk (u v i j : ℕ) (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v) i j = u + j := by
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

/-- 対角列の末尾切片は再び対角列（左端が `d` 桁だけ右へ）。 -/
private theorem segdrop_diagSeq_dk (u w d : ℕ) (hd : d < Lng (diagSeq u w)) :
    seg (diagSeq u w) d (Lng (diagSeq u w) - 1) = diagSeq (u + d) w := by
  have hd' : d < w + 1 - u := by rwa [length_diagSeq_dk] at hd
  apply List.ext_getElem
  · simp only [length_seg, length_diagSeq_dk]
    omega
  · intro n h1 h2
    have hdn : d + n < Lng (diagSeq u w) := by
      simp only [length_seg, length_diagSeq_dk] at h1
      rw [length_diagSeq_dk]
      omega
    rw [seg_getElem_68 (diagSeq u w) d (Lng (diagSeq u w) - 1) n h1,
      entry_diagSeq_dk u w 0 (d + n) hdn, entry_diagSeq_dk u w 1 (d + n) hdn]
    have hassoc : u + (d + n) = u + d + n := by omega
    rw [hassoc]
    simp [diagSeq, List.getElem_map, List.getElem_range']

/-! ## 2. 幹枝の簡約host 終切片値（Isabelle `crg_slice_value_of_trunk`, pss_wip.thy:91399） -/

/-- 全幹（`Br X = []`）の簡約列 `X` は対角 `diagSeq u w`（`u = X₁,₀`, `w = u + (Lng X - 1)`）
であり（`wnx_trunk_diagSeq`＋`baseU_Br_empty_TrMax`）、その末尾切片値は
`Trans (seg X q (Lng X - 1)) = D_{X₁,q} (bpHeadT (Trans X)) = D_{u+q} (D_w 0_B)`。 -/
private theorem crg_slice_value_of_trunk_dk (X : PS) (q : ℕ)
    (hXR : RTPS X) (htrunk : Br X = []) (hq : q < Lng X - 1) :
    Trans (seg X q (Lng X - 1)) = Dprin ((entry X 1 q : ℕ) : ℕ∞) (bpHeadT (Trans X)) := by
  have htr : TrMax X = Lng X - 1 := baseU_Br_empty_TrMax X htrunk
  have hdiag : X = diagSeq (entry X 1 0) (entry X 1 0 + (Lng X - 1)) :=
    wnx_trunk_diagSeq X hXR htr
  set u := entry X 1 0 with hudef
  set w := u + (Lng X - 1) with hwdef
  have huw : u < w := by rw [hwdef]; omega
  have huqw : u + q < w := by rw [hwdef]; omega
  have hLdiag : Lng (diagSeq u w) = Lng X := (congrArg Lng hdiag).symm
  have hqLd : q < Lng (diagSeq u w) := by rw [hLdiag]; omega
  have hTX : Trans X = Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    conv_lhs => rw [hdiag]
    exact diagSeq_Trans u w huw
  have hbph : bpHeadT (Trans X) = Dprin (w : ℕ∞) BZero := by rw [hTX]; rfl
  have hentq : entry X 1 q = u + q := by
    conv_lhs => rw [hdiag]
    exact entry_diagSeq_dk u w 1 q hqLd
  have hseg : seg X q (Lng X - 1) = diagSeq (u + q) w := by
    rw [hdiag]
    exact segdrop_diagSeq_dk u w q hqLd
  rw [hseg, diagSeq_Trans (u + q) w huqw, hentq, hbph]

/-! ## 3. 主定理 `NestScbD4aReducedValue`（regime/trunk 二分岐） -/

/-- **`NestScbD4aReducedValue` の完全証明**（無条件）。簡約host `R = Red (seg M j₋₃
(Lng M - 2))` の相対 offset `m = j₋₂ - j₋₃` の終切片値。`Br R` の空/非空で trunk 対角閉形式
/ regime VE（`Regsp_slx37_regSP_holds`＋`vcx_VE_all`）へ dispatch。 -/
theorem nestScbD4aReducedValue_holds : NestScbD4aReducedValue := by
  intro M hST hmono hp hj1 hcond
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := STPS_TPS M hST
  have hlen : 1 < Lng M := by omega
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hjm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have hjm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt hjm3le hjm2lt
  -- j₀ 経由で j₋₂ < Lng M - 2 を確定（«8».«8.4-d4a-target» と同じ連鎖）
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hj0lt : transJ0 M < Lng M - 1 := by
    have h := parent_lt_of_hasParent M 0 (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hjm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp hj1 hcond
  have hjm2lt2 : s84x_jm2 M < Lng M - 2 := by omega
  have hjm3lt2 : s84x_jm3 M < Lng M - 2 := by omega
  -- 到達性 leR M 0 j₋₃ (Lng M - 2)
  have hnextrel0 : nextrel0 M (transJ0 M) (Lng M - 1) = true := by simpa [nextR] using hnextM
  have hle0jm2j1 : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  have hle0jm2j0 : le0 M (s84x_jm2 M) (transJ0 M) = true :=
    scx_le0_to_parent M (s84x_jm2 M) (transJ0 M) (Lng M - 1) hMT hle0jm2j1 hnextrel0 (by omega)
  have hle0j0m2 : le0 M (transJ0 M) (Lng M - 2) = true := by
    have hraw := parent_block_le0_68 M (transJ0 M) (Lng M - 1)
      ((Lng M - 2) - transJ0 M) hMT hnextM (by omega)
    have hidx : transJ0 M + ((Lng M - 2) - transJ0 M) = Lng M - 2 := by omega
    rwa [hidx] at hraw
  have hleR_jm2j0 : leR M 0 (s84x_jm2 M) (transJ0 M) = true := by simpa [leR] using hle0jm2j0
  have hleR_j0m2 : leR M 0 (transJ0 M) (Lng M - 2) = true := by simpa [leR] using hle0j0m2
  have hleR_jm2m2 : leR M 0 (s84x_jm2 M) (Lng M - 2) = true :=
    row0_transitive M (s84x_jm2 M) (transJ0 M) (Lng M - 2) hMT hleR_jm2j0 hleR_j0m2
  have hle1_jm3jm2 : leR M 1 (s84x_jm3 M) (s84x_jm2 M) = true :=
    adm_row1_ancestry M (s84x_jm2 M) hMT (by omega)
  have hle0_jm3jm2 : leR M 0 (s84x_jm3 M) (s84x_jm2 M) = true :=
    row1_implies_row0 M (s84x_jm3 M) (s84x_jm2 M) hMT hle1_jm3jm2
  have hleR_jm3m2 : leR M 0 (s84x_jm3 M) (Lng M - 2) = true :=
    row0_transitive M (s84x_jm3 M) (s84x_jm2 M) (Lng M - 2) hMT hle0_jm3jm2 hleR_jm2m2
  -- 簡約host R = Red (seg M j₋₃ (Lng M - 2)) の基本性質
  set R := Red (seg M (s84x_jm3 M) (Lng M - 2)) with hRdef
  set m := s84x_jm2 M - s84x_jm3 M with hmdef
  have hDT : DTPS R :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 2) hST hjm3lt2 (by omega) hleR_jm3m2
  obtain ⟨hRR, hmonoR, hdescR⟩ := (DTPS_iff R).mp hDT
  have hRT : TPS R := RTPS_TPS R hRR
  have hLR : Lng R - 1 = (Lng M - 2) - s84x_jm3 M :=
    wnx_seg_transport_W3 M (s84x_jm3 M) (Lng M - 2) hjm3lt2
  have hmlt : m < Lng R - 1 := by rw [hmdef, hLR]; omega
  -- Br R の空/非空で dispatch
  by_cases hBr : Br R = []
  · -- trunk 枝: 対角閉形式で値を丸ごと閉じる
    exact crg_slice_value_of_trunk_dk R m hRR hBr hmlt
  · -- regime 枝: principal head ＋ body 保存
    -- Red (Pred (s84x_N M)) = R
    have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
      show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
      rw [length_seg]; omega
    have NT : TPS (s84x_N M) := by
      have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
      intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
    have hNeq : Red (Pred (s84x_N M)) = R := by
      rw [hRdef]
      have h1 : Red (Pred (s84x_N M)) = Pred (Red (s84x_N M)) := Red_Pred (s84x_N M) NT
      have h2 : Pred (Red (s84x_N M)) = Red (seg M (s84x_jm3 M) (Lng M - 1 - 1)) :=
        Pred_Red_terminal_slice M (s84x_jm3 M) (Lng M - 1) hjm3lt
      have he : Lng M - 1 - 1 = Lng M - 2 := by omega
      rw [h1, h2, he]
    -- body 保存 VEeq m R ＋ 単項性用 m ≤ 末尾関節
    have key : m ≤ (Joints R).getD ((Br R).length - 1) 0 ∧ VEeq m R := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · exact ⟨by rw [hm0]; exact Nat.zero_le _, by rw [hm0]; exact VE_index0 R hRT⟩
      · have hguard : s84x_jm3 M < s84x_jm2 M := by rw [hmdef] at hmpos; omega
        have hBrRP : Br (Red (Pred (s84x_N M))) ≠ [] := by rw [hNeq]; exact hBr
        have hVEReg0 : VEReg m R := by
          have h := Regsp_slx37_regSP_holds M hST hmono hp hj1 hcond hguard hBrRP
          rwa [hNeq, ← hmdef] at h
        refine ⟨?_, vcx_VE_all m R hVEReg0⟩
        obtain ⟨-, -, -, hdisj⟩ := hVEReg0
        rcases hdisj with hlt' | ⟨heq', -⟩ <;> omega
    obtain ⟨hmleq, hbody⟩ := key
    have hmonoSlice : monoT (seg R m (Lng R - 1)) = true :=
      mono_slice R m (Lng R - 1) hRT hmonoR hmlt (le_refl _) hmleq
    have hprinc := slice_Trans_principal_head R m (Lng R - 1) hRR hmlt (le_refl _) hmonoSlice
    unfold VEeq at hbody
    rw [hprinc, hbody]

#print axioms nestScbD4aReducedValue_holds

/-! ## 4. 合成: 無条件 `NestScbD4aTransport_ns` -/

/-- `NestScbD4aReducedValue` 完成により、`8.4-d4a-target`／`8.4-exch84-d4a` の 2 段
narrowing が無条件化: `nestScbD4aTransport_holds ∘ nestScbD4aTargetValue_holds`。 -/
theorem nestScbD4aTransport_dk : NestScbD4aTransport_ns :=
  nestScbD4aTransport_holds (nestScbD4aTargetValue_holds nestScbD4aReducedValue_holds)

#print axioms nestScbD4aTransport_dk

end PSS
