import «8».«8.4-corner-readouts»
import «8».«8.4-np-c2decomp»

/-!
# §8.4 隅の全域終切片輸送残差 `CornerNpSliceValue_cr2` の無条件 discharge

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-corner-readouts»:116 が宣言した named 残差
  `CornerNpSliceValue_cr2`（隅 `LEAF4` 用の全域終切片輸送、Isabelle `w84x_subslice_value`／
  `crx_slice_red_value` の非 Pred 版）:

    `Trans (s84x_Np M) = D_{M₁,ⱼ₋₂}(bpHeadT (Trans (s84x_N M)))`   （条件(IV) の下）

  これは既移植 `NestScbD4aTargetValue`（`8.4-d4a-trunk`、Pred 版・終端 `Lng M − 2`）の
  `Lng M − 1` 終端の兄弟であり、`8.4-regsp-strictlt` が `Red (Pred (s84x_N M))`（endpoint
  `Lng M − 2`）を扱ったのに対し、本残差は `Red (s84x_N M)`（FULL slice、endpoint `Lng M − 1`）の
  regime/reduced-value chain である。

## 攻め筋（house pattern、無条件討伐）

`8.4-np-c2decomp` の `np_c2decomp_holds` が内部で導出する値事実 `valNp`

    `Trans (s84x_Np M) = D_{M₁,ⱼ₋₂}(bpHeadT (Trans (s84x_N M)))`

は本残差 `CornerNpSliceValue_cr2` の結論そのものであり、その導出は scb 入力 `d2` に
一切依存しない（前提は `STPS`/`monoT`/`hasParent`/`1<Lng−1`/条件(III)∨(IV) のみ）。
本ファイルはその `valNp` chain をそのまま隅前提へ specialize する:

1. 簡約host `RN = Red (s84x_N M)` の基本性質（`standard_slice_Red_strongmono`＋`DTPS_iff`）。
2. 簡約host 終切片値 `Trans (seg RN m (Lng RN−1)) = D_{RN₁,ₘ}(bpHeadT (Trans RN))`
   （`m = 0`: `VE_index0`；`m > 0`: `regS_holds`＋`vcx_VE_all`＋`slice_Trans_principal_head`）。
3. M→R transport（`wnx_seg_transport_W1/W2`＋`repr_entry1_shift_gen`）で `Trans (s84x_Np M)` を
   host 値へ落とし、`entry` を M 座標へ引き戻す。

条件 `hcond`（`Np_c2decomp_sc3`/`Regs_mcx_regS` の要求）は `transCondIII ∨ transCondIV` なので、
隅前提 `transCondIV M = true` から `Or.inr` で供給する。

- 依存（すべてビルド済み・main 39e6765）: «8».«8.4-corner-readouts»
  （`CornerNpSliceValue_cr2` def）、«8».«8.4-np-c2decomp»（推移的に `regS_holds`／
  `Regs_jm3Marked_holds`／`regs_jm2_lt_transJ0_holds`／`Regs_MCOND_holds`／
  `wnx_seg_transport_W1/W2`／`repr_entry1_shift_gen`／`vcx_VE_all`／`VE_index0`／`VEeq`／
  `slice_Trans_principal_head`／`standard_slice_Red_strongmono`／`DTPS_iff`／`mono_slice`／
  `s84c1_jm2_basic`／`Adm_le`／`Lng_Red_invariance`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound、無条件）。
- Private helper suffix: `_cnv`。
-/

namespace PSS

/-! ## `CornerNpSliceValue_cr2` の無条件 discharge

`8.4-np-c2decomp` の `np_c2decomp_holds` 内 `valNp` chain（scb 入力非依存）の specialize。 -/

/-- **`CornerNpSliceValue_cr2`（«8».«8.4-corner-readouts»:116）の完全証明**（無条件）。
`Red (s84x_N M)`（FULL slice、endpoint `Lng M − 1`）の regime/reduced-value chain。 -/
theorem cornerNpSliceValue_holds_cnv : CornerNpSliceValue_cr2 := by
  intro M hST hmono hp hj1 hIV
  have hcond : transCondIII M = true ∨ transCondIV M = true := Or.inr hIV
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  -- 基本の添字
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have hle0jm2m1 : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR hMT hp).1.2.2
  -- 簡約host `RN = Red (s84x_N M)` の基本性質
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have hLenRN : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M :=
    (Lng_Red_invariance (s84x_N M) NT).trans hlenN
  have hDT : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  obtain ⟨hRNR, hmonoRN, _hdescRN⟩ := (DTPS_iff _).mp hDT
  have hRNT : TPS (Red (s84x_N M)) := RTPS_TPS _ hRNR
  have hmlt : s84x_jm2 M - s84x_jm3 M < Lng (Red (s84x_N M)) - 1 := by rw [hLenRN]; omega
  -- REGS の producer（無条件）
  have regSAll : Regs_mcx_regS :=
    regS_holds Regs_jm3Marked_holds regs_jm2_lt_transJ0_holds Regs_MCOND_holds
  -- 簡約host 値: `Trans (seg RN m (Lng RN-1)) = D_{RN₁,ₘ} (bpHeadT (Trans RN))`
  have hval : Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                (Lng (Red (s84x_N M)) - 1))
      = Dprin ((entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (s84x_N M)))) := by
    have key : s84x_jm2 M - s84x_jm3 M
          ≤ (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
        ∧ VEeq (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) := by
      rcases Nat.eq_zero_or_pos (s84x_jm2 M - s84x_jm3 M) with hm0 | hmpos
      · exact ⟨by rw [hm0]; exact Nat.zero_le _,
              by rw [hm0]; exact VE_index0 (Red (s84x_N M)) hRNT⟩
      · have hguard : s84x_jm3 M < s84x_jm2 M := by omega
        have hVEReg : VEReg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) :=
          regSAll M hST hmono hp hj1 hcond hguard
        refine ⟨?_, vcx_VE_all (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) hVEReg⟩
        obtain ⟨-, -, -, hdisj⟩ := hVEReg
        rcases hdisj with hlt' | ⟨heq', -⟩ <;> omega
    obtain ⟨hmleq, hbody⟩ := key
    have hmonoSlice : monoT (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
        (Lng (Red (s84x_N M)) - 1)) = true :=
      mono_slice (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M) (Lng (Red (s84x_N M)) - 1)
        hRNT hmonoRN hmlt (le_refl _) hmleq
    have hprinc := slice_Trans_principal_head (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
      (Lng (Red (s84x_N M)) - 1) hRNR hmlt (le_refl _) hmonoSlice
    unfold VEeq at hbody
    rw [hprinc, hbody]
  -- M→R transport bricks
  have ham : s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M) = s84x_jm2 M := by omega
  have hW1 : Trans (s84x_N M) = Trans (Red (s84x_N M)) :=
    wnx_seg_transport_W1 M (s84x_jm3 M) (Lng M - 1) jm3lt
  have hW2 : Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 1))
      = Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                 (Lng (Red (s84x_N M)) - 1)) :=
    wnx_seg_transport_W2 M (s84x_jm3 M) (Lng M - 1) (s84x_jm2 M - s84x_jm3 M) hMR
      jm3lt (le_refl _) leR3 (by rw [ham]; exact jm2lt) (by rw [ham]; exact hle0jm2m1)
  have hentry : entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M)
      = entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) :=
    repr_entry1_shift_gen M (s84x_jm3 M) (Lng M - 1) (s84x_jm2 M - s84x_jm3 M) hMR
      jm3lt (le_refl _) leR3
      (by show s84x_jm2 M - s84x_jm3 M < Lng (Red (s84x_N M)); rw [hLenRN]; omega)
  -- 値事実 `valNp` = 目標
  calc Trans (s84x_Np M)
      = Trans (seg M (s84x_jm2 M) (Lng M - 1)) := rfl
    _ = Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 1)) := by rw [ham]
    _ = Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                 (Lng (Red (s84x_N M)) - 1)) := hW2
    _ = Dprin ((entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞)
            (bpHeadT (Trans (Red (s84x_N M)))) := hval
    _ = Dprin ((entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) : ℕ) : ℕ∞)
            (bpHeadT (Trans (Red (s84x_N M)))) := by rw [hentry]
    _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            (bpHeadT (Trans (Red (s84x_N M)))) := by rw [ham]
    _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            (bpHeadT (Trans (s84x_N M))) := by rw [← hW1]

#print axioms cornerNpSliceValue_holds_cnv

end PSS
