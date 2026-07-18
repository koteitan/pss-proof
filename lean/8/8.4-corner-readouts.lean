import «8».«8.4-corner-core»
import «8».«8.4-corner-redesign»
import «8».«8.4-d4a-trunk»
import «8».«8.4-l1-slice-data»
import «8».«8.4-rm84-rfacts-close»
import «8».«8.4-rightmost-replace-close»

/-!
# §8.4 交換パッケージ condIV admeq 隅の `CornerCoreReadouts_cc` の discharge
（底スライス平坦式 `L₁`/`Trans (Lp)`/`Trans (Pred Np)`、共有 `(s0,b0)` に鍵付け）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-corner-core»:190 が宣言した named 残差
  `CornerCoreReadouts_cc`（隅 core の最後の 1 葉、`d4vx_core` 塔 readback、Isabelle
  `c4cx2_condIV_mnform_of_slice` の n=1 三連言に対応）。3 連言:
  * **LEAF3**（`L₁`）: `flatBT (Trans (s84x_L M 1))`（塔深さ 1 の平坦式、共有 `(s1,b1)`＋`(s0,b0)`）。
  * **LEAF4**（`Trans (Lp)`）: `flatBT (Trans (s84x_Lp M))`（頭 `D_{M₁,ⱼ₋₂}`・穴 `D_{M₁,ⱼ₋₂} 0`）。
  * **LEAF5**（`Trans (Pred Np)`）: `flatBT (Trans (Pred (s84x_Np M)))`（頭 `D_{M₁,ⱼ₋₂}`）。

## 攻め筋（house green-modulo、残差 = 全域終切片輸送 1 本）

隅（condIV ∧ admeq）では collapse 恒等式 `cornerCollapse_holds_cr`
（`Trans (s84x_N M) = transC2 M`、`Trans (Pred (s84x_N M)) = transC1 M`）が効き、
底スライスの 3 平坦式は既存資産で 1 本の輸送残差へ縮約される:

1. **LEAF5**: `NestScbD4aTargetValue`（`nestScbD4aTargetValue_holds`∘`nestScbD4aReducedValue_holds`、
   無条件）で `Trans (Pred (s84x_Np M)) = D_{M₁,ⱼ₋₂}(bpHeadT (Trans (Pred (s84x_N M))))`、
   collapse で `Trans (Pred (s84x_N M)) = transC1 M` → 平坦式。**無条件討伐**。
2. **LEAF3**: `l1SliceData_holds`（`transC2 (L₁) = c2hole_ch M M₁,ⱼ₋₂`、`transC1 (L₁) = transC1 M`、
   `Trans (Pred L₁) = Trans (Pred M)`）＋ c2hole エンジン（`c2hole_scb_ch`）＋
   `Trans_c1_c2_decomp`（L₁）を、入力 `hd1`（`(s1,b1)` pin）・`hinner`（`(s0,b0)` pin）へ
   scb 一意性で結ぶ。**無条件討伐**（Isabelle `base5` の隅版）。
3. **LEAF4**: 全域終切片輸送残差 `CornerNpSliceValue_cr2`
   （`Trans (s84x_Np M) = D_{M₁,ⱼ₋₂}(bpHeadT (Trans (s84x_N M)))`、Isabelle `w84x_subslice_value`／
   `crx_slice_red_value` の非 Pred 版、`cfbx_reg` 消費のため未移植だが 505/505 数値検証済）＋
   collapse で `d2 := scb_decomp (Trans (s84x_Np M)) (D_{M₁,ⱼ₋₂}::s0) (D_{M₁,ⱼ₁}0) b0` を組み、
   `Rightmost84ReplaceExists`（無条件・rc2）の Np/Lp 共有分解を scb 一意性で pin して
   `Trans (Lp)` 平坦式へ移送。

`CornerCoreReadouts_cc` は輸送残差 `CornerNpSliceValue_cr2` 1 本へ縮約される
（これは Isabelle の隅でも `d1/d2/d3` の "E2/E3 terminal-slice transports" 残差として carry
される、条件非依存の終切片輸送）。

- 依存（すべてビルド済み・main 6e1621a）: «8».«8.4-corner-core»
  （`CornerCoreReadouts_cc` def）、«8».«8.4-corner-redesign»（`cornerCollapse_holds_cr`）、
  «8».«8.4-d4a-trunk»（`nestScbD4aReducedValue_holds`／`nestScbD4aTargetValue_holds`）、
  «8».«8.4-l1-slice-data»（`l1SliceData_holds`／`c2hole_ch`／`c2hole_scb_ch`／`c2hole_at_j1_ch`／
  `Trans_c1_c2_decomp`／`scb_unique_decomp_unconditional`／`regs_jm2_lt_transJ0_holds`）、
  «8».«8.4-rm84-rfacts-close»（`rightmost84ReplaceExists_rc2`）、«8».«8.4-rightmost-replace-close»
  （`Rightmost84ReplaceExists`／`rrLp`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  LEAF3／LEAF5 無条件討伐。残差 = `CornerNpSliceValue_cr2`（全域終切片輸送 1 本、`needs` 参照）。
- Private helper suffix: `_cr2`。
-/

namespace PSS

/-! ## 0. 隅 setup（`8.4-corner-core` private helper の `_cr2` 複製） -/

/-- 隅 setup: `0 < transJ1 M` ＋ `transT1 M ≠ 0_B`。 -/
private theorem corner_setup_cr2 (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
    0 < transJ1 M ∧ transT1 M ≠ BZero := by
  have hlen : 1 < Lng M := by omega
  refine ⟨by simp only [transJ1, lastIdx]; omega, ?_⟩
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1' : Trans (Pred M) ≠ BZero :=
    (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
  simpa [transT1] using T1'

/-- 隅の域幅 `j₋₂ + 1 < Lng M − 1`（`cornerCollapse` proof と同じ chain）。 -/
private theorem corner_rng_cr2 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hIV : transCondIV M = true) :
    s84x_jm2 M + 1 < Lng M - 1 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp hj1 (Or.inr hIV)
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  omega

/-- `flatBT (transC2 M) = Dsym (transV M) :: flatBT (bpHeadT (transC2 M))`
（`8.4-corner-core` private `transC2_flat_head_cc` の複製）。 -/
private theorem transC2_flat_head_cr2 (M : PS) :
    flatBT (transC2 M) = Sym.dsym (transV M) :: flatBT (bpHeadT (transC2 M)) := by
  have h : ∃ body, transC2 M = Dprin (transV M) body := by
    unfold transC2 transC2Core; split_ifs <;> exact ⟨_, rfl⟩
  obtain ⟨body, hb⟩ := h
  rw [hb]; rfl

/-- 底穴 `flatBT (D_n 0_B)` の `isPTB_str`（`8.4-corner-core` private `isPTB_Dprin_nat_cc` の複製）。 -/
private theorem isPTB_Dprin_nat_cr2 (n : ℕ) :
    isPTB_str (flatBT (Dprin (n : ℕ∞) BZero)) :=
  ⟨.db (n : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩

/-! ## 1. 全域終切片輸送残差（Isabelle `w84x_subslice_value`／`crx_slice_red_value`、非 Pred 版） -/

/-- **残差**（`needs`）: `s84x_Np M = seg M j₋₂ (Lng M − 1)` の `Trans` は、外側頭 `D_{M₁,ⱼ₋₂}`
（行1親 `j₋₂` の行1成分）の内側に、`s84x_N M = seg M j₋₃ (Lng M − 1)` の `Trans` の
深い尾 `bpHeadT (Trans (s84x_N M))` を露出する:

    `Trans (s84x_Np M) = D_{M₁,ⱼ₋₂}(bpHeadT (Trans (s84x_N M)))`.

`s84x_Np` は `s84x_N` の相対 offset `j₋₂ − j₋₃` の終切片であり、終切片の deep-tail
共有（Isabelle `w84x_slice_value_of_reg` / `w84x_tail_share_of_reg`、`cfbx_reg` 正則性エンジン
消費）の非 Pred 版。`crx_slice_red_value` の M レベル出力そのもの。既移植の `NestScbD4aTargetValue`
（`8.4-exch84-d4a`）は Pred 版（`Lng M − 2` 終端）で、本残差はその `Lng M − 1` 終端の兄弟。
条件非依存（条件(III)/(IV) で成立、505/505 数値検証、`python/trans_model.py`）。 -/
def CornerNpSliceValue_cr2 : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true →
    Trans (s84x_Np M)
      = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) (bpHeadT (Trans (s84x_N M)))

/-! ## 2. LEAF5: `flatBT (Trans (Pred (s84x_Np M)))`（無条件、d4a ＋ collapse） -/

/-- **LEAF5 の無条件討伐**。`NestScbD4aTargetValue`（Pred 版終切片値、`8.4-d4a-trunk`）＋
collapse で `Trans (Pred (s84x_Np M)) = D_{M₁,ⱼ₋₂}(bpHeadT (transC1 M))`、平坦化。 -/
private theorem leaf5_cr2 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hIV : transCondIV M = true) (hadmeq : Adm M (s84x_jm2 M) = transJm1 M) :
    flatBT (Trans (Pred (s84x_Np M)))
      = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: flatBT (bpHeadT (transC1 M)) := by
  have hval := (nestScbD4aTargetValue_holds nestScbD4aReducedValue_holds)
    M hST hmono hp hj1 (Or.inr hIV)
  obtain ⟨_hcTN, hcPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
  rw [hcPN] at hval
  rw [hval]
  simp [Dprin, flatBT, flatBP]

/-! ## 3. LEAF4: `flatBT (Trans (s84x_Lp M))`（残差 ＋ collapse ＋ Rightmost） -/

/-- **LEAF4**（残差経由）。全域終切片輸送 `hNpVal`＋collapse で
`Trans (s84x_Np M) = D_{M₁,ⱼ₋₂}(bpHeadT (transC2 M))`、`hinner` で `d2` を組み、
`Rightmost84ReplaceExists`（無条件）の Np/Lp 共有分解を scb 一意性で pin。 -/
private theorem leaf4_cr2 (hNpVal : CornerNpSliceValue_cr2)
    (M : PS) (s0 b0 : List Sym) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hIV : transCondIV M = true) (hadmeq : Adm M (s84x_jm2 M) = transJm1 M)
    (hinner : scb_decomp (bpHeadT (transC2 M)) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    flatBT (Trans (s84x_Lp M))
      = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
          :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ b0) := by
  -- `Trans (s84x_Np M) = D_{jm2}(bpHeadT (transC2 M))`
  have hval := hNpVal M hST hmono hp hj1 hIV
  obtain ⟨hcTN, _hcPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
  rw [hcTN] at hval
  -- `d2`: scb 分解（頭 `dsym jm2 :: s0`、中心 `D_{M₁,ⱼ₁} 0`、尾 `b0`）
  have hd2np : scb_decomp (Trans (s84x_Np M))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: s0)
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 := by
    refine ⟨?_, ?_, hinner.2.2⟩
    · rw [hval]
      have hh : flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) (bpHeadT (transC2 M)))
          = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: flatBT (bpHeadT (transC2 M)) := by
        simp [Dprin, flatBT, flatBP]
      rw [hh, hinner.1]; simp [List.cons_append, List.append_assoc]
    · intro _; exact isPTB_Dprin_nat_cr2 (entry M 1 (Lng M - 1))
  -- Rightmost の Np/Lp 共有分解
  have hrng : s84x_jm2 M + 1 < Lng M - 1 := corner_rng_cr2 M hST hmono hp hj1 hIV
  obtain ⟨sb, hNpDec, hLpDec⟩ := rightmost84ReplaceExists_rc2 M hST hmono hp hrng
  -- 中心固定 ⇒ pin
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (s84x_Np M))
    (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: s0) sb.1
    (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 sb.2 hd2np hNpDec
  -- `rrLp = s84x_Lp`、平坦式へ
  have hLpeq : rrLp M = s84x_Lp M := rfl
  rw [hLpeq] at hLpDec
  rw [← hs, ← hb] at hLpDec
  have hflat := hLpDec.1
  have hc : flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)
      = [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] := by
    simp [Dprin, flatBT, flatBP, BZero]
  rw [hc] at hflat
  rw [hflat]; simp [List.cons_append, List.append_assoc]

/-! ## 4. LEAF3: `flatBT (Trans (s84x_L M 1))`（無条件、c2hole ＋ L1SliceData） -/

/-- **LEAF3 の無条件討伐**（Isabelle `base5` の隅版）。`l1SliceData_holds`（L₁ slice 幾何）＋
c2hole エンジン＋`Trans_c1_c2_decomp`（L₁）を、`hd1`（`(s1,b1)` pin）・`hinner`（`(s0,b0)` pin）へ
scb 一意性で結ぶ。 -/
private theorem leaf3_cr2
    (M : PS) (s0 b0 s1 b1 : List Sym) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hIV : transCondIV M = true) (hadmeq : Adm M (s84x_jm2 M) = transJm1 M)
    (hd1 : scb_decomp (Trans (oper M 1)) s1 (flatBT (transC1 M)) b1)
    (hinner : scb_decomp (bpHeadT (transC2 M)) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    flatBT (Trans (s84x_L M 1))
      = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
          ++ [Sym.zero] ++ b0 ++ b1 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlenM : 1 < Lng M := by omega
  obtain ⟨hJ1pos, hT1'⟩ := corner_setup_cr2 M hMR hj1
  -- transV = M₁,ⱼ₋₃
  obtain ⟨hTV, _hc1eq, _ht2TB, _hjm1lt⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1'
  have hjm3 : s84x_jm3 M = transJm1 M := hadmeq
  have hTVjm3 : transV M = ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) := by rw [hTV, hjm3]
  -- c2hole エンジン
  obtain ⟨w, w', W⟩ := c2hole_scb_ch M hMR hMT hmono hJ1pos hT1'
  -- W at `a = M₁,ⱼ₁` は `transC2 M` の分解
  have Wj1 : scb_decomp (transC2 M) (Sym.dsym (transV M) :: w)
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) w' := by
    rw [c2hole_at_j1_ch M]; exact W (entry M 1 (Lng M - 1))
  -- 頭剥がし: `bpHeadT (transC2 M)` の分解 `(w, w')`
  have hbody_decomp : scb_decomp (bpHeadT (transC2 M)) w
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) w' := by
    refine ⟨?_, ?_, Wj1.2.2⟩
    · have h := Wj1.1
      rw [transC2_flat_head_cr2 M] at h
      simp only [List.cons_append] at h
      exact (List.cons.inj h).2
    · intro _; exact isPTB_Dprin_nat_cr2 (entry M 1 (Lng M - 1))
  -- pin `(w, w') = (s0, b0)`
  obtain ⟨hw, hw'⟩ := scb_unique_decomp_unconditional (bpHeadT (transC2 M))
    w s0 (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) w' b0 hbody_decomp hinner
  subst hw; subst hw'
  -- L₁ slice 幾何
  obtain ⟨hLR, hLmono, hLlen, hLpred, hLc1, hLc2⟩ :=
    l1SliceData_holds M hST hmono hp hj1 (Or.inr hIV)
  -- `transC2 (L₁) = c2hole_ch M M₁,ⱼ₋₂` の平坦式（W at `a = M₁,ⱼ₋₂`）
  have Wjm2 : scb_decomp (transC2 (s84x_L M 1)) (Sym.dsym (transV M) :: w)
      (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) w' := by
    rw [hLc2]; exact W (entry M 1 (s84x_jm2 M))
  have hLc2flat : flatBT (transC2 (s84x_L M 1))
      = (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: w)
          ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ w' := by
    have h := Wjm2.1
    rw [hTVjm3] at h
    have hc : flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)
        = [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] := by
      simp [Dprin, flatBT, flatBP, BZero]
    rw [hc] at h; exact h
  -- `Trans_c1_c2_decomp` on L₁
  have hT1L : Trans (Pred (s84x_L M 1)) ≠ BZero := by
    rw [hLpred]; simpa [transT1] using hT1'
  obtain ⟨s1L, b1L, dc1L, dc2L⟩ := Trans_c1_c2_decomp (s84x_L M 1) hLR hLmono hLlen hT1L
  rw [hLpred, hLc1] at dc1L
  -- `hd1` を `Trans (Pred M)` 版へ
  have hoper : oper M 1 = Pred M := (pred_is_oper1 M hMT hlenM).symm
  rw [hoper] at hd1
  obtain ⟨hs1, hb1⟩ := scb_unique_decomp_unconditional (Trans (Pred M))
    s1L s1 (flatBT (transC1 M)) b1L b1 dc1L hd1
  subst hs1; subst hb1
  -- 平坦式の組み立て
  have hf := dc2L.1
  rw [hLc2flat] at hf
  rw [hf]; simp [List.cons_append, List.append_assoc]

/-! ## 5. 縮約本体（house pattern） -/

/-- **`CornerCoreReadouts_cc`（«8».«8.4-corner-core»:190）の drop-in**（house pattern）。
LEAF3／LEAF5 を無条件に組み、LEAF4 を全域終切片輸送残差 `CornerNpSliceValue_cr2` から取る。 -/
theorem cornerCoreReadouts_of_residual (hNpVal : CornerNpSliceValue_cr2) :
    CornerCoreReadouts_cc := by
  intro M s0 b0 s1 b1 hST hmono hp hj1 hIV hadmeq _hd1' _hd2 hinner
  -- 注: `CornerCoreReadouts_cc` の入力 `hd1` は `Trans (oper M 1)` 版
  refine ⟨?_, ?_, ?_⟩
  · exact leaf3_cr2 M s0 b0 s1 b1 hST hmono hp hj1 hIV hadmeq _hd1' hinner
  · exact leaf4_cr2 hNpVal M s0 b0 hST hmono hp hj1 hIV hadmeq hinner
  · exact leaf5_cr2 M hST hmono hp hj1 hIV hadmeq

#print axioms cornerCoreReadouts_of_residual

end PSS
