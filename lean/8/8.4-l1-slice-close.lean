import «8».«8.4-l6-readouts-close»

/-!
# §8.4 補題 part (2) の canonical 底葉 (3') `L₁ = operB base` の縮約
（producer 側 `fO 0` peel ＋ 無条件 `L₁` 幾何 `oper_rule_basic_part5` で sharp wrapper 残差へ）

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
- 対象: «8».«8.4-l6-readouts-close» が露出した canonical 3 葉 `L6BaseCoreResidual` のうち
  **葉 (3')**（`base5` の canonical 形）:

    `flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0))`

  （part (2) の n=1、producer 座標を一切含まない clean な等式）。
- Isabelle（設計図）: `base5`（`isabelle/layerB/pss_wip.thy`:60231）＝
  `s84d_L1_data` ＋ `s84d_c2hole_L1` ＋ c2hole hole engine で `L₁` 平坦式を組み、
  wrapper pinning `sbL : s1L = s1 ∧ b1L = b1`（`s84c2_Trans_c2_decomp(L₁)` と `dc1`）で
  `L₁` の scb wrapper を `M` の producer wrapper に一致させる。

## 本ファイルの寄与（house green-modulo、両側を無条件に peel し wrapper 残差 1 本へ）

葉 (3') の両辺を無条件に canonical な平坦形へ剥がし、残差を **`L₁` 幾何の scb wrapper が
producer 座標の組立 wrapper に一致する**という sharp な wrapper 恒等式 `L1SliceWrapperBridge`
1 本へ縮約する:

1. **RHS（operB 側）**: `fO 0` ＋ `hflat 0_B` で
   `flatBT (operB (Trans M) (numBT 0)) = s1 ++ D_{e₃} # (s0 ++ [D_ub, Z] ++ b0) ++ b1`
   に無条件展開（`coreTower_e34 ins 0_B 1 = ins 0_B`、`flatBT (ins 0_B) = s0 @ [D_ub,Z] @ b0`）。
   ＝«8».«8.4-l6-readouts-close» の `hstep`/`hinsB` と同一 peel。
2. **LHS（`L₁` 側）**: 無条件単一段補題 `oper_rule_basic_part5`（«8».«8.4-oper-basic»、
   Isabelle `m_8_4_oper_props_5`、条件(III)/(IV)・admeq 不要）を **n = 2** で読むと、その第 1 連言が
   `scb_decomp (Trans (s84x_L M 1)) sb.1 (flatBT (D_{M₁,ⱼ₋₂} 0)) sb.2`
   （`s84x_L M (2-1) = s84x_L M 1`、中心穴 `D_{M₁,ⱼ₋₂} 0`）を与える。ゆえに無条件に
   `flatBT (Trans (s84x_L M 1)) = sb.1 ++ [D_{M₁,ⱼ₋₂}, Z] ++ sb.2`。
3. 残差 `L1SliceWrapperBridge`: この幾何 wrapper `(sb.1, sb.2)` が producer の組立 wrapper
   `(s1 ++ D_{e₃} # s0, b0 ++ b1)` に一致し、かつ `M₁,ⱼ₋₂ = ub`（葉 (2) の pin）。
   これは Isabelle `base5` の `sbL`（wrapper 一致）＋`holeL1`（c2hole）＋葉 (2) を
   scb 一意性で束ねた形そのもの（(3) が真かつ葉 (2) が真なら scb 一意性で成立、真正）。

残る `L1SliceWrapperBridge` が真のブロッカー（§8.4 の `L₁` 切片幾何 `s84d_L1_data`/
`s84d_c2hole_L1` ＋ wrapper pinning、`cfbx_reg` 消費の Lean 未移植 frontier）。
既移植資産: `l1SliceData_holds`（«8».«8.4-l1-slice-data»、`transC2(L₁) = c2hole`）と
`leaf3_cr2`（«8».«8.4-corner-readouts»、condIV∧admeq 隅の `L₁` 平坦式）が discharge の材料。

- 依存（すべてビルド済み・main e0f67cd）: «8».«8.4-l6-readouts-close»
  （`L6BaseCoreResidual`・推移的に `oper_rule_basic_part5`・`s84x_L`/`s84x_jm2`・
  `coreTower_e34`・`operB`/`numBT`・`Trans`/`oper`/`entry`/`Lng`・`Dprin`/`BZero`・
  `flatBT`/`flatBP`・`scb_decomp`・`transCondIII`/`transCondIV`・`lessBT`/`leBT`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  葉 (3') の両側を無条件 peel し、残差は sharp wrapper 恒等式 `L1SliceWrapperBridge` 1 本。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
- Private helper suffix: `_l1c`。
-/

namespace PSS

/-! ## 1. sharp な wrapper 残差（`L₁` 幾何 wrapper ＝ producer 組立 wrapper） -/

/-- **葉 (3') を閉じるための sharp 残差**。無条件 `oper_rule_basic_part5`（n=2）が与える
`L₁ := s84x_L M 1` の scb 分解 `sb`（中心穴 `D_{M₁,ⱼ₋₂} 0`）に対し、その wrapper が
producer 座標の組立 wrapper `(s1 ++ D_{e₃} # s0, b0 ++ b1)` に一致し、かつ挿入深
`M₁,ⱼ₋₂ = ub`（葉 (2) の pin）であることを主張する。

Isabelle `base5`（`isabelle/layerB/pss_wip.thy`:60231）の wrapper pinning `sbL`
（`s84c2_Trans_c2_decomp(L₁)` の分解を `M` 側 `dc1` に scb 一意性で結ぶ）＋`holeL1`
（`s84d_c2hole_L1`）＋葉 (2) を束ねた形。**未移植**（§8.4 `L₁` 切片幾何 frontier）。

（`L6BaseCoreResidual` と同じ producer 仮定に、幾何分解 `sb` を追加で束ねる。(3) と葉 (2)
が真なら scb 一意性で成立するので真正な残差。） -/
def L1SliceWrapperBridge : Prop :=
  ∀ (M : PS) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym) (sb : List Sym × List Sym),
    STPS M → monoT M = true →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ x ∈ b1, x = Sym.rp) →
    (∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ub BZero) A0 = true →
    lessBT A0 (ins (Dprin ub BZero)) = true →
    leBT (Dprin ub BZero) (ins BZero) = true →
    scb_decomp (Trans (s84x_L M 1)) sb.1
      (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2 →
    ((entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
      ∧ sb.1 = s1 ++ Sym.dsym e3 :: s0
      ∧ sb.2 = b0 ++ b1

/-! ## 2. 葉 (3') の証明（両側 peel ＋ wrapper 残差） -/

/-- **`L6BaseCoreResidual` の葉 (3')**（`base5` の canonical 形、原文 part (2) の n=1）:

    `flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0))`.

`L6BaseCoreResidual` の全 producer 仮定を持ち込み（house pattern の drop-in、`n`/`hn` も
verbatim に保持）、RHS を `fO 0`＋`hflat 0_B` で、LHS を無条件 `oper_rule_basic_part5`（n=2）の
`L₁` scb 分解で peel し、残差は wrapper 恒等式 `L1SliceWrapperBridge` 1 本。 -/
theorem l6_base_leaf3_holds (hbridge : L1SliceWrapperBridge)
    (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp)
    (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0)) := by
  -- RHS（operB 側）の無条件 peel（«8».«8.4-l6-readouts-close» の `hinsB`/`hstep` と同一）
  have hinsB : flatBT (ins BZero) = s0 ++ [Sym.dsym ub, Sym.zero] ++ b0 := by
    have h := hflat BZero
    have hz : flatBT BZero = [Sym.zero] := rfl
    rw [h, hz]
  have hRHS : flatBT (operB (Trans M) (numBT 0))
      = s1 ++ Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) ++ b1 := by
    have hstep : flatBP (BP.db e3 (coreTower_e34 ins BZero (0 + 1)))
        = Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) := by
      show Sym.dsym e3 :: flatBT (ins BZero) = _
      rw [hinsB]
    rw [fO 0, hstep]
  -- LHS（`L₁` 側）の無条件 scb 分解（`oper_rule_basic_part5` at n=2、第 1 連言）
  obtain ⟨sb, ⟨hSL1, _, _⟩, _⟩ := oper_rule_basic_part5 M 2 hST hmono hp hj1 (by norm_num)
  have hSL1' : scb_decomp (Trans (s84x_L M 1)) sb.1
      (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2 := hSL1
  -- wrapper 残差
  obtain ⟨hub, hsb1, hsb2⟩ := hbridge M ins A0 e3 ub s0 b0 s1 b1 sb
    hST hmono hp hj1 hcond hflat hb0 hb1 fO fM base0 base1 Lbase hSL1'
  -- LHS を組立 wrapper へ
  have hLHS : flatBT (Trans (s84x_L M 1)) = sb.1 ++ [Sym.dsym ub, Sym.zero] ++ sb.2 := by
    have h := hSL1'.1
    have hc : flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)
        = [Sym.dsym ub, Sym.zero] := by
      rw [hub]; simp [Dprin, flatBT, flatBP, BZero]
    rw [hc] at h; exact h
  -- 両側の canonical 平坦形を突き合わせる
  rw [hLHS, hRHS, hsb1, hsb2]
  simp [List.append_assoc, List.cons_append]

#print axioms l6_base_leaf3_holds

end PSS
