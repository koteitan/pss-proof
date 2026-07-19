import «8».«8.4-l6-base-readouts»

/-!
# §8.4 補題 part (2) の底読み出し残差 `L6BaseReadoutsResidual` の縮約
（producer 座標の文字列代数を剥がし、canonical な 3 葉 `L6BaseCoreResidual` へ）

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
- 対象: ビルド済み «8».«8.4-l6-base-readouts» が露出した底読み出し残差
  `L6BaseReadoutsResidual`（producer 座標 `ub`/`s0`/`b0`/`s1`/`b1`/`e3`/`A0`/`ins` を
  仮定として持つ 3 連言）。
- Isabelle（設計図）: `y3l_p_8_4_oper_basic_part2` の底読み出し部（`base5` / `s84d_dec*`）。

## 本ファイルの寄与（house green-modulo、文字列代数を無条件に剥がす）

Wave BA/AZ の診断: producer 証人（`ub`/`s0`/`b0`）は **canonical 値を知らないと pin できず**、
Isabelle ルート（`base5` / `s84d_dec*` / `y3i`）は未 port の `cfbx_reg`（REGS/REGSP）正則性
コーパスを消費する。本ファイルは、この残差の **producer 座標依存の文字列代数を完全に
剥がし**、canonical な 3 葉 `L6BaseCoreResidual` へ無条件に縮約する:

| `L6BaseReadoutsResidual` の葉 | `L6BaseCoreResidual` の canonical 形 | 剥がした代数 |
|---|---|---|
| (2) `ub_eq` | そのまま `(M₁,ⱼ₋₂ : ℕ∞) = ub` | — |
| (3) `L₁` 平坦式（producer 座標） | `flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0))` | `fO 0` ＋ `hflat BZero` |
| (4) `Lp` 平坦式（producer 座標） | `flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero))` | `hflat BZero` |

**鍵となる観察**（無条件・純代数）:
* `fO 0` は `flatBT (operB (Trans M) (numBT 0))` を **葉 (3) の RHS そのもの**に展開する
  （`coreTower_e34 ins 0_B 1 = ins 0_B`、`flatBT (ins 0_B) = s0 @ [D_ub, Z] @ b0`）。
  ゆえに葉 (3) ⟺ `flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0))`
  （＝ part (2) の n=1、producer 座標を一切含まない clean な等式）。
* `hflat 0_B` は `flatBT (Dprin ub (ins 0_B)) = D_ub :: (s0 @ [D_ub, Z] @ b0)` を与え、
  これは **葉 (4) の RHS そのもの**。ゆえに葉 (4) ⟺
  `flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins 0_B))`（Lp の `Trans` は単項 `D_ub(·)`）。

残る canonical 3 葉（`L6BaseCoreResidual`）が真のブロッカー: §8.4 の L₁/Lp 切片の
`Trans` canonical 値（`base5` / `s84d_dec*`、`cfbx_reg` 消費、Lean 未移植 frontier）。
数値監査（`python/_l6_readouts_audit.py`）: canonical 3 葉はいずれも真（41/41）——
(3') `Trans(L₁)==operB(TransM,numBT 0)`、Lp が単項、Lp の頭 `= M₁,ⱼ₋₂`（＝ (2) ub の pin）。
（Wave Y/BA の `MnformBottomResidual`／`Rm84LpValue` は偽だったが、**本 canonical 形は真**。）

- 依存（すべてビルド済み・main ba9a88d）: «8».«8.4-l6-base-readouts»
  (`L6BaseReadoutsResidual`・`oper_basic_part2_br`・`s84x_L`/`s84x_Lp`/`s84x_jm2`・
  `coreTower_e34`・`operB`/`numBT`・`Trans`/`oper`/`entry`/`Lng`・`Dprin`/`BZero`/
  `flatBT`/`flatBP`・`transCondIII`/`transCondIV`・`lessBT`/`leBT`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  producer 座標の文字列代数を無条件に剥がし、残差は canonical 3 葉 `L6BaseCoreResidual` 1 本。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
- Private helper suffix: `_rc`。
-/

namespace PSS

/-! ## 1. sharp な canonical 残差（producer 座標の文字列代数を剥がした 3 葉） -/

/-- **`L6BaseReadoutsResidual` を閉じるための sharp 残差**。producer 座標の文字列代数を
剥がした canonical 3 葉:
* (2) `ub_eq`: `(M₁,ⱼ₋₂ : ℕ∞) = ub`（producer の挿入深 `ub` の pin）、
* (3') `L₁ = operB base`: `flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0))`
  （part (2) の n=1、producer 座標を一切含まない）、
* (4') `Lp = D_ub(insBody)`: `flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero))`
  （Lp の `Trans` は単項 `D_ub(ins 0_B)`）。

（`L6BaseReadoutsResidual` と同じ binder／同じ仮定を持ち、結論だけを canonical 形に
差し替えた真に下位の残差。§8.4 L₁/Lp 切片幾何＝`cfbx_reg` 未 port frontier。） -/
def L6BaseCoreResidual : Prop :=
  ∀ (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 ≤ n →
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
    ((entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
    ∧ (flatBT (Trans (s84x_L M 1)) = flatBT (operB (Trans M) (numBT 0)))
    ∧ (flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero)))

/-! ## 2. 縮約本体（house pattern、文字列代数は無条件） -/

/-- **`L6BaseReadoutsResidual`（«8».«8.4-l6-base-readouts»:230）の drop-in**（house pattern）。
canonical 3 葉 `L6BaseCoreResidual` から、producer 座標の文字列代数（`fO 0`・`hflat BZero`）を
無条件に組み立てて元の 3 葉へ戻す。 -/
theorem l6BaseReadouts_of_core (hcore : L6BaseCoreResidual) : L6BaseReadoutsResidual := by
  intro M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
    hflat hb0 hb1 fO fM base0 base1 Lbase
  obtain ⟨hub, hL1, hLp⟩ :=
    hcore M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase
  -- `ins 0_B` の平坦形（`hflat` at `X = 0_B`）
  have hinsB : flatBT (ins BZero) = s0 ++ [Sym.dsym ub, Sym.zero] ++ b0 := by
    have h := hflat BZero
    have hz : flatBT BZero = [Sym.zero] := rfl
    rw [h, hz]
  -- operB 底段 `D_{e₃}(coreTower ins 0_B 1)` の平坦形（葉 (3) の中心）
  have hstep : flatBP (BP.db e3 (coreTower_e34 ins BZero (0 + 1)))
      = Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) := by
    show Sym.dsym e3 :: flatBT (ins BZero) = _
    rw [hinsB]
  refine ⟨hub, ?_, ?_⟩
  · -- 葉 (3): `hL1`（clean 等式）＋ `fO 0` の展開で producer 座標形へ
    rw [hL1, fO 0, hstep]
  · -- 葉 (4): `hLp`（Lp は単項）＋ `hflat 0_B` の展開で producer 座標形へ
    rw [hLp]
    show Sym.dsym ub :: flatBT (ins BZero) = _
    rw [hinsB]

/-! ## 3. §8.4 part (2) への合成（`L6BaseCoreResidual` modulo） -/

/-- **§8.4 補題 part (2)**（原文 `tmp/content.md` 5008）を sharp 残差
`L6BaseCoreResidual` modulo で供給。親連鎖 `oper_basic_part2_br ∘ l6BaseReadouts_of_core`
を合成し、producer 座標の文字列代数を除去した canonical 残差 1 本まで尖鋭化する。 -/
theorem oper_basic_part2_core (hcore : L6BaseCoreResidual)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    operB (Trans M) (numBT (n - 1)) =
      Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)] (oper M (n + 1))) :=
  oper_basic_part2_br (l6BaseReadouts_of_core hcore) M n hST hmono hn hp hj₁ hcond

#print axioms l6BaseReadouts_of_core
#print axioms oper_basic_part2_core

end PSS
