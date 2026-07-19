import «8».«8.4-l6-readouts-close»

/-!
# §8.4 補題 part (2) の底読み出し `L6BaseCoreResidual` の Lp 半（葉 (4') と (2)）

（`L6BaseCoreResidual` の canonical 3 葉のうち **Lp 側の 2 葉**を、単一の
Lp 幾何残差 `LpReadoutResidual` へ縮約する。残る L₁ 側の葉 (3') は姉妹ファイルが扱う。）

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
- 対象: `«8».«8.4-l6-readouts-close»` が露出した canonical 残差 `L6BaseCoreResidual` の
  Lp 側 2 葉:
  * (2) `ub_eq`:  `(entry M 1 (s84x_jm2 M) : ℕ∞) = ub`（producer の挿入深 `ub` の pin）、
  * (4') `Lp = D_ub(insBody)`:
    `flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero))`。
- Isabelle（設計図）: `m_8_4_rightend_Trans`（`isabelle/layerB/pss_wip.thy:54650`）＋
  `s84d_dec*` の Lp 読み出し。`s84x_Lp M` は末尾列を差し替えた rightend 置換であり、
  `IncrFirst` で **単一の切片**（`seg`）に一致するので `Trans` は単一 principal になる
  （Isabelle: `Trans ((IncrFirst ^^ kk) (s84x_Lp M)) = Trans (s84x_Lp M)` ＋ slice の
  `Trans` は先頭 principal）。

## 本ファイルの寄与（house green-modulo、producer 座標の文字列代数を無条件に剥がす）

数値監査（`python/_l6_readouts_audit.py`、41/41）が確かめる 2 つの幾何事実——
* **(b) Lp 単一 principal**: `Trans (s84x_Lp M)` は単一 principal で、その頭指標は
  幾何量 `entry M 1 (s84x_jm2 M)`（`= M₁,ⱼ₋₂`、`slice_Trans_principal_head` の形）、
* **(a) Lp producer 平坦形（lpv 葉）**: `flatBT (Trans (s84x_Lp M)) = D_ub :: flatBT (ins 0_B)`
——を単一の named Prop `LpReadoutResidual` に束ね、そこから **葉 (4') と (2) を無条件に導く**:

* **(4')** は (a) の `flatBT` を `Dprin` へ畳むだけ（純粋な文字列代数）。
* **(2)** は **forcing**（本ファイルの核）: (a) と (b) はともに `flatBT (Trans (s84x_Lp M))`
  の表示であり、頭を突き合わせると `Sym.dsym ub = Sym.dsym (M₁,ⱼ₋₂)`、`Sym.dsym` の
  単射性から `ub = M₁,ⱼ₋₂`（＝ 葉 (2)）。ついでに body 平坦
  `flatBT (bpHeadT (Trans (s84x_Lp M))) = flatBT (ins 0_B)` も落ちる（`lp_body_flat_lpc`）。

**残差 `LpReadoutResidual`（`needs`）が真のブロッカー**: §8.4 の Lp 切片幾何
（Isabelle `m_8_4_rightend_Trans` / `s84d_dec*`、`cfbx_reg`（REGS/REGSP）正則性エンジン
消費、Lean 未移植の frontier）。producer 座標依存（`ub`/`ins`/`s0`/`b0` 等）は
`L6BaseCoreResidual` と同じ binder／同じ仮定として持ち込むので、`ub` を含む葉 (2) の
pin も本 wrapper が forcing で無条件に供給する（`ub` を仮定側から幾何量へ落とす結節点は
lpv 葉 (a) 一本に集約される）。

**なぜ (2) と (4') が結合しているか**（史料メモ）: 仮定 `hflat`/`fO`/`fM`/orderings は
`Trans (s84x_Lp M)` を producer 座標 `ub`/`ins` へ橋渡ししない（`ub_eq` は塔帰納
`l6_tower_l6` でも入力＝`hubeq` パラメータ）。よって (2)/(4') はいずれか一方を Lp 幾何
残差として持たねば導けない。本ファイルは lpv 葉 (a)（＝ (4') の平坦形）を残差に持ち、
純幾何の単一 principal 葉 (b) と頭突き合わせて (2) を **forcing** で導く形に整えた。

- 依存（すべてビルド済み・main e0f67cd）: «8».«8.4-l6-readouts-close»
  (`L6BaseCoreResidual`・`s84x_Lp`/`s84x_jm2`・`coreTower_e34`・`operB`/`numBT`・
  `Trans`/`oper`/`entry`/`Lng`・`Dprin`/`BZero`/`bpHeadT`/`bpHeadV`・`flatBT`/`flatBP`・
  `transCondIII`/`transCondIV`・`lessBT`/`leBT`・`Sym`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  producer 座標の文字列代数と (2) の forcing を無条件に剥がし、残差は Lp 幾何
  `LpReadoutResidual` 1 本（葉 (b)＋(a)）。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
- Private helper suffix: `_lpc`。
-/

namespace PSS

/-! ## 1. sharp な Lp 幾何残差（単一 principal 葉 (b) ＋ lpv 平坦葉 (a)） -/

/-- **`L6BaseCoreResidual` の Lp 側 2 葉を閉じるための sharp 残差**。
`L6BaseCoreResidual` と同じ binder／同じ仮定を持ち、結論を Lp 幾何の 2 事実に差し替えた:
* (b) `Trans (s84x_Lp M)` は単一 principal で頭指標 `= entry M 1 (s84x_jm2 M)`
  （`= M₁,ⱼ₋₂`、`slice_Trans_principal_head` の形。純幾何）、
* (a) その平坦形は producer 座標で `D_ub :: flatBT (ins 0_B)`（lpv 葉。`«8».«8.4-l6-slice-close»`
  `L6TowerResidual` の第 4 連言と同形）。

§8.4 Lp 切片幾何（Isabelle `m_8_4_rightend_Trans`/`s84d_dec*`、`cfbx_reg` 消費、
Lean 未移植 frontier）に属す。 -/
def LpReadoutResidual : Prop :=
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
    -- (b) 単一 principal（純幾何、頭 = M₁,ⱼ₋₂）
    (Trans (s84x_Lp M)
        = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) (bpHeadT (Trans (s84x_Lp M))))
    -- (a) lpv 平坦形（producer 座標）
    ∧ (flatBT (Trans (s84x_Lp M)) = Sym.dsym ub :: flatBT (ins BZero))

/-! ## 2. 葉 (4')（house pattern、文字列代数は無条件） -/

/-- **葉 (4')**（`L6BaseCoreResidual` の第 3 連言、`«8».«8.4-l6-readouts-close»:83`）を
verbatim に供給。lpv 葉 (a) の `flatBT` を `Dprin` へ畳むだけ（純粋な文字列代数）。 -/
theorem lp_readout_lpc (hres : LpReadoutResidual)
    (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero)) := by
  obtain ⟨_hb, ha⟩ :=
    hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase
  -- `flatBT (Dprin ub (ins 0_B)) = D_ub :: flatBT (ins 0_B)`（rfl）と (a) を突き合わせる
  show flatBT (Trans (s84x_Lp M)) = Sym.dsym ub :: flatBT (ins BZero)
  exact ha

/-! ## 3. 葉 (2)（forcing、`Sym.dsym` 単射性で `ub` を pin） -/

/-- **葉 (2)**（`L6BaseCoreResidual` の第 1 連言、`«8».«8.4-l6-readouts-close»:81`）を
verbatim に供給。**forcing**: 単一 principal 葉 (b) と lpv 葉 (a) はともに
`flatBT (Trans (s84x_Lp M))` の表示であり、頭を突き合わせると
`Sym.dsym ub = Sym.dsym (entry M 1 (s84x_jm2 M))`、`Sym.dsym` 単射から
`ub = entry M 1 (s84x_jm2 M)`。 -/
theorem ub_pin_lpc (hres : LpReadoutResidual)
    (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    (entry M 1 (s84x_jm2 M) : ℕ∞) = ub := by
  obtain ⟨hb, ha⟩ :=
    hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase
  -- (b) の `flatBT` 化: `flatBT (Trans (s84x_Lp M)) = D_{M₁,ⱼ₋₂} :: flatBT (body)`
  have hDp : flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) (bpHeadT (Trans (s84x_Lp M))))
      = Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT (bpHeadT (Trans (s84x_Lp M))) := rfl
  have hbflat : flatBT (Trans (s84x_Lp M))
      = Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT (bpHeadT (Trans (s84x_Lp M))) :=
    (congrArg flatBT hb).trans hDp
  -- (a) と (b) の頭を突き合わせる
  rw [ha] at hbflat
  -- hbflat : Sym.dsym ub :: flatBT (ins 0_B) = Sym.dsym (M₁,ⱼ₋₂) :: flatBT (bpHeadT …)
  have hhead : Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) = Sym.dsym ub :=
    (((List.cons.injEq _ _ _ _).mp hbflat).1).symm
  injection hhead

/-! ## 4. body 平坦の副産物（forcing の残り半分） -/

/-- forcing の副産物: Lp 単一 principal の body 平坦は producer の挿入 `ins 0_B` に一致。
（葉 (a)/(b) 頭突き合わせの tail 側。停止性連鎖には不要だが幾何橋の記録。） -/
theorem lp_body_flat_lpc (hres : LpReadoutResidual)
    (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    flatBT (bpHeadT (Trans (s84x_Lp M))) = flatBT (ins BZero) := by
  obtain ⟨hb, ha⟩ :=
    hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase
  have hDp : flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) (bpHeadT (Trans (s84x_Lp M))))
      = Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT (bpHeadT (Trans (s84x_Lp M))) := rfl
  have hbflat : flatBT (Trans (s84x_Lp M))
      = Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT (bpHeadT (Trans (s84x_Lp M))) :=
    (congrArg flatBT hb).trans hDp
  rw [ha] at hbflat
  exact (((List.cons.injEq _ _ _ _).mp hbflat).2).symm

/-! ## 5. Lp 半 2 葉の束（parent 合成用、`L6BaseCoreResidual` の (2)∧(4') 部分） -/

/-- **`L6BaseCoreResidual` の Lp 側 2 葉**（(2)∧(4')）を `LpReadoutResidual` modulo で束ねる。
L₁ 側の葉 (3') は姉妹ファイルが供給し、parent が三者を合成して `L6BaseCoreResidual` を得る。 -/
theorem lp_half2_lpc (hres : LpReadoutResidual)
    (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    ((entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
    ∧ (flatBT (Trans (s84x_Lp M)) = flatBT (Dprin ub (ins BZero))) :=
  ⟨ub_pin_lpc hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase,
   lp_readout_lpc hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase⟩

#print axioms lp_readout_lpc
#print axioms ub_pin_lpc
#print axioms lp_body_flat_lpc
#print axioms lp_half2_lpc

end PSS
