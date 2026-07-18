import «8».«8.4-exch84-regsp»
import «8».«8.4-parent-max»

/-!
# §8.4 交換パッケージ `Exch84_condIIIIV_slicepkg` の組み立て（`oi5_IIIIV_pkg`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- 対象: `Exch84_condIIIIV_slicepkg`（«8».«8.4-exch84-producer»:128、`oi5_IIIIV_pkg`
  (isabelle/layerC/pss_scratch.thy:1213) の出力を Lean 語彙に 1:1 で写した Prop、
  6 葉残差 bundle `TerminationResidual` の 1 つ `exch84slicepkg`）を、脚
  `mnform`/`base0`/`base1'` から**組み立てる**。

## Isabelle の組み立て構造（`oi5_IIIIV_pkg` ＋ ltJ 二分岐）

`oi5_IIIIV_pkg` は `ltJ`（`s84x_jm3 M < transJm1 M`）の下で成立し、REGS/REGSP/RUN を
discharge した上で `cpx_condIII_mnform` から `inner`/`k1`/`mnform` を、`crx_base0_of_run`
（condIV は `cnv_*`）から `base0`、`oy1_base1Y_*` から `base1'` を出す。
`slicepkg` は ltJ を仮定しない無条件形なので、`oi5_ltJ_or_IVadmeq`
(pss_scratch.thy:1453) の二分岐で覆う:

* **ltJ 枝** (`s84x_jm3 M < transJm1 M`): `cpx_condIII_mnform`
  = `Mnform_condIIIIV`（«8».«8.4-exch84-regsp»）。
* **condIV admeq 隅** (`transCondIV M ∧ Adm M (s84x_jm2 M) = transJm1 M`): `c4dx_condIV_k1`
  経由（そこでは `transC2 M = Trans (s84x_N M)`、`oi5_bodyOT` pss_scratch:1520-1554 参照）
  = 本ファイルが露出する `Mnform_condIV_admeq_sp`。

`condIII` では `adm M (lastParent M)` により `transJm1 M = transJ0 M` かつ
`s84x_jm2 M < transJ0 M`（`m_8_4_oper_props_1(1)` = `regs_jm2_lt_transJ0_holds`）なので
ltJ が必ず成立し、admeq 隅は condIV 専用（props.lean:42-43 の注記どおり）。

## 本ファイルの分担・状態

1. `ltJ_or_IVadmeq_sp`（**完全証明**）= Isabelle `oi5_ltJ_or_IVadmeq`。
   `regs_jm2_lt_transJ0_holds`（«8».«8.4-parent-max»、= `m_8_4_oper_props_1(1)`）＋
   `Adm_max`/`Adm_le`/`Adm_adm`（§6.3、許容化最大性）から二分岐を出す。
2. `SlicepkgMnformOut_sp`（def）= `oi5_IIIIV_pkg` の `obtain`（`inner`/`k1`/`mnform`）本体。
   `Mnform_condIIIIV` の出力そのもの（ltJ 仮定を除いた ∃ 束）。
3. `Mnform_condIV_admeq_sp`（named 残差）= condIV admeq 隅の `mnform`（`c4dx_condIV_k1`
   ルート）。ltJ 枝の `Mnform_condIIIIV` と同じ出力型を持つ。
4. `exch84slicepkg_holds`（**組み立て、green-modulo**）: 露出した 4 脚
   `Mnform_condIIIIV`（ltJ、«8».«8.4-exch84-regsp»）/ `Mnform_condIV_admeq_sp`（隅、本ファイル）
   / `Base0_condIIIIV`（«8».«8.4-exch84-regsp»、= `Base0_condIIIIV_holds` で `Base0_A0bridge`
   に縮約済）/ `Base1p_condIIIIV`（«8».«8.4-exch84-regsp»）から `Exch84_condIIIIV_slicepkg`
   を組む。`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`、
   `e₃ = M_{1,j₋₃}`、`v₁ = M_{1,Lng M-1}`。

これにより `TerminationResidual.exch84slicepkg` は 4 named 脚へ縮約される。うち 3 本
（`Mnform_condIIIIV`/`Base0_condIIIIV`/`Base1p_condIIIIV`）は既にツリーに露出済み、
新規は `Mnform_condIV_admeq_sp` の 1 本のみ。すべて Isabelle 側で証明済み＝bundle は充足可能。

- 依存（すべてビルド済み・committed）:
  «8».«8.4-exch84-regsp»（`Exch84_condIIIIV_slicepkg`（推移的に «8».«8.4-exch84-producer»）・
  `Mnform_condIIIIV`・`Base0_condIIIIV`・`Base1p_condIIIIV`・`coreTower_e34`・`s84x_*`・
  `scb_decomp`/`scb_kind1`/`Dprin`/`bpHeadT`・`transJm1`/`transJ0`/`transCondIII`/`transCondIV`・
  `Adm`/`Adm_le`/`Adm_adm`/`Adm_max`）、«8».«8.4-parent-max»（`regs_jm2_lt_transJ0_holds`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `ltJ_or_IVadmeq_sp` は無条件完全証明。`exch84slicepkg_holds` は上記 4 脚から完全に組む。
- Private helper suffix: `_sp`。
-/

namespace PSS

/-! ## 1. ltJ 二分岐（Isabelle `oi5_ltJ_or_IVadmeq`、完全証明） -/

/-- Isabelle `oi5_ltJ_or_IVadmeq` (layerC/pss_scratch.thy:1453)。
condIII/(IV) の `hasParent` ホストでは、`ltJ`（`s84x_jm3 M < transJm1 M`）が成立するか、
さもなくば condIV admeq 隅（`transCondIV M ∧ Adm M (s84x_jm2 M) = transJm1 M`）にいる。

証明: `j₋₂ < j₀`（`regs_jm2_lt_transJ0_holds` = `m_8_4_oper_props_1(1)`）と
`j₋₃ = Adm M j₋₂ ≤ j₋₂ < j₀`（`Adm_le`）から `j₋₃ ≤ j₀`、許容化最大性
`Adm_max`（`adm M j₋₃` は `Adm_adm`）で `j₋₃ ≤ Adm M j₀ = transJm1 M`。
`<` なら ltJ、`=` なら condIV（condIII だと `transJm1 = transJ0` で `j₋₃ = j₀` となり
`j₋₃ ≤ j₋₂ < j₀` に矛盾）。 -/
theorem ltJ_or_IVadmeq_sp (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    s84x_jm3 M < transJm1 M
      ∨ (transCondIV M = true ∧ Adm M (s84x_jm2 M) = transJm1 M) := by
  have jm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp hj1 hcond
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have admjm3 : adm M (s84x_jm3 M) = true := Adm_adm M (s84x_jm2 M)
  have jm3lej0 : s84x_jm3 M ≤ transJ0 M := by omega
  have le : s84x_jm3 M ≤ transJm1 M :=
    Adm_max M (s84x_jm3 M) (transJ0 M) admjm3 jm3lej0
  rcases le.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · -- heq : s84x_jm3 M = transJm1 M
    have cIV : transCondIV M = true := by
      rcases hcond with cIII | cIV
      · exfalso
        have hadmJ0 : adm M (transJ0 M) = true := by
          simp only [transCondIII, Bool.and_eq_true] at cIII
          exact cIII.2
        have hjm1eq : transJm1 M = transJ0 M := by
          simp [transJm1, Adm, hadmJ0]
        omega
      · exact cIV
    exact Or.inr ⟨cIV, heq⟩

/-! ## 2. `mnform` の出力（`oi5_IIIIV_pkg` の `obtain` 本体、`Mnform_condIIIIV` の出力型） -/

/-- Isabelle `oi5_IIIIV_pkg` (layerC/pss_scratch.thy:1213) の `obtain` 節本体
（`b0RP`/`b1RP`/`inner`/`k1`/`MNall`）を Lean 語彙で写した ∃ 束。
これは «8».«8.4-exch84-regsp» の `Mnform_condIIIIV` の**出力型そのもの**
（ltJ 仮定 `s84x_jm3 M < transJm1 M` を落とした形）。
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`、
`e₃ = M_{1,j₋₃}`、`v₁ = M_{1,Lng M-1}`、`ub = v₁ - 1`。 -/
def SlicepkgMnformOut_sp (M : PS) : Prop :=
  ∃ (ins : BT → BT) (s0 b0 s1 b1 : List Sym),
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) ∧
    (∀ x ∈ b0, x = Sym.rp) ∧
    (∀ x ∈ b1, x = Sym.rp) ∧
    scb_decomp (bpHeadT (Trans (s84x_N M))) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 ∧
    scb_kind1 (Trans M) s1
      (flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
                     (bpHeadT (Trans (s84x_N M))))) b1 ∧
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          (coreTower_e34 ins (bpHeadT (Trans (Pred (s84x_N M)))) (m - 1))) ++ b1)

/-- Isabelle の condIV admeq 隅の `mnform`（`c4dx_condIV_k1` ルート、
`oi5_bodyOT` pss_scratch:1520-1554 で `transC2 M = Trans (s84x_N M)` を経由して
`Mnform_condIIIIV` と同じ出力を作る段）を Lean 語彙で述べた named 残差。
ltJ 枝の `Mnform_condIIIIV`（«8».«8.4-exch84-regsp»）と**同じ出力型**
（`SlicepkgMnformOut_sp M`）を持つ。 -/
def Mnform_condIV_admeq_sp : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    SlicepkgMnformOut_sp M

/-! ## 3. `Exch84_condIIIIV_slicepkg` の組み立て（house pattern、green-modulo） -/

/-- `Exch84_condIIIIV_slicepkg`（«8».«8.4-exch84-producer»:128、`oi5_IIIIV_pkg` の出力）の
drop-in。4 脚から組む:

* `mnform`: ltJ 二分岐 `ltJ_or_IVadmeq_sp` で ltJ 枝は `Mnform_condIIIIV`（`hltJ`）、
  admeq 隅は `Mnform_condIV_admeq_sp`（`hcorner`）。どちらも `SlicepkgMnformOut_sp M`
  を出す。
* `base0`: `Base0_condIIIIV`（`hb0`）。
* `base1'`: `Base1p_condIIIIV`（`hb1`）に `mnform` の `ins`/`s0`/`b0`/`hflat`/`hb0RP`/`hinner`
  を渡す。

存在束の witness は `ins`（`mnform` から）、`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、
`body = bpHeadT (Trans (s84x_N M))`、`e₃ = M_{1,j₋₃}`、`v₁ = M_{1,Lng M-1}`。
残りの項（`hflat`/`b0RP`/`b1RP`/`inner`/`k1`/`mnform`）は `SlicepkgMnformOut_sp` と
`Exch84_condIIIIV_slicepkg` で同形（`ub = v₁ - 1` は nat 減算で defeq）。 -/
theorem exch84slicepkg_holds
    (hltJ : Mnform_condIIIIV) (hcorner : Mnform_condIV_admeq_sp)
    (hb0 : Base0_condIIIIV) (hb1 : Base1p_condIIIIV) :
    Exch84_condIIIIV_slicepkg := by
  intro M hST hmono hj1 hcond hp
  -- ltJ 二分岐で `mnform` の出力を得る
  have hmn : SlicepkgMnformOut_sp M := by
    rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hlt | ⟨hIV, hadmeq⟩
    · exact hltJ M hST hmono hp hj1 hcond hlt
    · exact hcorner M hST hmono hp hj1 hIV hadmeq
  obtain ⟨ins, s0, b0, s1, b1, hflat, hb0RP, hb1RP, hinner, hk1, hmnf⟩ := hmn
  refine ⟨ins, bpHeadT (Trans (Pred (s84x_N M))), bpHeadT (Trans (s84x_N M)),
    entry M 1 (s84x_jm3 M), entry M 1 (Lng M - 1), s0, b0, s1, b1,
    hflat, hb0RP, hb1RP, hinner, hk1, hmnf, ?_, ?_⟩
  · -- base0
    exact hb0 M hST hmono hp hj1 hcond
  · -- base1'
    exact hb1 M ins s0 b0 hST hmono hp hj1 hcond hflat hb0RP hinner

#print axioms ltJ_or_IVadmeq_sp
#print axioms exch84slicepkg_holds

end PSS
