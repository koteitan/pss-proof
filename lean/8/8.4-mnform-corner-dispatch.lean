import «8».«8.4-corner-redesign»
import «8».«8.4-exch84-mnform»
import «8».«8.4-exch84-mnform-bottom»
import «8».«8.4-exch84-regsp»
import «8».«8.4-exch84-producer»

/-!
# §8.4 `mnform` 鎖の `ltJ`/corner RE-DISPATCH（`8.4-corner-redesign` の反証を受けて）

## 背景（何が死んだか）

`8.4-corner-redesign` が **`Exch84_nestScbTriple`（無ガード）を機械反証**した
（`exch84_nestScbTriple_false_cr : ¬ Exch84_nestScbTriple`）。隅（condIV ∧ admeq,
`s84x_jm3 M = transJm1 M`）では切片が潰れ `Trans (s84x_N M) = transC2 M`／
`Trans (Pred (s84x_N M)) = transC1 M`（collapse 恒等式、`cornerCollapse_holds_cr`）となり、
非空 prefix `Dsym e₃ :: u1` を持つ c2/c3 の scb 分解が長さで不成立になるためである。

帰結として次の鎖が **死路**:

* `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362）— 全域偽。
* `Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370）— c2/c3 を束ねるため隅で偽。
* `MnformBottomResidual`（«8».«8.4-exch84-mnform-residual»）— 同上、隅で偽。
* `mnformBottomResidual_holds`（«8».«8.4-exch84-mnform-bottom»:108,
  `Exch84_nestScbTriple → MnformBottomExtResidual → MnformBottomResidual`）— 第 1 仮定が
  充足不能なので **live な供給者を持たない**。よって下流
  `mnformResidual_holds`（«8».«8.4-exch84-mnform-residual»,
  `MnformBottomResidual → (∀ M … → MnformResidual M)`）も供給者を失った。

しかし **`MnformResidual M`（«8».«8.4-exch84-mnform»:93）自身は隅でも真**（隅では
collapse ルートで組める。Isabelle `c4dx_condIV_k1`/`oi5_bodyOT`）。したがって下流の
`mnform_of_residual`／`Mnform_condIIIIV_mn`／`Mnform_condIV_admeq_sp_mn`／
`exch84slicepkg_holds`（すべて `MnformResidual M` を入力に取る）は生きている。
**必要なのは `∀ M … → MnformResidual M` を、死んだ底束を通さずに供給し直すこと**である。

## 本ファイルの RE-DISPATCH

`ltJ_or_IVadmeq_sp`（«8».«8.4-exch84-slicepkg», Isabelle `oi5_ltJ_or_IVadmeq`）で
`transCondIII ∨ transCondIV` の全域を `ltJ`（`s84x_jm3 M < transJm1 M`）と
condIV admeq 隅に**早期分岐**し、`MnformResidual M` を枝ごとに供給する:

* **ltJ 枝**: 証明済み nest エンジン `exch84_nestScbTriple_ltJ_holds_cr`
  （«8».«8.4-corner-redesign», `NestScbD4aTransport_ns` modulo）で c2/c3/c5 を得、
  c4 = `TransC2HoleDecomp_md`（本ファイル露出、Isabelle `d4c2_sd` private の twin）、
  `MnformBottomExtResidual`（«8».«8.4-exch84-mnform-bottom»）で hflat/c1/c7/L₁/M[1] を得、
  `ubeq` を無条件に足して底束を組み、`mnformResidual_of_bottom_md`（`mnformResidual_holds`
  の pointwise 読み出し）で `MnformResidual M` へ。
* **corner 枝**: collapse 恒等式 `cornerCollapse_holds_cr`（«8».«8.4-corner-redesign»,
  **完全証明**）で `Trans (s84x_N M) = transC2 M`／`Trans (Pred (s84x_N M)) = transC1 M`
  を得、それで `MnformResidual M` を `MnformCornerResidual_md`（本ファイル露出、Isabelle
  `oi5_bodyOT`：transC2/transC1 語彙の隅 mnform データ）から書き換えて組む。

これで死んだ `mnformBottomResidual_holds ∘ mnformResidual_holds` の合成を、
live な `mnformResidual_dispatch_md` に置換する。slicepkg 組み立て
`exch84slicepkg_of_dispatch_md` は既存の `Mnform_condIIIIV_mn`／
`Mnform_condIV_admeq_sp_mn`／`exch84slicepkg_holds` を再利用して
`Exch84_condIIIIV_slicepkg`（= `TerminationResidual.exch84slicepkg`）を組む。

## 露出する named 残差（`needs`）

* `NestScbD4aTransport_ns`（既出、«8».«8.4-exch84-nest-scb»）— d4a 転送。
* `MnformBottomExtResidual`（既出、«8».«8.4-exch84-mnform-bottom»）— hflat/c1/c7/L₁/M[1]。
* `TransC2HoleDecomp_md`（本ファイル）— c4（Isabelle `d4c2_sd`, Lean は private で近寄れず）。
* `MnformCornerResidual_md`（本ファイル）— 隅 mnform データ（Isabelle `oi5_bodyOT` 未移植）。
* `Base0_condIIIIV`／`Base1p_condIIIIV`（既出、«8».«8.4-exch84-regsp»）— slicepkg の残り 2 脚。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_md`。
-/

namespace PSS

/-! ## 0. 読み出し補助（«8».«8.4-exch84-mnform-residual» の private helper の再掲、suffix `_md`） -/

/-- `flatBT t = Dsym v :: rest` なら `flatBT (bpHeadT t) = rest`
（Isabelle `vf2x_flat_head_bpHeadT`）。`mnform-residual` の private `flat_head_bpHeadT_mr2` の再掲。 -/
private theorem flat_head_bpHeadT_md {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `flatBT t = Dsym v :: rest` なら `t = D_v (bpHeadT t)`（Isabelle `w84x_flat_head_Dpt`）。
`mnform-residual` の private `princ_of_flat_mr2` の再掲。 -/
private theorem princ_of_flat_md {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : t = Dprin v (bpHeadT t) := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      obtain ⟨h1, _⟩ := h
      simp only [Sym.dsym.injEq] at h1
      simp only [bpHeadT, Dprin, h1]
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `isPTB_str (flatBT (D_{n} 0_B))`（Isabelle `isPTB_str_Dpt`）。`mnform-residual` の
private `isPTB_Dprin_nat_mr2` の再掲。 -/
private theorem isPTB_Dprin_nat_md (n : ℕ) :
    isPTB_str (flatBT (Dprin (n : ℕ∞) BZero)) :=
  ⟨.db (n : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩

/-- `ubeq`（Isabelle `cpx_condIII_mnform` の `ubeq`、RedCondA ランプ）の無条件討伐。
«8».«8.4-exch84-mnform-bottom» の private `ubeq_mb` と同じ。 -/
private theorem ubeq_md (M : PS) (hST : STPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1 := by
  have condA : RedCondA M = true := (RTPS_condAB M (STPS_RTPS M hST)).1
  have hLM : Lng M - 1 < Lng M := by omega
  simp only [RedCondA, List.all_eq_true] at condA
  have hbody := condA 1 (by decide) (Lng M - 1) (List.mem_range.mpr hLM)
  rw [hp] at hbody
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
  have ramp : entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) := hbody
  omega

/-! ## 1. 露出する named 残差（本ファイル固有の genuinely-missing legs） -/

/-- **c4 残差**（Isabelle `d4c2_sd`, isabelle/layerB `cpx_various_scb_IIIIV` の `c4_1`）。
`transC2 M` の末尾 principal `D_{M₁,ₗₙ₋₁} 0_B` を露出する scb 分解。Lean 側の証明
（«8».«8.4-exch84-scbdecomp» の `d4c2_sd`）は **private** で import 越しに見えないため、
named Prop として露出する（`hcond` のみ消費、ltJ 非依存）。 -/
def TransC2HoleDecomp_md : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    ∃ u2 v2 : List Sym,
      scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2

/-- **隅 mnform 残差**（Isabelle condIV admeq 隅 `oi5_bodyOT`
(isabelle/layerC/pss_scratch.thy:1520-1554) / `c4dx_condIV_k1`）。隅（condIV ∧ admeq）では
collapse 恒等式で `Trans (s84x_N M) = transC2 M`／`Trans (Pred (s84x_N M)) = transC1 M`
となるので、隅 mnform データを **transC2/transC1 語彙**で述べる（`MnformResidual M` の
`Trans (s84x_N M)` 語彙を collapse で書き換えると本 Prop になる）。REGS/REGSP 隅エンジンは
Lean 未移植のため named Prop。 -/
def MnformCornerResidual_md : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    ∃ (ins : BT → BT) (s0 b0 s1 b1 : List Sym),
      (∀ X, flatBT (ins X)
          = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) ∧
      (∀ x ∈ b0, x = Sym.rp) ∧
      (∀ x ∈ b1, x = Sym.rp) ∧
      scb_decomp (bpHeadT (transC2 M)) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 ∧
      scb_kind1 (Trans M) s1
        (flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
                       (bpHeadT (transC2 M)))) b1 ∧
      entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1 ∧
      flatBT (Trans (oper M 1))
        = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: flatBT (bpHeadT (transC1 M)) ++ b1 ∧
      flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ b0 ++ b1 ∧
      flatBT (Trans (s84x_Lp M))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ b0) ∧
      flatBT (Trans (Pred (s84x_Np M)))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: flatBT (bpHeadT (transC1 M))

/-! ## 2. `MnformResidual M` の pointwise 読み出し（`mnformResidual_holds` の 1 点版） -/

/-- **底束の pointwise 読み出し**。`MnformBottomResidual` の ∃ 束（1 点 `M` 分）を明示引数で受け、
`MnformResidual M`（«8».«8.4-exch84-mnform»:93）を組む。«8».«8.4-exch84-mnform-residual»
の `mnformResidual_holds` の本体を 1 点化したもの。ltJ には非依存（読み出しは純代数）。 -/
private theorem mnformResidual_of_bottom_md (M : PS)
    (ins : BT → BT) (u0 u1 u2 v2 v1 v0 : List Sym)
    (hflat : ∀ X, flatBT (ins X)
        = (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞)
            :: flatBT X ++ (v2 ++ v1))
    (hc1 : scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0)
    (hc2 : scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1)
    (hc3 : scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1)
    (hc4 : scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (hc5 : scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1)
    (hc7 : scb_decomp (Trans (s84x_Lp M))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
        (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1))
    (hL1flat : flatBT (Trans (s84x_L M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ (v2 ++ v1) ++ v0)
    (hM1flat : flatBT (Trans (oper M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: u1 ++ flatBT (transC1 M) ++ v1 ++ v0)
    (hub : entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1) :
    MnformResidual M := by
  -- `c3` の頭形（`Trans N = D_{e₃} :: ...`）→ `princN`、`fbody`
  have c3flat : flatBT (Trans (s84x_N M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: (u1 ++ flatBT (transC2 M) ++ v1) := by
    have h := hc3.1; simpa [List.cons_append] using h
  have princN : Trans (s84x_N M)
      = Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) (bpHeadT (Trans (s84x_N M))) :=
    princ_of_flat_md c3flat
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1 :=
    flat_head_bpHeadT_md c3flat
  -- `c2` の頭形 → `fA0`
  have c2flat : flatBT (Trans (Pred (s84x_N M)))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: (u1 ++ flatBT (transC1 M) ++ v1) := by
    have h := hc2.1; simpa [List.cons_append] using h
  have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1 :=
    flat_head_bpHeadT_md c2flat
  -- `b0 = v2++v1`（全 RP）、`b1 = v0`（全 RP）
  have hb0rp : ∀ x ∈ (v2 ++ v1), x = Sym.rp := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hc4.2.2 x h
    · exact hc3.2.2 x h
  have hb1rp : ∀ x ∈ v0, x = Sym.rp := hc1.1.2.2
  -- 出力束
  refine ⟨ins, u1 ++ u2, v2 ++ v1, u0, v0, hflat, hb0rp, hb1rp, ?_, ?_, hub, ?_, ?_, ?_, ?_⟩
  · -- `hinner`
    refine ⟨?_, fun _ => isPTB_Dprin_nat_md (entry M 1 (Lng M - 1)), hb0rp⟩
    rw [fbody, hc4.1]
    simp only [List.append_assoc]
  · -- `hk1`
    have hbeq : flatBT (Trans (s84x_N M))
        = flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            (bpHeadT (Trans (s84x_N M)))) := congrArg flatBT princN
    exact hbeq ▸ hc1
  · -- `hM1`
    rw [hM1flat, fA0]
    simp only [List.cons_append, List.append_assoc]
  · -- `hL1`
    have h := hL1flat
    simpa [List.cons_append, List.append_assoc] using h
  · -- `hLp`
    have hDe2 : flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)
        = [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] := rfl
    have h := hc7.1
    rw [hDe2] at h
    simpa [List.cons_append, List.append_assoc] using h
  · -- `hPN`
    have c5flat : flatBT (Trans (Pred (s84x_Np M)))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: (u1 ++ flatBT (transC1 M) ++ v1) := by
      have h := hc5.1; simpa [List.cons_append] using h
    rw [c5flat, ← fA0]

/-! ## 3. ltJ 枝の供給（証明済み nest エンジン + 既存残差 + 読み出し） -/

/-- **ltJ 枝の `MnformResidual` 供給**。`exch84_nestScbTriple_ltJ_holds_cr`
（«8».«8.4-corner-redesign», `NestScbD4aTransport_ns` modulo）で c2/c3/c5、
`TransC2HoleDecomp_md` で c4、`MnformBottomExtResidual` で hflat/c1/c7/L₁/M[1]、
`ubeq_md` で ubeq を組み、`mnformResidual_of_bottom_md` で読み出す。 -/
theorem mnformResidualLtJ_holds_md
    (hD4a : NestScbD4aTransport_ns) (hC4 : TransC2HoleDecomp_md)
    (hext : MnformBottomExtResidual) :
    ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
      s84x_jm3 M < transJm1 M → MnformResidual M := by
  intro M hST hmono hp hj1 hcond hltJ
  -- nest エンジン（ltJ ガード付き三つ組）から c2/c3/c5
  obtain ⟨u1, v1, dP, d2, d4a⟩ :=
    exch84_nestScbTriple_ltJ_holds_cr hD4a M hST hmono hp hj1 hcond hltJ
  -- c4
  obtain ⟨u2, v2, d4c2⟩ := hC4 M hST hmono hp hj1 hcond
  -- hflat/c1/c7/L₁/M[1]
  obtain ⟨ins, u0, v0, hflat, hc1, hc7, hL1flat, hM1flat⟩ :=
    hext M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  -- ubeq
  have hub := ubeq_md M hST hp hj1
  -- 読み出し
  exact mnformResidual_of_bottom_md M ins u0 u1 u2 v2 v1 v0
    hflat hc1 dP d2 d4c2 d4a hc7 hL1flat hM1flat hub

/-! ## 4. corner 枝の供給（collapse 恒等式ルート、`cornerCollapse_holds_cr`） -/

/-- **corner 枝の `MnformResidual` 供給**。隅（condIV ∧ admeq）では collapse 恒等式
`cornerCollapse_holds_cr`（«8».«8.4-corner-redesign», 完全証明）で
`Trans (s84x_N M) = transC2 M`／`Trans (Pred (s84x_N M)) = transC1 M`。それで
transC2/transC1 語彙の隅 mnform データ `MnformCornerResidual_md` を `MnformResidual M`
の `Trans (s84x_N M)` 語彙へ戻す。 -/
theorem mnformResidualCorner_holds_md (hcorner : MnformCornerResidual_md) :
    ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
      MnformResidual M := by
  intro M hST hmono hp hj1 hIV hadmeq
  -- collapse 恒等式
  obtain ⟨cN, cPN⟩ :=
    cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
  -- 隅 mnform データ（transC2/transC1 語彙）
  obtain ⟨ins, s0, b0, s1, b1, hflat, hb0rp, hb1rp, hinner, hk1, hub, hM1, hL1, hLp, hPN⟩ :=
    hcorner M hST hmono hp hj1 hIV hadmeq
  -- collapse で transC2/transC1 → Trans (s84x_N M)/Trans (Pred (s84x_N M)) へ戻す
  have hbN : bpHeadT (transC2 M) = bpHeadT (Trans (s84x_N M)) := by rw [cN]
  have hbPN : bpHeadT (transC1 M) = bpHeadT (Trans (Pred (s84x_N M))) := by rw [cPN]
  refine ⟨ins, s0, b0, s1, b1, hflat, hb0rp, hb1rp, ?_, ?_, hub, ?_, hL1, hLp, ?_⟩
  · -- inner: bpHeadT (Trans (s84x_N M))
    rw [← hbN]; exact hinner
  · -- k1: bpHeadT (Trans (s84x_N M))
    rw [← hbN]; exact hk1
  · -- hM1: bpHeadT (Trans (Pred (s84x_N M)))
    rw [← hbPN]; exact hM1
  · -- hPN: bpHeadT (Trans (Pred (s84x_N M)))
    rw [← hbPN]; exact hPN

/-! ## 5. 全域 `MnformResidual` の dispatch（`ltJ_or_IVadmeq_sp` で二分岐） -/

/-- **RE-DISPATCH の本体**。`ltJ_or_IVadmeq_sp`（«8».«8.4-exch84-slicepkg»）で
`transCondIII ∨ transCondIV` を ltJ/corner に分岐し、`∀ M … → MnformResidual M` を供給する。
死んだ `mnformResidual_holds ∘ mnformBottomResidual_holds` の drop-in 置換。 -/
theorem mnformResidual_dispatch_md
    (hD4a : NestScbD4aTransport_ns) (hC4 : TransC2HoleDecomp_md)
    (hext : MnformBottomExtResidual) (hcorner : MnformCornerResidual_md) :
    ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) → MnformResidual M := by
  intro M hST hmono hp hj1 hcond
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hlt | ⟨hIV, hadmeq⟩
  · exact mnformResidualLtJ_holds_md hD4a hC4 hext M hST hmono hp hj1 hcond hlt
  · exact mnformResidualCorner_holds_md hcorner M hST hmono hp hj1 hIV hadmeq

/-! ## 6. slicepkg 組み立ての rewire（既存 `exch84slicepkg_holds` へ配線） -/

/-- **`Exch84_condIIIIV_slicepkg` の rewire**（= `TerminationResidual.exch84slicepkg`）。
RE-DISPATCH で全域 `MnformResidual` を供給し、既存の `Mnform_condIIIIV_mn`
（ltJ 脚）／`Mnform_condIV_admeq_sp_mn`（corner 脚）／`exch84slicepkg_holds` へ配線。
死んだ nest 三つ組ルートを一切通さない。残差 6 本（`needs`）へ縮約。 -/
theorem exch84slicepkg_of_dispatch_md
    (hD4a : NestScbD4aTransport_ns) (hC4 : TransC2HoleDecomp_md)
    (hext : MnformBottomExtResidual) (hcorner : MnformCornerResidual_md)
    (hb0 : Base0_condIIIIV) (hb1 : Base1p_condIIIIV) :
    Exch84_condIIIIV_slicepkg := by
  have hres := mnformResidual_dispatch_md hD4a hC4 hext hcorner
  exact exch84slicepkg_holds (Mnform_condIIIIV_mn hres) (Mnform_condIV_admeq_sp_mn hres) hb0 hb1

#print axioms mnformResidualLtJ_holds_md
#print axioms mnformResidualCorner_holds_md
#print axioms mnformResidual_dispatch_md
#print axioms exch84slicepkg_of_dispatch_md

end PSS
