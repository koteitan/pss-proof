import «8».«8.4-scbdecomp-pkg»

/-!
# §8.4 交換パッケージの Base 脚（`Base0_condIIIIV` / `Base1p_condIIIIV`）の ltJ/corner 再証明

- 原文: `tmp/content.md` §8.4。逐語形 = `p_8_4_Trans_oper_exchange`
  (isabelle/pss_paper.thy:1909)。Base 脚は Isabelle `oi5_IIIIV_pkg` の `base0`/`base1'`。
- ミッション: 死んだ `Exch84_scbDecompPkg`（無ガード、«8».«8.4-scbdecomp-pkg» で機械反証
  `Exch84_scbDecompPkg_refuted_sp2`）を通さず、`ltJ_or_IVadmeq_sp`
  （«8».«8.4-exch84-slicepkg»）の ltJ/corner dispatch で 2 脚を再証明する。

## 成果物

1. **`base0A0bridge_holds_bl3 (hcorner : MnformCornerResidual_md) : Base0_A0bridge`**（Leg 1）。
   ltJ 側は無条件 ltJ pkg `exch84ScbDecompPkgLtJ_holds_sp2`（«8».«8.4-scbdecomp-pkg»）の
   `dP`＋`c5`（共通 `(u1,v1)`、inner 共通 `flatBT (transC1 M)`）から flat 一致→`unflatBT`。
   corner 側は collapse 恒等式 `cornerCollapse_holds_cr`（«8».«8.4-corner-redesign»）＋
   `MnformCornerResidual_md` の hPN conjunct で両辺 `bpHeadT (transC1 M)` に潰す。
   `MnformCornerResidual_md` は slicepkg dispatch が既に消費する残差なので新規負債ゼロ。
   → `base0CondIIIIV_holds_bl3` で `Base0_condIIIIV`（house pattern, `Base0_condIIIIV_holds`）。

2. **`base1pCondIIIIV_holds_bl3 (hcorner1 : Base1pCorner_bl3) : Base1p_condIIIIV`**（Leg 2）。
   ltJ 側は ltJ pkg ＋ `Cnv_c2_shape_condIV_holds`/`Cnv_nested_hole_pair_holds`
   （«8».«8.4-exch84-scbdecomp»、closed）＋ base1p の oy1 論法の再移植（`_bl3` suffix）。
   corner 側は collapse で `Trans (s84x_N M)`/`Trans (Pred (s84x_N M))` を
   `transC2 M`/`transC1 M` に書き換え、隅専用 base1' 順序 fact `Base1pCorner_bl3`
   （named 残差、Isabelle 隅 base1' `oy1_base1Y_condIV` の admeq 退化版）へ帰着。

## 依存（すべてビルド済み・committed at 9ced7bd）

- «8».«8.4-scbdecomp-pkg»（推移的に «8».«8.4-slicepkg-residuals» → …）:
  `exch84ScbDecompPkgLtJ_holds_sp2`・`Exch84_scbDecompPkg_ltJ_sp2`・`Base0_A0bridge`・
  `Base0_condIIIIV`・`Base0_condIIIIV_holds`・`Base1p_condIIIIV`・`Cnv_c2_shape_condIV`・
  `Cnv_nested_hole_pair`・`Cnv_c2_shape_condIV_holds`・`Cnv_nested_hole_pair_holds`・
  `ltJ_or_IVadmeq_sp`・`cornerCollapse_holds_cr`・`MnformCornerResidual_md`・
  `c1_shape_holds`・`add_scb_marked`・`add_scb_replace_last`・
  `scb_unique_decomp_unconditional`・`lessBT_addBT_self`・`scbext_lessBT`・
  `transC1`/`transC2`/`transV`/`transT2`/`s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`。

## 状態

- 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 named Prop = `MnformCornerResidual_md`（既出、slicepkg dispatch が消費する既存残差、
  新規負債ゼロ）・`Base1pCorner_bl3`（隅 base1' 順序 fact、新規）。
- Private helper suffix: `_bl3`。
-/

namespace PSS

/-! ## 0. 純 `T_B`/scb 補助（base1p の private helper の再掲、suffix `_bl3`） -/

/-- Isabelle `vf2x_flat_head_bpHeadT` (layerB/pss_wip.thy:69403) の移植:
`flatBT t = Dsym v # rest` なら `flatBT (bpHeadT t) = rest`。base1p の private
`flat_head_bpHeadT_b1p` の再掲。 -/
private theorem flat_head_bpHeadT_bl3 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-! ## 1. Leg 1: `Base0_A0bridge` の ltJ/corner dispatch（`MnformCornerResidual_md` modulo） -/

/-- **`Base0_A0bridge`（«8».«8.4-exch84-base0»:326）の pkg 非依存 discharge**。
`ltJ_or_IVadmeq_sp` で `transCondIII ∨ transCondIV` を ltJ/corner に分岐:
- ltJ: 無条件 ltJ pkg `exch84ScbDecompPkgLtJ_holds_sp2` の `dP`（`s84x_N`）と
  `c5`（`s84x_Np`）が共通 `(u1,v1)`・共通 inner `flatBT (transC1 M)` を持つので
  `bpHeadT (Trans (Pred ·))` の flat 一致→`unflatBT` で潰す（`Base0_A0bridge_holds` と同型）。
- corner: `cornerCollapse_holds_cr` で `Trans (Pred (s84x_N M)) = transC1 M`、
  `MnformCornerResidual_md` の hPN で `flatBT (Trans (Pred (s84x_Np M)))
  = Dsym e₂ :: flatBT (bpHeadT (transC1 M))`。両辺 `bpHeadT (transC1 M)` に潰す。 -/
theorem base0A0bridge_holds_bl3 (hcorner : MnformCornerResidual_md) : Base0_A0bridge := by
  intro M hST hmono hp hj1 hcond
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hltJ | ⟨hIV, hadmeq⟩
  · -- ltJ 枝: ltJ pkg の dP + c5
    obtain ⟨_hT1, u1, u2, v1, v2, dP, _d2, _d4c2, c5⟩ :=
      exch84ScbDecompPkgLtJ_holds_sp2 M hST hmono hp hj1 hcond hltJ
    have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1 := by
      apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    have fNp : flatBT (bpHeadT (Trans (Pred (s84x_Np M)))) = u1 ++ flatBT (transC1 M) ++ v1 := by
      apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞))
      have h := c5.1; simpa [List.cons_append] using h
    have heq : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
             = flatBT (bpHeadT (Trans (Pred (s84x_Np M)))) := fA0.trans fNp.symm
    calc bpHeadT (Trans (Pred (s84x_N M)))
        = unflatBT (flatBT (bpHeadT (Trans (Pred (s84x_N M))))) := (unflatBT_flat _).symm
      _ = unflatBT (flatBT (bpHeadT (Trans (Pred (s84x_Np M))))) := by rw [heq]
      _ = bpHeadT (Trans (Pred (s84x_Np M))) := unflatBT_flat _
  · -- corner 枝: collapse 恒等式 + hPN
    obtain ⟨_cN, cPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
    obtain ⟨ins, s0, b0, s1, b1, _hflat, _hb0rp, _hb1rp, _hinner, _hk1, _hub, _hM1, _hL1, _hLp, hPN⟩ :=
      hcorner M hST hmono hp hj1 hIV hadmeq
    have h1 : bpHeadT (Trans (Pred (s84x_N M))) = bpHeadT (transC1 M) := by rw [cPN]
    have h2 : flatBT (bpHeadT (Trans (Pred (s84x_Np M)))) = flatBT (bpHeadT (transC1 M)) :=
      flat_head_bpHeadT_bl3 hPN
    have h3 : bpHeadT (Trans (Pred (s84x_Np M))) = bpHeadT (transC1 M) := by
      calc bpHeadT (Trans (Pred (s84x_Np M)))
          = unflatBT (flatBT (bpHeadT (Trans (Pred (s84x_Np M))))) := (unflatBT_flat _).symm
        _ = unflatBT (flatBT (bpHeadT (transC1 M))) := by rw [h2]
        _ = bpHeadT (transC1 M) := unflatBT_flat _
    rw [h1, h3]

#print axioms base0A0bridge_holds_bl3

/-- **`Base0_condIIIIV`（«8».«8.4-exch84-regsp»:226）の house-pattern drop-in**。
錨橋 `base0A0bridge_holds_bl3` を `Base0_condIIIIV_holds`（«8».«8.4-exch84-base0»）へ渡す。 -/
theorem base0CondIIIIV_holds_bl3 (hcorner : MnformCornerResidual_md) : Base0_condIIIIV :=
  Base0_condIIIIV_holds (base0A0bridge_holds_bl3 hcorner)

#print axioms base0CondIIIIV_holds_bl3

/-! ## 2. Leg 2 の純 `T_B`/scb 補助（base1p の private helper の再掲、suffix `_bl3`） -/

/-- condIII の c2 形状（Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353）。
base1p の private `crx_c2_shape_condIII_b1p` の再掲。 -/
private theorem crx_c2_shape_condIII_bl3 (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  unfold transC2 transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `D_v 0_B ∈ T_B`（`v` は有限指標）。base1p の private `Dprin_nat_mem_T_B_b1p` の再掲。 -/
private theorem Dprin_nat_mem_T_B_bl3 (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- 単項 `T_B` 項の flat 文字列は `isPTB_str`。base1p の private `isPTB_str_princ_b1p` の再掲。 -/
private theorem isPTB_str_princ_bl3 {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663) の再移植: `D_v` を被せると
scb 分解の左文脈に `Dsym v` が 1 つ増える。base1p の private `scb_Dprin_lift_b1p` の再掲。 -/
private theorem scb_Dprin_lift_bl3 {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（後向き）。
base1p の private `lessBP_same_head_b1p` の再掲。 -/
private theorem lessBP_same_head_bl3 (v : ℕ∞) {a b : BT} (h : lessBT a b = true) :
    lessBP (.db v a) (.db v b) = true := by
  simp [lessBP, h]

/-- `lessBP` は非反射的。base1p の private `lessBP_irrefl_b1p` の再掲。 -/
private theorem lessBP_irrefl_bl3 (p : BP) : lessBP p p = false := by
  cases p with
  | db u a => simp [lessBP, lessBT_linear_irrefl a]

/-- 共通前置 `ps` を落として `lessBPList` を比較。base1p の private `lessBPList_prefix_b1p` の再掲。 -/
private theorem lessBPList_prefix_bl3 (ps qs rs : List BP) :
    lessBPList (ps ++ qs) (ps ++ rs) = lessBPList qs rs := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.cons_append, lessBPList, lessBP_irrefl_bl3 p, beq_self_eq_true,
        Bool.true_and, Bool.false_or]
      exact ih

/-- `addBT` は右引数に対して狭義単調（前置 `t` を共有）。
base1p の private `lessBT_addBT_mono_right_b1p` の再掲。 -/
private theorem lessBT_addBT_mono_right_bl3 {a b : BT} (t : BT)
    (h : lessBT a b = true) : lessBT (addBT t a) (addBT t b) = true := by
  obtain ⟨tp⟩ := t; obtain ⟨ap⟩ := a; obtain ⟨bp⟩ := b
  show lessBPList (tp ++ ap) (tp ++ bp) = true
  rw [lessBPList_prefix_bl3]; exact h

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（前向き）。
base1p の private `lessBT_Dprin_same_b1p` の再掲。 -/
private theorem lessBT_Dprin_same_bl3 (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- Isabelle `cnv_body_grow` (layerB/pss_wip.thy:101757) の移植:
形状二分の下で `t₂ < t₃ + D_w(t₄ + c)`（`c ≠ 0_B`）。
base1p の private `cnv_body_grow_b1p` の再掲。 -/
private theorem cnv_body_grow_bl3 {t2 t3 t4 c : BT} {w : ℕ∞}
    (dich : (t3 = t2 ∧ t4 = t2) ∨ t2 = addBT t3 (Dprin w t4)) (cne : c ≠ BZero) :
    lessBT t2 (addBT t3 (Dprin w (addBT t4 c))) = true := by
  rcases dich with ⟨ht3, ht4⟩ | hb
  · subst ht3; subst ht4
    apply lessBT_addBT_self; simp [Dprin, BZero]
  · rw [hb]
    apply lessBT_addBT_mono_right_bl3
    apply lessBT_Dprin_same_bl3
    exact lessBT_addBT_self t4 c cne

/-! ## 3. Leg 2: oy1 base1' 順序 port の再移植（condIII / condIV 脚） -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `oy1_base1Y_condIII` (layerC/pss_scratch.thy:979) の Lean 完全移植。
base1p の private `oy1_base1Y_condIII_b1p` の再掲（`_bl3` helper 版）。
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))` と挿入項 `ins 0_B` の順序 `A₀ <_B ins 0_B`。 -/
private theorem oy1_base1Y_condIII_bl3
    (M : PS) (ins : BT → BT) (s0 b0 u1 u2 v1w v2 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcIII : transCondIII M = true) (hT1 : transT1 M ≠ BZero)
    (hflat : ∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (dP : scb_decomp (Trans (Pred (s84x_N M)))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1w)
    (d2 : scb_decomp (Trans (s84x_N M))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1w)
    (d4c2 : scb_decomp (transC2 M) u2
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (inner : scb_decomp (bpHeadT (Trans (s84x_N M))) s0
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    lessBT (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) = true := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  have c2sh : transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) :=
    crx_c2_shape_condIII_bl3 M hcIII
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set c' : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hc'def
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_bl3 _
  have c'TB : c' ∈ T_B := Dprin_nat_mem_T_B_bl3 _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'p : ∃ p, c' = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'ne : c' ≠ BZero := by simp [hc'def, Dprin, BZero]
  obtain ⟨w4, w4', d4⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
  have d4' : scb_decomp (addBT (transT2 M) c') w4 (flatBT c') w4' :=
    add_scb_replace_last (transT2 M) c c' w4 w4' ht2TB cTB cp c'TB c'p d4
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_bl3 cTB cp
  have d5 : scb_decomp (Dprin (transV M) (addBT (transT2 M) c))
              ((.dsym (transV M)) :: w4) (flatBT c) w4' :=
    scb_Dprin_lift_bl3 (transV M) d4 iptc
  have d5c2 : scb_decomp (transC2 M) ((.dsym (transV M)) :: w4) (flatBT c) w4' := by
    rw [c2sh]; exact d5
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: w4) (flatBT c) v2 w4' d4c2 d5c2
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
    have h := d2.1; simpa [List.cons_append] using h
  have fc2 : flatBT (transC2 M) = u2 ++ flatBT c ++ v2 := d4c2.1
  have v1RP : ∀ x ∈ v1w, x = Sym.rp := d2.2.2
  have v2RP : ∀ x ∈ v2, x = Sym.rp := d4c2.2.2
  have b0RP' : ∀ x ∈ v2 ++ v1w, x = Sym.rp := by
    intro x hx; rcases List.mem_append.mp hx with h | h
    · exact v2RP x h
    · exact v1RP x h
  have fbody2 : flatBT (bpHeadT (Trans (s84x_N M)))
      = (u1 ++ u2) ++ flatBT c ++ (v2 ++ v1w) := by
    rw [fbody, fc2]; simp [List.append_assoc]
  have innerC : scb_decomp (bpHeadT (Trans (s84x_N M))) (u1 ++ u2) (flatBT c) (v2 ++ v1w) :=
    ⟨fbody2, fun _ => iptc, b0RP'⟩
  obtain ⟨hs0, hb0⟩ := scb_unique_decomp_unconditional (bpHeadT (Trans (s84x_N M)))
    s0 (u1 ++ u2) (flatBT c) b0 (v2 ++ v1w) inner innerC
  have hflat0 := hflat BZero
  have hcflat' : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT c' := by
    simp [hc'def, Dprin, flatBT, flatBP]
  have hft2c' : flatBT (addBT (transT2 M) c') = w4 ++ flatBT c' ++ w4' := d4'.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT (transT2 M) c')) ++ v1w := by
    rw [hflat0, hs0, hb0]
    calc (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero ++ (v2 ++ v1w)
        = u1 ++ (u2 ++ (Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero) ++ v2) ++ v1w := by
          simp [List.append_assoc]
      _ = u1 ++ (u2 ++ flatBT c' ++ v2) ++ v1w := by rw [hcflat']
      _ = u1 ++ (Sym.dsym (transV M) :: (w4 ++ flatBT c' ++ w4')) ++ v1w := by
          rw [hu2, hv2]; simp [List.append_assoc]
      _ = u1 ++ (Sym.dsym (transV M) :: flatBT (addBT (transT2 M) c')) ++ v1w := by rw [hft2c']
      _ = u1 ++ flatBP (.db (transV M) (addBT (transT2 M) c')) ++ v1w := by simp [flatBP]
  have fA0' : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
      = u1 ++ flatBP (.db (transV M) (transT2 M)) ++ v1w := by
    have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1w := by
      apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  have grow : lessBT (transT2 M) (addBT (transT2 M) c') = true :=
    lessBT_addBT_self (transT2 M) c' c'ne
  have core : lessBP (.db (transV M) (transT2 M))
      (.db (transV M) (addBT (transT2 M) c')) = true :=
    lessBP_same_head_bl3 (transV M) grow
  exact scbext_lessBT fA0' fins2 v1RP core

set_option maxHeartbeats 1000000 in
/-- Isabelle `oy1_base1Y_condIV` (layerC/pss_scratch.thy:1086) の Lean 移植。
base1p の private `oy1_base1Y_condIV_b1p` の再掲（`_bl3` helper 版）。
condIII 脚の condIV 鏡像。c2 本体が入れ子になる分、`Cnv_c2_shape_condIV` と
`Cnv_nested_hole_pair` を消費し、成長は `cnv_body_grow_bl3` で出す。 -/
private theorem oy1_base1Y_condIV_bl3
    (M : PS) (ins : BT → BT) (s0 b0 u1 u2 v1w v2 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcIV : transCondIV M = true) (hT1 : transT1 M ≠ BZero)
    (hcnvShape : Cnv_c2_shape_condIV) (hcnvHole : Cnv_nested_hole_pair)
    (hflat : ∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0)
    (dP : scb_decomp (Trans (Pred (s84x_N M)))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1w)
    (d2 : scb_decomp (Trans (s84x_N M))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1w)
    (d4c2 : scb_decomp (transC2 M) u2
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (inner : scb_decomp (bpHeadT (Trans (s84x_N M))) s0
            (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0) :
    lessBT (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) = true := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  have c1sh : transC1 M = Dprin (transV M) (transT2 M) := by rw [hc1eq, hVeq]
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ := hcnvShape M hST hmono hj1 hT1 hcIV
  set w : ℕ∞ := ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) with hwdef
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set cc : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hccdef
  obtain ⟨sB, bB, holeU⟩ := hcnvHole t3 t4 w ht4TB
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_bl3 _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_bl3 _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccne : cc ≠ BZero := by simp [hccdef, Dprin, BZero]
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_bl3 cTB cp
  have dc2can0 : scb_decomp (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 c))))
      ((.dsym (transV M)) :: sB) (flatBT c) bB := scb_Dprin_lift_bl3 (transV M) dB iptc
  have dc2can : scb_decomp (transC2 M) ((.dsym (transV M)) :: sB) (flatBT c) bB := by
    rw [c2full]; exact dc2can0
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: sB) (flatBT c) v2 bB d4c2 dc2can
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
    have h := d2.1; simpa [List.cons_append] using h
  have fc2 : flatBT (transC2 M) = u2 ++ flatBT c ++ v2 := d4c2.1
  have v1RP : ∀ x ∈ v1w, x = Sym.rp := d2.2.2
  have v2RP : ∀ x ∈ v2, x = Sym.rp := d4c2.2.2
  have b0RP' : ∀ x ∈ v2 ++ v1w, x = Sym.rp := by
    intro x hx; rcases List.mem_append.mp hx with h | h
    · exact v2RP x h
    · exact v1RP x h
  have fbody2 : flatBT (bpHeadT (Trans (s84x_N M)))
      = (u1 ++ u2) ++ flatBT c ++ (v2 ++ v1w) := by
    rw [fbody, fc2]; simp [List.append_assoc]
  have innerC : scb_decomp (bpHeadT (Trans (s84x_N M))) (u1 ++ u2) (flatBT c) (v2 ++ v1w) :=
    ⟨fbody2, fun _ => iptc, b0RP'⟩
  obtain ⟨hs0, hb0⟩ := scb_unique_decomp_unconditional (bpHeadT (Trans (s84x_N M)))
    s0 (u1 ++ u2) (flatBT c) b0 (v2 ++ v1w) inner innerC
  have hflat0 := hflat BZero
  have hccflat : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero = flatBT cc := by
    simp [hccdef, Dprin, flatBT, flatBP]
  have hfB : flatBT (addBT t3 (Dprin w (addBT t4 cc))) = sB ++ flatBT cc ++ bB := dBcc.1
  have fins2 : flatBT (ins BZero)
      = u1 ++ flatBP (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by
    rw [hflat0, hs0, hb0]
    calc (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero ++ (v2 ++ v1w)
        = u1 ++ (u2 ++ (Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero) ++ v2) ++ v1w := by
          simp [List.append_assoc]
      _ = u1 ++ (u2 ++ flatBT cc ++ v2) ++ v1w := by rw [hccflat]
      _ = u1 ++ (Sym.dsym (transV M) :: (sB ++ flatBT cc ++ bB)) ++ v1w := by
          rw [hu2, hv2]; simp [List.append_assoc]
      _ = u1 ++ (Sym.dsym (transV M) :: flatBT (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by rw [hfB]
      _ = u1 ++ flatBP (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) ++ v1w := by simp [flatBP]
  have fA0' : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
      = u1 ++ flatBP (.db (transV M) (transT2 M)) ++ v1w := by
    have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1w := by
      apply flat_head_bpHeadT_bl3 (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  have grow : lessBT (transT2 M) (addBT t3 (Dprin w (addBT t4 cc))) = true :=
    cnv_body_grow_bl3 dich ccne
  have core : lessBP (.db (transV M) (transT2 M))
      (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) = true :=
    lessBP_same_head_bl3 (transV M) grow
  exact scbext_lessBT fA0' fins2 v1RP core

/-! ## 4. Leg 2: 隅専用 base1' 順序 fact（named 残差）＋ 2 脚 dispatch -/

/-- **隅専用 base1' 順序 fact**（Isabelle 隅 base1' `oy1_base1Y_condIV` の admeq 退化版）。
隅（condIV ∧ admeq）では collapse で `Trans (s84x_N M) = transC2 M`／
`Trans (Pred (s84x_N M)) = transC1 M` となり、base1' の oy1 論法は `dP` の退化で効かない。
`hinner`（`bpHeadT (transC2 M)` の scb 分解）から `lessBT (bpHeadT (transC1 M)) (ins 0_B)` を
出す隅専用の順序 fact を named 残差として露出する（REGS/REGSP 隅エンジンは Lean 未移植）。 -/
def Base1pCorner_bl3 : Prop :=
  ∀ (M : PS) (ins : BT → BT) (s0 b0 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    scb_decomp (bpHeadT (transC2 M)) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
    lessBT (bpHeadT (transC1 M)) (ins BZero) = true

/-- **`Base1p_condIIIIV`（«8».«8.4-exch84-regsp»:242）の pkg 非依存 discharge**。
`ltJ_or_IVadmeq_sp` で ltJ/corner に分岐:
- ltJ: 無条件 ltJ pkg `exch84ScbDecompPkgLtJ_holds_sp2` の `hT1`/`dP`/`d2`/`d4c2` を
  oy1 port（`oy1_base1Y_condIII_bl3` / `oy1_base1Y_condIV_bl3`、condIV は
  `Cnv_c2_shape_condIV_holds`/`Cnv_nested_hole_pair_holds` 消費）へ渡す。
- corner: `cornerCollapse_holds_cr` で `Trans (Pred (s84x_N M)) = transC1 M`／
  `Trans (s84x_N M) = transC2 M` に書き換え、隅専用 fact `Base1pCorner_bl3` へ帰着。 -/
theorem base1pCondIIIIV_holds_bl3
    (hcorner1 : Base1pCorner_bl3) : Base1p_condIIIIV := by
  intro M ins s0 b0 hST hmono hp hj1 hcond hflat hb0RP hinner
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hltJ | ⟨hIV, hadmeq⟩
  · -- ltJ 枝: ltJ pkg + oy1 port
    obtain ⟨hT1, u1, u2, v1, v2, dP, d2, d4c2, _c5⟩ :=
      exch84ScbDecompPkgLtJ_holds_sp2 M hST hmono hp hj1 hcond hltJ
    rcases hcond with hcIII | hcIV
    · exact oy1_base1Y_condIII_bl3 M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIII hT1
        hflat dP d2 d4c2 hinner
    · exact oy1_base1Y_condIV_bl3 M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIV hT1
        Cnv_c2_shape_condIV_holds Cnv_nested_hole_pair_holds hflat dP d2 d4c2 hinner
  · -- corner 枝: collapse で書き換え、Base1pCorner_bl3 へ帰着
    obtain ⟨cN, cPN⟩ := cornerCollapse_holds_cr M hST hmono hp hj1 hIV hadmeq
    have hinner' : scb_decomp (bpHeadT (transC2 M)) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 := by
      rw [← cN]; exact hinner
    rw [cPN]
    exact hcorner1 M ins s0 b0 hST hmono hp hj1 hIV hadmeq hflat hb0RP hinner'

#print axioms base1pCondIIIIV_holds_bl3

end PSS
