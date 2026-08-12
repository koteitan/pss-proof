import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «8».«8.4-exch84-regsp»
import «8».«8.4-exch84-base0»
import «8».«8.5-exchV-props»

/-!
# §8.4 交換パッケージ `slicepkg` の 2 つの base 脚（`base1'` と `base0` 錨橋）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- 対象（`slicepkg` 組み立ての base 脚、`8.4-exch84-slicepkg` の needs を参照）:
  1. `Base1p_condIIIIV`（«8».«8.4-exch84-regsp»:242）= Isabelle
     `oy1_base1Y_condIII` / `oy1_base1Y_condIV` (layerC/pss_scratch.thy:979/1086)。
     `A₀ = bpHeadT (Trans (Pred (s84x_N M)))` と挿入項 `ins 0_B` の順序
     `A₀ <_B ins 0_B`。純 `T_B`/scb 代数。
  2. `Base0_A0bridge`（«8».«8.4-exch84-base0»:326）= Isabelle `A0eq`
     (`cpx_condIII_mnform` 内, layerB/pss_wip.thy:98787)。`s84x_N`（j₋₃ 錨）と
     `s84x_Np`（j₋₂ 錨）の Pred スライスの principal 本体 `bpHeadT (Trans (Pred ·))`
     の一致。

## 移植構造

condIII 脚は **完全証明**（`oy1_base1Y_condIIII_b1p`）: `c1_shape_holds`（=
Isabelle `m_8_5_scbdec_c1_shape`, «8».«8.5-exchV-props»）＋ 本ファイル移植の
condIII c2 形状 `crx_c2_shape_condIII_b1p`（`transC2Core` の def 展開、`transCondIII`
枝）＋ `add_scb_marked`/`add_scb_replace_last`（«7».«7.2-add-scb»）＋
`scb_Dprin_lift_b1p`（= `scb_Dpt_lift`, layerB:1663 の再移植）＋
`scb_unique_decomp_unconditional`（«7».«7.2-scb-unique», = `m_7_2_scb_unique_sb`）＋
`flat_head_bpHeadT_b1p`（= `vf2x_flat_head_bpHeadT`, layerB:69403 の移植）＋
`lessBT_addBT_self`（«7».«7.3-c1-c2-order»）＋ `scbext_lessBT`
（«7».«7.3-Pred-Trans-descend»）から組む。

condIV 脚（`oy1_base1Y_condIV_b1p`）も同技法で **完全証明**するが、condIV 固有の
c2 本体の入れ子形状 `Cnv_c2_shape_condIV`（= `cnv_c2_shape_condIV`, layerB:101719 の
`c4dx_condIV_c2body_shape` を消費）と一様な入れ子穴 surgery 対 `Cnv_nested_hole_pair`
（= `cnv_nested_hole_pair`, layerB:101788 の `scb_addBT_left` を消費）は未移植の
深い機構なので named 残差として露出する。入れ子成長 `cnv_body_grow_b1p`
（= `cnv_body_grow`, layerB:101757）は `lessBT_addBT_mono_right_b1p`（本ファイル移植）
で完全証明する。

`base0` 錨橋 `A0eq` は純粋（`vf2x_flat_head_bpHeadT` ＋ `unflatBT_flat`）で、共有
scb 分解 `c2_1`（`s84x_N`）と `c5_1`（`s84x_Np`）から `bpHeadT` の flat 一致を出し
`unflatBT` で潰す。

両脚とも入力の scb 分解束（Isabelle `cpx_various_scb_IIIIV` (layerB:98605 近傍) の
`c2_1`/`c3_1`/`c4_1`/`c5_1`）は REGS/REGSP 正則性を消費するため、named 残差
`Exch84_scbDecompPkg` として露出し、house pattern で両公開定理へ渡す。

- 依存（すべてビルド済み・committed）:
  «8».«8.4-exch84-regsp»（`Base1p_condIIIIV`・`s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・
  `transC1`/`transC2`/`transV`/`transT2`/`transT1`/`transJ0`/`transJ1`・`transC2Core`・
  `add_scb_marked`/`add_scb_replace_last`・`scb_unique_decomp_unconditional`・
  `scbext_lessBT`・`unflatBT_flat`・`lessBT_addBT_self`・`STPS_RTPS`/`RTPS_TPS`・
  `addBT_mem_T_B`）、«8».«8.4-exch84-base0»（`Base0_A0bridge`）、
  «8».«8.5-exchV-props»（`c1_shape_holds`）、«Buchholz-1986».«Buchholz-1986-2.1-order»
  （`lessBT_linear_irrefl`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 named Prop = `Exch84_scbDecompPkg`（REGS/REGSP scb 分解束）、
  `Cnv_c2_shape_condIV`（condIV c2 本体形状）、`Cnv_nested_hole_pair`（condIV 入れ子穴
  surgery 対）。condIII 脚・condIV 脚 wiring・base0 錨橋はいずれも完全証明。
- 訂正: なし。
- Private helper suffix: `_b1p`。
-/

namespace PSS

/-! ## 1. 純 `T_B`/scb 補助（Isabelle 名 1:1、完全証明） -/

/-- condIII の c2 形状（Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353）。
`transC2Core` の `transCondI ∨ transCondIII ∨ transCondV` 枝の def 展開。 -/
private theorem crx_c2_shape_condIII_b1p (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  unfold transC2 transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `D_v 0_B ∈ T_B`（`v` は有限指標）。 -/
private theorem Dprin_nat_mem_T_B_b1p (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- 単項 `T_B` 項の flat 文字列は `isPTB_str`。 -/
private theorem isPTB_str_princ_b1p {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663) の再移植: `D_v` を被せると
scb 分解の左文脈に `Dsym v` が 1 つ増える。 -/
private theorem scb_Dprin_lift_b1p {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（後向き）。 -/
private theorem lessBP_same_head_b1p (v : ℕ∞) {a b : BT} (h : lessBT a b = true) :
    lessBP (.db v a) (.db v b) = true := by
  simp [lessBP, h]

/-- Isabelle `vf2x_flat_head_bpHeadT` (layerB/pss_wip.thy:69403) の移植:
`flatBT t = Dsym v # rest` なら `flatBT (bpHeadT t) = rest`。 -/
private theorem flat_head_bpHeadT_b1p {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `lessBP` は非反射的。 -/
private theorem lessBP_irrefl_b1p (p : BP) : lessBP p p = false := by
  cases p with
  | db u a => simp [lessBP, lessBT_linear_irrefl a]

/-- 共通前置 `ps` を落として `lessBPList` を比較。 -/
private theorem lessBPList_prefix_b1p (ps qs rs : List BP) :
    lessBPList (ps ++ qs) (ps ++ rs) = lessBPList qs rs := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.cons_append, lessBPList, lessBP_irrefl_b1p p, beq_self_eq_true,
        Bool.true_and, Bool.false_or]
      exact ih

/-- `addBT` は右引数に対して狭義単調（前置 `t` を共有）。 -/
private theorem lessBT_addBT_mono_right_b1p {a b : BT} (t : BT)
    (h : lessBT a b = true) : lessBT (addBT t a) (addBT t b) = true := by
  obtain ⟨tp⟩ := t; obtain ⟨ap⟩ := a; obtain ⟨bp⟩ := b
  show lessBPList (tp ++ ap) (tp ++ bp) = true
  rw [lessBPList_prefix_b1p]; exact h

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（前向き）。 -/
private theorem lessBT_Dprin_same_b1p (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- Isabelle `cnv_body_grow` (layerB/pss_wip.thy:101757) の移植:
形状二分の下で `t₂ < t₃ + D_w(t₄ + c)`（`c ≠ 0_B`）。 -/
private theorem cnv_body_grow_b1p {t2 t3 t4 c : BT} {w : ℕ∞}
    (dich : (t3 = t2 ∧ t4 = t2) ∨ t2 = addBT t3 (Dprin w t4)) (cne : c ≠ BZero) :
    lessBT t2 (addBT t3 (Dprin w (addBT t4 c))) = true := by
  rcases dich with ⟨ht3, ht4⟩ | hb
  · subst ht3; subst ht4
    apply lessBT_addBT_self; simp [Dprin, BZero]
  · rw [hb]
    apply lessBT_addBT_mono_right_b1p
    apply lessBT_Dprin_same_b1p
    exact lessBT_addBT_self t4 c cne

/-! ## 2. `base1'`（condIII 脚、完全証明） -/

set_option maxHeartbeats 1000000 in
/-- Isabelle `oy1_base1Y_condIII` (layerC/pss_scratch.thy:979) の Lean 完全移植。
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))` と挿入項 `ins 0_B` の順序 `A₀ <_B ins 0_B`。
挿入段 `ins` を `d4vx_ins_flat` の結論（`hflat`）で抽象化し、`inner`（bpHeadT 本体の
scb 分解）と scb 分解束 `dP`/`d2`/`d4c2` から共有 surgery 拡張で組む。 -/
private theorem oy1_base1Y_condIII_b1p
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
    crx_c2_shape_condIII_b1p M hcIII
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  set c' : BT := Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero with hc'def
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_b1p _
  have c'TB : c' ∈ T_B := Dprin_nat_mem_T_B_b1p _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'p : ∃ p, c' = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have c'ne : c' ≠ BZero := by simp [hc'def, Dprin, BZero]
  obtain ⟨w4, w4', d4⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
  have d4' : scb_decomp (addBT (transT2 M) c') w4 (flatBT c') w4' :=
    add_scb_replace_last (transT2 M) c c' w4 w4' ht2TB cTB cp c'TB c'p d4
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_b1p cTB cp
  have d5 : scb_decomp (Dprin (transV M) (addBT (transT2 M) c))
              ((.dsym (transV M)) :: w4) (flatBT c) w4' :=
    scb_Dprin_lift_b1p (transV M) d4 iptc
  have d5c2 : scb_decomp (transC2 M) ((.dsym (transV M)) :: w4) (flatBT c) w4' := by
    rw [c2sh]; exact d5
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: w4) (flatBT c) v2 w4' d4c2 d5c2
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
      apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  have grow : lessBT (transT2 M) (addBT (transT2 M) c') = true :=
    lessBT_addBT_self (transT2 M) c' c'ne
  have core : lessBP (.db (transV M) (transT2 M))
      (.db (transV M) (addBT (transT2 M) c')) = true :=
    lessBP_same_head_b1p (transV M) grow
  exact scbext_lessBT fA0' fins2 v1RP core

/-! ## 3. `base1'`（condIV 脚、named 残差 2 本 modulo で完全証明） -/

/-- 残差: condIV の c2 本体入れ子形状（Isabelle `cnv_c2_shape_condIV`,
layerB/pss_wip.thy:101719 の `c4dx_condIV_c2body_shape` を消費、未移植）。
`transC2 M = D_v(t₃ + D_{w}(t₄ + D_{v₁} 0_B))`、形状二分付き。 -/
def Cnv_c2_shape_condIV : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 →
    transT1 M ≠ BZero → transCondIV M = true →
    ∃ t3 t4 : BT, t3 ∈ T_B ∧ t4 ∈ T_B ∧
      transC2 M = Dprin (transV M)
        (addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)))) ∧
      ((t3 = transT2 M ∧ t4 = transT2 M)
       ∨ transT2 M = addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) t4))

/-- 残差: condIV の一様な入れ子穴 surgery 対（Isabelle `cnv_nested_hole_pair`,
layerB/pss_wip.thy:101788 の `scb_addBT_left` を消費、未移植）。
穴内容 `c'` に依らない単一の surgery 対 `(sB, bB)`。 -/
def Cnv_nested_hole_pair : Prop :=
  ∀ (t3 t4 : BT) (w : ℕ∞), t4 ∈ T_B →
    ∃ sB bB : List Sym, ∀ c' : BT, c' ∈ T_B → (∃ p, c' = BT.trm [p]) →
      scb_decomp (addBT t3 (Dprin w (addBT t4 c'))) sB (flatBT c') bB

set_option maxHeartbeats 1000000 in
/-- Isabelle `oy1_base1Y_condIV` (layerC/pss_scratch.thy:1086) の Lean 移植。
condIII 脚 (`oy1_base1Y_condIII_b1p`) の condIV 鏡像。c2 本体が入れ子
`t₃ + D_w(t₄ + ·)` になる分、`Cnv_c2_shape_condIV` と `Cnv_nested_hole_pair` を
消費し、成長は `cnv_body_grow_b1p` で出す。 -/
private theorem oy1_base1Y_condIV_b1p
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
  have cTB : c ∈ T_B := Dprin_nat_mem_T_B_b1p _
  have ccTB : cc ∈ T_B := Dprin_nat_mem_T_B_b1p _
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, cc = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have ccne : cc ≠ BZero := by simp [hccdef, Dprin, BZero]
  have dB : scb_decomp (addBT t3 (Dprin w (addBT t4 c))) sB (flatBT c) bB := holeU c cTB cp
  have dBcc : scb_decomp (addBT t3 (Dprin w (addBT t4 cc))) sB (flatBT cc) bB := holeU cc ccTB ccp
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_b1p cTB cp
  have dc2can0 : scb_decomp (Dprin (transV M) (addBT t3 (Dprin w (addBT t4 c))))
      ((.dsym (transV M)) :: sB) (flatBT c) bB := scb_Dprin_lift_b1p (transV M) dB iptc
  have dc2can : scb_decomp (transC2 M) ((.dsym (transV M)) :: sB) (flatBT c) bB := by
    rw [c2full]; exact dc2can0
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    ((.dsym (transV M)) :: sB) (flatBT c) v2 bB d4c2 dc2can
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1w := by
    apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
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
      apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
      have h := dP.1; simpa [List.cons_append] using h
    rw [fA0, c1sh]; simp [Dprin, flatBT, flatBP]
  have grow : lessBT (transT2 M) (addBT t3 (Dprin w (addBT t4 cc))) = true :=
    cnv_body_grow_b1p dich ccne
  have core : lessBP (.db (transV M) (transT2 M))
      (.db (transV M) (addBT t3 (Dprin w (addBT t4 cc)))) = true :=
    lessBP_same_head_b1p (transV M) grow
  exact scbext_lessBT fA0' fins2 v1RP core

/-! ## 4. 入力の scb 分解束（named 残差、Isabelle `cpx_various_scb_IIIIV`） -/

/-- 残差: `s84x_N`/`s84x_Np` の Pred/生スライスの scb 分解束（Isabelle
`cpx_various_scb_IIIIV` (layerB/pss_wip.thy:98605 近傍) の `c2_1`/`c3_1`/`c4_1`/`c5_1`）。
REGS/REGSP 正則性を消費するため未移植。base1'（condIII/IV）は `c2_1`/`c3_1`/`c4_1` を、
base0 錨橋は `c2_1`/`c5_1` を消費する。 -/
def Exch84_scbDecompPkg : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    transT1 M ≠ BZero ∧
    ∃ u1 u2 v1 v2 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 ∧
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-! ## 5. house pattern による 2 脚の discharge -/

/-- `Base1p_condIIIIV`（«8».«8.4-exch84-regsp»:242）の drop-in。
condIII 枝は完全証明 `oy1_base1Y_condIII_b1p`、condIV 枝は `Cnv_c2_shape_condIV` ／
`Cnv_nested_hole_pair` modulo で完全証明 `oy1_base1Y_condIV_b1p`。scb 分解束は
`Exch84_scbDecompPkg` から供給。 -/
theorem Base1p_condIIIIV_holds
    (pkg : Exch84_scbDecompPkg)
    (hcnvShape : Cnv_c2_shape_condIV) (hcnvHole : Cnv_nested_hole_pair) :
    Base1p_condIIIIV := by
  intro M ins s0 b0 hST hmono hp hj1 hcond hflat _hb0RP hinner
  obtain ⟨hT1, u1, u2, v1, v2, dP, d2, d4c2, _c5⟩ := pkg M hST hmono hp hj1 hcond
  rcases hcond with hcIII | hcIV
  · exact oy1_base1Y_condIII_b1p M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIII hT1
      hflat dP d2 d4c2 hinner
  · exact oy1_base1Y_condIV_b1p M ins s0 b0 u1 u2 v1 v2 hST hmono hj1 hcIV hT1
      hcnvShape hcnvHole hflat dP d2 d4c2 hinner

/-- `Base0_A0bridge`（«8».«8.4-exch84-base0»:326）の drop-in。
共有 scb 分解 `c2_1`（`s84x_N`）と `c5_1`（`s84x_Np`）から `bpHeadT (Trans (Pred ·))`
の flat 一致を出し `unflatBT` で潰す。scb 分解束は `Exch84_scbDecompPkg` から供給。 -/
theorem Base0_A0bridge_holds (pkg : Exch84_scbDecompPkg) : Base0_A0bridge := by
  intro M hST hmono hp hj1 hcond
  obtain ⟨_hT1, u1, u2, v1, v2, dP, _d2, _d4c2, c5⟩ := pkg M hST hmono hp hj1 hcond
  have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1 := by
    apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞))
    have h := dP.1; simpa [List.cons_append] using h
  have fNp : flatBT (bpHeadT (Trans (Pred (s84x_Np M)))) = u1 ++ flatBT (transC1 M) ++ v1 := by
    apply flat_head_bpHeadT_b1p (v := ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞))
    have h := c5.1; simpa [List.cons_append] using h
  have heq : flatBT (bpHeadT (Trans (Pred (s84x_N M))))
           = flatBT (bpHeadT (Trans (Pred (s84x_Np M)))) := fA0.trans fNp.symm
  calc bpHeadT (Trans (Pred (s84x_N M)))
      = unflatBT (flatBT (bpHeadT (Trans (Pred (s84x_N M))))) := (unflatBT_flat _).symm
    _ = unflatBT (flatBT (bpHeadT (Trans (Pred (s84x_Np M))))) := by rw [heq]
    _ = bpHeadT (Trans (Pred (s84x_Np M))) := unflatBT_flat _

#print axioms Base1p_condIIIIV_holds
#print axioms Base0_A0bridge_holds

end PSS
