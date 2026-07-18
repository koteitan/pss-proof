import «8».«8.4-exch84-base1p»
import «8».«8.5-exchV-props»
import «7».«7.2-add-scb»

/-!
# §8.4 交換パッケージ `base1'` 残差の discharge（condIV c2 形状・入れ子穴対・scb 分解束）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- 対象（`8.4-exch84-base1p` が露出する 3 つの named 残差の discharge）:
  1. `Cnv_c2_shape_condIV`（«8».«8.4-exch84-base1p»:256）= Isabelle
     `cnv_c2_shape_condIV` (layerB/pss_wip.thy:101719) 経由 `c4dx_condIV_c2body_shape`
     (layerB/pss_wip.thy:84387)。条件(IV) の `c₂` 本体の入れ子形状
     `transC2 M = D_v(t₃ + D_{e1j0}(t₄ + D_{e1j1} 0_B))` と形状二分。
  2. `Cnv_nested_hole_pair`（«8».«8.4-exch84-base1p»:269）= Isabelle
     `cnv_nested_hole_pair` (layerB/pss_wip.thy:101788) 経由 `scb_addBT_left`
     (layerB/pss_wip.thy:6941)。穴内容 `c'` に依らない単一 surgery 対。
  3. `Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370）= Isabelle
     `cpx_various_scb_IIIIV` (layerB/pss_wip.thy:98539) の `c2_1`/`c3_1`/`c4_1`/`c5_1`。
     ★ narrowing のみ: cheap 部（`transT1 ≠ 0_B` と `d4c2`）を discharge し、深い nest-scb
     エンジン部（dP/d2/d4a）を tighter 残差 `Exch84_nestScbTriple` に落とす
     （bridge = `Exch84_scbDecompPkg_of_triple`、house pattern）。

## 移植構造

(1) `Cnv_c2_shape_condIV`: `transC2Core` の condIV 枝（`transCondI/III/V/VI` が全て偽・
`transT2 M ≠ 0_B`）を def 展開すると本体は既に目的の入れ子形状。`leftDj₀` 分岐で
`t₃ = ΣB(take J₁ (PB t₂))` / `t₄ = bpHeadT(pJ)`、非分岐で `t₃ = t₄ = t₂`。形状二分の
`Or.inr` 等式 `t₂ = t₃ + D_{e1j0} t₄` から `dfree_BT` 準同型（`dfree_addBT_sd`）で
`t₃,t₄ ∈ T_B` を読み出す。`t₂ ∈ T_B` は `c1_shape_holds`（«8».«8.5-exchV-props»）。

(2) `Cnv_nested_hole_pair`: 内側の穴付き末尾 principal 対を
`add_scb_marked`/`add_scb_replace_last`（«7».«7.2-add-scb», = `m_7_2_add_scb_conj1/2`）で
作り、`scb_Dprin_lift_sd`（= `scb_Dpt_lift`）で `D_w` を被せ、`scb_addBT_left_sd`
（= `scb_addBT_left`, layerB:6941 の移植, witness `liftScbPrefix_sd`）で左summand `t₃` を
被せる。`t₃ = 0_B` 隅は恒等。穴内容 `c'` に依らない単一対 `(sB, bB)` を先に確定。

## 残差

本ファイルが露出する唯一の残差 = `Exch84_nestScbTriple`（`Exch84_scbDecompPkg` から
cheap 部を剥がした nest-scb エンジン部）。Isabelle では `s84d_dec2_nest_scb`（dP/d2 の
共通 `(u1,v1)` nest 分解）と `cpx_d4a_all`（d4a、REGSP `cfbx_reg` 正則性消費）が担う。
これらは `cfbx_reg` 正則性エンジンの nest 版で Lean 未移植・単一ファイルの範囲を超える
深い機構のため、tighter named Prop `Exch84_nestScbTriple` として残す。

- 依存（すべてビルド済み・committed）: «8».«8.4-exch84-base1p»
  （`Cnv_c2_shape_condIV`/`Cnv_nested_hole_pair`/`Exch84_scbDecompPkg` の Prop 定義・
  `s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transC2`/`transV`/`transT2`・
  `STPS_RTPS`/`RTPS_TPS`）、«8».«8.5-exchV-props»（`c1_shape_holds`）、«7».«7.2-add-scb»
  （`add_scb_marked`/`add_scb_replace_last`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 (1)`Cnv_c2_shape_condIV`・(2)`Cnv_nested_hole_pair` を完全 discharge。
  残差 (3)`Exch84_scbDecompPkg` は cheap 部 discharge の上 nest-scb エンジン部を
  `Exch84_nestScbTriple` に narrowing（bridge = `Exch84_scbDecompPkg_of_triple`）。
- 訂正: なし。
- Private helper suffix: `_sd`。
-/

namespace PSS

/-! ## 1. 純 `T_B`/`SigmaB`/`PB` 補助（Isabelle 名 1:1、完全証明） -/

/-- condIV は他の条件を全て排他（Isabelle `c4dx_condIV_excl`）。 -/
private theorem condIV_others_false_sd {N : PS} (cIV : transCondIV N = true) :
    transCondI N = false ∧ transCondIII N = false ∧ transCondV N = false ∧
      transCondVI N = false := by
  simp [transCondIV] at cIV
  obtain ⟨⟨hpos, hle⟩, hadm⟩ := cIV
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [transCondI]; omega
  · simp [transCondIII, hadm]
  · simp [transCondV]; omega
  · simp [transCondVI]; omega

private theorem SigmaB_single_sd (t : BT) : SigmaB [t] = t := by
  cases t; simp [SigmaB, untrm]

private theorem SigmaB_append_sd (xs ys : List BT) :
    SigmaB (xs ++ ys) = addBT (SigmaB xs) (SigmaB ys) := by
  simp [SigmaB, addBT, List.flatMap_append]

private theorem SigmaB_PB_sd (t : BT) : SigmaB (PB t) = t := by
  cases t with
  | trm ps => simp [SigmaB, PB, untrm, List.flatMap_map]

private theorem take_getD_last_sd {α : Type _} (l : List α) (d : α)
    (h : l ≠ []) : l.take (l.length - 1) ++ [l.getD (l.length - 1) d] = l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨xs, x, rfl⟩
  · exact absurd rfl h
  · simp [List.getD_eq_getElem?_getD]

private theorem PB_mem_principal_sd {t c : BT} (h : c ∈ PB t) :
    c = Dprin (bpHeadV c) (bpHeadT c) := by
  simp [PB] at h
  obtain ⟨p, -, rfl⟩ := h
  cases p with
  | db v a => simp [Dprin, bpHeadV, bpHeadT]

private theorem PB_ne_nil_sd {t : BT} (h : t ≠ BZero) : PB t ≠ [] := by
  cases t with
  | trm ps =>
      cases ps with
      | nil => exact absurd rfl h
      | cons q qs => simp [PB, untrm]

private theorem dfree_BPList_append_sd (as bs : List BP) :
    dfree_BPList (as ++ bs) = (dfree_BPList as && dfree_BPList bs) := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons p ps ih => simp [dfree_BPList, ih, Bool.and_assoc]

private theorem dfree_addBT_sd (a b : BT) :
    dfree_BT (addBT a b) = (dfree_BT a && dfree_BT b) := by
  cases a; cases b; simp [addBT, dfree_BT, dfree_BPList_append_sd]

/-! ## 2. 残差 (1): `Cnv_c2_shape_condIV`（Isabelle `cnv_c2_shape_condIV`） -/

/-- 残差 `Cnv_c2_shape_condIV`（«8».«8.4-exch84-base1p»:256）の house-pattern discharge。
Isabelle `cnv_c2_shape_condIV` (layerB/pss_wip.thy:101719) 経由
`c4dx_condIV_c2body_shape` (layerB/pss_wip.thy:84387)。 -/
theorem Cnv_c2_shape_condIV_holds : Cnv_c2_shape_condIV := by
  intro M hST hmono hj1 hT1 hcIV
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨_, _, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  obtain ⟨hI, hIII, hV, hVI⟩ := condIV_others_false_sd hcIV
  by_cases hz : transT2 M = BZero
  · refine ⟨BZero, BZero, ?_, ?_, ?_, Or.inl ⟨hz.symm, hz.symm⟩⟩
    · simp [T_B, dfree_BT, dfree_BPList, BZero]
    · simp [T_B, dfree_BT, dfree_BPList, BZero]
    · show transC2Core M (transV M) (transT2 M) = _
      simp [transC2Core, hI, hIII, hV, hVI, hz, lastIdx, addBT, BZero, Dprin, transJ0]
  · by_cases hlft : (bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        == (entry M 1 (lastParent M) : ℕ∞)) = true
    · -- leftDj₀ 分岐: 末尾 principal を 1 個剥がす
      have hne : PB (transT2 M) ≠ [] := PB_ne_nil_sd hz
      have hlen : (PB (transT2 M)).length - 1 < (PB (transT2 M)).length := by
        have := List.length_pos_of_ne_nil hne; omega
      have hmem : (PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero
          ∈ PB (transT2 M) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
          Option.getD_some]
        exact List.getElem_mem hlen
      have hprin := PB_mem_principal_sd hmem
      have hsplit := take_getD_last_sd (PB (transT2 M)) BZero hne
      have huv : bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
          = (entry M 1 (lastParent M) : ℕ∞) := by simpa using hlft
      have dich : transT2 M
          = addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
              (Dprin (entry M 1 (lastParent M) : ℕ∞)
                (bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero))) := by
        calc transT2 M
            = SigmaB (PB (transT2 M)) := (SigmaB_PB_sd _).symm
          _ = SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)
                ++ [(PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero]) := by
                rw [hsplit]
          _ = addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
                (SigmaB [(PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero]) :=
                SigmaB_append_sd _ _
          _ = addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
                ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero) := by
                rw [SigmaB_single_sd]
          _ = _ := by rw [← huv]; exact congrArg _ hprin
      -- `dfree_BT` 準同型で `t₃,t₄ ∈ T_B`
      have hd : dfree_BT (transT2 M) = true := ht2TB
      rw [dich, dfree_addBT_sd] at hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨hd3, hdD⟩ := hd
      have ht3TB : (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1))) ∈ T_B := hd3
      have ht4TB : (bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)) ∈ T_B := by
        have hDD : dfree_BT (Dprin (entry M 1 (lastParent M) : ℕ∞)
            (bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero))) = true := hdD
        simpa [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP] using hDD
      refine ⟨SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)),
        bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero),
        ht3TB, ht4TB, ?_, Or.inr dich⟩
      show transC2Core M (transV M) (transT2 M) = _
      simp only [transC2Core, hI, hIII, hV, hVI, Bool.or_self, lastIdx, if_false,
        Bool.false_eq_true, hlft, beq_iff_eq, if_true, transJ0]
      rw [if_neg (by simp [hz] : ¬((transT2 M == BZero) = true))]
    · -- 非 leftDj₀ 分岐: `t₃ = t₄ = t₂`
      refine ⟨transT2 M, transT2 M, ht2TB, ht2TB, ?_, Or.inl ⟨rfl, rfl⟩⟩
      show transC2Core M (transV M) (transT2 M) = _
      simp only [transC2Core, hI, hIII, hV, hVI, Bool.or_self, lastIdx, if_false,
        Bool.false_eq_true, hlft, beq_iff_eq, transJ0]
      rw [if_neg (by simp [hz] : ¬((transT2 M == BZero) = true))]

#print axioms Cnv_c2_shape_condIV_holds

/-! ## 3. 残差 (2): `Cnv_nested_hole_pair`（Isabelle `cnv_nested_hole_pair`） -/

/-- 単項 `T_B` 項の flat 文字列は `isPTB_str`（= Isabelle `addscb_princ_isPTB`）。 -/
private theorem isPTB_str_princ_sd {c : BT} (hc : c ∈ T_B) (hcP : ∃ p, c = BT.trm [p]) :
    isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): `D_v` を被せると scb 分解の
左文脈に `Dsym v` が 1 つ増える。 -/
private theorem scb_Dprin_lift_sd {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]; simp

/-- `addBT` の左 `0_B` は恒等。 -/
private theorem addBT_BZero_left_sd (X : BT) : addBT BZero X = X := by
  cases X; simp [addBT, BZero]

/-- Isabelle `liftS` (layerB/pss_wip.thy:6838): 左 summand `Y` の flat を被せる surgery
接頭辞。 -/
private def liftScbPrefix_sd (Y : BT) (s : List Sym) : List Sym :=
  match untrm Y with
  | [] => s
  | p :: ps => .lp :: flatBP p ++ flatBPTail ps ++ [.cm] ++ s

private theorem flatBPTail_append_singleton_sd (ps : List BP) (p : BP) :
    flatBPTail (ps ++ [p]) = flatBPTail ps ++ (.cm :: flatBP p) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

/-- Isabelle `scb_addBT_left` (layerB/pss_wip.thy:6941): 単項 principal `X` に左 summand
`Y (≠ 0_B)` を前置しても、`liftScbPrefix Y` の下で同じ穴 `c` の scb 分解が持ち上がる。 -/
private theorem scb_addBT_left_sd {X Y : BT} {s c b : List Sym}
    (hd : scb_decomp X s c b)
    (hXone : (untrm X).length = 1)
    (hYne : untrm Y ≠ []) :
    scb_decomp (addBT Y X) (liftScbPrefix_sd Y s) c (b ++ [.rp]) := by
  rcases X with ⟨xs⟩
  rcases Y with ⟨ys⟩
  simp only [untrm] at hXone hYne
  cases xs with
  | nil => simp at hXone
  | cons x xs =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact (hYne rfl).elim
          | cons y ys =>
              rcases hd with ⟨hflat, hprincipal, htail⟩
              have hXne : BT.trm [x] ≠ BZero := by simp [BZero]
              have hc : isPTB_str c := hprincipal hXne
              have hflat' : flatBP x = s ++ c ++ b := by
                simpa [flatBT] using hflat
              refine ⟨?_, ?_, ?_⟩
              · cases ys <;>
                  simp [addBT, flatBT, flatBPTail, liftScbPrefix_sd, untrm,
                    flatBPTail_append_singleton_sd, hflat', List.append_assoc]
              · intro _
                exact hc
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact htail z hz
                · simpa using hz
      | cons x' xs => simp at hXone

/-- 残差 `Cnv_nested_hole_pair`（«8».«8.4-exch84-base1p»:269）の house-pattern discharge。
Isabelle `cnv_nested_hole_pair` (layerB/pss_wip.thy:101788)。穴内容 `c'` に依らない
単一 surgery 対 `(sB, bB)` を先に確定し、`t₃ = 0_B` / `≠ 0_B` で分岐。 -/
theorem Cnv_nested_hole_pair_holds : Cnv_nested_hole_pair := by
  intro t3 t4 w ht4TB
  set c0 : BT := Dprin 0 BZero with hc0def
  have c0TB : c0 ∈ T_B := by simp [hc0def, T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]
  have c0p : ∃ p, c0 = BT.trm [p] := ⟨.db 0 BZero, rfl⟩
  obtain ⟨w4, w4', d40⟩ := add_scb_marked t4 c0 ht4TB c0TB c0p
  have step : ∀ c' : BT, c' ∈ T_B → (∃ p, c' = BT.trm [p]) →
      scb_decomp (Dprin w (addBT t4 c')) (Sym.dsym w :: w4) (flatBT c') w4' := by
    intro c' hc'TB hc'p
    have d4' := add_scb_replace_last t4 c0 c' w4 w4' ht4TB c0TB c0p hc'TB hc'p d40
    have ipt := isPTB_str_princ_sd hc'TB hc'p
    exact scb_Dprin_lift_sd w d4' ipt
  by_cases ht3 : t3 = BZero
  · refine ⟨Sym.dsym w :: w4, w4', ?_⟩
    intro c' hc'TB hc'p
    have hstep := step c' hc'TB hc'p
    rw [ht3, addBT_BZero_left_sd]
    exact hstep
  · refine ⟨liftScbPrefix_sd t3 (Sym.dsym w :: w4), w4' ++ [Sym.rp], ?_⟩
    intro c' hc'TB hc'p
    have hstep := step c' hc'TB hc'p
    have hX1 : (untrm (Dprin w (addBT t4 c'))).length = 1 := by simp [Dprin, untrm]
    have hYne : untrm t3 ≠ [] := by
      cases t3 with
      | trm ps =>
          cases ps with
          | nil => exact absurd rfl ht3
          | cons a as => simp [untrm]
    exact scb_addBT_left_sd hstep hX1 hYne

#print axioms Cnv_nested_hole_pair_holds

/-! ## 4. 残差 (3): `Exch84_scbDecompPkg` の narrowing（cheap 部を discharge） -/

/-- Isabelle setup（`m_8_5_scbdec` setup 相当）: 条件下で `transJ1 > 0` かつ
`transT1 M = Trans (Pred M) ≠ 0_B`。 -/
private theorem setup_sd {N : PS} (hR : RTPS N) (hj1 : 1 < Lng N - 1) :
    0 < transJ1 N ∧ transT1 N ≠ BZero := by
  have hlen : 1 < Lng N := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := by
    simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred N) = false := by
    simp [zeroT, hLP]; omega
  have T1' : Trans (Pred N) ≠ BZero :=
    (Trans_Mark_invariant (Pred N) (RTPS_Pred N hR)).2.1 nzP
  exact ⟨by simp [transJ1, lastIdx]; omega, by simpa [transT1] using T1'⟩

/-- condIII の c2 形状（Isabelle `crx_c2_shape_condIII`, layerB/pss_wip.thy:88353）。 -/
private theorem c2_shape_condIII_sd (M : PS) (hcIII : transCondIII M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) := by
  show transC2Core M (transV M) (transT2 M) = _
  unfold transC2Core
  simp only [hcIII, Bool.or_eq_true, or_true, true_or, if_true]
  rfl

/-- `d4c2`: `transC2 M` の末尾 principal `D_{e1(Lng-1)} 0_B` を露出する scb 分解。
condIII は単一 `addBT`（`add_scb_marked` + `scb_Dprin_lift`）、condIV は入れ子
（`Cnv_nested_hole_pair_holds` に穴 `= D_{e1(Lng-1)} 0_B` を代入 + `scb_Dprin_lift`）。 -/
private theorem d4c2_sd (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondIII M = true ∨ transCondIV M = true) :
    ∃ u2 v2 : List Sym,
      scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hT1 : transT1 M ≠ BZero := (setup_sd hMR hj1).2
  obtain ⟨_, _, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  set c : BT := Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero with hcdef
  have cTB : c ∈ T_B := by
    simp [hcdef, T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]
  have cp : ∃ p, c = BT.trm [p] := ⟨.db _ BZero, rfl⟩
  have iptc : isPTB_str (flatBT c) := isPTB_str_princ_sd cTB cp
  rcases hcond with hcIII | hcIV
  · -- condIII: transC2 = D_transV(t₂ + c)
    have c2eq : transC2 M = Dprin (transV M) (addBT (transT2 M) c) :=
      c2_shape_condIII_sd M hcIII
    obtain ⟨s, b, dmark⟩ := add_scb_marked (transT2 M) c ht2TB cTB cp
    refine ⟨Sym.dsym (transV M) :: s, b, ?_⟩
    rw [c2eq]
    exact scb_Dprin_lift_sd (transV M) dmark iptc
  · -- condIV: transC2 = D_transV(t₃ + D_u(t₄ + c))
    obtain ⟨t3, t4, _ht3TB, ht4TB, c2eq, _⟩ :=
      Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hcIV
    obtain ⟨sB, bB, hole⟩ :=
      Cnv_nested_hole_pair_holds t3 t4 ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) ht4TB
    have dbody := hole c cTB cp
    refine ⟨Sym.dsym (transV M) :: sB, bB, ?_⟩
    rw [c2eq]
    exact scb_Dprin_lift_sd (transV M) dbody iptc

/-- narrowed 残差: `s84x_N`/`s84x_Np` の Pred/生スライス nest-scb 三つ組（Isabelle
`s84d_dec2_nest_scb` (dP/d2) と `cpx_d4a_all` (d4a, REGSP `cfbx_reg` 正則性)）。
`Exch84_scbDecompPkg` から `transT1 ≠ 0_B`（`setup_sd`）と `d4c2`（`d4c2_sd`）を剥がした
残り。共通 `(u1, v1)` を持つ 3 分解。 -/
def Exch84_nestScbTriple : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    ∃ u1 v1 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-- house-pattern narrowing: `Exch84_nestScbTriple`（nest-scb エンジン）から
`Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370）を組み立てる。`transT1 ≠ 0_B` は
`setup_sd`、`d4c2` は `d4c2_sd`、残り 3 分解は三つ組から。 -/
theorem Exch84_scbDecompPkg_of_triple (triple : Exch84_nestScbTriple) :
    Exch84_scbDecompPkg := by
  intro M hST hmono hp hj1 hcond
  have hMR : RTPS M := STPS_RTPS M hST
  refine ⟨(setup_sd hMR hj1).2, ?_⟩
  obtain ⟨u1, v1, dP, d2, d4a⟩ := triple M hST hmono hp hj1 hcond
  obtain ⟨u2, v2, d4c2⟩ := d4c2_sd M hST hmono hj1 hcond
  exact ⟨u1, u2, v1, v2, dP, d2, d4c2, d4a⟩

#print axioms Exch84_scbDecompPkg_of_triple

end PSS
