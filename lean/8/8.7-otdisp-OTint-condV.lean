import «8».«8.7-otdisp-OTint»
import «8».«8.7-otint-uncond»
import «8».«8.5-exchV-props»
import «8».«8.7-OT-scb-recursive»

/-!
# §8.7 `OTdisp_OTint` — condition (V) の 2 本の hasParent leg

- 対象: ビルド済み «8».«8.7-otdisp-OTint» が declare した 4 分岐 Prop のうち、
  条件(V) の 2 本 `OTint_hp_condV_adm` / `OTint_hp_condV_nadm` を discharge する。
- Isabelle 設計図:
  - `oix_OTint_condV_adm` (`layerB/pss_wip.thy`:111599, ~180 行) — 許容枝。
    engine = `oix_twr` 塔 (`m_8_5_scbdec_adm_forms` の replicate-block 値形を
    塔閉形式に読み替え) ＋ `oix_transportD` ＋ `e4x_OT_B_operB_numBT`。
  - `oix_OTint_condV_nadm` (`layerB/pss_wip.thy`:112041, ~150 行) — 非許容枝。
    同じ塔を rebased head `u = M₁,j₋₁ ≤ e` で運ぶ（`oix_condV_newOT_gen` の
    G-antitonicity ＋ host descP から `HB`/`t2lb` を再導出）。
- KEY 資産:
  - `oix_transport_uncond`（«8».«8.7-otint-uncond»）＝ transport core は無条件。
    `oix_transportD oix_transport_uncond …` で純 `BT` sandwich を運ぶ。
  - §8.5 値形は `adm_forms_holds`/`nf3x_holds`（«8».«8.5-exchV-props»）から得る。
    これらは各々 `ExchVres_adm_M_tower` / `ExchV_nf3x`（= `ExchVres_nadm_M_tower`
    経由）の**まだ開いている塔閉形式**に乗る。よって本ファイルの 2 定理は
    house pattern に従い、その塔 Prop を**そのまま仮定に取る**（新設せず、
    §8.5 の既存 Prop を使う）。並行 agent が `ExchV_M_tower` を攻めており、
    それが両者を供給する。
  - `e4x_OT_B_operB_numBT` の twin ＝ `buchholz_fseq_closed`
    (`7.1-buchholz-fseq-closed`:1358, `a ∈ OT_B → a ≠ 0_B → operB a (numBT n) ∈ OT_B`)。
- 依存（ビルド済みのみ import）: «8».«8.7-otdisp-OTint»（4 分岐 Prop の定義元・
  推移的に `OT_B`/`Trans`/`m_8_7_OT_scb_recursive`）、«8».«8.7-otint-uncond»
  （`oix_transport_uncond`/`oix_transportD`/`b1x_setle`）、«8».«8.5-exchV-props»
  （`ExchVres_*`/`adm_forms_holds`/`nf3x_holds`/`fseq_condV_holds`/`condV_setup_holds`/
  `c1_shape_holds`/`s85b_W`/`e5x_bodyM`/`e5x_bodyO`/`add_scb_replace_last`/
  `addBT_mem_T_B`/`Dprin_mem_T_B`/`Trans_mem_T_B`）、«8».«8.7-OT-scb-recursive»
  （`OT_scb_recursive`）。
- 状態: 🤖 GREEN-MODULO。私的接尾辞 `_ocv`。
  `OTint_hp_condV_adm_holds` は `ExchVres_adm_M_tower` 上、
  `OTint_hp_condV_nadm_holds` は `ExchV_nf3x` 上（＝§8.4 `s84x_L` 塔クラスタの
  未移植 1 点。並行 agent の `ExchV_M_tower` が両者を落とす）。
-/

namespace PSS

/-! ## 0. 純 `BT` 補助（`8.7-otint-transport` の private 群の複製、接尾辞 `_ocv`） -/

private theorem leBT_refl_ocv (x : BT) : leBT x x = true := by simp [leBT]

private theorem leBT_of_less_ocv {a b : BT} (h : lessBT a b = true) :
    leBT a b = true := by simp [leBT, h]

private theorem leBT_iff_ocv (a b : BT) :
    leBT a b = true ↔ (lessBT a b = true ∨ a = b) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq]

private theorem leBT_trans_ocv {a b c : BT}
    (h1 : leBT a b = true) (h2 : leBT b c = true) : leBT a c = true := by
  rw [leBT_iff_ocv] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (lessBT_linear_trans a b c h1 h2)
  · subst h2; exact Or.inl h1
  · subst h1; exact Or.inl h2
  · subst h1; subst h2; exact Or.inr rfl

private theorem less_le_trans_ocv {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_ocv] at hbc
  rcases hbc with h | h
  · exact lessBT_linear_trans a b c hab h
  · subst h; exact hab

private theorem le_less_trans_ocv {a b c : BT}
    (hab : leBT a b = true) (hbc : lessBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_ocv] at hab
  rcases hab with h | h
  · exact lessBT_linear_trans a b c h hbc
  · subst h; exact hbc

/-- `flatBT (Dprin e X) = Dsym e :: flatBT X`。 -/
private theorem flatBT_Dprin_ocv (e : ℕ∞) (X : BT) :
    flatBT (Dprin e X) = Sym.dsym e :: flatBT X := rfl

/-- `isPTB_str (flatBT (Dprin e X))`（`X ∈ T_B` なら principal 文字列）。 -/
private theorem isPTB_str_Dpt_ocv (e : ℕ) {X : BT} (hX : X ∈ T_B) :
    isPTB_str (flatBT (Dprin (e : ℕ∞) X)) := by
  refine ⟨.db (e : ℕ∞) X, ?_, rfl⟩
  have h2 : dfree_BT X = true := hX
  simp only [dfree_BP, Bool.and_eq_true]
  refine ⟨?_, h2⟩
  simp [bne]

/-! ## 1. 塔 `oix_twr`（Isabelle `oix_twr`, pss_wip.thy:111129） -/

/-- Isabelle `oix_twr`: `block(x) = t₂ +_B D_e x`、`twr^k(base)`。 -/
private def oix_twr (t2 : BT) (e : ℕ) (base : BT) : ℕ → BT
  | 0 => base
  | k + 1 => addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e base k))

private theorem oix_twr_shift_ocv (t2 : BT) (e : ℕ) (base : BT) (k : ℕ) :
    oix_twr t2 e base (k + 1) = oix_twr t2 e (addBT t2 (Dprin (e : ℕ∞) base)) k := by
  induction k with
  | zero => rfl
  | succ j ih =>
      show addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e base (j + 1)))
         = addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e (addBT t2 (Dprin (e : ℕ∞) base)) j))
      rw [ih]

private theorem oix_twr_TB_ocv {t2 base : BT} {e : ℕ} (ht2 : t2 ∈ T_B)
    (hb : base ∈ T_B) (k : ℕ) : oix_twr t2 e base k ∈ T_B := by
  induction k with
  | zero => exact hb
  | succ j ih =>
      have hd : Dprin (e : ℕ∞) (oix_twr t2 e base j) ∈ T_B :=
        Dprin_mem_T_B (by simp) ih
      exact addBT_mem_T_B ht2 hd

private theorem s85b_W_eq_Dprin_twr_ocv (t2 base : BT) (e : ℕ) (k : ℕ) :
    s85b_W e t2 base k = Dprin (e : ℕ∞) (oix_twr t2 e base k) := by
  induction k with
  | zero => rfl
  | succ j ih => simp only [s85b_W, oix_twr, ih]

/-- `(replicate k xs).flatten ++ xs = xs ++ (replicate k xs).flatten`。 -/
private theorem flatten_rep_comm_ocv {α : Type} (xs : List α) (k : ℕ) :
    (List.replicate k xs).flatten ++ xs = xs ++ (List.replicate k xs).flatten := by
  induction k with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

/-- Isabelle `oix_twr_flat` (pss_wip.thy:111165)。塔の flat 文字列＝base の
`k`-fold `(s₀ D_e · b₀)` wrap（`m_7_2_add_scb_conj2` ＝ `add_scb_replace_last`）。 -/
private theorem oix_twr_flat_ocv {t2 c base : BT} {e : ℕ} {s0 b0 : List Sym}
    (inner : scb_decomp (addBT t2 c) s0 (flatBT c) b0)
    (ht2 : t2 ∈ T_B) (hc : c ∈ T_B) (hcp : ∃ p, c = .trm [p])
    (hb : base ∈ T_B) (k : ℕ) :
    flatBT (oix_twr t2 e base k)
      = (List.replicate k (s0 ++ [Sym.dsym (e : ℕ∞)])).flatten
        ++ flatBT base ++ (List.replicate k b0).flatten := by
  induction k with
  | zero => simp [oix_twr]
  | succ j ih =>
      have twrTB : oix_twr t2 e base j ∈ T_B := oix_twr_TB_ocv ht2 hb j
      have c'TB : Dprin (e : ℕ∞) (oix_twr t2 e base j) ∈ T_B :=
        Dprin_mem_T_B (by simp) twrTB
      have c'p : ∃ p, Dprin (e : ℕ∞) (oix_twr t2 e base j) = .trm [p] := ⟨_, rfl⟩
      have sub : scb_decomp (addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e base j))) s0
          (flatBT (Dprin (e : ℕ∞) (oix_twr t2 e base j))) b0 :=
        add_scb_replace_last t2 c (Dprin (e : ℕ∞) (oix_twr t2 e base j)) s0 b0
          ht2 hc hcp c'TB c'p inner
      have flateq : flatBT (addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e base j)))
          = s0 ++ flatBT (Dprin (e : ℕ∞) (oix_twr t2 e base j)) ++ b0 := sub.1
      have flatD : flatBT (Dprin (e : ℕ∞) (oix_twr t2 e base j))
          = Sym.dsym (e : ℕ∞) :: flatBT (oix_twr t2 e base j) := rfl
      show flatBT (addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e base j))) = _
      rw [flateq, flatD, ih]
      -- 文字列代数
      rw [List.replicate_succ, List.flatten_cons]
      have hb0 : (List.replicate (j + 1) b0).flatten
          = (List.replicate j b0).flatten ++ b0 := by
        rw [List.replicate_succ']; simp [List.flatten_append]
      rw [hb0]
      simp [List.append_assoc]

/-! ## 2. 塔の順序（Isabelle `oix_twr_grow`/`oix_twr_base_mono`/`oix_twr_ord_*0`） -/

/-- 同一 head `e` の `Dprin` の狭義単調性。 -/
private theorem lessBT_Dprin_same_ocv (e : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin e a) (Dprin e b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- `lessBP p p = false`。 -/
private theorem lessBP_irrefl_ocv (p : BP) : lessBP p p = false := by
  cases p with
  | db u b => simp [lessBP, lessBT_linear_irrefl]

/-- Isabelle `oix_twr_grow`。 -/
private theorem oix_twr_grow_ocv (t2 : BT) (e k : ℕ) :
    lessBT (oix_twr t2 e t2 k) (oix_twr t2 e t2 (k + 1)) = true := by
  induction k with
  | zero =>
      have ne : Dprin (e : ℕ∞) t2 ≠ BZero := by simp [Dprin, BZero]
      simpa [oix_twr] using lessBT_addBT_self t2 (Dprin (e : ℕ∞) t2) ne
  | succ j ih =>
      have hd : lessBT (Dprin (e : ℕ∞) (oix_twr t2 e t2 j))
          (Dprin (e : ℕ∞) (oix_twr t2 e t2 (j + 1))) = true :=
        lessBT_Dprin_same_ocv _ ih
      simpa [oix_twr] using addBT_lt_right_bf t2 _ _ hd

/-- Isabelle `oix_twr_base_mono`。 -/
private theorem oix_twr_base_mono_ocv {t2 base base' : BT} {e : ℕ}
    (h : leBT base base' = true) (k : ℕ) :
    leBT (oix_twr t2 e base k) (oix_twr t2 e base' k) = true := by
  induction k with
  | zero => exact h
  | succ j ih =>
      by_cases heq : oix_twr t2 e base j = oix_twr t2 e base' j
      · simp only [oix_twr, heq]; exact leBT_refl_ocv _
      · have hlt : lessBT (oix_twr t2 e base j) (oix_twr t2 e base' j) = true := by
          rw [leBT_iff_ocv] at ih; rcases ih with h' | h'
          · exact h'
          · exact absurd h' heq
        have hd : lessBT (Dprin (e : ℕ∞) (oix_twr t2 e base j))
            (Dprin (e : ℕ∞) (oix_twr t2 e base' j)) = true :=
          lessBT_Dprin_same_ocv _ hlt
        have := addBT_lt_right_bf t2 _ _ hd
        simp only [oix_twr]; exact leBT_of_less_ocv this

/-- `leBT BZero t2 = true`。 -/
private theorem leBT_BZero_ocv (t2 : BT) : leBT BZero t2 = true := by
  rcases t2 with ⟨ps⟩
  cases ps with
  | nil => exact leBT_refl_ocv BZero
  | cons a as => simp [leBT, lessBT, lessBPList, BZero]

/-- Isabelle `oix_twr_ord_lo0`。 -/
private theorem oix_twr_ord_lo0_ocv (t2 : BT) (e k : ℕ) :
    leBT (oix_twr t2 e BZero k) (oix_twr t2 e t2 k) = true :=
  oix_twr_base_mono_ocv (leBT_BZero_ocv t2) k

/-- Isabelle `oix_twr_ord_hi0`。 -/
private theorem oix_twr_ord_hi0_ocv (t2 : BT) (e k : ℕ) :
    leBT (oix_twr t2 e t2 k) (oix_twr t2 e BZero (k + 1)) = true := by
  have ne : Dprin (e : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
  have b : leBT t2 (addBT t2 (Dprin (e : ℕ∞) BZero)) = true :=
    leBT_of_less_ocv (lessBT_addBT_self t2 (Dprin (e : ℕ∞) BZero) ne)
  have hmono := oix_twr_base_mono_ocv (t2 := t2) (e := e) b k
  rwa [← oix_twr_shift_ocv] at hmono

/-! ## 3. `G` 機構（Isabelle `m_8_7_GBT_addBT`/`b1x_GBT_size`/`oix_lessBT_snoc_band`） -/

private theorem gatherBPList_append_ocv (u : ℕ∞) (xs ys : List BP) :
    gatherBPList u (xs ++ ys) = gatherBPList u xs ++ gatherBPList u ys := by
  induction xs with
  | nil => simp [gatherBPList]
  | cons a as ih => simp [gatherBPList, ih, List.append_assoc]

/-- Isabelle `m_8_7_GBT_addBT`。 -/
private theorem GBT_addBT_ocv (u : ℕ∞) (t c : BT) :
    GBT u (addBT t c) = GBT u t ∪ GBT u c := by
  rcases t with ⟨ps⟩; rcases c with ⟨qs⟩
  ext x
  simp only [addBT, GBT, gatherBT, gatherBPList_append_ocv, List.contains_append,
    Set.mem_setOf_eq, Set.mem_union, Bool.or_eq_true]

private theorem GBT_subset_addBT_left_ocv {u : ℕ∞} {t c : BT} {x : BT}
    (hx : x ∈ GBT u t) : x ∈ GBT u (addBT t c) := by
  rw [GBT_addBT_ocv]; exact Or.inl hx

/-- OT principal `DB w b` の `G_w` は body `b` で狭義下界（`GBT_lessBT_of_isOT_BP`）。 -/
private theorem GBT_lessBT_of_isOT_BP_ocv {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : ∀ x ∈ GBT w b, lessBT x b = true := by
  intro x hx
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

private theorem mem_gatherBPList_ocv (u : ℕ∞) (ps : List BP) (y : BT)
    (h : (gatherBPList u ps).contains y = true) :
    ∃ p ∈ ps, (gatherBP u p).contains y = true := by
  induction ps with
  | nil => simp [gatherBPList] at h
  | cons a as ih =>
      simp only [gatherBPList, List.contains_append, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨a, by simp, h⟩
      · obtain ⟨p, hp, hy⟩ := ih h
        exact ⟨p, by simp [hp], hy⟩

private theorem bpWeight_le_ocv {p : BP} :
    ∀ {ps : List BP}, p ∈ ps → bpWeight p ≤ bpListWeight ps
  | q :: qs, hmem => by
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h; simp only [bpListWeight]; omega
      · have := bpWeight_le_ocv h; simp only [bpListWeight]; omega

/-- Isabelle `b1x_GBT_size`（`btWeight` 版）。 -/
private theorem GBT_size_ocv (u : ℕ∞) (n : ℕ) :
    ∀ (t y : BT), btWeight t = n → y ∈ GBT u t → btWeight y < btWeight t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t y hn hy
    rcases t with ⟨ps⟩
    have hcontains : (gatherBPList u ps).contains y = true := by
      simpa [GBT, gatherBT] using hy
    obtain ⟨p, hp, hyp⟩ := mem_gatherBPList_ocv u ps y hcontains
    rcases p with ⟨w, b⟩
    have hwle : (gatherBP u (BP.db w b)).contains y = true := hyp
    by_cases hle : (u ≤ w)
    · rw [gatherBP, if_pos (by simpa using hle)] at hwle
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hwle
      have hbwp : bpWeight (BP.db w b) ≤ bpListWeight ps := bpWeight_le_ocv hp
      have hbw : btWeight b < btWeight (BT.trm ps) := by
        simp only [bpWeight, btWeight] at *; omega
      rcases hwle with hyb | hyb
      · subst hyb; exact hbw
      · have hymem : y ∈ GBT u b := by simpa [GBT, gatherBT] using hyb
        have := ih (btWeight b) (by rw [← hn]; exact hbw) b y rfl hymem
        omega
    · rw [gatherBP, if_neg (by simpa using hle)] at hwle
      simp at hwle

/-- Isabelle `oix_lessBT_snoc_band`（`btWeight` 版）。 -/
private theorem lessBT_snoc_band_ocv : ∀ (ps : List BP) (c : BP) (x : BT),
    lessBT x (BT.trm (ps ++ [c])) = true → btWeight x < btWeight (BT.trm ps) →
    lessBT x (BT.trm ps) = true
  | [], c, x, _, hsz => by
      rcases x with ⟨xs⟩
      simp only [btWeight, bpListWeight] at hsz
      omega
  | p :: ps', c, x, hlt, hsz => by
      rcases x with ⟨xs⟩
      cases xs with
      | nil => simp [lessBT, lessBPList]
      | cons a as =>
          simp only [List.cons_append, lessBT, lessBPList, Bool.or_eq_true,
            Bool.and_eq_true] at hlt
          rcases hlt with hlp | ⟨hap, hrest⟩
          · simp [lessBT, lessBPList, hlp]
          · have hab : a = p := by simpa using hap
            subst hab
            have hsz' : btWeight (BT.trm as) < btWeight (BT.trm ps') := by
              simp only [btWeight, bpListWeight] at hsz ⊢; omega
            have hrec : lessBT (BT.trm as) (BT.trm ps') = true :=
              lessBT_snoc_band_ocv ps' c (BT.trm as) hrest hsz'
            have : lessBPList as ps' = true := hrec
            simp [lessBT, lessBPList, lessBP_irrefl_ocv, this]

/-- Isabelle `oix_G_prefix_lt` (pss_wip.thy:111110)。host core の (OT3) guard が
`t₂` の prefix に制限される。 -/
private theorem oix_G_prefix_lt_ocv {u : ℕ∞} {t2 : BT} {cp : BP}
    (hostGP : isOT_BP (BP.db u (addBT t2 (BT.trm [cp]))) = true)
    {x : BT} (hx : x ∈ GBT u t2) : lessBT x t2 = true := by
  rcases t2 with ⟨ps2⟩
  have hsum : addBT (BT.trm ps2) (BT.trm [cp]) = BT.trm (ps2 ++ [cp]) := by simp [addBT]
  have xin : x ∈ GBT u (addBT (BT.trm ps2) (BT.trm [cp])) :=
    GBT_subset_addBT_left_ocv hx
  have xlt : lessBT x (BT.trm (ps2 ++ [cp])) = true := by
    have := GBT_lessBT_of_isOT_BP_ocv hostGP x
    rw [hsum] at this
    exact this xin
  have xsz : btWeight x < btWeight (BT.trm ps2) :=
    GBT_size_ocv u (btWeight (BT.trm ps2)) (BT.trm ps2) x rfl hx
  exact lessBT_snoc_band_ocv ps2 cp x xlt xsz

/-! ## 4. `descP` / `isOT_BPList` の append/snoc 補題（`8.7-otint-transport` の複製） -/

private theorem isOT_BPList_append_ocv (xs ys : List BP) :
    isOT_BPList (xs ++ ys) = (isOT_BPList xs && isOT_BPList ys) := by
  induction xs with
  | nil => simp [isOT_BPList]
  | cons p ps ih => simp [isOT_BPList, ih, Bool.and_assoc]

private theorem descP_prefix_ocv : ∀ (xs ys : List BP),
    descP (xs ++ ys) = true → descP xs = true
  | [], _, _ => by simp [descP]
  | [_], _, _ => by simp [descP]
  | p :: q :: ps, ys, h => by
      have hsplit : leBT (BT.trm [q]) (BT.trm [p]) = true ∧
          descP ((q :: ps) ++ ys) = true := by
        simpa [descP, List.cons_append] using h
      have hIH := descP_prefix_ocv (q :: ps) ys hsplit.2
      simp [descP, hsplit.1, hIH]

private theorem descP_ge_last_ocv : ∀ (ps : List BP) (q : BP) (hne : ps ≠ []),
    descP ps = true → q ∈ ps → leBT (BT.trm [ps.getLast hne]) (BT.trm [q]) = true
  | [p], q, _, _, hq => by
      have : q = p := by simpa using hq
      subst this; simpa using leBT_refl_ocv (BT.trm [q])
  | p :: q2 :: rest, q, _, h, hq => by
      have hne' : (q2 :: rest) ≠ [] := by simp
      have hsplit : leBT (BT.trm [q2]) (BT.trm [p]) = true ∧
          descP (q2 :: rest) = true := by simpa [descP] using h
      have hlast : (p :: q2 :: rest).getLast (by simp) = (q2 :: rest).getLast hne' := by
        simp [List.getLast_cons]
      rw [hlast]
      have hlastq2 : leBT (BT.trm [(q2 :: rest).getLast hne']) (BT.trm [q2]) = true :=
        descP_ge_last_ocv (q2 :: rest) q2 hne' hsplit.2 (by simp)
      rw [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst hq
        exact leBT_trans_ocv hlastq2 hsplit.1
      · exact descP_ge_last_ocv (q2 :: rest) q hne' hsplit.2 hq

private theorem descP_snoc_last_le_ocv : ∀ (qs : List BP) (c : BP) (hne : qs ≠ []),
    descP (qs ++ [c]) = true →
    leBT (BT.trm [c]) (BT.trm [qs.getLast hne]) = true
  | [], _, hne, _ => absurd rfl hne
  | [d], c, _, h => by
      have : leBT (BT.trm [c]) (BT.trm [d]) = true := by simpa [descP] using h
      simpa using this
  | d :: e :: es, c, _, h => by
      have hne' : (e :: es) ≠ [] := by simp
      have hsplit : leBT (BT.trm [e]) (BT.trm [d]) = true ∧
          descP ((e :: es) ++ [c]) = true := by
        simpa [descP, List.cons_append] using h
      have hIH := descP_snoc_last_le_ocv (e :: es) c hne' hsplit.2
      have hlast : (d :: e :: es).getLast (by simp) = (e :: es).getLast hne' := by
        simp [List.getLast_cons]
      rw [hlast]; exact hIH

private theorem descP_snoc_ocv : ∀ (xs : List BP) (pn : BP),
    descP xs = true →
    (∀ (h : xs ≠ []), leBT (BT.trm [pn]) (BT.trm [xs.getLast h]) = true) →
    descP (xs ++ [pn]) = true
  | [], _, _, _ => by simp [descP]
  | [d], pn, _, hle => by
      have hd : leBT (BT.trm [pn]) (BT.trm [d]) = true := by
        have := hle (by simp); simpa using this
      simp [descP, hd]
  | d :: e :: es, pn, hd, hle => by
      have hsplit : leBT (BT.trm [e]) (BT.trm [d]) = true ∧ descP (e :: es) = true := by
        simpa [descP] using hd
      have hle' : ∀ (h : (e :: es) ≠ []),
          leBT (BT.trm [pn]) (BT.trm [(e :: es).getLast h]) = true := by
        intro h
        have hne : (d :: e :: es) ≠ [] := by simp
        have hg : (d :: e :: es).getLast hne = (e :: es).getLast h := by
          simp [List.getLast_cons]
        have := hle hne; rwa [hg] at this
      have hIH := descP_snoc_ocv (e :: es) pn hsplit.2 hle'
      have hrw : (d :: e :: es) ++ [pn] = d :: e :: (es ++ [pn]) := by simp
      rw [hrw]
      have hIH' : descP (e :: (es ++ [pn])) = true := by
        have hcast : e :: (es ++ [pn]) = (e :: es) ++ [pn] := by simp
        rw [hcast]; exact hIH
      show (leBT (BT.trm [e]) (BT.trm [d]) && descP (e :: (es ++ [pn]))) = true
      simp only [hsplit.1, hIH', Bool.and_self]

/-- `isOT_BT (addBT t c) → isOT_BT t`（Isabelle `isOT_BT_addBT_left`）。 -/
private theorem isOT_BT_addBT_left_ocv {t c : BT}
    (h : isOT_BT (addBT t c) = true) : isOT_BT t = true := by
  rcases t with ⟨as⟩; rcases c with ⟨bs⟩
  simp only [addBT, isOT_BT, isOT_BPList_append_ocv, Bool.and_eq_true] at h
  simp only [isOT_BT, Bool.and_eq_true]
  exact ⟨h.1.1, descP_prefix_ocv as bs h.2⟩

/-! ## 5. host core 抽出（`hostGP` から `t₂ ∈ OT`・descP・HB を導出） -/

/-- `hostGP` の body OT 部分。 -/
private theorem host_body_isOT_ocv {t2 : BT} {u v1 : ℕ}
    (hostGP : isOT_BP (BP.db (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true) :
    isOT_BT (addBT t2 (Dprin (v1 : ℕ∞) BZero)) = true := by
  simp only [isOT_BP, Bool.and_eq_true] at hostGP; exact hostGP.1

private theorem host_t2OT_ocv {t2 : BT} {u v1 : ℕ}
    (hostGP : isOT_BP (BP.db (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true) :
    isOT_BT t2 = true :=
  isOT_BT_addBT_left_ocv (host_body_isOT_ocv hostGP)

/-- HB: `t₂` の各成分は末尾 `D_{v₁} 0` を上回る（host body の descP から）。 -/
private theorem host_HB_ocv {ps2 : List BP} {u v1 : ℕ}
    (hostGP : isOT_BP (BP.db (u : ℕ∞)
      (addBT (BT.trm ps2) (Dprin (v1 : ℕ∞) BZero))) = true)
    {q : BP} (hq : q ∈ ps2) :
    leBT (Dprin (v1 : ℕ∞) BZero) (BT.trm [q]) = true := by
  have hbody := host_body_isOT_ocv hostGP
  have hsum : addBT (BT.trm ps2) (Dprin (v1 : ℕ∞) BZero)
      = BT.trm (ps2 ++ [BP.db (v1 : ℕ∞) BZero]) := by simp [addBT, Dprin]
  rw [hsum] at hbody
  have hdesc : descP (ps2 ++ [BP.db (v1 : ℕ∞) BZero]) = true := by
    simp only [isOT_BT, Bool.and_eq_true] at hbody; exact hbody.2
  have hqin : q ∈ ps2 ++ [BP.db (v1 : ℕ∞) BZero] := by simp [hq]
  have hge := descP_ge_last_ocv (ps2 ++ [BP.db (v1 : ℕ∞) BZero]) q (by simp) hdesc hqin
  have hlast : (ps2 ++ [BP.db (v1 : ℕ∞) BZero]).getLast (by simp)
      = BP.db (v1 : ℕ∞) BZero := List.getLast_append_singleton _
  rw [hlast] at hge
  simpa [Dprin] using hge

/-! ## 6. `newOT`: 差し替え core `D_e(V_k)` は OT principal（Isabelle `oix_condV_adm_newOT`） -/

/-- `GBT e (Dprin e X) = insert X (GBT e X)`。 -/
private theorem GBT_Dprin_self_ocv (e : ℕ∞) (X : BT) :
    GBT e (Dprin e X) = insert X (GBT e X) := by
  have hd : decide (e ≤ e) = true := by simp
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, hd, if_true,
    List.append_nil, List.contains_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
    Bool.or_eq_true, beq_iff_eq]

/-- Isabelle `oix_condV_adm_newOT` (pss_wip.thy:111266)。塔高さ帰納で、host core の
(OT3) guard を通して差し替え core が OT principal であることを示す。HB は host body の
descP から内部で導出。 -/
private theorem oix_condV_adm_newOT_ocv {t2 : BT} {e v1 : ℕ}
    (hostGP : isOT_BP (BP.db (e : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true)
    (ev : e < v1) (t2ne : t2 ≠ BZero) (k : ℕ) :
    isOT_BP (BP.db (e : ℕ∞) (oix_twr t2 e t2 k)) = true := by
  obtain ⟨ps2⟩ := t2
  have ps2ne : ps2 ≠ [] := by rintro rfl; exact t2ne rfl
  have t2OT : isOT_BT (BT.trm ps2) = true := host_t2OT_ocv hostGP
  induction k with
  | zero =>
      show isOT_BP (BP.db (e : ℕ∞) (BT.trm ps2)) = true
      have G0 : ∀ x ∈ GBT (e : ℕ∞) (BT.trm ps2), lessBT x (BT.trm ps2) = true := by
        intro x hx
        exact oix_G_prefix_lt_ocv (cp := BP.db (v1 : ℕ∞) BZero) hostGP hx
      simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
      refine ⟨t2OT, ?_⟩
      intro x hx
      exact G0 x (by simpa [GBT, List.contains_iff_mem] using hx)
  | succ k ih =>
      set X := oix_twr (BT.trm ps2) e (BT.trm ps2) k with hXdef
      have XOT : isOT_BT X = true := by
        simp only [isOT_BP, Bool.and_eq_true] at ih; exact ih.1
      have GX : ∀ y ∈ GBT (e : ℕ∞) X, lessBT y X = true :=
        GBT_lessBT_of_isOT_BP_ocv ih
      have hlast_in : ps2.getLast ps2ne ∈ ps2 := List.getLast_mem ps2ne
      have HBl : leBT (Dprin (v1 : ℕ∞) BZero) (BT.trm [ps2.getLast ps2ne]) = true :=
        host_HB_ocv hostGP hlast_in
      have hev : ((e : ℕ∞) < (v1 : ℕ∞)) := by exact_mod_cast ev
      have headlt : lessBT (BT.trm [BP.db (e : ℕ∞) X]) (Dprin (v1 : ℕ∞) BZero) = true := by
        simp [Dprin, lessBT, lessBPList, lessBP, hev]
      have dstep : leBT (BT.trm [BP.db (e : ℕ∞) X]) (BT.trm [ps2.getLast ps2ne]) = true := by
        by_cases heq : Dprin (v1 : ℕ∞) BZero = BT.trm [ps2.getLast ps2ne]
        · rw [heq] at headlt; exact leBT_of_less_ocv headlt
        · have hlt : lessBT (Dprin (v1 : ℕ∞) BZero) (BT.trm [ps2.getLast ps2ne]) = true := by
            rw [leBT_iff_ocv] at HBl; rcases HBl with h | h
            · exact h
            · exact absurd h heq
          have : lessBT (Dprin (v1 : ℕ∞) BZero) (BT.trm [ps2.getLast ps2ne]) = true := hlt
          exact leBT_of_less_ocv
            (lessBT_linear_trans _ _ _ headlt this)
      have descps2 : descP ps2 = true := by
        simp only [isOT_BT, Bool.and_eq_true] at t2OT; exact t2OT.2
      have otps2 : isOT_BPList ps2 = true := by
        simp only [isOT_BT, Bool.and_eq_true] at t2OT; exact t2OT.1
      have descV : descP (ps2 ++ [BP.db (e : ℕ∞) X]) = true :=
        descP_snoc_ocv ps2 (BP.db (e : ℕ∞) X) descps2 (fun _ => dstep)
      have otV : isOT_BPList (ps2 ++ [BP.db (e : ℕ∞) X]) = true := by
        rw [isOT_BPList_append_ocv]
        simp only [isOT_BPList, Bool.and_true, Bool.and_eq_true]
        exact ⟨otps2, ih⟩
      have Veq : oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)
          = BT.trm (ps2 ++ [BP.db (e : ℕ∞) X]) := by
        show addBT (BT.trm ps2) (Dprin (e : ℕ∞) X) = _; simp [addBT, Dprin]
      have VOT : isOT_BT (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)) = true := by
        rw [Veq]; simp only [isOT_BT, Bool.and_eq_true]; exact ⟨otV, descV⟩
      have grow : lessBT X (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)) = true :=
        oix_twr_grow_ocv (BT.trm ps2) e k
      have t2lt : lessBT (BT.trm ps2) (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)) = true := by
        have ne : Dprin (e : ℕ∞) X ≠ BZero := by simp [Dprin, BZero]
        simpa [oix_twr] using lessBT_addBT_self (BT.trm ps2) (Dprin (e : ℕ∞) X) ne
      have GV : ∀ y ∈ GBT (e : ℕ∞) (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)),
          lessBT y (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)) = true := by
        intro y hy
        have hVadd : oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1)
            = addBT (BT.trm ps2) (Dprin (e : ℕ∞) X) := rfl
        rw [hVadd, GBT_addBT_ocv] at hy
        simp only [Set.mem_union] at hy
        rcases hy with hyt | hyd
        · have hxt := oix_G_prefix_lt_ocv (cp := BP.db (v1 : ℕ∞) BZero) hostGP hyt
          exact lessBT_linear_trans _ _ _ hxt t2lt
        · rw [GBT_Dprin_self_ocv] at hyd
          rcases Set.mem_insert_iff.mp hyd with hyX | hyGX
          · subst hyX; exact grow
          · exact lessBT_linear_trans _ _ _ (GX y hyGX) grow
      show isOT_BP (BP.db (e : ℕ∞) (oix_twr (BT.trm ps2) e (BT.trm ps2) (k + 1))) = true
      simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
      refine ⟨VOT, ?_⟩
      intro x hx
      exact GV x (by simpa [GBT, List.contains_iff_mem] using hx)

/-! ## 7. `setle`: `V`-塔は `W`-塔に `G`-支配される（Isabelle `oix_condV_adm_setle0`） -/

private theorem GBT_Dprin_le_ocv {u e : ℕ∞} (Y : BT) (h : u ≤ e) :
    GBT u (Dprin e Y) = insert Y (GBT u Y) := by
  have hd : decide (u ≤ e) = true := decide_eq_true h
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, hd, if_true,
    List.append_nil, List.contains_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
    Bool.or_eq_true, beq_iff_eq]

private theorem mem_GBT_Dprin_ocv {u e : ℕ∞} {Y x : BT}
    (hx : x ∈ GBT u (Dprin e Y)) : u ≤ e ∧ (x = Y ∨ x ∈ GBT u Y) := by
  by_cases h : u ≤ e
  · rw [GBT_Dprin_le_ocv Y h] at hx
    exact ⟨h, Set.mem_insert_iff.mp hx⟩
  · exfalso
    have hd : decide (u ≤ e) = false := decide_eq_false h
    simp [GBT, Dprin, gatherBT, gatherBPList, gatherBP, hd] at hx

/-- Isabelle `oix_condV_adm_setle0` (pss_wip.thy:111476)。仮定なし。 -/
private theorem oix_condV_adm_setle0_ocv (t2 : BT) (e : ℕ) (u : ℕ∞) (k : ℕ) :
    b1x_setle (GBT u (oix_twr t2 e t2 (k + 1)))
      (insert (oix_twr t2 e BZero (k + 1)) (GBT u (oix_twr t2 e BZero (k + 1)))) := by
  induction k with
  | zero =>
      intro x hx
      have hxadd : x ∈ GBT u (addBT t2 (Dprin (e : ℕ∞) t2)) := by
        have : oix_twr t2 e t2 (0 + 1) = addBT t2 (Dprin (e : ℕ∞) t2) := rfl
        rwa [this] at hx
      rw [GBT_addBT_ocv] at hxadd
      simp only [Set.mem_union] at hxadd
      have hW1 : oix_twr t2 e BZero (0 + 1) = addBT t2 (Dprin (e : ℕ∞) BZero) := rfl
      rcases hxadd with hxt | hxd
      · refine ⟨x, ?_, leBT_refl_ocv x⟩
        rw [Set.mem_insert_iff]; right
        rw [hW1, GBT_addBT_ocv]; exact Or.inl hxt
      · obtain ⟨_hue, hcase⟩ := mem_GBT_Dprin_ocv hxd
        rcases hcase with hxt2 | hxt2
        · have ne : Dprin (e : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
          refine ⟨oix_twr t2 e BZero (0 + 1), Set.mem_insert _ _, ?_⟩
          rw [hW1, hxt2]
          exact leBT_of_less_ocv (lessBT_addBT_self t2 (Dprin (e : ℕ∞) BZero) ne)
        · refine ⟨x, ?_, leBT_refl_ocv x⟩
          rw [Set.mem_insert_iff]; right
          rw [hW1, GBT_addBT_ocv]; exact Or.inl hxt2
  | succ k ih =>
      intro x hx
      have hVeq : oix_twr t2 e t2 (k + 1 + 1)
          = addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e t2 (k + 1))) := rfl
      have hWeq : oix_twr t2 e BZero (k + 1 + 1)
          = addBT t2 (Dprin (e : ℕ∞) (oix_twr t2 e BZero (k + 1))) := rfl
      rw [hVeq, GBT_addBT_ocv] at hx
      simp only [Set.mem_union] at hx
      rcases hx with hxt | hxd
      · refine ⟨x, ?_, leBT_refl_ocv x⟩
        rw [Set.mem_insert_iff]; right
        rw [hWeq, GBT_addBT_ocv]; exact Or.inl hxt
      · obtain ⟨hue, hcase⟩ := mem_GBT_Dprin_ocv hxd
        rcases hcase with hxVp | hxVp
        · subst hxVp
          -- x = Vp; leBT Vp W via base_mono + shift
          have ne : Dprin (e : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
          have hbase : leBT t2 (addBT t2 (Dprin (e : ℕ∞) BZero)) = true :=
            leBT_of_less_ocv (lessBT_addBT_self t2 (Dprin (e : ℕ∞) BZero) ne)
          have hmono := oix_twr_base_mono_ocv (t2 := t2) (e := e) hbase (k + 1)
          have hshift : oix_twr t2 e (addBT t2 (Dprin (e : ℕ∞) BZero)) (k + 1)
              = oix_twr t2 e BZero (k + 1 + 1) := (oix_twr_shift_ocv t2 e BZero (k + 1)).symm
          rw [hshift] at hmono
          exact ⟨oix_twr t2 e BZero (k + 1 + 1), Set.mem_insert _ _, hmono⟩
        · -- x ∈ GBT u Vp; use ih
          obtain ⟨y, hy, hxy⟩ := ih x hxVp
          have hsub : insert (oix_twr t2 e BZero (k + 1))
              (GBT u (oix_twr t2 e BZero (k + 1)))
              ⊆ GBT u (oix_twr t2 e BZero (k + 1 + 1)) := by
            rw [hWeq, GBT_addBT_ocv, ← GBT_Dprin_le_ocv (oix_twr t2 e BZero (k + 1)) hue]
            intro z hz; exact Or.inr hz
          refine ⟨y, ?_, hxy⟩
          rw [Set.mem_insert_iff]; right
          exact hsub hy

/-! ## 8. ホスト固有の小補題（exchV-props の private 版の複製） -/

/-- Isabelle `s85b_jm1_adm`。許容枝では第 2 基点が潰れる。 -/
private theorem jm1_adm_ocv {M : PS} (h : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by simp [transJm1, Adm, h]

/-- Isabelle `m_8_5_transC2_condV`。条件(V) 枝の `c₂` の閉形式。 -/
private theorem transC2_condV_ocv (M : PS) (hcond : transCondV M = true) :
    transC2 M = Dprin (transV M)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
  have hA : (transCondI M || transCondIII M || transCondV M) = true := by simp [hcond]
  simp [transC2, transC2Core, hA, transJ1]

/-- 条件(V) の算術: `e < v₁`。 -/
private theorem condV_ev_ocv {M : PS} (h : transCondV M = true) :
    entry M 1 (transJ0 M) < entry M 1 (transJ1 M) := by
  simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨_h1, h2⟩, _h3⟩ := h
  show entry M 1 (transJ0 M) < entry M 1 (transJ1 M)
  simp only [transJ0, transJ1]
  omega

private theorem BZero_mem_T_B_ocv : (BZero : BT) ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

/-! ## 9. 条件(V)-adm leg（Isabelle `oix_OTint_condV_adm`） -/

/-- **`OTint_hp_condV_adm` の discharge**（house pattern）。
値形 `ExchV_scbdec_adm_forms` は `ExchVres_adm_M_tower` 上で得られるので、その塔 Prop を
仮定に取る（並行 agent の `ExchV_M_tower` が供給）。 -/
theorem OTint_hp_condV_adm_holds (hAF : ExchVres_adm_M_tower) : OTint_hp_condV_adm := by
  intro N m hST hmono _j1gt hcond hadm _hhp hOT hm
  have hR : RTPS N := STPS_RTPS N hST
  have hM : TPS N := STPS_TPS N hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds N hR hM hmono hcond
  obtain ⟨hVraw, _hc1eq, ht2TBr, _hjm1lt⟩ := c1_shape_holds N hR hM hmono hj₁ ht₁
  have hjm1adm : transJm1 N = transJ0 N := jm1_adm_ocv hadm
  have ht2ner : transT2 N ≠ BZero := t2_nonzero_condV_holds N hR hM hmono hcond
  have hev0 : entry N 1 (transJ0 N) < entry N 1 (transJ1 N) := condV_ev_ocv hcond
  obtain ⟨s0, s1, b0, b1, hd0, _hd1, hk1, h4, h5⟩ :=
    adm_forms_holds hAF N hST hmono hcond hadm
  set e := entry N 1 (transJ0 N) with he_def
  set v1 := entry N 1 (transJ1 N) with hv1_def
  set t2 := transT2 N with ht2_def
  have ht2TB : t2 ∈ T_B := ht2TBr
  have ht2ne : t2 ≠ BZero := ht2ner
  have hev : e < v1 := hev0
  have hDv1TB : Dprin (v1 : ℕ∞) BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) BZero_mem_T_B_ocv
  have hVe : transV N = (e : ℕ∞) := by rw [hVraw, hjm1adm, ← he_def]
  have hc2eq : transC2 N = Dprin (e : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero)) := by
    rw [transC2_condV_ocv N hcond, hVe, ← ht2_def, ← hv1_def]
  have hc2dec : scb_decomp (Trans N) s1 (flatBT (transC2 N)) b1 := hk1.1
  have hb1 : ∀ x ∈ b1, x = Sym.rp := hc2dec.2.2
  have hc2TB : transC2 N ∈ T_B := by
    rw [hc2eq]; exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht2TB hDv1TB)
  have hc2OT : transC2 N ∈ OT := OT_scb_recursive (Trans N) (transC2 N) s1 b1 hOT hc2TB hc2dec
  have hostGP : isOT_BP (BP.db (e : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true := by
    have hh : isOT_BT (transC2 N) = true := hc2OT
    rw [hc2eq] at hh
    simpa [Dprin, isOT_BT, isOT_BPList, descP] using hh
  have hOTne : Trans N ≠ BZero := by
    intro h0
    have hmem : Sym.dsym (e : ℕ∞) ∈ flatBT (Trans N) := by
      rw [hc2dec.1, hc2eq, flatBT_Dprin_ocv]; simp
    rw [h0] at hmem
    simp [flatBT, BZero] at hmem
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 + 1 := ⟨m - 2, by omega⟩
  -- 塔 flat（値形の replicate-block を塔閉形式に読み替え）
  have hfz : flatBT (BZero : BT) = [Sym.zero] := rfl
  have hbodyV : flatBT (oix_twr t2 e t2 (j + 1))
      = (List.replicate (j + 1) (s0 ++ [Sym.dsym (e : ℕ∞)])).flatten ++ flatBT t2
        ++ (List.replicate (j + 1) b0).flatten :=
    oix_twr_flat_ocv (c := Dprin (v1 : ℕ∞) BZero) hd0 ht2TB hDv1TB ⟨_, rfl⟩ ht2TB (j + 1)
  have hbodyWL : flatBT (oix_twr t2 e BZero (j + 1))
      = (List.replicate (j + 1) (s0 ++ [Sym.dsym (e : ℕ∞)])).flatten ++ [Sym.zero]
        ++ (List.replicate (j + 1) b0).flatten := by
    have := oix_twr_flat_ocv (c := Dprin (v1 : ℕ∞) BZero) (base := BZero) (e := e)
      hd0 ht2TB hDv1TB ⟨_, rfl⟩ BZero_mem_T_B_ocv (j + 1)
    rwa [hfz] at this
  have hbodyWH : flatBT (oix_twr t2 e BZero (j + 1 + 1))
      = (List.replicate (j + 1 + 1) (s0 ++ [Sym.dsym (e : ℕ∞)])).flatten ++ [Sym.zero]
        ++ (List.replicate (j + 1 + 1) b0).flatten := by
    have := oix_twr_flat_ocv (c := Dprin (v1 : ℕ∞) BZero) (base := BZero) (e := e)
      hd0 ht2TB hDv1TB ⟨_, rfl⟩ BZero_mem_T_B_ocv (j + 1 + 1)
    rwa [hfz] at this
  -- 三つの scb 分解
  have hourflat : flatBT (Trans (oper N (j + 1 + 1)))
      = s1 ++ flatBT (Dprin (e : ℕ∞) (oix_twr t2 e t2 (j + 1))) ++ b1 := by
    rw [flatBT_Dprin_ocv, hbodyV, h5 (j + 1)]; simp [List.append_assoc]
  have hloflat : flatBT (operB (Trans N) (numBT j))
      = s1 ++ flatBT (Dprin (e : ℕ∞) (oix_twr t2 e BZero (j + 1))) ++ b1 := by
    rw [flatBT_Dprin_ocv, hbodyWL, h4 j]; simp [List.append_assoc]
  have hhiflat : flatBT (operB (Trans N) (numBT (j + 1)))
      = s1 ++ flatBT (Dprin (e : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1))) ++ b1 := by
    rw [flatBT_Dprin_ocv, hbodyWH, h4 (j + 1)]; simp [List.append_assoc]
  have ourdec : scb_decomp (Trans (oper N (j + 1 + 1))) s1
      (flatBT (Dprin (e : ℕ∞) (oix_twr t2 e t2 (j + 1)))) b1 :=
    ⟨hourflat, fun _ => isPTB_str_Dpt_ocv e (oix_twr_TB_ocv ht2TB ht2TB (j + 1)), hb1⟩
  have lodec : scb_decomp (operB (Trans N) (numBT j)) s1
      (flatBT (Dprin (e : ℕ∞) (oix_twr t2 e BZero (j + 1)))) b1 :=
    ⟨hloflat, fun _ => isPTB_str_Dpt_ocv e (oix_twr_TB_ocv ht2TB BZero_mem_T_B_ocv (j + 1)), hb1⟩
  have hidec : scb_decomp (operB (Trans N) (numBT (j + 1))) s1
      (flatBT (Dprin (e : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1)))) b1 :=
    ⟨hhiflat, fun _ => isPTB_str_Dpt_ocv e (oix_twr_TB_ocv ht2TB BZero_mem_T_B_ocv (j + 1 + 1)), hb1⟩
  -- transport の材料
  have loOT : isOT_BT (operB (Trans N) (numBT j)) = true :=
    (buchholz_fseq_closed (Trans N) j hOT hOTne).1
  have hiOT : isOT_BT (operB (Trans N) (numBT (j + 1))) = true :=
    (buchholz_fseq_closed (Trans N) (j + 1) hOT hOTne).1
  have newOT : isOT_BP (BP.db (e : ℕ∞) (oix_twr t2 e t2 (j + 1))) = true :=
    oix_condV_adm_newOT_ocv hostGP hev ht2ne (j + 1)
  have ordlo := oix_twr_ord_lo0_ocv t2 e (j + 1)
  have ordhi := oix_twr_ord_hi0_ocv t2 e (j + 1)
  have setle : ∀ u : ℕ∞, b1x_setle (GBT u (oix_twr t2 e t2 (j + 1)))
      (insert (oix_twr t2 e BZero (j + 1)) (GBT u (oix_twr t2 e BZero (j + 1)))) :=
    fun u => oix_condV_adm_setle0_ocv t2 e u j
  have isot : isOT_BT (Trans (oper N (j + 1 + 1))) = true :=
    oix_transportD oix_transport_uncond lodec ourdec hidec loOT hiOT newOT ordlo ordhi setle
  have hmST : STPS (oper N (j + 1 + 1)) := STPS.oper hST (j + 1 + 1) (by omega)
  have hmTB : Trans (oper N (j + 1 + 1)) ∈ T_B :=
    Trans_mem_T_B (oper N (j + 1 + 1)) (STPS_RTPS _ hmST)
  exact ⟨isot, hmTB⟩

#print axioms OTint_hp_condV_adm_holds

/-! ## 10. 非 adm 枝の追加機構: `G`-antitonicity ＋ rebased-head newOT -/

mutual
  private theorem gatherBT_antitone_mem_ocv {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ t : BT, x ∈ gatherBT v t → x ∈ gatherBT u t
    | .trm ps, hx => gatherBPList_antitone_mem_ocv huv x ps hx
  private theorem gatherBP_antitone_mem_ocv {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ p : BP, x ∈ gatherBP v p → x ∈ gatherBP u p
    | .db w b, hx => by
        have hvw : v ≤ w := by
          by_contra hn
          simp [gatherBP, hn] at hx
        have huw : u ≤ w := huv.trans hvw
        simp only [gatherBP, hvw, huw, decide_true, if_true, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (gatherBT_antitone_mem_ocv huv x b hx)
  private theorem gatherBPList_antitone_mem_ocv {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ ps : List BP, x ∈ gatherBPList v ps → x ∈ gatherBPList u ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_antitone_mem_ocv huv x p hx)
        · exact Or.inr (gatherBPList_antitone_mem_ocv huv x ps hx)
end

/-- Isabelle `b1x_GBT_antitone`（head の反単調性）を principal guard に持ち上げたもの
（Isabelle `oix_isOT_BP_head_antitone`）。 -/
private theorem oix_isOT_BP_head_antitone_ocv {u v : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db u b) = true) (huv : u ≤ v) : isOT_BP (BP.db v b) = true := by
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  intro x hx
  exact h.2 x (gatherBT_antitone_mem_ocv huv x b hx)

/-- Isabelle `oix_condV_G_guard_at` (pss_wip.thy:112247)。rebased head `u` での
`V`-塔の (OT3) guard（host guard を index `u` で使う）。 -/
private theorem oix_condV_G_guard_at_ocv {t2 : BT} {u e v1 : ℕ}
    (hostGP : isOT_BP (BP.db (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true)
    (k : ℕ) :
    ∀ x ∈ GBT (u : ℕ∞) (oix_twr t2 e t2 k), lessBT x (oix_twr t2 e t2 k) = true := by
  induction k with
  | zero =>
      intro x hx
      exact oix_G_prefix_lt_ocv (cp := BP.db (v1 : ℕ∞) BZero) hostGP hx
  | succ k ih =>
      intro y hy
      set X := oix_twr t2 e t2 k with hXdef
      have grow : lessBT X (oix_twr t2 e t2 (k + 1)) = true := oix_twr_grow_ocv t2 e k
      have t2lt : lessBT t2 (oix_twr t2 e t2 (k + 1)) = true := by
        have ne : Dprin (e : ℕ∞) X ≠ BZero := by simp [Dprin, BZero]
        simpa [oix_twr] using lessBT_addBT_self t2 (Dprin (e : ℕ∞) X) ne
      have hVadd : oix_twr t2 e t2 (k + 1) = addBT t2 (Dprin (e : ℕ∞) X) := rfl
      rw [hVadd, GBT_addBT_ocv] at hy
      simp only [Set.mem_union] at hy
      rcases hy with hyt | hyd
      · have hxt := oix_G_prefix_lt_ocv (cp := BP.db (v1 : ℕ∞) BZero) hostGP hyt
        exact lessBT_linear_trans _ _ _ hxt t2lt
      · obtain ⟨_hue, hcase⟩ := mem_GBT_Dprin_ocv hyd
        rcases hcase with hyX | hyGX
        · subst hyX; exact grow
        · exact lessBT_linear_trans _ _ _ (ih y hyGX) grow

/-- Isabelle `oix_condV_newOT_gen` (pss_wip.thy:112309)。rebased head `u ≤ e` での
newOT（body OT は index `e` の `oix_condV_adm_newOT` から、guard は index `u` で）。 -/
private theorem oix_condV_newOT_gen_ocv {t2 : BT} {u e v1 : ℕ}
    (hostGP : isOT_BP (BP.db (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true)
    (ue : u ≤ e) (ev : e < v1) (t2ne : t2 ≠ BZero) (k : ℕ) :
    isOT_BP (BP.db (u : ℕ∞) (oix_twr t2 e t2 k)) = true := by
  have hue : (u : ℕ∞) ≤ (e : ℕ∞) := by exact_mod_cast ue
  have hostGPe : isOT_BP (BP.db (e : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true :=
    oix_isOT_BP_head_antitone_ocv hostGP hue
  have inner : isOT_BP (BP.db (e : ℕ∞) (oix_twr t2 e t2 k)) = true :=
    oix_condV_adm_newOT_ocv hostGPe ev t2ne k
  have isot : isOT_BT (oix_twr t2 e t2 k) = true := by
    simp only [isOT_BP, Bool.and_eq_true] at inner; exact inner.1
  have guard : ∀ x ∈ GBT (u : ℕ∞) (oix_twr t2 e t2 k),
      lessBT x (oix_twr t2 e t2 k) = true := oix_condV_G_guard_at_ocv hostGP k
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
  refine ⟨isot, ?_⟩
  intro x hx
  exact guard x (by simpa [GBT, List.contains_iff_mem] using hx)

/-! ## 11. `u ≤ e`（Isabelle `viB_suffix_max`；exchV-props の private 版の複製） -/

private theorem entry1_step_ocv (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
    (hj₀ : j₀ < Lng M) (hge : Adm M j₀ ≤ j) (hlt : j < j₀) :
    entry M 1 j < entry M 1 (j + 1) := by
  have hnaS : adm M (j + 1) = false := by
    by_contra hcon
    have hadm : adm M (j + 1) = true := by simpa using hcon
    rcases Nat.lt_or_ge (j + 1) j₀ with h | h
    · have := Adm_max M (j + 1) j₀ hadm (by omega)
      omega
    · have hEq : j + 1 = j₀ := by omega
      rw [hEq] at hadm
      rw [hadm] at hna
      exact absurd hna (by simp)
  have hnadm : nadm M (j + 1) = true := by simpa [adm] using hnaS
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadm
  have hlen : ¬ (Lng M < j + 1) := by omega
  rcases hnadm with h | h
  · exact absurd h hlen
  · have hn1 : nextrel1 M j (j + 1) = true := by simpa [nextR] using h.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact hn1.1.1.2

private theorem entry1_Adm_le_ocv (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
    entry M 1 (Adm M j₀) ≤ entry M 1 j₀ := by
  by_cases hadm : adm M j₀ = true
  · simp [Adm, hadm]
  · have hna : adm M j₀ = false := by simpa using hadm
    have hmono : ∀ d a, d = j₀ - a → Adm M j₀ ≤ a → a ≤ j₀ →
        entry M 1 a ≤ entry M 1 j₀ := by
      intro d
      induction d with
      | zero => intro a hd _ hle; have : a = j₀ := by omega
                rw [this]
      | succ d ih =>
          intro a hd hge hle
          have hlt : a < j₀ := by omega
          have hstep := entry1_step_ocv M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-! ## 12. `e5x_body` の塔畳み込み（Isabelle `oix_bodyM_twr`/`oix_bodyO_twr`） -/

private theorem oix_bodyM_twr_ocv (t2 : BT) (e j : ℕ) :
    e5x_bodyM t2 e (j + 1) = oix_twr t2 e t2 (j + 1 + 1) := by
  show addBT t2 (s85b_W e t2 t2 (j + 1)) = oix_twr t2 e t2 (j + 1 + 1)
  rw [s85b_W_eq_Dprin_twr_ocv]
  rfl

private theorem oix_bodyO_twr_ocv (t2 : BT) (e n : ℕ) :
    e5x_bodyO t2 e n = oix_twr t2 e BZero (n + 1) := by
  show addBT t2 (s85b_W e t2 BZero n) = oix_twr t2 e BZero (n + 1)
  rw [s85b_W_eq_Dprin_twr_ocv]
  rfl

/-! ## 13. 条件(V)-nadm leg（Isabelle `oix_OTint_condV_nadm`） -/

/-- **`OTint_hp_condV_nadm` の discharge**（house pattern）。
非 adm 枝の値形 `ExchV_nf3x` をそのまま仮定に取る（`nf3x_holds` により
`ExchVres_nadm_M_tower` 上で得られ、並行 agent の `ExchV_M_tower` が供給）。
塔は rebased head `u = M₁,j₋₁ ≤ e` の下で運ぶ。 -/
theorem OTint_hp_condV_nadm_holds (hnf : ExchV_nf3x) : OTint_hp_condV_nadm := by
  intro N m hST hmono _j1gt hcond hnadm _hhp hOT hm
  have hR : RTPS N := STPS_RTPS N hST
  have hM : TPS N := STPS_TPS N hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds N hR hM hmono hcond
  obtain ⟨hVraw, _hc1eq, ht2TBr, _hjm1lt⟩ := c1_shape_holds N hR hM hmono hj₁ ht₁
  have ht2ner : transT2 N ≠ BZero := t2_nonzero_condV_holds N hR hM hmono hcond
  have hev0 : entry N 1 (transJ0 N) < entry N 1 (transJ1 N) := condV_ev_ocv hcond
  have hj0lt : transJ0 N < Lng N := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨_, h3⟩ := h
    show transJ0 N < Lng N
    simp only [transJ0, lastParent, lastIdx] at h3 ⊢
    omega
  have hue_raw : entry N 1 (transJm1 N) ≤ entry N 1 (transJ0 N) :=
    entry1_Adm_le_ocv N (transJ0 N) hj0lt
  obtain ⟨s1, b1, hd1, hk1⟩ := fseq_condV_holds N hR hM hmono hj₁ ht₁ hcond
  have hnadm' : adm N (parent N 0 (Lng N - 1)) = false := hnadm
  obtain ⟨hMtower, hOtower⟩ := hnf N s1 b1 hST hmono hcond hnadm' hd1 hk1
  set e := entry N 1 (transJ0 N) with he_def
  set u := entry N 1 (transJm1 N) with hu_def
  set v1 := entry N 1 (transJ1 N) with hv1_def
  set t2 := transT2 N with ht2_def
  have ht2TB : t2 ∈ T_B := ht2TBr
  have ht2ne : t2 ≠ BZero := ht2ner
  have hev : e < v1 := hev0
  have ue : u ≤ e := hue_raw
  have hDv1TB : Dprin (v1 : ℕ∞) BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) BZero_mem_T_B_ocv
  have hVu : transV N = (u : ℕ∞) := hVraw
  have hc2eq : transC2 N = Dprin (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero)) := by
    rw [transC2_condV_ocv N hcond, hVu, ← ht2_def, ← hv1_def]
  have hc2dec : scb_decomp (Trans N) s1 (flatBT (transC2 N)) b1 := hk1.1
  have hb1 : ∀ x ∈ b1, x = Sym.rp := hc2dec.2.2
  have hc2TB : transC2 N ∈ T_B := by
    rw [hc2eq]; exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht2TB hDv1TB)
  have hc2OT : transC2 N ∈ OT := OT_scb_recursive (Trans N) (transC2 N) s1 b1 hOT hc2TB hc2dec
  have hostGP : isOT_BP (BP.db (u : ℕ∞) (addBT t2 (Dprin (v1 : ℕ∞) BZero))) = true := by
    have hh : isOT_BT (transC2 N) = true := hc2OT
    rw [hc2eq] at hh
    simpa [Dprin, isOT_BT, isOT_BPList, descP] using hh
  have hOTne : Trans N ≠ BZero := by
    intro h0
    have hmem : Sym.dsym (u : ℕ∞) ∈ flatBT (Trans N) := by
      rw [hc2dec.1, hc2eq, flatBT_Dprin_ocv]; simp
    rw [h0] at hmem
    simp [flatBT, BZero] at hmem
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 + 1 := ⟨m - 2, by omega⟩
  have hMtw : e5x_bodyM t2 e (j + 1) = oix_twr t2 e t2 (j + 1 + 1) :=
    oix_bodyM_twr_ocv t2 e j
  have hOL : e5x_bodyO t2 e (j + 1) = oix_twr t2 e BZero (j + 1 + 1) :=
    oix_bodyO_twr_ocv t2 e (j + 1)
  have hOH : e5x_bodyO t2 e (j + 1 + 1) = oix_twr t2 e BZero (j + 1 + 1 + 1) :=
    oix_bodyO_twr_ocv t2 e (j + 1 + 1)
  have hourflat : flatBT (Trans (oper N (j + 1 + 1)))
      = s1 ++ flatBT (Dprin (u : ℕ∞) (oix_twr t2 e t2 (j + 1 + 1))) ++ b1 := by
    have h := hMtower (j + 1); rw [hMtw] at h; exact h
  have hloflat : flatBT (operB (Trans N) (numBT (j + 1)))
      = s1 ++ flatBT (Dprin (u : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1))) ++ b1 := by
    have h := hOtower (j + 1) (by omega); rw [hOL] at h; exact h
  have hhiflat : flatBT (operB (Trans N) (numBT (j + 1 + 1)))
      = s1 ++ flatBT (Dprin (u : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1 + 1))) ++ b1 := by
    have h := hOtower (j + 1 + 1) (by omega); rw [hOH] at h; exact h
  have ourdec : scb_decomp (Trans (oper N (j + 1 + 1))) s1
      (flatBT (Dprin (u : ℕ∞) (oix_twr t2 e t2 (j + 1 + 1)))) b1 :=
    ⟨hourflat, fun _ => isPTB_str_Dpt_ocv u (oix_twr_TB_ocv ht2TB ht2TB (j + 1 + 1)), hb1⟩
  have lodec : scb_decomp (operB (Trans N) (numBT (j + 1))) s1
      (flatBT (Dprin (u : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1)))) b1 :=
    ⟨hloflat, fun _ => isPTB_str_Dpt_ocv u (oix_twr_TB_ocv ht2TB BZero_mem_T_B_ocv (j + 1 + 1)), hb1⟩
  have hidec : scb_decomp (operB (Trans N) (numBT (j + 1 + 1))) s1
      (flatBT (Dprin (u : ℕ∞) (oix_twr t2 e BZero (j + 1 + 1 + 1)))) b1 :=
    ⟨hhiflat, fun _ => isPTB_str_Dpt_ocv u (oix_twr_TB_ocv ht2TB BZero_mem_T_B_ocv (j + 1 + 1 + 1)), hb1⟩
  have loOT : isOT_BT (operB (Trans N) (numBT (j + 1))) = true :=
    (buchholz_fseq_closed (Trans N) (j + 1) hOT hOTne).1
  have hiOT : isOT_BT (operB (Trans N) (numBT (j + 1 + 1))) = true :=
    (buchholz_fseq_closed (Trans N) (j + 1 + 1) hOT hOTne).1
  have newOT : isOT_BP (BP.db (u : ℕ∞) (oix_twr t2 e t2 (j + 1 + 1))) = true :=
    oix_condV_newOT_gen_ocv hostGP ue hev ht2ne (j + 1 + 1)
  have ordlo := oix_twr_ord_lo0_ocv t2 e (j + 1 + 1)
  have ordhi := oix_twr_ord_hi0_ocv t2 e (j + 1 + 1)
  have setle : ∀ uu : ℕ∞, b1x_setle (GBT uu (oix_twr t2 e t2 (j + 1 + 1)))
      (insert (oix_twr t2 e BZero (j + 1 + 1)) (GBT uu (oix_twr t2 e BZero (j + 1 + 1)))) :=
    fun uu => oix_condV_adm_setle0_ocv t2 e uu (j + 1)
  have isot : isOT_BT (Trans (oper N (j + 1 + 1))) = true :=
    oix_transportD oix_transport_uncond lodec ourdec hidec loOT hiOT newOT ordlo ordhi setle
  have hmST : STPS (oper N (j + 1 + 1)) := STPS.oper hST (j + 1 + 1) (by omega)
  have hmTB : Trans (oper N (j + 1 + 1)) ∈ T_B :=
    Trans_mem_T_B (oper N (j + 1 + 1)) (STPS_RTPS _ hmST)
  exact ⟨isot, hmTB⟩

#print axioms OTint_hp_condV_nadm_holds

end PSS
