import «8».«8.7-otint-transport-prims»
import «Buchholz-1986».«Buchholz-1986-2.1-order»

/-!
# PSS.«8».«8.7-otint-transport» — OT transport pillar: `oix_transport` and its discharge

`OTdisp_OTint`（§8.7 の最重量 leaf、`8.7-Trans-preserves-OT`:95）は III/IV/V の内部枝で
純 `BT` の **sandwich-transport** 残差 `oix_transport` に還元される
（`8.7-otdisp-OTint` は no-parent 隅を discharge 済み、残差は III/IV/V の hasParent 枝）。
本ファイルはその `oix_transport` インターフェースを定義し、Isabelle の discharge 連鎖
(`otx2_`/`otx3_`, r52/r53) を bottom-up に移植する。

## 移植元 (isabelle/layerB/pss_wip.thy)

- `oix_transport` (definition, wip:111571) / `oix_transportD` (wip:111583) — 純 `BT`
  の右端 spine core 置換が `isOT` を保つ residual。
- discharge: `otx3_transport` (theorem, wip:116928)、
  bricks `otx2_lessBT_snocsnoc`/`otx2_leBT_snocsnoc`/`otx2_descP_prefix`/
  `otx2_GBT_snoc`/`otx2_GBP_inf` (wip:113860–113980)、
  assembly `otx3_setle_triG`/`otx3_pOT`/`otx3_triG_lift`/`otx3_level`/`otx3_core`
  (wip:116700–116928)。

## 依存（ビルド済みのみ import）

- `8.7-otint-transport-prims`: `b1x_setle`(+subset/widen/union)、`b1x_triG`(+I/D)、`d4vx_*`。
- `Buchholz-1986-2.1-order`: `lessBT_linear_irrefl`/`_trans`/`_trichotomy`。
- 透過的に `PSS.*`（`flatBT`/`scb_decomp`/`GBT`/`GBP`/`leBT`/`lessBT`/`isOT_BT`/`isOT_BP`/
  `descP`/`Dprin`/`gatherBT`/`gatherBPList`/`btWeight`）と `PSS.Flat`（`flatBP_cancel`/
  `flatBT_injective`）。

## 状態

🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。私的接尾辞 `_oix`。

無条件で移植した部分:
- インターフェース `oix_transport` / `oix_transportD`。
- 純 `BT` 順序 brick 群（`otx2_lessBT_snocsnoc` / `otx2_leBT_snocsnoc` /
  `otx2_descP_prefix` / `descP_last_le` / `otx2_GBT_snoc` / `otx2_GBP_inf`）。
- setle→triG（`otx3_setle_triG`）、per-level guard（`otx3_pOT`）、`◁` level lift
  （`otx3_triG_lift`）、1 レベル組み立て（`otx3_level`）、文脈再帰（`otx3_core`）。
- `m_8_7_isOT_BT_snoc_leBT` は `isOT_BPList`/`descP` の snoc 補題で無条件に再証明。

**`oix_transport_holds : oix_transport`** は GREEN-MODULO、次の 4 本の generic Buchholz
residual に依存する（いずれも Isabelle 側で証明済み・満足可能）:
- `OixGControl`   ＝ [Buc1] Lemma 3.4（Isa `b1x_G_control` wip:50342;
  Lean private twin `G_control_bc` @ `Buchholz-1986-3.3`:254、`b1x_triG` は
  `triGBC` と defeq）。
- `OixSandwichPrefix` ＝ Isa `b1x_sandwich_prefix` (wip:50424;
  private twin `sandwich_prefix_bc`:334)。
- `OixSandwichDpt`    ＝ Isa `b1x_sandwich_Dpt` (wip:50455;
  private twin `sandwich_Dprin_bc`:379)。
- `OixAlign3`     ＝ Isa `otx2_align3` (wip:114296; Lean twin 未移植、flatinj toolkit
  `otx2_top_shape`/`otx2_peel` を要する)。
次 wave はこの 4 本を（private twin の public 昇格 or 移植で）discharge すれば
`oix_transport` が無条件化する。
-/

namespace PSS

/-! ## 1. インターフェース: `oix_transport` / `oix_transportD` -/

/-- Isabelle `oix_transport` (layerB/pss_wip.thy:111571)。
共有された右端 spine の穴 `(s, b)`（`b` 全 `RP`）で、同じ head `D_h` を持つ 3 つの core
`aLo ≤ a' ≤ aHi` を差し替える。両端 `tLo`, `tHi` が `OT` で、差し替え core `a'` 自身が
`OT` principal（`isOT_BP (D_h a')`）かつ その `G_u` 集合が LOW donor core に支配される
（`setle`）ならば、中間項 `t'` も `OT`。 -/
def oix_transport : Prop :=
  ∀ (tLo t' tHi : BT) (s b : List Sym) (h : ℕ) (aLo a' aHi : BT),
    scb_decomp tLo s (flatBT (Dprin (h : ℕ∞) aLo)) b →
    scb_decomp t' s (flatBT (Dprin (h : ℕ∞) a')) b →
    scb_decomp tHi s (flatBT (Dprin (h : ℕ∞) aHi)) b →
    isOT_BT tLo = true → isOT_BT tHi = true →
    isOT_BP (BP.db (h : ℕ∞) a') = true →
    leBT aLo a' = true → leBT a' aHi = true →
    (∀ u : ℕ∞, b1x_setle (GBT u a') (insert aLo (GBT u aLo))) →
    isOT_BT t' = true

/-- Isabelle `oix_transportD` (layerB/pss_wip.thy:111583)。 -/
theorem oix_transportD (htr : oix_transport)
    {tLo t' tHi : BT} {s b : List Sym} {h : ℕ} {aLo a' aHi : BT}
    (d1 : scb_decomp tLo s (flatBT (Dprin (h : ℕ∞) aLo)) b)
    (d2 : scb_decomp t' s (flatBT (Dprin (h : ℕ∞) a')) b)
    (d3 : scb_decomp tHi s (flatBT (Dprin (h : ℕ∞) aHi)) b)
    (loOT : isOT_BT tLo = true) (hiOT : isOT_BT tHi = true)
    (newOT : isOT_BP (BP.db (h : ℕ∞) a') = true)
    (o1 : leBT aLo a' = true) (o2 : leBT a' aHi = true)
    (setle : ∀ u : ℕ∞, b1x_setle (GBT u a') (insert aLo (GBT u aLo))) :
    isOT_BT t' = true :=
  htr tLo t' tHi s b h aLo a' aHi d1 d2 d3 loOT hiOT newOT o1 o2 setle

/-! ## 2. 純 `BT` の順序 brick 群（`otx2_`） -/

/-- `lessBP p p = false`（局所）。 -/
private theorem lessBP_irrefl_oix (p : BP) : lessBP p p = false := by
  cases p with
  | db u b => simp [lessBP, lessBT_linear_irrefl]

/-- Isabelle `otx2_lessBT_snocsnoc` (wip:113869)。共有 prefix `qs` の後に 1 成分を
snoc したとき、項の順序は snoc された principal の順序で決まる。 -/
private theorem lessBT_snocsnoc_oix (qs : List BP) (p q : BP) :
    lessBT (BT.trm (qs ++ [p])) (BT.trm (qs ++ [q])) = lessBP p q := by
  induction qs with
  | nil => simp [lessBT, lessBPList]
  | cons a qs' ih =>
    have h1 : lessBP a a = false := lessBP_irrefl_oix a
    have h2 : (a == a) = true := by simp
    simp only [List.cons_append, lessBT, lessBPList, h1, h2, Bool.false_or,
      Bool.true_and]
    simpa [lessBT] using ih

/-- Isabelle `otx2_leBT_snocsnoc` (wip:113885)。広義順序版。 -/
private theorem leBT_snocsnoc_oix {x y : BT} (w : ℕ∞) (qs : List BP)
    (h : leBT x y = true) :
    leBT (BT.trm (qs ++ [BP.db w x])) (BT.trm (qs ++ [BP.db w y])) = true := by
  by_cases hxy : x = y
  · subst hxy; simp [leBT]
  · have hne_beq : (x == y) = false := by
      simp only [beq_eq_false_iff_ne]; exact hxy
    have hlt : lessBT x y = true := by
      have he : leBT x y = lessBT x y := by simp [leBT, hne_beq]
      rw [he] at h; exact h
    have hlp : lessBP (BP.db w x) (BP.db w y) = true := by
      simp [lessBP, hlt]
    have hlt2 : lessBT (BT.trm (qs ++ [BP.db w x])) (BT.trm (qs ++ [BP.db w y]))
        = true := by rw [lessBT_snocsnoc_oix]; exact hlp
    simp [leBT, hlt2]

/-- Isabelle `otx2_descP_prefix` (wip:113940)。`descP` の prefix 遺伝。 -/
private theorem descP_prefix_oix : ∀ (xs ys : List BP),
    descP (xs ++ ys) = true → descP xs = true
  | [], _, _ => by simp [descP]
  | [_], _, _ => by simp [descP]
  | p :: q :: ps, ys, h => by
    have hsplit : leBT (BT.trm [q]) (BT.trm [p]) = true ∧
        descP ((q :: ps) ++ ys) = true := by
      simpa [descP, List.cons_append] using h
    have hIH := descP_prefix_oix (q :: ps) ys hsplit.2
    simp [descP, hsplit.1, hIH]

/-- snoc された末尾成分は直前成分以下（`descP` の隣接条件）。
Isabelle の `descP_last_le`（HIGH donor から幹末尾を読む）の本ファイル用形。 -/
private theorem descP_snoc_last_le_oix : ∀ (qs : List BP) (c : BP) (hne : qs ≠ []),
    descP (qs ++ [c]) = true →
    leBT (BT.trm [c]) (BT.trm [qs.getLast hne]) = true
  | [], _, hne, _ => absurd rfl hne
  | [d], c, _, h => by
    have : leBT (BT.trm [c]) (BT.trm [d]) = true := by
      simpa [descP] using h
    simpa using this
  | d :: e :: es, c, _, h => by
    have hne' : (e :: es) ≠ [] := by simp
    have hsplit : leBT (BT.trm [e]) (BT.trm [d]) = true ∧
        descP ((e :: es) ++ [c]) = true := by
      simpa [descP, List.cons_append] using h
    have hIH := descP_snoc_last_le_oix (e :: es) c hne' hsplit.2
    have hlast : (d :: e :: es).getLast (by simp) = (e :: es).getLast hne' := by
      simp [List.getLast_cons]
    rw [hlast]; exact hIH

/-- `gatherBPList` の append 準同型（局所）。 -/
private theorem gatherBPList_append_oix (u : ℕ∞) (xs ys : List BP) :
    gatherBPList u (xs ++ ys) = gatherBPList u xs ++ gatherBPList u ys := by
  induction xs with
  | nil => simp [gatherBPList]
  | cons a as ih => simp [gatherBPList, ih, List.append_assoc]

/-- Isabelle `otx2_GBT_snoc` (wip:113974)。`G_u` の snoc 分解（prefix 部と末尾 principal）。 -/
private theorem GBT_snoc_oix (u : ℕ∞) (qs : List BP) (p : BP) :
    GBT u (BT.trm (qs ++ [p])) = GBT u (BT.trm qs) ∪ GBP u p := by
  ext x
  simp only [GBT, GBP, gatherBT, gatherBPList_append_oix, gatherBPList,
    List.append_nil, List.contains_append, Set.mem_setOf_eq, Set.mem_union,
    Bool.or_eq_true]

/-- Isabelle `otx2_GBP_inf` (wip:113979) の `GBT` 版: head `∞` の principal の `G_u`。 -/
private theorem GBT_Dprin_inf_oix (u : ℕ∞) (x : BT) :
    GBT u (Dprin (⊤ : ℕ∞) x) = insert x (GBT u x) := by
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, le_top,
    decide_true, if_true, List.append_nil, List.contains_cons, Set.mem_setOf_eq,
    Set.mem_insert_iff, Bool.or_eq_true, beq_iff_eq]

/-! ## 3. `setle ⟹ ◁`: 変換の `setle` 前提は `D_∞(aLo)`-統制と一致 -/

/-- Isabelle `otx3_setle_triG` (wip:116705)。`setle` 前提は G-統制
`a' ◁_{D_∞(aLo)} aHi` に（中間 `c` 抜きで）等価。 -/
private theorem setle_triG_oix {aLo a' aHi : BT}
    (setle : ∀ u : ℕ∞, b1x_setle (GBT u a') (insert aLo (GBT u aLo))) :
    b1x_triG (Dprin (⊤ : ℕ∞) aLo) a' aHi := by
  apply b1x_triG_I
  intro u c _ _
  have hbase : b1x_setle (GBT u a') (GBT u (Dprin (⊤ : ℕ∞) aLo)) := by
    rw [GBT_Dprin_inf_oix]; exact setle u
  refine b1x_setle_widen hbase ?_
  intro z hz
  exact Or.inl (Or.inr hz)

/-! ## 4. 順序・`G` 補助 -/

/-- `leBT` の unfold: 広義順序は狭義順序または相等。 -/
private theorem leBT_iff_oix (a b : BT) :
    leBT a b = true ↔ (lessBT a b = true ∨ a = b) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq]

private theorem leBT_refl_oix (x : BT) : leBT x x = true := by simp [leBT]

/-- `leBT` の推移律。 -/
private theorem leBT_trans_oix {a b c : BT}
    (h1 : leBT a b = true) (h2 : leBT b c = true) : leBT a c = true := by
  rw [leBT_iff_oix] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (lessBT_linear_trans a b c h1 h2)
  · subst h2; exact Or.inl h1
  · subst h1; exact Or.inl h2
  · subst h1; subst h2; exact Or.inr rfl

/-- Isabelle `b1x_less_le_trans` (wip:50033)。 -/
private theorem less_le_trans_oix {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_oix] at hbc
  rcases hbc with h | h
  · exact lessBT_linear_trans a b c hab h
  · subst h; exact hab

/-- OT principal `D_w b` からその `G_w` 集合が `b` で strict 下界される。 -/
private theorem GBT_lessBT_of_isOT_BP {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : ∀ x ∈ GBT w b, lessBT x b = true := by
  intro x hx
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

/-- `u ≤ w` のとき `G_u (D_w x) = {x} ∪ G_u x`。 -/
private theorem GBP_db_le_oix {u w : ℕ∞} (x : BT) (h : u ≤ w) :
    GBP u (BP.db w x) = insert x (GBT u x) := by
  have hd : decide (u ≤ w) = true := decide_eq_true h
  ext y
  simp only [GBP, GBT, gatherBP, hd, if_true, Set.mem_setOf_eq,
    List.contains_iff_mem, List.mem_cons, Set.mem_insert_iff]

/-- `¬ u ≤ w` のとき `G_u (D_w x) = ∅`。 -/
private theorem GBP_db_not_le_oix {u w : ℕ∞} (x : BT) (h : ¬ u ≤ w) :
    GBP u (BP.db w x) = ∅ := by
  have hd : decide (u ≤ w) = false := decide_eq_false h
  ext y
  simp only [GBP, gatherBP, hd, if_false, Set.mem_setOf_eq,
    List.contains_nil, Set.mem_empty_iff_false, Bool.false_eq_true]

/-- 成分 `p ∈ ps` の `G_u p` は項全体の `G_u` に含まれる。 -/
private theorem GBP_subset_GBT_mem_oix {u : ℕ∞} {p : BP} :
    ∀ (ps : List BP), p ∈ ps → GBP u p ⊆ GBT u (BT.trm ps)
  | q :: qs, hmem => by
    intro x hx
    simp only [List.mem_cons] at hmem
    simp only [GBT, GBP, gatherBT, gatherBPList, Set.mem_setOf_eq,
      List.contains_append, Bool.or_eq_true] at hx ⊢
    rcases hmem with hmem | hmem
    · subst hmem; exact Or.inl hx
    · have hsub := GBP_subset_GBT_mem_oix (u := u) (p := p) qs hmem
      have hx2 : x ∈ GBT u (BT.trm qs) := hsub hx
      simp only [GBT, gatherBT, Set.mem_setOf_eq] at hx2
      exact Or.inr hx2

/-! ## 5. 残差 `Prop`（generic Buchholz machinery; `Buchholz-1986-3.3` の
private twin `G_control_bc`/`sandwich_prefix_bc`/`sandwich_Dprin_bc`、および
`otx2_align3`/`m_8_7_isOT_BT_snoc_leBT`。いずれも Isabelle 側で証明済み） -/

/-- Isabelle `b1x_G_control`（[Buc1] Lemma 3.4, wip:50342）。 -/
def OixGControl : Prop :=
  ∀ (z b a : BT) (u : ℕ∞), b1x_triG z b a → leBT b a = true →
    (∀ x ∈ GBT u a, lessBT x a = true) →
    (∀ x ∈ GBT u z, lessBT x b = true) →
    (∀ x ∈ GBT u b, lessBT x b = true)

/-- Isabelle `b1x_sandwich_prefix` (wip:50424)。 -/
def OixSandwichPrefix : Prop :=
  ∀ (ps xs ys : List BP) (c : BT),
    leBT (BT.trm (ps ++ xs)) c = true → leBT c (BT.trm (ps ++ ys)) = true →
    ∃ cs, c = BT.trm (ps ++ cs) ∧
      leBT (BT.trm xs) (BT.trm cs) = true ∧ leBT (BT.trm cs) (BT.trm ys) = true

/-- Isabelle `b1x_sandwich_Dpt` (wip:50455)。 -/
def OixSandwichDpt : Prop :=
  ∀ {v : ℕ∞} {x y c : BT},
    leBT (Dprin v x) c = true → leBT c (Dprin v y) = true →
    ∃ c₀ cs, c = BT.trm (BP.db v c₀ :: cs) ∧
      leBT x c₀ = true ∧ leBT c₀ y = true

/-- Isabelle `otx2_align3` (wip:114296)。 -/
def OixAlign3 : Prop :=
  ∀ (t1 t2 t3 : BT) (s b : List Sym) (cp1 cp2 cp3 : BP),
    flatBT t1 = s ++ flatBP cp1 ++ b →
    flatBT t2 = s ++ flatBP cp2 ++ b →
    flatBT t3 = s ++ flatBP cp3 ++ b →
    (∀ x ∈ b, x = Sym.rp) →
    (∃ qs, t1 = BT.trm (qs ++ [cp1]) ∧ t2 = BT.trm (qs ++ [cp2]) ∧
        t3 = BT.trm (qs ++ [cp3])) ∨
    (∃ qs w lb1 lb2 lb3 sc bc,
        t1 = BT.trm (qs ++ [BP.db w lb1]) ∧ t2 = BT.trm (qs ++ [BP.db w lb2]) ∧
        t3 = BT.trm (qs ++ [BP.db w lb3]) ∧
        flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧
        flatBT lb2 = sc ++ flatBP cp2 ++ bc ∧
        flatBT lb3 = sc ++ flatBP cp3 ++ bc ∧ (∀ x ∈ bc, x = Sym.rp))

/-! ## 6. per-level principal guard: `otx3_pOT` -/

/-- Isabelle `otx3_pOT` (wip:116723)。同 head の 2 OT principal に挟まれ、かつ LOW body
に対し `◁`-統制された OT body は、それ自身が head `w` の OT principal。 -/
private theorem pOT_oix (hGC : OixGControl)
    {w : ℕ∞} {xLo x' xHi : BT}
    (loP : isOT_BP (BP.db w xLo) = true) (hiP : isOT_BP (BP.db w xHi) = true)
    (xOT : isOT_BT x' = true)
    (o1 : leBT xLo x' = true) (o2 : leBT x' xHi = true)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    isOT_BP (BP.db w x') = true := by
  by_cases hx' : x' = xLo
  · subst hx'; exact loP
  · have lo_lt : lessBT xLo x' = true := by
      rw [leBT_iff_oix] at o1
      rcases o1 with h | h
      · exact h
      · exact absurd h.symm hx'
    have GLo : ∀ y ∈ GBT w xLo, lessBT y xLo = true := GBT_lessBT_of_isOT_BP loP
    have Ga : ∀ x ∈ GBT w xHi, lessBT x xHi = true := GBT_lessBT_of_isOT_BP hiP
    have Gz : ∀ x ∈ GBT w (Dprin (⊤ : ℕ∞) xLo), lessBT x x' = true := by
      intro x hx
      rw [GBT_Dprin_inf_oix, Set.mem_insert_iff] at hx
      rcases hx with hx | hx
      · subst hx; exact lo_lt
      · exact less_le_trans_oix (GLo x hx) o1
    have G : ∀ x ∈ GBT w x', lessBT x x' = true :=
      hGC (Dprin (⊤ : ℕ∞) xLo) x' xHi w tri o2 Ga Gz
    simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
    refine ⟨xOT, ?_⟩
    intro x hx
    exact G x (by simpa [GBT, List.contains_iff_mem] using hx)

/-! ## 7. `◁` level lift: `otx3_triG_lift` -/

/-- Isabelle `otx3_triG_lift` (wip:116762)。body の `◁`-統制を項レベルへ持ち上げる
（`z` を low body から low term へ弱める）。 -/
private theorem triG_lift_oix (hSP : OixSandwichPrefix) (hSD : OixSandwichDpt)
    {w : ℕ∞} {xLo x' xHi : BT} (qs : List BP)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    b1x_triG (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo])))
      (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) := by
  apply b1x_triG_I
  intro u c l1 l2
  -- sandwich prefix: c 共有 prefix qs の後の尾 cs
  obtain ⟨cs, ceq, s1, s2⟩ := hSP qs [BP.db w x'] [BP.db w xHi] c l1 l2
  -- sandwich Dpt: cs は head D_w の principal で始まる
  obtain ⟨c0, c1, cseq, xc0, c0hi⟩ :=
    hSD (v := w) (x := x') (y := xHi) (c := BT.trm cs)
      (show leBT (Dprin w x') (BT.trm cs) = true from s1)
      (show leBT (BT.trm cs) (Dprin w xHi) = true from s2)
  have cse : cs = BP.db w c0 :: c1 := by injection cseq
  have snocLo : GBT u (BT.trm (qs ++ [BP.db w xLo]))
      = GBT u (BT.trm qs) ∪ GBP u (BP.db w xLo) := GBT_snoc_oix u qs (BP.db w xLo)
  have snocX : GBT u (BT.trm (qs ++ [BP.db w x']))
      = GBT u (BT.trm qs) ∪ GBP u (BP.db w x') := GBT_snoc_oix u qs (BP.db w x')
  have tLoZ : GBT u (BT.trm (qs ++ [BP.db w xLo]))
      ⊆ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) := by
    rw [GBT_Dprin_inf_oix]; exact Set.subset_insert _ _
  -- part1: prefix 成分は LOW donor 経由で Z に入る
  have part1 : b1x_setle (GBT u (BT.trm qs))
      (GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero}) := by
    apply b1x_setle_subset
    intro z hz
    have h1 : z ∈ GBT u (BT.trm (qs ++ [BP.db w xLo])) := by
      rw [snocLo]; exact Or.inl hz
    exact Or.inl (Or.inr (tLoZ h1))
  -- part2: 新 principal x' の成分
  have part2 : b1x_setle (GBP u (BP.db w x'))
      (GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero}) := by
    by_cases hle : u ≤ w
    · -- u ≤ w
      have hmem : BP.db w c0 ∈ qs ++ cs := by
        rw [cse]; simp
      have hc0GBP : c0 ∈ GBP u (BP.db w c0) := by
        rw [GBP_db_le_oix c0 hle]; exact Set.mem_insert _ _
      have hGBPsub : GBP u (BP.db w c0) ⊆ GBT u c := by
        rw [ceq]; exact GBP_subset_GBT_mem_oix (u := u) (p := BP.db w c0) (qs ++ cs) hmem
      have c0in : c0 ∈ GBT u c := hGBPsub hc0GBP
      have Gc0sub : GBT u c0 ⊆ GBT u c := by
        have hins : GBT u c0 ⊆ GBP u (BP.db w c0) := by
          rw [GBP_db_le_oix c0 hle]; exact Set.subset_insert _ _
        exact hins.trans hGBPsub
      have hmemLo : BP.db w xLo ∈ qs ++ [BP.db w xLo] := by simp
      have sub2 : GBT u (Dprin (⊤ : ℕ∞) xLo)
          ⊆ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) := by
        have heq : GBT u (Dprin (⊤ : ℕ∞) xLo) = GBP u (BP.db w xLo) := by
          rw [GBT_Dprin_inf_oix, GBP_db_le_oix xLo hle]
        rw [heq]
        exact (GBP_subset_GBT_mem_oix (u := u) (p := BP.db w xLo)
          (qs ++ [BP.db w xLo]) hmemLo).trans tLoZ
      have deep : b1x_setle (GBT u x')
          (GBT u c0 ∪ GBT u (Dprin (⊤ : ℕ∞) xLo) ∪ {BZero}) :=
        b1x_triG_D (u := u) tri xc0 c0hi
      have hZsub : GBT u c0 ∪ GBT u (Dprin (⊤ : ℕ∞) xLo) ∪ {BZero}
          ⊆ GBT u c ∪ GBT u (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo]))) ∪ {BZero} := by
        intro z hz
        rcases hz with (hz | hz) | hz
        · exact Or.inl (Or.inl (Gc0sub hz))
        · exact Or.inl (Or.inr (sub2 hz))
        · exact Or.inr hz
      have deep' := b1x_setle_widen deep hZsub
      rw [GBP_db_le_oix x' hle]
      intro z hz
      rw [Set.mem_insert_iff] at hz
      rcases hz with hz | hz
      · subst hz
        exact ⟨c0, Or.inl (Or.inl c0in), xc0⟩
      · exact deep' z hz
    · -- ¬ u ≤ w: GBP 空
      rw [GBP_db_not_le_oix x' hle]
      intro z hz
      simp only [Set.mem_empty_iff_false] at hz
  rw [snocX]
  exact b1x_setle_union part1 part2

/-! ## 8. `isOT_BT` の snoc 補題（`m_8_7_isOT_BT_snoc_leBT` を無条件で証明） -/

/-- `isOT_BPList` の snoc 分解。 -/
private theorem isOT_BPList_snoc_oix (xs : List BP) (pn : BP) :
    isOT_BPList (xs ++ [pn]) = (isOT_BPList xs && isOT_BP pn) := by
  induction xs with
  | nil => simp [isOT_BPList]
  | cons p ps ih => simp [isOT_BPList, ih, Bool.and_assoc]

/-- `descP` の snoc: 末尾が直前以下なら降順を保つ（`descP_snoc_last_le_oix` の逆）。 -/
private theorem descP_snoc_oix : ∀ (xs : List BP) (pn : BP),
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
    have hIH := descP_snoc_oix (e :: es) pn hsplit.2 hle'
    have hrw : (d :: e :: es) ++ [pn] = d :: e :: (es ++ [pn]) := by simp
    rw [hrw]
    have hIH' : descP (e :: (es ++ [pn])) = true := by
      have hcast : e :: (es ++ [pn]) = (e :: es) ++ [pn] := by simp
      rw [hcast]; exact hIH
    show (leBT (BT.trm [e]) (BT.trm [d]) && descP (e :: (es ++ [pn]))) = true
    simp only [hsplit.1, hIH', Bool.and_self]

/-- Isabelle `m_8_7_isOT_BT_snoc_leBT` (wip:36604) を無条件で移植。 -/
private theorem isOT_snoc_leBT_oix (xs : List BP) (pn : BP)
    (hxs : isOT_BT (BT.trm xs) = true) (hpn : isOT_BP pn = true)
    (hle : ∀ (h : xs ≠ []), leBT (BT.trm [pn]) (BT.trm [xs.getLast h]) = true) :
    isOT_BT (BT.trm (xs ++ [pn])) = true := by
  have hsp : isOT_BPList xs = true ∧ descP xs = true := by
    simpa [isOT_BT, Bool.and_eq_true] using hxs
  simp only [isOT_BT, Bool.and_eq_true]
  refine ⟨?_, descP_snoc_oix xs pn hsp.2 hle⟩
  simp only [isOT_BPList_snoc_oix, hsp.1, hpn, Bool.and_self]

/-- OT principal の body は OT。 -/
private theorem isOT_BT_of_isOT_BP_oix {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : isOT_BT b = true := by
  simp only [isOT_BP, Bool.and_eq_true] at h; exact h.1

/-- snoc された末尾成分自身が OT principal。 -/
private theorem isOT_BP_last_of_snoc_oix {qs : List BP} {w : ℕ∞} {lb : BT}
    (h : isOT_BT (BT.trm (qs ++ [BP.db w lb])) = true) : isOT_BP (BP.db w lb) = true := by
  simp only [isOT_BT, isOT_BPList_snoc_oix, Bool.and_eq_true] at h
  exact h.1.2

/-! ## 9. 測度: `btWeight` の snoc 単調性 -/

private theorem bpListWeight_snoc_oix (qs : List BP) (p : BP) :
    bpListWeight (qs ++ [p]) = bpListWeight qs + bpWeight p + 1 := by
  induction qs with
  | nil => simp [bpListWeight]
  | cons q qs' ih => simp only [List.cons_append, bpListWeight, ih]; omega

private theorem btWeight_lt_snoc_oix (qs : List BP) (w : ℕ∞) (lb : BT) :
    btWeight lb < btWeight (BT.trm (qs ++ [BP.db w lb])) := by
  simp only [btWeight, bpListWeight_snoc_oix, bpWeight]
  omega

/-! ## 10. 1 レベル組み立て: `otx3_level` -/

/-- Isabelle `otx3_level` (wip:116796)。prefix 成分は LOW donor、descP-last は HIGH donor、
新 principal は仮定、順序・G-統制も同時に持ち上げる。 -/
private theorem level_oix (hSP : OixSandwichPrefix)
    (hSD : OixSandwichDpt) {w : ℕ∞} {xLo x' xHi : BT} (qs : List BP)
    (LoOT : isOT_BT (BT.trm (qs ++ [BP.db w xLo])) = true)
    (HiOT : isOT_BT (BT.trm (qs ++ [BP.db w xHi])) = true)
    (pOT : isOT_BP (BP.db w x') = true)
    (o1 : leBT xLo x' = true) (o2 : leBT x' xHi = true)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    isOT_BT (BT.trm (qs ++ [BP.db w x'])) = true ∧
    leBT (BT.trm (qs ++ [BP.db w xLo])) (BT.trm (qs ++ [BP.db w x'])) = true ∧
    leBT (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) = true ∧
    b1x_triG (Dprin (⊤ : ℕ∞) (BT.trm (qs ++ [BP.db w xLo])))
      (BT.trm (qs ++ [BP.db w x'])) (BT.trm (qs ++ [BP.db w xHi])) := by
  have descLo : descP (qs ++ [BP.db w xLo]) = true := by
    have := LoOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.2
  have qsBP : isOT_BPList qs = true := by
    have h1 : isOT_BPList (qs ++ [BP.db w xLo]) = true := by
      have := LoOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.1
    rw [isOT_BPList_snoc_oix, Bool.and_eq_true] at h1
    exact h1.1
  have qsD : descP qs = true := descP_prefix_oix qs [BP.db w xLo] descLo
  have qsOT : isOT_BT (BT.trm qs) = true := by
    simp only [isOT_BT, Bool.and_eq_true]; exact ⟨qsBP, qsD⟩
  have lelast : ∀ (hne : qs ≠ []),
      leBT (BT.trm [BP.db w x']) (BT.trm [qs.getLast hne]) = true := by
    intro hne
    have descHi : descP (qs ++ [BP.db w xHi]) = true := by
      have := HiOT; simp only [isOT_BT, Bool.and_eq_true] at this; exact this.2
    have hi_last : leBT (BT.trm [BP.db w xHi]) (BT.trm [qs.getLast hne]) = true :=
      descP_snoc_last_le_oix qs (BP.db w xHi) hne descHi
    have mid : leBT (BT.trm [BP.db w x']) (BT.trm [BP.db w xHi]) = true := by
      have := leBT_snocsnoc_oix (x := x') (y := xHi) w [] o2; simpa using this
    exact leBT_trans_oix mid hi_last
  have OT : isOT_BT (BT.trm (qs ++ [BP.db w x'])) = true :=
    isOT_snoc_leBT_oix qs (BP.db w x') qsOT pOT lelast
  have le1 := leBT_snocsnoc_oix (x := xLo) (y := x') w qs o1
  have le2 := leBT_snocsnoc_oix (x := x') (y := xHi) w qs o2
  have triL := triG_lift_oix hSP hSD (w := w) qs tri
  exact ⟨OT, le1, le2, triL⟩

/-! ## 11. 文脈再帰と変換定理: `otx3_core` / `oix_transport` -/

private theorem flatBT_Dprin_eq_flatBP (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = flatBP (BP.db v a) := rfl

/-- Isabelle `otx3_core` (wip:116861)。`size t'`（`btWeight`）強帰納で sandwich 順序と
G-統制を通して運ぶ。residual: `OixAlign3`/`OixGControl`/`OixSandwichPrefix`/
`OixSandwichDpt`。 -/
private theorem core_oix (hAlign : OixAlign3) (hGC : OixGControl)
    (hSP : OixSandwichPrefix) (hSD : OixSandwichDpt) :
    ∀ (n : ℕ) (t' tLo tHi : BT) (s b : List Sym) (h : ℕ) (aLo a' aHi : BT),
      btWeight t' = n →
      flatBT tLo = s ++ flatBP (BP.db (h : ℕ∞) aLo) ++ b →
      flatBT t' = s ++ flatBP (BP.db (h : ℕ∞) a') ++ b →
      flatBT tHi = s ++ flatBP (BP.db (h : ℕ∞) aHi) ++ b →
      (∀ x ∈ b, x = Sym.rp) →
      isOT_BT tLo = true → isOT_BT tHi = true →
      isOT_BP (BP.db (h : ℕ∞) a') = true →
      leBT aLo a' = true → leBT a' aHi = true →
      (∀ u : ℕ∞, b1x_setle (GBT u a') (insert aLo (GBT u aLo))) →
      isOT_BT t' = true ∧ leBT tLo t' = true ∧ leBT t' tHi = true ∧
        b1x_triG (Dprin (⊤ : ℕ∞) tLo) t' tHi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t' tLo tHi s b h aLo a' aHi hn F1 F2 F3 BR loOT hiOT newOT o1 o2 setle
    rcases hAlign tLo t' tHi s b (BP.db (h : ℕ∞) aLo) (BP.db (h : ℕ∞) a')
        (BP.db (h : ℕ∞) aHi) F1 F2 F3 BR with
      ⟨qs, hTLo, hT', hTHi⟩ |
      ⟨qs, w, lbLo, lb', lbHi, sc, bc, hTLo, hT', hTHi, F1', F2', F3', BC⟩
    · -- case A: 共有 qs 上の最終成分
      subst hTLo; subst hT'; subst hTHi
      have tri0 : b1x_triG (Dprin (⊤ : ℕ∞) aLo) a' aHi := setle_triG_oix setle
      exact level_oix hSP hSD qs loOT hiOT newOT o1 o2 tri0
    · -- case B: 共有最終成分の body へ降下
      subst hTLo; subst hT'; subst hTHi
      have loP : isOT_BP (BP.db w lbLo) = true := isOT_BP_last_of_snoc_oix loOT
      have hiP : isOT_BP (BP.db w lbHi) = true := isOT_BP_last_of_snoc_oix hiOT
      have loBT : isOT_BT lbLo = true := isOT_BT_of_isOT_BP_oix loP
      have hiBT : isOT_BT lbHi = true := isOT_BT_of_isOT_BP_oix hiP
      have sz : btWeight lb' < n := by
        rw [← hn]; exact btWeight_lt_snoc_oix qs w lb'
      obtain ⟨ih1, ih2, ih3, ih4⟩ :=
        ih (btWeight lb') sz lb' lbLo lbHi sc bc h aLo a' aHi rfl F1' F2' F3' BC
          loBT hiBT newOT o1 o2 setle
      have pOT : isOT_BP (BP.db w lb') = true := pOT_oix hGC loP hiP ih1 ih2 ih3 ih4
      exact level_oix hSP hSD qs loOT hiOT pOT ih2 ih3 ih4

/-- **`oix_transport` を discharge**（residual: `OixAlign3`/`OixGControl`/
`OixSandwichPrefix`/`OixSandwichDpt` — いずれも Isabelle 済、`Buchholz-1986-3.3`
の private twin `sandwich_*_bc`/`G_control_bc` と `otx2_align3` に対応）。 -/
theorem oix_transport_holds (hAlign : OixAlign3) (hGC : OixGControl)
    (hSP : OixSandwichPrefix) (hSD : OixSandwichDpt) : oix_transport := by
  intro tLo t' tHi s b h aLo a' aHi d1 d2 d3 loOT hiOT newOT o1 o2 setle
  have F1 : flatBT tLo = s ++ flatBP (BP.db (h : ℕ∞) aLo) ++ b := by
    have := d1.1; rwa [flatBT_Dprin_eq_flatBP] at this
  have F2 : flatBT t' = s ++ flatBP (BP.db (h : ℕ∞) a') ++ b := by
    have := d2.1; rwa [flatBT_Dprin_eq_flatBP] at this
  have F3 : flatBT tHi = s ++ flatBP (BP.db (h : ℕ∞) aHi) ++ b := by
    have := d3.1; rwa [flatBT_Dprin_eq_flatBP] at this
  have BR : ∀ x ∈ b, x = Sym.rp := d1.2.2
  exact (core_oix hAlign hGC hSP hSD (btWeight t') t' tLo tHi s b h aLo a' aHi
    rfl F1 F2 F3 BR loOT hiOT newOT o1 o2 setle).1

#print axioms oix_transportD
#print axioms oix_transport_holds

end PSS
