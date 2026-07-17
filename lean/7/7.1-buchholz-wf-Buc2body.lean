import «7».«7.1-buchholz-wf-W»

/-!
# §7.1 [Buc1] §2 本体 — `W` 階層の閉包定理 (foundation 2/2)

- 原文: `tmp/content.md` 5978 / 6331（`(OT_B, <)` の整礎性を [Buc1] 補題 2.2 で引用）
- [Buc1]: §2 p.137–139。2.4(a)(b)、2.5(1)、2.6、2.7、2.8。
  基本列は訂正 A23 後の `xseq`（`x₀ = D_u 0`, `x_{j+1} = D_u (b[x_j])`,
  `(D_v b)[n] = D_v (b[x_n])`）。
- 訂正: A23（[Buc1] 脚注 [30] の `xseq` 転置誤植の訂正。`bwl_DC` / `bwl_2_6` の
  case 4.2 が訂正後の形で証明される。Buchholz 自身の `b[1] ∈ W*` 迂回と
  「基点を全水準で」という回避策はいずれも不要になる）
- Isabelle: `isabelle/layerC/pss_scratch.thy`
  - `bwo_shift` (7773), `bwo_domB_Nil` (7997), `bwo_addBT_Nil_right` (8002),
    `bwo_addBT_Nil_left` (8005), `bwo_addBT_assoc` (8008), `bwo_addBT_domB` (8014),
    `bwo_operB_split` (8032), `bwo_addBT_operB` (8048),
    `bwo_domB_Dsucc0` (8181), `bwo_operB_Dsucc0` (8184)
  - `bwl_W2` (8851), `bwl_W3` (8860), `bwl_W_level_mono` (8874),
    `bwl_2_4a_shift` (8892), `bwl_2_4b_add` (8965), `bwl_2_4b_mult` (8981),
    `bwl_domB_one` (8993), `bwl_one_W` (8996), `bwl_numBT_W` (9006),
    `bwl_2_5_sub1` (9014), `bwl_domB_case_i` (9056), `bwl_TBv_neq_zero` (9061),
    `bwl_case_iii_guard_TBv` (9072), `bwl_D_zero_W` (9086),
    `bwl_key_collapse_sub` (9115), `bwl_key_collapse` (9213),
    `bwl_W_Dself` (9221), `bwl_numNat_numBT` (9228), `bwl_tbvIdx` (9231),
    `bwl_domB_case_ii` (9241), `bwl_operB_case_ii` (9252), `bwl_DC` (9278),
    `bwl_W_subset_star` (9441), `bwl_Wstar` (9458), `bwl_WstarI` (9461),
    `bwl_WstarD` (9464), `bwl_W_in_Wstar` (9469), `bwl_zero_Wstar` (9472),
    `bwl_2_6` (9477), `bwl_size_list_butlast` (9629), `bwl_size_butlast_lt` (9633),
    `bwl_2_7_aux` (9647), `bwl_2_8_dfree_Wstar` (9724), `bwl_2_8_principal` (9733)
- 依存: `7.1-buchholz-wf-W`（`bwl_Aop`/`bwl_Aset`/`bwl_W`/`bwl_A1`/`bwl_A2`/
  `bwl_A1_intro`/`bwl_A1_dest`/`bwl_A2'`/`bwl_W_zero`/`y3_W_mono`/
  `Bwl28Principal`/`Bwl24bAdd`）、`PSS.Buchholz`。
- 状態: ✅ green（sorry 0、名前付き仮定 0）。`7.1-buchholz-wf-W` の 2 つの名前付き
  仮定 `Bwl28Principal` / `Bwl24bAdd` を**定理として排出**する
  （`Bwl28Principal_holds` / `Bwl24bAdd_holds`）。

引用される [Buc1] 2.2 は**意味論的**（順序数への評価写像 `o`、`ψ_v`、`Ω_u`）であり、
定義的 HOL / Lean では表現できない。ここで移植するのは Buchholz–Schütte の
distinguished sets 法による**基数不要**の経路である。**順序数・`ψ`・`Ω` は一切現れない。**

Isabelle の `domB c = TBv (enat u)`（集合形）は Lean では tag 形 `domTag c = .below u`
で計算する。両者は `BDom.toSet` の単射性（`domB_below_iff_b2` 等）で橋渡しする。
private 補助の接尾辞は `_b2`。
-/

namespace PSS

/-! ## 0. `BDom.toSet` の単射性（Isabelle の集合形 ↔ Lean の tag 形）

built tree の `7.1-buchholz-wf-bachmann` に同内容の `private` 版があるが、`private` は
参照できないので再証明する。 -/

private theorem BZero_mem_TBv_b2 (v : ℕ∞) : BZero ∈ TBv v := by
  simp [TBv, BZero]

private theorem one_mem_TBv_b2 (v : ℕ∞) : Dprin 0 BZero ∈ TBv v := by
  simp [TBv, Dprin, BZero]

private theorem one_ne_BZero_b2 : Dprin 0 BZero ≠ BZero := by
  simp [Dprin, BZero]

private theorem w2_mem_TBv_b2 (v : ℕ∞) : Dprin 0 (Dprin 0 BZero) ∈ TBv v := by
  simp [TBv, Dprin, BZero]

private theorem w2_not_mem_NatSet_b2 : Dprin 0 (Dprin 0 BZero) ∉ NatSet := by
  rintro ⟨n, hn⟩
  match n, hn with
  | 0, hn => simp [numBT, Dprin, BZero] at hn
  | 1, hn => simp [numBT, Dprin, BZero] at hn
  | (n + 2), hn => simp [numBT, List.replicate, Dprin, BZero] at hn

private theorem Dprin_mem_TBv_self_b2 (u : ℕ) :
    Dprin (u : ℕ∞) BZero ∈ TBv (u : ℕ∞) := by
  simp [TBv, Dprin, BZero]

private theorem Dprin_not_mem_TBv_lt_b2 {u v : ℕ} (h : v < u) :
    Dprin (u : ℕ∞) BZero ∉ TBv (v : ℕ∞) := by
  simp only [TBv, Dprin, Set.mem_setOf_eq, List.all_cons, List.all_nil,
    Bool.and_true, decide_eq_true_eq, not_le]
  exact_mod_cast h

private theorem TBv_inj_b2 {u v : ℕ} (h : TBv (u : ℕ∞) = TBv (v : ℕ∞)) : u = v := by
  by_contra hne
  rcases Nat.lt_or_ge u v with hlt | hge
  · exact Dprin_not_mem_TBv_lt_b2 hlt (h ▸ Dprin_mem_TBv_self_b2 v)
  · have hlt : v < u := lt_of_le_of_ne hge (Ne.symm hne)
    exact Dprin_not_mem_TBv_lt_b2 hlt (h ▸ Dprin_mem_TBv_self_b2 u)

private theorem BZero_mem_NatSet_b2 : BZero ∈ NatSet := ⟨0, rfl⟩

private theorem one_mem_NatSet_b2 : Dprin 0 BZero ∈ NatSet :=
  ⟨1, by simp [numBT, Dprin, BZero, List.replicate]⟩

private theorem BDom_toSet_inj_b2 {d e : BDom} (h : d.toSet = e.toSet) : d = e := by
  cases d with
  | empty =>
      cases e with
      | empty => rfl
      | zeroOnly =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ (rfl : BZero ∈ ({BZero} : Set BT))
          exact absurd this (by simp [BDom.toSet])
      | naturals =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ BZero_mem_NatSet_b2
          exact absurd this (by simp [BDom.toSet])
      | below u =>
          have : BZero ∈ (BDom.empty).toSet := h ▸ BZero_mem_TBv_b2 (u : ℕ∞)
          exact absurd this (by simp [BDom.toSet])
  | zeroOnly =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.zeroOnly).toSet := rfl
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly => rfl
      | naturals =>
          have : Dprin 0 BZero ∈ (BDom.zeroOnly).toSet := h ▸ one_mem_NatSet_b2
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b2)
      | below u =>
          have : Dprin 0 BZero ∈ (BDom.zeroOnly).toSet := h ▸ one_mem_TBv_b2 (u : ℕ∞)
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b2)
  | naturals =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.naturals).toSet := BZero_mem_NatSet_b2
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly =>
          have : Dprin 0 BZero ∈ (BDom.naturals).toSet := one_mem_NatSet_b2
          rw [h] at this
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b2)
      | naturals => rfl
      | below u =>
          have : Dprin 0 (Dprin 0 BZero) ∈ (BDom.naturals).toSet :=
            h ▸ w2_mem_TBv_b2 (u : ℕ∞)
          exact absurd this w2_not_mem_NatSet_b2
  | below u =>
      cases e with
      | empty =>
          have : BZero ∈ (BDom.below u).toSet := BZero_mem_TBv_b2 (u : ℕ∞)
          rw [h] at this
          exact absurd this (by simp [BDom.toSet])
      | zeroOnly =>
          have : Dprin 0 BZero ∈ (BDom.below u).toSet := one_mem_TBv_b2 (u : ℕ∞)
          rw [h] at this
          exact absurd this (by simpa [BDom.toSet] using one_ne_BZero_b2)
      | naturals =>
          have : Dprin 0 (Dprin 0 BZero) ∈ (BDom.below u).toSet :=
            w2_mem_TBv_b2 (u : ℕ∞)
          rw [h] at this
          exact absurd this w2_not_mem_NatSet_b2
      | below v =>
          exact congrArg BDom.below (TBv_inj_b2 (by simpa [BDom.toSet] using h))

private theorem domB_below_iff_b2 (a : BT) (u : ℕ) :
    domB a = TBv (u : ℕ∞) ↔ domTag a = .below u := by
  constructor
  · intro h; exact BDom_toSet_inj_b2 (d := domTag a) (e := .below u) h
  · intro h; simp [domB, h, BDom.toSet]

private theorem domB_nat_iff_b2 (a : BT) :
    domB a = NatSet ↔ domTag a = .naturals := by
  constructor
  · intro h; exact BDom_toSet_inj_b2 (d := domTag a) (e := .naturals) h
  · intro h; simp [domB, h, BDom.toSet]

private theorem domB_zero_iff_b2 (a : BT) :
    domB a = {BZero} ↔ domTag a = .zeroOnly := by
  constructor
  · intro h; exact BDom_toSet_inj_b2 (d := domTag a) (e := .zeroOnly) h
  · intro h; simp [domB, h, BDom.toSet]

/-! ## 1. `operB` / `xseq` / `domTag` の展開（Isabelle の `b1x_*` / `bwl_*` 相当） -/

/-- Isabelle `b1x_xseq_0` (layerB/pss_wip.thy:28152)。 -/
private theorem xseq_zero_b2 (b : BT) (u : ℕ∞) :
    xseq b u 0 = Dprin u BZero := by
  simp [xseq, bOperCore]

/-- Isabelle `b1x_xseq_Suc` (layerB/pss_wip.thy:28155)。 -/
private theorem xseq_succ_b2 (b : BT) (u : ℕ∞) (i : ℕ) :
    xseq b u (i + 1) = Dprin u (operB b (xseq b u i)) := by
  simp [xseq, bOperCore, operB]

/-- Isabelle `b1x_operB_D0` (layerB/pss_wip.thy:28163)。 -/
private theorem operB_D0_b2 (z : BT) : operB (Dprin 0 BZero) z = BZero := by
  simp [operB, bOperCore, Dprin, BZero]

/-- Isabelle `b1x_operB_Dsucc` (layerB/pss_wip.thy:28170)。 -/
private theorem operB_Dsucc_b2 {v : ℕ∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) (z : BT) :
    operB (Dprin v BZero) z = z := by
  simp [operB, bOperCore, Dprin, BZero, hv0, hvtop]

/-- Isabelle `b1x_operB_case_i` (layerB/pss_wip.thy:28179)。 -/
private theorem operB_case_i_b2 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdb : domTag b = .zeroOnly) (z : BT) :
    operB (Dprin v b) z = multBT (Dprin v (operB b BZero)) (numNat z + 1) := by
  simp [operB, bOperCore, Dprin, hb, hdb]

/-- Isabelle `bwl_operB_case_ii` (pss_scratch.thy:9252)：訂正 A23 後の塔分岐。 -/
private theorem operB_case_ii_b2 {v : ℕ∞} {b : BT} {u : ℕ} (hb : b ≠ BZero)
    (hdb : domTag b = .below u) (hvu : v ≤ (u : ℕ∞)) (z : BT) :
    operB (Dprin v b) z = Dprin v (operB b (xseq b (u : ℕ∞) (numNat z))) := by
  simp [operB, bOperCore, Dprin, hb, hdb, hvu, xseq]

/-- Isabelle `b1x_operB_case_iii` (layerB/pss_wip.thy:28185)。 -/
private theorem operB_case_iii_b2 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdz : domTag b ≠ .zeroOnly)
    (hk : ∀ u : ℕ, domTag b = .below u → ¬ (v ≤ (u : ℕ∞))) (z : BT) :
    operB (Dprin v b) z = Dprin v (operB b z) := by
  cases hdb : domTag b with
  | empty => simp [operB, bOperCore, Dprin, hb, hdb]
  | zeroOnly => exact absurd hdb hdz
  | naturals => simp [operB, bOperCore, Dprin, hb, hdb]
  | below u => simp [operB, bOperCore, Dprin, hb, hdb, hk u hdb]

/-- Isabelle `b1x_operB_multi` (layerB/pss_wip.thy:28196)。 -/
private theorem operB_multi_b2 (p q : BP) (ps : List BP) (z : BT) :
    operB (.trm (p :: q :: ps)) z =
      addBT (.trm [p]) (operB (.trm (q :: ps)) z) := by
  simp [operB, bOperCore]

/-- Isabelle `b1x_domB_Dsucc` (layerB/pss_wip.thy:28216)。 -/
private theorem domTag_Dsucc_b2 {v : ℕ∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤) :
    domTag (Dprin v BZero) = .below (v.toNat - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero, hv0, hvtop]

/-- Isabelle `bwl_domB_case_i` (pss_scratch.thy:9056)。 -/
private theorem domTag_case_i_b2 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdb : domTag b = .zeroOnly) : domTag (Dprin v b) = .naturals := by
  simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]

/-- Isabelle `bwl_domB_case_ii` (pss_scratch.thy:9241)。 -/
private theorem domTag_case_ii_b2 {v : ℕ∞} {b : BT} {u : ℕ} (hb : b ≠ BZero)
    (hdb : domTag b = .below u) (hvu : v ≤ (u : ℕ∞)) :
    domTag (Dprin v b) = .naturals := by
  simp [domTag, domTagList, domTagBP, Dprin, hb, hdb, hvu]

/-- Isabelle `b1x_domB_case_iii` (layerB/pss_wip.thy:28205)。 -/
private theorem domTag_case_iii_b2 {v : ℕ∞} {b : BT} (hb : b ≠ BZero)
    (hdz : domTag b ≠ .zeroOnly)
    (hk : ∀ u : ℕ, domTag b = .below u → ¬ (v ≤ (u : ℕ∞))) :
    domTag (Dprin v b) = domTag b := by
  cases hdb : domTag b with
  | empty => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]
  | zeroOnly => exact absurd hdb hdz
  | naturals => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb]
  | below u => simp [domTag, domTagList, domTagBP, Dprin, hb, hdb, hk u hdb]

/-- Isabelle `bwl_numNat_numBT` (pss_scratch.thy:9228)。 -/
theorem bwl_numNat_numBT (n : ℕ) : numNat (numBT n) = n := by
  simp [numNat, numBT]

/-- Isabelle `b1x_mult_single` (layerB/pss_wip.thy:28225)。 -/
private theorem multBT_single_b2 (q : BP) (n : ℕ) :
    multBT (.trm [q]) n = .trm (List.replicate n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [multBT, ih]
      simp [addBT, List.replicate_succ']

/-! ## 2. `+_B` の代数と `dom` / `[·]` との相互作用 -/

/-- Isabelle `bwo_domB_Nil` (pss_scratch.thy:7997)。 -/
theorem bwo_domB_Nil : domB BZero = (∅ : Set BT) := by
  simp [domB, BZero, domTag, domTagList, BDom.toSet]

/-- Isabelle `bwo_addBT_Nil_right` (pss_scratch.thy:8002)。 -/
theorem bwo_addBT_Nil_right (a : BT) : addBT a BZero = a := by
  cases a; simp [addBT, BZero]

/-- Isabelle `bwo_addBT_Nil_left` (pss_scratch.thy:8005)。 -/
theorem bwo_addBT_Nil_left (b : BT) : addBT BZero b = b := by
  cases b; simp [addBT, BZero]

/-- Isabelle `bwo_addBT_assoc` (pss_scratch.thy:8008)。 -/
theorem bwo_addBT_assoc (a b c : BT) : addBT (addBT a b) c = addBT a (addBT b c) := by
  cases a; cases b; cases c; simp [addBT]

private theorem untrm_ne_nil_b2 {b : BT} {bs : List BP} (he : b = .trm bs)
    (hb : b ≠ BZero) : bs ≠ [] := by
  intro h; exact hb (by rw [he, h]; rfl)

private theorem domTagList_cons2_b2 (p q : BP) (qs : List BP) :
    domTagList (p :: q :: qs) = domTagList (q :: qs) := by
  simp [domTagList]

private theorem domTagList_append_b2 :
    ∀ (as bs : List BP), bs ≠ [] → domTagList (as ++ bs) = domTagList bs := by
  intro as
  induction as with
  | nil => intro bs _; simp
  | cons p as ih =>
      intro bs hbs
      have h : as ++ bs ≠ [] := fun e => hbs (List.append_eq_nil_iff.mp e).2
      cases hc : as ++ bs with
      | nil => exact absurd hc h
      | cons q qs =>
          have e1 : (p :: as) ++ bs = p :: q :: qs := by rw [List.cons_append, hc]
          rw [e1, domTagList_cons2_b2, ← hc]
          exact ih bs hbs

/-- Isabelle `bwo_addBT_domB` (pss_scratch.thy:8014)。 -/
theorem bwo_addBT_domB {a b : BT} (hb : b ≠ BZero) : domB (addBT a b) = domB b := by
  obtain ⟨as⟩ := a
  obtain ⟨bs⟩ := b
  have hbs : bs ≠ [] := untrm_ne_nil_b2 rfl hb
  show (domTag (.trm (as ++ bs))).toSet = (domTag (.trm bs)).toSet
  have : domTagList (as ++ bs) = domTagList bs := domTagList_append_b2 as bs hbs
  simpa [domTag] using congrArg BDom.toSet this

private theorem operB_append_b2 :
    ∀ (as bs : List BP), bs ≠ [] → ∀ z : BT,
      operB (.trm (as ++ bs)) z = addBT (.trm as) (operB (.trm bs) z) := by
  intro as
  induction as with
  | nil =>
      intro bs _ z
      simp only [List.nil_append]
      exact (bwo_addBT_Nil_left _).symm
  | cons p as ih =>
      intro bs hbs z
      have h : as ++ bs ≠ [] := fun e => hbs (List.append_eq_nil_iff.mp e).2
      cases hc : as ++ bs with
      | nil => exact absurd hc h
      | cons q qs =>
          have e1 : (p :: as) ++ bs = p :: q :: qs := by rw [List.cons_append, hc]
          rw [e1, operB_multi_b2 p q qs z, ← hc, ih bs hbs z, ← bwo_addBT_assoc]
          congr 1

/-- Isabelle `bwo_addBT_operB` (pss_scratch.thy:8048)。 -/
theorem bwo_addBT_operB {a b : BT} (hb : b ≠ BZero) (z : BT) :
    operB (addBT a b) z = addBT a (operB b z) := by
  obtain ⟨as⟩ := a
  obtain ⟨bs⟩ := b
  have hbs : bs ≠ [] := untrm_ne_nil_b2 rfl hb
  show operB (.trm (as ++ bs)) z = _
  exact operB_append_b2 as bs hbs z

/-- Isabelle `bwo_domB_Dsucc0` (pss_scratch.thy:8181)。 -/
theorem bwo_domB_Dsucc0 (u : ℕ) :
    domB (Dprin ((u + 1 : ℕ) : ℕ∞) BZero) = TBv (u : ℕ∞) := by
  refine (domB_below_iff_b2 _ u).mpr ?_
  have h0 : ((u + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero u
  rw [domTag_Dsucc_b2 h0 (ENat.coe_ne_top _)]
  congr 1

/-- Isabelle `bwo_operB_Dsucc0` (pss_scratch.thy:8184)。 -/
theorem bwo_operB_Dsucc0 (u : ℕ) (z : BT) :
    operB (Dprin ((u + 1 : ℕ) : ℕ∞) BZero) z = z := by
  refine operB_Dsucc_b2 ?_ (ENat.coe_ne_top _) z
  exact_mod_cast Nat.succ_ne_zero u

/-! ## 3. `W` の導入規則 (W2)/(W3) と水準単調性 -/

private theorem ne_BZero_of_dom_num_b2 {c : BT}
    (h : domB c = {BZero} ∨ domB c = NatSet) : c ≠ BZero := by
  intro hc
  subst hc
  rw [bwo_domB_Nil] at h
  rcases h with h | h
  · exact absurd ((Set.ext_iff.mp h BZero).mpr rfl) (by simp)
  · exact absurd ((Set.ext_iff.mp h BZero).mpr BZero_mem_NatSet_b2) (by simp)

private theorem ne_BZero_of_dom_TBv_b2 {c : BT} {u : ℕ}
    (h : domB c = TBv (u : ℕ∞)) : c ≠ BZero := by
  intro hc
  subst hc
  rw [bwo_domB_Nil] at h
  exact absurd ((Set.ext_iff.mp h BZero).mpr (BZero_mem_TBv_b2 _)) (by simp)

/-- Isabelle `bwl_W2` (pss_scratch.thy:8851)。 -/
theorem bwl_W2 {v : ℕ} {a : BT} (d : domB a = {BZero} ∨ domB a = NatSet)
    (op : ∀ n : ℕ, operB a (numBT n) ∈ bwl_W v) : a ∈ bwl_W v := by
  refine bwl_A1_intro ?_
  unfold bwl_Aop
  exact Or.inr (Or.inl ⟨d, op⟩)

/-- Isabelle `bwl_W3` (pss_scratch.thy:8860)。 -/
theorem bwl_W3 {u v : ℕ} {a : BT} (uv : u < v) (d : domB a = TBv (u : ℕ∞))
    (op : ∀ z ∈ bwl_W u, operB a z ∈ bwl_W v) : a ∈ bwl_W v := by
  refine bwl_A1_intro ?_
  unfold bwl_Aop
  refine Or.inr (Or.inr ⟨u, ?_, d, op⟩)
  exact_mod_cast uv

/-- Isabelle `bwl_W_level_mono` (pss_scratch.thy:8874)。built tree の `y3_W_mono`
    と同一命題（`7.1-buchholz-wf-W` で既に証明済み）。 -/
theorem bwl_W_level_mono {u v : ℕ} (uv : u ≤ v) : bwl_W u ⊆ bwl_W v := y3_W_mono uv

/-! ## 4. [Buc1] Lemma 2.4 -/

/-- [Buc1] p.138 (3) の `a`-シフト `X^{(a)} := {y | a + y ∈ X}`。
    Isabelle: `bwo_shift` (pss_scratch.thy:7773)。 -/
def bwo_shift (a : BT) (X : Set BT) : Set BT := {y | addBT a y ∈ X}

/-- [Buc1] 2.4(a)。Isabelle: `bwl_2_4a_shift` (pss_scratch.thy:8892)。 -/
theorem bwl_2_4a_shift {Wf : ℕ → Set BT} {nv : ℕ∞} {X : Set BT} {a b : BT}
    (Acl : ∀ c : BT, bwl_Aop Wf nv X c → c ∈ X) (aX : a ∈ X)
    (body : bwl_Aop Wf nv (bwo_shift a X) b) : b ∈ bwo_shift a X := by
  show addBT a b ∈ X
  unfold bwl_Aop at body
  rcases body with hz | ⟨hd, hop⟩ | ⟨u, hu, hd, hop⟩
  · rw [hz, bwo_addBT_Nil_right]; exact aX
  · have bne : b ≠ BZero := ne_BZero_of_dom_num_b2 hd
    have d : domB (addBT a b) = {BZero} ∨ domB (addBT a b) = NatSet := by
      rw [bwo_addBT_domB bne]; exact hd
    have op : ∀ n : ℕ, operB (addBT a b) (numBT n) ∈ X := by
      intro n
      rw [bwo_addBT_operB bne]
      exact hop n
    refine Acl _ ?_
    unfold bwl_Aop
    exact Or.inr (Or.inl ⟨d, op⟩)
  · have bne : b ≠ BZero := ne_BZero_of_dom_TBv_b2 hd
    have d : domB (addBT a b) = TBv (u : ℕ∞) := by rw [bwo_addBT_domB bne]; exact hd
    have op : ∀ z ∈ Wf u, operB (addBT a b) z ∈ X := by
      intro z hz
      rw [bwo_addBT_operB bne]
      exact hop z hz
    refine Acl _ ?_
    unfold bwl_Aop
    exact Or.inr (Or.inr ⟨u, hu, d, op⟩)

/-- [Buc1] 2.4(b)。Isabelle: `bwl_2_4b_add` (pss_scratch.thy:8965)。 -/
theorem bwl_2_4b_add {v : ℕ} {a b : BT} (ha : a ∈ bwl_W v) (hb : b ∈ bwl_W v) :
    addBT a b ∈ bwl_W v := by
  have Acl : ∀ c : BT, bwl_Aop bwl_W (v : ℕ∞) (bwl_W v) c → c ∈ bwl_W v :=
    fun _ h => bwl_A1_intro h
  have sh : ∀ c : BT, bwl_Aop bwl_W (v : ℕ∞) (bwo_shift a (bwl_W v)) c →
      c ∈ bwo_shift a (bwl_W v) := fun _ h => bwl_2_4a_shift Acl ha h
  have sub : bwl_W v ⊆ bwo_shift a (bwl_W v) := bwl_A2' sh
  exact sub hb

/-- [Buc1] 2.6 case 3 で使う反復形。Isabelle: `bwl_2_4b_mult` (pss_scratch.thy:8981)。 -/
theorem bwl_2_4b_mult {v : ℕ} {y : BT} (hy : y ∈ bwl_W v) (n : ℕ) :
    multBT y n ∈ bwl_W v := by
  induction n with
  | zero => exact bwl_W_zero v
  | succ n ih => exact bwl_2_4b_add ih hy

/-! ## 5. 数項はどの `W_v` にもいる -/

/-- Isabelle `bwl_domB_one` (pss_scratch.thy:8993)。 -/
theorem bwl_domB_one : domB (Dprin 0 BZero) = ({BZero} : Set BT) := by
  refine (domB_zero_iff_b2 _).mpr ?_
  simp [domTag, domTagList, domTagBP, Dprin, BZero]

/-- Isabelle `bwl_one_W` (pss_scratch.thy:8996)。 -/
theorem bwl_one_W (v : ℕ) : Dprin 0 BZero ∈ bwl_W v := by
  refine bwl_W2 (Or.inl bwl_domB_one) (fun n => ?_)
  rw [operB_D0_b2]
  exact bwl_W_zero v

/-- Isabelle `bwl_numBT_W` (pss_scratch.thy:9006)。 -/
theorem bwl_numBT_W (n v : ℕ) : numBT n ∈ bwl_W v := by
  have h := bwl_2_4b_mult (bwl_one_W v) n
  rw [show Dprin 0 BZero = (.trm [.db 0 BZero] : BT) from rfl, multBT_single_b2] at h
  exact h

/-! ## 6. [Buc1] Lemma 2.5 sub-result (1) -/

/-- Isabelle `bwl_2_5_sub1` (pss_scratch.thy:9014)。 -/
theorem bwl_2_5_sub1 {nv : ℕ∞} {X : Set BT} {a : BT} {u : ℕ}
    (Acl : ∀ c : BT, bwl_Aop bwl_W nv X c → c ∈ X) (aX : a ∈ X)
    (ult : (u : ℕ∞) < nv) :
    addBT a (Dprin ((u + 1 : ℕ) : ℕ∞) BZero) ∈ X := by
  set D : BT := Dprin ((u + 1 : ℕ) : ℕ∞) BZero with hD
  have Dne : D ≠ BZero := by simp [hD, Dprin, BZero]
  have domAD : domB (addBT a D) = TBv (u : ℕ∞) := by
    rw [bwo_addBT_domB Dne, hD, bwo_domB_Dsucc0]
  have opAD : ∀ z : BT, operB (addBT a D) z = addBT a z := by
    intro z
    rw [bwo_addBT_operB Dne, hD, bwo_operB_Dsucc0]
  have shiftAu : ∀ c : BT, bwl_Aop bwl_W (u : ℕ∞) (bwo_shift a X) c →
      c ∈ bwo_shift a X := by
    intro c hc
    exact bwl_2_4a_shift Acl aX (bwl_Aop_mono_nv (le_of_lt ult) hc)
  have WsubShift : bwl_W u ⊆ bwo_shift a X := bwl_A2' shiftAu
  have opX : ∀ z ∈ bwl_W u, operB (addBT a D) z ∈ X := by
    intro z hz
    rw [opAD z]
    exact WsubShift hz
  refine Acl _ ?_
  unfold bwl_Aop
  exact Or.inr (Or.inr ⟨u, ult, domAD, opX⟩)

/-! ## 7. `D_w c` の形補題（`operB` / `domB` のガード） -/

/-- Isabelle `bwl_TBv_neq_zero` (pss_scratch.thy:9061)。 -/
theorem bwl_TBv_neq_zero (m : ℕ) : TBv (m : ℕ∞) ≠ ({BZero} : Set BT) := by
  intro h
  exact absurd ((Set.ext_iff.mp h (Dprin 0 BZero)).mp (one_mem_TBv_b2 _)) one_ne_BZero_b2

/-- Isabelle `bwl_case_iii_guard_TBv` (pss_scratch.thy:9072)。 -/
theorem bwl_case_iii_guard_TBv {m w : ℕ} (mw : m < w) :
    ¬ ∃ u : ℕ, (w : ℕ∞) ≤ (u : ℕ∞) ∧ TBv (m : ℕ∞) = TBv (u : ℕ∞) := by
  rintro ⟨u, wu, eq⟩
  have : m = u := TBv_inj_b2 eq
  subst this
  have : w ≤ m := by exact_mod_cast wu
  omega

/-- Isabelle `bwl_domB_case_i` (pss_scratch.thy:9056)。 -/
theorem bwl_domB_case_i {v : ℕ∞} {b : BT} (bne : b ≠ BZero) (hd : domB b = {BZero}) :
    domB (Dprin v b) = NatSet :=
  (domB_nat_iff_b2 _).mpr (domTag_case_i_b2 bne ((domB_zero_iff_b2 b).mp hd))

/-- Isabelle `bwl_domB_case_ii` (pss_scratch.thy:9241)。 -/
theorem bwl_domB_case_ii {v : ℕ∞} {b : BT} {u : ℕ} (bne : b ≠ BZero)
    (hd : domB b = TBv (u : ℕ∞)) (hvu : v ≤ (u : ℕ∞)) : domB (Dprin v b) = NatSet :=
  (domB_nat_iff_b2 _).mpr (domTag_case_ii_b2 bne ((domB_below_iff_b2 b u).mp hd) hvu)

/-- Isabelle `bwl_tbvIdx` (pss_scratch.thy:9231)。 -/
theorem bwl_tbvIdx (u : ℕ) : tbvIdx (TBv (u : ℕ∞)) = u := by
  classical
  have hex : ∃ k : ℕ, TBv (u : ℕ∞) = TBv (k : ℕ∞) := ⟨u, rfl⟩
  unfold tbvIdx
  rw [dif_pos hex]
  exact (TBv_inj_b2 (Classical.choose_spec hex)).symm

/-- Isabelle `bwl_operB_case_ii` (pss_scratch.thy:9252)。訂正 A23 後の `xseq` 分岐。 -/
theorem bwl_operB_case_ii {v : ℕ∞} {b : BT} {u : ℕ} (bne : b ≠ BZero)
    (hd : domB b = TBv (u : ℕ∞)) (hvu : v ≤ (u : ℕ∞)) (z : BT) :
    operB (Dprin v b) z
      = Dprin v (operB b (xseq b ((tbvIdx (domB b) : ℕ) : ℕ∞) (numNat z))) := by
  rw [hd, bwl_tbvIdx]
  exact operB_case_ii_b2 bne ((domB_below_iff_b2 b u).mp hd) hvu z

/-! ## 8. `D_w 0 ∈ W_w` -/

/-- Isabelle `bwl_D_zero_W` (pss_scratch.thy:9086)。 -/
theorem bwl_D_zero_W (w : ℕ) : Dprin (w : ℕ∞) BZero ∈ bwl_W w := by
  cases w with
  | zero => simpa using bwl_one_W 0
  | succ s =>
      refine bwl_W3 (u := s) (Nat.lt_succ_self s) (bwo_domB_Dsucc0 s) (fun z hz => ?_)
      rw [bwo_operB_Dsucc0]
      exact bwl_W_level_mono (Nat.le_succ s) hz

/-! ## 9. 3 分岐の共通エンジン

Isabelle では `bwl_key_collapse_sub` / `bwl_DC` / `bwl_2_6` が同じ 3 分岐
（`A` の zero / num / `T_u` clause × `D_v` の ([].4)(i)/(ii)/(iii) 分岐）を
それぞれ書き下している。Lean では 3 本の private エンジンに括り出す。 -/

private theorem numBT_zero_b2 : numBT 0 = BZero := by
  simp [numBT, BZero]

/-- `A` の num clause（`dom c ∈ {{0}, ℕ}`）から `D_v c ∈ W_v` を出す。
    Isabelle の 3 箇所（9130 / 9308 / 9491）の `num` case に対応。 -/
private theorem Dprin_num_case_b2 {v : ℕ} {c : BT} (cne : c ≠ BZero)
    (hd : domB c = {BZero} ∨ domB c = NatSet)
    (hY : ∀ n : ℕ, Dprin (v : ℕ∞) (operB c (numBT n)) ∈ bwl_W v) :
    Dprin (v : ℕ∞) c ∈ bwl_W v := by
  by_cases hz : domB c = {BZero}
  · have htag : domTag c = .zeroOnly := (domB_zero_iff_b2 c).mp hz
    have dW : domB (Dprin (v : ℕ∞) c) = NatSet :=
      (domB_nat_iff_b2 _).mpr (domTag_case_i_b2 cne htag)
    have base : Dprin (v : ℕ∞) (operB c BZero) ∈ bwl_W v := by
      have h := hY 0
      rwa [numBT_zero_b2] at h
    refine bwl_W2 (Or.inr dW) (fun n => ?_)
    rw [operB_case_i_b2 cne htag, bwl_numNat_numBT]
    exact bwl_2_4b_mult base (n + 1)
  · have hN : domB c = NatSet := hd.resolve_left hz
    have htagN : domTag c = .naturals := (domB_nat_iff_b2 c).mp hN
    have hdz : domTag c ≠ .zeroOnly := by rw [htagN]; simp
    have hk : ∀ u : ℕ, domTag c = .below u → ¬ ((v : ℕ∞) ≤ (u : ℕ∞)) := by
      intro u hu; rw [htagN] at hu; exact absurd hu (by simp)
    have dW : domB (Dprin (v : ℕ∞) c) = domB c := by
      show (domTag (Dprin (v : ℕ∞) c)).toSet = (domTag c).toSet
      rw [domTag_case_iii_b2 cne hdz hk]
    refine bwl_W2 (Or.inr (by rw [dW, hN])) (fun n => ?_)
    rw [operB_case_iii_b2 cne hdz hk]
    exact hY n

/-- `A` の `T_k` clause で `k < v` のとき（[Buc1] ([].4)(iii)、規則 (W3)）。 -/
private theorem Dprin_below_case_iii_b2 {v k : ℕ} {c : BT} (cne : c ≠ BZero)
    (htag : domTag c = .below k) (hkv : k < v)
    (hY : ∀ z ∈ bwl_W k, Dprin (v : ℕ∞) (operB c z) ∈ bwl_W v) :
    Dprin (v : ℕ∞) c ∈ bwl_W v := by
  have hdz : domTag c ≠ .zeroOnly := by rw [htag]; simp
  have hk : ∀ u : ℕ, domTag c = .below u → ¬ ((v : ℕ∞) ≤ (u : ℕ∞)) := by
    intro u hu
    rw [htag] at hu
    have hku : k = u := by simpa using hu
    subst hku
    exact_mod_cast Nat.not_le.mpr hkv
  have dW : domB (Dprin (v : ℕ∞) c) = TBv (k : ℕ∞) := by
    refine (domB_below_iff_b2 _ k).mpr ?_
    rw [domTag_case_iii_b2 cne hdz hk, htag]
  refine bwl_W3 hkv dW (fun z hz => ?_)
  rw [operB_case_iii_b2 cne hdz hk]
  exact hY z hz

/-- `A` の `T_k` clause で `v ≤ k` のとき（[Buc1] ([].4)(ii) = 訂正 A23 後の `xseq`
    分岐、規則 (W2)）。 -/
private theorem Dprin_below_case_ii_b2 {v k : ℕ} {c : BT} (cne : c ≠ BZero)
    (htag : domTag c = .below k) (hvk : v ≤ k)
    (hx : ∀ j : ℕ, xseq c (k : ℕ∞) j ∈ bwl_W k)
    (hY : ∀ z ∈ bwl_W k, Dprin (v : ℕ∞) (operB c z) ∈ bwl_W v) :
    Dprin (v : ℕ∞) c ∈ bwl_W v := by
  have hvk' : (v : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hvk
  have dW : domB (Dprin (v : ℕ∞) c) = NatSet :=
    (domB_nat_iff_b2 _).mpr (domTag_case_ii_b2 cne htag hvk')
  refine bwl_W2 (Or.inr dW) (fun n => ?_)
  rw [operB_case_ii_b2 cne htag hvk', bwl_numNat_numBT]
  exact hY _ (hx n)

/-- 訂正 A23 後の `xseq` は `W_k` の中に留まる: `x₀ = D_k 0`, `x_{j+1} = D_k (c[x_j])`。 -/
private theorem xseq_mem_W_b2 {k : ℕ} {c : BT}
    (hstep : ∀ z : BT, z ∈ bwl_W k → Dprin (k : ℕ∞) (operB c z) ∈ bwl_W k) :
    ∀ j : ℕ, xseq c (k : ℕ∞) j ∈ bwl_W k := by
  intro j
  induction j with
  | zero => rw [xseq_zero_b2]; exact bwl_D_zero_W k
  | succ j ih => rw [xseq_succ_b2]; exact hstep _ ih

/-! ## 10. 上向き collapse `u ≤ w ⟹ x ∈ W_u ⟹ D_w x ∈ W_w` -/

/-- Isabelle `bwl_key_collapse_sub` (pss_scratch.thy:9115)。 -/
theorem bwl_key_collapse_sub {u w : ℕ} (uw : u ≤ w) :
    bwl_W u ⊆ {x : BT | Dprin (w : ℕ∞) x ∈ bwl_W w} := by
  refine bwl_A2' (fun c A => ?_)
  show Dprin (w : ℕ∞) c ∈ bwl_W w
  unfold bwl_Aop at A
  rcases A with hz | ⟨hd, hop⟩ | ⟨k, hk, hd, hop⟩
  · rw [hz]; exact bwl_D_zero_W w
  · exact Dprin_num_case_b2 (ne_BZero_of_dom_num_b2 hd) hd (fun n => hop n)
  · have ku : k < u := by exact_mod_cast hk
    have km : k < w := lt_of_lt_of_le ku uw
    exact Dprin_below_case_iii_b2 (ne_BZero_of_dom_TBv_b2 hd)
      ((domB_below_iff_b2 c k).mp hd) km (fun z hz => hop z hz)

/-- Isabelle `bwl_key_collapse` (pss_scratch.thy:9213)。 -/
theorem bwl_key_collapse {u w : ℕ} (uw : u ≤ w) {x : BT} (hx : x ∈ bwl_W u) :
    Dprin (w : ℕ∞) x ∈ bwl_W w := bwl_key_collapse_sub uw hx

/-- Isabelle `bwl_W_Dself` (pss_scratch.thy:9221)。 -/
theorem bwl_W_Dself {w : ℕ} {x : BT} (hx : x ∈ bwl_W w) :
    Dprin (w : ℕ∞) x ∈ bwl_W w := bwl_key_collapse le_rfl hx

/-! ## 11. 下向き collapse `W_m ⊆ {y | ∀ v ≤ m. D_v y ∈ W_v}`

訂正 A23 後の ([].4)(ii)（`x₀ = D_k 0`, `x_{j+1} = D_k (c[x_j])`,
`(D_v c)[n] = D_v (c[x_n])`）では `xseq` は丸ごと `W_k` に住むので、Isabelle が
`less_induct`（水準についての強帰納）で用意した基点回避策は**使われずに済む**
（Isabelle 側でも `less.IH` は本文中で一度も使われていない）。Lean では帰納法自体を
落とした。 -/

/-- Isabelle `bwl_DC` (pss_scratch.thy:9278)。 -/
theorem bwl_DC (m : ℕ) :
    bwl_W m ⊆ {y : BT | ∀ v ≤ m, Dprin (v : ℕ∞) y ∈ bwl_W v} := by
  refine bwl_A2' (fun c A => ?_)
  show ∀ v ≤ m, Dprin (v : ℕ∞) c ∈ bwl_W v
  intro v vm
  unfold bwl_Aop at A
  rcases A with hz | ⟨hd, hop⟩ | ⟨k, hk, hd, hop⟩
  · rw [hz]; exact bwl_D_zero_W v
  · exact Dprin_num_case_b2 (ne_BZero_of_dom_num_b2 hd) hd (fun n => (hop n) v vm)
  · have km : k < m := by exact_mod_cast hk
    have cne := ne_BZero_of_dom_TBv_b2 hd
    have htag : domTag c = .below k := (domB_below_iff_b2 c k).mp hd
    by_cases hkv : k < v
    · exact Dprin_below_case_iii_b2 cne htag hkv (fun z hz => (hop z hz) v vm)
    · have hvk : v ≤ k := Nat.le_of_not_lt hkv
      have hx : ∀ j : ℕ, xseq c (k : ℕ∞) j ∈ bwl_W k :=
        xseq_mem_W_b2 (fun z hz => (hop z hz) k (le_of_lt km))
      exact Dprin_below_case_ii_b2 cne htag hvk hx (fun z hz => (hop z hz) v vm)

/-- Isabelle `bwl_W_subset_star` (pss_scratch.thy:9441)。 -/
theorem bwl_W_subset_star {m v : ℕ} {y : BT} (hy : y ∈ bwl_W m) :
    Dprin (v : ℕ∞) y ∈ bwl_W v := by
  by_cases h : v ≤ m
  · exact (bwl_DC m hy) v h
  · exact bwl_key_collapse (Nat.not_le.mp h).le hy

/-! ## 12. [Buc1] p.138(5): `W* = {x | ∀ u < ν. D_u x ∈ W_u}`（ここで `ν = ω`） -/

/-- Isabelle `bwl_Wstar` (pss_scratch.thy:9458)。 -/
def bwl_Wstar : Set BT := {x : BT | ∀ u : ℕ, Dprin (u : ℕ∞) x ∈ bwl_W u}

/-- Isabelle `bwl_WstarI` (pss_scratch.thy:9461)。 -/
theorem bwl_WstarI {x : BT} (h : ∀ u : ℕ, Dprin (u : ℕ∞) x ∈ bwl_W u) :
    x ∈ bwl_Wstar := h

/-- Isabelle `bwl_WstarD` (pss_scratch.thy:9464)。 -/
theorem bwl_WstarD {x : BT} (h : x ∈ bwl_Wstar) (u : ℕ) :
    Dprin (u : ℕ∞) x ∈ bwl_W u := h u

/-- Isabelle `bwl_W_in_Wstar` (pss_scratch.thy:9469)。 -/
theorem bwl_W_in_Wstar {m : ℕ} {y : BT} (h : y ∈ bwl_W m) : y ∈ bwl_Wstar :=
  bwl_WstarI (fun _ => bwl_W_subset_star h)

/-- Isabelle `bwl_zero_Wstar` (pss_scratch.thy:9472)。 -/
theorem bwl_zero_Wstar : BZero ∈ bwl_Wstar := bwl_W_in_Wstar (bwl_W_zero 0)

/-! ## 13. [Buc1] Lemma 2.6: `A_ν(W*) ⊆ W*` -/

/-- Isabelle `bwl_2_6` (pss_scratch.thy:9477)。 -/
theorem bwl_2_6 {b : BT} (A : bwl_Aop bwl_W ⊤ bwl_Wstar b) : b ∈ bwl_Wstar := by
  refine bwl_WstarI (fun v => ?_)
  unfold bwl_Aop at A
  rcases A with hz | ⟨hd, hop⟩ | ⟨u, _, hd, hop⟩
  · rw [hz]; exact bwl_D_zero_W v
  · exact Dprin_num_case_b2 (ne_BZero_of_dom_num_b2 hd) hd
      (fun n => bwl_WstarD (hop n) v)
  · have bne := ne_BZero_of_dom_TBv_b2 hd
    have htag : domTag b = .below u := (domB_below_iff_b2 b u).mp hd
    by_cases huv : u < v
    · exact Dprin_below_case_iii_b2 bne htag huv (fun z hz => bwl_WstarD (hop z hz) v)
    · have hvu : v ≤ u := Nat.le_of_not_lt huv
      have hx : ∀ j : ℕ, xseq b (u : ℕ∞) j ∈ bwl_W u :=
        xseq_mem_W_b2 (fun z hz => bwl_WstarD (hop z hz) u)
      exact Dprin_below_case_ii_b2 bne htag hvu hx (fun z hz => bwl_WstarD (hop z hz) v)

/-! ## 14. [Buc1] Lemma 2.7（`D_ω`-free 項に対する長さ帰納）

`ν = ω = ⊤` を取り `D_ω`-free 項 `T_B` に制限する。すると Buchholz の case 3
（`a = D_ν b` で指標が `ν` に等しい場合。Lemma 2.5 と `D_ν`-閉包 `Xbar` を要する
唯一の case）は**起こり得ない** — `D_ω`-free な principal の指標は必ず有限、すなわち
Buchholz の case 4 であり、2.6 と最小性 (A2) で処理される。したがって [Buc1] 2.5 の
6-case `Xbar` 解析は丸ごと迂回される。帰納は `btWeight`（Isabelle の `size` に相当）
で行い、`X` は一般化する（case 2 でシフト `X^{(c)}`、case 3 で `W*` に具体化）。 -/

private theorem btWeight_trm_b2 (ps : List BP) :
    btWeight (.trm ps) = bpListWeight ps + 1 := by
  simp [btWeight]

private theorem bpWeight_db_b2 (v : ℕ∞) (b : BT) :
    bpWeight (.db v b) = btWeight b + 1 := by
  simp [bpWeight]

private theorem bpListWeight_nil_b2 : bpListWeight ([] : List BP) = 0 := by
  simp [bpListWeight]

private theorem bpListWeight_cons_b2 (p : BP) (ps : List BP) :
    bpListWeight (p :: ps) = bpWeight p + bpListWeight ps + 1 := by
  simp [bpListWeight]

private theorem btWeight_pos_b2 (a : BT) : 1 ≤ btWeight a := by
  obtain ⟨ps⟩ := a; rw [btWeight_trm_b2]; omega

private theorem bpWeight_ge_two_b2 (p : BP) : 2 ≤ bpWeight p := by
  obtain ⟨v, b⟩ := p
  rw [bpWeight_db_b2]
  have := btWeight_pos_b2 b
  omega

private theorem bpWeight_le_list_b2 :
    ∀ (ps : List BP) (p : BP), p ∈ ps → bpWeight p ≤ bpListWeight ps := by
  intro ps
  induction ps with
  | nil => intro p hp; simp at hp
  | cons q qs ih =>
      intro p hp
      rw [bpListWeight_cons_b2]
      rcases List.mem_cons.mp hp with rfl | hp'
      · omega
      · have := ih p hp'; omega

/-- Isabelle `bwl_size_list_butlast` (pss_scratch.thy:9629) /
    `bwl_size_butlast_lt` (9633)。 -/
private theorem bpListWeight_dropLast_lt_b2 :
    ∀ (xs : List BP), xs ≠ [] → bpListWeight xs.dropLast < bpListWeight xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons p ps ih =>
      intro _
      cases ps with
      | nil =>
          have hd : ([p] : List BP).dropLast = [] := rfl
          rw [hd, bpListWeight_cons_b2, bpListWeight_nil_b2]
          omega
      | cons q qs =>
          have hd : (p :: q :: qs).dropLast = p :: (q :: qs).dropLast := rfl
          rw [hd, bpListWeight_cons_b2, bpListWeight_cons_b2 p (q :: qs)]
          have := ih (by simp)
          omega

private theorem bpWeight_add_two_le_b2 (p q : BP) (qs : List BP) (r : BP)
    (hr : r ∈ p :: q :: qs) : bpWeight r + 2 ≤ bpListWeight (p :: q :: qs) := by
  rw [bpListWeight_cons_b2 p, bpListWeight_cons_b2 q]
  have hp := bpWeight_ge_two_b2 p
  rcases List.mem_cons.mp hr with rfl | hr'
  · omega
  · have h := bpWeight_le_list_b2 (q :: qs) r hr'
    rw [bpListWeight_cons_b2 q] at h
    omega

private theorem dfree_BT_trm_b2 (ps : List BP) :
    dfree_BT (.trm ps) = dfree_BPList ps := by simp [dfree_BT]

private theorem dfree_BPList_cons_b2 (p : BP) (ps : List BP) :
    dfree_BPList (p :: ps) = (dfree_BP p && dfree_BPList ps) := by
  simp [dfree_BPList]

private theorem dfree_BPList_forall_b2 :
    ∀ (ps : List BP), dfree_BPList ps = true → ∀ p ∈ ps, dfree_BP p = true := by
  intro ps
  induction ps with
  | nil => intro _ p hp; simp at hp
  | cons q qs ih =>
      intro h p hp
      rw [dfree_BPList_cons_b2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact h.1
      · exact ih h.2 p hp'

private theorem dfree_BPList_of_forall_b2 :
    ∀ (ps : List BP), (∀ p ∈ ps, dfree_BP p = true) → dfree_BPList ps = true := by
  intro ps
  induction ps with
  | nil => intro _; rfl
  | cons q qs ih =>
      intro h
      rw [dfree_BPList_cons_b2, Bool.and_eq_true]
      exact ⟨h q List.mem_cons_self, ih (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

private theorem addBT_trm_b2 (as bs : List BP) :
    addBT (.trm as) (.trm bs) = .trm (as ++ bs) := rfl

private theorem bwl_2_7_size_b2 : ∀ (n : ℕ) (a : BT), btWeight a ≤ n →
    ∀ X : Set BT, (∀ c : BT, bwl_Aop bwl_W ⊤ X c → c ∈ X) →
      dfree_BT a = true → a ∈ X := by
  intro n
  induction n with
  | zero =>
      intro a ha
      obtain ⟨ps⟩ := a
      rw [btWeight_trm_b2] at ha
      omega
  | succ n ih =>
      intro a ha X Acl dfa
      obtain ⟨xs⟩ := a
      cases xs with
      | nil =>
          refine Acl _ ?_
          unfold bwl_Aop
          exact Or.inl rfl
      | cons p ps =>
          cases ps with
          | nil =>
              -- 単一 principal `a = D_w b`。`D_ω`-free 性が `w = k < ω = ν` を強制
              -- （[Buc1] 2.7 case 4）。
              obtain ⟨w, b⟩ := p
              have dfa' : dfree_BPList [BP.db w b] = true := by
                rwa [dfree_BT_trm_b2] at dfa
              have dfp : dfree_BP (BP.db w b) = true := by
                rw [dfree_BPList_cons_b2, Bool.and_eq_true] at dfa'
                exact dfa'.1
              have hsp : w ≠ ⊤ ∧ dfree_BT b = true := by
                simpa [dfree_BP, Bool.and_eq_true, bne_iff_ne] using dfp
              obtain ⟨wne, dfb⟩ := hsp
              lift w to ℕ using wne with k
              have szb : btWeight b ≤ n := by
                rw [btWeight_trm_b2, bpListWeight_cons_b2, bpWeight_db_b2,
                  bpListWeight_nil_b2] at ha
                omega
              have Wcl : ∀ c : BT, bwl_Aop bwl_W ⊤ bwl_Wstar c → c ∈ bwl_Wstar :=
                fun _ h => bwl_2_6 h
              have bW : b ∈ bwl_Wstar := ih b szb bwl_Wstar Wcl dfb
              have Dn : Dprin (k : ℕ∞) b ∈ bwl_W k := bwl_WstarD bW k
              have AnX : ∀ c : BT, bwl_Aop bwl_W (k : ℕ∞) X c → c ∈ X :=
                fun c h => Acl c (bwl_Aop_mono_nv le_top h)
              exact bwl_A2' AnX Dn
          | cons q qs =>
              -- `a = c + a_k`（`c` は butlast）。[Buc1] 2.7 case 2、2.4(a) 経由。
              have hne : (p :: q :: qs) ≠ [] := by simp
              obtain ⟨L, hLmem, hsplit⟩ :
                  ∃ L : BP, L ∈ (p :: q :: qs) ∧
                    (p :: q :: qs).dropLast ++ [L] = p :: q :: qs :=
                ⟨(p :: q :: qs).getLast hne, List.getLast_mem hne,
                  List.dropLast_append_getLast hne⟩
              have hxs : bpListWeight (p :: q :: qs) ≤ n := by
                rw [btWeight_trm_b2] at ha; omega
              have szc : btWeight (BT.trm (p :: q :: qs).dropLast) ≤ n := by
                rw [btWeight_trm_b2]
                have := bpListWeight_dropLast_lt_b2 (p :: q :: qs) hne
                omega
              have szl : btWeight (BT.trm [L]) ≤ n := by
                rw [btWeight_trm_b2, bpListWeight_cons_b2, bpListWeight_nil_b2]
                have h1 := bpWeight_add_two_le_b2 p q qs L hLmem
                omega
              have dfxs : ∀ r ∈ (p :: q :: qs), dfree_BP r = true :=
                dfree_BPList_forall_b2 _ (by rwa [dfree_BT_trm_b2] at dfa)
              have dfc : dfree_BT (BT.trm (p :: q :: qs).dropLast) = true := by
                rw [dfree_BT_trm_b2]
                exact dfree_BPList_of_forall_b2 _
                  (fun r hr => dfxs r (List.dropLast_subset _ hr))
              have dfl : dfree_BT (BT.trm [L]) = true := by
                rw [dfree_BT_trm_b2]
                refine dfree_BPList_of_forall_b2 _ (fun r hr => ?_)
                rw [List.mem_singleton.mp hr]
                exact dfxs L hLmem
              have cX : BT.trm (p :: q :: qs).dropLast ∈ X := ih _ szc X Acl dfc
              have shcl : ∀ d : BT,
                  bwl_Aop bwl_W ⊤ (bwo_shift (BT.trm (p :: q :: qs).dropLast) X) d →
                    d ∈ bwo_shift (BT.trm (p :: q :: qs).dropLast) X :=
                fun _ h => bwl_2_4a_shift Acl cX h
              have lastIn : BT.trm [L] ∈ bwo_shift (BT.trm (p :: q :: qs).dropLast) X :=
                ih _ szl _ shcl dfl
              have final : addBT (BT.trm (p :: q :: qs).dropLast) (BT.trm [L]) ∈ X :=
                lastIn
              rw [addBT_trm_b2, hsplit] at final
              exact final

/-- Isabelle `bwl_2_7_aux` (pss_scratch.thy:9647)。 -/
theorem bwl_2_7_aux (a : BT) (X : Set BT)
    (Acl : ∀ c : BT, bwl_Aop bwl_W ⊤ X c → c ∈ X) (dfa : dfree_BT a = true) : a ∈ X :=
  bwl_2_7_size_b2 (btWeight a) a le_rfl X Acl dfa

/-! ## 15. [Buc1] 2.8 for `T_B`: `D_ω`-free 項はすべて `W*` にいる -/

/-- Isabelle `bwl_2_8_dfree_Wstar` (pss_scratch.thy:9724)。`OT`（正規形）仮定は不要。 -/
theorem bwl_2_8_dfree_Wstar {t : BT} (df : dfree_BT t = true) : t ∈ bwl_Wstar :=
  bwl_2_7_aux t bwl_Wstar (fun _ h => bwl_2_6 h) df

/-- Isabelle `bwl_2_8_principal` (pss_scratch.thy:9733)。 -/
theorem bwl_2_8_principal {u : ℕ} {t : BT} (df : dfree_BT t = true) :
    Dprin (u : ℕ∞) t ∈ bwl_W u :=
  bwl_WstarD (bwl_2_8_dfree_Wstar df) u

/-! ## 16. `7.1-buchholz-wf-W` の 2 つの名前付き仮定の排出 -/

/-- `7.1-buchholz-wf-W` の名前付き仮定 `Bwl28Principal`（= [Buc1] 2.8 の系）を
    定理として供給する。 -/
theorem Bwl28Principal_holds : Bwl28Principal :=
  fun _ _ df => bwl_2_8_principal df

/-- `7.1-buchholz-wf-W` の名前付き仮定 `Bwl24bAdd`（= [Buc1] 2.4(b)）を
    定理として供給する。 -/
theorem Bwl24bAdd_holds : Bwl24bAdd :=
  fun _ _ _ ha hb => bwl_2_4b_add ha hb

#print axioms bwl_numNat_numBT
#print axioms bwo_domB_Nil
#print axioms bwo_addBT_Nil_right
#print axioms bwo_addBT_Nil_left
#print axioms bwo_addBT_assoc
#print axioms bwo_addBT_domB
#print axioms bwo_addBT_operB
#print axioms bwo_domB_Dsucc0
#print axioms bwo_operB_Dsucc0
#print axioms bwl_W2
#print axioms bwl_W3
#print axioms bwl_W_level_mono
#print axioms bwl_2_4a_shift
#print axioms bwl_2_4b_add
#print axioms bwl_2_4b_mult
#print axioms bwl_domB_one
#print axioms bwl_one_W
#print axioms bwl_numBT_W
#print axioms bwl_2_5_sub1
#print axioms bwl_TBv_neq_zero
#print axioms bwl_case_iii_guard_TBv
#print axioms bwl_domB_case_i
#print axioms bwl_domB_case_ii
#print axioms bwl_tbvIdx
#print axioms bwl_operB_case_ii
#print axioms bwl_D_zero_W
#print axioms bwl_key_collapse_sub
#print axioms bwl_key_collapse
#print axioms bwl_W_Dself
#print axioms bwl_DC
#print axioms bwl_W_subset_star
#print axioms bwl_WstarI
#print axioms bwl_WstarD
#print axioms bwl_W_in_Wstar
#print axioms bwl_zero_Wstar
#print axioms bwl_2_6
#print axioms bwl_2_7_aux
#print axioms bwl_2_8_dfree_Wstar
#print axioms bwl_2_8_principal
#print axioms Bwl28Principal_holds
#print axioms Bwl24bAdd_holds

end PSS
