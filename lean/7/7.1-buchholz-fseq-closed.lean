import «7».«7.1-buchholz-fseq-lt»

/-!
# §7.1 [Buc1] Lemma 3.3: closure of fundamental sequences

This file proves that the executable Buchholz fundamental sequence operation
preserves `OT_B`.  As in the completed Isabelle development, the induction is
strengthened simultaneously with the `G`-control part of Buchholz's Lemma 3.6;
that invariant is needed in the modified A23 tower branch.
-/

namespace PSS

private theorem leBT_refl_bc (a : BT) : leBT a a = true := by
  simp [leBT]

private theorem leBT_of_less_bc {a b : BT} (h : lessBT a b = true) :
    leBT a b = true := by
  simp [leBT, h]

private theorem leBT_trans_bc (a b c : BT)
    (hab : leBT a b = true) (hbc : leBT b c = true) :
    leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab hbc ⊢
  rcases hab with hab | rfl
  · rcases hbc with hbc | rfl
    · exact Or.inl (lessBT_linear_trans a b c hab hbc)
    · exact Or.inl hab
  · exact hbc

private theorem le_less_trans_bc {a b c : BT}
    (hab : leBT a b = true) (hbc : lessBT b c = true) :
    lessBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab
  rcases hab with hab | rfl
  · exact lessBT_linear_trans a b c hab hbc
  · exact hbc

private theorem less_le_trans_bc {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) :
    lessBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hbc
  rcases hbc with hbc | rfl
  · exact lessBT_linear_trans a b c hab hbc
  · exact hab

private theorem leBT_antisymm_bc {a b : BT}
    (hab : leBT a b = true) (hba : leBT b a = true) : a = b := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab hba
  rcases hab with hab | hab
  · rcases hba with hba | hba
    · have := lessBT_linear_trans a b a hab hba
      have htf : true = false := this.symm.trans (lessBT_linear_irrefl a)
      exact (Bool.noConfusion htf)
    · exact hba.symm
  · exact hab

private theorem leBT_total_bc (a b : BT) :
    leBT a b = true ∨ leBT b a = true := by
  rcases lessBT_linear_trichotomy a b with h | rfl | h
  · exact Or.inl (leBT_of_less_bc h)
  · exact Or.inl (leBT_refl_bc _)
  · exact Or.inr (leBT_of_less_bc h)

private theorem BZero_le_bc (a : BT) : leBT BZero a = true := by
  rcases a with ⟨ps⟩
  cases ps <;> simp [BZero, leBT, lessBT, lessBPList]

/-! ## Finite `G`-set infrastructure -/

private def setLeBC (M N : Set BT) : Prop :=
  ∀ x, x ∈ M → ∃ y, y ∈ N ∧ leBT x y = true

def triGBC (z b a : BT) : Prop :=
  ∀ u c, leBT b c = true → leBT c a = true →
    setLeBC (GBT u b) (GBT u c ∪ GBT u z ∪ {BZero})

private theorem setLe_subset_bc {M N : Set BT} (h : M ⊆ N) :
    setLeBC M N := by
  intro x hx
  exact ⟨x, h hx, leBT_refl_bc x⟩

private theorem setLe_widen_bc {M N N' : Set BT}
    (hMN : setLeBC M N) (hNN' : N ⊆ N') : setLeBC M N' := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hMN x hx
  exact ⟨y, hNN' hy, hxy⟩

private theorem setLe_union_bc {M₁ M₂ N : Set BT}
    (h₁ : setLeBC M₁ N) (h₂ : setLeBC M₂ N) :
    setLeBC (M₁ ∪ M₂) N := by
  intro x hx
  rcases hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

private theorem gatherBPList_append_bc (u : ℕ∞) (as bs : List BP) :
    gatherBPList u (as ++ bs) = gatherBPList u as ++ gatherBPList u bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [gatherBPList, ih, List.append_assoc]

private theorem gatherBT_add_bc (u : ℕ∞) (a b : BT) :
    GBT u (addBT a b) = GBT u a ∪ GBT u b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  ext x
  simp [GBT, addBT, gatherBT, gatherBPList_append_bc]

private theorem gatherBT_Dprin_bc (u v : ℕ∞) (b : BT) :
    GBT u (Dprin v b) =
      if u ≤ v then ({b} ∪ GBT u b) else ∅ := by
  ext x
  by_cases huv : u ≤ v <;>
    simp [GBT, Dprin, gatherBT, gatherBPList, gatherBP, huv]

private theorem gatherBT_num_subset_zero_bc (u : ℕ∞) (n : ℕ) :
    GBT u (numBT n) ⊆ {BZero} := by
  intro x hx
  induction n with
  | zero => simp [GBT, numBT, gatherBT, gatherBPList] at hx
  | succ n ih =>
      rw [numBT, List.replicate_succ] at hx
      simp only [GBT, gatherBT, gatherBPList, List.contains_append,
        Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · by_cases hu : u ≤ 0
        · simpa [gatherBP, hu, BZero, gatherBT, gatherBPList] using hx
        · simp [gatherBP, hu] at hx
      · apply ih
        simpa [GBT, numBT, gatherBT] using hx

private theorem gatherBT_dfree_index_bc {u v : ℕ∞} {z : BT}
    (huv : u ≤ v) : z ∈ GBT u (Dprin v z) := by
  rw [gatherBT_Dprin_bc, if_pos huv]
  exact Or.inl rfl

mutual
  private theorem mem_gatherBT_weight_bc (u : ℕ∞) (x : BT) :
      ∀ t : BT, x ∈ gatherBT u t → btWeight x < btWeight t
    | .trm ps, hx => by
        have hlt := mem_gatherBPList_weight_bc u x ps (by
          simpa [gatherBT] using hx)
        simp only [btWeight]
        omega

  private theorem mem_gatherBP_weight_bc (u : ℕ∞) (x : BT) :
      ∀ p : BP, x ∈ gatherBP u p → btWeight x < bpWeight p
    | .db v b, hx => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [bpWeight]
          · have hlt := mem_gatherBT_weight_bc u x b hx
            simp only [bpWeight]
            omega
        · simp [gatherBP, huv] at hx

  private theorem mem_gatherBPList_weight_bc (u : ℕ∞) (x : BT) :
      ∀ ps : List BP, x ∈ gatherBPList u ps → btWeight x < bpListWeight ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx
        rcases hx with hx | hx
        · have hlt := mem_gatherBP_weight_bc u x p hx
          simp only [bpListWeight]
          omega
        · have hlt := mem_gatherBPList_weight_bc u x ps hx
          simp only [bpListWeight]
          omega
end

private theorem GBT_weight_lt_bc {u : ℕ∞} {x t : BT}
    (hx : x ∈ GBT u t) : btWeight x < btWeight t := by
  apply mem_gatherBT_weight_bc u x t
  simpa [GBT] using hx

mutual
  private theorem gatherBT_trans_mem_bc (u : ℕ∞) (y : BT) :
      ∀ t x : BT, x ∈ gatherBT u t → y ∈ gatherBT u x →
        y ∈ gatherBT u t
    | .trm ps, x, hx, hy =>
        gatherBPList_trans_mem_bc u y ps x hx hy

  private theorem gatherBP_trans_mem_bc (u : ℕ∞) (y : BT) :
      ∀ p : BP, ∀ x : BT, x ∈ gatherBP u p → y ∈ gatherBT u x →
        y ∈ gatherBP u p
    | .db v b, x, hx, hy => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true,
            List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr hy
          · exact Or.inr (gatherBT_trans_mem_bc u y b x hx hy)
        · simp [gatherBP, huv] at hx

  private theorem gatherBPList_trans_mem_bc (u : ℕ∞) (y : BT) :
      ∀ ps : List BP, ∀ x : BT,
        x ∈ gatherBPList u ps → y ∈ gatherBT u x →
          y ∈ gatherBPList u ps
    | [], x, hx, _ => by simp [gatherBPList] at hx
    | p :: ps, x, hx, hy => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_trans_mem_bc u y p x hx hy)
        · exact Or.inr (gatherBPList_trans_mem_bc u y ps x hx hy)
end

private theorem GBT_trans_bc {u : ℕ∞} {x t : BT}
    (hx : x ∈ GBT u t) : GBT u x ⊆ GBT u t := by
  intro y hy
  have hout := gatherBT_trans_mem_bc u y t x
    (by simpa [GBT] using hx) (by simpa [GBT] using hy)
  simpa [GBT] using hout

mutual
  private theorem gatherBT_antitone_mem_bc {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ t : BT, x ∈ gatherBT v t → x ∈ gatherBT u t
    | .trm ps, hx => gatherBPList_antitone_mem_bc huv x ps hx

  private theorem gatherBP_antitone_mem_bc {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ p : BP, x ∈ gatherBP v p → x ∈ gatherBP u p
    | .db w b, hx => by
        have hvw : v ≤ w := by
          by_contra hn
          simp [gatherBP, hn] at hx
        have huw : u ≤ w := huv.trans hvw
        simp only [gatherBP, hvw, huw, decide_true, if_true,
          List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (gatherBT_antitone_mem_bc huv x b hx)

  private theorem gatherBPList_antitone_mem_bc {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ ps : List BP,
        x ∈ gatherBPList v ps → x ∈ gatherBPList u ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_antitone_mem_bc huv x p hx)
        · exact Or.inr (gatherBPList_antitone_mem_bc huv x ps hx)
end

private theorem GBT_antitone_bc {u v : ℕ∞} (huv : u ≤ v) (t : BT) :
    GBT v t ⊆ GBT u t := by
  intro x hx
  have hout := gatherBT_antitone_mem_bc huv x t (by simpa [GBT] using hx)
  simpa [GBT] using hout

/-! Buchholz Lemma 3.4: `G`-control transfers the ordinal side condition. -/

theorem G_control_bc {z b a : BT} {u : ℕ∞}
    (htri : triGBC z b a) (hba : leBT b a = true)
    (hGa : ∀ x ∈ GBT u a, lessBT x a = true)
    (hGz : ∀ x ∈ GBT u z, lessBT x b = true) :
    ∀ x ∈ GBT u b, lessBT x b = true := by
  have bad : ∀ x, x ∈ GBT u b → leBT b x = true → False := by
    intro x hx hbx
    generalize hn : btWeight x = n
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
        have hxa : lessBT x a = true := by
          obtain ⟨y, hy, hxy⟩ := htri u a hba (leBT_refl_bc a) x hx
          rcases hy with (hya | hyz) | hy0
          · exact le_less_trans_bc hxy (hGa y hya)
          · have hyb := hGz y hyz
            have hxb := le_less_trans_bc hxy hyb
            have hbb := le_less_trans_bc hbx hxb
            simp [lessBT_linear_irrefl] at hbb
          · have hyzero : y = BZero := hy0
            subst y
            have hxzero : x = BZero :=
              leBT_antisymm_bc hxy (BZero_le_bc x)
            subst x
            have hbzero : b = BZero :=
              leBT_antisymm_bc hbx (BZero_le_bc b)
            subst b
            simp [GBT, BZero, gatherBT, gatherBPList] at hx
        obtain ⟨y, hy, hxy⟩ :=
          htri u x hbx (leBT_of_less_bc hxa) x hx
        rcases hy with (hyx | hyz) | hy0
        · have hyb : y ∈ GBT u b := GBT_trans_bc hx hyx
          have hyw : btWeight y < btWeight x := GBT_weight_lt_bc hyx
          have hby : leBT b y = true := leBT_trans_bc b x y hbx hxy
          exact ih (btWeight y) (by omega) y hyb hby rfl
        · have hyb := hGz y hyz
          have hxb := le_less_trans_bc hxy hyb
          have hbb := le_less_trans_bc hbx hxb
          simp [lessBT_linear_irrefl] at hbb
        · have hyzero : y = BZero := hy0
          subst y
          have hxzero : x = BZero :=
            leBT_antisymm_bc hxy (BZero_le_bc x)
          subst x
          have hbzero : b = BZero :=
            leBT_antisymm_bc hbx (BZero_le_bc b)
          subst b
          simp [GBT, BZero, gatherBT, gatherBPList] at hx
  intro x hx
  rcases lessBT_linear_trichotomy x b with hxb | rfl | hbx
  · exact hxb
  · exact (bad x hx (leBT_refl_bc x)).elim
  · exact (bad x hx (leBT_of_less_bc hbx)).elim

/-! ## Sandwich decompositions and congruence of `triGBC` -/

private theorem lessBP_single_bc (p q : BP) :
    lessBT (.trm [p]) (.trm [q]) = lessBP p q := by
  simp [lessBT, lessBPList]

private theorem lessBP_asymm_bc {p q : BP}
    (hpq : lessBP p q = true) (hqp : lessBP q p = true) : False := by
  have hpq' : lessBT (.trm [p]) (.trm [q]) = true := by
    simpa [lessBP_single_bc] using hpq
  have hqp' : lessBT (.trm [q]) (.trm [p]) = true := by
    simpa [lessBP_single_bc] using hqp
  have h := lessBT_linear_trans (.trm [p]) (.trm [q]) (.trm [p]) hpq' hqp'
  simp [lessBT_linear_irrefl] at h

private theorem lessBP_irrefl_bc (p : BP) : lessBP p p = false := by
  have h := lessBT_linear_irrefl (.trm [p])
  simpa [lessBP_single_bc] using h

private theorem leBT_cons_iff_bc (p q : BP) (ps qs : List BP) :
    leBT (.trm (p :: ps)) (.trm (q :: qs)) = true ↔
      lessBP p q = true ∨
        (p = q ∧ leBT (.trm ps) (.trm qs) = true) := by
  simp only [leBT, lessBT, lessBPList, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, BT.trm.injEq, List.cons.injEq]
  tauto

theorem sandwich_prefix_bc (ps xs ys : List BP) (c : BT)
    (h₁ : leBT (.trm (ps ++ xs)) c = true)
    (h₂ : leBT c (.trm (ps ++ ys)) = true) :
    ∃ cs, c = .trm (ps ++ cs) ∧
      leBT (.trm xs) (.trm cs) = true ∧
      leBT (.trm cs) (.trm ys) = true := by
  induction ps generalizing c with
  | nil =>
      rcases c with ⟨cs⟩
      exact ⟨cs, rfl, by simpa using h₁, by simpa using h₂⟩
  | cons p ps ih =>
      rcases c with ⟨cs⟩
      cases cs with
      | nil => simp [leBT, lessBT, lessBPList] at h₁
      | cons q qs =>
          have hs₁ : lessBP p q = true ∨
              (p = q ∧ leBT (.trm (ps ++ xs)) (.trm qs) = true) := by
            exact (leBT_cons_iff_bc p q (ps ++ xs) qs).mp h₁
          have hs₂ : lessBP q p = true ∨
              (q = p ∧ leBT (.trm qs) (.trm (ps ++ ys)) = true) := by
            exact (leBT_cons_iff_bc q p qs (ps ++ ys)).mp h₂
          have hpq : p = q := by
            rcases hs₁ with hpq | ⟨rfl, _⟩
            · rcases hs₂ with hqp | ⟨hqp, _⟩
              · exact (lessBP_asymm_bc hpq hqp).elim
              · exact hqp.symm
            · rfl
          subst q
          have hlo : leBT (.trm (ps ++ xs)) (.trm qs) = true := by
            rcases hs₁ with hp | ⟨_, hp⟩
            · have hirr := lessBP_irrefl_bc p
              rw [hirr] at hp
              contradiction
            · exact hp
          have hhi : leBT (.trm qs) (.trm (ps ++ ys)) = true := by
            rcases hs₂ with hp | ⟨_, hp⟩
            · have hirr := lessBP_irrefl_bc p
              rw [hirr] at hp
              contradiction
            · exact hp
          obtain ⟨ds, hq, hdx, hdy⟩ := ih (.trm qs) hlo hhi
          injection hq with hqs
          subst qs
          exact ⟨ds, rfl, hdx, hdy⟩

theorem sandwich_Dprin_bc {v : ℕ∞} {x y c : BT}
    (h₁ : leBT (Dprin v x) c = true)
    (h₂ : leBT c (Dprin v y) = true) :
    ∃ c₀ cs, c = .trm (.db v c₀ :: cs) ∧
      leBT x c₀ = true ∧ leBT c₀ y = true := by
  rcases c with ⟨cs⟩
  cases cs with
  | nil => simp [Dprin, leBT, lessBT, lessBPList] at h₁
  | cons p ps =>
      rcases p with ⟨w, c₀⟩
      have hs₁ : lessBP (.db v x) (.db w c₀) = true ∨
          ((.db v x : BP) = .db w c₀ ∧ leBT BZero (.trm ps) = true) := by
        exact (leBT_cons_iff_bc (.db v x) (.db w c₀) [] ps).mp
          (by simpa [Dprin, BZero] using h₁)
      have hs₂ : lessBP (.db w c₀) (.db v y) = true ∨
          ((.db w c₀ : BP) = .db v y ∧ leBT (.trm ps) BZero = true) := by
        exact (leBT_cons_iff_bc (.db w c₀) (.db v y) ps []).mp
          (by simpa [Dprin, BZero] using h₂)
      have hvw : v ≤ w := by
        rcases hs₁ with h | ⟨h, _⟩
        · simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at h
          rcases h with h | ⟨rfl, _⟩
          · exact h.le
          · exact le_rfl
        · cases h
          exact le_rfl
      have hwv : w ≤ v := by
        rcases hs₂ with h | ⟨h, _⟩
        · simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at h
          rcases h with h | ⟨rfl, _⟩
          · exact h.le
          · exact le_rfl
        · cases h
          exact le_rfl
      have hw : w = v := le_antisymm hwv hvw
      subst w
      have hxc : leBT x c₀ = true := by
        rcases hs₁ with h | ⟨h, _⟩
        · have hlt : lessBT x c₀ = true := by
            simpa [lessBP] using h
          exact leBT_of_less_bc hlt
        · have hxy : x = c₀ := by injection h
          subst c₀
          exact leBT_refl_bc _
      have hcy : leBT c₀ y = true := by
        rcases hs₂ with h | ⟨h, _⟩
        · have hlt : lessBT c₀ y = true := by
            simpa [lessBP] using h
          exact leBT_of_less_bc hlt
        · have hxy : c₀ = y := by injection h
          subst y
          exact leBT_refl_bc _
      exact ⟨c₀, ps, rfl, hxc, hcy⟩

private theorem triG_add_bc {z b₀ b : BT} (ps : List BP)
    (htri : triGBC z b₀ b) :
    triGBC z (addBT (.trm ps) b₀) (addBT (.trm ps) b) := by
  intro u c hlo hhi
  rcases b₀ with ⟨bs₀⟩
  rcases b with ⟨bs⟩
  obtain ⟨cs, hc, h₀c, hcb⟩ := sandwich_prefix_bc ps bs₀ bs c
    (by simpa [addBT] using hlo) (by simpa [addBT] using hhi)
  have hprefix : setLeBC (GBT u (.trm ps))
      (GBT u c ∪ GBT u z ∪ {BZero}) :=
    setLe_subset_bc (by
      intro x hx
      have hxc : x ∈ GBT u c := by
        rw [hc, show .trm (ps ++ cs) = addBT (.trm ps) (.trm cs) by rfl,
          gatherBT_add_bc]
        exact Or.inl hx
      exact Or.inl (Or.inl hxc))
  have htail₀ := htri u (.trm cs) h₀c hcb
  have htail : setLeBC (GBT u (.trm bs₀))
      (GBT u c ∪ GBT u z ∪ {BZero}) :=
    setLe_widen_bc htail₀ (by
      intro x hx
      rcases hx with (hxc | hxz) | hx0
      · have hxc' : x ∈ GBT u c := by
          rw [hc, show .trm (ps ++ cs) = addBT (.trm ps) (.trm cs) by rfl,
            gatherBT_add_bc]
          exact Or.inr hxc
        exact Or.inl (Or.inl hxc')
      · exact Or.inl (Or.inr hxz)
      · exact Or.inr hx0)
  rw [gatherBT_add_bc]
  exact setLe_union_bc hprefix htail

private theorem triG_Dprin_bc {z b₀ b : BT} (v : ℕ∞)
    (htri : triGBC z b₀ b) :
    triGBC z (Dprin v b₀) (Dprin v b) := by
  intro u c hlo hhi
  obtain ⟨c₀, cs, hc, h₀c, hcb⟩ := sandwich_Dprin_bc hlo hhi
  by_cases huv : u ≤ v
  · rw [gatherBT_Dprin_bc, if_pos huv]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨c₀, by
        left
        rw [hc]
        simp [GBT, gatherBT, gatherBPList, gatherBP, huv], h₀c⟩
    · obtain ⟨y, hy, hxy⟩ := htri u c₀ h₀c hcb x hx
      refine ⟨y, ?_, hxy⟩
      rcases hy with (hyc | hyz) | hy0
      · have hyc' : y ∈ GBT u c := by
          have hc₀mem : c₀ ∈ GBT u c := by
            rw [hc]
            simp [GBT, gatherBT, gatherBPList, gatherBP, huv]
          exact GBT_trans_bc hc₀mem hyc
        exact Or.inl (Or.inl hyc')
      · exact Or.inl (Or.inr hyz)
      · exact Or.inr hy0
  · rw [gatherBT_Dprin_bc, if_neg huv]
    intro x hx
    exact hx.elim

/-! ## Monotonicity and the lower bound on `T_w` domains -/

private theorem operB_mono_below_bc (a z₁ z₂ : BT) (w : ℕ)
    (htag : domTag a = .below w)
    (hz₁ : z₁ ∈ TBv (w : ℕ∞)) (hz₂ : z₂ ∈ TBv (w : ℕ∞))
    (hzlt : lessBT z₁ z₂ = true) :
    lessBT (operB a z₁) (operB a z₂) = true := by
  generalize hn : btWeight a = n
  induction n using Nat.strong_induction_on generalizing a w z₁ z₂ with
  | h n ih =>
      rcases a with ⟨xs⟩
      cases xs with
      | nil => simp [domTag, domTagList] at htag
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, b⟩
              by_cases hb : b = BZero
              · subst b
                by_cases hv₀ : v = 0
                · subst v
                  simp [domTag, domTagList, domTagBP, BZero] at htag
                · by_cases hvtop : v = ⊤
                  · subst v
                    simp [domTag, domTagList, domTagBP, BZero, hv₀] at htag
                  · simpa [operB, bOperCore, BZero, hv₀, hvtop] using hzlt
              · cases hdb : domTag b with
                | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | below u =>
                    by_cases hvu : v ≤ (u : ℕ∞)
                    · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag
                    · have huw : u = w := by
                        simpa [domTag, domTagList, domTagBP, hb, hdb, hvu] using htag
                      subst w
                      have hbn : btWeight b < n := by
                        rw [← hn]
                        simp [btWeight, bpListWeight, bpWeight]
                        omega
                      have hrec := ih (btWeight b) hbn b z₁ z₂ u hdb hz₁ hz₂ hzlt rfl
                      simpa [operB, bOperCore, Dprin, hb, hdb, hvu,
                        lessBT, lessBPList, lessBP, hrec]
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < n := by
                rw [← hn]
                simp [btWeight, bpListWeight]
              have htagtail : domTag (.trm (q :: qs)) = .below w := by
                simpa [domTag, domTagList] using htag
              have hrec := ih (btWeight (.trm (q :: qs))) htailn
                (.trm (q :: qs)) z₁ z₂ w htagtail hz₁ hz₂ hzlt rfl
              have hadd := addBT_lt_right_bf (.trm [p])
                (operB (.trm (q :: qs)) z₁)
                (operB (.trm (q :: qs)) z₂) hrec
              simpa [operB, bOperCore, addBT] using hadd

private theorem OT_tag_below_head_bc (p : BP) (ps : List BP) (w : ℕ)
    (hot : isOT_BT (.trm (p :: ps)) = true)
    (htag : domTag (.trm (p :: ps)) = .below w) :
    ∃ h c, p = .db h c ∧ (w : ℕ∞) < h := by
  let ys := p :: ps
  have hne : ys ≠ [] := by simp [ys]
  cases hlast : ys.getLast hne with
  | db hl cl =>
      have hotsplit : isOT_BPList ys = true ∧ descP ys = true := by
        simpa [ys, isOT_BT] using hot
      have htaglp : domTagBP (.db hl cl) = .below w := by
        rw [← domTag_snoc_bf ys.dropLast (.db hl cl)]
        have hdecomp : ys.dropLast ++ [.db hl cl] = ys := by
          rw [← hlast]
          exact List.dropLast_append_getLast hne
        rw [hdecomp]
        simpa [ys] using htag
      have hwhl : (w : ℕ∞) < hl := domTagBP_below_head_bf htaglp
      rcases p with ⟨hp, cp⟩
      have hle : leBT (.trm [.db hl cl]) (.trm [.db hp cp]) = true := by
        have hle₀ := descP_last_head_bf (.db hp cp) ps hotsplit.2
        simpa [ys, hlast] using hle₀
      have hhlp : hl ≤ hp := leBT_single_index_bf hl hp cl cp hle
      exact ⟨hp, cp, rfl, hwhl.trans_le hhlp⟩

private theorem operB_lowerbound_below_bc (a z : BT) (w : ℕ)
    (hot : isOT_BT a = true) (htag : domTag a = .below w)
    (hz : z ∈ TBv (w : ℕ∞)) : leBT z (operB a z) = true := by
  rcases a with ⟨xs⟩
  cases xs with
  | nil => simp [domTag, domTagList] at htag
  | cons p ps =>
      cases ps with
      | nil =>
          rcases p with ⟨v, b⟩
          by_cases hb : b = BZero
          · subst b
            by_cases hv₀ : v = 0
            · subst v
              simp [domTag, domTagList, domTagBP, BZero] at htag
            · by_cases hvtop : v = ⊤
              · subst v
                simp [domTag, domTagList, domTagBP, BZero, hv₀] at htag
              · simpa [operB, bOperCore, BZero, hv₀, hvtop] using
                  leBT_refl_bc z
          · cases hdb : domTag b with
            | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | zeroOnly => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | naturals => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | below u =>
                by_cases hvu : v ≤ (u : ℕ∞)
                · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag
                · have huw : u = w := by
                    simpa [domTag, domTagList, domTagBP, hb, hdb, hvu] using htag
                  subst w
                  have huv : (u : ℕ∞) < v := lt_of_not_ge hvu
                  apply leBT_of_less_bc
                  simpa [operB, bOperCore, Dprin, hb, hdb, hvu] using
                    (TBv_lt_head_bf (z := z) (c := operB b z)
                      (rest := []) hz huv)
      | cons q qs =>
          obtain ⟨h, c, hp, hwh⟩ :=
            OT_tag_below_head_bc p (q :: qs) w hot htag
          subst p
          rcases hopen : operB (.trm (q :: qs)) z with ⟨rs⟩
          apply leBT_of_less_bc
          have hlt := TBv_lt_head_bf (z := z) (c := c) (rest := rs) hz hwh
          have hop : operB (.trm (.db h c :: q :: qs)) z =
              addBT (.trm [.db h c]) (operB (.trm (q :: qs)) z) := by
            simp [operB, bOperCore]
          rw [hop, hopen]
          simpa [addBT] using hlt

/-! ## Boolean normal-form utilities used by the master induction -/

private theorem BZero_lt_of_ne_bc {a : BT} (hne : a ≠ BZero) :
    lessBT BZero a = true := by
  rcases a with ⟨ps⟩
  cases ps with
  | nil => exact (hne rfl).elim
  | cons p ps => simp [BZero, lessBT, lessBPList]

private theorem NatSet_mem_TBv_bc {z : BT} {w : ℕ}
    (hz : z ∈ NatSet) : z ∈ TBv (w : ℕ∞) := by
  rcases hz with ⟨n, rfl⟩
  simp [numBT, TBv, BZero]

private theorem xseq_mem_TBv_bc (b : BT) (w i : ℕ) :
    xseq b (w : ℕ∞) i ∈ TBv (w : ℕ∞) := by
  cases i with
  | zero => simp [xseq, bOperCore, Dprin, TBv]
  | succ i => simp [xseq, bOperCore, Dprin, TBv]

private theorem xseq_zero_bc (b : BT) (w : ℕ) :
    xseq b (w : ℕ∞) 0 = Dprin (w : ℕ∞) BZero := by
  simp [xseq, bOperCore]

private theorem xseq_succ_bc (b : BT) (w i : ℕ) :
    xseq b (w : ℕ∞) (i + 1) =
      Dprin (w : ℕ∞) (operB b (xseq b (w : ℕ∞) i)) := by
  simp [xseq, bOperCore, operB]

private theorem multBT_single_bc (q : BP) (n : ℕ) :
    multBT (.trm [q]) n = .trm (List.replicate n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [multBT, ih]
      simp [addBT, List.replicate_succ']

private theorem descP_replicate_bc (q : BP) (n : ℕ) :
    descP (List.replicate n q) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.replicate_succ] at ih ⊢
          simpa [descP, leBT_refl_bc] using ih

private theorem isOT_BPList_replicate_bc (q : BP) (n : ℕ)
    (hq : isOT_BP q = true) :
    isOT_BPList (List.replicate n q) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, isOT_BPList, hq, ih]

private theorem isOT_replicate_bc (q : BP) (n : ℕ)
    (hq : isOT_BP q = true) :
    isOT_BT (.trm (List.replicate n q)) = true := by
  simp [isOT_BT, isOT_BPList_replicate_bc q n hq,
    descP_replicate_bc]

private theorem dfree_BPList_replicate_bc (q : BP) (n : ℕ)
    (hq : dfree_BP q = true) :
    dfree_BPList (List.replicate n q) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dfree_BPList, hq, ih]

private theorem dfree_replicate_bc (q : BP) (n : ℕ)
    (hq : dfree_BP q = true) :
    dfree_BT (.trm (List.replicate n q)) = true := by
  simp [dfree_BT, dfree_BPList_replicate_bc q n hq]

private theorem gatherBT_replicate_succ_bc (u : ℕ∞) (q : BP) (n : ℕ) :
    GBT u (.trm (List.replicate (n + 1) q)) = GBT u (.trm [q]) := by
  ext x
  induction n with
  | zero => simp [GBT, gatherBT, gatherBPList]
  | succ n ih =>
      rw [Nat.succ_add, List.replicate_succ]
      simp only [GBT, gatherBT, gatherBPList, Set.mem_setOf_eq,
        List.contains_append, Bool.or_eq_true]
      have ih' := ih
      simp only [GBT, gatherBT, Set.mem_setOf_eq] at ih'
      have ih'' : (gatherBPList u (List.replicate (n + 1) q)).contains x = true ↔
          (gatherBP u q).contains x = true := by
        simpa [gatherBPList] using ih'
      tauto

private theorem leBT_single_replicate_succ_bc (q : BP) (n : ℕ) :
    leBT (.trm [q]) (.trm (List.replicate (n + 1) q)) = true := by
  cases n with
  | zero => exact leBT_refl_bc _
  | succ n =>
      rw [Nat.succ_add, List.replicate_succ]
      apply (leBT_cons_iff_bc q q [] (List.replicate (n + 1) q)).mpr
      exact Or.inr ⟨rfl, BZero_le_bc _⟩

private theorem isOT_num_bc (n : ℕ) : isOT_BT (numBT n) = true := by
  apply isOT_replicate_bc
  rfl

private theorem dfree_num_bc (n : ℕ) : dfree_BT (numBT n) = true := by
  apply dfree_replicate_bc
  simp [dfree_BP, BZero, dfree_BT, dfree_BPList]

private theorem GBT_TBv_small_empty_bc {z : BT} {w : ℕ} {v : ℕ∞}
    (hz : z ∈ TBv (w : ℕ∞)) (hwv : (w : ℕ∞) < v) :
    GBT v z = ∅ := by
  rcases z with ⟨ps⟩
  have hall : ∀ p ∈ ps,
      match p with | .db h _ => h ≤ (w : ℕ∞) := by
    intro p hp
    have hallb : ∀ p ∈ ps,
        (match p with | .db h _ => decide (h ≤ (w : ℕ∞))) = true := by
      simpa [TBv] using hz
    rcases p with ⟨h, a⟩
    simpa using hallb (.db h a) hp
  ext x
  have hgAux : ∀ qs : List BP,
      (∀ p ∈ qs, match p with | .db h _ => h ≤ (w : ℕ∞)) →
      gatherBPList v qs = [] := by
    intro qs hqs
    induction qs with
    | nil => rfl
    | cons p qs ih =>
        rcases p with ⟨h, b⟩
        have hhw : h ≤ (w : ℕ∞) := hqs (.db h b) (by simp)
        have hhv : h < v := hhw.trans_lt hwv
        have hnv : ¬v ≤ h := not_le_of_gt hhv
        have iht := ih (by
          intro q hq
          exact hqs q (by simp [hq]))
        simp [gatherBPList, gatherBP, hnv, iht]
  have hg : gatherBPList v ps = [] := hgAux ps hall
  simp [GBT, gatherBT, hg]

private theorem tag_empty_eq_zero_bc (a : BT)
    (htag : domTag a = .empty) : a = BZero := by
  generalize hn : btWeight a = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
      rcases a with ⟨ps⟩
      cases ps with
      | nil => rfl
      | cons p ps =>
          cases ps with
          | cons q qs =>
              have htailn : btWeight (.trm (q :: qs)) < n := by
                rw [← hn]
                simp [btWeight, bpListWeight]
              have htailtag : domTag (.trm (q :: qs)) = .empty := by
                simpa [domTag, domTagList] using htag
              have := ih _ htailn (.trm (q :: qs)) htailtag rfl
              simp [BZero] at this
          | nil =>
              rcases p with ⟨v, b⟩
              by_cases hb : b = BZero
              · subst b
                by_cases hv₀ : v = 0
                · subst v
                  simp [domTag, domTagList, domTagBP, BZero] at htag
                · by_cases hvtop : v = ⊤
                  · subst v
                    simp [domTag, domTagList, domTagBP, BZero, hv₀] at htag
                  · simp [domTag, domTagList, domTagBP, BZero, hv₀, hvtop] at htag
              · cases hdb : domTag b with
                | empty =>
                    have hbn : btWeight b < n := by
                      rw [← hn]
                      simp [btWeight, bpListWeight, bpWeight]
                      omega
                    have := ih _ hbn b hdb rfl
                    exact (hb this).elim
                | zeroOnly =>
                    simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | naturals =>
                    simp [domTag, domTagList, domTagBP, hb, hdb] at htag
                | below u =>
                    by_cases hvu : v ≤ (u : ℕ∞) <;>
                      simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag

private theorem operB_nonzero_naturals_bc (a z : BT)
    (htag : domTag a = .naturals) : operB a z ≠ BZero := by
  rcases a with ⟨ps⟩
  cases ps with
  | nil => simp [domTag, domTagList] at htag
  | cons p ps =>
      cases ps with
      | cons q qs =>
          rcases htail : bOperCore (.list (q :: qs) z) with ⟨rs⟩
          simp [operB, bOperCore, addBT, BZero, htail]
      | nil =>
          rcases p with ⟨v, b⟩
          by_cases hb : b = BZero
          · subst b
            by_cases hv₀ : v = 0
            · subst v
              simp [domTag, domTagList, domTagBP, BZero] at htag
            · by_cases hvtop : v = ⊤
              · subst v
                simp [operB, bOperCore, Dprin, BZero]
              · simp [domTag, domTagList, domTagBP, BZero, hv₀, hvtop] at htag
          · cases hdb : domTag b with
            | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
            | zeroOnly =>
                have hb' : b ≠ BT.trm [] := by simpa [BZero] using hb
                simp [operB, bOperCore, Dprin, hb', beq_iff_eq, hdb,
                  multBT_single_bc, BZero]
            | naturals =>
                have hb' : b ≠ BT.trm [] := by simpa [BZero] using hb
                simp [operB, bOperCore, Dprin, hb', beq_iff_eq, hdb, BZero]
            | below w =>
                by_cases hvw : v ≤ (w : ℕ∞)
                · have hb' : b ≠ BT.trm [] := by simpa [BZero] using hb
                  simp [operB, bOperCore, Dprin, hb', beq_iff_eq, hdb, hvw, BZero]
                · simp [domTag, domTagList, domTagBP, hb, hdb, hvw] at htag

private theorem triG_zero_to_bc {x b z : BT}
    (htri : triGBC BZero x b) : triGBC z x b := by
  intro u c hxc hcb
  apply setLe_widen_bc (htri u c hxc hcb)
  intro y hy
  rcases hy with (hyc | hyzeroG) | hyzero
  · exact Or.inl (Or.inl hyc)
  · simp [GBT, BZero, gatherBT, gatherBPList] at hyzeroG
  · exact Or.inr hyzero

private theorem triG_replicate_succ_bc {z x b : BT} (v : ℕ∞) (n : ℕ)
    (htri : triGBC z (Dprin v x) (Dprin v b)) :
    triGBC z (.trm (List.replicate (n + 1) (.db v x))) (Dprin v b) := by
  intro u c hrc hcb
  have hhead : leBT (Dprin v x) c = true :=
    leBT_trans_bc _ _ _ (leBT_single_replicate_succ_bc (.db v x) n) hrc
  have hout := htri u c hhead hcb
  simpa [gatherBT_replicate_succ_bc] using hout

private theorem close_Dprin_bc (v : ℕ∞) (y : BT)
    (hoty : isOT_BT y = true) (hdfy : dfree_BT y = true)
    (hGy : ∀ x ∈ GBT v y, lessBT x y = true) (hvfin : v ≠ ⊤) :
    isOT_BT (Dprin v y) = true ∧ dfree_BT (Dprin v y) = true := by
  constructor
  · simp only [Dprin, isOT_BT, isOT_BPList, isOT_BP,
      Bool.and_eq_true, descP]
    refine ⟨⟨⟨hoty, ?_⟩, trivial⟩, trivial⟩
    simpa [GBT] using hGy
  · simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hvfin, hdfy]

private theorem close_replicate_succ_bc (v : ℕ∞) (y : BT) (n : ℕ)
    (hoty : isOT_BT y = true) (hdfy : dfree_BT y = true)
    (hGy : ∀ x ∈ GBT v y, lessBT x y = true) (hvfin : v ≠ ⊤) :
    isOT_BT (.trm (List.replicate (n + 1) (.db v y))) = true ∧
      dfree_BT (.trm (List.replicate (n + 1) (.db v y))) = true := by
  have hqOT : isOT_BP (.db v y) = true := by
    simpa [isOT_BP, GBT] using And.intro hoty (by simpa [GBT] using hGy)
  have hqDF : dfree_BP (.db v y) = true := by
    simp [dfree_BP, hvfin, hdfy]
  exact ⟨isOT_replicate_bc _ _ hqOT, dfree_replicate_bc _ _ hqDF⟩

/-! The corrected A23 tower branch. -/

private theorem tower_case_bc (v : ℕ∞) (b z : BT) (w : ℕ)
    (hotb : isOT_BT b = true)
    (hbne : b ≠ BZero) (hdb : domTag b = .below w) (hvw : v ≤ (w : ℕ∞))
    (hGvb : ∀ x ∈ GBT v b, lessBT x b = true)
    (hIH : ∀ t, t ∈ TBv (w : ℕ∞) →
      triGBC t (operB b t) b ∧
        (isOT_BT t = true → dfree_BT t = true →
          isOT_BT (operB b t) = true ∧ dfree_BT (operB b t) = true)) :
    triGBC z
        (Dprin v (operB b (xseq b (w : ℕ∞) (numNat z))))
        (Dprin v b) ∧
      (isOT_BT z = true → dfree_BT z = true →
        isOT_BT (Dprin v (operB b (xseq b (w : ℕ∞) (numNat z)))) = true ∧
        dfree_BT (Dprin v (operB b (xseq b (w : ℕ∞) (numNat z)))) = true) := by
  have hxin : ∀ i, xseq b (w : ℕ∞) i ∈ TBv (w : ℕ∞) :=
    fun i => xseq_mem_TBv_bc b w i
  have htri : ∀ i, triGBC (xseq b (w : ℕ∞) i)
      (operB b (xseq b (w : ℕ∞) i)) b :=
    fun i => (hIH _ (hxin i)).1
  have hYlt : ∀ i, lessBT (operB b (xseq b (w : ℕ∞) i)) b = true := by
    intro i
    exact buchholz_fseq_descent b _ hotb hbne
      (Or.inl (by simpa [domB, hdb, BDom.toSet] using hxin i))
  have hYle : ∀ i, leBT (operB b (xseq b (w : ℕ∞) i)) b = true :=
    fun i => leBT_of_less_bc (hYlt i)
  have hxlow : ∀ i, leBT (xseq b (w : ℕ∞) i)
      (operB b (xseq b (w : ℕ∞) i)) = true :=
    fun i => operB_lowerbound_below_bc b _ w hotb hdb (hxin i)
  have hY₀ne : operB b (xseq b (w : ℕ∞) 0) ≠ BZero := by
    intro hzero
    have hxzero : xseq b (w : ℕ∞) 0 = BZero :=
      leBT_antisymm_bc (by simpa [hzero] using hxlow 0) (BZero_le_bc _)
    have hxne : xseq b (w : ℕ∞) 0 ≠ BZero := by
      simp [xseq_zero_bc, Dprin, BZero]
    exact hxne hxzero
  have hXmono : ∀ i, lessBT (xseq b (w : ℕ∞) i)
      (xseq b (w : ℕ∞) (i + 1)) = true := by
    intro i
    induction i with
    | zero =>
        have hzY : lessBT BZero (operB b (xseq b (w : ℕ∞) 0)) = true :=
          BZero_lt_of_ne_bc hY₀ne
        rw [xseq_zero_bc] at hzY
        rw [xseq_zero_bc, xseq_succ_bc, xseq_zero_bc]
        simpa [Dprin, lessBT, lessBPList, lessBP] using hzY
    | succ i ih =>
        have hYY := operB_mono_below_bc b
          (xseq b (w : ℕ∞) i) (xseq b (w : ℕ∞) (i + 1)) w
          hdb (hxin i) (hxin (i + 1)) ih
        change lessBT (xseq b (w : ℕ∞) (i + 1))
          (xseq b (w : ℕ∞) ((i + 1) + 1)) = true
        rw [xseq_succ_bc b w i, xseq_succ_bc b w (i + 1)]
        simpa [Dprin, lessBT, lessBPList, lessBP] using hYY
  have hYmono : ∀ i, lessBT (operB b (xseq b (w : ℕ∞) i))
      (operB b (xseq b (w : ℕ∞) (i + 1))) = true := by
    intro i
    exact operB_mono_below_bc b _ _ w hdb (hxin i) (hxin (i + 1)) (hXmono i)
  have hTI : ∀ i c u,
      leBT (operB b (xseq b (w : ℕ∞) i)) c = true →
      leBT c b = true →
      setLeBC (GBT u (operB b (xseq b (w : ℕ∞) i)))
        ({c} ∪ GBT u c ∪ {BZero}) := by
    intro i
    induction i with
    | zero =>
        intro c u hYc hcb
        apply setLe_widen_bc (htri 0 u c hYc hcb)
        intro y hy
        rcases hy with (hyc | hyX) | hyzero
        · exact Or.inl (Or.inr hyc)
        · have hyX₀ : y ∈ ({BZero} : Set BT) := by
            rw [xseq_zero_bc, gatherBT_Dprin_bc] at hyX
            split at hyX
            · simpa [GBT, BZero, gatherBT, gatherBPList] using hyX
            · contradiction
          exact Or.inr hyX₀
        · exact Or.inr hyzero
    | succ i ih =>
        intro c u hYc hcb
        have hmain := htri (i + 1) u c hYc hcb
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hmain x hx
        rcases hy with (hyc | hyX) | hyzero
        · exact ⟨y, Or.inl (Or.inr hyc), hxy⟩
        · have hparts : y = operB b (xseq b (w : ℕ∞) i) ∨
              y ∈ GBT u (operB b (xseq b (w : ℕ∞) i)) := by
            rw [xseq_succ_bc, gatherBT_Dprin_bc] at hyX
            split at hyX
            · exact hyX
            · contradiction
          rcases hparts with rfl | hyold
          · have hYic : leBT (operB b (xseq b (w : ℕ∞) i)) c = true :=
              leBT_trans_bc _ _ _ (leBT_of_less_bc (hYmono i)) hYc
            exact ⟨c, Or.inl (Or.inl rfl), leBT_trans_bc _ _ _ hxy hYic⟩
          · have hYic : leBT (operB b (xseq b (w : ℕ∞) i)) c = true :=
              leBT_trans_bc _ _ _ (leBT_of_less_bc (hYmono i)) hYc
            obtain ⟨y₂, hy₂, hyy₂⟩ := ih c u hYic hcb y hyold
            exact ⟨y₂, hy₂, leBT_trans_bc _ _ _ hxy hyy₂⟩
        · exact ⟨y, Or.inr hyzero, hxy⟩
  have hGwb : ∀ x ∈ GBT (w : ℕ∞) b, lessBT x b = true := by
    intro x hx
    exact hGvb x (GBT_antitone_bc hvw b hx)
  have hCL : ∀ i,
      isOT_BT (xseq b (w : ℕ∞) i) = true ∧
      dfree_BT (xseq b (w : ℕ∞) i) = true ∧
      (∀ x ∈ GBT v (xseq b (w : ℕ∞) i),
        lessBT x (operB b (xseq b (w : ℕ∞) i)) = true) := by
    intro i
    induction i with
    | zero =>
        have hot₀ : isOT_BT (xseq b (w : ℕ∞) 0) = true := by
          simp [xseq_zero_bc, Dprin, isOT_BT, isOT_BPList, isOT_BP,
            BZero, gatherBT, gatherBPList, descP]
        have hdf₀ : dfree_BT (xseq b (w : ℕ∞) 0) = true := by
          simp [xseq_zero_bc, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]
        refine ⟨hot₀, hdf₀, ?_⟩
        intro x hx
        have hxzero : x = BZero := by
          have hsub : x ∈ ({BZero} : Set BT) := by
            rw [xseq_zero_bc, gatherBT_Dprin_bc] at hx
            split at hx
            · simpa [GBT, BZero, gatherBT, gatherBPList] using hx
            · contradiction
          exact hsub
        subst x
        exact BZero_lt_of_ne_bc hY₀ne
    | succ i ih =>
        have hotXi := ih.1
        have hdfXi := ih.2.1
        have hPi := ih.2.2
        have hcloseY := (hIH _ (hxin i)).2 hotXi hdfXi
        have hGvY := G_control_bc (htri i) (hYle i) hGvb hPi
        have hPwi : ∀ x ∈ GBT (w : ℕ∞) (xseq b (w : ℕ∞) i),
            lessBT x (operB b (xseq b (w : ℕ∞) i)) = true := by
          intro x hx
          exact hPi x (GBT_antitone_bc hvw _ hx)
        have hGwY := G_control_bc (htri i) (hYle i) hGwb hPwi
        have hcloseX := close_Dprin_bc (w : ℕ∞)
          (operB b (xseq b (w : ℕ∞) i)) hcloseY.1 hcloseY.2 hGwY
          (by simp)
        refine ⟨?_, ?_, ?_⟩
        · simpa [xseq_succ_bc] using hcloseX.1
        · simpa [xseq_succ_bc] using hcloseX.2
        · intro x hx
          have hparts : x = operB b (xseq b (w : ℕ∞) i) ∨
              x ∈ GBT v (operB b (xseq b (w : ℕ∞) i)) := by
            rw [xseq_succ_bc, gatherBT_Dprin_bc, if_pos hvw] at hx
            exact hx
          rcases hparts with rfl | hxG
          · exact hYmono i
          · exact lessBT_linear_trans _ _ _ (hGvY _ hxG) (hYmono i)
  let n := numNat z
  have hcloseXn := hCL n
  have hcloseYn := (hIH _ (hxin n)).2 hcloseXn.1 hcloseXn.2.1
  have hGvYn := G_control_bc (htri n) (hYle n) hGvb hcloseXn.2.2
  have hcloseOuter := close_Dprin_bc v
    (operB b (xseq b (w : ℕ∞) n)) hcloseYn.1 hcloseYn.2 hGvYn
    (by intro hvtop; subst v; simp at hvw)
  have htriOuter : triGBC z
      (Dprin v (operB b (xseq b (w : ℕ∞) n))) (Dprin v b) := by
    intro u c hlo hhi
    obtain ⟨c₀, cs, hc, hYc₀, hc₀b⟩ := sandwich_Dprin_bc hlo hhi
    by_cases huv : u ≤ v
    · rw [gatherBT_Dprin_bc, if_pos huv]
      intro x hx
      have hc₀mem : c₀ ∈ GBT u c := by
        rw [hc]
        simp [GBT, gatherBT, gatherBPList, gatherBP, huv]
      rcases hx with rfl | hx
      · exact ⟨c₀, Or.inl (Or.inl hc₀mem), hYc₀⟩
      · obtain ⟨y, hy, hxy⟩ := hTI n c₀ u hYc₀ hc₀b x hx
        refine ⟨y, ?_, hxy⟩
        rcases hy with (rfl | hyc₀) | hyzero
        · exact Or.inl (Or.inl hc₀mem)
        · exact Or.inl (Or.inl (GBT_trans_bc hc₀mem hyc₀))
        · exact Or.inr hyzero
    · rw [gatherBT_Dprin_bc, if_neg huv]
      intro x hx
      exact hx.elim
  constructor
  · simpa [n] using htriOuter
  · intro _ _
    simpa [n] using hcloseOuter

private theorem head_le_of_less_cons_bc {y q : BP} {ys qs : List BP}
    (h : lessBT (.trm (y :: ys)) (.trm (q :: qs)) = true) :
    leBT (.trm [y]) (.trm [q]) = true := by
  simp only [lessBT, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h with hyq | ⟨rfl, _⟩
  · apply leBT_of_less_bc
    simpa [lessBP_single_bc] using hyq
  · exact leBT_refl_bc _

private theorem isOT_cons_bc (p : BP) (ys : List BP)
    (hp : isOT_BP p = true) (hy : isOT_BT (.trm ys) = true)
    (hbnd : ∀ y yr, ys = y :: yr → leBT (.trm [y]) (.trm [p]) = true) :
    isOT_BT (.trm (p :: ys)) = true := by
  have hylist : isOT_BPList ys = true ∧ descP ys = true := by
    simpa [isOT_BT] using hy
  simp only [isOT_BT, Bool.and_eq_true]
  constructor
  · simpa [isOT_BPList, hp] using hylist.1
  · cases ys with
    | nil => rfl
    | cons y ys =>
        have hle : leBT (.trm [y]) (.trm [p]) = true :=
          hbnd y ys rfl
        simpa [descP, hle] using hylist.2

private theorem dfree_cons_bc (p : BP) (ys : List BP)
    (hp : dfree_BP p = true) (hy : dfree_BT (.trm ys) = true) :
    dfree_BT (.trm (p :: ys)) = true := by
  simpa [dfree_BT, dfree_BPList, hp] using hy

private theorem isOT_Dprin_parts_bc (v : ℕ∞) (b : BT)
    (hot : isOT_BT (Dprin v b) = true) :
    isOT_BT b = true ∧ (∀ x ∈ GBT v b, lessBT x b = true) := by
  have hs : isOT_BT b = true ∧
      (gatherBT v b).all (fun x => lessBT x b) = true := by
    have := hot
    simp only [Dprin, isOT_BT, isOT_BPList, isOT_BP,
      Bool.and_eq_true, descP] at this
    exact this.1.1
  refine ⟨hs.1, ?_⟩
  simpa [GBT] using hs.2

private theorem dfree_Dprin_parts_bc (v : ℕ∞) (b : BT)
    (hdf : dfree_BT (Dprin v b) = true) :
    v ≠ ⊤ ∧ dfree_BT b = true := by
  simpa [Dprin, dfree_BT, dfree_BPList, dfree_BP] using hdf

/-! Buchholz Lemma 3.6 (G part) and Lemma 3.3, simultaneously. -/

private theorem buchholz_master_bc (a z : BT)
    (hot : isOT_BT a = true) (hdf : dfree_BT a = true)
    (hne : a ≠ BZero) (hz : z ∈ domB a ∨ z ∈ NatSet) :
    triGBC z (operB a z) a ∧
      (isOT_BT z = true → dfree_BT z = true →
        isOT_BT (operB a z) = true ∧ dfree_BT (operB a z) = true) := by
  generalize hn : btWeight a = n
  induction n using Nat.strong_induction_on generalizing a z with
  | h n ih =>
      rcases a with ⟨xs⟩
      cases xs with
      | nil => exact (hne rfl).elim
      | cons p ps =>
          cases ps with
          | nil =>
              rcases p with ⟨v, b⟩
              have hotparts := isOT_Dprin_parts_bc v b hot
              have hdfparts := dfree_Dprin_parts_bc v b hdf
              have hotb := hotparts.1
              have hGvb := hotparts.2
              have hdfb := hdfparts.2
              have hvfin := hdfparts.1
              have hbn : btWeight b < n := by
                rw [← hn]
                simp [btWeight, bpListWeight, bpWeight]
                omega
              by_cases hb : b = BZero
              · subst b
                by_cases hv₀ : v = 0
                · subst v
                  have hop : operB (.trm [.db 0 BZero]) z = BZero := by
                    simp [operB, bOperCore, BZero]
                  constructor
                  · rw [hop]
                    intro u c _ _ x hx
                    simp [GBT, BZero, gatherBT, gatherBPList] at hx
                  · intro _ _
                    rw [hop]
                    constructor <;> rfl
                · have hvtop : v ≠ ⊤ := hvfin
                  have hop : operB (.trm [.db v BZero]) z = z := by
                    simp [operB, bOperCore, BZero, hv₀, hvtop]
                  constructor
                  · rw [hop]
                    intro u c _ _
                    apply setLe_subset_bc
                    intro x hx
                    exact Or.inl (Or.inr hx)
                  · intro hzOT hzDF
                    simpa [hop] using And.intro hzOT hzDF
              · cases hdb : domTag b with
                | empty =>
                    have := tag_empty_eq_zero_bc b hdb
                    exact (hb this).elim
                | zeroOnly =>
                    have hIH₀ := ih (btWeight b) hbn b BZero hotb hdfb hb
                      (Or.inr ⟨0, rfl⟩) rfl
                    have htriX := hIH₀.1
                    have hcloseX := hIH₀.2 (by rfl) (by rfl)
                    have hXlt := buchholz_fseq_descent b BZero hotb hb
                      (Or.inr ⟨0, rfl⟩)
                    have hGvX := G_control_bc htriX (leBT_of_less_bc hXlt) hGvb
                      (by
                        intro x hx
                        simp [GBT, BZero, gatherBT, gatherBPList] at hx)
                    let X := operB b BZero
                    have htriXz : triGBC z X b := by
                      exact triG_zero_to_bc htriX
                    have htriD := triG_Dprin_bc v htriXz
                    have htriR := triG_replicate_succ_bc v (numNat z) htriD
                    have hcloseR := close_replicate_succ_bc v X (numNat z)
                      hcloseX.1 hcloseX.2 hGvX hvfin
                    have hop : operB (.trm [.db v b]) z =
                        .trm (List.replicate (numNat z + 1) (.db v X)) := by
                      simp [operB, bOperCore, Dprin, hb, hdb, X,
                        multBT_single_bc]
                    constructor
                    · rw [hop]
                      simpa [Dprin] using htriR
                    · intro _ _
                      rw [hop]
                      exact hcloseR
                | naturals =>
                    have hzb : z ∈ domB b ∨ z ∈ NatSet := by
                      rcases hz with hz | hz
                      · left
                        simpa [domB, domTag, domTagList, domTagBP, hb,
                          hdb, BDom.toSet] using hz
                      · exact Or.inr hz
                    have hIHb := ih (btWeight b) hbn b z hotb hdfb hb hzb rfl
                    have hYlt := buchholz_fseq_descent b z hotb hb hzb
                    have hzNat : z ∈ NatSet := by
                      rcases hzb with hzb | hzb
                      · simpa [domB, hdb, BDom.toSet] using hzb
                      · exact hzb
                    have hYne := operB_nonzero_naturals_bc b z hdb
                    have hGz : ∀ x ∈ GBT v z,
                        lessBT x (operB b z) = true := by
                      intro x hx
                      rcases hzNat with ⟨m, hm⟩
                      subst z
                      have hx₀ : x ∈ ({BZero} : Set BT) :=
                        gatherBT_num_subset_zero_bc v m hx
                      subst x
                      exact BZero_lt_of_ne_bc hYne
                    have hGvY := G_control_bc hIHb.1 (leBT_of_less_bc hYlt) hGvb hGz
                    have hclose : isOT_BT z = true → dfree_BT z = true →
                        isOT_BT (Dprin v (operB b z)) = true ∧
                          dfree_BT (Dprin v (operB b z)) = true := by
                      intro hzOT hzDF
                      have hc := hIHb.2 hzOT hzDF
                      exact close_Dprin_bc v _ hc.1 hc.2 hGvY hvfin
                    have hop : operB (.trm [.db v b]) z = Dprin v (operB b z) := by
                      simp [operB, bOperCore, Dprin, hb, hdb]
                    constructor
                    · rw [hop]
                      simpa [Dprin] using triG_Dprin_bc v hIHb.1
                    · intro hzOT hzDF
                      rw [hop]
                      exact hclose hzOT hzDF
                | below w =>
                    by_cases hvw : v ≤ (w : ℕ∞)
                    · have hIHtower : ∀ t, t ∈ TBv (w : ℕ∞) →
                          triGBC t (operB b t) b ∧
                            (isOT_BT t = true → dfree_BT t = true →
                              isOT_BT (operB b t) = true ∧
                                dfree_BT (operB b t) = true) := by
                        intro t ht
                        exact ih (btWeight b) hbn b t hotb hdfb hb
                          (Or.inl (by simpa [domB, hdb, BDom.toSet] using ht)) rfl
                      have htower := tower_case_bc v b z w hotb hb hdb hvw hGvb hIHtower
                      have hop : operB (.trm [.db v b]) z =
                          Dprin v (operB b (xseq b (w : ℕ∞) (numNat z))) := by
                        simp [operB, bOperCore, Dprin, hb, hdb, hvw, xseq]
                      rw [hop]
                      simpa [Dprin] using htower
                    · have hzb : z ∈ domB b ∨ z ∈ NatSet := by
                        rcases hz with hz | hz
                        · left
                          simpa [domB, domTag, domTagList, domTagBP, hb,
                            hdb, hvw, BDom.toSet] using hz
                        · exact Or.inr hz
                      have hIHb := ih (btWeight b) hbn b z hotb hdfb hb hzb rfl
                      have hYlt := buchholz_fseq_descent b z hotb hb hzb
                      have hzTB : z ∈ TBv (w : ℕ∞) := by
                        rcases hzb with hzb | hzb
                        · simpa [domB, hdb, BDom.toSet] using hzb
                        · exact NatSet_mem_TBv_bc hzb
                      have hwv : (w : ℕ∞) < v := lt_of_not_ge hvw
                      have hGz : ∀ x ∈ GBT v z,
                          lessBT x (operB b z) = true := by
                        intro x hx
                        rw [GBT_TBv_small_empty_bc hzTB hwv] at hx
                        exact hx.elim
                      have hGvY := G_control_bc hIHb.1 (leBT_of_less_bc hYlt) hGvb hGz
                      have hclose : isOT_BT z = true → dfree_BT z = true →
                          isOT_BT (Dprin v (operB b z)) = true ∧
                            dfree_BT (Dprin v (operB b z)) = true := by
                        intro hzOT hzDF
                        have hc := hIHb.2 hzOT hzDF
                        exact close_Dprin_bc v _ hc.1 hc.2 hGvY hvfin
                      have hop : operB (.trm [.db v b]) z = Dprin v (operB b z) := by
                        simp [operB, bOperCore, Dprin, hb, hdb, hvw]
                      constructor
                      · rw [hop]
                        simpa [Dprin] using triG_Dprin_bc v hIHb.1
                      · intro hzOT hzDF
                        rw [hop]
                        exact hclose hzOT hzDF
          | cons q qs =>
              let tail : BT := .trm (q :: qs)
              have htailn : btWeight tail < n := by
                rw [← hn]
                simp [tail, btWeight, bpListWeight]
              have hotsplit :
                  (isOT_BP p = true ∧ isOT_BPList (q :: qs) = true) ∧
                    descP (p :: q :: qs) = true := by
                simpa [isOT_BT, isOT_BPList] using hot
              have hdesctail : descP (q :: qs) = true := by
                have := hotsplit.2
                have hs : leBT (.trm [q]) (.trm [p]) = true ∧
                    descP (q :: qs) = true := by
                  simpa [descP] using this
                exact hs.2
              have hottail : isOT_BT tail = true := by
                simp [tail, isOT_BT, hotsplit.1.2, hdesctail]
              have hdfsplit : dfree_BP p = true ∧ dfree_BT tail = true := by
                simpa [tail, dfree_BT, dfree_BPList] using hdf
              have htagtail : domTag tail = domTag (.trm (p :: q :: qs)) := by
                simp [tail, domTag, domTagList]
              have hztail : z ∈ domB tail ∨ z ∈ NatSet := by
                rcases hz with hz | hz
                · left
                  rw [domB, htagtail]
                  exact hz
                · exact Or.inr hz
              have hIHtail := ih (btWeight tail) htailn tail z hottail hdfsplit.2
                (by simp [tail, BZero]) hztail rfl
              have htriFull := triG_add_bc [p] hIHtail.1
              have hop : operB (.trm (p :: q :: qs)) z =
                  addBT (.trm [p]) (operB tail z) := by
                simp [tail, operB, bOperCore]
              constructor
              · simpa [hop] using htriFull
              · intro hzOT hzDF
                have hcloseY := hIHtail.2 hzOT hzDF
                rcases hY : operB tail z with ⟨ys⟩
                have hotY : isOT_BT (.trm ys) = true := by simpa [hY] using hcloseY.1
                have hdfY : dfree_BT (.trm ys) = true := by simpa [hY] using hcloseY.2
                have hYlt := buchholz_fseq_descent tail z hottail
                  (by simp [tail, BZero]) hztail
                have hbnd : ∀ y yr, ys = y :: yr →
                    leBT (.trm [y]) (.trm [p]) = true := by
                  intro y yr hyr
                  subst ys
                  have hyq : leBT (.trm [y]) (.trm [q]) = true :=
                    head_le_of_less_cons_bc (by simpa [tail, hY] using hYlt)
                  have hqp : leBT (.trm [q]) (.trm [p]) = true := by
                    have hs : leBT (.trm [q]) (.trm [p]) = true ∧
                        descP (q :: qs) = true := by
                      simpa [descP] using hotsplit.2
                    exact hs.1
                  exact leBT_trans_bc _ _ _ hyq hqp
                have hotRes := isOT_cons_bc p ys hotsplit.1.1 hotY hbnd
                have hdfRes := dfree_cons_bc p ys hdfsplit.1 hdfY
                rw [hop, hY]
                simpa [addBT] using And.intro hotRes hdfRes

/-- Strengthened [Buc1] Lemma 3.3: `operB` preserves both the structural
ordinal predicate and `D_ω`-freeness for every accepted domain argument. -/
theorem buchholz_fseq_closed_general (a z : BT)
    (hot : isOT_BT a = true) (hdf : dfree_BT a = true)
    (hne : a ≠ BZero) (hz : z ∈ domB a ∨ z ∈ NatSet)
    (hzOT : isOT_BT z = true) (hzDF : dfree_BT z = true) :
    isOT_BT (operB a z) = true ∧ dfree_BT (operB a z) = true :=
  (buchholz_master_bc a z hot hdf hne hz).2 hzOT hzDF

/-- [Buc1] Lemma 3.3 in the exact numeral form cited by the paper. -/
theorem buchholz_fseq_closed (a : BT) (n : ℕ) (hot : a ∈ OT_B)
    (hne : a ≠ BZero) : operB a (numBT n) ∈ OT_B := by
  have hc := buchholz_fseq_closed_general a (numBT n) hot.1 hot.2 hne
    (Or.inr ⟨n, rfl⟩) (isOT_num_bc n) (dfree_num_bc n)
  exact ⟨hc.1, hc.2⟩

#print axioms TBv_lt_of_OT_tag_below_bf
#print axioms buchholz_fseq_closed_general
#print axioms buchholz_fseq_closed

end PSS
