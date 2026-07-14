import PSS.Mono
import «6».«6.2-P-components-nonmulti»
import «6».«6.2-P-additivity»

/-!
# §6.2 命題（`P` と基本列の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_P_oper_1`, `_2`
- 訂正: なし
- Isabelle: `m_6_2_P_oper_1`, `_2`
- 依存: `6.2-P-components-nonmulti`, `6.2-P-additivity`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem P_nonempty (M : PS) : P M ≠ [] := by
  unfold P
  cases Lng M with
  | zero => simp [PAux]
  | succ fuel =>
      simp only [PAux]
      split <;> simp

private theorem PAux_flatten (fuel : ℕ) (M : PS) (hbound : Lng M ≤ fuel) :
    (PAux fuel M).flatten = M := by
  induction fuel generalizing M with
  | zero =>
      have hlen : Lng M = 0 := by omega
      have hm : M = [] := List.length_eq_zero_iff.mp hlen
      subst M
      simp [PAux]
  | succ fuel ih =>
      by_cases hs : (multiT M && decide (1 < Lng M)) = true
      · have hsplit : multiT M = true ∧ 1 < Lng M := by simpa using hs
        have hc := Pcut_props M hsplit.2
        have hclt : Pcut M < Lng M := by omega
        have hprelen : Lng (M.take (Pcut M)) = Pcut M := by
          simp [Nat.min_eq_left hclt.le]
        have hprebound : Lng (M.take (Pcut M)) ≤ fuel := by omega
        rw [PAux, if_pos hs, List.flatten_append, ih (M.take (Pcut M)) hprebound]
        simp
      · rw [PAux, if_neg hs]
        simp

theorem P_concat (M : PS) : (P M).flatten = M := by
  exact PAux_flatten (Lng M) M (by rfl)

theorem P_last_multi (M : PS) (hm : multiT M = true) (hlen : 1 < Lng M) :
    (P M).getLastD [] = M.drop (Pcut M) ∧
      (P M).dropLast = P (M.take (Pcut M)) := by
  rw [P_multi_step M hm hlen]
  simp

private theorem le0Aux_refl_fseq (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

theorem nextR_implies_row0 (M : PS) (i j₀ j₁ : ℕ)
    (hn : nextR M i j₀ j₁ = true) :
    j₀ < j₁ ∧ leR M 0 j₀ j₁ = true := by
  by_cases hi : i = 0
  · have hn₀ : nextrel0 M j₀ j₁ = true := by simpa [nextR, hi] using hn
    have hh := hn₀
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hj₀L : j₀ < Lng M := hh.1.1.1.1
    have hj₁L : j₁ < Lng M := hh.1.1.1.2
    have hjlt : j₀ < j₁ := hh.1.1.2
    have haux : le0Aux M (Lng M) j₀ j₁ = true := by
      cases heq : Lng M with
      | zero => omega
      | succ fuel =>
          simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
            Bool.and_eq_true, List.mem_range]
          right
          exact ⟨j₀, hjlt, hn₀, le0Aux_refl_fseq M fuel j₀⟩
    exact ⟨hjlt, by simp [leR, le0, hj₀L, hj₁L, haux]⟩
  · have hn₁ : nextrel1 M j₀ j₁ = true := by simpa [nextR, hi] using hn
    have hh := hn₁
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact ⟨hh.1.1.1.2, by simpa [leR] using hh.1.2⟩

theorem parent_ge_Pcut (M : PS) (i j₀ : ℕ) (hM : TPS M)
    (hm : multiT M = true) (hlen : 1 < Lng M)
    (hpar : nextR M i j₀ (Lng M - 1) = true) :
    Pcut M ≤ j₀ := by
  have hj := nextR_implies_row0 M i j₀ (Lng M - 1) hpar
  by_contra hnot
  have hjc : j₀ < Pcut M := by omega
  by_cases hjzero : j₀ = 0
  · subst j₀
    have hz : zeroT M = false := by
      have ht := hm
      simp [multiT] at ht
      exact ht.1
    have hmono : monoT M = true := by simp [monoT, hz, hj.2]
    simp [multiT, hmono] at hm
  · have hjpos : 0 < j₀ := Nat.pos_of_ne_zero hjzero
    have hjlast : j₀ ≤ Lng M - 1 := by omega
    have hfalse := Pcut_not_candidate M hlen j₀ hjc
    simp [hjpos, hjlast, hj.2] at hfalse

private theorem nextrel0_drop_fseq (M : PS) (c a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    nextrel0 (M.drop c) a b = nextrel0 M (c + a) (c + b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.length_drop] at h ⊢
    rcases h with ⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩, ?_⟩
    · simpa [entry_drop] using he
    · intro k hk
      by_cases hak : c + a < k
      · have hck : c ≤ k := by omega
        let t := k - c
        have ht : t < b := by
          have hkcb : k < c + b := List.mem_range.mp hk
          simp [t]
          omega
        have hat : a < t := by simp [t]; omega
        have hs := hall t (List.mem_range.mpr ht)
        have hentry : entry M 0 (c + b) ≤ entry M 0 k := by
          simpa [hat, entry_drop, t, Nat.add_sub_of_le hck] using hs
        simp [hak, hentry]
      · simp [hak]
  · intro h
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.length_drop] at h ⊢
    rcases h with ⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨ha, hb⟩, by omega⟩, ?_⟩, ?_⟩
    · simpa [entry_drop] using he
    · intro k hk
      have hkb : k < b := List.mem_range.mp hk
      have hs := hall (c + k) (List.mem_range.mpr (by omega))
      simpa [entry_drop, hab, hkb] using hs

private theorem le0Aux_index_fseq {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans hpb.le

private theorem le0Aux_mono_succ_fseq (M : PS) (fuel a b : ℕ)
    (h : le0Aux M fuel a b = true) : le0Aux M (fuel + 1) a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      change ((a == b) || (List.range b).any
        (fun p => nextrel0 M p b && le0Aux M (fuel + 1) a p)) = true
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hpb, hpnext, ih p hap⟩

private theorem le0Aux_mono_fseq (M : PS) (f g a b : ℕ) (hfg : f ≤ g)
    (h : le0Aux M f a b = true) : le0Aux M g a b = true := by
  induction g generalizing f with
  | zero =>
      have : f = 0 := by omega
      simpa [this] using h
  | succ g ih =>
      by_cases heq : f = g + 1
      · simpa [heq] using h
      · have hfg' : f ≤ g := by omega
        exact le0Aux_mono_succ_fseq M g a b (ih f hfg' h)

private theorem le0Aux_bound_fseq (M : PS) (fuel a b : ℕ)
    (h : le0Aux M fuel a b = true) : le0Aux M (b + 1) a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · right
        refine ⟨p, hpb, hpnext, ?_⟩
        exact le0Aux_mono_fseq M (p + 1) b a p (by omega) (ih p hap)

private theorem le0Aux_drop_fwd_fseq (M : PS) (c fuel a b : ℕ)
    (hb : b < Lng M - c) (h : le0Aux (M.drop c) fuel a b = true) :
    le0Aux M fuel (c + a) (c + b) = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl (by omega)
      · right
        have hpbound : p < Lng M - c := hpb.trans hb
        have hpnext' : nextrel0 M (c + p) (c + b) = true := by
          simpa only [nextrel0_drop_fseq M c p b hpbound hb] using hpnext
        exact ⟨c + p, by omega, hpnext', ih p hpbound hap⟩

private theorem le0Aux_drop_bwd_fseq (M : PS) (c fuel a b : ℕ)
    (hb : b < Lng M - c) (h : le0Aux M fuel (c + a) (c + b) = true) :
    le0Aux (M.drop c) fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : c + a = c + b := by simpa [le0Aux] using h
      have : a = b := Nat.add_left_cancel hab
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨q, hqb, hqnext, haq⟩
      · exact Or.inl (Nat.add_left_cancel h)
      · have hcaq : c + a ≤ q := le0Aux_index_fseq haq
        let p := q - c
        have hpbound : p < Lng M - c := by simp [p]; omega
        have hpb : p < b := by simp [p]; omega
        have hqeq : c + p = q := by simp [p, Nat.add_sub_of_le (by omega : c ≤ q)]
        have hpnext : nextrel0 (M.drop c) p b = true := by
          rw [nextrel0_drop_fseq M c p b hpbound hb, hqeq]
          exact hqnext
        right
        exact ⟨p, hpb, hpnext, ih p hpbound (by simpa [hqeq] using haq)⟩

private theorem le0_drop_fseq (M : PS) (c a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    le0 (M.drop c) a b = le0 M (c + a) (c + b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hh := h
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq, List.length_drop] at hh ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hshift := le0Aux_drop_fwd_fseq M c (Lng M - c) a b hb hh.2
    exact le0Aux_mono_fseq M (Lng M - c) (Lng M) (c + a) (c + b)
      (Nat.sub_le _ _) hshift
  · intro h
    have hh := h
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq, List.length_drop] at hh ⊢
    refine ⟨⟨ha, hb⟩, ?_⟩
    have hshift := le0Aux_drop_bwd_fseq M c (Lng M) a b hb hh.2
    have hsmall := le0Aux_bound_fseq (M.drop c) (Lng M) a b hshift
    exact le0Aux_mono_fseq (M.drop c) (b + 1) (Lng M - c) a b (by omega) hsmall

private theorem le0_index_fseq {M : PS} {a b : ℕ}
    (h : le0 M a b = true) : a ≤ b := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  exact le0Aux_index_fseq hh.2

private theorem nextrel1_drop_fseq (M : PS) (c a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    nextrel1 (M.drop c) a b = nextrel1 M (c + a) (c + b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.length_drop] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hle⟩, hall⟩
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [entry_drop] using he
    · simpa only [le0_drop_fseq M c a b ha hb] using hle
    · intro k hk
      by_cases hak : c + a < k
      · by_cases hkle : le0 M k (c + b) = true
        · have hkcb : k ≤ c + b := le0_index_fseq hkle
          have hck : c ≤ k := by omega
          let t := k - c
          have htL : t < Lng M - c := by simp [t]; omega
          have hat : a < t := by simp [t]; omega
          have htle : le0 (M.drop c) t b = true := by
            rw [le0_drop_fseq M c t b htL hb]
            simpa [t, Nat.add_sub_of_le hck] using hkle
          have hs := hall t (List.mem_range.mpr htL)
          have hentry : entry M 1 (c + b) ≤ entry M 1 k := by
            simpa [hat, htle, entry_drop, t, Nat.add_sub_of_le hck] using hs
          simp [hak, hkle, hentry]
        · simp [hak, hkle]
      · simp [hak]
  · intro h
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.length_drop] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hle⟩, hall⟩
    refine ⟨⟨⟨⟨⟨ha, hb⟩, by omega⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [entry_drop] using he
    · simpa only [le0_drop_fseq M c a b ha hb] using hle
    · intro k hk
      have hkL : k < Lng M - c := List.mem_range.mp hk
      by_cases hak : a < k
      · by_cases hkle : le0 (M.drop c) k b = true
        · have hs := hall (c + k) (List.mem_range.mpr (by omega))
          have hkle' : le0 M (c + k) (c + b) = true := by
            simpa only [le0_drop_fseq M c k b hkL hb] using hkle
          simpa [hak, hkle, hkle', entry_drop] using hs
        · simp [hak, hkle]
      · simp [hak]

private theorem le1Aux_index_fseq {M : PS} {fuel a b : ℕ}
    (h : le1Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le1Aux] using h
      omega
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans hpb.le

private theorem le1Aux_mono_succ_fseq (M : PS) (fuel a b : ℕ)
    (h : le1Aux M fuel a b = true) : le1Aux M (fuel + 1) a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      change ((a == b) || (List.range b).any
        (fun p => nextrel1 M p b && le1Aux M (fuel + 1) a p)) = true
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hpb, hpnext, ih p hap⟩

private theorem le1Aux_mono_fseq (M : PS) (f g a b : ℕ) (hfg : f ≤ g)
    (h : le1Aux M f a b = true) : le1Aux M g a b = true := by
  induction g generalizing f with
  | zero =>
      have : f = 0 := by omega
      simpa [this] using h
  | succ g ih =>
      by_cases heq : f = g + 1
      · simpa [heq] using h
      · have hfg' : f ≤ g := by omega
        exact le1Aux_mono_succ_fseq M g a b (ih f hfg' h)

private theorem le1Aux_bound_fseq (M : PS) (fuel a b : ℕ)
    (h : le1Aux M fuel a b = true) : le1Aux M (b + 1) a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · right
        refine ⟨p, hpb, hpnext, ?_⟩
        exact le1Aux_mono_fseq M (p + 1) b a p (by omega) (ih p hap)

private theorem le1Aux_drop_fwd_fseq (M : PS) (c fuel a b : ℕ)
    (hb : b < Lng M - c) (h : le1Aux (M.drop c) fuel a b = true) :
    le1Aux M fuel (c + a) (c + b) = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl (by omega)
      · right
        have hpbound : p < Lng M - c := hpb.trans hb
        have hpnext' : nextrel1 M (c + p) (c + b) = true := by
          simpa only [nextrel1_drop_fseq M c p b hpbound hb] using hpnext
        exact ⟨c + p, by omega, hpnext', ih p hpbound hap⟩

private theorem le1Aux_drop_bwd_fseq (M : PS) (c fuel a b : ℕ)
    (hb : b < Lng M - c) (h : le1Aux M fuel (c + a) (c + b) = true) :
    le1Aux (M.drop c) fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : c + a = c + b := by simpa [le1Aux] using h
      have : a = b := Nat.add_left_cancel hab
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨q, hqb, hqnext, haq⟩
      · exact Or.inl (Nat.add_left_cancel h)
      · have hcaq : c + a ≤ q := le1Aux_index_fseq haq
        let p := q - c
        have hpbound : p < Lng M - c := by simp [p]; omega
        have hpb : p < b := by simp [p]; omega
        have hqeq : c + p = q := by simp [p, Nat.add_sub_of_le (by omega : c ≤ q)]
        have hpnext : nextrel1 (M.drop c) p b = true := by
          rw [nextrel1_drop_fseq M c p b hpbound hb, hqeq]
          exact hqnext
        right
        exact ⟨p, hpb, hpnext, ih p hpbound (by simpa [hqeq] using haq)⟩

private theorem le1_drop_fseq (M : PS) (c a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    le1 (M.drop c) a b = le1 M (c + a) (c + b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hh := h
    simp only [le1, Bool.and_eq_true, decide_eq_true_eq, List.length_drop] at hh ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hshift := le1Aux_drop_fwd_fseq M c (Lng M - c) a b hb hh.2
    exact le1Aux_mono_fseq M (Lng M - c) (Lng M) (c + a) (c + b)
      (Nat.sub_le _ _) hshift
  · intro h
    have hh := h
    simp only [le1, Bool.and_eq_true, decide_eq_true_eq, List.length_drop] at hh ⊢
    refine ⟨⟨ha, hb⟩, ?_⟩
    have hshift := le1Aux_drop_bwd_fseq M c (Lng M) a b hb hh.2
    have hsmall := le1Aux_bound_fseq (M.drop c) (Lng M) a b hshift
    exact le1Aux_mono_fseq (M.drop c) (b + 1) (Lng M - c) a b (by omega) hsmall

theorem nextR_drop (M : PS) (c i a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    nextR (M.drop c) i a b = nextR M i (c + a) (c + b) := by
  unfold nextR
  split <;> simp [nextrel0_drop_fseq M c a b ha hb,
    nextrel1_drop_fseq M c a b ha hb]

theorem leR_drop (M : PS) (c i a b : ℕ)
    (ha : a < Lng M - c) (hb : b < Lng M - c) :
    leR (M.drop c) i a b = leR M i (c + a) (c + b) := by
  unfold leR
  split <;> simp [le0_drop_fseq M c a b ha hb, le1_drop_fseq M c a b ha hb]

private theorem nextR_left_bound_fseq (M : PS) (i a b : ℕ)
    (h : nextR M i a b = true) : a < Lng M := by
  unfold nextR at h
  split at h <;> simp [nextrel0, nextrel1] at h <;> omega

private theorem mem_parents_iff_fseq (M : PS) (i j₁ j₀ : ℕ) :
    j₀ ∈ parents M i j₁ ↔ nextR M i j₀ j₁ = true := by
  constructor
  · intro h
    simpa [parents] using (List.mem_filter.mp h).2
  · intro h
    simp [parents, nextR_left_bound_fseq M i j₀ j₁ h, h]

theorem hasParent_iff_unique_fseq (M : PS) (i j₁ : ℕ) :
    hasParent M i j₁ = true ↔ ∃! j₀, nextR M i j₀ j₁ = true := by
  constructor
  · intro h
    have hlen : (parents M i j₁).length = 1 := by simpa [hasParent] using h
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨p, ?_, ?_⟩
    · apply (mem_parents_iff_fseq M i j₁ p).mp
      simp [hp]
    · intro y hy
      have hymem := (mem_parents_iff_fseq M i j₁ y).mpr hy
      simpa [hp] using hymem
  · rintro ⟨p, hp, huniq⟩
    have hpmem : p ∈ parents M i j₁ := (mem_parents_iff_fseq M i j₁ p).mpr hp
    have hparents : parents M i j₁ = [p] := by
      cases heq : parents M i j₁ with
      | nil => simp [heq] at hpmem
      | cons x xs =>
          have hxmem : x ∈ parents M i j₁ := by simp [heq]
          have hxnext := (mem_parents_iff_fseq M i j₁ x).mp hxmem
          have hxp : x = p := huniq x hxnext
          subst x
          cases xs with
          | nil => simpa using heq
          | cons y ys =>
              have hymem : y ∈ parents M i j₁ := by simp [heq]
              have hynext := (mem_parents_iff_fseq M i j₁ y).mp hymem
              have hyp : y = p := huniq y hynext
              subst y
              have hnodup : (parents M i j₁).Nodup := by
                exact List.nodup_range.filter _
              rw [heq] at hnodup
              simp at hnodup
    simp [hasParent, hparents]

theorem parent_eq_of_unique_fseq (M : PS) (i j₁ p : ℕ)
    (hp : nextR M i p j₁ = true)
    (huniq : ∀ y, nextR M i y j₁ = true → y = p) :
    parent M i j₁ = p := by
  have hmem : p ∈ parents M i j₁ := (mem_parents_iff_fseq M i j₁ p).mpr hp
  have hlist : parents M i j₁ = [p] := by
    cases heq : parents M i j₁ with
    | nil => simp [heq] at hmem
    | cons x xs =>
        have hxmem : x ∈ parents M i j₁ := by simp [heq]
        have hxp := huniq x ((mem_parents_iff_fseq M i j₁ x).mp hxmem)
        subst x
        cases xs with
        | nil => simpa using heq
        | cons y ys =>
            have hymem : y ∈ parents M i j₁ := by simp [heq]
            have hyp := huniq y ((mem_parents_iff_fseq M i j₁ y).mp hymem)
            subst y
            have hnodup : (parents M i j₁).Nodup := by
              exact List.nodup_range.filter _
            rw [heq] at hnodup
            simp at hnodup
  simp [parent, hlist]

theorem hasParent_drop_Pcut (M : PS) (c i : ℕ) (hM : TPS M)
    (hm : multiT M = true) (hlen : 1 < Lng M)
    (hc : c = Pcut M) (hclast : c < Lng M - 1) :
    hasParent (M.drop c) i (Lng (M.drop c) - 1) =
      hasParent M i (Lng M - 1) := by
  apply Bool.eq_iff_iff.mpr
  rw [hasParent_iff_unique_fseq, hasParent_iff_unique_fseq]
  have hcL : c < Lng M := by omega
  have hDlen : Lng (M.drop c) = Lng M - c := by simp
  have hlastD : Lng (M.drop c) - 1 = (Lng M - 1) - c := by omega
  constructor
  · rintro ⟨a, ha, hauniq⟩
    have haLt := (nextR_implies_row0 (M.drop c) i a (Lng (M.drop c) - 1) ha).1
    have haB : a < Lng M - c := by omega
    have hlastB : (Lng M - 1) - c < Lng M - c := by omega
    have haM : nextR M i (c + a) (Lng M - 1) = true := by
      have hs := nextR_drop M c i a ((Lng M - 1) - c) haB hlastB
      have ha' := ha
      rw [hlastD] at ha'
      rw [← Nat.add_sub_of_le (by omega : c ≤ Lng M - 1), ← hs]
      exact ha'
    refine ⟨c + a, haM, ?_⟩
    intro y hy
    have hge : c ≤ y := by simpa [hc] using parent_ge_Pcut M i y hM hm hlen hy
    have hylt := (nextR_implies_row0 M i y (Lng M - 1) hy).1
    let b := y - c
    have hbB : b < Lng M - c := by simp [b]; omega
    have hbD : nextR (M.drop c) i b (Lng (M.drop c) - 1) = true := by
      rw [hlastD, nextR_drop M c i b ((Lng M - 1) - c) hbB hlastB]
      simpa [b, Nat.add_sub_of_le hge,
        Nat.add_sub_of_le (by omega : c ≤ Lng M - 1)] using hy
    have hba : b = a := hauniq b hbD
    calc
      y = c + b := by simp [b, Nat.add_sub_of_le hge]
      _ = c + a := by rw [hba]
  · rintro ⟨p, hp, hpuniq⟩
    have hge : c ≤ p := by simpa [hc] using parent_ge_Pcut M i p hM hm hlen hp
    have hplt := (nextR_implies_row0 M i p (Lng M - 1) hp).1
    let a := p - c
    have haB : a < Lng M - c := by simp [a]; omega
    have hlastB : (Lng M - 1) - c < Lng M - c := by omega
    have haD : nextR (M.drop c) i a (Lng (M.drop c) - 1) = true := by
      rw [hlastD, nextR_drop M c i a ((Lng M - 1) - c) haB hlastB]
      simpa [a, Nat.add_sub_of_le hge,
        Nat.add_sub_of_le (by omega : c ≤ Lng M - 1)] using hp
    refine ⟨a, haD, ?_⟩
    intro b hb
    have hbLt := (nextR_implies_row0 (M.drop c) i b (Lng (M.drop c) - 1) hb).1
    have hbB : b < Lng M - c := by omega
    have hbM : nextR M i (c + b) (Lng M - 1) = true := by
      rw [hlastD] at hb
      rw [nextR_drop M c i b ((Lng M - 1) - c) hbB hlastB] at hb
      simpa [Nat.add_sub_of_le (by omega : c ≤ Lng M - 1)] using hb
    have : c + b = p := hpuniq (c + b) hbM
    simp [a]
    omega

theorem parent_drop_Pcut (M : PS) (c i : ℕ) (hM : TPS M)
    (hm : multiT M = true) (hlen : 1 < Lng M)
    (hc : c = Pcut M) (hclast : c < Lng M - 1)
    (hp : hasParent M i (Lng M - 1) = true) :
    parent M i (Lng M - 1) =
      c + parent (M.drop c) i (Lng (M.drop c) - 1) := by
  obtain ⟨p, hpnext, hpuniq⟩ := (hasParent_iff_unique_fseq M i (Lng M - 1)).mp hp
  have hge : c ≤ p := by simpa [hc] using parent_ge_Pcut M i p hM hm hlen hpnext
  let a := p - c
  have hDlen : Lng (M.drop c) = Lng M - c := by simp
  have hlastD : Lng (M.drop c) - 1 = (Lng M - 1) - c := by omega
  have haB : a < Lng M - c := by
    have hplt := (nextR_implies_row0 M i p (Lng M - 1) hpnext).1
    simp [a]
    omega
  have hlastB : (Lng M - 1) - c < Lng M - c := by omega
  have haD : nextR (M.drop c) i a (Lng (M.drop c) - 1) = true := by
    rw [hlastD, nextR_drop M c i a ((Lng M - 1) - c) haB hlastB]
    simpa [a, Nat.add_sub_of_le hge,
      Nat.add_sub_of_le (by omega : c ≤ Lng M - 1)] using hpnext
  have hauniq : ∀ b, nextR (M.drop c) i b (Lng (M.drop c) - 1) = true → b = a := by
    intro b hb
    have hbB : b < Lng M - c := by
      have := (nextR_implies_row0 (M.drop c) i b (Lng (M.drop c) - 1) hb).1
      omega
    have hbM : nextR M i (c + b) (Lng M - 1) = true := by
      rw [hlastD] at hb
      rw [nextR_drop M c i b ((Lng M - 1) - c) hbB hlastB] at hb
      simpa [Nat.add_sub_of_le (by omega : c ≤ Lng M - 1)] using hb
    have heq : c + b = p := hpuniq (c + b) hbM
    simp [a]
    omega
  have hparM : parent M i (Lng M - 1) = p :=
    parent_eq_of_unique_fseq M i (Lng M - 1) p hpnext hpuniq
  have hparD : parent (M.drop c) i (Lng (M.drop c) - 1) = a :=
    parent_eq_of_unique_fseq (M.drop c) i (Lng (M.drop c) - 1) a haD hauniq
  rw [hparM, hparD]
  simp [a, Nat.add_sub_of_le hge]

private theorem Pred_split_fseq (M : PS) (c : ℕ)
    (hclast : c < Lng M - 1) (hlen : 1 < Lng M) :
    Pred M = M.take c ++ Pred (M.drop c) := by
  have hDlen : Lng (M.drop c) = Lng M - c := by simp
  have hDgt : 1 < Lng (M.drop c) := by omega
  have hpredM : Pred M = M.take (Lng M - 1) := by
    rw [Pred, if_neg (Nat.not_le_of_lt hlen), List.dropLast_eq_take]
  have hpredD : Pred (M.drop c) = (M.drop c).take (Lng M - c - 1) := by
    rw [Pred, if_neg (Nat.not_le_of_lt hDgt), List.dropLast_eq_take]
    congr 2
  rw [hpredM, hpredD, ← List.take_add]
  congr 1
  omega

private theorem block_drop_fseq (M : PS) (c a len k d₀ d₁ : ℕ) :
    (List.range' (c + a) len).map (fun j =>
      (entry M 0 j + k * d₀, entry M 1 j + k * d₁)) =
    (List.range' a len).map (fun j =>
      (entry (M.drop c) 0 j + k * d₀, entry (M.drop c) 1 j + k * d₁)) := by
  apply List.ext_getElem
  · simp
  · intro t ht₁ ht₂
    have ht : t < len := by simpa using ht₁
    simp [List.getElem_range', entry_drop, ht, Nat.add_assoc]

theorem oper_drop_Pcut (M : PS) (c n : ℕ) (hM : TPS M)
    (hm : multiT M = true) (hlen : 1 < Lng M)
    (hc : c = Pcut M) (hclast : c < Lng M - 1) :
    oper M n = M.take c ++ oper (M.drop c) n := by
  let D := M.drop c
  let j₁ := Lng M - 1
  let j₁D := Lng D - 1
  have hcL : c < Lng M := by omega
  have hDlen : Lng D = Lng M - c := by simp [D]
  have hDgt : 1 < Lng D := by omega
  have hj₁ne : j₁ ≠ 0 := by simp [j₁]; omega
  have hj₁Dne : j₁D ≠ 0 := by simp [j₁D]; omega
  have hlastsum : c + j₁D = j₁ := by simp [j₁, j₁D, hDlen]; omega
  have e₀last : entry D 0 j₁D = entry M 0 j₁ := by
    simp [D, entry_drop, hlastsum]
  have e₁last : entry D 1 j₁D = entry M 1 j₁ := by
    simp [D, entry_drop, hlastsum]
  have hidx : idx1 D j₁D = idx1 M j₁ := by simp [idx1, e₁last]
  have hhas : hasParent D (idx1 D j₁D) j₁D =
      hasParent M (idx1 M j₁) j₁ := by
    have ht := hasParent_drop_Pcut M c (idx1 M (Lng M - 1)) hM hm hlen hc hclast
    calc
      hasParent D (idx1 D j₁D) j₁D = hasParent D (idx1 M j₁) j₁D := by rw [hidx]
      _ = hasParent M (idx1 M j₁) j₁ := by simpa [D, j₁, j₁D] using ht
  have hpred := Pred_split_fseq M c hclast hlen
  by_cases hz : entry M 0 j₁ = 0 ∧ entry M 1 j₁ = 0
  · have hzD : entry D 0 j₁D = 0 ∧ entry D 1 j₁D = 0 := by
      simpa [e₀last, e₁last] using hz
    have hopM : oper M n = Pred M := by simp [oper, j₁, hj₁ne, hz]
    have hopD : oper D n = Pred D := by simp [oper, j₁D, hj₁Dne, hzD]
    simpa [D, hopM, hopD] using hpred
  · have hzD : ¬ (entry D 0 j₁D = 0 ∧ entry D 1 j₁D = 0) := by
      simpa [e₀last, e₁last] using hz
    by_cases hp : hasParent M (idx1 M j₁) j₁ = true
    · have hpD : hasParent D (idx1 D j₁D) j₁D = true := by simpa [hhas] using hp
      let a := parent D (idx1 D j₁D) j₁D
      have hpar : parent M (idx1 M j₁) j₁ = c + a := by
        have ht := parent_drop_Pcut M c (idx1 M (Lng M - 1)) hM hm hlen hc hclast
          (by simpa [j₁] using hp)
        calc
          parent M (idx1 M j₁) j₁ = c + parent D (idx1 M j₁) j₁D := by
            simpa [D, j₁, j₁D] using ht
          _ = c + a := by rw [← hidx]
      let d₀ := if 0 < idx1 M j₁ then
        entry M 0 j₁ - entry M 0 (parent M (idx1 M j₁) j₁) else 0
      let d₁ := if 1 < idx1 M j₁ then
        entry M 1 j₁ - entry M 1 (parent M (idx1 M j₁) j₁) else 0
      have e₀par : entry D 0 a = entry M 0 (parent M (idx1 M j₁) j₁) := by
        simp [D, entry_drop, hpar]
      have e₁par : entry D 1 a = entry M 1 (parent M (idx1 M j₁) j₁) := by
        simp [D, entry_drop, hpar]
      have hlenblock : j₁ - (c + a) = j₁D - a := by
        simp [j₁, j₁D, hDlen]
        omega
      have hprefix : M.take (c + a) = M.take c ++ D.take a := by
        simp [D, ← List.take_add]
      have hblock : ∀ k, (List.range' (c + a) (j₁ - (c + a))).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁)) =
        (List.range' a (j₁D - a)).map (fun j =>
          (entry D 0 j + k * d₀, entry D 1 j + k * d₁)) := by
        intro k
        rw [hlenblock]
        exact block_drop_fseq M c a (j₁D - a) k d₀ d₁
      have hopM : oper M n = M.take (c + a) ++
          (List.range n).flatMap (fun k =>
            (List.range' (c + a) (j₁ - (c + a))).map (fun j =>
              (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
        simp [oper, j₁, hj₁ne, hz, hp, hpar, d₀, d₁]
      let d₀D := if 0 < idx1 D j₁D then
        entry D 0 j₁D - entry D 0 (parent D (idx1 D j₁D) j₁D) else 0
      let d₁D := if 1 < idx1 D j₁D then
        entry D 1 j₁D - entry D 1 (parent D (idx1 D j₁D) j₁D) else 0
      have hparentD : parent D (idx1 M j₁) j₁D = a := by rw [← hidx]
      have hd₀ : d₀D = d₀ := by
        simp [d₀D, d₀, hidx, e₀last, hparentD, e₀par]
      have hd₁ : d₁D = d₁ := by
        simp [d₁D, d₁, hidx, e₁last, hparentD, e₁par]
      have hopD : oper D n = D.take a ++
          (List.range n).flatMap (fun k =>
            (List.range' a (j₁D - a)).map (fun j =>
              (entry D 0 j + k * d₀, entry D 1 j + k * d₁))) := by
        have hraw : oper D n = D.take a ++
            (List.range n).flatMap (fun k =>
              (List.range' a (j₁D - a)).map (fun j =>
                (entry D 0 j + k * d₀D, entry D 1 j + k * d₁D))) := by
          simp [oper, j₁D, hj₁Dne, hzD, hpD, a, d₀D, d₁D]
        simpa [hd₀, hd₁] using hraw
      rw [hopM, hopD, hprefix, List.append_assoc]
      congr 1
      congr 1
      apply List.flatMap_congr
      intro k hk
      exact hblock k
    · have hpfalse : hasParent M (idx1 M j₁) j₁ = false := by simpa using hp
      have hpD : hasParent D (idx1 D j₁D) j₁D = false := by simpa [hhas] using hpfalse
      have hopM : oper M n = Pred M := by simp [oper, j₁, hj₁ne, hz, hpfalse]
      have hopD : oper D n = Pred D := by simp [oper, j₁D, hj₁Dne, hzD, hpD]
      simpa [D, hopM, hopD] using hpred

theorem hasParent_next_fseq (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) :
    nextR M i (parent M i j₁) j₁ = true := by
  obtain ⟨p, hpnext, hpuniq⟩ := (hasParent_iff_unique_fseq M i j₁).mp hp
  have hpar := parent_eq_of_unique_fseq M i j₁ p hpnext hpuniq
  simpa [hpar] using hpnext

theorem oper_head_fseq (M : PS) (n : ℕ) (hM : TPS M)
    (hlen : 1 < Lng M) (hn : 1 ≤ n) :
    (oper M n)[0]? = M[0]? := by
  let j₁ := Lng M - 1
  have hj₁pos : 0 < j₁ := by simp [j₁]; omega
  have hj₁ne : j₁ ≠ 0 := Nat.ne_of_gt hj₁pos
  have hpred : Pred M = M.take j₁ := by
    simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take, j₁]
  by_cases hz : entry M 0 j₁ = 0 ∧ entry M 1 j₁ = 0
  · have hop : oper M n = Pred M := by simp [oper, j₁, hj₁ne, hz]
    rw [hop, hpred, List.getElem?_take_of_lt hj₁pos]
  · let i₁ := idx1 M j₁
    by_cases hp : hasParent M i₁ j₁ = true
    · let j₀ := parent M i₁ j₁
      have hj₀lt : j₀ < j₁ :=
        (nextR_implies_row0 M i₁ j₀ j₁ (hasParent_next_fseq M i₁ j₁ hp)).1
      let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
      let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
      have hop : oper M n = M.take j₀ ++
          (List.range n).flatMap (fun k =>
            (List.range' j₀ (j₁ - j₀)).map (fun j =>
              (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
        simp [oper, j₁, hj₁ne, hz, i₁, hp, j₀, d₀, d₁]
      by_cases hj₀pos : 0 < j₀
      · rw [hop]
        have hj₀L : j₀ ≤ Lng M := by omega
        have htakepos : 0 < (M.take j₀).length := by
          simp [Nat.min_eq_left hj₀L, hj₀pos]
        rw [List.getElem?_append_left htakepos,
          List.getElem?_take_of_lt hj₀pos]
      · have hj₀zero : j₀ = 0 := by omega
        cases n with
        | zero => omega
        | succ n =>
            rw [hop]
            simp [hj₀zero, List.range_succ_eq_map, hj₁pos]
            cases h₀ : M[0]? with
            | none =>
                have hg := List.getElem?_eq_getElem (l := M)
                  (show 0 < Lng M by omega)
                rw [hg] at h₀
                simp at h₀
            | some p =>
                rcases p with ⟨x, y⟩
                simp [entry, h₀]
    · have hpfalse : hasParent M i₁ j₁ = false := by simpa using hp
      have hop : oper M n = Pred M := by simp [oper, j₁, hj₁ne, hz, i₁, hpfalse]
      rw [hop, hpred, List.getElem?_take_of_lt hj₁pos]

theorem oper_nonempty_fseq (M : PS) (n : ℕ) (hM : TPS M)
    (hlen : 1 < Lng M) (hn : 1 ≤ n) : oper M n ≠ [] := by
  intro heq
  have hh := oper_head_fseq M n hM hlen hn
  rw [heq] at hh
  simp at hh
  exact hM hh

theorem multi_length_fseq (M : PS) (hM : TPS M)
    (hm : multiT M = true) : 1 < Lng M := by
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  by_contra h
  have hlen : Lng M = 1 := by omega
  simp [multiT, monoT, zeroT, hlen, leR, le0, le0Aux] at hm

private theorem hasParent_exists_fseq (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) :
    ∃ j₀, nextR M i j₀ j₁ = true := by
  have hlen : (parents M i j₁).length = 1 := by
    simpa [hasParent] using hp
  have hne : parents M i j₁ ≠ [] := by
    intro heq
    simp [heq] at hlen
  obtain ⟨j₀, hj₀⟩ := List.exists_mem_of_ne_nil (parents M i j₁) hne
  have hj := hj₀
  simp [parents] at hj
  exact ⟨j₀, hj.2⟩

theorem P_fseq_1 (M : PS) (n : ℕ) (hM : TPS M) (hn : 1 ≤ n)
    (hlast : Lng ((P M).getLastD []) = 1) :
    oper M n = Pred M ∧
      (if (P M).length = 1 then P (oper M n) = [oper M n]
       else P (oper M n) = (P M).dropLast) := by
  by_cases hsing : (P M).length = 1
  · have hm : multiT M = false := by
      cases hm' : multiT M
      · rfl
      · have hgt := (P_components_multi_iff M hM).mp hm'
        omega
    have hPM := P_nonmulti_eq M hm
    have hlen : Lng M = 1 := by simpa [hPM] using hlast
    have hop : oper M n = M := by simp [oper, hlen]
    have hpred : Pred M = M := by simp [Pred, hlen]
    constructor
    · simpa [hop, hpred]
    · rw [if_pos hsing, hop]
      simpa [hop] using hPM
  · have hPlen : 1 < (P M).length := by
      have hnemp := P_nonempty M
      have hpos := List.length_pos_of_ne_nil hnemp
      omega
    have hm : multiT M = true := (P_components_multi_iff M hM).mpr hPlen
    have hlen := multi_length_fseq M hM hm
    have hlastP := (P_last_multi M hm hlen).1
    have hbutP := (P_last_multi M hm hlen).2
    have hc := Pcut_props M hlen
    have hclt : Pcut M < Lng M := by omega
    have hdropLen : Lng (M.drop (Pcut M)) = Lng M - Pcut M := by simp
    have htailone : Lng (M.drop (Pcut M)) = 1 := by
      calc
        Lng (M.drop (Pcut M)) = Lng ((P M).getLastD []) :=
          congrArg Lng hlastP.symm
        _ = 1 := hlast
    have hceq : Pcut M = Lng M - 1 := by omega
    have hnoparent : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false := by
      cases hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)
      · rfl
      · obtain ⟨j₀, hj₀⟩ := hasParent_exists_fseq M (idx1 M (Lng M - 1))
            (Lng M - 1) hp
        have hge := parent_ge_Pcut M (idx1 M (Lng M - 1)) j₀ hM hm hlen hj₀
        have hlt := (nextR_implies_row0 M (idx1 M (Lng M - 1)) j₀
          (Lng M - 1) hj₀).1
        omega
    have hop : oper M n = Pred M := by
      have hjne : Lng M - 1 ≠ 0 := by omega
      simp [oper, hjne, hnoparent]
    have hpred : Pred M = M.take (Pcut M) := by
      simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take, hceq]
    have hPoper : P (oper M n) = (P M).dropLast := by
      rw [hop, hpred, hbutP]
    constructor
    · exact hop
    · rw [if_neg hsing]
      exact hPoper

theorem P_fseq_2 (M : PS) (n : ℕ) (hM : TPS M) (hn : 1 ≤ n)
    (hlast : 1 < Lng ((P M).getLastD [])) :
    oper M n = (P M).dropLast.flatten ++ oper ((P M).getLastD []) n ∧
      P (oper M n) = (P M).dropLast ++ P (oper ((P M).getLastD []) n) := by
  by_cases hsing : (P M).length = 1
  · have hm : multiT M = false := by
      cases hm' : multiT M
      · rfl
      · have hgt := (P_components_multi_iff M hM).mp hm'
        omega
    have hPM := P_nonmulti_eq M hm
    simp [hPM]
  · have hPlen : 1 < (P M).length := by
      have hnemp := P_nonempty M
      have hpos := List.length_pos_of_ne_nil hnemp
      omega
    have hm : multiT M = true := (P_components_multi_iff M hM).mpr hPlen
    have hlen := multi_length_fseq M hM hm
    have hlastP := (P_last_multi M hm hlen).1
    have hbutP := (P_last_multi M hm hlen).2
    let c := Pcut M
    let D := M.drop c
    have hc := Pcut_props M hlen
    have hcpos : 0 < c := by simpa [c] using hc.1
    have hcle : c ≤ Lng M - 1 := by simpa [c] using hc.2.1
    have hcL : c < Lng M := by omega
    have hDlast : (P M).getLastD [] = D := by simpa [c, D] using hlastP
    have hDgt : 1 < Lng D := by
      rw [hDlast] at hlast
      exact hlast
    have hclast : c < Lng M - 1 := by
      have hDlen : Lng D = Lng M - c := by simp [D]
      omega
    have hop : oper M n = M.take c ++ oper D n := by
      exact oper_drop_Pcut M c n hM hm hlen (by rfl) hclast
    have hconcat : (P M).dropLast.flatten = M.take c := by
      rw [hbutP, P_concat]
    have hpart₁ : oper M n = (P M).dropLast.flatten ++
        oper ((P M).getLastD []) n := by
      rw [hconcat, hDlast]
      exact hop
    have hDT : TPS D := by
      intro heq
      have : Lng D = 0 := by simp [heq]
      omega
    have hoperDne : oper D n ≠ [] := oper_nonempty_fseq D n hDT hDgt hn
    let N := oper M n
    have hNeq : N = oper M n := rfl
    have htakeLen : Lng (M.take c) = c := by simp [Nat.min_eq_left hcL.le]
    have hNlen : Lng N = c + Lng (oper D n) := by simp [N, hop, htakeLen]
    have hNT : TPS N := by
      intro heq
      have : N = [] := heq
      rw [hNeq, hop] at this
      simp at this
      exact hoperDne this.2
    have hcN : c ≤ Lng N - 1 := by
      have hposD : 0 < Lng (oper D n) := List.length_pos_of_ne_nil hoperDne
      omega
    have hentryLeft : ∀ j, j < c → entry N 0 j = entry M 0 j := by
      intro j hj
      unfold entry
      rw [hNeq, hop, List.getElem?_append_left (by simpa [htakeLen] using hj),
        List.getElem?_take_of_lt hj]
    have hheadD := oper_head_fseq D n hDT hDgt hn
    have hentryCut : entry N 0 c = entry M 0 c := by
      unfold entry
      rw [hNeq, hop, List.getElem?_append_right (by simp [htakeLen])]
      simp only [List.length_take, Nat.min_eq_left hcL.le]
      simp only [Nat.sub_self]
      rw [hheadD]
      simp only [D, List.getElem?_drop]
      simp
    have hleftmin : ∀ j, j < c → entry N 0 c ≤ entry N 0 j := by
      intro j hj
      rw [hentryCut, hentryLeft j hj]
      exact Pcut_left_min M hM hm hlen j (by simpa [c] using hj)
    have hadd := P_additivity N c hNT hcpos hcN hleftmin
    have htakeN : N.take c = M.take c := by
      simp [N, hop, htakeLen]
    have hdropN : N.drop c = oper D n := by
      simp [N, hop, htakeLen]
    have hseg₀ : seg N 0 (c - 1) = N.take c :=
      (take_eq_seg N c hcpos hcN).symm
    have hseg₁ : seg N c (Lng N - 1) = N.drop c :=
      (drop_eq_seg N c (by omega)).symm
    have hpart₂ : P (oper M n) = (P M).dropLast ++
        P (oper ((P M).getLastD []) n) := by
      rw [hDlast]
      rw [← hNeq, hadd, hseg₀, hseg₁, htakeN, hdropN, ← hbutP]
    exact ⟨hpart₁, hpart₂⟩

#print axioms P_fseq_1
#print axioms P_fseq_2

end PSS
