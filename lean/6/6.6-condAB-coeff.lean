import «6».«6.6-reduced-iff-condAB»
import «6».«6.4-mono-slice»

/-!
# §6.6 補題（条件 (A), (B) と係数の基本性質）

- 原文: `tmp/content.md` の「補題（条件(A)と(B)と係数の基本性質）」
- 訂正: なし
- Isabelle: `m_6_6_condAB_coeff`, `condAB_row1_noparent_zero`
- 依存: §5.1, §6.4, §6.6 `RedCondA_apply`, `RedCondB_apply`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem parent_lt_of_hasParent (M : PS) (i j : ℕ)
    (hp : hasParent M i j = true) : parent M i j < j := by
  have hn := hasParent_next_fseq M i j hp
  by_cases hi : i = 0
  · have hh : nextrel0 M (parent M i j) j = true := by
      simpa [nextR, hi] using hn
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  · have hh : nextrel1 M (parent M i j) j = true := by
      simpa [nextR, hi] using hn
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.2

theorem noParent_row0_zero (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (j : ℕ) (hj : j < Lng M)
    (hnp : hasParent M 0 j = false) : entry M 0 j = 0 := by
  by_contra hne
  have hpos : 0 < entry M 0 j := Nat.pos_of_ne_zero hne
  have hjpos : 0 < j := by
    by_contra hj0
    have : j = 0 := by omega
    subst j
    exact hne he00
  obtain ⟨p, _, _, hp⟩ := parent_exists_1 M 0 j hM hjpos hj (by omega)
  have hhas : hasParent M 0 j = true :=
    (hasParent_iff_unique_fseq M 0 j).mpr
      ⟨p, hp, fun q hq => row0_parent_unique M q p j hq hp⟩
  rw [hnp] at hhas
  contradiction

private theorem le1Aux_refl_cc (M : PS) (fuel a : ℕ) :
    le1Aux M fuel a a = true := by
  cases fuel <;> simp [le1Aux]

private theorem le1Aux_fuel_step (M : PS) (fuel a b : ℕ)
    (h : le1Aux M fuel a b = true) :
    le1Aux M (fuel + 1) a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      exact le1Aux_refl_cc M 1 a
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        exact le1Aux_refl_cc M (fuel + 2) a
      · rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        exact Or.inr ⟨p, hpb, hpnext, ih p hap⟩

private theorem le1Aux_fuel_mono (M : PS) (f g a b : ℕ)
    (hfg : f ≤ g) (h : le1Aux M f a b = true) :
    le1Aux M g a b = true := by
  induction g, hfg using Nat.le_induction with
  | base => exact h
  | succ g hfg ih =>
      simpa [Nat.add_comm] using le1Aux_fuel_step M g a b ih

private theorem le1Aux_trim (M : PS) (a b fuel : ℕ)
    (h : le1Aux M fuel a b = true) :
    le1Aux M (b + 1) a b = true := by
  induction b using Nat.strong_induction_on generalizing fuel with
  | h b ih =>
      cases fuel with
      | zero =>
          have hab : a = b := by simpa [le1Aux] using h
          subst b
          exact le1Aux_refl_cc M (a + 1) a
      | succ fuel =>
          simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
            Bool.and_eq_true, List.mem_range] at h ⊢
          rcases h with h | ⟨p, hpb, hpnext, hap⟩
          · exact Or.inl h
          · have htrim := ih p hpb fuel hap
            have hlift : le1Aux M b a p = true :=
              le1Aux_fuel_mono M (p + 1) b a p (by omega) htrim
            exact Or.inr ⟨p, hpb, hpnext, hlift⟩

theorem nextR_leR_cc (M : PS) (i a b : ℕ)
    (hnext : nextR M i a b = true) : leR M i a b = true := by
  by_cases hi : i = 0
  · subst i
    exact nextR0_leR M a b hnext
  · have hn : nextrel1 M a b = true := by simpa [nextR, hi] using hnext
    have hh := hn
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    rcases hh with ⟨⟨⟨⟨⟨haL, hbL⟩, hab⟩, _⟩, _⟩, _⟩
    have hLpos : 0 < Lng M := Nat.zero_lt_of_lt hbL
    have haux : le1Aux M (Lng M) a b = true := by
      rw [show Lng M = (Lng M - 1) + 1 by omega]
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      right
      refine ⟨a, hab, hn, ?_⟩
      exact le1Aux_refl_cc M (Lng M - 1) a
    simp [leR, hi, le1, haL, hbL, haux]

theorem leR_then_next_cc (M : PS) (i a p b : ℕ) (hM : TPS M)
    (hap : leR M i a p = true) (hnext : nextR M i p b = true) :
    leR M i a b = true := by
  by_cases hi : i = 0
  · subst i
    exact row0_transitive M a p b hM hap (nextR0_leR M p b hnext)
  · have hn : nextrel1 M p b = true := by simpa [nextR, hi] using hnext
    have hhn := hn
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hhn
    rcases hhn with ⟨⟨⟨⟨⟨hpL, hbL⟩, hpb⟩, _⟩, _⟩, _⟩
    have haL : a < Lng M := by
      have hh := hap
      simp only [leR, if_neg hi, le1, Bool.and_eq_true,
        decide_eq_true_eq] at hh
      exact hh.1.1
    have haux : le1Aux M (Lng M) a p = true := by
      have hh := hap
      simp only [leR, if_neg hi, le1, Bool.and_eq_true,
        decide_eq_true_eq] at hh
      exact hh.2
    have htrim := le1Aux_trim M a p (Lng M) haux
    have hlift : le1Aux M (Lng M - 1) a p = true :=
      le1Aux_fuel_mono M (p + 1) (Lng M - 1) a p (by omega) htrim
    have hout : le1Aux M (Lng M) a b = true := by
      rw [show Lng M = (Lng M - 1) + 1 by omega]
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range]
      exact Or.inr ⟨p, hpb, hn, hlift⟩
    simp [leR, hi, le1, haL, hbL, hout]

/-- Under condition (B), a row-one position without a parent has value zero
when the two leftmost coefficients are zero. -/
theorem noParent_row1_zero (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (hB : RedCondB M = true) (j : ℕ) (hj : j < Lng M)
    (hnp : hasParent M 1 j = false) : entry M 1 j = 0 := by
  by_cases hj0 : j = 0
  · simpa [hj0] using he10
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    by_contra hne
    have hejpos : 0 < entry M 1 j := Nat.pos_of_ne_zero hne
    let Q := P M
    have htotal : (IdxSum Q).getD Q.length 0 = Lng M := by
      rw [idxSum_total]
      simpa [Q] using congrArg Lng (P_concat M)
    have hjtotal : j < (IdxSum Q).getD Q.length 0 := by
      rw [htotal]
      exact hj
    obtain ⟨J, hJ, haJ, hjnext⟩ := idxSum_locate Q j hjtotal
    let a := (IdxSum Q).getD J 0
    let nxt := (IdxSum Q).getD (J + 1) 0
    let C := Q.getD J []
    let e := nxt - 1
    let k := j - a
    have hdiff : nxt = a + Lng C := by
      simpa [nxt, a, C] using idxSum_diff Q J hJ
    have hCpos : 0 < Lng C := by
      simpa [Q, C] using P_component_nonempty M J hM
        (by simpa [Q] using hJ)
    have haLmin := P_leftend_lmin M J hM (by simpa [Q] using hJ)
    have hae0 : entry M 0 a = 0 := by
      by_cases ha0 : a = 0
      · simpa [ha0] using he00
      · have hmin0 : entry M 0 a ≤ entry M 0 0 := by
          simpa [a, Q] using haLmin.2 0 (Nat.pos_of_ne_zero ha0)
        omega
    have haL : a < Lng M := by
      have hMpos := List.length_pos_of_ne_nil hM
      have := haLmin.1
      omega
    have hnp0 : hasParent M 0 a = false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      have hn := hasParent_next_fseq M 0 a hp
      have hh : nextrel0 M (parent M 0 a) a = true := by
        simpa [nextR] using hn
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      omega
    have hae1 : entry M 1 a = 0 := by
      have heq := RedCondB_apply M hM hB a haL hnp0
      omega
    have haj : a < j := by
      have hale : a ≤ j := by simpa [a] using haJ
      by_contra hnot
      have heq : a = j := by omega
      rw [heq] at hae1
      omega
    have hkpos : 0 < k := by simp [k]; omega
    have hkC : k < Lng C := by
      have : j < nxt := by simpa [nxt] using hjnext
      rw [hdiff] at this
      simp [k]
      omega
    have hCT : TPS C := List.ne_nil_of_length_pos hCpos
    have hCmem : C ∈ P M := by
      have hget : C = Q[J] := by
        simpa [C] using getD_eq_getElem_idx Q [] hJ
      rw [hget]
      simpa [Q] using List.getElem_mem hJ
    have hCmono : monoT C = true := by
      rcases P_components_nonmulti M hM C hCmem with hz | hm
      · have hlen : Lng C = 1 := by
          have hh := hz
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
          exact hh.1
        omega
      · exact hm
    have hnextTotal : nxt ≤ (IdxSum Q).getD Q.length 0 := by
      simpa [nxt] using idxSum_mono Q (J + 1) Q.length (by omega) (le_refl _)
    have hnxtL : nxt ≤ Lng M := by
      rw [htotal] at hnextTotal
      exact hnextTotal
    have hnxtpos : 0 < nxt := by rw [hdiff]; omega
    have hae : a ≤ e := by simp [e]; rw [hdiff]; omega
    have heL : e < Lng M := by simp [e]; omega
    have hcomp : C = seg M a e := by
      have hJle : J ≤ (P M).length - 1 := by
        have : J ≤ Q.length - 1 := by omega
        simpa [Q] using this
      simpa [Q, C, a, e, nxt] using P_IdxSum M J hM hJle
    have hfull : leR C 0 0 (Lng C - 1) = true := by
      have hh := hCmono
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have hlocal : leR C 0 0 k = true :=
      ancestor_tree_1 C 0 k (Lng C - 1) hCT hfull (Nat.zero_le _) (by omega)
    have hseg0 : 0 < Lng (seg M a e) := by rw [← hcomp]; exact hCpos
    have hsegk : k < Lng (seg M a e) := by rw [← hcomp]; exact hkC
    have htransfer := leR0_seg_adm M a e 0 k hae heL hseg0 hsegk
    rw [hcomp, htransfer] at hlocal
    have hle0 : leR M 0 a j = true := by
      have hsum : a + k = j := by simp [k]; omega
      simpa [hsum] using hlocal
    obtain ⟨p, _, _, hp⟩ := parent_exists_2 M a j hM haj hj
      (by omega) hle0
    have hhas : hasParent M 1 j = true :=
      (hasParent_iff_unique_fseq M 1 j).mpr
        ⟨p, hp, fun q hq => nextR1_unique_mr M q p j hq hp⟩
    rw [hnp] at hhas
    contradiction

theorem RedCondA_row0_le_index (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (hA : RedCondA M = true)
    (j : ℕ) (hj : j < Lng M) : entry M 0 j ≤ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hp : hasParent M 0 j = true
      · let p := parent M 0 j
        have hpj : p < j := by simpa [p] using parent_lt_of_hasParent M 0 j hp
        have hpL : p < Lng M := hpj.trans hj
        have hprev := ih p hpj hpL
        have hstep := RedCondA_apply M hA 0 j (by omega) hj hp
        change entry M 0 p + 1 = entry M 0 j at hstep
        omega
      · have hp' : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hp
        rw [noParent_row0_zero M hM he00 j hj hp']
        omega

theorem RedCondAB_row1_le_row0 (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (hA : RedCondA M = true) (hB : RedCondB M = true)
    (j : ℕ) (hj : j < Lng M) : entry M 1 j ≤ entry M 0 j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hp : hasParent M 1 j = true
      · let p := parent M 1 j
        have hpj : p < j := by simpa [p] using parent_lt_of_hasParent M 1 j hp
        have hpL : p < Lng M := hpj.trans hj
        have hprev := ih p hpj hpL
        have hstep := RedCondA_apply M hA 1 j (by omega) hj hp
        change entry M 1 p + 1 = entry M 1 j at hstep
        have hn := hasParent_next_fseq M 1 j hp
        have hn1 : nextrel1 M p j = true := by simpa [p, nextR] using hn
        have hh := hn1
        simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
        have hanc0 : leR M 0 p j = true := by simpa [leR] using hh.1.2
        have hgrowth := ancestor_basic_1 M p j j hM hpj (le_refl _) hanc0
        omega
      · have hp' : hasParent M 1 j = false := Bool.eq_false_of_not_eq_true hp
        rw [noParent_row1_zero M hM he00 he10 hB j hj hp']
        omega

private theorem entry_le_index_cc (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (hA : RedCondA M = true) (i : ℕ) (hi : i ≤ 1)
    (hrow : i = 0 ∨ (i = 1 ∧ RedCondB M = true))
    (j : ℕ) (hj : j < Lng M) : entry M i j ≤ j := by
  rcases hrow with rfl | ⟨rfl, hB⟩
  · exact RedCondA_row0_le_index M hM he00 hA j hj
  · exact (RedCondAB_row1_le_row0 M hM he00 he10 hA hB j hj).trans
      (RedCondA_row0_le_index M hM he00 hA j hj)

theorem condAB_gap_entry_lt (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (hA : RedCondA M = true) (i : ℕ) (hi : i ≤ 1)
    (hrow : i = 0 ∨ (i = 1 ∧ RedCondB M = true))
    (j : ℕ) (hj : j < Lng M)
    (hgap : ∃ j₀ j₁, leR M i j₀ j₁ = false ∧ j₀ < j₁ ∧ j₁ ≤ j) :
    entry M i j < j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases hgap with ⟨j₀, j₁, hnot, hj₀j₁, hj₁j⟩
      have hjpos : 0 < j := by omega
      by_cases hp : hasParent M i j = true
      · let p := parent M i j
        have hpj : p < j := by simpa [p] using parent_lt_of_hasParent M i j hp
        have hpL : p < Lng M := hpj.trans hj
        have hstep := RedCondA_apply M hA i j (by omega) hj hp
        change entry M i p + 1 = entry M i j at hstep
        by_cases hj₁p : j₁ ≤ p
        · have hprev := ih p hpj hpL ⟨j₀, j₁, hnot, hj₀j₁, hj₁p⟩
          omega
        · by_cases hskip : p < j - 1
          · have hple := entry_le_index_cc M hM he00 he10 hA i hi hrow p hpL
            omega
          · have hpeq : p = j - 1 := by omega
            have hj₁eq : j₁ = j := by omega
            have hnot' : leR M i j₀ j = false := by simpa [hj₁eq] using hnot
            by_cases hj₀p : j₀ ≤ p
            · have hj₀ne : j₀ ≠ p := by
                intro heq
                have hle := nextR_leR_cc M i p j (hasParent_next_fseq M i j hp)
                rw [← heq, hnot'] at hle
                contradiction
              have hj₀ltp : j₀ < p := lt_of_le_of_ne hj₀p hj₀ne
              have hnotp : leR M i j₀ p = false := by
                by_contra hfalse
                have htrue : leR M i j₀ p = true := by
                  simpa using Bool.eq_true_of_not_eq_false hfalse
                have hout := leR_then_next_cc M i j₀ p j hM htrue
                  (hasParent_next_fseq M i j hp)
                rw [hnot'] at hout
                contradiction
              have hprev := ih p hpj hpL ⟨j₀, p, hnotp, hj₀ltp, le_rfl⟩
              omega
            · omega
      · have hp' : hasParent M i j = false := Bool.eq_false_of_not_eq_true hp
        rcases hrow with rfl | ⟨rfl, hB⟩
        · rw [noParent_row0_zero M hM he00 j hj hp']
          exact hjpos
        · rw [noParent_row1_zero M hM he00 he10 hB j hj hp']
          exact hjpos

/-- The three coefficient bounds of §6.6. -/
theorem condAB_coeff (M : PS) (hM : TPS M)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (hA : RedCondA M = true) :
    (∀ j, j ≤ Lng M - 1 → entry M 0 j ≤ j) ∧
    (RedCondB M = true → ∀ j, j ≤ Lng M - 1 →
      entry M 1 j ≤ entry M 0 j) ∧
    (∀ i, i ≤ 1 → (i = 0 ∨ (i = 1 ∧ RedCondB M = true)) →
      ∀ j, j ≤ Lng M - 1 →
        (∃ j₀ j₁, leR M i j₀ j₁ = false ∧ j₀ < j₁ ∧ j₁ ≤ j) →
        entry M i j < j) := by
  have hpos := List.length_pos_of_ne_nil hM
  constructor
  · intro j hj
    have hjL : j < Lng M := hj.trans_lt (Nat.sub_lt hpos (by omega))
    exact RedCondA_row0_le_index M hM he00 hA j hjL
  constructor
  · intro hB j hj
    have hjL : j < Lng M := hj.trans_lt (Nat.sub_lt hpos (by omega))
    exact RedCondAB_row1_le_row0 M hM he00 he10 hA hB j hjL
  · intro i hi hrow j hj hgap
    have hjL : j < Lng M := hj.trans_lt (Nat.sub_lt hpos (by omega))
    exact condAB_gap_entry_lt M hM he00 he10 hA i hi hrow j hjL hgap

#print axioms noParent_row0_zero
#print axioms noParent_row1_zero
#print axioms condAB_coeff
#print axioms nextR_leR_cc
#print axioms leR_then_next_cc

end PSS
