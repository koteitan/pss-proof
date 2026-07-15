import «6».«6.6-P-condAB»
import «6».«6.6-reduced-leftend»
import «6».«6.5-Red-Pred-commute»

/-!
# §6.6 命題（簡約性と係数の関係）

- 原文: `tmp/content.md` の「命題（簡約性と係数の関係）」
- 訂正: なし
- Isabelle: `p_6_6_reduced_iff_cond`, `kst_reduced_imp_condAB_uncond`
- 依存: §6.5 `Red_rebase_nonmulti`, §6.2
- 状態: 🚨 証明作業中
-/

namespace PSS

theorem no_parent_zero (M : PS) (i : ℕ) : hasParent M i 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hn := hasParent_next_fseq M i 0 hp
  by_cases hi : i = 0
  · simp [nextR, hi, nextrel0] at hn
  · simp [nextR, hi, nextrel1] at hn

theorem RedCondB_apply (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) (j : ℕ) (hj : j < Lng M)
    (hnp : hasParent M 0 j = false) :
    entry M 0 j = entry M 1 j := by
  have hh := hB
  simp only [RedCondB, List.all_eq_true, List.mem_range] at hh
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hj' : j < Lng M - 1 + 1 := by omega
  have hjB := hh j hj'
  simpa [hnp] using hjB

theorem RedCondB_head_eq (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) :
    entry M 0 0 = entry M 1 0 := by
  exact RedCondB_apply M hM hB 0 (List.length_pos_of_ne_nil hM)
    (no_parent_zero M 0)

theorem rebaseRow0_self_of_head_eq_nonmulti (M : PS) (hM : TPS M)
    (hnm : multiT M = false)
    (hhead : entry M 0 0 = entry M 1 0) :
    rebaseRow0 (entry M 0 0) (entry M 1 0) M = M := by
  have hfloor : ∀ j < Lng M, entry M 0 0 ≤ entry M 0 j := by
    by_cases hz : zeroT M = true
    · have hL : Lng M = 1 := by
        have hh := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        exact hh.1
      intro j hj
      have : j = 0 := by omega
      subst j
      exact le_rfl
    · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
      have hmono : monoT M = true := by
        have hh := hnm
        simp [multiT, hz'] at hh
        exact hh
      intro j hj
      exact mono_row0_min_mr M hM hmono j hj
  apply List.ext_getElem
  · simp [rebaseRow0]
  · intro j hjR hjM
    have hj : j < Lng M := by simpa using hjM
    have hMj : M[j] = (entry M 0 j, entry M 1 j) := by
      apply Prod.ext
      · exact (entry0_eq_fst_getElem_mr M j hj).symm
      · simpa [entry, List.getElem?_eq_getElem hj]
    simp only [rebaseRow0, List.getElem_map]
    rw [hMj, hhead]
    apply Prod.ext
    · simp only [Prod.fst]
      exact Nat.sub_add_cancel (by rw [← hhead]; exact hfloor j hj)
    · simp

/-- The non-multi half of the backward implication in
`reduced ↔ RedCondA ∧ RedCondB`. -/
theorem RTPS_of_condAB_nonmulti (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hB : RedCondB M = true)
    (hnm : multiT M = false) : RTPS M := by
  have hred := Red_rebase_nonmulti M hM hA hnm
  have hhead := RedCondB_head_eq M hM hB
  have hid := rebaseRow0_self_of_head_eq_nonmulti M hM hnm hhead
  have hfix : Red M = M := hred.trans hid
  have hne : M ≠ [] := hM
  simp [RTPS, reduced, hne, hfix]

theorem mono_hasParent_row0 (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (j : ℕ)
    (hjpos : 0 < j) (hjL : j < Lng M) :
    hasParent M 0 j = true := by
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hjlast : j ≤ Lng M - 1 := by omega
  have hanc := ancestor_tree_1 M 0 j (Lng M - 1) hM hfull
    (Nat.zero_le _) hjlast
  have hstrict := ancestor_basic_1 M 0 j j hM hjpos (le_refl _) hanc
  rcases parent_exists_1 M 0 j hM hjpos hjL hstrict with
    ⟨p, hp0, hpj, hp⟩
  exact (hasParent_iff_unique_fseq M 0 j).mpr
    ⟨p, hp, fun q hq => row0_parent_unique M q p j hq hp⟩

theorem RTPS_mono_RedCondB (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) : RedCondB M = true := by
  have hM := RTPS_TPS M hR
  have hhead := RTPS_mono_head_eq M hR hmono
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  by_cases hp : hasParent M 0 j = true
  · simp [hp]
  · have hp' : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hp
    have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hjL : j < Lng M := by omega
    have hj0 : j = 0 := by
      by_contra hjne
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      exact hp (mono_hasParent_row0 M hM hmono j hjpos hjL)
    subst j
    simp [hp', hhead]

theorem RTPS_iff_condAB_zeroT (M : PS) (hM : TPS M)
    (hz : zeroT M = true) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hfix := RTPS_Red_eq M hR
    have hred := Red_zero_mr M hz
    have hMeq : M = [(0, 0)] := by rw [← hfix, hred]
    subst M
    decide
  · rintro ⟨hA, hB⟩
    have hnm : multiT M = false := by simp [multiT, hz]
    exact RTPS_of_condAB_nonmulti M hM hA hB hnm

/-- The `multiT` branch of the keystone equivalence.  Once the equivalence is
known recursively on every `P` component, reducedness and conditions (A), (B)
are transferred blockwise in both directions. -/
theorem RTPS_iff_condAB_multi (M : PS) (hM : TPS M)
    (_hmulti : multiT M = true)
    (IH : ∀ J, J < (P M).length →
      (RTPS ((P M).getD J []) ↔
        RedCondA ((P M).getD J []) = true ∧
          RedCondB ((P M).getD J []) = true)) :
    RTPS M ↔ RedCondA M = true ∧ RedCondB M = true := by
  constructor
  · intro hR
    have hblocksR := (RTPS_iff_P_components M hM).mp hR
    apply RedCondAB_of_P_components M hM
    intro J hJ
    exact (IH J hJ).mp (hblocksR J hJ)
  · rintro ⟨hA, hB⟩
    apply (RTPS_iff_P_components M hM).mpr
    intro J hJ
    apply (IH J hJ).mpr
    exact RedCondAB_P_component M J hM hA hB hJ

/-- Condition (A) on a sequence with a nonempty diagonal prefix descends to
the original suffix.  This packages the suffix as a `seg`, so all parent
bookkeeping at the prefix/suffix junction is discharged by `RedCondA_seg`. -/
theorem RedCondA_of_diag_prefix (M : PS) (m : ℕ) (hM : TPS M)
    (hm : 0 < m)
    (hA : RedCondA (diagSeq 0 (m - 1) ++ M) = true) :
    RedCondA M = true := by
  let N := diagSeq 0 (m - 1) ++ M
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hDlen : Lng (diagSeq 0 (m - 1)) = m := by
    simp [diagSeq]
    omega
  have hNlen : Lng N = m + Lng M := by simp [N, hDlen]
  have hmN : m < Lng N := by omega
  have hmend : m ≤ Lng N - 1 := by omega
  have hend : Lng N - 1 < Lng N := by omega
  have hseg := RedCondA_seg N m (Lng N - 1) hmend hend (by simpa [N] using hA)
  have hdrop : N.drop m = M := by simp [N, hDlen]
  calc
    RedCondA M = RedCondA (N.drop m) := by rw [hdrop]
    _ = RedCondA (seg N m (Lng N - 1)) := by rw [drop_eq_seg N m hmN]
    _ = true := hseg

/-! ## Coefficient conditions on `Pred`

The last column plays no role in any parent edge whose target lies strictly
below it.  We record the corresponding `take` fact once; it is the common
input to both coefficient conditions and, later, to reducedness of `Pred`. -/

theorem hasParent_take_of_lt (M : PS) (n i j : ℕ)
    (hn : n ≤ Lng M) (hj : j < n) :
    hasParent (M.take n) i j = hasParent M i j := by
  apply Bool.eq_iff_iff.mpr
  rw [hasParent_iff_unique_fseq, hasParent_iff_unique_fseq]
  constructor
  · rintro ⟨p, hp, huniq⟩
    have hpj : p < j := (nextR_implies_row0 (M.take n) i p j hp).1
    have hpn : p < n := hpj.trans hj
    have hpM : nextR M i p j = true := by
      simpa only [nextR_take_adm M n i p j hn hpn hj] using hp
    refine ⟨p, hpM, ?_⟩
    intro q hqM
    have hqj : q < j := (nextR_implies_row0 M i q j hqM).1
    have hqn : q < n := hqj.trans hj
    have hq : nextR (M.take n) i q j = true := by
      simpa only [nextR_take_adm M n i q j hn hqn hj] using hqM
    exact huniq q hq
  · rintro ⟨p, hpM, huniq⟩
    have hpj : p < j := (nextR_implies_row0 M i p j hpM).1
    have hpn : p < n := hpj.trans hj
    have hp : nextR (M.take n) i p j = true := by
      simpa only [nextR_take_adm M n i p j hn hpn hj] using hpM
    refine ⟨p, hp, ?_⟩
    intro q hq
    have hqj : q < j := (nextR_implies_row0 (M.take n) i q j hq).1
    have hqn : q < n := hqj.trans hj
    have hqM : nextR M i q j = true := by
      simpa only [nextR_take_adm M n i q j hn hqn hj] using hq
    exact huniq q hqM

/-- `RedCondA` is inherited by deletion of the final column. -/
theorem RedCondA_Pred (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) : RedCondA (Pred M) = true := by
  by_cases hlen : Lng M ≤ 1
  · simpa [Pred, hlen] using hA
  · have hgt : 1 < Lng M := by omega
    have hPred : Pred M = M.take (Lng M - 1) := by
      simp [Pred, hlen, List.dropLast_eq_take]
    apply RedCondA_intro
    intro i j hi hj hp
    have hjTake : j < Lng M - 1 := by
      rw [hPred] at hj
      simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)] at hj
      exact hj
    have hjM : j < Lng M := hjTake.trans_le (Nat.sub_le _ _)
    have hpM : hasParent M i j = true := by
      rw [hPred, hasParent_take_of_lt M (Lng M - 1) i j (by omega) hjTake] at hp
      exact hp
    have hbase := RedCondA_apply M hA i j hi hjM hpM
    let p := parent (Pred M) i j
    have hnextP : nextR (Pred M) i p j = true :=
      hasParent_next_fseq (Pred M) i j hp
    have hpj : p < j := (nextR_implies_row0 (Pred M) i p j hnextP).1
    have hpn : p < Lng M - 1 := hpj.trans hjTake
    have hnextM : nextR M i p j = true := by
      rw [hPred] at hnextP
      simpa only [nextR_take_adm M (Lng M - 1) i p j (by omega) hpn hjTake]
        using hnextP
    obtain ⟨q, hq, huniqM⟩ :=
      (hasParent_iff_unique_fseq M i j).mp hpM
    have hpq : p = q := huniqM p hnextM
    have hparM : parent M i j = p := by
      apply parent_eq_of_unique_fseq M i j p hnextM
      intro y hy
      exact (huniqM y hy).trans hpq.symm
    have hparTake : parent (M.take (Lng M - 1)) i j = p := by
      dsimp [p]
      rw [← hPred]
    rw [hPred, hparTake]
    rw [entry_take M (Lng M - 1) i p hpn,
      entry_take M (Lng M - 1) i j hjTake]
    simpa [hparM] using hbase

/-- `RedCondB` is inherited by deletion of the final column. -/
theorem RedCondB_Pred (M : PS) (hM : TPS M)
    (hB : RedCondB M = true) : RedCondB (Pred M) = true := by
  by_cases hlen : Lng M ≤ 1
  · simpa [Pred, hlen] using hB
  · have hgt : 1 < Lng M := by omega
    have hPred : Pred M = M.take (Lng M - 1) := by
      simp [Pred, hlen, List.dropLast_eq_take]
    simp only [RedCondB, List.all_eq_true, List.mem_range]
    intro j hj
    have hjTake : j < Lng M - 1 := by
      rw [hPred] at hj
      simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)] at hj
      omega
    have hjM : j < Lng M - 1 + 1 := by omega
    have hBall := hB
    simp only [RedCondB, List.all_eq_true, List.mem_range] at hBall
    have hBj := hBall j hjM
    rw [hPred, hasParent_take_of_lt M (Lng M - 1) 0 j (by omega) hjTake,
      entry_take M (Lng M - 1) 0 j hjTake,
      entry_take M (Lng M - 1) 1 j hjTake]
    exact hBj

private theorem P_component_length_lt_of_multi (M : PS) (J : ℕ)
    (hM : TPS M) (hmulti : multiT M = true)
    (hJ : J < (P M).length) :
    Lng ((P M).getD J []) < Lng M := by
  have hQtwo : 1 < (P M).length :=
    (P_components_multi_iff M hM).mp hmulti
  obtain ⟨_, hBpos, hBend⟩ := P_block_data M J hM hJ
  by_cases hJ0 : J = 0
  · subst J
    obtain ⟨_, hB1pos, hB1end⟩ :=
      P_block_data M 1 hM (by omega)
    have hsum0 : (IdxSum (P M)).getD 0 0 = 0 := by
      simpa using idxSum_getD (P M) 0 (Nat.zero_le _)
    have hdiff0 := idxSum_diff (P M) 0 (by omega : 0 < (P M).length)
    have hstart1 :
        (IdxSum (P M)).getD 1 0 = Lng ((P M).getD 0 []) := by
      rw [hdiff0, hsum0]
      omega
    have hB1end' :
        (IdxSum (P M)).getD 1 0 + Lng ((P M).getD 1 []) - 1 < Lng M :=
      hB1end
    omega
  · have hJpos : 0 < J := Nat.pos_of_ne_zero hJ0
    have hprev : J - 1 < (P M).length := by omega
    have hprevpos : 0 < Lng ((P M).getD (J - 1) []) :=
      P_component_nonempty M (J - 1) hM hprev
    have hdiff := idxSum_diff (P M) (J - 1) hprev
    have hstartpos : 0 < (IdxSum (P M)).getD J 0 := by
      rw [show J = (J - 1) + 1 by omega, hdiff]
      omega
    omega

/-- The only genuinely new column in the `Pred` induction for condition (A)
is the final one.  This predicate isolates that local obligation. -/
def RedCondATop (M : PS) : Prop :=
  ∀ i, i < 2 → hasParent M i (Lng M - 1) = true →
    entry M i (parent M i (Lng M - 1)) + 1 =
      entry M i (Lng M - 1)

theorem nextR0_consecutive_of_strict (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he : entry M 0 j < entry M 0 (j + 1)) :
    nextR M 0 j (j + 1) = true := by
  simp only [nextR, if_pos, nextrel0, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · have hk' : k = j + 1 := by omega
    subst k
    simp
  · simp [hjk]

/-- The final-column step is immediate when the trunk occupies the entire
core sequence: fixedness makes every coefficient at column `j` equal to `j`.
-/
theorem RTPS_mono_core_RedCondATop_trunk (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0)
    (htr : TrMax M = Lng M - 1) : RedCondATop M := by
  have hM : TPS M := RTPS_TPS M hR
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hlong : 1 < Lng M := by
    by_contra hnot
    have hOne : Lng M = 1 := by omega
    have hz : zeroT M = true := by simp [zeroT, hOne, he10]
    have hh := hmono
    simp [monoT, hz] at hh
  have hfix : Red M = M := RTPS_Red_eq M hR
  have hentry (i j : ℕ) (hj : j < Lng M) : entry M i j = j := by
    have hh := Red_core_prefix_diag M hmono ⟨he00, he10⟩ i j (by omega)
    rw [hfix] at hh
    exact hh
  intro i hi hp
  let j₁ := Lng M - 1
  let p := parent M i j₁
  have hj₁L : j₁ < Lng M := by dsimp [j₁]; omega
  have hnext : nextR M i p j₁ = true := by
    simpa [p, j₁] using hasParent_next_fseq M i (Lng M - 1) hp
  have hpj₁ : p < j₁ := (nextR_implies_row0 M i p j₁ hnext).1
  have hsucc : p + 1 = j₁ := by
    by_contra hne
    have hplt : p + 1 < j₁ := by omega
    by_cases hi0 : i = 0
    · have hh := hnext
      simp only [nextR, if_pos hi0, nextrel0, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true] at hh
      have hbad := hh.2 (p + 1) (by simp; omega)
      have hpnext : p < p + 1 := by omega
      simp [hpnext] at hbad
      rw [hentry 0 j₁ hj₁L,
        hentry 0 (p + 1) (by omega)] at hbad
      omega
    · have hi1 : i = 1 := by omega
      have hh := hnext
      simp only [nextR, if_neg hi0, nextrel1, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true] at hh
      let q := j₁ - 1
      have hqsucc : q + 1 = j₁ := by dsimp [q]; omega
      have hqL : q < Lng M := by omega
      have hqnext : nextR M 0 q j₁ = true := by
        rw [← hqsucc]
        apply nextR0_consecutive_of_strict M q
        · simpa [hqsucc] using hj₁L
        · rw [hentry 0 q hqL, hentry 0 (q + 1) (by omega)]
          omega
      have hqle : le0 M q j₁ = true := by
        simpa [leR] using nextR0_leR M q j₁ hqnext
      have hpq : p < q := by dsimp [q]; omega
      have hbad := hh.2 q (by simp [q]; omega)
      simp [hpq, hqle] at hbad
      rw [hentry 1 j₁ hj₁L, hentry 1 q hqL] at hbad
      dsimp [q] at hbad
      omega
  rw [hentry i p (by omega), hentry i j₁ hj₁L]
  exact hsucc

private theorem parent_Pred_eq_of_lt (M : PS) (i j : ℕ)
    (hlen : 1 < Lng M) (hj : j < Lng M - 1)
    (hp : hasParent M i j = true) :
    parent (Pred M) i j = parent M i j := by
  have hPred : Pred M = M.take (Lng M - 1) := Pred_eq_take M hlen
  have htake : hasParent (M.take (Lng M - 1)) i j = hasParent M i j :=
    hasParent_take_of_lt M (Lng M - 1) i j (by omega) hj
  obtain ⟨p, hpM, huniqM⟩ := (hasParent_iff_unique_fseq M i j).mp hp
  have hpj : p < j := (nextR_implies_row0 M i p j hpM).1
  have hpTake : nextR (M.take (Lng M - 1)) i p j = true := by
    simpa only [nextR_take_adm M (Lng M - 1) i p j (by omega)
      (hpj.trans hj) hj] using hpM
  have hparM : parent M i j = p :=
    parent_eq_of_unique_fseq M i j p hpM huniqM
  have hparTake : parent (M.take (Lng M - 1)) i j = p := by
    apply parent_eq_of_unique_fseq (M.take (Lng M - 1)) i j p hpTake
    intro q hq
    have hqj : q < j := (nextR_implies_row0 (M.take (Lng M - 1)) i q j hq).1
    have hqM : nextR M i q j = true := by
      simpa only [nextR_take_adm M (Lng M - 1) i q j (by omega)
        (hqj.trans hj) hj] using hq
    exact huniqM q hqM
  rw [hPred, hparTake, hparM]

/-- Conditional core of the forward keystone.  If the final-column
coefficient step is available uniformly for reduced mono sequences beginning
with `(0,0)`, all of condition (A) follows by deleting final columns. -/
theorem RTPS_mono_core_RedCondA_of_top
    (topStep : ∀ N, RTPS N → monoT N = true →
      entry N 0 0 = 0 → entry N 1 0 = 0 → RedCondATop N)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (he00 : entry M 0 0 = 0) (he10 : entry M 1 0 = 0) :
    RedCondA M = true := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      apply RedCondA_intro
      intro i j hi hj hp
      have hi2 : i < 2 := by omega
      by_cases hjtop : j = Lng M - 1
      · subst j
        exact topStep M hR hmono he00 he10 i hi2 hp
      · have hjlt : j < Lng M - 1 := by omega
        by_cases hsmall : Lng M ≤ 2
        · have hj0 : j = 0 := by omega
          subst j
          rw [no_parent_zero M i] at hp
          contradiction
        · have hlen : 1 < Lng M := by omega
          have hlong : 2 < Lng M := by omega
          have hpredR : RTPS (Pred M) := RTPS_Pred M hR
          have hpredMono : monoT (Pred M) = true :=
            monoT_Pred_long M hM hmono hlong
          have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
          have hpredLt : Lng (Pred M) < n := by rw [hpredLen, ← hn]; omega
          have he00Pred : entry (Pred M) 0 0 = 0 := by
            rw [Pred_eq_take M hlen, entry_take M (Lng M - 1) 0 0 (by omega)]
            exact he00
          have he10Pred : entry (Pred M) 1 0 = 0 := by
            rw [Pred_eq_take M hlen, entry_take M (Lng M - 1) 1 0 (by omega)]
            exact he10
          have hAPred := ih (Lng (Pred M)) hpredLt (Pred M) hpredR
            hpredMono he00Pred he10Pred rfl
          have hpPred : hasParent (Pred M) i j = true := by
            rw [Pred_eq_take M hlen,
              hasParent_take_of_lt M (Lng M - 1) i j (by omega) hjlt]
            exact hp
          have hstep := RedCondA_apply (Pred M) hAPred i j hi
            (by rw [hpredLen]; exact hjlt) hpPred
          have hpar := parent_Pred_eq_of_lt M i j hlen hjlt hp
          rw [hpar] at hstep
          have hparlt : parent M i j < Lng M - 1 := by
            have hnext := hasParent_next_fseq M i j hp
            have := (nextR_implies_row0 M i (parent M i j) j hnext).1
            omega
          rw [Pred_eq_take M hlen,
            entry_take M (Lng M - 1) i (parent M i j) hparlt,
            entry_take M (Lng M - 1) i j hjlt] at hstep
          exact hstep

/-- Uniform reduction of the full forward implication to the core
final-column step.  The positive left end is moved to zero by the diagonal
prefix lemma, while the multi branch recurses on strictly shorter `P`
components. -/
theorem RTPS_condAB_of_core_top
    (topStep : ∀ N, RTPS N → monoT N = true →
      entry N 0 0 = 0 → entry N 1 0 = 0 → RedCondATop N)
    (M : PS) (hR : RTPS M) :
    RedCondA M = true ∧ RedCondB M = true := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      by_cases hz : zeroT M = true
      · exact (RTPS_iff_condAB_zeroT M hM hz).mp hR
      · have hz' : zeroT M = false := Bool.eq_false_of_not_eq_true hz
        by_cases hmulti : multiT M = true
        · apply RedCondAB_of_P_components M hM
          intro J hJ
          let B := (P M).getD J []
          have hBR : RTPS B :=
            (RTPS_iff_P_components M hM).mp hR J hJ
          have hBL : Lng B < n := by
            rw [← hn]
            simpa [B] using
              P_component_length_lt_of_multi M J hM hmulti hJ
          exact ih (Lng B) hBL B hBR rfl
        · have hmulti' : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
          have hmono : monoT M = true := by
            have hh := hmulti'
            simp [multiT, hz'] at hh
            exact hh
          have hB : RedCondB M = true := RTPS_mono_RedCondB M hR hmono
          have hhead : entry M 0 0 = entry M 1 0 :=
            RTPS_mono_head_eq M hR hmono
          have hA : RedCondA M = true := by
            by_cases hm : entry M 1 0 = 0
            · exact RTPS_mono_core_RedCondA_of_top topStep M hR hmono
                (hhead.trans hm) hm
            · have hmpos : 0 < entry M 1 0 := Nat.pos_of_ne_zero hm
              let N := diagSeq 0 (entry M 1 0 - 1) ++ M
              have hNfacts := RTPS_diag_prefix M 0 hR hmono (Nat.zero_le _)
              have hNR : RTPS N := by simpa [N, hmpos] using hNfacts.1
              have hNmono : monoT N = true := by
                simpa [N, hmpos] using hNfacts.2
              have hN00 : entry N 0 0 = 0 := by
                simp [N, diagSeq, entry]
              have hN10 : entry N 1 0 = 0 := by
                simp [N, diagSeq, entry]
              have hNA := RTPS_mono_core_RedCondA_of_top topStep N hNR
                hNmono hN00 hN10
              exact RedCondA_of_diag_prefix M (entry M 1 0) hM hmpos
                (by simpa [N] using hNA)
          exact ⟨hA, hB⟩

/-- Sharpened forward reduction: the full implication now depends only on the
non-trunk core case of the final-column step. -/
theorem RTPS_condAB_of_core_nontrunk_top
    (nontrunkStep : ∀ N, RTPS N → monoT N = true →
      entry N 0 0 = 0 → entry N 1 0 = 0 →
      TrMax N ≠ Lng N - 1 → RedCondATop N)
    (M : PS) (hR : RTPS M) :
    RedCondA M = true ∧ RedCondB M = true := by
  apply RTPS_condAB_of_core_top (M := M) (hR := hR)
  intro N hNR hmono he00 he10
  by_cases htr : TrMax N = Lng N - 1
  · exact RTPS_mono_core_RedCondATop_trunk N hNR hmono he00 he10 htr
  · exact nontrunkStep N hNR hmono he00 he10 htr

/-- Backward half of the §6.6 keystone: the two executable coefficient
conditions force `Red` to fix every nonempty pair sequence. -/
theorem RTPS_of_condAB (M : PS) (hM : TPS M)
    (hA : RedCondA M = true) (hB : RedCondB M = true) : RTPS M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hmulti : multiT M = true
      · apply (RTPS_iff_P_components M hM).mpr
        intro J hJ
        let B := (P M).getD J []
        have hBT : TPS B := by
          apply List.ne_nil_of_length_pos
          simpa [B] using P_component_nonempty M J hM hJ
        obtain ⟨hBA, hBB⟩ := RedCondAB_P_component M J hM hA hB hJ
        have hBL : Lng B < n := by
          rw [← hn]
          simpa [B] using P_component_length_lt_of_multi M J hM hmulti hJ
        exact ih (Lng B) hBL B hBT hBA hBB rfl
      · have hnm : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
        exact RTPS_of_condAB_nonmulti M hM hA hB hnm

#print axioms RTPS_of_condAB_nonmulti
#print axioms RTPS_mono_head_eq
#print axioms RTPS_mono_RedCondB
#print axioms RTPS_iff_condAB_zeroT
#print axioms RTPS_iff_condAB_multi
#print axioms RedCondA_of_diag_prefix
#print axioms RedCondA_Pred
#print axioms RedCondB_Pred
#print axioms RTPS_mono_core_RedCondA_of_top
#print axioms RTPS_mono_core_RedCondATop_trunk
#print axioms RTPS_condAB_of_core_nontrunk_top
#print axioms RTPS_of_condAB

end PSS
