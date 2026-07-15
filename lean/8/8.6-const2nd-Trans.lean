import «8».«8.1-diagSeq-Trans»
import «6».«6.6-reduced-iff-condAB»

/-!
# §8.6 補題（公差 `(1,0)` のペア数列の `Trans`）

- 原文: `tmp/content.md` article 5496
- 訂正: なし
- Isabelle: `m_8_6_const2nd_Trans`, `p_8_6_const2nd_Trans`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- The constant-second-row sequence `((m+j,u))_{j=0}^{j₁}`. -/
def const2ndSeq (m u j₁ : ℕ) : PS :=
  (List.range (j₁ + 1)).map fun j => (m + j, u)

/-- The Buchholz tower `D_u^k 0`. -/
def const2ndTower (u : ℕ) : ℕ → BT
  | 0 => BZero
  | k + 1 => Dprin (u : ℕ∞) (const2ndTower u k)

@[simp] private theorem const2ndTower_zero (u : ℕ) :
    const2ndTower u 0 = BZero := rfl

@[simp] private theorem const2ndTower_succ (u k : ℕ) :
    const2ndTower u (k + 1) =
      Dprin (u : ℕ∞) (const2ndTower u k) := rfl

private theorem flatBT_const2ndTower (u k : ℕ) :
    flatBT (const2ndTower u k) =
      List.replicate k (.dsym (u : ℕ∞)) ++ [.zero] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change .dsym (u : ℕ∞) :: flatBT (const2ndTower u k) =
        List.replicate (k + 1) (.dsym (u : ℕ∞)) ++ [.zero]
      rw [ih]
      rfl

private theorem scbContexts_const2ndTower_head (u k : ℕ) :
    (scbContexts (const2ndTower u (k + 1))
      (flatBT (const2ndTower u 1))).head? =
        some (List.replicate k (.dsym (u : ℕ∞)), []) := by
  have hDself :
      (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
    change ((u : ℕ∞) == (u : ℕ∞)) = true
    exact beq_self_eq_true _
  have hZself : (Sym.zero == Sym.zero) = true := rfl
  have hDZ : (Sym.dsym (u : ℕ∞) == Sym.zero) = false := rfl
  unfold scbContexts
  rw [flatBT_const2ndTower u (k + 1), flatBT_const2ndTower u 1]
  rw [List.head?_filterMap]
  apply List.findSome?_eq_some_iff.mpr
  refine ⟨List.range k, k, [], ?_, ?_, ?_⟩
  · simpa [Nat.succ_eq_add_one] using (List.range_succ (n := k))
  · have hkLen : k ≤ (List.replicate (k + 1)
        (Sym.dsym (u : ℕ∞))).length := by simp
    have hdropk :
        List.drop k (List.replicate (k + 1) (Sym.dsym (u : ℕ∞)) ++
          [Sym.zero]) = [Sym.dsym (u : ℕ∞), Sym.zero] := by
      rw [List.drop_append_of_le_length hkLen, List.drop_replicate]
      have hsub : k + 1 - k = 1 := by omega
      rw [hsub]
      rfl
    have htakek :
        List.take k (List.replicate (k + 1) (Sym.dsym (u : ℕ∞)) ++
          [Sym.zero]) = List.replicate k (Sym.dsym (u : ℕ∞)) := by
      rw [List.take_append_of_le_length hkLen, List.take_replicate,
        Nat.min_eq_left (by omega : k ≤ k + 1)]
    have hdropend :
        List.drop (k + 2)
            (List.replicate (k + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero]) =
          [] := by
      apply List.drop_eq_nil_of_le
      simp
    simp [hdropk, htakek, hdropend, hDself, hZself, isPTBStr,
      parseBPAux, parseBTAux, dfree_BP, dfree_BT, dfree_BPList, BZero,
      ENat.coe_ne_top]
  · intro i hi
    have hi' : i < k := by simpa using hi
    have hiLen : i ≤ (List.replicate (k + 1)
        (Sym.dsym (u : ℕ∞))).length := by simp; omega
    have htwo : 2 ≤ (List.replicate (k + 1 - i)
        (Sym.dsym (u : ℕ∞))).length := by simp; omega
    have htake :
        List.take 2 (List.drop i
          (List.replicate (k + 1) (Sym.dsym (u : ℕ∞)) ++ [Sym.zero])) =
          [Sym.dsym (u : ℕ∞), Sym.dsym (u : ℕ∞)] := by
      rw [List.drop_append_of_le_length hiLen, List.drop_replicate,
        List.take_append_of_le_length htwo, List.take_replicate,
        Nat.min_eq_left (by omega : 2 ≤ k + 1 - i)]
      rfl
    simp [htake, hDself, hDZ]

private theorem parseBTAux_const2ndTower (u k : ℕ) :
    parseBTAux (k + 2)
        (List.replicate k (Sym.dsym (u : ℕ∞)) ++ [Sym.zero]) =
      some (const2ndTower u k, []) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change parseBTAux (k + 3)
          (Sym.dsym (u : ℕ∞) ::
            (List.replicate k (Sym.dsym (u : ℕ∞)) ++ [Sym.zero])) =
        some (const2ndTower u (k + 1), [])
      rw [parseBTAux]
      rw [ih]
      rfl

private theorem unflatBT_flat_const2ndTower (u k : ℕ) :
    unflatBT (flatBT (const2ndTower u k)) = const2ndTower u k := by
  rw [flatBT_const2ndTower]
  unfold unflatBT
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  rw [show k + 1 + 1 = k + 2 by omega,
    parseBTAux_const2ndTower]

private theorem replaceScb_const2ndTower (u k : ℕ) :
    replaceScb (const2ndTower u (k + 1)) (const2ndTower u 1)
        (const2ndTower u 2) =
      const2ndTower u (k + 2) := by
  unfold replaceScb
  rw [scbContexts_const2ndTower_head]
  have hflat :
      List.replicate k (Sym.dsym (u : ℕ∞)) ++
          flatBT (const2ndTower u 2) ++ [] =
        flatBT (const2ndTower u (k + 2)) := by
    rw [flatBT_const2ndTower, flatBT_const2ndTower]
    simp only [List.append_nil]
    rw [← List.append_assoc, ← List.replicate_add]
  simp only
  rw [hflat, unflatBT_flat_const2ndTower]

private theorem length_const2ndSeq (m u j₁ : ℕ) :
    Lng (const2ndSeq m u j₁) = j₁ + 1 := by
  simp [const2ndSeq]

private theorem getElem?_const2ndSeq (m u j₁ j : ℕ)
    (hj : j < j₁ + 1) :
    (const2ndSeq m u j₁)[j]? = some (m + j, u) := by
  rw [List.getElem?_eq_getElem]
  · congr 1
    simp [const2ndSeq, List.getElem_map]
  · simpa [length_const2ndSeq] using hj

private theorem entry0_const2ndSeq (m u j₁ j : ℕ)
    (hj : j < j₁ + 1) :
    entry (const2ndSeq m u j₁) 0 j = m + j := by
  simp [entry, getElem?_const2ndSeq m u j₁ j hj]

private theorem entry1_const2ndSeq (m u j₁ j : ℕ)
    (hj : j < j₁ + 1) :
    entry (const2ndSeq m u j₁) 1 j = u := by
  simp [entry, getElem?_const2ndSeq m u j₁ j hj]

private theorem const2ndSeq_succ_snoc (m u j₁ : ℕ) :
    const2ndSeq m u (j₁ + 1) =
      const2ndSeq m u j₁ ++ [(m + (j₁ + 1), u)] := by
  simp [const2ndSeq, List.range_succ, List.map_append]

private theorem Pred_const2ndSeq_succ (m u j₁ : ℕ) :
    Pred (const2ndSeq m u (j₁ + 1)) = const2ndSeq m u j₁ := by
  rw [Pred, if_neg (by rw [length_const2ndSeq]; omega),
    const2ndSeq_succ_snoc]
  simp

private theorem nextR0_const2ndSeq_step (m u j₁ j : ℕ)
    (hj : j + 1 < j₁ + 1) :
    nextR (const2ndSeq m u j₁) 0 j (j + 1) = true := by
  simp only [nextR, if_pos]
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, by omega⟩, ?_⟩, ?_⟩
  · rw [length_const2ndSeq]
    omega
  · rw [length_const2ndSeq]
    omega
  · rw [entry0_const2ndSeq m u j₁ j (by omega),
      entry0_const2ndSeq m u j₁ (j + 1) hj]
    omega
  · intro k hk
    by_cases hjk : j < k
    · have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk]

private theorem const2ndSeq_parent_row0 (m u j₁ j : ℕ)
    (hjpos : 0 < j) (hj : j < j₁ + 1) :
    hasParent (const2ndSeq m u j₁) 0 j = true ∧
      parent (const2ndSeq m u j₁) 0 j = j - 1 := by
  have hstep : nextR (const2ndSeq m u j₁) 0 (j - 1) j = true := by
    have hs := nextR0_const2ndSeq_step m u j₁ (j - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hs
  have hparent := parent_eq_of_nextR0 (const2ndSeq m u j₁) (j - 1) j hstep
  have hhas : hasParent (const2ndSeq m u j₁) 0 j = true :=
    (hasParent_iff_unique_fseq (const2ndSeq m u j₁) 0 j).mpr
      ⟨j - 1, hstep, fun q hq =>
        row0_parent_unique (const2ndSeq m u j₁) q (j - 1) j hq hstep⟩
  exact ⟨hhas, hparent⟩

private theorem const2ndSeq_no_row1_parent (m u j₁ j : ℕ) :
    hasParent (const2ndSeq m u j₁) 1 j = false := by
  apply Bool.eq_false_iff.mpr
  intro hhas
  obtain ⟨p, hp, _⟩ :=
    (hasParent_iff_unique_fseq (const2ndSeq m u j₁) 1 j).mp hhas
  have hn : nextrel1 (const2ndSeq m u j₁) p j = true := by
    simpa [nextR] using hp
  have hh := hn
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hpL := hh.1.1.1.1.1
  have hjL := hh.1.1.1.1.2
  have hlt := hh.1.1.2
  rw [entry1_const2ndSeq m u j₁ p (by simpa [length_const2ndSeq] using hpL),
    entry1_const2ndSeq m u j₁ j (by simpa [length_const2ndSeq] using hjL)] at hlt
  omega

private theorem nextR1_const2ndSeq_false (m u j₁ a b : ℕ) :
    nextR (const2ndSeq m u j₁) 1 a b = false := by
  apply Bool.eq_false_iff.mpr
  intro hn
  have hr : nextrel1 (const2ndSeq m u j₁) a b = true := by
    simpa [nextR] using hn
  have hh := hr
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haL : a < j₁ + 1 := by
    simpa [length_const2ndSeq] using hh.1.1.1.1.1
  have hbL : b < j₁ + 1 := by
    simpa [length_const2ndSeq] using hh.1.1.1.1.2
  have hlt := hh.1.1.2
  rw [entry1_const2ndSeq m u j₁ a haL,
    entry1_const2ndSeq m u j₁ b hbL] at hlt
  omega

private theorem adm_const2ndSeq (m u j₁ j : ℕ) (hj : j ≤ j₁) :
    adm (const2ndSeq m u j₁) j = true := by
  have hprev := nextR1_const2ndSeq_false m u j₁ (j - 1) j
  have hnext := nextR1_const2ndSeq_false m u j₁ j (j + 1)
  simp [adm, nadm, length_const2ndSeq, hprev, hnext]
  omega

private theorem RedCondA_const2ndSeq (m u j₁ : ℕ) :
    RedCondA (const2ndSeq m u j₁) = true := by
  simp only [RedCondA, List.all_eq_true, List.mem_range]
  intro i hi j hj
  by_cases hp : hasParent (const2ndSeq m u j₁) i j = true
  · have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · have hn := nextR_parent0_of_hasParent (const2ndSeq m u j₁) j hp
      have hh : nextrel0 (const2ndSeq m u j₁)
          (parent (const2ndSeq m u j₁) 0 j) j = true := by
        simpa [nextR] using hn
      have h := hh
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
      have hjpos : 0 < j := by omega
      have hjL : j < j₁ + 1 := by
        simpa [length_const2ndSeq] using h.1.1.1.2
      have hparent := (const2ndSeq_parent_row0 m u j₁ j hjpos hjL).2
      simp [hp, hparent, entry0_const2ndSeq m u j₁ j hjL,
        entry0_const2ndSeq m u j₁ (j - 1) (by omega)]
      omega
    · exfalso
      exact (Bool.eq_false_iff.mp
        (const2ndSeq_no_row1_parent m u j₁ j)) hp
  · simp [hp]

private theorem RedCondB_canonical_const2ndSeq (u j₁ : ℕ) :
    RedCondB (const2ndSeq u u j₁) = true := by
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  by_cases hjzero : j = 0
  · subst j
    simp [entry0_const2ndSeq, entry1_const2ndSeq]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hjL : j < j₁ + 1 := by
      rw [length_const2ndSeq] at hj
      omega
    simp [(const2ndSeq_parent_row0 u u j₁ j hjpos hjL).1]

private theorem leR0_refl_const2nd (M : PS) (j : ℕ) (hj : j < Lng M) :
    leR M 0 j j = true := by
  have haux : le0Aux M (Lng M) j j = true := by
    cases hL : Lng M <;> simp [le0Aux]
  simp [leR, le0, hj, haux]

private theorem leR0_const2ndSeq_prefix (m u j₁ b : ℕ)
    (hb : b < j₁ + 1) :
    leR (const2ndSeq m u j₁) 0 0 b = true := by
  let M := const2ndSeq m u j₁
  have hM : TPS M := by simp [TPS, M, const2ndSeq]
  induction b with
  | zero =>
      apply leR0_refl_const2nd
      rw [length_const2ndSeq]
      omega
  | succ b ih =>
      have hle : leR M 0 0 b = true := ih (by omega)
      have hn : nextR M 0 b (b + 1) = true := by
        simpa [M] using nextR0_const2ndSeq_step m u j₁ b (by omega)
      exact row0_transitive M 0 b (b + 1) hM hle
        (nextR0_leR M b (b + 1) hn)

private theorem monoT_const2ndSeq (m u j₁ : ℕ)
    (hpos : 0 < j₁ ∨ 0 < u) :
    monoT (const2ndSeq m u j₁) = true := by
  have hnz : zeroT (const2ndSeq m u j₁) = false := by
    apply Bool.eq_false_iff.mpr
    intro hz
    have hh : j₁ = 0 ∧ u = 0 := by
      simpa [zeroT, length_const2ndSeq, entry1_const2ndSeq] using hz
    omega
  simp only [monoT, hnz, Bool.not_false, Bool.true_and]
  have hle := leR0_const2ndSeq_prefix m u j₁ j₁ (by omega)
  simpa [length_const2ndSeq] using hle

private theorem nonmulti_const2ndSeq (m u j₁ : ℕ) :
    multiT (const2ndSeq m u j₁) = false := by
  by_cases hzero : j₁ = 0 ∧ u = 0
  · rcases hzero with ⟨rfl, rfl⟩
    have hz : zeroT (const2ndSeq m 0 0) = true := by
      simp [zeroT, length_const2ndSeq, entry1_const2ndSeq]
    simp [multiT, hz]
  · have hpos : 0 < j₁ ∨ 0 < u := by omega
    have hm := monoT_const2ndSeq m u j₁ hpos
    simp [multiT, hm]

private theorem canonical_const2ndSeq_reduced (u j₁ : ℕ) :
    RTPS (const2ndSeq u u j₁) := by
  exact RTPS_of_condAB_nonmulti (const2ndSeq u u j₁)
    (by simp [TPS, const2ndSeq])
    (RedCondA_const2ndSeq u u j₁)
    (RedCondB_canonical_const2ndSeq u j₁)
    (nonmulti_const2ndSeq u u j₁)

private theorem canonical_step_indices (u j₁ : ℕ) :
    let M := const2ndSeq u u (j₁ + 1)
    transJ1 M = j₁ + 1 ∧ transJ0 M = j₁ ∧
      Adm M (transJ0 M) = j₁ ∧
      entry M 1 (transJ1 M) = u ∧
      entry M 1 (transJ0 M) = u := by
  let M := const2ndSeq u u (j₁ + 1)
  have hL : Lng M = j₁ + 2 := by simp [M, length_const2ndSeq]
  have hjlast : j₁ + 1 < (j₁ + 1) + 1 := by omega
  have hp := (const2ndSeq_parent_row0 u u (j₁ + 1) (j₁ + 1)
    (by omega) hjlast).2
  have hadm : adm M j₁ = true := by
    simpa [M] using adm_const2ndSeq u u (j₁ + 1) j₁ (by omega)
  have hj1 : transJ1 M = j₁ + 1 := by
    change Lng M - 1 = j₁ + 1
    rw [hL]
    omega
  have hj0 : transJ0 M = j₁ := by
    change parent M 0 (Lng M - 1) = j₁
    rw [hL]
    simpa [M] using hp
  refine ⟨hj1, hj0, ?_, ?_, ?_⟩
  · rw [hj0]
    have hadm' : adm (const2ndSeq u u (j₁ + 1)) j₁ = true := by
      simpa [M] using hadm
    simp [Adm, hadm']
  · rw [hj1]
    exact entry1_const2ndSeq u u (j₁ + 1) (j₁ + 1) (by omega)
  · rw [hj0]
    exact entry1_const2ndSeq u u (j₁ + 1) j₁ (by omega)

private theorem canonical_step_transC2 (u j₁ : ℕ) :
    transC2Core (const2ndSeq u u (j₁ + 1)) (u : ℕ∞) BZero =
      const2ndTower u 2 := by
  let M := const2ndSeq u u (j₁ + 1)
  have hi := canonical_step_indices u j₁
  have hp : parent M 0 (transJ1 M) = j₁ := by
    change transJ0 M = j₁
    simpa [M] using hi.2.1
  have hadm : adm M (parent M 0 (transJ1 M)) = true := by
    rw [hp]
    simpa [M] using adm_const2ndSeq u u (j₁ + 1) j₁ (by omega)
  have hc : (transCondI M || transCondIII M || transCondV M) = true := by
    by_cases hu : u = 0
    · have hI : transCondI M = true := by
        unfold transCondI
        change ((entry M 1 (transJ1 M) == 0) && adm M (transJ0 M)) = true
        rw [hi.2.2.2.1, show transJ0 M = j₁ by simpa [M] using hi.2.1]
        simp [hu, show adm M j₁ = true by simpa [hp] using hadm]
      simp [hI]
    · have hIII : transCondIII M = true := by
        have hupos : 0 < u := Nat.pos_of_ne_zero hu
        unfold transCondIII
        change ((0 < entry M 1 (transJ1 M)) &&
            (entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) &&
            adm M (transJ0 M)) = true
        rw [hi.2.2.2.1, hi.2.2.2.2]
        simp [hupos, show adm M (transJ0 M) = true by
          simpa [show transJ0 M = parent M 0 (transJ1 M) by rfl] using hadm]
      simp [hIII]
  have hc' :
      (transCondI (const2ndSeq u u (j₁ + 1)) ||
        transCondIII (const2ndSeq u u (j₁ + 1)) ||
        transCondV (const2ndSeq u u (j₁ + 1))) = true := by
    simpa [M] using hc
  unfold transC2Core
  simp only [hc', if_true]
  change Dprin (u : ℕ∞)
      (addBT BZero (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) =
    const2ndTower u 2
  rw [show entry M 1 (transJ1 M) = u by simpa [M] using hi.2.2.2.1]
  rfl

private theorem const2ndTower_beq_zero_false (u k : ℕ) :
    (const2ndTower u (k + 1) == BZero) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq := eq_of_beq h
  simp [const2ndTower, Dprin, BZero] at heq

private theorem canonical_singleton_aux (u fuel : ℕ) :
    TransAux (fuel + 1) (const2ndSeq u u 0) =
        (if u = 0 then BZero else const2ndTower u 1) ∧
      MarkAux (fuel + 1) (const2ndSeq u u 0) 0 =
        (if u = 0 then BZero else const2ndTower u 1) := by
  have hred : reduced (const2ndSeq u u 0) = true :=
    canonical_const2ndSeq_reduced u 0
  have hseq : const2ndSeq u u 0 = [(u, u)] := by
    simp [const2ndSeq]
  constructor
  · rw [TransAux]
    simp only [hred, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_pos (by
      change (transJ1 (const2ndSeq u u 0) == 0) = true
      have hj : transJ1 (const2ndSeq u u 0) = 0 := by
        change Lng (const2ndSeq u u 0) - 1 = 0
        rw [length_const2ndSeq]
      simp [hj])]
    simp [hseq, entry, const2ndTower]
  · rw [MarkAux]
    simp only [hred, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_pos (by
      change (transJ1 (const2ndSeq u u 0) == 0) = true
      have hj : transJ1 (const2ndSeq u u 0) = 0 := by
        change Lng (const2ndSeq u u 0) - 1 = 0
        rw [length_const2ndSeq]
      simp [hj])]
    simp [hseq, entry, const2ndTower]

private theorem canonical_rightmost_mark_aux (u j₁ fuel : ℕ)
    (hnonzero : ¬(j₁ = 0 ∧ u = 0)) :
    MarkAux (fuel + 1) (const2ndSeq u u j₁)
        (Lng (const2ndSeq u u j₁) - 1) =
      const2ndTower u 1 := by
  by_cases hj : j₁ = 0
  · subst j₁
    have hu : u ≠ 0 := by simpa using hnonzero
    simpa [length_const2ndSeq, hu] using
      (canonical_singleton_aux u fuel).2
  · have hjpos : 0 < j₁ := Nat.pos_of_ne_zero hj
    have hred : reduced (const2ndSeq u u j₁) = true :=
      canonical_const2ndSeq_reduced u j₁
    have hmono : monoT (const2ndSeq u u j₁) = true :=
      monoT_const2ndSeq u u j₁ (Or.inl hjpos)
    have hlen : 1 < Lng (const2ndSeq u u j₁) := by
      rw [length_const2ndSeq]
      omega
    have hr := MarkAux_rightmost_reduced_mono fuel
      (const2ndSeq u u j₁) hred hmono hlen
    have he : entry (const2ndSeq u u j₁) 1
        (Lng (const2ndSeq u u j₁) - 1) = u := by
      rw [length_const2ndSeq]
      apply entry1_const2ndSeq
      omega
    simpa [he, const2ndTower] using hr

private theorem canonical_step_aux (u j₁ fuel : ℕ)
    (hTrans : TransAux (fuel + 1) (const2ndSeq u u j₁) =
      if j₁ = 0 ∧ u = 0 then BZero else const2ndTower u (j₁ + 1)) :
    TransAux (fuel + 2) (const2ndSeq u u (j₁ + 1)) =
      const2ndTower u (j₁ + 2) := by
  let N := const2ndSeq u u j₁
  let M := const2ndSeq u u (j₁ + 1)
  have hred : reduced M = true := by
    simpa [M] using canonical_const2ndSeq_reduced u (j₁ + 1)
  have hmono : monoT M = true := by
    simpa [M] using monoT_const2ndSeq u u (j₁ + 1) (Or.inl (by omega))
  have hlen : 1 < Lng M := by
    rw [show M = const2ndSeq u u (j₁ + 1) from rfl,
      length_const2ndSeq]
    omega
  have hj1pos : transJ1 M ≠ 0 := by
    change Lng M - 1 ≠ 0
    omega
  have hPred : Pred M = N := by
    simpa [M, N] using Pred_const2ndSeq_succ u u j₁
  have hi := canonical_step_indices u j₁
  have hAdm : Adm M (transJ0 M) = j₁ := by simpa [M] using hi.2.2.1
  have he1 : entry M 1 (transJ1 M) = u := by simpa [M] using hi.2.2.2.1
  have hc2 : transC2Core M (u : ℕ∞) BZero = const2ndTower u 2 := by
    simpa [M] using canonical_step_transC2 u j₁
  have hfuel : fuel + 2 = (fuel + 1) + 1 := by omega
  change TransAux (fuel + 2) M = const2ndTower u (j₁ + 2)
  rw [hfuel, TransAux]
  simp only [hred, Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by
    intro h
    change (transJ1 M == 0) = true at h
    exact hj1pos (beq_iff_eq.mp h))]
  simp only [hmono, if_true]
  change (if (TransAux (fuel + 1) (Pred M) == BZero) = true then
      Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
    else
      replaceScb (TransAux (fuel + 1) (Pred M))
        (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))
        (transC2Core M
          (bpHeadV (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))
          (bpHeadT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))))) =
    const2ndTower u (j₁ + 2)
  by_cases hzero : j₁ = 0 ∧ u = 0
  · have hT : TransAux (fuel + 1) N = BZero := by
      simpa [N, hzero] using hTrans
    rw [hPred, hT, he1]
    simp [hzero.1, hzero.2, const2ndTower]
  · have hT : TransAux (fuel + 1) N = const2ndTower u (j₁ + 1) := by
      simpa [N, hzero] using hTrans
    have hMark : MarkAux (fuel + 1) N j₁ = const2ndTower u 1 := by
      have hm := canonical_rightmost_mark_aux u j₁ fuel hzero
      simpa [N, length_const2ndSeq] using hm
    have hbeq : (const2ndTower u (j₁ + 1) == BZero) = false :=
      const2ndTower_beq_zero_false u j₁
    have hvhead : bpHeadV (const2ndTower u 1) = (u : ℕ∞) := rfl
    have hthead : bpHeadT (const2ndTower u 1) = BZero := rfl
    rw [hPred, hAdm, hT, hMark]
    simp only [hbeq, Bool.false_eq_true, if_false, hvhead, hthead, hc2]
    exact replaceScb_const2ndTower u j₁

private theorem canonical_const2ndSeq_aux (u j₁ fuel : ℕ)
    (hfuel : j₁ + 1 ≤ fuel) :
    TransAux fuel (const2ndSeq u u j₁) =
      if j₁ = 0 ∧ u = 0 then BZero else const2ndTower u (j₁ + 1) := by
  induction j₁ generalizing fuel with
  | zero =>
      let g := fuel - 1
      have hfg : fuel = g + 1 := by dsimp [g]; omega
      rw [hfg]
      simpa using (canonical_singleton_aux u g).1
  | succ j₁ ih =>
      let g := fuel - 2
      have hfg : fuel = g + 2 := by dsimp [g]; omega
      have hchildFuel : j₁ + 1 ≤ g + 1 := by dsimp [g]; omega
      have hchild := ih (g + 1) hchildFuel
      rw [hfg]
      simpa using canonical_step_aux u j₁ g hchild

private theorem const2ndTower_eq_iterate (u k : ℕ) :
    const2ndTower u k =
      (Dprin (u : ℕ∞))^[k] BZero := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change Dprin (u : ℕ∞) (const2ndTower u k) =
        Dprin (u : ℕ∞) ((Dprin (u : ℕ∞))^[k] BZero)
      rw [ih]

private theorem Red_const2ndSeq (m u j₁ : ℕ) :
    Red (const2ndSeq m u j₁) = const2ndSeq u u j₁ := by
  rw [Red_rebase_nonmulti (const2ndSeq m u j₁)
    (by simp [TPS, const2ndSeq])
    (RedCondA_const2ndSeq m u j₁)
    (nonmulti_const2ndSeq m u j₁)]
  apply List.ext_getElem
  · simp [rebaseRow0, length_const2ndSeq]
  · intro j hjL hjR
    have hj : j < j₁ + 1 := by
      simpa [rebaseRow0, length_const2ndSeq] using hjL
    have hjM : j < Lng (const2ndSeq m u j₁) := by
      rw [length_const2ndSeq]
      exact hj
    have hget : (const2ndSeq m u j₁)[j] = (m + j, u) := by
      have hopt := getElem?_const2ndSeq m u j₁ j hj
      rw [List.getElem?_eq_getElem hjM] at hopt
      exact Option.some.inj hopt
    have he00 : entry (const2ndSeq m u j₁) 0 0 = m := by
      simpa using entry0_const2ndSeq m u j₁ 0 (by omega)
    have he10 : entry (const2ndSeq m u j₁) 1 0 = u := by
      simpa using entry1_const2ndSeq m u j₁ 0 (by omega)
    simp only [rebaseRow0, List.getElem_map]
    rw [hget, he00, he10]
    simp [const2ndSeq, List.getElem_map]
    omega

private theorem const2ndSeq_Trans_key (m u j₁ : ℕ) :
    Trans (const2ndSeq m u j₁) =
      if j₁ = 0 ∧ u = 0 then BZero else const2ndTower u (j₁ + 1) := by
  let M := const2ndSeq m u j₁
  let R := const2ndSeq u u j₁
  have hRed : Red M = R := by simpa [M, R] using Red_const2ndSeq m u j₁
  have hfuelBound : j₁ + 2 ≤ transFuel M := by
    unfold transFuel
    have hL : Lng M = j₁ + 1 := by simpa [M] using length_const2ndSeq m u j₁
    rw [hL]
    nlinarith [Nat.zero_le (nu M)]
  by_cases hred : reduced M = true
  · have hfix : Red M = M := RTPS_Red_eq M hred
    have hMR : M = R := hfix.symm.trans hRed
    have hfuelR : j₁ + 1 ≤ transFuel R := by
      have hh := hfuelBound
      rw [hMR] at hh
      omega
    unfold Trans
    rw [show const2ndSeq m u j₁ = M by rfl, hMR]
    exact canonical_const2ndSeq_aux u j₁ (transFuel R) hfuelR
  · have hred' : reduced M = false := Bool.eq_false_of_not_eq_true hred
    let g := transFuel M - 1
    have hfg : transFuel M = g + 1 := by dsimp [g]; omega
    have hgbound : j₁ + 1 ≤ g := by dsimp [g]; omega
    unfold Trans
    change TransAux (transFuel M) M = _
    rw [hfg, TransAux]
    simp only [hred', Bool.not_false, if_true, hRed]
    exact canonical_const2ndSeq_aux u j₁ g hgbound

/-- §8.6 (article 5496): a pair sequence with first row increasing by one
and constant second row translates to the corresponding iterated principal
term, apart from the unique zero singleton. -/
theorem const2nd_Trans (M : PS) (m u j₁ : ℕ)
    (hM : M = const2ndSeq m u j₁) (hTPS : TPS M) :
    (j₁ = 0 ∧ u = 0 → Trans M = BZero) ∧
      (0 < j₁ ∨ 0 < u →
        Trans M = (Dprin (u : ℕ∞))^[j₁ + 1] BZero) := by
  subst M
  have hkey := const2ndSeq_Trans_key m u j₁
  constructor
  · intro hz
    simpa [hz] using hkey
  · intro hpos
    have hnz : ¬(j₁ = 0 ∧ u = 0) := by omega
    rw [hkey, if_neg hnz, ← const2ndTower_eq_iterate]

#print axioms const2nd_Trans

end PSS
