import «7».«7.3-two-column»

/-!
# §8.1 補題（公差 `(1,1)` のペア数列の `Trans`）

- 原文: `tmp/content.md` article 2837
- 訂正: なし
- Isabelle: `m_8_1_diagSeq_Trans`, `p_8_1_diagSeq_Trans`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem diagSeq_succ_snoc_dT (u v : ℕ) (huv : u ≤ v) :
    diagSeq u (v + 1) = diagSeq u v ++ [(v + 1, v + 1)] := by
  have hrange :
      List.range' u (v + 1 + 1 - u) =
        List.range' u (v + 1 - u) ++ [v + 1] := by
    calc
      List.range' u (v + 1 + 1 - u) =
          List.range' u ((v + 1 - u) + 1) := by
        congr 1
        omega
      _ = List.range' u (v + 1 - u) ++
          List.range' (u + (v + 1 - u)) 1 := List.range'_append_1.symm
      _ = List.range' u (v + 1 - u) ++ [v + 1] := by
        rw [Nat.add_sub_of_le (by omega : u ≤ v + 1)]
        simp
  simp [diagSeq, hrange]

private theorem Pred_diagSeq_succ_dT (u v : ℕ) (huv : u ≤ v) :
    Pred (diagSeq u (v + 1)) = diagSeq u v := by
  have hlen : 1 < Lng (diagSeq u (v + 1)) := by
    simp [diagSeq]
    omega
  rw [Pred, if_neg (by omega), diagSeq_succ_snoc_dT u v huv]
  simp

private theorem length_diagSeq_dT (u v : ℕ) :
    Lng (diagSeq u v) = v + 1 - u := by
  simp [diagSeq]

private theorem entry_diagSeq_dT (u v i j : ℕ)
    (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v) i j = u + j := by
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

private theorem nextR0_consecutive_dT (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1)) :
    nextR M 0 j (j + 1) = true := by
  simp only [nextR, if_pos]
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · have : k = j + 1 := by omega
    subst k
    simp
  · simp [hjk]

private theorem nextR1_consecutive_dT (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 := nextR0_consecutive_dT M j hL he0
  have hle0 : le0 M j (j + 1) = true := by
    simpa [leR] using nextR0_leR M j (j + 1) hn0
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he1⟩, hle0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · by_cases hle : le0 M k (j + 1) = true
    · have hkle := le0_index_fseq hle
      have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk, hle]
  · simp [hjk]

private theorem diagSeq_reduced_mono_dT (u v : ℕ) (huv : u < v) :
    RTPS (diagSeq u v) ∧ monoT (diagSeq u v) = true := by
  have hsingleR : RTPS [(v, v)] := by
    have hfix := Red_singleton v v
    simp [RTPS, reduced, hfix]
  have hsingleMono : monoT [(v, v)] = true := by
    simp only [monoT, Bool.and_eq_true]
    constructor
    · simp [zeroT, entry]
      omega
    · simp [leR, le0, le0Aux]
  have hp := RTPS_diag_prefix [(v, v)] u hsingleR hsingleMono
    (by simpa [entry] using huv.le)
  have heq : diagSeq u v = diagSeq u (v - 1) ++ [(v, v)] := by
    have hs := diagSeq_succ_snoc_dT u (v - 1) (by omega)
    have hv : v - 1 + 1 = v := by omega
    simpa only [hv] using hs
  simpa [entry, if_pos huv, ← heq] using hp

private theorem diagSeq_parent_last_dT (u v : ℕ) (huv : u < v) :
    parent (diagSeq u v) 0 (Lng (diagSeq u v) - 1) =
      Lng (diagSeq u v) - 2 := by
  let M := diagSeq u v
  let j₁ := Lng M - 1
  let j₀ := Lng M - 2
  have hL : Lng M = v + 1 - u := length_diagSeq_dT u v
  have hlen : 1 < Lng M := by rw [hL]; omega
  have hj : j₀ + 1 = j₁ := by dsimp [j₀, j₁]; omega
  have hjL : j₀ + 1 < Lng M := by
    dsimp [j₀]
    omega
  have hj0L : j₀ < Lng M := by omega
  have he0 : entry M 0 j₀ < entry M 0 (j₀ + 1) := by
    change entry (diagSeq u v) 0 j₀ < entry (diagSeq u v) 0 (j₀ + 1)
    rw [entry_diagSeq_dT u v 0 j₀ (by simpa [M] using hj0L),
      entry_diagSeq_dT u v 0 (j₀ + 1) (by simpa [M] using hjL)]
    omega
  have hn := nextR0_consecutive_dT M j₀ hjL he0
  have hp := parent_eq_of_nextR0 M j₀ j₁ (by simpa [hj] using hn)
  simpa [M, j₀, j₁] using hp

private theorem diagSeq_adm_zero_dT (u v : ℕ) :
    adm (diagSeq u v) 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem find?_reverse_range_only_zero_dT (p : ℕ → Bool) (n : ℕ)
    (hn : 0 < n) (hzero : p 0 = true)
    (hpos : ∀ k, 0 < k → k < n → p k = false) :
    (List.range n).reverse.find? p = some 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        simp [hzero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        have hpn : p n = false := hpos n hnpos (by omega)
        have ihval : (List.range n).reverse.find? p = some 0 :=
          ih hnpos (fun k hk0 hkn => hpos k hk0 (by omega))
        simpa [List.range_succ, hpn] using ihval

private theorem diagSeq_nadm_interior_dT (u v j : ℕ)
    (hjpos : 0 < j) (hjL : j + 1 < Lng (diagSeq u v)) :
    nadm (diagSeq u v) j = true := by
  let M := diagSeq u v
  have hjprev : j - 1 + 1 = j := by omega
  have hprevL : j - 1 + 1 < Lng M := by
    simpa [M, hjprev] using (show j < Lng (diagSeq u v) by omega)
  have hjcurL : j + 1 < Lng M := by simpa [M] using hjL
  have heprev0 : entry M 0 (j - 1) < entry M 0 (j - 1 + 1) := by
    change entry (diagSeq u v) 0 (j - 1) <
      entry (diagSeq u v) 0 (j - 1 + 1)
    rw [entry_diagSeq_dT u v 0 (j - 1) (by omega),
      entry_diagSeq_dT u v 0 (j - 1 + 1) (by simpa [M] using hprevL)]
    omega
  have heprev1 : entry M 1 (j - 1) < entry M 1 (j - 1 + 1) := by
    change entry (diagSeq u v) 1 (j - 1) <
      entry (diagSeq u v) 1 (j - 1 + 1)
    rw [entry_diagSeq_dT u v 1 (j - 1) (by omega),
      entry_diagSeq_dT u v 1 (j - 1 + 1) (by simpa [M] using hprevL)]
    omega
  have hecur0 : entry M 0 j < entry M 0 (j + 1) := by
    change entry (diagSeq u v) 0 j < entry (diagSeq u v) 0 (j + 1)
    rw [entry_diagSeq_dT u v 0 j (by omega),
      entry_diagSeq_dT u v 0 (j + 1) (by simpa [M] using hjcurL)]
    omega
  have hecur1 : entry M 1 j < entry M 1 (j + 1) := by
    change entry (diagSeq u v) 1 j < entry (diagSeq u v) 1 (j + 1)
    rw [entry_diagSeq_dT u v 1 j (by omega),
      entry_diagSeq_dT u v 1 (j + 1) (by simpa [M] using hjcurL)]
    omega
  have hnprev := nextR1_consecutive_dT M (j - 1) hprevL heprev0 heprev1
  have hncur := nextR1_consecutive_dT M j hjcurL hecur0 hecur1
  have hnprev' : nextR M 1 (j - 1) j = true := by
    simpa only [hjprev] using hnprev
  simp [nadm, M, hnprev', hncur]

private theorem diagSeq_adm_interior_false_dT (u v j : ℕ)
    (hjpos : 0 < j) (hjL : j + 1 < Lng (diagSeq u v)) :
    adm (diagSeq u v) j = false := by
  simp [adm, diagSeq_nadm_interior_dT u v j hjpos hjL]

private theorem diagSeq_Adm_parent_last_dT (u v : ℕ) (huv : u < v) :
    Adm (diagSeq u v)
        (parent (diagSeq u v) 0 (Lng (diagSeq u v) - 1)) = 0 := by
  let M := diagSeq u v
  let j₀ := Lng M - 2
  have hL : Lng M = v + 1 - u := length_diagSeq_dT u v
  have hlen : 1 < Lng M := by rw [hL]; omega
  have hparent := diagSeq_parent_last_dT u v huv
  change Adm M (parent M 0 (Lng M - 1)) = 0
  rw [hparent]
  change Adm M j₀ = 0
  by_cases hjzero : j₀ = 0
  · simp [hjzero, Adm, M, diagSeq_adm_zero_dT]
  · have hjpos : 0 < j₀ := Nat.pos_of_ne_zero hjzero
    have hjnextL : j₀ + 1 < Lng M := by dsimp [j₀]; omega
    have hadm : adm M j₀ = false := by
      simpa [M] using diagSeq_adm_interior_false_dT u v j₀ hjpos
        (by simpa [M] using hjnextL)
    have hall : ∀ k, 0 < k → k < j₀ → adm M k = false := by
      intro k hkpos hkj
      apply diagSeq_adm_interior_false_dT u v k hkpos
      simpa [M] using (show k + 1 < Lng M by omega)
    have hfind : (List.range j₀).reverse.find? (fun k => adm M k) = some 0 :=
      find?_reverse_range_only_zero_dT (fun k => adm M k) j₀ hjpos
        (by simpa [M] using diagSeq_adm_zero_dT u v) hall
    simp [Adm, hadm, hfind]

private theorem diagSeq_trans_indices_dT (u v : ℕ) (huv : u < v) :
    transJ1 (diagSeq u v) = Lng (diagSeq u v) - 1 ∧
      transJ0 (diagSeq u v) = Lng (diagSeq u v) - 2 ∧
      entry (diagSeq u v) 1 (transJ1 (diagSeq u v)) = v ∧
      entry (diagSeq u v) 1 (transJ0 (diagSeq u v)) = v - 1 ∧
      Adm (diagSeq u v) (transJ0 (diagSeq u v)) = 0 := by
  let M := diagSeq u v
  have hL : Lng M = v + 1 - u := length_diagSeq_dT u v
  have hlen : 1 < Lng M := by rw [hL]; omega
  have hj1 : transJ1 M = Lng M - 1 := rfl
  have hj0 : transJ0 M = Lng M - 2 := by
    unfold transJ0
    change parent M 0 (Lng M - 1) = Lng M - 2
    exact diagSeq_parent_last_dT u v huv
  have he1 : entry M 1 (transJ1 M) = v := by
    have hjLM : Lng M - 1 < Lng M := by omega
    have hjL : Lng M - 1 < Lng (diagSeq u v) := by simpa [M] using hjLM
    rw [hj1, entry_diagSeq_dT u v 1 (Lng M - 1) hjL]
    rw [hL]
    omega
  have he0 : entry M 1 (transJ0 M) = v - 1 := by
    have hjLM : Lng M - 2 < Lng M := by omega
    have hjL : Lng M - 2 < Lng (diagSeq u v) := by simpa [M] using hjLM
    rw [hj0, entry_diagSeq_dT u v 1 (Lng M - 2) hjL]
    rw [hL]
    omega
  have hadm : Adm M (transJ0 M) = 0 := by
    unfold transJ0
    exact diagSeq_Adm_parent_last_dT u v huv
  exact ⟨hj1, hj0, he1, he0, hadm⟩

private theorem diagSeq_trans_conditions_dT (u v : ℕ) (huv : u < v) :
    (transCondI (diagSeq u v) || transCondIII (diagSeq u v) ||
        transCondV (diagSeq u v)) = false ∧
      transCondVI (diagSeq u v) = true := by
  let M := diagSeq u v
  have hi := diagSeq_trans_indices_dT u v huv
  have hj1 : transJ1 M = Lng M - 1 := by simpa [M] using hi.1
  have hj0 : transJ0 M = Lng M - 2 := by simpa [M] using hi.2.1
  have he1 : entry M 1 (transJ1 M) = v := by simpa [M] using hi.2.2.1
  have he0 : entry M 1 (transJ0 M) = v - 1 := by
    simpa [M] using hi.2.2.2.1
  have hlen : 1 < Lng M := by
    rw [length_diagSeq_dT u v]
    omega
  have hstep : transJ0 M + 1 = transJ1 M := by
    rw [hj1, hj0]
    omega
  have hpos : 0 < entry M 1 (transJ1 M) := by rw [he1]; omega
  have hcoeff : entry M 1 (transJ0 M) + 1 =
      entry M 1 (transJ1 M) := by
    rw [he0, he1]
    omega
  have hVI : transCondVI M = true := by
    unfold transCondVI
    change (decide (0 < entry M 1 (transJ1 M)) &&
      decide (entry M 1 (transJ0 M) + 1 = entry M 1 (transJ1 M)) &&
      (transJ0 M + 1 == transJ1 M)) = true
    simp [hpos, hcoeff, hstep]
  have hI : transCondI M = false := by
    unfold transCondI
    change ((entry M 1 (transJ1 M) == 0) && adm M (transJ0 M)) = false
    have hz : (entry M 1 (transJ1 M) == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      have heq := eq_of_beq hb
      omega
    simp [hz]
  have hIII : transCondIII M = false := by
    unfold transCondIII
    change (decide (0 < entry M 1 (transJ1 M)) &&
      decide (entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) &&
      adm M (transJ0 M)) = false
    have hnle : ¬entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) := by
      rw [he1, he0]
      omega
    simp [hnle]
  have hV : transCondV M = false := by
    unfold transCondV
    change (decide (0 < entry M 1 (transJ1 M)) &&
      (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) &&
      decide (transJ0 M + 1 < transJ1 M)) = false
    simp [hstep]
  constructor
  · simp [M, hI, hIII, hV]
  · simpa [M] using hVI

private theorem diagSeq_transC2_exact_dT (u v : ℕ) (huv : u < v) (t : BT) :
    transC2Core (diagSeq u v) (u : ℕ∞) t =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) := by
  have hc := diagSeq_trans_conditions_dT u v huv
  have hi := diagSeq_trans_indices_dT u v huv
  unfold transC2Core
  simp only [hc.1, Bool.false_eq_true, if_false, hc.2, if_true]
  change Dprin (u : ℕ∞)
      (Dprin (entry (diagSeq u v) 1 (transJ1 (diagSeq u v)) : ℕ∞) BZero) =
    Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)
  rw [hi.2.2.1]

private theorem unflatBT_flat_diag_dT (u v : ℕ) :
    unflatBT (flatBT (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))) =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) := by
  simp [unflatBT, flatBT, flatBP, parseBTAux, Dprin, BZero]

private theorem replaceScb_self_single_diag_dT (u v : ℕ) :
    replaceScb (Dprin (u : ℕ∞) BZero) (Dprin (u : ℕ∞) BZero)
      (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) := by
  have hdu : (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
    change ((u : ℕ∞) == (u : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [replaceScb, scbContexts, flatBT, flatBP, isPTBStr, dfree_BP,
    dfree_BT, dfree_BPList, ENat.coe_ne_top, unflatBT, parseBTAux,
    parseBPAux, Dprin, BZero, hdu, hz]

private theorem replaceScb_self_diag_dT (u v w : ℕ) :
    replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) =
        Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
  have hdu : (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
    change ((u : ℕ∞) == (u : ℕ∞)) = true
    exact beq_self_eq_true _
  have hdv : (Sym.dsym (v : ℕ∞) == Sym.dsym (v : ℕ∞)) = true := by
    change ((v : ℕ∞) == (v : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [replaceScb, scbContexts, flatBT, flatBP, isPTBStr, dfree_BP,
    dfree_BT, dfree_BPList, ENat.coe_ne_top, unflatBT, parseBTAux,
    parseBPAux, Dprin, BZero, hdu, hdv, hz]

private theorem scbContexts_self_single_head_dT (u : ℕ) :
    (scbContexts (Dprin (u : ℕ∞) BZero)
      (flatBT (Dprin (u : ℕ∞) BZero))).head? = some ([], []) := by
  have hdu : (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
    change ((u : ℕ∞) == (u : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [scbContexts, flatBT, flatBP, isPTBStr, dfree_BP, dfree_BT,
    dfree_BPList, ENat.coe_ne_top, parseBTAux, parseBPAux, Dprin, BZero,
    hdu, hz]

private theorem scbContexts_self_diag_head_dT (u v : ℕ) :
    (scbContexts (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (flatBT (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)))).head? =
        some ([], []) := by
  have hdu : (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
    change ((u : ℕ∞) == (u : ℕ∞)) = true
    exact beq_self_eq_true _
  have hdv : (Sym.dsym (v : ℕ∞) == Sym.dsym (v : ℕ∞)) = true := by
    change ((v : ℕ∞) == (v : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [scbContexts, flatBT, flatBP, isPTBStr, dfree_BP, dfree_BT,
    dfree_BPList, ENat.coe_ne_top, parseBTAux, parseBPAux, Dprin, BZero,
    hdu, hdv, hz]

private theorem TransAux_singleton_dT (fuel v : ℕ) :
    TransAux (fuel + 1) [(v, v)] =
      if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  have hred : reduced [(v, v)] = true := by
    have hfix := Red_singleton v v
    simp [reduced, hfix]
  rw [TransAux]
  simp [hred, entry, Dprin, BZero]
  intro h
  exact (h rfl).elim

private theorem MarkAux_singleton_dT (fuel v m : ℕ) :
    MarkAux (fuel + 1) [(v, v)] m =
      if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  have hred : reduced [(v, v)] = true := by
    have hfix := Red_singleton v v
    simp [reduced, hfix]
  rw [MarkAux]
  simp [hred, entry, Dprin, BZero]
  intro h
  exact (h rfl).elim

private theorem dprin_nat_zero_beq_false_dT (u : ℕ) :
    (Dprin (u : ℕ∞) BZero == BZero) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq : Dprin (u : ℕ∞) BZero = BZero := eq_of_beq h
  simp [Dprin, BZero] at heq

private theorem diagSeq_two_aux_dT (u fuel : ℕ) :
    TransAux (fuel + 2) (diagSeq u (u + 1)) =
        Dprin (u : ℕ∞) (Dprin (u + 1 : ℕ∞) BZero) ∧
      MarkAux (fuel + 2) (diagSeq u (u + 1)) 0 =
        Dprin (u : ℕ∞) (Dprin (u + 1 : ℕ∞) BZero) := by
  let M := diagSeq u (u + 1)
  let T := Dprin (u : ℕ∞) (Dprin (u + 1 : ℕ∞) BZero)
  have huv : u < u + 1 := by omega
  have hrm := diagSeq_reduced_mono_dT u (u + 1) huv
  have hred : reduced M = true := by simpa [M] using hrm.1
  have hmono : monoT M = true := by simpa [M] using hrm.2
  have hlen : 1 < Lng M := by
    simp [M, diagSeq]
    omega
  have hj1pos : transJ1 M ≠ 0 := by
    change Lng M - 1 ≠ 0
    omega
  have hPred : Pred M = [(u, u)] := by
    rw [show M = diagSeq u (u + 1) from rfl,
      Pred_diagSeq_succ_dT u u le_rfl]
    simp [diagSeq]
  have hi := diagSeq_trans_indices_dT u (u + 1) huv
  have hAdm : Adm M (transJ0 M) = 0 := by simpa [M] using hi.2.2.2.2
  have he1 : entry M 1 (transJ1 M) = u + 1 := by
    simpa [M] using hi.2.2.1
  have hc2 : transC2Core M (u : ℕ∞) BZero = T := by
    simpa [M, T] using diagSeq_transC2_exact_dT u (u + 1) huv BZero
  have hfuel : fuel + 2 = (fuel + 1) + 1 := by omega
  change TransAux (fuel + 2) M = T ∧ MarkAux (fuel + 2) M 0 = T
  constructor
  · rw [hfuel, TransAux]
    simp [hred]
    rw [if_neg (by
      intro h
      change transJ1 M = 0 at h
      exact hj1pos h)]
    simp [hmono]
    change (if (TransAux (fuel + 1) (Pred M) == BZero) = true then
        Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else
        replaceScb (TransAux (fuel + 1) (Pred M))
          (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))
          (transC2Core M
            (bpHeadV (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))
            (bpHeadT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))))) = T
    rw [hPred, hAdm, TransAux_singleton_dT fuel u,
      MarkAux_singleton_dT fuel u 0, he1]
    by_cases hu0 : u = 0
    · simp [hu0, T]
    · have hbeq := dprin_nat_zero_beq_false_dT u
      have hvhead : bpHeadV (Dprin (u : ℕ∞) BZero) = (u : ℕ∞) := rfl
      have hthead : bpHeadT (Dprin (u : ℕ∞) BZero) = BZero := rfl
      simp only [hu0, if_false, hbeq, Bool.false_eq_true, hvhead, hthead, hc2]
      simpa [T] using replaceScb_self_single_diag_dT u (u + 1)
  · rw [hfuel, MarkAux]
    simp [hred]
    rw [if_neg (by
      intro h
      change transJ1 M = 0 at h
      exact hj1pos h)]
    simp [hmono]
    change (if (TransAux (fuel + 1) (Pred M) == BZero) = true then
        Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else if 0 < transJ1 M then
        (match (scbContexts (MarkAux (fuel + 1) (Pred M) 0)
            (flatBT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))).head? with
          | some (s, r) =>
              unflatBT (s ++ (flatBT
                (transC2Core M
                  (bpHeadV (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))
                  (bpHeadT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))) ++ r))
          | none => Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) = T
    rw [hPred, hAdm, TransAux_singleton_dT fuel u,
      MarkAux_singleton_dT fuel u 0, he1]
    by_cases hu0 : u = 0
    · simp [hu0, T]
    · have hbeq := dprin_nat_zero_beq_false_dT u
      have hvhead : bpHeadV (Dprin (u : ℕ∞) BZero) = (u : ℕ∞) := rfl
      have hthead : bpHeadT (Dprin (u : ℕ∞) BZero) = BZero := rfl
      simp only [hu0, if_false, hbeq, Bool.false_eq_true]
      have hj1positive : 0 < transJ1 M := Nat.pos_of_ne_zero hj1pos
      simp only [if_pos hj1positive, scbContexts_self_single_head_dT,
        hvhead, hthead, hc2]
      simpa [T] using unflatBT_flat_diag_dT u (u + 1)

private theorem dprin_diag_beq_zero_false_dT (u v : ℕ) :
    (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) == BZero) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq : Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) = BZero := eq_of_beq h
  simp [Dprin, BZero] at heq

private theorem diagSeq_step_aux_dT (u v fuel : ℕ) (huv : u < v)
    (hTrans : TransAux (fuel + 1) (diagSeq u v) =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (hMark : MarkAux (fuel + 1) (diagSeq u v) 0 =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) :
    TransAux (fuel + 2) (diagSeq u (v + 1)) =
        Dprin (u : ℕ∞) (Dprin (v + 1 : ℕ∞) BZero) ∧
      MarkAux (fuel + 2) (diagSeq u (v + 1)) 0 =
        Dprin (u : ℕ∞) (Dprin (v + 1 : ℕ∞) BZero) := by
  let N := diagSeq u v
  let M := diagSeq u (v + 1)
  let T₁ := Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)
  let T₂ := Dprin (u : ℕ∞) (Dprin (v + 1 : ℕ∞) BZero)
  have huv' : u < v + 1 := by omega
  have hrm := diagSeq_reduced_mono_dT u (v + 1) huv'
  have hred : reduced M = true := by simpa [M] using hrm.1
  have hmono : monoT M = true := by simpa [M] using hrm.2
  have hlen : 1 < Lng M := by
    rw [show M = diagSeq u (v + 1) from rfl, length_diagSeq_dT]
    omega
  have hj1pos : transJ1 M ≠ 0 := by
    change Lng M - 1 ≠ 0
    omega
  have hPred : Pred M = N := by
    simpa [M, N] using Pred_diagSeq_succ_dT u v huv.le
  have hi := diagSeq_trans_indices_dT u (v + 1) huv'
  have hAdm : Adm M (transJ0 M) = 0 := by simpa [M] using hi.2.2.2.2
  have he1 : entry M 1 (transJ1 M) = v + 1 := by
    simpa [M] using hi.2.2.1
  have hc2 : transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) = T₂ := by
    simpa [M, T₂] using diagSeq_transC2_exact_dT u (v + 1) huv'
      (Dprin (v : ℕ∞) BZero)
  have hT : TransAux (fuel + 1) N = T₁ := by simpa [N, T₁] using hTrans
  have hM : MarkAux (fuel + 1) N 0 = T₁ := by simpa [N, T₁] using hMark
  have hbeq : (T₁ == BZero) = false := by
    simpa [T₁] using dprin_diag_beq_zero_false_dT u v
  have hvhead : bpHeadV T₁ = (u : ℕ∞) := rfl
  have hthead : bpHeadT T₁ = Dprin (v : ℕ∞) BZero := rfl
  have hfuel : fuel + 2 = (fuel + 1) + 1 := by omega
  change TransAux (fuel + 2) M = T₂ ∧ MarkAux (fuel + 2) M 0 = T₂
  constructor
  · rw [hfuel, TransAux]
    simp [hred]
    rw [if_neg (by
      intro h
      change transJ1 M = 0 at h
      exact hj1pos h)]
    simp [hmono]
    change (if (TransAux (fuel + 1) (Pred M) == BZero) = true then
        Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else
        replaceScb (TransAux (fuel + 1) (Pred M))
          (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))
          (transC2Core M
            (bpHeadV (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))
            (bpHeadT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M)))))) = T₂
    rw [hPred, hAdm, hT, hM]
    simp only [hbeq, Bool.false_eq_true, if_false, hvhead, hthead, hc2]
    simpa [T₁, T₂] using replaceScb_self_diag_dT u v (v + 1)
  · rw [hfuel, MarkAux]
    simp [hred]
    rw [if_neg (by
      intro h
      change transJ1 M = 0 at h
      exact hj1pos h)]
    simp [hmono]
    change (if (TransAux (fuel + 1) (Pred M) == BZero) = true then
        Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else if 0 < transJ1 M then
        (match (scbContexts (MarkAux (fuel + 1) (Pred M) 0)
            (flatBT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))).head? with
          | some (s, r) =>
              unflatBT (s ++ (flatBT
                (transC2Core M
                  (bpHeadV (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))
                  (bpHeadT (MarkAux (fuel + 1) (Pred M) (Adm M (transJ0 M))))) ++ r))
          | none => Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      else Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) = T₂
    rw [hPred, hAdm, hT, hM]
    have hj1positive : 0 < transJ1 M := Nat.pos_of_ne_zero hj1pos
    have hscb : (scbContexts T₁ (flatBT T₁)).head? = some ([], []) := by
      simpa [T₁] using scbContexts_self_diag_head_dT u v
    simp only [hbeq, Bool.false_eq_true, if_false, if_pos hj1positive,
      hscb, hvhead, hthead, hc2]
    simpa [T₂] using unflatBT_flat_diag_dT u (v + 1)

private theorem diagSeq_aux_dT (u v fuel : ℕ) (huv : u < v)
    (hfuel : v - u + 1 ≤ fuel) :
    TransAux fuel (diagSeq u v) =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) ∧
      MarkAux fuel (diagSeq u v) 0 =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) := by
  induction v generalizing u fuel with
  | zero => omega
  | succ v ih =>
      by_cases hbase : u = v
      · subst v
        let g := fuel - 2
        have hfg : fuel = g + 2 := by dsimp [g]; omega
        rw [hfg]
        exact diagSeq_two_aux_dT u g
      · have huv' : u < v := by omega
        let g := fuel - 2
        have hfg : fuel = g + 2 := by dsimp [g]; omega
        have hchildFuel : v - u + 1 ≤ g + 1 := by dsimp [g]; omega
        have hchild := ih u (g + 1) huv' hchildFuel
        rw [hfg]
        exact diagSeq_step_aux_dT u v g huv' hchild.1 hchild.2

/-- At the rightmost basepoint, the mono branch of `MarkAux` returns the
last row-one coefficient, independently of the recursive child value. -/
theorem MarkAux_rightmost_reduced_mono (fuel : ℕ) (M : PS)
    (hred : reduced M = true) (hmono : monoT M = true) (hlen : 1 < Lng M) :
    MarkAux (fuel + 1) M (Lng M - 1) =
      Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero := by
  rw [MarkAux]
  simp [hred]
  rw [if_neg (by
    intro h
    change transJ1 M = 0 at h
    change Lng M - 1 = 0 at h
    omega)]
  simp [hmono]
  have hm0 : Lng M - 1 ≠ 0 := by omega
  by_cases ht : (TransAux fuel (Pred M) == BZero) = true
  · simp [ht, hm0]
    change Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero =
      Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero
    rfl
  · simp [ht]
    rw [if_neg (by
      change ¬Lng M - 1 < transJ1 M
      have hj1 : transJ1 M = Lng M - 1 := rfl
      rw [hj1]
      exact Nat.lt_irrefl _)]
    change Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero =
      Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero
    rfl

/-- Reusable fuel-stable form of `diagSeq_Trans`, paired with the leftmost
mark needed by the recursive translation of an appended column. -/
theorem diagSeq_TransAux_MarkAux (u v fuel : ℕ) (huv : u < v)
    (hfuel : v - u + 1 ≤ fuel) :
    TransAux fuel (diagSeq u v) =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) ∧
      MarkAux fuel (diagSeq u v) 0 =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) :=
  diagSeq_aux_dT u v fuel huv hfuel

/-- Fuel-stable rightmost mark of a nontrivial diagonal pair sequence. -/
theorem diagSeq_MarkAux_rightmost (u v fuel : ℕ) (huv : u < v)
    (hfuel : v - u + 1 ≤ fuel) :
    MarkAux fuel (diagSeq u v) (Lng (diagSeq u v) - 1) =
      Dprin (v : ℕ∞) BZero := by
  let g := fuel - 1
  have hfg : fuel = g + 1 := by dsimp [g]; omega
  have hrm := diagSeq_reduced_mono_dT u v huv
  have he : entry (diagSeq u v) 1 (Lng (diagSeq u v) - 1) = v := by
    have hlen : 1 < Lng (diagSeq u v) := by rw [length_diagSeq_dT]; omega
    rw [entry_diagSeq_dT u v 1 (Lng (diagSeq u v) - 1) (by omega),
      length_diagSeq_dT]
    omega
  rw [hfg, MarkAux_rightmost_reduced_mono g (diagSeq u v) hrm.1 hrm.2
    (by rw [length_diagSeq_dT]; omega), he]

/-- §8.1 (article 2837): the translation of a nontrivial diagonal pair
sequence is the two-level Buchholz principal term determined by its two
endpoints. -/
theorem diagSeq_Trans (u v : ℕ) (huv : u < v) :
    Trans (diagSeq u v) =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) := by
  unfold Trans
  have hbound : v - u + 1 ≤ transFuel (diagSeq u v) := by
    unfold transFuel
    have hL : v - u + 1 = Lng (diagSeq u v) := by
      rw [length_diagSeq_dT]
      omega
    rw [hL]
    nlinarith [Nat.zero_le (nu (diagSeq u v)),
      Nat.zero_le (Lng (diagSeq u v))]
  exact (diagSeq_aux_dT u v (transFuel (diagSeq u v)) huv hbound).1

#print axioms diagSeq_Trans
#print axioms MarkAux_rightmost_reduced_mono
#print axioms diagSeq_TransAux_MarkAux
#print axioms diagSeq_MarkAux_rightmost

end PSS
