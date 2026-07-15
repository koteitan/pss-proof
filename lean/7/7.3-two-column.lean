import «6».«6.6-one-column»
import PSS.Trans

/-!
# §7.3 命題（`2` 列ペア数列の基本性質）

- 原文: `tmp/content.md` の「命題（2列ペア数列の基本性質）」
- 訂正: なし
- Isabelle: `p_7_3_twoColumn`, `m_7_3_twoColumn_Trans`,
  `m_7_3_twoColumn_Marked`, `m_7_3_twoColumn_Mark`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem unflatBT_flat_two_principal (v b : ℕ) :
    unflatBT (flatBT (Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero))) =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
  simp [unflatBT, flatBT, flatBP, parseBTAux, Dprin, BZero]

private theorem replaceScb_self_nested (v b : ℕ) :
    replaceScb (Dprin (v : ℕ∞) BZero) (Dprin (v : ℕ∞) BZero)
      (Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero)) =
        Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
  have hds : (Sym.dsym (v : ℕ∞) == Sym.dsym (v : ℕ∞)) = true := by
    change ((v : ℕ∞) == (v : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [replaceScb, scbContexts, flatBT, flatBP, isPTBStr, dfree_BP,
    dfree_BT, dfree_BPList, ENat.coe_ne_top, unflatBT, parseBTAux,
    parseBPAux, Dprin, BZero, hds, hz]

private theorem scbContexts_self_head (v : ℕ) :
    (scbContexts (Dprin (v : ℕ∞) BZero)
      (flatBT (Dprin (v : ℕ∞) BZero))).head? = some ([], []) := by
  have hds : (Sym.dsym (v : ℕ∞) == Sym.dsym (v : ℕ∞)) = true := by
    change ((v : ℕ∞) == (v : ℕ∞)) = true
    exact beq_self_eq_true _
  have hz : (Sym.zero == Sym.zero) = true := rfl
  simp [scbContexts, flatBT, flatBP, isPTBStr, dfree_BP, dfree_BT,
    dfree_BPList, ENat.coe_ne_top, parseBTAux, parseBPAux, Dprin, BZero,
    hds, hz]

private theorem nextR1_consecutive_tc (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 : nextR M 0 j (j + 1) = true := by
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

/-- The only coefficient fact from condition (A) needed for two columns.
It is proved directly from reduction: after adjoining the forced diagonal
left end, a rising second coefficient lies on the diagonal trunk. -/
private theorem two_column_row1_succ_of_lt (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true)
    (hvb : v < b) : b = v + 1 := by
  let D : PS := if 0 < v then diagSeq 0 (v - 1) else []
  let N : PS := D ++ [(v, v), (c, b)]
  have hDlen : Lng D = v := by
    dsimp [D]
    by_cases hv : 0 < v
    · simp [hv, diagSeq]
      omega
    · simp [hv]
      omega
  have hpref : RTPS N ∧ monoT N = true := by
    simpa [N, D, entry] using
      (RTPS_diag_prefix [(v, v), (c, b)] 0 hR hmono (Nat.zero_le v))
  have hNT : TPS N := RTPS_TPS N hpref.1
  have hfix : Red N = N := RTPS_Red_eq N hpref.1
  have hentry (i j : ℕ) (hj : j ≤ v) : entry N i j = j := by
    by_cases hjv : j < v
    · have hv : 0 < v := by omega
      rw [show N = D ++ [(v, v), (c, b)] from rfl,
        entry_append_left_mr D [(v, v), (c, b)] i j (by omega)]
      simp only [D, if_pos hv]
      exact entry_diagSeq_zero_mr (v - 1) i j (by omega)
    · have hjv' : j = v := by omega
      subst j
      rw [show N = D ++ [(v, v), (c, b)] from rfl,
        entry_append_right_mr D [(v, v), (c, b)] i v (by omega), hDlen]
      simp [entry]
  have hcore : entry N 0 0 = 0 ∧ entry N 1 0 = 0 := by
    exact ⟨hentry 0 0 (Nat.zero_le _), hentry 1 0 (Nat.zero_le _)⟩
  have hle01 : le0 [(v, v), (c, b)] 0 1 = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    simpa [leR] using hh.2
  have hcv : v < c := by
    have hh := le0_adjacent [(v, v), (c, b)] 0 hle01
    simp [nextrel0, entry] at hh
    exact hh
  have hNlen : Lng N = v + 2 := by simp [N, hDlen]
  have htr : v + 1 ≤ TrMax N := by
    apply le_TrMax_intro_wd N (v + 1) hNT
    intro j hj
    have hjL : j + 1 < Lng N := by rw [hNlen]; omega
    by_cases hjv : j < v
    · apply nextR1_consecutive_tc N j hjL
      · rw [hentry 0 j (by omega), hentry 0 (j + 1) (by omega)]
        omega
      · rw [hentry 1 j (by omega), hentry 1 (j + 1) (by omega)]
        omega
    · have hjeq : j = v := by omega
      subst j
      apply nextR1_consecutive_tc N v hjL
      · rw [hentry 0 v le_rfl]
        rw [show N = D ++ [(v, v), (c, b)] from rfl,
          entry_append_right_mr D [(v, v), (c, b)] 0 (v + 1)
          (by omega), hDlen]
        simpa [entry] using hcv
      · rw [hentry 1 v le_rfl]
        rw [show N = D ++ [(v, v), (c, b)] from rfl,
          entry_append_right_mr D [(v, v), (c, b)] 1 (v + 1)
          (by omega), hDlen]
        simpa [entry] using hvb
  have hdiag := Red_core_prefix_diag N hpref.2 hcore 1 (v + 1) htr
  have hlast : entry N 1 (v + 1) = b := by
    rw [show N = D ++ [(v, v), (c, b)] from rfl,
      entry_append_right_mr D [(v, v), (c, b)] 1 (v + 1)
      (by omega), hDlen]
    simp [entry]
  rw [hfix] at hdiag
  omega

private theorem two_column_row1_succ_of_lt_general (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hL : Lng M = 2)
    (hlt : entry M 1 0 < entry M 1 1) :
    entry M 1 1 = entry M 1 0 + 1 := by
  rcases List.length_eq_two.mp hL with ⟨p₀, p₁, rfl⟩
  rcases p₀ with ⟨a, v⟩
  rcases p₁ with ⟨c, b⟩
  have hhead := RTPS_mono_head_eq [(a, v), (c, b)] hR hmono
  simp [entry] at hhead hlt ⊢
  subst a
  exact two_column_row1_succ_of_lt v c b hR hmono hlt

private theorem TransAux_singleton (fuel v : ℕ) :
    TransAux (fuel + 1) [(v, v)] =
      if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  have hred : reduced [(v, v)] = true := by
    have hfix := Red_singleton v v
    simp [reduced, hfix]
  rw [TransAux]
  simp [hred, entry, Dprin, BZero]
  intro h
  exact (h rfl).elim

private theorem MarkAux_singleton (fuel v m : ℕ) :
    MarkAux (fuel + 1) [(v, v)] m =
      if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  have hred : reduced [(v, v)] = true := by
    have hfix := Red_singleton v v
    simp [reduced, hfix]
  rw [MarkAux]
  simp [hred, entry, Dprin, BZero]
  intro h
  exact (h rfl).elim

private theorem two_column_row0_lt (v c b : ℕ)
    (hmono : monoT [(v, v), (c, b)] = true) : v < c := by
  have hh := hmono
  simp only [monoT, Bool.and_eq_true] at hh
  have hle : le0 [(v, v), (c, b)] 0 1 = true := by
    simpa [leR] using hh.2
  have hn := le0_adjacent [(v, v), (c, b)] 0 hle
  simpa [nextrel0, entry] using hn

private theorem two_column_parent0 (v c b : ℕ) (hvc : v < c) :
    parent [(v, v), (c, b)] 0 1 = 0 := by
  have hn : nextR [(v, v), (c, b)] 0 0 1 = true := by
    simp [nextR, nextrel0, entry, hvc]
  exact parent_eq_of_nextR0 [(v, v), (c, b)] 0 1 hn

private theorem two_column_adm0 (v c b : ℕ) :
    adm [(v, v), (c, b)] 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem two_column_Adm0 (v c b : ℕ) :
    Adm [(v, v), (c, b)] 0 = 0 := by
  simp [Adm, two_column_adm0]

private theorem two_column_trans_condition (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true) :
    (transCondI [(v, v), (c, b)] ||
      transCondIII [(v, v), (c, b)] ||
      transCondV [(v, v), (c, b)]) = true ∨
        transCondVI [(v, v), (c, b)] = true := by
  have hvc := two_column_row0_lt v c b hmono
  have hpar := two_column_parent0 v c b hvc
  have hadm := two_column_adm0 v c b
  have hj1 : transJ1 [(v, v), (c, b)] = 1 := rfl
  have hj0 : transJ0 [(v, v), (c, b)] = 0 := by
    unfold transJ0
    change parent [(v, v), (c, b)] 0 1 = 0
    exact hpar
  by_cases hb0 : b = 0
  · left
    have hI : transCondI [(v, v), (c, b)] = true := by
      unfold transCondI
      change ((entry [(v, v), (c, b)] 1 (transJ1 [(v, v), (c, b)]) == 0) &&
        adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)])) = true
      rw [hj1, hj0]
      simpa [entry, hb0] using two_column_adm0 v c b
    simp [hI]
  · by_cases hbv : b ≤ v
    · left
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hIII : transCondIII [(v, v), (c, b)] = true := by
        unfold transCondIII
        change (decide (0 < entry [(v, v), (c, b)] 1
            (transJ1 [(v, v), (c, b)])) &&
          decide (entry [(v, v), (c, b)] 1 (transJ1 [(v, v), (c, b)]) ≤
            entry [(v, v), (c, b)] 1 (transJ0 [(v, v), (c, b)])) &&
          adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)])) = true
        rw [hj1, hj0]
        simp [entry, hbpos, hbv, two_column_adm0]
      simp [hIII]
    · right
      have hvb : v < b := by omega
      have hsucc := two_column_row1_succ_of_lt v c b hR hmono hvb
      have hVI : transCondVI [(v, v), (c, b)] = true := by
        unfold transCondVI
        change (decide (0 < entry [(v, v), (c, b)] 1
            (transJ1 [(v, v), (c, b)])) &&
          decide (entry [(v, v), (c, b)] 1 (transJ0 [(v, v), (c, b)]) + 1 =
            entry [(v, v), (c, b)] 1 (transJ1 [(v, v), (c, b)])) &&
          (transJ0 [(v, v), (c, b)] + 1 == transJ1 [(v, v), (c, b)])) = true
        rw [hj1, hj0]
        simp [entry, hsucc]
      exact hVI

private theorem two_column_transC2_exact (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true) :
    transC2Core [(v, v), (c, b)] (v : ℕ∞) BZero =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
  have hconds := two_column_trans_condition v c b hR hmono
  have hj1 : transJ1 [(v, v), (c, b)] = 1 := rfl
  unfold transC2Core
  change (if (transCondI [(v, v), (c, b)] ||
      transCondIII [(v, v), (c, b)] || transCondV [(v, v), (c, b)]) = true then
      Dprin (v : ℕ∞) (addBT BZero
        (Dprin (entry [(v, v), (c, b)] 1
          (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero))
    else if transCondVI [(v, v), (c, b)] = true then
      Dprin (v : ℕ∞) (Dprin (entry [(v, v), (c, b)] 1
        (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero)
    else if BZero == BZero then
      Dprin (v : ℕ∞) (Dprin (entry [(v, v), (c, b)] 1
        (transJ0 [(v, v), (c, b)]) : ℕ∞)
          (Dprin (entry [(v, v), (c, b)] 1
            (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero))
    else BZero) = Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero)
  by_cases hfirst : (transCondI [(v, v), (c, b)] ||
      transCondIII [(v, v), (c, b)] || transCondV [(v, v), (c, b)]) = true
  · simp [hfirst, hj1, entry, addBT, Dprin, BZero]
  · have hVI : transCondVI [(v, v), (c, b)] = true := hconds.resolve_left hfirst
    simp [hfirst, hVI, hj1, entry]

private theorem two_column_Trans_exact (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true) :
    Trans [(v, v), (c, b)] =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
  let g := transFuel [(v, v), (c, b)] - 2
  have hFuel : transFuel [(v, v), (c, b)] = g + 2 := by
    dsimp [g, transFuel]
    omega
  have hred : reduced [(v, v), (c, b)] = true := by exact hR
  unfold Trans
  rw [hFuel, TransAux]
  simp [hred, hmono]
  rw [if_neg (by
    intro h
    change (1 : ℕ) = 0 at h
    omega)]
  have hPred : Pred [(v, v), (c, b)] = [(v, v)] := by simp [Pred]
  have hj1 : transJ1 [(v, v), (c, b)] = 1 := rfl
  have hvc := two_column_row0_lt v c b hmono
  have hpar := two_column_parent0 v c b hvc
  have hj0 : transJ0 [(v, v), (c, b)] = 0 := by
    unfold transJ0
    change parent [(v, v), (c, b)] 0 1 = 0
    exact hpar
  have hAdm : Adm [(v, v), (c, b)]
      (transJ0 [(v, v), (c, b)]) = 0 := by
    rw [hj0]
    exact two_column_Adm0 v c b
  change (if (TransAux (g + 1) (Pred [(v, v), (c, b)]) == BZero) = true then
      Dprin 0 (Dprin (entry [(v, v), (c, b)] 1
        (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero)
    else
      replaceScb (TransAux (g + 1) (Pred [(v, v), (c, b)]))
        (MarkAux (g + 1) (Pred [(v, v), (c, b)])
          (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)])))
        (transC2Core [(v, v), (c, b)]
          (bpHeadV (MarkAux (g + 1) (Pred [(v, v), (c, b)])
            (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)]))))
          (bpHeadT (MarkAux (g + 1) (Pred [(v, v), (c, b)])
            (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)])))))) =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero)
  rw [hPred, hAdm, TransAux_singleton g v, MarkAux_singleton g v 0, hj1]
  by_cases hv0 : v = 0
  · simp [hv0, entry]
  · have hc2 := two_column_transC2_exact v c b hR hmono
    have hbeq : (Dprin (v : ℕ∞) BZero == BZero) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have heq : Dprin (v : ℕ∞) BZero = BZero := eq_of_beq h
      simp [Dprin, BZero] at heq
    have hvhead : bpHeadV (Dprin (v : ℕ∞) BZero) = (v : ℕ∞) := rfl
    have hthead : bpHeadT (Dprin (v : ℕ∞) BZero) = BZero := rfl
    simp only [hv0, if_false, hbeq, Bool.false_eq_true, hvhead, hthead, hc2]
    exact replaceScb_self_nested v b

private theorem two_column_Mark0_exact (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true) :
    Mark [(v, v), (c, b)] 0 =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
  let g := transFuel [(v, v), (c, b)] - 2
  have hFuel : transFuel [(v, v), (c, b)] = g + 2 := by
    dsimp [g, transFuel]
    omega
  have hred : reduced [(v, v), (c, b)] = true := by exact hR
  unfold Mark
  rw [hFuel, MarkAux]
  simp [hred, hmono]
  rw [if_neg (by
    intro h
    change (1 : ℕ) = 0 at h
    omega)]
  have hPred : Pred [(v, v), (c, b)] = [(v, v)] := by simp [Pred]
  have hj1 : transJ1 [(v, v), (c, b)] = 1 := rfl
  have hvc := two_column_row0_lt v c b hmono
  have hpar := two_column_parent0 v c b hvc
  have hj0 : transJ0 [(v, v), (c, b)] = 0 := by
    unfold transJ0
    change parent [(v, v), (c, b)] 0 1 = 0
    exact hpar
  have hAdm : Adm [(v, v), (c, b)]
      (transJ0 [(v, v), (c, b)]) = 0 := by
    rw [hj0]
    exact two_column_Adm0 v c b
  change (if (TransAux (g + 1) (Pred [(v, v), (c, b)]) == BZero) = true then
      Dprin 0 (Dprin (entry [(v, v), (c, b)] 1
        (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero)
    else if 0 < transJ1 [(v, v), (c, b)] then
      (match (scbContexts
          (MarkAux (g + 1) (Pred [(v, v), (c, b)]) 0)
          (flatBT (MarkAux (g + 1) (Pred [(v, v), (c, b)])
            (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)]))))).head? with
        | some (s, r) =>
            unflatBT
              (s ++ (flatBT
                  (transC2Core [(v, v), (c, b)]
                    (bpHeadV (MarkAux (g + 1) (Pred [(v, v), (c, b)])
                      (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)]))))
                    (bpHeadT (MarkAux (g + 1) (Pred [(v, v), (c, b)])
                      (Adm [(v, v), (c, b)] (transJ0 [(v, v), (c, b)]))))) ++ r))
        | none => Dprin (entry [(v, v), (c, b)] 1
            (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero)
    else Dprin (entry [(v, v), (c, b)] 1
      (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero) =
      Dprin (v : ℕ∞) (Dprin (b : ℕ∞) BZero)
  rw [hPred, hAdm, TransAux_singleton g v, MarkAux_singleton g v 0, hj1]
  by_cases hv0 : v = 0
  · simp [hv0, entry]
  · have hbeq : (Dprin (v : ℕ∞) BZero == BZero) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have heq : Dprin (v : ℕ∞) BZero = BZero := eq_of_beq h
      simp [Dprin, BZero] at heq
    have hvhead : bpHeadV (Dprin (v : ℕ∞) BZero) = (v : ℕ∞) := rfl
    have hthead : bpHeadT (Dprin (v : ℕ∞) BZero) = BZero := rfl
    have hc2 := two_column_transC2_exact v c b hR hmono
    simp only [hv0, if_false, hbeq, Bool.false_eq_true]
    simp only [scbContexts_self_head, hvhead, hthead, hc2]
    exact unflatBT_flat_two_principal v b

private theorem two_column_Mark1_exact (v c b : ℕ)
    (hR : RTPS [(v, v), (c, b)])
    (hmono : monoT [(v, v), (c, b)] = true) :
    Mark [(v, v), (c, b)] 1 = Dprin (b : ℕ∞) BZero := by
  let g := transFuel [(v, v), (c, b)] - 2
  have hFuel : transFuel [(v, v), (c, b)] = g + 2 := by
    dsimp [g, transFuel]
    omega
  have hred : reduced [(v, v), (c, b)] = true := by exact hR
  unfold Mark
  rw [hFuel, MarkAux]
  simp [hred, hmono]
  rw [if_neg (by
    intro h
    change (1 : ℕ) = 0 at h
    omega)]
  have hPred : Pred [(v, v), (c, b)] = [(v, v)] := by simp [Pred]
  have hj1 : transJ1 [(v, v), (c, b)] = 1 := rfl
  change (if (TransAux (g + 1) (Pred [(v, v), (c, b)]) == BZero) = true then
      Dprin (entry [(v, v), (c, b)] 1
        (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero
    else if 1 < transJ1 [(v, v), (c, b)] then BZero
    else Dprin (entry [(v, v), (c, b)] 1
      (transJ1 [(v, v), (c, b)]) : ℕ∞) BZero) = Dprin (b : ℕ∞) BZero
  rw [hPred, TransAux_singleton g v, hj1]
  by_cases hv0 : v = 0
  · simp [hv0, entry]
  · have hbeq : (Dprin (v : ℕ∞) BZero == BZero) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have heq : Dprin (v : ℕ∞) BZero = BZero := eq_of_beq h
      simp [Dprin, BZero] at heq
    simp [hv0, hbeq, entry]

private theorem two_column_Marked_exact (v c b : ℕ)
    (hmono : monoT [(v, v), (c, b)] = true) :
    Marked [(v, v), (c, b)] 0 ∧ Marked [(v, v), (c, b)] 1 := by
  have hT : TPS [(v, v), (c, b)] := by simp [TPS]
  have hle01 : leR [(v, v), (c, b)] 0 0 1 = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    simpa using hh.2
  have hle11 : leR [(v, v), (c, b)] 0 1 1 = true := by
    simp [leR, le0, le0Aux]
  have hadm0 := two_column_adm0 v c b
  have hadm1 : adm [(v, v), (c, b)] 1 = true := by
    simp [adm, nadm, nextR, nextrel1]
  exact ⟨⟨hT, hadm0, hle01⟩, ⟨hT, hadm1, hle11⟩⟩

/-- §7.3: the five basic facts for a reduced mono two-column pair
sequence.  This is the corrected article statement verbatim: the translation
and the mark at column `0` are `D_{M₁₀}(D_{M₁₁}0)`, both columns are marked,
and the mark at column `1` is `D_{M₁₁}0`. -/
theorem two_column (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : Lng M = 2) :
    Trans M = Dprin (entry M 1 0 : ℕ∞)
        (Dprin (entry M 1 1 : ℕ∞) BZero) ∧
      Marked M 0 ∧ Marked M 1 ∧
      Mark M 0 = Dprin (entry M 1 0 : ℕ∞)
        (Dprin (entry M 1 1 : ℕ∞) BZero) ∧
      Mark M 1 = Dprin (entry M 1 1 : ℕ∞) BZero := by
  rcases List.length_eq_two.mp hL with ⟨p₀, p₁, rfl⟩
  rcases p₀ with ⟨a, v⟩
  rcases p₁ with ⟨c, b⟩
  have hhead := RTPS_mono_head_eq [(a, v), (c, b)] hR hmono
  simp [entry] at hhead
  subst a
  have hTrans := two_column_Trans_exact v c b hR hmono
  have hMarked := two_column_Marked_exact v c b hmono
  have hMark0 := two_column_Mark0_exact v c b hR hmono
  have hMark1 := two_column_Mark1_exact v c b hR hmono
  simpa [entry] using And.intro hTrans
    (And.intro hMarked.1 (And.intro hMarked.2 (And.intro hMark0 hMark1)))

theorem two_column_Trans (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : Lng M = 2) :
    Trans M = Dprin (entry M 1 0 : ℕ∞)
      (Dprin (entry M 1 1 : ℕ∞) BZero) :=
  (two_column M hR hmono hL).1

theorem two_column_Marked (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hL : Lng M = 2) :
    Marked M 0 ∧ Marked M 1 :=
  ⟨(two_column M hR hmono hL).2.1,
    (two_column M hR hmono hL).2.2.1⟩

theorem two_column_Mark (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : Lng M = 2) :
    Mark M 0 = Dprin (entry M 1 0 : ℕ∞)
        (Dprin (entry M 1 1 : ℕ∞) BZero) ∧
      Mark M 1 = Dprin (entry M 1 1 : ℕ∞) BZero :=
  ⟨(two_column M hR hmono hL).2.2.2.1,
    (two_column M hR hmono hL).2.2.2.2⟩

#print axioms two_column
#print axioms two_column_Trans
#print axioms two_column_Marked
#print axioms two_column_Mark

end PSS
