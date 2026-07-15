import «8».«8.1-diagSeq-Trans»
import «6».«6.6-condAB-coeff»

/-!
# §8.1 系（`Pred` が対角列である場合の `Trans`）

- 原文: `tmp/content.md` article 2871
- 訂正: なし
- Isabelle: `m_8_1_Pred_diagSeq_Trans`, `p_8_1_Pred_diagSeq_Trans`
- 状態: ✅ 完了（sorry なし）
-/

namespace PSS

private theorem length_diagApp_pD (u v wp w : ℕ) :
    Lng (diagSeq u v ++ [(wp, w)]) = v + 1 - u + 1 := by
  simp [diagSeq]

private theorem entry_diagApp_lo_pD (u v wp w i j : ℕ)
    (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v ++ [(wp, w)]) i j = u + j := by
  rw [entry_append_left_mr (diagSeq u v) [(wp, w)] i j hj]
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

private theorem entry_diagApp_last0_pD (u v wp w : ℕ) :
    entry (diagSeq u v ++ [(wp, w)]) 0 (Lng (diagSeq u v)) = wp := by
  rw [entry_append_right_mr (diagSeq u v) [(wp, w)] 0
    (Lng (diagSeq u v)) (by simp)]
  simp [entry]

private theorem entry_diagApp_last1_pD (u v wp w : ℕ) :
    entry (diagSeq u v ++ [(wp, w)]) 1 (Lng (diagSeq u v)) = w := by
  rw [entry_append_right_mr (diagSeq u v) [(wp, w)] 1
    (Lng (diagSeq u v)) (by simp)]
  simp [entry]

private theorem Pred_diagApp_pD (u v wp w : ℕ) (huv : u ≤ v) :
    Pred (diagSeq u v ++ [(wp, w)]) = diagSeq u v := by
  have hlen : 1 < Lng (diagSeq u v ++ [(wp, w)]) := by
    rw [length_diagApp_pD]
    omega
  rw [Pred, if_neg (by omega)]
  simp

private theorem nextR0_consecutive_pD (M : PS) (j : ℕ)
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

private theorem nextR0_diagApp_step_pD (u v wp w j : ℕ)
    (huv : u ≤ v) (hj : j + 1 ≤ v - u) :
    nextR (diagSeq u v ++ [(wp, w)]) 0 j (j + 1) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hjL : j + 1 < Lng M := by simp [M, hDlen]; omega
  have hjD : j < Lng (diagSeq u v) := by rw [hDlen]; omega
  have hsD : j + 1 < Lng (diagSeq u v) := by rw [hDlen]; omega
  have he : entry M 0 j < entry M 0 (j + 1) := by
    rw [entry_diagApp_lo_pD u v wp w 0 j hjD,
      entry_diagApp_lo_pD u v wp w 0 (j + 1) hsD]
    omega
  exact nextR0_consecutive_pD M j hjL he

private theorem le0Aux_refl_pD (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_pD (M : PS) (j : ℕ) (hj : j < Lng M) :
    leR M 0 j j = true := by
  simp [leR, le0, hj, le0Aux_refl_pD]

private theorem leR0_diagApp_prefix_pD (u v wp w a b : ℕ)
    (huv : u ≤ v) (hab : a ≤ b) (hb : b ≤ v - u) :
    leR (diagSeq u v ++ [(wp, w)]) 0 a b = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hM : TPS M := by simp [TPS, M]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
      apply leR0_refl_pD
      simp [diagSeq]
      omega
  | succ d ih =>
      have hprev : a + d ≤ v - u := by omega
      have hle : leR M 0 a (a + d) = true := ih (by omega) hprev
      have hn : nextR M 0 (a + d) (a + d + 1) = true := by
        simpa [M, Nat.add_assoc] using
          nextR0_diagApp_step_pD u v wp w (a + d) huv (by omega)
      exact leR_then_next_cc M 0 a (a + d) (a + d + 1) hM hle hn

private theorem nextR0_diagApp_parent_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1) :
    nextR (diagSeq u v ++ [(wp, w)]) 0 (wp - u - 1)
      (Lng (diagSeq u v ++ [(wp, w)]) - 1) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  let p := wp - u - 1
  let j₁ := Lng M - 1
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hMlen : Lng M = v + 1 - u + 1 := by simp [M, hDlen]
  have hj1 : j₁ = Lng (diagSeq u v) := by dsimp [j₁]; simp [M]
  have hpD : p < Lng (diagSeq u v) := by dsimp [p]; rw [hDlen]; omega
  have hpM : p < Lng M := hpD.trans (by simp [M])
  have hjM : j₁ < Lng M := by rw [hMlen]; dsimp [j₁]; omega
  have hpj : p < j₁ := by rw [hj1, hDlen]; dsimp [p]; omega
  have hep : entry M 0 p = wp - 1 := by
    rw [entry_diagApp_lo_pD u v wp w 0 p hpD]
    dsimp [p]
    omega
  have hej : entry M 0 j₁ = wp := by
    rw [hj1]
    exact entry_diagApp_last0_pD u v wp w
  simp only [nextR, if_pos, nextrel0, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨hpM, hjM⟩, hpj⟩, ?_⟩, ?_⟩
  · rw [hep, hej]
    omega
  intro k hk
  by_cases hpk : p < k
  · have hkD : k < Lng (diagSeq u v) := by rw [← hj1]; exact hk
    have hek := entry_diagApp_lo_pD u v wp w 0 k hkD
    rw [hej, hek]
    dsimp [p] at hpk
    simp
    omega
  · change (!decide (p < k) ||
      decide (entry M 0 j₁ ≤ entry M 0 k)) = true
    simp [hpk]

private theorem parent0_diagApp_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1) :
    parent (diagSeq u v ++ [(wp, w)]) 0
        (Lng (diagSeq u v ++ [(wp, w)]) - 1) = wp - u - 1 := by
  exact parent_eq_of_nextR0 _ _ _
    (nextR0_diagApp_parent_pD u v wp w huv huwp hwpv)

private theorem monoT_diagApp_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1) :
    monoT (diagSeq u v ++ [(wp, w)]) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  let p := wp - u - 1
  let j₁ := Lng M - 1
  have hM : TPS M := by simp [TPS, M]
  have hMlen : Lng M = v + 1 - u + 1 := length_diagApp_pD u v wp w
  have hpv : p ≤ v - u := by dsimp [p]; omega
  have hle : leR M 0 0 p = true := by
    simpa [M] using leR0_diagApp_prefix_pD u v wp w 0 p huv.le (Nat.zero_le _) hpv
  have hn : nextR M 0 p j₁ = true := by
    simpa [M, p, j₁] using nextR0_diagApp_parent_pD u v wp w huv huwp hwpv
  have hfull : leR M 0 0 j₁ = true :=
    leR_then_next_cc M 0 0 p j₁ hM hle hn
  have hz : zeroT M = false := by
    simp [zeroT, hMlen]
    omega
  change monoT M = true
  simp only [monoT, Bool.and_eq_true]
  constructor
  · simpa using hz
  · change leR M 0 0 (Lng M - 1) = true
    simpa [j₁] using hfull

private theorem nextR_diagApp_prefix_parent_pD (u v wp w i p j : ℕ)
    (huv : u < v) (hi : i < 2) (hj : j ≤ v - u)
    (hn : nextR (diagSeq u v ++ [(wp, w)]) i p j = true) :
    p + 1 = j := by
  let M := diagSeq u v ++ [(wp, w)]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hjD : j < Lng (diagSeq u v) := by rw [hDlen]; omega
  have hej : entry M i j = u + j := entry_diagApp_lo_pD u v wp w i j hjD
  by_cases hi0 : i = 0
  · subst i
    have hn0 : nextrel0 M p j = true := by simpa [nextR] using hn
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range] at hh
    have hpj : p < j := hh.1.1.2
    by_contra hne
    have hmid : p < p + 1 ∧ p + 1 < j := by omega
    have hmD : p + 1 < Lng (diagSeq u v) := by omega
    have hem : entry M 0 (p + 1) = u + (p + 1) :=
      entry_diagApp_lo_pD u v wp w 0 (p + 1) hmD
    have hall := hh.2 (p + 1) (by omega)
    have hge : entry M 0 j ≤ entry M 0 (p + 1) := by
      simpa [hmid.1] using hall
    rw [hej, hem] at hge
    omega
  · have hi1 : i = 1 := by omega
    subst i
    have hn1 : nextrel1 M p j = true := by simpa [nextR] using hn
    have hh := hn1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range] at hh
    have hpj : p < j := hh.1.1.1.2
    by_contra hne
    have hmid : p < p + 1 ∧ p + 1 < j := by omega
    have hmD : p + 1 < Lng (diagSeq u v) := by omega
    have hem : entry M 1 (p + 1) = u + (p + 1) :=
      entry_diagApp_lo_pD u v wp w 1 (p + 1) hmD
    have hleR := leR0_diagApp_prefix_pD u v wp w (p + 1) j huv.le
      (by omega) hj
    have hle0 : le0 M (p + 1) j = true := by simpa [leR, M] using hleR
    have hMlen : Lng M = v + 1 - u + 1 := length_diagApp_pD u v wp w
    have hall := hh.2 (p + 1) (by rw [hMlen]; omega)
    have hge : entry M 1 j ≤ entry M 1 (p + 1) := by
      simpa [hmid.1, hle0] using hall
    rw [hej, hem] at hge
    omega

private theorem nextR1_diagApp_last_coeff_pD (u v wp w p : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1)
    (hwwp : w ≤ wp)
    (hn : nextR (diagSeq u v ++ [(wp, w)]) 1 p
      (Lng (diagSeq u v ++ [(wp, w)]) - 1) = true) :
    entry (diagSeq u v ++ [(wp, w)]) 1 p + 1 = w := by
  let M := diagSeq u v ++ [(wp, w)]
  let jp := wp - u - 1
  let j₁ := Lng M - 1
  change entry M 1 p + 1 = w
  have hM : TPS M := by simp [TPS, M]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hMlen : Lng M = v + 1 - u + 1 := by simp [M, hDlen]
  have hj1D : j₁ = Lng (diagSeq u v) := by dsimp [j₁]; simp [M]
  have hn1 : nextrel1 M p j₁ = true := by simpa [M, j₁, nextR] using hn
  have hh := hn1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hh
  have hpj1 : p < j₁ := hh.1.1.1.2
  have heplt : entry M 1 p < entry M 1 j₁ := hh.1.1.2
  have hple0 : le0 M p j₁ = true := hh.1.2
  have hej1 : entry M 1 j₁ = w := by
    rw [hj1D]
    exact entry_diagApp_last1_pD u v wp w
  have hn0 : nextR M 0 jp j₁ = true := by
    simpa [M, jp, j₁] using nextR0_diagApp_parent_pD u v wp w huv huwp hwpv
  have hpentry0 : entry M 0 p < entry M 0 j₁ := by
    have hleR : leR M 0 p j₁ = true := by simpa [leR] using hple0
    exact ancestor_basic_1 M p j₁ j₁ hM (by omega) le_rfl hleR
  have hpjp : p ≤ jp := nextR0_largest_below M jp p j₁ hn0 hpj1 hpentry0
  have hjpD : jp < Lng (diagSeq u v) := by dsimp [jp]; rw [hDlen]; omega
  have hpD : p < Lng (diagSeq u v) := by omega
  have hep : entry M 1 p = u + p := entry_diagApp_lo_pD u v wp w 1 p hpD
  by_cases hsucc : p + 1 ≤ jp
  · have hqj : p + 1 ≤ v - u := by dsimp [jp] at hsucc; omega
    have hqjp : leR M 0 (p + 1) jp = true := by
      simpa [M] using leR0_diagApp_prefix_pD u v wp w (p + 1) jp huv.le
        hsucc (by dsimp [jp]; omega)
    have hqj1 : leR M 0 (p + 1) j₁ = true :=
      leR_then_next_cc M 0 (p + 1) jp j₁ hM hqjp hn0
    have hqle0 : le0 M (p + 1) j₁ = true := by simpa [leR] using hqj1
    have hall := hh.2 (p + 1) (by rw [hMlen]; omega)
    have hge : entry M 1 j₁ ≤ entry M 1 (p + 1) := by
      simpa [hqle0] using hall
    have hqD : p + 1 < Lng (diagSeq u v) := by omega
    have heq : entry M 1 (p + 1) = u + (p + 1) :=
      entry_diagApp_lo_pD u v wp w 1 (p + 1) hqD
    rw [hep]
    rw [hej1, heq] at hge
    omega
  · have hpjp' : p = jp := by omega
    have hejp : entry M 1 jp = wp - 1 := by
      rw [entry_diagApp_lo_pD u v wp w 1 jp hjpD]
      dsimp [jp]
      omega
    rw [hpjp', hejp] at heplt ⊢
    rw [hej1] at heplt
    omega

private theorem RedCondA_diagApp_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1)
    (hwwp : w ≤ wp) :
    RedCondA (diagSeq u v ++ [(wp, w)]) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hMlen : Lng M = v + 1 - u + 1 := by simp [M, hDlen]
  change RedCondA M = true
  apply RedCondA_intro
  intro i j hi hj hp
  have hn := hasParent_next_fseq M i j hp
  have hjM : j < Lng M := by simpa [M] using hj
  have hjlast : j ≤ Lng M - 1 := by omega
  by_cases hj1 : j = Lng M - 1
  · subst j
    by_cases hi0 : i = 0
    · subst i
      have hpar := parent0_diagApp_pD u v wp w huv huwp hwpv
      have hpD : wp - u - 1 < Lng (diagSeq u v) := by rw [hDlen]; omega
      have hep : entry M 0 (wp - u - 1) = wp - 1 := by
        rw [entry_diagApp_lo_pD u v wp w 0 (wp - u - 1) hpD]
        omega
      have hej : entry M 0 (Lng M - 1) = wp := by
        have hjD : Lng M - 1 = Lng (diagSeq u v) := by simp [M]
        rw [hjD]
        exact entry_diagApp_last0_pD u v wp w
      rw [hpar, hep, hej]
      omega
    · have hi1 : i = 1 := by omega
      subst i
      have hc := nextR1_diagApp_last_coeff_pD u v wp w
        (parent M 1 (Lng M - 1)) huv huwp hwpv hwwp hn
      have hej : entry M 1 (Lng M - 1) = w := by
        have hjD : Lng M - 1 = Lng (diagSeq u v) := by simp [M]
        rw [hjD]
        exact entry_diagApp_last1_pD u v wp w
      rw [hej]
      exact hc
  · have hjpref : j ≤ v - u := by rw [hMlen] at hjlast; omega
    have hjpos : 0 < j := by
      by_contra hzero
      have : j = 0 := by omega
      subst j
      have hh := hn
      by_cases hi0 : i = 0
      · simp [nextR, hi0, nextrel0] at hh
      · simp [nextR, hi0, nextrel1] at hh
    have hs := nextR_diagApp_prefix_parent_pD u v wp w i (parent M i j) j
      huv hi hjpref hn
    have hpD : parent M i j < Lng (diagSeq u v) := by rw [hDlen]; omega
    have hjD : j < Lng (diagSeq u v) := by rw [hDlen]; omega
    rw [entry_diagApp_lo_pD u v wp w i (parent M i j) hpD,
      entry_diagApp_lo_pD u v wp w i j hjD]
    omega

private theorem RedCondB_diagApp_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1) :
    RedCondB (diagSeq u v ++ [(wp, w)]) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hM : TPS M := by simp [TPS, M]
  have hmono : monoT M = true := monoT_diagApp_pD u v wp w huv huwp hwpv
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  change RedCondB M = true
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  have hjL : j < Lng M := by omega
  by_cases hp : hasParent M 0 j = true
  · simp [hp]
  · have hpfalse : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hp
    have hjzero : j = 0 := by
      by_contra hjne
      have hptrue := mono_hasParent_row0 M hM hmono j (Nat.pos_of_ne_zero hjne) hjL
      exact hp hptrue
    subst j
    have h0D : 0 < Lng (diagSeq u v) := by simp [diagSeq]; omega
    have he0 := entry_diagApp_lo_pD u v wp w 0 0 h0D
    have he1 := entry_diagApp_lo_pD u v wp w 1 0 h0D
    simp only [hpfalse, Bool.false_or, decide_eq_true_eq]
    change entry (diagSeq u v ++ [(wp, w)]) 0 0 =
      entry (diagSeq u v ++ [(wp, w)]) 1 0
    rw [he0, he1]

private theorem RTPS_diagApp_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1)
    (hwwp : w ≤ wp) :
    RTPS (diagSeq u v ++ [(wp, w)]) := by
  let M := diagSeq u v ++ [(wp, w)]
  have hM : TPS M := by simp [TPS, M]
  have hmono : monoT M = true := monoT_diagApp_pD u v wp w huv huwp hwpv
  have hnm : multiT M = false := by simp [multiT, hmono]
  exact RTPS_of_condAB_nonmulti M hM
    (RedCondA_diagApp_pD u v wp w huv huwp hwpv hwwp)
    (RedCondB_diagApp_pD u v wp w huv huwp hwpv) hnm

private theorem nextR1_consecutive_pD (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 := nextR0_consecutive_pD M j hL he0
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

private theorem nextR1_diagApp_spine_pD (u v wp w j : ℕ)
    (huv : u ≤ v) (hj : j + 1 ≤ v - u) :
    nextR (diagSeq u v ++ [(wp, w)]) 1 j (j + 1) = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hjD : j < Lng (diagSeq u v) := by rw [hDlen]; omega
  have hsD : j + 1 < Lng (diagSeq u v) := by rw [hDlen]; omega
  have hsM : j + 1 < Lng M := hsD.trans (by simp [M])
  have he0 : entry M 0 j < entry M 0 (j + 1) := by
    rw [entry_diagApp_lo_pD u v wp w 0 j hjD,
      entry_diagApp_lo_pD u v wp w 0 (j + 1) hsD]
    omega
  have he1 : entry M 1 j < entry M 1 (j + 1) := by
    rw [entry_diagApp_lo_pD u v wp w 1 j hjD,
      entry_diagApp_lo_pD u v wp w 1 (j + 1) hsD]
    omega
  exact nextR1_consecutive_pD M j hsM he0 he1

private theorem nadm_diagApp_interior_pD (u v wp w j : ℕ)
    (huv : u < v) (hjpos : 0 < j) (hj : j < v - u) :
    nadm (diagSeq u v ++ [(wp, w)]) j = true := by
  let M := diagSeq u v ++ [(wp, w)]
  have hp : j - 1 + 1 = j := by omega
  have hnprev : nextR M 1 (j - 1) j = true := by
    have hn := nextR1_diagApp_spine_pD u v wp w (j - 1) huv.le (by omega)
    simpa [M, hp] using hn
  have hnnext : nextR M 1 j (j + 1) = true := by
    simpa [M] using nextR1_diagApp_spine_pD u v wp w j huv.le (by omega)
  simp [nadm, M, hnprev, hnnext]

private theorem adm_diagApp_interior_false_pD (u v wp w j : ℕ)
    (huv : u < v) (hjpos : 0 < j) (hj : j < v - u) :
    adm (diagSeq u v ++ [(wp, w)]) j = false := by
  simp [adm, nadm_diagApp_interior_pD u v wp w j huv hjpos hj]

private theorem adm_diagApp_zero_pD (u v wp w : ℕ) :
    adm (diagSeq u v ++ [(wp, w)]) 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem find?_reverse_range_only_zero_pD (p : ℕ → Bool) (n : ℕ)
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

private theorem Adm_diagApp_interior_zero_pD (u v wp w j : ℕ)
    (huv : u < v) (hj : j < v - u) :
    Adm (diagSeq u v ++ [(wp, w)]) j = 0 := by
  let M := diagSeq u v ++ [(wp, w)]
  change Adm M j = 0
  by_cases hjzero : j = 0
  · simp [hjzero, Adm]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hadm : adm M j = false := by
      simpa [M] using adm_diagApp_interior_false_pD u v wp w j huv hjpos hj
    have hall : ∀ k, 0 < k → k < j → adm M k = false := by
      intro k hkpos hkj
      simpa [M] using adm_diagApp_interior_false_pD u v wp w k huv hkpos
        (by omega)
    have hfind : (List.range j).reverse.find? (fun k => adm M k) = some 0 :=
      find?_reverse_range_only_zero_pD (fun k => adm M k) j hjpos
        (by simpa [M] using adm_diagApp_zero_pD u v wp w) hall
    simp [Adm, hadm, hfind]

private theorem adm_diagApp_lastPrefix_pD (u v w : ℕ)
    (huv : u < v) (hwv : w ≤ v) :
    adm (diagSeq u v ++ [(v + 1, w)]) (Lng (diagSeq u v) - 1) = true := by
  let M := diagSeq u v ++ [(v + 1, w)]
  let j := Lng (diagSeq u v) - 1
  let j₁ := Lng M - 1
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hDpos : 0 < Lng (diagSeq u v) := by rw [hDlen]; omega
  have hMlen : Lng M = Lng (diagSeq u v) + 1 := by simp [M]
  have hjD : j < Lng (diagSeq u v) := by dsimp [j]; omega
  have hej : entry M 1 j = v := by
    rw [entry_diagApp_lo_pD u v (v + 1) w 1 j hjD]
    dsimp [j]
    rw [hDlen]
    omega
  have hj1D : j₁ = Lng (diagSeq u v) := by dsimp [j₁]; simp [M]
  have hej1 : entry M 1 j₁ = w := by
    rw [hj1D]
    exact entry_diagApp_last1_pD u v (v + 1) w
  have hjnext : j + 1 = j₁ := by
    dsimp [j, j₁]
    rw [hMlen]
    omega
  have hnfalse : nextR M 1 j (j + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hn
    have hn1 : nextrel1 M j (j + 1) = true := by simpa [nextR] using hn
    have hh := hn1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hlt := hh.1.1.2
    rw [hjnext, hej, hej1] at hlt
    omega
  change adm M j = true
  have hnadm : nadm M j = false := by
    simp [nadm, hnfalse]
    omega
  simp [adm, hnadm]

private theorem diagApp_TransAux_reduce_pD (u v wp w fuel : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1)
    (hwwp : w ≤ wp)
    (hT : TransAux fuel (diagSeq u v) =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) :
    TransAux (fuel + 1) (diagSeq u v ++ [(wp, w)]) =
      replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
        (MarkAux fuel (diagSeq u v)
          (Adm (diagSeq u v ++ [(wp, w)])
            (transJ0 (diagSeq u v ++ [(wp, w)]))))
        (transC2Core (diagSeq u v ++ [(wp, w)])
          (bpHeadV (MarkAux fuel (diagSeq u v)
            (Adm (diagSeq u v ++ [(wp, w)])
              (transJ0 (diagSeq u v ++ [(wp, w)])))))
          (bpHeadT (MarkAux fuel (diagSeq u v)
            (Adm (diagSeq u v ++ [(wp, w)])
              (transJ0 (diagSeq u v ++ [(wp, w)])))))) := by
  let M := diagSeq u v ++ [(wp, w)]
  let T := Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)
  have hR := RTPS_diagApp_pD u v wp w huv huwp hwpv hwwp
  have hred : reduced M = true := by simpa [M] using hR
  have hmono : monoT M = true := monoT_diagApp_pD u v wp w huv huwp hwpv
  have hlen : 1 < Lng M := by rw [length_diagApp_pD u v wp w]; omega
  have hj1pos : transJ1 M ≠ 0 := by
    change Lng M - 1 ≠ 0
    omega
  have hPred : Pred M = diagSeq u v := by
    simpa [M] using Pred_diagApp_pD u v wp w huv.le
  have hbeq : (T == BZero) = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have heq : T = BZero := eq_of_beq hb
    simp [T, Dprin, BZero] at heq
  change TransAux (fuel + 1) M = _
  rw [TransAux]
  simp [hred]
  rw [if_neg (by
    intro h
    change transJ1 M = 0 at h
    exact hj1pos h)]
  simp [hmono]
  change (if (TransAux fuel (Pred M) == BZero) = true then
      Dprin 0 (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
    else replaceScb (TransAux fuel (Pred M))
      (MarkAux fuel (Pred M) (Adm M (transJ0 M)))
      (transC2Core M
        (bpHeadV (MarkAux fuel (Pred M) (Adm M (transJ0 M))))
        (bpHeadT (MarkAux fuel (Pred M) (Adm M (transJ0 M)))))) = _
  rw [hPred]
  have hT' : TransAux fuel (diagSeq u v) = T := by simpa [T] using hT
  rw [hT']
  simp only [hbeq, Bool.false_eq_true, if_false]
  rfl

private theorem scbContexts_self_diag_head_pD (u v : ℕ) :
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

private theorem scbContexts_inner_diag_head_pD (u v : ℕ) :
    (scbContexts (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (flatBT (Dprin (v : ℕ∞) BZero))).head? =
        some ([Sym.dsym (u : ℕ∞)], []) := by
  by_cases huv : u = v
  · subst v
    have hds : (Sym.dsym (u : ℕ∞) == Sym.dsym (u : ℕ∞)) = true := by
      change ((u : ℕ∞) == (u : ℕ∞)) = true
      exact beq_self_eq_true _
    have hdz : (Sym.dsym (u : ℕ∞) == Sym.zero) = false := rfl
    have hzr : (Sym.zero == Sym.rp) = false := rfl
    have hz : (Sym.zero == Sym.zero) = true := rfl
    simp [scbContexts, flatBT, flatBP, isPTBStr, dfree_BP, dfree_BT,
      dfree_BPList, ENat.coe_ne_top, parseBTAux, parseBPAux, Dprin, BZero]
    rw [show List.range 2 = [0, 1] by decide]
    unfold List.findSome?
    simp [hds, hdz, hzr, hz]
  · have hduv : (Sym.dsym (u : ℕ∞) == Sym.dsym (v : ℕ∞)) = false := by
      change ((u : ℕ∞) == (v : ℕ∞)) = false
      have hcoe : (u : ℕ∞) ≠ (v : ℕ∞) := by exact_mod_cast huv
      apply Bool.eq_false_iff.mpr
      intro hb
      exact hcoe (eq_of_beq hb)
    have hdv : (Sym.dsym (v : ℕ∞) == Sym.dsym (v : ℕ∞)) = true := by
      change ((v : ℕ∞) == (v : ℕ∞)) = true
      exact beq_self_eq_true _
    have hz : (Sym.zero == Sym.zero) = true := rfl
    simp [scbContexts, flatBT, flatBP, isPTBStr, dfree_BP, dfree_BT,
      dfree_BPList, ENat.coe_ne_top, parseBTAux, parseBPAux, Dprin, BZero]
    rw [show List.range 2 = [0, 1] by decide]
    unfold List.findSome?
    simp [hduv, hdv, hz]

private theorem replaceScb_self_diag_pD (u v : ℕ) (c₂ : BT)
    (hinv : unflatBT (flatBT c₂) = c₂) :
    replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) c₂ = c₂ := by
  unfold replaceScb
  rw [scbContexts_self_diag_head_pD]
  simpa using hinv

private theorem replaceScb_inner_diag_pD (u v : ℕ) (c₂ target : BT)
    (hflat : unflatBT ([Sym.dsym (u : ℕ∞)] ++ flatBT c₂) = target) :
    replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
      (Dprin (v : ℕ∞) BZero) c₂ = target := by
  unfold replaceScb
  rw [scbContexts_inner_diag_head_pD]
  simpa using hflat

private theorem unflat_case1_pD (u v w : ℕ) :
    unflatBT ([Sym.dsym (u : ℕ∞)] ++
      flatBT (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero))) =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero)) := by
  simp [unflatBT, flatBT, flatBP, parseBTAux, Dprin, BZero]

private theorem unflat_case24_pD (u v w : ℕ) :
    unflatBT (flatBT (Dprin (u : ℕ∞)
      (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) =
        Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) := by
  simp [unflatBT, flatBT, flatBP, flatBPTail, parseBTAux, parseBPAux,
    parseBPSeqAux, addBT, Dprin, BZero]

private theorem unflat_case3_pD (u v wp w : ℕ) :
    unflatBT (flatBT (Dprin (u : ℕ∞)
      (addBT (Dprin (v : ℕ∞) BZero)
        (Dprin (wp - 1 : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))))) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero)
          (Dprin (wp - 1 : ℕ∞)
            (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) := by
  simp [unflatBT, flatBT, flatBP, flatBPTail, parseBTAux, parseBPAux,
    parseBPSeqAux, addBT, Dprin, BZero]

private theorem diagApp_indices_pD (u v wp w : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v + 1) :
    transJ1 (diagSeq u v ++ [(wp, w)]) = Lng (diagSeq u v) ∧
      transJ0 (diagSeq u v ++ [(wp, w)]) = wp - u - 1 ∧
      entry (diagSeq u v ++ [(wp, w)]) 1
        (transJ1 (diagSeq u v ++ [(wp, w)])) = w ∧
      entry (diagSeq u v ++ [(wp, w)]) 1
        (transJ0 (diagSeq u v ++ [(wp, w)])) = wp - 1 := by
  let M := diagSeq u v ++ [(wp, w)]
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hj1 : transJ1 M = Lng (diagSeq u v) := by
    change Lng M - 1 = Lng (diagSeq u v)
    simp [M]
  have hj0 : transJ0 M = wp - u - 1 := by
    unfold transJ0
    change parent M 0 (Lng M - 1) = wp - u - 1
    exact parent0_diagApp_pD u v wp w huv huwp hwpv
  have he1 : entry M 1 (transJ1 M) = w := by
    rw [hj1]
    exact entry_diagApp_last1_pD u v wp w
  have hpD : wp - u - 1 < Lng (diagSeq u v) := by rw [hDlen]; omega
  have he0 : entry M 1 (transJ0 M) = wp - 1 := by
    rw [hj0, entry_diagApp_lo_pD u v wp w 1 (wp - u - 1) hpD]
    omega
  exact ⟨hj1, hj0, he1, he0⟩

private theorem transFirst_of_adm_le_pD (M : PS)
    (hadm : adm M (transJ0 M) = true)
    (hle : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) :
    (transCondI M || transCondIII M || transCondV M) = true := by
  by_cases hz : entry M 1 (transJ1 M) = 0
  · have hI : transCondI M = true := by
      unfold transCondI
      change ((entry M 1 (transJ1 M) == 0) && adm M (transJ0 M)) = true
      simp [hz, hadm]
    simp [hI]
  · have hpos : 0 < entry M 1 (transJ1 M) := Nat.pos_of_ne_zero hz
    have hIII : transCondIII M = true := by
      unfold transCondIII
      change (decide (0 < entry M 1 (transJ1 M)) &&
        decide (entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) &&
        adm M (transJ0 M)) = true
      simp [hpos, hle, hadm]
    simp [hIII]

private theorem diagApp_case1_data_pD (u v w : ℕ)
    (huv : u < v) (hwv : w ≤ v) :
    Adm (diagSeq u v ++ [(v + 1, w)])
        (transJ0 (diagSeq u v ++ [(v + 1, w)])) =
          Lng (diagSeq u v) - 1 ∧
      (transCondI (diagSeq u v ++ [(v + 1, w)]) ||
        transCondIII (diagSeq u v ++ [(v + 1, w)]) ||
        transCondV (diagSeq u v ++ [(v + 1, w)])) = true := by
  let M := diagSeq u v ++ [(v + 1, w)]
  have hi := diagApp_indices_pD u v (v + 1) w huv (by omega) le_rfl
  have hDlen : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
  have hj0 : transJ0 M = Lng (diagSeq u v) - 1 := by
    rw [hi.2.1, hDlen]
  have hadm : adm M (transJ0 M) = true := by
    rw [hj0]
    exact adm_diagApp_lastPrefix_pD u v w huv hwv
  have hAdm : Adm M (transJ0 M) = Lng (diagSeq u v) - 1 := by
    rw [Adm, if_pos hadm]
    exact hj0
  have hle : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) := by
    rw [hi.2.2.1, hi.2.2.2]
    exact hwv
  exact ⟨hAdm, transFirst_of_adm_le_pD M hadm hle⟩

private theorem diagApp_case2_data_pD (u v wp : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v) :
    Adm (diagSeq u v ++ [(wp, wp)])
        (transJ0 (diagSeq u v ++ [(wp, wp)])) = 0 ∧
      transCondV (diagSeq u v ++ [(wp, wp)]) = true := by
  let M := diagSeq u v ++ [(wp, wp)]
  have hi := diagApp_indices_pD u v wp wp huv huwp (by omega)
  have hpint : wp - u - 1 < v - u := by omega
  have hAdm : Adm M (transJ0 M) = 0 := by
    rw [hi.2.1]
    exact Adm_diagApp_interior_zero_pD u v wp wp (wp - u - 1) huv hpint
  have hstep : transJ0 M + 1 < transJ1 M := by
    rw [hi.1, hi.2.1]
    simp [diagSeq]
    omega
  have hV : transCondV M = true := by
    unfold transCondV
    change (decide (0 < entry M 1 (transJ1 M)) &&
      (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) &&
      decide (transJ0 M + 1 < transJ1 M)) = true
    rw [hi.2.2.1, hi.2.2.2]
    simp [hstep]
    omega
  exact ⟨hAdm, hV⟩

private theorem diagApp_case3_data_pD (u v wp w : ℕ)
    (huv : u < v) (hgap : u + 1 < wp) (hwpv : wp ≤ v) (hwwp : w < wp) :
    Adm (diagSeq u v ++ [(wp, w)])
        (transJ0 (diagSeq u v ++ [(wp, w)])) = 0 ∧
      (transCondI (diagSeq u v ++ [(wp, w)]) ||
        transCondIII (diagSeq u v ++ [(wp, w)]) ||
        transCondV (diagSeq u v ++ [(wp, w)])) = false ∧
      transCondVI (diagSeq u v ++ [(wp, w)]) = false := by
  let M := diagSeq u v ++ [(wp, w)]
  have huwp : u < wp := by omega
  have hi := diagApp_indices_pD u v wp w huv huwp (by omega)
  have hp : 0 < wp - u - 1 := by omega
  have hpint : wp - u - 1 < v - u := by omega
  have hAdm : Adm M (transJ0 M) = 0 := by
    rw [hi.2.1]
    exact Adm_diagApp_interior_zero_pD u v wp w (wp - u - 1) huv hpint
  have hadm : adm M (transJ0 M) = false := by
    rw [hi.2.1]
    exact adm_diagApp_interior_false_pD u v wp w (wp - u - 1) huv hp hpint
  have hI : transCondI M = false := by
    unfold transCondI
    change ((entry M 1 (transJ1 M) == 0) && adm M (transJ0 M)) = false
    simp [hadm]
  have hIII : transCondIII M = false := by
    unfold transCondIII
    change (decide (0 < entry M 1 (transJ1 M)) &&
      decide (entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) &&
      adm M (transJ0 M)) = false
    simp [hadm]
  have hcoeff : entry M 1 (transJ0 M) + 1 ≠ entry M 1 (transJ1 M) := by
    rw [hi.2.2.2, hi.2.2.1]
    omega
  have hV : transCondV M = false := by
    unfold transCondV
    change (decide (0 < entry M 1 (transJ1 M)) &&
      (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) &&
      decide (transJ0 M + 1 < transJ1 M)) = false
    have hb : (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) = false := by
      simpa [beq_iff_eq] using hcoeff
    simp [hb]
  have hVI : transCondVI M = false := by
    unfold transCondVI
    change (decide (0 < entry M 1 (transJ1 M)) &&
      (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) &&
      (transJ0 M + 1 == transJ1 M)) = false
    have hb : (entry M 1 (transJ0 M) + 1 == entry M 1 (transJ1 M)) = false := by
      simpa [beq_iff_eq] using hcoeff
    simp [hb]
  exact ⟨hAdm, by simp [M, hI, hIII, hV], by simpa [M] using hVI⟩

private theorem diagApp_case4_data_pD (u v w : ℕ)
    (huv : u < v) (hwwp : w < u + 1) :
    Adm (diagSeq u v ++ [(u + 1, w)])
        (transJ0 (diagSeq u v ++ [(u + 1, w)])) = 0 ∧
      (transCondI (diagSeq u v ++ [(u + 1, w)]) ||
        transCondIII (diagSeq u v ++ [(u + 1, w)]) ||
        transCondV (diagSeq u v ++ [(u + 1, w)])) = true := by
  let M := diagSeq u v ++ [(u + 1, w)]
  have hi := diagApp_indices_pD u v (u + 1) w huv (by omega) (by omega)
  have hj0 : transJ0 M = 0 := by rw [hi.2.1]; omega
  have hAdm : Adm M (transJ0 M) = 0 := by
    rw [hj0]
    exact Adm_diagApp_interior_zero_pD u v (u + 1) w 0 huv (by omega)
  have hadm : adm M (transJ0 M) = true := by
    rw [hj0]
    exact adm_diagApp_zero_pD u v (u + 1) w
  have hle : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) := by
    rw [hi.2.2.1, hi.2.2.2]
    omega
  exact ⟨hAdm, transFirst_of_adm_le_pD M hadm hle⟩

private theorem diagApp_case1_transC2_pD (u v w : ℕ)
    (huv : u < v) (hwv : w ≤ v) :
    transC2Core (diagSeq u v ++ [(v + 1, w)]) (v : ℕ∞) BZero =
      Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
  let M := diagSeq u v ++ [(v + 1, w)]
  change transC2Core M (v : ℕ∞) BZero = _
  have hd := diagApp_case1_data_pD u v w huv hwv
  have hi := diagApp_indices_pD u v (v + 1) w huv (by omega) le_rfl
  have hfirst : (transCondI M || transCondIII M || transCondV M) = true := by
    simpa [M] using hd.2
  have hlast : entry M 1 (transJ1 M) = w := by
    simpa [M] using hi.2.2.1
  unfold transC2Core
  rw [if_pos hfirst]
  change Dprin (v : ℕ∞)
    (addBT BZero (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) = _
  rw [hlast]
  rfl

private theorem diagApp_case2_transC2_pD (u v wp : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v) :
    transC2Core (diagSeq u v ++ [(wp, wp)]) (u : ℕ∞)
        (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (wp : ℕ∞) BZero)) := by
  let M := diagSeq u v ++ [(wp, wp)]
  change transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) = _
  have hd := diagApp_case2_data_pD u v wp huv huwp hwpv
  have hi := diagApp_indices_pD u v wp wp huv huwp (by omega)
  have hfirst : (transCondI M || transCondIII M || transCondV M) = true := by
    have hV : transCondV M = true := by simpa [M] using hd.2
    simp [hV]
  have hlast : entry M 1 (transJ1 M) = wp := by
    simpa [M] using hi.2.2.1
  unfold transC2Core
  rw [if_pos hfirst]
  change Dprin (u : ℕ∞)
    (addBT (Dprin (v : ℕ∞) BZero)
      (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) = _
  rw [hlast]

private theorem diagApp_case3_transC2_pD (u v wp w : ℕ)
    (huv : u < v) (hgap : u + 1 < wp) (hwpv : wp ≤ v) (hwwp : w < wp) :
    transC2Core (diagSeq u v ++ [(wp, w)]) (u : ℕ∞)
        (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero)
          (Dprin (wp - 1 : ℕ∞)
            (addBT (Dprin (v : ℕ∞) BZero)
              (Dprin (w : ℕ∞) BZero)))) := by
  let M := diagSeq u v ++ [(wp, w)]
  change transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) = _
  have huwp : u < wp := by omega
  have hd := diagApp_case3_data_pD u v wp w huv hgap hwpv hwwp
  have hi := diagApp_indices_pD u v wp w huv huwp (by omega)
  have hfirst : (transCondI M || transCondIII M || transCondV M) = false := by
    simpa [M] using hd.2.1
  have hVI : transCondVI M = false := by simpa [M] using hd.2.2
  have hlast : entry M 1 (transJ1 M) = w := by
    simpa [M] using hi.2.2.1
  have hparent : entry M 1 (transJ0 M) = wp - 1 := by
    simpa [M] using hi.2.2.2
  have hneNat : v ≠ wp - 1 := by omega
  have hneENat : (v : ℕ∞) ≠ (wp - 1 : ℕ∞) := by
    intro heq
    have : v = wp - 1 := by exact_mod_cast heq
    exact hneNat this
  unfold transC2Core
  rw [if_neg (by simpa using hfirst), if_neg (by simpa using hVI)]
  simp only [Dprin, BZero]
  change Dprin (u : ℕ∞)
    (addBT
      (if bpHeadV ((PB (Dprin (v : ℕ∞) BZero)).getD
          ((PB (Dprin (v : ℕ∞) BZero)).length - 1) BZero) ==
            (entry M 1 (transJ0 M) : ℕ∞) then
        SigmaB ((PB (Dprin (v : ℕ∞) BZero)).take
          ((PB (Dprin (v : ℕ∞) BZero)).length - 1))
       else Dprin (v : ℕ∞) BZero)
      (Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT
          (if bpHeadV ((PB (Dprin (v : ℕ∞) BZero)).getD
              ((PB (Dprin (v : ℕ∞) BZero)).length - 1) BZero) ==
                (entry M 1 (transJ0 M) : ℕ∞) then
            bpHeadT ((PB (Dprin (v : ℕ∞) BZero)).getD
              ((PB (Dprin (v : ℕ∞) BZero)).length - 1) BZero)
           else Dprin (v : ℕ∞) BZero)
          (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)))) = _
  rw [hparent, hlast]
  simp [PB, untrm, BZero, Dprin, bpHeadV, hneENat, addBT]

private theorem diagApp_case4_transC2_pD (u v w : ℕ)
    (huv : u < v) (hwwp : w < u + 1) :
    transC2Core (diagSeq u v ++ [(u + 1, w)]) (u : ℕ∞)
        (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) := by
  let M := diagSeq u v ++ [(u + 1, w)]
  change transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) = _
  have hd := diagApp_case4_data_pD u v w huv hwwp
  have hi := diagApp_indices_pD u v (u + 1) w huv (by omega) (by omega)
  have hfirst : (transCondI M || transCondIII M || transCondV M) = true := by
    simpa [M] using hd.2
  have hlast : entry M 1 (transJ1 M) = w := by
    simpa [M] using hi.2.2.1
  unfold transC2Core
  rw [if_pos hfirst]
  change Dprin (u : ℕ∞)
    (addBT (Dprin (v : ℕ∞) BZero)
      (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) = _
  rw [hlast]

private theorem diagApp_childFuel_bound_pD (u v wp w : ℕ) (huv : u < v) :
    v - u + 1 ≤ transFuel (diagSeq u v ++ [(wp, w)]) - 1 := by
  have hdiag : v - u + 1 = Lng (diagSeq u v) := by
    simp [diagSeq]
    omega
  have hlen : Lng (diagSeq u v ++ [(wp, w)]) = Lng (diagSeq u v) + 1 := by
    simp
  rw [hdiag]
  unfold transFuel
  rw [hlen]
  rw [show Lng (diagSeq u v) + 1 + 1 = Lng (diagSeq u v) + 2 by omega]
  have hcoef : 1 ≤ 8 * (nu (diagSeq u v ++ [(wp, w)]) + 1) := by omega
  have hmul := Nat.mul_le_mul_right (Lng (diagSeq u v) + 2) hcoef
  omega

private theorem diagApp_case1_Trans_pD (u v w : ℕ)
    (huv : u < v) (hwv : w ≤ v) :
    Trans (diagSeq u v ++ [(v + 1, w)]) =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero)) := by
  let M := diagSeq u v ++ [(v + 1, w)]
  let g := transFuel M - 1
  have hFuel : transFuel M = g + 1 := by
    dsimp [g]
    unfold transFuel
    omega
  have hbound : v - u + 1 ≤ g := by
    simpa [g, M] using diagApp_childFuel_bound_pD u v (v + 1) w huv
  have hchild := diagSeq_TransAux_MarkAux u v g huv hbound
  have hright := diagSeq_MarkAux_rightmost u v g huv hbound
  have hreduce := diagApp_TransAux_reduce_pD u v (v + 1) w g huv
    (by omega) le_rfl (by omega) hchild.1
  have hd := diagApp_case1_data_pD u v w huv hwv
  have hc2 := diagApp_case1_transC2_pD u v w huv hwv
  unfold Trans
  change TransAux (transFuel M) M = _
  rw [hFuel]
  rw [show TransAux (g + 1) M =
      replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
        (MarkAux g (diagSeq u v) (Adm M (transJ0 M)))
        (transC2Core M
          (bpHeadV (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))
          (bpHeadT (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))) by
        simpa [M] using hreduce]
  have hAdm : Adm M (transJ0 M) = Lng (diagSeq u v) - 1 := by
    simpa [M] using hd.1
  rw [hAdm, hright]
  change replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (Dprin (v : ℕ∞) BZero) (transC2Core M (v : ℕ∞) BZero) = _
  rw [show transC2Core M (v : ℕ∞) BZero =
      Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero) by simpa [M] using hc2]
  exact replaceScb_inner_diag_pD u v _ _ (unflat_case1_pD u v w)

private theorem diagApp_case2_Trans_pD (u v wp : ℕ)
    (huv : u < v) (huwp : u < wp) (hwpv : wp ≤ v) :
    Trans (diagSeq u v ++ [(wp, wp)]) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (wp : ℕ∞) BZero)) := by
  let M := diagSeq u v ++ [(wp, wp)]
  let g := transFuel M - 1
  have hFuel : transFuel M = g + 1 := by
    dsimp [g]
    unfold transFuel
    omega
  have hbound : v - u + 1 ≤ g := by
    simpa [g, M] using diagApp_childFuel_bound_pD u v wp wp huv
  have hchild := diagSeq_TransAux_MarkAux u v g huv hbound
  have hreduce := diagApp_TransAux_reduce_pD u v wp wp g huv huwp
    (by omega) le_rfl hchild.1
  have hd := diagApp_case2_data_pD u v wp huv huwp hwpv
  have hc2 := diagApp_case2_transC2_pD u v wp huv huwp hwpv
  unfold Trans
  change TransAux (transFuel M) M = _
  rw [hFuel]
  rw [show TransAux (g + 1) M =
      replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
        (MarkAux g (diagSeq u v) (Adm M (transJ0 M)))
        (transC2Core M
          (bpHeadV (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))
          (bpHeadT (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))) by
        simpa [M] using hreduce]
  have hAdm : Adm M (transJ0 M) = 0 := by simpa [M] using hd.1
  rw [hAdm, hchild.2]
  change replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) = _
  rw [show transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (wp : ℕ∞) BZero)) by
        simpa [M] using hc2]
  exact replaceScb_self_diag_pD u v _ (unflat_case24_pD u v wp)

private theorem diagApp_case3_Trans_pD (u v wp w : ℕ)
    (huv : u < v) (hgap : u + 1 < wp) (hwpv : wp ≤ v) (hwwp : w < wp) :
    Trans (diagSeq u v ++ [(wp, w)]) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero)
          (Dprin (wp - 1 : ℕ∞)
            (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) := by
  let M := diagSeq u v ++ [(wp, w)]
  let g := transFuel M - 1
  have hFuel : transFuel M = g + 1 := by
    dsimp [g]
    unfold transFuel
    omega
  have hbound : v - u + 1 ≤ g := by
    simpa [g, M] using diagApp_childFuel_bound_pD u v wp w huv
  have hchild := diagSeq_TransAux_MarkAux u v g huv hbound
  have hreduce := diagApp_TransAux_reduce_pD u v wp w g huv (by omega)
    (by omega) (by omega) hchild.1
  have hd := diagApp_case3_data_pD u v wp w huv hgap hwpv hwwp
  have hc2 := diagApp_case3_transC2_pD u v wp w huv hgap hwpv hwwp
  unfold Trans
  change TransAux (transFuel M) M = _
  rw [hFuel]
  rw [show TransAux (g + 1) M =
      replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
        (MarkAux g (diagSeq u v) (Adm M (transJ0 M)))
        (transC2Core M
          (bpHeadV (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))
          (bpHeadT (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))) by
        simpa [M] using hreduce]
  have hAdm : Adm M (transJ0 M) = 0 := by simpa [M] using hd.1
  rw [hAdm, hchild.2]
  change replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) = _
  rw [show transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero)
          (Dprin (wp - 1 : ℕ∞)
            (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) by
        simpa [M] using hc2]
  exact replaceScb_self_diag_pD u v _ (unflat_case3_pD u v wp w)

private theorem diagApp_case4_Trans_pD (u v w : ℕ)
    (huv : u < v) (hwwp : w < u + 1) :
    Trans (diagSeq u v ++ [(u + 1, w)]) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) := by
  let M := diagSeq u v ++ [(u + 1, w)]
  let g := transFuel M - 1
  have hFuel : transFuel M = g + 1 := by
    dsimp [g]
    unfold transFuel
    omega
  have hbound : v - u + 1 ≤ g := by
    simpa [g, M] using diagApp_childFuel_bound_pD u v (u + 1) w huv
  have hchild := diagSeq_TransAux_MarkAux u v g huv hbound
  have hreduce := diagApp_TransAux_reduce_pD u v (u + 1) w g huv
    (by omega) (by omega) (by omega) hchild.1
  have hd := diagApp_case4_data_pD u v w huv hwwp
  have hc2 := diagApp_case4_transC2_pD u v w huv hwwp
  unfold Trans
  change TransAux (transFuel M) M = _
  rw [hFuel]
  rw [show TransAux (g + 1) M =
      replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
        (MarkAux g (diagSeq u v) (Adm M (transJ0 M)))
        (transC2Core M
          (bpHeadV (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))
          (bpHeadT (MarkAux g (diagSeq u v) (Adm M (transJ0 M))))) by
        simpa [M] using hreduce]
  have hAdm : Adm M (transJ0 M) = 0 := by simpa [M] using hd.1
  rw [hAdm, hchild.2]
  change replaceScb (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero))
    (transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) = _
  rw [show transC2Core M (u : ℕ∞) (Dprin (v : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) by
        simpa [M] using hc2]
  exact replaceScb_self_diag_pD u v _ (unflat_case24_pD u v w)

/-- §8.1 (article 2871): translation of a diagonal pair sequence followed by
one predecessor column, split into the four possible positions of that
column relative to the diagonal. -/
theorem Pred_diagSeq_Trans (u v wp w : ℕ) (huv : u < v) :
    (wp = v + 1 ∧ u < w ∧ w ≤ v →
      Trans (diagSeq u v ++ [(wp, w)]) =
        Dprin (u : ℕ∞) (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero))) ∧
    (u < wp ∧ wp ≤ v ∧ w = wp →
      Trans (diagSeq u v ++ [(wp, w)]) =
        Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero))) ∧
    (u + 1 < wp ∧ wp ≤ v ∧ w < wp →
      Trans (diagSeq u v ++ [(wp, w)]) =
        Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero)
            (Dprin (wp - 1 : ℕ∞)
              (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero))))) ∧
    (u + 1 = wp ∧ w < wp →
      Trans (diagSeq u v ++ [(wp, w)]) =
        Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero))) := by
  constructor
  · rintro ⟨rfl, huw, hwv⟩
    exact diagApp_case1_Trans_pD u v w huv hwv
  constructor
  · rintro ⟨huwp, hwpv, rfl⟩
    exact diagApp_case2_Trans_pD u v w huv huwp hwpv
  constructor
  · rintro ⟨hgap, hwpv, hwwp⟩
    exact diagApp_case3_Trans_pD u v wp w huv hgap hwpv hwwp
  · rintro ⟨hwp, hwwp⟩
    subst wp
    exact diagApp_case4_Trans_pD u v w huv hwwp

#print axioms Pred_diagSeq_Trans

end PSS
