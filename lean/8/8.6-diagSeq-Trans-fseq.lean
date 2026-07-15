import «8».«8.6-const2nd-Trans»

/-!
# §8.6 補題（公差 `(1,1)` のペア数列の `Trans` の展開規則）

- 原文: `tmp/content.md` article 5575
- 訂正: なし
- Isabelle: `m_8_6_diagSeq_Trans_oper`, `p_8_6_diagSeq_Trans_oper`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- A diagonal sequence from `u` through `p-1`, followed by `n` columns
whose second component is constantly `p`.  Under `u < p` this is the
normal form of `oper (diagSeq u (p+1)) n`. -/
def runSeq (u p n : ℕ) : PS :=
  (List.range (p - u + n)).map fun j => (u + j, min (u + j) p)

@[simp] private theorem length_runSeq (u p n : ℕ) :
    Lng (runSeq u p n) = p - u + n := by
  simp [runSeq]

private theorem getElem?_runSeq (u p n j : ℕ)
    (hj : j < p - u + n) :
    (runSeq u p n)[j]? = some (u + j, min (u + j) p) := by
  rw [List.getElem?_eq_getElem]
  · congr 1
    simp [runSeq, List.getElem_map]
  · simpa using hj

private theorem entry0_runSeq (u p n j : ℕ)
    (hj : j < p - u + n) :
    entry (runSeq u p n) 0 j = u + j := by
  simp [entry, getElem?_runSeq u p n j hj]

private theorem entry1_runSeq (u p n j : ℕ)
    (hj : j < p - u + n) :
    entry (runSeq u p n) 1 j = min (u + j) p := by
  simp [entry, getElem?_runSeq u p n j hj]

private theorem entry1_runSeq_diag (u p n j : ℕ) (hup : u < p)
    (hj : j < p - u) :
    entry (runSeq u p n) 1 j = u + j := by
  rw [entry1_runSeq u p n j (by omega), Nat.min_eq_left]
  omega

private theorem entry1_runSeq_run (u p n j : ℕ) (hup : u < p)
    (hlo : p - u ≤ j) (hhi : j < p - u + n) :
    entry (runSeq u p n) 1 j = p := by
  rw [entry1_runSeq u p n j hhi, Nat.min_eq_right]
  omega

private theorem runSeq_succ_snoc (u p n : ℕ) :
    runSeq u p (n + 1) =
      runSeq u p n ++ [(u + (p - u + n), min (u + (p - u + n)) p)] := by
  unfold runSeq
  rw [show p - u + (n + 1) = (p - u + n) + 1 by omega,
    List.range_succ, List.map_append]
  rfl

private theorem runSeq_one_eq_diagSeq (u p : ℕ) (hup : u < p) :
    runSeq u p 1 = diagSeq u p := by
  apply List.ext_getElem
  · simp [runSeq, diagSeq]
    omega
  · intro j hjL hjR
    have hj : j < p - u + 1 := by simpa [runSeq] using hjL
    have hpj : u + j ≤ p := by omega
    simp [runSeq, diagSeq, List.getElem_map, hpj]

private theorem Pred_runSeq_succ (u p n : ℕ) (hup : u < p) :
    Pred (runSeq u p (n + 1)) = runSeq u p n := by
  rw [Pred, if_neg (by simp; omega), runSeq_succ_snoc]
  simp

private theorem nextR0_runSeq_step (u p n j : ℕ)
    (hj : j + 1 < p - u + n) :
    nextR (runSeq u p n) 0 j (j + 1) = true := by
  simp only [nextR, if_pos]
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, by omega⟩, ?_⟩, ?_⟩
  · simp
    omega
  · simp
    omega
  · rw [entry0_runSeq u p n j (by omega),
      entry0_runSeq u p n (j + 1) hj]
    omega
  · intro k hk
    by_cases hjk : j < k
    · have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk]

private theorem leR0_refl_runSeq (M : PS) (j : ℕ) (hj : j < Lng M) :
    leR M 0 j j = true := by
  have haux : le0Aux M (Lng M) j j = true := by
    cases hL : Lng M <;> simp [le0Aux]
  simp [leR, le0, hj, haux]

private theorem leR0_runSeq_interval (u p n a b : ℕ)
    (ha : a ≤ b) (hb : b < p - u + n) :
    leR (runSeq u p n) 0 a b = true := by
  let M := runSeq u p n
  have hM : TPS M := by
    simp [TPS, M, runSeq]
    omega
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      apply leR0_refl_runSeq
      simpa [M] using hb
  | succ b ih =>
      by_cases hab : a = b + 1
      · subst a
        apply leR0_refl_runSeq
        simpa [M] using hb
      · have hab' : a ≤ b := by omega
        have hle := ih hab' (by omega)
        have hn : nextR M 0 b (b + 1) = true := by
          simpa [M] using nextR0_runSeq_step u p n b hb
        exact row0_transitive M a b (b + 1) hM hle
          (nextR0_leR M b (b + 1) hn)

private theorem nextR1_runSeq_parent (u p n j : ℕ) (hup : u < p)
    (hjpos : 0 < j) (hj : j < p - u + n) :
    let q := p - u
    let a := if j ≤ q then j - 1 else q - 1
    nextR (runSeq u p n) 1 a j = true := by
  let q := p - u
  let a := if j ≤ q then j - 1 else q - 1
  have hqpos : 0 < q := by dsimp [q]; omega
  have haj : a < j := by
    dsimp [a]
    split <;> omega
  have haL : a < q + n := by omega
  have hleR : leR (runSeq u p n) 0 a j = true :=
    leR0_runSeq_interval u p n a j haj.le (by simpa [q] using hj)
  have hle0 : le0 (runSeq u p n) a j = true := by
    simpa [leR] using hleR
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, haj⟩, ?_⟩, hle0⟩, ?_⟩
  · simpa [q] using haL
  · simpa [q] using hj
  · by_cases hjq : j ≤ q
    · rw [if_pos (by simpa [q] using hjq)]
      by_cases hjqeq : j = q
      · subst j
        rw [entry1_runSeq_diag u p n (q - 1) hup (by dsimp [q]; omega),
          entry1_runSeq_run u p n q hup (by rfl) (by simpa [q] using hj)]
        dsimp [q]
        omega
      · rw [entry1_runSeq_diag u p n (j - 1) hup (by omega),
          entry1_runSeq_diag u p n j hup (by omega)]
        omega
    · rw [if_neg (by simpa [q] using hjq),
        entry1_runSeq_diag u p n (q - 1) hup (by dsimp [q]; omega),
        entry1_runSeq_run u p n j hup (by omega) (by simpa [q] using hj)]
      dsimp [q]
      omega
  · intro k hk
    by_cases hak : a < k
    · by_cases hlek : le0 (runSeq u p n) k j = true
      · have hkj : k ≤ j := le0_index_fseq hlek
        by_cases hjq : j ≤ q
        · have ha : a = j - 1 := by simp [a, hjq]
          have hkeq : k = j := by omega
          subst k
          simp
        · have ha : a = q - 1 := by simp [a, hjq]
          have hkq : q ≤ k := by omega
          have hkL : k < q + n := by omega
          rw [entry1_runSeq_run u p n j hup (by omega)
              (by simpa [q] using hj),
            entry1_runSeq_run u p n k hup (by simpa [q] using hkq)
              (by simpa [q] using hkL)]
          simp
      · simp [hlek]
    · have hka : k ≤ a := by omega
      have hnot : ¬(if j ≤ p - u then j - 1 else p - u - 1) < k := by
        simpa [a, q] using (show ¬a < k from hak)
      simp [hnot]

private theorem runSeq_row1_parent (u p n j : ℕ) (hup : u < p)
    (hjpos : 0 < j) (hj : j < p - u + n) :
    hasParent (runSeq u p n) 1 j = true ∧
      entry (runSeq u p n) 1 (parent (runSeq u p n) 1 j) + 1 =
        entry (runSeq u p n) 1 j := by
  let q := p - u
  let a := if j ≤ q then j - 1 else q - 1
  have hn : nextR (runSeq u p n) 1 a j = true := by
    simpa [q, a] using nextR1_runSeq_parent u p n j hup hjpos hj
  have huniq : ∀ y, nextR (runSeq u p n) 1 y j = true → y = a := by
    intro y hy
    exact nextR1_unique_mr (runSeq u p n) y a j hy hn
  have hhas : hasParent (runSeq u p n) 1 j = true :=
    (hasParent_iff_unique_fseq (runSeq u p n) 1 j).mpr ⟨a, hn, huniq⟩
  have hp : parent (runSeq u p n) 1 j = a :=
    parent_eq_of_unique_fseq (runSeq u p n) 1 j a hn huniq
  refine ⟨hhas, ?_⟩
  rw [hp]
  by_cases hjq : j ≤ q
  · have ha : a = j - 1 := by simp [a, hjq]
    rw [ha]
    by_cases hjqeq : j = q
    · subst j
      rw [entry1_runSeq_diag u p n (q - 1) hup (by dsimp [q]; omega),
        entry1_runSeq_run u p n q hup (by rfl) (by simpa [q] using hj)]
      dsimp [q]
      omega
    · rw [entry1_runSeq_diag u p n (j - 1) hup (by omega),
        entry1_runSeq_diag u p n j hup (by omega)]
      omega
  · have ha : a = q - 1 := by simp [a, hjq]
    rw [ha, entry1_runSeq_diag u p n (q - 1) hup (by dsimp [q]; omega),
      entry1_runSeq_run u p n j hup (by omega) (by simpa [q] using hj)]
    dsimp [q]
    omega

private theorem runSeq_row0_parent (u p n j : ℕ)
    (hjpos : 0 < j) (hj : j < p - u + n) :
    hasParent (runSeq u p n) 0 j = true ∧
      parent (runSeq u p n) 0 j = j - 1 := by
  have hn : nextR (runSeq u p n) 0 (j - 1) j = true := by
    have hs := nextR0_runSeq_step u p n (j - 1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hs
  have hp := parent_eq_of_nextR0 (runSeq u p n) (j - 1) j hn
  have hhas : hasParent (runSeq u p n) 0 j = true :=
    (hasParent_iff_unique_fseq (runSeq u p n) 0 j).mpr
      ⟨j - 1, hn, fun y hy =>
        row0_parent_unique (runSeq u p n) y (j - 1) j hy hn⟩
  exact ⟨hhas, hp⟩

private theorem RedCondA_runSeq (u p n : ℕ) (hup : u < p) :
    RedCondA (runSeq u p n) = true := by
  simp only [RedCondA, List.all_eq_true, List.mem_range]
  intro i hi j hj
  by_cases hp : hasParent (runSeq u p n) i j = true
  · have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · have hn := nextR_parent0_of_hasParent (runSeq u p n) j hp
      have hh := hn
      simp only [nextR, if_pos, nextrel0, Bool.and_eq_true,
        decide_eq_true_eq] at hh
      have hjpos : 0 < j := by omega
      have hjL : j < p - u + n := by simpa using hh.1.1.1.2
      have hparent := (runSeq_row0_parent u p n j hjpos hjL).2
      simp [hp, hparent, entry0_runSeq u p n j hjL,
        entry0_runSeq u p n (j - 1) (by omega)]
      omega
    · have hu := (hasParent_iff_unique_fseq (runSeq u p n) 1 j).mp hp
      obtain ⟨a, ha, _⟩ := hu
      have hh := ha
      simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
        Bool.and_eq_true, decide_eq_true_eq] at hh
      have hjpos : 0 < j := by omega
      have hjL : j < p - u + n := by simpa using hh.1.1.1.1.2
      simp [hp, (runSeq_row1_parent u p n j hup hjpos hjL).2]
  · simp [hp]

private theorem RedCondB_runSeq (u p n : ℕ) (hup : u < p) :
    RedCondB (runSeq u p n) = true := by
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hjzero : j = 0
  · subst j
    right
    rw [entry0_runSeq u p n 0 (by omega),
      entry1_runSeq u p n 0 (by omega)]
    simp [Nat.min_eq_left hup.le]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hjL : j < p - u + n := by
      simp only [length_runSeq] at hj
      omega
    exact Or.inl (runSeq_row0_parent u p n j hjpos hjL).1

private theorem monoT_runSeq (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    monoT (runSeq u p n) = true := by
  have hlen : 1 < p - u + n := by omega
  have hnz : zeroT (runSeq u p n) = false := by
    simp [zeroT]
    omega
  simp only [monoT, hnz, Bool.not_false, Bool.true_and]
  have hle := leR0_runSeq_interval u p n 0 (p - u + n - 1)
    (Nat.zero_le _) (by omega)
  simpa using hle

private theorem nonmulti_runSeq (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    multiT (runSeq u p n) = false := by
  simp [multiT, monoT_runSeq u p n hup hn]

private theorem runSeq_reduced (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    RTPS (runSeq u p n) := by
  exact RTPS_of_condAB_nonmulti (runSeq u p n)
    (by simp [TPS, runSeq]; omega)
    (RedCondA_runSeq u p n hup)
    (RedCondB_runSeq u p n hup)
    (nonmulti_runSeq u p n hup hn)

private theorem runSeq_eq_diag_append (u p n : ℕ) (hup : u < p) :
    runSeq u p n =
      diagSeq u (p - 1) ++ (List.range n).map (fun k => (p + k, p)) := by
  apply List.ext_getElem
  · simp [runSeq, diagSeq]
    omega
  · intro j hjL hjR
    have hj : j < p - u + n := by simpa [runSeq] using hjL
    by_cases hlo : j < p - u
    · have hdiag : j < Lng (diagSeq u (p - 1)) := by
        simp [diagSeq]
        omega
      rw [List.getElem_append_left hdiag]
      simp [runSeq, diagSeq, List.getElem_map,
        Nat.min_eq_left (by omega : u + j ≤ p)]
    · have hdiaglen : Lng (diagSeq u (p - 1)) = p - u := by
        simp [diagSeq]
        omega
      rw [List.getElem_append_right (by simpa [hdiaglen] using hlo)]
      have hrun : j - Lng (diagSeq u (p - 1)) < n := by
        rw [hdiaglen]
        omega
      have heq : u + j = p + (j - (p - u)) := by omega
      simp [runSeq, List.getElem_map, hdiaglen, heq]

private theorem diagSeq_last_row1_parent (u v : ℕ) (huv : u < v) :
    let q := v - u
    hasParent (diagSeq u v) 1 q = true ∧
      parent (diagSeq u v) 1 q = q - 1 := by
  let q := v - u
  have hrun : runSeq u v 1 = diagSeq u v := runSeq_one_eq_diagSeq u v huv
  have hn0 := nextR1_runSeq_parent u v 1 q huv (by dsimp [q]; omega)
    (by dsimp [q]; omega)
  have hn : nextR (diagSeq u v) 1 (q - 1) q = true := by
    rw [← hrun]
    simpa [q] using hn0
  have huniq : ∀ y, nextR (diagSeq u v) 1 y q = true → y = q - 1 := by
    intro y hy
    exact nextR1_unique_mr (diagSeq u v) y (q - 1) q hy hn
  exact ⟨(hasParent_iff_unique_fseq (diagSeq u v) 1 q).mpr
      ⟨q - 1, hn, huniq⟩,
    parent_eq_of_unique_fseq (diagSeq u v) 1 q (q - 1) hn huniq⟩

/-- The fundamental sequence of a sufficiently long diagonal sequence is
the diagonal prefix followed by the constant-second-row run. -/
theorem oper_diagSeq_eq_runSeq (u v n : ℕ) (huv : u + 1 < v) :
    oper (diagSeq u v) n = runSeq u (v - 1) n := by
  let M := diagSeq u v
  let q := v - u
  have hqpos : 1 < q := by dsimp [q]; omega
  have hL : Lng M = q + 1 := by
    simp [M, diagSeq, q]
    omega
  have hj1 : Lng M - 1 = q := by omega
  have hentry (i j : ℕ) (hj : j < Lng M) : entry M i j = u + j := by
    have hget : M[j]? = some (u + j, u + j) := by
      rw [List.getElem?_eq_getElem hj]
      congr 1
      simp [M, diagSeq, List.getElem_map]
    simp [entry, hget]
  have he0last : entry M 0 q = v := by
    rw [hentry 0 q (by omega)]
    dsimp [q]
    omega
  have he1last : entry M 1 q = v := by
    rw [hentry 1 q (by omega)]
    dsimp [q]
    omega
  have hidx : idx1 M q = 1 := by simp [idx1, he1last]; omega
  have hpar := diagSeq_last_row1_parent u v (by omega)
  have hhas : hasParent M 1 q = true := by simpa [M, q] using hpar.1
  have hp : parent M 1 q = q - 1 := by simpa [M, q] using hpar.2
  have he0par : entry M 0 (q - 1) = v - 1 := by
    rw [hentry 0 (q - 1) (by omega)]
    dsimp [q]
    omega
  have he1par : entry M 1 (q - 1) = v - 1 := by
    rw [hentry 1 (q - 1) (by omega)]
    dsimp [q]
    omega
  have hqne : q ≠ 0 := by omega
  have hvne : v ≠ 0 := by omega
  have hvsub : v - (v - 1) = 1 := by omega
  have hblock : List.range' (q - 1) (q - (q - 1)) = [q - 1] := by
    rw [show q - (q - 1) = 1 by omega]
    simp
  have htake : M.take (q - 1) = diagSeq u (v - 2) := by
    apply List.ext_getElem
    · simp [M, diagSeq]
      omega
    · intro j hjA hjB
      simp [M, diagSeq, List.getElem_map]
  have hflatten (xs : List ℕ) :
      (xs.map (fun k => [(v - 1 + k, v - 1)])).flatten =
        xs.map (fun k => (v - 1 + k, v - 1)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have hop : oper M n =
      diagSeq u (v - 2) ++
        (List.range n).map (fun k => (v - 1 + k, v - 1)) := by
    simp [oper, hj1, hqne, he0last, he1last, hvne, hvsub, hidx, hhas, hp,
      hblock, he0par, he1par, htake, List.flatMap_def]
    exact hflatten (List.range n)
  rw [show oper (diagSeq u v) n = oper M n from rfl, hop,
    runSeq_eq_diag_append u (v - 1) n (by omega)]
  congr 1

/-- The target term for the expanded run: `D_u (D_p^n 0)`. -/
def runTower (u p n : ℕ) : BT :=
  Dprin (u : ℕ∞) (const2ndTower p n)

private theorem flatBT_const2ndTower_run (p k : ℕ) :
    flatBT (const2ndTower p k) =
      List.replicate k (.dsym (p : ℕ∞)) ++ [.zero] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change .dsym (p : ℕ∞) :: flatBT (const2ndTower p k) =
        List.replicate (k + 1) (.dsym (p : ℕ∞)) ++ [.zero]
      rw [ih]
      rfl

private theorem flatBT_runTower (u p n : ℕ) :
    flatBT (runTower u p n) =
      .dsym (u : ℕ∞) ::
        (List.replicate n (.dsym (p : ℕ∞)) ++ [.zero]) := by
  rw [show runTower u p n = Dprin (u : ℕ∞) (const2ndTower p n) from rfl]
  change .dsym (u : ℕ∞) :: flatBT (const2ndTower p n) = _
  rw [flatBT_const2ndTower_run]

private theorem scbContexts_runTower_head (u p k : ℕ) :
    (scbContexts (runTower u p (k + 1))
      (flatBT (const2ndTower p 1))).head? =
        some (.dsym (u : ℕ∞) :: List.replicate k (.dsym (p : ℕ∞)), []) := by
  have hPself :
      (Sym.dsym (p : ℕ∞) == Sym.dsym (p : ℕ∞)) = true := by
    change ((p : ℕ∞) == (p : ℕ∞)) = true
    exact beq_self_eq_true _
  have hZself : (Sym.zero == Sym.zero) = true := rfl
  have hPZ : (Sym.dsym (p : ℕ∞) == Sym.zero) = false := rfl
  unfold scbContexts
  rw [flatBT_runTower u p (k + 1), flatBT_const2ndTower_run p 1]
  rw [List.head?_filterMap]
  apply List.findSome?_eq_some_iff.mpr
  refine ⟨List.range (k + 1), k + 1, [], ?_, ?_, ?_⟩
  · simpa using (List.range_succ (n := k + 1))
  · have hrepLen : k + 1 ≤
        (List.replicate (k + 1) (Sym.dsym (p : ℕ∞))).length := by simp
    have hdrop :
        List.drop (k + 1)
            (Sym.dsym (u : ℕ∞) ::
              (List.replicate (k + 1) (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) =
          [Sym.dsym (p : ℕ∞), Sym.zero] := by
      simp only [List.drop_succ_cons]
      rw [List.drop_append_of_le_length (by simp : k ≤
        (List.replicate (k + 1) (Sym.dsym (p : ℕ∞))).length),
        List.drop_replicate]
      rw [show k + 1 - k = 1 by omega]
      rfl
    have htake :
        List.take (k + 1)
            (Sym.dsym (u : ℕ∞) ::
              (List.replicate (k + 1) (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) =
          Sym.dsym (u : ℕ∞) ::
            List.replicate k (Sym.dsym (p : ℕ∞)) := by
      simp only [List.take_succ_cons]
      rw [List.take_append_of_le_length (by simp : k ≤
        (List.replicate (k + 1) (Sym.dsym (p : ℕ∞))).length),
        List.take_replicate, Nat.min_eq_left (by omega : k ≤ k + 1)]
    have hdropend :
        List.drop (k + 3)
            (Sym.dsym (u : ℕ∞) ::
              (List.replicate (k + 1) (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) = [] := by
      apply List.drop_eq_nil_of_le
      simp
    simp [hdrop, htake, hdropend, hPself, hZself, isPTBStr,
      parseBPAux, parseBTAux, dfree_BP, dfree_BT, dfree_BPList, BZero,
      ENat.coe_ne_top]
  · intro i hi
    have hi' : i < k + 1 := by simpa using hi
    by_cases hi0 : i = 0
    · subst i
      have htake0 :
          List.take 2
              (Sym.dsym (u : ℕ∞) ::
                (List.replicate (k + 1) (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) =
            [Sym.dsym (u : ℕ∞), Sym.dsym (p : ℕ∞)] := by
        simp only [List.take_succ_cons]
        rw [List.take_append_of_le_length (by simp : 1 ≤
          (List.replicate (k + 1) (Sym.dsym (p : ℕ∞))).length),
          List.take_replicate, Nat.min_eq_left (by omega : 1 ≤ k + 1)]
        rfl
      simp [htake0, hPZ]
    · let r := i - 1
      have hir : i = r + 1 := by dsimp [r]; omega
      have hr : r < k := by dsimp [r]; omega
      have hremain : 2 ≤ k + 1 - r := by omega
      have htake :
          List.take 2 (List.drop i
            (Sym.dsym (u : ℕ∞) ::
              (List.replicate (k + 1) (Sym.dsym (p : ℕ∞)) ++ [Sym.zero]))) =
            [Sym.dsym (p : ℕ∞), Sym.dsym (p : ℕ∞)] := by
        rw [hir]
        simp only [List.drop_succ_cons]
        rw [List.drop_append_of_le_length (by simp; omega),
          List.drop_replicate, List.take_append_of_le_length (by simp; omega),
          List.take_replicate, Nat.min_eq_left hremain]
        rfl
      simp [htake, hPself, hPZ]

private theorem parseBTAux_const2ndTower_run (p k : ℕ) :
    parseBTAux (k + 2)
        (List.replicate k (Sym.dsym (p : ℕ∞)) ++ [Sym.zero]) =
      some (const2ndTower p k, []) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change parseBTAux (k + 3)
          (Sym.dsym (p : ℕ∞) ::
            (List.replicate k (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) =
        some (const2ndTower p (k + 1), [])
      rw [parseBTAux, ih]
      rfl

private theorem unflatBT_flat_runTower (u p n : ℕ) :
    unflatBT (flatBT (runTower u p n)) = runTower u p n := by
  rw [flatBT_runTower]
  unfold unflatBT
  simp only [List.length_cons, List.length_append, List.length_replicate,
    List.length_nil, Nat.zero_add]
  rw [show n + 1 + 1 + 1 = n + 3 by omega]
  change (match parseBTAux (n + 3)
      (Sym.dsym (u : ℕ∞) ::
        (List.replicate n (Sym.dsym (p : ℕ∞)) ++ [Sym.zero])) with
    | some (t, []) => t
    | _ => BZero) = runTower u p n
  rw [parseBTAux, parseBTAux_const2ndTower_run]
  rfl

private theorem replaceScb_runTower (u p k : ℕ) :
    replaceScb (runTower u p (k + 1)) (const2ndTower p 1)
        (const2ndTower p 2) = runTower u p (k + 2) := by
  unfold replaceScb
  rw [scbContexts_runTower_head]
  have hflat :
      (Sym.dsym (u : ℕ∞) :: List.replicate k (Sym.dsym (p : ℕ∞))) ++
          flatBT (const2ndTower p 2) ++ [] =
        flatBT (runTower u p (k + 2)) := by
    rw [flatBT_const2ndTower_run, flatBT_runTower]
    simp only [List.append_nil, List.cons_append]
    rw [← List.append_assoc, ← List.replicate_add]
  simp only
  rw [hflat, unflatBT_flat_runTower]

private theorem runTower_beq_zero_false (u p k : ℕ) :
    (runTower u p k == BZero) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have heq := eq_of_beq h
  simp [runTower, Dprin, BZero] at heq

private theorem runSeq_step_indices (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    let M := runSeq u p (n + 1)
    let j₁ := p - u + n
    transJ1 M = j₁ ∧ transJ0 M = j₁ - 1 ∧
      Adm M (transJ0 M) = j₁ - 1 ∧
      entry M 1 (transJ1 M) = p ∧
      entry M 1 (transJ0 M) = p := by
  let M := runSeq u p (n + 1)
  let j₁ := p - u + n
  have hL : Lng M = j₁ + 1 := by simp [M, j₁]; omega
  have hjpos : 0 < j₁ := by dsimp [j₁]; omega
  have hp := (runSeq_row0_parent u p (n + 1) j₁ hjpos (by
    dsimp [j₁]
    omega)).2
  have hj1 : transJ1 M = j₁ := by
    change Lng M - 1 = j₁
    omega
  have hj0 : transJ0 M = j₁ - 1 := by
    change parent M 0 (Lng M - 1) = j₁ - 1
    rw [hL]
    simpa [M, j₁] using hp
  have hrunPrev : p - u ≤ j₁ - 1 := by dsimp [j₁]; omega
  have hrunLast : p - u ≤ j₁ := by dsimp [j₁]; omega
  have heprev : entry M 1 (j₁ - 1) = p := by
    simpa [M] using entry1_runSeq_run u p (n + 1) (j₁ - 1) hup
      hrunPrev (by dsimp [j₁]; omega)
  have helast : entry M 1 j₁ = p := by
    simpa [M] using entry1_runSeq_run u p (n + 1) j₁ hup
      hrunLast (by dsimp [j₁]; omega)
  have hnext : nextR M 1 (j₁ - 1) j₁ = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : nextrel1 M (j₁ - 1) j₁ = true := by simpa [nextR] using h
    have hs := hh
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hs
    omega
  have hsucc : j₁ - 1 + 1 = j₁ := by omega
  have hadm : adm M (j₁ - 1) = true := by
    simp [adm, nadm, hL, hsucc, hnext]
    omega
  have hAdm : Adm M (j₁ - 1) = j₁ - 1 := by simp [Adm, hadm]
  refine ⟨hj1, hj0, ?_, ?_, ?_⟩
  · rw [hj0]
    exact hAdm
  · rw [hj1]
    exact helast
  · rw [hj0]
    exact heprev

private theorem runSeq_step_transC2 (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    let M := runSeq u p (n + 1)
    transC2Core M (p : ℕ∞) BZero = const2ndTower p 2 := by
  let M := runSeq u p (n + 1)
  have hi := runSeq_step_indices u p n hup hn
  have hj0 : transJ0 M = p - u + n - 1 := by simpa [M] using hi.2.1
  have heLast : entry M 1 (transJ1 M) = p := by simpa [M] using hi.2.2.2.1
  have heParent : entry M 1 (transJ0 M) = p := by simpa [M] using hi.2.2.2.2
  have hL : Lng M = p - u + n + 1 := by simp [M]; omega
  have hnext : nextR M 1 (p - u + n - 1) (p - u + n) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : nextrel1 M (p - u + n - 1) (p - u + n) = true := by
      simpa [nextR] using h
    have hs := hh
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hs
    have eprev : entry M 1 (p - u + n - 1) = p := by
      simpa [M] using entry1_runSeq_run u p (n + 1) (p - u + n - 1) hup
        (by omega) (by omega)
    have elast : entry M 1 (p - u + n) = p := by
      simpa [M] using entry1_runSeq_run u p (n + 1) (p - u + n) hup
        (by omega) (by omega)
    omega
  have hsucc : p - u + n - 1 + 1 = p - u + n := by omega
  have hadmIndex : adm M (p - u + n - 1) = true := by
    simp [adm, nadm, hL, hsucc, hnext]
    omega
  have hadm : adm M (transJ0 M) = true := by rw [hj0]; exact hadmIndex
  have hIII : transCondIII M = true := by
    unfold transCondIII
    change ((0 < entry M 1 (transJ1 M)) &&
      (entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) &&
      adm M (transJ0 M)) = true
    rw [heLast, heParent, hadm]
    simp
    omega
  have hor : (transCondI M || transCondIII M || transCondV M) = true := by
    simp [hIII]
  unfold transJ1 at heLast
  change transC2Core M (p : ℕ∞) BZero = const2ndTower p 2
  unfold transC2Core
  rw [if_pos hor, heLast]
  rfl

private theorem runSeq_step_aux (u p n fuel : ℕ) (hup : u < p) (hn : 0 < n)
    (hTrans : TransAux (fuel + 1) (runSeq u p n) = runTower u p n) :
    TransAux (fuel + 2) (runSeq u p (n + 1)) = runTower u p (n + 1) := by
  let N := runSeq u p n
  let M := runSeq u p (n + 1)
  have hred : reduced M = true := by
    simpa [M] using runSeq_reduced u p (n + 1) hup (by omega)
  have hmono : monoT M = true := by
    simpa [M] using monoT_runSeq u p (n + 1) hup (by omega)
  have hlen : 1 < Lng M := by simp [M]; omega
  have hj1pos : transJ1 M ≠ 0 := by
    change Lng M - 1 ≠ 0
    omega
  have hPred : Pred M = N := by
    simpa [M, N] using Pred_runSeq_succ u p n hup
  have hi := runSeq_step_indices u p n hup hn
  have hAdm : Adm M (transJ0 M) = p - u + n - 1 := by
    simpa [M] using hi.2.2.1
  have he1 : entry M 1 (transJ1 M) = p := by simpa [M] using hi.2.2.2.1
  have hchildRed : reduced N = true := by
    simpa [N] using runSeq_reduced u p n hup hn
  have hchildMono : monoT N = true := by
    simpa [N] using monoT_runSeq u p n hup hn
  have hchildLen : 1 < Lng N := by simp [N]; omega
  have hMark : MarkAux (fuel + 1) N (Lng N - 1) = const2ndTower p 1 := by
    have hm := MarkAux_rightmost_reduced_mono fuel N hchildRed hchildMono hchildLen
    have hNlen : Lng N = p - u + n := by simp [N]
    have he : entry N 1 (Lng N - 1) = p := by
      have hlo : p - u ≤ Lng N - 1 := by
        rw [hNlen]
        omega
      have hhi : Lng N - 1 < p - u + n := by rw [hNlen]; omega
      exact entry1_runSeq_run u p n (Lng N - 1) hup hlo hhi
    simpa [he, const2ndTower] using hm
  have hAdmLast : p - u + n - 1 = Lng N - 1 := by simp [N]
  have hc2 : transC2Core M (p : ℕ∞) BZero = const2ndTower p 2 := by
    simpa [M] using runSeq_step_transC2 u p n hup hn
  have hT : TransAux (fuel + 1) N = runTower u p n := by
    simpa [N] using hTrans
  have hbeq : (runTower u p n == BZero) = false := runTower_beq_zero_false u p n
  have hvhead : bpHeadV (const2ndTower p 1) = (p : ℕ∞) := rfl
  have hthead : bpHeadT (const2ndTower p 1) = BZero := rfl
  have hfuel : fuel + 2 = (fuel + 1) + 1 := by omega
  change TransAux (fuel + 2) M = runTower u p (n + 1)
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
    runTower u p (n + 1)
  rw [hPred, hAdm, hAdmLast, hT, hMark]
  simp only [hbeq, Bool.false_eq_true, if_false, hvhead, hthead, hc2]
  have hr := replaceScb_runTower u p (n - 1)
  simpa [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] using hr

private theorem runSeq_aux (u p n fuel : ℕ) (hup : u < p) (hn : 0 < n)
    (hfuel : p - u + n ≤ fuel) :
    TransAux fuel (runSeq u p n) = runTower u p n := by
  induction n generalizing fuel with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        rw [runSeq_one_eq_diagSeq u p hup]
        change TransAux fuel (diagSeq u p) =
          Dprin (u : ℕ∞) (const2ndTower p 1)
        simpa [const2ndTower] using
          (diagSeq_TransAux_MarkAux u p fuel hup hfuel).1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        let g := fuel - 2
        have hfg : fuel = g + 2 := by dsimp [g]; omega
        have hchildFuel : p - u + n ≤ g + 1 := by dsimp [g]; omega
        have hchild := ih (g + 1) hnpos hchildFuel
        rw [hfg]
        exact runSeq_step_aux u p n g hup hnpos hchild

/-- Translation of a nonempty constant-second-row run appended to its
diagonal prefix. -/
theorem runSeq_Trans (u p n : ℕ) (hup : u < p) (hn : 0 < n) :
    Trans (runSeq u p n) = runTower u p n := by
  unfold Trans
  apply runSeq_aux u p n (transFuel (runSeq u p n)) hup hn
  unfold transFuel
  have hL : p - u + n = Lng (runSeq u p n) := by simp
  rw [hL]
  nlinarith [Nat.zero_le (nu (runSeq u p n)),
    Nat.zero_le (Lng (runSeq u p n))]

private theorem const2ndTower_eq_iterate_run (p n : ℕ) :
    const2ndTower p n = (Dprin (p : ℕ∞))^[n] BZero := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change Dprin (p : ℕ∞) (const2ndTower p n) =
        Dprin (p : ℕ∞) ((Dprin (p : ℕ∞))^[n] BZero)
      rw [ih]

/-- §8.6 (article 5575): translation commutes with the fundamental-sequence
expansion of a diagonal pair sequence. -/
theorem diagSeq_Trans_fseq (M : PS) (u j₁ n : ℕ)
    (hM : M = diagSeq u (u + j₁)) (hTPS : TPS M)
    (hn : 0 < n) (hj₁ : 1 < j₁) :
    Trans (oper M n) =
      Dprin (u : ℕ∞) ((Dprin (u + j₁ - 1 : ℕ∞))^[n] BZero) := by
  subst M
  have hop := oper_diagSeq_eq_runSeq u (u + j₁) n (by omega)
  rw [hop, runSeq_Trans u (u + j₁ - 1) n (by omega) hn]
  unfold runTower
  rw [const2ndTower_eq_iterate_run]
  have hcoe : ((u + j₁ - 1 : ℕ) : ℕ∞) =
      (u : ℕ∞) + (j₁ : ℕ∞) - 1 := by
    simp [ENat.coe_sub]
  rw [← hcoe]

#print axioms diagSeq_Trans_fseq

end PSS
