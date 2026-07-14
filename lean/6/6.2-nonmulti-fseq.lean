import «6».«6.2-P-fseq»
import «6».«6.2-mono-prefix»

/-!
# §6.2 命題（非複項性と基本列の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_nonmulti_oper_1`, `_2`
- 訂正: なし
- Isabelle: `m_6_2_nonmulti_oper_1`, `_2`
- 依存: `6.2-P-fseq`, `6.2-mono-prefix`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem map_entry_range_eq_fseq
    (M : PS) (a len : ℕ) (hbound : a + len ≤ Lng M) :
    (List.range' a len).map (fun j => (entry M 0 j, entry M 1 j)) =
      (M.drop a).take len := by
  apply List.ext_getElem
  · have hnle : len ≤ M.length - a :=
      Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hbound)
    simp [hnle]
  · intro k hk₁ hk₂
    have hklt : k < len := by simpa using hk₁
    have hak : a + k < Lng M := by omega
    have hget := List.getElem?_eq_getElem (l := M) hak
    simp only [List.getElem_map, List.getElem_range', List.getElem_take,
      List.getElem_drop]
    simp [entry, hget]

private theorem nonmulti_Pred_fseq (M : PS) (hM : TPS M)
    (hm : multiT M = false) (hlen : 1 < Lng M) :
    multiT (Pred M) = false := by
  have hpred : Pred M = M.take (Lng M - 1) := by
    simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take]
  have hpredlen : Lng (Pred M) = Lng M - 1 := by simp [hpred]
  have hpredT : TPS (Pred M) := by
    intro heq
    have : Lng (Pred M) = 0 := by simp [heq]
    omega
  apply (multi_criterion_12 (Pred M) hpredT).mpr
  intro j hjpos hjL
  rw [hpred, entry_take M (Lng M - 1) 0 0 (by omega),
    entry_take M (Lng M - 1) 0 j (by simpa [hpredlen] using hjL)]
  exact (multi_criterion_12 M hM).mp hm j hjpos (by omega)

private theorem entry_flatten_replicate_first (Q : PS) (m i j : ℕ)
    (hj : j < Lng Q) :
    entry (List.replicate (m + 1) Q).flatten i j = entry Q i j := by
  simp only [List.replicate_succ, List.flatten_cons]
  unfold entry
  rw [List.getElem?_append_left hj]

private theorem P_flatten_replicate_nonmulti (Q : PS) (hQ : TPS Q)
    (hm : multiT Q = false) (n : ℕ) (hn : 1 ≤ n) :
    P (List.replicate n Q).flatten = List.replicate n Q := by
  induction n with
  | zero => omega
  | succ m ih =>
      by_cases hmzero : m = 0
      · subst m
        simpa using P_nonmulti_eq Q hm
      · have hmpos : 1 ≤ m := by omega
        let N := (List.replicate (m + 1) Q).flatten
        have hQpos : 0 < Lng Q := List.length_pos_of_ne_nil hQ
        have hNlen : Lng N = (m + 1) * Lng Q := by
          simp [N, List.length_flatten]
        have hNT : TPS N := by
          simp only [N, List.replicate_succ, List.flatten_cons]
          intro heq
          exact hQ (List.append_eq_nil_iff.mp heq).1
        have hcN : Lng Q ≤ Lng N - 1 := by
          have : 2 * Lng Q ≤ (m + 1) * Lng Q := by
            exact Nat.mul_le_mul_right (Lng Q) (by omega)
          have h2 : 2 * Lng Q ≤ Lng N := by simpa [hNlen] using this
          omega
        have hcut : entry N 0 (Lng Q) = entry Q 0 0 := by
          simp only [N, List.replicate_succ, List.flatten_cons]
          unfold entry
          rw [List.getElem?_append_right (by rfl)]
          simp only [Nat.sub_self]
          have hhead := entry_flatten_replicate_first Q (m - 1) 0 0 hQpos
          simpa [entry, Nat.sub_add_cancel hmpos] using hhead
        have hleftmin : ∀ j, j < Lng Q →
            entry N 0 (Lng Q) ≤ entry N 0 j := by
          intro j hj
          rw [hcut, entry_flatten_replicate_first Q m 0 j hj]
          by_cases hjzero : j = 0
          · subst j
            exact le_rfl
          · exact ((multi_criterion_12 Q hQ).mp hm j (by omega) hj).le
        have hadd := P_additivity N (Lng Q) hNT hQpos hcN hleftmin
        have hdecomp : N = Q ++ (List.replicate m Q).flatten := by
          simp [N, List.replicate_succ]
        have htake : N.take (Lng Q) = Q := by
          rw [hdecomp]
          simp
        have hdrop : N.drop (Lng Q) = (List.replicate m Q).flatten := by
          rw [hdecomp]
          simp
        have hseg₀ : seg N 0 (Lng Q - 1) = N.take (Lng Q) :=
          (take_eq_seg N (Lng Q) hQpos hcN).symm
        have hseg₁ : seg N (Lng Q) (Lng N - 1) = N.drop (Lng Q) :=
          (drop_eq_seg N (Lng Q) (by omega)).symm
        rw [hadd, hseg₀, hseg₁, htake, hdrop, P_nonmulti_eq Q hm, ih hmpos]
        simp only [List.singleton_append, List.replicate_succ]

theorem nonmulti_fseq_1 (M : PS) (n : ℕ) (hM : TPS M) (hn : 1 ≤ n)
    (hm : multiT M = false)
    (hnext : nextR M 0 0 (Lng M - 1) = true)
    (hentry : entry M 1 (Lng M - 1) = 0) :
    P (oper M n) = List.replicate n (Pred M) := by
  let j₁ := Lng M - 1
  have hj₁pos : 0 < j₁ := (nextR_implies_row0 M 0 0 j₁ hnext).1
  have hlen : 1 < Lng M := by simp [j₁] at hj₁pos; omega
  have hj₁ne : j₁ ≠ 0 := Nat.ne_of_gt hj₁pos
  have hn₀ : nextrel0 M 0 j₁ = true := by simpa [nextR] using hnext
  have hn₀' := hn₀
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn₀'
  have he0pos : 0 < entry M 0 j₁ := by omega
  have hz : ¬(entry M 0 j₁ = 0 ∧ entry M 1 j₁ = 0) := by omega
  have hi₁ : idx1 M j₁ = 0 := by simp [idx1, j₁, hentry]
  have huniq : ∀ y, nextR M 0 y j₁ = true → y = 0 := by
    intro y hy
    by_cases hyzero : y = 0
    · exact hyzero
    · have hylt := (nextR_implies_row0 M 0 y j₁ hy).1
      have hmin := parent_basic_1 M 0 y j₁ hM (by omega)
        (Nat.le_of_lt hylt) hnext
      have hyn : nextrel0 M y j₁ = true := by simpa [nextR] using hy
      have hyn' := hyn
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hyn'
      omega
  have hhas : hasParent M (idx1 M j₁) j₁ = true := by
    rw [hi₁]
    exact (hasParent_iff_unique_fseq M 0 j₁).mpr ⟨0, hnext, huniq⟩
  have hparent : parent M (idx1 M j₁) j₁ = 0 := by
    rw [hi₁]
    exact parent_eq_of_unique_fseq M 0 j₁ 0 hnext huniq
  have hhas0 : hasParent M 0 j₁ = true := by simpa [hi₁] using hhas
  have hparent0 : parent M 0 j₁ = 0 := by simpa [hi₁] using hparent
  have hpred : Pred M = M.take j₁ := by
    simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take, j₁]
  have hblock :
      (List.range' 0 j₁).map (fun j => (entry M 0 j, entry M 1 j)) = Pred M := by
    rw [hpred]
    simpa using map_entry_range_eq_fseq M 0 j₁ (by omega)
  have hop : oper M n = (List.replicate n (Pred M)).flatten := by
    simp [oper, j₁, hj₁ne, hz, hi₁, hhas0, hparent0, hblock, List.flatMap_def]
  have hj₁le : j₁ ≤ Lng M := by omega
  have hpredlen : Lng (Pred M) = Lng M - 1 := by
    simp [hpred, Nat.min_eq_left hj₁le, j₁]
  have hpredT : TPS (Pred M) := by
    intro heq
    have : Lng (Pred M) = 0 := by simp [heq]
    rw [hpredlen] at this
    omega
  have hpredNM := nonmulti_Pred_fseq M hM hm hlen
  rw [hop]
  exact P_flatten_replicate_nonmulti (Pred M) hpredT hpredNM n hn

theorem nonmulti_fseq_2 (M : PS) (n : ℕ) (hM : TPS M) (hn : 1 ≤ n)
    (hm : multiT M = false)
    (hcond : nextR M 0 0 (Lng M - 1) = false ∨
      0 < entry M 1 (Lng M - 1)) :
    P (oper M n) = [oper M n] := by
  by_cases hlen1 : Lng M = 1
  · have hop : oper M n = M := by simp [oper, hlen1]
    rw [hop]
    exact P_nonmulti_eq M hm
  · have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hlen : 1 < Lng M := by omega
    let j₁ := Lng M - 1
    have hj₁pos : 0 < j₁ := by simp [j₁]; omega
    have hj₁ne : j₁ ≠ 0 := Nat.ne_of_gt hj₁pos
    have hj₁L : j₁ < Lng M := by simp [j₁]; omega
    have hstrictM := (multi_criterion_12 M hM).mp hm
    have he0last : 0 < entry M 0 j₁ := by
      have := hstrictM j₁ hj₁pos hj₁L
      omega
    have hz : ¬(entry M 0 j₁ = 0 ∧ entry M 1 j₁ = 0) := by omega
    let i₁ := idx1 M j₁
    by_cases hp : hasParent M i₁ j₁ = true
    · let j₀ := parent M i₁ j₁
      let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
      let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
      have hpar : nextR M i₁ j₀ j₁ = true := by
        exact hasParent_next_fseq M i₁ j₁ hp
      have hj₀lt : j₀ < j₁ := (nextR_implies_row0 M i₁ j₀ j₁ hpar).1
      have hop : oper M n = M.take j₀ ++
          (List.range n).flatMap (fun k =>
            (List.range' j₀ (j₁ - j₀)).map (fun j =>
              (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
        simp [oper, j₁, hj₁ne, hz, i₁, hp, j₀, d₀, d₁]
      let N := oper M n
      let A := (M.take j₀).map Prod.fst
      let B := (List.range n).flatMap (fun k =>
        (List.range' j₀ (j₁ - j₀)).map (fun j => entry M 0 j + k * d₀))
      have hfst : N.map Prod.fst = A ++ B := by
        simp only [N, hop, List.map_append, A, B]
        simp [List.map_flatMap, Function.comp_def]
      have hNT : TPS N := oper_nonempty_fseq M n hM hlen hn
      have hhead : entry N 0 0 = entry M 0 0 := by
        have hh := oper_head_fseq M n hM hlen hn
        unfold entry
        rw [hh]
      have htail : ∀ x ∈ (N.map Prod.fst).tail, entry M 0 0 < x := by
        by_cases hj₀pos : 0 < j₀
        · have hALen : A.length = j₀ := by
            simp [A, Nat.min_eq_left (by omega : j₀ ≤ Lng M)]
          have hAne : A ≠ [] := by
            intro heq
            have : A.length = 0 := by simp [heq]
            omega
          have ht : (N.map Prod.fst).tail = A.tail ++ B := by
            rw [hfst, List.tail_append_of_ne_nil hAne]
          intro x hx
          rw [ht] at hx
          rcases List.mem_append.mp hx with hxA | hxB
          · obtain ⟨r, hr, hrx⟩ := List.mem_iff_getElem.mp hxA
            have hrj : r + 1 < j₀ := by simp [hALen] at hr; omega
            have hval : x = entry M 0 (r + 1) := by
              have hrL : r + 1 < Lng M := by omega
              have hget := List.getElem?_eq_getElem (l := M) hrL
              rw [List.getElem_tail] at hrx
              simp [A, List.getElem_map, List.getElem_take] at hrx
              calc
                x = (M[r + 1]'hrL).1 := hrx.symm
                _ = entry M 0 (r + 1) := by simp [entry, hget]
            rw [hval]
            exact hstrictM (r + 1) (by omega) (by omega)
          · obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hxB
            obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp hy
            have hjrng : j₀ ≤ j ∧ j < j₁ := by
              have hjrng' : j₀ ≤ j ∧ j < j₀ + (j₁ - j₀) := by
                simpa using hj
              omega
            rw [← hjeq]
            have hlt := hstrictM j (by omega) (by omega)
            omega
        · have hj₀zero : j₀ = 0 := by omega
          have hi₁pos : 0 < i₁ := by
            by_contra hnot
            have hi₁zero : i₁ = 0 := by omega
            have he1zero : entry M 1 j₁ = 0 := by
              have hi := hi₁zero
              simp [i₁, idx1] at hi
              omega
            have hnext0 : nextR M 0 0 j₁ = true := by
              simpa [hi₁zero, hj₀zero] using hpar
            rcases hcond with hno | he1pos
            · have hno' : nextR M 0 0 j₁ = false := by simpa [j₁] using hno
              simp [hnext0] at hno'
            · have he1pos' : 0 < entry M 1 j₁ := by simpa [j₁] using he1pos
              omega
          have hd₀pos : 0 < d₀ := by
            have hlt := hstrictM j₁ hj₁pos hj₁L
            simp [d₀, hi₁pos, hj₀zero]
            omega
          let C := (List.range' 0 j₁).map (fun j => entry M 0 j)
          let R := (List.range (n - 1)).flatMap (fun q =>
            (List.range' 0 j₁).map (fun j =>
              entry M 0 j + (q + 1) * d₀))
          have hnform : n = (n - 1) + 1 := by omega
          have hB : B = C ++ R := by
            dsimp only [B, C, R]
            rw [hj₀zero]
            rw [hnform, List.range_succ_eq_map, List.flatMap_cons]
            congr 1
            · simp
            · rw [List.flatMap_map]
              simp [Nat.sub_add_cancel hn]
          have hCLen : C.length = j₁ := by simp [C]
          have hCne : C ≠ [] := by
            intro heq
            have : C.length = 0 := by simp [heq]
            omega
          have hAempty : A = [] := by simp [A, hj₀zero]
          have ht : (N.map Prod.fst).tail = C.tail ++ R := by
            rw [hfst, hAempty, List.nil_append, hB,
              List.tail_append_of_ne_nil hCne]
          intro x hx
          rw [ht] at hx
          rcases List.mem_append.mp hx with hxC | hxR
          · obtain ⟨r, hr, hrx⟩ := List.mem_iff_getElem.mp hxC
            have hrj : r + 1 < j₁ := by simp [hCLen] at hr; omega
            have hval : x = entry M 0 (r + 1) := by
              rw [List.getElem_tail] at hrx
              simp [C, List.getElem_map, List.getElem_range'] at hrx
              exact hrx.symm
            rw [hval]
            exact hstrictM (r + 1) (by omega) (by omega)
          · obtain ⟨q, hq, hy⟩ := List.mem_flatMap.mp hxR
            obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp hy
            have hjrng : j < j₁ := by simpa using hj
            rw [← hjeq]
            by_cases hjzero : j = 0
            · subst j
              have hprod : 0 < (q + 1) * d₀ := Nat.mul_pos (by omega) hd₀pos
              omega
            · have hlt := hstrictM j (by omega) (by omega)
              omega
      have hstrictN : ∀ k, 0 < k → k < Lng N →
          entry N 0 0 < entry N 0 k := by
        intro k hkpos hkN
        have hmaplen : (N.map Prod.fst).length = Lng N := by simp
        have htailLen : (N.map Prod.fst).tail.length = Lng N - 1 := by simp
        have hkTail : k - 1 < (N.map Prod.fst).tail.length := by omega
        have hmem := List.getElem_mem hkTail
        have hgt := htail ((N.map Prod.fst).tail[k - 1]) hmem
        have hkEq : k - 1 + 1 = k := by omega
        have hNth : (N.map Prod.fst).tail[k - 1] = entry N 0 k := by
          have htget := List.getElem_tail (l := N.map Prod.fst) hkTail
          have htget' : (N.map Prod.fst).tail[k - 1] =
              (N.map Prod.fst)[k] := by simpa only [hkEq] using htget
          have hget := List.getElem?_eq_getElem (l := N) hkN
          calc
            (N.map Prod.fst).tail[k - 1] = (N.map Prod.fst)[k] := htget'
            _ = N[k].1 := by simp
            _ = entry N 0 k := by simp [entry, hget]
        calc
          entry N 0 0 = entry M 0 0 := hhead
          _ < (N.map Prod.fst).tail[k - 1] := hgt
          _ = entry N 0 k := hNth
      have hnonmultiN : multiT N = false :=
        (multi_criterion_12 N hNT).mpr hstrictN
      change P N = [N]
      exact P_nonmulti_eq N hnonmultiN
    · have hpfalse : hasParent M i₁ j₁ = false := by simpa using hp
      have hop : oper M n = Pred M := by
        simp [oper, j₁, hj₁ne, hz, i₁, hpfalse]
      rw [hop]
      exact P_nonmulti_eq (Pred M) (nonmulti_Pred_fseq M hM hm hlen)

#print axioms nonmulti_fseq_1
#print axioms nonmulti_fseq_2

end PSS
