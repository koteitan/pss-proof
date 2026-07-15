import «6».«6.6-P-preserves-reduced»
import «6».«6.5-Red-le-invariance»

/-!
# §6.6 `P` ブロックと係数条件 (A), (B)

- Isabelle: `m_6_6_RedCond_P_block`, `m_6_6_RedCond_concat_lift`
- 依存: §6.4 `P_IdxSum`, `P_leftend_lmin`, §5.1 `ancestor_basic_1`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- `P M` のブロックは `IdxSum` から始まる非空の切片である。 -/
theorem P_block_data (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) :
    let B := (P M).getD J []
    let a := (IdxSum (P M)).getD J 0
    B = seg M a (a + Lng B - 1) ∧
      0 < Lng B ∧ a + Lng B - 1 < Lng M := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  let n := (IdxSum (P M)).getD (J + 1) 0
  have hpos : 0 < Lng B := by
    simpa [B] using P_component_nonempty M J hM hJ
  have hdiff : n = a + Lng B := by
    simpa [n, a, B] using idxSum_diff (P M) J hJ
  have hcomp : B = seg M a (n - 1) := by
    simpa [B, a, n] using P_IdxSum M J hM (by omega)
  have hnextle : n ≤ (IdxSum (P M)).getD (P M).length 0 := by
    simpa [n] using idxSum_mono (P M) (J + 1) (P M).length
      (by omega) (le_refl _)
  have htotal : (IdxSum (P M)).getD (P M).length 0 = Lng M := by
    calc
      (IdxSum (P M)).getD (P M).length 0 = Lng (P M).flatten :=
        idxSum_total (P M)
      _ = Lng M := congrArg Lng (P_concat M)
  have hend : a + Lng B - 1 < Lng M := by
    rw [← hdiff]
    omega
  have hfirst : B = seg M a (a + Lng B - 1) := by
    calc
      B = seg M a (n - 1) := hcomp
      _ = seg M a (a + Lng B - 1) := by rw [hdiff]
  exact ⟨by simpa [B, a] using hfirst,
    by simpa [B] using hpos, by simpa [B, a] using hend⟩

/-- ブロック内の係数は元の列の係数をオフセットしたもの。 -/
theorem P_component_entry (M : PS) (J i j : ℕ) (hM : TPS M)
    (hJ : J < (P M).length)
    (hj : j < Lng ((P M).getD J [])) :
    entry ((P M).getD J []) i j =
      entry M i ((IdxSum (P M)).getD J 0 + j) := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  obtain ⟨hB, _, _⟩ := P_block_data M J hM hJ
  have hB' : B = seg M a (a + Lng B - 1) := by
    simpa [B, a] using hB
  have hjseg : j < Lng (seg M a (a + Lng B - 1)) := by
    rw [← hB']
    simpa [B] using hj
  change entry B i j = entry M i (a + j)
  rw [hB']
  exact entry_seg M a (a + Lng B - 1) i j hjseg

private theorem nextR_lt_pc (M : PS) (i p q : ℕ)
    (hnext : nextR M i p q = true) : p < q := by
  by_cases hi : i = 0
  · have hh : nextrel0 M p q = true := by simpa [nextR, hi] using hnext
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  · have hh : nextrel1 M p q = true := by simpa [nextR, hi] using hnext
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.2

private theorem nextR_unique_pc (M : PS) (i p q : ℕ) (hi : i < 2)
    (hnext : nextR M i p q = true) :
    ∀ r, nextR M i r q = true → r = p := by
  intro r hr
  by_cases hi0 : i = 0
  · subst i
    exact row0_parent_unique M r p q hr hnext
  · have hi1 : i = 1 := by omega
    subst i
    exact nextR1_unique_mr M r p q hr hnext

/-- `P` ブロック内の親辺は元の列へシフトで持ち上がる。 -/
theorem P_local_nextR_lift (M : PS) (J i p q : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) (_hi : i < 2)
    (hp : p < Lng ((P M).getD J []))
    (hq : q < Lng ((P M).getD J [])) :
    nextR ((P M).getD J []) i p q =
      nextR M i ((IdxSum (P M)).getD J 0 + p)
        ((IdxSum (P M)).getD J 0 + q) := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  obtain ⟨hB, hpos, hend⟩ := P_block_data M J hM hJ
  have hB' : B = seg M a (a + Lng B - 1) := by
    simpa [B, a] using hB
  have hpos' : 0 < Lng B := by simpa [B] using hpos
  have hend' : a + Lng B - 1 < Lng M := by simpa [B, a] using hend
  have hse : a ≤ a + Lng B - 1 := by omega
  have hpseg : p < Lng (seg M a (a + Lng B - 1)) := by
    rw [← hB']
    simpa [B] using hp
  have hqseg : q < Lng (seg M a (a + Lng B - 1)) := by
    rw [← hB']
    simpa [B] using hq
  change nextR B i p q = nextR M i (a + p) (a + q)
  rw [hB']
  exact nextR_seg_adm M a (a + Lng B - 1) i p q
    hse hend' hpseg hqseg

/-- `P` ブロック内の列の親は、ブロック左端より左に出ない。 -/
theorem P_parent_ge_start (M : PS) (J i p j : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) (hi : i < 2)
    (hj : (IdxSum (P M)).getD J 0 ≤ j)
    (hnext : nextR M i p j = true) :
    (IdxSum (P M)).getD J 0 ≤ p := by
  let a := (IdxSum (P M)).getD J 0
  have hlmin := (P_leftend_lmin M J hM hJ).2
  have hanc : leR M 0 p j = true := by
    by_cases hi0 : i = 0
    · subst i
      exact nextR0_leR M p j hnext
    · have hi1 : i = 1 := by omega
      subst i
      have hn : nextrel1 M p j = true := by simpa [nextR] using hnext
      have hh := hn
      simp only [nextrel1, Bool.and_eq_true] at hh
      simpa [leR] using hh.1.2
  by_contra hnot
  have hpa : p < a := by simpa [a] using hnot
  have hstrict : entry M 0 p < entry M 0 a :=
    ancestor_basic_1 M p a j hM hpa (by simpa [a] using hj) hanc
  have hreverse : entry M 0 a ≤ entry M 0 p := by
    simpa [a] using hlmin p hpa
  omega

/-- グローバルな親辺を所属 `P` ブロックへ降ろす。 -/
theorem P_global_nextR_descend (M : PS) (J i p q : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) (hi : i < 2)
    (hq : q < Lng ((P M).getD J []))
    (hnext : nextR M i p ((IdxSum (P M)).getD J 0 + q) = true) :
    (IdxSum (P M)).getD J 0 ≤ p ∧
      nextR ((P M).getD J []) i
        (p - (IdxSum (P M)).getD J 0) q = true := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  have hge : a ≤ p :=
    P_parent_ge_start M J i p (a + q) hM hJ hi (by simp [a])
      (by simpa [a] using hnext)
  have hplt : p < a + q := nextR_lt_pc M i p (a + q) (by simpa [a] using hnext)
  have hqB : q < Lng B := by simpa [B] using hq
  have hlocal : p - a < Lng B := by
    have : p - a < q := by omega
    exact this.trans hqB
  have hbridge := P_local_nextR_lift M J i (p - a) q hM hJ hi
    (by simpa [B] using hlocal) hq
  have hshift : a + (p - a) = p := Nat.add_sub_of_le hge
  refine ⟨by simpa [a] using hge, ?_⟩
  rw [hbridge, hshift]
  simpa [a] using hnext

/-- ブロック内で親を持つことと、元の列でシフトした列が親を持つことは同値。 -/
theorem P_hasParent_iff (M : PS) (J i q : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) (hi : i < 2)
    (hq : q < Lng ((P M).getD J [])) :
    hasParent ((P M).getD J []) i q = true ↔
      hasParent M i ((IdxSum (P M)).getD J 0 + q) = true := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  constructor
  · intro hpB
    let p := parent B i q
    have hnB : nextR B i p q = true := hasParent_next_fseq B i q hpB
    have hplt : p < Lng B := (nextR_lt_pc B i p q hnB).trans hq
    have hnM : nextR M i (a + p) (a + q) = true := by
      have hb := P_local_nextR_lift M J i p q hM hJ hi
        (by simpa [B] using hplt) hq
      rw [← hb]
      simpa [B] using hnB
    exact (hasParent_iff_unique_fseq M i (a + q)).mpr
      ⟨a + p, hnM, nextR_unique_pc M i (a + p) (a + q) hi hnM⟩
  · intro hpM
    let p := parent M i (a + q)
    have hnM : nextR M i p (a + q) = true := hasParent_next_fseq M i (a + q) hpM
    obtain ⟨hge, hnB⟩ := P_global_nextR_descend M J i p q hM hJ hi hq
      (by simpa [a] using hnM)
    exact (hasParent_iff_unique_fseq B i q).mpr
      ⟨p - a, by simpa [B, a] using hnB,
        nextR_unique_pc B i (p - a) q hi (by simpa [B, a] using hnB)⟩

/-- 親の添字もブロック左端分だけシフトする。 -/
theorem P_parent_shift (M : PS) (J i q : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) (hi : i < 2)
    (hq : q < Lng ((P M).getD J []))
    (hp : hasParent ((P M).getD J []) i q = true) :
    (IdxSum (P M)).getD J 0 +
        parent ((P M).getD J []) i q =
      parent M i ((IdxSum (P M)).getD J 0 + q) := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  let p := parent B i q
  have hnB : nextR B i p q = true := hasParent_next_fseq B i q hp
  have hpL : p < Lng B := (nextR_lt_pc B i p q hnB).trans hq
  have hnM : nextR M i (a + p) (a + q) = true := by
    have hb := P_local_nextR_lift M J i p q hM hJ hi
      (by simpa [B] using hpL) hq
    rw [← hb]
    exact hnB
  have heq := parent_eq_of_unique_fseq M i (a + q) (a + p) hnM
    (nextR_unique_pc M i (a + p) (a + q) hi hnM)
  simpa [B, a, p] using heq.symm

/-- 条件 (A), (B) は各 `P` ブロックに遺伝する。 -/
theorem RedCondAB_P_component (M : PS) (J : ℕ) (hM : TPS M)
    (hA : RedCondA M = true) (hB : RedCondB M = true)
    (hJ : J < (P M).length) :
    RedCondA ((P M).getD J []) = true ∧
      RedCondB ((P M).getD J []) = true := by
  let B := (P M).getD J []
  let a := (IdxSum (P M)).getD J 0
  obtain ⟨hBseg, hBpos, hend⟩ := P_block_data M J hM hJ
  have hBseg' : B = seg M a (a + Lng B - 1) := by
    simpa [B, a] using hBseg
  have hBpos' : 0 < Lng B := by simpa [B] using hBpos
  have hend' : a + Lng B - 1 < Lng M := by simpa [B, a] using hend
  have hAblock : RedCondA B = true := by
    rw [hBseg']
    exact RedCondA_seg M a (a + Lng B - 1) (by omega) hend' hA
  have hBblock : RedCondB B = true := by
    have hglobal := hB
    simp only [RedCondB, List.all_eq_true, List.mem_range] at hglobal ⊢
    intro q hqrange
    have hq : q < Lng B := by omega
    by_cases hpB : hasParent B 0 q = true
    · simp [hpB]
    · have hpB' : hasParent B 0 q = false := Bool.eq_false_of_not_eq_true hpB
      have hpM' : hasParent M 0 (a + q) = false := by
        apply Bool.eq_false_iff.mpr
        intro hpM
        have := (P_hasParent_iff M J 0 q hM hJ (by omega) hq).mpr hpM
        exact hpB this
      have haqL : a + q < Lng M := by
        have : a + q ≤ a + Lng B - 1 := by omega
        exact this.trans_lt hend'
      have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hg := hglobal (a + q) (by omega)
      have heq : entry M 0 (a + q) = entry M 1 (a + q) := by
        simpa [hpM'] using hg
      have he0 := P_component_entry M J 0 q hM hJ hq
      have he1 := P_component_entry M J 1 q hM hJ hq
      have he0' : entry B 0 q = entry M 0 (a + q) := by
        simpa [B, a] using he0
      have he1' : entry B 1 q = entry M 1 (a + q) := by
        simpa [B, a] using he1
      simp only [hpB', Bool.false_or, decide_eq_true_eq]
      exact he0'.trans (heq.trans he1'.symm)
  exact ⟨by simpa [B] using hAblock, by simpa [B] using hBblock⟩

/-- 各 `P` ブロックの条件 (A), (B) は連結した元の列へ持ち上がる。 -/
theorem RedCondAB_of_P_components (M : PS) (hM : TPS M)
    (hblocks : ∀ J, J < (P M).length →
      RedCondA ((P M).getD J []) = true ∧
        RedCondB ((P M).getD J []) = true) :
    RedCondA M = true ∧ RedCondB M = true := by
  have hA : RedCondA M = true := by
    apply RedCondA_intro
    intro i j hi hj hpM
    have htotal : (IdxSum (P M)).getD (P M).length 0 = Lng M := by
      calc
        (IdxSum (P M)).getD (P M).length 0 = Lng (P M).flatten :=
          idxSum_total (P M)
        _ = Lng M := congrArg Lng (P_concat M)
    obtain ⟨J, hJ, haj, hjn⟩ := idxSum_locate (P M) j (by rw [htotal]; exact hj)
    let a := (IdxSum (P M)).getD J 0
    let B := (P M).getD J []
    let q := j - a
    have hdiff : (IdxSum (P M)).getD (J + 1) 0 = a + Lng B := by
      simpa [a, B] using idxSum_diff (P M) J hJ
    have hq : q < Lng B := by simp [q]; omega
    let p := parent M i j
    have hnM : nextR M i p j = true := hasParent_next_fseq M i j hpM
    have hnM' : nextR M i p (a + q) = true := by
      have : a + q = j := by simp [q]; omega
      rwa [this]
    obtain ⟨hpge, hnB⟩ := P_global_nextR_descend M J i p q hM hJ hi hq
      (by simpa [a] using hnM')
    have hpB : hasParent B i q = true :=
      (hasParent_iff_unique_fseq B i q).mpr
        ⟨p - a, by simpa [B, a] using hnB,
          nextR_unique_pc B i (p - a) q hi (by simpa [B, a] using hnB)⟩
    have hparB : parent B i q = p - a :=
      parent_eq_of_unique_fseq B i q (p - a) (by simpa [B, a] using hnB)
        (nextR_unique_pc B i (p - a) q hi (by simpa [B, a] using hnB))
    have hpLocal : p - a < Lng B := (nextR_lt_pc B i (p - a) q
      (by simpa [B, a] using hnB)).trans hq
    have hlocal := RedCondA_apply B (hblocks J hJ).1 i q hi hq hpB
    rw [hparB] at hlocal
    have hep := P_component_entry M J i (p - a) hM hJ
      (by simpa [B] using hpLocal)
    have heq := P_component_entry M J i q hM hJ hq
    have hashift : a + (p - a) = p := Nat.add_sub_of_le (by simpa [a] using hpge)
    have haq : a + q = j := by simp [q]; omega
    have hep' : entry B i (p - a) = entry M i (a + (p - a)) := by
      simpa [B, a] using hep
    have heq' : entry B i q = entry M i (a + q) := by
      simpa [B, a] using heq
    rw [hep', heq', hashift, haq] at hlocal
    simpa [p] using hlocal
  have hB : RedCondB M = true := by
    simp only [RedCondB, List.all_eq_true, List.mem_range]
    intro j hjrange
    by_cases hpM : hasParent M 0 j = true
    · simp [hpM]
    · have hpM' : hasParent M 0 j = false := Bool.eq_false_of_not_eq_true hpM
      have hj : j < Lng M := by
        have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
        omega
      have htotal : (IdxSum (P M)).getD (P M).length 0 = Lng M := by
        calc
          (IdxSum (P M)).getD (P M).length 0 = Lng (P M).flatten :=
            idxSum_total (P M)
          _ = Lng M := congrArg Lng (P_concat M)
      obtain ⟨J, hJ, haj, hjn⟩ := idxSum_locate (P M) j (by rw [htotal]; exact hj)
      let a := (IdxSum (P M)).getD J 0
      let B := (P M).getD J []
      let q := j - a
      have hdiff : (IdxSum (P M)).getD (J + 1) 0 = a + Lng B := by
        simpa [a, B] using idxSum_diff (P M) J hJ
      have hq : q < Lng B := by simp [q]; omega
      have hpB' : hasParent B 0 q = false := by
        apply Bool.eq_false_iff.mpr
        intro hpB
        have hpMtrue := (P_hasParent_iff M J 0 q hM hJ (by omega) hq).mp
          (by simpa [B] using hpB)
        have haq : a + q = j := by simp [q]; omega
        rw [show (IdxSum (P M)).getD J 0 + q = j by simpa [a] using haq] at hpMtrue
        exact hpM hpMtrue
      have hblockB := (hblocks J hJ).2
      have hh := hblockB
      simp only [RedCondB, List.all_eq_true, List.mem_range] at hh
      have hhB : ∀ x < Lng B - 1 + 1,
          (hasParent B 0 x || decide (entry B 0 x = entry B 1 x)) = true := by
        simpa [B] using hh
      have hqrange : q < Lng B - 1 + 1 := by omega
      have heqB : entry B 0 q = entry B 1 q := by
        simpa [hpB'] using hhB q hqrange
      have he0 := P_component_entry M J 0 q hM hJ hq
      have he1 := P_component_entry M J 1 q hM hJ hq
      have haq : a + q = j := by simp [q]; omega
      have he0' : entry B 0 q = entry M 0 (a + q) := by
        simpa [B, a] using he0
      have he1' : entry B 1 q = entry M 1 (a + q) := by
        simpa [B, a] using he1
      simp only [hpM', Bool.false_or, decide_eq_true_eq]
      rw [← haq]
      exact he0'.symm.trans (heqB.trans he1')
  exact ⟨hA, hB⟩

#print axioms RedCondAB_P_component
#print axioms RedCondAB_of_P_components

end PSS
