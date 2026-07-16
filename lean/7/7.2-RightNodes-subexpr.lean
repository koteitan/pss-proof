import «7».«7.2-scb-unique»

/-!
# §7.2 — `RightNodes` and subexpressions

Lean translation of `m_7_2_RightNodes_subexpr` from
`isabelle/pss_mechanized.thy`.  The construction replaces the zero argument at
the bottom of the rightmost principal spine and records the canonical split at
the last `zero` in the flattened code.
-/

namespace PSS

/-! ## Right-spine substitution -/

/- Replace the zero argument at the bottom of the rightmost principal spine
of a nonzero term by `c`.  At zero itself there is no principal to replace. -/
mutual
  def spineSub : BT → BT → BT
    | .trm ps, c => .trm (spineSubList ps c)
  def spineSubBP : BP → BT → BP
    | .db u (.trm []), c => .db u c
    | .db u (.trm (p :: ps)), c =>
        .db u (spineSub (.trm (p :: ps)) c)
  def spineSubList : List BP → BT → List BP
    | [], _ => []
    | [p], c => [spineSubBP p c]
    | p :: q :: ps, c => p :: spineSubList (q :: ps) c
end

/-! ## Canonical split at the right-spine bottom -/

/-- Flattening of a list of top-level principal components, without the outer
parentheses used for a multi-term. -/
private def flatBPSeq : List BP → List Sym
  | [] => []
  | p :: ps => flatBP p ++ flatBPTail ps

/- Prefix and suffix around the `zero` at the bottom of the rightmost spine. -/
mutual
  private def spinePre : BT → List Sym
    | .trm [] => []
    | .trm [p] => spinePreBP p
    | .trm (p :: q :: ps) => .lp :: spinePreList (p :: q :: ps)
  private def spinePreBP : BP → List Sym
    | .db u a => .dsym u :: spinePre a
  private def spinePreList : List BP → List Sym
    | [] => []
    | [p] => spinePreBP p
    | p :: q :: ps => flatBP p ++ (.cm :: spinePreList (q :: ps))
end

mutual
  private def spinePost : BT → List Sym
    | .trm [] => []
    | .trm [p] => spinePostBP p
    | .trm (p :: q :: ps) => spinePostList (p :: q :: ps) ++ [.rp]
  private def spinePostBP : BP → List Sym
    | .db _ a => spinePost a
  private def spinePostList : List BP → List Sym
    | [] => []
    | [p] => spinePostBP p
    | _ :: q :: ps => spinePostList (q :: ps)
end

#guard spineSub (Dprin 2 BZero) (Dprin 3 BZero) ==
  Dprin 2 (Dprin 3 BZero)
#guard RightNodes
    (spineSub (BT.trm [.db 0 BZero, .db 1 (Dprin 2 BZero)])
      (Dprin 3 BZero)) == [1, 2, 3]

private def SpineSplitBT (t : BT) : Prop :=
  flatBT t = spinePre t ++ [.zero] ++ spinePost t

private def SpineSplitBP (p : BP) : Prop :=
  flatBP p = spinePreBP p ++ [.zero] ++ spinePostBP p

private def SpineSplitList (ps : List BP) : Prop :=
  ps ≠ [] → flatBPSeq ps = spinePreList ps ++ [.zero] ++ spinePostList ps

/-- The selected `zero` is exactly the last `zero` on the rightmost spine. -/
private theorem spine_split (t : BT) : SpineSplitBT t := by
  exact BT.rec
    (motive_1 := SpineSplitBT)
    (motive_2 := SpineSplitBP)
    (motive_3 := SpineSplitList)
    (fun ps hps => by
      cases ps with
      | nil => simp [SpineSplitBT, flatBT, spinePre, spinePost]
      | cons p ps =>
          cases ps with
          | nil =>
              simpa [SpineSplitBT, SpineSplitList, flatBT, flatBPSeq,
                flatBPTail, spinePre, spinePost] using hps (by simp)
          | cons q qs =>
              have hs := hps (by simp)
              have hs' := congrArg (fun xs => xs ++ [.rp]) hs
              simpa [SpineSplitBT, SpineSplitList, flatBT, flatBPSeq,
                spinePre, spinePost, List.append_assoc] using hs')
    (fun u a ha => by
      simpa [SpineSplitBP, flatBP, spinePreBP, spinePostBP,
        SpineSplitBT, List.append_assoc] using
        congrArg (fun xs => .dsym u :: xs) ha)
    (by simp [SpineSplitList])
    (fun p ps hp hps => by
      intro _
      cases ps with
      | nil =>
          simpa [SpineSplitList, SpineSplitBP, flatBPSeq, spinePreList,
            flatBPTail, spinePostList] using hp
      | cons q qs =>
          have hs := hps (by simp)
          simpa [SpineSplitList, flatBPSeq, flatBPTail, spinePreList,
            spinePostList, List.append_assoc] using
            congrArg (fun xs => flatBP p ++ (.cm :: xs)) hs)
    t

private def SpinePostRPBT (t : BT) : Prop :=
  ∀ x ∈ spinePost t, x = .rp

private def SpinePostRPBP (p : BP) : Prop :=
  ∀ x ∈ spinePostBP p, x = .rp

private def SpinePostRPList (ps : List BP) : Prop :=
  ∀ x ∈ spinePostList ps, x = .rp

private theorem spinePost_allRP (t : BT) : SpinePostRPBT t := by
  exact BT.rec
    (motive_1 := SpinePostRPBT)
    (motive_2 := SpinePostRPBP)
    (motive_3 := SpinePostRPList)
    (fun ps hps => by
      cases ps with
      | nil => simp [SpinePostRPBT, spinePost]
      | cons p ps =>
          cases ps with
          | nil => simpa [SpinePostRPBT, SpinePostRPList, spinePost] using hps
          | cons q qs =>
              intro x hx
              simp only [spinePost, List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hps x hx
              · rfl)
    (fun _ a ha => by
      simpa [SpinePostRPBP, SpinePostRPBT, spinePostBP] using ha)
    (by simp [SpinePostRPList, spinePostList])
    (fun _ ps _ hps => by
      cases ps with
      | nil => simpa [SpinePostRPList, spinePostList]
      | cons q qs => simpa [SpinePostRPList, spinePostList] using hps)
    t

@[simp] private theorem spineSubList_length (ps : List BP) (c : BT) :
    (spineSubList ps c).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases ps with
      | nil => simp [spineSubList]
      | cons q qs => simpa [spineSubList] using ih

private def RNSubBT (t : BT) : Prop :=
  ∀ c, t ≠ BZero →
    RightNodes (spineSub t c) = RightNodes t ++ RightNodes c

private def RNSubBP (p : BP) : Prop :=
  ∀ c, rightNodesBP (spineSubBP p c) = rightNodesBP p ++ RightNodes c

private def RNSubList (ps : List BP) : Prop :=
  ∀ c, ps ≠ [] →
    rightNodesList (spineSubList ps c) =
      rightNodesList ps ++ RightNodes c

/-- Right-spine substitution concatenates the inserted spine. -/
private theorem rightNodes_spineSub (t : BT) : RNSubBT t := by
  exact BT.rec
    (motive_1 := RNSubBT)
    (motive_2 := RNSubBP)
    (motive_3 := RNSubList)
    (fun ps hps c ht => by
      have hne : ps ≠ [] := by
        intro h
        subst ps
        exact ht rfl
      simpa [RNSubBT, RNSubList, RightNodes, spineSub, BZero] using hps c hne)
    (fun u a ha c => by
      rcases a with ⟨ps⟩
      cases ps with
      | nil =>
          simp [spineSubBP, rightNodesBP, RightNodes, rightNodesList]
      | cons p ps =>
          have h := ha c (by simp [BZero])
          simpa [RNSubBP, RNSubBT, spineSubBP, rightNodesBP,
            List.append_assoc] using congrArg (List.cons u.toNat) h)
    (by simp [RNSubList])
    (fun p ps hp hps c _ => by
      cases ps with
      | nil =>
          simpa [RNSubList, RNSubBP, spineSubList, rightNodesList] using hp c
      | cons q qs =>
          have h := hps c (by simp)
          cases qs with
          | nil =>
              simpa [RNSubList, spineSubList, rightNodesList] using h
          | cons r rs =>
              simpa [RNSubList, spineSubList, rightNodesList] using h)
    t

private def FlatSubBT (t : BT) : Prop :=
  ∀ c, t ≠ BZero →
    flatBT (spineSub t c) =
      spinePre t ++ flatBT c ++ spinePost t

private def FlatSubBP (p : BP) : Prop :=
  ∀ c, flatBP (spineSubBP p c) =
    spinePreBP p ++ flatBT c ++ spinePostBP p

private def FlatSubList (ps : List BP) : Prop :=
  ∀ c, ps ≠ [] →
    flatBPSeq (spineSubList ps c) =
      spinePreList ps ++ flatBT c ++ spinePostList ps

/-- Flattening of the substitution replaces precisely the canonical bottom
`zero`, leaving its prefix and all-`)` suffix unchanged. -/
private theorem flat_spineSub (t : BT) : FlatSubBT t := by
  exact BT.rec
    (motive_1 := FlatSubBT)
    (motive_2 := FlatSubBP)
    (motive_3 := FlatSubList)
    (fun ps hps c ht => by
      cases ps with
      | nil => exact (ht rfl).elim
      | cons p ps =>
          cases ps with
          | nil =>
              have h := hps c (by simp)
              simpa [FlatSubBT, FlatSubList, spineSub, spineSubList,
                flatBT, flatBPSeq,
                flatBPTail, spinePre, spinePost] using h
          | cons q qs =>
              have h := hps c (by simp)
              have h' := congrArg (fun xs => .lp :: xs ++ [.rp]) h
              cases qs with
              | nil =>
                  simpa [FlatSubBT, FlatSubList, spineSub, spineSubList,
                    flatBT, flatBPSeq, flatBPTail, spinePre, spinePost,
                    spinePreList, spinePostList, List.append_assoc] using h'
              | cons r rs =>
                  simpa [FlatSubBT, FlatSubList, spineSub, spineSubList,
                    flatBT, flatBPSeq, flatBPTail, spinePre, spinePost,
                    spinePreList, spinePostList, List.append_assoc] using h')
    (fun u a ha c => by
      rcases a with ⟨ps⟩
      cases ps with
      | nil =>
          simp [spineSubBP, flatBP, spinePreBP, spinePre,
            spinePostBP, spinePost]
      | cons p ps =>
          have h := ha c (by simp [BZero])
          simpa [FlatSubBP, FlatSubBT, spineSubBP, flatBP, spinePreBP,
            spinePostBP, List.append_assoc] using
            congrArg (fun xs => .dsym u :: xs) h)
    (by simp [FlatSubList])
    (fun p ps hp hps c _ => by
      cases ps with
      | nil =>
          simpa [FlatSubList, FlatSubBP, spineSubList, flatBPSeq,
            flatBPTail, spinePreList, spinePostList] using hp c
      | cons q qs =>
          have h := hps c (by simp)
          cases qs with
          | nil =>
              simpa [FlatSubList, spineSubList, flatBPSeq, flatBPTail,
                spinePreList, spinePostList, List.append_assoc] using
                congrArg (fun xs => flatBP p ++ (.cm :: xs)) h
          | cons r rs =>
              simpa [FlatSubList, spineSubList, flatBPSeq, flatBPTail,
                spinePreList, spinePostList, List.append_assoc] using
                congrArg (fun xs => flatBP p ++ (.cm :: xs)) h)
    t

private def DFSubBT (t : BT) : Prop :=
  ∀ c, dfree_BT t = true → dfree_BT c = true →
    dfree_BT (spineSub t c) = true

private def DFSubBP (p : BP) : Prop :=
  ∀ c, dfree_BP p = true → dfree_BT c = true →
    dfree_BP (spineSubBP p c) = true

private def DFSubList (ps : List BP) : Prop :=
  ∀ c, dfree_BPList ps = true → dfree_BT c = true →
    dfree_BPList (spineSubList ps c) = true

/-- Right-spine substitution preserves `D_ω`-freeness. -/
private theorem dfree_spineSub (t : BT) : DFSubBT t := by
  exact BT.rec
    (motive_1 := DFSubBT)
    (motive_2 := DFSubBP)
    (motive_3 := DFSubList)
    (fun ps hps c ht hc => by
      simpa [DFSubBT, DFSubList, spineSub, dfree_BT] using hps c ht hc)
    (fun u a ha c hp hc => by
      rcases a with ⟨ps⟩
      cases ps with
      | nil =>
          simp [spineSubBP, dfree_BP, dfree_BT, dfree_BPList] at hp ⊢
          exact ⟨hp, hc⟩
      | cons p ps =>
          simp only [dfree_BP, Bool.and_eq_true] at hp
          simp only [spineSubBP, dfree_BP, Bool.and_eq_true]
          refine ⟨hp.1, ?_⟩
          exact ha c hp.2 hc)
    (by simp [DFSubList, spineSubList, dfree_BPList])
    (fun p ps hp hps c hpc hc => by
      simp only [dfree_BPList, Bool.and_eq_true] at hpc
      cases ps with
      | nil =>
          simpa [spineSubList, dfree_BPList] using hp c hpc.1 hc
      | cons q qs =>
          simp only [spineSubList, dfree_BPList, Bool.and_eq_true]
          refine ⟨hpc.1, ?_⟩
          exact hps c hpc.2 hc)
    t

/-- The substitution changes no top-level principal component. -/
private theorem numNat_spineSub (t c : BT) :
    numNat (spineSub t c) = numNat t := by
  rcases t with ⟨ps⟩
  change (spineSubList ps c).length = ps.length
  exact spineSubList_length ps c

/-! ## Aligning the canonical bottom with a marked occurrence -/

private theorem align_last_zero {aa bb pp qq : List Sym}
    (h : aa ++ (.zero :: pp) = bb ++ (.zero :: qq))
    (hpp : .zero ∉ pp) (hqq : .zero ∉ qq) :
    aa = bb ∧ pp = qq := by
  rcases List.append_eq_append_iff.mp h with
      ⟨mid, hbb, hrest⟩ | ⟨mid, haa, hrest⟩
  · cases mid with
    | nil =>
        simp only [List.append_nil, List.nil_append] at hbb hrest
        exact ⟨hbb.symm, by simpa using hrest⟩
    | cons x xs =>
        have hp : pp = xs ++ (.zero :: qq) := by
          simpa using congrArg List.tail hrest
        apply False.elim
        apply hpp
        rw [hp]
        simp
  · cases mid with
    | nil =>
        simp only [List.append_nil, List.nil_append] at haa hrest
        exact ⟨haa, by simpa using hrest.symm⟩
    | cons x xs =>
        have hq : qq = xs ++ (.zero :: pp) := by
          simpa using congrArg List.tail hrest
        apply False.elim
        apply hqq
        rw [hq]
        simp

private theorem flat_spineSub_at_occurrence {t₀ c : BT} {v : ℕ}
    {s b : List Sym}
    (hocc : flatBT t₀ =
      s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b)
    (hb : ∀ x ∈ b, x = .rp) (ht₀ : t₀ ≠ BZero) :
    flatBT (spineSub t₀ c) =
      s ++ flatBT (Dprin (v : ℕ∞) c) ++ b := by
  have hbzero : .zero ∉ b := by
    intro hz
    have := hb .zero hz
    cases this
  have hpostzero : .zero ∉ spinePost t₀ := by
    intro hz
    have := spinePost_allRP t₀ .zero hz
    cases this
  have halign :
      (s ++ [.dsym (v : ℕ∞)]) ++ (.zero :: b) =
        spinePre t₀ ++ (.zero :: spinePost t₀) := by
    calc
      (s ++ [.dsym (v : ℕ∞)]) ++ (.zero :: b) = flatBT t₀ := by
        simpa [Dprin, BZero, flatBT, flatBP, List.append_assoc] using hocc.symm
      _ = spinePre t₀ ++ (.zero :: spinePost t₀) := by
        simpa [SpineSplitBT, List.append_assoc] using spine_split t₀
  have aligned := align_last_zero halign hbzero hpostzero
  have hsub := flat_spineSub t₀ c ht₀
  rw [← aligned.1, ← aligned.2] at hsub
  simpa [Dprin, flatBT, flatBP, List.append_assoc] using hsub

private theorem rightNodes_ends_at_occurrence {t₀ : BT} {v : ℕ}
    {s b : List Sym}
    (hocc : flatBT t₀ =
      s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ a₀, RightNodes t₀ = a₀ ++ [v] := by
  have hocc' : flatBT t₀ =
      s ++ flatBP (.db (v : ℕ∞) BZero) ++ b := by
    simpa [Dprin, flatBT] using hocc
  obtain ⟨k, hk⟩ := scb_occurrence_rightNodes_suffix hocc' hb
  refine ⟨(RightNodes t₀).take k, ?_⟩
  calc
    RightNodes t₀ =
        (RightNodes t₀).take k ++ (RightNodes t₀).drop k :=
      (List.take_append_drop k (RightNodes t₀)).symm
    _ = (RightNodes t₀).take k ++ [v] := by
      rw [← hk]
      simp [RightNodes, rightNodesList, rightNodesBP, BZero]

/-! ## Proposition -/

/-- §7.2 proposition (`m_7_2_RightNodes_subexpr`): replacing a marked
`D_v 0` at the bottom of the rightmost spine by a principal term preserves the
top-level component count and determines a unique split of `RightNodes`.

`numNat` is the Lean definition of the article's `Lng (PB ·)`: both count the
top-level principal components of a Buchholz term. -/
theorem rightNodes_subexpr {t t₀ : BT} {v : ℕ} {s b : List Sym}
    (ht : t ∈ T_B) (_htPrincipal : ∃ p, t = .trm [p])
    (hb : ∀ x ∈ b, x = .rp) (ht₀ : t₀ ∈ T_B)
    (hocc : flatBT t₀ =
      s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b) :
    ∃ t₁, t₁ ∈ T_B ∧
      flatBT t₁ = s ++ flatBT (Dprin (v : ℕ∞) t) ++ b ∧
      numNat t₁ = numNat t₀ ∧
      ∃! aa : List ℕ × List ℕ,
        RightNodes t₁ = aa.1 ++ [v] ++ aa.2 ∧
        RightNodes t₀ = aa.1 ++ [v] ∧
        RightNodes (Dprin (v : ℕ∞) t) = [v] ++ aa.2 := by
  have ht₀ne : t₀ ≠ BZero := by
    intro hz
    subst t₀
    have hlen := congrArg List.length hocc
    simp [BZero, Dprin, flatBT, flatBP] at hlen
    omega
  let t₁ := spineSub t₀ t
  have ht₁ : t₁ ∈ T_B := by
    change dfree_BT t₁ = true
    exact dfree_spineSub t₀ t ht₀ ht
  have hflat₁ :
      flatBT t₁ = s ++ flatBT (Dprin (v : ℕ∞) t) ++ b :=
    flat_spineSub_at_occurrence hocc hb ht₀ne
  have hnum : numNat t₁ = numNat t₀ := numNat_spineSub t₀ t
  have hrn₁ : RightNodes t₁ = RightNodes t₀ ++ RightNodes t :=
    rightNodes_spineSub t₀ t ht₀ne
  obtain ⟨a₀, hrn₀⟩ := rightNodes_ends_at_occurrence hocc hb
  let a₁ := RightNodes t
  have hrnD : RightNodes (Dprin (v : ℕ∞) t) = [v] ++ a₁ := by
    simp [a₁, Dprin, RightNodes, rightNodesList, rightNodesBP]
  have hrn₁' : RightNodes t₁ = a₀ ++ [v] ++ a₁ := by
    rw [hrn₁, hrn₀]
  have huniq : ∃! aa : List ℕ × List ℕ,
      RightNodes t₁ = aa.1 ++ [v] ++ aa.2 ∧
      RightNodes t₀ = aa.1 ++ [v] ∧
      RightNodes (Dprin (v : ℕ∞) t) = [v] ++ aa.2 := by
    refine ⟨(a₀, a₁), ?_, ?_⟩
    · exact ⟨hrn₁', hrn₀, hrnD⟩
    · intro aa haa
      have hfst : aa.1 = a₀ :=
        List.append_cancel_right (haa.2.1.symm.trans hrn₀)
      have hsnd : aa.2 = a₁ :=
        List.append_cancel_left (haa.2.2.symm.trans hrnD)
      exact Prod.ext hfst hsnd
  exact ⟨t₁, ht₁, hflat₁, hnum, huniq⟩

/-- Principality-free form of the `RightNodes` splitting engine.  The body
inserted below `D_v` may be a multi-term; only its Buchholz well-formedness is
needed by downstream uses. -/
theorem rightNodes_subexpr_general {t t₀ : BT} {v : ℕ} {s b : List Sym}
    (_ht : t ∈ T_B) (hb : ∀ x ∈ b, x = .rp) (_ht₀ : t₀ ∈ T_B)
    (hocc : flatBT t₀ =
      s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b) :
    ∃! aa : List ℕ × List ℕ,
      RightNodes (spineSub t₀ t) = aa.1 ++ [v] ++ aa.2 ∧
      RightNodes t₀ = aa.1 ++ [v] ∧
      RightNodes (Dprin (v : ℕ∞) t) = [v] ++ aa.2 := by
  have ht₀ne : t₀ ≠ BZero := by
    intro hz
    subst t₀
    have hlen := congrArg List.length hocc
    simp [BZero, Dprin, flatBT, flatBP] at hlen
    omega
  have hrn : RightNodes (spineSub t₀ t) =
      RightNodes t₀ ++ RightNodes t :=
    rightNodes_spineSub t₀ t ht₀ne
  obtain ⟨a₀, hrn₀⟩ := rightNodes_ends_at_occurrence hocc hb
  let a₁ := RightNodes t
  have hrnD : RightNodes (Dprin (v : ℕ∞) t) = [v] ++ a₁ := by
    simp [a₁, Dprin, RightNodes, rightNodesList, rightNodesBP]
  have hrnSub : RightNodes (spineSub t₀ t) = a₀ ++ [v] ++ a₁ := by
    rw [hrn, hrn₀]
  refine ⟨(a₀, a₁), ⟨hrnSub, hrn₀, hrnD⟩, ?_⟩
  intro aa haa
  have hfst : aa.1 = a₀ :=
    List.append_cancel_right (haa.2.1.symm.trans hrn₀)
  have hsnd : aa.2 = a₁ :=
    List.append_cancel_left (haa.2.2.symm.trans hrnD)
  exact Prod.ext hfst hsnd

/-- Flattening companion to `rightNodes_subexpr_general`. -/
theorem flat_spineSub_at_dprin_occurrence {t₀ c : BT} {v : ℕ}
    {s b : List Sym}
    (hocc : flatBT t₀ =
      s ++ flatBT (Dprin (v : ℕ∞) BZero) ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    flatBT (spineSub t₀ c) =
      s ++ flatBT (Dprin (v : ℕ∞) c) ++ b := by
  apply flat_spineSub_at_occurrence hocc hb
  intro hz
  subst t₀
  have hlen := congrArg List.length hocc
  simp [BZero, Dprin, flatBT, flatBP] at hlen
  omega

#print axioms rightNodes_subexpr
#print axioms rightNodes_subexpr_general
#print axioms flat_spineSub_at_dprin_occurrence

end PSS
