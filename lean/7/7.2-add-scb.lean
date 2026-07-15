import «7».«7.2-scb-unique»
import «7».«7.2-scb-replaceable»

/-!
# §7.2 系（加法と scb 分解の関係）

- Isabelle: `m_7_2_add_scb_conj1`, `m_7_2_add_scb_conj2`,
  `m_7_2_add_scb_conj3_counterexample`, `m_7_2_add_scb_conj3_image`
- 状態: 第 1・第 2 主張と、原文第 3 主張の反例を移植中
-/

namespace PSS

private theorem dfree_BPList_append (xs ys : List BP) :
    dfree_BPList (xs ++ ys) = (dfree_BPList xs && dfree_BPList ys) := by
  induction xs with
  | nil => simp [dfree_BPList]
  | cons p ps ih => simp [dfree_BPList, ih, Bool.and_assoc]

/-- Buchholz addition preserves `D_ω`-freeness. -/
theorem addBT_mem_T_B {t c : BT} (ht : t ∈ T_B) (hc : c ∈ T_B) :
    addBT t c ∈ T_B := by
  rcases t with ⟨xs⟩
  rcases c with ⟨ys⟩
  change dfree_BPList xs = true at ht
  change dfree_BPList ys = true at hc
  change dfree_BPList (xs ++ ys) = true
  simp [dfree_BPList_append, ht, hc]

private theorem flatBPTail_append_singleton (xs : List BP) (p : BP) :
    flatBPTail (xs ++ [p]) = flatBPTail xs ++ (.cm :: flatBP p) := by
  induction xs with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

/-- The flat representation of an appended principal has a prefix and an
all-right-parenthesis suffix that depend only on the left summand. -/
private theorem addBT_principal_split (t : BT) :
    ∃ pre post : List Sym,
      (∀ x ∈ post, x = .rp) ∧
      ∀ p : BP,
        flatBT (addBT t (.trm [p])) = pre ++ flatBP p ++ post := by
  rcases t with ⟨xs⟩
  cases xs with
  | nil =>
      exact ⟨[], [], by simp, by intro p; simp [addBT, flatBT]⟩
  | cons q qs =>
      refine ⟨.lp :: (flatBP q ++ flatBPTail qs) ++ [.cm], [.rp], by simp, ?_⟩
      intro p
      cases qs with
      | nil => simp [addBT, flatBT, flatBPTail]
      | cons r rs =>
          change
            (.lp :: (flatBP q ++ flatBPTail ((r :: rs) ++ [p])) ++ [.rp]) =
              (.lp :: (flatBP q ++ flatBPTail (r :: rs)) ++ [.cm]) ++
                flatBP p ++ [.rp]
          rw [flatBPTail_append_singleton]
          simp [List.append_assoc]

private theorem principal_flat_isPTB {p : BP} (hp : BT.trm [p] ∈ T_B) :
    isPTB_str (flatBT (.trm [p])) := by
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hp

/-- Add-scb, conjunct (1): appending a principal term marks that last
principal component. -/
theorem add_scb_marked (t c : BT) (ht : t ∈ T_B) (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) :
    (addBT t c, c) ∈ MarkedB := by
  rcases hcP with ⟨p, rfl⟩
  rcases addBT_principal_split t with ⟨pre, post, hpost, hflat⟩
  refine ⟨pre, post, ?_⟩
  refine ⟨hflat p, ?_, hpost⟩
  intro _
  exact principal_flat_isPTB hc

/-- Add-scb, conjunct (2): replacing the final marked principal by another
principal preserves the same scb context. -/
theorem add_scb_replace_last (t c c' : BT) (s b : List Sym)
    (ht : t ∈ T_B) (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p])
    (hc' : c' ∈ T_B) (hc'P : ∃ p, c' = .trm [p])
    (h : scb_decomp (addBT t c) s (flatBT c) b) :
    scb_decomp (addBT t c') s (flatBT c') b := by
  rcases hcP with ⟨p, rfl⟩
  rcases hc'P with ⟨p', rfl⟩
  rcases addBT_principal_split t with ⟨pre, post, hpost, hflat⟩
  have hcanonical :
      scb_decomp (addBT t (.trm [p])) pre (flatBT (.trm [p])) post := by
    refine ⟨by simpa using hflat p, ?_, hpost⟩
    intro _
    exact principal_flat_isPTB hc
  have hcontexts : s = pre ∧ b = post :=
    scb_unique_decomp (addBT t (.trm [p])) s pre
      (flatBT (.trm [p])) b post (addBT_mem_T_B ht hc) h hcanonical
  rcases hcontexts with ⟨rfl, rfl⟩
  refine ⟨by simpa using hflat p', ?_, hpost⟩
  intro _
  exact principal_flat_isPTB hc'

/-- A13: the literal third add-scb claim is false because the occurrence in
its first flat-string equation need not be the occurrence selected by the scb
decomposition. -/
theorem add_scb_original_third_false :
    let t : BT := BZero
    let c : BT := Dprin 0 BZero
    let c' : BT := Dprin 0 (Dprin 0 BZero)
    let u₁ : BT := .trm [.db 0 (Dprin 0 BZero), .db 0 BZero]
    let s₁ : List Sym := [.lp]
    let b₁ : List Sym := [.cm, .dsym 0, .zero, .rp]
    let s₀ : List Sym := [.lp, .dsym 0, .dsym 0, .zero, .cm]
    let b₀ : List Sym := [.rp]
    t ∈ T_B ∧ c ∈ T_B ∧ (∃ p, c = .trm [p]) ∧
      c' ∈ T_B ∧ (∃ p, c' = .trm [p]) ∧ u₁ ∈ T_B ∧
      flatBT u₁ = s₁ ++ (.dsym 0 :: flatBT (addBT t c)) ++ b₁ ∧
      scb_decomp u₁ s₀ (flatBT c) b₀ ∧
      ¬∃ u₁', u₁' ∈ T_B ∧
        flatBT u₁' = s₁ ++ (.dsym 0 :: flatBT (addBT t c')) ++ b₁ ∧
        scb_decomp u₁' s₀ (flatBT c') b₀ := by
  dsimp
  refine ⟨by simp [T_B, BZero, dfree_BT, dfree_BPList],
    by simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList],
    ⟨.db 0 BZero, rfl⟩,
    by simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList],
    ⟨.db 0 (Dprin 0 BZero), rfl⟩,
    by simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList],
    by decide, ?_, ?_⟩
  · refine ⟨by decide, ?_, by decide⟩
    intro _
    exact ⟨.db 0 BZero, by decide, by decide⟩
  · rintro ⟨u₁', _, hflat, hscb⟩
    have hmarked := hscb.1
    simp [BZero, Dprin, addBT, flatBT, flatBP] at hflat hmarked
    have := hflat.symm.trans hmarked
    simp at this

/-- The image-existence part of corrected conjunct (3): replace the complete
outer principal `D_v(t+c)` by `D_v(t+c')`. -/
theorem add_scb_outer_image (v : ℕ) (t c c' u₁ : BT)
    (s₁ b₁ : List Sym) (ht : t ∈ T_B) (hc' : c' ∈ T_B)
    (hu₁ : u₁ ∈ T_B)
    (hflat : flatBT u₁ =
      s₁ ++ (.dsym (v : ℕ∞) :: flatBT (addBT t c)) ++ b₁) :
    ∃ u₁', u₁' ∈ T_B ∧ flatBT u₁' =
      s₁ ++ (.dsym (v : ℕ∞) :: flatBT (addBT t c')) ++ b₁ := by
  have htc' : addBT t c' ∈ T_B := addBT_mem_T_B ht hc'
  have hpr' : dfree_BP (.db (v : ℕ∞) (addBT t c')) = true := by
    simpa [dfree_BP, T_B] using htc'
  have hocc : flatBT u₁ =
      s₁ ++ flatBP (.db (v : ℕ∞) (addBT t c)) ++ b₁ := by
    simpa [flatBP] using hflat
  rcases principal_replacement_image hu₁ hpr' hocc with
    ⟨u₁', hu₁', hu₁'flat⟩
  exact ⟨u₁', hu₁', by simpa [flatBP] using hu₁'flat⟩

/-- Corrected A13 form of conjunct (3).  The alignment hypotheses state that
the `c` marked by the scb decomposition is the trailing principal occurrence
inside the displayed `D_v(t+c)` occurrence. -/
theorem add_scb_replace_aligned (v : ℕ) (t c c' u₁ : BT)
    (s₀ s₁ b₀ b₁ pre post : List Sym)
    (ht : t ∈ T_B) (_hc : c ∈ T_B) (_hcP : ∃ p, c = .trm [p])
    (hc' : c' ∈ T_B) (hc'P : ∃ p, c' = .trm [p])
    (hu₁ : u₁ ∈ T_B)
    (houter : flatBT u₁ =
      s₁ ++ (.dsym (v : ℕ∞) :: flatBT (addBT t c)) ++ b₁)
    (hmarked : scb_decomp u₁ s₀ (flatBT c) b₀)
    (hpre : flatBT (addBT t c) = pre ++ flatBT c ++ post)
    (hs : s₀ = s₁ ++ (.dsym (v : ℕ∞) :: pre))
    (hb : b₀ = post ++ b₁)
    (_hpost : ∀ x ∈ post, x = .rp)
    (hpre' : flatBT (addBT t c') = pre ++ flatBT c' ++ post) :
    ∃ u₁', u₁' ∈ T_B ∧ flatBT u₁' =
      s₁ ++ (.dsym (v : ℕ∞) :: flatBT (addBT t c')) ++ b₁ ∧
      scb_decomp u₁' s₀ (flatBT c') b₀ := by
  rcases add_scb_outer_image v t c c' u₁ s₁ b₁ ht hc' hu₁ houter with
    ⟨u₁', hu₁', hu₁'flat⟩
  have hstrings :
      s₁ ++ (.dsym (v : ℕ∞) :: flatBT (addBT t c')) ++ b₁ =
        s₀ ++ flatBT c' ++ b₀ := by
    rw [hs, hb, hpre']
    simp [List.append_assoc]
  have hu₁'markedFlat : flatBT u₁' = s₀ ++ flatBT c' ++ b₀ :=
    hu₁'flat.trans hstrings
  have hc'ptb : isPTB_str (flatBT c') := by
    rcases hc'P with ⟨p', rfl⟩
    exact principal_flat_isPTB hc'
  have hb₀rp : ∀ x ∈ b₀, x = .rp := hmarked.2.2
  have hu₁'scb : scb_decomp u₁' s₀ (flatBT c') b₀ :=
    ⟨hu₁'markedFlat, fun _ => hc'ptb, hb₀rp⟩
  exact ⟨u₁', hu₁', hu₁'flat, hu₁'scb⟩

#print axioms addBT_mem_T_B
#print axioms add_scb_marked
#print axioms add_scb_replace_last
#print axioms add_scb_original_third_false
#print axioms add_scb_outer_image
#print axioms add_scb_replace_aligned

end PSS
