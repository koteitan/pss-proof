import «Buchholz-1986».«Buchholz-1986-2.1»

/-!
# Buchholz (1986) Lemma 2.1 — `lessBT` が狭義線形順序であること

- Isabelle: `m_7_1_lessBT_linord`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

mutual
  private theorem lessBT_irrefl : ∀ t : BT, lessBT t t = false
    | .trm ps => by simpa [lessBT] using lessBPList_irrefl ps

  private theorem lessBP_irrefl : ∀ p : BP, lessBP p p = false
    | .db u a => by simp [lessBP, lessBT_irrefl a]

  private theorem lessBPList_irrefl : ∀ ps : List BP, lessBPList ps ps = false
    | [] => by simp [lessBPList]
    | p :: ps => by simp [lessBPList, lessBP_irrefl p, lessBPList_irrefl ps]
end

mutual
  private theorem lessBT_trans : ∀ a b c : BT,
      lessBT a b = true → lessBT b c = true → lessBT a c = true
    | .trm as, .trm bs, .trm cs => by
        simpa [lessBT] using lessBPList_trans as bs cs

  private theorem lessBP_trans : ∀ p q r : BP,
      lessBP p q = true → lessBP q r = true → lessBP p r = true
    | .db u a, .db v b, .db w c => by
        simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq]
        intro huv hvw
        rcases huv with huv | ⟨huv, hab⟩
        · rcases hvw with hvw | ⟨hvw, hbc⟩
          · exact Or.inl (huv.trans hvw)
          · subst w
            exact Or.inl huv
        · subst v
          rcases hvw with huw | ⟨huw, hbc⟩
          · exact Or.inl huw
          · subst w
            exact Or.inr ⟨rfl, lessBT_trans a b c hab hbc⟩

  private theorem lessBPList_trans : ∀ xs ys zs : List BP,
      lessBPList xs ys = true → lessBPList ys zs = true →
        lessBPList xs zs = true
    | [], [], zs => by simp [lessBPList]
    | [], _ :: _, [] => by simp [lessBPList]
    | [], _ :: _, _ :: _ => by simp [lessBPList]
    | _ :: _, [], zs => by simp [lessBPList]
    | _ :: _, _ :: _, [] => by simp [lessBPList]
    | x :: xs, y :: ys, z :: zs => by
        simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
        intro hxy hyz
        rcases hxy with hxy | ⟨hxy, hxys⟩
        · rcases hyz with hyz | ⟨hyz, hyzs⟩
          · exact Or.inl (lessBP_trans x y z hxy hyz)
          · subst z
            exact Or.inl hxy
        · subst y
          rcases hyz with hxz | ⟨hxz, hyzs⟩
          · exact Or.inl hxz
          · subst z
            exact Or.inr ⟨rfl, lessBPList_trans xs ys zs hxys hyzs⟩
end

mutual
  private theorem lessBT_trichotomy : ∀ a b : BT,
      lessBT a b = true ∨ a = b ∨ lessBT b a = true
    | .trm as, .trm bs => by
        simpa [lessBT] using lessBPList_trichotomy as bs

  private theorem lessBP_trichotomy : ∀ p q : BP,
      lessBP p q = true ∨ p = q ∨ lessBP q p = true
    | .db u a, .db v b => by
        rcases lt_trichotomy u v with huv | huv | huv
        · exact Or.inl (by simp [lessBP, huv])
        · subst v
          rcases lessBT_trichotomy a b with hab | hab | hab
          · exact Or.inl (by simp [lessBP, hab])
          · subst b
            exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (by simp [lessBP, hab]))
        · exact Or.inr (Or.inr (by simp [lessBP, huv]))

  private theorem lessBPList_trichotomy : ∀ xs ys : List BP,
      lessBPList xs ys = true ∨ xs = ys ∨ lessBPList ys xs = true
    | [], [] => Or.inr (Or.inl rfl)
    | [], _ :: _ => Or.inl (by simp [lessBPList])
    | _ :: _, [] => Or.inr (Or.inr (by simp [lessBPList]))
    | x :: xs, y :: ys => by
        rcases lessBP_trichotomy x y with hxy | hxy | hxy
        · exact Or.inl (by simp [lessBPList, hxy])
        · subst y
          rcases lessBPList_trichotomy xs ys with hxs | hxs | hxs
          · exact Or.inl (by simp [lessBPList, hxs])
          · subst ys
            exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (by simp [lessBPList, hxs]))
        · exact Or.inr (Or.inr (by simp [lessBPList, hxy]))
end

/-- `lessBT` is irreflexive. -/
theorem lessBT_linear_irrefl (t : BT) : lessBT t t = false := lessBT_irrefl t

/-- `lessBT` is transitive. -/
theorem lessBT_linear_trans (a b c : BT) (hab : lessBT a b = true)
    (hbc : lessBT b c = true) : lessBT a c = true :=
  lessBT_trans a b c hab hbc

/-- `lessBT` satisfies trichotomy. -/
theorem lessBT_linear_trichotomy (a b : BT) :
    lessBT a b = true ∨ a = b ∨ lessBT b a = true :=
  lessBT_trichotomy a b

#print axioms lessBT_linear_irrefl
#print axioms lessBT_linear_trans
#print axioms lessBT_linear_trichotomy

end PSS
