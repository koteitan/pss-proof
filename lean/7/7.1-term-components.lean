import PSS.Buchholz

/-!
# §7.1 命題（順序数項の単項成分の基本性質）

- Isabelle: `m_7_1_term_components`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- `PB` is empty exactly at zero, and recombining all its components recovers the term. -/
theorem term_components (t : BT) (ht : t ∈ T_B) :
    ((PB t).length = 0 ↔ t = BZero) ∧ SigmaB (PB t) = t := by
  cases t with
  | trm ps =>
      clear ht
      constructor
      · simp [PB, untrm, BZero]
      · have hflat :
            (ps.map (fun p => BT.trm [p])).flatMap untrm = ps := by
          induction ps with
          | nil => rfl
          | cons p ps ih => simp [untrm, ih]
        exact congrArg BT.trm hflat

#print axioms term_components

end PSS
