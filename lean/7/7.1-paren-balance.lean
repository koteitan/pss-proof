import PSS.Scb

/-!
# §7.1 命題（順序数項のカッコの個数が左右で等しいこと）

- Isabelle: `m_7_1_paren_balance`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private def symCount (s : Sym) (xs : List Sym) : ℕ :=
  (xs.filter fun x => x = s).length

private def parenBalanced (xs : List Sym) : Prop :=
  symCount .lp xs = symCount .rp xs

private theorem flatBT_parenBalanced (t : BT) : parenBalanced (flatBT t) := by
  exact BT.rec
    (motive_1 := fun a => parenBalanced (flatBT a))
    (motive_2 := fun p => parenBalanced (flatBP p))
    (motive_3 := fun ps => parenBalanced (flatBPTail ps))
    (fun ps ih => by
      cases ps with
      | nil => simp [flatBT, parenBalanced, symCount]
      | cons p ps =>
          cases ps with
          | nil =>
              simpa [flatBT, flatBPTail, parenBalanced, symCount] using ih
          | cons q qs =>
              simp [flatBT, flatBPTail, parenBalanced, symCount] at ih ⊢
              omega)
    (fun u a ih => by
      simpa [flatBP, parenBalanced, symCount] using ih)
    (by simp [flatBPTail, parenBalanced, symCount])
    (fun p ps ihp ihps => by
      simp [flatBPTail, parenBalanced, symCount] at ihp ihps ⊢
      omega)
    t

/-- The string representation of a Buchholz term contains equally many left and right parentheses. -/
theorem paren_balance (t : BT) (_ht : t ∈ T_B) :
    ((flatBT t).filter fun x => x = .lp).length =
      ((flatBT t).filter fun x => x = .rp).length := by
  exact flatBT_parenBalanced t

#print axioms paren_balance

end PSS
