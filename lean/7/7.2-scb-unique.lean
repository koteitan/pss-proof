import PSS.Scb

/-!
# §7.2 命題（scb 分解の一意性）

- Isabelle: `m_7_2_scb_unique_sb`, `m_7_2_scb_unique_decomp`
- 状態: 第 1 主張（固定した `c` に対する `(s,b)` の一意性）を証明済
-/

namespace PSS

/-- 文字列末尾の連続した右括弧の個数。 -/
private def trailRP (xs : List Sym) : ℕ :=
  (xs.reverse.takeWhile (· = .rp)).length

private theorem takeWhile_append_of_all {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : p x := h x (by simp)
      have hxs : ∀ y ∈ xs, p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

private theorem takeWhile_append_of_exists_not {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∃ x ∈ xs, ¬p x) :
    (xs ++ ys).takeWhile p = xs.takeWhile p := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x
      · have hxs : ∃ y ∈ xs, ¬p y := by
          rcases h with ⟨y, hy, hny⟩
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact (hny hx).elim
          · exact ⟨y, hy, hny⟩
        simp [hx, ih hxs]
      · simp [hx]

private theorem trailRP_append (xs b : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    trailRP (xs ++ b) = b.length + trailRP xs := by
  have hrev : ∀ x ∈ b.reverse, x = .rp := by
    intro x hx
    exact hb x (List.mem_reverse.mp hx)
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_all (fun x : Sym => x = .rp) b.reverse xs.reverse hrev]
  simp

private theorem trailRP_prefix (s c : List Sym)
    (hc : ∃ x ∈ c, x ≠ .rp) :
    trailRP (s ++ c) = trailRP c := by
  have hrev : ∃ x ∈ c.reverse, x ≠ .rp := by
    rcases hc with ⟨x, hx, hne⟩
    exact ⟨x, List.mem_reverse.mpr hx, hne⟩
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_exists_not (fun x : Sym => x = .rp)
    c.reverse s.reverse hrev]

private theorem isPTB_str_has_nonRP {c : List Sym} (hc : isPTB_str c) :
    ∃ x ∈ c, x ≠ .rp := by
  rcases hc with ⟨⟨u, a⟩, _, rfl⟩
  exact ⟨.dsym u, by simp [flatBP]⟩

private theorem allRP_eq_of_length_eq {b₀ b₁ : List Sym}
    (h₀ : ∀ x ∈ b₀, x = .rp) (h₁ : ∀ x ∈ b₁, x = .rp)
    (hlen : b₀.length = b₁.length) : b₀ = b₁ := by
  induction b₀ generalizing b₁ with
  | nil =>
      cases b₁ with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases b₁ with
      | nil => simp at hlen
      | cons y ys =>
          have hx : x = .rp := h₀ x (by simp)
          have hy : y = .rp := h₁ y (by simp)
          have hxs : ∀ z ∈ xs, z = .rp := by
            intro z hz
            exact h₀ z (by simp [hz])
          have hys : ∀ z ∈ ys, z = .rp := by
            intro z hz
            exact h₁ z (by simp [hz])
          have hlens : xs.length = ys.length := Nat.succ.inj hlen
          simp [hx, hy, ih hxs hys hlens]

private theorem scb_unique_nonzero {t : BT} {s₀ s₁ c b₀ b₁ : List Sym}
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁)
    (ht : t ≠ BZero) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  rcases h₀ with ⟨e₀, hp₀, hrp₀⟩
  rcases h₁ with ⟨e₁, _, hrp₁⟩
  have hnon := isPTB_str_has_nonRP (hp₀ ht)
  have trail₀ : trailRP (flatBT t) = b₀.length + trailRP c := by
    rw [e₀]
    simpa only [List.append_assoc] using
      trailRP_append (s₀ ++ c) b₀ hrp₀ |>.trans
        (congrArg (b₀.length + ·) (trailRP_prefix s₀ c hnon))
  have trail₁ : trailRP (flatBT t) = b₁.length + trailRP c := by
    rw [e₁]
    simpa only [List.append_assoc] using
      trailRP_append (s₁ ++ c) b₁ hrp₁ |>.trans
        (congrArg (b₁.length + ·) (trailRP_prefix s₁ c hnon))
  have hlen : b₀.length = b₁.length := Nat.add_right_cancel (trail₀.symm.trans trail₁)
  have hb : b₀ = b₁ := allRP_eq_of_length_eq hrp₀ hrp₁ hlen
  have heq : s₀ ++ (c ++ b₀) = s₁ ++ (c ++ b₀) := by
    simpa [List.append_assoc, hb] using e₀.symm.trans e₁
  exact ⟨List.append_cancel_right heq, hb⟩

/-- 固定した中央文字列 `c` を持つ scb 分解では、前置部 `s` と右括弧尾部 `b` が一意。
原文の一意性命題の第 1 主張。 -/
theorem scb_unique_decomp (t : BT) (s₀ s₁ c b₀ b₁ : List Sym)
    (_htb : t ∈ T_B)
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  by_cases ht : t = BZero
  · subst t
    rcases h₀ with ⟨e₀, _, hrp₀⟩
    rcases h₁ with ⟨e₁, _, hrp₁⟩
    have emptyTail (s c b : List Sym)
        (e : flatBT BZero = s ++ c ++ b) (hrp : ∀ x ∈ b, x = .rp) : b = [] := by
      by_contra hb
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b hb
      have hxrp : x = .rp := hrp x hx
      have hxflat : x ∈ flatBT BZero := by
        rw [e]
        simp [hx]
      subst x
      simpa [BZero, flatBT] using hxflat
    have hb₀ := emptyTail s₀ c b₀ e₀ hrp₀
    have hb₁ := emptyTail s₁ c b₁ e₁ hrp₁
    subst b₀
    subst b₁
    simp only [List.append_nil] at e₀ e₁
    exact ⟨List.append_cancel_right (e₀.symm.trans e₁), rfl⟩
  · exact scb_unique_nonzero h₀ h₁ ht

#print axioms scb_unique_decomp

end PSS
