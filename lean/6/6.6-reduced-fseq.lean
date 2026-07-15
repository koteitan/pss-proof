import «6».«6.6-reduced-iff-condAB»
import «6».«6.2-nonmulti-fseq»

/-!
# §6.6 命題（簡約性が基本列で保たれること）

- 原文: `tmp/content.md` の「命題（簡約性が基本列で保たれること）」
- 訂正: なし
- Isabelle: `m_6_6_reduced_oper`
- 依存: `6.6-reduced-iff-condAB`, §6.2 `P` と基本列の関係
- 状態: 🚧 証明中（sorry 0）

The elementary facts and the reduction to the non-multi case are kept public:
they are also the useful interface for the later standardness proof.
-/

namespace PSS

/-- A positive-index fundamental-sequence step remains nonempty. -/
theorem oper_TPS (M : PS) (n : ℕ) (hM : TPS M) (hn : 1 ≤ n) :
    TPS (oper M n) := by
  by_cases hlen : 1 < Lng M
  · exact oper_nonempty_fseq M n hM hlen hn
  · have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
    have hlen1 : Lng M = 1 := by omega
    simpa [oper, hlen1] using hM

/-- In each non-tiling branch, `oper` returns either its input or `Pred`. -/
theorem oper_eq_self_or_Pred_of_nontiling (M : PS) (n : ℕ)
    (h : Lng M - 1 = 0 ∨
      (entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∨
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false) :
    oper M n = M ∨ oper M n = Pred M := by
  rcases h with hlast | hzero | hparent
  · exact Or.inl (by simp [oper, hlast])
  · by_cases hlast : Lng M - 1 = 0
    · exact Or.inl (by simp [oper, hlast])
    · exact Or.inr (by simp [oper, hlast, hzero])
  · by_cases hlast : Lng M - 1 = 0
    · exact Or.inl (by simp [oper, hlast])
    · by_cases hzero :
        entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0
      · exact Or.inr (by simp [oper, hlast, hzero])
      · exact Or.inr (by simp [oper, hlast, hzero, hparent])

/-- `RedCondA` is preserved by the three non-tiling branches of `oper`. -/
theorem RedCondA_oper_nontiling (M : PS) (n : ℕ) (hM : TPS M)
    (hA : RedCondA M = true)
    (h : Lng M - 1 = 0 ∨
      (entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∨
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false) :
    RedCondA (oper M n) = true := by
  rcases oper_eq_self_or_Pred_of_nontiling M n h with hop | hop
  · simpa [hop] using hA
  · simpa [hop] using RedCondA_Pred M hM hA

/-- `RedCondB` is preserved by the three non-tiling branches of `oper`. -/
theorem RedCondB_oper_nontiling (M : PS) (n : ℕ) (hM : TPS M)
    (hB : RedCondB M = true)
    (h : Lng M - 1 = 0 ∨
      (entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∨
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false) :
    RedCondB (oper M n) = true := by
  rcases oper_eq_self_or_Pred_of_nontiling M n h with hop | hop
  · simpa [hop] using hB
  · simpa [hop] using RedCondB_Pred M hM hB

private theorem length_flatMap_range_const_rf {α : Type}
    (f : ℕ → List α) (n w : ℕ)
    (hlen : ∀ k, k < n → (f k).length = w) :
    ((List.range n).flatMap f).length = n * w := by
  rw [List.length_flatMap]
  have hmap : (List.range n).map (fun k => (f k).length) =
      List.replicate n w := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      have hk : k < n := by simpa using hk₁
      simp [hlen k hk]
  rw [hmap]
  simp

private theorem getElem_flatMap_range_const_rf {α : Type}
    (f : ℕ → List α) (n w q s : ℕ)
    (hlen : ∀ k, k < n → (f k).length = w)
    (hq : q < n) (hs : s < w) :
    ((List.range n).flatMap f)[q * w + s]? = (f q)[s]? := by
  induction n with
  | zero => omega
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      by_cases hqm : q < m
      · have hidx : q * w + s < m * w := by
          calc
            q * w + s < q * w + w := Nat.add_lt_add_left hs _
            _ = (q + 1) * w := by rw [Nat.add_mul]; simp
            _ ≤ m * w := Nat.mul_le_mul_right w (by omega)
        rw [List.getElem?_append_left]
        · exact ih (fun k hk => hlen k (by omega)) hqm
        · rw [length_flatMap_range_const_rf f m w
            (fun k hk => hlen k (by omega))]
          exact hidx
      · have hqeq : q = m := by omega
        subst q
        rw [List.getElem?_append_right]
        · rw [length_flatMap_range_const_rf f m w
              (fun k hk => hlen k (by omega))]
          simp
        · rw [length_flatMap_range_const_rf f m w
              (fun k hk => hlen k (by omega))]
          exact Nat.le_add_right _ _

/-- Literal expansion of a genuine tiling branch of `oper`. -/
theorem oper_tiling_expand (M : PS) (n : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    oper M n =
      let j₁ := Lng M - 1
      let i₁ := idx1 M j₁
      let j₀ := parent M i₁ j₁
      let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
      let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
      M.take j₀ ++ (List.range n).flatMap (fun k =>
        (List.range' j₀ (j₁ - j₀)).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
  have hj : Lng M - 1 ≠ 0 := by omega
  simp [oper, hj, hzero, hp]

theorem idx1_le_one_rf (M : PS) (j : ℕ) : idx1 M j ≤ 1 := by
  unfold idx1
  split <;> omega

/-- Length of a genuine tiling expansion. -/
theorem length_oper_tiling (M : PS) (n : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    Lng (oper M n) =
      let j₁ := Lng M - 1
      let j₀ := parent M (idx1 M j₁) j₁
      j₀ + n * (j₁ - j₀) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hj₀L : j₀ ≤ Lng M := by omega
  have hexpand : oper M n = M.take j₀ ++
      (List.range n).flatMap (fun k =>
        (List.range' j₀ w).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
    simpa [j₁, i₁, j₀, w, d₀, d₁] using
      oper_tiling_expand M n hlast hzero hp
  change Lng (oper M n) = j₀ + n * w
  rw [hexpand]
  simp only [List.length_append, List.length_take,
    Nat.min_eq_left hj₀L, List.length_flatMap]
  have hmap :
      (List.range n).map (fun k =>
        ((List.range' j₀ w).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))).length) =
        List.replicate n w := by simp
  rw [hmap]
  simp

/-- Entries before the active parent are copied verbatim by a tiling step. -/
theorem entry_oper_tiling_prefix (M : PS) (n i x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hx : x < parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    entry (oper M n) i x = entry M i x := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
  have hexpand : oper M n = M.take j₀ ++
      (List.range n).flatMap (fun k =>
        (List.range' j₀ w).map (fun j =>
          (entry M 0 j + k * d₀, entry M 1 j + k * d₁))) := by
    simpa [j₁, i₁, j₀, w, d₀, d₁] using
      oper_tiling_expand M n hlast hzero hp
  have hx' : x < j₀ := by simpa [j₀, i₁, j₁] using hx
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hxM : x < Lng M := by omega
  unfold entry
  rw [hexpand, List.getElem?_append_left]
  · rw [List.getElem?_take_of_lt hx']
  · simp only [List.length_take]
    exact lt_min hx' hxM

/-- Row-0 reading inside copy `q` of the active tiling block. -/
theorem entry_oper_tiling_block_zero (M : PS) (n q s : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hq : q < n)
    (hs : s < Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    entry (oper M n) 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) =
      entry M 0
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s) +
        q * (if 0 < idx1 M (Lng M - 1) then
          entry M 0 (Lng M - 1) -
            entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
          else 0) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hj₀L : j₀ ≤ Lng M := by omega
  have hs' : s < w := by simpa [w, j₀, i₁, j₁] using hs
  let f : ℕ → PS := fun k =>
    (List.range' j₀ w).map (fun j =>
      (entry M 0 j + k * d₀, entry M 1 j + k * d₁))
  have hflen : ∀ k, k < n → Lng (f k) = w := by simp [f]
  have hread := getElem_flatMap_range_const_rf f n w q s hflen hq hs'
  have hexpand : oper M n = M.take j₀ ++ (List.range n).flatMap f := by
    simpa [j₁, i₁, j₀, w, d₀, d₁, f] using
      oper_tiling_expand M n hlast hzero hp
  change entry (oper M n) 0 (j₀ + q * w + s) =
    entry M 0 (j₀ + s) + q * d₀
  unfold entry
  rw [hexpand, List.getElem?_append_right]
  · simp only [List.length_take, Nat.min_eq_left hj₀L]
    have hsub : j₀ + q * w + s - j₀ = q * w + s := by omega
    rw [hsub]
    rw [hread]
    simp [f, List.getElem?_map, List.getElem?_range' hs']
    rfl
  · simp only [List.length_take, Nat.min_eq_left hj₀L]
    omega

/-- Row 1 is periodic (unshifted) in every active tiling block. -/
theorem entry_oper_tiling_block_one (M : PS) (n q s : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hq : q < n)
    (hs : s < Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    entry (oper M n) 1
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) =
      entry M 1
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
  have hd₁ : d₁ = 0 := by
    dsimp only [d₁]
    rw [if_neg (Nat.not_lt_of_ge (idx1_le_one_rf M j₁))]
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hj₀L : j₀ ≤ Lng M := by omega
  have hs' : s < w := by simpa [w, j₀, i₁, j₁] using hs
  let f : ℕ → PS := fun k =>
    (List.range' j₀ w).map (fun j =>
      (entry M 0 j + k * d₀, entry M 1 j + k * d₁))
  have hflen : ∀ k, k < n → Lng (f k) = w := by simp [f]
  have hread := getElem_flatMap_range_const_rf f n w q s hflen hq hs'
  have hexpand : oper M n = M.take j₀ ++ (List.range n).flatMap f := by
    simpa [j₁, i₁, j₀, w, d₀, d₁, f] using
      oper_tiling_expand M n hlast hzero hp
  change entry (oper M n) 1 (j₀ + q * w + s) = entry M 1 (j₀ + s)
  unfold entry
  rw [hexpand, List.getElem?_append_right]
  · simp only [List.length_take, Nat.min_eq_left hj₀L]
    have hsub : j₀ + q * w + s - j₀ = q * w + s := by omega
    rw [hsub]
    rw [hread]
    simp [f, List.getElem?_map, List.getElem?_range' hs', hd₁]
    rfl
  · simp only [List.length_take, Nat.min_eq_left hj₀L]
    omega

/-- A valid row-0 column is parentless exactly when it is a weak running
minimum of row 0. -/
theorem hasParent_row0_false_iff_lmin (M : PS) (k : ℕ) (hM : TPS M)
    (hk : k < Lng M) :
    hasParent M 0 k = false ↔
      ∀ j, j < k → entry M 0 k ≤ entry M 0 j := by
  have hexiff : (∃! j₀, nextR M 0 j₀ k = true) ↔
      ∃ j₀, nextR M 0 j₀ k = true := by
    constructor
    · rintro ⟨j, hj, _⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, hj, fun y hy => row0_parent_unique M y j k hy hj⟩
  have hfalse : hasParent M 0 k = false ↔
      ¬ ∃! j₀, nextR M 0 j₀ k = true := by
    constructor
    · intro hf hu
      have ht := (hasParent_iff_unique_fseq M 0 k).mpr hu
      simp [hf] at ht
    · intro hn
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hn ((hasParent_iff_unique_fseq M 0 k).mp ht)
  rw [hfalse, hexiff]
  constructor
  · intro hno j hj
    by_contra hnot
    have hlt : entry M 0 j < entry M 0 k := by omega
    obtain ⟨p, _, _, hp⟩ := parent_exists_1 M j k hM hj hk hlt
    exact hno ⟨p, hp⟩
  · intro hmin ⟨p, hp⟩
    have hp0 : nextrel0 M p k = true := by simpa [nextR] using hp
    have hh := hp0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hreverse := hmin p hh.1.1.2
    omega

/-- `RedCondB` is preserved by a genuine tiling branch of `oper`. -/
theorem RedCondB_oper_tiling (M : PS) (n : ℕ) (hM : TPS M)
    (hB : RedCondB M = true) (hn : 1 ≤ n)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    RedCondB (oper M n) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let N := oper M n
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hwpos : 0 < w := by simp [w]; omega
  have hNL : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hNT : TPS N := by simpa [N] using oper_TPS M n hM hn
  have hNpos : 0 < Lng N := List.length_pos_of_ne_nil hNT
  have hpfx : ∀ i x, x < j₀ → entry N i x = entry M i x := by
    intro i x hx
    simpa [N, j₁, i₁, j₀] using
      entry_oper_tiling_prefix M n i x hlast hzero hp
        (by simpa [j₁, i₁, j₀] using hx)
  have hblk0 : ∀ q s, q < n → s < w →
      entry N 0 (j₀ + q * w + s) =
        entry M 0 (j₀ + s) + q * d₀ := by
    intro q s hq hs
    simpa [N, j₁, i₁, j₀, w, d₀] using
      entry_oper_tiling_block_zero M n q s hlast hzero hp hq
        (by simpa [j₁, i₁, j₀, w] using hs)
  have hblk1 : ∀ q s, q < n → s < w →
      entry N 1 (j₀ + q * w + s) = entry M 1 (j₀ + s) := by
    intro q s hq hs
    simpa [N, j₁, i₁, j₀, w] using
      entry_oper_tiling_block_one M n q s hlast hzero hp hq
        (by simpa [j₁, i₁, j₀, w] using hs)
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro x hx
  have hxN : x < Lng N := by rw [hNL] at hNpos hx ⊢; omega
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  change hasParent N 0 x = true ∨ entry N 0 x = entry N 1 x
  by_cases hpx : hasParent N 0 x = true
  · exact Or.inl hpx
  · have hpxf : hasParent N 0 x = false := Bool.eq_false_of_not_eq_true hpx
    apply Or.inr
    have hrmin := (hasParent_row0_false_iff_lmin N x hNT hxN).mp hpxf
    by_cases hxpre : x < j₀
    · have hrminM : ∀ y, y < x → entry M 0 x ≤ entry M 0 y := by
        intro y hy
        rw [← hpfx 0 x hxpre, ← hpfx 0 y (by omega)]
        exact hrmin y hy
      have hxM : x < Lng M := by omega
      have hnoM := (hasParent_row0_false_iff_lmin M x hM hxM).mpr hrminM
      have heq := RedCondB_apply M hM hB x hxM hnoM
      simpa [hpfx 0 x hxpre, hpfx 1 x hxpre] using heq
    · have hxge : j₀ ≤ x := by omega
      let q := (x - j₀) / w
      let s := (x - j₀) % w
      have hs : s < w := Nat.mod_lt _ hwpos
      have hxdecomp : x = j₀ + q * w + s := by
        calc
          x = j₀ + (x - j₀) := by omega
          _ = j₀ + (w * ((x - j₀) / w) + (x - j₀) % w) := by
            rw [Nat.div_add_mod]
          _ = j₀ + q * w + s := by
            simp [q, s, Nat.mul_comm, Nat.add_assoc]
      have hq : q < n := by
        change (x - j₀) / w < n
        rw [Nat.div_lt_iff_lt_mul hwpos]
        have hxbound : x < j₀ + n * w := by rw [← hNL]; exact hxN
        have hxsub : x - j₀ < n * w := by omega
        simpa [Nat.mul_comm] using hxsub
      let u := j₀ + s
      have huM : u < Lng M := by simp [u]; omega
      have huN : u < Lng N := by
        rw [hNL]
        have hnpos : 0 < n * w := Nat.mul_pos hn hwpos
        simp [u]
        omega
      have hux : u ≤ x := by rw [hxdecomp]; simp [u]
      have huxeq : entry N 0 x = entry M 0 u := by
        have hxread := hblk0 q s hq hs
        rw [← hxdecomp] at hxread
        have hqd : q * d₀ = 0 := by
          by_cases hqzero : q = 0
          · simp [hqzero]
          · have hqwpos : 0 < q * w := Nat.mul_pos (Nat.pos_of_ne_zero hqzero) hwpos
            have hult : u < x := by
              rw [hxdecomp]
              dsimp only [u]
              omega
            have hle := hrmin u hult
            have huread : entry N 0 u = entry M 0 u := by
              simpa [u] using hblk0 0 s hn hs
            have hle' : entry M 0 u + q * d₀ ≤ entry M 0 u := by
              simpa [hxread, huread, u] using hle
            apply Nat.add_left_cancel (n := entry M 0 u)
            apply Nat.le_antisymm
            · simpa using hle'
            · exact Nat.add_le_add_left (Nat.zero_le _) _
        simpa [u, hqd] using hxread
      have hrminM : ∀ y, y < u → entry M 0 u ≤ entry M 0 y := by
        intro y hy
        have hyx : y < x := lt_of_lt_of_le hy hux
        have hminy := hrmin y hyx
        rw [huxeq] at hminy
        by_cases hypre : y < j₀
        · simpa [hpfx 0 y hypre] using hminy
        · let t := y - j₀
          have hyge : j₀ ≤ y := by omega
          have ht : t < w := by simp [t, u] at hy ⊢; omega
          have hyform : y = j₀ + 0 * w + t := by simp [t]; omega
          have hyread := hblk0 0 t hn ht
          rw [← hyform] at hyread
          have hyEq : entry N 0 y = entry M 0 y := by
            simpa [t, Nat.add_sub_of_le hyge] using hyread
          rw [hyEq] at hminy
          exact hminy
      have hnoM := (hasParent_row0_false_iff_lmin M u hM huM).mpr hrminM
      have heq := RedCondB_apply M hM hB u huM hnoM
      have hx1 := hblk1 q s hq hs
      rw [← hxdecomp] at hx1
      calc
        entry N 0 x = entry M 0 u := huxeq
        _ = entry M 1 u := heq
        _ = entry N 1 x := by simpa [u] using hx1.symm

private theorem P_getLastD_mem_rf (M : PS) :
    (P M).getLastD [] ∈ P M := by
  have hne := P_nonempty M
  cases hPM : P M with
  | nil => exact (hne hPM).elim
  | cons A Q => simp [List.getLastD]

private theorem RTPS_P_member_rf (M Q : PS) (hM : TPS M)
    (hR : RTPS M) (hQ : Q ∈ P M) : RTPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hcomp := (RTPS_iff_P_components M hM).mp hR J hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hcomp
  exact hcomp

/-- To prove preservation for all reduced sequences, it suffices to prove it
for non-multi reduced sequences.  The `P` equations reduce a multi input to
its unchanged leading components and one non-multi final component. -/
theorem RTPS_oper_of_nonmulti_steps
    (step : ∀ Q n, TPS Q → RTPS Q → multiT Q = false →
      1 ≤ n → RTPS (oper Q n))
    (M : PS) (n : ℕ) (hR : RTPS M) (hn : 1 ≤ n) :
    RTPS (oper M n) := by
  have hM : TPS M := RTPS_TPS M hR
  by_cases hmulti : multiT M = true
  · have hPlen : 1 < (P M).length :=
      (P_components_multi_iff M hM).mp hmulti
    let D := (P M).getLastD []
    have hDmem : D ∈ P M := by
      simpa [D] using P_getLastD_mem_rf M
    have hDR : RTPS D := RTPS_P_member_rf M D hM hR hDmem
    have hDT : TPS D := RTPS_TPS D hDR
    have hDpos : 0 < Lng D := List.length_pos_of_ne_nil hDT
    have hDnm : multiT D = false := by
      rcases P_components_nonmulti M hM D hDmem with hz | hmono
      · simp [multiT, hz]
      · simp [multiT, hmono]
    have hDoperR : RTPS (oper D n) := step D n hDT hDR hDnm hn
    by_cases hDone : Lng D = 1
    · have hrel := P_fseq_1 M n hM hn (by simpa [D] using hDone)
      rw [hrel.1]
      exact RTPS_Pred M hR
    · have hDgt : 1 < Lng D := by omega
      have hrel := P_fseq_2 M n hM hn (by simpa [D] using hDgt)
      have hP : P (oper M n) = (P M).dropLast ++ P (oper D n) := by
        simpa [D] using hrel.2
      have hoperT : TPS (oper M n) := oper_TPS M n hM hn
      apply (RTPS_iff_P_components (oper M n) hoperT).mpr
      intro J hJ
      let Q := (P (oper M n)).getD J []
      have hQmem : Q ∈ P (oper M n) := by
        change (P (oper M n)).getD J [] ∈ P (oper M n)
        rw [getD_eq_getElem_idx (P (oper M n)) [] hJ]
        exact List.getElem_mem hJ
      have hQsplit : Q ∈ (P M).dropLast ++ P (oper D n) := by
        simpa only [hP] using hQmem
      rcases List.mem_append.mp hQsplit with hQlead | hQtail
      · exact RTPS_P_member_rf M Q hM hR
          (List.mem_of_mem_dropLast hQlead)
      · exact RTPS_P_member_rf (oper D n) Q (oper_TPS D n hDT hn)
          hDoperR hQtail
  · exact step M n hM hR (Bool.eq_false_of_not_eq_true hmulti) hn

#print axioms oper_TPS
#print axioms oper_eq_self_or_Pred_of_nontiling
#print axioms RedCondA_oper_nontiling
#print axioms RedCondB_oper_nontiling
#print axioms RedCondB_oper_tiling
#print axioms RTPS_oper_of_nonmulti_steps

end PSS
