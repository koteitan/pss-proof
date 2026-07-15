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

/-- The whole prefix before the active parent is copied as a list. -/
theorem take_oper_tiling_prefix (M : PS) (n : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    (oper M n).take
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) =
      M.take (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) := by
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
  change (oper M n).take j₀ = M.take j₀
  rw [hexpand]
  simp [Nat.min_eq_left hj₀L]

/-- Parent existence is unchanged on the copied prefix. -/
theorem hasParent_oper_tiling_prefix (M : PS) (n i x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hx : x < parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    hasParent (oper M n) i x = hasParent M i x := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hj₀M : j₀ ≤ Lng M := by omega
  have hNlen : Lng (oper M n) = j₀ + n * w := by
    simpa [j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hj₀N : j₀ ≤ Lng (oper M n) := by rw [hNlen]; omega
  have hx' : x < j₀ := by simpa [j₀, i₁, j₁] using hx
  rw [← hasParent_take_of_lt (oper M n) j₀ i x hj₀N hx',
    take_oper_tiling_prefix M n hlast hzero hp,
    hasParent_take_of_lt M j₀ i x hj₀M hx']

private theorem nextR_oper_tiling_prefix_rf (M : PS) (n i a x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (ha : a < parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hx : x < parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    nextR (oper M n) i a x = nextR M i a x := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnext).1
  have hj₀M : j₀ ≤ Lng M := by omega
  have hNlen : Lng (oper M n) = j₀ + n * w := by
    simpa [j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hj₀N : j₀ ≤ Lng (oper M n) := by rw [hNlen]; omega
  have ha' : a < j₀ := by simpa [j₀, i₁, j₁] using ha
  have hx' : x < j₀ := by simpa [j₀, i₁, j₁] using hx
  calc
    nextR (oper M n) i a x =
        nextR ((oper M n).take j₀) i a x := by
      symm
      exact nextR_take_adm (oper M n) j₀ i a x hj₀N ha' hx'
    _ = nextR (M.take j₀) i a x := by
      rw [take_oper_tiling_prefix M n hlast hzero hp]
    _ = nextR M i a x :=
      nextR_take_adm M j₀ i a x hj₀M ha' hx'

/-- The selected parent itself is unchanged on the copied prefix. -/
theorem parent_oper_tiling_prefix (M : PS) (n i x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hx : x < parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hpx : hasParent (oper M n) i x = true) :
    parent (oper M n) i x = parent M i x := by
  let N := oper M n
  have hpxM : hasParent M i x = true := by
    simpa [N, hasParent_oper_tiling_prefix M n i x hlast hzero hp hx] using hpx
  have hnextN := hasParent_next_fseq N i x (by simpa [N] using hpx)
  have hpNlt : parent N i x < x :=
    (nextR_implies_row0 N i (parent N i x) x hnextN).1
  have hpNpre : parent N i x <
      parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by omega
  have hnextM : nextR M i (parent N i x) x = true := by
    simpa [N, nextR_oper_tiling_prefix_rf M n i (parent N i x) x
      hlast hzero hp hpNpre hx] using hnextN
  obtain ⟨p, hpM, huniqM⟩ := (hasParent_iff_unique_fseq M i x).mp hpxM
  have heq : parent N i x = p := huniqM _ hnextM
  have hparM := parent_eq_of_unique_fseq M i x p hpM huniqM
  exact heq.trans hparM.symm

/-- Condition (A) transfers without change on the copied prefix. -/
theorem RedCondA_oper_tiling_prefix (M : PS) (n i x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hA : RedCondA M = true)
    (hi : i < 2)
    (hx : x < parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hpx : hasParent (oper M n) i x = true) :
    entry (oper M n) i (parent (oper M n) i x) + 1 =
      entry (oper M n) i x := by
  have hpar := parent_oper_tiling_prefix M n i x hlast hzero hp hx hpx
  have hpxM : hasParent M i x = true := by
    simpa [hasParent_oper_tiling_prefix M n i x hlast hzero hp hx] using hpx
  have hbase := RedCondA_apply M hA i x hi (by
    have hparentTop := hasParent_next_fseq M
      (idx1 M (Lng M - 1)) (Lng M - 1) hp
    have hj₀lt := (nextR_implies_row0 M _ _ _ hparentTop).1
    omega) hpxM
  have hparentlt : parent M i x <
      parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
    have hnext := hasParent_next_fseq M i x hpxM
    have := (nextR_implies_row0 M i (parent M i x) x hnext).1
    omega
  rw [hpar,
    entry_oper_tiling_prefix M n i (parent M i x) hlast hzero hp hparentlt,
    entry_oper_tiling_prefix M n i x hlast hzero hp hx]
  exact hbase

/-- Inside the active slice, every positive offset lies strictly above its
row-0 floor at the active parent. -/
theorem oper_tiling_strict_floor (M : PS) (s : ℕ)
    (hM : TPS M)
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hspos : 0 < s)
    (hsle : s ≤ Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :
    entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) <
      entry M 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  have hnext := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hanc := (nextR_implies_row0 M i₁ j₀ j₁ hnext).2
  apply ancestor_basic_1 M j₀ (j₀ + s) j₁ hM
  · omega
  · have hsle' : s ≤ j₁ - j₀ := by
      simpa [j₁, i₁, j₀] using hsle
    omega
  · exact hanc

/-- Every row-0 entry in the tiled suffix lies above the active slice floor. -/
theorem oper_tiling_block_floor (M : PS) (n y : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hyge : parent M (idx1 M (Lng M - 1)) (Lng M - 1) ≤ y)
    (hylt : y < Lng (oper M n)) :
    entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) ≤
      entry (oper M n) 0 y := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let k := (y - j₀) / w
  let s := (y - j₀) % w
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hlen : Lng (oper M n) = j₀ + n * w := by
    simpa [j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hyge' : j₀ ≤ y := by simpa [j₁, i₁, j₀] using hyge
  have hdelta : y - j₀ < n * w := by rw [hlen] at hylt; omega
  have hk : k < n := by
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hdelta
  have hs : s < w := by
    exact Nat.mod_lt _ hwpos
  have hdiv : k * w + s = y - j₀ := by
    simpa [k, s, Nat.mul_comm] using (Nat.div_add_mod (y - j₀) w)
  have hyform : y = j₀ + k * w + s := by omega
  have hread : entry (oper M n) 0 y =
      entry M 0 (j₀ + s) + k * d₀ := by
    rw [hyform]
    simpa [j₁, i₁, j₀, w, d₀, Nat.add_assoc] using
      entry_oper_tiling_block_zero M n k s hlast hzero hp hk hs
  have hfloor : entry M 0 j₀ ≤ entry M 0 (j₀ + s) := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      have hstrict : entry M 0 j₀ < entry M 0 (j₀ + s) := by
        simpa [j₁, i₁, j₀, w] using
          oper_tiling_strict_floor M s hM hp hspos hs.le
      exact hstrict.le
  have hresult : entry M 0 j₀ ≤ entry (oper M n) 0 y := by
    rw [hread]
    omega
  simpa [j₁, i₁, j₀] using hresult

/-- Row-0 condition (A) for a nonzero offset inside a tiling block. -/
theorem RedCondA_oper_tiling_row0_interior (M : PS) (n q s : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hA : RedCondA M = true)
    (hq : q < n) (hspos : 0 < s)
    (hs : s < Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hpx : hasParent (oper M n) 0
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
        q * (Lng M - 1 -
          parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) = true) :
    entry (oper M n) 0
        (parent (oper M n) 0
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
            q * (Lng M - 1 -
              parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)) + 1 =
      entry (oper M n) 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let N := oper M n
  let B := j₀ + q * w
  let x := B + s
  let u := j₀ + s
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [w, j₀, i₁, j₁] using hs
  have hq' : q < n := hq
  have hblk : ∀ t, t < w →
      entry N 0 (B + t) = entry M 0 (j₀ + t) + q * d₀ := by
    intro t ht
    simpa [N, B, j₁, i₁, j₀, w, d₀, Nat.add_assoc] using
      entry_oper_tiling_block_zero M n q t hlast hzero hp hq' ht
  have hxread : entry N 0 x = entry M 0 u + q * d₀ := by
    simpa [x, u] using hblk s hs'
  have hBread : entry N 0 B = entry M 0 j₀ + q * d₀ := by
    simpa using hblk 0 hwpos
  have hfloor : entry M 0 j₀ < entry M 0 u := by
    simpa [j₁, i₁, j₀, u, w] using
      oper_tiling_strict_floor M s hM hp hspos hs'.le
  have hBlt : entry N 0 B < entry N 0 x := by
    rw [hBread, hxread]
    omega
  have hpx' : hasParent N 0 x = true := by
    simpa [N, x, B, j₁, i₁, j₀, w, Nat.add_assoc] using hpx
  let p := parent N 0 x
  have hpstep : nextR N 0 p x = true := hasParent_next_fseq N 0 x hpx'
  have hpstep0 : nextrel0 N p x = true := by simpa [nextR] using hpstep
  have hpdata := hpstep0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpdata
  have hpxlt : p < x := hpdata.1.1.2
  have hvalley : ∀ z, p < z → z < x → entry N 0 x ≤ entry N 0 z := by
    intro z hpz hzx
    have hz := hpdata.2 z (List.mem_range.mpr hzx)
    simpa [hpz] using hz
  have hBp : B ≤ p := by
    by_contra hnot
    have hpB : p < B := by omega
    have hBx : B < x := by simp [x]; omega
    have := hvalley B hpB hBx
    omega
  let t := p - B
  have htS : t < s := by simp [t]; omega
  have htw : t < w := htS.trans hs'
  have hpform : p = B + t := by simp [t, Nat.add_sub_of_le hBp]
  have hpread : entry N 0 p = entry M 0 (j₀ + t) + q * d₀ := by
    rw [hpform]
    exact hblk t htw
  let p₀ := j₀ + t
  have hp₀u : p₀ < u := by simp [p₀, u]; omega
  have hp₀M : p₀ < Lng M := by simp [p₀]; omega
  have huM : u < Lng M := by simp [u]; omega
  have hstepM0 : nextrel0 M p₀ u = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hp₀M, huM⟩, hp₀u⟩, ?_⟩, ?_⟩
    · have hstrict := hpdata.1.2
      rw [hpread, hxread] at hstrict
      dsimp only [p₀]
      omega
    · intro z hzu
      by_cases hpz : p₀ < z
      · simp only [hpz, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq]
        have hzge : j₀ ≤ z := by simp [p₀] at hpz; omega
        let r := z - j₀
        have hrw : r < w := by simp [r, u] at hzu ⊢; omega
        have hzform : z = j₀ + r := by simp [r, Nat.add_sub_of_le hzge]
        have hpr : t < r := by simp [p₀] at hpz; omega
        have hrS : r < s := by simp [u] at hzu; omega
        have hBlock : p < B + r := by rw [hpform]; omega
        have hBlockX : B + r < x := by simp [x]; omega
        have hmin := hvalley (B + r) hBlock hBlockX
        have hreadr := hblk r hrw
        rw [hxread, hreadr] at hmin
        rw [hzform]
        omega
      · have hpz' : ¬p₀ < z := hpz
        simp [hpz']
  have hstepM : nextR M 0 p₀ u = true := by simpa [nextR] using hstepM0
  have hpMu : hasParent M 0 u = true :=
    (hasParent_iff_unique_fseq M 0 u).mpr
      ⟨p₀, hstepM, fun y hy => row0_parent_unique M y p₀ u hy hstepM⟩
  have hparM : parent M 0 u = p₀ :=
    parent_eq_of_unique_fseq M 0 u p₀ hstepM
      (fun y hy => row0_parent_unique M y p₀ u hy hstepM)
  have hbase := RedCondA_apply M hA 0 u (by omega) huM hpMu
  have hparN : parent N 0 x = p := rfl
  change entry N 0 (parent N 0 x) + 1 = entry N 0 x
  rw [hparM] at hbase
  dsimp only [p₀] at hbase
  rw [hparN, hpread, hxread]
  omega

/-- Row-0 condition (A) at the first start of the active tiling block. -/
theorem RedCondA_oper_tiling_row0_blockstart (M : PS) (n : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hA : RedCondA M = true)
    (hn : 1 ≤ n)
    (hpx : hasParent (oper M n) 0
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) = true) :
    entry (oper M n) 0
        (parent (oper M n) 0
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1))) + 1 =
      entry (oper M n) 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hj₀M : j₀ < Lng M := by omega
  have hj₀read : entry N 0 j₀ = entry M 0 j₀ := by
    simpa [N, j₁, i₁, j₀, w] using
      entry_oper_tiling_block_zero M n 0 0 hlast hzero hp
        (by omega) hwpos
  have hpx' : hasParent N 0 j₀ = true := by
    simpa [N, j₁, i₁, j₀] using hpx
  let p := parent N 0 j₀
  have hpstep : nextR N 0 p j₀ = true :=
    hasParent_next_fseq N 0 j₀ hpx'
  have hpstep0 : nextrel0 N p j₀ = true := by
    simpa [nextR] using hpstep
  have hpdata := hpstep0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpdata
  have hpj₀ : p < j₀ := hpdata.1.1.2
  have hpM : p < Lng M := hpj₀.trans hj₀M
  have hpread : entry N 0 p = entry M 0 p := by
    simpa [N, j₁, i₁, j₀] using
      entry_oper_tiling_prefix M n 0 p hlast hzero hp (by
        simpa [j₁, i₁, j₀] using hpj₀)
  have hstepM0 : nextrel0 M p j₀ = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hpM, hj₀M⟩, hpj₀⟩, ?_⟩, ?_⟩
    · rw [← hpread, ← hj₀read]
      exact hpdata.1.2
    · intro z hzj₀
      by_cases hpz : p < z
      · simp only [hpz, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq]
        have hvalley := hpdata.2 z (List.mem_range.mpr hzj₀)
        have hzpre : z < parent M
            (idx1 M (Lng M - 1)) (Lng M - 1) := by
          simpa [j₁, i₁, j₀] using hzj₀
        rw [hj₀read,
          entry_oper_tiling_prefix M n 0 z hlast hzero hp hzpre]
          at hvalley
        simpa [hpz] using hvalley
      · simp [hpz]
  have hstepM : nextR M 0 p j₀ = true := by
    simpa [nextR] using hstepM0
  have hpMj₀ : hasParent M 0 j₀ = true :=
    (hasParent_iff_unique_fseq M 0 j₀).mpr
      ⟨p, hstepM, fun y hy => row0_parent_unique M y p j₀ hy hstepM⟩
  have hparM : parent M 0 j₀ = p :=
    parent_eq_of_unique_fseq M 0 j₀ p hstepM
      (fun y hy => row0_parent_unique M y p j₀ hy hstepM)
  have hbase := RedCondA_apply M hA 0 j₀ (by omega) hj₀M hpMj₀
  rw [hparM] at hbase
  change entry N 0 (parent N 0 j₀) + 1 = entry N 0 j₀
  change entry N 0 p + 1 = entry N 0 j₀
  rw [hpread, hj₀read]
  exact hbase

/-- Row-0 condition (A) at a later block boundary when the active parent is
in row zero.  In this case the row-zero tiling shift is zero. -/
theorem RedCondA_oper_tiling_row0_boundary_zero (M : PS) (n q : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hA : RedCondA M = true)
    (hqpos : 1 ≤ q) (hq : q < n)
    (hpx : hasParent (oper M n) 0
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
        q * (Lng M - 1 -
          parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = true) :
    entry (oper M n) 0
        (parent (oper M n) 0
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
            q * (Lng M - 1 -
              parent M (idx1 M (Lng M - 1)) (Lng M - 1)))) + 1 =
      entry (oper M n) 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1))) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let x := j₀ + q * w
  have hi₁' : i₁ = 0 := by simpa [i₁, j₁] using hi₁
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hj₀M : j₀ < Lng M := by omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hxlt : x < Lng N := by
    rw [hlen]
    simp [x]
    nlinarith
  have hj₀x : j₀ < x := by
    have : 0 < q * w := Nat.mul_pos (by omega) hwpos
    simp [x]
    omega
  have hxread : entry N 0 x = entry M 0 j₀ := by
    simpa [N, x, j₁, i₁, j₀, w, hi₁'] using
      entry_oper_tiling_block_zero M n q 0 hlast hzero hp hq hwpos
  have hpx' : hasParent N 0 x = true := by
    simpa [N, x, j₁, i₁, j₀, w, Nat.add_assoc] using hpx
  let p := parent N 0 x
  have hpstep : nextR N 0 p x = true := hasParent_next_fseq N 0 x hpx'
  have hpstep0 : nextrel0 N p x = true := by simpa [nextR] using hpstep
  have hpdata := hpstep0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpdata
  have hpxlt : p < x := hpdata.1.1.2
  have hpN : p < Lng N := hpxlt.trans hxlt
  have hpj₀ : p < j₀ := by
    by_contra hnot
    have hj₀p : j₀ ≤ p := by omega
    have hfloor := oper_tiling_block_floor M n p hM hlast hzero hp
      (by simpa [j₁, i₁, j₀] using hj₀p) hpN
    have hfloor' : entry M 0 j₀ ≤ entry N 0 p := by
      simpa [N, j₁, i₁, j₀] using hfloor
    have hstrict := hpdata.1.2
    rw [hxread] at hstrict
    omega
  have hpM : p < Lng M := hpj₀.trans hj₀M
  have hpread : entry N 0 p = entry M 0 p := by
    simpa [N, j₁, i₁, j₀] using
      entry_oper_tiling_prefix M n 0 p hlast hzero hp (by
        simpa [j₁, i₁, j₀] using hpj₀)
  have hstepM0 : nextrel0 M p j₀ = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hpM, hj₀M⟩, hpj₀⟩, ?_⟩, ?_⟩
    · rw [← hpread, ← hxread]
      exact hpdata.1.2
    · intro z hzj₀
      by_cases hpz : p < z
      · simp only [hpz, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq]
        have hzx : z < x := hzj₀.trans hj₀x
        have hvalley := hpdata.2 z (List.mem_range.mpr hzx)
        have hzpre : z < parent M
            (idx1 M (Lng M - 1)) (Lng M - 1) := by
          simpa [j₁, i₁, j₀] using hzj₀
        rw [hxread,
          entry_oper_tiling_prefix M n 0 z hlast hzero hp hzpre]
          at hvalley
        simpa [hpz] using hvalley
      · simp [hpz]
  have hstepM : nextR M 0 p j₀ = true := by
    simpa [nextR] using hstepM0
  have hpMj₀ : hasParent M 0 j₀ = true :=
    (hasParent_iff_unique_fseq M 0 j₀).mpr
      ⟨p, hstepM, fun y hy => row0_parent_unique M y p j₀ hy hstepM⟩
  have hparM : parent M 0 j₀ = p :=
    parent_eq_of_unique_fseq M 0 j₀ p hstepM
      (fun y hy => row0_parent_unique M y p j₀ hy hstepM)
  have hbase := RedCondA_apply M hA 0 j₀ (by omega) hj₀M hpMj₀
  rw [hparM] at hbase
  change entry N 0 (parent N 0 x) + 1 = entry N 0 x
  change entry N 0 p + 1 = entry N 0 x
  rw [hpread, hxread]
  exact hbase

/-- Row-0 condition (A) at a later block boundary when the active parent is
in row one.  The parent edge is the previous-block image of the base row-zero
parent of the final column. -/
theorem RedCondA_oper_tiling_row0_boundary_one (M : PS) (n q : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hA : RedCondA M = true)
    (hqpos : 1 ≤ q) (hq : q < n)
    (hpx : hasParent (oper M n) 0
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
        q * (Lng M - 1 -
          parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = true) :
    entry (oper M n) 0
        (parent (oper M n) 0
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
            q * (Lng M - 1 -
              parent M (idx1 M (Lng M - 1)) (Lng M - 1)))) + 1 =
      entry (oper M n) 0
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1))) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := entry M 0 j₁ - entry M 0 j₀
  let N := oper M n
  let x := j₀ + q * w
  let qm := q - 1
  have hi₁' : i₁ = 1 := by simpa [i₁, j₁] using hi₁
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hj₀w : j₀ + w = j₁ := by simp [w]; omega
  have hj₁M : j₁ < Lng M := by simp [j₁]; omega
  have hfloor : entry M 0 j₀ < entry M 0 j₁ := by
    have hf := oper_tiling_strict_floor M w hM hp hwpos (by
      simp [w, j₁, i₁, j₀])
    rw [hj₀w] at hf
    exact hf
  have hdpos : 0 < d₀ := by simp [d₀]; omega
  have hfloorid : entry M 0 j₀ + d₀ = entry M 0 j₁ := by
    simp [d₀]
    omega
  have hp0 : hasParent M 0 j₁ = true := by
    cases hpar : hasParent M 0 j₁ with
    | true => rfl
    | false =>
        have hmin := (hasParent_row0_false_iff_lmin M j₁ hM hj₁M).mp hpar
        have := hmin j₀ hj₀lt
        omega
  let p₀ := parent M 0 j₁
  have hp₀step : nextR M 0 p₀ j₁ = true :=
    hasParent_next_fseq M 0 j₁ hp0
  have hp₀step0 : nextrel0 M p₀ j₁ = true := by
    simpa [nextR] using hp₀step
  have hp₀data := hp₀step0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hp₀data
  have hp₀j₁ : p₀ < j₁ := hp₀data.1.1.2
  have hj₀p₀ : j₀ ≤ p₀ := by
    by_contra hnot
    have hp₀j₀ : p₀ < j₀ := by omega
    have hvalley := hp₀data.2 j₀ (List.mem_range.mpr hj₀lt)
    have hle : entry M 0 j₁ ≤ entry M 0 j₀ := by
      simpa [hp₀j₀] using hvalley
    omega
  let r := p₀ - j₀
  have hrw : r < w := by simp [r, w]; omega
  have hp₀form : p₀ = j₀ + r := by
    simp [r, Nat.add_sub_of_le hj₀p₀]
  let P := j₀ + qm * w + r
  have hqm : qm < n := by simp [qm]; omega
  have hqeq : q = qm + 1 := by simp [qm]; omega
  have hqmulw : q * w = qm * w + w := by
    rw [hqeq, Nat.add_mul]
    simp
  have hqmuld : q * d₀ = qm * d₀ + d₀ := by
    rw [hqeq, Nat.add_mul]
    simp
  have hqshift : entry M 0 j₁ + qm * d₀ =
      entry M 0 j₀ + q * d₀ := by
    rw [hqmuld]
    omega
  have hblk : ∀ k t, k < n → t < w →
      entry N 0 (j₀ + k * w + t) =
        entry M 0 (j₀ + t) + k * d₀ := by
    intro k t hk ht
    simpa [N, j₁, i₁, j₀, w, d₀, hi₁', Nat.add_assoc] using
      entry_oper_tiling_block_zero M n k t hlast hzero hp hk ht
  have hxread : entry N 0 x = entry M 0 j₀ + q * d₀ := by
    simpa [x] using hblk q 0 hq hwpos
  have hPread : entry N 0 P = entry M 0 p₀ + qm * d₀ := by
    have hr := hblk qm r hqm hrw
    rw [hp₀form]
    simpa [P, Nat.add_assoc] using hr
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hxlt : x < Lng N := by
    rw [hlen]
    simp [x]
    nlinarith
  have hxform : x = j₀ + qm * w + w := by
    simp [x, hqmulw, Nat.add_assoc]
  have hPx : P < x := by
    rw [hxform]
    simp [P]
    omega
  have hPlt : P < Lng N := hPx.trans hxlt
  have hnextN0 : nextrel0 N P x = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨hPlt, hxlt⟩, hPx⟩, ?_⟩, ?_⟩
    · have hstrict := hp₀data.1.2
      rw [hPread, hxread]
      omega
    · intro z hzx
      by_cases hPz : P < z
      · simp only [hPz, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq]
        let t := z - (j₀ + qm * w)
        have hbasez : j₀ + qm * w ≤ z := by simp [P] at hPz; omega
        have htform : z = j₀ + qm * w + t := by
          simp [t, Nat.add_sub_of_le hbasez]
        have htw : t < w := by rw [hxform] at hzx; simp [t] at hzx ⊢; omega
        have hrt : r < t := by rw [htform] at hPz; simp [P] at hPz; omega
        have hp₀z : p₀ < j₀ + t := by rw [hp₀form]; omega
        have hzj₁ : j₀ + t < j₁ := by rw [← hj₀w]; omega
        have hvalley := hp₀data.2 (j₀ + t)
          (List.mem_range.mpr hzj₁)
        have hbaseval : entry M 0 j₁ ≤ entry M 0 (j₀ + t) := by
          simpa [hp₀z] using hvalley
        have hzread := hblk qm t hqm htw
        rw [← htform] at hzread
        rw [hxread, hzread]
        omega
      · simp [hPz]
  have hnextN : nextR N 0 P x = true := by
    simpa [nextR] using hnextN0
  have hpx' : hasParent N 0 x = true := by
    simpa [N, x, j₁, i₁, j₀, w, Nat.add_assoc] using hpx
  have hactual := hasParent_next_fseq N 0 x hpx'
  have hparN : parent N 0 x = P :=
    row0_parent_unique N (parent N 0 x) P x hactual hnextN
  have hbase := RedCondA_apply M hA 0 j₁ (by omega) hj₁M hp0
  have hbase' : entry M 0 p₀ + 1 = entry M 0 j₁ := by
    simpa [p₀] using hbase
  change entry N 0 (parent N 0 x) + 1 = entry N 0 x
  rw [hparN, hPread, hxread]
  omega

/-- The complete row-0 part of condition (A) for a genuine tiling branch. -/
theorem RedCondA_oper_tiling_row0 (M : PS) (n x : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hA : RedCondA M = true)
    (hn : 1 ≤ n)
    (hpx : hasParent (oper M n) 0 x = true) :
    entry (oper M n) 0 (parent (oper M n) 0 x) + 1 =
      entry (oper M n) 0 x := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hnext := hasParent_next_fseq N 0 x (by simpa [N] using hpx)
  have hnext0 : nextrel0 N (parent N 0 x) x = true := by
    simpa [nextR] using hnext
  have hdata := hnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdata
  have hxlt : x < Lng N := hdata.1.1.1.2
  by_cases hxpre : x < j₀
  · exact RedCondA_oper_tiling_prefix M n 0 x hlast hzero hp hA
      (by omega) (by simpa [j₁, i₁, j₀] using hxpre) hpx
  · have hj₀x : j₀ ≤ x := by omega
    let q := (x - j₀) / w
    let s := (x - j₀) % w
    have hs : s < w := Nat.mod_lt _ hwpos
    have hdelta : x - j₀ < n * w := by rw [hlen] at hxlt; omega
    have hq : q < n := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using hdelta
    have hdiv : q * w + s = x - j₀ := by
      simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod (x - j₀) w)
    have hxform : x = j₀ + q * w + s := by omega
    by_cases hs0 : s = 0
    · have hxboundary : x = j₀ + q * w := by omega
      by_cases hq0 : q = 0
      · have hxj₀ : x = j₀ := by simp [hxboundary, hq0]
        have hpxj₀ : hasParent N 0 j₀ = true := by
          simpa [hxj₀] using hpx
        have hresult := RedCondA_oper_tiling_row0_blockstart M n
          hlast hzero hp hA hn (by simpa [N, j₁, i₁, j₀] using hpxj₀)
        simpa [N, hxj₀, j₁, i₁, j₀] using hresult
      · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        have hpxq : hasParent N 0 (j₀ + q * w) = true := by
          simpa [hxboundary] using hpx
        by_cases hi₁0 : i₁ = 0
        · have hi₁0' : idx1 M (Lng M - 1) = 0 := by
            simpa [i₁, j₁] using hi₁0
          have hresult := RedCondA_oper_tiling_row0_boundary_zero M n q
            hM hlast hzero hp hi₁0' hA hqpos hq (by
              simpa [N, j₁, i₁, j₀, w] using hpxq)
          simpa [N, hxboundary, j₁, i₁, j₀, w] using hresult
        · have hi₁le : i₁ ≤ 1 := by
            simpa [i₁] using idx1_le_one_rf M j₁
          have hi₁one : i₁ = 1 := by omega
          have hi₁one' : idx1 M (Lng M - 1) = 1 := by
            simpa [i₁, j₁] using hi₁one
          have hresult := RedCondA_oper_tiling_row0_boundary_one M n q
            hM hlast hzero hp hi₁one' hA hqpos hq (by
              simpa [N, j₁, i₁, j₀, w] using hpxq)
          simpa [N, hxboundary, j₁, i₁, j₀, w] using hresult
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      have hpxqs : hasParent N 0 (j₀ + q * w + s) = true := by
        simpa [hxform] using hpx
      have hresult := RedCondA_oper_tiling_row0_interior M n q s
        hM hlast hzero hp hA hq hspos (by
          simpa [j₁, i₁, j₀, w] using hs) (by
            simpa [N, j₁, i₁, j₀, w] using hpxqs)
      simpa [N, hxform, j₁, i₁, j₀, w] using hresult

private theorem entry_eq_one_of_ne_zero_rf (M : PS) (i j : ℕ)
    (hi : i ≠ 0) : entry M i j = entry M 1 j := by
  unfold entry
  simp [hi]

/-- If the active parent is in row zero, both rows of the tiled suffix are
verbatim-periodic.  Every tiled entry therefore reads at its period base. -/
theorem entry_oper_tiling_base_zero (M : PS) (n i z : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hz : z < Lng (oper M n)) :
    entry (oper M n) i z = entry M i
      (if z < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then z
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         (z - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
           (Lng M - 1 -
             parent M (idx1 M (Lng M - 1)) (Lng M - 1))) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  have hi₁' : i₁ = 0 := by simpa [i₁, j₁] using hi₁
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hlen : Lng (oper M n) = j₀ + n * w := by
    simpa [j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  by_cases hzpre : z < j₀
  · have hread := entry_oper_tiling_prefix M n i z hlast hzero hp (by
      simpa [j₁, i₁, j₀] using hzpre)
    simpa [j₁, i₁, j₀, w, hzpre] using hread
  · have hj₀z : j₀ ≤ z := by omega
    let q := (z - j₀) / w
    let s := (z - j₀) % w
    have hs : s < w := Nat.mod_lt _ hwpos
    have hdelta : z - j₀ < n * w := by rw [hlen] at hz; omega
    have hq : q < n := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using hdelta
    have hdiv : q * w + s = z - j₀ := by
      simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod (z - j₀) w)
    have hzform : z = j₀ + q * w + s := by omega
    have hsorig : s < Lng M - 1 -
        parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
      simpa [j₁, i₁, j₀, w] using hs
    have hzpre' : ¬z < parent M
        (idx1 M (Lng M - 1)) (Lng M - 1) := by
      simpa [j₁, i₁, j₀] using hzpre
    have hmod :
        (z - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
            (Lng M - 1 -
              parent M (idx1 M (Lng M - 1)) (Lng M - 1)) = s := by
      change (z - j₀) % w = s
      rfl
    have hbase :
        (if z < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then z
         else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
           (z - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
             (Lng M - 1 -
               parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = j₀ + s := by
      rw [if_neg hzpre', hmod]
    by_cases hi : i = 0
    · subst i
      have hread := entry_oper_tiling_block_zero M n q s
        hlast hzero hp hq hsorig
      rw [hbase, hzform]
      simpa [j₁, i₁, j₀, w, hi₁'] using hread
    · have hread := entry_oper_tiling_block_one M n q s
        hlast hzero hp hq hsorig
      rw [entry_eq_one_of_ne_zero_rf (oper M n) i z hi,
        entry_eq_one_of_ne_zero_rf M i
          (if z < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then z
           else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
             (z - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
               (Lng M - 1 -
                 parent M (idx1 M (Lng M - 1)) (Lng M - 1))) hi]
      rw [hbase, hzform]
      simpa [j₁, i₁, j₀, w] using hread

private theorem le0Aux_map_rf (A B : PS) (f : ℕ → ℕ)
    (hmap : ∀ u v, nextrel0 A u v = true →
      f u = f v ∨ nextrel0 B (f u) (f v) = true)
    (fuel a b : ℕ) (h : le0Aux A fuel a b = true) :
    le0Aux B fuel (f a) (f b) = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with hab | ⟨p, hpb, hpstep, hap⟩
      · exact Or.inl (congrArg f hab)
      · have hchain := ih p hap
        rcases hmap p b hpstep with heq | hstep
        · rw [heq] at hchain
          have hmono := le0Aux_mono_fseq B fuel (fuel + 1) (f a) (f b)
            (by omega) hchain
          simpa only [le0Aux, Bool.or_eq_true, beq_iff_eq,
            List.any_eq_true, Bool.and_eq_true, List.mem_range] using hmono
        · have hlt : f p < f b := by
            have hh := hstep
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.1.2
          exact Or.inr ⟨f p, hlt, hstep, hchain⟩

private theorem le0_map_rf (A B : PS) (f : ℕ → ℕ) (a b : ℕ)
    (hfa : f a < Lng B) (hfb : f b < Lng B)
    (hmap : ∀ u v, nextrel0 A u v = true →
      f u = f v ∨ nextrel0 B (f u) (f v) = true)
    (h : le0 A a b = true) :
    le0 B (f a) (f b) = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  have haux := le0Aux_map_rf A B f hmap (Lng A) a b hh.2
  have hsmall := le0Aux_bound_fseq B (Lng A) (f a) (f b) haux
  have hlarge := le0Aux_mono_fseq B (f b + 1) (Lng B) (f a) (f b)
    (by omega) hsmall
  simp [le0, hfa, hfb, hlarge]

private theorem le0Aux_index_rf {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with hab | ⟨p, hpb, _, hap⟩
      · omega
      · exact (ih hap).trans hpb.le

private theorem le0_index_rf {M : PS} {a b : ℕ}
    (h : le0 M a b = true) : a ≤ b := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  exact le0Aux_index_rf hh.2

private theorem le0Aux_map_bounded_rf (A B : PS) (f : ℕ → ℕ) (cap : ℕ)
    (hmap : ∀ u v, v ≤ cap → nextrel0 A u v = true →
      f u = f v ∨ nextrel0 B (f u) (f v) = true)
    (fuel a b : ℕ) (hbcap : b ≤ cap)
    (h : le0Aux A fuel a b = true) :
    le0Aux B fuel (f a) (f b) = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with hab | ⟨p, hpb, hpstep, hap⟩
      · exact Or.inl (congrArg f hab)
      · have hpcap : p ≤ cap := hpb.le.trans hbcap
        have hchain := ih p hpcap hap
        rcases hmap p b hbcap hpstep with heq | hstep
        · rw [heq] at hchain
          have hmono := le0Aux_mono_fseq B fuel (fuel + 1) (f a) (f b)
            (by omega) hchain
          simpa only [le0Aux, Bool.or_eq_true, beq_iff_eq,
            List.any_eq_true, Bool.and_eq_true, List.mem_range] using hmono
        · have hlt : f p < f b := by
            have hh := hstep
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.1.2
          exact Or.inr ⟨f p, hlt, hstep, hchain⟩

private theorem le0_map_bounded_rf (A B : PS) (f : ℕ → ℕ)
    (a b cap : ℕ) (hbcap : b ≤ cap)
    (hfa : f a < Lng B) (hfb : f b < Lng B)
    (hmap : ∀ u v, v ≤ cap → nextrel0 A u v = true →
      f u = f v ∨ nextrel0 B (f u) (f v) = true)
    (h : le0 A a b = true) :
    le0 B (f a) (f b) = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  have haux := le0Aux_map_bounded_rf A B f cap hmap (Lng A) a b
    hbcap hh.2
  have hsmall := le0Aux_bound_fseq B (Lng A) (f a) (f b) haux
  have hlarge := le0Aux_mono_fseq B (f b + 1) (Lng B) (f a) (f b)
    (by omega) hsmall
  simp [le0, hfa, hfb, hlarge]

/-- In the zero-shift layout, a row-zero edge ending no later than block `q`
reflects under the period-base map to a row-zero edge of the original
sequence. -/
theorem nextrel0_oper_tiling_base_zero (M : PS) (n y z : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hstep : nextrel0 (oper M n) y z = true) :
    nextrel0 M
      (if y < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then y
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         (y - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
           (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)))
      (if z < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then z
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         (z - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
           (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let base := fun u => if u < j₀ then u else j₀ + (u - j₀) % w
  have hi₁' : i₁ = 0 := by simpa [i₁, j₁] using hi₁
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hj₀M : j₀ < Lng M := by omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hdata := hstep
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hdata
  have hyN : y < Lng N := hdata.1.1.1.1
  have hzN : z < Lng N := hdata.1.1.1.2
  have hyz : y < z := hdata.1.1.2
  have hstrict : entry N 0 y < entry N 0 z := hdata.1.2
  have hvalley : ∀ u, y < u → u < z → entry N 0 z ≤ entry N 0 u := by
    intro u hyu huz
    have hu := hdata.2 u (List.mem_range.mpr huz)
    simpa [hyu] using hu
  change nextrel0 M (base y) (base z) = true
  by_cases hzpre : z < j₀
  · have hypre : y < j₀ := hyz.trans hzpre
    have hyread := entry_oper_tiling_prefix M n 0 y hlast hzero hp (by
      simpa [j₁, i₁, j₀] using hypre)
    have hzread := entry_oper_tiling_prefix M n 0 z hlast hzero hp (by
      simpa [j₁, i₁, j₀] using hzpre)
    have hyM : y < Lng M := hypre.trans hj₀M
    have hzM : z < Lng M := hzpre.trans hj₀M
    have hstepM : nextrel0 M y z = true := by
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨hyM, hzM⟩, hyz⟩, ?_⟩, ?_⟩
      · rw [← hyread, ← hzread]
        exact hstrict
      · intro u huz
        by_cases hyu : y < u
        · simp only [hyu, decide_true, Bool.not_true, Bool.false_or,
            decide_eq_true_eq]
          have huread := entry_oper_tiling_prefix M n 0 u hlast hzero hp (by
            simpa [j₁, i₁, j₀] using huz.trans hzpre)
          rw [← hzread, ← huread]
          exact hvalley u hyu huz
        · simp [hyu]
    simpa [base, hypre, hzpre] using hstepM
  · have hj₀z : j₀ ≤ z := by omega
    let qz := (z - j₀) / w
    let sz := (z - j₀) % w
    let B := j₀ + qz * w
    have hsz : sz < w := Nat.mod_lt _ hwpos
    have hzdelta : z - j₀ < n * w := by rw [hlen] at hzN; omega
    have hqz : qz < n := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using hzdelta
    have hdiv : qz * w + sz = z - j₀ := by
      simpa [qz, sz, Nat.mul_comm] using (Nat.div_add_mod (z - j₀) w)
    have hzform : z = B + sz := by simp [B]; omega
    have hBform : B = j₀ + qz * w := rfl
    have hBz : B ≤ z := by rw [hzform]; omega
    have hBltN : B < Lng N := by
      rw [hlen]
      simp [B]
      nlinarith
    have hBread : entry N 0 B = entry M 0 j₀ := by
      simpa [N, B, j₁, i₁, j₀, w, hi₁'] using
        entry_oper_tiling_block_zero M n qz 0 hlast hzero hp hqz hwpos
    have hzread : entry N 0 z = entry M 0 (j₀ + sz) := by
      have hr := entry_oper_tiling_block_zero M n qz sz
        hlast hzero hp hqz (by
          simpa [j₁, i₁, j₀, w] using hsz)
      rw [hzform]
      simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using hr
    by_cases hypre : y < j₀
    · have hsz0 : sz = 0 := by
        by_contra hne
        have hszpos : 0 < sz := Nat.pos_of_ne_zero hne
        have hBstrict : B < z := by rw [hzform]; omega
        have hyB : y < B := hypre.trans_le (by simp [B])
        have hfloor : entry M 0 j₀ < entry M 0 (j₀ + sz) := by
          simpa [j₁, i₁, j₀, w] using
            oper_tiling_strict_floor M sz hM hp hszpos hsz.le
        have := hvalley B hyB hBstrict
        rw [hzread, hBread] at this
        omega
      have hzB : z = B := by rw [hzform, hsz0]; simp
      have hzbase : base z = j₀ := by
        simp [base, hzform, hsz0, B]
      have hybase : base y = y := by simp [base, hypre]
      have hyread := entry_oper_tiling_prefix M n 0 y hlast hzero hp (by
        simpa [j₁, i₁, j₀] using hypre)
      have hyM : y < Lng M := hypre.trans hj₀M
      have hstepM : nextrel0 M y j₀ = true := by
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨⟨hyM, hj₀M⟩, hypre⟩, ?_⟩, ?_⟩
        · rw [← hyread, ← hBread]
          simpa [hzB] using hstrict
        · intro u huj₀
          by_cases hyu : y < u
          · simp only [hyu, decide_true, Bool.not_true, Bool.false_or,
              decide_eq_true_eq]
            have huz : u < z := huj₀.trans_le (by rw [hzB]; simp [B])
            have huread := entry_oper_tiling_prefix M n 0 u hlast hzero hp (by
              simpa [j₁, i₁, j₀] using huj₀)
            rw [← hBread, ← huread]
            simpa [hzB] using hvalley u hyu huz
          · simp [hyu]
      simpa [hybase, hzbase] using hstepM
    · have hj₀y : j₀ ≤ y := by omega
      have hBy : B ≤ y := by
        by_contra hnot
        have hyB : y < B := by omega
        have hyltN : y < Lng N := hyN
        have hyfloor := oper_tiling_block_floor M n y hM hlast hzero hp
          (by simpa [j₁, i₁, j₀] using hj₀y) hyltN
        have hyfloor' : entry M 0 j₀ ≤ entry N 0 y := by
          simpa [N, j₁, i₁, j₀] using hyfloor
        by_cases hsz0 : sz = 0
        · have hzread0 : entry N 0 z = entry M 0 j₀ := by
            simpa [hsz0] using hzread
          rw [hzread0] at hstrict
          omega
        · have hBstrict : B < z := by rw [hzform]; omega
          have hv := hvalley B hyB hBstrict
          rw [hzread, hBread] at hv
          have hszpos : 0 < sz := Nat.pos_of_ne_zero hsz0
          have hf := oper_tiling_strict_floor M sz hM hp hszpos hsz.le
          have hf' : entry M 0 j₀ < entry M 0 (j₀ + sz) := by
            simpa [j₁, i₁, j₀, w] using hf
          omega
      let sy := y - B
      have hsylt : sy < sz := by simp [sy]; omega
      have hsyw : sy < w := hsylt.trans hsz
      have hyform : y = B + sy := by simp [sy, Nat.add_sub_of_le hBy]
      have hyread : entry N 0 y = entry M 0 (j₀ + sy) := by
        have hr := entry_oper_tiling_block_zero M n qz sy
          hlast hzero hp hqz (by
            simpa [j₁, i₁, j₀, w] using hsyw)
        rw [hyform]
        simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using hr
      have hybase : base y = j₀ + sy := by
        have hymod : (y - j₀) % w = sy := by
          have hsub : y - j₀ = qz * w + sy := by
            rw [hyform]
            simp only [B]
            omega
          rw [hsub]
          simp [Nat.add_mod, Nat.mod_eq_of_lt hsyw]
        simp [base, hypre, hymod]
      have hzbase : base z = j₀ + sz := by
        have hzmod : (z - j₀) % w = sz := rfl
        simp [base, hzpre, hzmod]
      have hsyM : j₀ + sy < Lng M := by omega
      have hszM : j₀ + sz < Lng M := by omega
      have hstepM : nextrel0 M (j₀ + sy) (j₀ + sz) = true := by
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨⟨hsyM, hszM⟩, by omega⟩, ?_⟩, ?_⟩
        · rw [← hyread, ← hzread]
          exact hstrict
        · intro u husz
          by_cases hsyu : j₀ + sy < u
          · simp only [hsyu, decide_true, Bool.not_true, Bool.false_or,
              decide_eq_true_eq]
            have hj₀u : j₀ ≤ u := by omega
            let t := u - j₀
            have htlt : t < sz := by simp [t] at husz ⊢; omega
            have htw : t < w := htlt.trans hsz
            have hyt : y < B + t := by rw [hyform]; simp [t] at hsyu ⊢; omega
            have htz : B + t < z := by rw [hzform]; omega
            have hv := hvalley (B + t) hyt htz
            have htread := entry_oper_tiling_block_zero M n qz t
              hlast hzero hp hqz (by
                simpa [j₁, i₁, j₀, w] using htw)
            rw [hzread] at hv
            have htread' : entry N 0 (B + t) = entry M 0 (j₀ + t) := by
              simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using htread
            rw [htread'] at hv
            have huform : u = j₀ + t := by
              simp [t, Nat.add_sub_of_le hj₀u]
            simpa [huform] using hv
          · simp [hsyu]
      simpa [hybase, hzbase] using hstepM

/-- In the zero-shift layout, every row-zero reachability statement reflects
under the period-base map to the original sequence. -/
theorem le0_oper_tiling_base_zero (M : PS) (n a b : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hle : le0 (oper M n) a b = true) :
    le0 M
      (if a < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then a
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         (a - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
           (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)))
      (if b < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then b
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         (b - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) %
           (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let base := fun u => if u < j₀ then u else j₀ + (u - j₀) % w
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hj₁M : j₁ < Lng M := by simp [j₁]; omega
  have hrange : ∀ u, u < Lng N → base u < Lng M := by
    intro u hu
    by_cases hupre : u < j₀
    · simp [base, hupre]
      omega
    · have hmod : (u - j₀) % w < w := Nat.mod_lt _ hwpos
      simp [base, hupre]
      omega
  have hledata := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hledata
  have haN : a < Lng N := hledata.1.1
  have hbN : b < Lng N := hledata.1.2
  have hmapped := le0_map_rf N M base a b (hrange a haN) (hrange b hbN)
    (fun u v huv => Or.inr (by
      simpa [N, base, j₁, i₁, j₀, w] using
        nextrel0_oper_tiling_base_zero M n u v hM hlast hzero hp hi₁ huv))
    (by simpa [N] using hle)
  simpa [base, j₁, i₁, j₀, w] using hmapped

/-- In the zero-shift layout, a base row-zero edge ending inside the active
slice lifts to any selected tiling block. -/
theorem nextrel0_oper_tiling_lift_zero (M : PS) (n q a b : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hq : q < n)
    (hb : b < Lng M - 1)
    (hstep : nextrel0 M a b = true) :
    nextrel0 (oper M n)
      (if a < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then a
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) +
         (a - parent M (idx1 M (Lng M - 1)) (Lng M - 1)))
      (if b < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then b
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) +
         (b - parent M (idx1 M (Lng M - 1)) (Lng M - 1))) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let lift := fun u => if u < j₀ then u else B + (u - j₀)
  have hi₁' : i₁ = 0 := by simpa [i₁, j₁] using hi₁
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hdata := hstep
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hdata
  have haM : a < Lng M := hdata.1.1.1.1
  have hbM : b < Lng M := hdata.1.1.1.2
  have hab : a < b := hdata.1.1.2
  have hstrict : entry M 0 a < entry M 0 b := hdata.1.2
  have hvalley : ∀ u, a < u → u < b → entry M 0 b ≤ entry M 0 u := by
    intro u hau hub
    have hu := hdata.2 u (List.mem_range.mpr hub)
    simpa [hau] using hu
  change nextrel0 N (lift a) (lift b) = true
  by_cases hbpre : b < j₀
  · have hapre : a < j₀ := hab.trans hbpre
    have haN : a < Lng N := by rw [hlen]; nlinarith
    have hbN : b < Lng N := by rw [hlen]; nlinarith
    have haread := entry_oper_tiling_prefix M n 0 a hlast hzero hp (by
      simpa [j₁, i₁, j₀] using hapre)
    have hbread := entry_oper_tiling_prefix M n 0 b hlast hzero hp (by
      simpa [j₁, i₁, j₀] using hbpre)
    have hstepN : nextrel0 N a b = true := by
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨haN, hbN⟩, hab⟩, ?_⟩, ?_⟩
      · rw [haread, hbread]
        exact hstrict
      · intro u hub
        by_cases hau : a < u
        · simp only [hau, decide_true, Bool.not_true, Bool.false_or,
            decide_eq_true_eq]
          have huread := entry_oper_tiling_prefix M n 0 u hlast hzero hp (by
            simpa [j₁, i₁, j₀] using hub.trans hbpre)
          rw [hbread, huread]
          exact hvalley u hau hub
        · simp [hau]
    simpa [lift, hapre, hbpre] using hstepN
  · have hj₀b : j₀ ≤ b := by omega
    by_cases hj₀a : j₀ ≤ a
    · have hapre : ¬a < j₀ := by omega
      have hbpre' : ¬b < j₀ := hbpre
      let sa := a - j₀
      let sb := b - j₀
      have hsa : sa < w := by simp [sa, w]; omega
      have hsb : sb < w := by simp [sb, w, j₁] at hb ⊢; omega
      have hsasb : sa < sb := by simp [sa, sb]; omega
      have haform : a = j₀ + sa := by simp [sa, Nat.add_sub_of_le hj₀a]
      have hbform : b = j₀ + sb := by simp [sb, Nat.add_sub_of_le hj₀b]
      have haN : B + sa < Lng N := by
        rw [hlen]
        simp [B]
        nlinarith
      have hbN : B + sb < Lng N := by
        rw [hlen]
        simp [B]
        nlinarith
      have haread : entry N 0 (B + sa) = entry M 0 a := by
        have hr := entry_oper_tiling_block_zero M n q sa hlast hzero hp hq
          (by simpa [j₁, i₁, j₀, w] using hsa)
        rw [haform]
        simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using hr
      have hbread : entry N 0 (B + sb) = entry M 0 b := by
        have hr := entry_oper_tiling_block_zero M n q sb hlast hzero hp hq
          (by simpa [j₁, i₁, j₀, w] using hsb)
        rw [hbform]
        simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using hr
      have hstepN : nextrel0 N (B + sa) (B + sb) = true := by
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨⟨haN, hbN⟩, by omega⟩, ?_⟩, ?_⟩
        · rw [haread, hbread]
          exact hstrict
        · intro u huBsb
          by_cases hBsaU : B + sa < u
          · simp only [hBsaU, decide_true, Bool.not_true, Bool.false_or,
              decide_eq_true_eq]
            have hBu : B ≤ u := by omega
            let t := u - B
            have hsat : sa < t := by simp [t] at hBsaU ⊢; omega
            have htsb : t < sb := by simp [t] at huBsb ⊢; omega
            have htw : t < w := htsb.trans hsb
            have huform : u = B + t := by simp [t, Nat.add_sub_of_le hBu]
            have hbaseu : j₀ + t < b := by rw [hbform]; omega
            have hau : a < j₀ + t := by rw [haform]; omega
            have hv := hvalley (j₀ + t) hau hbaseu
            have huread := entry_oper_tiling_block_zero M n q t
              hlast hzero hp hq (by
                simpa [j₁, i₁, j₀, w] using htw)
            have huread' : entry N 0 (B + t) = entry M 0 (j₀ + t) := by
              simpa [N, B, j₁, i₁, j₀, w, hi₁', Nat.add_assoc] using huread
            rw [huform, hbread]
            rw [huread']
            exact hv
          · simp [hBsaU]
      have hlifta : lift a = B + sa := by simp [lift, hapre, sa]
      have hliftb : lift b = B + sb := by simp [lift, hbpre', sb]
      rw [hlifta, hliftb]
      exact hstepN
    · have hapre : a < j₀ := by omega
      have hbEq : b = j₀ := by
        by_contra hne
        have hj₀b' : j₀ < b := by omega
        let s := b - j₀
        have hspos : 0 < s := by simp [s]; omega
        have hslt : s < w := by simp [s, w, j₁] at hb ⊢; omega
        have hfloor := oper_tiling_strict_floor M s hM hp hspos hslt.le
        have hbform : b = j₀ + s := by simp [s, Nat.add_sub_of_le hj₀b]
        have hle := hvalley j₀ hapre hj₀b'
        rw [hbform] at hle
        have hf : entry M 0 j₀ < entry M 0 (j₀ + s) := by
          simpa [j₁, i₁, j₀, w] using hfloor
        omega
      have haN : a < Lng N := by rw [hlen]; nlinarith
      have hBN : B < Lng N := by
        rw [hlen]
        simp [B]
        nlinarith
      have haread := entry_oper_tiling_prefix M n 0 a hlast hzero hp (by
        simpa [j₁, i₁, j₀] using hapre)
      have hBread : entry N 0 B = entry M 0 j₀ := by
        simpa [N, B, j₁, i₁, j₀, w, hi₁'] using
          entry_oper_tiling_block_zero M n q 0 hlast hzero hp hq hwpos
      have hstepN : nextrel0 N a B = true := by
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨⟨haN, hBN⟩, by simp [B]; omega⟩, ?_⟩, ?_⟩
        · rw [haread, hBread, ← hbEq]
          exact hstrict
        · intro u huB
          by_cases hau : a < u
          · simp only [hau, decide_true, Bool.not_true, Bool.false_or,
              decide_eq_true_eq]
            by_cases hupre : u < j₀
            · have huread := entry_oper_tiling_prefix M n 0 u hlast hzero hp (by
              simpa [j₁, i₁, j₀] using hupre)
              rw [hBread, huread, ← hbEq]
              exact hvalley u hau (by rw [hbEq]; exact hupre)
            · have hj₀u : j₀ ≤ u := by omega
              have huN : u < Lng N := huB.trans hBN
              have hfloor := oper_tiling_block_floor M n u hM hlast hzero hp
                (by simpa [j₁, i₁, j₀] using hj₀u) huN
              rw [hBread]
              simpa [N, j₁, i₁, j₀] using hfloor
          · simp [hau]
      simpa [lift, hapre, hbpre, hbEq, B] using hstepN

/-- In the zero-shift layout, row-zero reachability ending in the active slice
lifts to any selected tiling block. -/
theorem le0_oper_tiling_lift_zero (M : PS) (n q a s : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hq : q < n)
    (hs : s < Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hle : le0 M a
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s) = true) :
    le0 (oper M n)
      (if a < parent M (idx1 M (Lng M - 1)) (Lng M - 1) then a
       else parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
         q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) +
         (a - parent M (idx1 M (Lng M - 1)) (Lng M - 1)))
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
        q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let target := j₀ + s
  let lift := fun u => if u < j₀ then u else B + (u - j₀)
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [j₁, i₁, j₀, w] using hs
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hatarget : a ≤ target := by
    apply le0_index_rf
    simpa [target, j₁, i₁, j₀] using hle
  have hlifta : lift a < Lng N := by
    by_cases hapre : a < j₀
    · simp [lift, hapre]
      rw [hlen]
      nlinarith
    · have hj₀a : j₀ ≤ a := by omega
      have haoff : a - j₀ ≤ s := by simp [target] at hatarget; omega
      simp [lift, hapre, B]
      rw [hlen]
      nlinarith
  have hlifttarget : lift target = B + s := by
    simp [lift, target, B]
  have htargetN : lift target < Lng N := by
    rw [hlifttarget, hlen]
    simp [B]
    nlinarith
  have hmapped := le0_map_bounded_rf M N lift a target target (le_refl _)
    hlifta htargetN
    (fun u v hv hstep => Or.inr (by
      have hvj₁ : v < j₁ := by simp [target] at hv; omega
      simpa [N, lift, B, j₁, i₁, j₀, w] using
        nextrel0_oper_tiling_lift_zero M n q u v hM hlast hzero hp
          hi₁ hq (by simpa [j₁] using hvj₁) hstep))
    (by simpa [target, j₁, i₁, j₀] using hle)
  rw [hlifttarget] at hmapped
  simpa [N, lift, B, target, j₁, i₁, j₀, w] using hmapped

set_option maxHeartbeats 1000000 in
/-- Row-1 condition (A) at an arbitrary tiled column in the zero-shift
layout.  The selected parent reflects through the period-base map. -/
theorem RedCondA_oper_tiling_row1_zero (M : PS) (n q s : ℕ)
    (hM : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hA : RedCondA M = true)
    (hq : q < n)
    (hs : s < Lng M - 1 -
      parent M (idx1 M (Lng M - 1)) (Lng M - 1))
    (hpx : hasParent (oper M n) 1
      (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
        q * (Lng M - 1 -
          parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) = true) :
    entry (oper M n) 1
        (parent (oper M n) 1
          (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
            q * (Lng M - 1 -
              parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)) + 1 =
      entry (oper M n) 1
        (parent M (idx1 M (Lng M - 1)) (Lng M - 1) +
          q * (Lng M - 1 -
            parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let x := B + s
  let base := fun u => if u < j₀ then u else j₀ + (u - j₀) % w
  let bx := j₀ + s
  let p := parent N 1 x
  let bp := base p
  have hnextTop := hasParent_next_fseq M i₁ j₁ (by
    simpa [i₁, j₁] using hp)
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M i₁ j₀ j₁ hnextTop).1
  have hwpos : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [j₁, i₁, j₀, w] using hs
  have hj₁M : j₁ < Lng M := by simp [j₁]; omega
  have hbxM : bx < Lng M := by simp [bx]; omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w] using
      length_oper_tiling M n hlast hzero hp
  have hxN : x < Lng N := by
    rw [hlen]
    simp [x, B]
    nlinarith
  have hpx' : hasParent N 1 x = true := by
    simpa [N, x, B, j₁, i₁, j₀, w, Nat.add_assoc] using hpx
  have hpnext : nextR N 1 p x = true :=
    hasParent_next_fseq N 1 x hpx'
  have hpnext1 : nextrel1 N p x = true := by
    simpa [nextR] using hpnext
  have hpdata := hpnext1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hpdata
  have hpN : p < Lng N := hpdata.1.1.1.1.1
  have hpxlt : p < x := hpdata.1.1.1.2
  have hpstrict : entry N 1 p < entry N 1 x := hpdata.1.1.2
  have hpreach : le0 N p x = true := hpdata.1.2
  have hxread : entry N 1 x = entry M 1 bx := by
    have hr := entry_oper_tiling_block_one M n q s hlast hzero hp hq hs
    simpa [N, x, B, bx, j₁, i₁, j₀, w, Nat.add_assoc] using hr
  have hpread : entry N 1 p = entry M 1 bp := by
    have hr := entry_oper_tiling_base_zero M n 1 p hlast hzero hp hi₁ (by
      simpa [N] using hpN)
    simpa [N, base, bp, j₁, i₁, j₀, w] using hr
  have hbaseReach : le0 M bp bx = true := by
    have hr := le0_oper_tiling_base_zero M n p x hM hlast hzero hp hi₁
      (by simpa [N] using hpreach)
    have hxbase : base x = bx := by
      have hxmod : (x - j₀) % w = s := by
        have hsub : x - j₀ = q * w + s := by
          simp only [x, B]
          omega
        rw [hsub]
        simp [Nat.add_mod, Nat.mod_eq_of_lt hs']
      have hxnotpre : ¬x < j₀ := by
        simp only [x, B]
        omega
      simp [base, hxnotpre, bx, hxmod]
    simpa [base, bp, hxbase, bx, j₁, i₁, j₀, w] using hr
  have hbpM : bp < Lng M := by
    by_cases hppre : p < j₀
    · simp [bp, base, hppre]
      omega
    · have hmod : (p - j₀) % w < w := Nat.mod_lt _ hwpos
      simp [bp, base, hppre]
      omega
  have hbpbx : bp < bx := by
    have hle := le0_index_rf hbaseReach
    rw [hpread, hxread] at hpstrict
    have hne : bp ≠ bx := by
      intro heq
      rw [heq] at hpstrict
      omega
    exact lt_of_le_of_ne hle hne
  have hnextBase1 : nextrel1 M bp bx = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨hbpM, hbxM⟩, hbpbx⟩, ?_⟩, hbaseReach⟩, ?_⟩
    · rw [← hpread, ← hxread]
      exact hpstrict
    · intro u huM
      by_cases hbpu : bp < u
      · by_cases hureach : le0 M u bx = true
        · simp only [hbpu, decide_true, hureach, Bool.and_self,
            Bool.not_true, Bool.false_or, decide_eq_true_eq]
          have hubx : u ≤ bx := le0_index_rf hureach
          let liftu := if u < j₀ then u else B + (u - j₀)
          have hLiftReach : le0 N liftu x = true := by
            have hr := le0_oper_tiling_lift_zero M n q u s hM hlast hzero
              hp hi₁ hq hs hureach
            simpa [N, liftu, x, B, j₁, i₁, j₀, w] using hr
          have hliftN : liftu < Lng N := by
            have hh := hLiftReach
            simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.1
          have hliftread : entry N 1 liftu = entry M 1 u := by
            by_cases hupre : u < j₀
            · have hr := entry_oper_tiling_prefix M n 1 u hlast hzero hp (by
                simpa [j₁, i₁, j₀] using hupre)
              simpa [N, liftu, hupre] using hr
            · have hj₀u : j₀ ≤ u := by omega
              let t := u - j₀
              have ht : t < w := by simp [t, bx] at hubx; omega
              have huform : u = j₀ + t := by
                simp [t, Nat.add_sub_of_le hj₀u]
              have hr := entry_oper_tiling_block_one M n q t
                hlast hzero hp hq (by
                  simpa [j₁, i₁, j₀, w] using ht)
              rw [huform]
              simpa [N, liftu, B, t, hupre, j₁, i₁, j₀, w,
                Nat.add_assoc] using hr
          have hplift : p < liftu := by
            by_cases hppre : p < j₀
            · have hbp : bp = p := by simp [bp, base, hppre]
              by_cases hupre : u < j₀
              · simp [liftu, hupre]
                rw [← hbp]
                exact hbpu
              · simp [liftu, hupre, B]
                omega
            · have hj₀p : j₀ ≤ p := by omega
              let qp := (p - j₀) / w
              let sp := (p - j₀) % w
              have hsp : sp < w := Nat.mod_lt _ hwpos
              have hpdiv : qp * w + sp = p - j₀ := by
                simpa [qp, sp, Nat.mul_comm] using
                  (Nat.div_add_mod (p - j₀) w)
              have hpform : p = j₀ + qp * w + sp := by omega
              have hbpform : bp = j₀ + sp := by
                simp [bp, base, hppre, sp]
              have hqple : qp ≤ q := by
                by_contra hnot
                have hqqp : q + 1 ≤ qp := by omega
                have hmul : (q + 1) * w ≤ qp * w :=
                  Nat.mul_le_mul_right w hqqp
                simp [x, B] at hpxlt
                nlinarith
              have hupre : ¬u < j₀ := by rw [hbpform] at hbpu; omega
              have hj₀u : j₀ ≤ u := by omega
              have hspu : sp < u - j₀ := by
                rw [hbpform] at hbpu
                omega
              have hliftform : liftu = B + (u - j₀) := by
                simp [liftu, hupre]
              rw [hliftform, hpform]
              by_cases hqpq : qp = q
              · rw [hqpq]
                simpa only [B, Nat.add_assoc] using
                  Nat.add_lt_add_left hspu (j₀ + q * w)
              · have hqplt : qp < q := by omega
                have hmul : (qp + 1) * w ≤ q * w :=
                  Nat.mul_le_mul_right w (by omega)
                have hpblock : j₀ + qp * w + sp < j₀ + (qp + 1) * w := by
                  nlinarith
                have hblockB : j₀ + (qp + 1) * w ≤ B := by
                  simp only [B]
                  nlinarith
                omega
          have hall := hpdata.2 liftu hliftN
          have hge : entry N 1 x ≤ entry N 1 liftu := by
            simpa [hplift, hLiftReach] using hall
          rw [hxread, hliftread] at hge
          exact hge
        · simp [hbpu, hureach]
      · simp [hbpu]
  have hnextBase : nextR M 1 bp bx = true := by
    simpa [nextR] using hnextBase1
  have hpBase : hasParent M 1 bx = true :=
    (hasParent_iff_unique_fseq M 1 bx).mpr
      ⟨bp, hnextBase,
        fun r hr => nextR1_unique_mr M r bp bx hr hnextBase⟩
  have hparBase : parent M 1 bx = bp :=
    parent_eq_of_unique_fseq M 1 bx bp hnextBase
      (fun r hr => nextR1_unique_mr M r bp bx hr hnextBase)
  have hbase := RedCondA_apply M hA 1 bx (by omega) hbxM hpBase
  rw [hparBase] at hbase
  change entry N 1 p + 1 = entry N 1 x
  rw [hpread, hxread]
  exact hbase

/-- A row-zero edge contained in one positive-shift tiling block reflects to
the corresponding edge of the original active slice. -/
private theorem nextrel0_oper_tiling_block_back_one (M : PS)
    (n q a b : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hq : q < n) (ha : a < b)
    (hb : b < Lng M - 1 - parent M 1 (Lng M - 1))
    (hstep : nextrel0 (oper M n)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + a)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + b) = true) :
    nextrel0 M (parent M 1 (Lng M - 1) + a)
      (parent M 1 (Lng M - 1) + b) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let d := entry M 0 j₁ - entry M 0 j₀
  have hi₁' : i₁ = 1 := by simpa [i₁, j₁] using hi₁
  have hj₀idx : parent M i₁ j₁ = j₀ := by simp [j₀, hi₁']
  have hb' : b < w := by simpa [j₁, j₀, w] using hb
  have ha' : a < w := ha.trans hb'
  have hread (t : ℕ) (ht : t < w) :
      entry N 0 (B + t) = entry M 0 (j₀ + t) + q * d := by
    have hr := entry_oper_tiling_block_zero M n q t hlast hzero hp hq
      (by simpa [j₁, i₁, j₀, w, hj₀idx] using ht)
    simpa [N, B, d, j₁, i₁, j₀, w, hi₁', hj₀idx,
      Nat.add_assoc] using hr
  have hdata := hstep
  change nextrel0 N (B + a) (B + b) = true at hdata
  change nextrel0 M (j₀ + a) (j₀ + b) = true
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hdata ⊢
  have hstrictN : entry N 0 (B + a) < entry N 0 (B + b) :=
    hdata.1.2
  have hvalleyN : ∀ u, B + a < u → u < B + b →
      entry N 0 (B + b) ≤ entry N 0 u := by
    intro u hau hub
    have hu := hdata.2 u hub
    simpa [hau] using hu
  have hjaM : j₀ + a < Lng M := by simp [j₀]; omega
  have hjbM : j₀ + b < Lng M := by simp [j₀]; omega
  refine ⟨⟨⟨⟨hjaM, hjbM⟩, by omega⟩, ?_⟩, ?_⟩
  · rw [hread a ha', hread b hb'] at hstrictN
    omega
  · intro u hub
    by_cases hau : j₀ + a < u
    · simp only [hau, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq]
      have hju : j₀ ≤ u := by omega
      let t := u - j₀
      have hat : a < t := by simp [t] at hau ⊢; omega
      have htb : t < b := by simp [t] at hub ⊢; omega
      have htw : t < w := htb.trans hb'
      have huform : u = j₀ + t := by simp [t, Nat.add_sub_of_le hju]
      have hBt : B + a < B + t := by omega
      have hBtB : B + t < B + b := by omega
      have hv := hvalleyN (B + t) hBt hBtB
      rw [hread b hb', hread t htw] at hv
      rw [huform]
      omega
    · simp [hau]

/-- A row-zero edge of the original active slice lifts to the corresponding
edge in every positive-shift tiling block. -/
private theorem nextrel0_oper_tiling_block_lift_one (M : PS)
    (n q a b : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hq : q < n) (ha : a < b)
    (hb : b < Lng M - 1 - parent M 1 (Lng M - 1))
    (hstep : nextrel0 M (parent M 1 (Lng M - 1) + a)
      (parent M 1 (Lng M - 1) + b) = true) :
    nextrel0 (oper M n)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + a)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + b) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let d := entry M 0 j₁ - entry M 0 j₀
  have hi₁' : i₁ = 1 := by simpa [i₁, j₁] using hi₁
  have hj₀idx : parent M i₁ j₁ = j₀ := by simp [j₀, hi₁']
  have hb' : b < w := by simpa [j₁, j₀, w] using hb
  have ha' : a < w := ha.trans hb'
  have hwpos : 0 < w := by omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w, hj₀idx] using
      length_oper_tiling M n hlast hzero hp
  have hread (t : ℕ) (ht : t < w) :
      entry N 0 (B + t) = entry M 0 (j₀ + t) + q * d := by
    have hr := entry_oper_tiling_block_zero M n q t hlast hzero hp hq
      (by simpa [j₁, i₁, j₀, w, hj₀idx] using ht)
    simpa [N, B, d, j₁, i₁, j₀, w, hi₁', hj₀idx,
      Nat.add_assoc] using hr
  have hdata := hstep
  change nextrel0 M (j₀ + a) (j₀ + b) = true at hdata
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hdata
  have hstrictM : entry M 0 (j₀ + a) < entry M 0 (j₀ + b) :=
    hdata.1.2
  have hvalleyM : ∀ u, j₀ + a < u → u < j₀ + b →
      entry M 0 (j₀ + b) ≤ entry M 0 u := by
    intro u hau hub
    have hu := hdata.2 u hub
    simpa [hau] using hu
  have haN : B + a < Lng N := by rw [hlen]; simp [B]; nlinarith
  have hbN : B + b < Lng N := by rw [hlen]; simp [B]; nlinarith
  change nextrel0 N (B + a) (B + b) = true
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨haN, hbN⟩, by omega⟩, ?_⟩, ?_⟩
  · rw [hread a ha', hread b hb']
    omega
  · intro u hub
    by_cases hau : B + a < u
    · simp only [hau, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq]
      have hBu : B ≤ u := by omega
      let t := u - B
      have hat : a < t := by simp [t] at hau ⊢; omega
      have htb : t < b := by simp [t] at hub ⊢; omega
      have htw : t < w := htb.trans hb'
      have huform : u = B + t := by simp [t, Nat.add_sub_of_le hBu]
      have hv := hvalleyM (j₀ + t) (by omega) (by omega)
      rw [huform, hread b hb', hread t htw]
      omega
    · simp [hau]

private theorem le0Aux_map_interval_rf (A C : PS) (f : ℕ → ℕ)
    (floor cap : ℕ)
    (hmap : ∀ u v, floor ≤ u → v ≤ cap → nextrel0 A u v = true →
      f u = f v ∨ nextrel0 C (f u) (f v) = true)
    (fuel a b : ℕ) (hafloor : floor ≤ a) (hbcap : b ≤ cap)
    (h : le0Aux A fuel a b = true) :
    le0Aux C fuel (f a) (f b) = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le0Aux] using h
      subst b
      simp [le0Aux]
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with hab | ⟨p, hpb, hpstep, hap⟩
      · exact Or.inl (congrArg f hab)
      · have hpceil : p ≤ cap := hpb.le.trans hbcap
        have hpfloor : floor ≤ p :=
          hafloor.trans (le0Aux_index_rf hap)
        have hchain := ih p hpceil hap
        rcases hmap p b hpfloor hbcap hpstep with heq | hstep
        · rw [heq] at hchain
          have hmono := le0Aux_mono_fseq C fuel (fuel + 1) (f a) (f b)
            (by omega) hchain
          simpa only [le0Aux, Bool.or_eq_true, beq_iff_eq,
            List.any_eq_true, Bool.and_eq_true, List.mem_range] using hmono
        · have hlt : f p < f b := by
            have hh := hstep
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.1.2
          exact Or.inr ⟨f p, hlt, hstep, hchain⟩

private theorem le0_map_interval_rf (A C : PS) (f : ℕ → ℕ)
    (floor cap a b : ℕ) (hafloor : floor ≤ a) (hbcap : b ≤ cap)
    (hfa : f a < Lng C) (hfb : f b < Lng C)
    (hmap : ∀ u v, floor ≤ u → v ≤ cap → nextrel0 A u v = true →
      f u = f v ∨ nextrel0 C (f u) (f v) = true)
    (h : le0 A a b = true) : le0 C (f a) (f b) = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true] at hh
  have haux := le0Aux_map_interval_rf A C f floor cap hmap
    (Lng A) a b hafloor hbcap hh.2
  have hsmall := le0Aux_bound_fseq C (Lng A) (f a) (f b) haux
  have hlarge := le0Aux_mono_fseq C (f b + 1) (Lng C) (f a) (f b)
    (by omega) hsmall
  simp [le0, hfa, hfb, hlarge]

/-- Row-zero reachability confined to one positive-shift block reflects to the
same interval in the original active slice. -/
theorem le0_oper_tiling_block_back_one (M : PS) (n q a b : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hq : q < n) (ha : a < b)
    (hb : b < Lng M - 1 - parent M 1 (Lng M - 1))
    (hreach : le0 (oper M n)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + a)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + b) = true) :
    le0 M (parent M 1 (Lng M - 1) + a)
      (parent M 1 (Lng M - 1) + b) = true := by
  let j₁ := Lng M - 1
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let f := fun u => j₀ + (u - B)
  have hb' : b < w := by simpa [j₁, j₀, w] using hb
  have hfa : f (B + a) = j₀ + a := by simp [f, B]
  have hfb : f (B + b) = j₀ + b := by simp [f, B]
  have hjaM : j₀ + a < Lng M := by simp [j₀]; omega
  have hjbM : j₀ + b < Lng M := by simp [j₀]; omega
  have hmapped := le0_map_interval_rf N M f (B + a) (B + b)
    (B + a) (B + b) (le_refl _) (le_refl _)
    (by simpa [hfa] using hjaM) (by simpa [hfb] using hjbM)
    (fun u v hBu hvB hstep => Or.inr (by
      have hdata := hstep
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdata
      have huv : u < v := hdata.1.1.2
      have hBv : B ≤ v := by omega
      let su := u - B
      let sv := v - B
      have hsu : u = B + su := by dsimp only [su]; omega
      have hsv : v = B + sv := by dsimp only [sv]; omega
      have hsusv : su < sv := by omega
      have hsvb : sv ≤ b := by omega
      have hsvw : sv < w := hsvb.trans_lt hb'
      have hr := nextrel0_oper_tiling_block_back_one M n q su sv
        hlast hzero hp hi₁ hq hsusv
        (by simpa [j₁, j₀, w] using hsvw) (by
          change nextrel0 N (B + su) (B + sv) = true
          rw [← hsu, ← hsv]
          exact hstep)
      change nextrel0 M (j₀ + su) (j₀ + sv) = true
      exact hr)) hreach
  rw [hfa, hfb] at hmapped
  exact hmapped

/-- Row-zero reachability in the original active slice lifts into every
positive-shift block. -/
theorem le0_oper_tiling_block_lift_one (M : PS) (n q a b : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hq : q < n) (ha : a < b)
    (hb : b < Lng M - 1 - parent M 1 (Lng M - 1))
    (hreach : le0 M (parent M 1 (Lng M - 1) + a)
      (parent M 1 (Lng M - 1) + b) = true) :
    le0 (oper M n)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + a)
      (parent M 1 (Lng M - 1) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) + b) = true := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let f := fun u => B + (u - j₀)
  have hi₁' : i₁ = 1 := by simpa [i₁, j₁] using hi₁
  have hj₀idx : parent M i₁ j₁ = j₀ := by simp [j₀, hi₁']
  have hb' : b < w := by simpa [j₁, j₀, w] using hb
  have hwpos : 0 < w := by omega
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w, hj₀idx] using
      length_oper_tiling M n hlast hzero hp
  have hfa : f (j₀ + a) = B + a := by simp [f]
  have hfb : f (j₀ + b) = B + b := by simp [f]
  have haN : B + a < Lng N := by rw [hlen]; simp [B]; nlinarith
  have hbN : B + b < Lng N := by rw [hlen]; simp [B]; nlinarith
  have hmapped := le0_map_interval_rf M N f (j₀ + a) (j₀ + b)
    (j₀ + a) (j₀ + b) (le_refl _) (le_refl _)
    (by simpa [hfa] using haN) (by simpa [hfb] using hbN)
    (fun u v hju hvj hstep => Or.inr (by
      have hdata := hstep
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdata
      have huv : u < v := hdata.1.1.2
      have hjv : j₀ ≤ v := by omega
      let su := u - j₀
      let sv := v - j₀
      have hsu : u = j₀ + su := by dsimp only [su]; omega
      have hsv : v = j₀ + sv := by dsimp only [sv]; omega
      have hsusv : su < sv := by omega
      have hsvb : sv ≤ b := by omega
      have hsvw : sv < w := hsvb.trans_lt hb'
      have hr := nextrel0_oper_tiling_block_lift_one M n q su sv
        hlast hzero hp hi₁ hq hsusv
        (by simpa [j₁, j₀, w] using hsvw) (by
          change nextrel0 M (j₀ + su) (j₀ + sv) = true
          rw [← hsu, ← hsv]
          exact hstep)
      change nextrel0 N (B + su) (B + sv) = true
      simpa [N, B, j₁, j₀, w] using hr)) hreach
  rw [hfa, hfb] at hmapped
  simpa [N, B, j₁, j₀, w] using hmapped

set_option maxHeartbeats 1000000 in
/-- If the row-one parent of an interior base column stays in the active
slice, its copy in every positive-shift block is the row-one parent there. -/
theorem parent_oper_tiling_interior_one (M : PS) (n q s : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hq : q < n) (hspos : 0 < s)
    (hs : s < Lng M - 1 - parent M 1 (Lng M - 1))
    (hbaseParent : hasParent M 1
      (parent M 1 (Lng M - 1) + s) = true)
    (hparentGe : parent M 1 (Lng M - 1) ≤
      parent M 1 (parent M 1 (Lng M - 1) + s)) :
    parent (oper M n) 1
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s) =
      parent M 1 (parent M 1 (Lng M - 1) + s) +
        q * (Lng M - 1 - parent M 1 (Lng M - 1)) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let xbase := j₀ + s
  let pb := parent M 1 xbase
  let sp := pb - j₀
  let x := B + s
  let c := B + sp
  have hi₁' : i₁ = 1 := by simpa [i₁, j₁] using hi₁
  have hj₀idx : parent M i₁ j₁ = j₀ := by simp [j₀, hi₁']
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  have hwpos : 0 < w := by omega
  have hbaseParent' : hasParent M 1 xbase = true := by
    simpa [xbase, j₀, j₁] using hbaseParent
  have hbaseNext : nextR M 1 pb xbase = true := by
    simpa [pb] using hasParent_next_fseq M 1 xbase hbaseParent'
  have hbaseNext1 : nextrel1 M pb xbase = true := by
    simpa [nextR] using hbaseNext
  have hbaseData := hbaseNext1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hbaseData
  have hpblt : pb < xbase := hbaseData.1.1.1.2
  have hpbge : j₀ ≤ pb := by
    simpa [pb, xbase, j₀, j₁] using hparentGe
  have hpbform : pb = j₀ + sp := by simp [sp, Nat.add_sub_of_le hpbge]
  have hsps : sp < s := by simp [xbase] at hpblt; omega
  have hspw : sp < w := hsps.trans hs'
  have hlen : Lng N = j₀ + n * w := by
    simpa [N, j₁, i₁, j₀, w, hj₀idx] using
      length_oper_tiling M n hlast hzero hp
  have hxN : x < Lng N := by rw [hlen]; simp [x, B]; nlinarith
  have hcN : c < Lng N := by rw [hlen]; simp [c, B]; nlinarith
  have hread1 (t : ℕ) (ht : t < w) :
      entry N 1 (B + t) = entry M 1 (j₀ + t) := by
    have hr := entry_oper_tiling_block_one M n q t hlast hzero hp hq
      (by simpa [j₁, i₁, j₀, w, hj₀idx] using ht)
    simpa [N, B, j₁, i₁, j₀, w, hi₁', hj₀idx,
      Nat.add_assoc] using hr
  have hreachBase : le0 M (j₀ + sp) (j₀ + s) = true := by
    simpa [hpbform, xbase] using hbaseData.1.2
  have hreach : le0 N c x = true := by
    have hr := le0_oper_tiling_block_lift_one M n q sp s
      hlast hzero hp hi₁ hq hsps hs hreachBase
    simpa [N, c, x, B, j₁, j₀, w, Nat.add_assoc] using hr
  have hstrict : entry N 1 c < entry N 1 x := by
    have hbstrict : entry M 1 pb < entry M 1 xbase :=
      hbaseData.1.1.2
    rw [hread1 sp hspw, hread1 s hs']
    simpa [hpbform, xbase] using hbstrict
  have hnext1 : nextrel1 N c x = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨hcN, hxN⟩, by simp [c, x]; omega⟩, hstrict⟩,
      hreach⟩, ?_⟩
    intro u huN
    by_cases hcu : c < u
    · by_cases hux : le0 N u x = true
      · simp only [hcu, decide_true, hux, Bool.and_self,
          Bool.not_true, Bool.false_or, decide_eq_true_eq]
        have hule : u ≤ x := le0_index_rf hux
        have hBu : B ≤ u := by simp [c, B] at hcu; omega
        let t := u - B
        have huform : u = B + t := by dsimp only [t]; omega
        have hspt : sp < t := by simp [c, huform] at hcu; omega
        have hts : t ≤ s := by simp [x, huform] at hule; omega
        by_cases hteq : t = s
        · have huxeq : u = x := by rw [huform, hteq]
          rw [huxeq]
        · have htslt : t < s := lt_of_le_of_ne hts hteq
          have htw : t < w := htslt.trans hs'
          have hreachM : le0 M (j₀ + t) (j₀ + s) = true := by
            have hr := le0_oper_tiling_block_back_one M n q t s
              hlast hzero hp hi₁ hq htslt hs (by
                change le0 N (B + t) (B + s) = true
                rw [← huform]
                simpa [x] using hux)
            simpa [j₁, j₀, w] using hr
          have hpbt : pb < j₀ + t := by rw [hpbform]; omega
          have hjtM : j₀ + t < Lng M := by simp [j₀]; omega
          have hall := hbaseData.2 (j₀ + t) hjtM
          have hreachM' : le0 M (j₀ + t) xbase = true := by
            simpa [xbase] using hreachM
          have hge : entry M 1 xbase ≤ entry M 1 (j₀ + t) := by
            simpa [hpbt, hreachM'] using hall
          rw [huform, hread1 s hs', hread1 t htw]
          simpa [xbase] using hge
      · simp [hcu, hux]
    · simp [hcu]
  have hnext : nextR N 1 c x = true := by simpa [nextR] using hnext1
  have hparent : parent N 1 x = c :=
    parent_eq_of_unique_fseq N 1 x c hnext
      (fun r hr => nextR1_unique_mr N r c x hr hnext)
  rw [hparent]
  change c = pb + q * w
  rw [hpbform]
  simp [c, B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Row-one condition (A) for a positive-shift interior column whose base
parent remains in the active slice. -/
theorem RedCondA_oper_tiling_row1_one_interior (M : PS) (n q s : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 1)
    (hA : RedCondA M = true)
    (hq : q < n) (hspos : 0 < s)
    (hs : s < Lng M - 1 - parent M 1 (Lng M - 1))
    (hbaseParent : hasParent M 1
      (parent M 1 (Lng M - 1) + s) = true)
    (hparentGe : parent M 1 (Lng M - 1) ≤
      parent M 1 (parent M 1 (Lng M - 1) + s)) :
    entry (oper M n) 1
        (parent (oper M n) 1
          (parent M 1 (Lng M - 1) +
            q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)) + 1 =
      entry (oper M n) 1
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s) := by
  let j₁ := Lng M - 1
  let j₀ := parent M 1 j₁
  let w := j₁ - j₀
  let N := oper M n
  let B := j₀ + q * w
  let xbase := j₀ + s
  let pb := parent M 1 xbase
  let sp := pb - j₀
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  have hbaseParent' : hasParent M 1 xbase = true := by
    simpa [xbase, j₀, j₁] using hbaseParent
  have hpnext : nextR M 1 pb xbase = true := by
    simpa [pb] using hasParent_next_fseq M 1 xbase hbaseParent'
  have hpblt : pb < xbase :=
    (nextR_implies_row0 M 1 pb xbase hpnext).1
  have hpbge : j₀ ≤ pb := by
    simpa [pb, xbase, j₀, j₁] using hparentGe
  have hpbform : pb = j₀ + sp := by simp [sp, Nat.add_sub_of_le hpbge]
  have hsps : sp < s := by simp [xbase] at hpblt; omega
  have hspw : sp < w := hsps.trans hs'
  have hpar := parent_oper_tiling_interior_one M n q s
    hlast hzero hp hi₁ hq hspos hs hbaseParent hparentGe
  have hxread := entry_oper_tiling_block_one M n q s
    hlast hzero hp hq (by simpa [hi₁, j₁, j₀, w] using hs')
  have hpread := entry_oper_tiling_block_one M n q sp
    hlast hzero hp hq (by simpa [hi₁, j₁, j₀, w] using hspw)
  have hbase := RedCondA_apply M hA 1 xbase (by omega)
    (by simp [xbase, j₀]; omega) hbaseParent'
  change entry N 1
      (parent N 1 (B + s)) + 1 = entry N 1 (B + s)
  rw [show parent N 1 (B + s) = pb + q * w by
    simpa [N, B, pb, xbase, j₁, j₀, w, Nat.add_assoc] using hpar]
  have hpindex : pb + q * w = j₀ + q * w + sp := by
    rw [hpbform]
    omega
  rw [hpindex]
  rw [show entry N 1 (j₀ + q * w + sp) = entry M 1 pb by
    rw [hpbform]
    simpa [N, hi₁, j₁, j₀, w, Nat.add_assoc] using hpread]
  rw [show entry N 1 (B + s) = entry M 1 xbase by
    simpa [N, B, xbase, hi₁, j₁, j₀, w, Nat.add_assoc] using hxread]
  exact hbase

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
#print axioms RedCondA_oper_tiling_row0
#print axioms RedCondA_oper_tiling_row1_zero
#print axioms le0_oper_tiling_block_back_one
#print axioms le0_oper_tiling_block_lift_one
#print axioms parent_oper_tiling_interior_one
#print axioms RedCondA_oper_tiling_row1_one_interior
#print axioms RTPS_oper_of_nonmulti_steps

end PSS
