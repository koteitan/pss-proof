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
#print axioms RTPS_oper_of_nonmulti_steps

end PSS
