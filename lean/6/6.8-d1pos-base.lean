import «6».«6.8-standard-slice-Br-descending»
import «5».«5.1-ancestor-tree»

/-!
# §6.8 d1pos 基礎 brick（ブロック幾何と le0 背骨）

- 原文: `tmp/content.md` L1472–1545 付近（§6.8 証明本体の `i₁=1`（d1pos）ケース。
  LOW 切片の同定・ブロック開始点の行 0 到達性・切片の単項性）
- 訂正: なし（タイル展開の係数は訂正 A8 適用後の `*_68`/tiling 資産に依拠）
- Isabelle: `oper_d1pos_LOW_source_eq` (isabelle/pss_mechanized.thy:9780),
  `oper_d1pos_le0_confined` (同:10234), `oper_d1pos_entry0_boundary` (同:10266),
  `oper_d1pos_nextrel0_transfer` (同:10313), `oper_d1pos_block_chain` (同:10443),
  `oper_d1pos_le0_blockstarts` (同:10538), `oper_d1pos_seg_mono` (同:10593)
- 依存: «6».«6.8-standard-slice-Br-descending»（d1pos 読み出し `*_68` 群・
  `monoT_seg_of_le0_68`）, «5».«5.1-ancestor-tree»（`row0_transitive`）,
  «5».«5.1-ancestor-basic»（`ancestor_basic_1`）,
  «5».«5.1-parent-exists»（`parent_exists_3`）
- 状態: ✅ 証明済（sorry 0）

le0/nextrel0 系は Isabelle の rtrancl 持ち上げを使わず、値特徴付け
（`ancestor_basic_1` ＋ entry 一致 ＋ `parent_exists_3`）で構成する
（8.3-kind0-base-basepoint と同じ勝ち筋）。
-/

namespace PSS

/-! ## 補助（`le0` の反射律・基底 `le0 M j₀ j₁`） -/

private theorem le0Aux_refl_db (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_db (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_db]

/-- The base row-0 reachability `j₀ ≤₀ j₁` in `M`, from the row-1 parent
relation at the last column. -/
private theorem leR_base_db (M : PS)
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1) :
    leR M 0 (parent M 1 (Lng M - 1)) (Lng M - 1) = true := by
  have hnext := hasParent_next_fseq M (idx1 M (Lng M - 1)) (Lng M - 1) hp
  rw [hi] at hnext
  exact (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1) hnext).2

/-! ## LOW 切片の同定（原文の LOW source 分解） -/

/-- §6.8 (a): a slice of `M[n]` lying inside one period block `q` is the
corresponding base slice of `M` with every row-0 entry shifted by `q·δ`. -/
theorem oper_d1pos_LOW_source_eq
    (M : PS) (n q s₀ e₀ : ℕ) (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (_hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hq : q < n) (hse : s₀ ≤ e₀)
    (he : e₀ < Lng M - 1 - parent M 1 (Lng M - 1)) :
    seg (oper M n)
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s₀)
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e₀) =
      IncrFirstN
        (q * (entry M 0 (Lng M - 1) -
          entry M 0 (parent M 1 (Lng M - 1))))
        (seg M (parent M 1 (Lng M - 1) + s₀)
          (parent M 1 (Lng M - 1) + e₀)) :=
  seg_oper_d1pos_block_eq_68 M n q s₀ e₀ hlen hzero hp hi hq hse he

/-! ## 行 0 鎖の単調閉じ込め -/

/-- §6.8 d1pos confinement: a row-0 ancestor chain of `M[n]` is monotone in
index and in row-0 value, and stays inside the sequence.  (The d0zero-style
single-block confinement is FALSE here; this monotone bound is the strongest
true form.) -/
theorem oper_d1pos_le0_confined
    (M : PS) (n a b : ℕ) (_hlen : 1 < Lng M)
    (_hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (_hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (_hi : idx1 M (Lng M - 1) = 1)
    (_ha : parent M 1 (Lng M - 1) ≤ a)
    (_halt : a < Lng (oper M n))
    (hab : leR (oper M n) 0 a b = true) :
    a ≤ b ∧ entry (oper M n) 0 a ≤ entry (oper M n) 0 b ∧
      (a < b → b < Lng (oper M n)) := by
  have h0 : le0 (oper M n) a b = true := by simpa [leR] using hab
  have hh := h0
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haN : a < Lng (oper M n) := hh.1.1
  have hbN : b < Lng (oper M n) := hh.1.2
  have hidx : a ≤ b := le0Aux_index_fseq hh.2
  refine ⟨hidx, ?_, fun _ => hbN⟩
  rcases Nat.eq_or_lt_of_le hidx with heq | hlt
  · subst heq
    exact le_rfl
  · have hMn : TPS (oper M n) :=
      List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le a) haN)
    exact (ancestor_basic_1 (oper M n) a b b hMn hlt le_rfl hab).le

/-! ## ブロック境界の行 0 値 -/

/-- §6.8 d1pos row-0 value at the start of block `k + 1` (the right boundary
of block `k`): it is the last column's row-0 value shifted by `k·δ`. -/
theorem oper_d1pos_entry0_boundary
    (M : PS) (n k : ℕ) (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hk1 : k + 1 < n) :
    entry (oper M n) 0
        (parent M 1 (Lng M - 1) +
          (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1))) =
      entry M 0 (Lng M - 1) +
        k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by
  have hM : TPS M := List.ne_nil_of_length_pos (Nat.zero_lt_one.trans hlen)
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hread := entry_oper_d1pos_zero_68 M n (k + 1) 0 hlen hzero hp hi hk1 hw
  have hread' : entry (oper M n) 0
      (parent M 1 (Lng M - 1) +
        (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1))) =
      entry M 0 (parent M 1 (Lng M - 1)) +
        (k + 1) * (entry M 0 (Lng M - 1) -
          entry M 0 (parent M 1 (Lng M - 1))) := by
    simpa using hread
  have hδ : entry M 0 (parent M 1 (Lng M - 1)) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (parent M 1 (Lng M - 1)) (Lng M - 1) (Lng M - 1) hM
      hj₀lt le_rfl (leR_base_db M hp hi)
  have hsucc : (k + 1) * (entry M 0 (Lng M - 1) -
      entry M 0 (parent M 1 (Lng M - 1))) =
    k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) +
      (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) :=
    Nat.succ_mul k _
  rw [hread', hsucc]
  omega

/-! ## 行 0 一段親子関係のブロック `k` への転送 -/

/-- §6.8 d1pos `nextrel0` transfer: a base row-0 step of `M` inside the
period slice lifts verbatim into block `k` of `M[n]` (row 0 is shifted by the
constant `k·δ`, which preserves the strict-increase and valley conditions).
The right endpoint may be the block boundary `y = Lng M - 1`, whence
`k + 1 < n`. -/
theorem oper_d1pos_nextrel0_transfer
    (M : PS) (n k x y : ℕ) (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hk1 : k + 1 < n)
    (hxlo : parent M 1 (Lng M - 1) ≤ x)
    (hyhi : y ≤ Lng M - 1)
    (hstep : nextrel0 M x y = true) :
    nextrel0 (oper M n)
        (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
          (x - parent M 1 (Lng M - 1)))
        (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
          (y - parent M 1 (Lng M - 1))) = true := by
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hkw : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.succ_mul k _
  have hmul : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) <
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    mul_lt_mul_of_pos_right (by omega) hw
  have hlenN : Lng (oper M n) = parent M 1 (Lng M - 1) +
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    length_oper_d1pos_68 M n hlen hzero hp hi
  -- decode the base step
  have hdata := hstep
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hdata
  have hxy : x < y := hdata.1.1.2
  have hstrict : entry M 0 x < entry M 0 y := hdata.1.2
  have hvalley : ∀ u, x < u → u < y → entry M 0 y ≤ entry M 0 u := by
    intro u hxu huy
    have hu := hdata.2 u (List.mem_range.mpr huy)
    simpa [hxu] using hu
  have hxw : x - parent M 1 (Lng M - 1) <
      Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hyw : y - parent M 1 (Lng M - 1) ≤
      Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  -- row-0 reading at the transferred endpoints
  have hex : entry (oper M n) 0
      (parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (x - parent M 1 (Lng M - 1))) =
      entry M 0 x + k * (entry M 0 (Lng M - 1) -
        entry M 0 (parent M 1 (Lng M - 1))) := by
    have h := entry_oper_d1pos_zero_68 M n k (x - parent M 1 (Lng M - 1))
      hlen hzero hp hi (by omega) hxw
    rwa [show parent M 1 (Lng M - 1) + (x - parent M 1 (Lng M - 1)) = x by
      omega] at h
  have hey : entry (oper M n) 0
      (parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (y - parent M 1 (Lng M - 1))) =
      entry M 0 y + k * (entry M 0 (Lng M - 1) -
        entry M 0 (parent M 1 (Lng M - 1))) := by
    rcases Nat.lt_or_ge y (Lng M - 1) with hylt | hyge
    · have hyw' : y - parent M 1 (Lng M - 1) <
          Lng M - 1 - parent M 1 (Lng M - 1) := by omega
      have h := entry_oper_d1pos_zero_68 M n k (y - parent M 1 (Lng M - 1))
        hlen hzero hp hi (by omega) hyw'
      rwa [show parent M 1 (Lng M - 1) + (y - parent M 1 (Lng M - 1)) = y by
        omega] at h
    · have hyeq : y = Lng M - 1 := by omega
      have hidx : parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
          (y - parent M 1 (Lng M - 1)) =
        parent M 1 (Lng M - 1) +
          (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) := by omega
      rw [hidx, hyeq]
      exact oper_d1pos_entry0_boundary M n k hlen hzero hp hi hj₀lt hk1
  -- index bounds
  have htxN : parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
      (x - parent M 1 (Lng M - 1)) < Lng (oper M n) := by
    rw [hlenN]; omega
  have htyN : parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
      (y - parent M 1 (Lng M - 1)) < Lng (oper M n) := by
    rw [hlenN]; omega
  -- assemble the transferred step
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨htxN, htyN⟩, by omega⟩, ?_⟩, ?_⟩
  · rw [hex, hey]
    omega
  · intro u hu
    by_cases hau : parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (x - parent M 1 (Lng M - 1)) < u
    · simp only [hau, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq]
      have ht1 : x - parent M 1 (Lng M - 1) <
          u - (parent M 1 (Lng M - 1) +
            k * (Lng M - 1 - parent M 1 (Lng M - 1))) := by omega
      have ht2 : u - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1))) <
          y - parent M 1 (Lng M - 1) := by omega
      have hzu := entry_oper_d1pos_zero_68 M n k
        (u - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1))))
        hlen hzero hp hi (by omega) (by omega)
      rw [show parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
          (u - (parent M 1 (Lng M - 1) +
            k * (Lng M - 1 - parent M 1 (Lng M - 1)))) = u by omega] at hzu
      rw [hey, hzu]
      have hval := hvalley (parent M 1 (Lng M - 1) +
        (u - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)))))
        (by omega) (by omega)
      omega
    · simp [hau]

/-! ## 隣接ブロック開始点の行 0 到達性 -/

/-- §6.8 d1pos inter-block row-0 ancestry (article L1530–1538): consecutive
block starts of `M[n]` are row-0 ancestors.  Proved by the value
characterization (`parent_exists_3`): every index strictly inside
`(j₀+k·w, j₀+(k+1)·w]` reads a base value `> M₀,j₀` shifted by `k·δ`, and the
boundary itself carries the extra `δ > 0`. -/
theorem oper_d1pos_block_chain
    (M : PS) (n k : ℕ) (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hk1 : k + 1 < n) :
    leR (oper M n) 0
        (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)))
        (parent M 1 (Lng M - 1) +
          (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1))) = true := by
  have hM : TPS M := List.ne_nil_of_length_pos (Nat.zero_lt_one.trans hlen)
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hkw : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.succ_mul k _
  have hmul : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) <
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    mul_lt_mul_of_pos_right (by omega) hw
  have hlenN : Lng (oper M n) = parent M 1 (Lng M - 1) +
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    length_oper_d1pos_68 M n hlen hzero hp hi
  have hMn : TPS (oper M n) :=
    List.ne_nil_of_length_pos (show 0 < Lng (oper M n) by rw [hlenN]; omega)
  have hbase : leR M 0 (parent M 1 (Lng M - 1)) (Lng M - 1) = true :=
    leR_base_db M hp hi
  have hstart : entry (oper M n) 0
      (parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1))) =
      entry M 0 (parent M 1 (Lng M - 1)) +
        k * (entry M 0 (Lng M - 1) -
          entry M 0 (parent M 1 (Lng M - 1))) := by
    have h := entry_oper_d1pos_zero_68 M n k 0 hlen hzero hp hi (by omega) hw
    simpa using h
  apply parent_exists_3 (oper M n) _ _ hMn (by omega) (by rw [hlenN]; omega)
  intro j hj1 hj2
  rw [hstart]
  rcases Nat.lt_or_ge (j - (parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1))))
      (Lng M - 1 - parent M 1 (Lng M - 1)) with htw | htw
  · -- strictly inside block `k`: base value shifted by `k·δ`
    have hread := entry_oper_d1pos_zero_68 M n k
      (j - (parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1))))
      hlen hzero hp hi (by omega) htw
    rw [show parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (j - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)))) = j by omega] at hread
    rw [hread]
    have hgrow := ancestor_basic_1 M (parent M 1 (Lng M - 1))
      (parent M 1 (Lng M - 1) +
        (j - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)))))
      (Lng M - 1) hM (by omega) (by omega) hbase
    omega
  · -- the boundary `j = j₀ + (k+1)·w`: extra `δ > 0`
    have hjeq : j = parent M 1 (Lng M - 1) +
        (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) := by omega
    rw [hjeq, oper_d1pos_entry0_boundary M n k hlen hzero hp hi hj₀lt hk1]
    have hδ : entry M 0 (parent M 1 (Lng M - 1)) < entry M 0 (Lng M - 1) :=
      ancestor_basic_1 M (parent M 1 (Lng M - 1)) (Lng M - 1) (Lng M - 1) hM
        hj₀lt le_rfl hbase
    omega

/-! ## ブロック 0 開始点から任意ブロック開始点への到達性 -/

/-- §6.8 d1pos transitive inter-block reachability (article L1530–1545):
`j₀` row-0-reaches every later block start `j₀ + k·w` of `M[n]`, `k < n`.
Induction on `k`, composing `oper_d1pos_block_chain` via `row0_transitive`. -/
theorem oper_d1pos_le0_blockstarts
    (M : PS) (n k : ℕ) (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n) :
    leR (oper M n) 0 (parent M 1 (Lng M - 1))
        (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1))) = true := by
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hlenN : Lng (oper M n) = parent M 1 (Lng M - 1) +
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    length_oper_d1pos_68 M n hlen hzero hp hi
  have hnw : 0 < n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.mul_pos (by omega) hw
  have hj₀N : parent M 1 (Lng M - 1) < Lng (oper M n) := by
    rw [hlenN]; omega
  have hMn : TPS (oper M n) :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hj₀N)
  have main : ∀ m, m < n → leR (oper M n) 0 (parent M 1 (Lng M - 1))
      (parent M 1 (Lng M - 1) +
        m * (Lng M - 1 - parent M 1 (Lng M - 1))) = true := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using leR0_refl_db (oper M n) (parent M 1 (Lng M - 1)) hj₀N
    | succ m ih =>
        intro hsm
        exact row0_transitive (oper M n) _ _ _ hMn (ih (by omega))
          (oper_d1pos_block_chain M n m hlen hzero hp hi hj₀lt (by omega))
  exact main k hkn

/-! ## 到達切片の単項性（H1 brick） -/

/-- §6.8 d1pos H1 brick: a block-start-anchored `le0` slice of a d1pos
fundamental sequence is a single `monoT` component. -/
theorem oper_d1pos_seg_mono
    (M : PS) (n q a b : ℕ) (_hlen : 1 < Lng M)
    (_hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (_hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (_hi : idx1 M (Lng M - 1) = 1)
    (_hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (_haq : a = parent M 1 (Lng M - 1) +
      q * (Lng M - 1 - parent M 1 (Lng M - 1)))
    (_hqn : q < n)
    (hab : a < b) (hblt : b < Lng (oper M n))
    (hleab : leR (oper M n) 0 a b = true) :
    monoT (seg (oper M n) a b) = true :=
  monoT_seg_of_le0_68 (oper M n) a b hblt hab (by simpa [leR] using hleab)

#print axioms oper_d1pos_LOW_source_eq
#print axioms oper_d1pos_le0_confined
#print axioms oper_d1pos_entry0_boundary
#print axioms oper_d1pos_nextrel0_transfer
#print axioms oper_d1pos_block_chain
#print axioms oper_d1pos_le0_blockstarts
#print axioms oper_d1pos_seg_mono

end PSS
