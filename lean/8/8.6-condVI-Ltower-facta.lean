import «8».«8.4-fseq-basic»
import «7».«7.4-Trans-Mark-seg»
import «8».«8.5-exchV-props»
import «8».«8.6-Trans-fseq-condVI»

/-!
# §8.6 条件 (VI) L 塔 fact (a): 平坦 `oper` 版の基点保存

- 原文: 停止性定理の §8.6 条件 (VI) の基本列補題群（`tmp/content.md` 5484 系）の
  補助事実。ここでは Isabelle `s84c1_marked_L` の **条件 (VI) 崩壊形**（`w = 1`）を、
  scaffolding (`s84x_L`) を一切経由せず **平坦 `oper`** 上で述べ直す。
- Isabelle 対応:
  * `s84c1_marked_L`（`layerB/pss_wip.thy`:53860）= `s84c1_adm_L_mstar`（同 :53659, 120L）
    ＋ `s84c1_le0_L_mstar`（同 :53779, 81L）。
  * 崩壊事実 = `c6gx_condVI_bridge`（同 :69828, `hasParent M 1 (Lng M-1)` ＋
    `parent M 1 (Lng M-1) = Lng M-2`）＋ `c6gx_condVI_j0`（同 :69818, 指標事実）＋
    `c6zx_condVI_oper_L`（同 :72257, `M[Suc n] = s84x_L M n`）。
- 崩壊の要点（Wave-L condVI-nadm agent）: 条件 (VI) は `lastParent M + 1 = lastIdx M`
  なので隣接 `j₀ = Lng M - 2 = j₁ - 1` ⟹ `w = j₁ - j₀ = 1`、`d₁ = 0`。従って
  * ブロック内の行 1 は**定数** (`entry M 1 (Lng M-2)`) ⟹ `m*` 直前に行 1 の辺が立たない
    ⟹ `adm` は自明（Isabelle の `ccontr` は不要）。
  * ブロック内の行 0 は `entry M 0 (Lng M-2) + q·d₀`、`d₀ > 0`（`ancestor_basic_1`）
    ⟹ `le0` は `m* → m*+1` の単一 `nextrel0` 辺。
  そして `s84x_L M n = oper M (n+1)` なので `s84x_L` scaffolding は全て蒸発。
- 依存（すべて委譲・再移植なし）:
  * oper タイル展開 = `oper_tiling_expand` / `length_oper_tiling`
    / `entry_oper_tiling_block_zero` / `entry_oper_tiling_block_one`（§6.6）;
  * 親の一意性 = `hasParent_iff_unique_fseq` / `parent_eq_of_unique_fseq`
    / `hasParent_next_fseq` / `nextR_implies_row0`（§6.2）、`nextR1_unique_mr`（§6.5）、
    `nextR0_leR`（§6.4）、`ancestor_basic_1`（§5.1）、`le0_index_fseq`（§6.2）。
- 仮定は **最小** (`TPS M` ＋ `transCondVI M` ＋ `1 < Lng M - 1` ＋ `2 ≤ n`)。
  `STPS`/`RTPS`/`monoT` は不要（下流はこれらから `TPS` を供給できる）。
- 状態: ✅ GREEN（sorry 0）。公開: `s84c1_marked_L` / `s84c1_adm_L_mstar`
  / `s84c1_le0_L_mstar`（いずれも平坦 `oper` 崩壊形）。private 補助は `_fa` 接尾辞。
-/

namespace PSS

/-! ## 条件 (VI) の指標事実（Isabelle `c6gx_condVI_j0`, pss_wip.thy:69818） -/

/-- `transCondVI M` を展開して読み取る 3 事実（`lastParent = parent M 0 (Lng M-1)`）。 -/
private theorem condVI_idx_fa {M : PS} (hcond : transCondVI M = true) :
    parent M 0 (Lng M - 1) = Lng M - 2 ∧
    entry M 1 (Lng M - 2) + 1 = entry M 1 (Lng M - 1) ∧
    0 < entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  obtain ⟨⟨hpos, heq⟩, hadj⟩ := hcond
  have hp0 : parent M 0 (Lng M - 1) = Lng M - 2 := by omega
  refine ⟨hp0, ?_, hpos⟩
  rw [hp0] at heq; exact heq

/-! ## 正の親は本物の `nextR` 辺（`headD` から） -/

/-- `0 < parent M i k` なら `parent M i k` は実際に段 `i` の親（`nextR` 辺）。
`parents` は `nextR` でフィルタしたリストで、`headD 0` が正なら非空・先頭がそれ。 -/
private theorem nextR_of_parent_pos_fa (M : PS) (i k : ℕ)
    (hpos : 0 < parent M i k) : nextR M i (parent M i k) k = true := by
  have hmem : parent M i k ∈ parents M i k := by
    have hdef : parent M i k = (parents M i k).headD 0 := rfl
    cases hl : parents M i k with
    | nil => rw [hdef, hl] at hpos; simp at hpos
    | cons x xs => rw [hdef, hl]; simp
  simp only [parents, List.mem_filter] at hmem
  exact hmem.2

/-! ## 条件 (VI) の橋（Isabelle `c6gx_condVI_bridge`, pss_wip.thy:69828） -/

/-- 条件 (VI) の隣接から、最終列の行 1 の親が存在し `Lng M - 2` に一致する。 -/
private theorem condVI_bridge_fa (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    hasParent M 1 (Lng M - 1) = true ∧ parent M 1 (Lng M - 1) = Lng M - 2 := by
  obtain ⟨hp0, he1, hpos1⟩ := condVI_idx_fa hcond
  -- 行 0 の親が `Lng M - 2` である（隣接）
  have hpar0pos : 0 < parent M 0 (Lng M - 1) := by rw [hp0]; omega
  have hnext0 : nextR M 0 (Lng M - 2) (Lng M - 1) = true := by
    have h := nextR_of_parent_pos_fa M 0 (Lng M - 1) hpar0pos
    rwa [hp0] at h
  have hle0 : leR M 0 (Lng M - 2) (Lng M - 1) = true := nextR0_leR M _ _ hnext0
  have hle0' : le0 M (Lng M - 2) (Lng M - 1) = true := by simpa [leR] using hle0
  -- 行 1 の親関係 `nextrel1 M (Lng M-2) (Lng M-1)` を組み立てる
  have hnr1 : nextrel1 M (Lng M - 2) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, hle0'⟩, ?_⟩
    intro u _
    by_cases hpu : Lng M - 2 < u
    · by_cases hux : le0 M u (Lng M - 1) = true
      · have hule : u ≤ Lng M - 1 := le0_index_fseq hux
        have hueq : u = Lng M - 1 := by omega
        subst hueq
        simp [hpu, hux]
      · simp [hpu, hux]
    · simp [hpu]
  have hnextR1 : nextR M 1 (Lng M - 2) (Lng M - 1) = true := by simpa [nextR] using hnr1
  have huniq : ∀ y, nextR M 1 y (Lng M - 1) = true → y = Lng M - 2 := by
    intro y hy; exact nextR1_unique_mr M y (Lng M - 2) (Lng M - 1) hy hnextR1
  exact ⟨(hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨Lng M - 2, hnextR1, huniq⟩,
    parent_eq_of_unique_fseq M 1 (Lng M - 1) (Lng M - 2) hnextR1 huniq⟩

/-! ## `oper M N` の崩壊構造（`w = 1`）: 長さと基本列ブロックの成分 -/

/-- 条件 (VI) 下の `oper` の長さ `Lng (oper M N) = Lng M - 2 + N`（`w = 1`）。 -/
private theorem oper_len_fa (M : PS) (N : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Lng (oper M N) = Lng M - 2 + N := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_fa hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_fa M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have h := length_oper_tiling M N hlast hzero hp
  simp only [hi1] at h
  rw [hjp] at h
  rw [show Lng M - 1 - (Lng M - 2) = 1 by omega] at h
  simpa using h

/-- 行 1 はブロック内で定数（`d₁ = 0`）: `entry (oper M N) 1 (Lng M-2 + q) = entry M 1 (Lng M-2)`。 -/
private theorem oper_block1_fa (M : PS) (N q : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hq : q < N) :
    entry (oper M N) 1 (Lng M - 2 + q) = entry M 1 (Lng M - 2) := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_fa hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_fa M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have hjq : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by rw [hi1]; exact hjp
  have hw : Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) = 1 := by rw [hjq]; omega
  have hs : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by rw [hw]; omega
  have hb := entry_oper_tiling_block_one M N q 0 hlast hzero hp hq hs
  rw [hw] at hb
  rw [hjq] at hb
  simpa using hb

/-- 行 0 はブロック内で `entry M 0 (Lng M-2) + q·d₀`。 -/
private theorem oper_block0_fa (M : PS) (N q : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hq : q < N) :
    entry (oper M N) 0 (Lng M - 2 + q) =
      entry M 0 (Lng M - 2) + q * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_fa hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_fa M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have hjq : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by rw [hi1]; exact hjp
  have hw : Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) = 1 := by rw [hjq]; omega
  have hs : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by rw [hw]; omega
  have hif : (if 0 < idx1 M (Lng M - 1) then
      entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) else 0)
      = entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2) := by
    rw [if_pos (by rw [hi1]; exact Nat.zero_lt_one), hjq]
  have hb := entry_oper_tiling_block_zero M N q 0 hlast hzero hp hq hs
  rw [hif] at hb
  rw [hw] at hb
  rw [hjq] at hb
  simpa using hb

/-! ## 行 0 の差 `d₀ > 0`（Isabelle `s84c1_e0_jm2_lt`） -/

private theorem condVI_d0_pos_fa (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    entry M 0 (Lng M - 2) < entry M 0 (Lng M - 1) := by
  obtain ⟨hhp, hjp⟩ := condVI_bridge_fa M hM hcond hj₁
  have hnext1 := hasParent_next_fseq M 1 (Lng M - 1) hhp
  have hleR := (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1) hnext1).2
  rw [hjp] at hleR
  exact ancestor_basic_1 M (Lng M - 2) (Lng M - 1) (Lng M - 1) hM (by omega) (le_refl _) hleR

/-! ## 公開: `adm` 脚（Isabelle `s84c1_adm_L_mstar`, pss_wip.thy:53659, 平坦 `oper` 崩壊形） -/

/-- 条件 (VI) 崩壊形の `adm`。基点 `m* = Lng (oper M n) - 1` の行 1 が直前列と**等しい**
（ブロック内定数）ため、`m*` へ入る行 1 の辺が立たず `adm` は自明。 -/
theorem s84c1_adm_L_mstar (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 2 ≤ n) :
    adm (oper M (n + 1)) (Lng (oper M n) - 1) = true := by
  have hlen_n : Lng (oper M n) = Lng M - 2 + n := oper_len_fa M n hM hcond hj₁
  have hlen_sn : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_fa M (n + 1) hM hcond hj₁
  set ms := Lng (oper M n) - 1 with hms_def
  have hms : ms = Lng M - 2 + (n - 1) := by rw [hms_def, hlen_n]; omega
  -- 行 1 の定数性: `m*` と `m*-1` はともに `entry M 1 (Lng M-2)`
  have e_ms1 : entry (oper M (n + 1)) 1 ms = entry M 1 (Lng M - 2) := by
    rw [hms]; exact oper_block1_fa M (n + 1) (n - 1) hM hcond hj₁ (by omega)
  have e_msm1 : entry (oper M (n + 1)) 1 (ms - 1) = entry M 1 (Lng M - 2) := by
    have hpos : ms - 1 = Lng M - 2 + (n - 2) := by rw [hms]; omega
    rw [hpos]; exact oper_block1_fa M (n + 1) (n - 2) hM hcond hj₁ (by omega)
  have hrow : entry (oper M (n + 1)) 1 (ms - 1) = entry (oper M (n + 1)) 1 ms := by
    rw [e_ms1, e_msm1]
  -- `nadm = false`
  have h1 : decide (Lng (oper M (n + 1)) < ms) = false := by
    simp only [decide_eq_false_iff_not]; omega
  have h2 : nextR (oper M (n + 1)) 1 (ms - 1) ms = false := by
    by_contra hcon
    have h : nextR (oper M (n + 1)) 1 (ms - 1) ms = true := by
      cases hb : nextR (oper M (n + 1)) 1 (ms - 1) ms
      · exact absurd hb hcon
      · rfl
    simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hstrict⟩, _⟩, _⟩ := h
    rw [hrow] at hstrict
    exact absurd hstrict (lt_irrefl _)
  have hnadm : nadm (oper M (n + 1)) ms = false := by simp [nadm, h1, h2]
  simp [adm, hnadm]

/-! ## 公開: `le0` 脚（Isabelle `s84c1_le0_L_mstar`, pss_wip.thy:53779, 平坦 `oper` 崩壊形） -/

/-- 条件 (VI) 崩壊形の `le0`。`m* → m*+1` は単一 `nextrel0` 辺（行 0 が `d₀ > 0` で厳増）。 -/
theorem s84c1_le0_L_mstar (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 1 ≤ n) :
    leR (oper M (n + 1)) 0 (Lng (oper M n) - 1) (Lng (oper M (n + 1)) - 1) = true := by
  have hlen_n : Lng (oper M n) = Lng M - 2 + n := oper_len_fa M n hM hcond hj₁
  have hlen_sn : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_fa M (n + 1) hM hcond hj₁
  have hd0 : entry M 0 (Lng M - 2) < entry M 0 (Lng M - 1) := condVI_d0_pos_fa M hM hcond hj₁
  set d := entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2) with hd_def
  have hdpos : 0 < d := by rw [hd_def]; omega
  set ms := Lng (oper M n) - 1 with hms_def
  have hms : ms = Lng M - 2 + (n - 1) := by rw [hms_def, hlen_n]; omega
  have hlastidx : Lng (oper M (n + 1)) - 1 = ms + 1 := by rw [hlen_sn, hms]; omega
  rw [hlastidx]
  -- 行 0 の値
  have e_ms : entry (oper M (n + 1)) 0 ms = entry M 0 (Lng M - 2) + (n - 1) * d := by
    rw [hms]; exact oper_block0_fa M (n + 1) (n - 1) hM hcond hj₁ (by omega)
  have e_ms1 : entry (oper M (n + 1)) 0 (ms + 1) = entry M 0 (Lng M - 2) + n * d := by
    have hpos : ms + 1 = Lng M - 2 + n := by rw [hms]; omega
    rw [hpos]; exact oper_block0_fa M (n + 1) n hM hcond hj₁ (by omega)
  -- `n·d = (n-1)·d + d`
  have hd_eq : (n - 1) * d + d = n * d := by
    have hn1 : (n - 1) + 1 = n := by omega
    calc (n - 1) * d + d = (n - 1) * d + 1 * d := by rw [Nat.one_mul]
      _ = ((n - 1) + 1) * d := by rw [Nat.add_mul]
      _ = n * d := by rw [hn1]
  -- 単一 `nextrel0` 辺
  have hnr0 : nextrel0 (oper M (n + 1)) ms (ms + 1) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩, ?_⟩
    · rw [e_ms, e_ms1]; omega
    · intro j hj
      have hnlt : ¬ (ms < j) := by omega
      simp [hnlt]
  have hnextR0 : nextR (oper M (n + 1)) 0 ms (ms + 1) = true := by simpa [nextR] using hnr0
  exact nextR0_leR (oper M (n + 1)) ms (ms + 1) hnextR0

/-! ## 公開: 主 fact (a)（Isabelle `s84c1_marked_L`, pss_wip.thy:53860, 平坦 `oper` 崩壊形） -/

/-- **条件 (VI) L 塔 fact (a)**: 平坦 `oper` 上で `(oper M (n+1), Lng (oper M n) - 1) ∈ Marked`。
Isabelle `s84c1_marked_L` の `w = 1` 崩壊形（`s84x_L M n = oper M (n+1)` を経由せず直接）。 -/
theorem s84c1_marked_L (M : PS) (n : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) (hn : 2 ≤ n) :
    Marked (oper M (n + 1)) (Lng (oper M n) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have hlen_sn : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) :=
      oper_len_fa M (n + 1) hM hcond hj₁
    have hpos : 0 < Lng (oper M (n + 1)) := by rw [hlen_sn]; omega
    exact List.ne_nil_of_length_pos hpos
  · exact s84c1_adm_L_mstar M n hM hcond hj₁ hn
  · exact s84c1_le0_L_mstar M n hM hcond hj₁ (by omega)

#print axioms s84c1_adm_L_mstar
#print axioms s84c1_le0_L_mstar
#print axioms s84c1_marked_L

end PSS
