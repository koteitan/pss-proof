import «6».«6.6-reduced-fseq»
import «6».«6.2-P-fseq»
import «6».«6.5-Red-le-core»
import «6».«6.6-reduced-leftend»
import «5».«5.1-ancestor-basic»
import PSS.Adm

/-!
# §8.3 補題（第 `0` 種型基本列の基本分岐規則）

- 原文: `tmp/content.md` 3984 付近
- 訂正: なし
- Isabelle: `p_8_3_kind0_branch_rule` (isabelle/pss_paper.thy:1813) の証明は
             `m_8_3_kind0_branch_rule` (isabelle/layerB/pss_wip.thy:16920)
- 依存: `6.6-reduced-fseq`（タイル読み出し）、`6.2-P-fseq`、`6.5-Red-le-core`
  （`le0_adjacent`）、`6.6-reduced-leftend`（`RTPS_TPS`）、`5.1-ancestor-basic`、`PSS.Adm`
- 状態: ✅ 証明済（sorry 0）

`j₀` が非 `M` 許容なら行 1 の親子辺 `(1,j₀-1) <^Next (1,j₀)` が立ち、`le0` 隣接性から
行 0 の辺も立つ。`M[n]` のブロック開始 `j₀+q·w` は `M_{j₀}` の逐語コピー、`j₀-1` は
接頭辞の逐語コピーなので両行の親子辺が `M[n]` に持ち上がる。行 0 の谷はブロック開始の
行 0 最小性、行 1 の谷は「ブロック開始の `le0` 祖先で `j₀-1` を超えるものは自分自身だけ」
という閉じ込め（Isabelle `oper_d0zero_le0_confined`）で空虚に潰す。
-/

namespace PSS

/-- `nextrel0` 1 段は `le0`（Isabelle `r_into_rtranclp` 相当）。 -/
private theorem le0_of_nextrel0_83 (M : PS) (a b : ℕ)
    (h : nextrel0 M a b = true) : le0 M a b = true := by
  have hh := (nextR_implies_row0 M 0 a b (by simpa [nextR] using h)).2
  simpa [leR] using hh

/-- `le0` は添字を増やす。 -/
private theorem le0_index_mono_83 (M : PS) (a b : ℕ)
    (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_index_fseq h.2

/-- kind-0 の閉じ込め: `oper M n` 上の `le0 a b`（`a ≥ j₀`）は `a` のブロックを
右に越えられない（`6.8-standard-slice-Br-descending` の private 補題の複製）。 -/
private theorem oper_d0zero_le0_confined_83
    (N : PS) (n a b : ℕ) (hNT : TPS N)
    (hNlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (ha : parent N 0 (Lng N - 1) ≤ a)
    (hle : leR (oper N n) 0 a b = true) :
    b < parent N 0 (Lng N - 1) +
      ((a - parent N 0 (Lng N - 1)) /
          (Lng N - 1 - parent N 0 (Lng N - 1)) + 1) *
        (Lng N - 1 - parent N 0 (Lng N - 1)) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let q := (a - j₀) / w
  let B := j₀ + (q + 1) * w
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext := hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hdata := hle
  simp only [leR, if_pos, le0, Bool.and_eq_true,
    decide_eq_true_eq] at hdata
  have haL : a < Lng (oper N n) := hdata.1.1
  have hbL : b < Lng (oper N n) := hdata.1.2
  have hoperT : TPS (oper N n) :=
    List.ne_nil_of_length_pos ((Nat.zero_le a).trans_lt haL)
  have hj₀a : j₀ ≤ a := by simpa [j₀, j₁] using ha
  have hdiv : q * w + (a - j₀) % w = a - j₀ := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_add_mod (a - j₀) w
  have haform : a = j₀ + q * w + (a - j₀) % w := by
    have hsub := Nat.add_sub_of_le hj₀a
    omega
  have hrem : (a - j₀) % w < w := Nat.mod_lt _ hw
  have haB : a < B := by
    simp [B, Nat.add_mul]
    omega
  by_contra hnot
  have hBb : B ≤ b := by
    change ¬b < B at hnot
    omega
  have hBL : B < Lng (oper N n) := hBb.trans_lt hbL
  have hlen : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hNlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  have hq : q + 1 < n := by
    rw [hlen] at hBL
    simp [B, Nat.add_mul] at hBL
    nlinarith
  have hBentry : entry (oper N n) 0 B = entry N 0 j₀ := by
    have hh := entry_oper_tiling_block_zero N n (q + 1) 0
      hNlen hzero hp hq (by
        rw [hi]
        simpa [j₁, j₀, w] using hw)
    rw [hi] at hh
    simpa [B, j₁, j₀, w, Nat.add_assoc] using hh
  have hafloor : entry N 0 j₀ ≤ entry (oper N n) 0 a := by
    have hh := oper_tiling_block_floor N n a hNT hNlen hzero hp
      (by rw [hi]; simpa [j₁, j₀] using ha) haL
    rw [hi] at hh
    simpa [j₁, j₀] using hh
  have hgrowth : entry (oper N n) 0 a < entry (oper N n) 0 B :=
    ancestor_basic_1 (oper N n) a B b hoperT haB hBb hle
  rw [hBentry] at hgrowth
  omega

/-- 補題（第 `0` 種型基本列の基本分岐規則）。 -/
theorem kind0_branch_rule (M : PS) (n q : ℕ)
    (hMR : RTPS M) (hn : 0 < n)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (he1 : entry M 1 (Lng M - 1) = 0)
    (hq : q ≤ n - 1)
    (hnadm : adm M (parent M 0 (Lng M - 1)) = false) :
    nextR (oper M n) 0 (parent M 0 (Lng M - 1) - 1)
        (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true
      ∧ nextR (oper M n) 1 (parent M 0 (Lng M - 1) - 1)
        (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
  have hMT : TPS M := RTPS_TPS M hMR
  have hi : idx1 M (Lng M - 1) = 0 := by simp [idx1, he1]
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    rw [hi]; exact hp0
  have hnext0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hasParent_next_fseq M 0 (Lng M - 1) hp0
  have hdec := hnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdec
  have hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1 := hdec.1.1.2
  have he0j₀ : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := hdec.1.2
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by omega
  have hqn : q < n := by omega
  have hw : 0 < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hj₀Lng : parent M 0 (Lng M - 1) < Lng M := by omega
  -- 非許容性 → 行 1 の基底辺 `(1,j₀-1) <^Next (1,j₀)`
  have hnadm' : nadm M (parent M 0 (Lng M - 1)) = true := by
    simpa [adm] using hnadm
  have hnr1 : nextR M 1 (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1)) = true := by
    have hh := hnadm'
    simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hh
    rcases hh with h | h
    · omega
    · exact h.1
  have hnr1' : nextrel1 M (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1)) = true := by
    simpa [nextR] using hnr1
  have hdec1 := hnr1'
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdec1
  have hj₀pos : 0 < parent M 0 (Lng M - 1) := by
    have := hdec1.1.1.1.2
    omega
  have he1base : entry M 1 (parent M 0 (Lng M - 1) - 1)
      < entry M 1 (parent M 0 (Lng M - 1)) := hdec1.1.1.2
  have hle0base : le0 M (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1)) = true :=
    hdec1.1.2
  -- 行 0 の基底辺は `le0` 隣接性から
  have hnr0base : nextrel0 M (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1)) = true := by
    have heq : parent M 0 (Lng M - 1) - 1 + 1 = parent M 0 (Lng M - 1) := by omega
    have hb : le0 M (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1) - 1 + 1) = true := by
      rw [heq]; exact hle0base
    have hstep := le0_adjacent M (parent M 0 (Lng M - 1) - 1) hb
    rwa [heq] at hstep
  have he0base : entry M 0 (parent M 0 (Lng M - 1) - 1)
      < entry M 0 (parent M 0 (Lng M - 1)) := by
    have hh := hnr0base
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  -- 長さと添字の範囲
  have hqw : q * ((Lng M - 1) - parent M 0 (Lng M - 1))
      < n * ((Lng M - 1) - parent M 0 (Lng M - 1)) :=
    mul_lt_mul_of_pos_right hqn hw
  have hlen : Lng (oper M n) = parent M 0 (Lng M - 1)
      + n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    simpa [hi] using length_oper_tiling M n hlast hzero hp
  have hidxlt : parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))
      < Lng (oper M n) := by
    rw [hlen]; omega
  have hpm1Mn : parent M 0 (Lng M - 1) - 1 < Lng (oper M n) := by
    rw [hlen]; omega
  -- 読み出し: 接頭辞 `j₀-1` は逐語、ブロック開始 `j₀+q·w` は `M_{j₀}` の逐語コピー
  have hepm1 : ∀ i, entry (oper M n) i (parent M 0 (Lng M - 1) - 1)
      = entry M i (parent M 0 (Lng M - 1) - 1) := by
    intro i
    exact entry_oper_tiling_prefix M n i (parent M 0 (Lng M - 1) - 1) hlast hzero hp
      (by rw [hi]; omega)
  have heidx0 : entry (oper M n) 0
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      = entry M 0 (parent M 0 (Lng M - 1)) := by
    have hh := entry_oper_tiling_block_zero M n q 0 hlast hzero hp hqn
      (by rw [hi]; omega)
    rw [hi] at hh
    simpa using hh
  have heidx1 : entry (oper M n) 1
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      = entry M 1 (parent M 0 (Lng M - 1)) := by
    have hh := entry_oper_tiling_block_one M n q 0 hlast hzero hp hqn
      (by rw [hi]; omega)
    rw [hi] at hh
    simpa using hh
  -- ブロック床: `x ≥ j₀` の行 0 値は `M_{0,j₀}` 以上
  have hgemin : ∀ x, parent M 0 (Lng M - 1) ≤ x → x < Lng (oper M n) →
      entry M 0 (parent M 0 (Lng M - 1)) ≤ entry (oper M n) 0 x := by
    intro x hx hxL
    have hh := oper_tiling_block_floor M n x hMT hlast hzero hp
      (by rw [hi]; exact hx) hxL
    rw [hi] at hh
    exact hh
  -- ======== 行 0 ========
  have row0 : nextrel0 (oper M n) (parent M 0 (Lng M - 1) - 1)
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hpm1Mn, hidxlt⟩, by omega⟩, ?_⟩, ?_⟩
    · rw [hepm1 0, heidx0]; exact he0base
    · rw [List.all_eq_true]
      intro j hjmem
      have hjlt : j < parent M 0 (Lng M - 1)
          + q * ((Lng M - 1) - parent M 0 (Lng M - 1)) := List.mem_range.mp hjmem
      by_cases hgt : parent M 0 (Lng M - 1) - 1 < j
      · have hge : parent M 0 (Lng M - 1) ≤ j := by omega
        have hjL : j < Lng (oper M n) := by omega
        have hfloor := hgemin j hge hjL
        have hval : entry (oper M n) 0
            (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
            ≤ entry (oper M n) 0 j := by
          rw [heidx0]; exact hfloor
        simp [hval]
      · simp [hgt]
  -- 行 0 の 1 段 → `le0`（行 1 の直系先祖条件に使う）
  have hle0full : le0 (oper M n) (parent M 0 (Lng M - 1) - 1)
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true :=
    le0_of_nextrel0_83 _ _ _ row0
  -- ======== 行 1 の谷の空虚性 ========
  -- `j₀-1` を超えるブロック開始の `le0` 祖先は自分自身だけ
  have valley_eq : ∀ j, parent M 0 (Lng M - 1) - 1 < j →
      le0 (oper M n) j
        (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true →
      j = parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    intro j hgt hle
    have hge : parent M 0 (Lng M - 1) ≤ j := by omega
    have hjle : j ≤ parent M 0 (Lng M - 1)
        + q * ((Lng M - 1) - parent M 0 (Lng M - 1)) := le0_index_mono_83 _ _ _ hle
    have hleR : leR (oper M n) 0 j
        (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
      simpa [leR] using hle
    have hconf := oper_d0zero_le0_confined_83 M n j
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      hMT hlast hzero hp hi hge hleR
    -- 商 `qj` と剰余 `sj` に分解し、`qj = q` → `sj = 0` → `j = j₀+q·w`
    have hdm := Nat.div_add_mod (j - parent M 0 (Lng M - 1))
      ((Lng M - 1) - parent M 0 (Lng M - 1))
    rw [Nat.mul_comm] at hdm
    -- hdm : qj * w + sj = j - j₀
    have hlt1 : q * ((Lng M - 1) - parent M 0 (Lng M - 1))
        < ((j - parent M 0 (Lng M - 1)) / ((Lng M - 1) - parent M 0 (Lng M - 1)) + 1)
          * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
    have hqle : q ≤ (j - parent M 0 (Lng M - 1))
        / ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
      have hcancel := lt_of_mul_lt_mul_right hlt1 (Nat.zero_le _)
      omega
    have hle1 : ((j - parent M 0 (Lng M - 1)) / ((Lng M - 1) - parent M 0 (Lng M - 1)))
          * ((Lng M - 1) - parent M 0 (Lng M - 1))
        ≤ q * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
    have hqge : (j - parent M 0 (Lng M - 1))
        / ((Lng M - 1) - parent M 0 (Lng M - 1)) ≤ q :=
      le_of_mul_le_mul_right hle1 hw
    have hqeq : (j - parent M 0 (Lng M - 1))
        / ((Lng M - 1) - parent M 0 (Lng M - 1)) = q := by omega
    rw [hqeq] at hdm
    omega
  -- ======== 行 1 ========
  have row1 : nextrel1 (oper M n) (parent M 0 (Lng M - 1) - 1)
      (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨hpm1Mn, hidxlt⟩, by omega⟩, ?_⟩, hle0full⟩, ?_⟩
    · rw [hepm1 1, heidx1]; exact he1base
    · rw [List.all_eq_true]
      intro j hjmem
      by_cases hcase : parent M 0 (Lng M - 1) - 1 < j ∧ le0 (oper M n) j
          (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true
      · have hjeq := valley_eq j hcase.1 hcase.2
        simp [hjeq]
      · rcases not_and_or.mp hcase with h | h
        · simp [h]
        · have h' : le0 (oper M n) j
              (parent M 0 (Lng M - 1)
                + q * ((Lng M - 1) - parent M 0 (Lng M - 1))) = false := by
            revert h; simp
          simp [h']
  exact ⟨by simpa [nextR] using row0, by simpa [nextR] using row1⟩

/-! ## 回帰ベクトル -/

private def cexBR_83 : PS := [(0,0),(1,1),(2,2),(3,1),(2,0)]

#guard reduced cexBR_83
#guard hasParent cexBR_83 0 (Lng cexBR_83 - 1)
#guard entry cexBR_83 1 (Lng cexBR_83 - 1) == 0
#guard parent cexBR_83 0 (Lng cexBR_83 - 1) == 1
#guard !adm cexBR_83 1
-- 結論 (n=2): q=0 → idx=1、q=1 → idx=4。両行とも (i,0) <^Next (i,idx)
#guard nextR (oper cexBR_83 2) 0 0 1
#guard nextR (oper cexBR_83 2) 1 0 1
#guard nextR (oper cexBR_83 2) 0 0 4
#guard nextR (oper cexBR_83 2) 1 0 4

#print axioms kind0_branch_rule

end PSS
