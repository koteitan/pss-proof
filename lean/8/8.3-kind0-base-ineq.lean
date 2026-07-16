import «6».«6.6-reduced-fseq»
import «6».«6.2-P-fseq»

/-!
# §8.3 補題（第 `0` 種型基本列の基本不等式）

- 原文: `tmp/content.md` 3972 付近
- 訂正: **A22**（軽微）— 原文の結論の右辺添字は `q'(j₁-j₀)+r'` だが、原文自身の証明は
  `j₀+q'(j₁-j₀)+r'` を使っている（`j₀+` の脱落）。ここでは訂正後（証明側）の添字を証明し、
  原文の添字のままでは偽であることを反例 `M=(9,0)(0,0)(1,1)(2,1)(1,0)`, `n=2` で機械検証する。
- Isabelle: `p_8_3_kind0_base_ineq` (isabelle/pss_paper.thy:1795) の証明は
             `m_8_3_kind0_base_ineq` (isabelle/layerB/pss_wip.thy:13700)
- 依存: `6.6-reduced-fseq`（`oper` タイル展開の読み出し）、`6.2-P-fseq`（`hasParent`→`nextR`）
- 状態: ✅ 証明済（sorry 0）

kind-0（`i₁ = 0`）の基本列 `M[n]` は幹 `take j₀ M` に同一ブロック
`(M_j)_{j=j₀}^{j₁-1}` を `n` 回並べたもの。ブロック先頭（`j₀` 相当）の第 0 行値は
親子関係 `(0,j₀) <^Next (0,j₁)` の内部最小性からブロック内部（オフセット `r'`）の値より
真に小さい、というのが本補題の内容。
-/

namespace PSS

/-- `(0,j₀) <^Next_M (0,j₁)` のとき、開区間 `(j₀, j₁)` の内部の第 0 行値は
`M_{0,j₁}` 以上（`nextrel0` の最小性節の読み出し）。 -/
private theorem nextrel0_interior_min_83 (M : PS) (j₀ j₁ j : ℕ)
    (hn : nextrel0 M j₀ j₁ = true) (h₀ : j₀ < j) (h₁ : j < j₁) :
    entry M 0 j₁ ≤ entry M 0 j := by
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hn
  rcases hn.2 j h₁ with h | h
  · exact absurd h₀ h
  · exact h

/-- 補題（第 `0` 種型基本列の基本不等式）— A22 訂正形（右辺添字に `j₀+` を復元）。 -/
theorem kind0_base_ineq (M : PS) (n q q' r' : ℕ)
    (_hMT : TPS M) (hn : 0 < n) (hr : 0 < r')
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (he1 : entry M 1 (Lng M - 1) = 0)
    (hq : q ≤ n - 1) (hq' : q' ≤ n - 1)
    (hrw : r' < (Lng M - 1) - parent M 0 (Lng M - 1)) :
    entry (oper M n) 0
        (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      < entry (oper M n) 0
        (parent M 0 (Lng M - 1) + q' * ((Lng M - 1) - parent M 0 (Lng M - 1)) + r') := by
  have hi : idx1 M (Lng M - 1) = 0 := by simp [idx1, he1]
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    rw [hi]; exact hp0
  have hnext0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hasParent_next_fseq M 0 (Lng M - 1) hp0
  have hdec := hnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdec
  have hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1 := hdec.1.1.2
  have he0lt : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := hdec.1.2
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by omega
  have hqn : q < n := by omega
  have hq'n : q' < n := by omega
  -- 左辺: ブロック `q`・オフセット `0` の読み出し（`i₁ = 0` なのでシフト無し）
  have hlhs := entry_oper_tiling_block_zero M n q 0 hlast hzero hp hqn
    (by rw [hi]; omega)
  rw [hi] at hlhs
  simp at hlhs
  -- 右辺: ブロック `q'`・オフセット `r'` の読み出し
  have hrhs := entry_oper_tiling_block_zero M n q' r' hlast hzero hp hq'n
    (by rw [hi]; exact hrw)
  rw [hi] at hrhs
  simp at hrhs
  -- ブロック先頭は内部より真に小さい（`<^Next` の最小性）
  have hmin : entry M 0 (Lng M - 1) ≤ entry M 0 (parent M 0 (Lng M - 1) + r') :=
    nextrel0_interior_min_83 M (parent M 0 (Lng M - 1)) (Lng M - 1)
      (parent M 0 (Lng M - 1) + r') hnext0 (by omega) (by omega)
  rw [hlhs, hrhs]
  omega

/-- A22: 原文のままの右辺添字 `q'(j₁-j₀)+r'`（`j₀+` 脱落）では偽。
反例 `M=(9,0)(0,0)(1,1)(2,1)(1,0)`, `n=2`, `q=1`, `q'=0`, `r'=1`
（`j₁=4`, `j₀=1`, `w=3`: 左辺 `M[2]_{0,4}=0`、右辺 `M[2]_{0,1}=0` で `0<0` が破綻）。 -/
theorem kind0_base_ineq_original_false :
    ¬ ∀ (M : PS) (n q q' r' : ℕ), TPS M → 0 < n → 0 < r' →
      hasParent M 0 (Lng M - 1) = true →
      entry M 1 (Lng M - 1) = 0 →
      q ≤ n - 1 → q' ≤ n - 1 →
      r' < (Lng M - 1) - parent M 0 (Lng M - 1) →
      entry (oper M n) 0
          (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        < entry (oper M n) 0
          (q' * ((Lng M - 1) - parent M 0 (Lng M - 1)) + r') := by
  intro h
  have := h [(9,0),(0,0),(1,1),(2,1),(1,0)] 2 1 0 1 (List.cons_ne_nil _ _) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this
  decide

/-! ## 回帰ベクトル（反例列で仮定と訂正形の成立を機械確認） -/

private def cexM_83 : PS := [(9,0),(0,0),(1,1),(2,1),(1,0)]

#guard hasParent cexM_83 0 (Lng cexM_83 - 1)
#guard entry cexM_83 1 (Lng cexM_83 - 1) == 0
#guard parent cexM_83 0 (Lng cexM_83 - 1) == 1
-- 訂正形 (q,q',r')=(1,0,1): M[2]_{0,1+3} = 0 < 1 = M[2]_{0,1+0+1}
#guard decide (entry (oper cexM_83 2) 0 4 < entry (oper cexM_83 2) 0 2)
-- 原文形 (q,q',r')=(1,0,1): M[2]_{0,4} = 0 < 0 = M[2]_{0,1} は不成立
#guard !decide (entry (oper cexM_83 2) 0 4 < entry (oper cexM_83 2) 0 1)

#print axioms kind0_base_ineq
#print axioms kind0_base_ineq_original_false

end PSS
