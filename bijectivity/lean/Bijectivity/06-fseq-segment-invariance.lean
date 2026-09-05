import Bijectivity.Defs

/-!
# 命題（基本列の切片の不変性）

原文: 任意の \(M\in T_{\textrm{PS}}\) と \(j_0,j_1\in\mathbb{N}\) と
\(m,n\in\mathbb{N}_+\) に対して、\(j_0\leq j_1\) かつ
\(j_1<\textrm{Lng}(M[m])\) かつ \(j_1<\textrm{Lng}(M[n])\) ならば
\((M[m]_j)_{j=j_0}^{j_1}=(M[n]_j)_{j=j_0}^{j_1}\) である。

原文の証明（要旨）:
> \(m<n\) としてよい。\(M[n]\) の先頭 \(\textrm{Lng}(M[m])\) 項は
> \(G\oplus\left(\bigoplus(B_k)_{k=0}^{m-1}\right)=M[m]\) に一致する。
> よって \(j_0\leq j_1<\textrm{Lng}(M[m])\) より従う。□

証明の要は、\(m\leq n\) のとき \(M[n]\) が \(M[m]\) を接頭辞にもつこと
（`oper_prefix`）である。tiling 枝では
\(\textrm{range}\,n=\textrm{range}\,m\mathbin{+\!\!+}\textrm{range}'\,m\,(n-m)\)
によりブロック列が分かれ、退化枝では両者が \(\textrm{Pred}(M)\) で一致する。
-/

namespace Bijectivity

open PSS

/-- 連結の左側にある添字では `entry` は変わらない。 -/
theorem entry_append_left {A R : PS} {i j : ℕ} (h : j < A.length) :
    entry (A ++ R) i j = entry A i j := by
  simp [entry, List.getElem?_append_left h]

/-- \(m\leq n\) のとき \(M[n]\) は \(M[m]\) を接頭辞にもつ。 -/
theorem oper_prefix (M : PS) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ R : PS, oper M n = oper M m ++ R := by
  by_cases hM : 1 < Lng M
  case neg =>
    have h1 : Lng M - 1 = 0 := by omega
    exact ⟨[], by simp [oper, h1]⟩
  have hj1ne : Lng M - 1 ≠ 0 := by omega
  by_cases hz : entry M 0 (Lng M - 1) = 0 && entry M 1 (Lng M - 1) = 0
  · exact ⟨[], by simp [oper, hj1ne, hz]⟩
  · by_cases hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true
    · obtain ⟨j0, hj0⟩ : ∃ j0, parent M (idx1 M (Lng M - 1)) (Lng M - 1) = j0 := ⟨_, rfl⟩
      obtain ⟨d0, hd0⟩ : ∃ d0,
          (if 0 < idx1 M (Lng M - 1) then entry M 0 (Lng M - 1) - entry M 0 j0 else 0)
            = d0 := ⟨_, rfl⟩
      obtain ⟨d1, hd1⟩ : ∃ d1,
          (if 1 < idx1 M (Lng M - 1) then entry M 1 (Lng M - 1) - entry M 1 j0 else 0)
            = d1 := ⟨_, rfl⟩
      have hop : ∀ k, oper M k = M.take j0 ++ (List.range k).flatMap (fun c =>
          (List.range' j0 (Lng M - 1 - j0)).map (fun j =>
            (entry M 0 j + c * d0, entry M 1 j + c * d1))) := by
        intro k
        simp [oper, hj1ne, hz, hp, hj0, hd0, hd1, -mul_ite]
      obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
      refine ⟨((List.range d).map (m + ·)).flatMap (fun c =>
          (List.range' j0 (Lng M - 1 - j0)).map (fun j =>
            (entry M 0 j + c * d0, entry M 1 j + c * d1))), ?_⟩
      rw [hop (m + d), hop m, List.append_assoc]
      congr 1
      rw [← List.flatMap_append]
      congr 1
      exact List.range_add
    · exact ⟨[], by simp [oper, hj1ne, hz, hp]⟩

/-- 原文の命題（基本列の切片の不変性）。 -/
theorem oper_seg_invariance {M : PS} {j0 j1 m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hj : j0 ≤ j1)
    (h1 : j1 < Lng (oper M m)) (h2 : j1 < Lng (oper M n)) :
    seg (oper M m) j0 j1 = seg (oper M n) j0 j1 := by
  -- 原文どおり m と n について対称なので m ≤ n の場合に帰着する
  have key : ∀ p q : ℕ, 1 ≤ p → p ≤ q → j1 < Lng (oper M p) →
      seg (oper M p) j0 j1 = seg (oper M q) j0 j1 := by
    intro p q hp hpq hlt
    obtain ⟨R, hR⟩ := oper_prefix M hp hpq
    unfold seg
    apply List.map_congr_left
    intro j hj'
    have hjlt : j < Lng (oper M p) := by
      simp only [List.mem_range'] at hj'
      omega
    rw [hR, entry_append_left hjlt, entry_append_left hjlt]
  rcases Nat.le_total m n with h | h
  · exact key m n hm h h1
  · exact (key n m hn h h2).symm

end Bijectivity
