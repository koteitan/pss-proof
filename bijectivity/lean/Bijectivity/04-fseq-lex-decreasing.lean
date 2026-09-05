import Bijectivity.«02-lex-linear»

/-!
# 命題（基本列の辞書式的縮小性）

原文: 任意の \(M\in T_{\textrm{PS}}\) と \(n\in\mathbb{N}_+\) に対して、
\(\textrm{Lng}(M)>1\) ならば \(M[n]<_{\textrm{PS}}M\) である。

原文の証明（要旨）:
> \(\textrm{operator}[]\) の定義中の記号を \(M\) に対して定義する。条件より
> \(j_1>0\)。\(M[n]=\textrm{Pred}(M)\) なら明らか。よって \(M_{j_1}\neq(0,0)\) かつ
> ある \(j_0\) が存在して \((i_1,j_0)<^\textrm{Next}_M(i_1,j_1)\) とする。
> \(\textrm{Pred}\) が \([1]\) で表されることより \(n>1\) としてよい。
> \(M[n]=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}
> \left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)\) であるから、
> \(M[n]<_{\textrm{PS}}M\) は
> \(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})\) と同値。
> 先頭は \((M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)\) であり、\(i_1=0\) なら
> \(<^\textrm{Next}\) の定義より \(M_{0,j_0}<M_{0,j_1}\)、\(i_1=1\) なら
> \(M_{1,j_0}<M_{1,j_1}\)。いずれでも従う。□

UNPROVEN STUB — 原文の証明は `oper` の内部記号（\(j_0\), \(i_1\), \(\delta\), \(B\)）
に対する具体計算であり、`PSS.oper` の展開に対する補題群を要する。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（基本列の辞書式的縮小性）。 -/
theorem oper_ltPS {M : PS} (hM : 1 < Lng M) (n : ℕ) (hn : 1 ≤ n) : oper M n <ₚ M := by
  sorry

/-- 系: \(\textrm{Lng}\) の条件を外した弱形（\(\textrm{Lng}(M)\leq1\) では
`oper M n = M` なので等号で成立する）。 -/
theorem oper_lePS (M : PS) (n : ℕ) (hn : 1 ≤ n) : oper M n ≤ₚ M := by
  rcases Nat.lt_or_ge 1 (Lng M) with h | h
  · exact Or.inr (oper_ltPS h n hn)
  · left
    have : Lng M - 1 = 0 := by omega
    simp [oper, this]

end Bijectivity
