import Bijectivity.«02b-lex-list-lemmas»
import «6».«6.5-Red-Pred-commute»

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

/-- 退化枝: `oper M n = Pred M` のとき。真の接頭辞なので \(<_{\textrm{PS}}\)。 -/
theorem oper_ltPS_of_pred {M : PS} {n : ℕ} (hM : 1 < Lng M) (h : oper M n = Pred M) :
    oper M n <ₚ M := by
  rw [h, Pred_eq_take M hM]
  exact ltPS_take M (by omega)

/-- 原文の命題（基本列の辞書式的縮小性）。

退化枝（`oper M n = Pred M`）は `oper_ltPS_of_pred` で閉じている。
残るのは tiling 枝で、原文どおり \(\bigoplus(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})\)
を \(<^\textrm{Next}\) の定義（`nextrel0` / `nextrel1` が与える
\(M_{0,j_0}<M_{0,j_1}\) / \(M_{1,j_0}<M_{1,j_1}\)）から示す必要がある。 -/
theorem oper_ltPS {M : PS} (hM : 1 < Lng M) (n : ℕ) (hn : 1 ≤ n) : oper M n <ₚ M := by
  have hj1ne : Lng M - 1 ≠ 0 := by omega
  by_cases hz : entry M 0 (Lng M - 1) = 0 && entry M 1 (Lng M - 1) = 0
  · exact oper_ltPS_of_pred hM (by simp [oper, hj1ne, hz])
  · by_cases hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true
    · sorry
    · exact oper_ltPS_of_pred hM (by simp [oper, hj1ne, hz, hp])

/-- 系: \(\textrm{Lng}\) の条件を外した弱形（\(\textrm{Lng}(M)\leq1\) では
`oper M n = M` なので等号で成立する）。 -/
theorem oper_lePS (M : PS) (n : ℕ) (hn : 1 ≤ n) : oper M n ≤ₚ M := by
  rcases Nat.lt_or_ge 1 (Lng M) with h | h
  · exact Or.inr (oper_ltPS h n hn)
  · left
    have : Lng M - 1 = 0 := by omega
    simp [oper, this]

end Bijectivity
