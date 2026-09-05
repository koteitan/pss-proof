import Bijectivity.«06-fseq-segment-invariance»
import «5».«5.3-pred-is-oper1»
import «6».«6.5-Red-Pred-commute»

/-!
# 命題（展開と `Pred` の関係）

原文: 任意の \(M\in T_{\textrm{PS}}\) と \(n\in\mathbb{N}_+\) に対し、
\(j_1=\textrm{Lng}(M)-1\) と置くと、\(\textrm{Lng}(M[n])\geq j_1\) かつ
\((M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)\) である。

原文の証明:
> \(M[n]=M\) または \(M[n]=\textrm{Pred}(M)\) なら明らか。よって \(j_1>0\) かつ
> \(M_{j_1}\neq(0,0)\) かつある \(j_0\) が存在して
> \((i_1,j_0)<^\textrm{Next}_M(i_1,j_1)\) とする。
> \(\textrm{Lng}(M[n])=j_0+n(j_1-j_0)\geq j_1\) である。
> [1] の \(\textrm{Pred}\) が \([1]\) で表されること及び 基本列の切片の不変性 より
> \((M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)\) である。□

UNPROVEN STUB。なお原文の \((M[n]_j)_{j=0}^{j_1-1}=\textrm{Pred}(M)\) は
\(\textrm{Lng}(M)=1\)（\(j_1=0\)）のとき左辺が空列、右辺が \(M\) となり成り立たないので、
ここでは実際に使われる \(\textrm{Lng}(M)>1\) を仮定した形で述べる。
-/

namespace Bijectivity

open PSS

/-- 退化枝: `oper M n = Pred M` のとき。 -/
theorem oper_take_pred_of_pred {M : PS} {n : ℕ} (hM : 1 < Lng M) (h : oper M n = Pred M) :
    Lng M - 1 ≤ Lng (oper M n) ∧ (oper M n).take (Lng M - 1) = Pred M := by
  rw [h, length_Pred M hM]
  exact ⟨le_refl _, by
    rw [Pred_eq_take M hM, List.take_take]
    congr 1
    simp [Lng]⟩

/-- 原文の命題（展開と `Pred` の関係）。先頭 \(j_1\) 項を `List.take` で表す。 -/
theorem oper_take_pred {M : PS} (hM : 1 < Lng M) (n : ℕ) (hn : 1 ≤ n) :
    Lng M - 1 ≤ Lng (oper M n) ∧ (oper M n).take (Lng M - 1) = Pred M := by
  sorry

/-- 補助: 正の長さで `take` しても先頭は変わらない。 -/
theorem headD_take {α : Type _} (l : List α) (k : ℕ) (hk : 0 < k) (d : α) :
    (l.take k).headD d = l.headD d := by
  cases l with
  | nil => simp
  | cons a l =>
      cases k with
      | zero => omega
      | succ k => simp

/-- 補助: 長さ 2 以上なら `dropLast` は先頭を変えない。 -/
theorem headD_dropLast {α : Type _} (l : List α) (hl : 1 < l.length) (d : α) :
    l.dropLast.headD d = l.headD d := by
  cases l with
  | nil => simp at hl
  | cons a l =>
      cases l with
      | nil => simp at hl
      | cons b l => simp [List.dropLast]

/-- 系: 展開は最左列を保つ。原文の 最左列の不変性 の一歩分。 -/
theorem oper_head {M : PS} (hM : 1 < Lng M) (n : ℕ) (hn : 1 ≤ n) :
    (oper M n).headD (0, 0) = M.headD (0, 0) := by
  obtain ⟨_, htake⟩ := oper_take_pred hM n hn
  have hpos : 0 < Lng M - 1 := by omega
  have h1 := headD_take (oper M n) (Lng M - 1) hpos (0, 0)
  rw [htake] at h1
  have hPred : Pred M = M.dropLast := by simp [Pred, Nat.not_le.mpr hM]
  rw [hPred] at h1
  rw [← h1, headD_dropLast M hM]

end Bijectivity
