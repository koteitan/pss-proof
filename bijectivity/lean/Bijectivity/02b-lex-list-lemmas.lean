import Bijectivity.«02-lex-linear»

/-!
# 補助（辞書式的順序のリスト補題）

原文の 基本列の辞書式的縮小性 の証明で暗黙に使われる二つの事実:

* 真の接頭辞は \(<_{\textrm{PS}}\) で小さい（\(M[n]=\textrm{Pred}(M)\) の場合）。
* 共通の接頭辞は \(<_{\textrm{PS}}\) の比較で落とせる
  （\(M[n]=(M_j)_{j=0}^{j_1-1}\oplus\cdots\) と \(M\) の比較）。
-/

namespace Bijectivity

open PSS

/-- 共通接頭辞の消去。 -/
theorem ltPS_append_cancel : ∀ (A B C : PS), (A ++ B) <ₚ (A ++ C) ↔ B <ₚ C
  | [], _, _ => Iff.rfl
  | p :: A, B, C => by
      simp only [List.cons_append, ltPS, lt_irrefl, false_or, true_and, and_true]
      exact ltPS_append_cancel A B C

/-- 真の接頭辞は \(<_{\textrm{PS}}\) で小さい。 -/
theorem ltPS_take : ∀ (M : PS) {k : ℕ}, k < Lng M → M.take k <ₚ M
  | [], k, h => by simp [Lng] at h
  | p :: M, 0, _ => by simp [ltPS]
  | p :: M, k + 1, h => by
      have h' : k < Lng M := by simp [Lng] at h ⊢; omega
      simp only [List.take_succ_cons, ltPS, lt_irrefl, false_or, true_and]
      exact ltPS_take M h' 

end Bijectivity
