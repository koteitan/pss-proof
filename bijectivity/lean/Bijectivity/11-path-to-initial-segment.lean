import Bijectivity.«05-exp-implies-lex»
import Bijectivity.«09-standard-iff-exp»
import «5».«5.3-pred-is-oper1»
import «6».«6.5-Red-Pred-commute»

/-!
# 補題（標準形の始切片への経路）

原文: 任意の \(M\in ST_{\textrm{PS}}\) と \(j_1'\in\mathbb{N}\) に対し、
\(j_1=\textrm{Lng}(M)-1\) と置くと、\(j_1'\leq j_1\) ならば
\((M_j)_{j=0}^{j_1'}<_{\textrm{PS}[]}M\) である。

原文の証明:
> [1] の \(\textrm{Pred}\) が \([1]\) で表されることより、帰納法により
> \((M_j)_{j=0}^{j_1'}=\textrm{Pred}^{j_1-j_1'}(M)=M[1]^{j_1-j_1'}<_{\textrm{PS}[]}M\)。□

## 訂正候補: 結論は \(\leq_{\textrm{PS}[]}\) であるべき

\(j_1'=j_1\) のとき \((M_j)_{j=0}^{j_1'}=M\) なので、原文の結論は
\(M<_{\textrm{PS}[]}M\) を主張することになるが、\(<_{\textrm{PS}[]}\) の定義
（\(a\neq()\) なる \(a\) の存在）より \(\textrm{Lng}(M)>1\) のときこれは偽である
（\(M[1]=\textrm{Pred}(M)\neq M\) で、以降どれだけ展開しても \(M\) には戻らない）。

原文自身、後の 基本列的順序が辞書式的順序を含意すること の証明ではこの補題を
\(((j,j))_{j=0}^{v^M}\leq_{\textrm{PS}[]}((j,j))_{j=0}^v\) と\(\leq\) で用いている。
よって結論を \(\leq_{\textrm{PS}[]}\) とするのが正しい。
狭義にしたい場合は仮定を \(j_1'<j_1\) とする。

逐語形は上記の理由で UNPROVEN STUB のまま残し、訂正形を証明する。
-/

namespace Bijectivity

open PSS

/-- \(\textrm{seg}\,M\,0\,j\) は先頭 \(j+1\) 項である。 -/
theorem seg_zero_eq_take (M : PS) {j : ℕ} (h : j + 1 ≤ Lng M) :
    seg M 0 j = M.take (j + 1) := by
  apply List.ext_getElem
  · simp [seg, Lng] at h ⊢; omega
  · intro i h1 h2
    have hi : i < Lng M := by simp [seg] at h1; omega
    simp only [seg, List.getElem_map, List.getElem_range', List.getElem_take]
    simp [entry, List.getElem?_eq_getElem hi]

/-- 反復 `Pred`（＝反復 `[1]`）による先頭切片への経路。原文の帰納に対応する。 -/
theorem take_leExpPS : ∀ (k : ℕ) (M : PS), TPS M → k < Lng M →
    M.take (Lng M - k) ≤ₚ[] M
  | 0, M, _, _ => ⟨[], by simp, by simp [expand, Lng]⟩
  | k + 1, M, hM, hk => by
      have hlen : 1 < Lng M := by omega
      have hlenP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
      have hPne : TPS (Pred M) := by
        intro he
        have h0 : Lng (Pred M) = 0 := by rw [he]; rfl
        omega
      have ih := take_leExpPS k (Pred M) hPne (by omega)
      have hstep : Pred M ≤ₚ[] M := by
        rw [pred_is_oper1 M hM hlen]; exact oper_leExpPS M (le_refl 1)
      have heq : (Pred M).take (Lng (Pred M) - k) = M.take (Lng M - (k + 1)) := by
        rw [hlenP, Pred_eq_take M hlen, List.take_take]
        congr 1
        omega
      rw [heq] at ih
      exact leExpPS_trans ih hstep

/-- \(\textrm{Lng}(M)>1\) なら \(M<_{\textrm{PS}[]}M\) は偽（展開は狭義に下がる）。 -/
theorem ltExpPS_irrefl {M : PS} (hM : 1 < Lng M) : ¬ (M <ₚ[] M) :=
  fun h => ltPS_irrefl M (ltExpPS_ltPS_of_lng hM h)

/-- **原文の補題（標準形の始切片への経路）の逐語形は偽**（訂正 `B2`）。

反例は \(M=((j,j))_{j=0}^1\)、\(j_1'=j_1=1\)。このとき
\((M_j)_{j=0}^{j_1'}=M\) なので原文の結論は \(M<_{\textrm{PS}[]}M\) を主張するが、
\(\textrm{Lng}(M)>1\) では展開が狭義に下がるのでこれは偽である。
訂正形（結論を \(\leq_{\textrm{PS}[]}\) に）は下の `seg_leExpPS`。 -/
theorem not_seg_ltExpPS :
    ¬ (∀ (M : PS) (j1' : ℕ), STPS M → j1' ≤ Lng M - 1 → seg M 0 j1' <ₚ[] M) := by
  intro h
  have hS : STPS (diagSeq 0 1) := STPS.diag 0 1 (by omega)
  have hseg : seg (diagSeq 0 1) 0 1 = diagSeq 0 1 := by decide
  have hlen : 1 < Lng (diagSeq 0 1) := by decide
  have hx := h (diagSeq 0 1) 1 hS (by decide)
  rw [hseg] at hx
  exact ltExpPS_irrefl hlen hx

/-- 訂正形（結論を \(\leq_{\textrm{PS}[]}\) に）。 -/
theorem seg_leExpPS {M : PS} (hM : TPS M) {j1' : ℕ} (h : j1' ≤ Lng M - 1) :
    seg M 0 j1' ≤ₚ[] M := by
  have hpos : 0 < Lng M := by
    rcases M with _ | ⟨p, M⟩
    · exact absurd rfl hM
    · simp [Lng]
  have hle : j1' + 1 ≤ Lng M := by omega
  rw [seg_zero_eq_take M hle]
  have h2 := take_leExpPS (Lng M - (j1' + 1)) M hM (by omega)
  have heq : Lng M - (Lng M - (j1' + 1)) = j1' + 1 := by omega
  rw [heq] at h2
  exact h2

end Bijectivity
