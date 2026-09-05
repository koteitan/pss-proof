import Bijectivity.«09-standard-iff-exp»

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

UNPROVEN STUB（訂正形・逐語形とも）。
-/

namespace Bijectivity

open PSS

/-- 原文の補題（標準形の始切片への経路）の逐語形。上記のとおり \(j_1'=j_1\) が反例。 -/
theorem seg_ltExpPS_verbatim {M : PS} (hM : STPS M) {j1' : ℕ} (h : j1' ≤ Lng M - 1) :
    seg M 0 j1' <ₚ[] M := by
  sorry

/-- 訂正形（結論を \(\leq_{\textrm{PS}[]}\) に）。 -/
theorem seg_leExpPS {M : PS} (hM : STPS M) {j1' : ℕ} (h : j1' ≤ Lng M - 1) :
    seg M 0 j1' ≤ₚ[] M := by
  sorry

end Bijectivity
