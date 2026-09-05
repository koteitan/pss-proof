import Bijectivity.«10-countable-standard-origin»
import Bijectivity.«11-path-to-initial-segment»

/-!
# 命題（基本列的順序が辞書式的順序を含意すること）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}}N\) ならば
\(M<_{\textrm{PS}[]}N\) である。

原文の証明（要旨）: \(\textrm{Lng}(M)\) に関する強い帰納法。
> \(j_1^M=0\) なら \(M=((0,0))=(N_j)_{j=0}^0\) で 標準形の始切片への経路 より従う。
> \(j_1^M>0\) のとき、\(f=\min(\{\min(j_1^M,j_1^N)+1\}\cup\{j\mid j\leq\min(j_1^M,j_1^N)
> \land M_j\neq N_j\})\)（最初の不一致位置）で場合分けする。
> \(f=j_1^M+1\) なら \(M=(N_j)_{j=0}^{j_1^M}\) で 標準形の始切片への経路 より従う。
> \(f\leq j_1^M\) のときは \(f=j_1^N\) の場合に、\(\textrm{Lng}(M')=\textrm{Lng}(N)\) かつ
> \((M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\) なる \(M'\in CT_{\textrm{PS}}\) が
> 高々 \((j_1^N)^2\) 個であることを使い、内側の帰納を回す。
> 一般の \(f\leq j_1^N\) は \(N\) を \((N_j)_{j=0}^f\) に置き換えて帰着する。□

UNPROVEN STUB — 原文で最も長い証明であり、二重帰納と
「同じ始切片をもつ \(CT_{\textrm{PS}}\) の元が有限個」という有限性補題を要する。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（基本列的順序が辞書式的順序を含意すること）。 -/
theorem ltPS_ltExpPS {M N : PS} (hM : CTPS M) (hN : CTPS N) (h : M <ₚ N) : M <ₚ[] N := by
  sorry

end Bijectivity
