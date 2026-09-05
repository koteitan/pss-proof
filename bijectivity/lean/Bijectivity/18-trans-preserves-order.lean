import Bijectivity.«12-lex-implies-exp»
import Bijectivity.Cited
import PSS.Trans

/-!
# 命題（`Trans` が順序を保つこと）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}}N\) ならば
\(\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)\) である。

原文の証明: 基本列的順序が辞書式的順序を含意すること より \(M<_{\textrm{PS}[]}N\)。
（以降 [1] の基本列の降下性を反復する。）

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の命題（`Trans` が順序を保つこと）。 -/
theorem trans_lessBT_of_ltPS {M N : PS} (hM : CTPS M) (hN : CTPS N) (h : M <ₚ N) :
    lessBT (PSS.Trans M) (PSS.Trans N) = true := by
  sorry

end Bijectivity
