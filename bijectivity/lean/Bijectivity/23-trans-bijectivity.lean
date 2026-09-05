import Bijectivity.«18-trans-preserves-order»

/-!
# 定理（変換写像の全単射性）— 主定理

原文: \(\textrm{Trans}\) は
\(CT_{\textrm{PS}}\to\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\)
上で全域かつ全単射であり、特に同型写像である。

原文の証明:
> 可算な標準形の起源 及び 辞書式的順序が基本列的順序を含意すること より任意の
> \(M\in CT_{\textrm{PS}}\) に対してある \(v\) が存在して
> \(M\leq_{\textrm{PS}}((j,j))_{j=0}^v<_{\textrm{PS}}((j,j))_{j=0}^{v+1}\in CT_{\textrm{PS}}\)
> であるから、\(CT_{\textrm{PS}}=\bigcup_{M}\{N\mid N<_{\textrm{PS}}M\}\) である。
> [4] の Lemma 2.1 より値域側も同様に分解でき、対応する項の上界 (2) より
> \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}
> =\bigcup_{M\in CT_{\textrm{PS}}}\{t\mid t<_{\textrm{B}}\textrm{Trans}(M)\}\) である。
> ペア数列の解析 (2) より従う。□

`OT_{\textrm{B}\omega}` は \(D_\omega\) を許す順序数項の集合であり、既存の `PSS.OT`
がそのまま該当する（`isOT_BT` は \(D_\omega\)-自由性を要求しない）。

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の主定理の値域 \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\)。 -/
def TransRange : Set BT := {t | t ∈ OT ∧ lessBT t DzeroDomegaZero = true}

/-- 定理（変換写像の全単射性）: \(\textrm{Trans}\) は
\(CT_{\textrm{PS}}\) から `TransRange` への全単射である。 -/
theorem trans_bijOn : Set.BijOn PSS.Trans {M | CTPS M} TransRange := by
  sorry

/-- 定理（変換写像の全単射性）: 特に同型写像であること。 -/
theorem trans_order_iso {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M <ₚ N ↔ lessBT (PSS.Trans M) (PSS.Trans N) = true := by
  sorry

end Bijectivity
