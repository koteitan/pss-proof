import Bijectivity.Cited

/-!
# 補題（対応する項の上界未満の字母）

原文: 任意の \(t\in T_{\textrm{B}\omega}\) に対して、\(t<_{\textrm{B}}D_0D_\omega0\) ならば
\(t\in OT_{\textrm{B}\omega}\) は \(t\in OT_{\textrm{B}}\) と同値である。

すなわち上界 \(D_0D_\omega0\) 未満では \(D_\omega\) を許すかどうかが結論に影響しない。

UNPROVEN STUB。
-/

namespace Bijectivity

open PSS

/-- 原文の補題（対応する項の上界未満の字母）。 -/
theorem OT_iff_OT_B_of_lt {t : BT} (h : lessBT t DzeroDomegaZero = true) :
    t ∈ OT ↔ t ∈ OT_B := by
  sorry

end Bijectivity
