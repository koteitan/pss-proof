import Bijectivity.«16b-mono-fseq-rel»
import «OTB-well-founded-syntactic».«OTB-well-founded-syntactic-cofinality»

/-!
# `operB` の添字単調性

`lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-cofinality.lean` が
Isabelle `y4_N_mono` / `y4_N_mono_le` (`layerC/pss_scratch.thy`:12912 / 13034) を
**仮定ゼロ・`sorry` ゼロ**で証明済みなので、それを `16b` の `OperBNumMono` の形に
配線するだけである。

補題（基本列の関係）の 条件 (V)・非許容枝では [1] の交換関係 (3) が
\(\textrm{Trans}(M)[n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])\;(n\geq1)\) の形でしか
使えず、目標の添字 \(m=0\) だけが取り残される。そこをこれで埋める（訂正 W-34）。
-/

namespace Bijectivity

open PSS

/-- Isabelle `y4_N_mono`（`OTB-well-founded-syntactic-cofinality`）。 -/
theorem operB_numBT_step (a : BT) (hot : a ∈ OT_B)
    (htag : domTag a = BDom.naturals) (n : ℕ) :
    lessBT (operB a (numBT n)) (operB a (numBT (n + 1))) = true :=
  y4_N_mono a n hot.1 hot.2 htag

/-- Isabelle `y4_N_mono_le`（同上）。 -/
theorem operB_numBT_mono_holds : OperBNumMono :=
  fun _ _ _ hOT htag hle => y4_N_mono_le hOT.1 hOT.2 htag hle

end Bijectivity
