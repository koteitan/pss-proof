import Bijectivity.«16c-operB-mono»
import «8».«8.3-condII-masterCF»
import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-Dichotomy»
import «8».«8.3-condII-TrunkLeg»
import «8».«8.3-condII-LDJB-lttrmax»
import «8».«8.3-condII-R3LE»
import «8».«8.3-condII-NotLdjReg-close»
import «8».«8.3-condII-BoundaryLeg2»
import «8».«8.3-condII-Boundary-close»
import «8».«8.3-condII-step»
import «8».«8.2-condIIIV-close»
import «7».«7.2-scb-fseq»

/-!
# 条件 (II) の下での `Trans` と基本列の交換関係 (2)

原文 [1] の 条件(II) の下での `Trans` と基本列の交換関係 (2)
（Isabelle `y3j_p_8_3_condII_exchange_2`, `isabelle/8/Support_8_C.thy`:15272）:

\[
m_n\geq0 \;\Longrightarrow\; \textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n],\qquad
m_n=\begin{cases}n-1&(\textrm{leftD}_{j_0})\\ n-2&(\text{otherwise})\end{cases}
\]

Lean 側の `CondII_masterCF` は数え上げ `c` を存在量化に落としてしまっていて、
補題（基本列の関係）が要る「与えられた \(k\) に対して \(m_n=k\) となる \(n\)」を
取れない。`8.3-condII-masterCF` の `condII_masterCF_exact_of_tailval` が
数え上げ `\textrm{cnt}_1+(m-1)`（`cnt₁ = if condII_ldj M then 1 else 0`、
Isabelle の `y3j_mnp1` と同一）を露出しているので、そこから逆に解く。
-/

namespace Bijectivity

open PSS

/-- `CondII_TailvalAll_ST`（Isabelle `y3j_condII_tailval`,
`layerC/pss_scratch.thy`:17076）の無条件供給。`8.3-condII-Boundary-close` の
`condII_masterCF_of_condIIIV` と同じ配線を tailval 段で止めたもの。 -/
private theorem condII_tailvalAll_fr : CondII_TailvalAll_ST :=
  TailvalAll_ST_of_residuals_cm2 TV_Dichotomy_holds TV_TrunkLeg_holds
    (tv_boundaryleg_of_data (tvxBoundaryData_of_condIIIV condIIIVterminalSlice_holds))
    tv_notldjleg_holds tv_ldjb_holds TV_R3LE_holds

/-- Isabelle `operB_marked_scb_value` (pss_wip.thy:37100)。
`8.3-TransCondII-engine` / `8.3-condII-masterCF` の private 版と同一内容。 -/
private theorem operB_marked_scb_value_fr {t₀ t₁ t : BT} {u v n : ℕ} {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b) :
    operB t (numBT n)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b) := by
  have hd2 := scb_fseq_decomp (n := n) ht₀ ht₁ ht hd
  calc operB t (numBT n)
      = unflatBT (flatBT (operB t (numBT n))) := (unflatBT_flat _).symm
    _ = _ := by rw [hd2.1]

/-- 原文が引く 条件(II) の交換関係 (2) の、補題（基本列の関係）が要る向き。 -/
theorem condII_fseq_rel_holds : CondIIFseqRel := by
  intro M k hST hmono hj1 hcond
  have hR : RTPS M := STPS_RTPS M hST
  have htT : PSS.Trans M ∈ T_B := Trans_mem_T_B M hR
  obtain ⟨s, b, u, v, t₀, t₁, cnt, ht₀, ht₁, hcnt, hd, hall⟩ :=
    condII_masterCF_exact_of_tailval condII_step_holds M hR hmono hj1 hcond
      (condII_tailvalAll_fr M hST hmono hj1 hcond)
  refine ⟨k + 2 - cnt, by omega, ?_⟩
  rw [hall (k + 2 - cnt) (by omega),
    operB_marked_scb_value_fr (n := k) ht₀ ht₁ htT hd]
  have : cnt + (k + 2 - cnt - 1) = k + 1 := by omega
  rw [this]

end Bijectivity
