import Bijectivity.«08-leftmost-invariance»
import Bijectivity.«09-standard-iff-exp»

/-!
# 命題（可算な標準形の起源）

原文: 任意の \(M\in T_{\textrm{PS}}\) に対して、\(M\in CT_{\textrm{PS}}\) は
ある \(v\in\mathbb{N}\) が存在して \(M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v\)
であることと同値である。

原文の証明:
> (⇒) 標準形と基本列的順序の関係 より \(u\leq v\) と \(M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v\)
> が取れる。最左列の不変性 より \(M_0=(u,u)\)。\(CT_{\textrm{PS}}\) の定義より
> \(M_0=(0,0)\) だから \(u=0\)。
> (⇐) 最左列の不変性 より \(M_0=(0,0)\)。また \(M\in ST_{\textrm{PS}}\)。
> よって \(M\in CT_{\textrm{PS}}\)。□
-/

namespace Bijectivity

open PSS

/-- 対角列の最左列。 -/
theorem headD_diagSeq {u v : ℕ} (h : u ≤ v) : (diagSeq u v).headD (0, 0) = (u, u) := by
  have hlen : v + 1 - u = (v - u) + 1 := by omega
  simp [diagSeq, hlen, List.range']

/-- 原文の命題（可算な標準形の起源）。 -/
theorem ctps_iff_leExpPS (M : PS) :
    CTPS M ↔ ∃ v : ℕ, M ≤ₚ[] diagSeq 0 v := by
  constructor
  · rintro ⟨hst, hhd⟩
    obtain ⟨u, v, huv, hle⟩ := (stps_iff_leExpPS M).mp hst
    have h0 : M.headD (0, 0) = (u, u) := by
      rw [leExpPS_head hle, headD_diagSeq huv]
    have hu : u = 0 := by
      rw [hhd] at h0
      exact (Prod.mk.injEq .. ▸ h0.symm).1
    exact ⟨v, hu ▸ hle⟩
  · rintro ⟨v, hle⟩
    refine ⟨(stps_iff_leExpPS M).mpr ⟨0, v, Nat.zero_le v, hle⟩, ?_⟩
    rw [leExpPS_head hle, headD_diagSeq (Nat.zero_le v)]

end Bijectivity
