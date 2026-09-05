import Bijectivity.«07-oper-pred»

/-!
# 補題（最左列の不変性）

原文: 任意の \(M,N\in T_{\textrm{PS}}\) に対して、\(M\leq_{\textrm{PS}[]}N\) ならば
\(M_0=N_0\) である。

原文の証明:
> \(\leq_{\textrm{PS}[]}\) の定義よりある \(a\) が存在して
> \(M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\)。\(Q_0=N\)、\(Q_{i+1}=Q_i[a_i]\) とする。
> \(\textrm{Lng}(Q_k)=1\) なら \((Q_{k+1})_0=(Q_k)_0\)。\(\textrm{Lng}(Q_k)>1\) なら
> 展開と \(\textrm{Pred}\) の関係 より \((Q_{k+1})_0=\textrm{Pred}(Q_k)_0=(Q_k)_0\)。
> 帰納法により \(M_0=(Q_{\textrm{Lng}(a)})_0=N_0\) である。
-/

namespace Bijectivity

open PSS

/-- 原文の \(Q_i\) の帰納に対応する補題。 -/
theorem expand_head : ∀ (a : List ℕ) (N : PS), (∀ n ∈ a, 1 ≤ n) →
    (expand N a).headD (0, 0) = N.headD (0, 0)
  | [], N, _ => rfl
  | n :: a, N, ha => by
      rw [expand, expand_head a (oper N n) (fun m hm => ha m (by simp [hm]))]
      rcases Nat.lt_or_ge 1 (Lng N) with h | h
      · exact oper_head h n (ha n (by simp))
      · have : Lng N - 1 = 0 := by omega
        simp [oper, this]

/-- 原文の補題（最左列の不変性）。 -/
theorem leExpPS_head {M N : PS} (h : M ≤ₚ[] N) :
    M.headD (0, 0) = N.headD (0, 0) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact expand_head a N ha

end Bijectivity
