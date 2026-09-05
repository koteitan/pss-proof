import Bijectivity.«03-exp-order-transitive»

/-!
# 補題（標準形と基本列的順序の関係）

原文: 任意の \(M\in T_{\textrm{PS}}\) に対して、\(M\in ST_{\textrm{PS}}\) は
ある \(u,v\in\mathbb{N}\) が存在して \(u\leq v\) かつ
\(M\leq_{\textrm{PS}[]}((j,j))_{j=u}^v\) であることと同値である。

原文の証明:
> (⇒) \(S_0T_{\textrm{PS}}\) では \(a=()\) で成立。\(S_kT_{\textrm{PS}}\) で成立と仮定すると、
> \(M\in S_{k+1}T_{\textrm{PS}}\) には \(N\in S_kT_{\textrm{PS}}\) があって
> \(M\leq_{\textrm{PS}[]}N\) だから 基本列的順序が推移性 より従う。
> \(ST_{\textrm{PS}}=\bigcup_k S_kT_{\textrm{PS}}\) より結論。
> (⇐) \(Q_0=((j,j))_{j=u}^v\in ST_{\textrm{PS}}\)、\(Q_{k+1}=Q_k[a_k]\in ST_{\textrm{PS}}\)
> の帰納により \(M=Q_{\textrm{Lng}(a)}\in ST_{\textrm{PS}}\)。□
-/

namespace Bijectivity

open PSS

/-- 原文 (⇐) の \(Q_k\) の帰納。 -/
theorem stps_expand : ∀ (a : List ℕ) (N : PS), STPS N → (∀ n ∈ a, 1 ≤ n) →
    STPS (expand N a)
  | [], N, hN, _ => hN
  | n :: a, N, hN, ha => by
      exact stps_expand a (oper N n) (STPS.oper hN n (ha n (by simp)))
        (fun m hm => ha m (by simp [hm]))

/-- 一歩の展開は \(\leq_{\textrm{PS}[]}\) を与える。 -/
theorem oper_leExpPS (M : PS) {n : ℕ} (hn : 1 ≤ n) : oper M n ≤ₚ[] M :=
  ⟨[n], by simpa using hn, by simp [expand]⟩

/-- 原文の補題（標準形と基本列的順序の関係）。 -/
theorem stps_iff_leExpPS (M : PS) :
    STPS M ↔ ∃ u v : ℕ, u ≤ v ∧ M ≤ₚ[] diagSeq u v := by
  constructor
  · intro h
    induction h with
    | diag u v huv => exact ⟨u, v, huv, [], by simp, rfl⟩
    | @oper M hM n hn ih =>
        obtain ⟨u, v, huv, hle⟩ := ih
        exact ⟨u, v, huv, leExpPS_trans (oper_leExpPS M hn) hle⟩
  · rintro ⟨u, v, huv, a, ha, rfl⟩
    exact stps_expand a (diagSeq u v) (STPS.diag u v huv) ha

end Bijectivity
