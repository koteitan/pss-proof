import Bijectivity.«12-lex-implies-exp»
import Bijectivity.Cited
import «8».«8.7-termination»
import «Buchholz-1986».«Buchholz-1986-2.1-order»

/-!
# 命題（`Trans` が順序を保つこと）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}}N\) ならば
\(\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(N)\) である。

原文の証明:
> 基本列的順序が辞書式的順序を含意すること より \(M<_{\textrm{PS}[]}N\) である。
> \(<_{\textrm{PS}[]}\) の定義よりある \(a\in\mathbb{N}_+^{<\omega}\setminus\{()\}\) が
> 存在して \(M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\) である。
> \(((0,0))\) は \(<_{\textrm{PS}}\) に対して \(T_{\textrm{PS}}\) の最小の要素であるから
> \(N\neq((0,0))\)、よって \(\textrm{Lng}(N)>1\) である。
> \(Q_0=N\)、\(Q_{i+1}=Q_i[a_i]\) とする。
> [1] の基本列の降下性より \(\textrm{Trans}(Q_1)<_{\textrm{B}}\textrm{Trans}(N)\)。
> \(\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)\) とすると、[1] の基本列の降下性
> 及び [4] の Lemma 2.1 より
> \(\textrm{Trans}(Q_{i+1})\leq_{\textrm{B}}\textrm{Trans}(Q_i)<_{\textrm{B}}\textrm{Trans}(N)\)。
> 帰納法により \(\textrm{Trans}(M)=\textrm{Trans}(Q_{\textrm{Lng}(a)})
> <_{\textrm{B}}\textrm{Trans}(N)\) である。□

[1] の基本列の降下性は本リポジトリの `8/8.7-termination.lean` の
`Trans_fseq_descend`（仮定 0、`sorry` 0）である。
[4] の Lemma 2.1（\(<_{\textrm{B}}\) の線形性）は
`Buchholz-1986/Buchholz-1986-2.1-order.lean` の `lessBT_linear_trans`。
-/

namespace Bijectivity

open PSS

/-! ## \(\leq_{\textrm{B}}\) の小道具（[4] Lemma 2.1） -/

theorem leBT_lessBT_trans {a b c : BT} (h1 : leBT a b = true) (h2 : lessBT b c = true) :
    lessBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | rfl
  · exact lessBT_linear_trans a b c h1 h2
  · exact h2

theorem leBT_trans {a b c : BT} (h1 : leBT a b = true) (h2 : leBT b c = true) :
    leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lessBT_linear_trans a b c h1 h2)
    · exact Or.inl h1
  · exact h2

theorem leBT_refl (a : BT) : leBT a a = true := by simp [leBT]

/-! ## 反復展開に沿った \(\textrm{Trans}\) の非増加性 -/

/-- 長さ 1 の列では基本列操作は恒等。 -/
theorem oper_of_lng_le_one {Q : PS} (h : Lng Q ≤ 1) (n : ℕ) : oper Q n = Q := by
  simpa [expand] using expand_of_lng_le_one [n] h

/-- 原文の \(Q_i\) の帰納。[1] の基本列の降下性を反復する。 -/
theorem trans_leBT_expand : ∀ (a : List ℕ) (Q : PS), STPS Q → (∀ n ∈ a, 1 ≤ n) →
    leBT (PSS.Trans (expand Q a)) (PSS.Trans Q) = true
  | [], Q, _, _ => by simpa [expand] using leBT_refl (PSS.Trans Q)
  | n :: a, Q, hQ, ha => by
      have hn : 1 ≤ n := ha n (by simp)
      have hstep : leBT (PSS.Trans (oper Q n)) (PSS.Trans Q) = true := by
        by_cases hL : 1 < Lng Q
        · simp [leBT, Trans_fseq_descend Q n hQ hn hL]
        · rw [oper_of_lng_le_one (by omega) n]
          exact leBT_refl _
      have hrec := trans_leBT_expand a (oper Q n) (STPS.oper hQ n hn)
        (fun k hk => ha k (by simp [hk]))
      rw [expand]
      exact leBT_trans hrec hstep

/-! ## 主張 -/

/-- \(((0,0))\) は \(<_{\textrm{PS}}\) に対して \(CT_{\textrm{PS}}\) の最小元。 -/
theorem one_lt_lng_of_ltPS {M N : PS} (hM : CTPS M) (hN : CTPS N) (h : M <ₚ N) :
    1 < Lng N := by
  rcases ltPS_dest_idx h with ⟨hlen, _⟩ | ⟨k, hkM, hkN, _, hklt⟩
  · have hpos := List.length_pos_of_ne_nil (STPS_TPS M hM.1)
    simp only [Lng] at hlen hpos ⊢
    omega
  · by_contra hc
    have hk0 : k = 0 := by simp only [Lng] at hkN hc; omega
    subst hk0
    have hz := ctps_entry_zero hN
    rw [show pairAt N 0 = (0, 0) by simp [pairAt, hz.1, hz.2]] at hklt
    simp [pairLt] at hklt

/-- 原文の命題（`Trans` が順序を保つこと）。 -/
theorem trans_lessBT_of_ltPS {M N : PS} (hM : CTPS M) (hN : CTPS N) (h : M <ₚ N) :
    lessBT (PSS.Trans M) (PSS.Trans N) = true := by
  obtain ⟨a, hane, ha, hMa⟩ := ltPS_ltExpPS hM hN h
  have hNlen : 1 < Lng N := one_lt_lng_of_ltPS hM hN h
  cases a with
  | nil => exact absurd rfl hane
  | cons n a =>
      have hn : 1 ≤ n := ha n (by simp)
      have hd : lessBT (PSS.Trans (oper N n)) (PSS.Trans N) = true :=
        Trans_fseq_descend N n hN.1 hn hNlen
      have hle := trans_leBT_expand a (oper N n) (STPS.oper hN.1 n hn)
        (fun k hk => ha k (by simp [hk]))
      rw [hMa, expand]
      exact leBT_lessBT_trans hle hd

end Bijectivity
