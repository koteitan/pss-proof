import Bijectivity.«03-exp-order-transitive»
import Bijectivity.«04-fseq-lex-decreasing»

/-!
# 命題（辞書式的順序が基本列的順序を含意すること）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}[]}N\) ならば
\(M<_{\textrm{PS}}N\) である。

原文の証明:
> \(<_{\textrm{PS}[]}\) の定義よりある \(a\in\mathbb{N}_+^{<\omega}\setminus\{()\}\)
> が存在して \(M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\) である。
> \(N=(0,0)\) とすると、任意の \(n\) に対して \(N[n]=N\) であるから \(M=N\) となり、
> これは条件と反するから \(N\neq(0,0)\) である。上より \(\textrm{Lng}(N)>1\) である。
> \(Q_0=N\)、\(Q_{i+1}=Q_i[a_i]\) とすると 基本列の辞書式的縮小性 より
> \(Q_1<_{\textrm{PS}}N\)。帰納法と 辞書式的順序の線形性 より
> \(Q_{i+1}\leq_{\textrm{PS}}Q_i<_{\textrm{PS}}N\)。
> よって \(M=Q_{\textrm{Lng}(a)}<_{\textrm{PS}}N\)。□

## 訂正候補: 原文の言明は逐語形では偽

原文の証明は「\(M=N\) は条件と反する」と述べるが、\(<_{\textrm{PS}[]}\) の定義
（\(a\neq()\) なる \(a\) の存在）からは \(M\neq N\) は従わない。反例:

* \(N=((0,0))\in CT_{\textrm{PS}}\)、\(a=(1)\)。\(\textrm{Lng}(N)=1\) なので
  \(N[1]=N\)、よって \(M=N\)。このとき \(M<_{\textrm{PS}[]}N\) は成り立つが
  \(M<_{\textrm{PS}}N\) は偽である。

すなわち \(<_{\textrm{PS}[]}\) は狭義でなく、\(M\neq N\)（あるいは
\(\textrm{Lng}(N)>1\)）を補う必要がある。補った形を `ltExpPS_ltPS_of_lng` として、
逐語形が**偽であること自体**を `not_ltExpPS_ltPS` として与える（`sorry` は使わない）。
-/

namespace Bijectivity

open PSS

/-- 反復展開は \(\leq_{\textrm{PS}}\) を下げる。原文の \(Q_i\) の帰納に対応する。 -/
theorem expand_lePS : ∀ (a : List ℕ) (N : PS), (∀ n ∈ a, 1 ≤ n) → expand N a ≤ₚ N
  | [], N, _ => Or.inl rfl
  | n :: a, N, ha => by
      refine lePS_trans (expand_lePS a (oper N n) ?_) (oper_lePS N n (ha n (by simp)))
      intro m hm; exact ha m (by simp [hm])

/-- \(\textrm{Lng}(N)\leq1\) なら展開はすべて自明で、反復しても \(N\) のまま。 -/
theorem expand_of_lng_le_one : ∀ (a : List ℕ) {N : PS}, Lng N ≤ 1 → expand N a = N
  | [], _, _ => rfl
  | n :: a, N, hN => by
      have hop : oper N n = N := by
        have : Lng N - 1 = 0 := by omega
        simp [oper, this]
      rw [expand, hop, expand_of_lng_le_one a hN]

/-- \(((0,0))\in CT_{\textrm{PS}}\)。 -/
theorem ctps_zero_singleton : CTPS ([((0 : ℕ), (0 : ℕ))] : PS) := by
  refine ⟨?_, rfl⟩
  have h : ([((0 : ℕ), (0 : ℕ))] : PS) = diagSeq 0 0 := rfl
  rw [h]
  exact STPS.diag 0 0 (le_refl 0)

/-- **原文の命題（辞書式的順序が基本列的順序を含意すること）の逐語形は偽**（訂正 `B1`）。

反例は \(M=N=((0,0))\)、\(a=(1)\)。\(\textrm{Lng}(N)=1\) なので \(N[1]=N\) であり、
\(a\neq()\) だから \(M<_{\textrm{PS}[]}N\) は成り立つが \(M=N\) なので
\(M<_{\textrm{PS}}N\) は偽である。訂正形は下の `ltExpPS_ltPS_of_lng`。 -/
theorem not_ltExpPS_ltPS :
    ¬ (∀ M N : PS, CTPS M → CTPS N → M <ₚ[] N → M <ₚ N) := by
  intro h
  have hlt : ([((0 : ℕ), (0 : ℕ))] : PS) <ₚ[] [((0 : ℕ), (0 : ℕ))] :=
    ⟨[1], by simp, by simp, (expand_of_lng_le_one [1] (by simp [Lng])).symm⟩
  exact ltPS_irrefl _ (h _ _ ctps_zero_singleton ctps_zero_singleton hlt)

/-- 訂正形: \(\textrm{Lng}(N)>1\) を補うと原文の証明がそのまま通る。 -/
theorem ltExpPS_ltPS_of_lng {M N : PS} (hN : 1 < Lng N) (h : M <ₚ[] N) : M <ₚ N := by
  obtain ⟨a, hane, ha, rfl⟩ := h
  cases a with
  | nil => exact absurd rfl hane
  | cons n a =>
      have h1 : oper N n <ₚ N := oper_ltPS hN n (ha n (by simp))
      have h2 : expand (oper N n) a ≤ₚ oper N n := by
        refine expand_lePS a (oper N n) ?_
        intro m hm; exact ha m (by simp [hm])
      rcases h2 with he | hlt
      · simpa [expand, he] using h1
      · simpa [expand] using ltPS_trans hlt h1

end Bijectivity
