import Bijectivity.Defs

/-!
# 命題（基本列的順序が推移性）

原文: \(<_{\textrm{PS}[]}\) 及び \(\leq_{\textrm{PS}[]}\) は推移律を満たす。

原文の証明:
> 任意の \(M,N,O\in T_{\textrm{PS}}\) を取り、\(M\leq_{\textrm{PS}[]}N\) かつ
> \(N\leq_{\textrm{PS}[]}O\) であるとする。
> \(\leq_{\textrm{PS}[]}\) の定義より、ある \(a,b\in\mathbb{N}_+^{<\omega}\) が存在して
> \(M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\) かつ
> \(N=O[b_0]\cdots[b_{\textrm{Lng}(b)-1}]\) である。
> 上より \(M=O[b_0]\cdots[b_{\textrm{Lng}(b)-1}][a_0]\cdots[a_{\textrm{Lng}(a)-1}]\)
> であるから \(M\leq_{\textrm{PS}[]}O\) である。
> 従って \(\leq_{\textrm{PS}[]}\) は推移律を満たす。また \(<_{\textrm{PS}[]}\) の
> 推移性も同様に導かれる。□

この証明の要は「添字列の連結」であり、それを `expand_append` として切り出す。
-/

namespace Bijectivity

open PSS

/-- 添字列の連結: \(N[b_0]\cdots[a_0]\cdots = (N[b_0]\cdots)[a_0]\cdots\)。 -/
theorem expand_append (N : PS) (b a : List ℕ) :
    expand N (b ++ a) = expand (expand N b) a := by
  induction b generalizing N with
  | nil => simp [expand]
  | cons n b ih => simp [expand, ih]

/-- 原文の命題（基本列的順序が推移性）、\(\leq_{\textrm{PS}[]}\) の側。 -/
theorem leExpPS_trans {M N O : PS} (hMN : M ≤ₚ[] N) (hNO : N ≤ₚ[] O) : M ≤ₚ[] O := by
  obtain ⟨a, ha, rfl⟩ := hMN
  obtain ⟨b, hb, rfl⟩ := hNO
  refine ⟨b ++ a, ?_, ?_⟩
  · intro n hn
    rcases List.mem_append.mp hn with h | h
    · exact hb n h
    · exact ha n h
  · exact (expand_append O b a).symm ▸ rfl

/-- 原文の命題（基本列的順序が推移性）、\(<_{\textrm{PS}[]}\) の側。 -/
theorem ltExpPS_trans {M N O : PS} (hMN : M <ₚ[] N) (hNO : N <ₚ[] O) : M <ₚ[] O := by
  obtain ⟨a, hane, ha, rfl⟩ := hMN
  obtain ⟨b, hbne, hb, rfl⟩ := hNO
  refine ⟨b ++ a, ?_, ?_, ?_⟩
  · exact List.append_ne_nil_of_left_ne_nil hbne a
  · intro n hn
    rcases List.mem_append.mp hn with h | h
    · exact hb n h
    · exact ha n h
  · exact (expand_append O b a).symm ▸ rfl

end Bijectivity
