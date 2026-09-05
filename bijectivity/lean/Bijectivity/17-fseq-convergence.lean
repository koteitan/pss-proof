import Bijectivity.«16-fseq-relation»
import Bijectivity.«15-successor-fseq»
import «8».«8.7-termination»

/-!
# 命題（基本列の収束性）

原文: 任意の \(M\in ST_{\textrm{PS}}\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならば
\(\sup_{n\in\mathbb{N}_+}o(\textrm{Trans}(M[n]))=o(\textrm{Trans}(M))\) である。

原文の証明:
> 基本列の関係、[1] の基本列の降下性、[5] の Theorem 1.4(a) 及び Lemma 1.6 より
> \(\{o(\textrm{Trans}(M[n]))\mid n\in\mathbb{N}_+\}\) は \(o(\textrm{Trans}(M))\) の
> 非有界な部分集合であることから即座に従う。□

形式化もこの 3 つで閉じている。

* 基本列の関係 = `16-fseq-relation.lean` の `fseq_relation`（証明済み）
* [1] の基本列の降下性 = `lean/8/8.7-termination.lean` の `Trans_fseq_descend`（証明済み）
* [5] Theorem 1.4(a) / Lemma 1.6 = `Cited.lean` の `o_iSup_operB`（外部引用）

したがって本命題の外部引用は `o_iSup_operB`（と `o` / `o_lt_of_lessBT`）だけである
（`#print axioms` で確認できる）。
-/

namespace Bijectivity

open PSS

/-- \(\leq_{\textrm{B}}\) は \(o\) で保たれる（[Buc1] Lemma 2.2(c)）。 -/
theorem o_le_of_leBT {a b : BT} (ha : a ∈ OT) (hb : b ∈ OT) (h : leBT a b = true) :
    o a ≤ o b := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | rfl
  · exact le_of_lt (o_lt_of_lessBT ha hb h)
  · exact le_rfl

/-- 原文の命題（基本列の収束性）。 -/
theorem fseq_convergence {M : PS} (hM : STPS M) (hdom : domIsOmega (PSS.Trans M)) :
    ⨆ n : {n : ℕ // 1 ≤ n}, o (PSS.Trans (oper M n.1)) = o (PSS.Trans M) := by
  have hR : RTPS M := STPS_RTPS M hM
  have hlen : 1 < Lng M := one_lt_lng_of_domIsOmega hR hdom
  have hMOT : PSS.Trans M ∈ OT_B := Trans_STPS_OT_B M hM
  have hnOT : ∀ n : ℕ, 1 ≤ n → PSS.Trans (oper M n) ∈ OT_B :=
    fun n hn => Trans_STPS_OT_B _ (STPS.oper hM n hn)
  have hTne : PSS.Trans M ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT M (RTPS_TPS M hR)).2 h0
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    omega
  apply le_antisymm
  · -- [1] の基本列の降下性
    refine Ordinal.iSup_le_iff.mpr ?_
    rintro ⟨n, hn⟩
    exact le_of_lt (o_lt_of_lessBT (hnOT n hn).1 hMOT.1
      (Trans_fseq_descend M n hM hn hlen))
  · -- 基本列の関係 と [5] Theorem 1.4(a) / Lemma 1.6
    rw [← o_iSup_operB hMOT.1 hdom]
    refine Ordinal.iSup_le_iff.mpr ?_
    intro m
    obtain ⟨n, hn, hle⟩ := fseq_relation hM m hdom
    exact (o_le_of_leBT (buchholz_fseq_closed _ m hMOT hTne).1 (hnOT n hn).1 hle).trans
      (Ordinal.le_iSup (fun k : {n : ℕ // 1 ≤ n} => o (PSS.Trans (oper M k.1))) ⟨n, hn⟩)

end Bijectivity
