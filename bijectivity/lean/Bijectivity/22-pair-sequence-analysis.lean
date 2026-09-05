import Bijectivity.«21-ordinal-bijectivity»

/-!
# 系（ペア数列の解析）

原文:
(1) 任意の \(M\in CT_{\textrm{PS}}\) に対して、\(o\circ\textrm{Trans}\) は同型写像
\((\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\},<_{\textrm{PS}})
\to(\{\alpha\mid\alpha\in o(\textrm{Trans}(M))\},\in)\) である。
(2) 任意の \(M\in CT_{\textrm{PS}}\) に対して、\(\textrm{Trans}\) は同型写像
\((\{N\mid N\in CT_{\textrm{PS}}\land N<_{\textrm{PS}}M\},<_{\textrm{PS}})
\to(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}\textrm{Trans}(M)\},<_{\textrm{B}})\)
である。

原文の証明:
> (1) \(\textrm{Trans}\) が順序を保つこと 及び 変換写像の順序数への全単射性 より即座に従う。
> (2) 対応する項の上界 (1)(2)、対応する項の上界未満の字母、[4] Lemma 2.2(c) 及び 2.3(b) より
> \(o\) は \(\{t\mid t<_{\textrm{B}}D_0D_\omega0\}\to\psi_0\psi_\omega0\) の同型写像。
> \(\textrm{Trans}=o^{-1}\circ o\circ\textrm{Trans}\) であるから (1) より従う。□

## 状態

**全域性（`MapsTo`）と単射性（`InjOn`）は (1)(2) とも証明済み**。
全射性（`SurjOn`）は `21` の全射性待ち。
-/

namespace Bijectivity

open PSS

/-! ## (1) 順序数側 -/

/-- (1) の全域性。 -/
theorem analysis_ordinal_mapsTo {M : PS} (hM : CTPS M) :
    Set.MapsTo (fun N => o (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M}
      {α : Ordinal | α < o (PSS.Trans M)} := by
  rintro N ⟨hN, hlt⟩
  exact o_lt_of_lessBT (trans_lessBT_of_ltPS hN hM hlt)

/-- (1) の単射性。 -/
theorem analysis_ordinal_injOn {M : PS} :
    Set.InjOn (fun N => o (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M} :=
  fun _ hN _ hN' h => oTrans_injOn hN.1 hN'.1 h

/-- (1) の全射性。`21` の全射性と \(\textrm{Trans}\) が順序を保つことから従う。 -/
theorem analysis_ordinal_surjOn {M : PS} (hM : CTPS M) :
    Set.SurjOn (fun N => o (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M}
      {α : Ordinal | α < o (PSS.Trans M)} := by
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  have hbound : α < psi0psiOmega0 := lt_trans hα (oTrans_mapsTo hM)
  obtain ⟨N, hN, hNo⟩ := oTrans_surjOn hbound
  have hNo' : o (PSS.Trans N) = α := hNo
  refine ⟨N, ⟨hN, ?_⟩, hNo⟩
  by_contra hc
  rcases ltPS_trichotomy N M with h1 | h1 | h1
  · exact hc h1
  · rw [h1] at hNo'
    rw [hNo'] at hα
    exact absurd hα (lt_irrefl _)
  · have hlt2 := o_lt_of_lessBT (trans_lessBT_of_ltPS hM hN h1)
    rw [hNo'] at hlt2
    exact absurd (lt_trans hlt2 hα) (lt_irrefl _)

/-- 原文の系（ペア数列の解析）(1)。 -/
theorem analysis_ordinal {M : PS} (hM : CTPS M) :
    Set.BijOn (fun N => o (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M}
      {α : Ordinal | α < o (PSS.Trans M)} :=
  ⟨analysis_ordinal_mapsTo hM, analysis_ordinal_injOn, analysis_ordinal_surjOn hM⟩

/-! ## (2) 項側 -/

/-- (2) の全域性。 -/
theorem analysis_term_mapsTo {M : PS} (hM : CTPS M) :
    Set.MapsTo PSS.Trans {N : PS | CTPS N ∧ N <ₚ M}
      {t : BT | t ∈ OT ∧ lessBT t (PSS.Trans M) = true} := by
  rintro N ⟨hN, hlt⟩
  exact ⟨(Trans_STPS_OT_B N hN.1).1, trans_lessBT_of_ltPS hN hM hlt⟩

/-- (2) の単射性。 -/
theorem analysis_term_injOn {M : PS} :
    Set.InjOn PSS.Trans {N : PS | CTPS N ∧ N <ₚ M} :=
  fun _ hN _ hN' h => trans_injOn hN.1 hN'.1 h

/-- [4] Lemma 2.2(c) より \(o\) は単射（\(<_{\textrm{B}}\) の三分律から従う）。 -/
theorem o_injective {a b : BT} (h : o a = o b) : a = b := by
  rcases lessBT_linear_trichotomy a b with h1 | h1 | h1
  · have hlt := o_lt_of_lessBT h1
    rw [h] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact h1
  · have hlt := o_lt_of_lessBT h1
    rw [h] at hlt
    exact absurd hlt (lt_irrefl _)

/-- (2) の全射性。(1) の全射性と \(o\) の単射性から従う。 -/
theorem analysis_term_surjOn {M : PS} (hM : CTPS M) :
    Set.SurjOn PSS.Trans {N : PS | CTPS N ∧ N <ₚ M}
      {t : BT | t ∈ OT ∧ lessBT t (PSS.Trans M) = true} := by
  rintro t ⟨htOT, htlt⟩
  have hα : o t < o (PSS.Trans M) := o_lt_of_lessBT htlt
  obtain ⟨N, hN, hNo⟩ := analysis_ordinal_surjOn hM hα
  exact ⟨N, hN, o_injective hNo⟩

/-- 原文の系（ペア数列の解析）(2)。 -/
theorem analysis_term {M : PS} (hM : CTPS M) :
    Set.BijOn PSS.Trans {N : PS | CTPS N ∧ N <ₚ M}
      {t : BT | t ∈ OT ∧ lessBT t (PSS.Trans M) = true} :=
  ⟨analysis_term_mapsTo hM, analysis_term_injOn, analysis_term_surjOn hM⟩

end Bijectivity
