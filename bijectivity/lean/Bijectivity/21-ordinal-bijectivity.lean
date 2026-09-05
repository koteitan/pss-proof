import Bijectivity.«17-fseq-convergence»
import Bijectivity.«18-trans-preserves-order»
import Bijectivity.«20-term-upper-bound»

/-!
# 命題（変換写像の順序数への全単射性）

原文: \(o\circ\textrm{Trans}\) は \(CT_{\textrm{PS}}\to\psi_0\psi_\omega0\) 上で
全域かつ全単射である。

原文の証明:
> 対応する項の上界未満の字母、対応する項の上界 (1)(2) 及び [1] の \(\textrm{Trans}\) が
> 標準形を保つことより \(\{\textrm{Trans}(M)\}\) は
> \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\) の
> \(<_{\textrm{B}}\) に対して非有界な部分集合である。
> [4] Lemma 2.2(c) より \(\{o(\textrm{Trans}(M))\}\) は \(\psi_0\psi_\omega0\) の
> 非有界な部分集合である。
> [4] Lemma 2.3(b) 及び [5] Lemma 1.6 より \(\textrm{dom}(t)=\textrm{cof}(o(t))\)。
> 後続な項の基本列 より \(\textrm{cof}=1\) の場合、基本列の収束性 より
> \(\textrm{cof}=\omega\) の場合が押さえられ、[3] の命題 11 より全射。
> \(\textrm{Trans}\) が順序を保つこと、[4] Lemma 2.1 及び 2.2(c) より単射。□

## 状態

**全域性（`MapsTo`）と単射性（`InjOn`）は証明済み**。どちらも新たな外部引用を
必要とせず、既に証明した 命題（対応する項の上界）(1) と
命題（\(\textrm{Trans}\) が順序を保つこと）、および `Cited.lean` に既にある
[4] Lemma 2.2(c)（`o_lt_of_lessBT`）だけで閉じる。

**全射性（`SurjOn`）が未証明**。原文の証明どおり 命題（後続な項の基本列）と
命題（基本列の収束性）を使うが、前者は前半が、後者は 補題（基本列の関係）が
それぞれ未証明である。
-/

namespace Bijectivity

open PSS

/-! ## 全域性 -/

/-- 原文の全域性: \(o(\textrm{Trans}(M))<\psi_0\psi_\omega0\)。 -/
theorem oTrans_mapsTo :
    Set.MapsTo (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} := by
  intro M hM
  show o (PSS.Trans M) < psi0psiOmega0
  rw [← o_DzeroDomegaZero]
  exact o_lt_of_lessBT (trans_lt_bound hM)

/-! ## 単射性 -/

/-- 原文の単射性: \(\textrm{Trans}\) が順序を保つこと と \(<_{\textrm{PS}}\) の
三分律（[4] Lemma 2.1 にあたる \(<_{\textrm{B}}\) の線形性）から従う。 -/
theorem trans_injOn : Set.InjOn PSS.Trans {M : PS | CTPS M} := by
  intro M hM N hN h
  rcases ltPS_trichotomy M N with h1 | h1 | h1
  · have hb := trans_lessBT_of_ltPS hM hN h1
    rw [h, lessBT_linear_irrefl] at hb
    exact absurd hb (by simp)
  · exact h1
  · have hb := trans_lessBT_of_ltPS hN hM h1
    rw [h, lessBT_linear_irrefl] at hb
    exact absurd hb (by simp)

/-- \(o\circ\textrm{Trans}\) の単射性（[4] Lemma 2.2(c) を追加で使う）。 -/
theorem oTrans_injOn : Set.InjOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M} := by
  intro M hM N hN h
  simp only at h
  rcases ltPS_trichotomy M N with h1 | h1 | h1
  · exact absurd (o_lt_of_lessBT (trans_lessBT_of_ltPS hM hN h1))
      (by rw [h]; exact lt_irrefl _)
  · exact h1
  · exact absurd (o_lt_of_lessBT (trans_lessBT_of_ltPS hN hM h1))
      (by rw [← h]; exact lt_irrefl _)

/-! ## 全射性（未証明） -/

/-- 原文の全射性。命題（後続な項の基本列）と命題（基本列の収束性）待ち。 -/
theorem oTrans_surjOn :
    Set.SurjOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} := by
  sorry

/-- 原文の命題（変換写像の順序数への全単射性）。 -/
theorem oTrans_bijOn :
    Set.BijOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} :=
  ⟨oTrans_mapsTo, oTrans_injOn, oTrans_surjOn⟩

end Bijectivity
