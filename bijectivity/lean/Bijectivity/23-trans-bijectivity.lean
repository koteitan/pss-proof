import Bijectivity.«22-pair-sequence-analysis»

/-!
# 定理（変換写像の全単射性）— 主定理

原文: \(\textrm{Trans}\) は
\(CT_{\textrm{PS}}\to\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\)
上で全域かつ全単射であり、特に同型写像である。

原文の証明:
> 可算な標準形の起源 及び 辞書式的順序が基本列的順序を含意すること より任意の
> \(M\in CT_{\textrm{PS}}\) に対してある \(v\) が存在して
> \(M\leq_{\textrm{PS}}((j,j))_{j=0}^v<_{\textrm{PS}}((j,j))_{j=0}^{v+1}\in CT_{\textrm{PS}}\)
> であるから、\(CT_{\textrm{PS}}=\bigcup_{M}\{N\mid N<_{\textrm{PS}}M\}\) である。
> [4] の Lemma 2.1 より値域側も同様に分解でき、対応する項の上界 (2) より
> \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}
> =\bigcup_{M\in CT_{\textrm{PS}}}\{t\mid t<_{\textrm{B}}\textrm{Trans}(M)\}\) である。
> ペア数列の解析 (2) より従う。□

`OT_{\textrm{B}\omega}` は \(D_\omega\) を許す順序数項の集合であり、既存の `PSS.OT`
がそのまま該当する（`isOT_BT` は \(D_\omega\)-自由性を要求しない）。

## 状態

* 同型写像であること（`trans_order_iso`）: **証明済み**
* 全域性（`MapsTo`）・単射性（`InjOn`）: **証明済み**
* 定義域・値域の被覆（原文の \(CT_{\textrm{PS}}=\bigcup\cdots\) と
  値域の \(\bigcup\cdots\)）: **証明済み**
* 全射性（`SurjOn`）: 原文どおり ペア数列の解析 (2) に帰着済み。
  そちらは `21` の全射性待ち。
-/

namespace Bijectivity

open PSS

/-- 原文の主定理の値域 \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\)。 -/
def TransRange : Set BT := {t | t ∈ OT ∧ lessBT t DzeroDomegaZero = true}

/-! ## 原文の被覆 -/

/-- 原文「\(CT_{\textrm{PS}}=\bigcup_{M}\{N\mid N<_{\textrm{PS}}M\}\)」。
可算な標準形の起源 と 対角列の始切片 から、どの元にも真に大きい元がある。 -/
theorem ctps_cover {M : PS} (hM : CTPS M) : ∃ N : PS, CTPS N ∧ M <ₚ N := by
  obtain ⟨v, hv⟩ := (ctps_iff_leExpPS M).mp hM
  refine ⟨diagSeq 0 (v + 1), ctps_diagSeq (v + 1), ?_⟩
  have hstep : diagSeq 0 v <ₚ diagSeq 0 (v + 1) := by
    have hlen : Lng (diagSeq 0 (v + 1)) = v + 2 := by
      rw [length_diagSeq]; omega
    have := ltPS_take (diagSeq 0 (v + 1)) (k := v + 1) (by rw [hlen]; omega)
    rwa [diagSeq_take (Nat.le_succ v)] at this
  obtain ⟨a, ha, hMa⟩ := hv
  have hMle : M ≤ₚ diagSeq 0 v := by
    rw [hMa]; exact expand_lePS a _ ha
  exact lePS_ltPS_trans hMle hstep

/-- 原文「値域 \(=\bigcup_{M\in CT_{\textrm{PS}}}\{t\mid t<_{\textrm{B}}\textrm{Trans}(M)\}\)」。
対応する項の上界未満の字母 と 対応する項の上界 (2) から従う。 -/
theorem transRange_cover {t : BT} (ht : t ∈ TransRange) :
    ∃ M : PS, CTPS M ∧ lessBT t (PSS.Trans M) = true := by
  have htB : t ∈ T_B := ((OT_iff_OT_B_of_lt ht.2).mp ht.1).2
  exact exists_trans_gt htB ht.2

/-! ## 全域性・単射性 -/

/-- 主定理の全域性: [1] の \(\textrm{Trans}\) が標準形を保つこと と
命題（対応する項の上界）(1)。 -/
theorem trans_mapsTo : Set.MapsTo PSS.Trans {M : PS | CTPS M} TransRange := by
  intro M hM
  exact ⟨(Trans_STPS_OT_B M hM.1).1, trans_lt_bound hM⟩

/-- 主定理の単射性（`21` の `trans_injOn`）。 -/
theorem trans_bij_injOn : Set.InjOn PSS.Trans {M : PS | CTPS M} := trans_injOn

/-! ## 全射性（ペア数列の解析 (2) へ帰着） -/

/-- 主定理の全射性。原文どおり 系（ペア数列の解析）(2) に帰着する。 -/
theorem trans_surjOn : Set.SurjOn PSS.Trans {M : PS | CTPS M} TransRange := by
  intro t ht
  obtain ⟨M, hM, hlt⟩ := transRange_cover ht
  have hmem : t ∈ {t : BT | t ∈ OT ∧ lessBT t (PSS.Trans M) = true} := ⟨ht.1, hlt⟩
  obtain ⟨N, hN, hNt⟩ := analysis_term_surjOn hM hmem
  exact ⟨N, hN.1, hNt⟩

/-- 定理（変換写像の全単射性）: \(\textrm{Trans}\) は
\(CT_{\textrm{PS}}\) から `TransRange` への全単射である。 -/
theorem trans_bijOn : Set.BijOn PSS.Trans {M | CTPS M} TransRange :=
  ⟨trans_mapsTo, trans_bij_injOn, trans_surjOn⟩

/-- 定理（変換写像の全単射性）: 特に同型写像であること。

原文の証明の単射性の部分（「\(\textrm{Trans}\) が順序を保つこと、[4] Lemma 2.1
及び 2.2(c) より単射」）にあたる。順序の三分律と \(<_{\textrm{B}}\) の線形性から従う。 -/
theorem trans_order_iso {M N : PS} (hM : CTPS M) (hN : CTPS N) :
    M <ₚ N ↔ lessBT (PSS.Trans M) (PSS.Trans N) = true := by
  constructor
  · exact trans_lessBT_of_ltPS hM hN
  · intro h
    rcases ltPS_trichotomy M N with h1 | rfl | h1
    · exact h1
    · simp [lessBT_linear_irrefl] at h
    · have := lessBT_linear_trans _ _ _ h (trans_lessBT_of_ltPS hN hM h1)
      simp [lessBT_linear_irrefl] at this

end Bijectivity
