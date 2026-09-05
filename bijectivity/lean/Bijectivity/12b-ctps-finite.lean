import Bijectivity.«12a-lex-toolkit»
import «6».«6.6-condAB-coeff»
import «6».«6.6-reduced-coeff»
import «6».«6.7-standard-reduced»
import «6».«6.7-standard-prefix»
import Mathlib.Order.WellFoundedSet

/-!
# 補助（`CT_PS` の係数評価と有限性）

原文 基本列的順序が辞書式的順序を含意すること の内側の帰納法は

> [1] の簡約性と係数の関係、条件(A)と(B)と係数の基本性質(1)及び(2)、標準形の簡約性
> 及び \(CT_{\textrm{PS}}\) の定義より任意の \(M'\in CT_{\textrm{PS}}\) に対して、
> \(\textrm{Lng}(M')=\textrm{Lng}(N)\) ならば \(M'_{1,j_1^N}\leq M'_{0,j_1^N}\leq j_1^N\)
> である。
> 従って \(\textrm{Lng}(M')=\textrm{Lng}(N)\) かつ
> \((M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\) である \(M'\in CT_{\textrm{PS}}\)
> は高々 \((j_1^N)^2\) 個である。

という有限性を使う。ここで引かれる [1]（= ペア数列の停止性）の事実は本リポジトリの
`6/6.6-reduced-coeff.lean`, `6/6.6-condAB-coeff.lean`, `6/6.7-standard-reduced.lean`
に既にある。

原文は「長さと先頭 \(j_1^N\) 項を固定した集合」で帰納するが、その最大元における
基底段階が原文では扱われていない。ここでは代わりに「長さ \(L\) 以下の
\(CT_{\textrm{PS}}\) の元全体」（これも有限）で下降帰納する。この集合で取ると、
最大元では帰納法の主張が空虚に成り立つので基底段階が自動的に閉じる。
-/

namespace Bijectivity

open PSS

/-- `CT_PS` の元の最左列は `(0,0)`。 -/
theorem ctps_entry_zero {M : PS} (h : CTPS M) : entry M 0 0 = 0 ∧ entry M 1 0 = 0 := by
  obtain ⟨hst, hhd⟩ := h
  have hM : TPS M := STPS_TPS M hst
  cases M with
  | nil => exact absurd rfl hM
  | cons p Q =>
      simp only [List.headD_cons] at hhd
      subst hhd
      simp [entry]

/-- 原文が [1] から引く係数の評価: \(M\in CT_{\textrm{PS}}\) なら
\(M_{1,j}\leq M_{0,j}\leq j\)。 -/
theorem ctps_coeff {M : PS} (h : CTPS M) {j : ℕ} (hj : j < Lng M) :
    entry M 1 j ≤ entry M 0 j ∧ entry M 0 j ≤ j := by
  have hst := h.1
  have hM : TPS M := STPS_TPS M hst
  have hR : RTPS M := STPS_RTPS M hst
  obtain ⟨hA, _⟩ := RTPS_condAB M hR
  exact ⟨reduced_coeff M hR j hj,
    RedCondA_row0_le_index M hM (ctps_entry_zero h).1 hA j hj⟩

/-- 添字の範囲外も込めた係数評価。 -/
theorem ctps_entry_le {M : PS} (h : CTPS M) (j : ℕ) :
    entry M 0 j ≤ j ∧ entry M 1 j ≤ j := by
  by_cases hj : j < Lng M
  · obtain ⟨h1, h0⟩ := ctps_coeff h hj
    omega
  · have hnone : M[j]? = none := List.getElem?_eq_none (by simp only [Lng] at hj ⊢; omega)
    simp [entry, hnone]

/-- 長さ `L` 以下の `CT_PS` の元は有限個。原文の「高々 \((j_1^N)^2\) 個」に対応する。 -/
theorem ctps_finite (L : ℕ) : {M : PS | CTPS M ∧ Lng M ≤ L}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.finite_range (fun x : Fin (L + 1) × (Fin L → Fin (L + 1) × Fin (L + 1)) =>
      (List.range x.1.val).map (fun j =>
        if h : j < L then (((x.2 ⟨j, h⟩).1.val, (x.2 ⟨j, h⟩).2.val)) else (0, 0)))) ?_
  rintro M ⟨hM, hlen⟩
  simp only [Lng] at hlen
  have hb := ctps_entry_le hM
  refine ⟨(⟨M.length, by omega⟩,
    fun i => (⟨entry M 0 i.val, by have := (hb i.val).1; omega⟩,
              ⟨entry M 1 i.val, by have := (hb i.val).2; omega⟩)), ?_⟩
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hjM : j < M.length := by simpa using h1
    have hjL : j < L := by omega
    simp only [List.getElem_map, List.getElem_range, hjL, dif_pos]
    have := pairAt_eq_getElem M (show j < Lng M by simpa using hjM)
    simpa [pairAt] using this

/-- `<ₚ` の逆向きは、長さ `L` 以下の `CT_PS` 上で整礎（下降帰納が使える）。 -/
theorem ctps_wf (L : ℕ) :
    WellFounded (fun X Y : PS =>
      Y <ₚ X ∧ (CTPS X ∧ Lng X ≤ L) ∧ (CTPS Y ∧ Lng Y ≤ L)) := by
  letI : IsStrictOrder PS (fun X Y : PS => Y <ₚ X) :=
    { irrefl := fun a h => ltPS_irrefl a h
      trans := fun _ _ _ hab hbc => ltPS_trans hbc hab }
  exact Set.wellFoundedOn_iff.mp ((ctps_finite L).wellFoundedOn)

end Bijectivity
