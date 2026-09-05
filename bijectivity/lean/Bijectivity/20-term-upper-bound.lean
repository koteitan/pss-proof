import Bijectivity.«19-alphabet-below-bound»
import Bijectivity.«18-trans-preserves-order»
import Bijectivity.«10-countable-standard-origin»
import «8».«8.1-diagSeq-Trans»

/-!
# 命題（対応する項の上界）

原文:
(1) 任意の \(M\in CT_{\textrm{PS}}\) に対して \(\textrm{Trans}(M)<_{\textrm{B}}D_0D_\omega0\)。
(2) 任意の \(t\in T_{\textrm{B}}\) に対して、\(t<_{\textrm{B}}D_0D_\omega0\) ならば
ある \(M\in CT_{\textrm{PS}}\) が存在して \(t<_{\textrm{B}}\textrm{Trans}(M)\)。

原文の証明 (1):
> 可算な標準形の起源 より \(M\leq_{\textrm{PS}[]}((j,j))_{j=0}^v\) なる \(v\) が取れ、
> 辞書式的順序が基本列的順序を含意すること より \(M\leq_{\textrm{PS}}((j,j))_{j=0}^v\)。
> [1] の公差 \((1,1)\) のペア数列の \(\textrm{Trans}\) の基本性質より
> \(\textrm{Trans}(((j,j))_{j=0}^v)=D_0D_v0<_{\textrm{B}}D_0D_\omega0\)。
> \(\textrm{Trans}\) が順序を保つこと より
> \(\textrm{Trans}(M)<_{\textrm{B}}\textrm{Trans}(((j,j))_{j=0}^v)<_{\textrm{B}}D_0D_\omega0\)。□

原文の証明 (2):
> 任意の \(t'\in T_{\textrm{B}}\) をとる。\(t'=0\) なら \(t'<_{\textrm{B}}D_00\)。
> \(t'=D_ua\) または \(t'=\underline{(}D_ua\underline{,}s\underline{)}\) なら
> \(t'<_{\textrm{B}}D_{u+1}0\)。よっていずれの場合でもある \(u\in\mathbb{N}\) が存在して
> \(t'<_{\textrm{B}}D_u0\)。
> \(t=0\) なら \(t<_{\textrm{B}}D_00\)。\(t=D_0a\) または
> \(t=\underline{(}D_0a\underline{,}s\underline{)}\) なら、上よりある \(u\) が存在して
> \(a<_{\textrm{B}}D_u0\) なので \(t<_{\textrm{B}}D_0D_u0\)。
> [1] の公差 \((1,1)\) のペア数列の \(\textrm{Trans}\) の基本性質より
> \(D_0D_u0=\textrm{Trans}(((j,j))_{j=0}^u)\)。□

[1] の公差 \((1,1)\) のペア数列の \(\textrm{Trans}\) の基本性質は本リポジトリの
`8/8.1-diagSeq-Trans.lean` の `diagSeq_Trans`。
-/

namespace Bijectivity

open PSS

/-! ## \(D_0D_u0\) の比較 -/

theorem lessBPList_nil_right : ∀ ps : List BP, lessBPList ps [] = false
  | [] => rfl
  | _ :: _ => rfl

/-- \(D_0D_v0<_{\textrm{B}}D_0D_\omega0\)。 -/
theorem DD_lt_DDomega (v : ℕ) :
    lessBT (Dprin 0 (Dprin (v : ℕ∞) BZero)) DzeroDomegaZero = true := by
  simp [DzeroDomegaZero, Dprin, BZero, lessBT, lessBPList, lessBP]

/-- \(u<v\) なら \(D_0D_u0<_{\textrm{B}}D_0D_v0\)。 -/
theorem DD_mono {u v : ℕ} (h : u < v) :
    lessBT (Dprin 0 (Dprin (u : ℕ∞) BZero)) (Dprin 0 (Dprin (v : ℕ∞) BZero)) = true := by
  simp [Dprin, BZero, lessBT, lessBPList, lessBP, h]

/-- \(\textrm{Trans}(((j,j))_{j=0}^{v})=D_0D_v0\)（`8.1-diagSeq-Trans` の言い換え）。 -/
theorem Trans_diagSeq_zero (v : ℕ) (hv : 0 < v) :
    PSS.Trans (diagSeq 0 v) = Dprin 0 (Dprin (v : ℕ∞) BZero) := by
  simpa using diagSeq_Trans 0 v hv

/-- 対角列は \(CT_{\textrm{PS}}\) の元。 -/
theorem ctps_diagSeq (v : ℕ) : CTPS (diagSeq 0 v) :=
  ⟨STPS.diag 0 v (Nat.zero_le v), headD_diagSeq (Nat.zero_le v)⟩

/-! ## (1) -/

/-- 原文の命題（対応する項の上界）(1)。 -/
theorem trans_lt_bound {M : PS} (hM : CTPS M) :
    lessBT (PSS.Trans M) DzeroDomegaZero = true := by
  obtain ⟨v, hv⟩ := (ctps_iff_leExpPS M).mp hM
  have hv1 : M ≤ₚ[] diagSeq 0 (v + 1) :=
    leExpPS_trans hv (diagSeq_leExpPS (Nat.le_succ v))
  have hD : CTPS (diagSeq 0 (v + 1)) := ctps_diagSeq (v + 1)
  have hle : leBT (PSS.Trans M) (PSS.Trans (diagSeq 0 (v + 1))) = true := by
    obtain ⟨a, ha, hMa⟩ := hv1
    have hM2 : M ≤ₚ diagSeq 0 (v + 1) := by
      rw [hMa]; exact expand_lePS a _ ha
    rcases hM2 with heq | hlt
    · rw [heq]; exact leBT_refl _
    · simp [leBT, trans_lessBT_of_ltPS hM hD hlt]
  rw [Trans_diagSeq_zero (v + 1) (by omega)] at hle
  exact leBT_lessBT_trans hle (DD_lt_DDomega (v + 1))

/-! ## (2) -/

/-- 原文の補助主張: \(T_{\textrm{B}}\) の項はある \(D_u0\) 未満。 -/
theorem exists_index_bound {t : BT} (ht : t ∈ T_B) :
    ∃ u : ℕ, lessBT t (Dprin (u : ℕ∞) BZero) = true := by
  cases t with
  | trm ps =>
    cases ps with
    | nil => exact ⟨0, by simp [lessBT, lessBPList, Dprin]⟩
    | cons p rest =>
      cases p with
      | db w a =>
        have hd : dfree_BT (BT.trm (BP.db w a :: rest)) = true := ht
        simp only [dfree_BT, dfree_BPList, dfree_BP, Bool.and_eq_true, bne_iff_ne,
          ne_eq] at hd
        obtain ⟨u0, rfl⟩ := WithTop.ne_top_iff_exists.mp hd.1.1
        refine ⟨u0 + 1, ?_⟩
        have hlt : (u0 : ℕ∞) < (u0 : ℕ∞) + 1 := by exact_mod_cast Nat.lt_succ_self u0
        simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq, Nat.cast_add, Nat.cast_one]
        exact Or.inl (Or.inl hlt)

/-- 原文の命題（対応する項の上界）(2)。 -/
theorem exists_trans_gt {t : BT} (ht : t ∈ T_B) (h : lessBT t DzeroDomegaZero = true) :
    ∃ M : PS, CTPS M ∧ lessBT t (PSS.Trans M) = true := by
  have key : ∃ u : ℕ, lessBT t (Dprin 0 (Dprin (u : ℕ∞) BZero)) = true := by
    cases t with
    | trm ps =>
      cases ps with
      | nil => exact ⟨0, by simp [lessBT, lessBPList, Dprin]⟩
      | cons p rest =>
        cases p with
        | db w a =>
          have hd : dfree_BT (BT.trm (BP.db w a :: rest)) = true := ht
          simp only [dfree_BT, dfree_BPList, dfree_BP, Bool.and_eq_true, bne_iff_ne,
            ne_eq] at hd
          obtain ⟨u0, rfl⟩ := WithTop.ne_top_iff_exists.mp hd.1.1
          -- 上界より先頭の添字は 0
          simp only [DzeroDomegaZero, Dprin, lessBT, lessBPList, lessBP,
            lessBPList_nil_right, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq, Bool.false_eq_true, and_false, or_false] at h
          have hu0 : u0 = 0 := by
            rcases h with h | ⟨h1, _⟩
            · exact absurd h (by simp)
            · exact WithTop.coe_eq_zero.mp h1
          subst hu0
          obtain ⟨u, hu⟩ := exists_index_bound (t := a) hd.1.2
          refine ⟨u, ?_⟩
          simp only [Dprin] at hu
          simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq]
          exact Or.inl (Or.inr ⟨rfl, hu⟩)
  obtain ⟨u, hu⟩ := key
  refine ⟨diagSeq 0 (u + 1), ctps_diagSeq (u + 1), ?_⟩
  rw [Trans_diagSeq_zero (u + 1) (by omega)]
  exact lessBT_linear_trans _ _ _ hu (DD_mono (by omega))

end Bijectivity
