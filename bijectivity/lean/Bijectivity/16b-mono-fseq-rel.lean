import Bijectivity.«16a-fseq-addBT»
import «8».«8.1-Trans-fseq-condI»
import «8».«8.1-condI-masterCF-chunk5»
import «8».«8.4-Trans-fseq-condIII-IV»
import «8».«8.4-exch84-props»
import «8».«8.4-exch84-regsp»
import «8».«8.4-exch84-noparent»
import «8».«8.4-np-c2decomp»
import «8».«8.4-corner-readouts»
import «8».«8.4-corner-np-value»
import «8».«8.5-Trans-fseq-condV-close»
import «8».«8.6-Trans-fseq-condVI-close»
import «8».«8.7-Trans-preserves-OT»
import «8».«8.7-const00-Trans»

/-!
# 補題（基本列の関係）— 単項の場合

原文の 補題（基本列の関係）の証明のうち \(M\) が単項である部分。原文は

* \(t_1=0\)（Lean では \(j_1=1\)、すなわち 2 列）のとき 2 例を直接計算し、
* \(t_1\neq0\) のとき条件 (I)–(VI) で場合分けして [1] の交換関係を引く

という構成である。本ファイルもその構成をそのまま辿る。

## 原文の 5 つの交換関係と Lean 側の資産

| 条件 | 原文が引く結論 | Lean の無条件供給 |
|---|---|---|
| (I) | (1) \(\textrm{Trans}(M[n])=\textrm{Trans}(M)[n-1]\) | `condI_exchange1`（`8.1-Trans-fseq-condI`）＋ `scx_condI_j0pos_masterCF` |
| (II) | (2) \(\textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n]\) | **未移植**（下の `CondIIFseqRel`） |
| (III)/(IV) | (3) \(\textrm{Trans}(M)[n-1]<_{\textrm{B}}\textrm{Trans}(M[n+1])\) | `Trans_oper_exchange` 第 2 結論（`8.4-Trans-fseq-condIII-IV`） |
| (V) | (3) \(\textrm{Trans}(M)[m_n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])\) | `Trans_oper_exchange_condV_adm_uncond_vc` 第 4 結論（許容枝のみ） |
| (VI) | (2) \(\textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n]\) | `p_8_6_Trans_fseq_condVI_uncond` 第 2 結論 |

条件 (III)/(IV) の「\(j_1\) が段 1 に親を持たない」枝は
`Exch84_noParent_domTag_holds` が \(\textrm{dom}(\textrm{Trans}(M))=T_{e-1}\neq\omega\)
を与えるので、仮定 \(\textrm{dom}(\textrm{Trans}(M))=\omega\) の下では起こらない。

条件 (V) の非許容枝は `ExchV_nf3x` の閉形式から \(m\geq1\) で出る。\(m=0\) だけは
`operB` の添字単調性（下の `OperBNumMono`）を経由する。
-/

namespace Bijectivity

open PSS

/-! ## 残差 `Prop`（Isabelle 名 1:1） -/

/-- Isabelle `y3j_p_8_3_condII_exchange_2` (`isabelle/8/Support_8_C.thy`:15272)。
原文の 条件(II) の下での `Trans` と基本列の交換関係 (2)。Isabelle では
`m_n = if leftDj0 M then n-1 else n-2` なので、目標の添字 `m` に対して
`n = m+1`（`leftDj0`）または `n = m+2` を取れば下の形になる。 -/
def CondIIFseqRel : Prop :=
  ∀ (M : PS) (m : ℕ), STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondII M = true →
    ∃ n, 1 ≤ n ∧ PSS.Trans (oper M n) = operB (PSS.Trans M) (numBT m)

/-- Isabelle `y4_N_mono_le` (`isabelle/8/Support_8_C.thy`:11924)。
`dom(a) = ω` なる順序数項の基本列は添字について広義単調。 -/
def OperBNumMono : Prop :=
  ∀ (a : BT) (m m' : ℕ), a ∈ OT_B → domTag a = BDom.naturals → m ≤ m' →
    leBT (operB a (numBT m)) (operB a (numBT m')) = true

/-! ## 小さな道具 -/

private theorem leBT_of_eq_fr {a b : BT} (h : a = b) : leBT a b = true := by
  simp [leBT, h]

private theorem leBT_of_lessBT_fr {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

private theorem leBT_trans_fr2 {a b c : BT} (h1 : leBT a b = true) (h2 : leBT b c = true) :
    leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lessBT_linear_trans _ _ _ h1 h2)
    · exact Or.inl h1
  · exact h2

private theorem hasParent_nextR_fr (M : PS) (i j : ℕ) (h : hasParent M i j = true) :
    nextR M i (parent M i j) j = true := by
  simp only [hasParent, beq_iff_eq] at h
  have hmem : parent M i j ∈ parents M i j := by
    unfold parent
    cases hl : parents M i j with
    | nil => rw [hl] at h; simp at h
    | cons a as => simp
  exact (show parent M i j < Lng M ∧ nextR M i (parent M i j) j = true by
    simpa [parents, List.mem_filter] using hmem).2

private theorem nextrel0_entry_lt_fr {M : PS} {a c : ℕ} (h : nextrel0 M a c = true) :
    entry M 0 a < entry M 0 c := by
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

private theorem entry0_pos_of_hasParent_fr {M : PS} {j : ℕ}
    (h : hasParent M 0 j = true) : 0 < entry M 0 j := by
  have hn := hasParent_nextR_fr M 0 j h
  simp only [nextR] at hn
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (nextrel0_entry_lt_fr hn)

private theorem numNat_numBT_fr (m : ℕ) : numNat (numBT m) = m := by
  simp [numNat, numBT]

private theorem xseq_zero_fr (b : BT) (w : ℕ∞) : xseq b w 0 = Dprin w BZero := by
  simp [xseq, bOperCore]

private theorem xseq_succ_fr (b : BT) (w : ℕ∞) (i : ℕ) :
    xseq b w (i + 1) = Dprin w (operB b (xseq b w i)) := by
  show bOperCore (.xseq b w (i + 1)) =
    Dprin w (bOperCore (.term b (bOperCore (.xseq b w i))))
  rw [bOperCore.eq_def]

private theorem operB_Dv0_id_fr (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0]

private theorem domTag_Dv0_fr (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  have hv0 : ((v : ℕ∞) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    simpa using (Nat.ne_of_gt hv)
  have hvtop : ((v : ℕ∞) == ⊤) = false := by simp
  simp [domTag, domTagList, domTagBP, Dprin, BZero, hv0, hvtop]

private theorem xseq_Dv0_tower_fr (v : ℕ) (hv : 0 < v) (w : ℕ∞) :
    ∀ i, xseq (Dprin (v : ℕ∞) BZero) w i = (Dprin w)^[i + 1] BZero := by
  intro i
  induction i with
  | zero => simpa using xseq_zero_fr (Dprin (v : ℕ∞) BZero) w
  | succ i ih =>
      rw [xseq_succ_fr, operB_Dv0_id_fr v _ hv, ih,
        Function.iterate_succ_apply' (Dprin w) (i + 1) BZero]

/-- `u < v` のとき `D_u(D_v 0)` の基本列（訂正 A23 後の第 1 種分岐）。 -/
private theorem operB_Du_Dv0_fr (u v m : ℕ) (huv : u < v) :
    operB (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) (numBT m)
      = Dprin (u : ℕ∞) ((Dprin ((v - 1 : ℕ) : ℕ∞))^[m + 1] BZero) := by
  have hv : 0 < v := by omega
  have hne : Dprin (v : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
  have htag : domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := domTag_Dv0_fr v hv
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by norm_cast; omega
  rw [operB_dprin_kind1 hne htag hle, numNat_numBT_fr,
    xseq_Dv0_tower_fr v hv _ m, operB_Dv0_id_fr v _ hv]

private theorem lessBT_BZero_fr {t : BT} (h : t ≠ BZero) : lessBT BZero t = true := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact absurd rfl h
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-- Isabelle `s85b_W_mono_seed`: 塔 `s85b_W` は種について狭義単調。 -/
private theorem s85b_W_mono_seed_fr (u : ℕ) (t : BT) {c c' : BT}
    (h : lessBT c c' = true) :
    ∀ k, lessBT (s85b_W u t c k) (s85b_W u t c' k) = true := by
  intro k
  induction k with
  | zero => simpa [s85b_W, Dprin, lessBT, lessBPList, lessBP] using h
  | succ j ih =>
      simpa [s85b_W, Dprin, lessBT, lessBPList, lessBP] using
        addBT_lt_right_bf t _ _ ih

private theorem nextrel1_entry_lt_fr {M : PS} {a c : ℕ} (h : nextrel1 M a c = true) :
    entry M 1 a < entry M 1 c := by
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-! ## 条件 (I)–(VI) の網羅（`8.7-fseq-descend` の `trans_cond_cases_fd` の複製） -/

private theorem trans_cond_cases_fr (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hL : 1 < Lng M) :
    transCondI M = true ∨ transCondII M = true ∨ transCondIII M = true
      ∨ transCondIV M = true ∨ transCondV M = true ∨ transCondVI M = true := by
  by_cases c1 : transCondI M = true
  · exact Or.inl c1
  by_cases c3 : transCondIII M = true
  · exact Or.inr (Or.inr (Or.inl c3))
  by_cases c5 : transCondV M = true
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c5))))
  by_cases c6 : transCondVI M = true
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c6))))
  have h6 : transCondVI M = false := by simpa using c6
  rcases condII_or_condIV M hR hmono hL (by tauto) h6 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ## 条件 (III)/(IV) producer の無条件供給（`8.7-termination`:253 の複製） -/

private theorem exch84producer_fr : Exch84_condIIIIV_producer :=
  Exch84_condIIIIV_producer_holds
    (Exch84_condIIIIV_pkg_holds
      (exch84slicepkg_of_cornerReadouts_nc2
        (cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv)))

/-! ## 条件 (III)/(IV)

原文が引く結論 (3)。段 1 に親が無い枝は `dom(Trans M) = T_{e-1} ≠ ω` なので
仮定の下では起こらない。 -/

private theorem condIIIIV_case_fr (M : PS) (m : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hL : 1 < Lng M)
    (hdom' : domTag (PSS.Trans M) = BDom.naturals)
    (hR : RTPS M) (hp0 : hasParent M 0 (Lng M - 1) = true)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    ∃ n, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true := by
  have hfacts : 0 < entry M 1 (Lng M - 1) ∧
      entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1)) := by
    rcases hcond with c | c
    · simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent] at c
      exact ⟨c.1.1, c.1.2⟩
    · simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent] at c
      exact ⟨c.1.1, c.1.2⟩
  by_cases hp1 : hasParent M 1 (Lng M - 1) = true
  · have hj1gt : 1 < Lng M - 1 := by
      by_contra hcon
      have hj1one : Lng M - 1 = 1 := by omega
      have hp1' : hasParent M 1 1 = true := by rw [hj1one] at hp1; exact hp1
      have hnr := hasParent_nextR_fr M 1 1 hp1'
      rw [parent_one_zero_fd M 1 hp1'] at hnr
      have hlt : entry M 1 0 < entry M 1 1 := by
        refine nextrel1_entry_lt_fr ?_
        simpa [nextR] using hnr
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hpz : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0'
      have hge := hfacts.2
      rw [hj1one, hpz] at hge
      omega
    refine ⟨m + 2, by omega, ?_⟩
    have hx := (Trans_oper_exchange exch84producer_fr (n := m + 1) hST hmono hj1gt
      hcond hp1 (by omega)).2
    simp only [Nat.add_sub_cancel] at hx
    exact leBT_of_lessBT_fr hx
  · exfalso
    have hp1f : hasParent M 1 (Lng M - 1) = false := by simpa using hp1
    have hd := Exch84_noParent_domTag_holds M hR hmono (by omega) hfacts.1 hp1f
    rw [hdom'] at hd
    exact BDom.noConfusion hd

/-! ## 原文の単項の場合 -/

/-- 補題（基本列の関係）の単項の場合。原文の証明の構成をそのまま辿る。 -/
theorem mono_fseq_rel (hcII : CondIIFseqRel) (hOBmono : OperBNumMono) : MonoFseqRel := by
  intro M m hST hmono hL hdom
  have hdom' : domTag (PSS.Trans M) = BDom.naturals := hdom
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := RTPS_TPS M hR
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hT hmono (Lng M - 1) (by omega) (by omega)
  have hdiag : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
  rcases trans_cond_cases_fr M hR hmono hL with cI | cII | cIII | cIV | cV | cVI
  ---------------------------------------------------------------- 条件 (I)
  · have e1z : entry M 1 (Lng M - 1) = 0 := by
      simp only [transCondI, Bool.and_eq_true, beq_iff_eq, lastIdx] at cI
      exact cI.1
    by_cases hj1one : Lng M - 1 = 1
    · -- 原文の `t₁ = 0`（2 列）: `Trans M = D_u(D_0 0)`、`M[n] = ((u,u))^n`
      have hL2 : Lng M = 2 := by omega
      have he11z : entry M 1 1 = 0 := by rw [hj1one] at e1z; exact e1z
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hi1 : idx1 M 1 = 0 := by simp [idx1, he11z]
      have hnz1 : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by
        have := entry0_pos_of_hasParent_fr hp0'
        rintro ⟨h1, -⟩; omega
      have hp1 : hasParent M (idx1 M 1) 1 = true := by rw [hi1]; exact hp0'
      have hop : ∀ k : ℕ, oper M (k + 1)
          = List.replicate (k + 1) (entry M 1 0, entry M 1 0) := by
        intro k
        rw [oper_len2_fd M hL2 hnz1 hp1 0 0 (by simp [hi1]) (by simp [hi1])]
        rw [hdiag]
        simp [List.map_const', List.eq_replicate_iff]
      have hTM : PSS.Trans M = Dprin (entry M 1 0 : ℕ∞) (Dprin 0 BZero) := by
        rw [two_column_Trans M hR hmono hL2, he11z]; rfl
      have hOp : operB (PSS.Trans M) (numBT m)
          = multBT (Dprin (entry M 1 0 : ℕ∞) BZero) (m + 1) := by
        rw [hTM]
        exact operB_succ_body_ci BZero (entry M 1 0 : ℕ∞) m
      by_cases hu : entry M 1 0 = 0
      · refine ⟨m + 2, by omega, ?_⟩
        have hc := const00_Trans (entry M 1 0) (m + 1)
        rw [if_pos hu] at hc
        have : oper M (m + 2) = List.replicate (m + 2) (entry M 1 0, entry M 1 0) :=
          hop (m + 1)
        rw [hOp, this, hc]
        simp [leBT]
      · refine ⟨m + 1, by omega, ?_⟩
        have hc := const00_Trans (entry M 1 0) m
        rw [if_neg hu] at hc
        rw [hOp, hop m, hc]
        simp [leBT]
    · -- 原文の `t₁ ≠ 0`、条件 (I): 交換関係 (1) をそのまま使う
      have hj1gt : 1 < Lng M - 1 := by omega
      refine ⟨m + 1, by omega, ?_⟩
      have hx := condI_exchange1 scx_condI_j0pos_masterCF operI_j0zero_trans_mult_holds
        FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds M (m + 1) hR hmono
        hj1gt cI (by omega)
      simp only [Nat.add_sub_cancel] at hx
      exact leBT_of_eq_fr hx.symm
  ---------------------------------------------------------------- 条件 (II)
  · have hj1gt : 1 < Lng M - 1 := by
      by_contra hcon
      have hj1one : Lng M - 1 = 1 := by omega
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hpz : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0'
      simp only [transCondII, Bool.and_eq_true, lastParent, lastIdx, hj1one, hpz,
        adm_zero] at cII
      simp at cII
    obtain ⟨n, hn, hx⟩ := hcII M m hST hmono hj1gt cII
    exact ⟨n, hn, leBT_of_eq_fr hx.symm⟩
  ---------------------------------------------------------------- 条件 (III)
  · exact condIIIIV_case_fr M m hST hmono hL hdom' hR hp0 (Or.inl cIII)
  ---------------------------------------------------------------- 条件 (IV)
  · exact condIIIIV_case_fr M m hST hmono hL hdom' hR hp0 (Or.inr cIV)
  ---------------------------------------------------------------- 条件 (V)
  · have hj1gt : 1 < Lng M - 1 := by
      simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent] at cV
      omega
    by_cases hadm : adm M (parent M 0 (Lng M - 1)) = true
    · refine ⟨m + 2, by omega, ?_⟩
      have hx := (Trans_oper_exchange_condV_adm_uncond_vc M (m + 1) hST hmono
        (by omega) cV hadm).2.2.2
      simp only [Nat.add_sub_cancel] at hx
      exact leBT_of_lessBT_fr hx
    · -- 非 adm 枝: `nf3x` の閉形式から直接比較する
      have hnadm : adm M (parent M 0 (Lng M - 1)) = false := by simpa using hadm
      obtain ⟨hJ1, hT1⟩ := condV_setup_holds M hR hT hmono cV
      obtain ⟨s₁, b₁, hd1, hk1⟩ := fseq_condV_holds M hR hT hmono hJ1 hT1 cV
      obtain ⟨hMform, hOform⟩ := nf3x_vc M s₁ b₁ hST hmono cV hnadm hd1 hk1
      have hrp : ∀ x ∈ b₁, x = Sym.rp := hd1.2.2
      have ht2 : transT2 M ≠ BZero := t2_nonzero_condV_holds M hR hT hmono cV
      have hstep : ∀ j : ℕ, leBT (operB (PSS.Trans M) (numBT (j + 1)))
          (PSS.Trans (oper M (j + 2))) = true := by
        intro j
        refine leBT_of_lessBT_fr ?_
        have hb : lessBT (e5x_bodyO (transT2 M) (entry M 1 (transJ0 M)) (j + 1))
            (e5x_bodyM (transT2 M) (entry M 1 (transJ0 M)) (j + 1)) = true := by
          simp only [e5x_bodyO, e5x_bodyM]
          exact addBT_lt_right_bf _ _ _
            (s85b_W_mono_seed_fr _ _ (lessBT_BZero_fr ht2) (j + 1))
        exact scbext_lessBT (hOform (j + 1) (by omega)) (hMform (j + 1)) hrp
          (by simp [lessBP, hb])
      cases m with
      | zero =>
          refine ⟨2, by omega, ?_⟩
          refine leBT_trans_fr2 ?_ (hstep 0)
          exact hOBmono (PSS.Trans M) 0 1 (Trans_STPS_OT_B M hST) hdom' (by omega)
      | succ j => exact ⟨j + 2, by omega, hstep j⟩
  ---------------------------------------------------------------- 条件 (VI)
  · by_cases hj1one : Lng M - 1 = 1
    · -- 原文の `t₁ = 0` のもう一方: `Trans M = D_u(D_{u+1}0)`、`M[n] = D_u^n 0`
      have hL2 : Lng M = 2 := by omega
      simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        lastIdx, lastParent, hj1one] at cVI
      have he1pos : 0 < entry M 1 1 := cVI.1.1
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hpz0 : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0'
      have he11 : entry M 1 1 = entry M 1 0 + 1 := by
        have := cVI.1.2; rw [hpz0] at this; omega
      have hi1 : idx1 M 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent M (idx1 M 1) 1 = true := by
        rw [hi1]
        by_contra hc
        have hcf : hasParent M 1 1 = false := by simpa using hc
        have := Exch84_noParent_domTag_holds M hR hmono (by omega)
          (by rw [hj1one]; exact he1pos) (by rw [hj1one]; exact hcf)
        rw [hdom'] at this
        exact BDom.noConfusion this
      have hpz1 : parent M (idx1 M 1) 1 = 0 := parent_one_zero_fd M _ hp1
      have hnz1 : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by rintro ⟨-, h2⟩; omega
      have hcondA := (RTPS_condAB M hR).1
      have he01 : entry M 0 1 = entry M 1 0 + 1 := by
        simp only [RedCondA, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_true_eq] at hcondA
        have h := hcondA 0 (by omega) 1 (by omega)
        rcases h with h | h
        · rw [hp0'] at h; exact absurd h (by simp)
        · rw [hpz0, hdiag] at h; omega
      have hop : ∀ k : ℕ, oper M (k + 1)
          = (List.range (k + 1)).map (fun j => (entry M 1 0 + j, entry M 1 0)) := by
        intro k
        rw [oper_len2_fd M hL2 hnz1 hp1 1 0
          (by rw [hi1] at hpz1 ⊢; simp [hi1, hpz1, he01, hdiag])
          (by simp [hi1])]
        simp [hdiag]
      have hTMn : ∀ k : ℕ, PSS.Trans (oper M (k + 2))
          = (fun a => Dprin (entry M 1 0 : ℕ∞) a)^[k + 2] BZero := by
        intro k
        rw [hop (k + 1), FseqDesc_m_8_6_rcseq_Trans_holds (entry M 1 0) (k + 1),
          if_neg (by simp)]
      have hTM : PSS.Trans M = Dprin (entry M 1 0 : ℕ∞)
          (Dprin ((entry M 1 0 + 1 : ℕ) : ℕ∞) BZero) := by
        rw [two_column_Trans M hR hmono hL2, he11]
      refine ⟨m + 2, by omega, ?_⟩
      have hOp : operB (PSS.Trans M) (numBT m)
          = (fun a => Dprin (entry M 1 0 : ℕ∞) a)^[m + 2] BZero := by
        rw [hTM, operB_Du_Dv0_fr (entry M 1 0) (entry M 1 0 + 1) m (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [Function.iterate_succ_apply' (Dprin (entry M 1 0 : ℕ∞)) (m + 1) BZero]
      rw [hOp, hTMn m]
      simp [leBT]
    · -- 原文の `t₁ ≠ 0`、条件 (VI): 交換関係 (2) をそのまま使う
      have hj1gt : 1 < Lng M - 1 := by omega
      by_cases hadm : adm M (parent M 0 (Lng M - 1)) = true
      · refine ⟨m + 2, by omega, ?_⟩
        have hx := (p_8_6_Trans_fseq_condVI_uncond M (m + 2) hST hR hmono (by omega)
          hj1gt cVI).2.1 (by simp)
        rw [if_pos hadm] at hx
        simp only [Nat.add_sub_cancel] at hx
        exact leBT_of_eq_fr hx.symm
      · have hnadm : adm M (parent M 0 (Lng M - 1)) = false := by simpa using hadm
        refine ⟨m + 1, by omega, ?_⟩
        have hx := (p_8_6_Trans_fseq_condVI_uncond M (m + 1) hST hR hmono (by omega)
          hj1gt cVI).2.1 (by simp [hnadm])
        rw [if_neg (by simp [hnadm])] at hx
        simp only [Nat.add_sub_cancel] at hx
        exact leBT_of_eq_fr hx.symm

end Bijectivity
