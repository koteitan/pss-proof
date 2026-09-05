import Bijectivity.«16b-mono-fseq-rel»
import «Buchholz-1986».«Buchholz-1986-3.3»

/-!
# `operB` の添字単調性

Isabelle `y4_N_mono` / `y4_N_mono_le` (`isabelle/8/Support_8_C.thy`:11802 / 11924)
の移植。\(\textrm{dom}(a)=\omega\) なる順序数項 \(a\) に対して
\(a[0]<_{\textrm{B}}a[1]<_{\textrm{B}}\cdots\) である。

補題（基本列の関係）の 条件 (V)・非許容枝では、[1] の交換関係 (3) が
\(\textrm{Trans}(M)[n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])\;(n\geq1)\) の形でしか
使えず、目標の添字 \(m=0\) だけが取り残される。そこを本ファイルが埋める
（訂正 B5）。

Isabelle の証明は `isOT_BT a` に加えて `dfree_BT a`（\(D_\omega\) を含まないこと）を
仮定するが、\(D_\omega0\) の枝は `operB (D_ω 0) n = D_{n+1} 0` で単調なので不要である。
本ファイルは `dfree` を仮定しない。
-/

namespace Bijectivity

open PSS

/-! ## 小さな道具 -/

private theorem multBT_single_fr (q : BP) :
    ∀ k, multBT (BT.trm [q]) k = BT.trm (List.replicate k q)
  | 0 => rfl
  | k + 1 => by
      rw [multBT, multBT_single_fr q k]
      simp [addBT, List.replicate_succ']

private theorem lessBT_replicate_succ_fr (q : BP) : ∀ k,
    lessBT (BT.trm (List.replicate k q)) (BT.trm (List.replicate (k + 1) q)) = true
  | 0 => by simp [lessBT, lessBPList]
  | k + 1 => by
      have ih := lessBT_replicate_succ_fr q k
      simp only [List.replicate_succ, lessBT, lessBPList, Bool.or_eq_true,
        Bool.and_eq_true, beq_self_eq_true, true_and]
      exact Or.inr (by simpa [lessBT] using ih)

private theorem numNat_numBT_fr2 (m : ℕ) : numNat (numBT m) = m := by
  simp [numNat, numBT]

private theorem xseq_zero_fr2 (b : BT) (w : ℕ∞) : xseq b w 0 = Dprin w BZero := by
  simp [xseq, bOperCore]

private theorem xseq_succ_fr2 (b : BT) (w : ℕ∞) (i : ℕ) :
    xseq b w (i + 1) = Dprin w (operB b (xseq b w i)) := by
  show bOperCore (.xseq b w (i + 1)) =
    Dprin w (bOperCore (.term b (bOperCore (.xseq b w i))))
  rw [bOperCore.eq_def]

private theorem lessBT_Dprin_same_fr (v : ℕ∞) {a b : BT} (h : lessBT a b = true) :
    lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

private theorem lessBT_BZero_ne_fr {t : BT} (h : t ≠ BZero) : lessBT BZero t = true := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact absurd rfl h
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-! ## 補助列 `x_i` の狭義増大（Isabelle `y4_xseq_lt`） -/

private theorem xseq_lt_fr (b : BT) (w : ℕ) (hot : isOT_BT b = true)
    (hdb : domTag b = .below w) :
    ∀ i, lessBT (xseq b (w : ℕ∞) i) (xseq b (w : ℕ∞) (i + 1)) = true := by
  have hxin : ∀ i, xseq b (w : ℕ∞) i ∈ TBv (w : ℕ∞) := xseq_mem_TBv_bc b w
  have hY0 : operB b (xseq b (w : ℕ∞) 0) ≠ BZero := by
    intro hz
    have hlow := operB_lowerbound_below_bc b (xseq b (w : ℕ∞) 0) w hot hdb (hxin 0)
    rw [hz, xseq_zero_fr2] at hlow
    simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hlow
    rcases hlow with h | h
    · simp [Dprin, BZero, lessBT, lessBPList] at h
    · simp [Dprin, BZero] at h
  intro i
  induction i with
  | zero =>
      rw [xseq_zero_fr2, xseq_succ_fr2, xseq_zero_fr2]
      refine lessBT_Dprin_same_fr _ ?_
      have := lessBT_BZero_ne_fr hY0
      rwa [xseq_zero_fr2] at this
  | succ i ih =>
      rw [xseq_succ_fr2 b (w : ℕ∞) i, xseq_succ_fr2 b (w : ℕ∞) (i + 1)]
      exact lessBT_Dprin_same_fr _
        (operB_mono_below_bc b _ _ w hdb (hxin i) (hxin (i + 1)) ih)

/-! ## Isabelle `y4_N_mono` -/

private theorem operB_numBT_step_aux : ∀ (k : ℕ) (a : BT), btWeight a = k →
    isOT_BT a = true → domTag a = BDom.naturals →
    ∀ n, lessBT (operB a (numBT n)) (operB a (numBT (n + 1))) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a hk hot htag n
    rcases a with ⟨xs⟩
    cases xs with
    | nil => simp [domTag, domTagList] at htag
    | cons p ps =>
        cases ps with
        | cons q qs =>
            -- 先頭 principal を剥がす
            have hop : ∀ z : BT, operB (BT.trm (p :: q :: qs)) z
                = addBT (BT.trm [p]) (operB (BT.trm (q :: qs)) z) := by
              intro z
              simp only [operB]
              rw [term_eq_list_fr, term_eq_list_fr]
              exact bOperCore_list_append_fr [p] (q :: qs) z (by simp)
            have htag' : domTag (BT.trm (q :: qs)) = BDom.naturals := by
              simpa [domTag, domTagList] using htag
            have hot' : isOT_BT (BT.trm (q :: qs)) = true := by
              have hsplit : isOT_BPList (p :: q :: qs) = true ∧ descP (p :: q :: qs) = true := by
                simpa [isOT_BT, Bool.and_eq_true] using hot
              have h2 : isOT_BPList (q :: qs) = true := by
                have h := hsplit.1
                rw [show isOT_BPList (p :: q :: qs)
                      = (isOT_BP p && isOT_BPList (q :: qs)) from rfl] at h
                exact ((Bool.and_eq_true _ _).mp h).2
              have h3 : descP (q :: qs) = true := by
                have := hsplit.2
                simp only [descP, Bool.and_eq_true] at this
                exact this.2
              simp [isOT_BT, h2, h3]
            have hlt := ih (btWeight (BT.trm (q :: qs))) (by
                subst hk
                simp only [btWeight, bpListWeight]
                omega)
              (BT.trm (q :: qs)) rfl hot' htag' n
            rw [hop, hop]
            exact addBT_lt_right_bf _ _ _ hlt
        | nil =>
            rcases p with ⟨v, b⟩
            have hotb : isOT_BT b = true := by
              simp only [isOT_BT, isOT_BPList, isOT_BP, Bool.and_eq_true] at hot
              exact hot.1.1.1
            by_cases hb : b = BZero
            · subst b
              by_cases hv0 : v = 0
              · subst v; simp [domTag, domTagList, domTagBP, BZero] at htag
              · by_cases hvtop : v = ⊤
                · subst v
                  have hz : ∀ z : BT, operB (BT.trm [BP.db ⊤ BZero]) z
                      = Dprin ((numNat z + 1 : ℕ) : ℕ∞) BZero := by
                    intro z; simp [operB, bOperCore, BZero]
                  rw [hz, hz, numNat_numBT_fr2, numNat_numBT_fr2]
                  simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true,
                    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.cast_add,
                    Nat.cast_one]
                  refine Or.inl (Or.inl ?_)
                  first
                    | omega
                    | exact_mod_cast Nat.lt_succ_self (n + 1)
                · simp [domTag, domTagList, domTagBP, BZero, hv0, hvtop] at htag
            · cases hdb : domTag b with
              | empty => simp [domTag, domTagList, domTagBP, hb, hdb] at htag
              | zeroOnly =>
                  have hop : ∀ z : BT, operB (BT.trm [BP.db v b]) z
                      = multBT (Dprin v (operB b BZero)) (numNat z + 1) := by
                    intro z
                    simp [operB, bOperCore, hb, hdb]
                  rw [hop, hop, numNat_numBT_fr2, numNat_numBT_fr2]
                  rw [show (Dprin v (operB b BZero) : BT) = BT.trm [.db v (operB b BZero)]
                        from rfl,
                    multBT_single_fr, multBT_single_fr]
                  exact lessBT_replicate_succ_fr _ (n + 1)
              | naturals =>
                  have hop : ∀ z : BT, operB (BT.trm [BP.db v b]) z
                      = Dprin v (operB b z) := by
                    intro z
                    simp [operB, bOperCore, hb, hdb]
                  rw [hop, hop]
                  refine lessBT_Dprin_same_fr _ ?_
                  exact ih (btWeight b) (by
                      subst hk
                      simp only [btWeight, bpListWeight, bpWeight]
                      omega) b rfl hotb hdb n
              | below u =>
                  by_cases hvu : v ≤ (u : ℕ∞)
                  · have hop : ∀ z : BT, operB (BT.trm [BP.db v b]) z
                        = Dprin v (operB b (xseq b (u : ℕ∞) (numNat z))) := by
                      intro z
                      simp [operB, bOperCore, xseq, hb, hdb, hvu]
                    rw [hop, hop, numNat_numBT_fr2, numNat_numBT_fr2]
                    refine lessBT_Dprin_same_fr _ ?_
                    exact operB_mono_below_bc b _ _ u hdb
                      (xseq_mem_TBv_bc b u n) (xseq_mem_TBv_bc b u (n + 1))
                      (xseq_lt_fr b u hotb hdb n)
                  · simp [domTag, domTagList, domTagBP, hb, hdb, hvu] at htag

/-- Isabelle `y4_N_mono` (`isabelle/8/Support_8_C.thy`:11802)。 -/
theorem operB_numBT_step (a : BT) (hot : isOT_BT a = true)
    (htag : domTag a = BDom.naturals) (n : ℕ) :
    lessBT (operB a (numBT n)) (operB a (numBT (n + 1))) = true :=
  operB_numBT_step_aux (btWeight a) a rfl hot htag n

/-- Isabelle `y4_N_mono_le` (`isabelle/8/Support_8_C.thy`:11924)。 -/
theorem operB_numBT_mono_holds : OperBNumMono := by
  intro a m m' hOT htag hle
  induction m' with
  | zero =>
      have : m = 0 := by omega
      subst this
      simp [leBT]
  | succ k ih =>
      rcases Nat.lt_or_ge k m with hkm | hkm
      · have : m = k + 1 := by omega
        subst this
        simp [leBT]
      · have hstep := operB_numBT_step a hOT.1 htag k
        have h1 := ih hkm
        simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl (lessBT_linear_trans _ _ _ h1 hstep)
        · rw [h1]; exact Or.inl hstep

end Bijectivity
