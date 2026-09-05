import Bijectivity.«15-successor-fseq»
import «6».«6.7-standard-P-components»
import «8».«8.7-fseq-descend»
import «8».«8.7-fseq-descend-props»
import «8».«8.7-termination»

/-!
# 補題（基本列の関係）— 複項の場合の帰着

原文の 補題（基本列の関係）の証明のうち、\(M\) が複項である部分を単項の場合へ
帰着させる。原文が使う道具はつぎの 3 つで、本ファイルもそれだけを使う。

* 「任意の \(t_0,t_1\in T_{\textrm{B}}\) と \(m\in\textrm{dom}(t_1)\) に対して
  \(\textrm{dom}(t_0+t_1)=\textrm{dom}(t_1)\) かつ \((t_0+t_1)[m]=t_0+(t_1[m])\)」
  ＝ `domTag_addBT_right`（`15-successor-fseq`）と `operB_addBT_right`（本ファイル）。
* [1] の \(P\) と基本列の関係 (2) ＝ `FseqDesc_m_6_2_P_oper_2_holds`。
* [1] の \(\textrm{Trans}\) の \(P\) 同変性 ＝ `f7x_Trans_append_Pblocks_holds`。

## 原文との差 (訂正 B4)

原文の複項の場合の末尾の計算は

\[
\textrm{Trans}(M)[m]=\dots=\Sigma_{\textrm{B}}(P(M)_J^+)_{J=0}^{J_1-1}
  +\textrm{Trans}(P(M)_{J_1}[m])=\textrm{Trans}(M[m])
\]

と書かれているが、単項の場合の結論は \(\textrm{Trans}(P(M)_{J_1})[m]
\leq_{\textrm{B}}\textrm{Trans}(P(M)_{J_1}[n])\) であって添字 \(n\) は \(m\) とは
限らず、しかも \(=\) ではなく \(\leq_{\textrm{B}}\) である。正しくは
\(\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])\)。詳細は
`bijectivity/corrections.md` の B4。
-/

namespace Bijectivity

open PSS

/-! ## `+_B` と基本列の交換（原文「任意の \(t_0,t_1\) …」の後半） -/

theorem addBT_assoc_fr (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  rcases a with ⟨as⟩; rcases b with ⟨bs⟩; rcases c with ⟨cs⟩
  simp [addBT, List.append_assoc]

theorem zero_addBT_fr (a : BT) : addBT BZero a = a := by
  rcases a with ⟨as⟩; simp [addBT, BZero]

theorem bOperCore_list_append_fr :
    ∀ (as bs : List BP) (z : BT), bs ≠ [] →
      bOperCore (.list (as ++ bs) z) = addBT (.trm as) (bOperCore (.list bs z))
  | [], bs, z, _ => by
      simp only [List.nil_append]
      exact (zero_addBT_fr _).symm
  | [a], bs, z, hbs => by
      cases bs with
      | nil => exact absurd rfl hbs
      | cons b bs' =>
          rw [bOperCore.eq_def]
          rfl
  | a :: a' :: as, bs, z, hbs => by
      have ih := bOperCore_list_append_fr (a' :: as) bs z hbs
      rw [bOperCore.eq_def]
      change addBT (.trm [a]) (bOperCore (.list ((a' :: as) ++ bs) z))
        = addBT (.trm (a :: a' :: as)) (bOperCore (.list bs z))
      rw [ih, ← addBT_assoc_fr]
      rfl

theorem term_eq_list_fr (ps : List BP) (z : BT) :
    bOperCore (.term (.trm ps) z) = bOperCore (.list ps z) := by
  conv_lhs => rw [bOperCore.eq_def]

/-- 原文「任意の \(t_0,t_1\in T_{\textrm{B}}\) と \(m\in\textrm{dom}(t_1)\) に対して
\((t_0+t_1)[m]=t_0+(t_1[m])\)」。 -/
theorem operB_addBT_right (t u z : BT) (hu : u ≠ BZero) :
    operB (addBT t u) z = addBT t (operB u z) := by
  rcases t with ⟨as⟩
  rcases u with ⟨bs⟩
  have hbs : bs ≠ [] := by
    intro h; exact hu (by rw [h]; rfl)
  show bOperCore (.term (.trm (as ++ bs)) z) = addBT (.trm as) (bOperCore (.term (.trm bs) z))
  rw [term_eq_list_fr, term_eq_list_fr, bOperCore_list_append_fr as bs z hbs]

/-! ## 先頭 \(D_00\) の補正項（`f7x_Trans_append_Pblocks` の `if` 枝） -/

private theorem descP_cons_all_D00_fr :
    ∀ (qs : List BP), descP (.db 0 BZero :: qs) = true → ∀ q ∈ qs, q = .db 0 BZero := by
  intro qs
  induction qs with
  | nil => intro _ q hq; exact absurd hq (by simp)
  | cons r rs ih =>
      intro hd q hq
      simp only [descP, Bool.and_eq_true] at hd
      have hr : r = .db 0 BZero := by
        rcases r with ⟨v, b⟩
        have hle := hd.1
        simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hle
        rcases hle with hlt | heq
        · exfalso
          simp only [lessBT, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at hlt
          rcases hlt with hlp | ⟨-, hnil⟩
          · simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
              beq_iff_eq] at hlp
            rcases hlp with h | ⟨-, h2⟩
            · exact absurd h (by simp)
            · rcases b with ⟨cs⟩
              cases cs <;> simp [BZero, lessBT, lessBPList] at h2
          · simp at hnil
        · simpa using heq
      subst hr
      rcases List.mem_cons.mp hq with h | h
      · exact h
      · exact ih hd.2 q h

/-- 先頭に `D_00` を足しても小さくならない。`descP` が「後続はすべて `D_00`」を
強制するので、実際には狭義に大きくなる。 -/
theorem lessBT_addBT_D00_left {t : BT}
    (h : descP (.db 0 BZero :: untrm t) = true) :
    lessBT t (addBT (Dprin 0 BZero) t) = true := by
  rcases t with ⟨qs⟩
  have hall := descP_cons_all_D00_fr qs h
  show lessBPList qs (.db 0 BZero :: qs) = true
  clear h
  induction qs with
  | nil => simp [lessBPList]
  | cons r rs ih =>
      have hr : r = .db 0 BZero := hall r (by simp)
      have hall' : ∀ q ∈ rs, q = .db 0 BZero := fun q hq => hall q (by simp [hq])
      have := ih hall'
      subst hr
      simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_self_eq_true, true_and]
      exact Or.inr this

private theorem descP_tail_fr : ∀ (ps : List BP), descP ps = true → descP ps.tail = true
  | [], _ => by simp [descP]
  | [_], _ => by simp [descP]
  | _ :: q :: ps, h => by
      simp only [descP, Bool.and_eq_true] at h
      simpa using h.2

private theorem descP_suffix_fr : ∀ (as bs : List BP), descP (as ++ bs) = true → descP bs = true
  | [], _, h => h
  | a :: as, bs, h => by
      refine descP_suffix_fr as bs ?_
      have := descP_tail_fr (a :: (as ++ bs)) (by simpa using h)
      simpa using this

private theorem leBT_trans_fr {a b c : BT} (h1 : leBT a b = true) (h2 : leBT b c = true) :
    leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lessBT_linear_trans _ _ _ h1 h2)
    · exact Or.inl h1
  · exact h2

private theorem leBT_addBT_right_fr (t : BT) {x y : BT} (h : leBT x y = true) :
    leBT (addBT t x) (addBT t y) = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | rfl
  · exact Or.inl (addBT_lt_right_bf t x y h)
  · exact Or.inr rfl

/-! ## 単項の場合を仮定した複項への持ち上げ -/

/-- 補題（基本列の関係）の**単項の場合**。原文の証明はこれを先に片付け、
複項の場合を最終 `P` 成分へ帰着させる。 -/
def MonoFseqRel : Prop :=
  ∀ (M : PS) (m : ℕ), STPS M → monoT M = true → 1 < Lng M →
    domIsOmega (PSS.Trans M) →
    ∃ n, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true

private theorem STPS_SkTPS_fr (M : PS) (h : STPS M) : ∃ k, SkTPS k M := by
  induction h with
  | diag u v huv => exact ⟨0, u, v, rfl, huv⟩
  | oper hM n hn ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, _, n, rfl, hk, hn⟩

/-- 原文の複項の場合。最終 `P` 成分 `P(M)_{J₁}` へ帰着する。 -/
theorem fseq_relation_of_mono (hmn : MonoFseqRel) (M : PS) (m : ℕ)
    (hST : STPS M) (hdom : domIsOmega (PSS.Trans M)) :
    ∃ n, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := one_lt_lng_of_domIsOmega hR hdom
  by_cases hmono : monoT M = true
  · exact hmn M m hST hmono hL hdom
  -- 以下 `M` は複項
  have hnotzT : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  have hmulti : multiT M = true := by
    simp only [multiT, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hnotzT, by simpa using hmono⟩
  set A := M.take (Pcut M) with hAdef
  set PJ := M.drop (Pcut M) with hPJdef
  have hlast := P_last_multi M hmulti hL
  -- `P(M)_{J₁} ≠ ((0,0))`（原文: `dom(t + D₀0) = 1 ≠ ω`）
  have hmeq := (Trans_Mark_multi_equations M hR hmulti).1
  simp only [← hAdef, ← hPJdef] at hmeq
  have hPJne00 : PJ ≠ [(0, 0)] := by
    intro h
    have hz : (PJ == [((0 : ℕ), (0 : ℕ))]) = true := by simp [h]
    rw [hz, if_pos rfl] at hmeq
    have : domTag (PSS.Trans M) = BDom.zeroOnly := by
      rw [hmeq, domTag_addBT_right (by simp [Dprin, BZero])]
      simp [domTag, domTagList, domTagBP, Dprin, BZero]
    rw [hdom] at this
    exact BDom.noConfusion this
  have hTM : PSS.Trans M = addBT (PSS.Trans A) (PSS.Trans PJ) := by
    rw [hmeq, if_neg (by simpa using hPJne00)]
  -- `P(M)_{J₁}` は標準形・単項
  have hidx0 : (P M).length - 1 < (P M).length := by
    have hne := P_nonempty M
    cases hPM : P M with
    | nil => exact absurd hPM hne
    | cons a as => simp
  have hPJmem : PJ ∈ P M := by
    have hg := (trans_multi_last_component M hM hmulti).1
    rw [hPJdef, ← hg, getD_eq_getElem_idx (P M) [] hidx0]
    exact List.getElem_mem hidx0
  have hPJST : STPS PJ := by
    obtain ⟨k, hk⟩ := STPS_SkTPS_fr M hST
    have hcomp := SkTPS_P_components k M hk ((P M).length - 1) hidx0
    rw [(trans_multi_last_component M hM hmulti).1] at hcomp
    exact SkTPS_STPS k PJ hcomp
  have hPJR : RTPS PJ := STPS_RTPS PJ hPJST
  have hPJT : TPS PJ := RTPS_TPS PJ hPJR
  have hPJmono : monoT PJ = true := by
    rcases P_components_nonmulti M hM PJ hPJmem with h | h
    · exfalso
      have := eq_zero_singleton_of_zeroT hPJR h
      exact hPJne00 this
    · exact h
  -- `Trans(P(M)_{J₁}) ≠ 0` と `dom(Trans(P(M)_{J₁})) = ω`
  have hTPJne : PSS.Trans PJ ≠ BZero := by
    intro h0
    exact hPJne00 (eq_zero_singleton_of_zeroT hPJR
      ((Trans_preserves_zeroT PJ hPJT).2 h0))
  have hdomPJ : domIsOmega (PSS.Trans PJ) := by
    have := domTag_addBT_right (t := PSS.Trans A) hTPJne
    rw [← hTM] at this
    rw [domIsOmega, ← this]; exact hdom
  have hLPJ : 1 < Lng PJ := one_lt_lng_of_domIsOmega hPJR hdomPJ
  -- 単項の場合を適用
  obtain ⟨n, hn, hle⟩ := hmn PJ m hPJST hPJmono hLPJ hdomPJ
  refine ⟨n, hn, ?_⟩
  -- `M[n] = A @ P(M)_{J₁}[n]`（[1] の `P` と基本列の関係 (2)）
  have hlastgt : 1 < Lng ((P M).getLastD []) := by rw [hlast.1]; exact hLPJ
  obtain ⟨hopsplit, hPsplit⟩ := FseqDesc_m_6_2_P_oper_2_holds M n hM hn hlastgt
  have hconcA : (P M).dropLast.flatten = A := by rw [hlast.2]; exact P_concat A
  have hopeq : oper M n = A ++ oper PJ n := by rw [hopsplit, hconcA, hlast.1]
  have hPeq : P (oper M n) = P A ++ P (oper PJ n) := by
    rw [hPsplit, hlast.2, hlast.1]
  have hMnST : STPS (oper M n) := STPS.oper hST n hn
  have hMnR : RTPS (oper M n) := STPS_RTPS _ hMnST
  have hPJnR : RTPS (oper PJ n) := STPS_RTPS _ (STPS.oper hPJST n hn)
  have hKR : RTPS (A ++ oper PJ n) := by rw [← hopeq]; exact hMnR
  have hPeq' : P (A ++ oper PJ n) = P A ++ P (oper PJ n) := by rw [← hopeq]; exact hPeq
  have haddK := f7x_Trans_append_Pblocks_holds A (oper PJ n) hKR hPJnR hPeq'
  rw [← hopeq] at haddK
  -- 先頭 `D₀0` の補正込みで比較する
  have hcorr : leBT (PSS.Trans (oper PJ n))
      (if (P (oper PJ n)).getD 0 [] = [(0, 0)]
       then addBT (Dprin 0 BZero) (PSS.Trans (oper PJ n))
       else PSS.Trans (oper PJ n)) = true := by
    by_cases hexc : (P (oper PJ n)).getD 0 [] = [(0, 0)]
    · rw [if_pos hexc]
      -- `Trans (M[n])` は順序数項なので principal リストは広義降順
      have hdesc : descP (.db 0 BZero :: untrm (PSS.Trans (oper PJ n))) = true := by
        have hOT : isOT_BT (PSS.Trans (oper M n)) = true := (Trans_STPS_OT_B _ hMnST).1
        rw [haddK, if_pos hexc] at hOT
        rcases hA : PSS.Trans A with ⟨as⟩
        rcases hT : PSS.Trans (oper PJ n) with ⟨qs⟩
        rw [show (addBT (PSS.Trans A) (addBT (Dprin 0 BZero) (PSS.Trans (oper PJ n))))
              = BT.trm (as ++ (.db 0 BZero :: qs)) by
            rw [hA, hT]; simp [addBT, Dprin, BZero]] at hOT
        simp only [isOT_BT, Bool.and_eq_true] at hOT
        have := descP_suffix_fr as (.db 0 BZero :: qs) hOT.2
        simpa [hT, untrm] using this
      simp [leBT, lessBT_addBT_D00_left hdesc]
    · rw [if_neg hexc]; simp [leBT]
  rw [haddK, hTM, operB_addBT_right _ _ _ hTPJne]
  exact leBT_addBT_right_fr _ (leBT_trans_fr hle hcorr)

end Bijectivity
