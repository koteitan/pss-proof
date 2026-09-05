import Bijectivity.«16c-operB-mono»

/-!
# [Buc2] Theorem 1.4(a) — 基本列の共終性

`Cited.lean` に残る唯一の外部引用 `FseqCofinal` を証明するための開発。

## 一般形

\(\textrm{dom}(t)=\omega\) に限らず、**基本列の族 \(\{t[z]\mid z\in\textrm{dom}(t)\}\) が
\(\{u\in OT_{\textrm{B}}\mid u<_{\textrm{B}}t\}\) で共終**であることを示す。
`operB` の再帰が `dom` の 3 種類（\(\{0\}\)・\(\mathbb{N}\)・\(T_w\)）を跨ぐので、
\(\omega\) に限った形では帰納が回らない。
-/

namespace Bijectivity

open PSS

/-- 一般形の共終性: \(t\) 未満の順序数項はすべて \(t\) の基本列のどれかで覆える。 -/
def CofBelow (t : BT) : Prop :=
  ∀ u : BT, u ∈ OT_B → lessBT u t = true →
    ∃ z : BT, z ∈ domB t ∧ z ∈ OT_B ∧ leBT u (operB t z) = true

/-! ## principal リストの分解 -/

/-- `cs <lex ps ++ [p]` は「`cs <lex ps`」「`cs = ps`」「`cs = ps ++ (q :: rest)` かつ
`q < p`」の 3 通りに尽きる。 -/
theorem lessBPList_snoc_dest :
    ∀ (ps : List BP) (p : BP) (cs : List BP), lessBPList cs (ps ++ [p]) = true →
      lessBPList cs ps = true ∨ cs = ps ∨
        ∃ q rest, cs = ps ++ (q :: rest) ∧ lessBP q p = true
  | [], p, cs, h => by
      cases cs with
      | nil => exact Or.inr (Or.inl rfl)
      | cons c rest =>
          simp only [List.nil_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with hcp | ⟨-, hnil⟩
          · exact Or.inr (Or.inr ⟨c, rest, rfl, hcp⟩)
          · cases rest <;> simp [lessBPList] at hnil
  | a :: ps, p, cs, h => by
      cases cs with
      | nil => exact Or.inl (by simp [lessBPList])
      | cons c cs' =>
          simp only [List.cons_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with hca | ⟨hca, hrest⟩
          · exact Or.inl (by simp [lessBPList, hca])
          · subst hca
            rcases lessBPList_snoc_dest ps p cs' hrest with h1 | h1 | ⟨q, rest, hq, hqp⟩
            · exact Or.inl (by simp [lessBPList, h1])
            · exact Or.inr (Or.inl (by rw [h1]))
            · exact Or.inr (Or.inr ⟨q, rest, by rw [hq]; simp, hqp⟩)

/-- `.trm ps ≤ addBT (.trm ps) x`。 -/
theorem leBT_addBT_left (s x : BT) : leBT s (addBT s x) = true := by
  rcases s with ⟨as⟩
  rcases x with ⟨xs⟩
  cases xs with
  | nil => simp [leBT, addBT]
  | cons q qs =>
      have key : lessBPList as (as ++ (q :: qs)) = true := by
        induction as with
        | nil => simp [lessBPList]
        | cons a as ih =>
            simp only [List.cons_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
              beq_self_eq_true, true_and]
            exact Or.inr ih
      simp only [addBT, leBT, Bool.or_eq_true]
      exact Or.inl key

/-! ## `dom` が空でないこと -/

mutual
theorem domTagBP_ne_empty_cof : ∀ p : BP, domTagBP p ≠ BDom.empty
  | .db v b => by
      by_cases hb : b = BZero
      · subst hb
        by_cases hv : v = 0
        · subst hv; simp [domTagBP, BZero]
        · by_cases hvt : v = ⊤
          · subst hvt; simp [domTagBP, BZero]
          · simp [domTagBP, BZero, hv, hvt]
      · have hbne := domTag_ne_empty_cof b hb
        have hbb : (b == BZero) = false := by simpa using hb
        unfold domTagBP
        simp only [hbb, Bool.false_eq_true, if_false]
        cases hd : domTag b with
        | empty => exact absurd hd hbne
        | zeroOnly => simp [hd]
        | naturals => simp [hd]
        | below u => by_cases hvu : v ≤ (u : ℕ∞) <;> simp [hd, hvu]

theorem domTag_ne_empty_cof : ∀ t : BT, t ≠ BZero → domTag t ≠ BDom.empty
  | .trm ps => fun h => domTagList_ne_empty_cof ps (by
      intro hp; exact h (by rw [hp]; rfl))

theorem domTagList_ne_empty_cof : ∀ ps : List BP, ps ≠ [] → domTagList ps ≠ BDom.empty
  | [], h => absurd rfl h
  | [p], _ => domTagBP_ne_empty_cof p
  | _ :: q :: qs, _ => domTagList_ne_empty_cof (q :: qs) (by simp)
end

/-- `BZero` はどの `dom` にも属する（`dom ≠ ∅` のとき）。 -/
theorem BZero_mem_domB {t : BT} (h : domTag t ≠ BDom.empty) : BZero ∈ domB t := by
  unfold domB
  cases hd : domTag t with
  | empty => exact absurd hd h
  | zeroOnly => simp [BDom.toSet]
  | naturals => exact ⟨0, rfl⟩
  | below u => simp [BDom.toSet, TBv, BZero]

theorem BZero_mem_OTB_cof : BZero ∈ OT_B :=
  ⟨by show isOT_BT BZero = true; decide, by show dfree_BT BZero = true; decide⟩

/-! ## 多項の剥がし -/

theorem operB_snoc_cof (ps : List BP) (p : BP) (z : BT) :
    operB (BT.trm (ps ++ [p])) z = addBT (BT.trm ps) (operB (BT.trm [p]) z) := by
  show bOperCore (.term (BT.trm (ps ++ [p])) z)
    = addBT (BT.trm ps) (bOperCore (.term (BT.trm [p]) z))
  rw [term_eq_list_fr, term_eq_list_fr]
  exact bOperCore_list_append_fr ps [p] z (by simp)

private theorem isOT_BPList_suffix_cof : ∀ (ps qs : List BP),
    isOT_BPList (ps ++ qs) = true → isOT_BPList qs = true
  | [], _, h => h
  | a :: as, qs, h => by
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at h
      exact isOT_BPList_suffix_cof as qs h.2

private theorem dfree_BPList_suffix_cof : ∀ (ps qs : List BP),
    dfree_BPList (ps ++ qs) = true → dfree_BPList qs = true
  | [], _, h => h
  | a :: as, qs, h => by
      simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h
      exact dfree_BPList_suffix_cof as qs h.2

theorem OTB_suffix_cof {ps qs : List BP} (h : BT.trm (ps ++ qs) ∈ OT_B) :
    BT.trm qs ∈ OT_B := by
  have hOT : isOT_BT (BT.trm (ps ++ qs)) = true := h.1
  have hDF : dfree_BPList (ps ++ qs) = true := h.2
  simp only [isOT_BT, Bool.and_eq_true] at hOT
  refine ⟨?_, ?_⟩
  · show isOT_BT (BT.trm qs) = true
    simp only [isOT_BT, Bool.and_eq_true]
    exact ⟨isOT_BPList_suffix_cof ps qs hOT.1, descP_suffix_fr ps qs hOT.2⟩
  · show dfree_BPList qs = true
    exact dfree_BPList_suffix_cof ps qs hDF

/-- 末尾 principal へ帰着する剥がし。 -/
theorem cof_peel {ps : List BP} {p : BP}
    (hOT : BT.trm (ps ++ [p]) ∈ OT_B) (hip : CofBelow (BT.trm [p])) :
    CofBelow (BT.trm (ps ++ [p])) := by
  have hpne : domTagBP p ≠ BDom.empty := domTagBP_ne_empty_cof p
  have hdom : domB (BT.trm (ps ++ [p])) = domB (BT.trm [p]) := by
    unfold domB
    rw [domTag_snoc_bf ps p, show domTag (BT.trm [p]) = domTagBP p from rfl]
  have hz0 : BZero ∈ domB (BT.trm (ps ++ [p])) := by
    refine BZero_mem_domB ?_
    rw [domTag_snoc_bf ps p]
    exact hpne
  intro u huOTB hult
  rcases u with ⟨cs⟩
  rcases lessBPList_snoc_dest ps p cs hult with h1 | h1 | ⟨q, rest, hq, hqp⟩
  · refine ⟨BZero, hz0, BZero_mem_OTB_cof, ?_⟩
    rw [operB_snoc_cof]
    exact leBT_trans_fr (by simp only [leBT, Bool.or_eq_true]; exact Or.inl h1)
      (leBT_addBT_left _ _)
  · refine ⟨BZero, hz0, BZero_mem_OTB_cof, ?_⟩
    rw [operB_snoc_cof, h1]
    exact leBT_addBT_left _ _
  · have hwOTB : BT.trm (q :: rest) ∈ OT_B := by
      rw [hq] at huOTB
      exact OTB_suffix_cof huOTB
    have hwlt : lessBT (BT.trm (q :: rest)) (BT.trm [p]) = true := by
      simp [lessBT, lessBPList, hqp]
    obtain ⟨z, hzdom, hzOTB, hzle⟩ := hip _ hwOTB hwlt
    refine ⟨z, by rw [hdom]; exact hzdom, hzOTB, ?_⟩
    rw [operB_snoc_cof, hq]
    have hsplit : (BT.trm (ps ++ q :: rest) : BT)
        = addBT (BT.trm ps) (BT.trm (q :: rest)) := rfl
    rw [hsplit]
    exact leBT_addBT_right_fr _ hzle

/-! ## 単項の場合 — \(b=0\) の枝 -/

private theorem descP_mem_le_head : ∀ (c : BP) (rest : List BP), descP (c :: rest) = true →
    ∀ q ∈ rest, leBT (BT.trm [q]) (BT.trm [c]) = true
  | _, [], _, _, hq => absurd hq (by simp)
  | c, r :: rs, h, q, hq => by
      simp only [descP, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact h.1
      · exact leBT_trans_fr (descP_mem_le_head r rs h.2 q hq') h.1

private theorem operB_Dv0_id_cof (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0]

/-- \(t=D_00\): 唯一の元 \(0\) が基本列の値。 -/
theorem cof_D00 : CofBelow (Dprin 0 BZero) := by
  intro u _ hult
  have hu : u = BZero := eq_BZero_of_lessBT_DzeroZero hult
  refine ⟨BZero, ?_, BZero_mem_OTB_cof, ?_⟩
  · show BZero ∈ domB (Dprin 0 BZero)
    simp [domB, domTag, domTagList, domTagBP, Dprin, BZero, BDom.toSet]
  · have hop : operB (Dprin 0 BZero) BZero = BZero := by
      simp [operB, bOperCore, Dprin, BZero]
    rw [hop, hu]
    simp [leBT]

/-- \(t=D_v0\)（\(v>0\) 有限）: \(t[z]=z\) なので \(u\) 自身が証人。 -/
theorem cof_Dv0 {v : ℕ} (hv : 0 < v) : CofBelow (Dprin (v : ℕ∞) BZero) := by
  intro u huOTB hult
  have htag : domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
    have hv0 : ((v : ℕ∞) == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      simpa using (Nat.ne_of_gt hv)
    have hvtop : ((v : ℕ∞) == ⊤) = false := by simp
    simp [domTag, domTagList, domTagBP, Dprin, BZero, hv0, hvtop]
  refine ⟨u, ?_, huOTB, by rw [operB_Dv0_id_cof v u hv]; simp [leBT]⟩
  rw [domB, htag]
  show u ∈ TBv ((v - 1 : ℕ) : ℕ∞)
  rcases u with ⟨cs⟩
  cases cs with
  | nil => simp [TBv]
  | cons c rest =>
      rcases c with ⟨uc, bc⟩
      have hchead : uc < (v : ℕ∞) := by
        simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hult
        rcases hult with (h | ⟨-, hb⟩) | ⟨-, hnil⟩
        · exact h
        · exfalso; rcases bc with ⟨ds⟩; cases ds <;> simp [BZero, lessBT, lessBPList] at hb
        · exfalso; cases rest <;> simp [lessBPList] at hnil
      have hdesc : descP (BP.db uc bc :: rest) = true := by
        have h : isOT_BT (BT.trm (BP.db uc bc :: rest)) = true := huOTB.1
        simp only [isOT_BT, Bool.and_eq_true] at h
        exact h.2
      have hbound : ∀ uq : ℕ∞, uq ≤ uc → uq ≤ ((v - 1 : ℕ) : ℕ∞) := by
        intro uq hq
        have hlt : uq < (v : ℕ∞) := lt_of_le_of_lt hq hchead
        have hne : uq ≠ ⊤ := by
          intro h; rw [h] at hlt; exact absurd hlt (by simp)
        obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
        have hn : n < v := WithTop.coe_lt_coe.mp hlt
        exact WithTop.coe_le_coe.mpr (Nat.le_sub_one_of_lt hn)
      show ((BP.db uc bc :: rest).all
        fun p => match p with | .db w _ => decide (w ≤ ((v - 1 : ℕ) : ℕ∞))) = true
      simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      refine ⟨hbound uc le_rfl, ?_⟩
      intro q hq
      rcases q with ⟨uq, bq⟩
      simp only [decide_eq_true_eq]
      refine hbound uq ?_
      have hle := descP_mem_le_head (BP.db uc bc) rest hdesc (BP.db uq bq) hq
      exact leBT_single_index_bf uq uc bq bc (by simpa [Dprin] using hle)

/-! ## 還元 — 残るのは単項かつ \(b\neq0\) の場合だけ -/

/-- 残差: 単項 \(D_vb\)（\(b\neq0\)）の共終性。`operB` の 4 分岐
（\(\textrm{dom}(b)=\{0\}\) / \(T_w\) with \(v\leq w\) / \(T_w\) with \(v>w\) /
\(\mathbb{N}\)）がそのままここに残っている。 -/
def CofSinglePrincipal : Prop :=
  ∀ (v : ℕ∞) (b : BT), BT.trm [.db v b] ∈ OT_B → b ≠ BZero →
    CofBelow (BT.trm [.db v b])

/-- 単項の場合。\(b=0\) の 2 枝は上で閉じてあり、\(v=\omega\) は
`dfree`（\(OT_{\textrm{B}}\)）で排除される。 -/
theorem cofBelow_single (h : CofSinglePrincipal) {v : ℕ∞} {b : BT}
    (hOT : BT.trm [BP.db v b] ∈ OT_B) : CofBelow (BT.trm [BP.db v b]) := by
  by_cases hb : b = BZero
  · subst hb
    have hvne : v ≠ ⊤ := by
      have hdf : dfree_BPList [BP.db v BZero] = true := hOT.2
      simp only [dfree_BPList, dfree_BP, Bool.and_eq_true, bne_iff_ne, ne_eq] at hdf
      exact hdf.1.1
    by_cases hv0 : v = 0
    · subst hv0
      exact cof_D00
    · obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hvne
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact absurd rfl hv0
        · exact hpos
      exact cof_Dv0 hn
  · exact h v b hOT hb

/-- 一般の \(t\in OT_{\textrm{B}}\setminus\{0\}\) の共終性。末尾 principal へ剥がす。 -/
theorem cofBelow_all (h : CofSinglePrincipal) :
    ∀ t : BT, t ∈ OT_B → t ≠ BZero → CofBelow t := by
  rintro ⟨ps⟩ hOT htne
  have hpsne : ps ≠ [] := by
    intro h0; exact htne (by rw [h0]; rfl)
  have hsplit : ps = ps.dropLast ++ [ps.getLast hpsne] :=
    (List.dropLast_append_getLast hpsne).symm
  rw [hsplit] at hOT ⊢
  refine cof_peel hOT ?_
  rcases hlast : ps.getLast hpsne with ⟨v, b⟩
  rw [hlast] at hOT
  exact cofBelow_single h (OTB_suffix_cof (qs := [BP.db v b]) hOT)

/-- 残差から `Cited.lean` の `FseqCofinal` を出す。 -/
theorem fseq_cofinal_of (h : CofSinglePrincipal) : FseqCofinal := by
  intro t hOT hdom u huOTB hult
  have htne : t ≠ BZero := by
    intro h0
    rw [h0] at hdom
    simp [domTag, domTagList, BZero] at hdom
  obtain ⟨z, hzdom, hzOTB, hzle⟩ := cofBelow_all h t hOT htne u huOTB hult
  rw [domB, hdom] at hzdom
  obtain ⟨m, rfl⟩ := (hzdom : z ∈ NatSet)
  exact ⟨m, hzle⟩

/-- **[Buc2] Theorem 1.4(a) の残差**。上の還元により、残っているのは
単項 \(D_vb\)（\(b\neq0\)）の場合だけである。 -/
axiom cof_single_principal : CofSinglePrincipal

/-- `Cited.lean` の `FseqCofinal`。 -/
theorem fseq_cofinal : FseqCofinal := fseq_cofinal_of cof_single_principal

end Bijectivity
