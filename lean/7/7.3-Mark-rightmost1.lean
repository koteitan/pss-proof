import «7».«7.3-Pred-Trans-descend»
import «7».«7.2-scb-unique»

/-!
# §7.3 命題（右端第1基点の `Mark` の基本性質）

- 原文: `tmp/content.md` の同名命題
- Isabelle: `Mark_MarkedB_nest`, `Mark_tail_nonzero`,
  `m_7_3_Mark_rightmost1`
- 訂正: A17（零項 `[(0,0)]` を除外する）
- 状態: 🚧 証明中
-/

namespace PSS

/-! ## `MarkedB` の小さな構造補題 -/

private theorem markedBSelfPrincipal {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) : (c, c) ∈ MarkedB := by
  refine ⟨[], [], ?_⟩
  refine ⟨by simp, ?_, by simp⟩
  intro _
  exact (principal_flat_properties hc hcP).1

private theorem markedBZeroSelf : (BZero, BZero) ∈ MarkedB := by
  refine ⟨[], [], ?_⟩
  simp [scb_decomp, BZero, flatBT]

private theorem markedBDprinLift {t c : BT} (v : ℕ∞)
    (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p])
    (hm : (t, c) ∈ MarkedB) : (Dprin v t, c) ∈ MarkedB := by
  rcases hm with ⟨s, b, hd⟩
  exact ⟨.dsym v :: s, b,
    scb_compose_dprin v t s (flatBT c) b hd
      (principal_flat_properties hc hcP).1⟩

private theorem markedBCompose {t c₀ c₁ : BT}
    (hc₀P : ∃ p, c₀ = .trm [p])
    (h₀ : (t, c₀) ∈ MarkedB) (h₁ : (c₀, c₁) ∈ MarkedB) :
    (t, c₁) ∈ MarkedB := by
  rcases h₀ with ⟨s₀, b₀, hd₀⟩
  rcases h₁ with ⟨s₁, b₁, hd₁⟩
  exact ⟨s₀ ++ s₁, b₁ ++ b₀,
    scb_compose t c₀ s₀ s₁ (flatBT c₁) b₁ b₀ hc₀P hd₀ hd₁⟩

private theorem markedBHostNeZero {t c : BT}
    (hcP : ∃ p, c = .trm [p]) (hm : (t, c) ∈ MarkedB) : t ≠ BZero := by
  obtain ⟨p, rfl⟩ := hcP
  rcases p with ⟨u, a⟩
  rcases hm with ⟨s, b, hd⟩
  intro ht
  subst t
  have hlen := congrArg List.length hd.1
  have hapos : 0 < (flatBT a).length := by
    rcases a with ⟨ps⟩
    cases ps with
    | nil => simp [flatBT]
    | cons p ps =>
        cases ps with
        | nil => rcases p with ⟨v, z⟩; simp [flatBT, flatBP]
        | cons q qs => simp [flatBT]
  simp only [BZero, flatBT, flatBP, List.length_cons,
    List.length_append, List.length_nil, Nat.zero_add] at hlen
  omega

private theorem zeroMemTB : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem dfreeBPListTake (ps : List BP) (n : ℕ)
    (hps : dfree_BPList ps = true) : dfree_BPList (ps.take n) = true := by
  induction n generalizing ps with
  | zero => simp [dfree_BPList]
  | succ n ih =>
      cases ps with
      | nil => simp [dfree_BPList]
      | cons p ps =>
          simp only [dfree_BPList, Bool.and_eq_true] at hps
          simpa [dfree_BPList] using And.intro hps.1 (ih ps hps.2)

private theorem flatMapUntrmTakeMap (ps : List BP) (n : ℕ) :
    ((ps.map fun p => BT.trm [p]).take n).flatMap untrm = ps.take n := by
  induction n generalizing ps with
  | zero => simp
  | succ n ih =>
      cases ps with
      | nil => simp
      | cons p ps => simp [ih ps, untrm]

private theorem sigmaPBTakeMemTB (t : BT) (n : ℕ) (ht : t ∈ T_B) :
    SigmaB ((PB t).take n) ∈ T_B := by
  rcases t with ⟨ps⟩
  change dfree_BPList ps = true at ht
  change dfree_BPList
    (((ps.map fun p => BT.trm [p]).take n).flatMap untrm) = true
  rw [flatMapUntrmTakeMap]
  exact dfreeBPListTake ps n ht

private theorem dfreeBPOfMem {ps : List BP} {p : BP}
    (hps : dfree_BPList ps = true) (hp : p ∈ ps) : dfree_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [dfree_BPList, Bool.and_eq_true] at hps
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]
        exact hps.1
      · exact ih hps.2 hp

private theorem pbGetDMemTB (t : BT) (j : ℕ) (ht : t ∈ T_B) :
    (PB t).getD j BZero ∈ T_B := by
  by_cases hj : j < (PB t).length
  · rw [getD_eq_getElem_idx (PB t) BZero hj]
    rcases t with ⟨ps⟩
    change dfree_BPList ps = true at ht
    simp only [PB, List.length_map] at hj
    simp only [PB, List.getElem_map]
    have hmem : ps[j] ∈ ps := List.getElem_mem hj
    have hdf : dfree_BP ps[j] = true := dfreeBPOfMem ht hmem
    simpa [T_B, dfree_BT, dfree_BPList] using hdf
  · have hget : (PB t).getD j BZero = BZero := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hget]
    exact zeroMemTB

private theorem bpHeadTMemTB (t : BT) (ht : t ∈ T_B) : bpHeadT t ∈ T_B := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simpa [bpHeadT] using zeroMemTB
  | cons p ps =>
      rcases p with ⟨v, b⟩
      change dfree_BPList (.db v b :: ps) = true at ht
      simp only [dfree_BPList, dfree_BP, Bool.and_eq_true] at ht
      simpa [bpHeadT, T_B] using ht.1.2

/-! `c₂` の右端には常に、最終列の一項 `D` が現れる。 -/

private theorem transC2CoreMarkedLastAux (M : PS) (w : ℕ∞) (t₂ : BT)
    (ht₂ : t₂ ∈ T_B) :
    (transC2Core M w t₂,
      Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) ∈ MarkedB := by
  let db : BT := Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero
  have hdb : db ∈ T_B :=
    Dprin_mem_T_B (v := (entry M 1 (lastIdx M) : ℕ∞)) (by simp)
      zeroMemTB
  have hdbP : ∃ p, db = .trm [p] := ⟨_, rfl⟩
  have hself : (db, db) ∈ MarkedB := markedBSelfPrincipal hdb hdbP
  by_cases hA :
      (transCondI M || transCondIII M || transCondV M) = true
  · have hm : (addBT t₂ db, db) ∈ MarkedB :=
      add_scb_marked t₂ db ht₂ hdb hdbP
    have hout := markedBDprinLift w hdb hdbP hm
    simpa [transC2Core, hA, db] using hout
  · by_cases hVI : transCondVI M = true
    · have hout := markedBDprinLift w hdb hdbP hself
      simpa [transC2Core, hA, hVI, db] using hout
    · by_cases hz : t₂ = BZero
      · have hmid := markedBDprinLift
          (entry M 1 (lastParent M) : ℕ∞) hdb hdbP hself
        have hout := markedBDprinLift w hdb hdbP hmid
        simpa [transC2Core, hA, hVI, hz, db] using hout
      · let pJ := (PB t₂).getD ((PB t₂).length - 1) BZero
        have hpJ : pJ ∈ T_B :=
          pbGetDMemTB t₂ ((PB t₂).length - 1) ht₂
        let leftDj₀ := bpHeadV pJ == (entry M 1 (lastParent M) : ℕ∞)
        let t₃ := if leftDj₀ then
          SigmaB ((PB t₂).take ((PB t₂).length - 1)) else t₂
        let t₄ := if leftDj₀ then bpHeadT pJ else t₂
        have ht₃ : t₃ ∈ T_B := by
          dsimp [t₃]
          split
          · exact sigmaPBTakeMemTB t₂ ((PB t₂).length - 1) ht₂
          · exact ht₂
        have ht₄ : t₄ ∈ T_B := by
          dsimp [t₄]
          split
          · exact bpHeadTMemTB pJ hpJ
          · exact ht₂
        let middle : BT :=
          Dprin (entry M 1 (lastParent M) : ℕ∞) (addBT t₄ db)
        have hinnerTB : addBT t₄ db ∈ T_B := addBT_mem_T_B ht₄ hdb
        have hmiddleTB : middle ∈ T_B := by
          exact Dprin_mem_T_B
            (v := (entry M 1 (lastParent M) : ℕ∞)) (by simp) hinnerTB
        have hmiddleP : ∃ p, middle = .trm [p] := ⟨_, rfl⟩
        have hinnerM : (addBT t₄ db, db) ∈ MarkedB :=
          add_scb_marked t₄ db ht₄ hdb hdbP
        have hmiddleM : (middle, db) ∈ MarkedB := by
          exact markedBDprinLift
            (entry M 1 (lastParent M) : ℕ∞) hdb hdbP hinnerM
        have houtLast : (addBT t₃ middle, middle) ∈ MarkedB :=
          add_scb_marked t₃ middle ht₃ hmiddleTB hmiddleP
        have houtDb : (addBT t₃ middle, db) ∈ MarkedB :=
          markedBCompose hmiddleP houtLast hmiddleM
        have hout := markedBDprinLift w hdb hdbP houtDb
        simpa [transC2Core, hA, hVI, hz, pJ, leftDj₀, t₃, t₄,
          middle, db] using hout

private theorem transC2CoreMarkedLast (M : PS) (c₁ : BT)
    (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p]) :
    (transC2Core M (bpHeadV c₁) (bpHeadT c₁),
      Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) ∈ MarkedB := by
  obtain ⟨p, rfl⟩ := hc₁P
  rcases p with ⟨w, t₂⟩
  change dfree_BT (.trm [.db w t₂]) = true at hc₁
  simp only [dfree_BT, dfree_BPList, dfree_BP,
    Bool.and_eq_true] at hc₁
  have ht₂ : t₂ ∈ T_B := hc₁.1.2
  simpa [bpHeadV, bpHeadT] using
    transC2CoreMarkedLastAux M w t₂ ht₂

private theorem MarkSelfMarkedB (M : PS) (m : ℕ)
    (hR : RTPS M) (hm : Marked M m) :
    (Mark M m, Mark M m) ∈ MarkedB := by
  have hM : TPS M := RTPS_TPS M hR
  have hmk := (Trans_Mark_invariant M hR).2.2 m hm
  by_cases ht : Trans M = BZero
  · have hz : zeroT M = true := (Trans_preserves_zeroT M hM).2 ht
    have hzero : M = [(0, 0)] := by
      rw [← RTPS_Red_eq M hR]
      exact Red_zero_mr M hz
    subst M
    have hR0 : RTPS [(0, 0)] := hR
    have hmark : Mark [(0, 0)] m = BZero := by
      rw [Mark_eq_lengthAux [(0, 0)] m hR0]
      have hred : reduced [(0, 0)] = true := hR0
      simp [MarkAux, lastIdx, BZero, hred]
    rw [hmark]
    exact markedBZeroSelf
  · have hp : ∃ p, Mark M m = .trm [p] :=
      marked_component_principal ht hmk.2
    exact markedBSelfPrincipal hmk.1 hp

private theorem flatBTLengthPos (t : BT) : 0 < (flatBT t).length := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [flatBT]
  | cons p ps =>
      cases ps with
      | nil => rcases p with ⟨v, a⟩; simp [flatBT, flatBP]
      | cons q qs => simp [flatBT]

private theorem flatBTNonzeroLength (t : BT) (ht : t ≠ BZero) :
    2 ≤ (flatBT t).length := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => exact (ht rfl).elim
  | cons p ps =>
      cases ps with
      | nil =>
          rcases p with ⟨v, a⟩
          simp only [flatBT, flatBP, List.length_cons]
          have := flatBTLengthPos a
          omega
      | cons q qs =>
          rcases p with ⟨v, a⟩
          simp [flatBT, flatBP]

private theorem addBTNeZeroRight (a b : BT) (hb : b ≠ BZero) :
    addBT a b ≠ BZero := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  cases bs with
  | nil => exact (hb rfl).elim
  | cons p ps => simp [addBT, BZero]

private theorem transC2CoreBodyNeZero (M : PS) (w : ℕ∞) (t : BT) :
    bpHeadT (transC2Core M w t) ≠ BZero := by
  unfold transC2Core
  split
  · simp only [bpHeadT, Dprin]
    exact addBTNeZeroRight t _ (by simp [BZero])
  · split
    · simp [bpHeadT, Dprin, BZero]
    · split
      · simp [bpHeadT, Dprin, BZero]
      · simp only [bpHeadT, Dprin]
        exact addBTNeZeroRight _ _ (by simp [BZero])

private theorem transC2CoreFlatLength (M : PS) (c₁ : BT) :
    3 ≤ (flatBT (transC2Core M (bpHeadV c₁) (bpHeadT c₁))).length := by
  let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
  have hc₂one : (PB c₂).length = 1 := by
    dsimp [c₂]
    unfold transC2Core
    split <;> try split <;> try split
    all_goals simp [PB, Dprin, untrm]
  have hc₂eq : c₂ = Dprin (bpHeadV c₂) (bpHeadT c₂) :=
    principal_reconstruct hc₂one
  have hbody : bpHeadT c₂ ≠ BZero := by
    simpa [c₂] using transC2CoreBodyNeZero M (bpHeadV c₁) (bpHeadT c₁)
  have hlen := flatBTNonzeroLength (bpHeadT c₂) hbody
  change 3 ≤ (flatBT c₂).length
  rw [hc₂eq]
  simpa [Dprin, flatBT, flatBP] using Nat.succ_le_succ hlen

/-! ## 印の入れ子構造 -/

private theorem MarkMarkedBNestSurgery (M : PS) (m m' : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hlen : 1 < Lng M)
    (ht₁ne : Trans (Pred M) ≠ BZero)
    (hm : Marked M m) (hm' : Marked M m') (hmm' : m ≤ m')
    (ih : ∀ a b, Marked (Pred M) a → Marked (Pred M) b → a ≤ b →
      (Mark (Pred M) a, Mark (Pred M) b) ∈ MarkedB) :
    (Mark M m, Mark M m') ∈ MarkedB := by
  have hM : TPS M := RTPS_TPS M hR
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  let j₁ := lastIdx M
  let jp := lastParent M
  let t₁ := Trans (Pred M)
  let c₁ := Mark (Pred M) (Adm M jp)
  let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
  let db := Dprin (entry M 1 j₁ : ℕ∞) BZero
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hc₁Marked : Marked (Pred M) (Adm M jp) := by
    simpa [jp] using Marked_Pred_Adm M hM hlen hp
  have hc₁Inv := (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hc₁Marked
  have hc₁TB : c₁ ∈ T_B := by simpa [c₁] using hc₁Inv.1
  have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
    simpa [t₁, c₁] using hc₁Inv.2
  have hc₁P : ∃ p, c₁ = .trm [p] := by
    apply marked_component_principal
    · simpa [t₁] using ht₁ne
    · exact ht₁c₁
  have hc₂Facts := transC2Core_properties M c₁ hc₁TB hc₁P
  have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂Facts.1
  have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂Facts.2
  have hc₂db : (c₂, db) ∈ MarkedB := by
    simpa [c₂, db, j₁] using transC2CoreMarkedLast M c₁ hc₁TB hc₁P
  have heq := (Trans_Mark_mono_equations M hR hlen hmono).2
  have surgFacts : ∀ k, Marked M k → k < j₁ →
      ∃ c₀, c₀ = Mark (Pred M) k ∧ c₀ ∈ T_B ∧
        (c₀, c₁) ∈ MarkedB ∧ (∃ p, c₀ = .trm [p]) ∧
        Mark M k = replaceScb c₀ c₁ c₂ := by
    intro k hk hklt
    let c₀ := Mark (Pred M) k
    have hklt' : k < Lng M - 1 := by simpa [j₁, lastIdx] using hklt
    have hkPred : Marked (Pred M) k := Marked_Pred M k hM hlen hk hklt'
    have hkjp : k ≤ jp := by
      simpa [jp, lastParent] using marked_le_lastParent M hk hmono hlen hklt'
    have hkAdm : k ≤ Adm M jp := Adm_max M k jp hk.2.1 hkjp
    have hc₀c₁ : (c₀, c₁) ∈ MarkedB := by
      simpa [c₀, c₁] using ih k (Adm M jp) hkPred hc₁Marked hkAdm
    have hc₀Inv := (Trans_Mark_invariant (Pred M) hpredR).2.2 k hkPred
    have hc₀TB : c₀ ∈ T_B := by simpa [c₀] using hc₀Inv.1
    have hc₀P : ∃ p, c₀ = .trm [p] := by
      apply marked_component_principal
      · simpa [t₁] using ht₁ne
      · simpa [t₁, c₀] using hc₀Inv.2
    have hrep := replaceScb_preserves_marked
      hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
    have hrepNe : replaceScb c₀ c₁ c₂ ≠ BZero :=
      markedBHostNeZero hc₂P hrep.2
    have hmark : Mark M k = replaceScb c₀ c₁ c₂ := by
      cases hhead : (scbContexts c₀ (flatBT c₁)).head? with
      | none =>
          have hz : replaceScb c₀ c₁ c₂ = BZero := by
            simp [replaceScb, hhead]
          exact (hrepNe hz).elim
      | some sb =>
          rcases sb with ⟨s, b⟩
          have hraw := heq k
          simp [j₁, jp, c₁, c₀, ht₁ne, hklt, hhead] at hraw
          simpa [replaceScb, hhead] using hraw
    exact ⟨c₀, rfl, hc₀TB, hc₀c₁, hc₀P, hmark⟩
  have hm'Last : m' ≤ j₁ := by
    simpa [j₁, lastIdx] using Marked_index_le_last hm'
  by_cases hm'lt : m' < j₁
  · have hmlt : m < j₁ := lt_of_le_of_lt hmm' hm'lt
    obtain ⟨c₀, hc₀eq, hc₀TB, hc₀c₁, hc₀P, hmark⟩ :=
      surgFacts m hm hmlt
    obtain ⟨c₀', hc₀'eq, hc₀'TB, hc₀'c₁, hc₀'P, hmark'⟩ :=
      surgFacts m' hm' hm'lt
    have hmPred : Marked (Pred M) m := by
      apply Marked_Pred M m hM hlen hm
      simpa [j₁, lastIdx] using hmlt
    have hm'Pred : Marked (Pred M) m' := by
      apply Marked_Pred M m' hM hlen hm'
      simpa [j₁, lastIdx] using hm'lt
    have hnestPred : (c₀, c₀') ∈ MarkedB := by
      simpa [hc₀eq, hc₀'eq] using ih m m' hmPred hm'Pred hmm'
    rcases hnestPred with ⟨sA, bA, hdA⟩
    obtain ⟨s, b, hd, hflat, _⟩ :=
      replaceScb_spec hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
    obtain ⟨s', b', hd', hflat', _⟩ :=
      replaceScb_spec hc₀'TB hc₁TB hc₁P hc₂TB hc₂P hc₀'c₁
    have hdComp : scb_decomp c₀ (sA ++ s') (flatBT c₁) (b' ++ bA) :=
      scb_compose c₀ c₀' sA s' (flatBT c₁) b' bA hc₀'P hdA hd'
    have hctx : s = sA ++ s' ∧ b = b' ++ bA :=
      scb_unique_decomp_unconditional c₀ s (sA ++ s') (flatBT c₁)
        b (b' ++ bA) hd hdComp
    have hflatNest : flatBT (Mark M m) =
        sA ++ flatBT (Mark M m') ++ bA := by
      rw [hmark, hmark', hflat, hflat', hctx.1, hctx.2]
      simp [List.append_assoc]
    have hmark'Facts := replaceScb_preserves_marked
      hc₀'TB hc₁TB hc₁P hc₂TB hc₂P hc₀'c₁
    have hmark'P := replaceScb_principal
      hc₀'TB hc₀'P hc₁TB hc₁P hc₂TB hc₂P hc₀'c₁
    refine ⟨sA, bA, hflatNest, ?_, hdA.2.2⟩
    intro _
    rw [hmark']
    exact (principal_flat_properties hmark'Facts.1 hmark'P).1
  · have hm'eq : m' = j₁ := by omega
    have hmarkLast : Mark M m' = db := by
      simpa [j₁, t₁, jp, c₁, c₂, db, ht₁ne, hm'eq] using heq m'
    by_cases hmlt : m < j₁
    · obtain ⟨c₀, _hc₀eq, hc₀TB, hc₀c₁, _hc₀P, hmark⟩ :=
        surgFacts m hm hmlt
      have hmarkC₂ : (Mark M m, c₂) ∈ MarkedB := by
        rw [hmark]
        exact (replaceScb_preserves_marked
          hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁).2
      rw [hmarkLast]
      exact markedBCompose hc₂P hmarkC₂ hc₂db
    · have hmeq : m = j₁ := by
        have hmLast : m ≤ j₁ := hmm'.trans hm'Last
        omega
      have heqmm' : m = m' := hmeq.trans hm'eq.symm
      rw [← heqmm']
      exact MarkSelfMarkedB M m hR hm

/-- If `m ≤ m'` are marked columns of a reduced pair sequence, the later
marked value occurs as a marked principal component of the earlier one. -/
theorem Mark_MarkedB_nest (M : PS) (m m' : ℕ)
    (hm : Marked M m) (hm' : Marked M m') (hmm' : m ≤ m')
    (hR : RTPS M) : (Mark M m, Mark M m') ∈ MarkedB := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M m m' with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hmLast := Marked_index_le_last hm
      have hm'Last := Marked_index_le_last hm'
      by_cases hOne : Lng M = 1
      · have heq : m = m' := by omega
        rw [← heq]
        exact MarkSelfMarkedB M m hR hm
      · have hlen : 1 < Lng M := by omega
        by_cases hmono : monoT M = true
        · have hpredR : RTPS (Pred M) := RTPS_Pred M hR
          have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
          have hpredLt : Lng (Pred M) < n := by rw [hpredLen, ← hn]; omega
          have ihPred : ∀ a b, Marked (Pred M) a → Marked (Pred M) b →
              a ≤ b → (Mark (Pred M) a, Mark (Pred M) b) ∈ MarkedB := by
            intro a b ha hb hab
            exact ih (Lng (Pred M)) hpredLt (Pred M) a b ha hb hab hpredR rfl
          by_cases ht₁ : Trans (Pred M) = BZero
          · have hpredM : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
            have hzPred : zeroT (Pred M) = true :=
              (Trans_preserves_zeroT (Pred M) hpredM).2 ht₁
            have hpredOne : Lng (Pred M) = 1 := by
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzPred
              exact hzPred.1
            have hMtwo : Lng M = 2 := by omega
            by_cases heq : m = m'
            · rw [← heq]
              exact MarkSelfMarkedB M m hR hm
            · have hm0 : m = 0 := by omega
              have hm'1 : m' = 1 := by omega
              let db := Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero
              have hdbTB : db ∈ T_B :=
                Dprin_mem_T_B (v := (entry M 1 (lastIdx M) : ℕ∞))
                  (by simp) zeroMemTB
              have hdbP : ∃ p, db = .trm [p] := ⟨_, rfl⟩
              have hself : (db, db) ∈ MarkedB :=
                markedBSelfPrincipal hdbTB hdbP
              have hnest : (Dprin 0 db, db) ∈ MarkedB :=
                markedBDprinLift 0 hdbTB hdbP hself
              have heqs := (Trans_Mark_mono_equations M hR hlen hmono).2
              have hmark0 : Mark M m = Dprin 0 db := by
                simpa [hm0, db, ht₁] using heqs m
              have hmark1 : Mark M m' = db := by
                simpa [hm'1, hMtwo, lastIdx, db, ht₁] using heqs m'
              simpa [hmark0, hmark1] using hnest
          · exact MarkMarkedBNestSurgery M m m' hR hmono hlen ht₁
              hm hm' hmm' ihPred
        · have hz : zeroT M = false := by
            simp [zeroT, hOne]
          have hmulti : multiT M = true := by
            simp [multiT, hz, hmono]
          let J := M.drop (Pcut M)
          have hlast := trans_multi_last_component M hM hmulti
          let pJ := (P M).getD ((P M).length - 1) []
          have hpJeq : pJ = J := by simpa [pJ, J] using hlast.1
          have hPne : P M ≠ [] := P_nonempty M
          have hidx : (P M).length - 1 < (P M).length := by
            have := List.length_pos_of_ne_nil hPne
            omega
          have hpJR : RTPS pJ :=
            (RTPS_iff_P_components M hM).1 hR ((P M).length - 1) hidx
          have hJR : RTPS J := by simpa [hpJeq] using hpJR
          have hcut := Pcut_props M hlen
          have hJLen : Lng J = Lng M - Pcut M := by simp [J]
          have hJLt : Lng J < n := by rw [hJLen, ← hn]; omega
          have hmeq := (Trans_Mark_multi_equations M hR hmulti).2
          by_cases hJzero : J = [(0, 0)]
          · have hdbTB : Dprin 0 BZero ∈ T_B :=
              Dprin_mem_T_B (by simp) zeroMemTB
            have hself := markedBSelfPrincipal hdbTB
              (show ∃ p, Dprin 0 BZero = .trm [p] from ⟨_, rfl⟩)
            have hmarkm : Mark M m = Dprin 0 BZero := by
              simpa [J, hJzero] using hmeq m
            have hmarkm' : Mark M m' = Dprin 0 BZero := by
              simpa [J, hJzero] using hmeq m'
            simpa [hmarkm, hmarkm'] using hself
          · have hmComp := multi_Marked_last_component M m hM hmulti hm
            have hm'Comp := multi_Marked_last_component M m' hM hmulti hm'
            have hnestJ := ih (Lng J) hJLt J (m - Pcut M) (m' - Pcut M)
              (by simpa [J] using hmComp.2)
              (by simpa [J] using hm'Comp.2) (Nat.sub_le_sub_right hmm' _) hJR rfl
            have hmarkm : Mark M m = Mark J (m - Pcut M) := by
              simpa [J, hJzero] using hmeq m
            have hmarkm' : Mark M m' = Mark J (m' - Pcut M) := by
              simpa [J, hJzero] using hmeq m'
            simpa [hmarkm, hmarkm'] using hnestJ

/-! ## 右端値 -/

/-- The marked translation at the final column is its row-1 principal term.
The nonzero assumption is necessary only for the singleton base case. -/
theorem Mark_rightmost1_forward (M : PS) (hR : RTPS M)
    (hz : zeroT M = false) :
    Mark M (Lng M - 1) =
      Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      rw [← hn]
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      by_cases hOne : Lng M = 1
      · obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
        subst M
        have hR' : RTPS [(v, v)] := hR
        have hv : v ≠ 0 := by
          intro hv
          subst v
          simp [zeroT, entry] at hz
        change Mark [(v, v)] 0 = Dprin (v : ℕ∞) BZero
        rw [Mark_eq_lengthAux [(v, v)] 0 hR']
        have hred : reduced [(v, v)] = true := hR'
        simp [MarkAux, lastIdx, entry, hv, BZero, hred]
      · have hlen : 1 < Lng M := by omega
        by_cases hmono : monoT M = true
        · have heq := (Trans_Mark_mono_equations M hR hlen hmono).2
          have hlastNe : Lng M - 1 ≠ 0 := by omega
          simpa [lastIdx, hlastNe] using heq (Lng M - 1)
        · have hmulti : multiT M = true := by
            simp [multiT, hz, hmono]
          let J := M.drop (Pcut M)
          have hlast := (trans_multi_last_component M hM hmulti).1
          have hPne : P M ≠ [] := P_nonempty M
          have hidx : (P M).length - 1 < (P M).length := by
            have := List.length_pos_of_ne_nil hPne
            omega
          have hJR : RTPS J := by
            have hh := (RTPS_iff_P_components M hM).1 hR
              ((P M).length - 1) hidx
            dsimp [J]
            rw [← hlast]
            exact hh
          have hcut := Pcut_props M hlen
          have hJLen : Lng J = Lng M - Pcut M := by simp [J]
          have hJLt : Lng J < n := by rw [hJLen, ← hn]; omega
          have heq := (Trans_Mark_multi_equations M hR hmulti).2
          by_cases hJzero : J = [(0, 0)]
          · have hlastEq : Lng M - 1 = Pcut M := by
              have : Lng J = 1 := by simp [hJzero]
              omega
            have hentry : entry M 1 (Lng M - 1) = 0 := by
              have hd := entry_drop M (Pcut M) 1 0
              have hd' : entry J 1 0 = entry M 1 (Pcut M + 0) := by
                simpa [J] using hd
              simpa [hJzero, entry, hlastEq] using hd'.symm
            simpa [J, hJzero, hentry] using heq (Lng M - 1)
          · have hzJ : zeroT J = false := by
              apply Bool.eq_false_of_not_eq_true
              intro hzJ
              apply hJzero
              rw [← RTPS_Red_eq J hJR]
              exact Red_zero_mr J hzJ
            have hIH := ih (Lng J) hJLt J hJR hzJ rfl
            have hshift : Lng M - 1 - Pcut M = Lng J - 1 := by
              rw [hJLen]
              omega
            have hentry : entry J 1 (Lng J - 1) =
                entry M 1 (Lng M - 1) := by
              rw [entry_drop]
              congr 2
              rw [hJLen]
              omega
            have hmark : Mark M (Lng M - 1) =
                Mark J (Lng J - 1) := by
              simpa [J, hJzero, hshift] using heq (Lng M - 1)
            rw [hmark, hIH, hentry]

/-- Before the final marked column, a marked value still has a nonempty body;
in particular it is not the one-node row-1 principal term. -/
theorem Mark_tail_nonzero (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hmlt : m < Lng M - 1) :
    Mark M m ≠ Dprin (entry M 1 m : ℕ∞) BZero := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M m with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hlen : 1 < Lng M := by
        have hpos := List.length_pos_of_ne_nil hM
        omega
      by_cases hmono : monoT M = true
      · have hpredR : RTPS (Pred M) := RTPS_Pred M hR
        have hpredM : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
        have heq := (Trans_Mark_mono_equations M hR hlen hmono).2
        by_cases ht₁ : Trans (Pred M) = BZero
        · have hzPred : zeroT (Pred M) = true :=
            (Trans_preserves_zeroT (Pred M) hpredM).2 ht₁
          have hpredOne : Lng (Pred M) = 1 := by
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzPred
            exact hzPred.1
          have hpredLen := length_Pred M hlen
          have hMtwo : Lng M = 2 := by omega
          have hm0 : m = 0 := by omega
          let db := Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero
          have hmark : Mark M m = Dprin 0 db := by
            simpa [hm0, db, ht₁] using heq m
          intro hbad
          have hflat := congrArg (fun t => (flatBT t).length) hbad
          rw [hmark] at hflat
          simp [db, Dprin, BZero, flatBT, flatBP] at hflat
        · let j₁ := lastIdx M
          let jp := lastParent M
          let t₁ := Trans (Pred M)
          let c₁ := Mark (Pred M) (Adm M jp)
          let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
          let c₀ := Mark (Pred M) m
          have hp : hasParent M 0 (Lng M - 1) = true :=
            mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
          have hc₁Marked : Marked (Pred M) (Adm M jp) := by
            simpa [jp] using Marked_Pred_Adm M hM hlen hp
          have hc₁Inv :=
            (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hc₁Marked
          have hc₁TB : c₁ ∈ T_B := by simpa [c₁] using hc₁Inv.1
          have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
            simpa [t₁, c₁] using hc₁Inv.2
          have hc₁P : ∃ p, c₁ = .trm [p] := by
            apply marked_component_principal
            · simpa [t₁] using ht₁
            · exact ht₁c₁
          have hmPred : Marked (Pred M) m :=
            Marked_Pred M m hM hlen hm hmlt
          have hmjp : m ≤ jp := by
            simpa [jp, lastParent] using
              marked_le_lastParent M hm hmono hlen hmlt
          have hmAdm : m ≤ Adm M jp := Adm_max M m jp hm.2.1 hmjp
          have hc₀c₁ : (c₀, c₁) ∈ MarkedB := by
            simpa [c₀, c₁] using
              Mark_MarkedB_nest (Pred M) m (Adm M jp)
                hmPred hc₁Marked hmAdm hpredR
          have hc₀Inv := (Trans_Mark_invariant (Pred M) hpredR).2.2 m hmPred
          have hc₀TB : c₀ ∈ T_B := by simpa [c₀] using hc₀Inv.1
          have hc₂Facts := transC2Core_properties M c₁ hc₁TB hc₁P
          have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂Facts.1
          have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂Facts.2
          have hrep := replaceScb_preserves_marked
            hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
          have hrepNe : replaceScb c₀ c₁ c₂ ≠ BZero :=
            markedBHostNeZero hc₂P hrep.2
          have hmark : Mark M m = replaceScb c₀ c₁ c₂ := by
            have hmltj : m < j₁ := by simpa [j₁, lastIdx] using hmlt
            cases hhead : (scbContexts c₀ (flatBT c₁)).head? with
            | none =>
                have hzrep : replaceScb c₀ c₁ c₂ = BZero := by
                  simp [replaceScb, hhead]
                exact (hrepNe hzrep).elim
            | some sb =>
                rcases sb with ⟨s, b⟩
                have hraw := heq m
                simp [j₁, jp, c₁, c₀, ht₁, hmltj, hhead] at hraw
                simpa [replaceScb, hhead] using hraw
          have hmarkC₂ : (Mark M m, c₂) ∈ MarkedB := by
            rw [hmark]
            exact hrep.2
          intro hbad
          rcases hmarkC₂ with ⟨s, b, hd⟩
          have hflatLen := congrArg List.length hd.1
          rw [hbad] at hflatLen
          have hc₂Len : 3 ≤ (flatBT c₂).length := by
            simpa [c₂] using transC2CoreFlatLength M c₁
          simp only [List.length_append] at hflatLen
          have htargetLen :
              (flatBT (Dprin (entry M 1 m : ℕ∞) BZero)).length = 2 := by
            simp [Dprin, BZero, flatBT, flatBP]
          rw [htargetLen] at hflatLen
          omega
      · have hz : zeroT M = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hz
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
          omega
        have hmulti : multiT M = true := by simp [multiT, hz, hmono]
        let J := M.drop (Pcut M)
        have hlast := (trans_multi_last_component M hM hmulti).1
        have hPne : P M ≠ [] := P_nonempty M
        have hidx : (P M).length - 1 < (P M).length := by
          have := List.length_pos_of_ne_nil hPne
          omega
        have hJR : RTPS J := by
          have hh := (RTPS_iff_P_components M hM).1 hR
            ((P M).length - 1) hidx
          dsimp [J]
          rw [← hlast]
          exact hh
        have hcut := Pcut_props M hlen
        have hJLen : Lng J = Lng M - Pcut M := by simp [J]
        have hJLt : Lng J < n := by rw [hJLen, ← hn]; omega
        have hmParts := multi_Marked_last_component M m hM hmulti hm
        have hmJ : Marked J (m - Pcut M) := by simpa [J] using hmParts.2
        have hmJLast := Marked_index_le_last hmJ
        have hmJlt : m - Pcut M < Lng J - 1 := by
          rw [hJLen]
          omega
        have heq := (Trans_Mark_multi_equations M hR hmulti).2
        by_cases hJzero : J = [(0, 0)]
        · have hJone : Lng J = 1 := by simp [hJzero]
          omega
        · have hIH := ih (Lng J) hJLt J (m - Pcut M)
            hmJ hJR hmJlt rfl
          have hmark : Mark M m = Mark J (m - Pcut M) := by
            simpa [J, hJzero] using heq m
          have hentry : entry J 1 (m - Pcut M) = entry M 1 m := by
            rw [entry_drop]
            congr 2
            omega
          intro hbad
          apply hIH
          have hbad' := hmark.symm.trans hbad
          simpa [hentry] using hbad'

/-- Corrected A17 form of the article proposition.  The zero singleton must be
excluded: its marked value is `BZero`, not `D_0 BZero`. -/
theorem m_7_3_Mark_rightmost1 (M : PS) (m : ℕ)
    (hm : Marked M m) (hR : RTPS M) (hz : zeroT M = false) :
    (m = Lng M - 1) ↔
      Mark M m = Dprin (entry M 1 m : ℕ∞) BZero := by
  constructor
  · intro hlast
    subst m
    exact Mark_rightmost1_forward M hR hz
  · intro hmark
    have hmLast := Marked_index_le_last hm
    by_contra hne
    have hmlt : m < Lng M - 1 := by omega
    exact Mark_tail_nonzero M m hm hR hmlt hmark

/-- Executable/formal witness for correction A17: the verbatim article form
fails on the reduced zero singleton. -/
theorem Mark_rightmost1_original_counterexample :
    Marked [(0, 0)] 0 ∧ RTPS [(0, 0)] ∧
      0 = Lng [(0, 0)] - 1 ∧
      Mark [(0, 0)] 0 ≠ Dprin (entry [(0, 0)] 1 0 : ℕ∞) BZero := by
  have hR : RTPS [(0, 0)] := by
    simpa [diagSeq] using RTPS_diagSeq_zero 0
  have hm : Marked [(0, 0)] 0 := by
    simp [Marked, TPS, adm, nadm, nextR, nextrel1, leR, le0, le0Aux,
      nextrel0, entry]
  have hmark : Mark [(0, 0)] 0 = BZero := by
    rw [Mark_eq_lengthAux [(0, 0)] 0 hR]
    have hred : reduced [(0, 0)] = true := hR
    simp [MarkAux, lastIdx, BZero, hred]
  refine ⟨hm, hR, by simp, ?_⟩
  rw [hmark]
  simp [entry, Dprin, BZero]

#print axioms Mark_MarkedB_nest
#print axioms Mark_rightmost1_forward
#print axioms Mark_tail_nonzero
#print axioms m_7_3_Mark_rightmost1
#print axioms Mark_rightmost1_original_counterexample

end PSS
