import «6».«6.5-Red-Pred-commute»
import «6».«6.3-marked-slice»
import «6».«6.3-admof-slice»
import «6».«6.6-P-preserves-reduced»
import «6».«6.6-reduced-leftend»
import «6».«6.6-condAB-coeff»
import «6».«6.6-one-column»
import «6».«6.6-Red2»
import «7».«7.2-scb-replaceable»
import «7».«7.2-scb-compose»
import «7».«7.2-add-scb»
import PSS.Trans

/-!
# §7.3 命題（`Trans` の well-defined 性）

- 原文: `tmp/content.md` の「命題（`Trans` の well-defined 性）」
- 訂正: A15（`RTPS` 核と有限 `Red` 軌道を組み合わせる）
- Isabelle: `Pred_RT_PS`, `trans_multiT_prefix_RT_PS`,
  `trans_multiT_last_component`, `Trans_Mark_invariant_aux`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private def flatBPSeq_tw : List BP → List Sym
  | [] => []
  | p :: ps => flatBP p ++ flatBPTail ps

private def ParsesBT (t : BT) : Prop :=
  ∀ rest fuel, (flatBT t).length < fuel →
    parseBTAux fuel (flatBT t ++ rest) = some (t, rest)

private def ParsesBP (p : BP) : Prop :=
  ∀ rest fuel, (flatBP p).length < fuel →
    parseBPAux fuel (flatBP p ++ rest) = some (p, rest)

private def ParsesSeq (ps : List BP) : Prop :=
  ps ≠ [] → ∀ acc rest fuel,
    (flatBPSeq_tw ps).length + 1 < fuel →
    parseBPSeqAux fuel (flatBPSeq_tw ps ++ .rp :: rest) acc =
      some (.trm (acc ++ ps), rest)

private def ParsesBPList : List BP → Prop
  | [] => True
  | p :: ps => ParsesBP p ∧ ParsesBPList ps ∧ ParsesSeq (p :: ps)

private theorem flatBPSeq_tw_cons (p : BP) (ps : List BP) :
    flatBPSeq_tw (p :: ps) = flatBP p ++ flatBPTail ps := rfl

private theorem parse_flat_BT (t : BT) : ParsesBT t := by
  exact BT.rec
    (motive_1 := ParsesBT)
    (motive_2 := ParsesBP)
    (motive_3 := ParsesBPList)
    (fun ps hps rest fuel hfuel => by
      cases ps with
      | nil =>
          cases fuel with
          | zero => simp [flatBT] at hfuel
          | succ fuel => simp [flatBT, parseBTAux, BZero]
      | cons p ps =>
          cases ps with
          | nil =>
              have hp := hps.1 rest fuel (by simpa [flatBT] using hfuel)
              cases p with
              | db u a =>
                  cases fuel with
                  | zero => simp [flatBT, flatBP] at hfuel
                  | succ fuel =>
                      cases hba : parseBTAux fuel (flatBT a ++ rest) with
                      | none => simp [flatBP, parseBPAux, hba] at hp
                      | some z =>
                          rcases z with ⟨a', rest'⟩
                          simp [flatBP, parseBPAux, hba] at hp
                          obtain ⟨rfl, rfl⟩ := hp
                          simp [flatBT, flatBP, parseBTAux, hba, Dprin]
          | cons q qs =>
              cases fuel with
              | zero => simp [flatBT] at hfuel
              | succ fuel =>
                  have hseq :
                      (flatBPSeq_tw (p :: q :: qs)).length + 1 < fuel := by
                    simp [flatBT, flatBPSeq_tw, List.length_append,
                      Nat.add_comm, Nat.add_left_comm] at hfuel ⊢
                    omega
                  have hpseq := hps.2.2 (by simp) [] rest fuel hseq
                  simpa [flatBT, flatBPSeq_tw, parseBTAux,
                    List.append_assoc] using hpseq)
    (fun u a ha rest fuel hfuel => by
      cases fuel with
      | zero => simp [flatBP] at hfuel
      | succ fuel =>
          have hbody : (flatBT a).length < fuel := by
            simpa [flatBP] using hfuel
          simp [flatBP, parseBPAux, ha rest fuel hbody])
    trivial
    (fun p ps hp hps => by
      refine ⟨hp, hps, ?_⟩
      intro _hne acc rest fuel hfuel
      cases fuel with
      | zero => simp [flatBPSeq_tw] at hfuel
      | succ fuel =>
          have hpbound : (flatBP p).length < fuel := by
            simp only [flatBPSeq_tw_cons, List.length_append] at hfuel
            omega
          let tail := flatBPTail ps ++ .rp :: rest
          have hparsep :
              parseBPAux fuel (flatBP p ++ tail) = some (p, tail) :=
            hp tail fuel hpbound
          dsimp [tail] at hparsep
          cases ps with
          | nil =>
              have hp0 :
                  parseBPAux fuel (flatBP p ++ .rp :: rest) =
                    some (p, .rp :: rest) := by
                simpa [flatBPTail] using hparsep
              rw [parseBPSeqAux]
              simp only [flatBPSeq_tw, flatBPTail, List.append_nil]
              rw [hp0]
          | cons q qs =>
              have htailbound :
                  (flatBPSeq_tw (q :: qs)).length + 1 < fuel := by
                simp [flatBPSeq_tw, flatBPTail] at hfuel ⊢
                omega
              have htailparse := hps.2.2 (by simp)
                (acc ++ [p]) rest fuel htailbound
              have hp0 :
                  parseBPAux fuel
                      (flatBP p ++ ((.cm :: flatBP q) ++
                        (flatBPTail qs ++ .rp :: rest))) =
                    some (p, ((.cm :: flatBP q) ++
                      (flatBPTail qs ++ .rp :: rest))) := by
                simpa [flatBPTail, List.append_assoc] using hparsep
              rw [parseBPSeqAux]
              simp only [flatBPSeq_tw, flatBPTail, List.append_assoc]
              rw [hp0]
              simpa [flatBPSeq_tw, List.append_assoc] using htailparse)
    t

/-- The executable parser used by `replaceScb` is a left inverse of the flat
encoding on every Buchholz term. -/
theorem unflatBT_flat (t : BT) : unflatBT (flatBT t) = t := by
  have hparse := parse_flat_BT t [] ((flatBT t).length + 1) (by omega)
  have hparse' :
      parseBTAux ((flatBT t).length + 1) (flatBT t) = some (t, []) := by
    simpa using hparse
  rw [unflatBT, hparse']

private theorem parse_flat_BP (p : BP) : ParsesBP p := by
  rcases p with ⟨u, a⟩
  intro rest fuel hfuel
  cases fuel with
  | zero => simp [flatBP] at hfuel
  | succ fuel =>
      have hbody : (flatBT a).length < fuel := by
        simpa [flatBP] using hfuel
      simp [flatBP, parseBPAux, parse_flat_BT a rest fuel hbody]

private theorem isPTBStr_flatBP (p : BP) :
    isPTBStr (flatBP p) = dfree_BP p := by
  have hp := parse_flat_BP p [] ((flatBP p).length + 1) (by omega)
  have hp' : parseBPAux ((flatBP p).length + 1) (flatBP p) =
      some (p, []) := by simpa using hp
  simp [isPTBStr, hp']

private theorem principal_flat_properties {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) :
    isPTB_str (flatBT c) ∧ isPTBStr (flatBT c) = true := by
  obtain ⟨p, rfl⟩ := hcP
  have hp : dfree_BP p = true := by
    simpa [T_B, dfree_BT, dfree_BPList] using hc
  constructor
  · exact ⟨p, hp, by simp [flatBT]⟩
  · simpa [flatBT, isPTBStr_flatBP p, hp]

private theorem scbContexts_contains {t : BT} {s c b : List Sym}
    (hd : scb_decomp t s c b) (hexec : isPTBStr c = true) :
    (s, b) ∈ scbContexts t c := by
  rcases hd with ⟨hflat, _hprincipal, htail⟩
  have htake : (flatBT t).take s.length = s := by
    rw [hflat]
    simp
  have hmid : ((flatBT t).drop s.length).take c.length = c := by
    rw [hflat]
    simp
  have hdrop : (flatBT t).drop (s.length + c.length) = b := by
    rw [hflat]
    simp
  have hall : b.all (fun x => decide (x = .rp)) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [htail x hx]
    decide
  have hidx : s.length < (flatBT t).length - c.length + 1 := by
    have hlen := congrArg List.length hflat
    simp only [List.length_append] at hlen
    omega
  unfold scbContexts
  rw [List.mem_filterMap]
  refine ⟨s.length, by simp [hidx], ?_⟩
  simp [htake, hmid, hdrop, hexec, hall]

private theorem flat_split_at (xs : List Sym) (i n : ℕ) :
    xs = xs.take i ++ (xs.drop i).take n ++ xs.drop (i + n) := by
  calc
    xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
    _ = xs.take i ++ ((xs.drop i).take n ++ (xs.drop i).drop n) := by
      exact congrArg (xs.take i ++ ·)
        (List.take_append_drop n (xs.drop i)).symm
    _ = xs.take i ++ (xs.drop i).take n ++ xs.drop (i + n) := by
      simp [List.drop_drop, List.append_assoc, Nat.add_comm]

private theorem scbContexts_mem_decomp {t : BT} {s c b : List Sym}
    (hc : isPTB_str c) (hm : (s, b) ∈ scbContexts t c) :
    scb_decomp t s c b := by
  unfold scbContexts at hm
  rw [List.mem_filterMap] at hm
  obtain ⟨i, hi, hout⟩ := hm
  simp only [List.mem_range] at hi
  dsimp only at hout
  split at hout
  next hcond =>
    have hh := hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hh
    have hpair : ((flatBT t).take i,
        (flatBT t).drop (i + c.length)) = (s, b) := by
      simpa using Option.some.inj hout
    have hs : (flatBT t).take i = s := congrArg Prod.fst hpair
    have hb : (flatBT t).drop (i + c.length) = b := congrArg Prod.snd hpair
    have hmidEq : ((flatBT t).drop i).take c.length = c := hh.1.1
    have hflat := flat_split_at (flatBT t) i c.length
    refine ⟨?_, fun _ => hc, ?_⟩
    · rw [hmidEq, hs, hb] at hflat
      exact hflat
    · intro x hx
      apply hh.2
      simpa [hb] using hx
  next hcond => simp at hout

private theorem scbContexts_head_decomp {t : BT} {s c b : List Sym}
    (hc : isPTB_str c)
    (hh : (scbContexts t c).head? = some (s, b)) :
    scb_decomp t s c b := by
  have hm : (s, b) ∈ scbContexts t c := by
    cases hlist : scbContexts t c with
    | nil => simp [hlist] at hh
    | cons x xs =>
        have hx : x = (s, b) := by simpa [hlist] using hh
        subst x
        simp [hlist]
  exact scbContexts_mem_decomp hc hm

private theorem scbContexts_head_exists {t c : BT}
    (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p])
    (hm : (t, c) ∈ MarkedB) :
    ∃ s b, (scbContexts t (flatBT c)).head? = some (s, b) ∧
      scb_decomp t s (flatBT c) b := by
  obtain ⟨hcptb, hcexec⟩ := principal_flat_properties hc hcP
  rcases hm with ⟨s₀, b₀, hd₀⟩
  have hmem := scbContexts_contains hd₀ hcexec
  cases hlist : scbContexts t (flatBT c) with
  | nil => simp [hlist] at hmem
  | cons x xs =>
      rcases x with ⟨s, b⟩
      refine ⟨s, b, by simp [hlist], ?_⟩
      apply scbContexts_mem_decomp hcptb
      simp [hlist]

private theorem replaceScb_preserves_marked {t c₁ c₂ : BT}
    (ht : t ∈ T_B) (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p])
    (hc₂ : c₂ ∈ T_B) (hc₂P : ∃ p, c₂ = .trm [p])
    (hm : (t, c₁) ∈ MarkedB) :
    replaceScb t c₁ c₂ ∈ T_B ∧
      (replaceScb t c₁ c₂, c₂) ∈ MarkedB := by
  obtain ⟨s, b, hhead, hd⟩ := scbContexts_head_exists hc₁ hc₁P hm
  have hc₂ptb := (principal_flat_properties hc₂ hc₂P).1
  obtain ⟨t₂, ht₂, hflat₂, hd₂⟩ :=
    scb_replaceable_corrected c₁ c₂ t s b hc₁ hc₂ ht hd
      (Or.inl hc₂ptb)
  have hrepl : replaceScb t c₁ c₂ = t₂ := by
    unfold replaceScb
    simp [hhead, ← hflat₂, unflatBT_flat]
  rw [hrepl]
  exact ⟨ht₂, ⟨s, b, hd₂⟩⟩

private theorem flatBT_length_pos (t : BT) : 0 < (flatBT t).length := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [flatBT]
  | cons p ps =>
      cases ps with
      | nil => rcases p with ⟨u, a⟩; simp [flatBT, flatBP]
      | cons q qs => simp [flatBT]

private theorem markedB_host_ne_zero_of_principal {t c : BT}
    (hcP : ∃ p, c = .trm [p]) (hm : (t, c) ∈ MarkedB) :
    t ≠ BZero := by
  obtain ⟨p, rfl⟩ := hcP
  rcases p with ⟨u, a⟩
  rcases hm with ⟨s, b, hd⟩
  intro ht
  subst t
  have hlen := congrArg List.length hd.1
  have hapos := flatBT_length_pos a
  simp only [BZero, flatBT, flatBP, List.length_cons,
    List.length_append, List.length_nil, Nat.zero_add] at hlen
  omega

private theorem replaceScb_ne_zero {t c₁ c₂ : BT}
    (ht : t ∈ T_B) (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p])
    (hc₂ : c₂ ∈ T_B) (hc₂P : ∃ p, c₂ = .trm [p])
    (hm : (t, c₁) ∈ MarkedB) : replaceScb t c₁ c₂ ≠ BZero := by
  have hmarked := (replaceScb_preserves_marked ht hc₁ hc₁P hc₂ hc₂P hm).2
  exact markedB_host_ne_zero_of_principal hc₂P hmarked

private theorem replaceScb_spec {t c₁ c₂ : BT}
    (ht : t ∈ T_B) (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p])
    (hc₂ : c₂ ∈ T_B) (hc₂P : ∃ p, c₂ = .trm [p])
    (hm : (t, c₁) ∈ MarkedB) :
    ∃ s b, scb_decomp t s (flatBT c₁) b ∧
      flatBT (replaceScb t c₁ c₂) = s ++ flatBT c₂ ++ b ∧
      scb_decomp (replaceScb t c₁ c₂) s (flatBT c₂) b := by
  obtain ⟨s, b, hhead, hd⟩ := scbContexts_head_exists hc₁ hc₁P hm
  have hc₂ptb := (principal_flat_properties hc₂ hc₂P).1
  obtain ⟨t₂, _ht₂, hflat₂, hd₂⟩ :=
    scb_replaceable_corrected c₁ c₂ t s b hc₁ hc₂ ht hd
      (Or.inl hc₂ptb)
  have hrepl : replaceScb t c₁ c₂ = t₂ := by
    unfold replaceScb
    simp [hhead, ← hflat₂, unflatBT_flat]
  subst t₂
  exact ⟨s, b, hd, hflat₂, hd₂⟩

private theorem principal_of_flatBT_head_dsym {t : BT}
    (h : ∃ v, (flatBT t).head? = some (.dsym v)) :
    ∃ p, t = .trm [p] := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [flatBT] at h
  | cons p ps =>
      cases ps with
      | nil => exact ⟨p, rfl⟩
      | cons q qs => simp [flatBT] at h

private theorem replaceScb_principal {c₀ c₁ c₂ : BT}
    (hc₀ : c₀ ∈ T_B) (hc₀P : ∃ p, c₀ = .trm [p])
    (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p])
    (hc₂ : c₂ ∈ T_B) (hc₂P : ∃ p, c₂ = .trm [p])
    (hm : (c₀, c₁) ∈ MarkedB) :
    ∃ p, replaceScb c₀ c₁ c₂ = .trm [p] := by
  obtain ⟨s, b, hd, hflat, _⟩ :=
    replaceScb_spec hc₀ hc₁ hc₁P hc₂ hc₂P hm
  obtain ⟨p₀, hp₀⟩ := hc₀P
  obtain ⟨p₂, hp₂⟩ := hc₂P
  have hhead : ∃ v,
      (flatBT (replaceScb c₀ c₁ c₂)).head? = some (.dsym v) := by
    cases s with
    | nil =>
        rcases p₂ with ⟨v, a⟩
        refine ⟨v, ?_⟩
        simpa [hp₂, flatBT, flatBP] using congrArg List.head? hflat
    | cons x xs =>
        rcases p₀ with ⟨v, a⟩
        have hx : x = .dsym v := by
          have hh := congrArg List.head? hd.1
          simpa [hp₀, flatBT, flatBP] using hh.symm
        refine ⟨v, ?_⟩
        have hh := congrArg List.head? hflat
        simpa [hx] using hh
  exact principal_of_flatBT_head_dsym hhead

private theorem marked_component_principal {t c : BT}
    (ht : t ≠ BZero) (hm : (t, c) ∈ MarkedB) :
    ∃ p, c = .trm [p] := by
  rcases hm with ⟨s, b, hd⟩
  rcases hd.2.1 ht with ⟨p, _hp, hflat⟩
  refine ⟨p, ?_⟩
  apply flatBT_injective
  simpa [flatBT] using hflat

private theorem addBT_ne_zero_right (a b : BT) (hb : b ≠ BZero) :
    addBT a b ≠ BZero := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  cases bs with
  | nil => exact (hb rfl).elim
  | cons p ps => simp [addBT, BZero]

private theorem BZero_mem_T_B : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem Dprin_mem_T_B {v : ℕ∞} {t : BT} (hv : v ≠ ⊤)
    (ht : t ∈ T_B) : Dprin v t ∈ T_B := by
  simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList, hv] using ht

private theorem dfree_BPList_take (ps : List BP) (n : ℕ)
    (hps : dfree_BPList ps = true) : dfree_BPList (ps.take n) = true := by
  induction n generalizing ps with
  | zero => simp [dfree_BPList]
  | succ n ih =>
      cases ps with
      | nil => simp [dfree_BPList]
      | cons p ps =>
          simp only [dfree_BPList, Bool.and_eq_true] at hps
          simpa [dfree_BPList] using And.intro hps.1 (ih ps hps.2)

private theorem flatMap_untrm_take_map (ps : List BP) (n : ℕ) :
    ((ps.map fun p => BT.trm [p]).take n).flatMap untrm = ps.take n := by
  induction n generalizing ps with
  | zero => simp
  | succ n ih =>
      cases ps with
      | nil => simp
      | cons p ps => simp [ih ps, untrm]

private theorem SigmaB_PB_take_mem_T_B (t : BT) (n : ℕ) (ht : t ∈ T_B) :
    SigmaB ((PB t).take n) ∈ T_B := by
  rcases t with ⟨ps⟩
  change dfree_BPList ps = true at ht
  change dfree_BPList (((ps.map fun p => BT.trm [p]).take n).flatMap untrm) = true
  rw [flatMap_untrm_take_map]
  exact dfree_BPList_take ps n ht

private theorem dfree_BP_of_mem_local {ps : List BP} {p : BP}
    (hps : dfree_BPList ps = true) (hp : p ∈ ps) : dfree_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [dfree_BPList, Bool.and_eq_true] at hps
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]
        exact hps.1
      · exact ih hps.2 hp

private theorem PB_getD_mem_T_B (t : BT) (j : ℕ) (ht : t ∈ T_B) :
    (PB t).getD j BZero ∈ T_B := by
  by_cases hj : j < (PB t).length
  · rw [getD_eq_getElem_idx (PB t) BZero hj]
    rcases t with ⟨ps⟩
    change dfree_BPList ps = true at ht
    simp only [PB, List.length_map] at hj
    simp only [PB, List.getElem_map]
    have hmem : ps[j] ∈ ps := List.getElem_mem hj
    have hdf : dfree_BP ps[j] = true := dfree_BP_of_mem_local ht hmem
    simpa [T_B, dfree_BT, dfree_BPList] using hdf
  · have hget : (PB t).getD j BZero = BZero := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hget]
    exact BZero_mem_T_B

private theorem bpHeadT_mem_T_B (t : BT) (ht : t ∈ T_B) :
    bpHeadT t ∈ T_B := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simpa [bpHeadT] using BZero_mem_T_B
  | cons p ps =>
      rcases p with ⟨v, b⟩
      change dfree_BPList (.db v b :: ps) = true at ht
      simp only [dfree_BPList, dfree_BP, Bool.and_eq_true] at ht
      simpa [bpHeadT, T_B] using ht.1.2

private theorem transC2Core_mem_T_B_aux (M : PS) (w : ℕ∞) (t₂ : BT)
    (hw : w ≠ ⊤) (ht₂ : t₂ ∈ T_B) : transC2Core M w t₂ ∈ T_B := by
  let db : BT := Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero
  have hdb : db ∈ T_B := by
    apply Dprin_mem_T_B
    · simp
    · exact BZero_mem_T_B
  by_cases hA :
      (transCondI M || transCondIII M || transCondV M) = true
  · simp only [transC2Core, hA, if_true]
    exact Dprin_mem_T_B hw (addBT_mem_T_B ht₂ hdb)
  · by_cases hVI : transCondVI M = true
    · simp only [transC2Core, hA, if_false, hVI, if_true]
      exact Dprin_mem_T_B hw
        (Dprin_mem_T_B
          (v := (entry M 1 (lastIdx M) : ℕ∞)) (by simp) BZero_mem_T_B)
    · by_cases hz : t₂ = BZero
      · simp only [transC2Core, hA, if_false, hVI, beq_iff_eq, hz, if_true]
        exact Dprin_mem_T_B hw
          (Dprin_mem_T_B
            (v := (entry M 1 (lastParent M) : ℕ∞)) (by simp)
            (Dprin_mem_T_B
              (v := (entry M 1 (lastIdx M) : ℕ∞)) (by simp) BZero_mem_T_B))
      · let pJ := (PB t₂).getD ((PB t₂).length - 1) BZero
        have hpJ : pJ ∈ T_B := PB_getD_mem_T_B t₂ ((PB t₂).length - 1) ht₂
        let leftDj₀ := bpHeadV pJ == (entry M 1 (lastParent M) : ℕ∞)
        let t₃ := if leftDj₀ then SigmaB ((PB t₂).take ((PB t₂).length - 1)) else t₂
        let t₄ := if leftDj₀ then bpHeadT pJ else t₂
        have ht₃ : t₃ ∈ T_B := by
          dsimp [t₃]
          split
          · exact SigmaB_PB_take_mem_T_B t₂ ((PB t₂).length - 1) ht₂
          · exact ht₂
        have ht₄ : t₄ ∈ T_B := by
          dsimp [t₄]
          split
          · exact bpHeadT_mem_T_B pJ hpJ
          · exact ht₂
        have hinner : addBT t₄ db ∈ T_B := addBT_mem_T_B ht₄ hdb
        have hmiddle :
            Dprin (entry M 1 (lastParent M) : ℕ∞) (addBT t₄ db) ∈ T_B :=
          Dprin_mem_T_B (by simp) hinner
        have hbody : addBT t₃
            (Dprin (entry M 1 (lastParent M) : ℕ∞) (addBT t₄ db)) ∈ T_B :=
          addBT_mem_T_B ht₃ hmiddle
        simpa [transC2Core, hA, hVI, hz, pJ, leftDj₀, t₃, t₄] using
          Dprin_mem_T_B hw hbody

private theorem transC2Core_principal (M : PS) (w : ℕ∞) (t₂ : BT) :
    ∃ p, transC2Core M w t₂ = .trm [p] := by
  unfold transC2Core
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

private theorem transC2Core_properties (M : PS) (c₁ : BT)
    (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p]) :
    transC2Core M (bpHeadV c₁) (bpHeadT c₁) ∈ T_B ∧
      ∃ p, transC2Core M (bpHeadV c₁) (bpHeadT c₁) = .trm [p] := by
  obtain ⟨p, rfl⟩ := hc₁P
  rcases p with ⟨w, t₂⟩
  change dfree_BT (.trm [.db w t₂]) = true at hc₁
  simp only [dfree_BT, dfree_BPList, dfree_BP,
    Bool.and_eq_true, Bool.true_eq] at hc₁
  have hw : w ≠ ⊤ := by simpa using hc₁.1.1
  have ht₂ : t₂ ∈ T_B := hc₁.1.2
  constructor
  · simpa [bpHeadV, bpHeadT] using
      transC2Core_mem_T_B_aux M w t₂ hw ht₂
  · simpa [bpHeadV, bpHeadT] using transC2Core_principal M w t₂

private theorem markedB_self_principal {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) : (c, c) ∈ MarkedB := by
  refine ⟨[], [], ?_⟩
  refine ⟨by simp, ?_, by simp⟩
  intro _
  exact (principal_flat_properties hc hcP).1

private theorem markedB_Dprin_lift {t c : BT} (v : ℕ∞)
    (hc : c ∈ T_B) (hcP : ∃ p, c = .trm [p])
    (hm : (t, c) ∈ MarkedB) : (Dprin v t, c) ∈ MarkedB := by
  rcases hm with ⟨s, b, hd⟩
  exact ⟨.dsym v :: s, b,
    scb_compose_dprin v t s (flatBT c) b hd
      (principal_flat_properties hc hcP).1⟩

private theorem markedB_compose {t c₀ c₁ : BT}
    (hc₀P : ∃ p, c₀ = .trm [p])
    (h₀ : (t, c₀) ∈ MarkedB) (h₁ : (c₀, c₁) ∈ MarkedB) :
    (t, c₁) ∈ MarkedB := by
  rcases h₀ with ⟨s₀, b₀, hd₀⟩
  rcases h₁ with ⟨s₁, b₁, hd₁⟩
  exact ⟨s₀ ++ s₁, b₁ ++ b₀,
    scb_compose t c₀ s₀ s₁ (flatBT c₁) b₁ b₀
      hc₀P hd₀ hd₁⟩

private theorem markedB_addBT_right {Y X c : BT} (hX : X ≠ BZero)
    (hm : (X, c) ∈ MarkedB) : (addBT Y X, c) ∈ MarkedB := by
  rcases X with ⟨xs⟩
  cases xs with
  | nil => exact (hX rfl).elim
  | cons p ps =>
      rcases Y with ⟨ys⟩
      cases ys with
      | nil => simpa [addBT] using hm
      | cons y ys =>
          rcases hm with ⟨s, b, hd⟩
          change scb_decomp (.trm (p :: ps)) s (flatBT c) b at hd
          have hhost : BT.trm (p :: ps) ≠ BZero := by simp [BZero]
          have hcptb : isPTB_str (flatBT c) := hd.2.1 hhost
          rcases hcptb with ⟨cp, hcpdf, hcflat⟩
          cases ps with
          | nil =>
              refine ⟨(.lp :: flatComponentRun (y :: ys)) ++ s,
                b ++ [.rp], ?_⟩
              change scb_decomp (addBT (.trm (y :: ys)) (.trm [p]))
                ((.lp :: flatComponentRun (y :: ys)) ++ s)
                (flatBT c) (b ++ [.rp])
              refine ⟨?_, fun _ => ⟨cp, hcpdf, hcflat⟩, ?_⟩
              · change flatBT (.trm ((y :: ys) ++ [p])) = _
                rw [flatBT_multi_snoc]
                have hpflat : flatBP p = s ++ flatBT c ++ b := by
                  simpa [flatBT] using hd.1
                rw [hpflat]
                simp [List.append_assoc]
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hd.2.2 x hx
                · simpa using hx
          | cons q qs =>
              let tail : List BP := q :: qs
              have htail : tail ≠ [] := by simp [tail]
              let lastp : BP := tail.getLast htail
              let init : List BP := p :: tail.dropLast
              have hsplit : init ++ [lastp] = p :: tail := by
                simp only [init, List.cons_append]
                rw [List.dropLast_append_getLast htail]
              have hd' : scb_decomp (.trm (init ++ [lastp])) s
                  (flatBT c) b := by
                rw [hsplit]
                simpa [tail] using hd
              have hocc : flatBT (.trm (init ++ [lastp])) =
                  s ++ flatBP cp ++ b := by
                simpa [hcflat] using hd'.1
              have hcut : 1 + (flatComponentRun init).length ≤ s.length := by
                simpa [init] using
                  scb_cut_reaches_last p tail.dropLast lastp cp s b hocc hd'.2.2
              let oldPre : List Sym := .lp :: flatComponentRun init
              have holdlen : oldPre.length ≤ s.length := by
                dsimp [oldPre]
                omega
              have hshapeOld : flatBT (.trm (init ++ [lastp])) =
                  oldPre ++ flatBP lastp ++ [.rp] := by
                simpa [oldPre, init] using
                  flatBT_multi_snoc p tail.dropLast lastp
              have htake : s.take oldPre.length = oldPre := by
                have heq : oldPre ++ (flatBP lastp ++ [.rp]) =
                    s ++ (flatBP cp ++ b) := by
                  simpa [List.append_assoc] using hshapeOld.symm.trans hocc
                have ht := congrArg (List.take oldPre.length) heq
                simpa [List.take_append_of_le_length holdlen] using ht.symm
              have hs : s = oldPre ++ s.drop oldPre.length := by
                calc
                  s = s.take oldPre.length ++ s.drop oldPre.length :=
                    (List.take_append_drop oldPre.length s).symm
                  _ = oldPre ++ s.drop oldPre.length := by rw [htake]
              have hinner : flatBP lastp ++ [.rp] =
                  s.drop oldPre.length ++ flatBT c ++ b := by
                have heq := hshapeOld.symm.trans hd'.1
                rw [hs] at heq
                have heq' : oldPre ++ (flatBP lastp ++ [.rp]) =
                    oldPre ++
                      (s.drop oldPre.length ++ flatBT c ++ b) := by
                  simpa [List.append_assoc] using heq
                exact List.append_cancel_left heq'
              let newPre : List Sym :=
                .lp :: flatComponentRun (y :: (ys ++ init))
              have hadd :
                  addBT (.trm (y :: ys)) (.trm (p :: q :: qs)) =
                    .trm ((y :: (ys ++ init)) ++ [lastp]) := by
                simp only [addBT]
                congr 1
                rw [List.cons_append, List.cons_append, List.append_assoc,
                  hsplit]
              rw [hadd]
              refine ⟨newPre ++ s.drop oldPre.length, b, ?_⟩
              change scb_decomp
                (.trm ((y :: (ys ++ init)) ++ [lastp]))
                (newPre ++ s.drop oldPre.length) (flatBT c) b
              refine ⟨?_, fun _ => ⟨cp, hcpdf, hcflat⟩, hd'.2.2⟩
              rw [flatBT_multi_snoc]
              change newPre ++ flatBP lastp ++ [.rp] = _
              calc
                newPre ++ flatBP lastp ++ [.rp] =
                    newPre ++ (flatBP lastp ++ [.rp]) := by
                      simp [List.append_assoc]
                _ = newPre ++
                    (s.drop oldPre.length ++ flatBT c ++ b) := by rw [hinner]
                _ = (newPre ++ s.drop oldPre.length) ++ flatBT c ++ b := by
                      simp [List.append_assoc]

private theorem transC2Core_marked_fallback_aux (M : PS) (w : ℕ∞) (t₂ : BT)
    (hw : w ≠ ⊤) (ht₂ : t₂ ∈ T_B) :
    (transC2Core M w t₂,
      Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) ∈ MarkedB := by
  let db : BT := Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero
  have hdb : db ∈ T_B :=
    Dprin_mem_T_B (v := (entry M 1 (lastIdx M) : ℕ∞)) (by simp)
      BZero_mem_T_B
  have hdbP : ∃ p, db = .trm [p] := ⟨_, rfl⟩
  have hself : (db, db) ∈ MarkedB := markedB_self_principal hdb hdbP
  by_cases hA :
      (transCondI M || transCondIII M || transCondV M) = true
  · have hm : (addBT t₂ db, db) ∈ MarkedB :=
      add_scb_marked t₂ db ht₂ hdb hdbP
    have hout := markedB_Dprin_lift w hdb hdbP hm
    simpa [transC2Core, hA, db] using hout
  · by_cases hVI : transCondVI M = true
    · have hout := markedB_Dprin_lift w hdb hdbP hself
      simpa [transC2Core, hA, hVI, db] using hout
    · by_cases hz : t₂ = BZero
      · have hmid := markedB_Dprin_lift
          (entry M 1 (lastParent M) : ℕ∞) hdb hdbP hself
        have hout := markedB_Dprin_lift w hdb hdbP hmid
        simpa [transC2Core, hA, hVI, hz, db] using hout
      · let pJ := (PB t₂).getD ((PB t₂).length - 1) BZero
        have hpJ : pJ ∈ T_B :=
          PB_getD_mem_T_B t₂ ((PB t₂).length - 1) ht₂
        let leftDj₀ := bpHeadV pJ == (entry M 1 (lastParent M) : ℕ∞)
        let t₃ := if leftDj₀ then
          SigmaB ((PB t₂).take ((PB t₂).length - 1)) else t₂
        let t₄ := if leftDj₀ then bpHeadT pJ else t₂
        have ht₃ : t₃ ∈ T_B := by
          dsimp [t₃]
          split
          · exact SigmaB_PB_take_mem_T_B t₂ ((PB t₂).length - 1) ht₂
          · exact ht₂
        have ht₄ : t₄ ∈ T_B := by
          dsimp [t₄]
          split
          · exact bpHeadT_mem_T_B pJ hpJ
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
          exact markedB_Dprin_lift
            (entry M 1 (lastParent M) : ℕ∞) hdb hdbP hinnerM
        have houtLast : (addBT t₃ middle, middle) ∈ MarkedB :=
          add_scb_marked t₃ middle ht₃ hmiddleTB hmiddleP
        have houtDb : (addBT t₃ middle, db) ∈ MarkedB :=
          markedB_compose hmiddleP houtLast hmiddleM
        have hout := markedB_Dprin_lift w hdb hdbP houtDb
        simpa [transC2Core, hA, hVI, hz, pJ, leftDj₀, t₃, t₄,
          middle, db] using hout

private theorem transC2Core_marked_fallback (M : PS) (c₁ : BT)
    (hc₁ : c₁ ∈ T_B) (hc₁P : ∃ p, c₁ = .trm [p]) :
    (transC2Core M (bpHeadV c₁) (bpHeadT c₁),
      Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) ∈ MarkedB := by
  obtain ⟨p, rfl⟩ := hc₁P
  rcases p with ⟨w, t₂⟩
  change dfree_BT (.trm [.db w t₂]) = true at hc₁
  simp only [dfree_BT, dfree_BPList, dfree_BP,
    Bool.and_eq_true] at hc₁
  have hw : w ≠ ⊤ := by simpa using hc₁.1.1
  have ht₂ : t₂ ∈ T_B := hc₁.1.2
  simpa [bpHeadV, bpHeadT] using
    transC2Core_marked_fallback_aux M w t₂ hw ht₂

private theorem le1Aux_consecutive_chain (M : PS) (a b fuel : ℕ)
    (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → nextrel1 M (j - 1) j = true)
    (hfuel : b - a ≤ fuel) : le1Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by omega
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      by_cases heq : a = b
      · subst b
        simp [le1Aux]
      · have hablt : a < b := lt_of_le_of_ne hab heq
        rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        refine ⟨b - 1, by omega, hstep b hablt (le_refl _), ?_⟩
        apply ih (b := b - 1)
        · omega
        · intro j haj hjb
          exact hstep j haj (by omega)
        · omega

private theorem adm_row1_ancestry_local (M : PS) (j : ℕ)
    (hM : TPS M) (hj : j ≤ Lng M - 1) :
    leR M 1 (Adm M j) j = true := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : j < Lng M := by omega
  have haLe : Adm M j ≤ j := Adm_le M j
  have haL : Adm M j < Lng M := haLe.trans_lt hjL
  have hstep : ∀ k, Adm M j < k → k ≤ j →
      nextrel1 M (k - 1) k = true := by
    intro k hak hkj
    have hkadm : adm M k = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M k j hk hkj
      omega
    have hnadm : nadm M k = true := by
      simpa [adm] using hkadm
    have hkL : k < Lng M := hkj.trans_lt hjL
    have hpair : nextR M 1 (k - 1) k = true ∧
        nextR M 1 k (k + 1) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · exact hn
    simpa [nextR] using hpair.1
  have haux : le1Aux M (Lng M) (Adm M j) j = true :=
    le1Aux_consecutive_chain M (Adm M j) j (Lng M)
      haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_refl_local (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_implies_row0_local (M : PS) (fuel a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_local]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_local]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

private theorem row1_implies_row0_local (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_implies_row0_local M (Lng M) a b hM hh.1.2 hh.2

private theorem marked_Pred_local (M : PS) (m : ℕ)
    (hM : TPS M) (hlen : 1 < Lng M)
    (hm : Marked M m) (hmlast : m < Lng M - 1) :
    Marked (Pred M) m := by
  have hs := marked_slice M m 0 (Lng M - 2) hm
    (Nat.zero_le _) (by omega) (by omega)
  have hseg : seg M 0 (Lng M - 2) = Pred M := by
    calc
      seg M 0 (Lng M - 2) = M.take (Lng M - 1) := by
        symm
        simpa using take_eq_seg M (Lng M - 1) (by omega) (by omega)
      _ = Pred M := (Pred_eq_take M hlen).symm
  simpa [hseg] using hs

private theorem marked_Pred_Adm_local (M : PS)
    (hM : TPS M) (hlen : 1 < Lng M)
    (hp : hasParent M 0 (Lng M - 1) = true) :
    Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) := by
  let j₁ := Lng M - 1
  let jp := parent M 0 j₁
  let a := Adm M jp
  have hjp : jp < j₁ := by
    simpa [jp, j₁] using parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hjpLast : jp ≤ Lng M - 1 := by omega
  have haLe : a ≤ jp := by exact Adm_le M jp
  have haLast : a < j₁ := by omega
  have haAdm : adm M a = true := Adm_adm M jp
  have hle₁ : leR M 1 a jp = true :=
    adm_row1_ancestry_local M jp hM hjpLast
  have hle₀ : leR M 0 a jp = true :=
    row1_implies_row0_local M a jp hM hle₁
  have hnext : nextR M 0 jp j₁ = true := by
    simpa [jp, j₁] using hasParent_next_fseq M 0 (Lng M - 1) hp
  have hstep₀ : leR M 0 jp j₁ = true := nextR0_leR M jp j₁ hnext
  have hfull : leR M 0 a j₁ = true :=
    row0_transitive M a jp j₁ hM hle₀ hstep₀
  have hm : Marked M a := by
    exact ⟨hM, haAdm, by simpa [j₁] using hfull⟩
  simpa [a, jp, j₁] using marked_Pred_local M a hM hlen hm haLast

private theorem multi_Marked_last_component_local (M : PS) (m : ℕ)
    (hM : TPS M) (hmulti : multiT M = true) (hm : Marked M m) :
    Pcut M ≤ m ∧ Marked (M.drop (Pcut M)) (m - Pcut M) := by
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hle : leR M 0 m (Lng M - 1) = true := hm.2.2
  have hmle : m ≤ Lng M - 1 := by
    exact le0_index_fseq (by simpa [leR] using hle)
  have hcutm : Pcut M ≤ m := by
    by_contra hnot
    have hmlt : m < Pcut M := by omega
    by_cases hm0 : m = 0
    · subst m
      have hp := hmulti
      simp only [multiT, Bool.and_eq_true] at hp
      have hmono : monoT M = true := by
        simp [monoT, hp.1, hle]
      have hnmono : monoT M = false := by simpa using hp.2
      rw [hnmono] at hmono
      contradiction
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hcand : ((0 < m) && (m ≤ Lng M - 1) &&
          leR M 0 m (Lng M - 1)) = true := by
        simp [hmpos, hmle, hle]
      have hfalse := Pcut_not_candidate M hlen m hmlt
      rw [hcand] at hfalse
      contradiction
  refine ⟨hcutm, ?_⟩
  have hs := marked_slice M m (Pcut M) (Lng M - 1) hm
    hcutm hmle (le_refl _)
  have hcutL : Pcut M < Lng M := by
    have hc := Pcut_props M hlen
    omega
  rw [drop_eq_seg M (Pcut M) hcutL]
  exact hs

#print axioms unflatBT_flat

/-- In the multi branch, the prefix left after removing the final principal
component is again a reduced pair sequence. -/
theorem trans_multi_prefix_RTPS (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true) : RTPS (M.take (Pcut M)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have htakeT : TPS (M.take (Pcut M)) := by
    have htakeLen : Lng (M.take (Pcut M)) = Pcut M := by
      simp [Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
    exact List.ne_nil_of_length_pos (by simpa [htakeLen] using hcut.1)
  apply (RTPS_iff_P_components (M.take (Pcut M)) htakeT).2
  intro J hJ
  have hblocks : (P M).dropLast = P (M.take (Pcut M)) :=
    (P_last_multi M hmulti hlen).2
  have hJdrop : J < (P M).dropLast.length := by simpa [hblocks] using hJ
  have hJfull : J < (P M).length := by
    have hPne : P M ≠ [] := P_nonempty M
    simp only [List.length_dropLast] at hJdrop
    omega
  have hcomp := (RTPS_iff_P_components M hM).1 hR J hJfull
  have hget : ((P M).dropLast).getD J [] = (P M).getD J [] := by
    rw [getD_eq_getElem_idx ((P M).dropLast) [] hJdrop,
      getD_eq_getElem_idx (P M) [] hJfull]
    simp only [List.getElem_dropLast]
  rw [← hblocks]
  exact hget ▸ hcomp

private theorem getLastD_eq_getD_last_tw {α : Type} (Q : List α) (d : α)
    (hQ : Q ≠ []) : Q.getLastD d = Q.getD (Q.length - 1) d := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons x xs =>
      simp [List.getLastD, List.getD, List.getLast_eq_getElem]

/-- The last `P` component in the multi branch is exactly the suffix beginning
at `Pcut M`; consequently the local index `j₀` used by `TransAux` is `Pcut M`. -/
theorem trans_multi_last_component (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    (P M).getD ((P M).length - 1) [] = M.drop (Pcut M) ∧
      Lng M - 1 - Lng ((P M).getD ((P M).length - 1) []) + 1 = Pcut M := by
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hPne : P M ≠ [] := P_nonempty M
  have hlast : (P M).getD ((P M).length - 1) [] = M.drop (Pcut M) := by
    rw [← getLastD_eq_getD_last_tw (P M) [] hPne]
    exact (P_last_multi M hmulti hlen).1
  refine ⟨hlast, ?_⟩
  have hdropLen : Lng (M.drop (Pcut M)) = Lng M - Pcut M := by simp
  rw [hlast, hdropLen]
  omega

/-- The prefix expression occurring literally in `TransAux`'s multi branch is
the prefix ending just before `Pcut M`. -/
theorem trans_multi_prefix_seg (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) :
    let pJ := (P M).getD ((P M).length - 1) []
    let j₀ := Lng M - 1 - Lng pJ + 1
    seg M 0 (j₀ - 1) = M.take (Pcut M) := by
  dsimp only
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hj₀ := (trans_multi_last_component M hM hmulti).2
  rw [hj₀]
  exact (take_eq_seg M (Pcut M) hcut.1 hcut.2.1).symm

/-- On reduced inputs, every recursive call strictly shortens the pair
sequence.  Hence two fuel values at least `Lng M` compute identical `TransAux`
and `MarkAux` values.  This is the total Lean counterpart of the domain part
of Isabelle's `Trans_Mark_invariant_aux`. -/
theorem TransAux_MarkAux_fuel_irrel_RTPS (M : PS) (hR : RTPS M)
    (fuel₁ fuel₂ : ℕ) (hf₁ : Lng M ≤ fuel₁) (hf₂ : Lng M ≤ fuel₂) :
    TransAux fuel₁ M = TransAux fuel₂ M ∧
      ∀ m, MarkAux fuel₁ M m = MarkAux fuel₂ M m := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M fuel₁ fuel₂ with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hred : reduced M = true := hR
      cases fuel₁ with
      | zero => omega
      | succ fuel₁ =>
          cases fuel₂ with
          | zero => omega
          | succ fuel₂ =>
              by_cases hlast : Lng M - 1 = 0
              · constructor
                · simp [TransAux, lastIdx, hred, hlast]
                · intro m
                  simp [MarkAux, lastIdx, hred, hlast]
              · have hlen : 1 < Lng M := by omega
                by_cases hmono : monoT M = true
                · have hPR : RTPS (Pred M) := RTPS_Pred M hR
                  have hPL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
                  have hrec := ih (Lng (Pred M)) (by omega) (Pred M) hPR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  by_cases ht : TransAux fuel₁ (Pred M) = BZero
                  · have ht₂ : TransAux fuel₂ (Pred M) = BZero :=
                      hrec.1.symm.trans ht
                    constructor
                    · simp [TransAux, lastIdx, hred, hlast, hmono,
                        ht, ht₂]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        ht, ht₂]
                  · have ht₂ : TransAux fuel₂ (Pred M) ≠ BZero := by
                      intro heq
                      exact ht (hrec.1.trans heq)
                    constructor
                    · simp [TransAux, lastIdx, hred, hlast, hmono,
                        ht₂, hrec.1, hrec.2]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        ht₂, hrec.1, hrec.2]
                · have hzero : zeroT M = false := by
                    simp [zeroT]
                    omega
                  have hmulti : multiT M = true := by
                    simp [multiT, hzero, hmono]
                  have hcut := Pcut_props M hlen
                  let pJ := (P M).getD ((P M).length - 1) []
                  have hlastComp := trans_multi_last_component M hM hmulti
                  have hpJeq : pJ = M.drop (Pcut M) := by
                    simpa [pJ] using hlastComp.1
                  have hPne : P M ≠ [] := P_nonempty M
                  have hJ : (P M).length - 1 < (P M).length := by
                    have := List.length_pos_of_ne_nil hPne
                    omega
                  have hpJR : RTPS pJ := by
                    simpa [pJ] using
                      (RTPS_iff_P_components M hM).1 hR
                        ((P M).length - 1) hJ
                  have hpJL : Lng pJ < Lng M := by
                    calc
                      Lng pJ = Lng M - Pcut M := by rw [hpJeq]; simp
                      _ < Lng M := by omega
                  have hpJrec := ih (Lng pJ) (by omega) pJ hpJR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  let A := M.take (Pcut M)
                  have hAR : RTPS A := by
                    simpa [A] using trans_multi_prefix_RTPS M hR hmulti
                  have hAL : Lng A < Lng M := by
                    simp [A, Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
                    omega
                  have hArec := ih (Lng A) (by omega) A hAR
                    fuel₁ fuel₂ (by omega) (by omega) rfl
                  have hend :
                      Lng M - 1 - Lng
                          ((P M).getD ((P M).length - 1) []) =
                        Pcut M - 1 := by
                    omega
                  have hseg :
                      seg M 0
                        (Lng M - 1 - Lng
                          ((P M).getD ((P M).length - 1) [])) = A := by
                    rw [hend]
                    simpa [A] using
                      (take_eq_seg M (Pcut M) hcut.1 hcut.2.1).symm
                  have hsegRec :
                      TransAux fuel₁
                          (seg M 0
                            (Lng M - 1 - Lng
                              ((P M).getD ((P M).length - 1) []))) =
                        TransAux fuel₂
                          (seg M 0
                            (Lng M - 1 - Lng
                              ((P M).getD ((P M).length - 1) []))) := by
                    rw [hseg]
                    exact hArec.1
                  have hpJTrec :
                      TransAux fuel₁
                          ((P M).getD ((P M).length - 1) []) =
                        TransAux fuel₂
                          ((P M).getD ((P M).length - 1) []) := by
                    simpa [pJ] using hpJrec.1
                  have hpJMrec : ∀ m,
                      MarkAux fuel₁
                          ((P M).getD ((P M).length - 1) []) m =
                        MarkAux fuel₂
                          ((P M).getD ((P M).length - 1) []) m := by
                    simpa [pJ] using hpJrec.2
                  simp only [List.getD_eq_getElem?_getD] at hsegRec hpJTrec hpJMrec
                  by_cases hpJzero :
                      (P M).getD ((P M).length - 1) [] = [(0, 0)]
                  · simp only [List.getD_eq_getElem?_getD] at hpJzero
                    have hsegRecZero :
                        TransAux fuel₁ (seg M 0 (Lng M - 1 - 1)) =
                          TransAux fuel₂ (seg M 0 (Lng M - 1 - 1)) := by
                      simpa [hpJzero] using hsegRec
                    constructor
                    ·
                      simp [TransAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hsegRecZero]
                    · intro m
                      simp [MarkAux, lastIdx, hred, hlast, hmono, hpJzero]
                  · constructor
                    · simp only [List.getD_eq_getElem?_getD] at hpJzero
                      simp [TransAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hsegRec, hpJTrec]
                    · intro m
                      simp only [List.getD_eq_getElem?_getD] at hpJzero
                      simp [MarkAux, lastIdx, hred, hlast, hmono,
                        hpJzero, hpJMrec]

/-- The conservative public fuel bound is in particular at least the input
length. -/
theorem transFuel_ge_length (M : PS) : Lng M ≤ transFuel M := by
  have hfactor : 1 ≤ 8 * (nu M + 1) := by omega
  calc
    Lng M ≤ 1 * (Lng M + 1) := by omega
    _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
      Nat.mul_le_mul_right (Lng M + 1) hfactor
    _ ≤ (8 * (nu M + 1)) * (Lng M + 1) + 8 := by omega
    _ = transFuel M := by simp [transFuel, Nat.mul_assoc]

/-- On a reduced input, the public translation is already determined by the
minimal length fuel. -/
theorem Trans_eq_lengthAux (M : PS) (hR : RTPS M) :
    Trans M = TransAux (Lng M) M := by
  exact (TransAux_MarkAux_fuel_irrel_RTPS M hR
    (transFuel M) (Lng M) (transFuel_ge_length M) (le_refl _)).1

/-- The analogous minimal-fuel equation for every marked translation. -/
theorem Mark_eq_lengthAux (M : PS) (m : ℕ) (hR : RTPS M) :
    Mark M m = MarkAux (Lng M) M m := by
  exact (TransAux_MarkAux_fuel_irrel_RTPS M hR
    (transFuel M) (Lng M) (transFuel_ge_length M) (le_refl _)).2 m

private theorem Trans_Mark_mono_eq (M : PS) (hR : RTPS M)
    (hlen : 1 < Lng M) (hmono : monoT M = true) :
    (Trans M =
      let j₁ := lastIdx M
      let t₁ := Trans (Pred M)
      if t₁ == BZero then
        Dprin 0 (Dprin (entry M 1 j₁ : ℕ∞) BZero)
      else
        let j' := lastParent M
        let c₁ := Mark (Pred M) (Adm M j')
        let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
        replaceScb t₁ c₁ c₂) ∧
    ∀ m, Mark M m =
      let j₁ := lastIdx M
      let t₁ := Trans (Pred M)
      if t₁ == BZero then
        if m == 0 then Dprin 0 (Dprin (entry M 1 j₁ : ℕ∞) BZero)
        else Dprin (entry M 1 j₁ : ℕ∞) BZero
      else
        let j' := lastParent M
        let c₁ := Mark (Pred M) (Adm M j')
        let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
        if m < j₁ then
          let c₀ := Mark (Pred M) m
          match (scbContexts c₀ (flatBT c₁)).head? with
          | some (s, b) => unflatBT (s ++ flatBT c₂ ++ b)
          | none => Dprin (entry M 1 j₁ : ℕ∞) BZero
        else Dprin (entry M 1 j₁ : ℕ∞) BZero := by
  have hPR : RTPS (Pred M) := RTPS_Pred M hR
  cases hL : Lng M with
  | zero => omega
  | succ fuel =>
      have hPL : Lng (Pred M) = fuel := by
        rw [length_Pred M hlen]
        omega
      have hirr := TransAux_MarkAux_fuel_irrel_RTPS (Pred M) hPR
        fuel (transFuel (Pred M)) (by omega) (transFuel_ge_length (Pred M))
      have ht : TransAux fuel (Pred M) = Trans (Pred M) := by
        simpa [Trans] using hirr.1
      have hm : ∀ m, MarkAux fuel (Pred M) m = Mark (Pred M) m := by
        intro m
        simpa [Mark] using hirr.2 m
      have hred : reduced M = true := hR
      have hfuel0 : fuel ≠ 0 := by omega
      have hlast0 : Lng M - 1 ≠ 0 := by omega
      constructor
      · rw [Trans_eq_lengthAux M hR, hL]
        simp [TransAux, lastIdx, hred, hmono, hfuel0, ht, hm]
        rw [if_neg hlast0, ht]
      · intro m
        rw [Mark_eq_lengthAux M m hR, hL]
        simp [MarkAux, lastIdx, hred, hmono, hfuel0, ht, hm]
        rw [if_neg hlast0, ht]
        rfl

private theorem Trans_Mark_multi_eq (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true) :
    let A := M.take (Pcut M)
    let J := M.drop (Pcut M)
    (Trans M = if J == [(0, 0)] then
        addBT (Trans A) (Dprin 0 BZero)
      else addBT (Trans A) (Trans J)) ∧
    ∀ m, Mark M m = if J == [(0, 0)] then Dprin 0 BZero
      else Mark J (m - Pcut M) := by
  dsimp only
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
  have hcut := Pcut_props M hlen
  have hAR : RTPS (M.take (Pcut M)) :=
    trans_multi_prefix_RTPS M hR hmulti
  have hlast := trans_multi_last_component M hM hmulti
  let pJ := (P M).getD ((P M).length - 1) []
  have hpJeq : pJ = M.drop (Pcut M) := by simpa [pJ] using hlast.1
  have hPne : P M ≠ [] := P_nonempty M
  have hidx : (P M).length - 1 < (P M).length := by
    have := List.length_pos_of_ne_nil hPne
    omega
  have hpJR : RTPS pJ :=
    (RTPS_iff_P_components M hM).1 hR ((P M).length - 1) hidx
  have hJR : RTPS (M.drop (Pcut M)) := by simpa [hpJeq] using hpJR
  cases hL : Lng M with
  | zero => omega
  | succ fuel =>
      have hAL : Lng (M.take (Pcut M)) ≤ fuel := by
        simp only [List.length_take]
        omega
      have hdropLen₀ : Lng (M.drop (Pcut M)) = Lng M - Pcut M := by
        simp
      have hJL : Lng (M.drop (Pcut M)) ≤ fuel := by
        rw [hdropLen₀, hL]
        omega
      have hAirr := TransAux_MarkAux_fuel_irrel_RTPS
        (M.take (Pcut M)) hAR fuel (transFuel (M.take (Pcut M)))
        hAL (transFuel_ge_length (M.take (Pcut M)))
      have hJirr := TransAux_MarkAux_fuel_irrel_RTPS
        (M.drop (Pcut M)) hJR fuel (transFuel (M.drop (Pcut M)))
        hJL (transFuel_ge_length (M.drop (Pcut M)))
      have hAT : TransAux fuel (M.take (Pcut M)) =
          Trans (M.take (Pcut M)) := by simpa [Trans] using hAirr.1
      have hJT : TransAux fuel (M.drop (Pcut M)) =
          Trans (M.drop (Pcut M)) := by simpa [Trans] using hJirr.1
      have hJM : ∀ m, MarkAux fuel (M.drop (Pcut M)) m =
          Mark (M.drop (Pcut M)) m := by
        intro m
        simpa [Mark] using hJirr.2 m
      have hred : reduced M = true := hR
      have hnmono : monoT M = false := by
        have hh := hmulti
        simp [multiT] at hh
        exact hh.2
      have hj₀ :
          Lng M - 1 - Lng ((P M).getD ((P M).length - 1) []) + 1 =
            Pcut M := hlast.2
      have hseg := trans_multi_prefix_seg M hM hmulti
      have hseg' : seg M 0
          (Lng M - 1 - Lng ((P M).getD ((P M).length - 1) []) + 1 - 1) =
          M.take (Pcut M) := by
        simpa using hseg
      have hpJraw : (P M).getD ((P M).length - 1) [] =
          M.drop (Pcut M) := hlast.1
      simp only [List.getD_eq_getElem?_getD] at hpJraw hseg' hj₀
      rw [hpJraw] at hseg' hj₀
      have hsegFuel : seg M 0 (fuel - Lng (M.drop (Pcut M))) =
          M.take (Pcut M) := by
        simpa [hL] using hseg'
      have hjFuel : fuel - Lng (M.drop (Pcut M)) + 1 = Pcut M := by
        simpa [hL] using hj₀
      rw [hdropLen₀] at hsegFuel hjFuel
      have hfuel0 : fuel ≠ 0 := by omega
      constructor
      · rw [Trans_eq_lengthAux M hR, hL]
        simp only [TransAux, hred, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, lastIdx, hL, Nat.succ_sub_one, hnmono]
        simp [hfuel0, hpJraw, hsegFuel, hAT, hJT]
      · intro m
        rw [Mark_eq_lengthAux M m hR, hL]
        simp only [MarkAux, hred, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, lastIdx, hL, Nat.succ_sub_one, hnmono]
        simp [hfuel0, hpJraw, hjFuel, hJM]

/-- Public recursion equations for the multi branch of `Trans` and `Mark`. -/
theorem Trans_Mark_multi_equations (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true) :
    let A := M.take (Pcut M)
    let J := M.drop (Pcut M)
    (Trans M = if J == [(0, 0)] then
        addBT (Trans A) (Dprin 0 BZero)
      else addBT (Trans A) (Trans J)) ∧
    ∀ m, Mark M m = if J == [(0, 0)] then Dprin 0 BZero
      else Mark J (m - Pcut M) :=
  Trans_Mark_multi_eq M hR hmulti

private theorem trans_inv_mono_hard (M : PS) (hR : RTPS M)
    (hlen : 1 < Lng M) (hmono : monoT M = true)
    (ht₁ne : Trans (Pred M) ≠ BZero)
    (ht₁TB : Trans (Pred M) ∈ T_B)
    (IHmk : ∀ m, Marked (Pred M) m →
      Mark (Pred M) m ∈ T_B ∧
        (Trans (Pred M), Mark (Pred M) m) ∈ MarkedB) :
    Trans M ∈ T_B ∧ Trans M ≠ BZero ∧
      ∀ m, Marked M m →
        Mark M m ∈ T_B ∧ (Trans M, Mark M m) ∈ MarkedB := by
  have hM : TPS M := RTPS_TPS M hR
  let j₁ := lastIdx M
  let jp := lastParent M
  let t₁ := Trans (Pred M)
  let c₁ := Mark (Pred M) (Adm M jp)
  let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
  let db := Dprin (entry M 1 j₁ : ℕ∞) BZero
  have hj₁ : j₁ = Lng M - 1 := rfl
  have hjp : jp = parent M 0 (Lng M - 1) := rfl
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hc₁Marked : Marked (Pred M) (Adm M jp) := by
    simpa [jp] using marked_Pred_Adm_local M hM hlen hp
  have hc₁facts := IHmk (Adm M jp) hc₁Marked
  have hc₁TB : c₁ ∈ T_B := by simpa [c₁] using hc₁facts.1
  have ht₁c₁ : (t₁, c₁) ∈ MarkedB := by
    simpa [t₁, c₁] using hc₁facts.2
  have ht₁ne' : t₁ ≠ BZero := by simpa [t₁] using ht₁ne
  have ht₁TB' : t₁ ∈ T_B := by simpa [t₁] using ht₁TB
  have hc₁P : ∃ p, c₁ = .trm [p] :=
    marked_component_principal ht₁ne' ht₁c₁
  have hc₂facts := transC2Core_properties M c₁ hc₁TB hc₁P
  have hc₂TB : c₂ ∈ T_B := by simpa [c₂] using hc₂facts.1
  have hc₂P : ∃ p, c₂ = .trm [p] := by simpa [c₂] using hc₂facts.2
  have hdbTB : db ∈ T_B := by
    exact Dprin_mem_T_B (v := (entry M 1 j₁ : ℕ∞)) (by simp)
      BZero_mem_T_B
  have hdbP : ∃ p, db = .trm [p] := ⟨_, rfl⟩
  have hc₂db : (c₂, db) ∈ MarkedB := by
    simpa [c₂, db, j₁] using
      transC2Core_marked_fallback M c₁ hc₁TB hc₁P
  have heq := Trans_Mark_mono_eq M hR hlen hmono
  have hTrans : Trans M = replaceScb t₁ c₁ c₂ := by
    simpa [j₁, jp, t₁, c₁, c₂, ht₁ne'] using heq.1
  have hrepFacts := replaceScb_preserves_marked
    ht₁TB' hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
  have hrepNe := replaceScb_ne_zero
    ht₁TB' hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
  have hTransTB : Trans M ∈ T_B := by rw [hTrans]; exact hrepFacts.1
  have hTransNe : Trans M ≠ BZero := by rw [hTrans]; exact hrepNe
  have hTransDb : (Trans M, db) ∈ MarkedB := by
    rw [hTrans]
    exact markedB_compose hc₂P hrepFacts.2 hc₂db
  refine ⟨hTransTB, hTransNe, ?_⟩
  intro m hmM
  by_cases hmlt : m < j₁
  · let c₀ := Mark (Pred M) m
    have hmPred : Marked (Pred M) m := by
      apply marked_Pred_local M m hM hlen hmM
      simpa [j₁] using hmlt
    have hc₀facts := IHmk m hmPred
    have hc₀TB : c₀ ∈ T_B := by simpa [c₀] using hc₀facts.1
    have ht₁c₀ : (t₁, c₀) ∈ MarkedB := by
      simpa [t₁, c₀] using hc₀facts.2
    have hc₀P : ∃ p, c₀ = .trm [p] :=
      marked_component_principal ht₁ne' ht₁c₀
    cases hhead : (scbContexts c₀ (flatBT c₁)).head? with
    | none =>
        have hMark : Mark M m = db := by
          simpa [j₁, jp, t₁, c₁, c₂, c₀, db,
            ht₁ne', hmlt, hhead] using heq.2 m
        rw [hMark]
        exact ⟨hdbTB, hTransDb⟩
    | some sb =>
        rcases sb with ⟨sm, bm⟩
        have hc₁ptb := (principal_flat_properties hc₁TB hc₁P).1
        have hdec₀₁ : scb_decomp c₀ sm (flatBT c₁) bm :=
          scbContexts_head_decomp hc₁ptb hhead
        have hc₀c₁ : (c₀, c₁) ∈ MarkedB := ⟨sm, bm, hdec₀₁⟩
        have hMark : Mark M m = replaceScb c₀ c₁ c₂ := by
          simpa [j₁, jp, t₁, c₁, c₂, c₀, db,
            ht₁ne', hmlt, hhead, replaceScb] using heq.2 m
        have hmarkFacts := replaceScb_preserves_marked
          hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
        have hmarkP := replaceScb_principal
          hc₀TB hc₀P hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
        obtain ⟨s₀, b₀, hd₀⟩ := ht₁c₀
        obtain ⟨so, bo, hdo, hfo, _⟩ := replaceScb_spec
          ht₁TB' hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
        obtain ⟨si, bi, hdi, hfi, _⟩ := replaceScb_spec
          hc₀TB hc₁TB hc₁P hc₂TB hc₂P hc₀c₁
        have hdcomp : scb_decomp t₁ (s₀ ++ si) (flatBT c₁) (bi ++ b₀) :=
          scb_compose t₁ c₀ s₀ si (flatBT c₁) bi b₀
            hc₀P hd₀ hdi
        have hctx : so = s₀ ++ si ∧ bo = bi ++ b₀ :=
          scb_unique_decomp t₁ so (s₀ ++ si) (flatBT c₁)
            bo (bi ++ b₀) ht₁TB' hdo hdcomp
        have hflatCoh :
            flatBT (replaceScb t₁ c₁ c₂) =
              s₀ ++ flatBT (replaceScb c₀ c₁ c₂) ++ b₀ := by
          rw [hfo, hctx.1, hctx.2, hfi]
          simp [List.append_assoc]
        have hcoh :
            (replaceScb t₁ c₁ c₂,
              replaceScb c₀ c₁ c₂) ∈ MarkedB := by
          refine ⟨s₀, b₀, hflatCoh, ?_, hd₀.2.2⟩
          intro _
          exact (principal_flat_properties hmarkFacts.1 hmarkP).1
        rw [hMark]
        refine ⟨hmarkFacts.1, ?_⟩
        rw [hTrans]
        exact hcoh
  · have hMark : Mark M m = db := by
      simpa [j₁, jp, t₁, c₁, c₂, db,
        ht₁ne', hmlt] using heq.2 m
    rw [hMark]
    exact ⟨hdbTB, hTransDb⟩

private theorem trans_inv_multi (M : PS) (hR : RTPS M)
    (hmulti : multiT M = true)
    (hATB : Trans (M.take (Pcut M)) ∈ T_B)
    (hJTB : Trans (M.drop (Pcut M)) ∈ T_B)
    (hJnz : zeroT (M.drop (Pcut M)) = false →
      Trans (M.drop (Pcut M)) ≠ BZero)
    (IHJ : ∀ m, Marked (M.drop (Pcut M)) m →
      Mark (M.drop (Pcut M)) m ∈ T_B ∧
        (Trans (M.drop (Pcut M)),
          Mark (M.drop (Pcut M)) m) ∈ MarkedB) :
    Trans M ∈ T_B ∧ Trans M ≠ BZero ∧
      ∀ m, Marked M m →
        Mark M m ∈ T_B ∧ (Trans M, Mark M m) ∈ MarkedB := by
  have hM : TPS M := RTPS_TPS M hR
  let A := M.take (Pcut M)
  let J := M.drop (Pcut M)
  have heq := Trans_Mark_multi_eq M hR hmulti
  have hD₀TB : Dprin 0 BZero ∈ T_B :=
    Dprin_mem_T_B (v := 0) (by simp) BZero_mem_T_B
  have hD₀P : ∃ p, Dprin 0 BZero = .trm [p] := ⟨_, rfl⟩
  have hD₀self : (Dprin 0 BZero, Dprin 0 BZero) ∈ MarkedB :=
    markedB_self_principal hD₀TB hD₀P
  by_cases hJzero : J = [(0, 0)]
  · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
      simpa [A, J, hJzero] using heq.1
    have hMark : ∀ m, Mark M m = Dprin 0 BZero := by
      intro m
      simpa [J, hJzero] using heq.2 m
    have hTransTB : Trans M ∈ T_B := by
      rw [hTrans]
      exact addBT_mem_T_B (by simpa [A] using hATB) hD₀TB
    have hTransNe : Trans M ≠ BZero := by
      rw [hTrans]
      exact addBT_ne_zero_right _ _ (by simp [Dprin, BZero])
    have hmarked : (Trans M, Dprin 0 BZero) ∈ MarkedB := by
      rw [hTrans]
      exact markedB_addBT_right (by simp [Dprin, BZero]) hD₀self
    refine ⟨hTransTB, hTransNe, ?_⟩
    intro m _hm
    rw [hMark m]
    exact ⟨hD₀TB, hmarked⟩
  · have hJR : RTPS J := by
      have hlast := (trans_multi_last_component M hM hmulti).1
      have hPne : P M ≠ [] := P_nonempty M
      have hidx : (P M).length - 1 < (P M).length := by
        have := List.length_pos_of_ne_nil hPne
        omega
      have hpJR := (RTPS_iff_P_components M hM).1 hR
        ((P M).length - 1) hidx
      dsimp [J]
      rw [← hlast]
      exact hpJR
    have hJnotzeroT : zeroT J = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hz
      have hh := hz
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
      obtain ⟨v, hv⟩ :=
        (one_column J (RTPS_TPS J hJR)).1 ⟨hh.1, hJR⟩
      have hv₀ : v = 0 := by
        simpa [hv, entry] using hh.2
      exact hJzero (by simpa [hv₀] using hv)
    have hTJne : Trans J ≠ BZero := by
      exact hJnz (by simpa [J] using hJnotzeroT)
    have hTrans : Trans M = addBT (Trans A) (Trans J) := by
      simpa [A, J, hJzero] using heq.1
    have hMark : ∀ m, Mark M m = Mark J (m - Pcut M) := by
      intro m
      simpa [J, hJzero] using heq.2 m
    have hTransTB : Trans M ∈ T_B := by
      rw [hTrans]
      exact addBT_mem_T_B (by simpa [A] using hATB) (by simpa [J] using hJTB)
    have hTransNe : Trans M ≠ BZero := by
      rw [hTrans]
      exact addBT_ne_zero_right _ _ hTJne
    refine ⟨hTransTB, hTransNe, ?_⟩
    intro m hm
    have hmJ := (multi_Marked_last_component_local M m hM hmulti hm).2
    have hmk := IHJ (m - Pcut M) hmJ
    rw [hMark m]
    refine ⟨by simpa [J] using hmk.1, ?_⟩
    rw [hTrans]
    exact markedB_addBT_right hTJne (by simpa [J] using hmk.2)

/-- Corrected A15 value invariant on reduced pair sequences.  Besides the
`T_B` range statements it carries the nonzero fact needed by the right-summand
assembly in the multi branch. -/
theorem Trans_Mark_invariant (M : PS) (hR : RTPS M) :
    Trans M ∈ T_B ∧
      (zeroT M = false → Trans M ≠ BZero) ∧
      ∀ m, Marked M m →
        Mark M m ∈ T_B ∧ (Trans M, Mark M m) ∈ MarkedB := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      by_cases hOne : Lng M = 1
      · obtain ⟨v, hMv⟩ := (one_column M hM).1 ⟨hOne, hR⟩
        subst M
        have hR' : RTPS [(v, v)] := hR
        by_cases hv : v = 0
        · subst v
          have hred : reduced [(0, 0)] = true := hR'
          have hTrans : Trans [(0, 0)] = BZero := by
            rw [Trans_eq_lengthAux [(0, 0)] hR']
            simp [TransAux, lastIdx, entry, BZero, hred]
          have hMark : ∀ m, Mark [(0, 0)] m = BZero := by
            intro m
            rw [Mark_eq_lengthAux [(0, 0)] m hR']
            simp [MarkAux, lastIdx, entry, BZero, hred]
          have hzeroTB : BZero ∈ T_B := BZero_mem_T_B
          have hzeroMarked : (BZero, BZero) ∈ MarkedB := by
            refine ⟨[], [], ?_⟩
            simp [scb_decomp, BZero, flatBT]
          refine ⟨by simpa [hTrans] using hzeroTB, ?_, ?_⟩
          · intro hz
            simp [zeroT, entry] at hz
          · intro m _hm
            rw [hMark m, hTrans]
            exact ⟨hzeroTB, hzeroMarked⟩
        · have hred : reduced [(v, v)] = true := hR'
          have hTrans : Trans [(v, v)] = Dprin (v : ℕ∞) BZero := by
            rw [Trans_eq_lengthAux [(v, v)] hR']
            simp [TransAux, lastIdx, entry, hv, BZero, hred]
          have hMark : ∀ m, Mark [(v, v)] m = Dprin (v : ℕ∞) BZero := by
            intro m
            rw [Mark_eq_lengthAux [(v, v)] m hR']
            simp [MarkAux, lastIdx, entry, hv, BZero, hred]
          have hdTB : Dprin (v : ℕ∞) BZero ∈ T_B :=
            Dprin_mem_T_B (v := (v : ℕ∞)) (by simp) BZero_mem_T_B
          have hdP : ∃ p, Dprin (v : ℕ∞) BZero = .trm [p] := ⟨_, rfl⟩
          have hdMarked := markedB_self_principal hdTB hdP
          refine ⟨by simpa [hTrans] using hdTB, ?_, ?_⟩
          · intro _
            rw [hTrans]
            simp [Dprin, BZero]
          · intro m _hm
            rw [hMark m, hTrans]
            exact ⟨hdTB, hdMarked⟩
      · have hlen : 1 < Lng M := by omega
        have hzero : zeroT M = false := by
          simp [zeroT]
          omega
        by_cases hmono : monoT M = true
        · have hPR : RTPS (Pred M) := RTPS_Pred M hR
          have hPL : Lng (Pred M) < Lng M := by
            rw [length_Pred M hlen]
            omega
          have hIH := ih (Lng (Pred M)) (by omega) (Pred M) hPR rfl
          by_cases ht₁z : Trans (Pred M) = BZero
          · let j₁ := lastIdx M
            let db := Dprin (entry M 1 j₁ : ℕ∞) BZero
            let out := Dprin 0 db
            have heq := Trans_Mark_mono_eq M hR hlen hmono
            have hTrans : Trans M = out := by
              simpa [j₁, db, out, ht₁z] using heq.1
            have hMark : ∀ m, Mark M m = if m == 0 then out else db := by
              intro m
              simpa [j₁, db, out, ht₁z] using heq.2 m
            have hdbTB : db ∈ T_B := by
              exact Dprin_mem_T_B
                (v := (entry M 1 j₁ : ℕ∞)) (by simp) BZero_mem_T_B
            have hdbP : ∃ p, db = .trm [p] := ⟨_, rfl⟩
            have houtTB : out ∈ T_B :=
              Dprin_mem_T_B (v := 0) (by simp) hdbTB
            have houtP : ∃ p, out = .trm [p] := ⟨_, rfl⟩
            have houtSelf := markedB_self_principal houtTB houtP
            have hdbSelf := markedB_self_principal hdbTB hdbP
            have houtDb : (out, db) ∈ MarkedB :=
              markedB_Dprin_lift 0 hdbTB hdbP hdbSelf
            refine ⟨by rw [hTrans]; exact houtTB, ?_, ?_⟩
            · intro _
              rw [hTrans]
              simp [out, Dprin, BZero]
            · intro m _hm
              by_cases hm₀ : m = 0
              · rw [hMark m]
                simp [hm₀]
                exact ⟨houtTB, by simpa [hTrans] using houtSelf⟩
              · rw [hMark m]
                simp [hm₀]
                exact ⟨hdbTB, by simpa [hTrans] using houtDb⟩
          · have hhard := trans_inv_mono_hard M hR hlen hmono ht₁z
              hIH.1 hIH.2.2
            exact ⟨hhard.1, fun _ => hhard.2.1, hhard.2.2⟩
        · have hmulti : multiT M = true := by
            simp [multiT, hzero, hmono]
          have hcut := Pcut_props M hlen
          let A := M.take (Pcut M)
          let J := M.drop (Pcut M)
          have hAR : RTPS A := by
            simpa [A] using trans_multi_prefix_RTPS M hR hmulti
          have hAL : Lng A < Lng M := by
            simp [A, Nat.min_eq_left (by omega : Pcut M ≤ Lng M)]
            omega
          have hlast := (trans_multi_last_component M hM hmulti).1
          have hPne : P M ≠ [] := P_nonempty M
          have hidx : (P M).length - 1 < (P M).length := by
            have := List.length_pos_of_ne_nil hPne
            omega
          have hpJR := (RTPS_iff_P_components M hM).1 hR
            ((P M).length - 1) hidx
          have hJR : RTPS J := by
            dsimp [J]
            rw [← hlast]
            exact hpJR
          have hJL : Lng J < Lng M := by
            calc
              Lng J = Lng M - Pcut M := by simp [J]
              _ < Lng M := Nat.sub_lt hpos hcut.1
          have hIHA := ih (Lng A) (by omega) A hAR rfl
          have hIHJ := ih (Lng J) (by omega) J hJR rfl
          have hmultiInv := trans_inv_multi M hR hmulti
            (by simpa [A] using hIHA.1)
            (by simpa [J] using hIHJ.1)
            (by simpa [J] using hIHJ.2.1)
            (by simpa [J] using hIHJ.2.2)
          exact ⟨hmultiInv.1, fun _ => hmultiInv.2.1, hmultiInv.2.2⟩

/-- `Trans` maps reduced pair sequences into Buchholz terms. -/
theorem Trans_mem_T_B (M : PS) (hR : RTPS M) : Trans M ∈ T_B :=
  (Trans_Mark_invariant M hR).1

/-- A marked column of a reduced pair sequence translates to a Buchholz term. -/
theorem Mark_mem_T_B (M : PS) (m : ℕ) (hR : RTPS M) (hm : Marked M m) :
    Mark M m ∈ T_B :=
  (Trans_Mark_invariant M hR).2.2 m hm |>.1

/-- `Mark` selects an scb-marked principal subterm of `Trans`. -/
theorem Trans_Mark_mem_MarkedB (M : PS) (m : ℕ) (hR : RTPS M)
    (hm : Marked M m) : (Trans M, Mark M m) ∈ MarkedB :=
  (Trans_Mark_invariant M hR).2.2 m hm |>.2

private theorem transMark_fuel_after_red_ge (M : PS) (hM : TPS M) :
    Lng (Red M) ≤ transFuel M - 1 := by
  have hmul : Lng M + 1 ≤ 8 * (nu M + 1) * (Lng M + 1) :=
    Nat.le_mul_of_pos_left (Lng M + 1) (by positivity)
  rw [Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

private theorem transMark_fuel_after_red2_ge (M : PS) (hM : TPS M) :
    Lng (Red (Red M)) ≤ transFuel M - 2 := by
  have hRM : TPS (Red M) := Red_TPS M hM
  have hfactor : 2 ≤ 8 * (nu M + 1) := by
    calc
      2 ≤ 8 * 1 := by norm_num
      _ ≤ 8 * (nu M + 1) :=
        Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
  have hmul : Lng M + 2 ≤ 8 * (nu M + 1) * (Lng M + 1) := by
    calc
      Lng M + 2 ≤ 2 * (Lng M + 1) := by omega
      _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
        Nat.mul_le_mul_right (Lng M + 1) hfactor
  rw [Lng_Red_invariance (Red M) hRM, Lng_Red_invariance M hM]
  simp only [transFuel]
  omega

/-- Joint one-step value equation when the reduct has reached the reduced
kernel. -/
theorem Trans_Mark_Red_of_Red_reduced (M : PS) (hM : TPS M)
    (hRR : RTPS (Red M)) :
    Trans M = Trans (Red M) ∧ ∀ m, Mark M m = Mark (Red M) m := by
  by_cases hR : RTPS M
  · have hfix := RTPS_Red_eq M hR
    constructor
    · simp [hfix]
    · intro m
      simp [hfix]
  · have hred : reduced M = false := Bool.eq_false_of_not_eq_true hR
    have hirr := TransAux_MarkAux_fuel_irrel_RTPS (Red M) hRR
      (transFuel M - 1) (transFuel (Red M))
      (transMark_fuel_after_red_ge M hM)
      (transFuel_ge_length (Red M))
    constructor
    · calc
        Trans M = TransAux (transFuel M - 1) (Red M) := by
          rw [Trans, show transFuel M = (transFuel M - 1) + 1 by
            have : 0 < transFuel M := by simp [transFuel]
            omega]
          simp [TransAux, hred]
        _ = TransAux (transFuel (Red M)) (Red M) := hirr.1
        _ = Trans (Red M) := rfl
    · intro m
      calc
        Mark M m = MarkAux (transFuel M - 1) (Red M) m := by
          rw [Mark, show transFuel M = (transFuel M - 1) + 1 by
            have : 0 < transFuel M := by simp [transFuel]
            omega]
          simp [MarkAux, hred]
        _ = MarkAux (transFuel (Red M)) (Red M) m := hirr.2 m
        _ = Mark (Red M) m := rfl

/-- Corrected A15: the public fuel-bounded functions satisfy the simultaneous
non-reduced recursion equations on every pair sequence.  RED2 bounds the
same-length `Red` orbit by two steps, after which fuel irrelevance on the
reduced kernel supplies uniqueness of the values. -/
theorem Trans_Mark_welldefined (M : PS) (hM : TPS M) :
    Trans M = Trans (Red M) ∧ ∀ m, Mark M m = Mark (Red M) m := by
  have hRR2 := Red2 M hM
  by_cases hRR : RTPS (Red M)
  · exact Trans_Mark_Red_of_Red_reduced M hM hRR
  · have hRM : TPS (Red M) := Red_TPS M hM
    have hredR : reduced (Red M) = false :=
      Bool.eq_false_of_not_eq_true hRR
    have hredM : reduced M = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hR
      have hfix : Red M = M := RTPS_Red_eq M hR
      exact hRR (by simpa [hfix] using hR)
    have hfuel : 2 ≤ transFuel M := by
      have hfactor : 2 ≤ 8 * (nu M + 1) := by
        calc
          2 ≤ 8 * 1 := by norm_num
          _ ≤ 8 * (nu M + 1) :=
            Nat.mul_le_mul_left 8 (Nat.succ_le_succ (Nat.zero_le (nu M)))
      calc
        2 ≤ 2 * (Lng M + 1) := by omega
        _ ≤ (8 * (nu M + 1)) * (Lng M + 1) :=
          Nat.mul_le_mul_right (Lng M + 1) hfactor
        _ ≤ transFuel M := by simp [transFuel]
    have hirr := TransAux_MarkAux_fuel_irrel_RTPS (Red (Red M)) hRR2
      (transFuel M - 2) (transFuel (Red (Red M)))
      (transMark_fuel_after_red2_ge M hM)
      (transFuel_ge_length (Red (Red M)))
    have hstepR := Trans_Mark_Red_of_Red_reduced (Red M) hRM hRR2
    constructor
    · calc
        Trans M = TransAux (transFuel M - 2) (Red (Red M)) := by
          rw [Trans, show transFuel M = (transFuel M - 2) + 2 by omega]
          simp [TransAux, hredM, hredR]
        _ = TransAux (transFuel (Red (Red M))) (Red (Red M)) := hirr.1
        _ = Trans (Red (Red M)) := rfl
        _ = Trans (Red M) := hstepR.1.symm
    · intro m
      calc
        Mark M m = MarkAux (transFuel M - 2) (Red (Red M)) m := by
          rw [Mark, show transFuel M = (transFuel M - 2) + 2 by omega]
          simp [MarkAux, hredM, hredR]
        _ = MarkAux (transFuel (Red (Red M))) (Red (Red M)) m :=
          hirr.2 m
        _ = Mark (Red (Red M)) m := rfl
        _ = Mark (Red M) m := (hstepR.2 m).symm

#print axioms TransAux_MarkAux_fuel_irrel_RTPS
#print axioms Trans_eq_lengthAux
#print axioms Mark_eq_lengthAux

#print axioms trans_multi_prefix_RTPS
#print axioms trans_multi_last_component
#print axioms trans_multi_prefix_seg

#print axioms Trans_Mark_invariant
#print axioms Trans_mem_T_B
#print axioms Mark_mem_T_B
#print axioms Trans_Mark_mem_MarkedB
#print axioms Trans_Mark_Red_of_Red_reduced
#print axioms Trans_Mark_welldefined

end PSS
