import «8».«8.6-diagSeq-Trans-fseq»
import «7».«7.2-scb-fseq»

/-!
# §8.6 補題（順序数項の末尾単項の零化可能性）

- 原文: `tmp/content.md` article 5621
- 訂正 A23 後の Buchholz 基本列を使用する。旧 A25 は A23 の旧誤読に
  由来するため撤回済みであり、原文の一般 scb 定理をそのまま証明する。
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

@[simp] private theorem zero_addBT_tpa (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩
  rfl

@[simp] private theorem addBT_zero_tpa (t : BT) : addBT t BZero = t := by
  rcases t with ⟨ps⟩
  simp [addBT, BZero]

private theorem addBT_assoc_tpa (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp [addBT, List.append_assoc]

private theorem bOperCore_list_snoc_tpa (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      exact (zero_addBT_tpa _).symm
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih, ← addBT_assoc_tpa]
          rfl

private theorem operB_single_tpa (p : BP) (z : BT) :
    operB (.trm [p]) z = bOperCore (.princ p z) := by
  simp [operB, bOperCore]

private theorem operB_snoc_tpa (ps : List BP) (p : BP) (z : BT) :
    operB (.trm (ps ++ [p])) z =
      addBT (.trm ps) (operB (.trm [p]) z) := by
  rw [operB, bOperCore.eq_def]
  change bOperCore (.list (ps ++ [p]) z) =
    addBT (.trm ps) (operB (.trm [p]) z)
  rw [bOperCore_list_snoc_tpa, operB_single_tpa]

private theorem domTagList_snoc_tpa (ps : List BP) (p : BP) :
    domTagList (ps ++ [p]) = domTagBP p := by
  induction ps with
  | nil => simp [domTagList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [domTagList]
      | cons r rs => simpa [domTagList] using ih

private theorem domTag_snoc_tpa (ps : List BP) (p : BP) :
    domTag (.trm (ps ++ [p])) = domTagBP p := by
  simp [domTag, domTagList_snoc_tpa]

private def scbLastPre_tpa : List BP → List Sym
  | [] => []
  | p :: ps => .lp :: flatComponentRun (p :: ps)

private def scbLastPost_tpa : List BP → List Sym
  | [] => []
  | _ :: _ => [.rp]

private theorem dfree_BP_of_mem_tpa {p : BP} {ps : List BP}
    (hdf : dfree_BPList ps = true) (hp : p ∈ ps) :
    dfree_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp [dfree_BPList] at hdf
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hdf.1
      · exact ih hdf.2 hp

/-- A `below m` right-spine suffix can only keep the same tag or trigger the
unique transition to the natural-number domain when heads are prepended. -/
private theorem rnDom_drop_below_lift_tpa (R : List ℕ) (k m : ℕ)
    (h : rnDom (R.drop k) = .below m) :
    rnDom R = .below m ∨ rnDom R = .naturals := by
  induction k generalizing R with
  | zero =>
      simpa using Or.inl h
  | succ k ih =>
      cases R with
      | nil => simp [rnDom] at h
      | cons v vs =>
          have htail : rnDom vs = .below m ∨ rnDom vs = .naturals := by
            apply ih
            simpa using h
          rcases htail with hbelow | hnat
          · cases vs with
            | nil => simp [rnDom] at hbelow
            | cons w ws =>
                by_cases hv : v ≤ m
                · exact Or.inr (by simp [rnDom, hbelow, hv])
                · exact Or.inl (by simp [rnDom, hbelow, hv])
          · cases vs with
            | nil => simp [rnDom] at hnat
            | cons w ws => exact Or.inr (by simp [rnDom, hnat])

private theorem scb_occurrence_tag_below_lift_tpa
    {t : BT} {p : BP} {s b : List Sym} {m : ℕ}
    (ht : t ∈ T_B)
    (hocc : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hdfp : dfree_BP p = true)
    (htagp : domTag (.trm [p]) = .below m) :
    domTag t = .below m ∨ domTag t = .naturals := by
  obtain ⟨k, hk⟩ := scb_occurrence_rightNodes_suffix hocc hb
  have hdfpt : dfree_BT (.trm [p]) = true := by
    simpa [dfree_BT, dfree_BPList] using hdfp
  have hpdom := domTag_eq_rnDom (.trm [p]) hdfpt
  have hdrop : rnDom ((RightNodes t).drop k) = .below m := by
    rw [← hk, ← hpdom]
    exact htagp
  have hlift := rnDom_drop_below_lift_tpa (RightNodes t) k m hdrop
  have htdom := domTag_eq_rnDom t ht
  rcases hlift with hbelow | hnat
  · exact Or.inl (htdom.trans hbelow)
  · exact Or.inr (htdom.trans hnat)

private theorem scbOfFlat_tpa {t : BT} {p : BP} {s b : List Sym}
    (hflat : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp) (hdf : dfree_BP p = true) :
    scb_decomp t s (flatBP p) b := by
  refine ⟨hflat, ?_, hb⟩
  intro _
  exact ⟨p, hdf, rfl⟩

/-- If a `below m` principal occurrence lies on a natural-domain right spine,
the first transition above it feeds exactly `D_m 0` into that occurrence. -/
private theorem operB_scb_spine_transition_tpa
    {t : BT} {p p' : BP} {s b : List Sym} {m : ℕ}
    (ht : t ∈ T_B)
    (hocc : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hdfp : dfree_BP p = true)
    (htagp : domTag (.trm [p]) = .below m)
    (htagt : domTag t = .naturals)
    (hopm : operB (.trm [p])
      (Dprin (m : ℕ∞) BZero) = .trm [p']) :
    flatBT (operB t (numBT 0)) = s ++ flatBP p' ++ b := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s b with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length hocc
          have hpge := flatBP_length_ge_two p
          simp [flatBT] at hlen
          omega
      | cons y ys =>
          let full : List BP := y :: ys
          have hfull : full ≠ [] := by simp [full]
          let init := full.dropLast
          let q := full.getLast hfull
          have hsnoc : init ++ [q] = full :=
            List.dropLast_append_getLast hfull
          have hlist : init ++ [q] = y :: ys := by
            simpa [full] using hsnoc
          have hocc' : flatBT (.trm (init ++ [q])) =
              s ++ flatBP p ++ b := by
            rw [hsnoc]
            simpa [full] using hocc
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          have ht' : (.trm (init ++ [q]) : BT) ∈ T_B := by
            rw [hsnoc]
            simpa [full] using ht
          have htagt' : domTag (.trm (init ++ [q])) = .naturals := by
            rw [hsnoc]
            simpa [full] using htagt
          let pre : List Sym := scbLastPre_tpa init
          let post : List Sym := scbLastPost_tpa init
          have hshape : flatBT (.trm (init ++ [q])) =
              pre ++ flatBP q ++ post := by
            cases hi : init with
            | nil =>
                simp [pre, post, hi, scbLastPre_tpa, scbLastPost_tpa, flatBT]
            | cons r rs =>
                simpa [pre, post, hi, scbLastPre_tpa, scbLastPost_tpa]
                  using flatBT_multi_snoc r rs q
          have hpost : ∀ x ∈ post, x = .rp := by
            cases hi : init <;> simp [post, hi, scbLastPost_tpa]
          have hcut : pre.length ≤ s.length := by
            cases hi : init with
            | nil => simp [pre, hi, scbLastPre_tpa]
            | cons r rs =>
                have hc := scb_cut_reaches_last r rs q p s b
                  (by simpa [hi] using hocc') hb
                simp [pre, hi, scbLastPre_tpa]
                omega
          have hd := scb_last_dichotomy
            (pre := pre) (post := post) (q := q) (pp := p)
            (hshape.symm.trans hocc') hb hpost hcut
          rcases hd with hmax |
              ⟨w, a, s₂, b₂, hq, haocc, hb₂, _⟩
          · have hpq : p = q := flatBP_injective hmax.2.1
            have htagq : domTag (.trm [q]) = .naturals := by
              have := htagt'
              rw [domTag_snoc_tpa] at this
              simpa [domTag, domTagList] using this
            rw [← hpq, htagp] at htagq
            contradiction
          · have hlt : (flatBT a).length < n := by
              rw [← hn', hshape, hq]
              simp [flatBP]
              omega
            have hane : a ≠ BZero := by
              intro ha
              subst a
              have hlen := congrArg List.length haocc
              have hpge := flatBP_length_ge_two p
              simp [BZero, flatBT] at hlen
              omega
            have hdfq : dfree_BP q = true := by
              have hdfList : dfree_BPList (init ++ [q]) = true := ht'
              exact dfree_BP_of_mem_tpa hdfList (by simp)
            have hta : a ∈ T_B := by
              rw [hq] at hdfq
              have hparts : w ≠ ⊤ ∧ dfree_BT a = true := by
                simpa [dfree_BP] using hdfq
              exact hparts.2
            have htagq : domTagBP q = .naturals := by
              simpa [domTag_snoc_tpa] using htagt'
            have htagLift := scb_occurrence_tag_below_lift_tpa
              hta haocc hb₂ hdfp htagp
            let canS := pre ++ (.dsym w :: s₂)
            let canB := b₂ ++ post
            have hcanflat : flatBT (.trm (init ++ [q])) =
                canS ++ flatBP p ++ canB := by
              rw [hshape, hq]
              simp [flatBP, haocc, canS, canB, List.append_assoc]
            have hcan : scb_decomp (.trm (init ++ [q]))
                canS (flatBP p) canB := by
              apply scbOfFlat_tpa hcanflat
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hb₂ x hx
                · exact hpost x hx
              · exact hdfp
            have horig : scb_decomp (.trm (init ++ [q]))
                s (flatBP p) b := scbOfFlat_tpa hocc' hb hdfp
            have halign := scb_unique_decomp_unconditional
              (.trm (init ++ [q])) s canS (flatBP p) b canB horig hcan
            have finish (q' : BP)
                (hopq : operB (.trm [q]) (numBT 0) = .trm [q'])
                (hqflat : flatBP q' =
                  .dsym w :: (s₂ ++ flatBP p' ++ b₂)) :
                flatBT (operB (.trm (init ++ [q])) (numBT 0)) =
                  s ++ flatBP p' ++ b := by
              have hopen : operB (.trm (init ++ [q])) (numBT 0) =
                  .trm (init ++ [q']) := by
                rw [operB_snoc_tpa, hopq]
                rfl
              have hflatop :
                  flatBT (operB (.trm (init ++ [q])) (numBT 0)) =
                    canS ++ flatBP p' ++ canB := by
                rw [hopen]
                cases hi : init with
                | nil =>
                    simp only [List.nil_append]
                    change flatBP q' = _
                    rw [hqflat]
                    simp [pre, post, canS, canB, hi, scbLastPre_tpa,
                      scbLastPost_tpa, List.append_assoc]
                | cons r rs =>
                    rw [flatBT_multi_snoc]
                    simp [pre, post, canS, canB, hi, scbLastPre_tpa,
                      scbLastPost_tpa, hqflat, List.append_assoc]
              rw [halign.1, halign.2]
              exact hflatop
            rcases htagLift with hbelow | hnat
            · have haop := PSS.operB_scb_spine_below haocc hb₂ hdfp
                hbelow hopm
              have hle : w ≤ (m : ℕ∞) := by
                by_contra hnle
                rw [hq] at htagq
                simp [domTagBP, hane, hbelow, hnle] at htagq
              let q' : BP := .db w
                (operB a (Dprin (m : ℕ∞) BZero))
              have hopq : operB (.trm [q]) (numBT 0) = .trm [q'] := by
                rw [hq]
                have heval := PSS.operB_dprin_kind1
                  (body := a) (z := numBT 0) (u := w) (m := m)
                  hane hbelow hle
                simpa [q', numBT, numNat, xseq, bOperCore, BZero]
                  using heval
              have hqflat : flatBP q' =
                  .dsym w :: (s₂ ++ flatBP p' ++ b₂) := by
                simp [q', flatBP, haop]
              have hout := finish q' hopq hqflat
              simpa [hlist] using hout
            · have haop := ih (flatBT a).length hlt
                (t := a) (s := s₂) (b := b₂)
                hta haocc hb₂ hnat rfl
              let q' : BP := .db w (operB a (numBT 0))
              have hopq : operB (.trm [q]) (numBT 0) = .trm [q'] := by
                rw [hq]
                simp [operB, bOperCore, Dprin, hane, hnat, q']
              have hqflat : flatBP q' =
                  .dsym w :: (s₂ ++ flatBP p' ++ b₂) := by
                simp [q', flatBP, haop]
              have hout := finish q' hopq hqflat
              simpa [hlist] using hout

private theorem operB_Dv0_zero_tpa (v : ℕ) :
    operB (Dprin (v : ℕ∞) BZero) BZero = BZero := by
  by_cases hv : v = 0
  · subst v
    simp [operB, bOperCore, Dprin, BZero]
  · have hv0 : (v : ℕ∞) ≠ 0 := by simpa using hv
    simp [operB, bOperCore, Dprin, BZero, hv0, ENat.coe_ne_top]

private theorem operB_addBT_Dv0_zero_tpa (t' : BT) (v : ℕ) :
    operB (addBT t' (Dprin (v : ℕ∞) BZero)) BZero = t' := by
  rcases t' with ⟨ps⟩
  change operB (.trm (ps ++ [.db (v : ℕ∞) BZero])) BZero = .trm ps
  rw [operB_snoc_tpa]
  have hz : operB (.trm [.db (v : ℕ∞) BZero]) BZero = BZero := by
    simpa [Dprin] using operB_Dv0_zero_tpa v
  rw [hz]
  exact addBT_zero_tpa _

private theorem domTag_addBT_Dv0_tpa (t' : BT) (v : ℕ) (hv : 0 < v) :
    domTag (addBT t' (Dprin (v : ℕ∞) BZero)) = .below (v - 1) := by
  rcases t' with ⟨ps⟩
  change domTag (.trm (ps ++ [.db (v : ℕ∞) BZero])) = .below (v - 1)
  simp [domTag, domTagList_snoc_tpa, domTagBP, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

private theorem addBT_Dv0_ne_zero_tpa (t' : BT) (v : ℕ) :
    addBT t' (Dprin (v : ℕ∞) BZero) ≠ BZero := by
  rcases t' with ⟨ps⟩
  simp [addBT, Dprin, BZero]

/-- Direct one-step peel in the non-kind-1 branch.  This is one local case of
the article's general scb theorem. -/
theorem trailing_principal_peel (t' : BT) (u v : ℕ)
    (huv : v = 0 ∨ v ≤ u) :
    operB (Dprin (u : ℕ∞)
      (addBT t' (Dprin (v : ℕ∞) BZero))) (numBT 0) =
      Dprin (u : ℕ∞) t' := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  have hbodyne : body ≠ BZero := by
    simpa [body] using addBT_Dv0_ne_zero_tpa t' v
  have hinner : operB body BZero = t' := by
    simpa [body] using operB_addBT_Dv0_zero_tpa t' v
  have hbq : (body == BZero) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hbodyne (eq_of_beq h)
  change operB (Dprin (u : ℕ∞) body) BZero = Dprin (u : ℕ∞) t'
  by_cases hv : v = 0
  · subst v
    have htag : domTag body = .zeroOnly := by
      rcases t' with ⟨ps⟩
      simp [body, addBT, Dprin, BZero, domTag, domTagList_snoc_tpa,
        domTagBP]
    rw [operB]
    change bOperCore (.term (.trm [.db (u : ℕ∞) body]) BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    change bOperCore (.list [.db (u : ℕ∞) body] BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    change bOperCore (.princ (.db (u : ℕ∞) body) BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    unfold operB at hinner
    have hbq' : (body == BT.trm []) = false := by simpa [BZero] using hbq
    have hinner' : bOperCore (.term body (.trm [])) = t' := by
      simpa [BZero] using hinner
    simp [hbq', htag, hinner', multBT, numNat, Dprin, BZero]
    exact zero_addBT_tpa _
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    have hvu : v ≤ u := huv.resolve_left hv
    have htag : domTag body = .below (v - 1) := by
      simpa [body] using domTag_addBT_Dv0_tpa t' v hvpos
    have hnle : ¬(u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
      norm_cast
      omega
    have hnle' : ¬(u : ℕ∞) ≤ (v : ℕ∞) - 1 := by
      intro hle
      have hle' : u ≤ v - 1 := by exact_mod_cast hle
      omega
    rw [operB]
    change bOperCore (.term (.trm [.db (u : ℕ∞) body]) BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    change bOperCore (.list [.db (u : ℕ∞) body] BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    change bOperCore (.princ (.db (u : ℕ∞) body) BZero) =
      Dprin (u : ℕ∞) t'
    rw [bOperCore.eq_def]
    unfold operB at hinner
    simp [hbq, htag, hnle', hinner, Dprin]

private theorem operB_Dv0_id_tpa (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0, ENat.coe_ne_top]

private theorem operB_addBT_Dv0_id_tpa (t' z : BT) (v : ℕ)
    (hv : 0 < v) :
    operB (addBT t' (Dprin (v : ℕ∞) BZero)) z = addBT t' z := by
  rcases t' with ⟨ps⟩
  change operB (.trm (ps ++ [.db (v : ℕ∞) BZero])) z =
    addBT (.trm ps) z
  rw [operB_snoc_tpa]
  have hz : operB (.trm [.db (v : ℕ∞) BZero]) z = z := by
    simpa [Dprin] using operB_Dv0_id_tpa v z hv
  rw [hz]

private theorem domTag_Dv0_tpa (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

private theorem domTagBP_Du_trailing_kind1_tpa (t' : BT) (u v : ℕ)
    (hv : 0 < v) (huv : u < v) :
    domTagBP (.db (u : ℕ∞)
      (addBT t' (Dprin (v : ℕ∞) BZero))) = .naturals := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  have hbodyne : body ≠ BZero := by
    simpa [body] using addBT_Dv0_ne_zero_tpa t' v
  have htag : domTag body = .below (v - 1) := by
    simpa [body] using domTag_addBT_Dv0_tpa t' v hv
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  have hle' : (u : ℕ∞) ≤ (v : ℕ∞) - 1 := by
    rw [show (v : ℕ∞) - (1 : ℕ∞) = ((v - 1 : ℕ) : ℕ∞) by
      exact (ENat.coe_sub v 1).symm]
    exact hle
  simp [body, domTagBP, hbodyne, htag, hle']

private theorem domTagBP_Du_trailing_below_tpa (t' : BT) (u v : ℕ)
    (hv : 0 < v) (hvu : v ≤ u) :
    domTagBP (.db (u : ℕ∞)
      (addBT t' (Dprin (v : ℕ∞) BZero))) = .below (v - 1) := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  have hbodyne : body ≠ BZero := by
    simpa [body] using addBT_Dv0_ne_zero_tpa t' v
  have htag : domTag body = .below (v - 1) := by
    simpa [body] using domTag_addBT_Dv0_tpa t' v hv
  have hnle : ¬(u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  have hlt : (v : ℕ∞) - 1 < (u : ℕ∞) := by
    rw [show (v : ℕ∞) - (1 : ℕ∞) = ((v - 1 : ℕ) : ℕ∞) by
      exact (ENat.coe_sub v 1).symm]
    norm_cast
    omega
  simp [body, domTagBP, hbodyne, htag, hlt]

private theorem operB_Du_trailing_kind1_tpa (t' : BT) (u v : ℕ)
    (hv : 0 < v) (huv : u < v) :
    operB (Dprin (u : ℕ∞)
      (addBT t' (Dprin (v : ℕ∞) BZero))) (numBT 0) =
      Dprin (u : ℕ∞)
        (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero)) := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  have hbodyne : body ≠ BZero := by
    simpa [body] using addBT_Dv0_ne_zero_tpa t' v
  have htag : domTag body = .below (v - 1) := by
    simpa [body] using domTag_addBT_Dv0_tpa t' v hv
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  have hinner : operB body (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) =
      addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) := by
    simpa [body] using operB_addBT_Dv0_id_tpa t'
      (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) v hv
  have heval := PSS.operB_dprin_kind1
    (body := body) (z := numBT 0) (u := (u : ℕ∞)) (m := v - 1)
    hbodyne htag hle
  have heval' : operB (Dprin (u : ℕ∞) body) BZero =
      Dprin (u : ℕ∞)
        (operB body (Dprin ((v - 1 : ℕ) : ℕ∞) BZero)) := by
    simpa [numBT, numNat, xseq, bOperCore, BZero] using heval
  rw [hinner] at heval'
  simpa [body] using heval'

private theorem operB_Du_trailing_arg_tpa (t' : BT) (u v : ℕ)
    (hv : 0 < v) (hvu : v ≤ u) :
    operB (Dprin (u : ℕ∞)
      (addBT t' (Dprin (v : ℕ∞) BZero)))
        (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) =
      Dprin (u : ℕ∞)
        (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero)) := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  have hbodyne : body ≠ BZero := by
    simpa [body] using addBT_Dv0_ne_zero_tpa t' v
  have htag : domTag body = .below (v - 1) := by
    simpa [body] using domTag_addBT_Dv0_tpa t' v hv
  have hmw : ((v - 1 : ℕ) : ℕ∞) < (u : ℕ∞) := by
    norm_cast
    omega
  have hinner : operB body (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) =
      addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) := by
    simpa [body] using operB_addBT_Dv0_id_tpa t'
      (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) v hv
  have heval := PSS.operB_dprin_below
    (a := body) (z := Dprin ((v - 1 : ℕ) : ℕ∞) BZero)
    (w := (u : ℕ∞)) (m := v - 1) hbodyne htag hmw
  rw [hinner] at heval
  simpa [body] using heval

/-- One zero step either deletes the marked trailing principal or lowers its
index by one.  This is the exact induction step used in the paper. -/
private theorem trailing_principal_step_tpa
    {t t' : BT} {s b : List Sym} (u v : ℕ)
    (ht : t ∈ T_B) (ht' : t' ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t' (Dprin (v : ℕ∞) BZero)))) b) :
    scb_decomp (operB t (numBT 0)) s
        (flatBT (Dprin (u : ℕ∞) t')) b ∨
      (0 < v ∧ scb_decomp (operB t (numBT 0)) s
        (flatBT (Dprin (u : ℕ∞)
          (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero)))) b) := by
  let body := addBT t' (Dprin (v : ℕ∞) BZero)
  let p : BP := .db (u : ℕ∞) body
  let p₀ : BP := .db (u : ℕ∞) t'
  have hdvT : Dprin (v : ℕ∞) BZero ∈ T_B := by
    simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList,
      ENat.coe_ne_top]
  have hbodyT : body ∈ T_B := by
    simpa [body] using addBT_mem_T_B ht' hdvT
  have hdfp : dfree_BP p = true := by
    simp [p, dfree_BP, ENat.coe_ne_top, show dfree_BT body = true from hbodyT]
  have hdfp₀ : dfree_BP p₀ = true := by
    simp [p₀, dfree_BP, ENat.coe_ne_top, show dfree_BT t' = true from ht']
  have hocc : flatBT t = s ++ flatBP p ++ b := by
    simpa [p, body, Dprin, flatBT] using hd.1
  have hb := hd.2.2
  have mkLeft (hflat : flatBT (operB t (numBT 0)) =
      s ++ flatBP p₀ ++ b) :
      scb_decomp (operB t (numBT 0)) s
        (flatBT (Dprin (u : ℕ∞) t')) b := by
    have hout := scbOfFlat_tpa hflat hb hdfp₀
    simpa [p₀, Dprin, flatBT] using hout
  by_cases hv : v = 0
  · subst v
    left
    have htagbody : domTag body = .zeroOnly := by
      rcases t' with ⟨ps⟩
      simp [body, addBT, Dprin, BZero, domTag, domTagList_snoc_tpa,
        domTagBP]
    have hbodyne : body ≠ BZero := by
      simpa [body] using addBT_Dv0_ne_zero_tpa t' 0
    have htagp : domTagBP p = .naturals := by
      simp [p, domTagBP, hbodyne, htagbody]
    have hop : operB (.trm [p]) (numBT 0) = .trm [p₀] := by
      simpa [p, p₀, body, Dprin] using
        trailing_principal_peel t' u 0 (Or.inl rfl)
    exact mkLeft (PSS.operB_scb_spine hocc hb hdfp htagp hop).2
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    let ppred : BP := .db (u : ℕ∞)
      (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero))
    have hdvmT : Dprin ((v - 1 : ℕ) : ℕ∞) BZero ∈ T_B := by
      simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList,
        ENat.coe_ne_top]
    have hpredBodyT :
        addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) ∈ T_B :=
      addBT_mem_T_B ht' hdvmT
    have hdfpred : dfree_BP ppred = true := by
      change ((u : ℕ∞) != ⊤ &&
        dfree_BT (addBT t'
          (Dprin ((v - 1 : ℕ) : ℕ∞) BZero))) = true
      simp only [Bool.and_eq_true]
      exact ⟨by simp [ENat.coe_ne_top], hpredBodyT⟩
    have mkRight (hflat : flatBT (operB t (numBT 0)) =
        s ++ flatBP ppred ++ b) :
        scb_decomp (operB t (numBT 0)) s
          (flatBT (Dprin (u : ℕ∞)
            (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero)))) b := by
      have hout := scbOfFlat_tpa hflat hb hdfpred
      simpa [ppred, Dprin, flatBT] using hout
    by_cases huv : u < v
    · right
      refine ⟨hvpos, ?_⟩
      have htagp : domTagBP p = .naturals := by
        simpa [p, body] using
          domTagBP_Du_trailing_kind1_tpa t' u v hvpos huv
      have hop : operB (.trm [p]) (numBT 0) = .trm [ppred] := by
        simpa [p, ppred, body, Dprin] using
          operB_Du_trailing_kind1_tpa t' u v hvpos huv
      exact mkRight (PSS.operB_scb_spine hocc hb hdfp htagp hop).2
    · have hvu : v ≤ u := by omega
      have htagp : domTagBP p = .below (v - 1) := by
        simpa [p, body] using
          domTagBP_Du_trailing_below_tpa t' u v hvpos hvu
      have htagpt : domTag (.trm [p]) = .below (v - 1) := by
        simpa [domTag, domTagList] using htagp
      have hlift := scb_occurrence_tag_below_lift_tpa
        ht hocc hb hdfp htagpt
      rcases hlift with hbelow | hnat
      · left
        have hop : operB (.trm [p]) (numBT 0) = .trm [p₀] := by
          simpa [p, p₀, body, Dprin] using
            trailing_principal_peel t' u v (Or.inr hvu)
        exact mkLeft (PSS.operB_scb_spine_below hocc hb hdfp hbelow hop)
      · right
        refine ⟨hvpos, ?_⟩
        have hopm : operB (.trm [p])
            (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) = .trm [ppred] := by
          simpa [p, ppred, body, Dprin] using
            operB_Du_trailing_arg_tpa t' u v hvpos hvu
        exact mkRight (operB_scb_spine_transition_tpa
          ht hocc hb hdfp htagpt hnat hopm)

private theorem operB_Du_Dw0_kind1_tpa (u w : ℕ) (huw : u < w) :
    operB (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) (numBT 0) =
      Dprin (u : ℕ∞) (Dprin (w - 1 : ℕ) BZero) := by
  let body := Dprin (w : ℕ∞) BZero
  have hwpos : 0 < w := by omega
  have hbodyne : body ≠ BZero := by simp [body, Dprin, BZero]
  have hbq : (body == BZero) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hbodyne (eq_of_beq h)
  have htag : domTag body = .below (w - 1) := by
    simpa [body] using domTag_Dv0_tpa w hwpos
  have hle : (u : ℕ∞) ≤ ((w - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  have hx : bOperCore (.xseq body ((w - 1 : ℕ) : ℕ∞) 0) =
      Dprin ((w - 1 : ℕ) : ℕ∞) BZero := by
    simp [bOperCore]
  have hop : bOperCore (.term body (Dprin ((w - 1 : ℕ) : ℕ∞) BZero)) =
      Dprin ((w - 1 : ℕ) : ℕ∞) BZero := by
    change operB body (Dprin ((w - 1 : ℕ) : ℕ∞) BZero) = _
    simpa [body] using operB_Dv0_id_tpa w
      (Dprin ((w - 1 : ℕ) : ℕ∞) BZero) hwpos
  rw [operB]
  change bOperCore (.term (.trm [.db (u : ℕ∞) body]) BZero) = _
  rw [bOperCore.eq_def]
  change bOperCore (.list [.db (u : ℕ∞) body] BZero) = _
  rw [bOperCore.eq_def]
  change bOperCore (.princ (.db (u : ℕ∞) body) BZero) = _
  rw [bOperCore.eq_def]
  have htag' : domTag body = .below (w - 1) := htag
  simp only [htag']
  simp only [hle, decide_true, if_true]
  simp only [hbq, Bool.false_eq_true, if_false]
  change Dprin (u : ℕ∞)
      (bOperCore (.term body
        (bOperCore (.xseq body ((w - 1 : ℕ) : ℕ∞) 0)))) = _
  rw [hx, hop]

private theorem operB_Du_Dw0_floor_tpa (u w : ℕ) (hwu : w ≤ u) :
    operB (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) (numBT 0) =
      Dprin (u : ℕ∞) BZero := by
  have hclean : w = 0 ∨ w ≤ u := by
    by_cases hw : w = 0
    · exact Or.inl hw
    · exact Or.inr hwu
  have hp := trailing_principal_peel BZero u w hclean
  simpa using hp

/-- An isolated `D_u (D_w 0)` reaches `D_u 0` after between one and `w+1`
zero steps. -/
theorem trailing_principal_annihilable_zero_body (u w : ℕ) :
    ∃ k, 0 < k ∧ k ≤ w + 1 ∧
      ((fun a => operB a (numBT 0))^[k])
          (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) =
        Dprin (u : ℕ∞) BZero := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
      let f := fun a => operB a (numBT 0)
      by_cases hwu : w ≤ u
      · refine ⟨1, by omega, by omega, ?_⟩
        change f (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) =
          Dprin (u : ℕ∞) BZero
        simpa [f] using operB_Du_Dw0_floor_tpa u w hwu
      · have huw : u < w := by omega
        have hwpos : 0 < w := by omega
        obtain ⟨k, hkpos, hkle, hk⟩ := ih (w - 1) (by omega)
        refine ⟨k + 1, by omega, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        change (f^[k])
            (f (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero))) =
          Dprin (u : ℕ∞) BZero
        rw [show f (Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero)) =
            Dprin (u : ℕ∞) (Dprin (w - 1 : ℕ) BZero) by
          simpa [f] using operB_Du_Dw0_kind1_tpa u w huw]
        exact hk

/-- Article §8.6: a marked trailing `D_v 0` on an scb/right spine can be
annihilated by between one and `v+1` zero fundamental-sequence steps. -/
theorem trailing_principal_annihilable
    (t t' : BT) (s b : List Sym) (u v : ℕ)
    (ht : t ∈ T_B) (ht' : t' ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t' (Dprin (v : ℕ∞) BZero)))) b) :
    ∃ k, 0 < k ∧ k ≤ v + 1 ∧
      scb_decomp
        (((fun a => operB a (numBT 0))^[k]) t)
        s (flatBT (Dprin (u : ℕ∞) t')) b := by
  induction v using Nat.strong_induction_on generalizing t s b with
  | h v ih =>
      have hstep := trailing_principal_step_tpa u v ht ht' hd
      rcases hstep with hdone | ⟨hvpos, hpred⟩
      · refine ⟨1, by omega, by omega, ?_⟩
        simpa using hdone
      · let p : BP := .db (u : ℕ∞)
          (addBT t' (Dprin (v : ℕ∞) BZero))
        let ppred : BP := .db (u : ℕ∞)
          (addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero))
        have hdvmT : Dprin ((v - 1 : ℕ) : ℕ∞) BZero ∈ T_B := by
          simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList,
            ENat.coe_ne_top]
        have hpredBodyT :
            addBT t' (Dprin ((v - 1 : ℕ) : ℕ∞) BZero) ∈ T_B :=
          addBT_mem_T_B ht' hdvmT
        have hdfpred : dfree_BP ppred = true := by
          change ((u : ℕ∞) != ⊤ &&
            dfree_BT (addBT t'
              (Dprin ((v - 1 : ℕ) : ℕ∞) BZero))) = true
          simp only [Bool.and_eq_true]
          exact ⟨by simp [ENat.coe_ne_top], hpredBodyT⟩
        have hocc : flatBT t = s ++ flatBP p ++ b := by
          simpa [p, Dprin, flatBT] using hd.1
        obtain ⟨t₁, ht₁, ht₁flat⟩ :=
          principal_replacement_image ht hdfpred hocc
        have hopflat : flatBT (operB t (numBT 0)) =
            s ++ flatBP ppred ++ b := by
          simpa [ppred, Dprin, flatBT] using hpred.1
        have hopT : operB t (numBT 0) ∈ T_B := by
          have heq : operB t (numBT 0) = t₁ :=
            flatBT_injective (hopflat.trans ht₁flat.symm)
          simpa [heq] using ht₁
        obtain ⟨k, hkpos, hkle, hk⟩ := ih (v - 1) (by omega)
          (t := operB t (numBT 0)) (s := s) (b := b)
          hopT hpred
        refine ⟨k + 1, by omega, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hk

/- The example behind the withdrawn A25 follows the paper's second branch
under the corrected A23 rule, and reaches the deleted form on the next step. -/
#guard operB
    (Dprin (0 : ℕ∞)
      (addBT (Dprin (1 : ℕ∞) BZero) (Dprin (1 : ℕ∞) BZero)))
    (numBT 0) ==
  Dprin (0 : ℕ∞)
    (addBT (Dprin (1 : ℕ∞) BZero) (Dprin (0 : ℕ∞) BZero))

#guard operB
    (Dprin (0 : ℕ∞)
      (addBT (Dprin (1 : ℕ∞) BZero) (Dprin (0 : ℕ∞) BZero)))
    (numBT 0) ==
  Dprin (0 : ℕ∞) (Dprin (1 : ℕ∞) BZero)

#print axioms trailing_principal_peel
#print axioms trailing_principal_annihilable_zero_body
#print axioms trailing_principal_annihilable

end PSS
