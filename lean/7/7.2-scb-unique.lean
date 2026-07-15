import PSS.Flat

/-!
# §7.2 命題（scb 分解の一意性）

- Isabelle: `m_7_2_scb_unique_sb`, `m_7_2_scb_unique_decomp`
- 状態: 第 1 主張（固定した `c` に対する `(s,b)` の一意性）を証明済
-/

namespace PSS

/-! ## 右端 principal への降下で使う flatten 補題 -/

private theorem allRP_zero_not_mem {b : List Sym}
    (hb : ∀ x ∈ b, x = .rp) : .zero ∉ b := by
  intro hz
  have := hb .zero hz
  cases this

/-- 完全な項文字列と principal 文字列が右括弧尾部をまたいで重なることはない。 -/
private theorem scb_straddle_excluded {m : List Sym} {p : BP} {a : BT}
    {us : List Sym}
    (h : m ++ flatBP p = flatBT a ++ us)
    (hus : ∀ x ∈ us, x = .rp) :
    us = [] := by
  by_contra hne
  have hnozero : .zero ∉ us := allRP_zero_not_mem hus
  rcases List.append_eq_append_iff.mp h with
    ⟨mid, hterm, hrest⟩ | ⟨mid, hm, husplit⟩
  · have hmid : mid ≠ [] := by
      intro hz
      subst mid
      simp only [List.nil_append] at hrest
      have hzmem : .zero ∈ us := by
        rw [← hrest]
        exact flatBP_zero_mem p
      exact hnozero hzmem
    have hmnonneg : 0 ≤ flatSum m :=
      flatBT_properPrefix_nonneg hterm hmid
    have hw := congrArg flatSum h
    simp [flatBP_sum, flatBT_sum, flatSum_allRP hus] at hw
    have hlenNat : 0 < us.length := by
      cases us with
      | nil => exact (hne rfl).elim
      | cons x xs => simp
    have hlenInt : 0 < (us.length : ℤ) := by exact_mod_cast hlenNat
    omega
  · have hzmem : .zero ∈ us := by
      rw [husplit]
      exact List.mem_append.mpr (Or.inr (flatBP_zero_mem p))
    exact hnozero hzmem

/-- multi 項の、最後の principal より前にある完全成分とコンマの列。 -/
private def flatComponentRun : List BP → List Sym
  | [] => []
  | p :: ps => flatBP p ++ .cm :: flatComponentRun ps

/-- `flatComponentRun ms` の後ろにまだ文字があるなら、右括弧尾部を持つ
principal occurrence の開始位置はその成分列をすべて通過している。 -/
private theorem scb_peel_components {pp : BP} {b tail : List Sym}
    (ms : List BP) (s : List Sym)
    (h : s ++ flatBP pp ++ b = flatComponentRun ms ++ tail)
    (hb : ∀ x ∈ b, x = .rp) :
    (flatComponentRun ms).length ≤ s.length := by
  induction ms generalizing s with
  | nil => simp [flatComponentRun]
  | cons r ms ih =>
      have heq : s ++ (flatBP pp ++ b) =
          flatBP r ++ (.cm :: (flatComponentRun ms ++ tail)) := by
        simpa [flatComponentRun, List.append_assoc] using h
      rcases List.append_eq_append_iff.mp heq with
        ⟨mid, hr, hafter⟩ | ⟨mid, hs, hafter⟩
      · have hmid : mid ≠ [] := by
          intro hm
          subst mid
          simp only [List.nil_append] at hafter
          rcases pp with ⟨u, a⟩
          simp [flatBP] at hafter
        have hsnonneg : 0 ≤ flatSum s :=
          flatBP_properPrefix_nonneg hr hmid
        have hmweight := congrArg flatSum hr
        simp [flatBP_sum] at hmweight
        have hmneg : flatSum mid ≤ -1 := by omega
        rcases List.append_eq_append_iff.mp hafter with
          ⟨d, hmidEq, hbEq⟩ | ⟨d, hppEq, htailEq⟩
        · have hcm : .cm ∈ b := by
            rw [hbEq]
            simp
          have := hb .cm hcm
          cases this
        · have hd : d ≠ [] := by
            intro hd
            subst d
            simp only [List.nil_append] at htailEq
            have hcm : .cm ∈ b := by
              rw [← htailEq]
              simp
            have := hb .cm hcm
            cases this
          have hmnonneg : 0 ≤ flatSum mid :=
            flatBP_properPrefix_nonneg hppEq hd
          omega
      · have hmid : mid ≠ [] := by
          intro hm
          subst mid
          simp only [List.nil_append] at hafter
          rcases pp with ⟨u, a⟩
          simp [flatBP] at hafter
        cases mid with
        | nil => exact (hmid rfl).elim
        | cons x xs =>
            have hx : x = .cm := by
              simpa using (congrArg List.head? hafter).symm
            subst x
            have hrec : xs ++ flatBP pp ++ b = flatComponentRun ms ++ tail := by
              simpa [List.append_assoc] using hafter.symm
            have hle := ih xs hrec
            simp [flatComponentRun, hs, List.append_assoc]
            omega

private theorem flatBPTail_snoc (ps : List BP) (p : BP) :
    flatBPTail (ps ++ [p]) = .cm :: (flatComponentRun ps ++ flatBP p) := by
  induction ps with
  | nil => simp [flatBPTail, flatComponentRun]
  | cons q qs ih =>
      simp [flatBPTail, flatComponentRun, ih, List.append_assoc]

private theorem flatBT_multi_snoc (p : BP) (ps : List BP) (q : BP) :
    flatBT (.trm ((p :: ps) ++ [q])) =
      .lp :: (flatComponentRun (p :: ps) ++ flatBP q) ++ [.rp] := by
  cases ps with
  | nil => simp [flatBT, flatBPTail, flatComponentRun]
  | cons r rs =>
      change .lp :: (flatBP p ++ flatBPTail (r :: (rs ++ [q]))) ++ [.rp] = _
      rw [show r :: (rs ++ [q]) = (r :: rs) ++ [q] by rfl,
        flatBPTail_snoc]
      simp [flatComponentRun, List.append_assoc]

private theorem rightNodesList_snoc (ps : List BP) (p : BP) :
    rightNodesList (ps ++ [p]) = rightNodesBP p := by
  induction ps with
  | nil => simp [rightNodesList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [rightNodesList]
      | cons r rs => simpa [rightNodesList] using ih

private theorem flatBP_length_ge_two (p : BP) : 2 ≤ (flatBP p).length := by
  rcases p with ⟨u, a⟩
  have hne : flatBT a ≠ [] := by
    intro h
    have := flatBT_zero_mem a
    simp [h] at this
  cases hfa : flatBT a with
  | nil => exact (hne hfa).elim
  | cons x xs => simp [flatBP, hfa]

/-- multi 項では、右括弧尾部を持つ principal occurrence は最後の
top-level principal の開始位置より左には始まらない。 -/
private theorem scb_cut_reaches_last (p : BP) (ps : List BP) (q pp : BP)
    (s b : List Sym)
    (h : flatBT (.trm ((p :: ps) ++ [q])) = s ++ flatBP pp ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    1 + (flatComponentRun (p :: ps)).length ≤ s.length := by
  have hshape := flatBT_multi_snoc p ps q
  have hsne : s ≠ [] := by
    intro hs
    subst s
    rcases pp with ⟨u, a⟩
    have hh := congrArg List.head? (h.symm.trans hshape)
    simp [flatBP] at hh
  cases s with
  | nil => exact (hsne rfl).elim
  | cons x xs =>
      have hx : x = .lp := by
        have hh := congrArg List.head? (h.symm.trans hshape)
        simpa using hh
      subst x
      have hpeel : xs ++ flatBP pp ++ b =
          flatComponentRun (p :: ps) ++ (flatBP q ++ [.rp]) := by
        have he := h.symm.trans hshape
        simpa [List.append_assoc] using he
      have hle := scb_peel_components (p :: ps) xs hpeel hb
      simp
      omega

/-- 最後の top-level principal 以後にある occurrence は、その principal 全体か、
その引数内の occurrence のどちらかである。 -/
private theorem scb_last_dichotomy {pre post s b : List Sym} {q pp : BP}
    (h : pre ++ flatBP q ++ post = s ++ flatBP pp ++ b)
    (hb : ∀ x ∈ b, x = .rp) (hpost : ∀ x ∈ post, x = .rp)
    (hcut : pre.length ≤ s.length) :
    (s.length = pre.length ∧ flatBP pp = flatBP q ∧ b = post) ∨
      ∃ u a s₂ b₂, q = .db u a ∧
        flatBT a = s₂ ++ flatBP pp ++ b₂ ∧
        (∀ x ∈ b₂, x = .rp) ∧
        s.length = pre.length + 1 + s₂.length := by
  have heq : pre ++ (flatBP q ++ post) = s ++ (flatBP pp ++ b) := by
    simpa [List.append_assoc] using h
  rcases List.append_eq_append_iff.mp heq with
    ⟨mid, hs, hafter⟩ | ⟨mid, hpre, hafter⟩
  · cases mid with
    | nil =>
        simp only [List.append_nil, List.nil_append] at hs hafter
        subst s
        rcases flatBP_cancel hafter.symm with ⟨hpq, hbp⟩
        exact Or.inl ⟨rfl, hpq, hbp⟩
    | cons x xs =>
        rcases q with ⟨u, a⟩
        have hx : x = .dsym u := by
          simpa [flatBP] using (congrArg List.head? hafter).symm
        subst x
        have hinner : flatBT a ++ post = xs ++ flatBP pp ++ b := by
          simpa [flatBP, List.append_assoc] using hafter
        have hoverlap : (xs ++ flatBP pp) ++ b = flatBT a ++ post := by
          simpa [List.append_assoc] using hinner.symm
        rcases List.append_eq_append_iff.mp hoverlap with
          ⟨us, hterm, hbsplit⟩ | ⟨us, hmark, hpostsplit⟩
        · have hus : ∀ z ∈ us, z = .rp := by
            intro z hz
            exact hb z (by rw [hbsplit]; simp [hz])
          exact Or.inr ⟨u, a, xs, us, rfl, by
            simpa [List.append_assoc] using hterm, hus, by simp [hs]; omega⟩
        · have hus : ∀ z ∈ us, z = .rp := by
            intro z hz
            exact hpost z (by rw [hpostsplit]; simp [hz])
          have hunil : us = [] := scb_straddle_excluded hmark hus
          subst us
          simp only [List.append_nil, List.nil_append] at hmark hpostsplit
          exact Or.inr ⟨u, a, xs, [], rfl, by
            simpa [List.append_assoc] using hmark.symm, by simp, by simp [hs]; omega⟩
  · have hmidlen : mid.length = 0 := by
      have hpLen := congrArg List.length hpre
      simp at hpLen
      omega
    have hmid : mid = [] := by
      cases mid with
      | nil => rfl
      | cons x xs => simp at hmidlen
    subst mid
    simp only [List.append_nil, List.nil_append] at hpre hafter
    subst pre
    rcases flatBP_cancel hafter with ⟨hpq, hbp⟩
    exact Or.inl ⟨rfl, hpq, hbp⟩

/-- 右括弧尾部を持つ principal occurrence の `RightNodes` は、周囲の項の
`RightNodes` の suffix である。記事の kind-1 maximality の構文的核心。 -/
theorem scb_occurrence_rightNodes_suffix {t : BT} {pp : BP} {s b : List Sym}
    (hocc : flatBT t = s ++ flatBP pp ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ k, RightNodes (.trm [pp]) = (RightNodes t).drop k := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s pp b with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length hocc
          have hge := flatBP_length_ge_two pp
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
          have hocc' : flatBT (.trm (init ++ [q])) = s ++ flatBP pp ++ b := by
            rw [hsnoc]
            simpa [full] using hocc
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          cases hi : init with
          | nil =>
              have hlistSingle : [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccSingle : flatBT (.trm [q]) = s ++ flatBP pp ++ b := by
                simpa [hi] using hocc'
              have hnSingle : (flatBT (.trm [q])).length = n := by
                simpa [hi] using hn'
              have hd := scb_last_dichotomy
                (pre := []) (post := []) (q := q) (pp := pp)
                (h := by simpa [flatBT, List.append_assoc] using hoccSingle)
                hb (by simp) (by simp)
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                refine ⟨0, ?_⟩
                rw [← hlistSingle]
                simpa [RightNodes, rightNodesList, hpq]
              ·
                have hlt : (flatBT a).length < n := by
                  rw [← hnSingle, hq]
                  simp [flatBT, flatBP]
                obtain ⟨k, hk⟩ :=
                  ih (flatBT a).length hlt (t := a) (s := s₂)
                    (pp := pp) (b := b₂) haocc hb₂ rfl
                refine ⟨k.succ, ?_⟩
                rw [← hlistSingle, hq]
                simpa [RightNodes, rightNodesList, rightNodesBP] using hk
          | cons p ps =>
              have hlistMulti : (p :: ps) ++ [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccMulti : flatBT (.trm ((p :: ps) ++ [q])) =
                  s ++ flatBP pp ++ b := by
                simpa [hi] using hocc'
              have hnMulti : (flatBT (.trm ((p :: ps) ++ [q]))).length = n := by
                simpa [hi] using hn'
              have hshape := flatBT_multi_snoc p ps q
              have hsplit :
                  (.lp :: flatComponentRun (p :: ps)) ++ flatBP q ++ [.rp] =
                    s ++ flatBP pp ++ b := by
                simpa [List.append_assoc] using hshape.symm.trans hoccMulti
              have hcut := scb_cut_reaches_last p ps q pp s b hoccMulti hb
              have hcut' : (.lp :: flatComponentRun (p :: ps)).length ≤ s.length := by
                simp
                omega
              have hd := scb_last_dichotomy
                (pre := .lp :: flatComponentRun (p :: ps))
                (post := [.rp]) (q := q) (pp := pp)
                hsplit hb (by simp) hcut'
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                refine ⟨0, ?_⟩
                simp only [List.drop_zero]
                rw [← hlistMulti]
                change rightNodesBP pp = rightNodesList ((p :: ps) ++ [q])
                rw [rightNodesList_snoc, hpq]
              ·
                have hlt : (flatBT a).length < n := by
                  rw [← hnMulti, flatBT_multi_snoc, hq]
                  simp [flatBP]
                  omega
                obtain ⟨k, hk⟩ :=
                  ih (flatBT a).length hlt (t := a) (s := s₂)
                    (pp := pp) (b := b₂) haocc hb₂ rfl
                have hrn : RightNodes (.trm (y :: ys)) =
                    u.toNat :: RightNodes a := by
                  rw [← hlistMulti, RightNodes, rightNodesList_snoc, hq]
                  simp [rightNodesBP]
                refine ⟨k.succ, ?_⟩
                rw [hrn]
                simpa using hk

private theorem scb_cut_pin_at_last
    {n : ℕ} {pre post s₀ s₁ b₀ b₁ : List Sym} {q p₀ p₁ : BP}
    (h₀ : pre ++ flatBP q ++ post = s₀ ++ flatBP p₀ ++ b₀)
    (hb₀ : ∀ x ∈ b₀, x = .rp)
    (h₁ : pre ++ flatBP q ++ post = s₁ ++ flatBP p₁ ++ b₁)
    (hb₁ : ∀ x ∈ b₁, x = .rp)
    (hpost : ∀ x ∈ post, x = .rp)
    (hcut₀ : pre.length ≤ s₀.length) (hcut₁ : pre.length ≤ s₁.length)
    (hrn : (RightNodes (.trm [p₀])).length =
      (RightNodes (.trm [p₁])).length)
    (hsmaller : ∀ u a, q = .db u a → (flatBT a).length < n)
    (hrec : ∀ {a : BT} {r₀ r₁ : BP} {z₀ z₁ d₀ d₁ : List Sym},
      (flatBT a).length < n →
      flatBT a = z₀ ++ flatBP r₀ ++ d₀ → (∀ x ∈ d₀, x = .rp) →
      flatBT a = z₁ ++ flatBP r₁ ++ d₁ → (∀ x ∈ d₁, x = .rp) →
      (RightNodes (.trm [r₀])).length = (RightNodes (.trm [r₁])).length →
      z₀.length = z₁.length) :
    s₀.length = s₁.length := by
  have hd₀ := scb_last_dichotomy h₀ hb₀ hpost hcut₀
  have hd₁ := scb_last_dichotomy h₁ hb₁ hpost hcut₁
  rcases hd₀ with hm₀ | ⟨u₀, a₀, z₀, d₀, hq₀, ha₀, hd₀, hs₀⟩
  · rcases hd₁ with hm₁ | ⟨u₁, a₁, z₁, d₁, hq₁, ha₁, hd₁, hs₁⟩
    · exact hm₀.1.trans hm₁.1.symm
    · have hp₀q : p₀ = q := flatBP_injective hm₀.2.1
      have hlen₀ : (RightNodes (.trm [p₀])).length =
          1 + (RightNodes a₁).length := by
        rw [hp₀q, hq₁]
        simp [RightNodes, rightNodesList, rightNodesBP]
        omega
      obtain ⟨k, hk⟩ := scb_occurrence_rightNodes_suffix ha₁ hd₁
      have hle : (RightNodes (.trm [p₁])).length ≤ (RightNodes a₁).length := by
        rw [hk]
        simp
      omega
  · rcases hd₁ with hm₁ | ⟨u₁, a₁, z₁, d₁, hq₁, ha₁, hd₁, hs₁⟩
    · have hp₁q : p₁ = q := flatBP_injective hm₁.2.1
      have hlen₁ : (RightNodes (.trm [p₁])).length =
          1 + (RightNodes a₀).length := by
        rw [hp₁q, hq₀]
        simp [RightNodes, rightNodesList, rightNodesBP]
        omega
      obtain ⟨k, hk⟩ := scb_occurrence_rightNodes_suffix ha₀ hd₀
      have hle : (RightNodes (.trm [p₀])).length ≤ (RightNodes a₀).length := by
        rw [hk]
        simp
      omega
    · have hqa : BP.db u₀ a₀ = BP.db u₁ a₁ := hq₀.symm.trans hq₁
      have haeq : a₀ = a₁ := by injection hqa
      subst a₁
      have hz : z₀.length = z₁.length :=
        hrec (hsmaller u₀ a₀ hq₀) ha₀ hd₀ ha₁ hd₁ hrn
      omega

/-- 同じ項の二つの右端 occurrence で marked-principal の `RightNodes` 長が
等しければ、文字列内の開始位置も等しい。 -/
theorem scb_occurrence_rightNodes_length_pins_cut
    {t : BT} {p₀ p₁ : BP} {s₀ s₁ b₀ b₁ : List Sym}
    (h₀ : flatBT t = s₀ ++ flatBP p₀ ++ b₀)
    (hb₀ : ∀ x ∈ b₀, x = .rp)
    (h₁ : flatBT t = s₁ ++ flatBP p₁ ++ b₁)
    (hb₁ : ∀ x ∈ b₁, x = .rp)
    (hrn : (RightNodes (.trm [p₀])).length =
      (RightNodes (.trm [p₁])).length) :
    s₀.length = s₁.length := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s₀ s₁ p₀ p₁ b₀ b₁ with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length h₀
          have hge := flatBP_length_ge_two p₀
          simp [flatBT] at hlen
          omega
      | cons y ys =>
          let full : List BP := y :: ys
          have hfull : full ≠ [] := by simp [full]
          let init := full.dropLast
          let q := full.getLast hfull
          have hsnoc : init ++ [q] = full :=
            List.dropLast_append_getLast hfull
          have h₀' : flatBT (.trm (init ++ [q])) = s₀ ++ flatBP p₀ ++ b₀ := by
            rw [hsnoc]
            simpa [full] using h₀
          have h₁' : flatBT (.trm (init ++ [q])) = s₁ ++ flatBP p₁ ++ b₁ := by
            rw [hsnoc]
            simpa [full] using h₁
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          have hrec : ∀ {a : BT} {r₀ r₁ : BP} {z₀ z₁ d₀ d₁ : List Sym},
              (flatBT a).length < n →
              flatBT a = z₀ ++ flatBP r₀ ++ d₀ → (∀ x ∈ d₀, x = .rp) →
              flatBT a = z₁ ++ flatBP r₁ ++ d₁ → (∀ x ∈ d₁, x = .rp) →
              (RightNodes (.trm [r₀])).length =
                (RightNodes (.trm [r₁])).length →
              z₀.length = z₁.length := by
            intro a r₀ r₁ z₀ z₁ d₀ d₁ hlt ha₀ hd₀ ha₁ hd₁ hre
            exact ih (flatBT a).length hlt (t := a) (s₀ := z₀) (s₁ := z₁)
              (p₀ := r₀) (p₁ := r₁) (b₀ := d₀) (b₁ := d₁)
              ha₀ hd₀ ha₁ hd₁ hre rfl
          cases hi : init with
          | nil =>
              have h₀s : flatBT (.trm [q]) = s₀ ++ flatBP p₀ ++ b₀ := by
                simpa [hi] using h₀'
              have h₁s : flatBT (.trm [q]) = s₁ ++ flatBP p₁ ++ b₁ := by
                simpa [hi] using h₁'
              have hns : (flatBT (.trm [q])).length = n := by
                simpa [hi] using hn'
              have hsmall : ∀ u a, q = .db u a → (flatBT a).length < n := by
                intro u a hq
                rw [← hns, hq]
                simp [flatBT, flatBP]
              apply scb_cut_pin_at_last
                (n := n) (pre := []) (post := []) (q := q)
                (p₀ := p₀) (p₁ := p₁)
              · simpa [flatBT, List.append_assoc] using h₀s
              · exact hb₀
              · simpa [flatBT, List.append_assoc] using h₁s
              · exact hb₁
              · simp
              · simp
              · simp
              · exact hrn
              · exact hsmall
              · exact hrec
          | cons p ps =>
              have h₀m : flatBT (.trm ((p :: ps) ++ [q])) =
                  s₀ ++ flatBP p₀ ++ b₀ := by
                simpa [hi] using h₀'
              have h₁m : flatBT (.trm ((p :: ps) ++ [q])) =
                  s₁ ++ flatBP p₁ ++ b₁ := by
                simpa [hi] using h₁'
              have hnm : (flatBT (.trm ((p :: ps) ++ [q]))).length = n := by
                simpa [hi] using hn'
              have hshape := flatBT_multi_snoc p ps q
              have hs₀ :
                  (.lp :: flatComponentRun (p :: ps)) ++ flatBP q ++ [.rp] =
                    s₀ ++ flatBP p₀ ++ b₀ := by
                simpa [List.append_assoc] using hshape.symm.trans h₀m
              have hs₁ :
                  (.lp :: flatComponentRun (p :: ps)) ++ flatBP q ++ [.rp] =
                    s₁ ++ flatBP p₁ ++ b₁ := by
                simpa [List.append_assoc] using hshape.symm.trans h₁m
              have hc₀ := scb_cut_reaches_last p ps q p₀ s₀ b₀ h₀m hb₀
              have hc₁ := scb_cut_reaches_last p ps q p₁ s₁ b₁ h₁m hb₁
              have hc₀' : (.lp :: flatComponentRun (p :: ps)).length ≤ s₀.length := by
                simp
                omega
              have hc₁' : (.lp :: flatComponentRun (p :: ps)).length ≤ s₁.length := by
                simp
                omega
              have hsmall : ∀ u a, q = .db u a → (flatBT a).length < n := by
                intro u a hq
                rw [← hnm, flatBT_multi_snoc, hq]
                simp [flatBP]
                omega
              exact scb_cut_pin_at_last (n := n) hs₀ hb₀ hs₁ hb₁
                (by simp) hc₀' hc₁' hrn hsmall hrec

/-- 文字列末尾の連続した右括弧の個数。 -/
private def trailRP (xs : List Sym) : ℕ :=
  (xs.reverse.takeWhile (· = .rp)).length

private theorem takeWhile_append_of_all {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : p x := h x (by simp)
      have hxs : ∀ y ∈ xs, p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

private theorem takeWhile_append_of_exists_not {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∃ x ∈ xs, ¬p x) :
    (xs ++ ys).takeWhile p = xs.takeWhile p := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x
      · have hxs : ∃ y ∈ xs, ¬p y := by
          rcases h with ⟨y, hy, hny⟩
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact (hny hx).elim
          · exact ⟨y, hy, hny⟩
        simp [hx, ih hxs]
      · simp [hx]

private theorem trailRP_append (xs b : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    trailRP (xs ++ b) = b.length + trailRP xs := by
  have hrev : ∀ x ∈ b.reverse, x = .rp := by
    intro x hx
    exact hb x (List.mem_reverse.mp hx)
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_all (fun x : Sym => x = .rp) b.reverse xs.reverse hrev]
  simp

private theorem trailRP_prefix (s c : List Sym)
    (hc : ∃ x ∈ c, x ≠ .rp) :
    trailRP (s ++ c) = trailRP c := by
  have hrev : ∃ x ∈ c.reverse, x ≠ .rp := by
    rcases hc with ⟨x, hx, hne⟩
    exact ⟨x, List.mem_reverse.mpr hx, hne⟩
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_exists_not (fun x : Sym => x = .rp)
    c.reverse s.reverse hrev]

private theorem isPTB_str_has_nonRP {c : List Sym} (hc : isPTB_str c) :
    ∃ x ∈ c, x ≠ .rp := by
  rcases hc with ⟨⟨u, a⟩, _, rfl⟩
  exact ⟨.dsym u, by simp [flatBP]⟩

private theorem allRP_eq_of_length_eq {b₀ b₁ : List Sym}
    (h₀ : ∀ x ∈ b₀, x = .rp) (h₁ : ∀ x ∈ b₁, x = .rp)
    (hlen : b₀.length = b₁.length) : b₀ = b₁ := by
  induction b₀ generalizing b₁ with
  | nil =>
      cases b₁ with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases b₁ with
      | nil => simp at hlen
      | cons y ys =>
          have hx : x = .rp := h₀ x (by simp)
          have hy : y = .rp := h₁ y (by simp)
          have hxs : ∀ z ∈ xs, z = .rp := by
            intro z hz
            exact h₀ z (by simp [hz])
          have hys : ∀ z ∈ ys, z = .rp := by
            intro z hz
            exact h₁ z (by simp [hz])
          have hlens : xs.length = ys.length := Nat.succ.inj hlen
          simp [hx, hy, ih hxs hys hlens]

private theorem scb_unique_nonzero {t : BT} {s₀ s₁ c b₀ b₁ : List Sym}
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁)
    (ht : t ≠ BZero) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  rcases h₀ with ⟨e₀, hp₀, hrp₀⟩
  rcases h₁ with ⟨e₁, _, hrp₁⟩
  have hnon := isPTB_str_has_nonRP (hp₀ ht)
  have trail₀ : trailRP (flatBT t) = b₀.length + trailRP c := by
    rw [e₀]
    simpa only [List.append_assoc] using
      trailRP_append (s₀ ++ c) b₀ hrp₀ |>.trans
        (congrArg (b₀.length + ·) (trailRP_prefix s₀ c hnon))
  have trail₁ : trailRP (flatBT t) = b₁.length + trailRP c := by
    rw [e₁]
    simpa only [List.append_assoc] using
      trailRP_append (s₁ ++ c) b₁ hrp₁ |>.trans
        (congrArg (b₁.length + ·) (trailRP_prefix s₁ c hnon))
  have hlen : b₀.length = b₁.length := Nat.add_right_cancel (trail₀.symm.trans trail₁)
  have hb : b₀ = b₁ := allRP_eq_of_length_eq hrp₀ hrp₁ hlen
  have heq : s₀ ++ (c ++ b₀) = s₁ ++ (c ++ b₀) := by
    simpa [List.append_assoc, hb] using e₀.symm.trans e₁
  exact ⟨List.append_cancel_right heq, hb⟩

/-- 固定した中央文字列 `c` を持つ scb 分解では、前置部 `s` と右括弧尾部 `b` が一意。
原文の一意性命題の第 1 主張。 -/
theorem scb_unique_decomp (t : BT) (s₀ s₁ c b₀ b₁ : List Sym)
    (_htb : t ∈ T_B)
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  by_cases ht : t = BZero
  · subst t
    rcases h₀ with ⟨e₀, _, hrp₀⟩
    rcases h₁ with ⟨e₁, _, hrp₁⟩
    have emptyTail (s c b : List Sym)
        (e : flatBT BZero = s ++ c ++ b) (hrp : ∀ x ∈ b, x = .rp) : b = [] := by
      by_contra hb
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b hb
      have hxrp : x = .rp := hrp x hx
      have hxflat : x ∈ flatBT BZero := by
        rw [e]
        simp [hx]
      subst x
      simpa [BZero, flatBT] using hxflat
    have hb₀ := emptyTail s₀ c b₀ e₀ hrp₀
    have hb₁ := emptyTail s₁ c b₁ e₁ hrp₁
    subst b₀
    subst b₁
    simp only [List.append_nil] at e₀ e₁
    exact ⟨List.append_cancel_right (e₀.symm.trans e₁), rfl⟩
  · exact scb_unique_nonzero h₀ h₁ ht

private theorem scb_same_cut_unique {t : BT}
    {s₀ s₁ c₀ c₁ b₀ b₁ : List Sym}
    (ht : t ≠ BZero)
    (h₀ : scb_decomp t s₀ c₀ b₀) (h₁ : scb_decomp t s₁ c₁ b₁)
    (hlen : s₀.length = s₁.length) :
    (s₀, c₀, b₀) = (s₁, c₁, b₁) := by
  rcases h₀ with ⟨he₀, hp₀, hb₀⟩
  rcases h₁ with ⟨he₁, hp₁, hb₁⟩
  rcases hp₀ ht with ⟨p₀, _, hc₀⟩
  rcases hp₁ ht with ⟨p₁, _, hc₁⟩
  have he : s₀ ++ (c₀ ++ b₀) = s₁ ++ (c₁ ++ b₁) := by
    simpa [List.append_assoc] using he₀.symm.trans he₁
  have hparts : s₀ = s₁ ∧ c₀ ++ b₀ = c₁ ++ b₁ := by
    rcases List.append_eq_append_iff.mp he with
      ⟨mid, hs₁, htail⟩ | ⟨mid, hs₀, htail⟩
    · have hm : mid = [] := by
        have hl := congrArg List.length hs₁
        simp at hl
        have : mid.length = 0 := by omega
        cases mid <;> simp_all
      subst mid
      simp only [List.append_nil, List.nil_append] at hs₁ htail
      exact ⟨hs₁.symm, htail⟩
    · have hm : mid = [] := by
        have hl := congrArg List.length hs₀
        simp at hl
        have : mid.length = 0 := by omega
        cases mid <;> simp_all
      subst mid
      simp only [List.append_nil, List.nil_append] at hs₀ htail
      exact ⟨hs₀, htail.symm⟩
  have hflat : flatBP p₀ ++ b₀ = flatBP p₁ ++ b₁ := by
    simpa [hc₀, hc₁] using hparts.2
  rcases flatBP_cancel hflat with ⟨hpflat, hbeq⟩
  have hceq : c₀ = c₁ := hc₀.trans (hpflat.trans hc₁.symm)
  simp [hparts.1, hceq, hbeq]

/-- 訂正 A14 後の第 4 主張。非零項の第 0 種 scb 分解は一意。 -/
theorem scb_kind0_unique {t : BT} {s₀ s₁ c₀ c₁ b₀ b₁ : List Sym}
    (_htb : t ∈ T_B) (ht : t ≠ BZero)
    (h₀ : scb_kind0 t s₀ c₀ b₀) (h₁ : scb_kind0 t s₁ c₁ b₁) :
    (s₀, c₀, b₀) = (s₁, c₁, b₁) := by
  rcases h₀.1.2.1 ht with ⟨p₀, _, hc₀⟩
  rcases h₁.1.2.1 ht with ⟨p₁, _, hc₁⟩
  have hocc₀ : flatBT t = s₀ ++ flatBP p₀ ++ b₀ := by
    simpa [hc₀] using h₀.1.1
  have hocc₁ : flatBT t = s₁ ++ flatBP p₁ ++ b₁ := by
    simpa [hc₁] using h₁.1.1
  have hrn₀ := (h₀.2 p₀ hc₀).1
  have hrn₁ := (h₁.2 p₁ hc₁).1
  have hrn : (RightNodes (.trm [p₀])).length =
      (RightNodes (.trm [p₁])).length := hrn₀.trans hrn₁.symm
  have hcut := scb_occurrence_rightNodes_length_pins_cut
    hocc₀ h₀.1.2.2 hocc₁ h₁.1.2.2 hrn
  exact scb_same_cut_unique ht h₀.1 h₁.1 hcut

/-! ## 第 0 種・第 1 種の排他性 -/

/-- 反転した flatten 文字列から、末尾の右括弧列を飛ばして最深部の
`zero` 直前にある `D` の添字を読む。 -/
private def scanBottom : List Sym → Option ℕ
  | .rp :: xs => scanBottom xs
  | .zero :: .dsym u :: _ => some u.toNat
  | _ => none

private def bottomIndex (xs : List Sym) : Option ℕ :=
  scanBottom xs.reverse

private theorem scanBottom_append_of_some {xs : List Sym} {n : ℕ}
    (h : scanBottom xs = some n) (ys : List Sym) :
    scanBottom (xs ++ ys) = some n := by
  induction xs with
  | nil => simp [scanBottom] at h
  | cons x xs ih =>
      cases x with
      | lp => simp [scanBottom] at h
      | cm => simp [scanBottom] at h
      | rp =>
          simp only [scanBottom] at h ⊢
          exact ih h
      | zero =>
          cases xs with
          | nil => simp [scanBottom] at h
          | cons y xs =>
              cases y <;> simp_all [scanBottom]
      | dsym u => simp [scanBottom] at h

private theorem scanBottom_allRP_prefix (b xs : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    scanBottom (b ++ xs) = scanBottom xs := by
  induction b with
  | nil => rfl
  | cons x b ih =>
      have hx : x = .rp := hb x (by simp)
      have htail : ∀ y ∈ b, y = .rp := by
        intro y hy
        exact hb y (by simp [hy])
      subst x
      simpa [scanBottom] using ih htail

private theorem bottomIndex_append_allRP (xs b : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    bottomIndex (xs ++ b) = bottomIndex xs := by
  have hrev : ∀ x ∈ b.reverse, x = .rp := by
    intro x hx
    exact hb x (List.mem_reverse.mp hx)
  simpa [bottomIndex, List.reverse_append] using
    scanBottom_allRP_prefix b.reverse xs.reverse hrev

private theorem bottomIndex_prefix_of_some (pre xs : List Sym) {n : ℕ}
    (h : bottomIndex xs = some n) :
    bottomIndex (pre ++ xs) = some n := by
  unfold bottomIndex at h ⊢
  rw [List.reverse_append]
  exact scanBottom_append_of_some h pre.reverse

private theorem bottomIndex_prefix_of_ne_none (pre xs : List Sym)
    (h : bottomIndex xs ≠ none) :
    bottomIndex (pre ++ xs) = bottomIndex xs := by
  cases hx : bottomIndex xs with
  | none => exact (h hx).elim
  | some n => exact bottomIndex_prefix_of_some pre xs hx

private theorem rightNodesBP_ne_nil (p : BP) : rightNodesBP p ≠ [] := by
  cases p
  simp [rightNodesBP]

private theorem rightNodesList_ne_nil : ∀ ps : List BP,
    ps ≠ [] → rightNodesList ps ≠ []
  | [], h => (h rfl).elim
  | [p], _ => by simp [rightNodesList, rightNodesBP_ne_nil]
  | p :: q :: ps, _ => by
      simpa [rightNodesList] using
        rightNodesList_ne_nil (q :: ps) (by simp)

private theorem getLast?_ne_none_of_ne_nil {α : Type} {xs : List α}
    (h : xs ≠ []) : xs.getLast? ≠ none := by
  intro hn
  exact h (List.getLast?_eq_none_iff.mp hn)

private theorem getLast?_cons_of_ne_nil {α : Type} (x : α) {xs : List α}
    (h : xs ≠ []) : (x :: xs).getLast? = xs.getLast? := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons y ys => simp [List.getLast?_cons]

private def BPBottom (p : BP) : Prop :=
  bottomIndex (flatBP p) = (rightNodesBP p).getLast?

private def AllBPBottom : List BP → Prop
  | [] => True
  | p :: ps => BPBottom p ∧ AllBPBottom ps

private theorem flatBPTail_bottom (ps : List BP) (hps : AllBPBottom ps) :
    bottomIndex (flatBPTail ps) = (rightNodesList ps).getLast? := by
  induction ps with
  | nil => simp [flatBPTail, rightNodesList, bottomIndex, scanBottom]
  | cons p ps ih =>
      rcases hps with ⟨hp, hps⟩
      cases ps with
      | nil =>
          have hn : bottomIndex (flatBP p) ≠ none := by
            rw [hp]
            exact getLast?_ne_none_of_ne_nil (rightNodesBP_ne_nil p)
          simpa [flatBPTail, rightNodesList] using
            (bottomIndex_prefix_of_ne_none [.cm] (flatBP p) hn).trans hp
      | cons q qs =>
          have htail := ih hps
          have hrn : rightNodesList (q :: qs) ≠ [] :=
            rightNodesList_ne_nil (q :: qs) (by simp)
          have hn : bottomIndex (flatBPTail (q :: qs)) ≠ none := by
            rw [htail]
            exact getLast?_ne_none_of_ne_nil hrn
          simpa [flatBPTail, rightNodesList, List.append_assoc] using
            (bottomIndex_prefix_of_ne_none (.cm :: flatBP p)
              (flatBPTail (q :: qs)) hn).trans htail

private theorem flatBT_bottom (t : BT) :
    bottomIndex (flatBT t) = (RightNodes t).getLast? := by
  exact BT.rec
    (motive_1 := fun t => bottomIndex (flatBT t) = (RightNodes t).getLast?)
    (motive_2 := BPBottom)
    (motive_3 := AllBPBottom)
    (fun ps hps => by
      cases ps with
      | nil => simp [flatBT, RightNodes, rightNodesList, bottomIndex, scanBottom]
      | cons p ps =>
          rcases hps with ⟨hp, hps⟩
          cases ps with
          | nil => simpa [flatBT, RightNodes, rightNodesList] using hp
          | cons q qs =>
              have htail := flatBPTail_bottom (q :: qs) hps
              have hrn : rightNodesList (q :: qs) ≠ [] :=
                rightNodesList_ne_nil (q :: qs) (by simp)
              have hn : bottomIndex (flatBPTail (q :: qs)) ≠ none := by
                rw [htail]
                exact getLast?_ne_none_of_ne_nil hrn
              calc
                bottomIndex (flatBT (.trm (p :: q :: qs))) =
                    bottomIndex (((.lp :: flatBP p) ++ flatBPTail (q :: qs)) ++ [.rp]) := by
                      simp [flatBT, List.append_assoc]
                _ = bottomIndex ((.lp :: flatBP p) ++ flatBPTail (q :: qs)) :=
                      bottomIndex_append_allRP _ _ (by simp)
                _ = bottomIndex (flatBPTail (q :: qs)) :=
                      bottomIndex_prefix_of_ne_none _ _ hn
                _ = (rightNodesList (q :: qs)).getLast? := htail
                _ = (RightNodes (.trm (p :: q :: qs))).getLast? := by
                      simp [RightNodes, rightNodesList])
    (fun u a ih => by
      cases a with
      | trm ps =>
          cases ps with
          | nil =>
              simp [BPBottom, flatBP, flatBT, rightNodesBP, RightNodes,
                rightNodesList, bottomIndex, scanBottom]
          | cons p ps =>
              have hrn : RightNodes (.trm (p :: ps)) ≠ [] := by
                simpa [RightNodes] using
                  rightNodesList_ne_nil (p :: ps) (by simp)
              have hn : bottomIndex (flatBT (.trm (p :: ps))) ≠ none := by
                rw [ih]
                exact getLast?_ne_none_of_ne_nil hrn
              calc
                bottomIndex (flatBP (.db u (.trm (p :: ps)))) =
                    bottomIndex ([.dsym u] ++ flatBT (.trm (p :: ps))) := by
                      simp [flatBP]
                _ = bottomIndex (flatBT (.trm (p :: ps))) :=
                      bottomIndex_prefix_of_ne_none _ _ hn
                _ = (RightNodes (.trm (p :: ps))).getLast? := ih
                _ = (rightNodesBP (.db u (.trm (p :: ps)))).getLast? := by
                      simpa [rightNodesBP] using
                        (getLast?_cons_of_ne_nil u.toNat hrn).symm)
    trivial
    (fun _ _ hp hps => ⟨hp, hps⟩)
    t

private theorem flatBP_bottom (p : BP) :
    bottomIndex (flatBP p) = (rightNodesBP p).getLast? := by
  simpa [flatBT, RightNodes, rightNodesList] using
    flatBT_bottom (.trm [p])

/-- scb-shaped occurrence of a principal has the same deepest right-spine index
as the ambient term. -/
theorem scb_occurrence_bottom {t : BT} {p : BP} {s b : List Sym}
    (hflat : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    (RightNodes t).getLast? = (rightNodesBP p).getLast? := by
  have hp := flatBP_bottom p
  have hpn : bottomIndex (flatBP p) ≠ none := by
    rw [hp]
    exact getLast?_ne_none_of_ne_nil (rightNodesBP_ne_nil p)
  calc
    (RightNodes t).getLast? = bottomIndex (flatBT t) := (flatBT_bottom t).symm
    _ = bottomIndex ((s ++ flatBP p) ++ b) := by
      exact congrArg bottomIndex (by simpa [List.append_assoc] using hflat)
    _ = bottomIndex (s ++ flatBP p) := bottomIndex_append_allRP _ _ hb
    _ = bottomIndex (flatBP p) := bottomIndex_prefix_of_ne_none _ _ hpn
    _ = (rightNodesBP p).getLast? := hp

private theorem getLast?_eq_some_getD_last {α : Type} (xs : List α) (d : α)
    (hxs : xs ≠ []) :
    xs.getLast? = some (xs.getD (xs.length - 1) d) := by
  have hlt : xs.length - 1 < xs.length := by
    have : 0 < xs.length := by
      cases xs with
      | nil => exact (hxs rfl).elim
      | cons x xs => simp
    omega
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt]
  rfl

private theorem getD_drop (R : List ℕ) (k j d : ℕ) :
    (R.drop k).getD j d = R.getD (k + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_drop_last (R : List ℕ) (k d : ℕ)
    (hk : k < R.length) :
    (R.drop k).getD ((R.drop k).length - 1) d =
      R.getD (R.length - 1) d := by
  rw [getD_drop]
  congr 2
  simp only [List.length_drop]
  omega

/-- 同じリストの二つの suffix がとも第 1 種の形なら、開始位置は一致する。
記事の kind-1 maximality に対応する純リスト核。 -/
theorem scb_kind1_drop_index_pin (R : List ℕ) (k₀ k₁ : ℕ)
    (hk₀ : k₀ < R.length) (hk₁ : k₁ < R.length)
    (hlen₀ : 2 ≤ (R.drop k₀).length) (hlen₁ : 2 ≤ (R.drop k₁).length)
    (hhead₀ : (R.drop k₀).getD 0 0 <
      (R.drop k₀).getD ((R.drop k₀).length - 1) 0)
    (hinner₀ : ∀ j, 0 < j → j < (R.drop k₀).length - 1 →
      (R.drop k₀).getD ((R.drop k₀).length - 1) 0 ≤
        (R.drop k₀).getD j 0)
    (hhead₁ : (R.drop k₁).getD 0 0 <
      (R.drop k₁).getD ((R.drop k₁).length - 1) 0)
    (hinner₁ : ∀ j, 0 < j → j < (R.drop k₁).length - 1 →
      (R.drop k₁).getD ((R.drop k₁).length - 1) 0 ≤
        (R.drop k₁).getD j 0) :
    k₀ = k₁ := by
  let L := R.length - 1
  let U := R.getD L 0
  have hlast₀ : (R.drop k₀).getD ((R.drop k₀).length - 1) 0 = U := by
    simpa [L, U] using getD_drop_last R k₀ 0 hk₀
  have hlast₁ : (R.drop k₁).getD ((R.drop k₁).length - 1) 0 = U := by
    simpa [L, U] using getD_drop_last R k₁ 0 hk₁
  have hk₀L : k₀ < L := by
    simp [L, List.length_drop] at hlen₀ ⊢
    omega
  have hk₁L : k₁ < L := by
    simp [L, List.length_drop] at hlen₁ ⊢
    omega
  have hheadR₀ : R.getD k₀ 0 < U := by
    have h := hhead₀
    rw [hlast₀, getD_drop] at h
    simpa using h
  have hheadR₁ : R.getD k₁ 0 < U := by
    have h := hhead₁
    rw [hlast₁, getD_drop] at h
    simpa using h
  have hinterR₀ : ∀ i, k₀ < i → i < L → U ≤ R.getD i 0 := by
    intro i hi₀ hiL
    have hjpos : 0 < i - k₀ := by omega
    have hjlt : i - k₀ < (R.drop k₀).length - 1 := by
      simp [L, List.length_drop] at hiL ⊢
      omega
    have h := hinner₀ (i - k₀) hjpos hjlt
    rw [hlast₀, getD_drop] at h
    have : k₀ + (i - k₀) = i := by omega
    simpa [this] using h
  have hinterR₁ : ∀ i, k₁ < i → i < L → U ≤ R.getD i 0 := by
    intro i hi₁ hiL
    have hjpos : 0 < i - k₁ := by omega
    have hjlt : i - k₁ < (R.drop k₁).length - 1 := by
      simp [L, List.length_drop] at hiL ⊢
      omega
    have h := hinner₁ (i - k₁) hjpos hjlt
    rw [hlast₁, getD_drop] at h
    have : k₁ + (i - k₁) = i := by omega
    simpa [this] using h
  rcases lt_trichotomy k₀ k₁ with hlt | heq | hgt
  · exact (not_lt_of_ge (hinterR₀ k₁ hlt hk₁L) hheadR₁).elim
  · exact heq
  · exact (not_lt_of_ge (hinterR₁ k₀ hgt hk₀L) hheadR₀).elim

/-- 訂正 A14 後の第 5 主張。非零項の第 1 種 scb 分解は一意。 -/
theorem scb_kind1_unique {t : BT} {s₀ s₁ c₀ c₁ b₀ b₁ : List Sym}
    (_htb : t ∈ T_B) (ht : t ≠ BZero)
    (h₀ : scb_kind1 t s₀ c₀ b₀) (h₁ : scb_kind1 t s₁ c₁ b₁) :
    (s₀, c₀, b₀) = (s₁, c₁, b₁) := by
  rcases h₀.1.2.1 ht with ⟨p₀, _, hc₀⟩
  rcases h₁.1.2.1 ht with ⟨p₁, _, hc₁⟩
  have hocc₀ : flatBT t = s₀ ++ flatBP p₀ ++ b₀ := by
    simpa [hc₀] using h₀.1.1
  have hocc₁ : flatBT t = s₁ ++ flatBP p₁ ++ b₁ := by
    simpa [hc₁] using h₁.1.1
  obtain ⟨k₀, hk₀⟩ :=
    scb_occurrence_rightNodes_suffix hocc₀ h₀.1.2.2
  obtain ⟨k₁, hk₁⟩ :=
    scb_occurrence_rightNodes_suffix hocc₁ h₁.1.2.2
  let R := RightNodes t
  let r₀ := RightNodes (.trm [p₀])
  let r₁ := RightNodes (.trm [p₁])
  have hs₀ :
      1 ≤ r₀.length - 1 ∧
        r₀.getD 0 0 < r₀.getD (r₀.length - 1) 0 ∧
        ∀ j, 0 < j → j < r₀.length - 1 →
          r₀.getD (r₀.length - 1) 0 ≤ r₀.getD j 0 := by
    simpa [r₀] using h₀.2 p₀ hc₀
  have hs₁ :
      1 ≤ r₁.length - 1 ∧
        r₁.getD 0 0 < r₁.getD (r₁.length - 1) 0 ∧
        ∀ j, 0 < j → j < r₁.length - 1 →
          r₁.getD (r₁.length - 1) 0 ≤ r₁.getD j 0 := by
    simpa [r₁] using h₁.2 p₁ hc₁
  have hlen₀ : 2 ≤ r₀.length := by omega
  have hlen₁ : 2 ≤ r₁.length := by omega
  have hk₀' : r₀ = R.drop k₀ := by simpa [r₀, R] using hk₀
  have hk₁' : r₁ = R.drop k₁ := by simpa [r₁, R] using hk₁
  have hk₀lt : k₀ < R.length := by
    rw [hk₀'] at hlen₀
    simp only [List.length_drop] at hlen₀
    omega
  have hk₁lt : k₁ < R.length := by
    rw [hk₁'] at hlen₁
    simp only [List.length_drop] at hlen₁
    omega
  have hk : k₀ = k₁ := by
    apply scb_kind1_drop_index_pin R k₀ k₁ hk₀lt hk₁lt
    · simpa [← hk₀'] using hlen₀
    · simpa [← hk₁'] using hlen₁
    · simpa [← hk₀'] using hs₀.2.1
    · simpa [← hk₀'] using hs₀.2.2
    · simpa [← hk₁'] using hs₁.2.1
    · simpa [← hk₁'] using hs₁.2.2
  have hrn : (RightNodes (.trm [p₀])).length =
      (RightNodes (.trm [p₁])).length := by
    have : r₀ = r₁ := hk₀'.trans (by simpa [hk] using hk₁'.symm)
    simpa [r₀, r₁] using congrArg List.length this
  have hcut := scb_occurrence_rightNodes_length_pins_cut
    hocc₀ h₀.1.2.2 hocc₁ h₁.1.2.2 hrn
  exact scb_same_cut_unique ht h₀.1 h₁.1 hcut

/-- 訂正 A14 後の第 3 主張。非零項は第 0 種と第 1 種の両方には分解できない。 -/
theorem scb_kinds_exclusive {t : BT} (ht : t ≠ BZero) :
    ¬scb_kind0_able t ∨ ¬scb_kind1_able t := by
  by_contra hboth
  have hk0 : scb_kind0_able t := by tauto
  have hk1 : scb_kind1_able t := by tauto
  rcases hk0 with ⟨s₀, c₀, b₀, hkind0⟩
  rcases hk1 with ⟨s₁, c₁, b₁, hkind1⟩
  rcases hkind0.1.2.1 ht with ⟨p₀, _, hc₀⟩
  rcases hkind1.1.2.1 ht with ⟨p₁, _, hc₁⟩
  have hbottom : (rightNodesBP p₀).getLast? = (rightNodesBP p₁).getLast? := by
    have hf₀ : flatBT t = s₀ ++ flatBP p₀ ++ b₀ := by
      simpa [hc₀] using hkind0.1.1
    have hf₁ : flatBT t = s₁ ++ flatBP p₁ ++ b₁ := by
      simpa [hc₁] using hkind1.1.1
    rw [← scb_occurrence_bottom hf₀ hkind0.1.2.2,
      ← scb_occurrence_bottom hf₁ hkind1.1.2.2]
  have hzero := hkind0.2 p₀ hc₀
  have hlast0 : (rightNodesBP p₀).getLast? = some 0 := by
    let r := rightNodesBP p₀
    have hzero' : r.length = 2 ∧ r.getD 1 0 = 0 := by
      simpa [r, RightNodes, rightNodesList] using hzero
    have hrne : r ≠ [] := by
      intro hr
      simp [hr] at hzero'
    have hlast := getLast?_eq_some_getD_last r 0 hrne
    rw [hzero'.1] at hlast
    norm_num at hlast
    have hvalopt : r[1]?.getD 0 = 0 := by
      rw [← List.getD_eq_getElem?_getD]
      exact hzero'.2
    rw [hvalopt] at hlast
    simpa [r] using hlast
  have hone := hkind1.2 p₁ hc₁
  let r := rightNodesBP p₁
  let j := r.length - 1
  have hone' : 1 ≤ j ∧ r.getD 0 0 < r.getD j 0 ∧
      ∀ k, 0 < k → k < j → r.getD j 0 ≤ r.getD k 0 := by
    simpa [r, j, RightNodes, rightNodesList] using hone
  have hj : 1 ≤ j := hone'.1
  have hlt : r.getD 0 0 < r.getD j 0 := hone'.2.1
  have hrne : r ≠ [] := by
    intro hr
    simp [r, j, hr] at hj
  have hpos : 0 < r.getD j 0 := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hlast1 : r.getLast? = some (r.getD j 0) := by
    simpa [j] using getLast?_eq_some_getD_last r 0 hrne
  have hbottom' : (rightNodesBP p₀).getLast? = r.getLast? := by
    simpa [r] using hbottom
  have hs : some (0 : ℕ) = some (r.getD j 0) :=
    hlast0.symm.trans (hbottom'.trans hlast1)
  have hz : 0 = r.getD j 0 := Option.some.inj hs
  exact (Nat.ne_of_gt hpos) hz.symm

/-- A14 の零項反例。`c = []` は principal 文字列ではないが、零項ではその条件が
免除されるため、第 0 種・第 1 種の条件がともに空虚に成立する。 -/
theorem scb_kinds_exclusive_original_false :
    scb_kind0_able BZero ∧ scb_kind1_able BZero := by
  have hdecomp : scb_decomp BZero [.zero] [] [] := by
    simp [scb_decomp, BZero, flatBT]
  constructor
  · refine ⟨[.zero], [], [], hdecomp, ?_⟩
    intro p hp
    cases p with
    | db u a => simp [flatBP] at hp
  · refine ⟨[.zero], [], [], hdecomp, ?_⟩
    intro p hp
    cases p with
    | db u a => simp [flatBP] at hp

#print axioms scb_unique_decomp
#print axioms scb_occurrence_bottom
#print axioms scb_kind1_drop_index_pin
#print axioms scb_kind0_unique
#print axioms scb_kind1_unique
#print axioms scb_kinds_exclusive
#print axioms scb_kinds_exclusive_original_false

end PSS
