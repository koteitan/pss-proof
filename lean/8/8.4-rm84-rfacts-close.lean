import «8».«8.4-rm84-rfacts»
import «6».«6.6-reduced-iff-condAB»

/-!
# §8.4 補題 — 残差 `Rm84RFacts` の無条件討伐（`rm84Exists` フィールド陥落）

- 攻略対象: `«8».«8.4-rm84-rfacts»` の残差 `Rm84RFacts`（dich / `RTPS (s84rs_R M)` /
  `adm`・`Adm` の `j₀` 一致の 4 conjunct）。
- ブループリント: Isabelle `s84c2_R_facts`（`isabelle/layerB/pss_wip.thy` 54302–54594）。
  接頭辞一致機構（行0 関係は全域一致、行1 関係は下端未満で一致、右端に行1親が消える）。

## 本ファイルの寄与

汎用補題 `s84Rfacts_core_rc2 Q R`（Isabelle `s84c2_R_facts` の忠実 port）を
`Q = s84rs_Q M`, `R = s84rs_R M` に適用し、`rm84RFacts_holds` を無条件で得る。
合成 `rm84SurgeryFrame_of_rfacts_rf → rightmost84ReplaceExists_of_rfacts_rf` により
termination の存在部フィールド `rm84Exists` が陥落する。

- 状態: 🤖（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private suffix: `_rc2`。
-/

namespace PSS

/-! ## 0. リスト畳み込みの congruence -/

private theorem hall_congr_rc2 (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.all_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem hany_congr_rc2 (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem find_congr_rc2 (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.find? f = l.find? g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.find?_cons]
      rw [h a (by simp)]
      cases hga : g a with
      | true => rfl
      | false => exact ih (fun x hx => h x (by simp [hx]))

/-! ## 1. `R` の構造事実（Isabelle `s84c2_R_base`） -/

private theorem rBase_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) :
    Lng R = Lng Q ∧
    (∀ j, j < Lng Q → entry R 0 j = entry Q 0 j) ∧
    (∀ j, j < Lng Q - 1 → entry R 1 j = entry Q 1 j) ∧
    entry R 1 (Lng Q - 1) = entry Q 1 0 ∧
    Pred R = Pred Q := by
  have hQpos : 0 < Lng Q := by omega
  have hdl : (Q.dropLast).length = Lng Q - 1 := by simp
  have hLngR : Lng R = Lng Q := by
    rw [hR]; simp only [List.length_append, List.length_cons, List.length_nil, hdl]; omega
  have hlt : ∀ j, j < Lng Q - 1 → R[j]? = Q[j]? := by
    intro j hj; rw [hR, List.getElem?_append_left (by rw [hdl]; omega),
      List.dropLast_eq_take, List.getElem?_take_of_lt (by omega)]
  have hlast : R[Lng Q - 1]? = some (entry Q 0 (Lng Q - 1), entry Q 1 0) := by
    rw [hR, List.getElem?_append_right (by rw [hdl])]; simp [hdl]
  have he0R : ∀ j, j < Lng Q → entry R 0 j = entry Q 0 j := by
    intro j hj
    by_cases hjl : j < Lng Q - 1
    · unfold entry; rw [hlt j hjl]
    · have hje : j = Lng Q - 1 := by omega
      subst hje; simp [entry, hlast]
  have he1ltR : ∀ j, j < Lng Q - 1 → entry R 1 j = entry Q 1 j := by
    intro j hj; unfold entry; rw [hlt j hj]
  have he1lastR : entry R 1 (Lng Q - 1) = entry Q 1 0 := by simp [entry, hlast]
  have hPredR : Pred R = Pred Q := by
    have h1 : ¬ Lng R ≤ 1 := by rw [hLngR]; omega
    have h2 : ¬ Lng Q ≤ 1 := by omega
    simp only [Pred, h1, h2, if_false]; rw [hR]; simp [List.dropLast_append_of_ne_nil]
  exact ⟨hLngR, he0R, he1ltR, he1lastR, hPredR⟩

/-! ## 2. 行0 関係の全域一致（Isabelle `iff0`/`le0eq`/`hp0eq`/`par0eq`） -/

private theorem nextrel0_eq_rc2 (M N : PS) (hL : Lng M = Lng N)
    (he : ∀ j, j < Lng N → entry M 0 j = entry N 0 j)
    (j0 j1 : ℕ) (hj0 : j0 < Lng N) (hj1 : j1 < Lng N) :
    nextrel0 M j0 j1 = nextrel0 N j0 j1 := by
  unfold nextrel0
  have e0 := he j0 hj0
  have e1 := he j1 hj1
  have hallc : (List.range j1).all
        (fun j => !decide (j0 < j) || decide (entry M 0 j1 ≤ entry M 0 j))
      = (List.range j1).all
        (fun j => !decide (j0 < j) || decide (entry N 0 j1 ≤ entry N 0 j)) := by
    apply hall_congr_rc2
    intro x hx
    have hxj1 : x < j1 := List.mem_range.mp hx
    rw [e1, he x (hxj1.trans hj1)]
  rw [hallc, hL, e0, e1]

private theorem le0Aux_eq_rc2 (M N : PS)
    (hne : ∀ a b, a < Lng N → b < Lng N → nextrel0 M a b = nextrel0 N a b)
    (fuel j0 j1 : ℕ) (hj1 : j1 < Lng N) :
    le0Aux M fuel j0 j1 = le0Aux N fuel j0 j1 := by
  induction fuel generalizing j1 with
  | zero => rfl
  | succ f ih =>
      simp only [le0Aux]
      congr 1
      apply hany_congr_rc2
      intro j hj
      have hjj1 : j < j1 := List.mem_range.mp hj
      have hjL : j < Lng N := hjj1.trans hj1
      rw [hne j j1 hjL hj1, ih j hjL]

private theorem le0_eq_rc2 (M N : PS) (hL : Lng M = Lng N)
    (hne : ∀ a b, a < Lng N → b < Lng N → nextrel0 M a b = nextrel0 N a b)
    (j0 j1 : ℕ) (hj1 : j1 < Lng N) :
    le0 M j0 j1 = le0 N j0 j1 := by
  unfold le0
  rw [hL, le0Aux_eq_rc2 M N hne (Lng N) j0 j1 hj1]

private theorem parents0_eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q) :
    parents R 0 j1 = parents Q 0 j1 := by
  obtain ⟨hLngR, he0R, _, _, _⟩ := rBase_rc2 Q R hL3 hR
  unfold parents
  rw [hLngR]
  apply List.filter_congr
  intro p hp'
  have hpL : p < Lng Q := List.mem_range.mp hp'
  simp only [nextR]
  exact nextrel0_eq_rc2 R Q hLngR he0R p j1 hpL hj1

private theorem hp0eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q) :
    hasParent R 0 j1 = hasParent Q 0 j1 := by
  unfold hasParent
  rw [parents0_eq_rc2 Q R hL3 hR j1 hj1]

private theorem par0eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q) :
    parent R 0 j1 = parent Q 0 j1 := by
  unfold parent
  rw [parents0_eq_rc2 Q R hL3 hR j1 hj1]

private theorem nextR_parent_rc2 (M : PS) (i j1 : ℕ) (hp : hasParent M i j1 = true) :
    nextR M i (parent M i j1) j1 = true := by
  obtain ⟨p, hp1, huniq⟩ := (hasParent_iff_unique_fseq M i j1).mp hp
  have heq := parent_eq_of_unique_fseq M i j1 p hp1 (fun y hy => huniq y hy)
  rw [heq]; exact hp1

/-! ## 3. 行1 関係の接頭辞一致（Isabelle `iff1`、下端 `j₁ = Lng Q - 1` 未満） -/

private theorem iff1_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (a b : ℕ) (hbj : b < Lng Q - 1) :
    nextrel1 R a b = nextrel1 Q a b := by
  obtain ⟨hLngR, he0R, he1ltR, _, _⟩ := rBase_rc2 Q R hL3 hR
  have hne : ∀ x y, x < Lng Q → y < Lng Q → nextrel0 R x y = nextrel0 Q x y :=
    fun x y hx hy => nextrel0_eq_rc2 R Q hLngR he0R x y hx hy
  have hle0eq : ∀ x y, y < Lng Q → le0 R x y = le0 Q x y :=
    fun x y hy => le0_eq_rc2 R Q hLngR hne x y hy
  have hbQ : b < Lng Q := by omega
  have key : (nextrel1 R a b = true) ↔ (nextrel1 Q a b = true) := by
    constructor
    · intro h
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨_, _⟩, hab⟩, hent⟩, hle⟩, hvalley⟩ := h
      have haQ : a < Lng Q := by omega
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨haQ, hbQ⟩, hab⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [← he1ltR a (by omega), ← he1ltR b hbj]; exact hent
      · rw [← hle0eq a b hbQ]; exact hle
      · rw [List.all_eq_true]
        intro j hj
        have hjQ : j < Lng Q := List.mem_range.mp hj
        by_cases hjc : j < Lng Q - 1
        · have hvj := List.all_eq_true.mp hvalley j
            (List.mem_range.mpr (by rw [hLngR]; exact hjQ))
          rw [← hle0eq j b hbQ, ← he1ltR b hbj, ← he1ltR j hjc]
          exact hvj
        · have hfalse : le0 Q j b = false := by
            by_contra hcon
            rw [Bool.not_eq_false] at hcon
            simp only [le0, Bool.and_eq_true] at hcon
            have := le0Aux_index_fseq hcon.2
            omega
          simp [hfalse]
    · intro h
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨_, _⟩, hab⟩, hent⟩, hle⟩, hvalley⟩ := h
      have haR : a < Lng R := by rw [hLngR]; omega
      have hbR : b < Lng R := by rw [hLngR]; omega
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨haR, hbR⟩, hab⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [he1ltR a (by omega), he1ltR b hbj]; exact hent
      · rw [hle0eq a b hbQ]; exact hle
      · rw [List.all_eq_true]
        intro j hj
        have hjR : j < Lng R := List.mem_range.mp hj
        have hjQ : j < Lng Q := by rw [← hLngR]; exact hjR
        by_cases hjc : j < Lng Q - 1
        · have hvj := List.all_eq_true.mp hvalley j (List.mem_range.mpr hjQ)
          rw [hle0eq j b hbQ, he1ltR b hbj, he1ltR j hjc]
          exact hvj
        · have hfalse : le0 R j b = false := by
            by_contra hcon
            rw [Bool.not_eq_false] at hcon
            simp only [le0, Bool.and_eq_true] at hcon
            have := le0Aux_index_fseq hcon.2
            omega
          simp [hfalse]
  by_cases hRt : nextrel1 R a b = true
  · rw [hRt, key.mp hRt]
  · have hRf : nextrel1 R a b = false := by simpa using hRt
    have hQf : nextrel1 Q a b = false := by
      by_contra hc
      have : nextrel1 Q a b = true := by simpa using hc
      exact hRt (key.mpr this)
    rw [hRf, hQf]

private theorem parents1_eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q - 1) :
    parents R 1 j1 = parents Q 1 j1 := by
  obtain ⟨hLngR, _, _, _, _⟩ := rBase_rc2 Q R hL3 hR
  unfold parents
  rw [hLngR]
  apply List.filter_congr
  intro p hp'
  have e1 : nextR R 1 p j1 = nextrel1 R p j1 := by simp [nextR]
  have e2 : nextR Q 1 p j1 = nextrel1 Q p j1 := by simp [nextR]
  rw [e1, e2]
  exact iff1_rc2 Q R hL3 hR p j1 hj1

private theorem hp1eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q - 1) :
    hasParent R 1 j1 = hasParent Q 1 j1 := by
  unfold hasParent
  rw [parents1_eq_rc2 Q R hL3 hR j1 hj1]

private theorem par1eq_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j1 : ℕ) (hj1 : j1 < Lng Q - 1) :
    parent R 1 j1 = parent Q 1 j1 := by
  unfold parent
  rw [parents1_eq_rc2 Q R hL3 hR j1 hj1]

/-! ## 4. `Q` 側の順序事実（`par1` 由来）と右端の行1親消滅 -/

private theorem uq1_rc2 (Q : PS) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (j : ℕ) (hj : nextR Q 1 j (Lng Q - 1) = true) : j = 0 :=
  nextR1_unique_mr Q j 0 (Lng Q - 1) hj hpar1

private theorem e10lt_rc2 (Q : PS) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true) :
    entry Q 1 0 < entry Q 1 (Lng Q - 1) := by
  have hnr1 : nextrel1 Q 0 (Lng Q - 1) = true := by simpa [nextR] using hpar1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hnr1
  exact hnr1.1.1.2

private theorem clause0_rc2 (Q : PS) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (j : ℕ) (hj0 : 0 < j) (hle : le0 Q j (Lng Q - 1) = true) :
    entry Q 1 (Lng Q - 1) ≤ entry Q 1 j := by
  have hnr1 : nextrel1 Q 0 (Lng Q - 1) = true := by simpa [nextR] using hpar1
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hnr1
  obtain ⟨_, hvalley⟩ := hnr1
  have hjL : j < Lng Q := by
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hle; exact hle.1.1
  have hv := List.all_eq_true.mp hvalley j (List.mem_range.mpr hjL)
  have hd0 : decide (0 < j) = true := by simp [hj0]
  rw [hd0, hle] at hv
  simp only [Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hv
  exact hv

private theorem hp0Q_rc2 (Q : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) : hasParent Q 0 (Lng Q - 1) = true :=
  mono_hasParent_row0 Q (RTPS_TPS Q hQR) hmonoQ (Lng Q - 1) (by omega) (by omega)

private theorem j0lt_rc2 (Q : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) : parent Q 0 (Lng Q - 1) < Lng Q - 1 :=
  (nextR_implies_row0 Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1)
    (nextR_parent_rc2 Q 0 (Lng Q - 1) (hp0Q_rc2 Q hQR hmonoQ hL3))).1

private theorem nopar1R_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (j : ℕ) : nextrel1 R j (Lng Q - 1) = false := by
  obtain ⟨hLngR, he0R, he1ltR, he1lastR, _⟩ := rBase_rc2 Q R hL3 hR
  have hne : ∀ x y, x < Lng Q → y < Lng Q → nextrel0 R x y = nextrel0 Q x y :=
    fun x y hx hy => nextrel0_eq_rc2 R Q hLngR he0R x y hx hy
  have hle0eq : ∀ x y, y < Lng Q → le0 R x y = le0 Q x y :=
    fun x y hy => le0_eq_rc2 R Q hLngR hne x y hy
  have e10lt := e10lt_rc2 Q hpar1
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hcon
  obtain ⟨⟨⟨⟨⟨_, _⟩, hjlt⟩, hlt⟩, hle⟩, _⟩ := hcon
  have er : entry R 1 (Lng Q - 1) = entry Q 1 0 := he1lastR
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · subst hj0
    have h0 : entry R 1 0 = entry Q 1 0 := he1ltR 0 (by omega)
    rw [h0, er] at hlt; omega
  · have hleQ : le0 Q j (Lng Q - 1) = true := by
      rw [← hle0eq j (Lng Q - 1) (by omega)]; exact hle
    have gej : entry Q 1 (Lng Q - 1) ≤ entry Q 1 j := clause0_rc2 Q hpar1 j hj0 hleQ
    have ejr : entry R 1 j = entry Q 1 j := he1ltR j hjlt
    rw [ejr, er] at hlt
    omega

/-! ## 5. 二分律（Isabelle `dich`） -/

private theorem dich_rc2 (Q : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true) :
    entry Q 1 (Lng Q - 1) ≤ entry Q 1 (parent Q 0 (Lng Q - 1))
      ∨ parent Q 0 (Lng Q - 1) = 0 := by
  by_cases hlt : entry Q 1 (parent Q 0 (Lng Q - 1)) < entry Q 1 (Lng Q - 1)
  · right
    have hp0Q := hp0Q_rc2 Q hQR hmonoQ hL3
    have hpar0 : nextR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
      nextR_parent_rc2 Q 0 (Lng Q - 1) hp0Q
    have hj0lt : parent Q 0 (Lng Q - 1) < Lng Q - 1 :=
      (nextR_implies_row0 Q 0 _ (Lng Q - 1) hpar0).1
    have hle0j0 : le0 Q (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
      have := (nextR_implies_row0 Q 0 _ (Lng Q - 1) hpar0).2
      simpa [leR] using this
    have hbuild : nextrel1 Q (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hlt⟩, hle0j0⟩, ?_⟩
      rw [List.all_eq_true]
      intro j hj
      by_cases hc : (decide (parent Q 0 (Lng Q - 1) < j) && le0 Q j (Lng Q - 1)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hj0j, hlej⟩ := hc
        have hjpos : 0 < j := by omega
        have hgej := clause0_rc2 Q hpar1 j hjpos hlej
        have hd : decide (parent Q 0 (Lng Q - 1) < j) = true := by simp [hj0j]
        rw [hd, hlej]
        simp only [Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact hgej
      · rw [Bool.not_eq_true] at hc
        rw [hc]; simp
    have hnextR1 : nextR Q 1 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
      simpa [nextR] using hbuild
    exact uq1_rc2 Q hpar1 _ hnextR1
  · left; omega

/-! ## 6. 許容性一致（Isabelle `admeq`/`admltEq`/`Admeq`） -/

private theorem adm_agree_below_rc2 (Q R : PS) (hL3 : 3 ≤ Lng Q)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)])
    (x : ℕ) (hx1 : x + 1 < Lng Q - 1) : adm R x = adm Q x := by
  obtain ⟨hLngR, _, _, _, _⟩ := rBase_rc2 Q R hL3 hR
  have e1 : nextR R 1 (x - 1) x = nextR Q 1 (x - 1) x := by
    have er : nextR R 1 (x - 1) x = nextrel1 R (x - 1) x := by simp [nextR]
    have eq : nextR Q 1 (x - 1) x = nextrel1 Q (x - 1) x := by simp [nextR]
    rw [er, eq]; exact iff1_rc2 Q R hL3 hR (x - 1) x (by omega)
  have e2 : nextR R 1 x (x + 1) = nextR Q 1 x (x + 1) := by
    have er : nextR R 1 x (x + 1) = nextrel1 R x (x + 1) := by simp [nextR]
    have eq : nextR Q 1 x (x + 1) = nextrel1 Q x (x + 1) := by simp [nextR]
    rw [er, eq]; exact iff1_rc2 Q R hL3 hR x (x + 1) hx1
  unfold adm nadm
  rw [hLngR, e1, e2]

private theorem admeq_rc2 (Q R : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) :
    adm R (parent Q 0 (Lng Q - 1)) = adm Q (parent Q 0 (Lng Q - 1)) := by
  set j0 := parent Q 0 (Lng Q - 1) with hj0
  have hj0lt : j0 < Lng Q - 1 := j0lt_rc2 Q hQR hmonoQ hL3
  by_cases hcase : j0 + 1 < Lng Q - 1
  · exact adm_agree_below_rc2 Q R hL3 hR j0 hcase
  · have hje : j0 + 1 = Lng Q - 1 := by omega
    have hj0pos : 0 < j0 := by omega
    obtain ⟨hLngR, _, _, _, _⟩ := rBase_rc2 Q R hL3 hR
    have hRnadm : nadm R j0 = false := by
      unfold nadm
      have hedge : nextR R 1 j0 (j0 + 1) = false := by
        have hh : nextR R 1 j0 (j0 + 1) = nextrel1 R j0 (j0 + 1) := by simp [nextR]
        rw [hh, hje]; exact nopar1R_rc2 Q R hL3 hpar1 hR j0
      have hLR : decide (Lng R < j0) = false := by
        rw [hLngR]; have : ¬ (Lng Q < j0) := by omega
        simp [this]
      rw [hLR, hedge]; simp
    have hQnadm : nadm Q j0 = false := by
      unfold nadm
      have hedge : nextR Q 1 j0 (j0 + 1) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hh : nextR Q 1 j0 (Lng Q - 1) = true := by rw [← hje]; exact hc
        have := uq1_rc2 Q hpar1 j0 hh
        omega
      have hLQ : decide (Lng Q < j0) = false := by
        have : ¬ (Lng Q < j0) := by omega
        simp [this]
      rw [hLQ, hedge]; simp
    unfold adm
    rw [hRnadm, hQnadm]

private theorem Admeq_rc2 (Q R : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) :
    Adm R (parent Q 0 (Lng Q - 1)) = Adm Q (parent Q 0 (Lng Q - 1)) := by
  set j0 := parent Q 0 (Lng Q - 1) with hj0
  have hj0lt : j0 < Lng Q - 1 := j0lt_rc2 Q hQR hmonoQ hL3
  have hadmeq : adm R j0 = adm Q j0 := admeq_rc2 Q R hQR hmonoQ hL3 hpar1 hR
  have hfind : (List.range j0).reverse.find? (fun j' => adm R j')
      = (List.range j0).reverse.find? (fun j' => adm Q j') := by
    apply find_congr_rc2
    intro x hx
    have hxlt : x < j0 := by rw [List.mem_reverse, List.mem_range] at hx; exact hx
    exact adm_agree_below_rc2 Q R hL3 hR x (by omega)
  unfold Adm
  rw [hadmeq, hfind]

/-! ## 7. `R` の RedCond(A)(B) → `RTPS R`（Isabelle `condA_R`/`condB_R`/`RRT`） -/

private theorem condA_R_rc2 (Q R : PS) (hQR : RTPS Q) (_hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) : RedCondA R = true := by
  obtain ⟨hLngR, he0R, he1ltR, _, _⟩ := rBase_rc2 Q R hL3 hR
  obtain ⟨hCA_Q, _⟩ := RTPS_condAB Q hQR
  rw [RedCondA]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  have hjQ : j < Lng Q := by rw [← hLngR]; exact hj
  cases hpRb : hasParent R i j with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
    interval_cases i
    · have hpQ : hasParent Q 0 j = true := by
        rw [← hp0eq_rc2 Q R hL3 hR j hjQ]; exact hpRb
      have eQ : entry Q 0 (parent Q 0 j) + 1 = entry Q 0 j :=
        RedCondA_apply Q hCA_Q 0 j (by omega) hjQ hpQ
      have hpar0lt : parent Q 0 j < j :=
        (nextR_implies_row0 Q 0 _ _ (nextR_parent_rc2 Q 0 j hpQ)).1
      have hpe : parent R 0 j = parent Q 0 j := par0eq_rc2 Q R hL3 hR j hjQ
      rw [hpe, he0R (parent Q 0 j) (by omega), he0R j hjQ]
      exact eQ
    · obtain ⟨p, hpfs, _⟩ := (hasParent_iff_unique_fseq R 1 j).mp hpRb
      have hpnr : nextrel1 R p j = true := by simpa [nextR] using hpfs
      have hjLR : j < Lng R := by
        obtain ⟨⟨⟨⟨⟨_, hb⟩, _⟩, _⟩, _⟩, _⟩ := by
          simpa only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] using hpnr
        exact hb
      have hjne : j ≠ Lng Q - 1 := by
        intro hje
        have hh : nextrel1 R p (Lng Q - 1) = true := by rw [← hje]; exact hpnr
        rw [nopar1R_rc2 Q R hL3 hpar1 hR p] at hh
        simp at hh
      have hjlt2 : j < Lng Q - 1 := by rw [hLngR] at hjLR; omega
      have hpQ : hasParent Q 1 j = true := by
        rw [← hp1eq_rc2 Q R hL3 hR j hjlt2]; exact hpRb
      have eQ : entry Q 1 (parent Q 1 j) + 1 = entry Q 1 j :=
        RedCondA_apply Q hCA_Q 1 j (by omega) hjQ hpQ
      have hpar1lt : parent Q 1 j < j :=
        (nextR_implies_row0 Q 1 _ _ (nextR_parent_rc2 Q 1 j hpQ)).1
      have hpe : parent R 1 j = parent Q 1 j := par1eq_rc2 Q R hL3 hR j hjlt2
      rw [hpe, he1ltR (parent Q 1 j) (by omega), he1ltR j hjlt2]
      exact eQ

private theorem condB_R_rc2 (Q R : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (_hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) : RedCondB R = true := by
  obtain ⟨hLngR, he0R, he1ltR, _, _⟩ := rBase_rc2 Q R hL3 hR
  obtain ⟨_, hCB_Q⟩ := RTPS_condAB Q hQR
  have hp0Q := hp0Q_rc2 Q hQR hmonoQ hL3
  have hQT : TPS Q := RTPS_TPS Q hQR
  rw [RedCondB]
  simp only [List.all_eq_true, List.mem_range]
  intro j hj
  have hjR : j < Lng R := by omega
  have hjQ : j < Lng Q := by rw [← hLngR]; exact hjR
  cases hpRb : hasParent R 0 j with
  | true => simp
  | false =>
    simp only [Bool.false_or, decide_eq_true_eq]
    have hnpQ : hasParent Q 0 j = false := by
      rw [← hp0eq_rc2 Q R hL3 hR j hjQ]; exact hpRb
    have hjne : j ≠ Lng Q - 1 := by
      intro hje; rw [hje, hp0Q] at hnpQ; simp at hnpQ
    have hjlt2 : j < Lng Q - 1 := by omega
    have eqQ : entry Q 0 j = entry Q 1 j := RedCondB_apply Q hQT hCB_Q j hjQ hnpQ
    rw [he0R j hjQ, he1ltR j hjlt2]; exact eqQ

private theorem RRT_rc2 (Q R : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) : RTPS R := by
  have hTPS_R : TPS R := by rw [hR]; apply List.ne_nil_of_length_pos; simp
  exact RTPS_of_condAB R hTPS_R (condA_R_rc2 Q R hQR hmonoQ hL3 hpar1 hR)
    (condB_R_rc2 Q R hQR hmonoQ hL3 hpar1 hR)

/-! ## 8. 汎用コア（Isabelle `s84c2_R_facts` の残差成分） -/

private theorem s84Rfacts_core_rc2 (Q R : PS) (hQR : RTPS Q) (hmonoQ : monoT Q = true)
    (hL3 : 3 ≤ Lng Q) (hpar1 : nextR Q 1 0 (Lng Q - 1) = true)
    (hR : R = Q.dropLast ++ [(entry Q 0 (Lng Q - 1), entry Q 1 0)]) :
    (entry Q 1 (Lng Q - 1) ≤ entry Q 1 (parent Q 0 (Lng Q - 1))
        ∨ parent Q 0 (Lng Q - 1) = 0)
    ∧ RTPS R
    ∧ adm R (parent Q 0 (Lng Q - 1)) = adm Q (parent Q 0 (Lng Q - 1))
    ∧ Adm R (parent Q 0 (Lng Q - 1)) = Adm Q (parent Q 0 (Lng Q - 1)) :=
  ⟨dich_rc2 Q hQR hmonoQ hL3 hpar1,
   RRT_rc2 Q R hQR hmonoQ hL3 hpar1 hR,
   admeq_rc2 Q R hQR hmonoQ hL3 hpar1 hR,
   Admeq_rc2 Q R hQR hmonoQ hL3 hpar1 hR⟩

/-! ## 9. `Q = s84rs_Q M` の前提（`ancestor_slice_Red_IncrFirst` 帰結、rfacts と同型） -/

private theorem tps_Np_rc2 (M : PS) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    TPS (s84x_Np M) := by
  have hlen : 0 < Lng (s84x_Np M) := by unfold s84x_Np; rw [length_seg]; omega
  exact List.ne_nil_of_length_pos hlen

private theorem q_facts_rc2 (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    RTPS (s84rs_Q M) ∧ monoT (s84rs_Q M) = true ∧
      s84x_Np M = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_Q M) := by
  obtain ⟨hjm2lt, _, hle0⟩ := s84c1_jm2_basic M hp
  have hleR : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using hle0
  have hanc := ancestor_slice_Red_IncrFirst M (s84x_jm2 M) (Lng M - 1) hMR hjm2lt (le_refl _) hleR
  obtain ⟨hRedN, hmonoN, hIF⟩ := hanc
  have hRedN' : Red (Red (s84x_Np M)) = Red (s84x_Np M) := hRedN
  refine ⟨?_, hmonoN, hIF⟩
  have h2 := Red2 (s84x_Np M) (tps_Np_rc2 M hrng); rw [hRedN'] at h2; exact h2

private theorem lenQ_eq_rc2 (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    Lng (s84rs_Q M) = Lng M - 1 + 1 - s84x_jm2 M := by
  obtain ⟨_, _, hIF⟩ := q_facts_rc2 M hMR hp hrng
  have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
    have h := congrArg Lng hIF; rwa [length_IncrFirstN] at h
  have h1 : Lng (s84x_Np M) = Lng M - 1 + 1 - s84x_jm2 M := by unfold s84x_Np; rw [length_seg]
  omega

private theorem lenQ3_rc2 (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    3 ≤ Lng (s84rs_Q M) := by
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have h := lenQ_eq_rc2 M hMR hp hrng; omega

private theorem par1Q_rc2 (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    nextR (s84rs_Q M) 1 0 (Lng (s84rs_Q M) - 1) = true := by
  obtain ⟨_, _, hIF⟩ := q_facts_rc2 M hMR hp hrng
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hLQ := lenQ_eq_rc2 M hMR hp hrng
  have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
    have h := congrArg Lng hIF; rwa [length_IncrFirstN] at h
  have hseg : s84x_Np M = seg M (s84x_jm2 M) (Lng M - 1) := rfl
  have hstep1 : nextR (s84rs_Q M) 1 0 (Lng (s84rs_Q M) - 1)
      = nextR (s84x_Np M) 1 0 (Lng (s84rs_Q M) - 1) := by rw [hIF, nextR_IncrFirstN_ri]
  have hstep2 : nextR (s84x_Np M) 1 0 (Lng (s84rs_Q M) - 1)
      = nextR M 1 (s84x_jm2 M + 0) (s84x_jm2 M + (Lng (s84rs_Q M) - 1)) := by
    rw [hseg]
    exact nextR_seg_adm M (s84x_jm2 M) (Lng M - 1) 1 0 (Lng (s84rs_Q M) - 1)
      (by omega) (by omega) (by rw [← hseg, hlenNp]; omega) (by rw [← hseg, hlenNp]; omega)
  have harg : s84x_jm2 M + (Lng (s84rs_Q M) - 1) = Lng M - 1 := by omega
  rw [hstep1, hstep2, Nat.add_zero, harg]
  exact nextR_parent_rc2 M 1 (Lng M - 1) hp

/-! ## 10. 残差 `Rm84RFacts` の無条件討伐と存在部フィールドへの合成 -/

/-- **R-facts 残差の討伐**（Isabelle `s84c2_R_facts` の Lean 版、`s84rs_Q`/`s84rs_R` 適用）。 -/
theorem rm84RFacts_holds : ∀ M : PS, STPS M → monoT M = true →
    hasParent M 1 (Lng M - 1) = true → s84x_jm2 M + 1 < Lng M - 1 → Rm84RFacts M := by
  intro M hST hmono hp hrng
  have hMR : RTPS M := STPS_RTPS M hST
  obtain ⟨hQR, hmonoQ, _⟩ := q_facts_rc2 M hMR hp hrng
  have hL3 : 3 ≤ Lng (s84rs_Q M) := lenQ3_rc2 M hMR hp hrng
  have hpar1 : nextR (s84rs_Q M) 1 0 (Lng (s84rs_Q M) - 1) = true := par1Q_rc2 M hMR hp hrng
  have hReq : s84rs_R M = (s84rs_Q M).dropLast
      ++ [(entry (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1), entry (s84rs_Q M) 1 0)] := rfl
  obtain ⟨hdich, hRRT, hadmR, hAdmR⟩ :=
    s84Rfacts_core_rc2 (s84rs_Q M) (s84rs_R M) hQR hmonoQ hL3 hpar1 hReq
  exact ⟨hdich, hRRT, hadmR, hAdmR⟩

/-- **合成**: `Rm84RFacts` から手術フレーム、そして存在部フィールド
`Rightmost84ReplaceExists`。termination の `rm84Exists` フィールドが陥落する。 -/
theorem rm84SurgeryFrame_rc2 : Rm84SurgeryFrame :=
  rm84SurgeryFrame_of_rfacts_rf rm84RFacts_holds

theorem rightmost84ReplaceExists_rc2 : Rightmost84ReplaceExists :=
  rightmost84ReplaceExists_of_rfacts_rf rm84RFacts_holds

#print axioms rm84RFacts_holds
#print axioms rm84SurgeryFrame_rc2
#print axioms rightmost84ReplaceExists_rc2

end PSS
