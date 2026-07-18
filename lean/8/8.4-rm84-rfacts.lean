import «8».«8.4-rm84-surgery»

/-!
# §8.4 補題（右端置き換えと `Trans`）— 手術フレーム残差 `Rm84SurgeryFrame` の R-facts 還元

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は DEFERRED。
- ブループリント: Isabelle `s84c2_R_base`/`s84c2_R_facts`（`isabelle/layerB/pss_wip.thy`
  54240–54594）＋ `m_8_4_rightend_Trans`（同 54650、part(2)(3) の branch 解析
  `condAQ_iff`/`condAR_iff`）。
- 攻略対象: `«8».«8.4-rm84-surgery»` の残差 `Rm84SurgeryFrame`（同 :157）。5 部:
  (1)(2) `β`/`γ` 値橋（`aQeq`/`aReq`）、(3) `transC2 (s84rs_R M) = c2hole_ch (s84rs_Q M) γ`
  （branch 解析）、(4) `Trans (rrLp M) = Trans (s84rs_R M)`（`Lp = IncrFirst^k R`＋`Trans_Red`）、
  (5) 共有 scb 対（`s84c2_Trans_c2_decomp` を `Q`,`R` に＋`scb_unique`）。

## 本ファイルの寄与（5 部すべてを無条件 or R-facts modulo で証明）

- **(1)(2)** `part1_rf`/`part2_rf`（無条件、`IncrFirstN` 行1不変＋`entry_seg`）。
- **(4)** `part4_rf`（無条件、`rrLp M = IncrFirst^k (s84rs_R M)` の `LpIF_rf`＋`Red` の
  `IncrFirst` 不変＋`Trans_Red`）。
- **(3)** `part3_rf`：`c2hole_ch` congruence。branch 選択の一致は `condAQ_rf`/`condAR_rf`
  （Isabelle `condAQ_iff`/`condAR_iff` の忠実 port、`estep`/`dich`/`weak`/`adm_zero` 経由）
  ＋ `notVIQ_rf`/`notVIR_rf`。R-facts（`dich`/`admRQ`/`AdmRQ`）を仮定。
- **(5)** `part5_rf`：`s84c2_Trans_c2_decomp`（局所 `tsurg_rf`）を `Q`,`R` に適用し
  `scb_unique_decomp_unconditional` で `(s,b)` を一致。R-facts（`RTPS R`/`AdmRQ`）を仮定。
- 無条件に得た R-facts の部分: `monoT (s84rs_R M)`（`monoR_rf`、行0一致）、
  `par0R`（`par0R_rf`）、`transC1 R = transC1 Q`（`transC1_eq_rf`）、Q 側順序事実
  （`par1Q`/`parent1Q`/`estep`/`j0lt`/`weak`）。

## 残差 `Rm84RFacts`（= Isabelle `s84c2_R_facts` の中核）

`dich`（行1親一意性の帰結）・`RTPS (s84rs_R M)`（条件(A)(B)）・`adm`/`Adm` の `j₀` 一致。
prefix-agreement 機構（行1の下端未満一致＋右端に行1親が消える）が要。数値検証済
（45/45＋cex＋A30、`8.4-rm84-surgery` header）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private suffix: `_rf`。
-/

namespace PSS

/-! ## 0. `s84rs_R` の構造事実（Isabelle `s84c2_R_base`） -/

private theorem rBase_rf (Q R : PS) (hL3 : 3 ≤ Lng Q)
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

/-! ## 1. `Q = Red (s84x_Np M)` の基本性質（`ancestor_slice_Red_IncrFirst` の帰結） -/

private theorem tps_Np_rf (M : PS) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    TPS (s84x_Np M) := by
  have hlen : 0 < Lng (s84x_Np M) := by unfold s84x_Np; rw [length_seg]; omega
  exact List.ne_nil_of_length_pos hlen

private theorem q_facts_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    RTPS (s84rs_Q M) ∧ monoT (s84rs_Q M) = true ∧
      s84x_Np M = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_Q M) := by
  obtain ⟨hjm2lt, _, hle0⟩ := s84c1_jm2_basic M hp
  have hleR : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using hle0
  have hanc := ancestor_slice_Red_IncrFirst M (s84x_jm2 M) (Lng M - 1) hMR hjm2lt (le_refl _) hleR
  obtain ⟨hRedN, hmonoN, hIF⟩ := hanc
  have hRedN' : Red (Red (s84x_Np M)) = Red (s84x_Np M) := hRedN
  refine ⟨?_, hmonoN, hIF⟩
  have h2 := Red2 (s84x_Np M) (tps_Np_rf M hrng); rw [hRedN'] at h2; exact h2

private theorem lenQ_eq_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    Lng (s84rs_Q M) = Lng M - 1 + 1 - s84x_jm2 M := by
  obtain ⟨_, _, hIF⟩ := q_facts_rf M hMR hp hrng
  have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
    have h := congrArg Lng hIF; rwa [length_IncrFirstN] at h
  have h1 : Lng (s84x_Np M) = Lng M - 1 + 1 - s84x_jm2 M := by unfold s84x_Np; rw [length_seg]
  omega

private theorem lenQ3_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    3 ≤ Lng (s84rs_Q M) := by
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have h := lenQ_eq_rf M hMR hp hrng; omega

/-! ## 2. 値橋 (1)(2)（Isabelle `aQeq`/`aReq`、`eQ1` 経由） -/

private theorem entryQ1_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (j : ℕ) (hj : j < Lng (s84rs_Q M)) :
    entry (s84rs_Q M) 1 j = entry M 1 (s84x_jm2 M + j) := by
  obtain ⟨_, _, hIF⟩ := q_facts_rf M hMR hp hrng
  have hA : entry (s84x_Np M) 1 j = entry (s84rs_Q M) 1 j := by
    rw [hIF]; exact entry_IncrFirstN_one _ _ j
  have hnpj : j < Lng (s84x_Np M) := by
    have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
      have h := congrArg Lng hIF; rwa [length_IncrFirstN] at h
    rw [hlenNp]; exact hj
  have hB : entry (s84x_Np M) 1 j = entry M 1 (s84x_jm2 M + j) := by
    have heq : s84x_Np M = seg M (s84x_jm2 M) (Lng M - 1) := rfl
    have hseg := entry_seg M (s84x_jm2 M) (Lng M - 1) 1 j (by rw [← heq]; exact hnpj)
    rw [heq]; exact hseg
  exact hA.symm.trans hB

private theorem part1_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) = entry M 1 (Lng M - 1) := by
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hLQ := lenQ_eq_rf M hMR hp hrng
  have h := entryQ1_rf M hMR hp hrng (Lng (s84rs_Q M) - 1) (by omega)
  rw [h]; congr 1; omega

private theorem part2_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    entry (s84rs_Q M) 1 0 = entry M 1 (s84x_jm2 M) := by
  have h3 := lenQ3_rf M hMR hp hrng
  have h := entryQ1_rf M hMR hp hrng 0 (by omega)
  simpa using h

/-! ## 3. `Trans` 一致 (4)（Isabelle `TransLp`、`Lp = IncrFirst^k R`） -/

private theorem dropLast_seg_rf (M : PS) (a b : ℕ) (hab : a < b) :
    (seg M a b).dropLast = seg M a (b - 1) := by
  unfold seg
  rw [← List.map_dropLast]
  congr 1
  have h1 : b + 1 - a = (b - a) + 1 := by omega
  have h2 : (b - 1) + 1 - a = b - a := by omega
  rw [h1, h2, List.range'_concat]; simp

private theorem red_incrFirstN_rf (n : ℕ) (X : PS) (hX : TPS X) :
    Red (IncrFirstN n X) = Red X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
      rw [IncrFirstN]
      have hI : TPS (IncrFirst X) := by simpa [TPS, IncrFirst] using hX
      rw [ih (IncrFirst X) hI, Red_IncrFirst X hX]

private theorem e0last_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    entry (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)
      + (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) = entry M 0 (Lng M - 1) := by
  obtain ⟨_, _, hIF⟩ := q_facts_rf M hMR hp hrng
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hLQ := lenQ_eq_rf M hMR hp hrng
  have h3 := lenQ3_rf M hMR hp hrng
  have hA : entry (s84x_Np M) 0 (Lng (s84rs_Q M) - 1)
      = entry (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)
        + (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) := by
    rw [hIF]; exact entry_IncrFirstN_zero _ _ _ (by omega)
  have hnpj : Lng (s84rs_Q M) - 1 < Lng (s84x_Np M) := by
    have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
      have h := congrArg Lng hIF; rwa [length_IncrFirstN] at h
    rw [hlenNp]; omega
  have hB : entry (s84x_Np M) 0 (Lng (s84rs_Q M) - 1) = entry M 0 (Lng M - 1) := by
    have heq : s84x_Np M = seg M (s84x_jm2 M) (Lng M - 1) := rfl
    have hseg := entry_seg M (s84x_jm2 M) (Lng M - 1) 0 (Lng (s84rs_Q M) - 1) (by
      rw [← heq]; exact hnpj)
    rw [heq, hseg]; congr 1; omega
  rw [← hA, hB]

private theorem LpIF_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    rrLp M
      = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_R M) := by
  obtain ⟨_, _, hIF⟩ := q_facts_rf M hMR hp hrng
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  unfold rrLp s84rs_R
  rw [IncrFirstN_eq_map, List.map_append]
  congr 1
  · rw [List.map_dropLast, ← IncrFirstN_eq_map, ← hIF]
    have hds : (s84x_Np M).dropLast = seg M (s84x_jm2 M) (Lng M - 2) := by
      have hnp : s84x_Np M = seg M (s84x_jm2 M) (Lng M - 1) := rfl
      have harg : Lng M - 1 - 1 = Lng M - 2 := by omega
      rw [hnp, dropLast_seg_rf M (s84x_jm2 M) (Lng M - 1) (by omega), harg]
    rw [hds]
  · have he0 := e0last_rf M hMR hp hrng
    have he1 := part2_rf M hMR hp hrng
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true]
    exact ⟨by omega, he1.symm⟩

private theorem part4_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    Trans (rrLp M) = Trans (s84rs_R M) := by
  have hLpIF := LpIF_rf M hMR hp hrng
  have hTPSr : TPS (s84rs_R M) := by
    unfold s84rs_R; apply List.ne_nil_of_length_pos; simp
  have hTPSlp : TPS (rrLp M) := by
    unfold rrLp; apply List.ne_nil_of_length_pos; simp
  rw [Trans_Red (rrLp M) hTPSlp, hLpIF, red_incrFirstN_rf _ (s84rs_R M) hTPSr]
  exact (Trans_Red (s84rs_R M) hTPSr).symm

/-! ## 4. R-facts（行0一致 → `monoT R`・`par0R`） -/

private theorem hall_congr_rf (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.all_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem hany_congr_rf (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.any_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem nextrel0_eq_rf (M N : PS) (hL : Lng M = Lng N)
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
    apply hall_congr_rf
    intro x hx
    have hxj1 : x < j1 := List.mem_range.mp hx
    rw [e1, he x (hxj1.trans hj1)]
  rw [hallc, hL, e0, e1]

private theorem le0Aux_eq_rf (M N : PS)
    (hne : ∀ a b, a < Lng N → b < Lng N → nextrel0 M a b = nextrel0 N a b)
    (fuel j0 j1 : ℕ) (hj1 : j1 < Lng N) :
    le0Aux M fuel j0 j1 = le0Aux N fuel j0 j1 := by
  induction fuel generalizing j1 with
  | zero => rfl
  | succ f ih =>
      simp only [le0Aux]
      congr 1
      apply hany_congr_rf
      intro j hj
      have hjj1 : j < j1 := List.mem_range.mp hj
      have hjL : j < Lng N := hjj1.trans hj1
      rw [hne j j1 hjL hj1, ih j hjL]

private theorem le0_eq_rf (M N : PS) (hL : Lng M = Lng N)
    (hne : ∀ a b, a < Lng N → b < Lng N → nextrel0 M a b = nextrel0 N a b)
    (j0 j1 : ℕ) (hj1 : j1 < Lng N) :
    le0 M j0 j1 = le0 N j0 j1 := by
  unfold le0
  rw [hL, le0Aux_eq_rf M N hne (Lng N) j0 j1 hj1]

private theorem monoR_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    monoT (s84rs_R M) = true := by
  obtain ⟨_, hQmono, _⟩ := q_facts_rf M hMR hp hrng
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, he0R, _, _, _⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hne : ∀ a b, a < Lng (s84rs_Q M) → b < Lng (s84rs_Q M) →
      nextrel0 (s84rs_R M) a b = nextrel0 (s84rs_Q M) a b :=
    fun a b ha hb => nextrel0_eq_rf (s84rs_R M) (s84rs_Q M) hLngR he0R a b ha hb
  have hleQ : leR (s84rs_Q M) 0 0 (Lng (s84rs_Q M) - 1) = true := by
    have := hQmono; simp only [monoT, Bool.and_eq_true] at this; exact this.2
  have hle0Q : le0 (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = true := by simpa [leR] using hleQ
  have hle0R : le0 (s84rs_R M) 0 (Lng (s84rs_Q M) - 1) = true := by
    rw [le0_eq_rf (s84rs_R M) (s84rs_Q M) hLngR hne 0 (Lng (s84rs_Q M) - 1) (by omega)]
    exact hle0Q
  have hzR : zeroT (s84rs_R M) = false := by
    unfold zeroT
    rw [hLngR]
    have : (Lng (s84rs_Q M) == 1) = false := by rw [beq_eq_false_iff_ne]; omega
    rw [this, Bool.false_and]
  have hleR0 : leR (s84rs_R M) 0 0 (Lng (s84rs_R M) - 1) = true := by
    rw [hLngR]; simp only [leR]; exact hle0R
  simp only [monoT, hzR, Bool.not_false, Bool.true_and]
  exact hleR0

private theorem parents0_eq_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (j1 : ℕ) (hj1 : j1 < Lng (s84rs_Q M)) :
    parents (s84rs_R M) 0 j1 = parents (s84rs_Q M) 0 j1 := by
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, he0R, _, _, _⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  unfold parents
  rw [hLngR]
  apply List.filter_congr
  intro p hp'
  have hpL : p < Lng (s84rs_Q M) := List.mem_range.mp hp'
  simp only [nextR]
  exact nextrel0_eq_rf (s84rs_R M) (s84rs_Q M) hLngR he0R p j1 hpL hj1

private theorem par0R_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    parent (s84rs_R M) 0 (Lng (s84rs_Q M) - 1)
      = parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) := by
  have h3 := lenQ3_rf M hMR hp hrng
  unfold parent
  rw [parents0_eq_rf M hMR hp hrng (Lng (s84rs_Q M) - 1) (by omega)]

/-! ## 5. Q 側順序事実（`par1Q`/`parent1Q`/`estep`/`j0lt`/`weak`） -/

private theorem nextR_parent_rf (M : PS) (i j1 : ℕ) (hp : hasParent M i j1 = true) :
    nextR M i (parent M i j1) j1 = true := by
  obtain ⟨p, hp1, huniq⟩ := (hasParent_iff_unique_fseq M i j1).mp hp
  have heq := parent_eq_of_unique_fseq M i j1 p hp1 (fun y hy => huniq y hy)
  rw [heq]; exact hp1

private theorem par1Q_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    nextR (s84rs_Q M) 1 0 (Lng (s84rs_Q M) - 1) = true := by
  obtain ⟨_, _, hIF⟩ := q_facts_rf M hMR hp hrng
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hLQ := lenQ_eq_rf M hMR hp hrng
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
  exact nextR_parent_rf M 1 (Lng M - 1) hp

private theorem hasParent1Q_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    hasParent (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) = true := by
  apply (hasParent_iff_unique_fseq (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)).mpr
  refine ⟨0, par1Q_rf M hMR hp hrng, ?_⟩
  intro y hy
  exact nextR1_unique_mr (s84rs_Q M) y 0 (Lng (s84rs_Q M) - 1) hy (par1Q_rf M hMR hp hrng)

private theorem parent1Q_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    parent (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) = 0 := by
  apply parent_eq_of_unique_fseq (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) 0 (par1Q_rf M hMR hp hrng)
  intro y hy
  exact nextR1_unique_mr (s84rs_Q M) y 0 (Lng (s84rs_Q M) - 1) hy (par1Q_rf M hMR hp hrng)

private theorem estep_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    entry (s84rs_Q M) 1 0 + 1 = entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) := by
  obtain ⟨hQR, _, _⟩ := q_facts_rf M hMR hp hrng
  have h3 := lenQ3_rf M hMR hp hrng
  have hA := (RTPS_condAB (s84rs_Q M) hQR).1
  have hp1 := hasParent1Q_rf M hMR hp hrng
  have hstep := RedCondA_apply (s84rs_Q M) hA 1 (Lng (s84rs_Q M) - 1) (by omega) (by omega) hp1
  rw [parent1Q_rf M hMR hp hrng] at hstep
  exact hstep

private theorem hasParent0Q_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    hasParent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = true := by
  obtain ⟨hQR, hQmono, _⟩ := q_facts_rf M hMR hp hrng
  have h3 := lenQ3_rf M hMR hp hrng
  have hQT : TPS (s84rs_Q M) := RTPS_TPS _ hQR
  exact mono_hasParent_row0 (s84rs_Q M) hQT hQmono (Lng (s84rs_Q M) - 1) (by omega) (by omega)

private theorem j0lt_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) < Lng (s84rs_Q M) - 1 := by
  have hp0 := hasParent0Q_rf M hMR hp hrng
  have hnext := nextR_parent_rf (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) hp0
  exact (nextR_implies_row0 (s84rs_Q M) 0 _ _ hnext).1

private theorem weak_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0) :
    entry (s84rs_Q M) 1 0
      ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)) := by
  have he := estep_rf M hMR hp hrng
  rcases hdich with h | h
  · omega
  · rw [h]

/-! ## 6. 局所 `s84c2_Trans_c2_decomp`＋`transC1 R = transC1 Q`＋部分 (5) -/

private theorem transT1ne_rf (Q : PS) (hQR : RTPS Q) (hLen3 : 3 ≤ Lng Q) :
    transT1 Q ≠ BZero := by
  have hlen : 1 < Lng Q := by omega
  have hLP : Lng (Pred Q) = Lng Q - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred Q) = false := by simp [zeroT, hLP]; omega
  have T1' : Trans (Pred Q) ≠ BZero :=
    (Trans_Mark_invariant (Pred Q) (RTPS_Pred Q hQR)).2.1 nzP
  simpa [transT1] using T1'

private theorem tsurg_rf (X : PS) (hR : RTPS X)
    (hmono : monoT X = true) (hj₁ : 0 < transJ1 X) (ht₁ : transT1 X ≠ BZero) :
    ∃ s b, scb_decomp (Trans (Pred X)) s (flatBT (transC1 X)) b ∧
      scb_decomp (Trans X) s (flatBT (transC2 X)) b := by
  have hM : TPS X := RTPS_TPS X hR
  have hlen : 1 < Lng X := by simp only [transJ1, lastIdx] at hj₁; omega
  have hpredR : RTPS (Pred X) := RTPS_Pred X hR
  have hp : hasParent X 0 (Lng X - 1) = true :=
    mono_hasParent_row0 X hM hmono (Lng X - 1) (by omega) (by omega)
  have hmarked : Marked (Pred X) (transJm1 X) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm X hM hlen hp
  have hinv := (Trans_Mark_invariant (Pred X) hpredR).2.2 _ hmarked
  have ht₁TB : Trans (Pred X) ∈ T_B := (Trans_Mark_invariant (Pred X) hpredR).1
  have hc₁TB : transC1 X ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using hinv.1
  have hmb : (Trans (Pred X), transC1 X) ∈ MarkedB := by
    simpa [transT1, transC1, transJm1, transJ0, lastParent] using hinv.2
  have hc₁P : ∃ p, transC1 X = .trm [p] := by
    have h := principal_reconstruct (transC1_single_principal X hR hmono hj₁ ht₁)
    exact ⟨.db (transV X) (transT2 X), by simpa [Dprin] using h⟩
  have hprops := transC2Core_properties X (transC1 X) hc₁TB hc₁P
  have hc₂TB : transC2 X ∈ T_B := by simpa [transC2, transV, transT2] using hprops.1
  have hc₂P : ∃ p, transC2 X = .trm [p] := by simpa [transC2, transV, transT2] using hprops.2
  obtain ⟨s, b, hd₁, _hflat, hd₂⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P hmb
  refine ⟨s, b, hd₁, ?_⟩
  have hTM : Trans X = replaceScb (Trans (Pred X)) (transC1 X) (transC2 X) := by
    have heq := (Trans_Mark_mono_equations X hR hlen hmono).1
    have ht₁b : (Trans (Pred X) == BZero) = false := by simpa [beq_iff_eq, transT1] using ht₁
    simpa [transT1, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent, ht₁b] using heq
  rw [hTM]; exact hd₂

private theorem transC1_eq_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hAdmR : Adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
           = Adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))) :
    transC1 (s84rs_R M) = transC1 (s84rs_Q M) := by
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, _, _, _, hPredR⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hpar0R := par0R_rf M hMR hp hrng
  have hj0R : transJ0 (s84rs_R M) = parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) := by
    unfold transJ0 lastParent lastIdx; rw [hLngR]; exact hpar0R
  have hj0Q : transJ0 (s84rs_Q M) = parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) := rfl
  have hjm1 : transJm1 (s84rs_R M) = transJm1 (s84rs_Q M) := by
    unfold transJm1; rw [hj0R, hj0Q, hAdmR]
  unfold transC1; rw [hPredR, hjm1]

private theorem part5_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hRRT : RTPS (s84rs_R M))
    (hAdmR : Adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
           = Adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))) :
    ∃ s1 b1 : List Sym,
      scb_decomp (Trans (s84rs_Q M)) s1 (flatBT (transC2 (s84rs_Q M))) b1 ∧
      scb_decomp (Trans (s84rs_R M)) s1 (flatBT (transC2 (s84rs_R M))) b1 := by
  obtain ⟨hQR, hQmono, _⟩ := q_facts_rf M hMR hp hrng
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, _, _, _, hPredR⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hRmono := monoR_rf M hMR hp hrng
  have hC1eq := transC1_eq_rf M hMR hp hrng hAdmR
  have hJ1Q : 0 < transJ1 (s84rs_Q M) := by simp only [transJ1, lastIdx]; omega
  have hJ1R : 0 < transJ1 (s84rs_R M) := by
    simp only [transJ1, lastIdx]; rw [hLngR]; omega
  have hT1Q : transT1 (s84rs_Q M) ≠ BZero := transT1ne_rf (s84rs_Q M) hQR h3
  have hT1R : transT1 (s84rs_R M) ≠ BZero := by
    have heq : transT1 (s84rs_R M) = transT1 (s84rs_Q M) := by unfold transT1; rw [hPredR]
    rw [heq]; exact hT1Q
  obtain ⟨s1, b1, dPQ, dTQ⟩ := tsurg_rf (s84rs_Q M) hQR hQmono hJ1Q hT1Q
  obtain ⟨s1', b1', dPR, dTR⟩ := tsurg_rf (s84rs_R M) hRRT hRmono hJ1R hT1R
  rw [hPredR, hC1eq] at dPR
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (Pred (s84rs_Q M)))
    s1' s1 (flatBT (transC1 (s84rs_Q M))) b1' b1 dPR dPQ
  rw [hs, hb] at dTR
  exact ⟨s1, b1, dTQ, dTR⟩

/-! ## 7. branch 解析（Isabelle `condAQ_iff`/`condAR_iff`）＋部分 (3) -/

private theorem notVIQ_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0) :
    transCondVI (s84rs_Q M) = false := by
  have h3 := lenQ3_rf M hMR hp hrng
  have he := estep_rf M hMR hp hrng
  rw [Bool.eq_false_iff]; intro hVI
  simp only [transCondVI, lastIdx, lastParent, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hVI
  obtain ⟨⟨_, hueq⟩, hjeq⟩ := hVI
  rcases hdich with hle | hj0
  · omega
  · omega

private theorem notVIR_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0) :
    transCondVI (s84rs_R M) = false := by
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, _, he1ltR, he1lastR, _⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hpar0R := par0R_rf M hMR hp hrng
  have hj0lt := j0lt_rf M hMR hp hrng
  have hw := weak_rf M hMR hp hrng hdich
  rw [Bool.eq_false_iff]; intro hVI
  simp only [transCondVI, lastIdx, lastParent, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hVI
  obtain ⟨⟨_, hueq⟩, _⟩ := hVI
  rw [hLngR] at hueq
  rw [hpar0R] at hueq
  rw [he1ltR _ hj0lt, he1lastR] at hueq
  omega

private theorem condAR_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0)
    (hadmR : adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
           = adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))) :
    (transCondI (s84rs_R M) || transCondIII (s84rs_R M) || transCondV (s84rs_R M))
      = adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)) := by
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, _, he1ltR, he1lastR, _⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hpar0R := par0R_rf M hMR hp hrng
  have hj0lt := j0lt_rf M hMR hp hrng
  have hw := weak_rf M hMR hp hrng hdich
  simp only [transCondI, transCondIII, transCondV, lastIdx, lastParent, hLngR]
  rw [hpar0R, he1lastR, he1ltR _ hj0lt, hadmR]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ((⟨_, ha⟩ | ⟨⟨_, _⟩, ha⟩) | ⟨⟨_, hu1⟩, _⟩)
    · exact ha
    · exact ha
    · exfalso; omega
  · intro ha
    by_cases hv0 : entry (s84rs_Q M) 1 0 = 0
    · exact Or.inl (Or.inl ⟨hv0, ha⟩)
    · exact Or.inl (Or.inr ⟨⟨Nat.pos_of_ne_zero hv0, hw⟩, ha⟩)

private theorem condAQ_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0) :
    (transCondI (s84rs_Q M) || transCondIII (s84rs_Q M) || transCondV (s84rs_Q M))
      = adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)) := by
  have h3 := lenQ3_rf M hMR hp hrng
  have he := estep_rf M hMR hp hrng
  have hj0lt := j0lt_rf M hMR hp hrng
  simp only [transCondI, transCondIII, transCondV, lastIdx, lastParent]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ((⟨_, ha⟩ | ⟨⟨_, _⟩, ha⟩) | ⟨⟨_, hu1⟩, _⟩)
    · exact ha
    · exact ha
    · rcases hdich with hle | hj0
      · exfalso; omega
      · rw [hj0]; exact adm_zero (s84rs_Q M)
  · intro ha
    rcases hdich with hle | hj0
    · exact Or.inl (Or.inr ⟨⟨by omega, hle⟩, ha⟩)
    · refine Or.inr ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [hj0]; exact he
      · rw [hj0]; omega

private theorem part3_rf (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hdich : entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
        ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0)
    (hadmR : adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
           = adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1)))
    (hAdmR : Adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
           = Adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))) :
    transC2 (s84rs_R M) = c2hole_ch (s84rs_Q M) (entry (s84rs_Q M) 1 0) := by
  have h3 := lenQ3_rf M hMR hp hrng
  obtain ⟨hLngR, _, he1ltR, he1lastR, _⟩ := rBase_rf (s84rs_Q M) (s84rs_R M) h3 rfl
  have hpar0R := par0R_rf M hMR hp hrng
  have hj0lt := j0lt_rf M hMR hp hrng
  have hC1eq := transC1_eq_rf M hMR hp hrng hAdmR
  have hEL : entry (s84rs_R M) 1 (lastIdx (s84rs_R M)) = entry (s84rs_Q M) 1 0 := by
    unfold lastIdx; rw [hLngR]; exact he1lastR
  have A1 : (transCondI (s84rs_R M) || transCondIII (s84rs_R M) || transCondV (s84rs_R M))
      = (transCondI (s84rs_Q M) || transCondIII (s84rs_Q M) || transCondV (s84rs_Q M)) :=
    (condAR_rf M hMR hp hrng hdich hadmR).trans (condAQ_rf M hMR hp hrng hdich).symm
  have A2 : transCondVI (s84rs_R M) = transCondVI (s84rs_Q M) :=
    (notVIR_rf M hMR hp hrng hdich).trans (notVIQ_rf M hMR hp hrng hdich).symm
  have A3 : transV (s84rs_R M) = transV (s84rs_Q M) := by unfold transV; rw [hC1eq]
  have A4 : transT2 (s84rs_R M) = transT2 (s84rs_Q M) := by unfold transT2; rw [hC1eq]
  have A5 : entry (s84rs_R M) 1 (lastParent (s84rs_R M))
      = entry (s84rs_Q M) 1 (lastParent (s84rs_Q M)) := by
    unfold lastParent lastIdx; rw [hLngR, hpar0R]; exact he1ltR _ hj0lt
  have A6 : c2hole_t3_ch (s84rs_R M) = c2hole_t3_ch (s84rs_Q M) := by
    unfold c2hole_t3_ch; rw [A4, A5]
  have A7 : c2hole_t4_ch (s84rs_R M) = c2hole_t4_ch (s84rs_Q M) := by
    unfold c2hole_t4_ch; rw [A4, A5]
  rw [c2hole_at_j1_ch (s84rs_R M), hEL]
  unfold c2hole_ch
  rw [A1, A2, A3, A4, A5, A6, A7]

/-! ## 8. 残差 `Rm84RFacts`（Isabelle `s84c2_R_facts` 中核）と `Rm84SurgeryFrame` への合成 -/

/-- **R-facts 残差** = Isabelle `s84c2_R_facts` の中核（`dich` = 行1親一意性の帰結、
`R ∈ RT_PS`、`adm`/`Adm` の行0親 `j₀` での一致）。prefix-agreement 機構が要。 -/
def Rm84RFacts (M : PS) : Prop :=
  (entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1)
      ≤ entry (s84rs_Q M) 1 (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
    ∨ parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1) = 0)
  ∧ RTPS (s84rs_R M)
  ∧ adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      = adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
  ∧ Adm (s84rs_R M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))
      = Adm (s84rs_Q M) (parent (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1))

/-- `Rm84RFacts` が域全体で成り立てば、5 部すべてが揃い `Rm84SurgeryFrame` が閉じる。 -/
theorem rm84SurgeryFrame_of_rfacts_rf
    (h : ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      s84x_jm2 M + 1 < Lng M - 1 → Rm84RFacts M) :
    Rm84SurgeryFrame := by
  intro M hST hmono hp hrng
  have hMR : RTPS M := STPS_RTPS M hST
  obtain ⟨hdich, hRRT, hadmR, hAdmR⟩ := h M hST hmono hp hrng
  exact ⟨part1_rf M hMR hp hrng, part2_rf M hMR hp hrng,
    part3_rf M hMR hp hrng hdich hadmR hAdmR,
    part4_rf M hMR hp hrng,
    part5_rf M hMR hp hrng hRRT hAdmR⟩

/-- 合成: `Rm84RFacts` から `Rightmost84ReplaceExists`（存在部フィールド）。 -/
theorem rightmost84ReplaceExists_of_rfacts_rf
    (h : ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      s84x_jm2 M + 1 < Lng M - 1 → Rm84RFacts M) :
    Rightmost84ReplaceExists :=
  rightmost84ReplaceExists_of_surgeryFrame_rs (rm84SurgeryFrame_of_rfacts_rf h)

#print axioms rm84SurgeryFrame_of_rfacts_rf
#print axioms rightmost84ReplaceExists_of_rfacts_rf

end PSS
