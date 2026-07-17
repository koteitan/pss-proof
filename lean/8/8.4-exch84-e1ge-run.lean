import «8».«8.4-s84x-vocab-run»
import «6».«6.8-d1pos-final»
import «6».«6.8-standard-slice-Br-descending»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-mono-slice»
import «6».«6.5-monoT-Red»
import «6».«6.4-P-IdxSum»
import «6».«6.4-P-IdxSum-characterization»
import «6».«6.2-P-fseq»
import «6».«6.2-mono-ancestor-slice»
import «8».«8.5-Joints-FirstNodes-basic»

/-!
# §8.4 RUN 脚: `E1GE` 非祖先枝の値不等式（残差 `e1x_ineq_nonanc` の討伐）

- Isabelle 対応（すべて `isabelle/layerB/pss_wip.thy`）:
  * `e1x_ineq_nonanc` (:97657, ~200 行) → `e1x_ineq_nonanc`（本ファイル、house pattern で
    vocab の `e1x_ineq_nonanc_Prop` を TYPE にした drop-in）。
  * `e1x_child_is_FN` (:97622) → private `child_is_FN_er`。
  * `e1x_e1ge_uncond` (:97869) → `e1x_e1ge_uncond`（`e1x_e1ge_uncond_of_ineq` へ残差を注入して
    **無条件化**。これで RUN 脚全体が解禁）。

- 証明骨格（Isabelle 97664–97862 のまま、Lean idiom で短縮）:
  by_contra `asm : entry M 1 (jm2+1) ≤ entry M 1 jm2`。アンカー切片
  `S = seg M jm2 j1`（`jm2 = s84x_jm2 M`, `j1 = Lng M - 1`）。`asm` が最初の幹 step を殺すので
  `TrMax S = 0`、`Br S ≠ []`。`le0 M jm2 j1` の最初の行0辺を子 `a`（非祖先なので `a > jm2+1`）へ
  peel。`RedCondA` が `entry M 0 a = entry M 0 (jm2+1) = entry M 0 jm2 + 1`（行0 head 一致）。
  `FirstNodes 0` と `Ja` の 2 枝 head は行0 head が等しく、`descending (Br S)`（`descendingD`）の
  行1 tie-break で `entry M 1 a ≤ entry M 1 (jm2+1)`。`nextrel1 M jm2 j1` の valley
  （`s84c1_jm2_univ`）で `entry M 1 j1 ≤ entry M 1 a`。`e1jm2lt` と `asm` で矛盾。

- 依存（すべてビルド済み・committed）:
  `s84x_jm2`/`s84c1_jm2_basic`/`s84c1_jm2_univ`/`c3cx_nextrel0_adj_of_le0`/`e1x_ineq_nonanc_Prop`/
  `e1x_e1ge_uncond_of_ineq`（8.4-s84x-vocab-run）、`standard_slice_Br_descending`（6.8-d1pos-final）、
  `descending`/`cdom`/`descendingD`（6.8-standard-slice-Br-descending）、
  `branch_component_le0`/`TrMax_trunk_step`（6.4-mono-slice）、
  `entry_FirstNodes_eq_component_mr`（6.5-monoT-Red）、`FirstNodes_getD`（6.4-FirstNodes-TrMax-Joints）、
  `parent_eq_of_nextR0`（6.4-mono-slice-next 経由）、`row0_parent_unique`（6.4-P-IdxSum-characterization）、
  `hasParent_iff_unique_fseq`/`P_nonempty`（6.2-P-fseq）、`entry_seg`/`length_seg`（6.2-mono-ancestor-slice）、
  `idxSum_getD`（6.4-P-IdxSum）、`RTPS_condAB`/`STPS_RTPS`（6.6/6.7 経由）。

- 状態: 🤖 leaf クローズ狙い（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_er`。
-/

namespace PSS

/-! ## 1. `nextrel0` フィールド抽出と `le0` の前方 peel（前方の最初の子） -/

/-- `nextrel0 M a c` から辺の三事実（添字増加・行0 head 増加・`c < Lng M`）。 -/
private theorem nextrel0_lt_er {M : PS} {a c : ℕ} (h : nextrel0 M a c = true) :
    a < c ∧ entry M 0 a < entry M 0 c ∧ c < Lng M := by
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.1.1.1.2⟩

/-- `nextrel0 M a c` の谷条件: `a < j < c` なら `entry M 0 c ≤ entry M 0 j`。 -/
private theorem nextrel0_valley_er {M : PS} {a c j : ℕ}
    (h : nextrel0 M a c = true) (haj : a < j) (hjc : j < c) :
    entry M 0 c ≤ entry M 0 j := by
  simp only [nextrel0, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hb := h.2 j hjc
  rw [decide_eq_true haj] at hb
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hb
  exact hb

private theorem le0Aux_refl_er (M : PS) (fuel a : ℕ) : le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0Aux_index_er {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero => simp only [le0Aux, beq_iff_eq] at h; omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        List.mem_range, Bool.and_eq_true] at h
      rcases h with h | ⟨j, hjb, _, haj⟩
      · omega
      · exact le_trans (ih haj) (le_of_lt hjb)

private theorem le0_le_er {M : PS} {a b : ℕ} (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_index_er h.2

/-- `le0Aux` の前方 peel: `a < b` なら最初の子 `c`（`nextrel0 M a c`）で `c ≤ b` かつ
`c` から `b` へ到達（`le0Aux M fuel c b`）。燃料に関する構造帰納で末尾辺を剥がしながら
最初の子を取り出す。 -/
private theorem le0Aux_first_er (M : PS) : ∀ (fuel a b : ℕ),
    le0Aux M fuel a b = true → a < b →
    ∃ c, nextrel0 M a c = true ∧ c ≤ b ∧ le0Aux M fuel c b = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b h hab
      simp only [le0Aux, beq_iff_eq] at h
      omega
  | succ fuel ih =>
      intro a b h hab
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        List.mem_range, Bool.and_eq_true] at h
      rcases h with heq | ⟨p, hpb, hnp, hap⟩
      · omega
      · by_cases hap_eq : a = p
        · subst hap_eq
          exact ⟨b, hnp, le_refl b, le0Aux_refl_er M (fuel + 1) b⟩
        · have hle : a ≤ p := le0Aux_index_er hap
          have hlt : a < p := lt_of_le_of_ne hle hap_eq
          obtain ⟨c, hnc, hcp, hcp2⟩ := ih a p hap hlt
          refine ⟨c, hnc, le_trans hcp (le_of_lt hpb), ?_⟩
          simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
            List.mem_range, Bool.and_eq_true]
          exact Or.inr ⟨p, hpb, hnp, hcp2⟩

/-- `le0 M a b`（`a < b`）から最初の行0の子 `c`: `nextrel0 M a c` かつ `le0 M c b`。 -/
private theorem le0_first_child_er (M : PS) {a b : ℕ}
    (h : le0 M a b = true) (hab : a < b) :
    ∃ c, nextrel0 M a c = true ∧ le0 M c b = true := by
  have hh := h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨_, hbL⟩, haux⟩ := hh
  obtain ⟨c, hnc, _, hcaux⟩ := le0Aux_first_er M (Lng M) a b haux hab
  obtain ⟨_, _, hcL⟩ := nextrel0_lt_er hnc
  refine ⟨c, hnc, ?_⟩
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hcL, hbL⟩, hcaux⟩

/-- `nextR M 0 p k` から行0の親一意性で `hasParent M 0 k`。 -/
private theorem hasParent0_of_nextR0_er (M : PS) (p k : ℕ)
    (hp : nextR M 0 p k = true) : hasParent M 0 k = true :=
  (hasParent_iff_unique_fseq M 0 k).mpr
    ⟨p, hp, fun q hq => row0_parent_unique M q p k hq hp⟩

/-! ## 2. `e1x_child_is_FN` の Lean 版（アンカーの子 = ある枝頭） -/

/-- Isabelle `e1x_child_is_FN` (wip:97622): `TrMax S = 0` の単項切片 `S` で、アンカー 0 の
行0の子 `c`（`c ≤ Lng S - 1`）は `FirstNodes` のどれかに一致する。 -/
private theorem child_is_FN_er (S : PS) (c : ℕ)
    (hST : TPS S) (hmono : monoT S = true) (tr0 : TrMax S = 0)
    (nr : nextrel0 S 0 c = true) (cL : c ≤ Lng S - 1) :
    ∃ J, J < (Br S).length ∧ (FirstNodes S).getD J 0 = c := by
  obtain ⟨hcpos, _, _⟩ := nextrel0_lt_er nr
  have trc : TrMax S < c := by rw [tr0]; exact hcpos
  obtain ⟨J, hJBr, hleFN⟩ := branch_component_le0 S c hST hmono trc cL
  have hfge1 : 1 ≤ (FirstNodes S).getD J 0 := by
    rw [FirstNodes_getD S J hJBr, tr0]; omega
  have hle0 : le0 S ((FirstNodes S).getD J 0) c = true := by simpa [leR] using hleFN
  have hfle : (FirstNodes S).getD J 0 ≤ c := le0_le_er hle0
  have hfeq : (FirstNodes S).getD J 0 = c := by
    by_contra hfne
    have hflt : (FirstNodes S).getD J 0 < c := lt_of_le_of_ne hfle hfne
    have hlt2 : entry S 0 ((FirstNodes S).getD J 0) < entry S 0 c :=
      ancestor_basic_1 S ((FirstNodes S).getD J 0) c c hST hflt (le_refl c) hleFN
    have hge : entry S 0 c ≤ entry S 0 ((FirstNodes S).getD J 0) :=
      nextrel0_valley_er nr (by omega) hflt
    omega
  exact ⟨J, hJBr, hfeq⟩

/-! ## 3. 残差 `e1x_ineq_nonanc` の討伐（house pattern: vocab の Prop を TYPE に） -/

theorem e1x_ineq_nonanc : e1x_ineq_nonanc_Prop := by
  intro M hST _hmono hp j1gt nonanc
  obtain ⟨jm2lt, e1jm2lt, le0j1⟩ := s84c1_jm2_basic M hp
  by_contra hcon
  rw [not_lt] at hcon
  set jm2 := s84x_jm2 M with hjm2def
  set j1 := Lng M - 1 with hj1def
  -- 基本パラメータ
  have jm2L : jm2 < Lng M := by
    have h := le0j1
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have j1L : j1 < Lng M := by omega
  have leR0 : leR M 0 jm2 j1 = true := by simpa [leR] using le0j1
  -- RedCondA
  have condA : RedCondA M = true := (RTPS_condAB M (STPS_RTPS M hST)).1
  have condA' : ∀ i, i < 2 → ∀ j, j < Lng M →
      (!hasParent M i j || decide (entry M i (parent M i j) + 1 = entry M i j)) = true := by
    intro i hi j hj
    have h := condA
    simp only [RedCondA, List.all_eq_true, List.mem_range] at h
    exact h i hi j hj
  have condA_row0 : ∀ k, k < Lng M → hasParent M 0 k = true → parent M 0 k = jm2 →
      entry M 0 k = entry M 0 jm2 + 1 := by
    intro k hkL hhas hpar
    have hb := condA' 0 (by norm_num) k hkL
    rw [hhas] at hb
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hb
    rw [hpar] at hb
    omega
  -- アンカー切片 S = seg M jm2 j1、単項性・降順性
  obtain ⟨monoS, descS⟩ := standard_slice_Br_descending M jm2 j1 hST jm2lt hj1def.le leR0
  set S := seg M jm2 j1 with hSdef
  have hLS : Lng S = j1 + 1 - jm2 := by rw [hSdef]; exact length_seg M jm2 j1
  have SL2 : 1 < Lng S := by rw [hLS]; omega
  have SL0 : 0 < Lng S := by omega
  have ST : TPS S := List.ne_nil_of_length_pos SL0
  have eS : ∀ i k, k < Lng S → entry S i k = entry M i (jm2 + k) := by
    intro i k hk
    have hk' : k < Lng (seg M jm2 j1) := by rw [← hSdef]; exact hk
    rw [hSdef]; exact entry_seg M jm2 j1 i k hk'
  have eS10 : entry S 1 0 = entry M 1 jm2 := by
    have := eS 1 0 SL0; simpa using this
  have eS11 : entry S 1 1 = entry M 1 (jm2 + 1) := by
    have := eS 1 1 SL2; simpa using this
  -- 行0辺の子 a（非祖先なので a > jm2+1）
  have nr0adj : nextrel0 M jm2 (jm2 + 1) = true := c3cx_nextrel0_adj_of_le0 M le0j1 jm2lt
  obtain ⟨a, hnc, le0aj1⟩ := le0_first_child_er M le0j1 jm2lt
  obtain ⟨hjm2a, he0lt, haL⟩ := nextrel0_lt_er hnc
  have aleJ1 : a ≤ j1 := le0_le_er le0aj1
  have hane : a ≠ jm2 + 1 := by
    intro heq
    rw [heq] at le0aj1
    rw [nonanc] at le0aj1
    exact absurd le0aj1 (by decide)
  have hjm2p1a : jm2 + 1 < a := by omega
  have hjm2p1L : jm2 + 1 < Lng M := by omega
  -- 親と RedCondA による行0 head 一致
  have hnR0 : nextR M 0 jm2 a = true := by simpa [nextR] using hnc
  have hnR0adj : nextR M 0 jm2 (jm2 + 1) = true := by simpa [nextR] using nr0adj
  have hpar_a : parent M 0 a = jm2 := parent_eq_of_nextR0 M jm2 a hnR0
  have hhas_a : hasParent M 0 a = true := hasParent0_of_nextR0_er M jm2 a hnR0
  have e0a : entry M 0 a = entry M 0 jm2 + 1 := condA_row0 a haL hhas_a hpar_a
  have hpar_p1 : parent M 0 (jm2 + 1) = jm2 := parent_eq_of_nextR0 M jm2 (jm2 + 1) hnR0adj
  have hhas_p1 : hasParent M 0 (jm2 + 1) = true := hasParent0_of_nextR0_er M jm2 (jm2 + 1) hnR0adj
  have e0p1 : entry M 0 (jm2 + 1) = entry M 0 jm2 + 1 := condA_row0 (jm2 + 1) hjm2p1L hhas_p1 hpar_p1
  -- `asm` が最初の幹 step を殺す: TrMax S = 0
  have TrMax0 : TrMax S = 0 := by
    by_contra htr
    have h0 : 0 < TrMax S := Nat.pos_of_ne_zero htr
    have hstep := TrMax_trunk_step S 0 ST h0
    have hnr1 : nextrel1 S 0 1 = true := by simpa [nextR] using hstep
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hnr1
    have he : entry S 1 0 < entry S 1 1 := hnr1.1.1.2
    rw [eS10, eS11] at he
    omega
  -- Br S 非空
  have BrSne : Br S ≠ [] := by
    have hne : ¬ (TrMax S = Lng S - 1) := by rw [TrMax0]; omega
    rw [Br, if_neg hne]
    exact P_nonempty _
  have Br0L : 0 < (Br S).length := List.length_pos_of_ne_nil BrSne
  -- a の S 内添字 a - jm2
  have cLng : a - jm2 < Lng S := by rw [hLS]; omega
  have jaeq : jm2 + (a - jm2) = a := by omega
  have eS0a : entry S 0 (a - jm2) = entry M 0 a := by
    have := eS 0 (a - jm2) cLng; rw [jaeq] at this; exact this
  -- a - jm2 は S のアンカー 0 の行0の子
  have nr0S : nextrel0 S 0 (a - jm2) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨SL0, cLng⟩, by omega⟩, ?_⟩, ?_⟩
    · have h00 : entry S 0 0 = entry M 0 jm2 := by have := eS 0 0 SL0; simpa using this
      rw [h00, eS0a]; exact he0lt
    · intro x hx
      by_cases hx0 : 0 < x
      · rw [decide_eq_true hx0]
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
        have hxL : x < Lng S := lt_trans hx cLng
        have h0x : entry S 0 x = entry M 0 (jm2 + x) := eS 0 x hxL
        rw [eS0a, h0x]
        exact nextrel0_valley_er hnc (by omega) (by omega)
      · have : x = 0 := by omega
        subst this; simp
  -- FirstNodes 0 = 1、a - jm2 = FirstNodes Ja
  have FN0 : (FirstNodes S).getD 0 0 = 1 := by
    rw [FirstNodes_getD S 0 Br0L, TrMax0]
    have hz : (IdxSum (Br S)).getD 0 0 = 0 := by simpa using idxSum_getD (Br S) 0 (Nat.zero_le _)
    rw [hz]
  obtain ⟨Ja, JaBr, FNa⟩ := child_is_FN_er S (a - jm2) ST monoS TrMax0 nr0S (by omega)
  -- 2 枝 head の値
  have eF0_0 : entry ((Br S).getD 0 []) 0 0 = entry M 0 (jm2 + 1) := by
    have h := entry_FirstNodes_eq_component_mr S 0 0 ST Br0L
    rw [FN0] at h
    rw [← h]; have := eS 0 1 SL2; simpa using this
  have eF0_1 : entry ((Br S).getD 0 []) 1 0 = entry M 1 (jm2 + 1) := by
    have h := entry_FirstNodes_eq_component_mr S 0 1 ST Br0L
    rw [FN0] at h
    rw [← h]; exact eS11
  have eFa_0 : entry ((Br S).getD Ja []) 0 0 = entry M 0 a := by
    have h := entry_FirstNodes_eq_component_mr S Ja 0 ST JaBr
    rw [FNa] at h
    rw [← h]; exact eS0a
  have eFa_1 : entry ((Br S).getD Ja []) 1 0 = entry M 1 a := by
    have h := entry_FirstNodes_eq_component_mr S Ja 1 ST JaBr
    rw [FNa] at h
    rw [← h]; have := eS 1 (a - jm2) cLng; rw [jaeq] at this; exact this
  -- 行0 head 一致 + descending の行1 tie-break
  have row0eq : entry ((Br S).getD 0 []) 0 0 = entry ((Br S).getD Ja []) 0 0 := by
    rw [eF0_0, eFa_0, e0p1, e0a]
  have cdomJ : cdom ((Br S).getD 0 []) ((Br S).getD Ja []) :=
    descendingD descS (Nat.zero_le Ja) JaBr
  have e1a_le : entry M 1 a ≤ entry M 1 (jm2 + 1) := by
    have hcdom := cdomJ.2 row0eq
    rw [eFa_1, eF0_1] at hcdom
    exact hcdom
  -- nextrel1 M jm2 j1 の valley
  have e1a_ge : entry M 1 j1 ≤ entry M 1 a := by
    have h := s84c1_jm2_univ M hp hjm2a le0aj1
    rw [hj1def]; exact h
  omega

/-! ## 4. `E1GE` 両枝を無条件化（RUN 脚の解禁） -/

/-- Isabelle `e1x_e1ge_uncond` (wip:97869): 残差を注入して無条件化。 -/
theorem e1x_e1ge_uncond (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (j1gt : 1 < Lng M - 1) :
    entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1) :=
  e1x_e1ge_uncond_of_ineq e1x_ineq_nonanc M hST hmono hp j1gt

#print axioms e1x_ineq_nonanc
#print axioms e1x_e1ge_uncond

end PSS
