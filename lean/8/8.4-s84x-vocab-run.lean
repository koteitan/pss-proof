import PSS.Adm
import «5».«5.1-ancestor-basic»
import «5».«5.1-parent-exists»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.7-standard-reduced»

/-!
# §8.4 共有語彙 `s84x_*` ＋ RUN 脚（`M0RUN` / `E1GE`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）の
  共通 setup。この節が使う「記事局所の列」を露出する。
- Isabelle 対応（すべて `isabelle/layerB/pss_wip.thy`）:
  * `s84x_jm2` (:52620) = `parent M 1 (Lng M - 1)`（行1の親 `j₋₂`）。
  * `s84x_jm3` (:52623) = `Adm M (s84x_jm2 M)`（`j₋₃`）。
  * `s84x_N`  (:52626) = `seg M (s84x_jm3 M) (Lng M - 1)`。
  * `s84x_Np` (:52629) = `seg M (s84x_jm2 M) (Lng M - 1)`。
  （`s84x_L`/`s84x_Lp`/`s84x_s1`/`s84x_b1` は RUN 脚が使わないので本ファイルでは
  定義しない。次 wave の scb 分解クラスタが導入する。）

- RUN 脚（`oi5_IIIIV_pkg` scratch:1213 が discharge する 3 束のうち RUN）:
  1. `s84c1_nextR1_jm2` (:52672) / `s84c1_jm2_basic` (:52676) / `s84c1_jm2_univ`
     (:52691): 行1の親辺 `nextrel1 M j₋₂ (Lng M - 1)` とその 3 事実＋普遍節。
     エンジン = 行 `i` 一般の親証拠 `nextR_parent_witness` (:49253) の Lean 版
     (`nextR_parent_sv`、`8.1-Trans-fseq-condI` の `nextR_parent_ci` と同型)。
  2. `c3cx_nextrel0_adj_of_le0` (:93321) / `c3cx_M0RUN_of_a` (:93354): 行0の隣接辺と
     `M0RUN`（`nextR M 1 j₋₂ (j₋₂+1)`）。Isabelle は `le0` を rtrancl として peel するが、
     Lean は fuel 版 `le0` の**値特徴付け**（`ancestor_basic_1` / `parent_exists_3`、§5.1）
     で置き換えた（`le0` の第1辺の peel が不要）。valley は `le0` の添字単調性
     （`le0_le_sv`、`5.1` の `le0_index_mono` の再掲）で `k = j₋₂+1` に潰れる。
  3. `wgx37_m0run_ineq_of_e1ge` (:96916) / `wgx37_m0run_of_e1ge` (:96930):
     `E1GE ⟹ (i) ⟹ M0RUN`。**無条件に閉じた**（`wgx37_m0run_of_e1ge`）。
  4. `wgx37_e1ge_of_anc` (:96958): `E1GE` の祖先枝（FREE、`s84c1_jm2_univ` 一発）。
  5. `e1x_e1ge_uncond` (:97869): 祖先枝＝(4)、非祖先枝＝`e1x_ineq_nonanc` (:97657)
     ＋ RedCondA ランプ。**非祖先枝の値不等式 `e1x_ineq_nonanc` は本 wave では未移植**
     （§8.4 の切片 `descending`／`FirstNodes`／`cdom` を要する ~200 行、依存に
     `m_6_8_standard_slice_Br_descending` 等）。本ファイルは `e1x_e1ge_uncond` を
     その残差 Prop `e1x_ineq_nonanc_Prop` に**縮約**する drop-in（`e1x_e1ge_uncond_of_ineq`）
     を banked。祖先枝と RedCondA ランプ（`RTPS_condAB` (§6.6) 経由）は discharge 済み。

- 依存（すべてビルド済み・committed）: `PSS.Adm`（`parent`/`seg`/`entry`/`le0`/`nextR`/
  `nextrel0`/`nextrel1`/`hasParent`/`Adm`）、«5».«5.1-ancestor-basic»（`ancestor_basic_1`）、
  «5».«5.1-parent-exists»（`parent_exists_3`）、«6».«6.6-reduced-iff-condAB»（`RTPS_condAB`）、
  «6».«6.7-standard-reduced»（`STPS`/`STPS_RTPS`）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  無条件に閉じた: `wgx37_m0run_of_e1ge` ＋ その下流 brick 群。
  残差: `e1x_ineq_nonanc_Prop`（非祖先枝の値不等式、次 wave）。

- Private helper suffix: `_sv`。
-/

namespace PSS

/-! ## 1. §8.4 共有語彙の定義（`isabelle/layerB/pss_wip.thy`:52620–52629 と 1:1） -/

/-- Isabelle `s84x_jm2` (wip:52620): 行1における最終列 `j₁ = Lng M - 1` の親 `j₋₂`。 -/
def s84x_jm2 (M : PS) : ℕ := parent M 1 (Lng M - 1)

/-- Isabelle `s84x_jm3` (wip:52623): `j₋₂` の許容化 `j₋₃`。 -/
def s84x_jm3 (M : PS) : ℕ := Adm M (s84x_jm2 M)

/-- Isabelle `s84x_N` (wip:52626): 切片 `(M_j)_{j=j₋₃}^{j₁}`。 -/
def s84x_N (M : PS) : PS := seg M (s84x_jm3 M) (Lng M - 1)

/-- Isabelle `s84x_Np` (wip:52629): 切片 `(M_j)_{j=j₋₂}^{j₁}`。 -/
def s84x_Np (M : PS) : PS := seg M (s84x_jm2 M) (Lng M - 1)

/-! ## 2. 小補題（§5.1 private の再掲、suffix `_sv`） -/

/-- Isabelle `nextR_parent_witness` (wip:49253) の行 `i` 一般版。
`8.1-Trans-fseq-condI` の private `nextR_parent_ci` と同型。 -/
private theorem nextR_parent_sv (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) : nextR M i (parent M i j₁) j₁ = true := by
  unfold hasParent at hp
  unfold parent
  have hlen : (parents M i j₁).length = 1 := by simpa using hp
  match hm : parents M i j₁ with
  | [] => rw [hm] at hlen; simp at hlen
  | x :: xs =>
      have hx : x ∈ parents M i j₁ := by rw [hm]; simp
      have := List.of_mem_filter (l := List.range (Lng M))
        (p := fun j₀ => nextR M i j₀ j₁) (by simpa [parents] using hx)
      simpa [hm] using this

/-- `le0` の添字単調性（§5.1 の private `le0_index_mono` の再掲）。 -/
private theorem le0Aux_le_sv {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero => simp [le0Aux] at h; omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, hjb, _, haj⟩
      · omega
      · exact (ih haj).trans (Nat.le_of_lt hjb)

private theorem le0_le_sv {M : PS} {a b : ℕ}
    (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_le_sv h.2

/-- `le0 M a b` は始点が範囲内なので `M` は空でない。 -/
private theorem TPS_of_le0_sv {M : PS} {a b : ℕ} (h : le0 M a b = true) : TPS M := by
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
  have haL : a < Lng M := h.1.1
  intro hnil; rw [hnil] at haL; simp [Lng] at haL

/-! ## 3. 行1の親辺（Isabelle `s84c1_*`） -/

/-- Isabelle `s84c1_nextR1_jm2` (wip:52672)。 -/
theorem s84c1_nextR1_jm2 (M : PS) (hp : hasParent M 1 (Lng M - 1) = true) :
    nextR M 1 (s84x_jm2 M) (Lng M - 1) = true := by
  have h := nextR_parent_sv M 1 (Lng M - 1) hp
  simpa [s84x_jm2] using h

/-- Isabelle `s84c1_jm2_basic` (wip:52676): 行1の親 `j₋₂` の 3 基本事実。 -/
theorem s84c1_jm2_basic (M : PS) (hp : hasParent M 1 (Lng M - 1) = true) :
    s84x_jm2 M < Lng M - 1 ∧
    entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) ∧
    le0 M (s84x_jm2 M) (Lng M - 1) = true := by
  have hn : nextrel1 M (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [nextR] using s84c1_nextR1_jm2 M hp
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨_, _⟩, hC⟩, hD⟩, hE⟩, _⟩ := hn
  exact ⟨hC, hD, hE⟩

/-- Isabelle `s84c1_jm2_univ` (wip:52691): 行1の親辺の普遍節。
`j > j₋₂` かつ `(0,j) ≤_M (0,j₁)` なら `M_{1,j} ≥ M_{1,j₁}`。 -/
theorem s84c1_jm2_univ (M : PS) (hp : hasParent M 1 (Lng M - 1) = true)
    {j : ℕ} (jgt : s84x_jm2 M < j) (jle : le0 M j (Lng M - 1) = true) :
    entry M 1 (Lng M - 1) ≤ entry M 1 j := by
  have hn : nextrel1 M (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [nextR] using s84c1_nextR1_jm2 M hp
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hn
  obtain ⟨_, hF⟩ := hn
  have hjL : j < Lng M := by
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at jle
    exact jle.1.1
  have hbody := hF j (List.mem_range.mpr hjL)
  have h1 : decide (s84x_jm2 M < j) = true := by simp [jgt]
  rw [h1, jle] at hbody
  simp only [Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
  exact hbody

/-! ## 4. 行0の隣接辺と `M0RUN`（Isabelle `c3cx_*`） -/

/-- Isabelle `c3cx_nextrel0_adj_of_le0` (wip:93321): `le0 M a b`（`a < b`）から
行0の隣接辺 `nextrel0 M a (a+1)`。**Lean は値特徴付けで書く**: `a+1 ≤ b` なので
`ancestor_basic_1` が `entry M 0 a < entry M 0 (a+1)` を出し、valley は空虚。 -/
theorem c3cx_nextrel0_adj_of_le0 (M : PS) {a b : ℕ}
    (hle : le0 M a b = true) (hlt : a < b) :
    nextrel0 M a (a + 1) = true := by
  have hM : TPS M := TPS_of_le0_sv hle
  have hh := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haL : a < Lng M := hh.1.1
  have hbL : b < Lng M := hh.1.2
  have ha1b : a + 1 ≤ b := hlt
  have ha1L : a + 1 < Lng M := lt_of_le_of_lt ha1b hbL
  have hleR : leR M 0 a b = true := by simpa [leR] using hle
  have hgrow : entry M 0 a < entry M 0 (a + 1) :=
    ancestor_basic_1 M a (a + 1) b hM (Nat.lt_succ_self a) ha1b hleR
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨haL, ha1L⟩, Nat.lt_succ_self a⟩, hgrow⟩, ?_⟩
  intro j hj
  have hjlt : j < a + 1 := List.mem_range.mp hj
  have hnaj : ¬ (a < j) := by omega
  simp [hnaj]

/-- Isabelle `c3cx_M0RUN_of_a` (wip:93354): 単一の行1不等式 `(i)` から `M0RUN`。 -/
theorem c3cx_M0RUN_of_a (M : PS) (hp : hasParent M 1 (Lng M - 1) = true)
    (A : entry M 1 (s84x_jm2 M) < entry M 1 (s84x_jm2 M + 1)) :
    nextR M 1 (s84x_jm2 M) (s84x_jm2 M + 1) = true := by
  obtain ⟨jm2lt, -, le0j1⟩ := s84c1_jm2_basic M hp
  -- (ii): 行0の後続辺
  have nr0 : nextrel0 M (s84x_jm2 M) (s84x_jm2 M + 1) = true :=
    c3cx_nextrel0_adj_of_le0 M le0j1 jm2lt
  have hh := nr0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have jm2L : s84x_jm2 M < Lng M := hh.1.1.1.1
  have jm2p1L : s84x_jm2 M + 1 < Lng M := hh.1.1.1.2
  have hgrow : entry M 0 (s84x_jm2 M) < entry M 0 (s84x_jm2 M + 1) := hh.1.2
  have hM : TPS M := TPS_of_le0_sv le0j1
  -- le0 M j₋₂ (j₋₂+1)（値特徴付け）
  have le0adj : le0 M (s84x_jm2 M) (s84x_jm2 M + 1) = true := by
    have hlr : leR M 0 (s84x_jm2 M) (s84x_jm2 M + 1) = true :=
      parent_exists_3 M (s84x_jm2 M) (s84x_jm2 M + 1) hM (Nat.lt_succ_self _) jm2p1L
        (fun j hj hj2 => by
          have hje : j = s84x_jm2 M + 1 := by omega
          rw [hje]; exact hgrow)
    simpa [leR] using hlr
  -- (iii): 行1の valley は `k = j₋₂+1` に潰れる
  have valley : ∀ k, s84x_jm2 M < k → le0 M k (s84x_jm2 M + 1) = true →
      entry M 1 (s84x_jm2 M + 1) ≤ entry M 1 k := by
    intro k hk hkle
    have : k = s84x_jm2 M + 1 := by
      have := le0_le_sv hkle; omega
    rw [this]
  -- 組み立て
  have goalnr1 : nextrel1 M (s84x_jm2 M) (s84x_jm2 M + 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨jm2L, jm2p1L⟩, Nat.lt_succ_self _⟩, A⟩, le0adj⟩, ?_⟩
    intro j hj
    cases hc : (decide (s84x_jm2 M < j) && le0 M j (s84x_jm2 M + 1)) with
    | false => simp
    | true =>
        have hc' := hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact valley j hc'.1 hc'.2
  simpa [nextR] using goalnr1

/-! ## 5. RUN 脚: `E1GE ⟹ M0RUN`（Isabelle `wgx37_*`） -/

/-- Isabelle `wgx37_m0run_ineq_of_e1ge` (wip:96916): `E1GE` から単一不等式 `(i)`。 -/
theorem wgx37_m0run_ineq_of_e1ge (M : PS) (hp : hasParent M 1 (Lng M - 1) = true)
    (e1ge : entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1)) :
    entry M 1 (s84x_jm2 M) < entry M 1 (s84x_jm2 M + 1) := by
  have h := (s84c1_jm2_basic M hp).2.1
  omega

/-- Isabelle `wgx37_m0run_of_e1ge` (wip:96930): `E1GE ⟹ M0RUN`。**無条件クローズ**。 -/
theorem wgx37_m0run_of_e1ge (M : PS) (hp : hasParent M 1 (Lng M - 1) = true)
    (e1ge : entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1)) :
    nextR M 1 (s84x_jm2 M) (s84x_jm2 M + 1) = true :=
  c3cx_M0RUN_of_a M hp (wgx37_m0run_ineq_of_e1ge M hp e1ge)

/-- Isabelle `wgx37_e1ge_of_anc` (wip:96958): `E1GE` の祖先枝は FREE。 -/
theorem wgx37_e1ge_of_anc (M : PS) (hp : hasParent M 1 (Lng M - 1) = true)
    (anc : le0 M (s84x_jm2 M + 1) (Lng M - 1) = true) :
    entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1) :=
  s84c1_jm2_univ M hp (Nat.lt_succ_self _) anc

/-! ## 6. `e1x_e1ge_uncond` の縮約（残差 = 非祖先枝の値不等式） -/

/-- Isabelle `e1x_ineq_nonanc` (wip:97657) を Lean の語彙に写した残差 Prop。
非祖先枝（`¬ le0 M (j₋₂+1) j₁`）での単一不等式。§8.4 の切片 `descending`/
`FirstNodes`/`cdom` を要する ~200 行で、依存に `m_6_8_standard_slice_Br_descending`
（Lean: `6.8-standard-slice-Br-descending`）等。本 wave では未移植＝次 wave の残差。 -/
def e1x_ineq_nonanc_Prop : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → le0 M (s84x_jm2 M + 1) (Lng M - 1) = false →
    entry M 1 (s84x_jm2 M) < entry M 1 (s84x_jm2 M + 1)

/-- Isabelle `e1x_e1ge_uncond` (wip:97869) の drop-in（house pattern）。
祖先枝＝`wgx37_e1ge_of_anc`、非祖先枝＝残差 `e1x_ineq_nonanc_Prop` ＋ RedCondA ランプ
（`entry M 1 j₁ = entry M 1 j₋₂ + 1`、`RTPS_condAB` (§6.6) 経由）。 -/
theorem e1x_e1ge_uncond_of_ineq (h : e1x_ineq_nonanc_Prop)
    (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (j1gt : 1 < Lng M - 1) :
    entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1) := by
  cases hanc : le0 M (s84x_jm2 M + 1) (Lng M - 1) with
  | true => exact wgx37_e1ge_of_anc M hp hanc
  | false =>
      have ineq := h M hST hmono hp j1gt hanc
      -- RedCondA ランプ
      have condA : RedCondA M = true := (RTPS_condAB M (STPS_RTPS M hST)).1
      have hLM : Lng M - 1 < Lng M := by omega
      simp only [RedCondA, List.all_eq_true] at condA
      have hbody := condA 1 (by decide) (Lng M - 1) (List.mem_range.mpr hLM)
      rw [hp] at hbody
      simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
      -- `s84x_jm2 M = parent M 1 (Lng M - 1)`（defeq）
      have ramp : entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) := hbody
      omega

#print axioms s84c1_nextR1_jm2
#print axioms s84c1_jm2_basic
#print axioms s84c1_jm2_univ
#print axioms c3cx_nextrel0_adj_of_le0
#print axioms c3cx_M0RUN_of_a
#print axioms wgx37_m0run_ineq_of_e1ge
#print axioms wgx37_m0run_of_e1ge
#print axioms wgx37_e1ge_of_anc
#print axioms e1x_e1ge_uncond_of_ineq

end PSS
