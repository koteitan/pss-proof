import «5».«5.3-pred-is-oper1»
import «6».«6.2-P-fseq»
import «6».«6.2-P-additivity»
import «6».«6.2-P-components-nonmulti»
import «6».«6.3-admof-slice»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-leftend»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.7-standard-reduced»
import «6».«6.7-standard-P-components»
import «7».«7.1-lessBT-linear-order»
import «7».«7.1-buchholz-fseq-lt»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Trans-preserves-monoT»
import «7».«7.3-two-column»
import «7».«7.3-Pred-Trans-descend»
import «8».«8.2-subexpr-adm0-ctx»
import «8».«8.7-const00-Trans»

/-!
# §8.7 補題（基本列の降下性）

- 原文: `tmp/content.md` 5869（§8.7）。逐語形は `p_8_7_fseq_descend`
  (isabelle/pss_paper.thy:2253)。訂正: なし（A 番号の該当なし）。
- Isabelle: `m_8_7_fseq_descend_dispatcher` (isabelle/layerB/pss_wip.thy:52353)、
  その mono 部 `f7x_fseq_descend_mono` (同 :52051)、
  形状確認 `m_8_7_fseq_descend_of_exchange` (同 :52553)。
- 系: `p_8_3_TransCondII_oper_descend` (pss_paper.thy:1863, article 3958) は
  本項目の系（tree の `8.3-Trans-fseq-condII ⛔8.7-fseq-descend`）。
  dispatcher の条件 (II) 枝そのものなので、同じ仮定から出る。
- 依存（ビルド済みのみ import）: `7.3-Pred-Trans-descend`（`m_7_3_Pred_Trans_descend`）、
  `7.3-two-column`（`two_column_Trans`）、`7.3-Trans-welldefined`
  （`Trans_Mark_multi_equations` ＝ Isabelle `trans_multi_split`、
  `trans_multi_last_component`）、`7.3-Trans-preserves-zeroT`/`-monoT`、
  `7.1-buchholz-fseq-lt`（`buchholz_fseq_lt` ＝ `m_buc1_3_2a_fseq_lt`、
  `addBT_lt_right_bf` ＝ `lessBT_addBT_mono_right`）、`7.1-lessBT-linear-order`、
  `8.2-subexpr-adm0-ctx`（`condII_or_condIV` ＝ `m_8_2_condII_or_condIV`）、
  `8.7-const00-Trans`、`6.7-standard-reduced`/`-P-components`、
  `6.6-reduced-leftend`（`RTPS_mono_head_eq` ＝ `reduced_mono_head_diag`）、
  `6.6-reduced-iff-condAB`（`RTPS_condAB`）、`6.6-P-condAB`
  （`mono_hasParent_row0` ＝ `monoT_hasParent0_last`）、`6.2-P-fseq`
  （`P_concat`/`P_last_multi`/`parent_ge_Pcut`/`nextR_implies_row0`）、
  `6.2-P-additivity`（`P_nonmulti_eq` ＝ `poper_P_nonmulti`）、
  `6.2-P-components-nonmulti`、`6.3-admof-slice`（`adm_zero` ＝ `f7x_adm_zero`）、
  `5.3-pred-is-oper1`（`pred_is_oper1` ＝ `m_8_4_oper1_eq_Pred`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  7 本の交換則 ＋ 未移植 brick を名前付き `Prop` として露出し、そこから
  dispatcher と逐語形を証明する。露出した `Prop` は全 16 本（`FseqDesc_*`）。
  **全 16 本は標準形プール（`diagSeq` を基本列で閉じた 81 本）上で `#guard`
  数値検証済み**＝空虚ではない。Isabelle 側では全て証明済みなので、移植すれば
  そのまま外れる。

## 自前で証明した Isabelle brick（`Prop` にしていない）

`f7x_multBT_lessBT_principal` / `f7x_lessBT_D00_imp_zero` / `f7x_Dpow_lessBT_Dpt` /
`f7x_parent_one_zero` / `f7x_concat_map_singleton` / `m_6_7_ST_eq_Union_SkT` の
`⟹` 向き / `m_8_1_Trans_fseq_condI_descent` / `m_8_1_condI_oper_pow_j0zero` の
`Lng M = 2` 特殊化（`oper_len2_fd` で `oper` を直接計算）。
-/

namespace PSS

/-! ## 七つの交換則 -/

/-- Isabelle `TOT`。 -/
def FseqDesc_Trans_preserves_OT : Prop :=
  ∀ N : PS, STPS N → monoT N = true → 1 < Lng N - 1 → Trans N ∈ OT_B

/-- Isabelle `exchI`。 -/
def FseqDesc_exchI : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondI N = true → 0 < parent N 0 (Lng N - 1) → 1 < m →
    Trans (oper N m) = operB (Trans N) (numBT (m - 1))

/-- Isabelle `exchII`。 -/
def FseqDesc_exchII : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondII N = true → 1 < m →
    ∃ k, Trans (oper N m) = operB (Trans N) (numBT k)

/-- Isabelle `exchIII`。 -/
def FseqDesc_exchIII : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondIII N = true → 1 < m →
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true

/-- Isabelle `exchIV`。 -/
def FseqDesc_exchIV : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondIV N = true → 1 < m →
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true

/-- Isabelle `exchV`。 -/
def FseqDesc_exchV : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondV N = true → 1 < m →
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true

/-- Isabelle `exchVI`。 -/
def FseqDesc_exchVI : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondVI N = true → 1 < m →
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true

/-! ## 未移植 brick（Isabelle 名 1:1、GREEN-MODULO の仮定） -/

/-- Isabelle `operI_j0zero_trans_mult` (pss_wip.thy:36977)。 -/
def FseqDesc_operI_j0zero_trans_mult : Prop :=
  ∀ (M : PS) (k : ℕ), RTPS M → hasParent M 0 (Lng M - 1) = true →
    entry M 1 (Lng M - 1) = 0 → parent M 0 (Lng M - 1) = 0 → 1 < Lng M - 1 →
    Trans (oper M (k + 1)) = multBT (Trans (Pred M)) (k + 1)

/-- Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause1` (pss_wip.thy:19436)。 -/
def FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1 : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transJm1 M = 0 →
    (transCondI M = true ∨ transCondIII M = true ∨ transCondV M = true) →
    ∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t₁ (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero))

/-- Isabelle `m_8_6_rcseq_Trans` (pss_wip.thy:14299)。
`rcseq u j₁ = map (λj. (u+j, u)) [0..<j₁+1]`、`Dpow u k = (D_u)^k 0_B`。 -/
def FseqDesc_m_8_6_rcseq_Trans : Prop :=
  ∀ u j₁ : ℕ,
    Trans ((List.range (j₁ + 1)).map (fun j => (u + j, u)))
      = if j₁ = 0 ∧ u = 0 then BZero
        else (fun a => Dprin (u : ℕ∞) a)^[j₁ + 1] BZero

/-- Isabelle `m_8_3_TransCondII_oper_descend_engine` (pss_wip.thy:28563)。 -/
def FseqDesc_m_8_3_TransCondII_oper_descend_engine : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondII M = true → 0 < n → Trans M ∈ OT_B →
    (1 < n → ∃ k, Trans (oper M n) = operB (Trans M) (numBT k)) →
    lessBT (Trans (oper M n)) (Trans M) = true

/-- Isabelle `m_8_5_TransCondV_oper_descend_engine` (pss_wip.thy:37496)。 -/
def FseqDesc_m_8_5_TransCondV_oper_descend_engine : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondV M = true → 0 < n → Trans M ∈ OT_B →
    (1 < n → ∃ k, leBT (Trans (oper M n)) (operB (Trans M) (numBT k)) = true) →
    lessBT (Trans (oper M n)) (Trans M) = true

/-- Isabelle `m_8_6_TransCondVI_oper_descend_engine` (pss_wip.thy:40250)。 -/
def FseqDesc_m_8_6_TransCondVI_oper_descend_engine : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → 1 < Lng M - 1 →
    transCondVI M = true → 0 < n → Trans M ∈ OT_B →
    (1 < n → ∃ k, leBT (Trans (oper M n)) (operB (Trans M) (numBT k)) = true) →
    lessBT (Trans (oper M n)) (Trans M) = true

/-- Isabelle `m_6_2_P_oper_2` (pss_mechanized.thy:2539)。 -/
def FseqDesc_m_6_2_P_oper_2 : Prop :=
  ∀ (M : PS) (n : ℕ), TPS M → 1 ≤ n → 1 < Lng ((P M).getLastD []) →
    oper M n = (P M).dropLast.flatten ++ oper ((P M).getLastD []) n ∧
      P (oper M n) = (P M).dropLast ++ P (oper ((P M).getLastD []) n)

/-- Isabelle `f7x_Trans_append_Pblocks` (pss_wip.thy:51888)。 -/
def FseqDesc_f7x_Trans_append_Pblocks : Prop :=
  ∀ A N : PS, RTPS (A ++ N) → RTPS N → P (A ++ N) = P A ++ P N →
    Trans (A ++ N) = addBT (Trans A)
      (if (P N).getD 0 [] = [(0, 0)] then addBT (Dprin 0 BZero) (Trans N)
       else Trans N)

/-- Isabelle `m_7_3_Trans_leftmost` (pss_wip.thy:16569) の (2)。 -/
def FseqDesc_m_7_3_Trans_leftmost_2 : Prop :=
  ∀ M : PS, RTPS M → (P M).getD 0 [] ≠ [(0, 0)] →
    (PB (Trans M)).getD 0 BZero = Trans ((P M).getD 0 []) ∧
      bpHeadV (Trans M) = (entry M 1 0 : ℕ∞)

/-! ## 小さな Buchholz 補題（自前で証明する） -/

/-- Isabelle `multBT_Trm_single`: `(Trm [p]) ×_B m = Trm (replicate m p)`。 -/
private theorem multBT_single_fd (p : BP) (m : ℕ) :
    multBT (.trm [p]) m = .trm (List.replicate m p) := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [multBT, ih]
      simp [addBT, List.replicate_succ']

/-- Isabelle `f7x_multBT_lessBT_principal` (pss_wip.thy:51801)。 -/
private theorem multBT_lessBT_principal_fd {p q : BP} (hpq : lessBP p q = true)
    (m : ℕ) : lessBT (multBT (.trm [p]) m) (.trm [q]) = true := by
  rw [multBT_single_fd]
  cases m with
  | zero => simp [lessBT, lessBPList]
  | succ k => simp [List.replicate_succ, lessBT, lessBPList, hpq]

/-- `0_B` は `lessBT` の最小元。 -/
private theorem lessBPList_nil_right_fd (xs : List BP) :
    lessBPList xs [] = false := by cases xs <;> rfl

private theorem lessBT_BZero_fd (t : BT) : lessBT t BZero = false := by
  rcases t with ⟨ps⟩
  simpa [BZero, lessBT] using lessBPList_nil_right_fd ps

/-- Isabelle `f7x_lessBT_D00_imp_zero` (pss_wip.thy:51828):
`D₀ 0` より真に小さい項は `0_B` のみ。 -/
private theorem lessBT_D00_imp_zero_fd {t : BT}
    (hlt : lessBT t (Dprin 0 BZero) = true) : t = BZero := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => rfl
  | cons p rest =>
      exfalso
      rcases p with ⟨w, c⟩
      have hz : ¬ (w < (0 : ℕ∞)) := by simp
      simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, lessBT_BZero_fd c,
        lessBPList_nil_right_fd rest] at hlt
      rcases hlt with (hlt | hlt) | hlt
      · exact hz hlt
      · exact Bool.noConfusion hlt.2
      · exact Bool.noConfusion hlt.2

/-- Isabelle `f7x_Dpow_lessBT_Dpt` (pss_wip.thy:51815):
`u < v` なら `D_u^m 0 < D_v c`。 -/
private theorem Dpow_lessBT_Dprin_fd {u v : ℕ} (huv : u < v) (c : BT) (m : ℕ) :
    lessBT ((fun a => Dprin (u : ℕ∞) a)^[m] BZero) (Dprin (v : ℕ∞) c) = true := by
  cases m with
  | zero => simp [BZero, Dprin, lessBT, lessBPList]
  | succ k =>
      rw [Function.iterate_succ_apply']
      have hlt : ((u : ℕ∞) < (v : ℕ∞)) := by exact_mod_cast huv
      simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true]
      exact Or.inl (Or.inl (decide_eq_true hlt))

/-- `leBT` と `lessBT` の連結。 -/
private theorem leBT_lessBT_trans_fd {a b c : BT} (hab : leBT a b = true)
    (hbc : lessBT b c = true) : lessBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab
  rcases hab with hab | rfl
  · exact lessBT_linear_trans a b c hab hbc
  · exact hbc

/-- 同じ指標の principal 項は本体の順序を継承する。 -/
private theorem lessBT_Dprin_congr_fd {v : ℕ∞} {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- `0_B` は任意の principal 項より小さい。 -/
private theorem lessBT_BZero_Dprin_fd (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-! ## 親が唯一のときの `parent M i 1 = 0` -/

/-- Isabelle `f7x_parent_one_zero` (pss_wip.thy:51861)。 -/
private theorem parent_one_zero_fd (M : PS) (i : ℕ)
    (hp : hasParent M i 1 = true) : parent M i 1 = 0 := by
  have hmem : parent M i 1 ∈ parents M i 1 := by
    unfold parent
    cases h : parents M i 1 with
    | nil =>
        rw [hasParent, h] at hp
        simp at hp
    | cons a as => simp [List.headD]
  have hmem' : parent M i 1 < Lng M ∧ nextR M i (parent M i 1) 1 = true := by
    simpa [parents, List.mem_filter] using hmem
  have hnext := hmem'.2
  have hlt : parent M i 1 < 1 := by
    unfold nextR at hnext
    by_cases hi : i = 0
    · rw [if_pos hi] at hnext
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnext
      exact hnext.1.1.2
    · rw [if_neg hi] at hnext
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hnext
      exact hnext.1.1.1.2
  omega

/-- 親が唯一なら `parent` は実際に親辺を張る。 -/
private theorem hasParent_nextR_fd (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) : nextR M i (parent M i j₁) j₁ = true := by
  have hmem : parent M i j₁ ∈ parents M i j₁ := by
    unfold parent
    cases h : parents M i j₁ with
    | nil =>
        rw [hasParent, h] at hp
        simp at hp
    | cons a as => simp [List.headD]
  have hmem' : parent M i j₁ < Lng M ∧ nextR M i (parent M i j₁) j₁ = true := by
    simpa [parents, List.mem_filter] using hmem
  exact hmem'.2

/-- 親が唯一なら親辺は `0 <^Next 1`。 -/
private theorem parent_one_nextR_fd (M : PS) (i : ℕ)
    (hp : hasParent M i 1 = true) : nextR M i 0 1 = true := by
  have h := hasParent_nextR_fd M i 1 hp
  rwa [parent_one_zero_fd M i hp] at h

/-! ## `Pred` の基本性質 -/

private theorem Lng_Pred_fd (M : PS) (hL : 1 < Lng M) : Lng (Pred M) = Lng M - 1 := by
  unfold Pred
  rw [if_neg (by omega)]
  simp

private theorem Pred_TPS_fd (M : PS) (hL : 1 < Lng M) : TPS (Pred M) := by
  intro h
  have hz : Lng (Pred M) = 0 := by rw [h]; rfl
  rw [Lng_Pred_fd M hL] at hz
  omega

/-- 行 1 の親辺 `0 <^Next 1` は `M_{1,0} < M_{1,1}` を与える。 -/
private theorem nextR_row1_lt_fd (M : PS) (h : nextR M 1 0 1 = true) :
    entry M 1 0 < entry M 1 1 := by
  rw [nextR, if_neg (by omega)] at h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-! ## 条件 (I)–(VI) の網羅（Isabelle `m_8_2_condII_or_condIV` 経由） -/

private theorem trans_cond_cases_fd (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hL : 1 < Lng M) :
    transCondI M = true ∨ transCondII M = true ∨ transCondIII M = true
      ∨ transCondIV M = true ∨ transCondV M = true ∨ transCondVI M = true := by
  by_cases c1 : transCondI M = true
  · exact Or.inl c1
  by_cases c3 : transCondIII M = true
  · exact Or.inr (Or.inr (Or.inl c3))
  by_cases c5 : transCondV M = true
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c5))))
  by_cases c6 : transCondVI M = true
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c6))))
  have h6 : transCondVI M = false := by
    simpa using c6
  rcases condII_or_condIV M hR hmono hL (by tauto) h6 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ## `oper` の直接計算（Isabelle `oper_def`/`Let_def` の展開に対応） -/

/-- Isabelle `f7x_concat_map_singleton`。 -/
private theorem flatten_map_singleton_fd {α β : Type _} (f : α → β) (l : List α) :
    (l.map (fun a => [f a])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- 末尾が `(0,0)` なら `M[n] = Pred M`。 -/
private theorem oper_of_last_zero_fd (M : PS) (n : ℕ) (hj : Lng M - 1 ≠ 0)
    (h0 : entry M 0 (Lng M - 1) = 0) (h1 : entry M 1 (Lng M - 1) = 0) :
    oper M n = Pred M := by
  unfold oper
  simp [hj, h0, h1]

/-- 段 `i₁` に親がなければ `M[n] = Pred M`。 -/
private theorem oper_of_no_parent_fd (M : PS) (n : ℕ) (hj : Lng M - 1 ≠ 0)
    (hnp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false) :
    oper M n = Pred M := by
  unfold oper
  simp only [hj, if_false, hnp]
  by_cases h0 : entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0
  · simp [h0.1, h0.2]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h0 ⊢
    rw [if_neg (by simpa using h0)]
    simp

/-- `Lng M = 2` かつ末尾に親があるときの `M[n]` の閉形式。
`d₀`/`d₁` は Isabelle の `oper_def` の `Let` 束縛そのもの。 -/
private theorem oper_len2_fd (M : PS) (hL : Lng M = 2)
    (hnz : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0))
    (hp : hasParent M (idx1 M 1) 1 = true) (d0 d1 : ℕ)
    (hd0 : (if 0 < idx1 M 1 then
              entry M 0 1 - entry M 0 (parent M (idx1 M 1) 1) else 0) = d0)
    (hd1 : (if 1 < idx1 M 1 then
              entry M 1 1 - entry M 1 (parent M (idx1 M 1) 1) else 0) = d1)
    (n : ℕ) :
    oper M n =
      (List.range n).map (fun k => (entry M 0 0 + k * d0, entry M 1 0 + k * d1)) := by
  have hj : Lng M - 1 = 1 := by omega
  have hpar : parent M (idx1 M 1) 1 = 0 := parent_one_zero_fd M (idx1 M 1) hp
  unfold oper
  simp only [hj, Nat.one_ne_zero, if_false, hp, Bool.not_true]
  rw [if_neg (by simpa using hnz)]
  simp only [Bool.false_eq_true, if_false, hd0, hd1]
  simp only [hpar, List.take_zero, List.nil_append, Nat.sub_zero]
  rw [List.range'_eq_map_range]
  simp only [List.flatMap, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.range_one, Nat.zero_add]
  exact flatten_map_singleton_fd _ _

/-! ## `ST_PS = ⋃ₖ SkT_PS k`（Isabelle `m_6_7_ST_eq_Union_SkT` の一方向） -/

private theorem STPS_SkTPS_fd (M : PS) (h : STPS M) : ∃ k, SkTPS k M := by
  induction h with
  | diag u v huv => exact ⟨0, u, v, rfl, huv⟩
  | oper hM n hn ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, _, n, rfl, hk, hn⟩

/-! ## 単項列の降下（Isabelle `f7x_fseq_descend_mono`, pss_wip.thy:52051） -/

/-- Isabelle `f7x_fseq_descend_mono`。`M ∈ PT_PS` は `RTPS M ∧ monoT M` で綴る
（`STPS M` から `TPS M` が出るので `M ∈ PT_PS` と同値）。 -/
theorem fseq_descend_mono_fd
    (hTOT : FseqDesc_Trans_preserves_OT)
    (hI : FseqDesc_exchI) (hII : FseqDesc_exchII) (hIII : FseqDesc_exchIII)
    (hIV : FseqDesc_exchIV) (hV : FseqDesc_exchV) (hVI : FseqDesc_exchVI)
    (bMult : FseqDesc_operI_j0zero_trans_mult)
    (bAdm0 : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (bRc : FseqDesc_m_8_6_rcseq_Trans)
    (eII : FseqDesc_m_8_3_TransCondII_oper_descend_engine)
    (eV : FseqDesc_m_8_5_TransCondV_oper_descend_engine)
    (eVI : FseqDesc_m_8_6_TransCondVI_oper_descend_engine)
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true)
    (hn : 1 ≤ n) (hL : 1 < Lng M) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := RTPS_TPS M hR
  by_cases hB : oper M n = Pred M
  · rw [hB]
    exact m_7_3_Pred_Trans_descend M hM hL
  -- 以降 `M[n] ≠ Pred M`
  have hj1pos : Lng M - 1 ≠ 0 := by omega
  have hn2 : 1 < n := by
    rcases Nat.lt_or_ge 1 n with h | h
    · exact h
    · exfalso
      have hn1 : n = 1 := by omega
      subst hn1
      exact hB (pred_is_oper1 M hM hL).symm
  have hnotzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    intro h
    exact hB (oper_of_last_zero_fd M n hj1pos h.1 h.2)
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    cases hh : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) with
    | false => exact absurd (oper_of_no_parent_fd M n hj1pos hh) hB
    | true => rfl
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnotzT : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  have hTne : Trans M ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT M hM).2 h
    rw [hnotzT] at hz
    exact Bool.noConfusion hz
  have hdiag : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmpos : 0 < m := by omega
  rcases trans_cond_cases_fd M hR hmono hL with cI | cII | cIII | cIV | cV | cVI
  ---------------------------------------------------------------- 条件 (I)
  · have e1z : entry M 1 (Lng M - 1) = 0 := by
      simp only [transCondI, Bool.and_eq_true, beq_iff_eq, lastIdx] at cI
      exact cI.1
    by_cases hj1one : Lng M - 1 = 1
    · -- `Lng M = 2`: `M[n] = ((u,u))^n`
      have hL2 : Lng M = 2 := by omega
      have he11z : entry M 1 1 = 0 := by rw [hj1one] at e1z; exact e1z
      have hi1 : idx1 M 1 = 0 := by simp [idx1, he11z]
      have hnz1 : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by
        rw [hj1one] at hnotzero; exact hnotzero
      have hp1 : hasParent M (idx1 M 1) 1 = true := by rw [hj1one] at hp; exact hp
      have hop : oper M (m + 1) = List.replicate (m + 1) (entry M 1 0, entry M 1 0) := by
        rw [oper_len2_fd M hL2 hnz1 hp1 0 0 (by simp [hi1]) (by simp [hi1])]
        rw [hdiag]
        simp [List.map_const', List.eq_replicate_iff]
      have hTMn := const00_Trans (entry M 1 0) m
      have hTM : Trans M = Dprin (entry M 1 0 : ℕ∞) (Dprin 0 BZero) := by
        rw [two_column_Trans M hR hmono hL2, he11z]
        rfl
      have hhd : lessBP (.db (entry M 1 0 : ℕ∞) BZero)
          (.db (entry M 1 0 : ℕ∞) (Dprin 0 BZero)) = true := by
        simp [lessBP, lessBT_BZero_Dprin_fd]
      have key := multBT_lessBT_principal_fd hhd
      rw [hop, hTMn, hTM]
      by_cases hu : entry M 1 0 = 0
      · simpa [hu, Dprin] using key m
      · simpa [hu, Dprin] using key (m + 1)
    · -- `1 < Lng M - 1`
      have hj1gt : 1 < Lng M - 1 := by omega
      have hTOTM : Trans M ∈ OT_B := hTOT M hST hmono hj1gt
      by_cases hj0z : parent M 0 (Lng M - 1) = 0
      · -- `j₀ = 0`: `Trans (M[n]) = (Trans (Pred M)) ×_B n`
        have haddv := bMult M m hR hp0 e1z hj0z hj1gt
        have hAdm0 : transJm1 M = 0 := by
          simp only [transJm1, transJ0, lastParent, lastIdx, hj0z, Adm, adm_zero]
          simp
        obtain ⟨t₁, ⟨htp, htm⟩, -⟩ := bAdm0 M hR hmono hj1gt hAdm0 (Or.inl cI)
        have hXne : Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero ≠ BZero := by
          simp [Dprin, BZero]
        have hself := lessBT_addBT_self t₁ _ hXne
        have hhd : lessBP (.db (entry M 1 0 : ℕ∞) t₁)
            (.db (entry M 1 0 : ℕ∞)
              (addBT t₁ (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero))) = true := by
          simp [lessBP, hself]
        have key := multBT_lessBT_principal_fd hhd (m + 1)
        rw [haddv, htp, htm]
        simpa [Dprin] using key
      · -- `j₀ > 0`: 交換則 (I) ＋ [Buc1] Lemma 3.2(a)
        have hj0pos : 0 < parent M 0 (Lng M - 1) := by omega
        have hcomm := hI M (m + 1) hST hmono hj1gt cI hj0pos hn2
        rw [hcomm]
        simpa using buchholz_fseq_lt (Trans M) m hTOTM hTne
  ---------------------------------------------------------------- 条件 (II)
  · have hj1gt : 1 < Lng M - 1 := by
      by_contra hcon
      have hj1one : Lng M - 1 = 1 := by omega
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hpz : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0'
      simp only [transCondII, Bool.and_eq_true, lastParent, lastIdx, hj1one, hpz,
        adm_zero] at cII
      simp at cII
    exact eII M (m + 1) hST hmono hj1gt cII (by omega) (hTOT M hST hmono hj1gt)
      (fun h => hII M (m + 1) hST hmono hj1gt cII h)
  ---------------------------------------------------------------- 条件 (III)
  · have hj1gt : 1 < Lng M - 1 := by
      by_contra hcon
      have hj1one : Lng M - 1 = 1 := by omega
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent, hj1one] at cIII
      have he1pos : 0 < entry M 1 1 := cIII.1.1
      have hge : entry M 1 1 ≤ entry M 1 (parent M 0 1) := cIII.1.2
      have hi1 : idx1 M 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent M 1 1 = true := by
        rw [hj1one, hi1] at hp; exact hp
      have hlt := nextR_row1_lt_fd M (parent_one_nextR_fd M 1 hp1)
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      rw [parent_one_zero_fd M 0 hp0'] at hge
      omega
    have hTOTM : Trans M ∈ OT_B := hTOT M hST hmono hj1gt
    obtain ⟨k, hke⟩ := hIII M (m + 1) hST hmono hj1gt cIII hn2
    exact leBT_lessBT_trans_fd hke (buchholz_fseq_lt (Trans M) k hTOTM hTne)
  ---------------------------------------------------------------- 条件 (IV)
  · have hj1gt : 1 < Lng M - 1 := by
      by_contra hcon
      have hj1one : Lng M - 1 = 1 := by omega
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent, hj1one] at cIV
      have he1pos : 0 < entry M 1 1 := cIV.1.1
      have hge : entry M 1 1 ≤ entry M 1 (parent M 0 1) := cIV.1.2
      have hi1 : idx1 M 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent M 1 1 = true := by
        rw [hj1one, hi1] at hp; exact hp
      have hlt := nextR_row1_lt_fd M (parent_one_nextR_fd M 1 hp1)
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      rw [parent_one_zero_fd M 0 hp0'] at hge
      omega
    have hTOTM : Trans M ∈ OT_B := hTOT M hST hmono hj1gt
    obtain ⟨k, hke⟩ := hIV M (m + 1) hST hmono hj1gt cIV hn2
    exact leBT_lessBT_trans_fd hke (buchholz_fseq_lt (Trans M) k hTOTM hTne)
  ---------------------------------------------------------------- 条件 (V)
  · have hj1gt : 1 < Lng M - 1 := by
      simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent] at cV
      omega
    exact eV M (m + 1) hST hmono hj1gt cV (by omega) (hTOT M hST hmono hj1gt)
      (fun h => hV M (m + 1) hST hmono hj1gt cV h)
  ---------------------------------------------------------------- 条件 (VI)
  · by_cases hj1one : Lng M - 1 = 1
    · -- `Lng M = 2`: `M[n] = rcseq u (n-1)`
      have hL2 : Lng M = 2 := by omega
      simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        lastIdx, lastParent, hj1one] at cVI
      have he1pos : 0 < entry M 1 1 := cVI.1.1
      have hp0' : hasParent M 0 1 = true := by rw [hj1one] at hp0; exact hp0
      have hpz0 : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0'
      have he11 : entry M 1 1 = entry M 1 0 + 1 := by
        have := cVI.1.2; rw [hpz0] at this; omega
      have hi1 : idx1 M 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent M (idx1 M 1) 1 = true := by rw [hj1one] at hp; exact hp
      have hpz1 : parent M (idx1 M 1) 1 = 0 := parent_one_zero_fd M _ hp1
      have hnz1 : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by
        rw [hj1one] at hnotzero; exact hnotzero
      -- 条件 (A) から `M_{0,1} = u + 1`
      have hcondA := (RTPS_condAB M hR).1
      have he01 : entry M 0 1 = entry M 1 0 + 1 := by
        simp only [RedCondA, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_true_eq] at hcondA
        have := hcondA 0 (by omega) 1 (by omega)
        rcases this with h | h
        · rw [hp0'] at h; exact absurd h (by simp)
        · rw [hpz0, hdiag] at h; omega
      have hop : oper M (m + 1)
          = (List.range (m + 1)).map (fun k => (entry M 1 0 + k, entry M 1 0)) := by
        rw [oper_len2_fd M hL2 hnz1 hp1 1 0
          (by rw [hi1] at hpz1 ⊢; simp [hi1, hpz1, he01, hdiag])
          (by simp [hi1])]
        simp [hdiag]
      have hTMn : Trans (oper M (m + 1))
          = (fun a => Dprin (entry M 1 0 : ℕ∞) a)^[m + 1] BZero := by
        rw [hop, bRc (entry M 1 0) m]
        rw [if_neg (by omega)]
      have hTM : Trans M = Dprin (entry M 1 0 : ℕ∞)
          (Dprin ((entry M 1 0 + 1 : ℕ) : ℕ∞) BZero) := by
        rw [two_column_Trans M hR hmono hL2, he11]
      have hinner := Dpow_lessBT_Dprin_fd
        (u := entry M 1 0) (v := entry M 1 0 + 1) (by omega) BZero m
      rw [hTMn, hTM, Function.iterate_succ_apply']
      exact lessBT_Dprin_congr_fd hinner
    · have hj1gt : 1 < Lng M - 1 := by omega
      exact eVI M (m + 1) hST hmono hj1gt cVI (by omega) (hTOT M hST hmono hj1gt)
        (fun h => hVI M (m + 1) hST hmono hj1gt cVI h)

/-! ## FULL dispatcher（Isabelle `m_8_7_fseq_descend_dispatcher`, pss_wip.thy:52353） -/

/-- Isabelle `m_8_7_fseq_descend_dispatcher`。複項 `M` では展開が最終 `P` 成分
`PJ = drop (Pcut M) M` に閉じ込められ（`Pcut M ≤ j₀ < j₁`）、`M[n] = A @ PJ[n]` の
`P` 境界整合（`m_6_2_P_oper_2`）＋ `f7x_Trans_append_Pblocks` ＋
`lessBT_addBT_mono_right` が成分の降下を持ち上げる。 -/
theorem m_8_7_fseq_descend_dispatcher
    (hTOT : FseqDesc_Trans_preserves_OT)
    (hI : FseqDesc_exchI) (hII : FseqDesc_exchII) (hIII : FseqDesc_exchIII)
    (hIV : FseqDesc_exchIV) (hV : FseqDesc_exchV) (hVI : FseqDesc_exchVI)
    (bMult : FseqDesc_operI_j0zero_trans_mult)
    (bAdm0 : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (bRc : FseqDesc_m_8_6_rcseq_Trans)
    (eII : FseqDesc_m_8_3_TransCondII_oper_descend_engine)
    (eV : FseqDesc_m_8_5_TransCondV_oper_descend_engine)
    (eVI : FseqDesc_m_8_6_TransCondVI_oper_descend_engine)
    (bPoper : FseqDesc_m_6_2_P_oper_2)
    (bAppend : FseqDesc_f7x_Trans_append_Pblocks)
    (bLeftmost : FseqDesc_m_7_3_Trans_leftmost_2)
    (M : PS) (n : ℕ) (hST : STPS M) (hn : 1 ≤ n) (hL : 1 < Lng M) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := RTPS_TPS M hR
  have hnotzT : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  by_cases hmono : monoT M = true
  · exact fseq_descend_mono_fd hTOT hI hII hIII hIV hV hVI bMult bAdm0 bRc eII eV eVI
      M n hST hmono hn hL
  -- 複項の場合
  have hnmono : monoT M = false := by simpa using hmono
  have hmulti : multiT M = true := by
    simp only [multiT, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hnotzT, hnmono⟩
  by_cases hB : oper M n = Pred M
  · rw [hB]
    exact m_7_3_Pred_Trans_descend M hM hL
  have hj1pos : Lng M - 1 ≠ 0 := by omega
  have hnotzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    intro h
    exact hB (oper_of_last_zero_fd M n hj1pos h.1 h.2)
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    cases hh : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) with
    | false => exact absurd (oper_of_no_parent_fd M n hj1pos hh) hB
    | true => rfl
  -- 最終列の親が `Pcut M < Lng M - 1` を固定する
  have hnext := hasParent_nextR_fd M (idx1 M (Lng M - 1)) (Lng M - 1) hp
  have hrow := nextR_implies_row0 M (idx1 M (Lng M - 1))
    (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) (Lng M - 1) hnext
  have hj0pos : 0 < parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
    by_contra hcon
    have hz : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = 0 := by omega
    rw [hz] at hrow
    have : monoT M = true := by
      simp only [monoT, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hnotzT, hrow.2⟩
    rw [hnmono] at this
    exact Bool.noConfusion this
  have hpcle : Pcut M ≤ parent M (idx1 M (Lng M - 1)) (Lng M - 1) :=
    parent_ge_Pcut M (idx1 M (Lng M - 1)) _ hM hmulti hL hnext
  have hclt : Pcut M < Lng M - 1 := by omega
  -- `A` と最終成分 `PJ`
  set A := M.take (Pcut M) with hAdef
  set PJ := M.drop (Pcut M) with hPJdef
  have hLPJ : 1 < Lng PJ := by
    -- `Lng X` と `X.length` は別の omega atom になるので defeq で橋渡しする
    have hclt' : Pcut M < M.length - 1 := hclt
    have hLM : 1 < M.length := hL
    show 1 < (M.drop (Pcut M)).length
    rw [List.length_drop]
    omega
  have hlast := P_last_multi M hmulti hL
  have hlastgt : 1 < Lng ((P M).getLastD []) := by rw [hlast.1]; exact hLPJ
  obtain ⟨hopsplit, hPsplit⟩ := bPoper M n hM hn hlastgt
  have hconcA : (P M).dropLast.flatten = A := by rw [hlast.2]; exact P_concat A
  have hopeq : oper M n = A ++ oper PJ n := by
    rw [hopsplit, hconcA, hlast.1]
  have hPeq : P (oper M n) = P A ++ P (oper PJ n) := by
    rw [hPsplit, hlast.2, hlast.1]
  -- `PJ` は標準形・単項・非退化
  have hidx0 : (P M).length - 1 < (P M).length := by
    have hne := P_nonempty M
    cases hPM : P M with
    | nil => exact absurd hPM hne
    | cons a as => simp
  have hPJST : STPS PJ := by
    obtain ⟨k, hk⟩ := STPS_SkTPS_fd M hST
    have hcomp := SkTPS_P_components k M hk ((P M).length - 1) hidx0
    rw [(trans_multi_last_component M hM hmulti).1] at hcomp
    exact SkTPS_STPS k PJ hcomp
  have hPJR : RTPS PJ := STPS_RTPS PJ hPJST
  have hPJT : TPS PJ := RTPS_TPS PJ hPJR
  have hPJnz : zeroT PJ = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine Or.inl ?_
    show ¬ (Lng PJ = 1)
    omega
  have hPJne00 : PJ ≠ [(0, 0)] := by
    intro h
    rw [h] at hLPJ
    simp at hLPJ
  have hPJmono : monoT PJ = true := by
    have hmem : PJ ∈ P M := by
      have hg := (trans_multi_last_component M hM hmulti).1
      rw [hPJdef, ← hg, getD_eq_getElem_idx (P M) [] hidx0]
      exact List.getElem_mem hidx0
    rcases P_components_nonmulti M hM PJ hmem with h | h
    · rw [hPJnz] at h; exact Bool.noConfusion h
    · exact h
  have hPJnonmulti : multiT PJ = false := by
    simp only [multiT, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_true']
    exact Or.inr hPJmono
  -- `M[n]` と `PJ[n]` の簡約性
  have hMnST : STPS (oper M n) := STPS.oper hST n hn
  have hMnR : RTPS (oper M n) := STPS_RTPS _ hMnST
  have hPJnST : STPS (oper PJ n) := STPS.oper hPJST n hn
  have hPJnR : RTPS (oper PJ n) := STPS_RTPS _ hPJnST
  have hKR : RTPS (A ++ oper PJ n) := by rw [← hopeq]; exact hMnR
  have hPeq' : P (A ++ oper PJ n) = P A ++ P (oper PJ n) := by
    rw [← hopeq]; exact hPeq
  -- 境界を跨ぐ加法性
  have haddK := bAppend A (oper PJ n) hKR hPJnR hPeq'
  have hTMsplit : Trans M = addBT (Trans A) (Trans PJ) := by
    have h := (Trans_Mark_multi_equations M hR hmulti).1
    simp only [← hAdef, ← hPJdef] at h
    rw [h, if_neg (by simpa using hPJne00)]
  -- 成分の降下（mono dispatcher、同じ `n`）
  have hcomp_lt : lessBT (Trans (oper PJ n)) (Trans PJ) = true :=
    fseq_descend_mono_fd hTOT hI hII hIII hIV hV hVI bMult bAdm0 bRc eII eV eVI
      PJ n hPJST hPJmono hn hLPJ
  -- `D₀ 0` 補正込みの降下
  have hcorr_lt : lessBT
      (if (P (oper PJ n)).getD 0 [] = [(0, 0)]
       then addBT (Dprin 0 BZero) (Trans (oper PJ n)) else Trans (oper PJ n))
      (Trans PJ) = true := by
    by_cases hexc : (P (oper PJ n)).getD 0 [] = [(0, 0)]
    · rw [if_pos hexc]
      -- `Trans PJ` は単一 principal 項
      have hPPJ : P PJ = [PJ] := P_nonmulti_eq PJ hPJnonmulti
      have hP0nz : zeroT ((P PJ).getD 0 []) = false := by rw [hPPJ]; exact hPJnz
      have hlen1 : (PB (Trans PJ)).length = 1 :=
        (m_7_3_Trans_monoT PJ hPJR hP0nz).1 hPJmono
      obtain ⟨ps, hTps⟩ : ∃ ps, Trans PJ = .trm ps := by
        cases h : Trans PJ with | trm ps => exact ⟨ps, rfl⟩
      have hlps : ps.length = 1 := by
        rw [hTps] at hlen1
        simpa [PB, untrm] using hlen1
      obtain ⟨p, hpsp⟩ : ∃ p, ps = [p] := by
        cases ps with
        | nil => simp at hlps
        | cons a as => cases as with
          | nil => exact ⟨a, rfl⟩
          | cons b bs => simp at hlps
      obtain ⟨w, body⟩ := p
      have hTPJ : Trans PJ = .trm [.db w body] := by rw [hTps, hpsp]
      have hPJne00' : (P PJ).getD 0 [] ≠ [(0, 0)] := by rw [hPPJ]; exact hPJne00
      have hwval : w = (entry PJ 1 0 : ℕ∞) := by
        have h := (bLeftmost PJ hPJR hPJne00').2
        rw [hTPJ] at h
        simpa [bpHeadV] using h
      -- 先頭 principal の比較
      have hhead_lt : lessBP (.db 0 BZero) (.db w body) = true := by
        by_cases hz : entry PJ 1 0 = 0
        · have hw0 : w = 0 := by rw [hwval, hz]; rfl
          have hbodyne : body ≠ BZero := by
            intro hb
            have hTPJ0 : Trans PJ = Dprin 0 BZero := by
              rw [hTPJ, hw0, hb]; rfl
            have hpd := m_7_3_Pred_Trans_descend PJ hPJT hLPJ
            rw [hTPJ0] at hpd
            have hzero := lessBT_D00_imp_zero_fd hpd
            have hzP : zeroT (Pred PJ) = true :=
              (Trans_preserves_zeroT (Pred PJ) (Pred_TPS_fd PJ hLPJ)).2 hzero
            have hLP : Lng (Pred PJ) = 1 := by
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP
              exact hzP.1
            rw [Lng_Pred_fd PJ hLPJ] at hLP
            have hL2 : Lng PJ = 2 := by omega
            have h2 := two_column_Trans PJ hPJR hPJmono hL2
            rw [hTPJ0, hz] at h2
            simp [Dprin, BZero] at h2
          rw [hw0]
          simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true, beq_self_eq_true,
            true_and]
          exact Or.inr (by cases body with
            | trm bs => cases bs with
              | nil => exact absurd rfl hbodyne
              | cons c cs => simp [BZero, lessBT, lessBPList])
        · have hwpos : (0 : ℕ∞) < w := by
            rw [hwval]
            exact_mod_cast Nat.pos_of_ne_zero hz
          simp only [lessBP, Bool.or_eq_true]
          exact Or.inl (decide_eq_true hwpos)
      obtain ⟨ps', hTn⟩ : ∃ ps', Trans (oper PJ n) = .trm ps' := by
        cases h : Trans (oper PJ n) with | trm ps' => exact ⟨ps', rfl⟩
      rw [hTn, hTPJ]
      simp only [Dprin, addBT, List.singleton_append, lessBT, lessBPList,
        Bool.or_eq_true]
      exact Or.inl hhead_lt
    · rw [if_neg hexc]
      exact hcomp_lt
  have hfinal := addBT_lt_right_bf (Trans A) _ _ hcorr_lt
  rw [hopeq, haddK, hTMsplit]
  exact hfinal

/-! ## 逐語形（原文 §8.7 補題（基本列の降下性）） -/

/-- 原文 §8.7 補題（基本列の降下性）、article 5869
（Isabelle `p_8_7_fseq_descend`, pss_paper.thy:2253）:
`M ∈ ST_PS`、`n ≥ 1`、`Lng M > 1` なら `Trans(M[n]) < Trans(M)`。 -/
theorem p_8_7_fseq_descend
    (hTOT : FseqDesc_Trans_preserves_OT)
    (hI : FseqDesc_exchI) (hII : FseqDesc_exchII) (hIII : FseqDesc_exchIII)
    (hIV : FseqDesc_exchIV) (hV : FseqDesc_exchV) (hVI : FseqDesc_exchVI)
    (bMult : FseqDesc_operI_j0zero_trans_mult)
    (bAdm0 : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (bRc : FseqDesc_m_8_6_rcseq_Trans)
    (eII : FseqDesc_m_8_3_TransCondII_oper_descend_engine)
    (eV : FseqDesc_m_8_5_TransCondV_oper_descend_engine)
    (eVI : FseqDesc_m_8_6_TransCondVI_oper_descend_engine)
    (bPoper : FseqDesc_m_6_2_P_oper_2)
    (bAppend : FseqDesc_f7x_Trans_append_Pblocks)
    (bLeftmost : FseqDesc_m_7_3_Trans_leftmost_2)
    (M : PS) (n : ℕ) (hST : STPS M) (hn : 1 ≤ n) (hL : 1 < Lng M) :
    lessBT (Trans (oper M n)) (Trans M) = true :=
  m_8_7_fseq_descend_dispatcher hTOT hI hII hIII hIV hV hVI bMult bAdm0 bRc
    eII eV eVI bPoper bAppend bLeftmost M n hST hn hL

/-- 原文 §8.3 命題（条件 (II) の下での `Trans` と基本列の交換関係）、article 3958
（Isabelle `p_8_3_TransCondII_oper_descend`, pss_paper.thy:1863）:
`M ∈ ST_PS ∩ PT_PS`、`0 < n`、`Lng M - 1 > 1`、条件 (II) なら
`Trans(M[n]) < Trans(M)`。tree の `8.3-Trans-fseq-condII` はこの項目の系
（⛔8.7-fseq-descend）で、dispatcher の条件 (II) 枝そのものである。 -/
theorem p_8_3_TransCondII_oper_descend
    (hTOT : FseqDesc_Trans_preserves_OT)
    (hI : FseqDesc_exchI) (hII : FseqDesc_exchII) (hIII : FseqDesc_exchIII)
    (hIV : FseqDesc_exchIV) (hV : FseqDesc_exchV) (hVI : FseqDesc_exchVI)
    (bMult : FseqDesc_operI_j0zero_trans_mult)
    (bAdm0 : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (bRc : FseqDesc_m_8_6_rcseq_Trans)
    (eII : FseqDesc_m_8_3_TransCondII_oper_descend_engine)
    (eV : FseqDesc_m_8_5_TransCondV_oper_descend_engine)
    (eVI : FseqDesc_m_8_6_TransCondVI_oper_descend_engine)
    (bPoper : FseqDesc_m_6_2_P_oper_2)
    (bAppend : FseqDesc_f7x_Trans_append_Pblocks)
    (bLeftmost : FseqDesc_m_7_3_Trans_leftmost_2)
    (M : PS) (n : ℕ) (hST : STPS M) (_hmono : monoT M = true) (hn : 0 < n)
    (hj₁ : 1 < Lng M - 1) (_cII : transCondII M = true) :
    lessBT (Trans (oper M n)) (Trans M) = true :=
  m_8_7_fseq_descend_dispatcher hTOT hI hII hIII hIV hV hVI bMult bAdm0 bRc
    eII eV eVI bPoper bAppend bLeftmost M n hST hn (by omega)

#print axioms fseq_descend_mono_fd
#print axioms m_8_7_fseq_descend_dispatcher
#print axioms p_8_7_fseq_descend
#print axioms p_8_3_TransCondII_oper_descend

end PSS
