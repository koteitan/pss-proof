import «5».«5.3-pred-is-oper1»
import «6».«6.3-admof-slice»
import «6».«6.6-one-column»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.7-standard-reduced»
import «Buchholz-1986».«Buchholz-1986-3.3»
import «7».«7.3-two-column»
import «7».«7.3-Trans-preserves-zeroT»
import «8».«8.1-diagSeq-Trans»
import «8».«8.2-subexpr-adm0-ctx»
import «8».«8.7-OT-examples»

/-!
# §8.7 補題（`Trans` が標準形を保つこと）

- 原文: `tmp/content.md` 6122（§8.7）。逐語形は `p_8_7_Trans_preserves_OT`
  (`isabelle/pss_paper.thy`:2317)。訂正: なし（A 番号の該当なし）。
- Isabelle: 無条件版は `y5_Trans_OT_B` (`isabelle/layerC/pss_scratch.thy`:14205)。
  その実体は census `oi12_census`(1) (:14102) → `oi8_census_final_ivadmeq`(1)
  (:5800) → `oc4_termination_census_master_v2`(1)
  (`isabelle/layerB/pss_wip.thy`:118034) → `apx_termination_final`(1) (:110241)
  → `apx_Trans_OT_all_of_otx_slots` (:110001) →
  **`otx_Trans_preserves_OT_dispatch` (:85710)**。
  本ファイルが移植したのはこの最後の `otx_Trans_preserves_OT_dispatch`＝
  `ST_PS` 帰納そのもの（OT 柱の実体）。基底は
  `m_8_7_Trans_preserves_OT_base` (:28738)。
- 停止性の 2 本柱のうちの 1 本（もう 1 本は降下性 `8.7-fseq-descend`）。
  `ST_PS` 上の `Trans` が [Buc1] の順序数項に落ちることを言う。
- 依存（ビルド済みのみ import）: `8.1-diagSeq-Trans`（`diagSeq_Trans`
  ＝ `m_8_1_diagSeq_Trans`）、`8.7-OT-examples`（`OT_examples_1`/`OT_examples_2`
  ＝ `m_8_7_OT_ex1`/`m_8_7_OT_ex2`）、`Buchholz-1986-3.3`
  （`buchholz_fseq_closed` ＝ [Buc1] Lemma 3.3、`e4x_OT_B_operB_numBT` の非零脚）、
  `8.2-subexpr-adm0-ctx`（`condII_or_condIV` ＝ `m_8_2_condII_or_condIV`）、
  `6.6-P-condAB`（`mono_hasParent_row0` ＝ `monoT_hasParent0_last`）、
  `6.3-admof-slice`（`adm_zero` ＝ `f7x_adm_zero`）、`6.7-standard-reduced`
  （`STPS_RTPS` ＝ `m_6_7_ST_PS_subseteq_RT_PS`）、`6.6-one-column`
  （`one_column` ＝ `m_6_6_oneColumn`）、`7.3-Trans-preserves-zeroT`、
  `7.3-two-column`、`5.3-pred-is-oper1`（`pred_is_oper1` ＝ `m_8_4_oper1_eq_Pred`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `otx_Trans_preserves_OT_dispatch` が仮定として取る 5 本
  （`OTint`/`OTpred`/`OTmulti`/`exchI`/`exchII`）＋ Isabelle 側では証明済だが
  Lean 未移植の 7 本の交換則（`otx_*_eq` / `m_8_1_Trans_fseq_condI_n1`）を
  名前付き `Prop` として露出し、そこから `ST_PS` 帰納を完全に実行する。
  露出した `Prop` は全 12 本（`OTdisp_*`、いずれも Isabelle 名と 1:1）。

## 露出 `Prop` の非空虚性・忠実性検証（`python/audit_8_7_trans_preserves_OT.py`）

緑でも `Prop` が偽（転記ミス）なら無価値なので、標準形プール（`diagSeq` を
基本列で閉じた 113 本、全て `reduced`）上で 12 本すべてを数値検証した:

* **11/12 は発火し、反例 0**（`OTint` 100 例、`OTpred` 87 例、`condVI_adm_eq` 60 例…）。
  定理自身も 113/113 で `Trans M ∈ OT_B`。
* **`OTdisp_exchII` のみプール上で 1 例も発火しない**（＝この検証では未確認）。
  条件 (II)＝「行 0 の親が非許容かつ `M_{1,j₁} = 0`」は稀な regime で、
  別途 18318 本（`Lng ≤ 16` まで）を走査しても **0 件**。代わりの裏付けとして、
  `OTdisp_exchII` はビルド済 `8.7-fseq-descend.lean` の `FseqDesc_exchII` と
  **バイト単位で同一**（`OTdisp_exchI` も同様）。

## 他ファイルの `Prop` との接続

本ファイルの `Trans_preserves_OT` は、既にビルド済の 2 本の名前付き `Prop` を
そのまま落とす（drop-in）:

* `TransPreservesOT`（`8.6-Trans-fseq-condVI.lean`:247）
  ＝ `∀ M, STPS M → Trans M ∈ OT_B` ——**同一形**。
* `FseqDesc_Trans_preserves_OT`（`8.7-fseq-descend.lean`:67）
  ＝ `∀ N, STPS N → monoT N = true → 1 < Lng N - 1 → Trans N ∈ OT_B`
  ——本定理の弱化（`Trans_preserves_OT_fseqdesc_form` で明示的に確認）。
-/

namespace PSS

/-! ## `otx_Trans_preserves_OT_dispatch` の 5 本の仮定（Isabelle 名 1:1）

`M ∈ PT_PS` は `RTPS M ∧ monoT M` と綴る規約（`STPS M` から `TPS M` が出るので
`STPS M ∧ monoT M` で `M ∈ ST_PS ∩ PT_PS` を表す）。 -/

/-- Isabelle `exchI`（`otx_Trans_preserves_OT_dispatch` の仮定、
`scx_condI_exchange1` が供給）。`8.7-fseq-descend.lean` の `FseqDesc_exchI` と同一形。 -/
def OTdisp_exchI : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondI N = true → 0 < parent N 0 (Lng N - 1) → 1 < m →
    Trans (oper N m) = operB (Trans N) (numBT (m - 1))

/-- Isabelle `exchII`（`c2sx_exchange_ex_condII_of_tailval` が供給）。
`8.7-fseq-descend.lean` の `FseqDesc_exchII` と同一形。 -/
def OTdisp_exchII : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondII N = true → 1 < m →
    ∃ k, Trans (oper N m) = operB (Trans N) (numBT k)

/-- Isabelle `OTint`（条件 (III)/(IV)/(V) の内部枝。census では
`oi8_OTint_condIII`/`oi8_OTint_condIV` ＋ condV 脚が供給）。 -/
def OTdisp_OTint : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    (transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true) →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-- Isabelle `OTpred`（`opx_OTpred_of_residuals`、残差 `{DEEPOT, NOBR}`）。 -/
def OTdisp_OTpred : Prop :=
  ∀ N : PS, STPS N → Trans N ∈ OT_B → 2 < Lng N →
    ¬ (entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    ¬ (monoT N = true ∧ transCondI N = true) →
    ¬ (monoT N = true ∧ transCondVI N = true ∧ ¬ (adm N (transJ0 N) = true)) →
    Trans (Pred N) ∈ OT_B

/-- Isabelle `OTmulti`（`opx_OTmulti`）。 -/
def OTdisp_OTmulti : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → multiT N = true → Trans N ∈ OT_B →
    1 < m → oper N m ≠ Pred N → Trans (oper N m) ∈ OT_B

/-! ## Isabelle では証明済・Lean 未移植の交換則（`otx_*` / `m_8_1_*`） -/

/-- Isabelle `otx_zerocol_predval` (`layerB/pss_wip.thy`:85474)。 -/
def OTdisp_zerocol_predval : Prop :=
  ∀ (M : PS) (m : ℕ), RTPS M → 1 < Lng M →
    entry M 0 (Lng M - 1) = 0 → entry M 1 (Lng M - 1) = 0 →
    operB (Trans M) (numBT m) = Trans (Pred M)

/-- Isabelle `m_8_1_Trans_fseq_condI_n1`（条件 (I) の `n = 1` 交換）。 -/
def OTdisp_Trans_fseq_condI_n1 : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondI M = true →
    Trans (oper M 1) = operB (Trans M) (numBT 0)

/-- Isabelle `otx_condI_j0z_eq` (`layerB/pss_wip.thy`:85292)。 -/
def OTdisp_condI_j0z_eq : Prop :=
  ∀ (M : PS) (n : ℕ), RTPS M → monoT M = true → 1 < Lng M - 1 →
    transCondI M = true → parent M 0 (Lng M - 1) = 0 → 1 ≤ n →
    Trans (oper M n) = operB (Trans M) (numBT (n - 1))

/-- Isabelle `otx_condI_j1eq1_eq` (`layerB/pss_wip.thy`:85516)。 -/
def OTdisp_condI_j1eq1_eq : Prop :=
  ∀ (M : PS) (n : ℕ), RTPS M → monoT M = true → Lng M = 2 →
    transCondI M = true → 2 ≤ n →
    Trans (oper M n) =
      operB (Trans M) (numBT (if entry M 1 0 = 0 then n - 2 else n - 1))

/-- Isabelle `otx_condVI_j1eq1_eq` (`layerB/pss_wip.thy`:85582)。 -/
def OTdisp_condVI_j1eq1_eq : Prop :=
  ∀ (M : PS) (n : ℕ), RTPS M → monoT M = true → Lng M = 2 →
    transCondVI M = true → hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true →
    2 ≤ n → Trans (oper M n) = operB (Trans M) (numBT (n - 2))

/-- Isabelle `otx_condVI_adm_eq` (`layerB/pss_wip.thy`:85236、
`c613x_condVI_exch_adm` が供給)。 -/
def OTdisp_condVI_adm_eq : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → adm M (transJ0 M) = true → 2 ≤ n →
    Trans (oper M n) = operB (Trans M) (numBT (n - 2))

/-- Isabelle `otx_condVI_nadm_eq` (`layerB/pss_wip.thy`:85260、
`c6nx_condVI_exch_nadm_uncond` が供給)。`8.6-Trans-fseq-condVI.lean` の
`CondVIExchNadm` の結論 (2) と同一。 -/
def OTdisp_condVI_nadm_eq : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → ¬ (adm M (transJ0 M) = true) → 1 ≤ n →
    Trans (oper M n) = operB (Trans M) (numBT (n - 1))

/-! ## 小補題 -/

/-- `0_B ∈ OT_B`。Isabelle `m_8_7_OT_zero` / `otx_OT_B_zero`。 -/
private theorem BZero_OT_B_tot : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- `operB 0_B z = 0_B`。Isabelle `b1x_operB_zero`。 -/
private theorem operB_BZero_tot (z : BT) : operB BZero z = BZero := by
  simp [operB, BZero, bOperCore]

/-- Isabelle `e4x_OT_B_operB_numBT` (`layerB/pss_wip.thy`:61390)。
ビルド済 `buchholz_fseq_closed` は `a ≠ 0_B` を要求するので、零脚を
`operB_BZero_tot` で埋めて無条件化する。 -/
private theorem OT_B_operB_numBT_tot {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz, operB_BZero_tot]; exact BZero_OT_B_tot
  · exact buchholz_fseq_closed a n ha hz

/-- 対角 1 列 `[(v,v)]` の翻訳。Isabelle `Trans_singleton`。 -/
private theorem Trans_singleton_tot (v : ℕ) :
    Trans [(v, v)] = if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  by_cases hv : v = 0
  · subst hv
    have hT : TPS ([((0:ℕ), (0:ℕ))]) := by simp [TPS]
    have hz : zeroT [((0:ℕ), (0:ℕ))] = true := by
      simp [zeroT, Lng, entry]
    simpa using (Trans_preserves_zeroT _ hT).mp hz
  · have hred : reduced [(v, v)] = true := by
      have hfix := Red_singleton v v
      simp [reduced, hfix]
    have hfuel : transFuel [(v, v)] = (transFuel [(v, v)] - 1) + 1 := by
      simp [transFuel]
    rw [Trans, hfuel, TransAux]
    simp [hred, lastIdx, entry, Dprin, BZero, hv]

/-- `SkT_PS 0` 基底。Isabelle `m_8_7_Trans_preserves_OT_base`
(`layerB/pss_wip.thy`:28738)。 -/
private theorem Trans_diagSeq_OT_tot (u v : ℕ) (huv : u ≤ v) :
    Trans (diagSeq u v) ∈ OT_B := by
  by_cases he : u = v
  · subst he
    have hd : diagSeq u u = [(u, u)] := by
      simp [diagSeq]
    rw [hd, Trans_singleton_tot]
    by_cases hu : u = 0
    · simp [hu, BZero_OT_B_tot]
    · simp only [hu, if_false]
      exact OT_examples_1 u
  · have hlt : u < v := by omega
    rw [diagSeq_Trans u v hlt]
    exact OT_examples_2 u v

/-! ## `parent` / `nextR` の小補題（Isabelle `f7x_parent_one_zero` ほか） -/

/-- Isabelle `f7x_parent_one_zero`。 -/
private theorem parent_one_zero_tot (M : PS) (i : ℕ)
    (hp : hasParent M i 1 = true) : parent M i 1 = 0 := by
  have hmem : parent M i 1 ∈ parents M i 1 := by
    unfold parent
    cases h : parents M i 1 with
    | nil => rw [hasParent, h] at hp; simp at hp
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
private theorem hasParent_nextR_tot (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) : nextR M i (parent M i j₁) j₁ = true := by
  have hmem : parent M i j₁ ∈ parents M i j₁ := by
    unfold parent
    cases h : parents M i j₁ with
    | nil => rw [hasParent, h] at hp; simp at hp
    | cons a as => simp [List.headD]
  have hmem' : parent M i j₁ < Lng M ∧ nextR M i (parent M i j₁) j₁ = true := by
    simpa [parents, List.mem_filter] using hmem
  exact hmem'.2

/-- 行 1 の親辺 `0 <^Next 1` は `M_{1,0} < M_{1,1}` を与える。 -/
private theorem nextR_row1_lt_tot (M : PS) (h : nextR M 1 0 1 = true) :
    entry M 1 0 < entry M 1 1 := by
  rw [nextR, if_neg (by omega)] at h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-! ## `oper` の直接計算 -/

/-- 末尾が `(0,0)` なら `M[n] = Pred M`。 -/
private theorem oper_of_last_zero_tot (M : PS) (n : ℕ) (hj : Lng M - 1 ≠ 0)
    (h0 : entry M 0 (Lng M - 1) = 0) (h1 : entry M 1 (Lng M - 1) = 0) :
    oper M n = Pred M := by
  unfold oper; simp [hj, h0, h1]

/-- 段 `i₁` に親がなければ `M[n] = Pred M`。 -/
private theorem oper_of_no_parent_tot (M : PS) (n : ℕ) (hj : Lng M - 1 ≠ 0)
    (hnp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = false) :
    oper M n = Pred M := by
  unfold oper
  simp only [hj, if_false, hnp]
  by_cases h0 : entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0
  · simp [h0.1, h0.2]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h0 ⊢
    rw [if_neg (by simpa using h0)]
    simp

/-! ## 条件 (I)–(VI) の網羅（Isabelle `m_8_2_condII_or_condIV` 経由） -/

private theorem trans_cond_cases_tot (M : PS) (hR : RTPS M)
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
  have h6 : transCondVI M = false := by simpa using c6
  rcases condII_or_condIV M hR hmono hL (by tauto) h6 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ## `1 < Lng N - 1` の導出（条件 (II)/(III)/(IV) 枝、Isabelle 逐語） -/

/-- 条件 (II) では `j₁ = 1` はあり得ない: `j₁ = 1` なら `j₀ = 0` で
`adm M 0` は常に真、しかし条件 (II) は `¬ adm M j₀` を要求する。 -/
private theorem condII_j1gt_tot (M : PS) (hL : 1 < Lng M)
    (hp0 : hasParent M 0 (Lng M - 1) = true) (c : transCondII M = true) :
    1 < Lng M - 1 := by
  by_contra hcon
  have j1one : Lng M - 1 = 1 := by omega
  have hp0' : hasParent M 0 1 = true := by rwa [j1one] at hp0
  have p0 : parent M 0 1 = 0 := parent_one_zero_tot M 0 hp0'
  have hnadm : adm M (lastParent M) = false := by
    simp only [transCondII, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c
    exact c.2
  have : lastParent M = 0 := by
    simp only [lastParent, lastIdx, j1one]; exact p0
  rw [this, adm_zero M] at hnadm
  exact Bool.noConfusion hnadm

/-- 条件 (III)/(IV) では `j₁ = 1` はあり得ない: `j₁ = 1` なら親辺 `0 <^Next 1` が
`M_{1,0} < M_{1,1}` を与えるが、条件 (III)/(IV) は `M_{1,1} ≤ M_{1,0}` を要求する。 -/
private theorem cond34_j1gt_tot (M : PS) (hL : 1 < Lng M)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hpos : 0 < entry M 1 (lastIdx M))
    (hge : entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)) :
    1 < Lng M - 1 := by
  by_contra hcon
  have j1one : Lng M - 1 = 1 := by omega
  have hpos' : 0 < entry M 1 (Lng M - 1) := hpos
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos']
  have hp1 : hasParent M 1 1 = true := by rwa [hi1, j1one] at hp
  have hnext : nextR M 1 (parent M 1 1) 1 = true := hasParent_nextR_tot M 1 1 hp1
  rw [parent_one_zero_tot M 1 hp1] at hnext
  have hlt : entry M 1 0 < entry M 1 1 := nextR_row1_lt_tot M hnext
  have hp0' : hasParent M 0 1 = true := by rwa [j1one] at hp0
  have p0 : lastParent M = 0 := by
    show parent M 0 (Lng M - 1) = 0
    rw [j1one]; exact parent_one_zero_tot M 0 hp0'
  have hge' : entry M 1 (Lng M - 1) ≤ entry M 1 0 := by rw [p0] at hge; exact hge
  rw [j1one] at hge'
  omega

/-- Isabelle `Lng (Pred M) = Lng M - 1`。 -/
private theorem Lng_Pred_tot (M : PS) (hL : 1 < Lng M) : Lng (Pred M) = Lng M - 1 := by
  unfold Pred; rw [if_neg (by omega)]; simp

/-! ## `otx_Trans_preserves_OT_dispatch` (`layerB/pss_wip.thy`:85710) の移植

`ST_PS` 帰納。基底は `Trans_diagSeq_OT_tot`、帰納段は Isabelle 逐語の
場合分け（`Lng N ≤ 1` / `N[n] = Pred N`（4 枝）/ `N[n] ≠ Pred N`（単項 6 枝 ＋ 複項））。 -/
private theorem Trans_preserves_OT_dispatch_tot
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq)
    (M : PS) (hM : STPS M) : Trans M ∈ OT_B := by
  induction hM with
  | diag u v huv => exact Trans_diagSeq_OT_tot u v huv
  | @oper N hN n hn ih =>
    have hNR : RTPS N := STPS_RTPS N hN
    have hNT : TPS N := RTPS_TPS N hNR
    by_cases hLle : Lng N ≤ 1
    · -- `Lng N ≤ 1` では `N[n] = N`
      have hEq : oper N n = N := by
        unfold oper; simp [show Lng N - 1 = 0 by omega]
      rw [hEq]; exact ih
    have L : 1 < Lng N := by omega
    have j1pos : Lng N - 1 ≠ 0 := by omega
    by_cases predc : oper N n = Pred N
    · -- `N[n] = Pred N`
      by_cases L2 : Lng N = 2
      · -- `Pred N` は 1 列 `[(v,v)]`
        have hPR : RTPS (Pred N) := RTPS_Pred N hNR
        have hPT : TPS (Pred N) := RTPS_TPS _ hPR
        have LP1 : Lng (Pred N) = 1 := by rw [Lng_Pred_tot N L]; omega
        obtain ⟨v, pv⟩ := (one_column (Pred N) hPT).mp ⟨LP1, hPR⟩
        rw [predc, pv, Trans_singleton_tot]
        by_cases hv : v = 0
        · simp [hv, BZero_OT_B_tot]
        · simp only [hv, if_false]; exact OT_examples_1 v
      have L3 : 2 < Lng N := by omega
      by_cases zc : entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0
      · -- 末尾零列: `Trans (Pred N) = Trans N [0]`
        rw [predc, ← hZC N 0 hNR L zc.1 zc.2]
        exact OT_B_operB_numBT_tot ih 0
      by_cases cI : monoT N = true ∧ transCondI N = true
      · have j1gt : 1 < Lng N - 1 := by omega
        have o1 : Pred N = oper N 1 := pred_is_oper1 N hNT L
        rw [predc, o1, hCIn1 N hNR cI.1 j1gt cI.2]
        exact OT_B_operB_numBT_tot ih 0
      by_cases cVIn : monoT N = true ∧ transCondVI N = true ∧
          ¬ (adm N (transJ0 N) = true)
      · have j1gt : 1 < Lng N - 1 := by omega
        have o1 : Pred N = oper N 1 := pred_is_oper1 N hNT L
        have e1 := hCVIn N 1 hN cVIn.1 cVIn.2.1 j1gt cVIn.2.2 (le_refl 1)
        rw [predc, o1, e1]
        exact OT_B_operB_numBT_tot ih 0
      · rw [predc]
        exact hOTpred N hN ih L3 zc cI cVIn
    · -- `N[n] ≠ Pred N`
      have n2 : 1 < n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · exact absurd (by rw [show n = 1 by omega]; exact (pred_is_oper1 N hNT L).symm)
            predc
        · omega
      have hne1 : ¬ (Lng N = 1) := by omega
      have notzT : zeroT N = false := by simp [zeroT, hne1]
      by_cases mono : monoT N = true
      · have notzero : ¬ (entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) := by
          intro h; exact predc (oper_of_last_zero_tot N n j1pos h.1 h.2)
        have hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true := by
          by_contra hc
          exact predc (oper_of_no_parent_tot N n j1pos (by simpa using hc))
        have hp0 : hasParent N 0 (Lng N - 1) = true :=
          mono_hasParent_row0 N hNT mono (Lng N - 1) (by omega) (by omega)
        rcases trans_cond_cases_tot N hNR mono L with c1 | c2 | c3 | c4 | c5 | c6
        · -- 条件 (I)
          by_cases j1one : Lng N - 1 = 1
          · rw [hCIj1 N n hNR mono (by omega) c1 (by omega)]
            exact OT_B_operB_numBT_tot ih _
          · have j1gt : 1 < Lng N - 1 := by omega
            by_cases j0z : parent N 0 (Lng N - 1) = 0
            · rw [hCIj0 N n hNR mono j1gt c1 j0z (by omega)]
              exact OT_B_operB_numBT_tot ih _
            · rw [hI N n hN mono j1gt c1 (by omega) n2]
              exact OT_B_operB_numBT_tot ih _
        · -- 条件 (II)
          have j1gt : 1 < Lng N - 1 := condII_j1gt_tot N L hp0 c2
          obtain ⟨k, hk⟩ := hII N n hN mono j1gt c2 n2
          rw [hk]; exact OT_B_operB_numBT_tot ih _
        · -- 条件 (III)
          simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at c3
          have j1gt : 1 < Lng N - 1 := cond34_j1gt_tot N L hp0 hp c3.1.1 c3.1.2
          refine hOTint N n hN mono j1gt (Or.inl ?_) ih n2
          simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq]
          exact c3
        · -- 条件 (IV)
          simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at c4
          have j1gt : 1 < Lng N - 1 := cond34_j1gt_tot N L hp0 hp c4.1.1 c4.1.2
          refine hOTint N n hN mono j1gt (Or.inr (Or.inl ?_)) ih n2
          simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true']
          exact c4
        · -- 条件 (V): `j₀ + 1 < j₁` から直ちに `1 < j₁`
          have j1gt : 1 < Lng N - 1 := by
            simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq,
              beq_iff_eq] at c5
            have hlt : lastParent N + 1 < Lng N - 1 := c5.2
            omega
          exact hOTint N n hN mono j1gt (Or.inr (Or.inr c5)) ih n2
        · -- 条件 (VI)
          by_cases j1one : Lng N - 1 = 1
          · rw [hCVIj1 N n hNR mono (by omega) c6 hp (by omega)]
            exact OT_B_operB_numBT_tot ih _
          · have j1gt : 1 < Lng N - 1 := by omega
            by_cases hadm : adm N (transJ0 N) = true
            · rw [hCVIa N n hN mono c6 j1gt hadm (by omega)]
              exact OT_B_operB_numBT_tot ih _
            · rw [hCVIn N n hN mono c6 j1gt hadm (by omega)]
              exact OT_B_operB_numBT_tot ih _
      · -- 複項: `OTmulti`
        have mono' : monoT N = false := by simpa using mono
        have mu : multiT N = true := by simp [multiT, notzT, mono']
        exact hOTmulti N n hN mu ih n2 predc

/-! ## 原文の命題（green-modulo、露出 `Prop` 12 本） -/

/-- **§8.7 補題（`Trans` が標準形を保つこと）**（原文 `tmp/content.md` 6122、
Isabelle 逐語 `p_8_7_Trans_preserves_OT` ＝ `isabelle/pss_paper.thy`:2317、
無条件版 `y5_Trans_OT_B` ＝ `isabelle/layerC/pss_scratch.thy`:14205）。

`M ∈ ST_PS` なら `Trans M ∈ OT_B`。停止性定理が乗る 2 本柱のうちの 1 本
（もう 1 本は基本列の降下性 `p_8_7_fseq_descend`）。

Isabelle 側では census（`oi12_census`(1)）が `SETLE1`/`FINRC` まで含めて
すべて閉じているので、露出した 12 本の `Prop` は移植すればそのまま外れる。 -/
theorem p_8_7_Trans_preserves_OT
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq)
    (M : PS) (hM : STPS M) : Trans M ∈ OT_B :=
  Trans_preserves_OT_dispatch_tot hI hII hOTint hOTpred hOTmulti hZC hCIn1
    hCIj0 hCIj1 hCVIj1 hCVIa hCVIn M hM

/-- `8.6-Trans-fseq-condVI.lean`:247 の名前付き仮定 `TransPreservesOT`
（＝ `∀ M, STPS M → Trans M ∈ OT_B`）と**同一形**。同ファイルを import すると
循環するのでここでは形を書き下すに留める（drop-in であることの明示）。 -/
theorem Trans_preserves_OT
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq) :
    ∀ M : PS, STPS M → Trans M ∈ OT_B :=
  fun M hM => p_8_7_Trans_preserves_OT hI hII hOTint hOTpred hOTmulti hZC hCIn1
    hCIj0 hCIj1 hCVIj1 hCVIa hCVIn M hM

/-- `8.7-fseq-descend.lean`:67 の名前付き仮定 `FseqDesc_Trans_preserves_OT`
（＝ `∀ N, STPS N → monoT N = true → 1 < Lng N - 1 → Trans N ∈ OT_B`）と**同一形**。
本ファイルの結論はこれより強い（`monoT`/`Lng` の制限が不要）ので、降下柱側の
16 本の `Prop` のうちこの 1 本はそのまま外れる。 -/
theorem Trans_preserves_OT_fseqdesc_form
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq) :
    ∀ N : PS, STPS N → monoT N = true → 1 < Lng N - 1 → Trans N ∈ OT_B :=
  fun N hN _ _ => p_8_7_Trans_preserves_OT hI hII hOTint hOTpred hOTmulti hZC
    hCIn1 hCIj0 hCIj1 hCVIj1 hCVIa hCVIn N hN

/-! ## 回帰ベクトル（基底の具体値。`Prop` の非空虚性検証は
`python/audit_8_7_trans_preserves_OT.py` を参照） -/

#guard Trans (diagSeq 2 5) == Dprin (2 : ℕ∞) (Dprin (5 : ℕ∞) BZero)
#guard isOT_BT (Trans (diagSeq 2 5))
#guard isOT_BT (Trans (diagSeq 0 3))
#guard Trans (diagSeq 4 4) == Dprin (4 : ℕ∞) BZero
#guard Trans (diagSeq 0 0) == BZero
#guard isOT_BT (Trans (diagSeq 4 4))

#print axioms p_8_7_Trans_preserves_OT
#print axioms Trans_preserves_OT
#print axioms Trans_preserves_OT_fseqdesc_form

end PSS
