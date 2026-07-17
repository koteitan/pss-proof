import «8».«8.7-fseq-descend»
import «7».«7.2-scb-fseq»
import «7».«7.4-Trans-Mark-Pred»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-c1-c2-order»
import «6».«6.8-standard-slice-Br-descending»
import «5».«5.1-ancestor-basic»

/-!
# §8.1 命題（条件(I)の下での `Trans` と基本列の交換関係）

- 原文: `tmp/content.md` 2827（§8.1）。逐語形は `p_8_1_Trans_fseq_condI`
  (isabelle/pss_paper.thy:1769):
  `M ∈ RT_PS ∩ PT_PS`、`n ∈ ℕ₊`、`j₁ = Lng M - 1 > 1`、条件(I) のとき
  (1) `Trans(M[n]) = Trans(M)[n-1]`、(2) `Trans(M[n]) < Trans(M)`。
  `a[k] = operB a (numBT k)`、`<` = `lessBT`、`n ∈ ℕ₊` = `1 ≤ n`。
- 訂正: **本命題に対する訂正は無い**。A20/A21 は §8.1 の *別命題*
  「補題（条件(I)か(III)の下での c₁ 前後の具体表示）」(`p_8_1_condI_III_c1_around`)
  の part(1)/part(5) に対するもの（corrections.md:763/805、
  pss_scratch.thy:19327 も同旨）で、本命題には掛からない。
  corrections-old.md の A20 言及はガード緩和の注記であり取り下げではない。
- Isabelle:
  - 最終形 `y3g_p_8_1_Trans_fseq_condI` (layerC/pss_scratch.thy:14826)
  - 交換 (1) `y3g_condI_exchange1_rtps` (同 :14693)
  - 降下 (2) `y3g_condI_descent_rtps` (同 :14760)
  - 帰納足場 `m_8_1_Trans_fseq_condI_comm_append_reduce` (layerB/pss_wip.thy:33418)
  - n=1 基底 `m_8_1_Trans_fseq_condI_n1` (同 :33271)、
    その中身 `m_8_1_operB_numBT0_Pred` (同 :33088)
  - 一歩追加 `operI_Suc_append` (同 :17621)
  - `j₀>0` 側 `m_8_1_stepT_j0pos_of_lhs_closed` (同 :37137)、
    その入力 `scx_condI_j0pos_masterCF` (同 :83639)
  - Buchholz 側 `operB_marked_scb_value` (同 :37100) ＝ `m_7_2_scb_fseq_scb` の読み戻し
  - `j₀=0` 側 `m_8_1_condI_oper_pow_j0zero` (同 :33616)、
    `m_8_1_Trans_replicate_pred_condI` (同 :37059)、`m_8_1_operB_condI_value` (同 :37012)
- 依存（ビルド済みのみ import）: `8.7-fseq-descend`（`FseqDesc_exchI` の drop-in 先、
  および既出 brick `FseqDesc_operI_j0zero_trans_mult` /
  `FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1` の再利用）、
  `7.2-scb-fseq`（`scb_fseq_decomp` ＝ `m_7_2_scb_fseq_scb`、`scb_fseq_succ`、
  `operB_scb_spine`）、`7.4-Trans-Mark-Pred`（`Trans_Mark_Pred` ＝ Isabelle
  `s84c2_Trans_c2_decomp` の役割）、`7.4-Mark-Trans-repr`
  （`Mark_transJm1_eq_transC2`）、`7.3-c1-c2-order`（`transC1_single_principal`、
  `principal_reconstruct`）、`6.8-standard-slice-Br-descending`
  （`oper_d0zero_expand_68`）、`5.1-ancestor-basic`。
  推移的に `7.3-Pred-Trans-descend`（`Pred_Trans_descend`、`scbext_lessBT`）、
  `6.7-standard-reduced`（`STPS_RTPS`）、`5.3-pred-is-oper1`（`pred_is_oper1`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。

  **本ファイルが新たに露出する `Prop` は `CondI_masterCF` の 1 本だけ**
  （Isabelle `scx_condI_j0pos_masterCF`、r28-STEPCORE ブロック ≈2000 行）。
  `j₀ = 0` 側に必要な 2 本は**ビルド済 `8.7-fseq-descend` が既に露出している**
  `FseqDesc_operI_j0zero_trans_mult` /
  `FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1` をそのまま再利用する
  （新規の仮定を増やさない）。
  **`FseqDesc_exchI` の drop-in `exchI_holds` は `CondI_masterCF` 1 本のみに依存**
  （`0 < parent` を仮定するので `j₀ = 0` 分岐が呼ばれない）。

  自前で証明したもの: `operI_Suc_append_ci`（一歩追加、Isabelle `operI_Suc_append`）、
  `operB_marked_scb_value_ci`（Buchholz 側の値）、`operB_numBT0_Pred_ci`
  （n=1 基底 ＝ Isabelle `m_8_1_operB_numBT0_Pred`。Isabelle は mono surgery 分岐を
  書き下して共有 scb 分解を再構成するが、Lean は §7.4 の `Trans_Mark_Pred`(A46 形)を
  基点 `j₋₁` に当てるだけで済む — **条件(I) は `adm M j₀` を含むので `j₋₁ = j₀`**
  (`condI_transJm1_eq_ci`) という所が効く）、`comm_append_reduce_ci`（帰納足場）、
  `stepT_j0pos_of_lhs_closed_ci`、`operB_condI_value_ci`、`multBT_lt_top_ci`
  （Isabelle `d2x_multBT_lt_top`）、降下 (2) の両分岐、組み立て。

  Isabelle からの短縮: `m_8_1_condI_oper_pow_j0zero` /
  `m_8_1_Trans_replicate_pred_condI`（`M[n] = (Pred M)^n` の
  `concat (replicate …)` 迂回）は **不要**。`stepT` を `oper M k ++ B = oper M (k+1)`
  の `oper` 形で閉じるので、`j₀ = 0` 側は `operI_j0zero_trans_mult`（LHS）と
  `m_8_1_operB_condI_value`（RHS）を直結できる。

- 数値検証: `python/audit_81_condI.py`（標準形プール = `diagSeq` を `oper` で閉じたもの。
  ランダムなペア数列はほぼ簡約形にならないので、これが唯一の実プール）。
  **`CondI_masterCF` は空虚でも偽でもない**ことを結論まで確認済み
  （2026-07-17、`umax=4/vmax=7/gens=4/lenCap=10` → RT_PS ∩ PT_PS 962 形）:
  * 仮定集合（`Lng-1>1 ∧ condI ∧ hasParent`）は **129 例**で非空虚。
    内訳 = `j₀>0`（`FseqDesc_exchI` ／ masterCF の regime）**112 例**、`j₀=0` **17 例**。
  * `CondI_masterCF`: 112/112 で `dM` の証人が存在し `lhsCF`（`k=1..2`）も成立、**反例 0**。
    〔Wave F の教訓 — blueprint が空虚（仮定が充足不能）でないかを移植前に確認する — の適用。
    `m_8_4_..._corrected_condIII` のような取り下げ訂正への依存も無い（下記 訂正欄）。〕
  * 交換 (1)・降下 (2): `n = 1..3`、129 例で **反例 0**。
-/

namespace PSS

/-! ## Isabelle `kind0_parent_facts` (pss_wip.thy:13671) -/

/-- 条件(I) の下で最終列の行 0 の親は行 `i₁ = 0`。 -/
private theorem idx1_zero_ci (M : PS) (e1z : entry M 1 (Lng M - 1) = 0) :
    idx1 M (Lng M - 1) = 0 := by simp [idx1, e1z]

/-- 親辺 `nextR M 0 j₀ j₁` は `hasParent` から取れる。 -/
private theorem nextR_parent_ci (M : PS) (i j₁ : ℕ)
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

/-- Isabelle `kind0_parent_facts` の (2)(3)(4)(5)(6)。 -/
private theorem kind0_parent_facts_ci (M : PS)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true ∧
    parent M 0 (Lng M - 1) < Lng M - 1 ∧
    ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
    hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
    1 < Lng M := by
  have hpar := nextR_parent_ci M 0 (Lng M - 1) hp0
  have h0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hpar
  have hfacts := h0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hfacts
  have hlt : parent M 0 (Lng M - 1) < Lng M - 1 := hfacts.1.1.2
  have he0 : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := hfacts.1.2
  refine ⟨h0, hlt, ?_, ?_, by omega⟩
  · omega
  · rw [idx1_zero_ci M e1z]; exact hp0

/-! ## Isabelle `operI_Suc_append` (pss_wip.thy:17621) -/

/-- 条件(I)（kind-0）の一歩追加: `M[n+1] = M[n] ++ B`、
`B = (M_j)_{j=j₀}^{j₁-1}`。 -/
private theorem operI_Suc_append_ci (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    oper M (n + 1) = oper M n ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
  obtain ⟨_, _, hnz, hp, hL⟩ := kind0_parent_facts_ci M hp0 e1z
  have hn := oper_d0zero_expand_68 M n hL hnz hp e1z
  have hsn := oper_d0zero_expand_68 M (n + 1) hL hnz hp e1z
  simp only at hn hsn
  rw [hn, hsn, List.range_succ, List.flatMap_append]
  simp [List.append_assoc]

/-! ## Buchholz 側の値 — Isabelle `operB_marked_scb_value` (pss_wip.thy:37100) -/

/-- Isabelle `operB_marked_scb_value`: 条件(I) の marked principal
`D_u(t₀ +_B D_v(t₁ +_B D₀0))` での scb 分解を持つ項の基本列は、末尾 `D₀0` を潰して
内側 principal を `n+1` 個に畳む。`m_7_2_scb_fseq_scb`（Lean `scb_fseq_decomp`）を
`unflatBT_flat` で読み戻すだけ。 -/
private theorem operB_marked_scb_value_ci {t₀ t₁ t : BT} {u v n : ℕ}
    {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b) :
    operB t (numBT n) =
      unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b) := by
  have hd2 := scb_fseq_decomp (n := n) ht₀ ht₁ ht hd
  calc operB t (numBT n)
      = unflatBT (flatBT (operB t (numBT n))) := (unflatBT_flat _).symm
    _ = _ := by rw [hd2.1]

/-! ## n=1 基底 — Isabelle `m_8_1_operB_numBT0_Pred` (pss_wip.thy:33088)

Isabelle は mono surgery 分岐を書き下して共有 scb 分解 `s84c2_Trans_c2_decomp` を
再構成するが、Lean には既に §7.4 の `Trans_Mark_Pred`（訂正 A46 形）があるので、
基点 `m = j₋₁ = Adm_M(j₀)` に適用すれば同じものが直接出る。
`Mark (Pred M) (transJm1 M) = transC1 M` は定義そのもの、
`Mark M (transJm1 M) = transC2 M` は `Mark_transJm1_eq_transC2`（§7.4）。 -/

private theorem domTagList_snoc_ci (ps : List BP) (p : BP) :
    domTagList (ps ++ [p]) = domTagBP p := by
  induction ps with
  | nil => simp [domTagList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [domTagList]
      | cons r rs => simpa [domTagList] using ih

private theorem bOperCore_list_snoc_ci (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      rcases hb : bOperCore (.princ p z) with ⟨cs⟩
      simp [addBT, BZero]
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih]
          rcases hb : bOperCore (.princ p z) with ⟨cs⟩
          simp [addBT]

/-- `D_v(t₂ +_B D₀0)` の基本列は `(D_v t₂) ×_B (n+1)`。`scb_fseq_succ` の
`t₀ = 0_B` 特殊化だが、`v : ℕ∞` を一般のまま扱う（`transV M` は `ℕ∞`）。 -/
theorem operB_succ_body_ci (t₂ : BT) (v : ℕ∞) (n : ℕ) :
    operB (Dprin v (addBT t₂ (Dprin 0 BZero))) (numBT n) =
      multBT (Dprin v t₂) (n + 1) := by
  rcases t₂ with ⟨ps₂⟩
  simp [operB, bOperCore, bOperCore_list_snoc_ci, domTagList_snoc_ci,
    addBT, numBT, numNat, Dprin, BZero, domTag, domTagBP]

/-- `D_v(t₂ +_B D₀0)` の domain tag は `naturals`（`v` に依らない）。 -/
private theorem domTagBP_succ_body_ci (t₂ : BT) (v : ℕ∞) :
    domTagBP (.db v (addBT t₂ (Dprin 0 BZero))) = .naturals := by
  rcases t₂ with ⟨ps₂⟩
  simp [addBT, Dprin, BZero, domTagBP, domTag, domTagList_snoc_ci]

/-- 条件(I) は `j₀` の許容性を含むので `j₋₁ = Adm_M(j₀) = j₀`。 -/
private theorem condI_transJm1_eq_ci (M : PS) (hI : transCondI M = true) :
    transJm1 M = transJ0 M := by
  simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
  simp [transJm1, transJ0, Adm, hI.2]

/-- Isabelle `s84c2_Trans_c2_decomp` に相当する共有 scb 分解。
条件(I) では基点 `j₋₁ = j₀` なので §7.4 の `Trans_Mark_Pred`（A46 形）が直接効く。 -/
private theorem shared_scb_condI_ci (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (hI : transCondI M = true) :
    ∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (Mark M (transJm1 M))) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hjm : transJm1 M = transJ0 M := condI_transJm1_eq_ci M hI
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hadm : adm M (transJ0 M) = true := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [transJ0] using hI.2
  have hle : leR M 0 (transJ0 M) (Lng M - 1) = true := by
    have hnx : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
      simpa [transJ0, lastParent, lastIdx] using
        hasParent_next_fseq M 0 (Lng M - 1) hp
    exact nextR0_leR M _ _ hnx
  have hmk : Marked M (transJm1 M) := by
    rw [hjm]; exact ⟨hM, hadm, hle⟩
  obtain ⟨⟨s, b⟩, ⟨hd1, hd2⟩, _⟩ :=
    Trans_Mark_Pred M (transJm1 M) hmk hR (by omega)
  exact ⟨s, b, hd1, hd2⟩

/-- `Lng M > 1` なら `Trans M ≠ 0_B`。 -/
private theorem Trans_ne_zero_ci (M : PS) (hM : TPS M) (hlen : 1 < Lng M) :
    Trans M ≠ BZero := by
  intro h0
  have hz : zeroT M = true := (Trans_preserves_zeroT M hM).mpr h0
  simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
  omega

/-- Isabelle `m_8_1_operB_numBT0_Pred` (pss_wip.thy:33088):
条件(I) の下で `Trans(M)[0] = Trans(Pred M)`。 -/
private theorem operB_numBT0_Pred_ci (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) (hI : transCondI M = true) :
    operB (Trans M) (numBT 0) = Trans (Pred M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hj1 : 0 < transJ1 M := by simp [transJ1, lastIdx]; omega
  have hT1 : transT1 M ≠ BZero := by simpa [transT1] using ht₁
  have he1z : entry M 1 (lastIdx M) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI; exact hI.1
  obtain ⟨s, b, hd1, hd2⟩ := shared_scb_condI_ci M hR hmono hlen hI
  rw [Mark_transJm1_eq_transC2 M hR hmono hlen ht₁] at hd2
  -- `c₁` は単一 principal
  have hc1 : transC1 M = Dprin (transV M) (transT2 M) :=
    principal_reconstruct (transC1_single_principal M hR hmono hj1 hT1)
  -- 条件(I) 分岐の `c₂`
  have hc2 : transC2 M =
      Dprin (transV M) (addBT (transT2 M) (Dprin 0 BZero)) := by
    simp [transC2, transC2Core, hI, he1z]
  set v := transV M with hv
  set t₂ := transT2 M with ht₂
  let p : BP := .db v (addBT t₂ (Dprin 0 BZero))
  let p' : BP := .db v t₂
  have hocc : flatBT (Trans M) = s ++ flatBP p ++ b := by
    have := hd2.1; rw [hc2] at this; simpa [p, Dprin, flatBT] using this
  have hdfp : dfree_BP p = true := by
    have hipt := hd2.2.1 (Trans_ne_zero_ci M hM hlen)
    rw [hc2] at hipt
    obtain ⟨q, hq, hqf⟩ := hipt
    have hqp : q = p :=
      flatBP_injective (p := q) (q := p)
        (by simpa [p, Dprin, flatBT] using hqf.symm)
    rwa [hqp] at hq
  have hop : operB (.trm [p]) (numBT 0) = .trm [p'] := by
    have h := operB_succ_body_ci t₂ v 0
    simpa [p, p', Dprin, multBT, addBT, BZero] using h
  obtain ⟨_, hflat⟩ :=
    operB_scb_spine hocc hd2.2.2 hdfp (domTagBP_succ_body_ci t₂ v) hop
  apply flatBT_injective
  rw [hflat]
  have := hd1.1
  rw [hc1] at this
  simpa [p', Dprin, flatBT] using this.symm

/-- Isabelle `m_8_1_Trans_fseq_condI_n1` (pss_wip.thy:33271): 交換 (1) の `n = 1` 基底。 -/
private theorem Trans_fseq_condI_n1_ci (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true) :
    Trans (oper M 1) = operB (Trans M) (numBT 0) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have ht₁ : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz : zeroT (Pred M) = true :=
      (Trans_preserves_zeroT (Pred M) (RTPS_TPS _ (RTPS_Pred M hR))).mpr h0
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    rw [length_Pred M hlen] at hz
    omega
  rw [← pred_is_oper1 M hM hlen]
  exact (operB_numBT0_Pred_ci M hR hmono hlen ht₁ hI).symm

/-! ## 帰納足場 — Isabelle `m_8_1_Trans_fseq_condI_comm_append_reduce` (pss_wip.thy:33418)

原文の `n` に関する帰納法のうち、regime に依らない二つの半分（`n=1` 基底と一歩追加
`M[k+1] = M[k] ++ B`）を落とし、残りを一本の仮定 `stepT` に集約する。 -/

/-- 条件(I) の一歩追加ブロック `B = (M_j)_{j=j₀}^{j₁-1}`。 -/
private def blockB_ci (M : PS) : PS :=
  (List.range' (parent M 0 (Lng M - 1))
    (Lng M - 1 - parent M 0 (Lng M - 1))).map
    (fun j => (entry M 0 j, entry M 1 j))

private theorem comm_append_reduce_ci (M : PS) (n : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (stepT : ∀ k, 1 ≤ k →
      Trans (oper M k ++ blockB_ci M) = operB (Trans M) (numBT k))
    (hn : 1 ≤ n) :
    Trans (oper M n) = operB (Trans M) (numBT (n - 1)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  match n, hn with
  | 1, _ => simpa using Trans_fseq_condI_n1_ci M hR hmono hj1 hI
  | (k + 2), _ =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hap : oper M (k + 2) = oper M (k + 1) ++ blockB_ci M := by
        simpa [blockB_ci] using operI_Suc_append_ci M (k + 1) hp0 he1z
      rw [hap, stepT (k + 1) hk1]
      simp

/-! ## `j₀ > 0` 側の `stepT` — Isabelle `m_8_1_stepT_j0pos_of_lhs_closed`
(pss_wip.thy:37137) -/

private theorem stepT_j0pos_of_lhs_closed_ci (M : PS) {t₀ t₁ : BT} {u v k : ℕ}
    {s b : List Sym}
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (he1z : entry M 1 (Lng M - 1) = 0)
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (htT : Trans M ∈ T_B)
    (hd : scb_decomp (Trans M) s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b)
    (hlhs : ∀ j, 1 ≤ j → Trans (oper M (j + 1)) =
      unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (j + 1)))) ++ b))
    (hk1 : 1 ≤ k) :
    Trans (oper M k ++ blockB_ci M) = operB (Trans M) (numBT k) := by
  have hap : oper M (k + 1) = oper M k ++ blockB_ci M := by
    simpa [blockB_ci] using operI_Suc_append_ci M k hp0 he1z
  rw [← hap, hlhs k hk1]
  exact (operB_marked_scb_value_ci ht₀ ht₁ htT hd).symm

/-! ## `j₀ = 0` 側の `stepT` — Isabelle `m_8_1_operB_condI_value` (pss_wip.thy:37012)

Isabelle は `M[n] = (Pred M)^n` (`m_8_1_condI_oper_pow_j0zero`) を経由して
`m_8_1_Trans_replicate_pred_condI` を作るが、Lean 側の `stepT` は既に
`oper M k ++ B = oper M (k+1)`（`operI_Suc_append_ci`）で `oper` 形に閉じているので、
`concat (replicate …)` の迂回は不要。必要なのは
`operI_j0zero_trans_mult`（LHS）と `m_8_1_operB_condI_value`（RHS）の 2 本だけで、
どちらも **ビルド済 `8.7-fseq-descend` が既に露出している `Prop`** で賄える。 -/

/-- Isabelle `m_8_1_operB_condI_value`。 -/
private theorem operB_condI_value_ci
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (M : PS) (m : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0z : parent M 0 (Lng M - 1) = 0) :
    operB (Trans M) (numBT m) = multBT (Trans (Pred M)) (m + 1) := by
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  have hjm : transJm1 M = 0 := by
    simp [transJm1, transJ0, lastParent, lastIdx, hj0z, Adm, adm_zero M]
  obtain ⟨t₁, ⟨htp, htm⟩, _⟩ := hA M hR hmono hj1 hjm (Or.inl hI)
  have htm' : Trans M = Dprin (entry M 1 0 : ℕ∞)
      (addBT t₁ (Dprin 0 BZero)) := by rw [htm, he1z]; norm_num
  rw [htm', operB_succ_body_ci, htp]

/-! ## `Trans M` が `T_B` に居ること -/

private theorem Trans_mem_T_B_ci (M : PS) (hR : RTPS M) : Trans M ∈ T_B :=
  (Trans_Mark_invariant M hR).1

/-! ## 露出した `Prop`（Isabelle 名 1:1、GREEN-MODULO の仮定）

`8.7-fseq-descend` が既に露出している 2 本
（`FseqDesc_operI_j0zero_trans_mult` ＝ Isabelle `operI_j0zero_trans_mult`、
`FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1` ＝ Isabelle
`m_8_2_subexpr_component_Pred_Adm0_clause1`）はそのまま再利用し、
本ファイルが新たに露出するのは次の 1 本だけ。 -/

/-- Isabelle `scx_condI_j0pos_masterCF` (pss_wip.thy:83639)。
条件(I)・`j₀ > 0` の marking-nesting 閉形式パッケージ:
`Trans M` の marked principal での scb 分解 `dM` と、反復の閉形式 `lhsCF`。
Isabelle 側は r28-STEPCORE ブロック（pss_wip.thy:82085–83900、`scx_host_basic` /
`scx_N_facts` / `scx_mark_pin` / `scx_stepA` / `scx_stepB` の約 2000 行）。 -/
def CondI_masterCF : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondI M = true →
    0 < parent M 0 (Lng M - 1) →
    ∃ (s b : List Sym) (u v : ℕ) (t₀ t₁ : BT), t₀ ∈ T_B ∧ t₁ ∈ T_B ∧
      scb_decomp (Trans M) s
        (flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b ∧
      (∀ k, 1 ≤ k → Trans (oper M (k + 1)) =
        unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (k + 1)))) ++ b))

/-! ## 交換 (1) — Isabelle `y3g_condI_exchange1_rtps` (pss_scratch.thy:14693)

Isabelle の監査結果どおり、`M ∈ ST_PS` は不要（`scx_*` 系は全て `RT_PS` 級）で、
原文の定義域 `RT_PS ∩ PT_PS` でそのまま成立する。 -/

theorem condI_exchange1 (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true) (hn : 1 ≤ n) :
    Trans (oper M n) = operB (Trans M) (numBT (n - 1)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  have stepT : ∀ k, 1 ≤ k →
      Trans (oper M k ++ blockB_ci M) = operB (Trans M) (numBT k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos (parent M 0 (Lng M - 1)) with hz | hpos
    · -- `j₀ = 0`: コピー加法性
      have hap : oper M (k + 1) = oper M k ++ blockB_ci M := by
        simpa [blockB_ci] using operI_Suc_append_ci M k hp0 he1z
      rw [← hap, hMul M k hR hp0 he1z hz hj1,
        operB_condI_value_ci hA M k hR hmono hj1 hI hz]
    · -- `j₀ > 0`: marking-nesting 閉形式
      obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, hlhs⟩ :=
        hCF M hR hmono hj1 hI hpos
      exact stepT_j0pos_of_lhs_closed_ci M hp0 he1z ht₀ ht₁
        (Trans_mem_T_B_ci M hR) hd hlhs hk
  exact comm_append_reduce_ci M n hR hmono hj1 hI stepT hn

/-! ## 降下 (2) — Isabelle `y3g_condI_descent_rtps` (pss_scratch.thy:14760) -/

/-- Isabelle `d2x_multBT_replicate`。 -/
private theorem multBT_single_ci (p : BP) (m : ℕ) :
    multBT (.trm [p]) m = .trm (List.replicate m p) := by
  induction m with
  | zero => rfl
  | succ k ih => rw [multBT, ih]; simp [addBT, List.replicate_succ']

/-- Isabelle `d2x_multBT_lt_top` (pss_wip.thy:62017): `k` 個の複製
`(D_v t₁)^k` は単一の上位 principal `D_v(t₁ +_B D₀0)` より真に小さい。 -/
private theorem multBT_lt_top_ci (v : ℕ∞) (t₁ : BT) (k : ℕ) :
    lessBT (multBT (Dprin v t₁) k)
      (Dprin v (addBT t₁ (Dprin 0 BZero))) = true := by
  have hne : (Dprin 0 BZero : BT) ≠ BZero := by simp [Dprin, BZero]
  have hbody : lessBT t₁ (addBT t₁ (Dprin 0 BZero)) = true :=
    lessBT_addBT_self t₁ _ hne
  have hp : lessBP (.db v t₁) (.db v (addBT t₁ (.trm [.db 0 BZero]))) = true := by
    simp only [Dprin] at hbody
    simp [lessBP, hbody]
  rw [show (Dprin v t₁ : BT) = .trm [.db v t₁] from rfl, multBT_single_ci]
  cases k with
  | zero => simp [Dprin, lessBT, lessBPList]
  | succ j => simp [List.replicate_succ, Dprin, lessBT, lessBPList, hp]

theorem condI_descent (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true) (hn : 1 ≤ n) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  rcases Nat.lt_or_ge 1 n with hbig | hone
  · -- `n > 1`
    have hexch := condI_exchange1 hCF hMul hA M n hR hmono hj1 hI hn
    rcases Nat.eq_zero_or_pos (parent M 0 (Lng M - 1)) with hz | hpos
    · -- `j₀ = 0`
      have hjm : transJm1 M = 0 := by
        simp [transJm1, transJ0, lastParent, lastIdx, hz, Adm, adm_zero M]
      obtain ⟨t₁, ⟨htp, htm⟩, _⟩ := hA M hR hmono hj1 hjm (Or.inl hI)
      have htm' : Trans M = Dprin (entry M 1 0 : ℕ∞)
          (addBT t₁ (Dprin 0 BZero)) := by rw [htm, he1z]; norm_num
      have hval := operB_condI_value_ci hA M (n - 1) hR hmono hj1 hI hz
      rw [hexch, hval, htp, htm']
      exact multBT_lt_top_ci _ t₁ (n - 1 + 1)
    · -- `j₀ > 0`
      obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, _⟩ :=
        hCF M hR hmono hj1 hI hpos
      have hdOp := scb_fseq_decomp (n := n - 1) ht₀ ht₁ (Trans_mem_T_B_ci M hR) hd
      have hfMn : flatBT (Trans (oper M n)) =
          s ++ flatBP (.db (u : ℕ∞)
            (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n - 1 + 1)))) ++ b := by
        rw [hexch]; simpa [Dprin, flatBT] using hdOp.1
      have hfTM : flatBT (Trans M) =
          s ++ flatBP (.db (u : ℕ∞)
            (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero))))) ++ b := by
        simpa [Dprin, flatBT] using hd.1
      have hbodyLt : lessBT (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n - 1 + 1)))
          (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))) = true :=
        addBT_lt_right_bf t₀ _ _ (multBT_lt_top_ci _ t₁ (n - 1 + 1))
      have hcoreLt : lessBP
          (.db (u : ℕ∞) (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n - 1 + 1))))
          (.db (u : ℕ∞)
            (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero))))) = true := by
        simp [lessBP, hbodyLt]
      exact scbext_lessBT hfMn hfTM hd.2.2 hcoreLt
  · -- `n = 1`
    have hn1 : n = 1 := by omega
    subst hn1
    rw [← pred_is_oper1 M hM hlen]
    exact Pred_Trans_descend M hM hlen

/-! ## 原文の命題（`p_8_1_Trans_fseq_condI`, pss_paper.thy:1769）

`M ∈ RT_PS ∩ PT_PS`（Lean: `RTPS M` ＋ `monoT M = true`）、`n ≥ 1`、
`Lng M - 1 > 1`、条件(I)。Isabelle `y3g_p_8_1_Trans_fseq_condI` と逐語一致。 -/

theorem Trans_fseq_condI (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true) :
    Trans (oper M n) = operB (Trans M) (numBT (n - 1)) ∧
    lessBT (Trans (oper M n)) (Trans M) = true :=
  ⟨condI_exchange1 hCF hMul hA M n hR hmono hj1 hI hn,
   condI_descent hCF hMul hA M n hR hmono hj1 hI hn⟩

/-- Isabelle 互換名。 -/
theorem p_8_1_Trans_fseq_condI (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1)
    (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true) :
    Trans (oper M n) = operB (Trans M) (numBT (n - 1)) ∧
    lessBT (Trans (oper M n)) (Trans M) = true :=
  Trans_fseq_condI hCF hMul hA M n hR hmono hn hj1 hI

/-! ## `8.7-fseq-descend` の `FseqDesc_exchI` への drop-in

`FseqDesc_exchI` は `0 < parent N 0 (Lng N - 1)` を仮定するので、`j₀ = 0` 分岐は
そもそも呼ばれない。したがって drop-in は `CondI_masterCF` **1 本だけ**に依存する。 -/

theorem exchI_holds (hCF : CondI_masterCF) : FseqDesc_exchI := by
  intro N m hS hmono hj1 hI _hpos hm
  have hR : RTPS N := STPS_RTPS N hS
  have hM : TPS N := RTPS_TPS N hR
  have hlen : 1 < Lng N := by omega
  have hp0 : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have he1z : entry N 1 (Lng N - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  have stepT : ∀ k, 1 ≤ k →
      Trans (oper N k ++ blockB_ci N) = operB (Trans N) (numBT k) := by
    intro k hk
    obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, hlhs⟩ :=
      hCF N hR hmono hj1 hI _hpos
    exact stepT_j0pos_of_lhs_closed_ci N hp0 he1z ht₀ ht₁
      (Trans_mem_T_B_ci N hR) hd hlhs hk
  exact comm_append_reduce_ci N m hR hmono hj1 hI stepT (by omega)

#print axioms condI_exchange1
#print axioms condI_descent
#print axioms Trans_fseq_condI
#print axioms p_8_1_Trans_fseq_condI
#print axioms exchI_holds

end PSS
