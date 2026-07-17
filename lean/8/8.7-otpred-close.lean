import «8».«8.7-otdisp-OTpred»
import «8».«8.7-otpred-brickB»
import «8».«8.7-otpred-brickC0»
import «8».«8.7-otpred-brickD»
import «8».«8.6-condVI-props»
import «8».«8.7-Trans-preserves-OT»
import «6».«6.2-P-components-nonmulti»
import «6».«6.7-standard-P-components»
import «6».«6.8-standard-slice-Br-descending»
import «7».«7.3-Trans-preserves-monoT»
import «7».«7.3-Pred-Trans-descend»
import «8».«8.7-descend-last2»
import «8».«8.7-otdisp-OTmulti»
import «8».«8.7-fseq-descend-props»

/-!
# §8.7 `OTdisp_OTpred` の閉包 — Brick C（`od4_site_c2`）から `od4_OTpred_final` まで

- Isabelle（設計図）: `isabelle/layerC/pss_scratch.thy` の `r54/r55-od4` 節
  ＋ `isabelle/layerB/pss_wip.thy` の `opx_OTpred_*` 節。
  * Brick C  `od4_site_c2`             (`layerC`:634) → `od4_site_c2`
  * Brick D  `od4_master_R`            (`layerC`:760) → `od4_master_R`
  * Brick E  `od4_OTpred_mono`         (`layerC`:803) → `od4_OTpred_mono`（無仮定 mono ステップ）
  * 複項脚 `opx_OTpred_multi_of_mono`  (`layerB`:116306) → `opx_OTpred_multi_of_mono`
  * 束ね `opx_OTpred_of_residuals`     (`layerB`:116573) → `OTdisp_OTpred_of_multiResidual`
- 依存（ビルド済みのみ import）:
  * Brick A `«8».«8.7-otdisp-OTpred»`（`od4R_op`/`od4sz_op`/`od4R_isOT`/`od4R_OT_B`）
  * Brick B `«8».«8.7-otpred-brickB»`（`od4_scbext_R`）
  * Brick C0 `«8».«8.7-otpred-brickC0»`（`od4_condVI_nadm_c1`）
  * Brick D `«8».«8.7-otpred-brickD»`（`od4_master_R_of_site`）
  * `«8».«8.6-condVI-props»`（PUBLIC `condVI_transC2_v6p`/`condVI_transC1_adm_v6p`）
  * `«8».«8.7-Trans-preserves-OT»`（`OTdisp_OTpred` の定義／`STPS_RTPS` ほか推移）
  * 複項脚用: `«8».«8.7-descend-last2»`（`f7x_Trans_append_Pblocks_holds`）,
    `«8».«8.7-otdisp-OTmulti»`（`OT_append_corr_om`）,
    `«8».«8.7-fseq-descend-props»`（`FseqDesc_m_6_2_P_oper_2_holds`）,
    `«6».«6.7-standard-P-components»`（`SkTPS_P_component`）,
    `«6».«6.8-standard-slice-Br-descending»`（`STPS_exists_rank_68`）,
    `«7».«7.3-Pred-Trans-descend»`（`Pred_Trans_descend`）,
    `«6».«6.2-P-components-nonmulti»`（`P_components_nonmulti`）,
    `«7».«7.3-Trans-preserves-monoT»`（`m_7_3_Trans_monoT`）。
- 状態: 🤖 GREEN（`sorry` 0、axioms = propext/Classical.choice/Quot.sound）。
  **`OTdisp_OTpred` を無条件で完全に閉じた**（`OTdisp_OTpred_holds`）。
  非複項枝＝Brick E（`od4_OTpred_mono`）、複項枝＝`opx_OTpred_multi_of_mono`。
  `OTdisp_OTpred` は `od4_OTpred_final`（Isabelle :874）の弱化なので偽性リスクなし
  （`2 < Lng`＋3 corner 除外は不要な追加仮定）。

`transC2` の 6 分岐 dispatch（`transC2Core`, `PSS/Trans.lean`:139）:
* (I)/(III)/(V) と 2 つの else 枝は末尾 principal を 1 段 append（`od4R_op.drop`/`.deep`）
* 条件 (VI) 許容枝は `condVI_transC1_adm_v6p` で `t₂ = 0_B` → `.drop`
* 条件 (VI) 非許容枝は Brick C0 で `t₂ = D_{M₁,ⱼ₀} 0 <_BP D_{M₁,ⱼ₁} 0` → `.triv`

private helper suffix: `_oc`。
-/

namespace PSS

/-! ## 小補題 -/

private theorem bpHeadT_Dprin_oc (v : ℕ∞) (b : BT) : bpHeadT (Dprin v b) = b := rfl

/-- 末尾に principal を 1 個 append する `od4R_op.drop`（`addBT` 形）。 -/
private theorem od4_drop_addBT_oc (t : BT) (p : BP) :
    od4R_op t (addBT t (BT.trm [p])) := by
  cases t with
  | trm ts => exact od4R_op.drop ts p

private theorem getD_last_oc (init : List BP) (uu : ℕ∞) (bb : BT) :
    ((init.map (fun p => BT.trm [p]) ++ [BT.trm [BP.db uu bb]])).getD
      ((init.map (fun p => BT.trm [p]) ++ [BT.trm [BP.db uu bb]]).length - 1) BZero
      = BT.trm [BP.db uu bb] := by
  rw [List.getD_eq_getElem?_getD]; simp

private theorem take_init_oc (init : List BP) (uu : ℕ∞) (bb : BT) :
    ((init.map (fun p => BT.trm [p]) ++ [BT.trm [BP.db uu bb]])).take
      ((init.map (fun p => BT.trm [p]) ++ [BT.trm [BP.db uu bb]]).length - 1)
      = init.map (fun p => BT.trm [p]) := by
  simp

private theorem SigmaB_map_oc (init : List BP) :
    SigmaB (init.map (fun p => BT.trm [p])) = BT.trm init := by
  simp [SigmaB, untrm, List.flatMap_map]

/-- CD/t2n 枝（¬I∧¬III∧¬V∧¬VI, `t₂ ≠ 0_B`）の `transC2` の閉形式。
`transT2 M = Trm (init ++ [D_uu bb])` から `transC2Core` の else 枝を計算する。 -/
private theorem CD_t2n_shape_oc (M : PS) (init : List BP) (uu : ℕ∞) (bb : BT)
    (hA' : (transCondI M || transCondIII M || transCondV M) = false)
    (hB' : transCondVI M = false)
    (hbt2 : transT2 M = BT.trm (init ++ [BP.db uu bb])) :
    transC2 M = Dprin (transV M)
      (addBT
        (if (uu == (entry M 1 (lastParent M) : ℕ∞)) then BT.trm init else transT2 M)
        (Dprin (entry M 1 (lastParent M) : ℕ∞)
          (addBT
            (if (uu == (entry M 1 (lastParent M) : ℕ∞)) then bb else transT2 M)
            (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)))) := by
  have hPB : PB (transT2 M) = init.map (fun p => BT.trm [p]) ++ [BT.trm [BP.db uu bb]] := by
    rw [hbt2]; simp [PB, untrm]
  have hne : (transT2 M == BZero) = false := by rw [hbt2]; simp [BZero]
  unfold transC2 transC2Core
  simp only [hA', hB', hne, Bool.false_eq_true, if_false, hPB, getD_last_oc,
    take_init_oc, SigmaB_map_oc, bpHeadV, bpHeadT]

/-! ## Brick C: 手術サイトは（全 `transC2` 分岐で）un-insertion である
（Isabelle `od4_site_c2`, `layerC/pss_scratch.thy`:634）。 -/

theorem od4_site_c2 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (ht₁ : transT1 M ≠ BZero) :
    od4R_op (transT2 M) (bpHeadT (transC2 M)) := by
  by_cases hA : (transCondI M || transCondIII M || transCondV M) = true
  · -- Branch A: (I)/(III)/(V) — 末尾に D_{M₁,j₁} 0 を append
    have hbt : bpHeadT (transC2 M)
        = addBT (transT2 M) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) := by
      have hc2 : transC2 M = Dprin (transV M)
          (addBT (transT2 M) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)) := by
        simp only [transC2, transC2Core, hA, if_true]
      rw [hc2, bpHeadT_Dprin_oc]
    rw [hbt]
    exact od4_drop_addBT_oc (transT2 M) (.db (entry M 1 (lastIdx M) : ℕ∞) BZero)
  by_cases hB : transCondVI M = true
  · -- Branch B: 条件 (VI)
    have hbt : bpHeadT (transC2 M) = Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero := by
      rw [condVI_transC2_v6p hB, bpHeadT_Dprin_oc]
    by_cases hadm : adm M (transJ0 M) = true
    · -- 許容: t₂ = 0_B → drop
      have hc1 := condVI_transC1_adm_v6p M hR hB hj1gt hadm
      have ht2 : transT2 M = BZero := by show bpHeadT (transC1 M) = BZero; rw [hc1]; rfl
      rw [ht2, hbt]
      exact od4_drop_addBT_oc BZero (.db (entry M 1 (Lng M - 1) : ℕ∞) BZero)
    · -- 非許容: t₂ = D_{M₁,j₀} 0 <_BP D_{M₁,j₁} 0 → triv
      have hnadm : adm M (transJ0 M) = false := by simpa using hadm
      have ht2 : transT2 M = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero :=
        (od4_condVI_nadm_c1 M hR hmono hB hj1gt hnadm).2
      have hstep : entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) := by
        simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          lastIdx, lastParent] at hB
        simpa [transJ0, lastParent, lastIdx] using hB.1.2
      have hlt : (entry M 1 (transJ0 M) : ℕ∞) < (entry M 1 (Lng M - 1) : ℕ∞) := by
        have : entry M 1 (transJ0 M) < entry M 1 (Lng M - 1) := by omega
        exact_mod_cast this
      rw [ht2, hbt]
      exact od4R_op.triv (w := (entry M 1 (transJ0 M) : ℕ∞))
        (p := .db (entry M 1 (Lng M - 1) : ℕ∞) BZero) []
        (by simp only [lessBP, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl hlt)
  · -- Branch CD: ¬I ∧ ¬III ∧ ¬V ∧ ¬VI
    have hA' : (transCondI M || transCondIII M || transCondV M) = false := by simpa using hA
    have hB' : transCondVI M = false := by simpa using hB
    by_cases ht2z : transT2 M = BZero
    · -- t₂ = 0_B — 末尾に単一 principal を drop
      have hbt : bpHeadT (transC2 M)
          = Dprin (entry M 1 (lastParent M) : ℕ∞) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) := by
        have hc2 : transC2 M = Dprin (transV M)
            (Dprin (entry M 1 (lastParent M) : ℕ∞) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)) := by
          unfold transC2 transC2Core
          simp only [ht2z, hA', hB', BZero, beq_self_eq_true, Bool.false_eq_true,
            if_false, if_true]
        rw [hc2, bpHeadT_Dprin_oc]
      rw [ht2z, hbt]
      exact od4_drop_addBT_oc BZero
        (.db (entry M 1 (lastParent M) : ℕ∞) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero))
    · -- t₂ ≠ 0_B — 深い枝
      obtain ⟨qs, hqs⟩ : ∃ qs, transT2 M = BT.trm qs :=
        ⟨untrm (transT2 M), by cases transT2 M; rfl⟩
      have hqsne : qs ≠ [] := by intro h; apply ht2z; rw [hqs, h]; rfl
      obtain ⟨init, pl, hqinit⟩ : ∃ init pl, qs = init ++ [pl] :=
        ⟨qs.dropLast, qs.getLast hqsne, (List.dropLast_append_getLast hqsne).symm⟩
      rcases pl with ⟨uu, bb⟩
      have hbt2 : transT2 M = BT.trm (init ++ [BP.db uu bb]) := by rw [hqs, hqinit]
      have hbt : bpHeadT (transC2 M)
          = addBT (if (uu == (entry M 1 (lastParent M) : ℕ∞)) then BT.trm init else transT2 M)
              (Dprin (entry M 1 (lastParent M) : ℕ∞)
                (addBT (if (uu == (entry M 1 (lastParent M) : ℕ∞)) then bb else transT2 M)
                  (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero))) := by
        rw [CD_t2n_shape_oc M init uu bb hA' hB' hbt2, bpHeadT_Dprin_oc]
      rw [hbt]
      by_cases hC : (uu == (entry M 1 (lastParent M) : ℕ∞)) = true
      · -- leftDj₀ = True: 深い枝を deep で 1 段降りる
        have huu : uu = (entry M 1 (lastParent M) : ℕ∞) := by simpa using hC
        simp only [hC, if_true]
        rw [hbt2, huu]
        exact od4R_op.deep (od4_drop_addBT_oc bb (.db (entry M 1 (lastIdx M) : ℕ∞) BZero))
          init (entry M 1 (lastParent M) : ℕ∞)
      · -- leftDj₀ = False: 末尾 principal を drop
        have hC' : (uu == (entry M 1 (lastParent M) : ℕ∞)) = false := by simpa using hC
        simp only [hC', Bool.false_eq_true, if_false]
        exact od4_drop_addBT_oc (transT2 M)
          (.db (entry M 1 (lastParent M) : ℕ∞)
            (addBT (transT2 M) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)))

/-! ## Brick D: MASTER — `Trans (Pred M)` は `Trans M` の un-insertion
（Isabelle `od4_master_R`, `layerC/pss_scratch.thy`:760）。 -/

theorem od4_master_R (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (ht₁ : transT1 M ≠ BZero) :
    od4R_op (Trans (Pred M)) (Trans M) :=
  od4_master_R_of_site M hR hmono hj1gt ht₁ (od4_site_c2 M hR hmono hj1gt ht₁)

/-! ## Brick E に必要な小補題（`8.7-Trans-preserves-OT` の private を複製） -/

/-- `0_B ∈ OT_B`。Isabelle `otx_OT_B_zero` / `m_8_7_OT_zero`。 -/
private theorem BZero_OT_B_oc : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- 対角 1 列 `[(v,v)]` の翻訳。Isabelle `Trans_singleton`。 -/
private theorem Trans_singleton_oc (v : ℕ) :
    Trans [(v, v)] = if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  by_cases hv : v = 0
  · subst hv
    have hT : TPS ([((0:ℕ), (0:ℕ))]) := by simp [TPS]
    have hz : zeroT [((0:ℕ), (0:ℕ))] = true := by simp [zeroT, Lng, entry]
    simpa using (Trans_preserves_zeroT _ hT).mp hz
  · have hred : reduced [(v, v)] = true := by
      have hfix := Red_singleton v v; simp [reduced, hfix]
    have hfuel : transFuel [(v, v)] = (transFuel [(v, v)] - 1) + 1 := by simp [transFuel]
    rw [Trans, hfuel, TransAux]
    simp [hred, lastIdx, entry, Dprin, BZero, hv]

/-! ## Brick E: mono `OTpred` ステップ（分岐・条件仮定を一切取らない）
（Isabelle `od4_OTpred_mono`, `layerC/pss_scratch.thy`:803）。

任意の mono 標準 host について `Trans M ∈ OT_B → Trans (Pred M) ∈ OT_B`。
`Trans (Pred M) = 0_B` と `Lng M = 2` は自由な corner、それ以外は master un-insertion
＋ Brick A の後向き `isOT` 保存（`od4R_OT_B`）で閉じる。両残差 `DEEPOT`/`NOBR` より
真に強い。これがちょうど `opx_OTpred_multi_of_mono`（`layerB`:116306）が要求する
`monoPred` 仮定である。 -/

theorem od4_OTpred_mono (M : PS) (hMST : STPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) (hostOT : Trans M ∈ OT_B) : Trans (Pred M) ∈ OT_B := by
  have hMR : RTPS M := STPS_RTPS M hMST
  have hpredRT : RTPS (Pred M) := RTPS_Pred M hMR
  have hpredTB : Trans (Pred M) ∈ T_B := Trans_mem_T_B (Pred M) hpredRT
  by_cases ht1z : Trans (Pred M) = BZero
  · rw [ht1z]; exact BZero_OT_B_oc
  · by_cases hL2 : Lng M = 2
    · -- `Pred M` は 1 列 `[(v,v)]`
      have hpredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredRT
      have LP1 : Lng (Pred M) = 1 := by rw [length_Pred M hL]; omega
      obtain ⟨v, pv⟩ := (one_column (Pred M) hpredT).mp ⟨LP1, hpredRT⟩
      rw [pv, Trans_singleton_oc]
      by_cases hv : v = 0
      · simp only [hv, if_true]; exact BZero_OT_B_oc
      · simp only [hv, if_false]; exact OT_examples_1 v
    · have hj1gt : 1 < Lng M - 1 := by omega
      have ht₁ : transT1 M ≠ BZero := by simpa [transT1] using ht1z
      exact od4R_OT_B (od4_master_R M hMR hmono hj1gt ht₁) hostOT hpredTB

/-! ## Brick: 複項 host の `OTpred` は mono 成分の `OTpred` に還元される
（Isabelle `opx_OTpred_multi_of_mono`, `layerB/pss_wip.thy`:116306）。

複項 host `N` について `L := last (P N)`（mono 標準）・`A := take (Pcut N) N` で
`Pred N` は `L` の内部に作用する。`f7x_Trans_append_Pblocks`（Trans の複項分解）と
`OT_append_corr_om`（末尾 principal 置換）＋`monoPred`（＝本ファイルの
`od4_OTpred_mono`）で `OT_B` を再組立する。 -/

private theorem DB0_OT_oc : BT.trm [BP.db 0 BZero] ∈ OT_B := by
  simp [OT_B, OT, T_B, isOT_BT, isOT_BPList, isOT_BP, descP, dfree_BT, dfree_BPList,
    dfree_BP, BZero, gatherBT, gatherBPList]


private theorem Trans_zeropair_oc : Trans [((0:ℕ),(0:ℕ))] = BZero := by
  have hT : TPS ([((0:ℕ),(0:ℕ))]) := by simp [TPS]
  have hz : zeroT [((0:ℕ),(0:ℕ))] = true := by simp [zeroT, Lng, entry]
  simpa using (Trans_preserves_zeroT _ hT).mp hz


private theorem leBT_min_oc (p : BP) : leBT (Dprin 0 BZero) (BT.trm [p]) = true := by
  cases p with
  | db v b =>
    rcases eq_or_ne v 0 with rfl | hv
    · cases b with
      | trm bs => cases bs with
        | nil => simp [leBT, Dprin, BZero]
        | cons c cs => simp [leBT, Dprin, BZero, lessBT, lessBPList, lessBP]
    · have hvp : (0 : ℕ∞) < v := pos_iff_ne_zero.mpr hv
      simp [leBT, Dprin, lessBT, lessBPList, lessBP, hvp]


private theorem mono_Trans_singleton_oc (L : PS) (hR : RTPS L) (hmono : monoT L = true) :
    ∃ pl : BP, Trans L = BT.trm [pl] := by
  have hnm : multiT L = false := by
    by_contra hc
    have : multiT L = true := by simpa using hc
    rw [multiT] at this; simp [hmono] at this
  have hz0 : zeroT ((P L).getD 0 []) = false := by
    rw [P_nonmulti_eq L hnm]; simp only [List.getD_cons_zero]
    by_contra hc
    have hzt : zeroT L = true := by simpa using hc
    rw [monoT] at hmono; simp [hzt] at hmono
  have hlen : (PB (Trans L)).length = 1 := (m_7_3_Trans_monoT L hR hz0).mp hmono
  cases hT : Trans L with
  | trm ps =>
    have hp1 : ps.length = 1 := by
      have : (PB (BT.trm ps)).length = 1 := by rw [← hT]; exact hlen
      simpa [PB, untrm] using this
    obtain ⟨pl, rfl⟩ := List.length_eq_one_iff.mp hp1
    exact ⟨pl, rfl⟩



private theorem isOT_BPList_last_oc : ∀ (as : List BP) (pl : BP),
    isOT_BPList (as ++ [pl]) = true → isOT_BP pl = true
  | [], pl, h => by simpa [isOT_BPList] using h
  | a :: as, pl, h => by
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at h
      exact isOT_BPList_last_oc as pl h.2

/-- host term の末尾 principal は `isOT_BP`。 -/
private theorem isOT_last_oc (as : List BP) (pl : BP)
    (h : BT.trm (as ++ [pl]) ∈ OT_B) : isOT_BP pl = true := by
  have hOT : isOT_BT (BT.trm (as ++ [pl])) = true := h.1
  rw [isOT_BT, Bool.and_eq_true] at hOT
  exact isOT_BPList_last_oc as pl hOT.1


theorem opx_OTpred_multi_of_mono (N : PS)
    (monoPred : ∀ K : PS, STPS K → monoT K = true → 1 < Lng K → Trans K ∈ OT_B →
      Trans (Pred K) ∈ OT_B)
    (hNST : STPS N) (hmulti : multiT N = true) (hostOT : Trans N ∈ OT_B) :
    Trans (Pred N) ∈ OT_B := by
  have hNR : RTPS N := STPS_RTPS N hNST
  have hNT : TPS N := RTPS_TPS N hNR
  have LN : 1 < Lng N := multi_length_fseq N hNT hmulti
  set A := N.take (Pcut N) with hAdef
  set L := N.drop (Pcut N) with hLdef
  have hNAL : A ++ L = N := List.take_append_drop _ _
  have hPL_last : (P N).getLastD [] = L ∧ (P N).dropLast = P A := by
    have h := P_last_multi N hmulti LN; rw [hLdef, hAdef]; exact h
  have hPNe : P N ≠ [] := P_nonempty N
  have hLmem : L ∈ P N := by
    rw [← hPL_last.1]
    cases hpn : P N with
    | nil => exact absurd hpn hPNe
    | cons a as => simp only [List.getLastD_cons]; exact List.getLastD_mem_cons
  have hARTPS : RTPS A := by rw [hAdef]; exact trans_multi_prefix_RTPS N hNR hmulti
  have hLST : STPS L := by
    obtain ⟨k, hk⟩ := STPS_exists_rank_68 N hNST
    exact SkTPS_STPS k L (SkTPS_P_component k N L hk hLmem)
  have hLR : RTPS L := STPS_RTPS L hLST
  have hLT : TPS L := RTPS_TPS L hLR
  have hLne : L ≠ [] := hLT
  have hLzm : zeroT L = true ∨ monoT L = true := P_components_nonmulti N hNT L hLmem
  have hLnm : multiT L = false := by rcases hLzm with h | h <;> simp [multiT, h]
  have hPLsingle : P L = [L] := P_nonmulti_eq L hLnm
  have hgl : (P N).getLast hPNe = L := by
    have hconv : (P N).getLast hPNe = (P N).getLastD [] := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hPNe, Option.getD_some]
    rw [hconv]; exact hPL_last.1
  have hPsplit : P N = P A ++ [L] := by
    have h1 := List.dropLast_append_getLast hPNe
    rw [hPL_last.2, hgl] at h1; exact h1.symm
  have hPeq : P N = P A ++ P L := by rw [hPLsingle]; exact hPsplit
  obtain ⟨as, hTA⟩ : ∃ as, Trans A = BT.trm as := ⟨untrm (Trans A), by cases Trans A; rfl⟩
  have hRAL : RTPS (A ++ L) := by rw [hNAL]; exact hNR
  have hsplit := f7x_Trans_append_Pblocks_holds A L hRAL hLR (by rw [hNAL]; exact hPeq)
  have hPLget : (P L).getD 0 [] = L := by rw [hPLsingle, List.getD_cons_zero]
  rw [hNAL, hPLget] at hsplit
  have hPredN : Pred N = N.dropLast := by simp only [Pred, if_neg (Nat.not_le_of_lt LN)]
  have hpredRT : RTPS (Pred N) := RTPS_Pred N hNR
  have hpredTB : Trans (Pred N) ∈ T_B := Trans_mem_T_B (Pred N) hpredRT
  by_cases hL00 : L = [((0:ℕ),(0:ℕ))]
  · have hTLz : Trans L = BZero := by rw [hL00]; exact Trans_zeropair_oc
    rw [if_pos hL00, hTLz] at hsplit
    have hTN : Trans N = BT.trm (as ++ [BP.db 0 BZero]) := by
      rw [hsplit, hTA]; simp [addBT, Dprin, BZero]
    have hPredNA : Pred N = A := by rw [hPredN, ← hNAL, hL00]; simp
    have hTPredN : Trans (Pred N) = BT.trm as := by rw [hPredNA, hTA]
    have host : BT.trm (as ++ [BP.db 0 BZero]) ∈ OT_B := by rw [← hTN]; exact hostOT
    have hres := OT_append_corr_om as [] (BP.db 0 BZero) host BZero_OT_B_oc
      (by simp [leBT, lessBT, BZero, lessBPList])
      (by rw [List.append_nil, ← hTPredN]; exact hpredTB)
    rw [hTPredN]; simpa using hres
  · rw [if_neg hL00] at hsplit
    by_cases hL1 : Lng L = 1
    · obtain ⟨v, hLv⟩ := (one_column L hLT).mp ⟨hL1, hLR⟩
      have hvne : v ≠ 0 := by intro h; apply hL00; rw [hLv, h]
      have hTL : Trans L = Dprin (v : ℕ∞) BZero := by rw [hLv, Trans_singleton_oc]; simp [hvne]
      have hTN : Trans N = BT.trm (as ++ [BP.db (v:ℕ∞) BZero]) := by
        rw [hsplit, hTA, hTL]; simp [addBT, Dprin]
      have hPredNA : Pred N = A := by rw [hPredN, ← hNAL, hLv]; simp
      have hTPredN : Trans (Pred N) = BT.trm as := by rw [hPredNA, hTA]
      have host : BT.trm (as ++ [BP.db (v:ℕ∞) BZero]) ∈ OT_B := by rw [← hTN]; exact hostOT
      have hres := OT_append_corr_om as [] (BP.db (v:ℕ∞) BZero) host BZero_OT_B_oc
        (by simp [leBT, lessBT, BZero, lessBPList])
        (by rw [List.append_nil, ← hTPredN]; exact hpredTB)
      rw [hTPredN]; simpa using hres
    · have hLgt : 1 < Lng L := by
        have : 0 < Lng L := List.length_pos_of_ne_nil hLne
        omega
      have hLmono : monoT L = true := by
        rcases hLzm with h | h
        · exfalso; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h; omega
        · exact h
      obtain ⟨pl, hTL⟩ := mono_Trans_singleton_oc L hLR hLmono
      have hTN : Trans N = BT.trm (as ++ [pl]) := by rw [hsplit, hTA, hTL]; simp [addBT]
      have host : BT.trm (as ++ [pl]) ∈ OT_B := by rw [← hTN]; exact hostOT
      have hplOT : isOT_BP pl = true := isOT_last_oc as pl host
      have hTransLOT : Trans L ∈ OT_B := by
        rw [hTL]
        refine ⟨?_, ?_⟩
        · show isOT_BT (BT.trm [pl]) = true
          simp only [isOT_BT, isOT_BPList, descP, hplOT, Bool.and_true, Bool.true_and]
        · have := Trans_mem_T_B L hLR; rw [hTL] at this; exact this
      have hPredL : Pred L = L.dropLast := by simp only [Pred, if_neg (Nat.not_le_of_lt hLgt)]
      have hPredNAL : Pred N = A ++ Pred L := by
        rw [hPredN, ← hNAL, List.dropLast_append_of_ne_nil hLne, hPredL]
      have hPPredN : P (Pred N) = P A ++ P (Pred L) := by
        have ho := (FseqDesc_m_6_2_P_oper_2_holds N 1 hNT (le_refl 1)
          (by rw [hPL_last.1]; exact hLgt)).2
        rw [pred_is_oper1 N hNT LN, ho, hPL_last.2, hPL_last.1, ← pred_is_oper1 L hLT hLgt]
      have hPredLnm : multiT (Pred L) = false := nonmulti_Pred L hLT hLnm hLgt
      have hPredLsingle : P (Pred L) = [Pred L] := P_nonmulti_eq (Pred L) hPredLnm
      have hpredLRT : RTPS (Pred L) := RTPS_Pred L hLR
      have hRAPL : RTPS (A ++ Pred L) := by rw [← hPredNAL]; exact hpredRT
      have hsplit2 := f7x_Trans_append_Pblocks_holds A (Pred L) hRAPL hpredLRT
        (by rw [← hPredNAL]; exact hPPredN)
      have hPLget2 : (P (Pred L)).getD 0 [] = Pred L := by rw [hPredLsingle, List.getD_cons_zero]
      rw [← hPredNAL, hPLget2] at hsplit2
      have hPredLST : STPS (Pred L) := by
        rw [pred_is_oper1 L hLT hLgt]; exact STPS.oper hLST 1 (le_refl 1)
      have hPredLOT : Trans (Pred L) ∈ OT_B := monoPred L hLST hLmono hLgt hTransLOT
      by_cases hPL00 : Pred L = [((0:ℕ),(0:ℕ))]
      · have hTPLz : Trans (Pred L) = BZero := by rw [hPL00]; exact Trans_zeropair_oc
        rw [if_pos hPL00, hTPLz] at hsplit2
        have hTPredN : Trans (Pred N) = BT.trm (as ++ [BP.db 0 BZero]) := by
          rw [hsplit2, hTA]; simp [addBT, Dprin, BZero]
        rw [hTPredN]
        exact OT_append_corr_om as [BP.db 0 BZero] pl host DB0_OT_oc
          (leBT_min_oc pl) (by rw [← hTPredN]; exact hpredTB)
      · rw [if_neg hPL00] at hsplit2
        have hPredLzm : zeroT (Pred L) = true ∨ monoT (Pred L) = true := by
          by_contra hc
          rw [not_or] at hc
          have h0 : zeroT (Pred L) = false := by simpa using hc.1
          have h1 : monoT (Pred L) = false := by simpa using hc.2
          rw [multiT, h0, h1] at hPredLnm; simp at hPredLnm
        have hPredLmono : monoT (Pred L) = true := by
          rcases hPredLzm with h | h
          · exfalso
            have hL1P : Lng (Pred L) = 1 := by
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h; exact h.1
            obtain ⟨w, hw⟩ := (one_column (Pred L) (RTPS_TPS _ hpredLRT)).mp ⟨hL1P, hpredLRT⟩
            apply hPL00
            have hw0 : w = 0 := by
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
              rw [hw] at h; simpa [entry] using h.2
            rw [hw, hw0]
          · exact h
        obtain ⟨pl', hTPL⟩ := mono_Trans_singleton_oc (Pred L) hpredLRT hPredLmono
        have hTPredN : Trans (Pred N) = BT.trm (as ++ [pl']) := by
          rw [hsplit2, hTA, hTPL]; simp [addBT]
        have hdesc : lessBT (Trans (Pred L)) (Trans L) = true := Pred_Trans_descend L hLT hLgt
        have hjunc : leBT (BT.trm [pl']) (BT.trm [pl]) = true := by
          rw [← hTPL, ← hTL]; simp only [leBT, hdesc, Bool.true_or]
        rw [hTPredN]
        exact OT_append_corr_om as [pl'] pl host (by rw [← hTPL]; exact hPredLOT) hjunc
          (by rw [← hTPredN]; exact hpredTB)


/-! ## `OTdisp_OTpred` への配線（複項脚を残差として露出）

`OTdisp_OTpred`（`8.7-Trans-preserves-OT`:101）は `STPS N`（mono を仮定しない）を
受けるので、複項 host も覆わねばならない。dispatcher（同ファイル:395–396）は
`oper N n = Pred N` 枝で mono/multi を分けずに呼ぶ。非複項枝は
`od4_OTpred_mono`（本ファイル・無条件）で閉じ、複項枝だけを残差
`OTpred_multi_residual` に落とす。 -/

/-- 複項 host に対する `OTpred`（Isabelle `opx_OTpred_multi_of_mono`,
`layerB/pss_wip.thy`:116306）。mono ステップ `od4_OTpred_mono` が既に無条件で
閉じているので、`OTdisp_OTpred` に残る唯一の残差はこれ 1 本。 -/
def OTpred_multi_residual : Prop :=
  ∀ N : PS, STPS N → multiT N = true → Trans N ∈ OT_B → Trans (Pred N) ∈ OT_B

/-- `OTdisp_OTpred`（`8.7-Trans-preserves-OT`:101）を、複項残差
`OTpred_multi_residual` を仮定として閉じる。非複項枝は `od4_OTpred_mono` で
無条件に外れる。`OTdisp_OTpred` は `od4_OTpred_final`（Isabelle :874）の弱化
なので偽性リスクなし（3 corner 除外＋`2 < Lng` は不要な追加仮定）。 -/
theorem OTdisp_OTpred_of_multiResidual (hmul : OTpred_multi_residual) :
    OTdisp_OTpred := by
  intro N hN hOT hL3 _hzc _hcI _hcVIn
  by_cases hmono : monoT N = true
  · exact od4_OTpred_mono N hN hmono (by omega) hOT
  · have hL1 : Lng N ≠ 1 := by omega
    have hzT : zeroT N = false := by simp [zeroT, hL1]
    have hmulti : multiT N = true := by
      have hmono' : monoT N = false := by simpa using hmono
      simp [multiT, hzT, hmono']
    exact hmul N hN hmulti hOT

/-- 複項残差の discharge: `opx_OTpred_multi_of_mono` に mono ステップ
`od4_OTpred_mono` を渡す。 -/
theorem OTpred_multi_residual_holds : OTpred_multi_residual :=
  fun N hNST hmulti hostOT =>
    opx_OTpred_multi_of_mono N od4_OTpred_mono hNST hmulti hostOT

/-- **`OTdisp_OTpred`（`8.7-Trans-preserves-OT`:101）を無条件で閉じる**。
非複項枝＝`od4_OTpred_mono`（Brick E）、複項枝＝`opx_OTpred_multi_of_mono`。
`od4_OTpred_final`（Isabelle :874）の弱化なので偽性リスクなし。 -/
theorem OTdisp_OTpred_holds : OTdisp_OTpred :=
  OTdisp_OTpred_of_multiResidual OTpred_multi_residual_holds

#print axioms od4_site_c2
#print axioms od4_master_R
#print axioms od4_OTpred_mono
#print axioms opx_OTpred_multi_of_mono
#print axioms OTdisp_OTpred_of_multiResidual
#print axioms OTpred_multi_residual_holds
#print axioms OTdisp_OTpred_holds

end PSS
