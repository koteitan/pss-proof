import «8».«8.7-otint-a0ot-nub»
import «8».«8.7-otint-tri0-census»
import «8».«8.4-corner-np-value»
import «8».«8.7-otpred-close»
import «7».«7.4-Mark-Trans-repr»
import «8».«8.2-condV-terminal-slice-Trans»

/-!
# §8.7 唯一の真の未知 `A0OT_an` を census provenance から discharge

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの内点ケースの surgery 残差）。
- Isabelle: `ot1_A0OT` (`isabelle/layerC/pss_scratch.thy`:4762)。census では
  `A₀ = bpHeadT (Trans (Pred (s84x_N M)))`。§6 Red/slice ＋ §7 Trans ＋
  `m_8_7_OT_scb_recursive`（PORTED: `8.7-OT-scb-recursive`）で閉じる。
- 対象: `8.7-otint-a0ot-nub`:252 が宣言した named 残差 `A0OT_an`
  （抽象 census 形の `isOT_BT A₀`。抽象前提束からは導けない「唯一の真の未知」）。
- 本ファイルの成果（**完全 discharge**）:
  * `A0OT_holds_ac : CensusProvenance → A0OT_an`。抽象 binder を `censusPin_tc`
    （`8.7-otint-tri0-census`）で census provenance に pin し
    （`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`、
    `e₃ = M₁,ⱼ₋₃`）、Isabelle `ot1_A0OT` の証明線をそのまま辿る:
    - STEP 3: `Trans (s84x_N M) ∈ OT_B`。簡約 host `RN = Red (s84x_N M)` の頭項形
      `Trans RN = D_{RN₁,₀}(bpHeadT (Trans RN))`（`Trans_principal_head`）＋座標引き戻し
      `entry RN 1 0 = M₁,ⱼ₋₃`（`repr_entry1_shift_gen`）で `Trans (s84x_N M) = D_{e₃} body`
      を得、census 前提 `hk1`（scb-kind1 分解）に `OT_scb_recursive` を掛けて
      `D_{e₃} body ∈ OT`。
    - STEP 1: `Trans (Pred RN) ∈ OT_B`（`od4_OTpred_mono_RT_ac`＝`od4_OTpred_mono`
      の RTPS 版。私が本ファイルで再構成、engine は公開 `od4_master_R`／`od4R_OT_B`）。
    - transport: `Trans (Pred (s84x_N M)) = Trans (Pred RN)`（`Trans_Red`＋`Red_Pred`。
      ltJ 不要—原文の `bpax_Trans_PredN_leR` が要求する `jm3 < Lng M − 2` を回避、
      `jm3 < Lng M − 1`（jm3lt）のみで閉じる）。
    - STEP 4: `A₀ = bpHeadT (Trans (Pred (s84x_N M)))` の頭項は OT（`isOT_bpHeadT_ac`）。
  * ⇒ Isabelle `ot1_A0OT` 由来の残差 `A0OT_an` は **census provenance のみ** に縮小
    （`CensusProvenance` は既存の otSetleCore フィールド）。
- 依存（すべてビルド済み・main 6117365）:
  * `8.7-otint-a0ot-nub`（`A0OT_an`）、`8.7-otint-tri0-census`（`censusPin_tc`／
    `CensusProvenance`）、`8.7-OT-scb-recursive`（`OT_scb_recursive`）、
    `8.4-corner-np-value`（slice geometry／`slice_Trans_principal_head`／
    `repr_entry1_shift_gen`／`standard_slice_Red_strongmono`／`DTPS_iff`／
    `Regs_jm3Marked_holds`／`s84c1_jm2_basic`／`Adm_le`／`Lng_Red_invariance`／
    `STPS_RTPS`／`RTPS_TPS`／`length_seg`）、`8.7-otpred-close`（`od4_master_R`／
    `od4R_OT_B`／`OT_examples_1`／`transT1`）、`7.4-Mark-Trans-repr`（`Red_Pred`）、
    `8.2-condV-terminal-slice-Trans`（`Trans_principal_head`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 = `CensusProvenance`（既存フィールド）のみ。私的接尾辞 `_ac`。
-/

namespace PSS

/-! ## 1. 遺伝性: OT 項の頭本体は OT（Isabelle `otx_bpHeadT_OT`） -/

/-- `isOT_BT t → isOT_BT (bpHeadT t)`。頭 principal 成分の本体が OT。 -/
private theorem isOT_bpHeadT_ac {t : BT} (h : isOT_BT t = true) :
    isOT_BT (bpHeadT t) = true := by
  cases t with
  | trm ps =>
    cases ps with
    | nil => rfl
    | cons p rest =>
      cases p with
      | db v body =>
        show isOT_BT body = true
        have h1 : isOT_BPList (BP.db v body :: rest) = true := by
          have h' := h
          simp only [isOT_BT, Bool.and_eq_true] at h'
          exact h'.1
        simp only [isOT_BPList, Bool.and_eq_true] at h1
        have h2 : isOT_BP (BP.db v body) = true := h1.1
        simp only [isOT_BP, Bool.and_eq_true] at h2
        exact h2.1

/-! ## 2. OTpred の RTPS 版（`8.7-otpred-close` の `od4_OTpred_mono` を RTPS 入力で再構成） -/

/-- `0_B ∈ OT_B`（Isabelle `otx_OT_B_zero`）。 -/
private theorem BZero_OT_B_ac : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- 対角 1 列 `[(v,v)]` の翻訳（Isabelle `Trans_singleton`）。 -/
private theorem Trans_singleton_ac (v : ℕ) :
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

/-- **`od4_OTpred_mono` の RTPS 版**（Isabelle `od4_OTpred_mono_RT`）。RTPS 標準 host に
ついて `Trans M ∈ OT_B → Trans (Pred M) ∈ OT_B`。engine は公開 `od4_master_R`／
`od4R_OT_B`。 -/
private theorem od4_OTpred_mono_RT_ac (M : PS) (hMR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) (hostOT : Trans M ∈ OT_B) : Trans (Pred M) ∈ OT_B := by
  have hpredRT : RTPS (Pred M) := RTPS_Pred M hMR
  have hpredTB : Trans (Pred M) ∈ T_B := Trans_mem_T_B (Pred M) hpredRT
  by_cases ht1z : Trans (Pred M) = BZero
  · rw [ht1z]; exact BZero_OT_B_ac
  · by_cases hL2 : Lng M = 2
    · have hpredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredRT
      have LP1 : Lng (Pred M) = 1 := by rw [length_Pred M hL]; omega
      obtain ⟨v, pv⟩ := (one_column (Pred M) hpredT).mp ⟨LP1, hpredRT⟩
      rw [pv, Trans_singleton_ac]
      by_cases hv : v = 0
      · simp only [hv, if_true]; exact BZero_OT_B_ac
      · simp only [hv, if_false]; exact OT_examples_1 v
    · have hj1gt : 1 < Lng M - 1 := by omega
      have ht₁ : transT1 M ≠ BZero := by simpa [transT1] using ht1z
      exact od4R_OT_B (od4_master_R M hMR hmono hj1gt ht₁) hostOT hpredTB

/-! ## 3. `A0OT_an` の discharge（Isabelle `ot1_A0OT`） -/

/-- **`A0OT_an` の完全 discharge**（Isabelle `ot1_A0OT`）。抽象 census 残差
`A0OT_an`（`isOT_BT A₀`、`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`）を、既存の
otSetleCore フィールド `CensusProvenance` のみへ縮小する。 -/
theorem A0OT_holds_ac (hprov : CensusProvenance) : A0OT_an := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- === census provenance で抽象 binder を pin ===
  obtain ⟨hv1, he3, hbody, hA0⟩ := censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1
    (hprov M hST hmono hp hj1 hcond) hOT hb1 hinner hk1 hmn
  subst hA0
  -- 目標: isOT_BT (bpHeadT (Trans (Pred (s84x_N M)))) = true
  apply isOT_bpHeadT_ac
  -- 目標: isOT_BT (Trans (Pred (s84x_N M))) = true
  suffices hfin : Trans (Pred (s84x_N M)) ∈ OT_B from hfin.1
  -- === census slice geometry ===
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR hMT hp).1.2.2
  -- === 簡約 host RN = Red (s84x_N M) の基本性質 ===
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have hLenRN : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M :=
    (Lng_Red_invariance (s84x_N M) NT).trans hlenN
  have hDT : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  obtain ⟨hRNR, hmonoRN, _hdescRN⟩ := (DTPS_iff _).mp hDT
  have hRNpos : 1 < Lng (Red (s84x_N M)) := by rw [hLenRN]; omega
  -- === STEP 3: Trans (s84x_N M) ∈ OT_B ===
  -- 簡約 host の頭項形
  have hprinc : Trans (Red (s84x_N M))
      = Dprin (entry (Red (s84x_N M)) 1 0 : ℕ∞) (bpHeadT (Trans (Red (s84x_N M)))) :=
    Trans_principal_head (Red (s84x_N M)) hRNR hmonoRN
  -- 頭指標を M 座標へ引き戻し: entry RN 1 0 = M₁,ⱼ₋₃ = e₃
  have hentry0 : entry (Red (s84x_N M)) 1 0 = entry M 1 (s84x_jm3 M) := by
    have h := repr_entry1_shift_gen M (s84x_jm3 M) (Lng M - 1) 0 hMR jm3lt (le_refl _) leR3
      (by show 0 < Lng (Red (s84x_N M)); rw [hLenRN]; omega)
    rw [Nat.add_zero] at h
    exact h
  have he0 : entry (Red (s84x_N M)) 1 0 = e3 := hentry0.trans he3.symm
  have hbh : bpHeadT (Trans (Red (s84x_N M))) = body := by
    rw [← Trans_Red (s84x_N M) NT]; exact hbody.symm
  -- Trans (s84x_N M) = D_{e₃} body
  have hTsN : Trans (s84x_N M) = Dprin (e3 : ℕ∞) body := by
    calc Trans (s84x_N M) = Trans (Red (s84x_N M)) := Trans_Red (s84x_N M) NT
      _ = Dprin (entry (Red (s84x_N M)) 1 0 : ℕ∞) (bpHeadT (Trans (Red (s84x_N M)))) := hprinc
      _ = Dprin (e3 : ℕ∞) body := by rw [he0, hbh]
  -- T_B / OT of the core
  have hTsN_TB : Trans (s84x_N M) ∈ T_B := by
    rw [Trans_Red (s84x_N M) NT]; exact Trans_mem_T_B (Red (s84x_N M)) hRNR
  have hcore_TB : Dprin (e3 : ℕ∞) body ∈ T_B := by rw [← hTsN]; exact hTsN_TB
  have hcore_OT : Dprin (e3 : ℕ∞) body ∈ OT :=
    OT_scb_recursive (Trans M) (Dprin (e3 : ℕ∞) body) s1 b1 hOT hcore_TB hk1.1
  have hsN_OTB : Trans (s84x_N M) ∈ OT_B := by
    refine ⟨?_, hTsN_TB⟩
    show isOT_BT (Trans (s84x_N M)) = true
    rw [hTsN]; exact hcore_OT
  -- === Trans RN ∈ OT_B ===
  have hRN_OTB : Trans (Red (s84x_N M)) ∈ OT_B := by
    rw [← Trans_Red (s84x_N M) NT]; exact hsN_OTB
  -- === STEP 1: Trans (Pred RN) ∈ OT_B ===
  have hPredRN_OTB : Trans (Pred (Red (s84x_N M))) ∈ OT_B :=
    od4_OTpred_mono_RT_ac (Red (s84x_N M)) hRNR hmonoRN hRNpos hRN_OTB
  -- === transport: Trans (Pred (s84x_N M)) = Trans (Pred RN)（ltJ 不要）===
  have hPredNT : TPS (Pred (s84x_N M)) := by
    have hpos : 0 < Lng (Pred (s84x_N M)) := by
      rw [length_Pred (s84x_N M) (by rw [hlenN]; omega), hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have htrans : Trans (Pred (s84x_N M)) = Trans (Pred (Red (s84x_N M))) := by
    rw [Trans_Red (Pred (s84x_N M)) hPredNT, Red_Pred (s84x_N M) NT]
  rw [htrans]; exact hPredRN_OTB

#print axioms A0OT_holds_ac

/-! ## 4. `NubRegimeE3_an` の discharge（Isabelle `oi5_regime(2)`、行 1 entry 単調性） -/

/-- **`NubRegimeE3_an` の完全 discharge**（Isabelle `oi5_regime(2)`）。census では
`e₃ = M₁,ⱼ₋₃`、`v₁ = M₁,Lng M−1`。行 1 の許容化祖先鎖 `s84x_jm3 M = Adm M (s84x_jm2 M)`
に沿う entry 単調性（`adm_row1_ancestry`＋`le1_imp_entry1_le`）と親辺 strict 増加
（`s84c1_jm2_basic(2)`）から `e₃ < v₁`、ゆえ `e₃ ≤ v₁ − 1`。 -/
theorem NubRegimeE3_holds_ac (hprov : CensusProvenance) : NubRegimeE3_an := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  obtain ⟨hv1, he3, _hbody, _hA0⟩ := censusPin_tc M ins A0 body e3 v1 s0 b0 s1 b1
    (hprov M hST hmono hp hj1 hcond) hOT hb1 hinner hk1 hmn
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have huv2 : entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) := (s84c1_jm2_basic M hp).2.1
  have hle1 : leR M 1 (s84x_jm3 M) (s84x_jm2 M) = true :=
    adm_row1_ancestry M (s84x_jm2 M) hMT (by omega)
  have he3le : entry M 1 (s84x_jm3 M) ≤ entry M 1 (s84x_jm2 M) :=
    le1_imp_entry1_le M (s84x_jm3 M) (s84x_jm2 M) hle1
  subst he3; subst hv1
  omega

#print axioms NubRegimeE3_holds_ac

end PSS
