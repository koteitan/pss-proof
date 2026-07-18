import «8».«8.7-otdisp-OTmulti»
import «8».«8.7-otmulti-interior»
import «8».«8.7-otx-condVI-eqs»
import «8».«8.7-Trans-preserves-OT-props»
import «8».«8.6-condVI-close»
import «8».«8.6-condVI-adm-forms»
import «8».«8.6-condVI-props»
import «8».«8.6-condVI-nadm-close»
import «8».«8.2-subexpr-adm0-ctx»
import «6».«6.2-nonmulti-fseq»
import «6».«6.3-admof-slice»
import «6».«6.4-mono-slice-next»
import «7».«7.3-Trans-preserves-zeroT»

/-!
# §8.7 OT 柱 — `OTmulti_interior_notCondI_om2` の条件 II–VI ＋零脚枝クローズ

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTmulti_interior_notCondI_om2`
  （`«8».«8.7-otmulti-interior»`:139）＝ Isabelle `opx_OTmulti` の `casea` 条件
  (II)–(VI) 脚 ＋ `Lng L > 2` の零脚（`isabelle/layerB/pss_wip.thy`:115556 の
  `case casea` 内、条件別 dispatch）。訂正: なし。
- 状態: 🤖 GREEN-MODULO 1（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `OTmulti_interior_notCondI_om2` の guard `¬ transCondI L ∨ (C ∧ 1 < Lng L - 1)`
  のうち、**条件 (VI) 全域**と**零脚（C-true）全域**を無条件で閉じ、残り
  （条件 (II)/(III)/(IV)/(V) の内部枝）を ONE narrower Prop
  `OTmulti_interior_intCond_nc1` に露出する。数値監査
  （`python/audit_8_7_otmulti_interior.py`）では guard 領域は標準形上 220/220 が
  条件 (I) ＝ **経験的に空**だが、空虚性は証明不能なので枝を移植する。

## 証明の骨格（`opx_OTmulti` の `casea` 逐語）

末尾 mono 成分 `L`（`Trans L = Trm [pl]`, host 埋め込み `Trm (as ++ [pl])`）に対し、
BLK は f7x の零脚フラグ `C := (P (oper L m)).getD 0 [] = [(0,0)]` 込みの再組立:

* **C-true（零脚）**: guard の下では常に casea（`¬ caseb`）に落ちる
  （`caseb ⟹ transCondI` かつ `caseb ∧ C-true ⟹ Lng L = 2`）。casea では
  `P (oper L m) = [oper L m]`（`nonmulti_fseq_2`）ゆえ `oper L m = [(0,0)]`、
  `Trans (oper L m) = 0_B`、BLK = `addBT (D₀0) 0_B = D₀0`。host 末尾 principal を
  最小項 `D₀0` に置換する `OT_append_corr_om` で閉じる（Isabelle `casea` の `lm00`）。
* **C-false**: BLK = `Trans (oper L m)`。
  - 条件 (VI): 交換等式 `Trans (oper L m) = operB (Trans L) (numBT k)`
    （`OTdisp_condVI_j1eq1_eq` / `..._adm_eq` / `..._nadm_eq`、供給は無条件）→
    `operB` snoc 局在 → `e4x`（Isabelle `closEx`）。
  - 条件 (II)/(III)/(IV)/(V): 内部 OT 所属 `Trans (oper L m) ∈ OT_B` ＋
    順序 `leBT (Trans (oper L m)) (Trans L)`（Isabelle `OTint`/`ordIntC`）を
    narrower Prop `OTmulti_interior_intCond_nc1` から得て `OT_append_corr_om` で閉じる。

## ONE narrower Prop に露出したもの（経験的に空）

`OTmulti_interior_intCond_nc1`: 末尾 mono 成分 `L` が条件 (II)/(III)/(IV)/(V) の
とき `Trans (oper L m) ∈ OT_B ∧ leBT (Trans (oper L m)) (Trans L)`（内部 OT
ステップ＋降下柱の弱化）。Isabelle `opx_OTmulti` の `OTint` ＋ `ordIntC`（条件 II は
`TVall` 経由の交換脚）の合流に相当。ビルド済みツリーでは `OTdisp_OTint` は
`8.7-termination` の `TerminationResidual.otSetleCore`/`exch84slicepkg`/`condIIIVts`/
`exchVMnadmAtomic` から供給される（slicepkg / condV 塔 / condII masterCF 依存）ため、
mono 成分に適用した本 Prop は無条件には閉じない。

- 依存（ビルド済みのみ import）: `«8».«8.7-otdisp-OTmulti»`（`OT_append_corr_om`）、
  `«8».«8.7-otmulti-interior»`（`OTmulti_interior_notCondI_om2`）、
  `«8».«8.7-otx-condVI-eqs»`（`OTdisp_condVI_j1eq1_eq_holds`）、
  `«8».«8.7-Trans-preserves-OT-props»`（`OTdisp_condVI_adm_eq_of_CondVIAdmTowerScb` /
  `OTdisp_condVI_nadm_eq_of_CondVIExchNadm`）、`«8».«8.6-condVI-close»` /
  `«8».«8.6-condVI-adm-forms»` / `«8».«8.6-condVI-props»` /
  `«8».«8.6-condVI-nadm-close»`（condVI 供給群）、`«8».«8.2-subexpr-adm0-ctx»`
  （`condII_or_condIV`）、`«6».«6.2-nonmulti-fseq»`（`nonmulti_fseq_1` / `_2`）、
  `«6».«6.3-admof-slice»`（`adm_zero`）、`«6».«6.4-mono-slice-next»`
  （`parent_eq_of_nextR0`）、`«7».«7.3-Trans-preserves-zeroT»`（`Trans_preserves_zeroT`）。
- private helper suffix: `_nc1`。
-/

namespace PSS

/-! ## 1. Buchholz 側の小補題（`«8».«8.7-otdisp-OTmulti» private 版の再導出） -/

/-- `0_B ∈ OT_B`。 -/
private theorem BZero_OT_B_nc1 : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- `operB 0_B z = 0_B`。Isabelle `b1x_operB_zero`。 -/
private theorem operB_BZero_nc1 (z : BT) : operB BZero z = BZero := by
  simp [operB, BZero, bOperCore]

/-- Isabelle `e4x_OT_B_operB_numBT` (`layerB/pss_wip.thy`:61390): 零脚を
`operB_BZero_nc1` で埋めて `buchholz_fseq_closed` を無条件化。 -/
private theorem OT_B_operB_numBT_nc1 {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz, operB_BZero_nc1]; exact BZero_OT_B_nc1
  · exact buchholz_fseq_closed a n ha hz

/-- Isabelle `opx_operB_snoc_local`: `operB` は最後の top-level principal に局在する。 -/
private theorem operB_snoc_local_nc1 : ∀ (as : List BP) (pl : BP) (z : BT),
    operB (BT.trm (as ++ [pl])) z = addBT (BT.trm as) (operB (BT.trm [pl]) z)
  | [], pl, z => by
      cases hop : operB (BT.trm [pl]) z with
      | trm xs => simp [addBT, hop]
  | a :: as, pl, z => by
      have hne : as ++ [pl] ≠ [] := by simp
      obtain ⟨q, qs, hq⟩ : ∃ q qs, as ++ [pl] = q :: qs := by
        cases h : as ++ [pl] with
        | nil => exact absurd h hne
        | cons q qs => exact ⟨q, qs, rfl⟩
      have hstep : operB (BT.trm (a :: (as ++ [pl]))) z
          = addBT (BT.trm [a]) (operB (BT.trm (as ++ [pl])) z) := by
        rw [hq]; simp [operB, bOperCore]
      rw [List.cons_append, hstep, operB_snoc_local_nc1 as pl z]
      cases hop : operB (BT.trm [pl]) z with
      | trm xs => simp [addBT]

/-- Isabelle `opx_leBT_min`: `D_0 0` は全 principal 項以下。 -/
private theorem leBT_min_nc1 (p : BP) : leBT (Dprin 0 BZero) (BT.trm [p]) = true := by
  cases p with
  | db v b =>
    rcases eq_or_ne v 0 with rfl | hv
    · cases b with
      | trm bs =>
        cases bs with
        | nil => simp [leBT, Dprin, BZero]
        | cons c cs =>
          simp [leBT, Dprin, BZero, lessBT, lessBPList, lessBP]
    · have hvp : (0 : ℕ∞) < v := pos_iff_ne_zero.mpr hv
      simp [leBT, Dprin, lessBT, lessBPList, lessBP, hvp]

/-- `D₀0 = D_0 0_B ∈ OT_B`。 -/
private theorem D00_OT_B_nc1 : Dprin (0 : ℕ∞) BZero ∈ OT_B := by
  refine ⟨?_, ?_⟩
  · show isOT_BT (Dprin (0 : ℕ∞) BZero) = true
    simp [Dprin, BZero, isOT_BT, isOT_BPList, isOT_BP, descP, gatherBT, gatherBPList]
  · show dfree_BT (Dprin (0 : ℕ∞) BZero) = true
    simp [Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP]

/-! ## 2. `T_B` の append 準同型と `Trans` 側の小補題 -/

/-- `dfree_BPList` は append 準同型。 -/
private theorem dfree_BPList_append_nc1 : ∀ (xs ys : List BP),
    dfree_BPList (xs ++ ys) = (dfree_BPList xs && dfree_BPList ys)
  | [], ys => by simp [dfree_BPList]
  | x :: xs, ys => by
      simp [dfree_BPList, dfree_BPList_append_nc1 xs ys, Bool.and_assoc]

/-- host 側の `as` と `cs = untrm (Trans (oper L m))` の連結が `T_B` に留まる。 -/
private theorem Trm_append_T_B_nc1 (as cs : List BP) (p : BP)
    (hasTB : BT.trm (as ++ [p]) ∈ T_B) (hcsTB : BT.trm cs ∈ T_B) :
    BT.trm (as ++ cs) ∈ T_B := by
  have has : dfree_BPList as = true := by
    have h : dfree_BT (BT.trm (as ++ [p])) = true := hasTB
    rw [dfree_BT, dfree_BPList_append_nc1] at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have hcs : dfree_BPList cs = true := hcsTB
  show dfree_BT (BT.trm (as ++ cs)) = true
  simp [dfree_BT, dfree_BPList_append_nc1, has, hcs]

/-- `Trans [(0,0)] = 0_B`。 -/
private theorem Trans_zerocol_nc1 : Trans [((0 : ℕ), (0 : ℕ))] = BZero := by
  have hT : TPS ([((0 : ℕ), (0 : ℕ))]) := by simp [TPS]
  have hz : zeroT [((0 : ℕ), (0 : ℕ))] = true := by simp [zeroT, Lng, entry]
  exact (Trans_preserves_zeroT _ hT).mp hz

/-! ## 3. `oper` / 条件の橋渡し補題 -/

/-- `oper L m ≠ Pred L`（末尾 mono・`Lng L > 1`・末尾非全零）なら親を持つ
（Isabelle `casea` の `hpL` 導出、`oper_def` の `!hasParent → Pred` 枝の対偶）。 -/
private theorem hasParent_of_oper_ne_Pred_nc1 (L : PS) (m : ℕ) (hLgt : 1 < Lng L)
    (hz : ¬(entry L 0 (Lng L - 1) = 0 ∧ entry L 1 (Lng L - 1) = 0))
    (hpred : oper L m ≠ Pred L) :
    hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = true := by
  by_contra hnp
  apply hpred
  have hj1ne : Lng L - 1 ≠ 0 := by omega
  have hnpF : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = false := by
    cases h : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) with
    | true => exact absurd h hnp
    | false => rfl
  simp [oper, hj1ne, hz, hnpF]

/-- Isabelle `casea` が `caseb`（`nextR L 0 0 (Lng L-1) ∧ e1L`）を排するのに使う
含意: `caseb ⟹ transCondI L`（`parent = 0` ＋ `adm L 0`）。 -/
private theorem caseb_transCondI_nc1 (L : PS)
    (hnext : nextR L 0 0 (Lng L - 1) = true)
    (he1z : entry L 1 (Lng L - 1) = 0) : transCondI L = true := by
  have hpar0 : parent L 0 (Lng L - 1) = 0 := parent_eq_of_nextR0 L 0 (Lng L - 1) hnext
  simp [transCondI, lastIdx, lastParent, he1z, hpar0, adm_zero L]

/-! ## 4. 露出する narrower Prop（条件 (II)/(III)/(IV)/(V) の内部枝） -/

/-- **`OTmulti_interior_notCondI_om2` の内部残差**（本ファイルで閉じなかった部分）。
末尾 mono 成分 `L` が条件 (II)/(III)/(IV)/(V) を満たすとき、基本列 `oper L m` の翻訳が
`OT_B` に留まり（内部 OT ステップ、Isabelle `OTint`）、かつ `Trans L` 以下である
（降下柱の弱化、Isabelle `ordIntC`）。経験的に mono 末尾成分は 220/220 が条件 (I)
ゆえ本仮定領域は空。 -/
def OTmulti_interior_intCond_nc1 : Prop :=
  ∀ (L : PS) (m : ℕ), STPS L → monoT L = true → 1 < Lng L → 1 < m →
    oper L m ≠ Pred L → Trans L ∈ OT_B →
    (transCondII L = true ∨ transCondIII L = true ∨
      transCondIV L = true ∨ transCondV L = true) →
    Trans (oper L m) ∈ OT_B ∧ leBT (Trans (oper L m)) (Trans L) = true

/-! ## 5. `OTmulti_interior_notCondI_om2` の条件 II–VI ＋零脚クローズ -/

/-- **`OTmulti_interior_notCondI_om2`（`8.7-otmulti-interior`:139）を narrower Prop
`OTmulti_interior_intCond_nc1` から閉じる**。条件 (VI) 全域と零脚（C-true）全域を
無条件で処理する（Isabelle `opx_OTmulti` の `casea`：`lm00` 零脚 ＋ `closEx` の
条件 (VI) 脚）。 -/
theorem otMultiNotCondI_nc1_holds (H : OTmulti_interior_intCond_nc1) :
    OTmulti_interior_notCondI_om2 := by
  intro L m as pl hLST hLmono hLgt hm hLpred hTL hTLOT hostReshaped hguard
  have hLR : RTPS L := STPS_RTPS L hLST
  have hLT : TPS L := RTPS_TPS L hLR
  have hLnm : multiT L = false := by
    by_contra hc
    have h : multiT L = true := by simpa using hc
    rw [multiT] at h; simp [hLmono] at h
  by_cases hC : (P (oper L m)).getD 0 [] = [((0 : ℕ), (0 : ℕ))]
  · -- C-true: guard の下で常に casea に落ち、`oper L m = [(0,0)]`
    rw [if_pos hC]
    have hcond_casea : nextR L 0 0 (Lng L - 1) = false ∨ 0 < entry L 1 (Lng L - 1) := by
      by_cases hnext : nextR L 0 0 (Lng L - 1) = true
      · by_cases he1 : 0 < entry L 1 (Lng L - 1)
        · exact Or.inr he1
        · exfalso
          have he1z : entry L 1 (Lng L - 1) = 0 := by omega
          rcases hguard with hnotI | ⟨_, hbig⟩
          · exact hnotI (caseb_transCondI_nc1 L hnext he1z)
          · have hPrep : P (oper L m) = List.replicate m (Pred L) :=
              nonmulti_fseq_1 L m hLT (by omega) hLnm hnext he1z
            have hfirst : (P (oper L m)).getD 0 [] = Pred L := by
              rw [hPrep]
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              simp [List.replicate_succ]
            have hPred00 : Pred L = [((0 : ℕ), (0 : ℕ))] := hfirst.symm.trans hC
            have hPredLng : Lng (Pred L) = Lng L - 1 := by
              rw [Pred, if_neg (by omega : ¬ Lng L ≤ 1)]
              simp [Lng, List.length_dropLast]
            have h1 : Lng (Pred L) = 1 := by rw [hPred00]; simp [Lng]
            rw [hPredLng] at h1
            omega
      · left
        cases h : nextR L 0 0 (Lng L - 1) with
        | false => rfl
        | true => exact absurd h hnext
    have hPsingle : P (oper L m) = [oper L m] :=
      nonmulti_fseq_2 L m hLT (by omega) hLnm hcond_casea
    have hfirst : (P (oper L m)).getD 0 [] = oper L m := by rw [hPsingle]; simp
    have holm00 : oper L m = [((0 : ℕ), (0 : ℕ))] := hfirst.symm.trans hC
    have hTrans00 : Trans (oper L m) = BZero := by rw [holm00]; exact Trans_zerocol_nc1
    rw [hTrans00]
    have haddD0 : addBT (Dprin (0 : ℕ∞) BZero) BZero = Dprin (0 : ℕ∞) BZero := by
      simp [addBT, Dprin, BZero]
    rw [haddD0]
    have hgoalT : BT.trm (as ++ [BP.db (0 : ℕ∞) BZero]) ∈ OT_B :=
      OT_append_corr_om as [BP.db (0 : ℕ∞) BZero] pl hostReshaped D00_OT_B_nc1
        (leBT_min_nc1 pl)
        (Trm_append_T_B_nc1 as [BP.db (0 : ℕ∞) BZero] pl hostReshaped.2 D00_OT_B_nc1.2)
    have hrw : addBT (BT.trm as) (Dprin (0 : ℕ∞) BZero)
        = BT.trm (as ++ [BP.db (0 : ℕ∞) BZero]) := by simp [addBT, Dprin]
    rw [hrw]; exact hgoalT
  · -- C-false: BLK = Trans (oper L m)
    rw [if_neg hC]
    have hnotI : ¬ (transCondI L = true) := by
      rcases hguard with h | ⟨hC', _⟩
      · exact h
      · exact absurd hC' hC
    by_cases hVI : transCondVI L = true
    · -- 条件 (VI): 交換等式 → operB snoc 局在 → e4x（closEx）
      have condVIadmTower : CondVIAdmTowerScb :=
        condVIAdmTowerScb_of_scbforms_v6 CondVI_scbdec_adm_forms_v6_holds
      have condVInadm : CondVIExchNadm :=
        condVIExchNadm_holds_v6p CondVIres_nadm_Ltower_holds_nc
      have condVIadmEq : OTdisp_condVI_adm_eq :=
        OTdisp_condVI_adm_eq_of_CondVIAdmTowerScb condVIadmTower
      have condVInadmEq : OTdisp_condVI_nadm_eq :=
        OTdisp_condVI_nadm_eq_of_CondVIExchNadm condVInadm
      have he1pos : 0 < entry L 1 (Lng L - 1) := by
        have h := hVI
        simp only [transCondVI, lastIdx, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at h
        omega
      obtain ⟨k, hk⟩ : ∃ k, Trans (oper L m) = operB (Trans L) (numBT k) := by
        by_cases hL2 : Lng L = 2
        · have hz : ¬(entry L 0 (Lng L - 1) = 0 ∧ entry L 1 (Lng L - 1) = 0) := by
            rintro ⟨_, h2⟩; omega
          have hpL := hasParent_of_oper_ne_Pred_nc1 L m hLgt hz hLpred
          exact ⟨m - 2, OTdisp_condVI_j1eq1_eq_holds L m hLR hLmono hL2 hVI hpL (by omega)⟩
        · have hj1gt : 1 < Lng L - 1 := by omega
          by_cases hadm : adm L (transJ0 L) = true
          · exact ⟨m - 2, condVIadmEq L m hLST hLmono hVI hj1gt hadm (by omega)⟩
          · exact ⟨m - 1, condVInadmEq L m hLST hLmono hVI hj1gt hadm (by omega)⟩
      rw [hk, hTL, ← operB_snoc_local_nc1 as pl (numBT k)]
      exact OT_B_operB_numBT_nc1 hostReshaped k
    · -- 条件 (II)/(III)/(IV)/(V): narrower Prop から OT 所属＋順序を得て OT_append_corr
      have hVIf : transCondVI L = false := by
        cases h : transCondVI L with
        | true => exact absurd h hVI
        | false => rfl
      have hcond : transCondII L = true ∨ transCondIII L = true ∨
          transCondIV L = true ∨ transCondV L = true := by
        by_cases hIII : transCondIII L = true
        · exact Or.inr (Or.inl hIII)
        · by_cases hV : transCondV L = true
          · exact Or.inr (Or.inr (Or.inr hV))
          · have hnotA : ¬(transCondI L = true ∨ transCondIII L = true
                ∨ transCondV L = true) := by
              rintro (h | h | h)
              · exact hnotI h
              · exact hIII h
              · exact hV h
            rcases condII_or_condIV L hLR hLmono hLgt hnotA hVIf with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
      obtain ⟨hmemOT, hord⟩ := H L m hLST hLmono hLgt hm hLpred hTLOT hcond
      obtain ⟨cs, hcs⟩ : ∃ cs, Trans (oper L m) = BT.trm cs :=
        ⟨untrm (Trans (oper L m)), by cases Trans (oper L m); rfl⟩
      have hcsOT : BT.trm cs ∈ OT_B := hcs ▸ hmemOT
      have hjunc : leBT (BT.trm cs) (BT.trm [pl]) = true := by
        have h := hord; rw [hcs, hTL] at h; exact h
      have hgoalT : BT.trm (as ++ cs) ∈ OT_B :=
        OT_append_corr_om as cs pl hostReshaped hcsOT hjunc
          (Trm_append_T_B_nc1 as cs pl hostReshaped.2 hcsOT.2)
      rw [hcs]
      show addBT (BT.trm as) (BT.trm cs) ∈ OT_B
      have hrw : addBT (BT.trm as) (BT.trm cs) = BT.trm (as ++ cs) := rfl
      rw [hrw]; exact hgoalT

#print axioms otMultiNotCondI_nc1_holds

end PSS
