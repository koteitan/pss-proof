import «8».«8.7-otdisp-OTmulti2»
import «8».«8.7-otx-condI-eqs»
import «8».«8.1-condI-masterCF-chunk5»
import «8».«8.7-descend-last2»
import «8».«8.7-fseq-descend-props»
import «8».«8.7-const00-Trans»

/-!
# §8.7 OT 柱 — `OTmulti_interior_om2` の条件 (I) 内部枝クローズ（零脚込み）

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTmulti_interior_om2`
  （`«8».«8.7-otdisp-OTmulti2»`:116）＝ Isabelle `opx_OTmulti` の `casea`/`caseb`
  内部残差 (`isabelle/layerB/pss_wip.thy`:115556、6 分岐 dispatch のうち条件 (I) 枝
  ＋ `caseb`/`lm00` の零脚)。訂正: なし。
- 状態: 🤖 GREEN-MODULO 1（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `OTmulti_interior_om2` の**条件 (I) 全域を無条件で閉じ**（C-false ＋ `Lng L = 2`
  の零脚 C-true）、残り（条件 II–VI ＋ `Lng L > 2` の零脚＝経験的に空）を
  ONE narrower Prop `OTmulti_interior_notCondI_om2` に露出する。

## `OTmulti_interior_om2` の構造（`opx_OTmulti` casea/caseb）

複項 host の構造層は `«8».«8.7-otdisp-OTmulti2»` の
`OTdisp_OTmulti_of_interior_om2` が `f7x_Trans_append_Pblocks` で無条件に除去済み。
残る内部残差 `OTmulti_interior_om2` は、末尾 mono 成分 `L`（`Trans L = Trm [pl]`,
host 埋め込み `Trm (as ++ [pl])`）に対する `addBT (Trm as) BLK ∈ OT_B` の一点で、
`BLK` は f7x の零脚フラグ込みの再組立
（`C := (P (oper L m)).getD 0 [] = [(0,0)]` で `D₀0` の前置が入る）。

数値監査（`«8».«8.7-otdisp-OTmulti»` ヘッダ ＋ 本 wave の ST_PS orbit 追検証）では、
複項 host の末尾 mono 成分（`1 < Lng L`）は **標準形 orbit 上 220/220 が条件 (I)**
（条件 II–VI は経験的に空）で、さらに **`C = true ⟺ Lng L = 2`**
（`Lng L > 2` の条件 (I) では `oper L m` の先頭 P ブロックが長さ ≥ 2 で
`[(0,0)]` になり得ない＝C-false。零脚 C-true の実例は `L = ((0,0),(1,0))` 系で
`oper L m = ((0,0))ᵐ`、20 個の複項標準形 host の末尾成分として出現）。

## 本ファイルが閉じたもの（条件 (I) 全域）

`transCondI L` のとき、`C` の真偽で 2 通り:

* **C-false**: `BLK = Trans (oper L m)`。条件 (I) の交換等式
  `Trans (oper L m) = operB (Trans L) (numBT k)`（Isabelle `closEx`）:
  - `1 < Lng L - 1`: `condI_exchange1`（`8.1-Trans-fseq-condI`:433、Isabelle
    `y3g_condI_exchange1_rtps`）で `k = m - 1`。parent の値に依らない。
  - `Lng L = 2`: `OTdisp_condI_j1eq1_eq_holds`（`8.7-otx-condI-eqs`:228、Isabelle
    `otx_condI_j1eq1_eq`）で `k = (if entry L 1 0 = 0 then m-2 else m-1)`。
* **C-true ＋ `Lng L = 2`（零脚）**: 先頭ブロック `[(0,0)]` ＝ `oper L m = ((0,0))ᵐ`
  （`oper_len2_fd` ＋ `P_concat` の先頭列一致で `entry L 1 0 = 0`）ゆえ
  `Trans (oper L m) = (D₀0) ×_B (m-1)`（`const00_Trans`）で、`D₀0` 前置後は
  `(D₀0) ×_B m = operB (Trans L) (numBT (m-1))`（`Trans L = D₀(D₀0)`,
  `operB_succ_body_ci`）に畳まれる（Isabelle `caseb`/`lm00` の数項化）。

いずれも `operB` の snoc 局在
`addBT (Trm as) (operB (Trm [pl]) (numBT k)) = operB (Trm (as ++ [pl])) (numBT k)`
（Isabelle `opx_operB_snoc_local`）と `e4x_OT_B_operB_numBT`（`buchholz_fseq_closed`
の零脚埋め）で `OT_B` に留まる（host `Trm (as ++ [pl]) ∈ OT_B` から供給）。

## ONE narrower Prop に露出したもの（経験的に空）

`OTmulti_interior_notCondI_om2` は仮定
`¬ transCondI L ∨ (C = true ∧ 1 < Lng L - 1)` の下で残差結論を要求する:
* `¬ transCondI L`: 条件 (II)/(III)/(IV)/(V)/(VI)（末尾 mono 成分では経験的に空）。
* `C = true ∧ 1 < Lng L - 1`: `Lng L > 2` の零脚（`oper L m` の先頭 P ブロックは
  長さ ≥ 2 なので経験的に空）。

- 依存（ビルド済みのみ import）: `«8».«8.7-otdisp-OTmulti2»`
  （`OTmulti_interior_om2`）、`«8».«8.7-otx-condI-eqs»`（`OTdisp_condI_j1eq1_eq_holds`
  ／推移的に `condI_exchange1`・`operB_succ_body_ci`・`two_column_Trans`・
  `buchholz_fseq_closed`・`oper_len2_fd`・`mono_hasParent_row0`・`RTPS_mono_head_eq`・
  `hasParent_next_fseq`）、`«8».«8.1-condI-masterCF-chunk5»`
  （`scx_condI_j0pos_masterCF`）、`«8».«8.7-descend-last2»`
  （`operI_j0zero_trans_mult_holds`／`P_concat`・`P_nonempty`）、
  `«8».«8.7-fseq-descend-props»`
  （`FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds`）、
  `«8».«8.7-const00-Trans»`（`const00_Trans`）。
- private helper suffix: `_mi`。
-/

namespace PSS

/-! ## 1. Buchholz 側の小補題（`«8».«8.7-otdisp-OTmulti»` の private 版を再導出） -/

/-- `0_B ∈ OT_B`。 -/
private theorem BZero_OT_B_mi : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- `operB 0_B z = 0_B`。Isabelle `b1x_operB_zero`。 -/
private theorem operB_BZero_mi (z : BT) : operB BZero z = BZero := by
  simp [operB, BZero, bOperCore]

/-- Isabelle `e4x_OT_B_operB_numBT` (`layerB/pss_wip.thy`:61390): 零脚を
`operB_BZero_mi` で埋めて `buchholz_fseq_closed` を無条件化。 -/
private theorem OT_B_operB_numBT_mi {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz, operB_BZero_mi]; exact BZero_OT_B_mi
  · exact buchholz_fseq_closed a n ha hz

/-- Isabelle `opx_operB_snoc_local`（`b1x_operB_multi` の snoc 版）:
`operB` は最後の top-level principal に局在する。 -/
private theorem operB_snoc_local_mi : ∀ (as : List BP) (pl : BP) (z : BT),
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
      rw [List.cons_append, hstep, operB_snoc_local_mi as pl z]
      cases hop : operB (BT.trm [pl]) z with
      | trm xs => simp [addBT]

/-- Isabelle `d2x_multBT_replicate`: 単一 principal の自然数倍は複製。 -/
private theorem multBT_single_mi (p : BP) (k : ℕ) :
    multBT (BT.trm [p]) k = BT.trm (List.replicate k p) := by
  induction k with
  | zero => rfl
  | succ j ih => rw [multBT, ih]; simp [addBT, List.replicate_succ']

/-- `D₀0` を数項 `(D₀0) ×_B k` の左に足すと `(D₀0) ×_B (k+1)`。 -/
private theorem addBT_D0_multBT_mi (k : ℕ) :
    addBT (Dprin (0 : ℕ∞) BZero) (multBT (Dprin 0 BZero) k)
      = multBT (Dprin 0 BZero) (k + 1) := by
  rw [show (Dprin (0 : ℕ∞) BZero) = BT.trm [BP.db 0 BZero] from rfl,
    multBT_single_mi, multBT_single_mi, addBT]
  simp [List.replicate_succ]

/-! ## 2. 露出する narrower Prop（条件 II–VI ＋ `Lng L > 2` の零脚） -/

/-- **`OTmulti_interior_om2` の残差**（本ファイルで閉じなかった部分）。
仮定 `¬ transCondI L ∨ ((P (oper L m)).getD 0 [] = [(0,0)] ∧ 1 < Lng L - 1)`
の下で残差結論を要求する。経験的に前者（条件 II–VI）は空、後者（`Lng L > 2` の
零脚）も空（`oper L m` の先頭 P ブロックは長さ ≥ 2）。 -/
def OTmulti_interior_notCondI_om2 : Prop :=
  ∀ (L : PS) (m : ℕ) (as : List BP) (pl : BP),
    STPS L → monoT L = true → 1 < Lng L → 1 < m → oper L m ≠ Pred L →
    Trans L = BT.trm [pl] → Trans L ∈ OT_B → BT.trm (as ++ [pl]) ∈ OT_B →
    (¬ (transCondI L = true) ∨
      ((P (oper L m)).getD 0 [] = [(0, 0)] ∧ 1 < Lng L - 1)) →
    addBT (BT.trm as)
      (if (P (oper L m)).getD 0 [] = [(0, 0)]
       then addBT (Dprin 0 BZero) (Trans (oper L m))
       else Trans (oper L m)) ∈ OT_B

/-! ## 3. `OTmulti_interior_om2` の条件 (I) 全域クローズ -/

/-- **`OTmulti_interior_om2`（`8.7-otdisp-OTmulti2`:116）を narrower Prop
`OTmulti_interior_notCondI_om2` から閉じる**。条件 (I) 全域（C-false ＋ `Lng L = 2`
の零脚 C-true）を無条件で処理する（Isabelle `opx_OTmulti` の `closEx`／零脚数項化）。 -/
theorem otMultiInterior_holds (h : OTmulti_interior_notCondI_om2) :
    OTmulti_interior_om2 := by
  intro L m as pl hLST hLmono hLgt hm hLpred hTL hTLOT hostReshaped
  have hLR : RTPS L := STPS_RTPS L hLST
  by_cases hI : transCondI L = true
  · by_cases hC : (P (oper L m)).getD 0 [] = [(0, 0)]
    · -- C-true
      by_cases hbig : 1 < Lng L - 1
      · -- Lng L > 2 の零脚は narrower Prop に委譲（経験的に空）
        exact h L m as pl hLST hLmono hLgt hm hLpred hTL hTLOT hostReshaped
          (Or.inr ⟨hC, hbig⟩)
      · -- Lng L = 2 の零脚: oper L m = ((0,0))ᵐ、数項化
        have hL2 : Lng L = 2 := by omega
        have hLT : TPS L := RTPS_TPS L hLR
        -- 条件 (I) の setup（Lng L = 2）
        have e1z : entry L 1 (Lng L - 1) = 0 := by
          simp only [transCondI, Bool.and_eq_true, beq_iff_eq, lastIdx] at hI; exact hI.1
        have hj1 : Lng L - 1 = 1 := by omega
        have he11z : entry L 1 1 = 0 := by rw [hj1] at e1z; exact e1z
        have hp0 : hasParent L 0 (Lng L - 1) = true :=
          mono_hasParent_row0 L hLT hLmono (Lng L - 1) (by omega) (by omega)
        have he0pos : 0 < entry L 0 (Lng L - 1) := by
          have hn := hasParent_next_fseq L 0 (Lng L - 1) hp0
          have hh : nextrel0 L (parent L 0 (Lng L - 1)) (Lng L - 1) = true := by
            simpa [nextR] using hn
          simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh; omega
        have hnz1 : ¬(entry L 0 1 = 0 ∧ entry L 1 1 = 0) := by
          rw [hj1] at he0pos; omega
        have hi1 : idx1 L 1 = 0 := by simp [idx1, he11z]
        have hp1 : hasParent L (idx1 L 1) 1 = true := by rw [hi1, ← hj1]; exact hp0
        have hdiag : entry L 0 0 = entry L 1 0 := RTPS_mono_head_eq L hLR hLmono
        have hop : oper L m = List.replicate m (entry L 1 0, entry L 1 0) := by
          rw [oper_len2_fd L hL2 hnz1 hp1 0 0 (by simp [hi1]) (by simp [hi1])]
          rw [hdiag]; simp [List.map_const']
        -- 先頭ブロック一致で entry L 1 0 = 0
        have hm1 : 1 ≤ m := by omega
        have hhead0 : (oper L m).getD 0 ((0 : ℕ), (0 : ℕ)) = (0, 0) := by
          have hflat : (P (oper L m)).flatten = oper L m := P_concat (oper L m)
          cases hP : P (oper L m) with
          | nil => exact absurd hP (P_nonempty (oper L m))
          | cons b bs =>
            have hb : b = [(0, 0)] := by rw [hP] at hC; simpa using hC
            have hsplit : oper L m = b ++ bs.flatten := by rw [← hflat, hP]; simp
            rw [hsplit, hb]; simp
        have hheadu : (oper L m).getD 0 ((0 : ℕ), (0 : ℕ)) = (entry L 1 0, entry L 1 0) := by
          rw [hop]
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp [List.replicate_succ]
        have hu0 : entry L 1 0 = 0 := by
          have huu : (entry L 1 0, entry L 1 0) = ((0 : ℕ), (0 : ℕ)) := hheadu.symm.trans hhead0
          simp only [Prod.mk.injEq] at huu; exact huu.1
        -- Trans L = D₀(D₀0)
        have hTLval : Trans L = Dprin (0 : ℕ∞) (Dprin 0 BZero) := by
          rw [two_column_Trans L hLR hLmono hL2, he11z, hu0]; norm_num
        -- Trans (oper L m) = (D₀0) ×_B (m-1)
        have hTransoper : Trans (oper L m) = multBT (Dprin (0 : ℕ∞) BZero) (m - 1) := by
          rw [hop, hu0]
          have hc00 := const00_Trans 0 (m - 1)
          rw [show m - 1 + 1 = m from by omega] at hc00
          rw [hc00]; norm_num
        -- BLK = operB (Trans L) (numBT (m-1))
        have hBLK_eq : addBT (Dprin (0 : ℕ∞) BZero) (Trans (oper L m))
            = operB (Trans L) (numBT (m - 1)) := by
          rw [hTransoper, addBT_D0_multBT_mi, hTLval,
            show Dprin (0 : ℕ∞) (Dprin 0 BZero)
                = Dprin (0 : ℕ∞) (addBT BZero (Dprin 0 BZero)) from rfl,
            operB_succ_body_ci BZero (0 : ℕ∞) (m - 1)]
        rw [if_pos hC, hBLK_eq, hTL, ← operB_snoc_local_mi as pl (numBT (m - 1))]
        exact OT_B_operB_numBT_mi hostReshaped (m - 1)
    · -- 条件 (I) ＋ C-false: 交換等式 → `operB` snoc 局在 → `e4x`
      rw [if_neg hC]
      obtain ⟨k, hk⟩ : ∃ k, Trans (oper L m) = operB (Trans L) (numBT k) := by
        by_cases hbig : 1 < Lng L - 1
        · exact ⟨m - 1, condI_exchange1 scx_condI_j0pos_masterCF
            operI_j0zero_trans_mult_holds
            FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds
            L m hLR hLmono hbig hI (by omega)⟩
        · have hL2 : Lng L = 2 := by omega
          exact ⟨_, OTdisp_condI_j1eq1_eq_holds L m hLR hLmono hL2 hI (by omega)⟩
      rw [hk, hTL, ← operB_snoc_local_mi as pl (numBT k)]
      exact OT_B_operB_numBT_mi hostReshaped k
  · -- 条件 (II)–(VI) は narrower Prop に委譲
    exact h L m as pl hLST hLmono hLgt hm hLpred hTL hTLOT hostReshaped (Or.inl hI)

#print axioms otMultiInterior_holds

end PSS
