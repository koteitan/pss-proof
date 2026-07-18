import «5».«5.3-pred-is-oper1»
import «6».«6.2-P-fseq»
import «6».«6.2-P-components-nonmulti»
import «6».«6.7-standard-P-components»
import «6».«6.8-standard-slice-Br-descending»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-monoT»
import «8».«8.7-descend-last2»
import «8».«8.7-Trans-preserves-OT»

/-!
# §8.7 OT 柱 — `OTdisp_OTmulti` の複項 host 構造分解（`opx_OTmulti` 移植・第2弾）

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTdisp_OTmulti`
  （`«8».«8.7-Trans-preserves-OT»`:109）＝ Isabelle `opx_OTmulti`
  (`isabelle/layerB/pss_wip.thy`:115556)。訂正: なし。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  **`OTdisp_OTmulti` を複項 host の構造分解によって、末尾 mono 成分 `L` に関する
  内部残差 `OTmulti_interior_om2` へ還元する**（`OTdisp_OTmulti_of_interior_om2`）。
  これは Isabelle `opx_OTmulti` が行う「複項 host 構造スロットの除去」そのもの
  （census: *the multi-host structural slot is eliminated in favour of the strictly
  smaller interior residual*）。

## 証明の骨格（`opx_OTmulti` 逐語）と Lean 移植の勝ち筋

複項 host `N`（`L := last (P N) = drop (Pcut N) N`, `A := take (Pcut N) N`）について:
* `A ++ L = N`、`L ∈ ST_PS`、`monoT L`、`1 < Lng L`（`L[m] ≠ Pred N` から）
  （`STPS_exists_rank_68`/`SkTPS_STPS`/`SkTPS_P_component`、`P_components_nonmulti`、
  `multi_length_fseq`、`P_fseq_1` の対偶）。
* `P N = P A ++ P L`、`P L = [L]`（`P_last_multi`/`P_nonmulti_eq`）ゆえ
  `f7x_Trans_append_Pblocks` で `Trans N = Trm (as ++ [pl])`
  （`Trans A = Trm as`, `Trans L = Trm [pl]`＝mono 単一 principal）。
* `oper N m = A ++ oper L m`、`P (oper N m) = P A ++ P (oper L m)`（`P_fseq_2`）ゆえ
  再び `f7x_Trans_append_Pblocks` で
  `Trans (oper N m) = addBT (Trm as) (flag ? addBT (D₀0) (Trans (oper L m)) : Trans (oper L m))`。
* あとは `Trans (oper N m) ∈ OT_B` は末尾 mono 成分 `L` の内部残差
  `OTmulti_interior_om2` そのもの（`f7x` の零脚フラグ込みで露出）。

Isabelle 版は `caseb`（`L[m]` 複項＝replicate）と `casea`（`L[m]` 単項）に分けて
`opx_OT_append_rep` の peel 帰納を回すが、Lean 版は接頭辞 `A` を切り出す
`f7x_Trans_append_Pblocks` が両ケースを一様に処理するので peel 帰納は不要。

## 残差（`OTmulti_interior_om2`）— これ以上の還元に必要なもの

内部残差 `OTmulti_interior_om2` は末尾 mono 成分 `L` の
`Trans (oper L m)` の OT 再組立を要求する。これを discharge するには、Isabelle
`opx_OTmulti` の `casea` 6 分岐 dispatch が要る:
* 条件 (I)/(VI): 交換等式 → `operB` → `e4x_OT_B_operB_numBT`（露出済 `OTdisp_*` 群）。
* 条件 (II): `OTdisp_exchII`（`c2sx_tailval` 経由の交換脚）。
* 条件 (III)/(IV)/(V): `OTdisp_OTint`（残差本体）＋ 内部 `leBT` 降下（Isabelle `ordIntC`）。
* さらに `f7x` の零脚（`(P (oper L m)).getD 0 [] = [(0,0)]` ＝先頭零列で
  `Trans (oper L m)` が `0_B` になる補題）。
本ファイルはこれらを **1 本の内部残差** に束ねて露出し、複項構造層のみを無条件で外す。

- 依存（ビルド済みのみ import）: `«5».«5.3-pred-is-oper1»`（`pred_is_oper1`）、
  `«6».«6.2-P-fseq»`（`P_last_multi`/`P_fseq_1`/`P_fseq_2`/`P_concat`/`P_nonempty`/
  `P_nonmulti_eq`/`multi_length_fseq`）、`«6».«6.2-P-components-nonmulti»`
  （`P_components_nonmulti`）、`«6».«6.7-standard-P-components»`
  （`SkTPS_STPS`/`SkTPS_P_component`）、`«6».«6.8-standard-slice-Br-descending»`
  （`STPS_exists_rank_68`）、`«7».«7.3-Trans-welldefined»`
  （`trans_multi_prefix_RTPS`/`Trans_mem_T_B`/`STPS_RTPS`/`RTPS_TPS`）、
  `«7».«7.3-Trans-preserves-monoT»`（`m_7_3_Trans_monoT`）、
  `«8».«8.7-descend-last2»`（`f7x_Trans_append_Pblocks_holds`）、
  `«8».«8.7-Trans-preserves-OT»`（`OTdisp_OTmulti` の定義ほか）。

private helper suffix: `_om2`。
-/

namespace PSS

/-! ## 1. 小補題（mono 成分の単一 principal 化、host 末尾の isOT） -/

/-- Isabelle `opx_mono_Trans_singleton`: mono 成分の `Trans` は単一 principal。 -/
private theorem mono_Trans_singleton_om2 (L : PS) (hR : RTPS L) (hmono : monoT L = true) :
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

/-- host 末尾 principal は `isOT_BP`。 -/
private theorem isOT_BPList_last_om2 : ∀ (as : List BP) (pl : BP),
    isOT_BPList (as ++ [pl]) = true → isOT_BP pl = true
  | [], pl, h => by simpa [isOT_BPList] using h
  | a :: as, pl, h => by
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at h
      exact isOT_BPList_last_om2 as pl h.2

private theorem isOT_last_om2 (as : List BP) (pl : BP)
    (h : BT.trm (as ++ [pl]) ∈ OT_B) : isOT_BP pl = true := by
  have hOT : isOT_BT (BT.trm (as ++ [pl])) = true := h.1
  rw [isOT_BT, Bool.and_eq_true] at hOT
  exact isOT_BPList_last_om2 as pl hOT.1

/-! ## 2. 内部残差（末尾 mono 成分の `Trans (oper L m)` OT 再組立） -/

/-- **`OTdisp_OTmulti` の内部残差**（Isabelle `opx_OTmulti` の `casea`/`caseb`
内部枝、および `OTint`/`ordIntC`/`c2sx_tailval` 依存部を 1 本に束ねたもの）。

末尾 mono 成分 `L`（host 埋め込み `Trans L = Trm [pl]`, `Trans N = Trm (as ++ [pl])`）に
対し、`f7x_Trans_append_Pblocks` の零脚フラグ込みで再組立した `Trans (oper N m)` が
`OT_B` に留まることを要求する。複項 host の構造層は本ファイルで無条件に除去済み。 -/
def OTmulti_interior_om2 : Prop :=
  ∀ (L : PS) (m : ℕ) (as : List BP) (pl : BP),
    STPS L → monoT L = true → 1 < Lng L → 1 < m → oper L m ≠ Pred L →
    Trans L = BT.trm [pl] → Trans L ∈ OT_B → BT.trm (as ++ [pl]) ∈ OT_B →
    addBT (BT.trm as)
      (if (P (oper L m)).getD 0 [] = [(0, 0)]
       then addBT (Dprin 0 BZero) (Trans (oper L m))
       else Trans (oper L m)) ∈ OT_B

/-! ## 3. 複項 host 構造分解 — `OTdisp_OTmulti` を内部残差へ還元 -/

/-- **`OTdisp_OTmulti`（`8.7-Trans-preserves-OT`:109）を内部残差
`OTmulti_interior_om2` から閉じる**。Isabelle `opx_OTmulti`
(`layerB/pss_wip.thy`:115556) の複項 host 構造分解を逐語移植。 -/
theorem OTdisp_OTmulti_of_interior_om2 (hint : OTmulti_interior_om2) :
    OTdisp_OTmulti := by
  intro N m hNST hmulti hostOT hm hNpred
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
  -- L is standard, mono, of length > 1
  obtain ⟨k, hk⟩ := STPS_exists_rank_68 N hNST
  have hLST : STPS L := SkTPS_STPS k L (SkTPS_P_component k N L hk hLmem)
  have hLR : RTPS L := STPS_RTPS L hLST
  have hLT : TPS L := RTPS_TPS L hLR
  have hLne : L ≠ [] := hLT
  have hLgt : 1 < Lng L := by
    rcases Nat.lt_or_ge (Lng L) 2 with h | h
    · exfalso
      have hL1 : Lng L = 1 := by
        have : 0 < Lng L := List.length_pos_of_ne_nil hLne
        omega
      have hlast1 : Lng ((P N).getLastD []) = 1 := by rw [hPL_last.1]; exact hL1
      exact hNpred (P_fseq_1 N m hNT (by omega) hlast1).1
    · omega
  have hLzm : zeroT L = true ∨ monoT L = true := P_components_nonmulti N hNT L hLmem
  have hLnm : multiT L = false := by rcases hLzm with h | h <;> simp [multiT, h]
  have hLmono : monoT L = true := by
    rcases hLzm with h | h
    · exfalso; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h; omega
    · exact h
  have hLne00 : L ≠ [(0, 0)] := by
    intro h; rw [h] at hLgt; simp [Lng] at hLgt
  -- Buchholz side: Trans L = Trm [pl], Trans A = Trm as, Trans N = Trm (as ++ [pl])
  obtain ⟨pl, hTL⟩ := mono_Trans_singleton_om2 L hLR hLmono
  obtain ⟨as, hTA⟩ : ∃ as, Trans A = BT.trm as := ⟨untrm (Trans A), by cases Trans A; rfl⟩
  have hPLsingle : P L = [L] := P_nonmulti_eq L hLnm
  have hgl : (P N).getLast hPNe = L := by
    have hconv : (P N).getLast hPNe = (P N).getLastD [] := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hPNe, Option.getD_some]
    rw [hconv]; exact hPL_last.1
  have hPsplit : P N = P A ++ [L] := by
    have h1 := List.dropLast_append_getLast hPNe
    rw [hPL_last.2, hgl] at h1; exact h1.symm
  have hPeqN : P N = P A ++ P L := by rw [hPLsingle]; exact hPsplit
  have hARTPS : RTPS A := trans_multi_prefix_RTPS N hNR hmulti
  have hRAL : RTPS (A ++ L) := by rw [hNAL]; exact hNR
  have hTN : Trans N = BT.trm (as ++ [pl]) := by
    have hs := f7x_Trans_append_Pblocks_holds A L hRAL hLR (by rw [hNAL]; exact hPeqN)
    rw [hNAL, hPLsingle, List.getD_cons_zero, if_neg hLne00, hTA, hTL] at hs
    simpa [addBT] using hs
  have hostReshaped : BT.trm (as ++ [pl]) ∈ OT_B := hTN ▸ hostOT
  have hTransLOT : Trans L ∈ OT_B := by
    rw [hTL]
    refine ⟨?_, ?_⟩
    · show isOT_BT (BT.trm [pl]) = true
      have hpl : isOT_BP pl = true := isOT_last_om2 as pl hostReshaped
      simp only [isOT_BT, isOT_BPList, descP, hpl, Bool.and_true]
    · have := Trans_mem_T_B L hLR; rw [hTL] at this; exact this
  -- oper L m ≠ Pred L
  have hfs2 := P_fseq_2 N m hNT (by omega) (by rw [hPL_last.1]; exact hLgt)
  have hAflat : (P N).dropLast.flatten = A := by rw [hPL_last.2, P_concat]
  have hoval : oper N m = A ++ oper L m := by rw [hfs2.1, hAflat, hPL_last.1]
  have hPoval : P (oper N m) = P A ++ P (oper L m) := by
    rw [hfs2.2, hPL_last.2, hPL_last.1]
  have hLmPred : oper L m ≠ Pred L := by
    intro e
    apply hNpred
    have h2 : Pred L = L.dropLast := by simp [Pred, Nat.not_le_of_lt hLgt]
    have h3 : Pred N = N.dropLast := by simp [Pred, Nat.not_le_of_lt LN]
    rw [hoval, e, h2, h3, ← hNAL, List.dropLast_append_of_ne_nil hLne]
  -- Trans (oper N m) via prefix split, then apply the interior residual
  have hRNm : RTPS (oper N m) := STPS_RTPS _ (STPS.oper hNST m (by omega))
  have hRLm : RTPS (oper L m) := STPS_RTPS _ (STPS.oper hLST m (by omega))
  have hsplitM := f7x_Trans_append_Pblocks_holds A (oper L m)
    (by rw [← hoval]; exact hRNm) hRLm (by rw [← hoval]; exact hPoval)
  rw [hoval, hsplitM, hTA]
  exact hint L m as pl hLST hLmono hLgt hm hLmPred hTL hTransLOT hostReshaped

#print axioms OTdisp_OTmulti_of_interior_om2

end PSS
