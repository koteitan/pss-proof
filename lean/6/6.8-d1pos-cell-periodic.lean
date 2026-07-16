import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-base»
import «6».«6.8-d1pos-trmax»
import «6».«6.8-d1pos-le0»
import «6».«6.8-d1pos-notbrle»
import «6».«6.8-d1pos-anchor-regA»
import «6».«6.8-d1pos-anchor-regB»
import «6».«6.8-d1pos-period»

/-!
# §6.8 d1pos CELL-4 (PERIODIC-TAIL) take-eq セル ＋ shamt=0 anchor 束

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域、周期尾部セルと LOW regB/boundary セルの anchor 束）
- Isabelle (isabelle/pss_mechanized.thy):
  - `oper_d1pos_notbrle_LOW_take_eq_periodic` (20584)
  - `oper_d1pos_low_anchor_shamt0` (20904)
  - 私的再証明（並行 agent 域、suffix `_cp`）:
    `oper_d1pos_ctx_notbrleNp_verbatim` (20322)
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Props・`oper_d1pos_ctx_j0lt`/
  `oper_d1pos_ctx_r1le`）、«6».«6.8-d1pos-notbrle»（`oper_d1pos_notbrle_Br_align`
  /`_regA`・`oper_d1pos_tail_junction`）、«6».«6.8-d1pos-anchor-regB»
  （`oper_d1pos_row0_agree`・`oper_d1pos_clt_regB`・`oper_d1pos_lenPSeq_unified`
  ・`oper_d1pos_ctx_multiM`）、«6».«6.8-d1pos-le0»
  （`oper_d1pos_le0_start_to_any`）、推移 import の `*_68` 読み出し群
  （`length_oper_d1pos_68`・`entry_oper_d1pos_one_68`・`entry_oper_lt_last_68`
  ・`seg_getElem_68`・`getD_dropLast_68`・`last_anchor_coincide_shift_prefix_68`）
  と基盤（`entry_seg`/`length_seg`/`leR0_seg_adm`/`ancestor_basic_1`/
  `parent_exists_3`/`P_component_nonempty`/`entry_IncrFirstN_zero`/`_one`）
- 状態: ✅ 証明済（sorry 0、公開定理 2 本 ＋ `D1pos_*_holds` 2 本）
- Isabelle との差分メモ:
  - collapse（LOW = butlast の +shamt 写像）は Isabelle の
    `branch_butl`/`lowshift'`/`branch_collapse_concrete` 経路の代わりに
    `last_anchor_coincide_shift_prefix_68` の第 4 conjunct
    （`(P S).dropLast = ((P Sn).dropLast).map (IncrFirstN sh)`）から直接取得。
  - `le0` の周期転送（Isa `le0_prefix_row0_shift_rev` rtrancl 帰納）は
    値特徴付け（`ancestor_basic_1`＋行 0 一致＋`parent_exists_3`）で置換。
  - `le0_trans` は `leR0_trans_cp`（値特徴付け経由）で私的再証明。
-/

namespace PSS

/-! ## 私用補助（suffix `_cp`） -/

/-- `1 < (P S).length` なら `S ≠ []`（`P [] = [[]]` は長さ 1）。 -/
private theorem TPS_of_P_multi_cp (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

private theorem le0Aux_refl_cp (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_cp (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_cp]

/-- 行 0 先祖関係の推移律（値特徴付け `parent_exists_3` 経由の私的再証明。
Isabelle `le0_trans` 相当、使用箇所に合わせ `a ≤ b < c` の幾何を仮定）。 -/
private theorem leR0_trans_cp (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : a ≤ b) (hbc : b < c) (hc : c < Lng M)
    (h1 : leR M 0 a b = true) (h2 : leR M 0 b c = true) :
    leR M 0 a c = true := by
  apply parent_exists_3 M a c hM (by omega) hc
  intro j hj hjc
  rcases Nat.eq_or_lt_of_le hab with heq | hlt
  · subst heq
    exact ancestor_basic_1 M a j c hM hj hjc h2
  · by_cases hjb : j ≤ b
    · exact ancestor_basic_1 M a j b hM hj hjb h1
    · have hbj : b < j := by omega
      have hab' : entry M 0 a < entry M 0 b :=
        ancestor_basic_1 M a b b hM hlt (le_refl _) h1
      have hbj' : entry M 0 b < entry M 0 j :=
        ancestor_basic_1 M b j c hM hbj hjc h2
      omega

/-- 空でないリストの `dropLast ++ [最終要素]` 分解（`getD` 形）。 -/
private theorem split_last_cp {α : Type} (Q : List α) (d : α) (hQ : Q ≠ []) :
    Q = Q.dropLast ++ [Q.getD (Q.length - 1) d] := by
  have hpos : 0 < Q.length := List.length_pos_of_ne_nil hQ
  rw [getD_eq_getElem_idx Q d (by omega), ← List.getLast_eq_getElem hQ]
  exact (List.dropLast_concat_getLast hQ).symm

/-! ## verbatim `notbrleNp`（Isabelle 20322 の私的再証明）

PREFIX セル（`j₀' < Lng N - 1`）で参照切片 `Np = seg N j₀' (Lng N - 1)` の
¬brle を消費側の ¬brle から転送する。D1 は `tnc` から、D2 は背理法:
行 0 逐語一致（`oper_d1pos_row0_agree`）で `le0 Np → le0 Mp` を値特徴付けで
持ち上げ、TrEq（`oper_d1pos_notbrle_Br_align_regA` 第 1 conjunct）で幹を
そろえ、capped 側（`Lng N - 1 < j₁'`）は `oper_d1pos_le0_start_to_any`
（`k = 1`）の境界到達で右端まで延長して消費側の ¬le0 と矛盾させる。 -/
private theorem oper_d1pos_ctx_notbrleNp_verbatim_cp
    (N : PS) (n j0' j1' : ℕ)
    (hNT : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hj0plt : j0' < Lng N - 1)
    (hlt : j0' < j1')
    (hbge : Lng N - 1 ≤ j1')
    (hjM : j1' < Lng (oper N n))
    (htnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0')
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false)
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    ¬(TrMax (seg N j0' (Lng N - 1)) = Lng (seg N j0' (Lng N - 1)) - 1 ∨
      leR (seg N j0' (Lng N - 1)) 0 (TrMax (seg N j0' (Lng N - 1)) + 1)
        (Lng (seg N j0' (Lng N - 1)) - 1) = true) := by
  have hLngM := length_oper_d1pos_68 N n hL hzero hp hi1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hbnd : Lng N - 1 < Lng (oper N n) := by omega
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' :=
    length_seg _ _ _
  have hLNp : Lng (seg N j0' (Lng N - 1)) = (Lng N - 1) + 1 - j0' :=
    length_seg _ _ _
  have hMpT : TPS (seg (oper N n) j0' j1') := by
    have hpos : 0 < Lng (seg (oper N n) j0' j1') := by omega
    exact List.ne_nil_of_length_pos hpos
  have hNpT : TPS (seg N j0' (Lng N - 1)) := by
    have hpos : 0 < Lng (seg N j0' (Lng N - 1)) := by omega
    exact List.ne_nil_of_length_pos hpos
  have hTrEq : TrMax (seg (oper N n) j0' j1') =
      TrMax (seg N j0' (Lng N - 1)) :=
    (oper_d1pos_notbrle_Br_align_regA N n j0' (Lng N - 1) j0' j1' hL hzero hp
      hi1z hj0lt hn1 (le_refl _) hj0plt (by omega) rfl hlt hjM htnc hstop
      hnotbrle).1
  obtain ⟨_htrneM, hnotleM⟩ := not_or.mp hnotbrle
  intro hcon
  rcases hcon with hD1 | hD2
  · -- D1: `tnc` と `TrMax Np = Lng Np - 1` が矛盾
    omega
  · -- D2: `le0 Np` を `le0 Mp` に持ち上げて消費側 ¬le0 と矛盾
    have hagree : ∀ j, j ≤ Lng N - 1 - j0' →
        entry (seg (oper N n) j0' j1') 0 j =
          entry (seg N j0' (Lng N - 1)) 0 j := by
      intro j hj
      rw [entry_seg (oper N n) j0' j1' 0 j (by omega),
        entry_seg N j0' (Lng N - 1) 0 j (by omega)]
      exact oper_d1pos_row0_agree N n (j0' + j) hL hzero hp hi1z hj0lt hbnd
        (by omega)
    have htN1m : TrMax (seg N j0' (Lng N - 1)) + 1 ≤ Lng N - 1 - j0' := by
      omega
    have hmLMp : Lng N - 1 - j0' < Lng (seg (oper N n) j0' j1') := by omega
    have hleMpm : leR (seg (oper N n) j0' j1') 0
        (TrMax (seg N j0' (Lng N - 1)) + 1) (Lng N - 1 - j0') = true := by
      rcases Nat.eq_or_lt_of_le htN1m with heq | hlt2
      · rw [← heq]
        exact leR0_refl_cp _ _ (by omega)
      · apply parent_exists_3 _ _ _ hMpT hlt2 hmLMp
        intro j hj hjle
        have hgrow : entry (seg N j0' (Lng N - 1)) 0
            (TrMax (seg N j0' (Lng N - 1)) + 1) <
            entry (seg N j0' (Lng N - 1)) 0 j :=
          ancestor_basic_1 _ _ j _ hNpT hj (by omega) hD2
        rw [← hagree (TrMax (seg N j0' (Lng N - 1)) + 1) htN1m,
          ← hagree j hjle] at hgrow
        exact hgrow
    have hleMpm' : leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1 - j0') = true := by
      rw [hTrEq]
      exact hleMpm
    have hleFull : leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true := by
      rcases Nat.eq_or_lt_of_le hbge with hcap | hcapped
      · -- UNCAPPED: `Lng N - 1 = j1'`、右端が一致
        have hEq : Lng N - 1 - j0' = Lng (seg (oper N n) j0' j1') - 1 := by
          omega
        rw [← hEq]
        exact hleMpm'
      · -- CAPPED: `Lng N - 1 < j1'`、境界到達で延長
        have hn2 : 1 < n := by
          by_contra hcon2
          have hneq : n = 1 := by omega
          subst hneq
          rw [Nat.one_mul] at hLngM
          omega
        have hxge : parent N 1 (Lng N - 1) +
            1 * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤ j1' := by
          rw [Nat.one_mul]
          omega
        have hboundMn := oper_d1pos_le0_start_to_any N n 1 j1' hNT hL hzero
          hp hi1z hj0lt hn2 hxge hjM
        rw [show parent N 1 (Lng N - 1) +
            1 * (Lng N - 1 - parent N 1 (Lng N - 1)) = Lng N - 1 by
          rw [Nat.one_mul]; omega] at hboundMn
        have hmtrans : leR (seg (oper N n) j0' j1') 0 (Lng N - 1 - j0')
            (Lng (seg (oper N n) j0' j1') - 1) = true := by
          rw [leR0_seg_adm (oper N n) j0' j1' (Lng N - 1 - j0')
              (Lng (seg (oper N n) j0' j1') - 1) (by omega) hjM hmLMp
              (by omega),
            show j0' + (Lng N - 1 - j0') = Lng N - 1 by omega,
            show j0' + (Lng (seg (oper N n) j0' j1') - 1) = j1' by omega]
          exact hboundMn
        exact leR0_trans_cp _ _ _ _ hMpT (by omega) (by omega) (by omega)
          hleMpm' hmtrans
    exact hnotleM hleFull

/-! ## shamt=0 anchor 束のコア（抽象 `A` 版）

`A` を抽象化した LOW セル（`j₋₂ ≤ A < Lng N - 1`）の 6 conjunct 束。
公開定理は `A := j0' + TrMax (seg M j0' j1') + 1` で即時具体化する。 -/

private theorem low_anchor_core_cp
    (N : PS) (n A j1' : ℕ)
    (_hNT : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hAjm2 : parent N 1 (Lng N - 1) ≤ A)
    (hAltN : A < Lng N - 1)
    (hbge : Lng N - 1 ≤ j1')
    (hjM : j1' < Lng (oper N n))
    (hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (hmultiS : 1 < (P (seg (oper N n) A j1')).length)
    (hmultiSn : 1 < (P (seg N A (Lng N - 1))).length) :
    (seg (seg (oper N n) A j1') 0 (Lng (seg N A (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1))) ∧
    (entry (seg (oper N n) A j1') 0 (Lng (seg N A (Lng N - 1)) - 1) =
      entry (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1) + 0) ∧
    (entry (seg (oper N n) A j1') 1 (Lng (seg N A (Lng N - 1)) - 1) ≤
      entry (seg N A (Lng N - 1)) 1 (Lng (seg N A (Lng N - 1)) - 1)) ∧
    ((P (seg (oper N n) A j1')).length = (P (seg N A (Lng N - 1))).length) ∧
    ((IdxSum (P (seg (oper N n) A j1'))).getD
        ((P (seg (oper N n) A j1')).length - 1) 0 ≤
      Lng (seg N A (Lng N - 1)) - 1) ∧
    (Lng (seg N A (Lng N - 1)) - 1 ≤ Lng (seg (oper N n) A j1') - 1) := by
  have hLngM := length_oper_d1pos_68 N n hL hzero hp hi1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hbnd : Lng N - 1 < Lng (oper N n) := by omega
  have hLS : Lng (seg (oper N n) A j1') = j1' + 1 - A := length_seg _ _ _
  have hLSn : Lng (seg N A (Lng N - 1)) = (Lng N - 1) + 1 - A :=
    length_seg _ _ _
  have hST : TPS (seg (oper N n) A j1') := TPS_of_P_multi_cp _ hmultiS
  have hSnT : TPS (seg N A (Lng N - 1)) := TPS_of_P_multi_cp _ hmultiSn
  -- (shiftEqB) verbatim 窓 `[A, A+m-1] = [A, Lng N - 2]`（shamt = 0）
  have hshiftEq0 : seg (seg (oper N n) A j1') 0
      (Lng (seg N A (Lng N - 1)) - 1 - 1) =
      seg (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1) := by
    apply List.ext_getElem
    · simp only [length_seg]
    · intro k hk1 hk2
      have hk1' : k < Lng (seg N A (Lng N - 1)) - 1 - 1 + 1 - 0 := by
        simpa only [length_seg] using hk1
      have hAk : A + k < Lng N - 1 := by omega
      have hkS : k < Lng (seg (oper N n) A j1') := by omega
      have hkSn : k < Lng (seg N A (Lng N - 1)) := by omega
      rw [seg_getElem_68 _ 0 _ k hk1, seg_getElem_68 _ 0 _ k hk2]
      simp only [Nat.zero_add]
      rw [entry_seg (oper N n) A j1' 0 k hkS,
        entry_seg (oper N n) A j1' 1 k hkS,
        entry_seg N A (Lng N - 1) 0 k hkSn,
        entry_seg N A (Lng N - 1) 1 k hkSn,
        entry_oper_lt_last_68 N n 0 (A + k) hL hn1 (Or.inl rfl) hAk,
        entry_oper_lt_last_68 N n 1 (A + k) hL hn1 (Or.inr rfl) hAk]
  have hshiftEq : seg (seg (oper N n) A j1') 0
      (Lng (seg N A (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1)) :=
    hshiftEq0
  -- (boundEq0B) 境界添字 `m` は N 添字 `Lng N - 1` に写り、行 0 が一致
  have hmSn : Lng (seg N A (Lng N - 1)) - 1 < Lng (seg N A (Lng N - 1)) := by
    omega
  have hmS : Lng (seg N A (Lng N - 1)) - 1 < Lng (seg (oper N n) A j1') := by
    omega
  have hmAdd : A + (Lng (seg N A (Lng N - 1)) - 1) = Lng N - 1 := by omega
  have hb0 : entry (seg (oper N n) A j1') 0 (Lng (seg N A (Lng N - 1)) - 1) =
      entry (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1) + 0 := by
    rw [entry_seg (oper N n) A j1' 0 _ hmS,
      entry_seg N A (Lng N - 1) 0 _ hmSn, hmAdd,
      oper_d1pos_row0_agree N n (Lng N - 1) hL hzero hp hi1z hj0lt hbnd
        (le_refl _)]
    omega
  -- (boundEq1B) 行 1: `entry M 1 (Lng N - 1) = entry N 1 j₋₂ ≤ entry N 1 (Lng N - 1)`
  have hn2 : 1 < n := by
    by_contra hcon
    have hneq : n = 1 := by omega
    subst hneq
    rw [Nat.one_mul] at hLngM
    omega
  have he1M : entry (oper N n) 1 (Lng N - 1) =
      entry N 1 (parent N 1 (Lng N - 1)) := by
    have hh := entry_oper_d1pos_one_68 N n 1 0 hL hzero hp hi1z hn2 hw
    rw [show parent N 1 (Lng N - 1) +
        1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = Lng N - 1 by
      rw [Nat.one_mul]; omega] at hh
    rw [hh]
    simp only [Nat.add_zero]
  have hr1le : entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 (Lng N - 1) :=
    oper_d1pos_ctx_r1le N hp hi1z
  have hb1 : entry (seg (oper N n) A j1') 1 (Lng (seg N A (Lng N - 1)) - 1) ≤
      entry (seg N A (Lng N - 1)) 1 (Lng (seg N A (Lng N - 1)) - 1) := by
    rw [entry_seg (oper N n) A j1' 1 _ hmS,
      entry_seg N A (Lng N - 1) 1 _ hmSn, hmAdd, he1M]
    exact hr1le
  -- (mleSB)
  have hmleS : Lng (seg N A (Lng N - 1)) - 1 ≤
      Lng (seg (oper N n) A j1') - 1 := by omega
  -- (cleMB) regime-B anchor 上界
  have hcleM := oper_d1pos_clt_regB N A j1' n hL hzero hp hi1z hj0lt hn1
    hAjm2 hAltN hbge hjM hdpos hmultiS
  -- (lenPSeqB) 周期統一の成分数一致
  have hlenP : (P (seg (oper N n) A j1')).length =
      (P (seg N A (Lng N - 1))).length :=
    oper_d1pos_lenPSeq_unified (seg (oper N n) A j1') (seg N A (Lng N - 1)) 0
      hST hmultiS hSnT hmultiSn hmleS hcleM hshiftEq hb0
  exact ⟨hshiftEq, hb0, hb1, hlenP, hcleM, hmleS⟩

/-! ## 公開定理 1: `oper_d1pos_low_anchor_shamt0`（Isabelle 20904）

LOW regB/boundary セルの shamt = 0 anchor 束（shiftEqB/boundEq0B/boundEq1B/
lenPSeqB/cleMB/mleSB の 6 conjunct）。 -/

theorem oper_d1pos_low_anchor_shamt0
    (N M : PS) (n j0' j1' : ℕ)
    (hNT : TPS N) (_hmonoN : monoT N = true) (_hstd : STPS N)
    (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hNeq : M = oper N n)
    (hn1 : 1 ≤ n)
    (hj0plt : j0' < Lng N - 1)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (hbge : Lng N - 1 ≤ j1')
    (hAjm2 : parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1)
    (hAltN : j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1)
    (hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (hmultiM : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (_hle0M : leR M 0 j0' j1' = true)
    (hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (htnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0')
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false) :
    (seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
          (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1))) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) =
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + 0) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ≤
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)) ∧
    ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length) ∧
    ((IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ∧
    (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1) := by
  subst hNeq
  have hj0lt : parent N 1 (Lng N - 1) < Lng N - 1 :=
    oper_d1pos_ctx_j0lt N hp hi1z
  -- multiSn: verbatim notbrleNp → regA TrEq → `oper_d1pos_ctx_multiM`
  have hnotbrleNp := oper_d1pos_ctx_notbrleNp_verbatim_cp N n j0' j1' hNT hL
    hzero hp hi1z hj0lt hn1 hj0plt hlt hbge hjM htnc hstop hnotbrle
  have hTrEq : TrMax (seg (oper N n) j0' j1') =
      TrMax (seg N j0' (Lng N - 1)) :=
    (oper_d1pos_notbrle_Br_align_regA N n j0' (Lng N - 1) j0' j1' hL hzero hp
      hi1z hj0lt hn1 (le_refl _) hj0plt (by omega) rfl hlt hjM htnc hstop
      hnotbrle).1
  have hnpT : TPS (seg N j0' (Lng N - 1)) := by
    have hpos : 0 < Lng (seg N j0' (Lng N - 1)) := by
      rw [length_seg]
      omega
    exact List.ne_nil_of_length_pos hpos
  have hmultiSn : 1 < (P (seg N
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1))).length := by
    rw [hTrEq]
    exact oper_d1pos_ctx_multiM N j0' (Lng N - 1) hnpT hj0plt hnotbrleNp
  exact low_anchor_core_cp N n (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'
    hNT hL hzero hp hi1z hj0lt hn1 hAjm2 hAltN hbge hjM hdpos hmultiM
    hmultiSn

/-- Prop discharge: `D1pos_oper_d1pos_low_anchor_shamt0`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_low_anchor_shamt0_holds :
    D1pos_oper_d1pos_low_anchor_shamt0 := by
  intro N M n j0' j1' hNT hmonoN hstd hL hzero hp hi1z hNeq hn1 hj0plt hlt
    hjM hbge hAjm2 hAltN hdpos hmultiM hle0M hnotbrle htnc hstop
  exact oper_d1pos_low_anchor_shamt0 N M n j0' j1' hNT hmonoN hstd hL hzero
    hp hi1z hNeq hn1 hj0plt hlt hjM hbge hAjm2 hAltN hdpos hmultiM hle0M
    hnotbrle htnc hstop

/-! ## PERIODIC take-eq のコア（抽象 S/Sn 版）

anchor 一致・tail junction・collapse・組み立てを抽象 `S`/`Sn` で行う。
collapse は `last_anchor_coincide_shift_prefix_68` の第 4 conjunct から直接。 -/

private theorem periodic_core_cp
    (N Mp Np S Sn : PS) (j0red j1red shamt : ℕ)
    (hBrM : Br Mp = P S) (hBrN : Br Np = P Sn) (hBrNne : Br Np ≠ [])
    (hST : TPS S) (hSnT : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hmleS : Lng Sn - 1 ≤ Lng S - 1)
    (hcleM : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Sn - 1)
    (hlenP : (P S).length = (P Sn).length)
    (hshift : seg S 0 (Lng Sn - 1 - 1) =
      IncrFirstN shamt (seg Sn 0 (Lng Sn - 1 - 1)))
    (hb0 : entry S 0 (Lng Sn - 1) = entry Sn 0 (Lng Sn - 1) + shamt)
    (hb1 : entry S 1 (Lng Sn - 1) ≤ entry Sn 1 (Lng Sn - 1))
    (hNpdef : Np = seg N j0red j1red)
    (hltred : j0red < j1red) (hlered : j1red ≤ Lng N - 1)
    (hle0red : le0 N j0red j1red = true) :
    d1posAlignment_68 N Mp := by
  obtain ⟨_hceq, hF8end, hF9end, hLOWmap⟩ :=
    last_anchor_coincide_shift_prefix_68 S Sn shamt hST hSnT hmultiS hmultiSn
      hmleS hcleM hlenP hshift hb0 hb1
  obtain ⟨htail0, htail1⟩ := oper_d1pos_tail_junction S Sn shamt hST hmultiS
    hSnT hmultiSn hF8end hF9end
  refine ⟨j0red, j1red, shamt, ((P Sn).dropLast).map (IncrFirstN shamt),
    (P S).getD ((P S).length - 1) [], hltred, hlered, hle0red, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- `Br Mp = LOW ++ [TL]`（collapse）
    have hsplit := split_last_cp (P S) [] (P_nonempty S)
    rw [hLOWmap] at hsplit
    exact hBrM.trans hsplit
  · -- `Br (seg N j0red j1red) ≠ []`
    rw [← hNpdef]
    exact hBrNne
  · -- LOW 長
    rw [← hNpdef, hBrN]
    simp
  · -- LOW 成分ごとの +shamt / 行 1 恒等
    intro J hJ
    have hJlen : J < ((P Sn).dropLast).length := by
      simpa using hJ
    have hJP : J < (P Sn).length := by
      have hdl : ((P Sn).dropLast).length = (P Sn).length - 1 :=
        List.length_dropLast
      omega
    have hnode : 0 < Lng ((P Sn).getD J []) :=
      P_component_nonempty Sn J hSnT hJP
    have hgetD : (((P Sn).dropLast).map (IncrFirstN shamt)).getD J [] =
        IncrFirstN shamt ((P Sn).getD J []) := by
      rw [getD_eq_getElem_idx _ _ hJ]
      simp only [List.getElem_map]
      congr 1
      rw [← getD_eq_getElem_idx ((P Sn).dropLast) [] hJlen]
      exact getD_dropLast_68 (P Sn) [] J hJlen
    rw [← hNpdef, hBrN, hgetD]
    constructor
    · exact entry_IncrFirstN_zero shamt _ 0 hnode
    · exact entry_IncrFirstN_one shamt _ 0
  · -- tail 行 0（F8）
    rw [← hNpdef, hBrN]
    exact htail0
  · -- tail 行 1（F9）
    rw [← hNpdef, hBrN]
    exact htail1

/-! ## 公開定理 2: `oper_d1pos_notbrle_LOW_take_eq_periodic`（Isabelle 20584）

CELL-4（周期尾部 `j0' ≥ Lng N - 1`）の take-eq 主 brick。結論
`d1posAlignment_68 N (seg M j0' j1')` は Isabelle の存在文と逐語一致。 -/

theorem oper_d1pos_notbrle_LOW_take_eq_periodic
    (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ)
    (hNT : TPS N) (_hmonoN : monoT N = true) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hNeq : M = oper N n)
    (hn1 : 1 ≤ n)
    (_hM'T : TPS (seg M j0' j1'))
    (_hle0M : leR M 0 j0' j1' = true)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (_hbge : Lng N - 1 ≤ j1')
    (hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (hj0pge : Lng N - 1 ≤ j0')
    (hq0 : q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hs0 : s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hj0red : j0red = parent N 1 (Lng N - 1) + s0)
    (hj1red : j1red = min (j0red + (j1' - j0')) (Lng N - 1))
    (hshamt : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hmultiM : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (hmultiNp : 1 <
      (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length)
    (hle0Np : leR N 0 j0red j1red = true)
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (hshiftEqB : seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1) =
      IncrFirstN shamt
        (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
          (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)))
    (hboundEq0B : entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) =
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) +
        shamt)
    (hboundEq1B : entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) ≤
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1))
    (hlenPSeqB : (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length)
    (hcleMB : (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
    (hmleSB : Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1) :
    d1posAlignment_68 N (seg M j0' j1') := by
  subst hNeq
  -- 幾何: div/mod 分解と `q0 < n`
  have hLngM := length_oper_d1pos_68 N n hL hzero hp hi1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1) := by
    rw [hs0]
    exact Nat.mod_lt _ hw
  have hj0redlt : j0red < Lng N - 1 := by omega
  have hdm := Nat.div_add_mod (j0' - parent N 1 (Lng N - 1))
    (Lng N - 1 - parent N 1 (Lng N - 1))
  rw [← hq0, ← hs0, Nat.mul_comm] at hdm
  have hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 := by omega
  have hq0n : q0 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hj1redle : j1red ≤ Lng N - 1 := by omega
  have hj0j1red : j0red < j1red := by omega
  have hj1redspan : j1red ≤ j0red + (j1' - j0') := by omega
  -- Br 整列（shifted TrEq キーストーン）
  obtain ⟨_hTrEq, hBrM, hBrN, _hBrMne, hBrNne⟩ :=
    oper_d1pos_notbrle_Br_align N n q0 s0 j0red j1red j0' j1' shamt
      hNT hL hzero hp hi1z hj0lt hn1 hq0n hj0redlt hj0red hs0lt hj0'eq hshamt
      hj1redle hj0j1red hj1redspan hlt hjM htnc hstop hnotbrle
  -- S/Sn の T_PS 性
  have hST : TPS (seg (oper N n)
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
    TPS_of_P_multi_cp _ hmultiM
  have hSnT : TPS (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) :=
    TPS_of_P_multi_cp _ hmultiNp
  have hle0red : le0 N j0red j1red = true := by
    simpa [leR] using hle0Np
  exact periodic_core_cp N (seg (oper N n) j0' j1') (seg N j0red j1red)
    (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')
    (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)
    j0red j1red shamt hBrM hBrN hBrNne hST hSnT hmultiM hmultiNp
    hmleSB hcleMB hlenPSeqB hshiftEqB hboundEq0B hboundEq1B rfl
    hj0j1red hj1redle hle0red

/-- Prop discharge: `D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic`
（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic_holds :
    D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic := by
  intro N M n j0' j1' q0 s0 j0red j1red shamt hNT hmonoN hL hzero hp hi1z
    hNeq hn1 hM'T hle0M hlt hjM hbge hnotbrle hj0lt hdpos hj0pge hq0 hs0
    hj0red hj1red hshamt hmultiM hmultiNp hle0Np htnc hstop hshiftEqB
    hboundEq0B hboundEq1B hlenPSeqB hcleMB hmleSB
  exact oper_d1pos_notbrle_LOW_take_eq_periodic N M n j0' j1' q0 s0 j0red
    j1red shamt hNT hmonoN hL hzero hp hi1z hNeq hn1 hM'T hle0M hlt hjM hbge
    hnotbrle hj0lt hdpos hj0pge hq0 hs0 hj0red hj1red hshamt hmultiM
    hmultiNp hle0Np htnc hstop hshiftEqB hboundEq0B hboundEq1B hlenPSeqB
    hcleMB hmleSB

end PSS

#print axioms PSS.oper_d1pos_low_anchor_shamt0
#print axioms PSS.D1pos_oper_d1pos_low_anchor_shamt0_holds
#print axioms PSS.oper_d1pos_notbrle_LOW_take_eq_periodic
#print axioms PSS.D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic_holds
