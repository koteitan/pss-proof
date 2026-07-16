import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-base»
import «6».«6.8-d1pos-le0»
import «6».«6.8-d1pos-period»
import «6».«6.8-d1pos-notbrle»
import «6».«6.8-d1pos-anchor-regA»
import «6».«6.8-d1pos-anchor-regB»
import «5».«5.1-ancestor-basic»
import «5».«5.1-parent-exists»

/-!
# §6.8 d1pos CELL-1（regime A）＋ notbrleNp ctx brick 族

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域、¬brle 跨りスライスの regime A セルと、参照簡約切片
  `Np` への ¬brle 転送）
- Isabelle (isabelle/pss_mechanized.thy):
  `oper_d1pos_notbrle_LOW_take_eq_regA` (17737),
  `oper_d1pos_ctx_notbrleNp` (20172),
  `oper_d1pos_ctx_notbrleNp_verbatim` (20322)
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Prop 定義）,
  «6».«6.8-d1pos-notbrle»（`oper_d1pos_notbrle_Br_align_regA`）,
  «6».«6.8-d1pos-anchor-regA»（`oper_d1pos_branch_lowshift_regA` /
  `oper_d1pos_clt_regA` / `oper_d1pos_cNlt_of_Ajm2`）,
  «6».«6.8-d1pos-anchor-regB»（`oper_d1pos_anchor_coincide_regA2` /
  `oper_d1pos_row0_agree`）,
  «6».«6.8-d1pos-period»（`oper_d1pos_period_row0_unif`）,
  «6».«6.8-d1pos-le0»（`oper_d1pos_seg_le0_boundary` /
  `oper_d1pos_le0_start_to_any`）,
  «6».«6.8-standard-slice-Br-descending»（`TrMax_seg_oper_d1pos_eq_span_68` /
  `d1posAlignment_of_anchor_data_68` / `leR0_refl_68` ほか *_68 読み出し）,
  «5».«5.1-ancestor-basic»（`ancestor_basic_1`）,
  «5».«5.1-parent-exists»（`parent_exists_3`）
- 状態: ✅ 証明済（sorry 0）

Isabelle の `le0_prefix_row0_shift_rev`（rtrancl 帰納）は使わず、le0 の転送は
値特徴付け（`ancestor_basic_1` ＋ entry 一致 ＋ `parent_exists_3`）で構成する
（memo.md §4.5 の勝ち筋）。cross-scope private の複製:
`TrMax_seg_oper_d1pos_eq_regA_ca`（Isabelle `TrMax_seg_oper_d1pos_eq_regA`
15218、notbrle の private `_nb` と同一 statement）と
`TPS_of_P_multi_ca`。
-/

namespace PSS

/-! ## 私用補助 -/

/-- `1 < (P S).length` なら `S` は空列でない（cross-scope private 複製）。 -/
private theorem TPS_of_P_multi_ca (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

/-- REGIME A TrEq キーストーン（Isabelle `TrMax_seg_oper_d1pos_eq_regA` 15218、
notbrle の private `_nb` の複製）: `j0red = j0'`（シフト無し）で接頭辞
`[0, j1red-1-j0red]` は両側とも `N` を逐語読みするので、非対称接頭辞
キーストーンで幹が一致。 -/
private theorem TrMax_seg_oper_d1pos_eq_regA_ca
    (N : PS) (n j0red j1red j0' j1' : ℕ)
    (hL : 1 < Lng N)
    (hn1 : 1 ≤ n)
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hj1redspan : j1red ≤ j0red + (j1' - j0'))
    (hj0eqA : j0red = j0')
    (hj0j1' : j0' < j1')
    (_hj1lt : j1' < Lng (oper N n))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false) :
    TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) := by
  let Mp := seg (oper N n) j0' j1'
  let Np := seg N j0red j1red
  let c := j1red - 1 - j0red
  have hcd : c = j1red - 1 - j0red := rfl
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hLMp : Lng Mp = j1' + 1 - j0' := by simp [Mp]
  have hLNp : Lng Np = j1red + 1 - j0red := by simp [Np]
  have hcM : c < Lng Mp := by rw [hLMp]; omega
  have hcN : c < Lng Np := by rw [hLNp]; omega
  have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Np.getD s (0, 0) := by
    intro s hsc
    have hsM : s < Lng Mp := by omega
    have hsN : s < Lng Np := by omega
    have hidxlt' : j0' + s < Lng N - 1 := by omega
    rw [getD_eq_getElem_idx Mp (0, 0) hsM,
      getD_eq_getElem_idx Np (0, 0) hsN,
      seg_getElem_68 (oper N n) j0' j1' s hsM,
      seg_getElem_68 N j0red j1red s hsN,
      entry_oper_lt_last_68 N n 0 (j0' + s) hL hn1 (Or.inl rfl) hidxlt',
      entry_oper_lt_last_68 N n 1 (j0' + s) hL hn1 (Or.inr rfl) hidxlt',
      hj0eqA]
  exact TrMax_eq_of_prefix_agree_68 Mp Np c hMpT hNpT hagree hcM hcN
    htnc hstop

/-! ## CELL-1（regime A）: ¬brle LOW take-eq
Isabelle `oper_d1pos_notbrle_LOW_take_eq_regA` (pss_mechanized.thy:17737)。
(1) `oper_d1pos_notbrle_Br_align_regA`（TrEq ＋ 両 `Br = P (seg ..)` 再形成）
(2) `oper_d1pos_anchor_coincide_regA2`（`c = cN` / F8end / F9end）
(3) `oper_d1pos_clt_regA` / `oper_d1pos_cNlt_of_Ajm2`（アンカーは境界の内側）
    → `oper_d1pos_branch_lowshift_regA`（`shamt = 0` の LOW 窓逐語一致）
(4) `d1posAlignment_of_anchor_data_68` で存在文に梱包。 -/

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_regA` (pss_mechanized.thy:17737)。 -/
theorem oper_d1pos_notbrle_LOW_take_eq_regA
    (N M : PS) (n j0' j1' : ℕ)
    (_hNT : TPS N) (_hmonoN : monoT N = true) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hMeq : M = oper N n)
    (hn1 : 1 ≤ n)
    (_hMpT : TPS (seg M j0' j1'))
    (_hle0M : leR M 0 j0' j1' = true)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (hbge : Lng N - 1 ≤ j1')
    (hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (hAreg : j0' + TrMax (seg M j0' j1') + 1 < parent N 1 (Lng N - 1))
    (hmultiM : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (hmultiNp :
      1 < (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length)
    (hle0Np : leR N 0 j0' (Lng N - 1) = true)
    (htnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0')
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false) :
    d1posAlignment_68 N (seg M j0' j1') := by
  subst hMeq
  -- 幾何: regime A では `j0' < j₋₂ < Lng N - 1`
  have hj0red : j0' < Lng N - 1 := by omega
  have hspan : Lng N - 1 ≤ j0' + (j1' - j0') := by omega
  -- (1) Br align（`j0red = j0'`、`j1red = Lng N - 1`）
  obtain ⟨hTrEq, hBrM, hBrN, _hBrMne, _hBrNne⟩ :=
    oper_d1pos_notbrle_Br_align_regA N n j0' (Lng N - 1) j0' j1' hL hzero hp
      hi1z hj0lt hn1 (le_refl _) hj0red hspan rfl hlt hjM htnc hstop hnotbrle
  -- `Br Np` の再形成を M 側 TrMax（= A の定義）に書き換え
  rw [← hTrEq] at hBrN
  -- 以降 `A = j0' + TrMax M' + 1` を畳む
  set A := j0' + TrMax (seg (oper N n) j0' j1') + 1 with hA
  -- (2) anchor 一致（regime A: `A < j₋₂`）
  obtain ⟨hceq, hend0, hend1⟩ :=
    oper_d1pos_anchor_coincide_regA2 N A j1' n hL hzero hp hi1z hj0lt hn1
      hAreg hbge hjM hdpos hmultiM hmultiNp
  -- (3) アンカーは境界の内側（c < m, cN < m）
  have hclt := oper_d1pos_clt_regA N A j1' n hL hzero hp hi1z hj0lt hn1
    hAreg hbge hjM hdpos hmultiM
  have hcNlt := oper_d1pos_cNlt_of_Ajm2 N A hL (by omega) hmultiNp
    (Nat.le_of_lt hAreg) hj0lt hdpos
  have hLSn : Lng (seg N A (Lng N - 1)) = Lng N - 1 + 1 - A :=
    length_seg _ _ _
  -- LOW 窓の逐語一致（shamt = 0）
  have hshift := oper_d1pos_branch_lowshift_regA N n A A
    ((IdxSum (P (seg (oper N n) A j1'))).getD
      ((P (seg (oper N n) A j1')).length - 1) 0)
    ((IdxSum (P (seg N A (Lng N - 1)))).getD
      ((P (seg N A (Lng N - 1))).length - 1) 0)
    j1' (Lng N - 1) hL hzero hp hi1z hj0lt hn1 rfl hceq
    (by omega) (by omega) (by omega) (by omega) (by omega)
  -- (4) 梱包
  have hST : TPS (seg (oper N n) A j1') := TPS_of_P_multi_ca _ hmultiM
  have hSnT : TPS (seg N A (Lng N - 1)) := TPS_of_P_multi_ca _ hmultiNp
  have hle : le0 N j0' (Lng N - 1) = true := by simpa [leR] using hle0Np
  have hend0' : entry (seg (oper N n) A j1') 0
      ((IdxSum (P (seg (oper N n) A j1'))).getD
        ((P (seg (oper N n) A j1')).length - 1) 0) =
    entry (seg N A (Lng N - 1)) 0
      ((IdxSum (P (seg N A (Lng N - 1)))).getD
        ((P (seg N A (Lng N - 1))).length - 1) 0) + 0 := by omega
  exact d1posAlignment_of_anchor_data_68 N (seg (oper N n) j0' j1')
    (seg (oper N n) A j1') (seg N A (Lng N - 1)) j0' (Lng N - 1) 0
    hj0red (le_refl _) hle hBrM hBrN hST hSnT hmultiM hmultiNp
    hshift hend0' hend1

/-- Prop discharge: `D1pos_oper_d1pos_notbrle_LOW_take_eq_regA`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_notbrle_LOW_take_eq_regA_holds :
    D1pos_oper_d1pos_notbrle_LOW_take_eq_regA := by
  intro N M n j0' j1' hNT hmonoN hL hzero hp hi1z hMeq hn1 hMpT hle0M hlt
    hjM hbge hnotbrle hj0lt hdpos hAreg hmultiM hmultiNp hle0Np htnc hstop
  exact oper_d1pos_notbrle_LOW_take_eq_regA N M n j0' j1' hNT hmonoN hL hzero
    hp hi1z hMeq hn1 hMpT hle0M hlt hjM hbge hnotbrle hj0lt hdpos hAreg
    hmultiM hmultiNp hle0Np htnc hstop

/-! ## ctx brick: notbrleNp（周期セル用）
Isabelle `oper_d1pos_ctx_notbrleNp` (pss_mechanized.thy:20172)。
D1 は `tnc` から直接。D2 は背理法: TrEq（span キーストーン）＋ `+shamt`
行 0 一様一致（`oper_d1pos_period_row0_unif`）で `le0 Np` の値鎖を `M'` 側に
移送し、CAPPED のときは境界到達（`oper_d1pos_seg_le0_boundary`）で
`Lng M' - 1` まで延長、`parent_exists_3` で `le0 M'` を再構成して
¬brle conj-2 と矛盾。 -/

/-- Isabelle `oper_d1pos_ctx_notbrleNp` (pss_mechanized.thy:20172)。 -/
theorem oper_d1pos_ctx_notbrleNp
    (N M : PS) (n q0 s0 j0red j1red j0' j1' shamt : ℕ)
    (hNT : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hMeq : M = oper N n)
    (hn1 : 1 ≤ n) (hq0n : q0 < n)
    (hs0w : j0red < Lng N - 1)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0reds : j0red = parent N 1 (Lng N - 1) + s0)
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1reddef : j1red = min (j0red + (j1' - j0')) (Lng N - 1))
    (hj0j1red : j0red < j1red)
    (hj0j1' : j0' < j1')
    (hjM : j1' < Lng M)
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true)) :
    ¬(TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1 ∨
      leR (seg N j0red j1red) 0 (TrMax (seg N j0red j1red) + 1)
        (Lng (seg N j0red j1red) - 1) = true) := by
  subst hMeq
  intro hbrleNp
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red := length_seg _ _ _
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' := length_seg _ _ _
  have hj1redle : j1red ≤ Lng N - 1 := by omega
  have hj1redspan : j1red ≤ j0red + (j1' - j0') := by omega
  rcases hbrleNp with hD1 | hD2
  · -- D1: `tnc` から `TrMax Np < Lng Np - 1`
    omega
  · -- D2: 背理法。まず TrEq（CAPPED 一般 span キーストーン）
    have hTrEq : TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) :=
      TrMax_seg_oper_d1pos_eq_span_68 N n q0 s0 j0red j1red j0' j1' shamt
        hNT hL hzero hp hi1z hq0n hs0w hj0reds hs0lt hj0'eq hshamt hj1redle
        hj0j1red hj1redspan hj0j1' hjM htnc hstop
    have hMpT : TPS (seg (oper N n) j0' j1') := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng (seg (oper N n) j0' j1')
      omega
    have hNpT : TPS (seg N j0red j1red) := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng (seg N j0red j1red)
      omega
    -- `+shamt` 行 0 一様一致（両端点込み、切片座標）
    have hagree : ∀ j, j ≤ j1red - j0red →
        entry (seg (oper N n) j0' j1') 0 j =
          entry (seg N j0red j1red) 0 j + shamt := by
      intro j hj
      rw [entry_seg (oper N n) j0' j1' 0 j (by omega),
        entry_seg N j0red j1red 0 j (by omega)]
      exact oper_d1pos_period_row0_unif N n q0 s0 j0red j0' shamt j1red j
        hL hzero hp hi1z hj0lt hq0n hs0lt hj0reds hj0'eq hshamt hj1redle
        (Nat.le_of_lt hj0j1red) (by omega) hj
    have htN1m : TrMax (seg N j0red j1red) + 1 ≤ j1red - j0red := by omega
    -- `le0 Np` の値鎖を `M'` 側に移送（接頭辞 [0, m]）
    have hchainM : ∀ x, TrMax (seg N j0red j1red) + 1 < x →
        x ≤ j1red - j0red →
        entry (seg (oper N n) j0' j1') 0 (TrMax (seg N j0red j1red) + 1) <
          entry (seg (oper N n) j0' j1') 0 x := by
      intro x hx1 hx2
      have hNx := ancestor_basic_1 (seg N j0red j1red)
        (TrMax (seg N j0red j1red) + 1) x (Lng (seg N j0red j1red) - 1)
        hNpT hx1 (by omega) hD2
      have h1 := hagree (TrMax (seg N j0red j1red) + 1) htN1m
      have h2 := hagree x hx2
      omega
    -- `Lng M' - 1` まで延長して `le0 M'` を再構成
    have hfull : leR (seg (oper N n) j0' j1') 0
        (TrMax (seg N j0red j1red) + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true := by
      by_cases hdeg : TrMax (seg N j0red j1red) + 1 =
          Lng (seg (oper N n) j0' j1') - 1
      · rw [hdeg]
        exact leR0_refl_68 _ _ (by omega)
      · apply parent_exists_3 _ _ _ hMpT (by omega) (by omega)
        intro x hx1 hx2
        by_cases hxm : x ≤ j1red - j0red
        · exact hchainM x hx1 hxm
        · -- CAPPED: `j1red = Lng N - 1`、境界到達で尾部を跨ぐ
          have hspanlt : j1red < j0red + (j1' - j0') := by omega
          have hcap : j1red = Lng N - 1 := by omega
          have hbound := oper_d1pos_seg_le0_boundary N n q0 j0red j1red s0
            j0' j1' hNT hL hzero hp hi1z hj0lt hn1 hq0n hj0reds hs0lt
            hj0'eq hcap hspanlt hj0j1' hjM
          rw [show j1red - 1 - j0red + 1 = j1red - j0red from by omega]
            at hbound
          have hMx := ancestor_basic_1 (seg (oper N n) j0' j1')
            (j1red - j0red) x (Lng (seg (oper N n) j0' j1') - 1) hMpT
            (by omega) hx2 hbound
          by_cases htm : TrMax (seg N j0red j1red) + 1 = j1red - j0red
          · rw [htm]
            exact hMx
          · have h1 := hchainM (j1red - j0red) (by omega) (le_refl _)
            omega
    exact hnotbrle (Or.inr (by rw [hTrEq]; exact hfull))

/-- Prop discharge: `D1pos_oper_d1pos_ctx_notbrleNp`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_ctx_notbrleNp_holds :
    D1pos_oper_d1pos_ctx_notbrleNp := by
  intro N M n q0 s0 j0red j1red j0' j1' shamt hNT hL hzero hp hi1z hj0lt
    hMeq hn1 hq0n hs0w hs0lt hj0reds hj0'eq hshamt hj1reddef hj0j1red
    hj0j1' hjM htnc hstop hnotbrle
  exact oper_d1pos_ctx_notbrleNp N M n q0 s0 j0red j1red j0' j1' shamt hNT
    hL hzero hp hi1z hj0lt hMeq hn1 hq0n hs0w hs0lt hj0reds hj0'eq hshamt
    hj1reddef hj0j1red hj0j1' hjM htnc hstop hnotbrle

/-! ## ctx brick: notbrleNp VERBATIM（regA / boundary セル用）
Isabelle `oper_d1pos_ctx_notbrleNp_verbatim` (pss_mechanized.thy:20322)。
PREFIX セル（`j0red = j0'`、`shamt = 0`、`j1red = Lng N - 1`）のミラー。
D1 は `tnc` から。D2 は SHAMT-ZERO 行 0 一致（`oper_d1pos_row0_agree`）＋
regA TrEq キーストーン、CAPPED（`Lng N - 1 < j1'`）は verbatim 周期境界到達
（`oper_d1pos_le0_start_to_any`、`k = 1`）で延長。 -/

/-- Isabelle `oper_d1pos_ctx_notbrleNp_verbatim` (pss_mechanized.thy:20322)。 -/
theorem oper_d1pos_ctx_notbrleNp_verbatim
    (N M : PS) (n j0' j1' : ℕ)
    (hNT : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hMeq : M = oper N n)
    (hn1 : 1 ≤ n)
    (hj0plt : j0' < Lng N - 1)
    (hj0j1' : j0' < j1')
    (hbge : Lng N - 1 ≤ j1')
    (hjM : j1' < Lng M)
    (htnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0')
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false)
    (hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true)) :
    ¬(TrMax (seg N j0' (Lng N - 1)) = Lng (seg N j0' (Lng N - 1)) - 1 ∨
      leR (seg N j0' (Lng N - 1)) 0 (TrMax (seg N j0' (Lng N - 1)) + 1)
        (Lng (seg N j0' (Lng N - 1)) - 1) = true) := by
  subst hMeq
  intro hbrleNp
  have hLNp : Lng (seg N j0' (Lng N - 1)) = Lng N - 1 + 1 - j0' :=
    length_seg _ _ _
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' := length_seg _ _ _
  rcases hbrleNp with hD1 | hD2
  · -- D1: `tnc` から `TrMax Np < Lng Np - 1`
    omega
  · -- D2: 背理法。TrEq（regA / verbatim キーストーン、`j0red = j0'`）
    have hTrEq : TrMax (seg (oper N n) j0' j1') =
        TrMax (seg N j0' (Lng N - 1)) :=
      TrMax_seg_oper_d1pos_eq_regA_ca N n j0' (Lng N - 1) j0' j1' hL hn1
        (le_refl _) hj0plt (by omega) rfl hj0j1' hjM htnc hstop
    have hMpT : TPS (seg (oper N n) j0' j1') := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng (seg (oper N n) j0' j1')
      omega
    have hNpT : TPS (seg N j0' (Lng N - 1)) := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng (seg N j0' (Lng N - 1))
      omega
    have hbnd : Lng N - 1 < Lng (oper N n) := by omega
    -- SHAMT-ZERO 行 0 一致（切片座標、両端点込み）
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
    -- `le0 Np` の値鎖を `M'` 側に移送（接頭辞 [0, m]）
    have hchainM : ∀ x, TrMax (seg N j0' (Lng N - 1)) + 1 < x →
        x ≤ Lng N - 1 - j0' →
        entry (seg (oper N n) j0' j1') 0
            (TrMax (seg N j0' (Lng N - 1)) + 1) <
          entry (seg (oper N n) j0' j1') 0 x := by
      intro x hx1 hx2
      have hNx := ancestor_basic_1 (seg N j0' (Lng N - 1))
        (TrMax (seg N j0' (Lng N - 1)) + 1) x
        (Lng (seg N j0' (Lng N - 1)) - 1) hNpT hx1 (by omega) hD2
      have h1 := hagree (TrMax (seg N j0' (Lng N - 1)) + 1) htN1m
      have h2 := hagree x hx2
      omega
    -- `Lng M' - 1` まで延長して `le0 M'` を再構成
    have hfull : leR (seg (oper N n) j0' j1') 0
        (TrMax (seg N j0' (Lng N - 1)) + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true := by
      by_cases hdeg : TrMax (seg N j0' (Lng N - 1)) + 1 =
          Lng (seg (oper N n) j0' j1') - 1
      · rw [hdeg]
        exact leR0_refl_68 _ _ (by omega)
      · apply parent_exists_3 _ _ _ hMpT (by omega) (by omega)
        intro x hx1 hx2
        by_cases hxm : x ≤ Lng N - 1 - j0'
        · exact hchainM x hx1 hxm
        · -- CAPPED: `Lng N - 1 < j1'`、verbatim 周期境界到達（k = 1）
          have hcapN : Lng N - 1 < j1' := by omega
          have hLngM := length_oper_d1pos_68 N n hL hzero hp hi1z
          have hn2 : 1 < n := by
            by_contra hcon
            have hn1' : n = 1 := by omega
            subst hn1'
            omega
          have hstart := oper_d1pos_le0_start_to_any N n 1 j1' hNT hL hzero
            hp hi1z hj0lt hn2 (by omega) hjM
          rw [show parent N 1 (Lng N - 1) +
              1 * (Lng N - 1 - parent N 1 (Lng N - 1)) = Lng N - 1
            from by omega] at hstart
          have hMnT : TPS (oper N n) := by
            apply List.ne_nil_of_length_pos
            show 0 < Lng (oper N n)
            omega
          have hMx : entry (seg (oper N n) j0' j1') 0 (Lng N - 1 - j0') <
              entry (seg (oper N n) j0' j1') 0 x := by
            rw [entry_seg (oper N n) j0' j1' 0 (Lng N - 1 - j0') (by omega),
              entry_seg (oper N n) j0' j1' 0 x (by omega),
              show j0' + (Lng N - 1 - j0') = Lng N - 1 from by omega]
            exact ancestor_basic_1 (oper N n) (Lng N - 1) (j0' + x) j1'
              hMnT (by omega) (by omega) hstart
          by_cases htm : TrMax (seg N j0' (Lng N - 1)) + 1 =
              Lng N - 1 - j0'
          · rw [htm]
            exact hMx
          · have h1 := hchainM (Lng N - 1 - j0') (by omega) (le_refl _)
            omega
    exact hnotbrle (Or.inr (by rw [hTrEq]; exact hfull))

/-- Prop discharge: `D1pos_oper_d1pos_ctx_notbrleNp_verbatim`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_ctx_notbrleNp_verbatim_holds :
    D1pos_oper_d1pos_ctx_notbrleNp_verbatim := by
  intro N M n j0' j1' hNT hL hzero hp hi1z hj0lt hMeq hn1 hj0plt hj0j1'
    hbge hjM htnc hstop hnotbrle
  exact oper_d1pos_ctx_notbrleNp_verbatim N M n j0' j1' hNT hL hzero hp
    hi1z hj0lt hMeq hn1 hj0plt hj0j1' hbge hjM htnc hstop hnotbrle

end PSS

#print axioms PSS.oper_d1pos_notbrle_LOW_take_eq_regA
#print axioms PSS.D1pos_oper_d1pos_notbrle_LOW_take_eq_regA_holds
#print axioms PSS.oper_d1pos_ctx_notbrleNp
#print axioms PSS.D1pos_oper_d1pos_ctx_notbrleNp_holds
#print axioms PSS.oper_d1pos_ctx_notbrleNp_verbatim
#print axioms PSS.D1pos_oper_d1pos_ctx_notbrleNp_verbatim_holds
