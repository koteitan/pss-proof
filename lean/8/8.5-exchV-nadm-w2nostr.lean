import «8».«8.5-exchV-nadm-atomics»
import «8».«8.2-condV-VE-close»
import «8».«8.2-condV-VE-wnx»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.4-rightmost-nonadm-ancestor»
import «8».«8.2-subexpr-component-Pred»
import «8».«8.7-otpred-brickC0»
import «8».«8.1-diagSeq-Trans»
import «7».«7.4-Mark-Trans-repr»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.5-Red-Pred-commute»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.5 ExchV 非許容枝 `NadmW2nostr`（no-straddle body transfer）の証明

## 目的

«8».«8.5-exchV-nadm-atomics» が据え置いた深い残差 `NadmW2nostr` を無条件に閉じる
（house pattern: `theorem nadmW2nostr_holds : NadmW2nostr`）。

`NadmW2nostr` は、非許容前線 `[j₋₁, j₀]`（`j₋₁ = transJm1 M = Adm M (transJ0 M)`,
`j₀ = transJ0 M`）を跨いでも `Trans` 本体（`bpHeadT`）が `c ∈ {Lng M - 1, Lng M - 2}`
で一定であること:

  `bpHeadT (Trans (seg M j₀ c)) = bpHeadT (Trans (seg M j₋₁ c))`.

## 原文 / Isabelle 対応

Isabelle blueprint（`isabelle/layerB/pss_wip.thy`）:

* `wnx_W2nostr_c1` (81279) → 本ファイル `nadmW2nostr_holds` の `c = Lng M - 1` 枝。
* `wnx_W2nostr_c2` (81304) → 同 `c = Lng M - 2` 枝（幹/枝の二分岐）。
* `wnx_setup` (81008) → 私的 `nadm_setup_w2`（«8».«8.5-exchV-nadm-atomics» の private
  `nadm_setup_na` を逐語再構成。private は module 跨ぎ不可）。
* `wnx_transfer_of_reg` (80867) → 私的 `transfer_of_reg_w2`
  （`wnx_seg_transport_W1/W2`（«8».«8.2-condV-VE-wnx»）＋ VE 本体 `vcx_VE_all`
  （«8».«8.2-condV-VE-close»）の合成）。
* `wnx_reg_c1` (81070) → 私的 `reg_c1_w2`（体制確立の crux。DIAG は条件(V)の係数算術
  で確立）。`m_8_4_rightmost_nonadm_ancestor` = `rightmost_nonadm_ancestor`
  （«8».«8.4-rightmost-nonadm-ancestor»）＋ `m_8_2_standard_slice_Red_strongmono`
  = `standard_slice_Red_strongmono`（`DTPS`）＋ `wnx_run_entries`
  （«8».«8.7-otpred-brickC0»）を使う。
* `wnx_trunk_diagSeq` (80890) / `wnx_trunk_transfer` (80956) → 私的 `trunk_transfer_w2`
  （`baseU_alltrunk_diag_entry`（«8».«8.2-subexpr-component-Pred»）で簡約純幹＝`diagSeq`
  を復元し `diagSeq_Trans`（«8».«8.1-diagSeq-Trans»）で二段塔化）。
* `vjx_RPj1eq` (74726) → `rpj1eq_vc`（«8».«8.2-condV-VE-close»、`RPj1eqResidual` を無条件で
  閉じる。c2 枝分岐の体制遺伝）。
* `s84c2_seg_butlast` + `a1_Red_funpow_IncrFirst` による `R2eq` は Lean では
  `Pred_Red_terminal_slice`（«7».«7.4-Mark-Trans-repr»）＋ `TrMax_Pred_nontrunk`
  （«6».«6.5-Red-Pred-commute»）で迂回する。

## 依存（すべて committed 緑, main 19dc5fd）

`NadmW2nostr`（«8».«8.5-exchV-nadm-atomics»）,
`vcx_VE_all`/`rpj1eq_vc`（«8».«8.2-condV-VE-close»）,
`wnx_seg_transport_W1`/`wnx_seg_transport_W2`（«8».«8.2-condV-VE-wnx»）,
`standard_slice_Red_strongmono`/`DTPS_iff`/`DTPS_TPS`（«8».«8.2-standard-slice-Red-strongmono»）,
`rightmost_nonadm_ancestor`（«8».«8.4-rightmost-nonadm-ancestor»）,
`baseU_alltrunk_diag_entry`（«8».«8.2-subexpr-component-Pred»）,
`wnx_run_entries`（«8».«8.7-otpred-brickC0»）,
`diagSeq_Trans`（«8».«8.1-diagSeq-Trans»）,
`Pred_Red_terminal_slice`（«7».«7.4-Mark-Trans-repr»）,
`ancestor_slice_Red_IncrFirst`（«6».«6.6-ancestor-slice-Red-IncrFirst»）,
`TrMax_Pred_nontrunk`（«6».«6.5-Red-Pred-commute»）,
`entry_diagSeq_68`/`leR0_refl_68`（«6».«6.8-standard-slice-Br-descending»）,
`Lng_Red_invariance`/`RedCondA_apply`/`entry_IncrFirstN_zero`/`entry_IncrFirstN_one`
（§6.5）, `RTPS_condAB`/`RTPS_mono_head_eq`（§6.6）, `entry_seg`（§6.2）,
`Trans_Red`（§7.3）.

## 状態

GREEN（sorry 0, axioms = [propext, Classical.choice, Quot.sound]）。
`NadmW2nostr` を無条件に discharge。これにより «8».«8.5-exchV-nadm-atomics» の
`ExchVMNadmAtomicPackage` 残差束は `{Rightmost84ReplaceCorrected, NadmC2L1}` の 2 本へ縮む。

## private 接尾辞: `_w2`
-/

namespace PSS

/-! ## 私的補助（suffix `_w2`） -/

/-- `le0`（`leR _ 0 _`）の推移律。«8».«8.5-exchV-nadm-atomics» の private
`le0_trans_na` と同一骨格（`parent_exists_3` + `ancestor_basic_1`）。 -/
private theorem le0_trans_w2 (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hbc : leR M 0 b c = true)
    (halt : a < b) (hblt : b < c) (hcL : c < Lng M) :
    leR M 0 a c = true := by
  apply parent_exists_3 M a c hM (by omega) hcL
  intro j haj hjc
  by_cases hjb : j ≤ b
  · exact ancestor_basic_1 M a j b hM haj hjb hab
  · have h1 : entry M 0 a < entry M 0 b :=
      ancestor_basic_1 M a b b hM halt le_rfl hab
    have h2 : entry M 0 b < entry M 0 j :=
      ancestor_basic_1 M b j c hM (by omega) hjc hbc
    omega

/-- Isabelle `wnx_setup`（pss_wip.thy:81008）の到達性束。«8».«8.5-exchV-nadm-atomics»
の private `nadm_setup_na` を逐語再構成（private は module 跨ぎ不可）。 -/
private theorem nadm_setup_w2 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hnadm : adm M (transJ0 M) = false) :
    transJm1 M < transJ0 M ∧
      transJ0 M + 1 < Lng M - 1 ∧
      leR M 0 (transJm1 M) (Lng M - 1) = true ∧
      leR M 0 (transJ0 M) (Lng M - 1) = true ∧
      leR M 0 (transJ0 M) (Lng M - 2) = true ∧
      leR M 0 (transJm1 M) (Lng M - 2) = true ∧
      nextR M 0 (transJ0 M) (Lng M - 1) = true := by
  have hM : TPS M := STPS_TPS M hST
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hjm1lt : transJm1 M < transJ0 M := by
    have hle : transJm1 M ≤ transJ0 M := Adm_le M (transJ0 M)
    have hadm : adm M (transJm1 M) = true := Adm_adm M (transJ0 M)
    rcases Nat.lt_or_ge (transJm1 M) (transJ0 M) with h | h
    · exact h
    · exfalso
      have heq : transJm1 M = transJ0 M := by omega
      rw [heq, hnadm] at hadm
      exact Bool.noConfusion hadm
  have hle1a : leR M 1 (transJm1 M) (transJ0 M) = true :=
    adm_row1_ancestry M (transJ0 M) hM (by omega)
  have hle0a : leR M 0 (transJm1 M) (transJ0 M) = true :=
    row1_implies_row0 M (transJm1 M) (transJ0 M) hM hle1a
  have hle0c1 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M (transJ0 M) (Lng M - 1) hnextM
  have hle0c2 : leR M 0 (transJ0 M) (Lng M - 2) = true := by
    have hraw := parent_block_le0_68 M (transJ0 M) (Lng M - 1)
      ((Lng M - 2) - transJ0 M) hM hnextM (by omega)
    have hidx : transJ0 M + ((Lng M - 2) - transJ0 M) = Lng M - 2 := by omega
    rw [hidx] at hraw
    simpa [leR] using hraw
  refine ⟨hjm1lt, hrng, ?_, hle0c1, hle0c2, ?_, hnextM⟩
  · exact le0_trans_w2 M (transJm1 M) (transJ0 M) (Lng M - 1) hM hle0a hle0c1
      hjm1lt (by omega) (by omega)
  · exact le0_trans_w2 M (transJm1 M) (transJ0 M) (Lng M - 2) hM hle0a hle0c2
      hjm1lt (by omega) (by omega)

/-- Isabelle `wnx_reg_c1`（pss_wip.thy:81070）: 非許容前線 `[j₋₁, j₀]` の簡約祖先切片
`R = Red (seg M j₋₁ (Lng M - 1))` が offset `d = j₀ - j₋₁` で §8.2 体制 `VEReg d R` に入り、
最終枝は末尾単項（`VEj1p R = Lng R - 1`）で `R` は純幹でない（`TrMax R < Lng R - 1`）。

DIAG（体制の対角条件）は条件(V)の係数算術で確立する:
`R` の最終列が対角（`entry R 0 (Lng R - 1) = entry R 1 (Lng R - 1)`）であることを、
非許容 run の一次性（`wnx_run_entries`）と条件(V)の係数関係、および `IncrFirstN` シフト
（`ancestor_slice_Red_IncrFirst`）から組み立てる。 -/
private theorem reg_c1_w2 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hnadm : adm M (transJ0 M) = false) :
    VEReg (transJ0 M - transJm1 M) (Red (seg M (transJm1 M) (Lng M - 1))) ∧
      VEj1p (Red (seg M (transJm1 M) (Lng M - 1)))
          = Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 ∧
      TrMax (Red (seg M (transJm1 M) (Lng M - 1)))
          < Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hAdmEq : Adm M (transJ0 M) = transJm1 M := rfl
  have htj0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  -- setup（`wnx_setup`）
  obtain ⟨hjm1lt, hrng, hleab, hle0c1, _hle0c2, _hleabc2, hnxt0⟩ :=
    nadm_setup_w2 M hST hmono hcond hnadm
  have hL : 1 < Lng M := by omega
  have hj1lt : Lng M - 1 < Lng M := by omega
  have hjm1j1 : transJm1 M < Lng M - 1 := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  -- `notnx1`: 最終列の行 1 隣接辺は存在しない（親一意性）
  have notnx1 : nextR M 1 (Lng M - 1 - 1) (Lng M - 1) = false := by
    cases hb : nextR M 1 (Lng M - 1 - 1) (Lng M - 1) with
    | false => rfl
    | true =>
        exfalso
        have hn1 : nextrel1 M (Lng M - 1 - 1) (Lng M - 1) = true := by
          simpa [nextR] using hb
        have hle0x : le0 M (Lng M - 1 - 1) (Lng M - 1) = true := by
          have hh := hn1
          simp only [nextrel1, Bool.and_eq_true] at hh
          exact hh.1.2
        have hsucc : Lng M - 1 - 1 + 1 = Lng M - 1 := by omega
        have hle0adj : le0 M (Lng M - 1 - 1) (Lng M - 1 - 1 + 1) = true := by
          rw [hsucc]; exact hle0x
        have hnr0 := le0_adjacent M (Lng M - 1 - 1) hle0adj
        have hnx0 : nextR M 0 (Lng M - 1 - 1) (Lng M - 1) = true := by
          have h := hnr0
          rw [hsucc] at h
          simpa [nextR] using h
        have heqp : Lng M - 1 - 1 = transJ0 M :=
          row0_parent_unique M (Lng M - 1 - 1) (transJ0 M) (Lng M - 1) hnx0 hnxt0
        omega
  -- 右端非許容直系先祖（`m_8_4_rightmost_nonadm_ancestor`）
  have hleRefl : leR M 0 (Lng M - 1) (Lng M - 1) = true := leR0_refl_68 M (Lng M - 1) hj1lt
  have m84 := rightmost_nonadm_ancestor M (transJ0 M) (Lng M - 1)
    hST hmono hnxt0 hleRefl notnx1 hnadm
  rw [hAdmEq] at m84
  obtain ⟨hBrge, ⟨hdpos, _hdTr⟩, hjointEq, hfnEq⟩ := m84
  -- 標準祖先切片は `DT_PS`（強単調）
  have hDT : DTPS (Red (seg M (transJm1 M) (Lng M - 1))) :=
    standard_slice_Red_strongmono M (transJm1 M) (Lng M - 1) hST hjm1j1 (le_refl _) hleab
  have hRRT : RTPS (Red (seg M (transJm1 M) (Lng M - 1))) := ((DTPS_iff _).mp hDT).1
  have hmonoR : monoT (Red (seg M (transJm1 M) (Lng M - 1))) = true :=
    ((DTPS_iff _).mp hDT).2.1
  have hdescR : descendingB (Br (Red (seg M (transJm1 M) (Lng M - 1)))) = true :=
    ((DTPS_iff _).mp hDT).2.2
  -- 長さ
  have hsegpos : 0 < Lng (seg M (transJm1 M) (Lng M - 1)) := by rw [length_seg]; omega
  have hsegT : TPS (seg M (transJm1 M) (Lng M - 1)) :=
    List.ne_nil_of_length_pos hsegpos
  have hLR : Lng (Red (seg M (transJm1 M) (Lng M - 1))) = (Lng M - 1) + 1 - transJm1 M := by
    rw [Lng_Red_invariance _ hsegT, length_seg]
  have hLRm1 : Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 = (Lng M - 1) - transJm1 M := by
    rw [hLR]; omega
  have hLRpos : 0 < Lng (Red (seg M (transJm1 M) (Lng M - 1))) := by rw [hLR]; omega
  -- `IncrFirst` シフト
  have hanc_if := ancestor_slice_Red_IncrFirst M (transJm1 M) (Lng M - 1)
    hMR hjm1j1 (le_refl _) hleab
  have hIF : seg M (transJm1 M) (Lng M - 1)
      = IncrFirstN (entry M 0 (transJm1 M) - entry M 1 (transJm1 M))
          (Red (seg M (transJm1 M) (Lng M - 1))) := hanc_if.2.2
  set k := entry M 0 (transJm1 M) - entry M 1 (transJm1 M) with hkdef
  have hcol0R : entry (Red (seg M (transJm1 M) (Lng M - 1))) 0 0
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 0 :=
    RTPS_mono_head_eq _ hRRT hmonoR
  -- 非許容 run の一次性（`wnx_run_entries`）
  have hj0L : transJ0 M < Lng M := by omega
  have hrun := wnx_run_entries M hMR (transJ0 M) (transJ0 M - transJm1 M) hj0L hnadm (by omega)
  rw [hAdmEq] at hrun
  have hidx : transJm1 M + (transJ0 M - transJm1 M) = transJ0 M := by omega
  rw [hidx] at hrun
  obtain ⟨hej0_0, hej0_1⟩ := hrun
  -- 条件(V): 行1の +1 段差
  have hej1_1 : entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.1.2
  -- 条件(A): 行0の +1 段差（最終列）
  have hcondA : RedCondA M = true := (RTPS_condAB M hMR).1
  have hej1_0 : entry M 0 (transJ0 M) + 1 = entry M 0 (Lng M - 1) := by
    have h := RedCondA_apply M hcondA 0 (Lng M - 1) (by omega) hj1lt hp0
    rw [← htj0] at h
    exact h
  -- シフト定数 `k` の関係
  have hjlt00 : (0 : ℕ) < Lng (seg M (transJm1 M) (Lng M - 1)) := by rw [length_seg]; omega
  have heSM00 : entry (seg M (transJm1 M) (Lng M - 1)) 0 0 = entry M 0 (transJm1 M) := by
    rw [entry_seg M (transJm1 M) (Lng M - 1) 0 0 hjlt00, Nat.add_zero]
  have heSM10 : entry (seg M (transJm1 M) (Lng M - 1)) 1 0 = entry M 1 (transJm1 M) := by
    rw [entry_seg M (transJm1 M) (Lng M - 1) 1 0 hjlt00, Nat.add_zero]
  have heS00 : entry (seg M (transJm1 M) (Lng M - 1)) 0 0
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 0 0 + k := by
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_zero k (Red (seg M (transJm1 M) (Lng M - 1))) 0 hLRpos
  have heS10 : entry (seg M (transJm1 M) (Lng M - 1)) 1 0
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 0 := by
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_one k (Red (seg M (transJm1 M) (Lng M - 1))) 0
  have hkEq : entry M 0 (transJm1 M) = entry M 1 (transJm1 M) + k := by
    omega
  -- `R` の最終列の両段
  have hjltL : (Lng M - 1) - transJm1 M < Lng (seg M (transJm1 M) (Lng M - 1)) := by
    rw [length_seg]; omega
  have hjltR : (Lng M - 1) - transJm1 M < Lng (Red (seg M (transJm1 M) (Lng M - 1))) := by
    rw [hLR]; omega
  have hidxe : transJm1 M + ((Lng M - 1) - transJm1 M) = Lng M - 1 := by omega
  have e1_0 : entry (seg M (transJm1 M) (Lng M - 1)) 0 ((Lng M - 1) - transJm1 M)
      = entry M 0 (Lng M - 1) := by
    rw [entry_seg M (transJm1 M) (Lng M - 1) 0 ((Lng M - 1) - transJm1 M) hjltL, hidxe]
  have e2_0 : entry (seg M (transJm1 M) (Lng M - 1)) 0 ((Lng M - 1) - transJm1 M)
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 0 ((Lng M - 1) - transJm1 M) + k := by
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_zero k (Red (seg M (transJm1 M) (Lng M - 1)))
      ((Lng M - 1) - transJm1 M) hjltR
  have heRlast0 : entry (Red (seg M (transJm1 M) (Lng M - 1))) 0
        (Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1) + k = entry M 0 (Lng M - 1) := by
    rw [hLRm1, ← e2_0]; exact e1_0
  have e1_1 : entry (seg M (transJm1 M) (Lng M - 1)) 1 ((Lng M - 1) - transJm1 M)
      = entry M 1 (Lng M - 1) := by
    rw [entry_seg M (transJm1 M) (Lng M - 1) 1 ((Lng M - 1) - transJm1 M) hjltL, hidxe]
  have e2_1 : entry (seg M (transJm1 M) (Lng M - 1)) 1 ((Lng M - 1) - transJm1 M)
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 1 ((Lng M - 1) - transJm1 M) := by
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_one k (Red (seg M (transJm1 M) (Lng M - 1)))
      ((Lng M - 1) - transJm1 M)
  have heRlast1 : entry (Red (seg M (transJm1 M) (Lng M - 1))) 1
        (Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1) = entry M 1 (Lng M - 1) := by
    rw [hLRm1, ← e2_1]; exact e1_1
  -- DIAG: 最終列が対角
  have hDIAG : entry (Red (seg M (transJm1 M) (Lng M - 1))) 0
        (Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1)
      = entry (Red (seg M (transJm1 M) (Lng M - 1))) 1
        (Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1) := by
    omega
  -- 枝は非空、最終枝は末尾単項、純幹でない
  have hBrne : Br (Red (seg M (transJm1 M) (Lng M - 1))) ≠ [] := by
    intro he; rw [he] at hBrge; simp at hBrge
  have hfnLast : VEj1p (Red (seg M (transJm1 M) (Lng M - 1)))
      = Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 := by
    unfold VEj1p
    rw [hfnEq, ← hLRm1]
  have hTrbound : TrMax (Red (seg M (transJm1 M) (Lng M - 1)))
      ≤ Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 :=
    TrMax_bound _ (RTPS_TPS _ hRRT)
  have hTrne : TrMax (Red (seg M (transJm1 M) (Lng M - 1)))
      ≠ Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 := by
    intro he; apply hBrne; simp [Br, he]
  refine ⟨⟨hRRT, hmonoR, hBrne, Or.inr ⟨hjointEq, ?_, hdescR⟩⟩, hfnLast, ?_⟩
  · rw [hfnLast]; exact hDIAG
  · omega

/-- Isabelle `wnx_transfer_of_reg`（pss_wip.thy:80867）: 簡約切片が §8.2 体制
（`VEReg d`）に入るとき、run offset `d` の本体転送を無条件 VE 本体 `vcx_VE_all` で閉じる。
`wnx_seg_transport_W1/W2`（«8».«8.2-condV-VE-wnx»）で両 `Trans` を簡約切片へ落とす。 -/
private theorem transfer_of_reg_w2 (M : PS) (a b d : ℕ) (hMR : RTPS M)
    (hab : a < b) (hbL : b ≤ Lng M - 1) (hleab : leR M 0 a b = true)
    (hamb : a + d < b) (hleam : le0 M (a + d) b = true)
    (hREG : VEReg d (Red (seg M a b))) :
    bpHeadT (Trans (seg M (a + d) b)) = bpHeadT (Trans (seg M a b)) := by
  have t1 : Trans (seg M a b) = Trans (Red (seg M a b)) :=
    wnx_seg_transport_W1 M a b hab
  have t2 : Trans (seg M (a + d) b)
      = Trans (seg (Red (seg M a b)) d (Lng (Red (seg M a b)) - 1)) :=
    wnx_seg_transport_W2 M a b d hMR hab hbL hleab hamb hleam
  have hVE : VEeq d (Red (seg M a b)) := vcx_VE_all d (Red (seg M a b)) hREG
  rw [t2, t1]
  exact hVE

/-! ## 純幹分岐（`wnx_trunk_diagSeq` / `wnx_trunk_transfer`） -/

/-- 各列の対 `Q[j]` を係数 `entry` で読み出す。 -/
private theorem getElem_pair_w2 (Q : PS) (j : ℕ) (hj : j < Lng Q) :
    Q[j] = (entry Q 0 j, entry Q 1 j) := by
  apply Prod.ext
  · simp [entry, List.getElem?_eq_getElem hj]
  · simp [entry, List.getElem?_eq_getElem hj]

/-- Isabelle `wnx_trunk_diagSeq`（pss_wip.thy:80890）: 簡約された純幹（`TrMax Q = Lng Q - 1`）
は対角列 `diagSeq`。両段が `Q₁,₀ + j`（`baseU_alltrunk_diag_entry`）であることによる。 -/
private theorem trunk_eq_diagSeq_w2 (Q : PS) (hQR : RTPS Q) (hmono : monoT Q = true)
    (htr : TrMax Q = Lng Q - 1) :
    Q = diagSeq (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) := by
  have hQT : TPS Q := RTPS_TPS Q hQR
  have hpos : 0 < Lng Q := List.length_pos_of_ne_nil hQT
  apply List.ext_getElem
  · show Lng Q = _
    simp only [diagSeq, List.length_map, List.length_range']
    omega
  · intro i h1 h2
    have hiQ : i < Lng Q := h1
    have ho := baseU_alltrunk_diag_entry Q i hQR hmono htr hiQ
    have hdget : (diagSeq (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)))[i]
        = (entry Q 1 0 + i, entry Q 1 0 + i) := by
      simp [diagSeq, List.getElem_map, List.getElem_range']
    rw [getElem_pair_w2 Q i hiQ, hdget, ho.1, ho.2]

/-- Isabelle `wnx_trunk_transfer`（pss_wip.thy:80956）: 簡約祖先切片が純幹のとき、
両 `Trans` は同じ本体 `D_w 0` を持つ二段塔なので `bpHeadT` は一致。 -/
private theorem trunk_transfer_w2 (M : PS) (a b d : ℕ) (hMR : RTPS M)
    (hab : a < b) (hbL : b ≤ Lng M - 1) (hleab : leR M 0 a b = true)
    (hamb : a + d < b) (hleam : le0 M (a + d) b = true)
    (hTR : TrMax (Red (seg M a b)) = Lng (Red (seg M a b)) - 1) :
    bpHeadT (Trans (seg M (a + d) b)) = bpHeadT (Trans (seg M a b)) := by
  have hbLng : b < Lng M := by omega
  have hsegpos : 0 < Lng (seg M a b) := by rw [length_seg]; omega
  have hsegT : TPS (seg M a b) := List.ne_nil_of_length_pos hsegpos
  have hfacts := ancestor_slice_Red_IncrFirst M a b hMR hab hbL hleab
  have hRedR : Red (Red (seg M a b)) = Red (seg M a b) := hfacts.1
  have hmonoR : monoT (Red (seg M a b)) = true := hfacts.2.1
  have hLR : Lng (Red (seg M a b)) = b + 1 - a := by
    rw [Lng_Red_invariance _ hsegT, length_seg]
  have hRTpos : 0 < Lng (Red (seg M a b)) := by rw [hLR]; omega
  have hRT : TPS (Red (seg M a b)) := List.ne_nil_of_length_pos hRTpos
  have hRRT : RTPS (Red (seg M a b)) := by
    show reduced (Red (seg M a b)) = true
    have hne : Red (seg M a b) ≠ [] := hRT
    simp [reduced, hne, hRedR]
  have Rdiag : Red (seg M a b)
      = diagSeq (entry (Red (seg M a b)) 1 0)
          (entry (Red (seg M a b)) 1 0 + (Lng (Red (seg M a b)) - 1)) :=
    trunk_eq_diagSeq_w2 (Red (seg M a b)) hRRT hmonoR hTR
  set u := entry (Red (seg M a b)) 1 0 with hu
  set w := u + (Lng (Red (seg M a b)) - 1) with hw
  have hLRm1 : Lng (Red (seg M a b)) - 1 = b - a := by rw [hLR]; omega
  have huw : u < w := by rw [hw, hLRm1]; omega
  have humw : u + d < w := by rw [hw, hLRm1]; omega
  have hdlt : d < Lng (Red (seg M a b)) := by rw [hLR]; omega
  have t1 : Trans (seg M a b) = Trans (Red (seg M a b)) := wnx_seg_transport_W1 M a b hab
  have t2 : Trans (seg M (a + d) b)
      = Trans (seg (Red (seg M a b)) d (Lng (Red (seg M a b)) - 1)) :=
    wnx_seg_transport_W2 M a b d hMR hab hbL hleab hamb hleam
  have T1 : Trans (Red (seg M a b)) = Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    conv_lhs => rw [Rdiag]
    exact diagSeq_Trans u w huw
  have segdrop : seg (Red (seg M a b)) d (Lng (Red (seg M a b)) - 1) = diagSeq (u + d) w := by
    rw [seg_to_last_eq_drop (Red (seg M a b)) d hdlt]
    conv_lhs => rw [Rdiag]
    simp only [diagSeq, ← List.map_drop, List.drop_range']
    congr 2 <;> omega
  have T2 : Trans (seg (Red (seg M a b)) d (Lng (Red (seg M a b)) - 1))
      = Dprin ((u + d : ℕ) : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    rw [segdrop]
    exact diagSeq_Trans (u + d) w humw
  rw [t1, t2, T1, T2]
  rfl

/-! ## 主定理 -/

/-- Isabelle `wnx_W2nostr_c1`(81279) / `wnx_W2nostr_c2`(81304): 非許容前線
`[j₋₁, j₀]` を跨いでも `Trans` 本体 `bpHeadT` は `c ∈ {Lng M - 1, Lng M - 2}` で一定。 -/
theorem nadmW2nostr_holds : NadmW2nostr := by
  intro M hST hmono hcond hnadm
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨hjm1lt, hrng, hleab, hle0c1, hle0c2, hleabc2, _hnxt0⟩ :=
    nadm_setup_w2 M hST hmono hcond hnadm
  obtain ⟨hREG, hVEj1p, hTrlt⟩ := reg_c1_w2 M hST hmono hcond hnadm
  have hjm1j1 : transJm1 M < Lng M - 1 := by omega
  have hle0c1' : le0 M (transJ0 M) (Lng M - 1) = true := by simpa [leR] using hle0c1
  have hle0c2' : le0 M (transJ0 M) (Lng M - 2) = true := by simpa [leR] using hle0c2
  have hidxj0 : transJm1 M + (transJ0 M - transJm1 M) = transJ0 M := by omega
  refine ⟨?_, ?_⟩
  · -- c1: c = Lng M - 1
    have h := transfer_of_reg_w2 M (transJm1 M) (Lng M - 1) (transJ0 M - transJm1 M)
      hMR hjm1j1 (le_refl _) hleab (by omega) (by rw [hidxj0]; exact hle0c1') hREG
    rw [hidxj0] at h
    exact h
  · -- c2: c = Lng M - 2
    -- Pred R = Red (seg M j₋₁ (Lng M - 2))
    have hRRT : RTPS (Red (seg M (transJm1 M) (Lng M - 1))) := hREG.1
    have hRT : TPS (Red (seg M (transJm1 M) (Lng M - 1))) := RTPS_TPS _ hRRT
    have hsegpos : 0 < Lng (seg M (transJm1 M) (Lng M - 1)) := by rw [length_seg]; omega
    have hsegT : TPS (seg M (transJm1 M) (Lng M - 1)) := List.ne_nil_of_length_pos hsegpos
    have hLR : Lng (Red (seg M (transJm1 M) (Lng M - 1))) = (Lng M - 1) + 1 - transJm1 M := by
      rw [Lng_Red_invariance _ hsegT, length_seg]
    have hRL1 : 1 < Lng (Red (seg M (transJm1 M) (Lng M - 1))) := by rw [hLR]; omega
    have hPredR : Pred (Red (seg M (transJm1 M) (Lng M - 1)))
        = Red (seg M (transJm1 M) (Lng M - 2)) := by
      have h := Pred_Red_terminal_slice M (transJm1 M) (Lng M - 1) hjm1j1
      rw [show Lng M - 1 - 1 = Lng M - 2 from by omega] at h
      exact h
    by_cases hcase : TrMax (Red (seg M (transJm1 M) (Lng M - 1))) + 2
        = Lng (Red (seg M (transJm1 M) (Lng M - 1)))
    · -- 純幹分岐
      have hTrne : TrMax (Red (seg M (transJm1 M) (Lng M - 1)))
          ≠ Lng (Red (seg M (transJm1 M) (Lng M - 1))) - 1 := by omega
      have hTrRc : TrMax (Red (seg M (transJm1 M) (Lng M - 2)))
          = Lng (Red (seg M (transJm1 M) (Lng M - 2))) - 1 := by
        rw [← hPredR, TrMax_Pred_nontrunk (Red (seg M (transJm1 M) (Lng M - 1))) hRT hRL1 hTrne,
          length_Pred (Red (seg M (transJm1 M) (Lng M - 1))) hRL1]
        omega
      have h := trunk_transfer_w2 M (transJm1 M) (Lng M - 2) (transJ0 M - transJm1 M)
        hMR (by omega) (by omega) hleabc2 (by omega) (by rw [hidxj0]; exact hle0c2') hTrRc
      rw [hidxj0] at h
      exact h
    · -- 体制遺伝分岐
      have hnonmin : TrMax (Red (seg M (transJm1 M) (Lng M - 1))) + 2
          < Lng (Red (seg M (transJm1 M) (Lng M - 1))) := by omega
      have hREGc : VEReg (transJ0 M - transJm1 M) (Red (seg M (transJm1 M) (Lng M - 2))) := by
        rw [← hPredR]
        exact rpj1eq_vc (transJ0 M - transJm1 M) (Red (seg M (transJm1 M) (Lng M - 1)))
          hREG hVEj1p hnonmin
      have h := transfer_of_reg_w2 M (transJm1 M) (Lng M - 2) (transJ0 M - transJm1 M)
        hMR (by omega) (by omega) hleabc2 (by omega) (by rw [hidxj0]; exact hle0c2') hREGc
      rw [hidxj0] at h
      exact h

#print axioms nadmW2nostr_holds

end PSS

