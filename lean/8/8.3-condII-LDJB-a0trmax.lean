import «8».«8.3-condII-LDJB»
import «7».«7.4-RightNodes-Mark»
import «8».«8.1-diagSeq-Trans»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.5-Red-welldefined»
import «6».«6.6-reduced-leftend»
import «6».«6.5-Lng-Red-invariance»
import «7».«7.3-Trans-welldefined»

/-!
# §8.3 条件(II) — `TV_LDJB` の残差 `RN_a0_trmax_ldjb` の discharge

## 目的

ビルド済み «8».«8.3-condII-LDJB» が露出した campaign-size 残差 `Prop`
`RN_a0_trmax_ldjb`（= Isabelle `ljx_RightNodes_a0_trmax`）を、Isabelle の証明構造で
**無条件に** discharge する。`j_L = TrMax R_c` の場合、`RightNodes (Trans R_c)` の第 2 成分は
`entry R_c 1 j_L`（幹対角プレフィックス分解）。

## Isabelle 対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `ljx_RightNodes_a0_trmax` | layerB/pss_wip.thy:114607 | `RN_a0_trmax_holds`（`RN_a0_trmax_ldjb` を drop-in、無条件） |
| `ljx_lastblock_le0`       | layerB/pss_wip.thy:114499 | private `lastblock_le0_lat` |
| `m_7_4_RightNodes_Mark`   | «7».«7.4-RightNodes-Mark»:256 | 基点分割 |
| `m_8_1_diagSeq_Trans`     | «8».«8.1-diagSeq-Trans»:665 | `diagSeq_Trans` |
| `trunk_entries_offset`    | «6».«6.5-Red-le-core»:274 | 幹の行 0/1 一次性 |
| `Joints_nextR_FirstNodes` | «6».«6.5-Red-welldefined»:390 | `nextR0 (joint) (fn)` |
| `FirstNodes_TrMax_Joints` | «6».«6.4-FirstNodes-TrMax-Joints» | （lastblock 経由） |
| `wf21_Br_eq_seg`          | «8».«8.2-condV-rightmost-parent»:98 | 最終枝＝接尾切片 |
| `le0_monoT_seg_into_list` | «8».«8.2-condV-rightmost-parent»:62 | mono 切片の `le0` |
| `Br_component_nonmulti`   | «6».«6.5-Red-welldefined»:347 | 枝成分の非多項性 |
| `kfwd_reduced_monoT_diag00` | — | `RTPS_mono_head_eq`（«6».«6.6-reduced-leftend»） |

## 証明構造（`ljx_RightNodes_a0_trmax` の逐語移植）

1. `?jm1 = Adm M (parent M 0 (Lng M - 1))`、`R_c = tvx_Rc M = Red (seg M ?jm1 (Lng M - 2))`。
   到達性 `leab`（`condII_reach_lat`）＋`ancestor_slice_Red_IncrFirst` で `R_c` の
   `RT_PS`/`monoT`/`TPS`/`RedCondA`。
2. `?BL = (Br R_c).length - 1`、`?jL = tvx_jL M`、`?fn = tvx_fn M`。
   `nx0 : nextR R_c 0 ?jL ?fn`（`Joints_nextR_FirstNodes`）から `le0J`、
   `lastblock_le0_lat` から `le0F`、推移で `le0E`。`adm R_c ?jL`（`adm_TrMax_lat`＋`jeq`）と
   合わせて `mk : Marked R_c ?jL`。
3. `jlt2 : ?jL < Lng R_c - 1`（`TrMax_bound`＋`Br ≠ []`）で `m_7_4_RightNodes_Mark`。
   基点分割 `SPL`/`SPL2`。
4. `segdiag : seg R_c 0 ?jL = diagSeq (entry R_c 1 0) (entry R_c 1 0 + ?jL)`
   （`trunk_entries_offset`＋`diag00`）→ `diagSeq_Trans` → `RND`。
5. `SPL2` と `RND` と `offsJ`（`entry R_c 1 ?jL = entry R_c 1 0 + ?jL`）の突き合わせで
   `a0 = [entry R_c 1 0]`、`SPL` で結論。

## 状態

* ✅ `RN_a0_trmax_holds`: `RN_a0_trmax_ldjb` を無条件に discharge（sorry 0、
  axiom = [propext, Classical.choice, Quot.sound]）。
* private `_lat`: `le0Aux_refl_lat`/`le0_refl_lat`/`RightNodes_Dprin_lat`/`condII_reach_lat`/
  `nextR1_TrMax_fail_lat`/`adm_TrMax_lat`/`le0_trans_lat`/`seg_getElem_lat`/
  `diagSeq_getElem_lat`/`lastblock_le0_lat`（module 跨ぎ不可の private の逐語複製）。
-/

namespace PSS

/-! ## 反射律（`le0Aux_refl_at` の逐語複製） -/

private theorem le0Aux_refl_lat (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0_refl_lat (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 0 a a = true := by
  simp [leR, le0, ha, le0Aux_refl_lat]

/-! ## `Dprin` の `RightNodes` 展開（`RightNodes_Dprin_lr` の逐語複製） -/

private theorem RightNodes_Dprin_lat (v : ℕ∞) (a : BT) :
    RightNodes (Dprin v a) = v.toNat :: RightNodes a := by
  simp only [Dprin, RightNodes, rightNodesList, rightNodesBP]

/-! ## 到達性脚 `leab`（R3LE `condII_reach_r3` の逐語複製） -/

private theorem condII_reach_lat (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
    (hmk : Marked (Pred K) a) (hab : a < Lng K - 2) :
    leR K 0 a (Lng K - 2) = true := by
  have hKT : TPS K := RTPS_TPS K hKR
  have hpredT : TPS (Pred K) := hmk.1
  have hpl : Lng (Pred K) = Lng K - 1 := length_Pred K hL
  have hle0P : leR (Pred K) 0 a (Lng (Pred K) - 1) = true := hmk.2.2
  have hidx : Lng (Pred K) - 1 = Lng K - 2 := by omega
  rw [hidx] at hle0P
  have hLK2 : Lng K - 2 < Lng K := by omega
  apply parent_exists_3 K a (Lng K - 2) hKT hab hLK2
  intro j hlo hhi
  have hgrowPred : entry (Pred K) 0 a < entry (Pred K) 0 j :=
    ancestor_basic_1 (Pred K) a j (Lng K - 2) hpredT hlo hhi hle0P
  have haLt : a < Lng K - 1 := by omega
  have hjLt : j < Lng K - 1 := by omega
  rw [entry_Pred K 0 a haLt, entry_Pred K 0 j hjLt] at hgrowPred
  exact hgrowPred

/-! ## `adm_TrMax`（`nextR1_TrMax_fail_ck`＋`adm_TrMax_ck` の逐語複製） -/

private theorem nextR1_TrMax_fail_lat (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hst : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j, j < TrMax M + 1 → nextR M 1 j (j + 1) = true := by
        intro j hj
        rcases Nat.lt_or_ge j (TrMax M) with h | h
        · exact TrMax_trunk_step M j hM h
        · have hje : j = TrMax M := by omega
          rw [hje]; exact hst
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

private theorem adm_TrMax_lat (M : PS) (hM : TPS M) : adm M (TrMax M) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_lat M hM
  have hno : ¬ Lng M < TrMax M := by omega
  simp [adm, nadm, hnostep, hno]

/-! ## `le0` 推移律（`le0_trans_c2s` の逐語複製） -/

private theorem le0_trans_lat (M : PS) (a b c : ℕ) (hM : TPS M)
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

/-! ## `seg`/`diagSeq` の getElem（`seg_getElem_m0` の逐語複製＋対角版） -/

private theorem seg_getElem_lat (M : PS) (a b i : ℕ) (hi : i < Lng (seg M a b)) :
    (seg M a b)[i] = (entry M 0 (a + i), entry M 1 (a + i)) := by
  simp [seg, List.getElem_range']

private theorem diagSeq_getElem_lat (u v i : ℕ) (hi : i < Lng (diagSeq u v)) :
    (diagSeq u v)[i] = (u + i, u + i) := by
  simp [diagSeq, List.getElem_map, List.getElem_range']

/-! ## 最終枝の `le0`（`ljx_lastblock_le0` の逐語移植） -/

private theorem lastblock_le0_lat (R : PS) (hRT : TPS R) (hmono : monoT R = true)
    (hBr : Br R ≠ []) :
    leR R 0 ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1) = true := by
  have hRpos : 0 < Lng R := List.length_pos_of_ne_nil hRT
  have hBrpos : 0 < (Br R).length := List.length_pos_of_ne_nil hBr
  have hBLlt : (Br R).length - 1 < (Br R).length := by omega
  have nx := Joints_nextR_FirstNodes R ((Br R).length - 1) hRT hmono hBLlt
  have hrel : nextrel0 R ((Joints R).getD ((Br R).length - 1) 0)
      ((FirstNodes R).getD ((Br R).length - 1) 0) = true := by simpa [nextR] using nx
  have hrel' := hrel
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hrel'
  have hfnlt : (FirstNodes R).getD ((Br R).length - 1) 0 < Lng R := hrel'.1.1.1.2
  have hfnle : (FirstNodes R).getD ((Br R).length - 1) 0 ≤ Lng R - 1 := by omega
  by_cases hfe : (FirstNodes R).getD ((Br R).length - 1) 0 = Lng R - 1
  · rw [hfe]; exact le0_refl_lat R (Lng R - 1) (by omega)
  · have hblk : (Br R).getD ((Br R).length - 1) []
        = seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1) :=
      wf21_Br_eq_seg R hRT hBr
    have hgt : 1 < Lng (seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1)) := by
      rw [length_seg]; omega
    have hnz : zeroT (seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1)) = false := by
      cases h : zeroT (seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1)) with
      | false => rfl
      | true =>
        exfalso
        have hL1 : Lng (seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1)) = 1 := by
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
          exact h.1
        omega
    have hbrmono := Br_component_nonmulti R ((Br R).length - 1) hRT hBLlt
    have hsegmono : monoT (seg R ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1)) = true := by
      rcases hbrmono with hz | hm
      · rw [hblk, hnz] at hz; exact Bool.noConfusion hz
      · rwa [hblk] at hm
    have hres := le0_monoT_seg_into_list R
      ((FirstNodes R).getD ((Br R).length - 1) 0) (Lng R - 1) (Lng R - 1)
      hRT hsegmono hfnle le_rfl (by omega)
    simpa [leR] using hres

/-! ## `RN_a0_trmax_ldjb` の discharge（`ljx_RightNodes_a0_trmax` の逐語移植） -/

/-- Isabelle `ljx_RightNodes_a0_trmax` (layerB/pss_wip.thy:114607) の 1:1 移植。
`j_L = TrMax R_c` の場合、`RightNodes (Trans R_c)` の位置 0/1 は
`entry R_c 1 0` / `entry R_c 1 j_L`。 -/
theorem RN_a0_trmax_holds : RN_a0_trmax_ldjb := by
  intro M hR hmono hj1 hcond hBR hjpos hjeq
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _hE1z, _hNadm, _hParPos, hAdmLt, hParLt, _hCond, _hVI, _hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  have hb2 : Lng M - 2 ≤ Lng M - 1 := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hMT hlen hp0
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    condII_reach_lat M (Adm M (parent M 0 (Lng M - 1))) hR hlen hmk hab
  -- `R_c` の性質
  have hSegT : TPS (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) := by
    have h0 : 0 < Lng (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) := by
      rw [length_seg]; omega
    exact List.ne_nil_of_length_pos h0
  have hAIF := ancestor_slice_Red_IncrFirst M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)
    hR hab hb2 leab
  have hmonoRc : monoT (tvx_Rc M) = true := hAIF.2.1
  have hfix : Red (tvx_Rc M) = tvx_Rc M := hAIF.1
  have hRcLen : Lng (tvx_Rc M)
      = (Lng M - 2) + 1 - (Adm M (parent M 0 (Lng M - 1))) := by
    show Lng (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))) = _
    rw [Lng_Red_invariance _ hSegT, length_seg]
  have hRcpos : 0 < Lng (tvx_Rc M) := by rw [hRcLen]; omega
  have hRcT : TPS (tvx_Rc M) := List.ne_nil_of_length_pos hRcpos
  have hRcRT : RTPS (tvx_Rc M) := by
    show reduced (tvx_Rc M) = true
    have hne : tvx_Rc M ≠ [] := hRcT
    simp [reduced, hne, hfix]
  have hcondARc : RedCondA (tvx_Rc M) = true := (RTPS_condAB (tvx_Rc M) hRcRT).1
  have hdiag00 : entry (tvx_Rc M) 0 0 = entry (tvx_Rc M) 1 0 :=
    RTPS_mono_head_eq (tvx_Rc M) hRcRT hmonoRc
  -- 最終枝インデックス
  have hBrpos : 0 < (Br (tvx_Rc M)).length := List.length_pos_of_ne_nil hBR
  have hBLlt : (Br (tvx_Rc M)).length - 1 < (Br (tvx_Rc M)).length := by omega
  -- `nx0 : nextR R_c 0 j_L fn`
  have hjL_def : tvx_jL M = (Joints (tvx_Rc M)).getD ((Br (tvx_Rc M)).length - 1) 0 := rfl
  have hfn_def : tvx_fn M = (FirstNodes (tvx_Rc M)).getD ((Br (tvx_Rc M)).length - 1) 0 := rfl
  have nx0 : nextR (tvx_Rc M) 0 (tvx_jL M) (tvx_fn M) = true := by
    rw [hjL_def, hfn_def]
    exact Joints_nextR_FirstNodes (tvx_Rc M) ((Br (tvx_Rc M)).length - 1) hRcT hmonoRc hBLlt
  have hnxrel : nextrel0 (tvx_Rc M) (tvx_jL M) (tvx_fn M) = true := by simpa [nextR] using nx0
  have hnxrel' := hnxrel
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnxrel'
  have hjLfn : tvx_jL M < tvx_fn M := hnxrel'.1.1.2
  have hfnlt : tvx_fn M < Lng (tvx_Rc M) := hnxrel'.1.1.1.2
  -- `le0J`, `le0F`, `le0E`
  have le0J : leR (tvx_Rc M) 0 (tvx_jL M) (tvx_fn M) = true :=
    nextR0_leR (tvx_Rc M) (tvx_jL M) (tvx_fn M) nx0
  have le0F : leR (tvx_Rc M) 0 (tvx_fn M) (Lng (tvx_Rc M) - 1) = true :=
    lastblock_le0_lat (tvx_Rc M) hRcT hmonoRc hBR
  have le0E : leR (tvx_Rc M) 0 (tvx_jL M) (Lng (tvx_Rc M) - 1) = true := by
    by_cases hfe : tvx_fn M = Lng (tvx_Rc M) - 1
    · rw [← hfe]; exact le0J
    · have hfnlt1 : tvx_fn M < Lng (tvx_Rc M) - 1 := by omega
      exact le0_trans_lat (tvx_Rc M) (tvx_jL M) (tvx_fn M) (Lng (tvx_Rc M) - 1)
        hRcT le0J le0F hjLfn hfnlt1 (by omega)
  -- `adm R_c j_L` と `mk`
  have hadmJ : adm (tvx_Rc M) (tvx_jL M) = true := by
    rw [hjeq]; exact adm_TrMax_lat (tvx_Rc M) hRcT
  have mk : Marked (tvx_Rc M) (tvx_jL M) := ⟨hRcT, hadmJ, le0E⟩
  -- `jlt2 : j_L < Lng R_c - 1`
  have htrne : TrMax (tvx_Rc M) ≠ Lng (tvx_Rc M) - 1 := by
    intro heq; exact hBR (by simp [Br, heq])
  have htrbound := TrMax_bound (tvx_Rc M) hRcT
  have hjlt2 : tvx_jL M < Lng (tvx_Rc M) - 1 := by rw [hjeq]; omega
  -- 基点分割
  obtain ⟨a0, a1, hSPL, hSPL2, _hMark⟩ :=
    m_7_4_RightNodes_Mark (tvx_Rc M) (tvx_jL M) mk hRcRT hjpos hjlt2
  -- `offsJ`, `diag00`
  have hjle : tvx_jL M ≤ TrMax (tvx_Rc M) := le_of_eq hjeq
  have hoffJ := trunk_entries_offset (tvx_Rc M) hRcT hcondARc (tvx_jL M) hjle
  -- `segdiag`
  have segdiag : seg (tvx_Rc M) 0 (tvx_jL M)
      = diagSeq (entry (tvx_Rc M) 1 0) (entry (tvx_Rc M) 1 0 + tvx_jL M) := by
    apply List.ext_getElem
    · have hL1 : (seg (tvx_Rc M) 0 (tvx_jL M)).length = tvx_jL M + 1 := by
        rw [show (seg (tvx_Rc M) 0 (tvx_jL M)).length
          = Lng (seg (tvx_Rc M) 0 (tvx_jL M)) from rfl, length_seg]; omega
      have hL2 : (diagSeq (entry (tvx_Rc M) 1 0) (entry (tvx_Rc M) 1 0 + tvx_jL M)).length
          = tvx_jL M + 1 := by
        simp only [diagSeq, List.length_map, List.length_range']; omega
      rw [hL1, hL2]
    · intro i h1 h2
      have hile : i ≤ tvx_jL M := by
        have hh := h1
        rw [show (seg (tvx_Rc M) 0 (tvx_jL M)).length
          = Lng (seg (tvx_Rc M) 0 (tvx_jL M)) from rfl, length_seg] at hh
        omega
      have ho := trunk_entries_offset (tvx_Rc M) hRcT hcondARc i (by omega)
      rw [seg_getElem_lat (tvx_Rc M) 0 (tvx_jL M) i h1,
        diagSeq_getElem_lat (entry (tvx_Rc M) 1 0) (entry (tvx_Rc M) 1 0 + tvx_jL M) i h2]
      rw [Nat.zero_add]
      have hc0 : entry (tvx_Rc M) 0 i = entry (tvx_Rc M) 1 0 + i := by rw [ho.1, hdiag00]
      rw [hc0, ho.2]
  -- `RND`
  have huw : entry (tvx_Rc M) 1 0 < entry (tvx_Rc M) 1 0 + tvx_jL M := by omega
  have hTD : Trans (seg (tvx_Rc M) 0 (tvx_jL M))
      = Dprin ((entry (tvx_Rc M) 1 0 : ℕ) : ℕ∞)
          (Dprin ((entry (tvx_Rc M) 1 0 + tvx_jL M : ℕ) : ℕ∞) BZero) := by
    rw [segdiag]
    exact diagSeq_Trans (entry (tvx_Rc M) 1 0) (entry (tvx_Rc M) 1 0 + tvx_jL M) huw
  have hRND : RightNodes (Trans (seg (tvx_Rc M) 0 (tvx_jL M)))
      = [entry (tvx_Rc M) 1 0, entry (tvx_Rc M) 1 0 + tvx_jL M] := by
    rw [hTD, RightNodes_Dprin_lat, RightNodes_Dprin_lat]
    have hz : RightNodes BZero = [] := rfl
    rw [hz]
    simp only [ENat.toNat_coe]
  -- `a0 = [entry R_c 1 0]`
  have hcatSPL : a0 ++ [entry (tvx_Rc M) 1 (tvx_jL M)]
      = [entry (tvx_Rc M) 1 0] ++ [entry (tvx_Rc M) 1 (tvx_jL M)] := by
    have h1 : a0 ++ [entry (tvx_Rc M) 1 (tvx_jL M)]
        = [entry (tvx_Rc M) 1 0, entry (tvx_Rc M) 1 0 + tvx_jL M] := hSPL2.symm.trans hRND
    rw [h1, hoffJ.2]
    rfl
  have ha0 : a0 = [entry (tvx_Rc M) 1 0] := List.append_cancel_right hcatSPL
  -- 結論
  refine ⟨a1, ?_⟩
  rw [hSPL, ha0]
  rfl

#print axioms RN_a0_trmax_holds

end PSS
