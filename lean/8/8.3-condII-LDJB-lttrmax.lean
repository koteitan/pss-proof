import «8».«8.3-condII-LDJB-a0trmax»
import «8».«8.3-condII-LDJB-readouts»
import «7».«7.4-RightAnces-RightNodes»
import «6».«6.8-standard-slice-Br-descending»
import «8».«8.2-condV-VE-wnx»

/-!
# §8.3 条件(II) — `TV_LDJB` の最重量残差 `RN_a0_lt_trmax_ldjb` の discharge

## 目的

ビルド済み «8».«8.3-condII-LDJB» が露出した campaign-size 残差 `Prop`
`RN_a0_lt_trmax_ldjb`（= Isabelle `ljx_RightNodes_a0_lt_trmax`）を、Isabelle の証明構造で
**無条件に** discharge する。`j_L < TrMax R_c` の場合、`RightNodes (Trans R_c)` の位置 1 は
`entry R_c 1 j_L`（非対角付き、cond II/IV 側）か `entry R_c 1 j_L + 1`（cond V 側で対角排除）。

三つ組の最後の readout（`RN_a0_trmax_ldjb`=«8».«8.3-condII-LDJB-a0trmax»、
`RN_ldj_pj_ldjb`/`TVX_pos1ldj_ldjb`=«8».«8.3-condII-LDJB-readouts»、
`TVX_dstrict_ldjb`=«8».«8.2-condV-VE-wnx» は既閉）を閉じて、5 本すべての readout から
`TV_LDJB` を組み立てる `tv_ldjb_holds` も bank する。

## Isabelle 対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `ljx_RightNodes_a0_lt_trmax` | layerB/pss_wip.thy:114847 | `RN_a0_lt_trmax_holds`（`RN_a0_lt_trmax_ldjb` を drop-in、無条件） |
| `ljx_nextrel0_seg0`          | layerB:114520 | private `nextrel0_seg0_lt` |
| `ljx_nextrel0_unique`        | layerB:114461 | private `parent_eq_of_nextR0` で代替（一意化） |
| `ljx_Adm_eq_0`               | layerB:114 gap | private `Adm_eq_zero_lt`（`TrMax N = TrMax R_c` 経由で `trunk_interior_nadm` に還元） |
| `ljx_trunk_interior_nadm`    | layerB:114483 | private `trunk_interior_nadm_lt` |
| `ljx_RA_unfold_mono`         | layerB gap | private `RA_mono_unfold_lt`（`RightAncesAux_RTPS_equation` の 1 段展開） |
| `ljx_lastblock_le0`          | layerB:114499 | private `lastblock_le0_lt` |
| `m_7_4_RightNodes_Mark`      | «7».«7.4-RightNodes-Mark» | 基点分割（splice） |
| `m_7_4_RightAnces_RightNodes`| «7».«7.4-RightAnces-RightNodes» | `RA_mono_unfold_lt` 内で `RightNodes (Trans N)` に橋渡し |
| `TrMax_eq_of_prefix_agree`   | «6».«6.8-standard-slice-Br-descending»:618 | `TrMax N = TrMax R_c`（adm-transport 回避） |

## 証明構造（`ljx_RightNodes_a0_lt_trmax` の逐語移植・要点）

1. `R_c = tvx_Rc M`、`j_L = tvx_jL M`、`fn = tvx_fn M`、`N = seg R_c 0 fn`。
   `R_c` の `RT_PS`/`monoT`/`TPS`/`RedCondA`（a0trmax と同型）。`TrMax R_c < fn`、
   `fn < Lng R_c`、`j_L + 1 < fn`。
2. `N` の性質: `monoT N`（`mono_ancestor_slice` ＋ `0 → j_L → fn` の `le0`）、
   `TrMax N = TrMax R_c`（`TrMax_eq_of_prefix_agree_sym_68`）で `j_L < TrMax N`。
   ゆえに `adm N k = false`（`1 ≤ k ≤ j_L`、`trunk_interior_nadm`）→ `Adm N j_L = 0`。
   `parent N 0 (Lng N - 1) = j_L`（`nextrel0_seg0_lt` ＋ `parent_eq_of_nextR0`）。
3. `RA_mono_unfold_lt`: `RightNodes (Trans N)` を 1 段展開（cond I/III/VI は排除）:
   cond V なら `[e₁(0), e₁(fn)]`、さもなくば `[e₁(0), e₁(j_L), e₁(fn)]`。
4. `adm R_c fn`（`row0_valley_general_lt`）＋`lastblock_le0_lt` で `Marked R_c fn` →
   splice `RightNodes (Trans R_c) = RightNodes (Trans N) @ a1`。
5. cond V 分岐: `e₁(fn) = e₁(j_L) + 1` → 右選言。さもなくば: `RedCondA` で fn 対角を
   排除（対角⇒cond V ⇒矛盾）→ 左選言。

## 状態

* ✅ `RN_a0_lt_trmax_holds`: `RN_a0_lt_trmax_ldjb` を無条件に discharge。
* ✅ `tv_ldjb_holds : TV_LDJB`（5 本の readout をすべて配線）。
* private `_lt`: module 跨ぎ不可の private の逐語複製群。
-/

namespace PSS

/-! ## 反射律（`le0Aux_refl_at` の逐語複製） -/

private theorem le0Aux_refl_lt (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0_refl_lt (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 0 a a = true := by
  simp [leR, le0, ha, le0Aux_refl_lt]

/-! ## 到達性脚 `leab`（R3LE `condII_reach_r3` の逐語複製） -/

private theorem condII_reach_lt (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
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

/-! ## 幹の停止（`nextR1_TrMax_fail_ck` の逐語複製） -/

private theorem nextR1_TrMax_fail_lt (M : PS) (hM : TPS M) :
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

/-! ## 幹内部の非許容性（`adm_trunk_interior_nadm_ck` の逐語複製） -/

private theorem trunk_interior_nadm_lt (M : PS) (j : ℕ) (hM : TPS M)
    (hjpos : 0 < j) (hjlt : j < TrMax M) : adm M j = false := by
  have hs1 : nextR M 1 (j - 1) (j - 1 + 1) = true :=
    TrMax_trunk_step M (j - 1) hM (by omega)
  have hkeq : j - 1 + 1 = j := by omega
  rw [hkeq] at hs1
  have hs2 : nextR M 1 j (j + 1) = true := TrMax_trunk_step M j hM hjlt
  simp [adm, nadm, hs1, hs2]

/-! ## `Adm = 0`（`find_adm_zero_gp` / `Adm_eq_0_of_nadm_below` の逐語複製） -/

private theorem find_adm_zero_lt (M : PS) :
    ∀ j, adm M 0 = true → (∀ k, 1 ≤ k → k < j → adm M k = false) → 0 < j →
      (((List.range j).reverse.find? (fun j' => adm M j')).getD 0) = 0
  | 0, _, _, h0 => absurd h0 (by omega)
  | 1, hadm0, _, _ => by
      simp [List.range_succ, hadm0]
  | (j + 2), hadm0, hfail, _ => by
      rw [show List.range (j + 2) = List.range (j + 1) ++ [j + 1] from
        List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      rw [List.find?_cons_of_neg (by
        rw [hfail (j + 1) (by omega) (by omega)]
        simp)]
      exact find_adm_zero_lt M (j + 1) hadm0
        (fun k h1 hk => hfail k h1 (by omega)) (by omega)

private theorem Adm_eq_zero_lt (M : PS) (j : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ j → adm M k = false) : Adm M j = 0 := by
  unfold Adm
  by_cases hj : j = 0
  · subst hj
    simp [adm_zero]
  · have hja : adm M j = false := h j (by omega) (le_refl j)
    rw [hja]
    simp only [Bool.false_eq_true, if_false]
    exact find_adm_zero_lt M j (adm_zero M)
      (fun k h1 hk => h k h1 (by omega)) (by omega)

/-! ## `nextrel0` の接頭辞への輸送（`ljx_nextrel0_seg0` の逐語移植） -/

private theorem nextrel0_seg0_lt (M : PS) (j0 j1 c : ℕ)
    (nx : nextrel0 M j0 j1 = true) (hj1c : j1 ≤ c) (_hcL : c < Lng M) :
    nextrel0 (seg M 0 c) j0 j1 = true := by
  have ent : ∀ j, j ≤ c → entry (seg M 0 c) 0 j = entry M 0 j := by
    intro j hj
    have hjs : j < Lng (seg M 0 c) := by rw [length_seg]; omega
    have := entry_seg M 0 c 0 j hjs
    simpa using this
  have hh := nx
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hh
  obtain ⟨⟨⟨⟨hj0L, hj1L⟩, hlt⟩, helt⟩, hmid⟩ := hh
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, hlt⟩, ?_⟩, ?_⟩
  · rw [length_seg]; omega
  · rw [length_seg]; omega
  · rw [ent j0 (by omega), ent j1 hj1c]; exact helt
  · intro j hj
    have hjc : j ≤ c := by omega
    have hm := hmid j hj
    by_cases hj0j : j0 < j
    · have hm' : entry M 0 j1 ≤ entry M 0 j := by
        simp only [hj0j, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq] at hm
        exact hm
      simp only [hj0j, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      rw [ent j1 hj1c, ent j hjc]; exact hm'
    · simp [hj0j]

/-! ## `le0` の最終段抽出＋行 0 の谷（`le0Aux_last_step_sx`／`row0_valley_last_sx` の逐語複製） -/

private theorem le0Aux_last_step_lt {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) (hne : a ≠ b) :
    ∃ p, nextrel0 M p b = true ∧ le0Aux M fuel a p = true := by
  cases fuel with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      exact absurd this hne
  | succ fuel =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _, hnext, hap⟩
      · exact absurd h hne
      · exact ⟨p, hnext,
          le0Aux_mono_fseq M fuel (fuel + 1) a p (by omega) hap⟩

private theorem row0_valley_general_lt (M : PS) (c j : ℕ)
    (hlt : parent M 0 c < j) (hle : le0 M j c = true) : j = c := by
  by_contra hne
  have hh := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨p, hnext, hap⟩ := le0Aux_last_step_lt hh.2 hne
  have hpR : nextR M 0 p c = true := by simpa [nextR] using hnext
  have hpar : parent M 0 c = p := parent_eq_of_nextR0 M p c hpR
  have hjp : j ≤ p := le0Aux_index_fseq hap
  omega

/-! ## `getD` とペアの一致（接頭辞一致補題用） -/

private theorem getD_pair_lt (M : PS) (j : ℕ) (hj : j < Lng M) :
    M.getD j (0, 0) = (entry M 0 j, entry M 1 j) := by
  rw [getD_eq_getElem_idx M (0, 0) hj]
  simp [entry, List.getElem?_eq_getElem hj]

private theorem seg_getElem_lt (M : PS) (a b i : ℕ) (hi : i < Lng (seg M a b)) :
    (seg M a b)[i] = (entry M 0 (a + i), entry M 1 (a + i)) := by
  simp [seg, List.getElem_range']

/-! ## 最終枝の `le0`（`ljx_lastblock_le0` の逐語移植） -/

private theorem lastblock_le0_lt (R : PS) (hRT : TPS R) (hmono : monoT R = true)
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
  · rw [hfe]; exact le0_refl_lt R (Lng R - 1) (by omega)
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

/-! ## `RightAnces` の 1 段展開（`ljx_RA_unfold_mono` の役割） -/

/-- 単項でない `monoT` 接頭辞 `N`（`Pred N` 非零、幹頭 `Adm N (parent N 0 (Lng N-1)) = 0`）
での `RightNodes (Trans N)` の閉形式。`RightAncesAux_RTPS_equation` の 1 段展開＋
`RightAncesAux_eq_RightNodes_Trans` の橋で、a 値は根の単項 `[entry N 1 0]` に潰れる。 -/
private theorem RA_mono_unfold_lt (N : PS) (hNR : RTPS N) (hmono : monoT N = true)
    (hL3 : 2 < Lng N) (hpredNz : zeroT (Pred N) = false)
    (hAdm0 : Adm N (parent N 0 (Lng N - 1)) = 0) :
    RightNodes (Trans N) =
      (if transCondI N || transCondIII N || transCondV N || transCondVI N
       then [entry N 1 0, entry N 1 (Lng N - 1)]
       else [entry N 1 0, entry N 1 (parent N 0 (Lng N - 1)), entry N 1 (Lng N - 1)]) := by
  have hSeg00R : RTPS (seg N 0 0) := RTPS_initial_slice N 0 hNR (by omega)
  have hSeg00L : Lng (seg N 0 0) = 1 := by rw [length_seg]
  have hentry00 : entry (seg N 0 0) 1 0 = entry N 1 0 := by
    have := entry_seg N 0 0 1 0 (by rw [hSeg00L]; omega)
    simpa using this
  have hj1ne : ((Lng N - 1) == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  -- a 値: 根の単項に潰れる
  have ha : (if zeroT (seg N 0 0) then [0]
      else RightAncesAux (Lng N - 1) (seg N 0 0)) = [entry N 1 0] := by
    by_cases hz : zeroT (seg N 0 0) = true
    · rw [if_pos hz]
      have hz2 : entry (seg N 0 0) 1 0 = 0 := by
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
        exact hz.2
      rw [hentry00] at hz2
      rw [hz2]
    · rw [if_neg hz]
      have hfuel : Lng N - 1 = (Lng N - 2) + 1 := by omega
      rw [hfuel, RightAncesAux_RTPS_equation (Lng N - 2) (seg N 0 0) hSeg00R]
      have hne00 : ((seg N 0 0).getD 0 (0, 0) == (0, 0)) = false := by
        rw [getD_pair_lt (seg N 0 0) 0 (by rw [hSeg00L]; omega)]
        have hz2 : entry (seg N 0 0) 1 0 ≠ 0 := by
          intro he
          apply hz
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hSeg00L, he⟩
        simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq, not_and]
        intro _
        exact hz2
      simp only [hSeg00L, Nat.sub_self, beq_self_eq_true, if_true, hne00,
        Bool.false_eq_true, if_false, hentry00]
  -- 外側の 1 段展開
  have hEq : RightAncesAux ((Lng N - 1) + 1) N = RightNodes (Trans N) :=
    RightAncesAux_eq_RightNodes_Trans N ((Lng N - 1) + 1) hNR (by omega)
  rw [← hEq, RightAncesAux_RTPS_equation (Lng N - 1) N hNR]
  simp only [hj1ne, Bool.false_eq_true, if_false, hmono, if_true, hpredNz, hAdm0, ha,
    List.cons_append, List.nil_append]

/-! ## `RN_a0_lt_trmax_ldjb` の discharge（`ljx_RightNodes_a0_lt_trmax` の逐語移植） -/

/-- Isabelle `ljx_RightNodes_a0_lt_trmax` (layerB/pss_wip.thy:114847) の 1:1 移植。
`j_L < TrMax R_c` の場合、`RightNodes (Trans R_c)` の位置 1 は
`entry R_c 1 j_L`（非対角付き）か `entry R_c 1 j_L + 1`（cond V 側で対角排除）。 -/
theorem RN_a0_lt_trmax_holds : RN_a0_lt_trmax_ldjb := by
  intro M hR hmono hj1 hcond hBR hjpos hjlt
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _hE1z, _hNadm, _hParPos, hAdmLt, hParLt, _hCond, _hVI, _hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  have hb2 : Lng M - 2 ≤ Lng M - 1 := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hMT hlen hp0
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    condII_reach_lt M (Adm M (parent M 0 (Lng M - 1))) hR hlen hmk hab
  -- `R_c = tvx_Rc M` の性質（a0trmax と同型）
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
  -- 最終枝インデックス／`fn`／`jL` のバウンド
  have hBrpos : 0 < (Br (tvx_Rc M)).length := List.length_pos_of_ne_nil hBR
  have hBLlt : (Br (tvx_Rc M)).length - 1 < (Br (tvx_Rc M)).length := by omega
  have hFJ := FirstNodes_TrMax_Joints (tvx_Rc M) ((Br (tvx_Rc M)).length - 1) hRcT hmonoRc hBLlt
  have htmfn : TrMax (tvx_Rc M) < tvx_fn M := hFJ.2
  have nx0 : nextR (tvx_Rc M) 0 (tvx_jL M) (tvx_fn M) = true :=
    Joints_nextR_FirstNodes (tvx_Rc M) ((Br (tvx_Rc M)).length - 1) hRcT hmonoRc hBLlt
  have hnxrel : nextrel0 (tvx_Rc M) (tvx_jL M) (tvx_fn M) = true := by simpa [nextR] using nx0
  have hnxrel' := hnxrel
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnxrel'
  have hjLfn : tvx_jL M < tvx_fn M := hnxrel'.1.1.2
  have hfnlt : tvx_fn M < Lng (tvx_Rc M) := hnxrel'.1.1.1.2
  have hfnpos : 0 < tvx_fn M := by omega
  have hfn2 : 2 ≤ tvx_fn M := by omega
  have hjLfn1 : tvx_jL M + 1 < tvx_fn M := by omega
  -- `N = seg R_c 0 fn` の基本量
  have hNR : RTPS (seg (tvx_Rc M) 0 (tvx_fn M)) :=
    RTPS_initial_slice (tvx_Rc M) (tvx_fn M) hRcRT (by omega)
  have hNT : TPS (seg (tvx_Rc M) 0 (tvx_fn M)) := RTPS_TPS _ hNR
  have hNLen : Lng (seg (tvx_Rc M) 0 (tvx_fn M)) = tvx_fn M + 1 := by simp [length_seg]
  have hLN1 : Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1 = tvx_fn M := by simp [hNLen]
  have entN : ∀ i j, j ≤ tvx_fn M →
      entry (seg (tvx_Rc M) 0 (tvx_fn M)) i j = entry (tvx_Rc M) i j := by
    intro i j hj
    have hjLng : j < Lng (seg (tvx_Rc M) 0 (tvx_fn M)) := by rw [hNLen]; omega
    have := entry_seg (tvx_Rc M) 0 (tvx_fn M) i j hjLng
    simpa using this
  have eN0 : entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1 0 = entry (tvx_Rc M) 1 0 :=
    entN 1 0 (by omega)
  have eNfn : entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1 (tvx_fn M) = entry (tvx_Rc M) 1 (tvx_fn M) :=
    entN 1 (tvx_fn M) le_rfl
  have eNjL : entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1 (tvx_jL M) = entry (tvx_Rc M) 1 (tvx_jL M) :=
    entN 1 (tvx_jL M) (by omega)
  -- `TrMax N = TrMax R_c`（adm-transport 回避）
  have hagree : ∀ j, j ≤ tvx_fn M →
      (tvx_Rc M).getD j (0, 0) = (seg (tvx_Rc M) 0 (tvx_fn M)).getD j (0, 0) := by
    intro j hj
    rw [getD_pair_lt (tvx_Rc M) j (by omega),
      getD_pair_lt (seg (tvx_Rc M) 0 (tvx_fn M)) j (by rw [hNLen]; omega),
      entN 0 j hj, entN 1 j hj]
  have hTrMaxN : TrMax (seg (tvx_Rc M) 0 (tvx_fn M)) = TrMax (tvx_Rc M) :=
    (TrMax_eq_of_prefix_agree_sym_68 (tvx_Rc M) (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_fn M)
      hRcT hNT hagree hfnlt (by rw [hNLen]; omega) (by omega)
      (nextR1_TrMax_fail_lt (tvx_Rc M) hRcT)).symm
  -- `parent N 0 fn = jL`
  have nxN : nextrel0 (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_jL M) (tvx_fn M) = true :=
    nextrel0_seg0_lt (tvx_Rc M) (tvx_jL M) (tvx_fn M) (tvx_fn M) hnxrel le_rfl hfnlt
  have pN : parent (seg (tvx_Rc M) 0 (tvx_fn M)) 0 (tvx_fn M) = tvx_jL M := by
    have hpR : nextR (seg (tvx_Rc M) 0 (tvx_fn M)) 0 (tvx_jL M) (tvx_fn M) = true := by
      simpa [nextR] using nxN
    exact parent_eq_of_nextR0 (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_jL M) (tvx_fn M) hpR
  have hlpN : parent (seg (tvx_Rc M) 0 (tvx_fn M)) 0
      (Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1) = tvx_jL M := by rw [hLN1]; exact pN
  -- `adm N k = false`（`1 ≤ k ≤ jL`）→ `Adm N jL = 0`
  have hadmNjL : adm (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_jL M) = false :=
    trunk_interior_nadm_lt (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_jL M) hNT hjpos
      (by rw [hTrMaxN]; exact hjlt)
  have hAdmN : Adm (seg (tvx_Rc M) 0 (tvx_fn M)) (tvx_jL M) = 0 := by
    apply Adm_eq_zero_lt
    intro k hk1 hk2
    exact trunk_interior_nadm_lt (seg (tvx_Rc M) 0 (tvx_fn M)) k hNT (by omega)
      (by rw [hTrMaxN]; omega)
  have hAdm0 : Adm (seg (tvx_Rc M) 0 (tvx_fn M))
      (parent (seg (tvx_Rc M) 0 (tvx_fn M)) 0 (Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1)) = 0 := by
    rw [hlpN]; exact hAdmN
  -- `monoT N`（`0 → j_L → fn` の `le0`）と `Pred N` 非零
  have hle0Rc0fn : leR (tvx_Rc M) 0 0 (tvx_fn M) = true :=
    row0_transitive (tvx_Rc M) 0 (tvx_jL M) (tvx_fn M) hRcT
      (trunk_le0 (tvx_Rc M) 0 (tvx_jL M) hRcT (Nat.zero_le _) (le_of_lt hjlt))
      (nextR0_leR (tvx_Rc M) (tvx_jL M) (tvx_fn M) nx0)
  have hmonoN : monoT (seg (tvx_Rc M) 0 (tvx_fn M)) = true :=
    mono_ancestor_slice (tvx_Rc M) 0 (tvx_fn M) hRcT hfnpos hle0Rc0fn
  have hLPredN : Lng (Pred (seg (tvx_Rc M) 0 (tvx_fn M))) = tvx_fn M := by
    rw [length_Pred (seg (tvx_Rc M) 0 (tvx_fn M)) (by rw [hNLen]; omega), hLN1]
  have hpredNz : zeroT (Pred (seg (tvx_Rc M) 0 (tvx_fn M))) = false := by
    have hne1 : (Lng (Pred (seg (tvx_Rc M) 0 (tvx_fn M))) == 1) = false :=
      beq_eq_false_iff_ne.mpr (by rw [hLPredN]; omega)
    simp [zeroT, hne1]
  -- `RightNodes (Trans N)` の 1 段展開（cond I/III/VI は排除）
  have hRAN := RA_mono_unfold_lt (seg (tvx_Rc M) 0 (tvx_fn M)) hNR hmonoN
    (by rw [hNLen]; omega) hpredNz hAdm0
  have hnotI : transCondI (seg (tvx_Rc M) 0 (tvx_fn M)) = false := by
    simp only [transCondI, lastParent, lastIdx, hLN1, pN, hadmNjL, Bool.and_false]
  have hnotIII : transCondIII (seg (tvx_Rc M) 0 (tvx_fn M)) = false := by
    simp only [transCondIII, lastParent, lastIdx, hLN1, pN, hadmNjL, Bool.and_false]
  have hnotVI : transCondVI (seg (tvx_Rc M) 0 (tvx_fn M)) = false := by
    have hbne : (tvx_jL M + 1 == tvx_fn M) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [transCondVI, lastParent, lastIdx, hLN1, pN, hbne, Bool.and_false]
  have hguard : (transCondI (seg (tvx_Rc M) 0 (tvx_fn M))
      || transCondIII (seg (tvx_Rc M) 0 (tvx_fn M))
      || transCondV (seg (tvx_Rc M) 0 (tvx_fn M))
      || transCondVI (seg (tvx_Rc M) 0 (tvx_fn M)))
      = transCondV (seg (tvx_Rc M) 0 (tvx_fn M)) := by
    rw [hnotI, hnotIII, hnotVI]; simp
  rw [hguard] at hRAN
  -- `parent R_c 0 fn = jL` と `adm R_c fn`
  have hpar : parent (tvx_Rc M) 0 (tvx_fn M) = tvx_jL M :=
    parent_eq_of_nextR0 (tvx_Rc M) (tvx_jL M) (tvx_fn M) nx0
  have hadmfn : adm (tvx_Rc M) (tvx_fn M) = true := by
    by_contra hcon
    have hadmf : adm (tvx_Rc M) (tvx_fn M) = false := by
      simp only [Bool.not_eq_true] at hcon; exact hcon
    have hnadmt : nadm (tvx_Rc M) (tvx_fn M) = true := by
      have h1 : adm (tvx_Rc M) (tvx_fn M) = !nadm (tvx_Rc M) (tvx_fn M) := rfl
      rw [h1] at hadmf; simpa using hadmf
    have hfnltd : decide (Lng (tvx_Rc M) < tvx_fn M) = false := by
      simp only [decide_eq_false_iff_not]; omega
    have hconj : (nextR (tvx_Rc M) 1 (tvx_fn M - 1) (tvx_fn M)
        && nextR (tvx_Rc M) 1 (tvx_fn M) (tvx_fn M + 1)) = true := by
      have h2 := hnadmt
      unfold nadm at h2
      rw [hfnltd] at h2
      simpa using h2
    have hnx1 : nextR (tvx_Rc M) 1 (tvx_fn M - 1) (tvx_fn M) = true := by
      have hc := hconj
      simp only [Bool.and_eq_true] at hc
      exact hc.1
    have hnxrel1 : nextrel1 (tvx_Rc M) (tvx_fn M - 1) (tvx_fn M) = true := by
      simpa [nextR] using hnx1
    have hle0h : le0 (tvx_Rc M) (tvx_fn M - 1) (tvx_fn M) = true := by
      have hh := hnxrel1
      simp only [nextrel1, Bool.and_eq_true] at hh
      exact hh.1.2
    have hvalley := row0_valley_general_lt (tvx_Rc M) (tvx_fn M) (tvx_fn M - 1)
      (by rw [hpar]; omega) hle0h
    omega
  have hle0fn : leR (tvx_Rc M) 0 (tvx_fn M) (Lng (tvx_Rc M) - 1) = true :=
    lastblock_le0_lt (tvx_Rc M) hRcT hmonoRc hBR
  have hmkfn : Marked (tvx_Rc M) (tvx_fn M) := ⟨hRcT, hadmfn, hle0fn⟩
  -- splice: `RightNodes (Trans R_c) = RightNodes (Trans N) @ a1`
  have hRNsplit : ∃ a1, RightNodes (Trans (tvx_Rc M))
      = RightNodes (Trans (seg (tvx_Rc M) 0 (tvx_fn M))) ++ a1 := by
    by_cases hfe : tvx_fn M = Lng (tvx_Rc M) - 1
    · have hNeqRc : seg (tvx_Rc M) 0 (tvx_fn M) = tvx_Rc M := by
        have hlen : (seg (tvx_Rc M) 0 (tvx_fn M)).length = (tvx_Rc M).length := by
          show Lng (seg (tvx_Rc M) 0 (tvx_fn M)) = Lng (tvx_Rc M)
          rw [length_seg, hfe]; omega
        apply List.ext_getElem hlen
        intro j h1 h2
        have hjseg : j < Lng (seg (tvx_Rc M) 0 (tvx_fn M)) := h1
        have hjL : j < Lng (tvx_Rc M) := h2
        rw [seg_getElem_lt (tvx_Rc M) 0 (tvx_fn M) j hjseg, Nat.zero_add,
          ← getD_eq_getElem_idx (tvx_Rc M) (0, 0) hjL, getD_pair_lt (tvx_Rc M) j hjL]
      exact ⟨[], by rw [hNeqRc, List.append_nil]⟩
    · have hfnlt1 : tvx_fn M < Lng (tvx_Rc M) - 1 := by omega
      obtain ⟨a0, a1, hTM, hTS, _⟩ :=
        m_7_4_RightNodes_Mark (tvx_Rc M) (tvx_fn M) hmkfn hRcRT hfnpos hfnlt1
      exact ⟨a1, by rw [hTM, hTS]⟩
  obtain ⟨a1, hsplit⟩ := hRNsplit
  by_cases hV : transCondV (seg (tvx_Rc M) 0 (tvx_fn M)) = true
  · -- cond V: 位置 1 = `entry R_c 1 j_L + 1`（右選言）
    rw [if_pos hV, hLN1, eN0, eNfn] at hRAN
    rw [hRAN] at hsplit
    have hvval : entry (tvx_Rc M) 1 (tvx_fn M) = entry (tvx_Rc M) 1 (tvx_jL M) + 1 := by
      have hh := hV
      simp only [transCondV, lastParent, lastIdx, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hh
      obtain ⟨⟨_, hc2⟩, _⟩ := hh
      rw [hlpN, hLN1, eNjL, eNfn] at hc2
      omega
    right
    refine ⟨a1, ?_⟩
    rw [hsplit]; simp only [List.cons_append, List.nil_append, hvval]
  · -- else: 位置 1 = `entry R_c 1 j_L`（非対角、左選言）
    rw [if_neg hV, hlpN, hLN1, eN0, eNjL, eNfn] at hRAN
    rw [hRAN] at hsplit
    have hneq : entry (tvx_Rc M) 1 (tvx_fn M) ≠ entry (tvx_Rc M) 0 (tvx_fn M) := by
      intro hdg
      have hp0fn : hasParent (tvx_Rc M) 0 (tvx_fn M) = true :=
        mono_hasParent_row0 (tvx_Rc M) hRcT hmonoRc (tvx_fn M) hfnpos hfnlt
      have hcondA := RedCondA_apply (tvx_Rc M) hcondARc 0 (tvx_fn M) (by omega) hfnlt hp0fn
      rw [hpar] at hcondA
      have hoff := trunk_entries_offset (tvx_Rc M) hRcT hcondARc (tvx_jL M) (le_of_lt hjlt)
      have hv1 : entry (tvx_Rc M) 1 (tvx_fn M) = entry (tvx_Rc M) 1 (tvx_jL M) + 1 := by
        rw [hdg, ← hcondA, hoff.1, hdiag00, ← hoff.2]
      have hc1 : 0 < entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1
          (Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1) := by
        rw [hLN1, eNfn, hv1]; omega
      have hc2 : entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1
          (parent (seg (tvx_Rc M) 0 (tvx_fn M)) 0 (Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1)) + 1
          = entry (seg (tvx_Rc M) 0 (tvx_fn M)) 1 (Lng (seg (tvx_Rc M) 0 (tvx_fn M)) - 1) := by
        rw [hlpN, hLN1, eNjL, eNfn, hv1]
      have hVtrue : transCondV (seg (tvx_Rc M) 0 (tvx_fn M)) = true := by
        simp only [transCondV, lastParent, lastIdx, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq]
        refine ⟨⟨hc1, hc2⟩, ?_⟩
        rw [hlpN, hLN1]; exact hjLfn1
      exact hV hVtrue
    left
    refine ⟨entry (tvx_Rc M) 1 (tvx_fn M) :: a1, ?_, hneq⟩
    rw [hsplit]; simp only [List.cons_append, List.nil_append]

#print axioms RN_a0_lt_trmax_holds

/-! ## 5 本の readout をすべて配線: `TV_LDJB` の無条件組み立て -/

/-- `TV_LDJB`（«8».«8.3-condII-masterCF-port»:148）を 5 本の readout をすべて閉じて無条件に
充足する。`RN_ldj_pj_holds` / `TVX_pos1ldj_holds`（readouts）、`RN_a0_trmax_holds`
（a0trmax）、`RN_a0_lt_trmax_holds`（本ファイル）、`TVX_dstrict_ldjb_holds`（condV-VE-wnx）。 -/
theorem tv_ldjb_holds : TV_LDJB :=
  TV_LDJB_of_readouts RN_ldj_pj_holds RN_a0_trmax_holds RN_a0_lt_trmax_holds
    TVX_pos1ldj_holds TVX_dstrict_ldjb_holds

#print axioms tv_ldjb_holds

end PSS
