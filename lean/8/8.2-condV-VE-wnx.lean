import «8».«8.3-condII-LDJB»
import «7».«7.3-Trans-IncrFirst-Red»
import «7».«7.3-Trans-welldefined»
import «8».«8.6-Trans-Red-funpow-IncrFirst»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.2 条件(V) VE 周辺の portable perimeter（`wnx_*` bricks）

## 原文 / Isabelle 対応

`CondII` の `NotLdj` / `Boundary` / `LDJB` 脚が共有する «8».§8.2 の shared bricks を
移植する（VE body 本体 `vcx_VE_all` / `vg2x_VE34` は本ファイルの範囲外）。

| Isabelle | 位置 | 本ファイル | 状態 |
|---|---|---|---|
| `repr_entry1_shift_gen` | layerB/pss_wip.thy:12828 | `repr_entry1_shift_gen`（PUBLIC） | ✅ 無条件 |
| `wnx_run_entries` | layerB/pss_wip.thy:80739 | ⚠️ **既存**（«8».«8.7-otpred-brickC0»）— 重複回避で非宣言 | ✅ 済 |
| `wnx_seg_transport` | layerB/pss_wip.thy:80767 | `wnx_seg_transport_W1/_W2/_W3`（PUBLIC） | ✅ 無条件 |
| `c2sx_reach`(1)(2) | layerB/pss_wip.thy:87666 | `c2sx_reach_leab/_leam`（PUBLIC） | ✅ 無条件 |
| `tvx_d_lt_TrMax` | layerB/pss_wip.thy:110442 | `TVX_dstrict_ldjb_holds`（house pattern） | ✅ 無条件 |

## 依存（すべて COMMITTED 緑）

* «8».«8.3-condII-LDJB» — `TVX_dstrict_ldjb` Prop・`condII_reach_r3`（= leab 脚）・
  `condII_host_basic_holds`・`tvx_Rc`/`tvx_d`・`standard_slice_Red_strongmono`。
* «7».«7.3-Trans-IncrFirst-Red» — `Trans_Red`（W1）。
* «8».«8.6-Trans-Red-funpow-IncrFirst» — `Trans_funpow_IncrFirst`（W2）。
* «6».«6.6-ancestor-slice-Red-IncrFirst» — `ancestor_slice_Red_IncrFirst`。
* «6».«6.3-adm-slice» — `adm_slice`。
* «6».«6.8-standard-slice-Br-descending» — `seg_of_seg_68`。

## 状態

✅ 5 target 全達成（sorry 0、axioms = [propext, Classical.choice, Quot.sound]）。
`TVX_dstrict_ldjb_holds` は «8».«8.3-condII-LDJB» の名前付き残差 `TVX_dstrict_ldjb`
を house pattern で drop-in 充足する。target(2) `wnx_run_entries` は既存資産のため非宣言。
-/

namespace PSS

/-! ## 補助（private, 接尾辞 `_vw`） -/

/-- 切片 `seg M m b`（`m < b`）は非空。 -/
private theorem seg_TPS_vw (M : PS) (m b : ℕ) (hmb : m < b) :
    TPS (seg M m b) := by
  have h : 0 < Lng (seg M m b) := by simp only [length_seg]; omega
  exact List.ne_nil_of_length_pos h

/-! ## (1) `repr_entry1_shift_gen`（PUBLIC）

Isabelle `repr_entry1_shift_gen`（pss_wip.thy:12828）: 簡約後方切片の行 1 entry は
シフトのみ（`entry (Red (seg M m b)) 1 i = entry M 1 (m + i)`）。8.1-part4-trans の
private twin（`part4_TransN_engine_pt` 内 `hE1`）を公開・一般化したもの。 -/
theorem repr_entry1_shift_gen (M : PS) (m b i : ℕ)
    (hMR : RTPS M) (hmb : m < b) (hbL : b ≤ Lng M - 1)
    (hleM : leR M 0 m b = true)
    (hil : i < Lng (Red (seg M m b))) :
    entry (Red (seg M m b)) 1 i = entry M 1 (m + i) := by
  have hfacts := ancestor_slice_Red_IncrFirst M m b hMR hmb hbL hleM
  have hIF : seg M m b
      = IncrFirstN (entry M 0 m - entry M 1 m) (Red (seg M m b)) := hfacts.2.2
  have hST : TPS (seg M m b) := seg_TPS_vw M m b hmb
  have hLR : Lng (Red (seg M m b)) = Lng (seg M m b) :=
    Lng_Red_invariance (seg M m b) hST
  have iS : i < Lng (seg M m b) := hLR ▸ hil
  have eN : entry (seg M m b) 1 i = entry (Red (seg M m b)) 1 i := by
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_one _ (Red (seg M m b)) i
  have eM : entry (seg M m b) 1 i = entry M 1 (m + i) := entry_seg M m b 1 i iS
  exact eN.symm.trans eM

#print axioms repr_entry1_shift_gen

/-! ## (3) `wnx_seg_transport`（PUBLIC）

Isabelle `wnx_seg_transport`（pss_wip.thy:80767）は 3 結論:
* W1: `Trans (seg M a b) = Trans (Red (seg M a b))`（`Trans_Red` の easy half）。
* W3: `Lng (Red (seg M a b)) - 1 = b - a`。
* W2: `Trans (seg M (a + m) b)
        = Trans (seg (Red (seg M a b)) m (Lng (Red (seg M a b)) - 1))`
  （peeled-slice を `Trans_funpow_IncrFirst` で剥ぐ harder half）。 -/

/-- W1: `Trans (seg M a b) = Trans (Red (seg M a b))`（`Trans_Red`）。 -/
theorem wnx_seg_transport_W1 (M : PS) (a b : ℕ) (hab : a < b) :
    Trans (seg M a b) = Trans (Red (seg M a b)) :=
  Trans_Red (seg M a b) (seg_TPS_vw M a b hab)

/-- W3: 簡約切片の長さ。 -/
theorem wnx_seg_transport_W3 (M : PS) (a b : ℕ) (hab : a < b) :
    Lng (Red (seg M a b)) - 1 = b - a := by
  have hST : TPS (seg M a b) := seg_TPS_vw M a b hab
  have hLR : Lng (Red (seg M a b)) = Lng (seg M a b) :=
    Lng_Red_invariance (seg M a b) hST
  rw [hLR]; simp only [length_seg]; omega

#print axioms wnx_seg_transport_W1
#print axioms wnx_seg_transport_W3

/-- `seg` は行 0 のシフト `IncrFirstN` と可換（`b < Lng X` 範囲）。8.3-condII-TrunkLeg の
private `seg_IncrFirstN_tl` と同型。 -/
private theorem seg_IncrFirstN_vw (sh : ℕ) (X : PS) (a b : ℕ) (hb : b < Lng X) :
    seg (IncrFirstN sh X) a b = IncrFirstN sh (seg X a b) := by
  apply List.ext_getElem
  · simp [IncrFirstN_eq_map]
  · intro i h1 h2
    have hib : i < b + 1 - a := by simpa using h1
    have hiX : a + i < Lng X := by omega
    have h2' : i < Lng (seg X a b) := by simp only [length_seg]; omega
    rw [seg_getElem_68 (IncrFirstN sh X) a b i h1,
      entry_IncrFirstN_zero sh X (a + i) hiX, entry_IncrFirstN_one sh X (a + i)]
    simp only [IncrFirstN_eq_map, List.getElem_map]
    rw [seg_getElem_68 X a b i h2']

/-- W2（`wnx_seg_transport` の harder half, pss_wip.thy:80767 の結論(2)）: 剥ぎ取り切片の
`Trans` は `Trans_funpow_IncrFirst`（8.6）で簡約切片へ落ちる。 -/
theorem wnx_seg_transport_W2 (M : PS) (a b m : ℕ) (hMR : RTPS M)
    (hab : a < b) (hbL : b ≤ Lng M - 1) (hleab : leR M 0 a b = true)
    (hamb : a + m < b) (hleam : le0 M (a + m) b = true) :
    Trans (seg M (a + m) b)
      = Trans (seg (Red (seg M a b)) m (Lng (Red (seg M a b)) - 1)) := by
  have hMT : TPS M := RTPS_TPS M hMR
  have hbLng : b < Lng M := by omega
  have hST : TPS (seg M a b) := seg_TPS_vw M a b hab
  have hfacts := ancestor_slice_Red_IncrFirst M a b hMR hab hbL hleab
  have hRedR : Red (Red (seg M a b)) = Red (seg M a b) := hfacts.1
  have hIF : seg M a b
      = IncrFirstN (entry M 0 a - entry M 1 a) (Red (seg M a b)) := hfacts.2.2
  have hLRval : Lng (Red (seg M a b)) = b + 1 - a := by
    rw [Lng_Red_invariance (seg M a b) hST, length_seg]
  have hLRm1 : Lng (Red (seg M a b)) - 1 = b - a := by rw [hLRval]; omega
  have hRT : TPS (Red (seg M a b)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (Red (seg M a b))
    rw [hLRval]; omega
  have hRRT : RTPS (Red (seg M a b)) := by
    show reduced (Red (seg M a b)) = true
    have hne : Red (seg M a b) ≠ [] := hRT
    simp [reduced, hne, hRedR]
  -- geometry: peeled slice = slice-of-slice
  have geom : seg M (a + m) b = seg (seg M a b) m (b - a) := by
    have e : a + (b - a) = b := by omega
    rw [seg_of_seg_68 M a b m (b - a) (by omega) (le_refl (b - a)), e]
  -- seg commutes with IncrFirst
  have hbaLR : b - a < Lng (Red (seg M a b)) := by rw [hLRval]; omega
  have segB : seg (seg M a b) m (b - a)
      = IncrFirstN (entry M 0 a - entry M 1 a)
          (seg (Red (seg M a b)) m (b - a)) := by
    conv_lhs => rw [hIF]
    rw [seg_IncrFirstN_vw (entry M 0 a - entry M 1 a) (Red (seg M a b)) m (b - a) hbaLR]
  -- reach inside R
  have hmba : m < b - a := by omega
  have hbaS : b - a < Lng (seg M a b) := by rw [length_seg]; omega
  have hmS : m < Lng (seg M a b) := by rw [length_seg]; omega
  have hleRseg : leR (seg M a b) 0 m (b - a) = true := by
    rw [leR0_seg_adm M a b m (b - a) (by omega) hbLng hmS hbaS]
    have e : a + (b - a) = b := by omega
    rw [e]
    simpa [leR] using hleam
  have hleFun : leR (seg M a b) = leR (Red (seg M a b)) := by
    conv_lhs => rw [hIF]
    rw [leR_IncrFirstN]
  have hleR : leR (Red (seg M a b)) 0 m (b - a) = true := by
    rw [← hleFun]; exact hleRseg
  -- base facts for Trans_funpow_IncrFirst
  have hbaseT : TPS (seg (Red (seg M a b)) m (b - a)) :=
    seg_TPS_vw (Red (seg M a b)) m (b - a) hmba
  have hfacts2 := ancestor_slice_Red_IncrFirst (Red (seg M a b)) m (b - a) hRRT hmba
    (le_of_eq hLRm1.symm) hleR
  have hRedR2 : Red (Red (seg (Red (seg M a b)) m (b - a)))
      = Red (seg (Red (seg M a b)) m (b - a)) := hfacts2.1
  have hbaseRedT : TPS (Red (seg (Red (seg M a b)) m (b - a))) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (Red (seg (Red (seg M a b)) m (b - a)))
    rw [Lng_Red_invariance _ hbaseT, length_seg]; omega
  have hRbaseRT : RTPS (Red (seg (Red (seg M a b)) m (b - a))) := by
    show reduced (Red (seg (Red (seg M a b)) m (b - a))) = true
    have hne : Red (seg (Red (seg M a b)) m (b - a)) ≠ [] := hbaseRedT
    simp [reduced, hne, hRedR2]
  calc Trans (seg M (a + m) b)
      = Trans (seg (seg M a b) m (b - a)) := by rw [geom]
    _ = Trans (IncrFirstN (entry M 0 a - entry M 1 a)
          (seg (Red (seg M a b)) m (b - a))) := by rw [segB]
    _ = Trans (seg (Red (seg M a b)) m (b - a)) :=
          Trans_funpow_IncrFirst (seg (Red (seg M a b)) m (b - a))
            (entry M 0 a - entry M 1 a) hbaseT hRbaseRT
    _ = Trans (seg (Red (seg M a b)) m (Lng (Red (seg M a b)) - 1)) := by rw [hLRm1]

#print axioms wnx_seg_transport_W2

/-! ## (5)+(4) `c2sx_reach` leab と `tvx_d_lt_TrMax` → `TVX_dstrict_ldjb`

`tvx_d_lt_TrMax`（Isabelle pss_wip.thy:110442）は非許容 run の長さ `d` が幹長
`TrMax R_c` より真に短いことを示す。到達性 leab は `condII_reach_r3`（R3LE 公開）を
再利用し、run の非許容性を `R_c` へ transport（`tvx_run_nadm_Rc`）してから
`le_TrMax_intro_wd` で `d + 1 ≤ TrMax R_c` を得る。 -/

/-- Isabelle `wnx_run_nadm`（pss_wip.thy:80700）: run 上の点は `M` で非許容。
（8.3-condII-step の private `run_nadm_c2s` の逐語複製；private は module 跨ぎ不可。） -/
private theorem run_nadm_vw (M : PS) (j0 s : ℕ) (_h0 : adm M j0 = false)
    (lo : Adm M j0 < s) (hi : s ≤ j0) : adm M s = false := by
  by_contra h
  have h' : adm M s = true := by simpa using h
  have hmax := Adm_max M s j0 h' hi
  omega

/-- `adm` は行 0 のシフト `IncrFirstN` で不変（Isabelle `adm_funpow_IncrFirst_eq`）。 -/
private theorem adm_IncrFirstN_vw (n : ℕ) (X : PS) (j : ℕ) :
    adm (IncrFirstN n X) j = adm X j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

/-- 非許容点（`adm R s = false`、かつ添字が範囲内）は行 1 の隣接辺を両側に与える。
（`nadm` の定義展開。） -/
private theorem nadm_edge_vw (R : PS) (s : ℕ) (h0 : adm R s = false) (hs : ¬ Lng R < s) :
    nextR R 1 (s - 1) s = true ∧ nextR R 1 s (s + 1) = true := by
  have hna : nadm R s = true := by
    have : adm R s = false := h0
    simpa [adm] using this
  rw [nadm] at hna
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hna
  rcases hna with h | h
  · exact absurd h hs
  · exact h

/-- Isabelle `tvx_d_lt_TrMax` の有限性コア（`TrMax` 集合の Max 論法を
`le_TrMax_intro_wd` に置換）。 -/
private theorem d_lt_TrMax_core_vw (Rc : PS) (d : ℕ)
    (hRcT : TPS Rc) (hdpos : 0 < d) (hddlt : d < Lng Rc - 1)
    (hnadm : ∀ k, 1 ≤ k → k ≤ d → adm Rc k = false) :
    d < TrMax Rc := by
  have steps : ∀ p, p ≤ d → nextR Rc 1 p (p + 1) = true := by
    intro p hp
    by_cases hpd : p = d
    · subst hpd
      have hadm : adm Rc p = false := hnadm p (by omega) (le_refl p)
      have hs : ¬ Lng Rc < p := by omega
      exact (nadm_edge_vw Rc p hadm hs).2
    · have hplt : p < d := by omega
      have hadm : adm Rc (p + 1) = false := hnadm (p + 1) (by omega) (by omega)
      have hs : ¬ Lng Rc < p + 1 := by omega
      have h := (nadm_edge_vw Rc (p + 1) hadm hs).1
      simpa using h
  have hall : ∀ j, j < d + 1 → nextR Rc 1 j (j + 1) = true := fun j hj => steps j (by omega)
  have hge : d + 1 ≤ TrMax Rc := le_TrMax_intro_wd Rc (d + 1) hRcT hall
  omega

/-- (5) `c2sx_reach`(1) leab（PUBLIC）: `leR M 0 (Adm M j₀) (Lng M - 2)`。
`condII_reach_r3`（R3LE）＋`Marked_Pred_Adm` の合成。 -/
theorem c2sx_reach_leab (M : PS) (hMR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hII : transCondII M = true) :
    leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true := by
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hMR hmono hj1 hII
  have hMT : TPS M := RTPS_TPS M hMR
  have hL : 1 < Lng M := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hMT hL hp0
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  exact condII_reach_r3 M (Adm M (parent M 0 (Lng M - 1))) hMR hL hmk hab

#print axioms c2sx_reach_leab

/-- (5) `c2sx_reach`(2) leam（PUBLIC）: `le0 M j₀ (Lng M - 2)`。最終節の親 `j₀` から
その直前 `Lng M - 2` への行 0 ブロック到達（`parent_block_le0_68`）。 -/
theorem c2sx_reach_leam (M : PS) (hMR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hII : transCondII M = true) :
    le0 M (parent M 0 (Lng M - 1)) (Lng M - 2) = true := by
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hMR hmono hj1 hII
  have hMT : TPS M := RTPS_TPS M hMR
  have hnext : nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hs : (Lng M - 2) - parent M 0 (Lng M - 1)
      < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hblk := parent_block_le0_68 M (parent M 0 (Lng M - 1)) (Lng M - 1)
    ((Lng M - 2) - parent M 0 (Lng M - 1)) hMT hnext hs
  have hidx : parent M 0 (Lng M - 1) + ((Lng M - 2) - parent M 0 (Lng M - 1))
      = Lng M - 2 := by omega
  rw [hidx] at hblk
  exact hblk

#print axioms c2sx_reach_leam

/-- Isabelle `tvx_run_nadm_Rc`（pss_wip.thy:110390）: run 上の各点は簡約祖先切片
`R_c` でも非許容。`adm_slice`（6.3）＋`ancestor_slice_Red_IncrFirst`（6.6）で transport。 -/
private theorem tvx_run_nadm_Rc_vw (M : PS) (k : ℕ)
    (hMR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hII : transCondII M = true)
    (hk1 : 1 ≤ k)
    (hk2 : k ≤ parent M 0 (Lng M - 1) - Adm M (parent M 0 (Lng M - 1))) :
    adm (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))) k = false := by
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hMR hmono hj1 hII
  have hMT : TPS M := RTPS_TPS M hMR
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    c2sx_reach_leab M hMR hmono hj1 hII
  set j0 := parent M 0 (Lng M - 1) with hj0
  set jm1 := Adm M j0 with hjm1
  have hjm1le : jm1 ≤ j0 := by rw [hjm1]; exact Adm_le M j0
  have hlo : Adm M j0 < jm1 + k := by rw [← hjm1]; omega
  have hhi : jm1 + k ≤ j0 := by omega
  have hnadmM : adm M (jm1 + k) = false := run_nadm_vw M j0 (jm1 + k) hNadm hlo hhi
  have hsj : jm1 ≤ jm1 + k := by omega
  have hje : jm1 + k ≤ Lng M - 2 := by omega
  have he : Lng M - 2 ≤ Lng M - 1 := by omega
  have hiff := adm_slice M jm1 (jm1 + k) (Lng M - 2) hMT hsj hje he
  have hnotL : ¬ (adm M (jm1 + k) = true ∨ jm1 = jm1 + k ∨ jm1 + k = Lng M - 2) := by
    rintro (h | h | h)
    · rw [hnadmM] at h; exact Bool.noConfusion h
    · omega
    · omega
  have hsegfalse : adm (seg M jm1 (Lng M - 2)) ((jm1 + k) - jm1) = false := by
    have hnr : ¬ (adm (seg M jm1 (Lng M - 2)) ((jm1 + k) - jm1) = true) :=
      fun hr => hnotL (hiff.mpr hr)
    simpa using hnr
  have hkk : (jm1 + k) - jm1 = k := by omega
  rw [hkk] at hsegfalse
  have hfacts := ancestor_slice_Red_IncrFirst M jm1 (Lng M - 2) hMR (by omega) (by omega) leab
  have hIF : seg M jm1 (Lng M - 2)
      = IncrFirstN (entry M 0 jm1 - entry M 1 jm1)
          (Red (seg M jm1 (Lng M - 2))) := hfacts.2.2
  rw [hIF, adm_IncrFirstN_vw] at hsegfalse
  exact hsegfalse

/-- (4) `TVX_dstrict_ldjb`（«8».«8.3-condII-LDJB»:121）を house pattern で discharge。
Isabelle `tvx_d_lt_TrMax`（pss_wip.thy:110442）の 1:1 移植。 -/
theorem TVX_dstrict_ldjb_holds : TVX_dstrict_ldjb := by
  intro M hMR hmono hj1 hII
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hMR hmono hj1 hII
  have hMT : TPS M := RTPS_TPS M hMR
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    c2sx_reach_leab M hMR hmono hj1 hII
  have hsegT : TPS (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) := by
    apply seg_TPS_vw; omega
  have hLRc : Lng (tvx_Rc M)
      = (Lng M - 2) + 1 - Adm M (parent M 0 (Lng M - 1)) := by
    unfold tvx_Rc
    rw [Lng_Red_invariance _ hsegT, length_seg]
  have hddlt : tvx_d M < Lng (tvx_Rc M) - 1 := by
    unfold tvx_d; rw [hLRc]; omega
  have hdpos : 0 < tvx_d M := by unfold tvx_d; omega
  have hRcT : TPS (tvx_Rc M) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (tvx_Rc M)
    rw [hLRc]; omega
  have hnadm : ∀ k, 1 ≤ k → k ≤ tvx_d M → adm (tvx_Rc M) k = false := by
    intro k hk1 hk2
    unfold tvx_d at hk2
    have h := tvx_run_nadm_Rc_vw M k hMR hmono hj1 hII hk1 hk2
    unfold tvx_Rc
    exact h
  exact d_lt_TrMax_core_vw (tvx_Rc M) (tvx_d M) hRcT hdpos hddlt hnadm

#print axioms TVX_dstrict_ldjb_holds

/-! ## (2) `wnx_run_entries` — 既存資産（重複回避）

Isabelle `wnx_run_entries`（pss_wip.thy:80739）は **既に «8».«8.7-otpred-brickC0» で
公開移植済み**（`theorem wnx_run_entries (M) (hR) (j0 t) (jL) (nadm0) (ht) : …`）。
同名の再宣言は co-import 時にヘッダを毒するため、本ファイルでは宣言しない
（内容 grep で既存を確認済み ＝ 資産盲点回避）。run-step の行 0・行 1 補題
（`run_nadm_vw` / `nadm_edge_vw`）は本ファイル内で再利用している。 -/

end PSS
