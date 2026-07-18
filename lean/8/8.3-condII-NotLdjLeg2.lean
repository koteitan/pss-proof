import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-NotLdjLeg»
import «8».«8.3-condII-TrunkLeg»
import «8».«8.4-rightmost-nonadm-ancestor»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»
import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.2-P-fseq»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-Adm-nextAdm»
import «5».«5.1-ancestor-tree»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.3 条件(II) — `TV_Dichotomy`（`cdx_d_le_joints`）を無条件で閉じ、`TV_NotLdjLeg`
を単一残差 `TV_NotLdjReg` へ還元する

## 目的

«8».«8.3-condII-NotLdjLeg» は `TV_NotLdjLeg` を 3 脚
（`TV_Dichotomy` / `TV_TrunkLeg` / `TV_NotLdjReg`）へ還元する骨格
`TV_NotLdjLeg_of_legs` を bank した。うち `TV_TrunkLeg` は
«8».«8.3-condII-TrunkLeg» の `TV_TrunkLeg_holds` で既に閉じている。本ファイルは
残る `TV_Dichotomy`（構造的二分岐）を Isabelle `cdx_d_le_joints` の 1:1 移植で
**無条件に閉じ**、`TV_NotLdjLeg` を **`TV_NotLdjReg` の 1 本のみに還元**する。

## Isabelle 対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `cdx_d_le_joints` | layerB/pss_wip.thy:90230 (~170 行) | ✅ `tv_dichotomy_nl2`（private。`TV_Dichotomy` を house pattern で drop-in） |
| `m_8_4_rightmost_nonadm_ancestor` | pss_mechanized.thy | `rightmost_nonadm_ancestor`（«8».«8.4-rightmost-nonadm-ancestor»） |
| `wid_Br_Pred` | — | `Br_Pred_core_nontrunk`（«6».«6.5-Red-Pred-commute»） |
| `wid_Joints_Pred` | — | `Joints_Pred_core`（同上） |
| `m_7_4_Pred_Red_slice` | — | `Pred_Red_terminal_slice`（«7».«7.4-Mark-Trans-repr»） |
| `m_6_5_Lng_Red` | — | `Lng_Red_invariance`（«6».«6.5-Lng-Red-invariance»） |
| `wf21_Br_eq_seg` | — | `wf21_Br_eq_seg`（«8».«8.2-condV-rightmost-parent»） |
| `m_6_4_FirstNodes_Joints_mono_aux` | — | `FirstNodes_Joints_mono`（«6».«6.4-FirstNodes-Joints-mono»） |
| `c2sx_host_basic` | — | `condII_host_basic_holds`（推移的に «8».«8.3-condII-masterCF»） |

## 証明骨格（`cdx_d_le_joints`）

`j₀ := parent K 0 (Lng K-1)`、`j₋₁ := Adm K j₀`、`j₁ := Lng K-1`、
`R84 := Red (seg K j₋₁ j₁)`、`Rc := Red (seg K j₋₁ (Lng K-2)) = tvx_Rc K`。
1. host basic（`(0,j₀)<^Next(0,j₁)`, `entry 1 j₁ = 0`, `¬adm j₀`, `j₋₁<j₀`, `j₀+1<j₁`）。
2. `rightmost_nonadm_ancestor` で `d := j₀-j₋₁ = Joints R84 ! last`、
   `FirstNodes R84 ! last = j₁-j₋₁ = Lng R84 - 1`（最終枝は末尾単項）。
3. `standard_slice_Red_strongmono` で `R84 ∈ DT_PS`。
4. `wf21_Br_eq_seg` + `length_seg` で `Lng (last (Br R84)) = 1`。
5. `Pred_Red_terminal_slice` で `Rc = Pred R84`、`Br_Pred_core_nontrunk` で
   `Br Rc = (Br R84).dropLast`（末尾単項枝を剥がす）。
6. 場合分け `Lng (Br R84) = 1`:
   * trunk: `Br Rc = []` ⇒ `TrMax Rc = Lng Rc - 1`（左枝）。
   * 枝: `Joints_Pred_core` + `FirstNodes_Joints_mono`（joint 単調）で
     `d = Joints R84 ! last ≤ Joints R84 ! (last-1) = Joints Rc ! last`（右枝）。

## 状態

* ✅ `tv_dichotomy_nl2 : TV_Dichotomy`（private, sorry 0, 無条件, 公理 3 個）。
  ＝Isabelle `cdx_d_le_joints` の 1:1 移植。⚠️ 公開名 `TV_Dichotomy_holds` は
  並行 wave（«8».«8.3-condII-Dichotomy», 未 commit）が用意するため、衝突回避で private。
* ✅ `tv_notldjleg_of_reg : TV_NotLdjReg → TV_NotLdjLeg`（無条件還元）。
  `TV_NotLdjLeg` は `TV_Dichotomy`（本ファイルで閉）＋ `TV_TrunkLeg`（既閉）
  ＋ `TV_NotLdjReg` の 3 脚だったが、前 2 本が閉じたので **残差は `TV_NotLdjReg` の 1 本のみ**。
* ✅ 後続 «8».«8.3-condII-NotLdjReg-close» が無条件 `vcx_VE_all` と
  `wnx_seg_transport_W1/W2` を配線して `TV_NotLdjReg` を閉じ、
  `tv_notldjleg_holds : TV_NotLdjLeg` を公開する。本ファイル自身は還元層を担う。
-/

namespace PSS

/-! ## 私的補助（`getLastD` ↔ `getD (length-1)`、suffix `_nl2`） -/

private theorem getD_default_nl2 {α : Type} (l : List α) (n : ℕ) (d d' : α)
    (h : n < l.length) : l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

private theorem getLastD_cons_eq_nl2 {α : Type} :
    ∀ (l : List α) (a d : α), (a :: l).getLastD d = (a :: l).getD l.length d := by
  intro l
  induction l with
  | nil => intro a d; rfl
  | cons b bs ih =>
      intro a d
      have hstep : (a :: b :: bs).getLastD d = (b :: bs).getLastD a := rfl
      rw [hstep, ih b a]
      simp only [List.length_cons, List.getD_cons_succ]
      exact getD_default_nl2 (b :: bs) bs.length a d (by simp)

private theorem getLastD_eq_getD_nl2 {α : Type} (l : List α) (d : α) (hl : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simpa using getLastD_cons_eq_nl2 as a d

/-! ## `TV_Dichotomy`（Isabelle `cdx_d_le_joints`, layerB/pss_wip.thy:90230） -/

/-- Isabelle `cdx_d_le_joints` (layerB/pss_wip.thy:90230) の 1:1 移植。
`R_c = tvx_Rc K` は**幹**（`TrMax = 最終添字`）であるか、さもなくば枝を持ち
`d ≤ Joints R_c ! last` である、という構造的二分岐を**無条件**で閉じる。

⚠️ `private`（＝module 内限定）である理由: 並行 wave が同名の公開
`TV_Dichotomy_holds : TV_Dichotomy` を «8».«8.3-condII-Dichotomy»（未 commit）で
用意しており、公開名の衝突（silent header poisoning）を避けるため。公開の
Dichotomy 閉包はあちらが担い、本ファイルは自給自足でこの private を内部利用する。 -/
private theorem tv_dichotomy_nl2 : TV_Dichotomy := by
  intro K hST hmono hj1 hcond
  have hKR : RTPS K := STPS_RTPS K hST
  have hKT : TPS K := RTPS_TPS K hKR
  have hL : 1 < Lng K := by omega
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds K hKR hmono hj1 hcond
  -- `j₋₁ = Adm K j₀ < Lng K - 1 = j₁`
  have hjm1lt : Adm K (parent K 0 (Lng K - 1)) < Lng K - 1 := by omega
  -- `R84 = Red (seg K j₋₁ j₁)` を不透明な fvar にする
  obtain ⟨R84, hR84⟩ :
      ∃ x, x = Red (seg K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1)) := ⟨_, rfl⟩
  have hsegT : TPS (seg K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1)) := by
    have hpos : 0 < Lng (seg K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1)) := by
      rw [length_seg]; omega
    exact List.ne_nil_of_length_pos hpos
  -- `rightmost_nonadm_ancestor` の入力: 最終の行0辺・行1辺の非存在・`¬adm`
  have hnx : nextR K 0 (parent K 0 (Lng K - 1)) (Lng K - 1) = true :=
    hasParent_next_fseq K 0 (Lng K - 1) hp0
  have hle : leR K 0 (Lng K - 1) (Lng K - 1) = true :=
    leR0_refl_68 K (Lng K - 1) (by omega)
  have hnotnx1 : nextR K 1 (Lng K - 1 - 1) (Lng K - 1) = false := by
    cases hb : nextR K 1 (Lng K - 1 - 1) (Lng K - 1) with
    | false => rfl
    | true =>
      exfalso
      have hn1 : nextrel1 K (Lng K - 1 - 1) (Lng K - 1) = true := by
        simpa [nextR] using hb
      have hh := hn1
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hp4⟩, _⟩, _⟩ := hh
      rw [hE1] at hp4
      exact absurd hp4 (by omega)
  have hRN := rightmost_nonadm_ancestor K (parent K 0 (Lng K - 1)) (Lng K - 1)
    hST hmono hnx hle hnotnx1 hNadm
  rw [← hR84] at hRN
  obtain ⟨hRN1, _hRNmid, hRN3, hRN4⟩ := hRN
  -- `R84` の基本量
  have hBr84ne : Br R84 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hLng84 : Lng R84 = (Lng K - 1) + 1 - Adm K (parent K 0 (Lng K - 1)) := by
    rw [hR84, Lng_Red_invariance _ hsegT, length_seg]
  have R84L : 1 < Lng R84 := by omega
  have R84LR1 : Lng R84 - 1 = (Lng K - 1) - Adm K (parent K 0 (Lng K - 1)) := by omega
  have trne84 : TrMax R84 ≠ Lng R84 - 1 := by
    intro heq
    exact hBr84ne (by simp [Br, heq])
  -- `R84 ∈ DT_PS`（標準祖先切片）
  have leRjm1j1 : leR K 0 (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1) = true := by
    have hle1a : leR K 1 (Adm K (parent K 0 (Lng K - 1))) (parent K 0 (Lng K - 1)) = true :=
      adm_row1_ancestry K (parent K 0 (Lng K - 1)) hKT (by omega)
    have hle0a : leR K 0 (Adm K (parent K 0 (Lng K - 1))) (parent K 0 (Lng K - 1)) = true :=
      row1_implies_row0 K _ _ hKT hle1a
    have hle0b : leR K 0 (parent K 0 (Lng K - 1)) (Lng K - 1) = true :=
      nextR0_leR K _ _ hnx
    exact row0_transitive K _ _ _ hKT hle0a hle0b
  have hR84DT : DTPS R84 := by
    rw [hR84]
    exact standard_slice_Red_strongmono K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1)
      hST hjm1lt (le_refl _) leRjm1j1
  have R84mono : monoT R84 = true := ((DTPS_iff R84).mp hR84DT).2.1
  have R84T : TPS R84 := DTPS_TPS R84 hR84DT
  -- 最終枝は末尾単項
  have hFN84last : (FirstNodes R84).getD ((Br R84).length - 1) 0 = Lng R84 - 1 := by
    rw [hRN4]; omega
  have hblk : (Br R84).getD ((Br R84).length - 1) [] =
      seg R84 ((FirstNodes R84).getD ((Br R84).length - 1) 0) (Lng R84 - 1) :=
    wf21_Br_eq_seg R84 R84T hBr84ne
  have lastlen1 : Lng ((Br R84).getD ((Br R84).length - 1) []) = 1 := by
    rw [hblk, hFN84last, length_seg]; omega
  have hifcond : Lng ((Br R84).getLastD []) ≤ 1 := by
    rw [getLastD_eq_getD_nl2 (Br R84) [] hBr84ne]; omega
  have hBrRc : Br (Pred R84) = (Br R84).dropLast := by
    rw [Br_Pred_core_nontrunk R84 R84T R84L trne84, if_pos hifcond, List.append_nil]
  -- `Rc = Pred R84`
  have hRcP : Red (seg K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2)) = Pred R84 := by
    have h21 : Lng K - 2 = Lng K - 1 - 1 := by omega
    rw [h21, hR84,
      Pred_Red_terminal_slice K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 1) hjm1lt]
  -- ゴールを `Pred R84` の言葉で開く
  simp only [tvx_Rc, tvx_d, tvx_jL]
  rw [hRcP]
  by_cases hcaseT : (Br R84).length = 1
  · -- 幹: `Br (Pred R84) = []`
    left
    have hBrPe : Br (Pred R84) = [] := by
      have hlen0 : (Br (Pred R84)).length = 0 := by
        rw [hBrRc, List.length_dropLast, hcaseT]
      exact List.eq_nil_of_length_eq_zero hlen0
    by_contra hne
    have hBrP2 : Br (Pred R84) =
        P (seg (Pred R84) (TrMax (Pred R84) + 1) (Lng (Pred R84) - 1)) := by
      simp only [Br, if_neg hne]
    rw [hBrP2] at hBrPe
    exact P_nonempty _ hBrPe
  · -- 枝: `Br (Pred R84) ≠ []` かつ `d ≤ Joints (Pred R84) ! last`
    right
    have hBr84ge2 : 2 ≤ (Br R84).length := by omega
    have lenRc : (Br (Pred R84)).length = (Br R84).length - 1 := by
      rw [hBrRc, List.length_dropLast]
    have hBrPne : Br (Pred R84) ≠ [] :=
      List.ne_nil_of_length_pos (by rw [lenRc]; omega)
    have hJBr1 : (Br R84).length - 1 < (Br R84).length := by omega
    have hJBrP : (Br R84).length - 2 < (Br (Pred R84)).length := by rw [lenRc]; omega
    have jPN : (Joints (Pred R84)).getD ((Br R84).length - 2) 0
        = (Joints R84).getD ((Br R84).length - 2) 0 :=
      Joints_Pred_core R84 R84T R84mono R84L trne84 ((Br R84).length - 2) hJBrP
    have jointRc : (Joints (Pred R84)).getD ((Br (Pred R84)).length - 1) 0
        = (Joints R84).getD ((Br R84).length - 2) 0 := by
      rw [show (Br (Pred R84)).length - 1 = (Br R84).length - 2 from by rw [lenRc]; omega]
      exact jPN
    have jmono : (Joints R84).getD ((Br R84).length - 1) 0
        ≤ (Joints R84).getD ((Br R84).length - 2) 0 :=
      (FirstNodes_Joints_mono R84 ((Br R84).length - 2) ((Br R84).length - 1)
        R84T R84mono (by omega) hJBr1).2.1
    refine ⟨hBrPne, ?_⟩
    omega

/-! ## `TV_NotLdjLeg` を `TV_NotLdjReg` へ還元（house pattern）

«8».«8.3-condII-NotLdjLeg» の `TV_NotLdjLeg_of_legs`
（`TV_Dichotomy → TV_TrunkLeg → TV_NotLdjReg → TV_NotLdjLeg`）に、本ファイルの
`TV_Dichotomy_holds` と «8».«8.3-condII-TrunkLeg» の `TV_TrunkLeg_holds` を食わせる。 -/

/-- `TV_NotLdjLeg` は最早 `TV_NotLdjReg` の 1 本のみに依存する。
`TV_Dichotomy`（本ファイル private `tv_dichotomy_nl2`）と `TV_TrunkLeg`
（«8».«8.3-condII-TrunkLeg» の `TV_TrunkLeg_holds`）は閉じているので、
`TV_NotLdjLeg_of_legs` の 3 脚のうち残るのは `TV_NotLdjReg` の 1 本。 -/
theorem tv_notldjleg_of_reg (hReg : TV_NotLdjReg) : TV_NotLdjLeg :=
  TV_NotLdjLeg_of_legs tv_dichotomy_nl2 TV_TrunkLeg_holds hReg

#print axioms tv_dichotomy_nl2
#print axioms tv_notldjleg_of_reg

end PSS
