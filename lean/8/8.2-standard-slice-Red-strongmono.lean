import «6».«6.2-mono-ancestor-slice»
import «6».«6.2-P-IncrFirst-equivariance»
import «6».«6.4-P-IdxSum»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.6-reduced-leftend»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.7-standard-reduced»
import «6».«6.7-standard-prefix»

/-!
# §8.2 命題（標準形の直系先祖による切片の簡約化の強単項性）

- 原文: `tmp/content.md` L3273–L3295（強単項性の定義 L3279–L3281、命題 L3283、証明 L3285–L3295）
- 訂正: なし（同節 A9 は `LastStep` の添字に効くもので、本命題には効かない）
- Isabelle: `p_8_2_standard_slice_Red_strongmono` (isabelle/pss_paper.thy:1499) の証明は
            `m_8_2_standard_slice_Red_strongmono` (isabelle/layerB/pss_wip.thy:15020)
- 依存: «6».«6.6-ancestor-slice-Red-IncrFirst»（`Red` 読み戻し・`monoT`・簡約性）、
        §6.8 命題（標準形の切片と `Br` の降順性の関係）。後者の Lean ファイル
        `6/6.8-standard-slice-Br-descending.lean` は未緑（olean 無し）のため import できず、
        本ファイルでは `standard_slice_Br_descending_dep`（private・sorry）として隔離した。
        それが本ファイル唯一の sorry である。
- 定義: 強単項性 `strongMono`／`DTPS`（`cdomB`・`descendingB` とも Bool 値・計算可能）を
        本ファイルで導入する（§8.2 の後続 6 項目が共有層から再利用する想定）。
- 数値検証: `python/strongmono_audit.py` — 標準形プール 442 本・直系先祖切片 13,264 例で
        命題の反例 0・輸送不変量（読み戻し／`Br` map）の反例 0。定義チェックサムは
        成分 <4・長さ ≤4 の全 69,904 列で Python/Lean とも `430760048`（下の #guard も同出力）。
- 状態: 🚨 部分証明（sorry 1 = §6.8 依存のみ。それ以外の全補題・主定理の組み立ては完了。
        `standard_slice_Red_strongmono_of_Br_descending` は sorry 0 で公理は
        `[propext, Classical.choice, Quot.sound]`）
-/

namespace PSS

/-! ## 強単項性の定義（§8.2, 原文 L3273–L3281）

原文 L1402–L1412（§6.8 降順性）: `Q` が降順であるとは、`J'₀ ≤ J'₁ ≤ Lng Q - 1` なる任意の
添字対で、左端の第 0 行が広義単調減少、第 0 行が同点なら第 1 行も広義単調減少ということ。
原文 L3279: `M` が強単項であるとは、`M` が簡約かつ単項かつ `Br M` が降順ということ。
原文 L3281: 強単項ペア数列全体を `DT_PS ⊂ T_PS` と置く。 -/

/-- 降順性の 1 比較（成分 `C` が成分 `D` を支配する）: 第 0 行左端が `≥`、
同点なら第 1 行左端も `≥`。 -/
def cdomB (C D : PS) : Bool :=
  decide (entry D 0 0 ≤ entry C 0 0) &&
    (!(entry C 0 0 == entry D 0 0) || decide (entry D 1 0 ≤ entry C 1 0))

/-- `Q` が降順（§6.8, 原文 L1408–L1412）: すべての `J₀ ≤ J₁ < Lng Q` で
`cdomB (Q_J₀) (Q_J₁)`。 -/
def descendingB (Q : List PS) : Bool :=
  (List.range Q.length).all fun J₁ =>
    (List.range (J₁ + 1)).all fun J₀ =>
      cdomB (Q.getD J₀ []) (Q.getD J₁ [])

/-- `M` が強単項（§8.2, 原文 L3279）: 簡約かつ単項かつ `Br M` が降順。 -/
def strongMono (M : PS) : Bool :=
  reduced M && monoT M && descendingB (Br M)

/-- `DT_PS`（§8.2, 原文 L3281）: 強単項ペア数列全体。`reduced` が非空性を含むので
`DT_PS ⊂ T_PS` は従う（`DTPS_TPS`）。 -/
def DTPS (M : PS) : Prop := strongMono M = true

instance (M : PS) : Decidable (DTPS M) := by
  unfold DTPS
  infer_instance

/-! `python/strongmono_audit.py` の guard vectors と 1:1 の回帰テスト。 -/

#guard strongMono [(0, 0)] == false
#guard strongMono [(0, 0), (1, 1)] == true
#guard strongMono [(0, 0), (1, 1), (2, 2)] == true
#guard strongMono [(0, 0), (1, 1), (2, 1)] == true
#guard strongMono [(0, 0), (1, 1), (2, 2), (3, 1), (3, 1)] == true
#guard strongMono [(0, 0), (1, 1), (2, 2), (3, 3), (3, 2), (3, 1)] == true
#guard strongMono [(0, 0), (1, 1), (2, 2), (3, 1), (3, 2)] == false
#guard strongMono [(1, 1), (2, 2)] == true
#guard strongMono [(0, 0), (0, 2)] == false

/-! ## 定義の展開 API -/

theorem cdomB_iff (C D : PS) :
    cdomB C D = true ↔
      entry D 0 0 ≤ entry C 0 0 ∧
        (entry C 0 0 = entry D 0 0 → entry D 1 0 ≤ entry C 1 0) := by
  unfold cdomB
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun hEq => ?_⟩
    rcases h1 with hne | hle
    · exact absurd hEq hne
    · exact hle
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    by_cases hEq : entry C 0 0 = entry D 0 0
    · exact Or.inr (h1 hEq)
    · exact Or.inl hEq

theorem descendingB_iff (Q : List PS) :
    descendingB Q = true ↔
      ∀ J₀ J₁ : ℕ, J₀ ≤ J₁ → J₁ < Q.length →
        cdomB (Q.getD J₀ []) (Q.getD J₁ []) = true := by
  unfold descendingB
  rw [List.all_eq_true]
  constructor
  · intro h J₀ J₁ h01 hJ₁
    have h1 := h J₁ (List.mem_range.mpr hJ₁)
    rw [List.all_eq_true] at h1
    exact h1 J₀ (List.mem_range.mpr (by omega))
  · intro h J₁ hJ₁
    rw [List.all_eq_true]
    intro J₀ hJ₀
    have hJ₁' : J₁ < Q.length := List.mem_range.mp hJ₁
    have hJ₀' : J₀ < J₁ + 1 := List.mem_range.mp hJ₀
    exact h J₀ J₁ (by omega) hJ₁'

theorem DTPS_iff (M : PS) :
    DTPS M ↔ RTPS M ∧ monoT M = true ∧ descendingB (Br M) = true := by
  unfold DTPS strongMono RTPS
  simp [Bool.and_eq_true, and_assoc]

theorem DTPS_TPS (M : PS) (hM : DTPS M) : TPS M :=
  RTPS_TPS M ((DTPS_iff M).mp hM).1

/-! ## `IncrFirstN` 輸送補題群

Isabelle 側の `Br_funpow_IncrFirst`／`descending_funpow_IncrFirst_rev`
(isabelle/layerB/pss_wip.thy:14915–15004) に対応する。`Br` は行 0 の一様シフトと可換で、
降順性は逆向きに輸送される（比較が第 0 行 `+k` 同士・第 1 行そのまま、なので）。 -/

private theorem TrMax_IncrFirstN_sm (k : ℕ) (M : PS) :
    TrMax (IncrFirstN k M) = TrMax M := by
  unfold TrMax
  rw [nextR_IncrFirstN_ri, length_IncrFirstN]

private theorem seg_IncrFirstN_sm (k : ℕ) (M : PS) (a b : ℕ)
    (hb : b < Lng M) :
    seg (IncrFirstN k M) a b = IncrFirstN k (seg M a b) := by
  rw [IncrFirstN_eq_map k (seg M a b)]
  unfold seg
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range'_1.mp hj
  have hjM : j < Lng M := by omega
  simp only [Function.comp]
  rw [entry_IncrFirstN_zero k M j hjM, entry_IncrFirstN_one k M j]

private theorem P_IncrFirstN_sm (k : ℕ) (Q : PS) :
    P (IncrFirstN k Q) = (P Q).map (IncrFirstN k) := by
  induction k generalizing Q with
  | zero =>
      show P Q = (P Q).map (IncrFirstN 0)
      have h : (P Q).map (IncrFirstN 0) = (P Q).map id :=
        List.map_congr_left (fun x _ => rfl)
      rw [h, List.map_id]
  | succ k ih =>
      show P (IncrFirstN k (IncrFirst Q)) = (P Q).map (IncrFirstN (k + 1))
      rw [ih (IncrFirst Q), P_IncrFirst_equivariance, List.map_map]
      exact List.map_congr_left (fun x _ => rfl)

private theorem Br_IncrFirstN_sm (k : ℕ) (N : PS) (hN : TPS N) :
    Br (IncrFirstN k N) = (Br N).map (IncrFirstN k) := by
  have hpos : 0 < Lng N := List.length_pos_of_ne_nil hN
  unfold Br
  rw [TrMax_IncrFirstN_sm, length_IncrFirstN]
  by_cases h : TrMax N = Lng N - 1
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h,
      seg_IncrFirstN_sm k N (TrMax N + 1) (Lng N - 1) (by omega),
      P_IncrFirstN_sm]

private theorem getD_map_IncrFirstN_sm (k : ℕ) (Q : List PS) (J : ℕ)
    (hJ : J < Q.length) :
    (Q.map (IncrFirstN k)).getD J [] = IncrFirstN k (Q.getD J []) := by
  have hJm : J < (Q.map (IncrFirstN k)).length := by simpa using hJ
  rw [getD_eq_getElem_idx _ _ hJm, getD_eq_getElem_idx _ _ hJ,
    List.getElem_map]

/-- 降順性の逆向き輸送: 各成分が非空なら、行 0 一様シフト後の降順性から元の降順性が戻る。 -/
private theorem descendingB_of_map_IncrFirstN_sm (k : ℕ) (Q : List PS)
    (hne : ∀ J, J < Q.length → 0 < Lng (Q.getD J []))
    (hdesc : descendingB (Q.map (IncrFirstN k)) = true) :
    descendingB Q = true := by
  rw [descendingB_iff] at hdesc ⊢
  intro J₀ J₁ h01 hJ₁
  have hJ₀ : J₀ < Q.length := by omega
  have hJ₁m : J₁ < (Q.map (IncrFirstN k)).length := by simpa using hJ₁
  have h := hdesc J₀ J₁ h01 hJ₁m
  rw [getD_map_IncrFirstN_sm k Q J₀ hJ₀,
    getD_map_IncrFirstN_sm k Q J₁ hJ₁] at h
  rw [cdomB_iff] at h ⊢
  rw [entry_IncrFirstN_zero k _ 0 (hne J₀ hJ₀),
    entry_IncrFirstN_zero k _ 0 (hne J₁ hJ₁),
    entry_IncrFirstN_one k _ 0, entry_IncrFirstN_one k _ 0] at h
  obtain ⟨h0, h1⟩ := h
  constructor
  · omega
  · intro hEq
    exact h1 (by omega)

/-! ## §6.8 依存（未緑ファイルの隔離） -/

/-- §6.8 命題（標準形の切片と `Br` の降順性の関係）の降順性部分（`descendingB` 版）。

対応する Lean ファイル `6/6.8-standard-slice-Br-descending.lean`（訂正 A7・A8、
Isabelle: `m_6_8_standard_slice_Br_descending`）は本稿執筆時点で未緑のため import
できない。同ファイルが緑になり次第、この private sorry を
`descendingB_iff`＋`cdomB_iff` 経由で同ファイルの `descending (Br (seg M j₀' j₁'))`
（Prop 版, getD ベース）へ橋渡しして置き換える。本ファイル唯一の sorry。 -/
private theorem standard_slice_Br_descending_dep (M : PS) (j₀' j₁' : ℕ)
    (hM : STPS M) (hlt : j₀' < j₁') (hj₁ : j₁' ≤ Lng M - 1)
    (hanc : leR M 0 j₀' j₁' = true) :
    descendingB (Br (seg M j₀' j₁')) = true := by
  sorry

/-! ## 主定理 -/

/-- 主定理の §6.8 明示版（sorry 0）: `M` が簡約で、直系先祖切片 `M' = (M_j)_{j=j₀'}^{j₁'}`
の `Br M'` が降順なら、`Red M'` は強単項。標準性は §6.8 の降順性供給にだけ要るので、
ここでは `RTPS M` まで弱めてある（Isabelle 版の証明構造と同じ）。 -/
theorem standard_slice_Red_strongmono_of_Br_descending
    (M : PS) (j₀' j₁' : ℕ)
    (hMR : RTPS M) (hlt : j₀' < j₁') (hj₁ : j₁' ≤ Lng M - 1)
    (hanc : leR M 0 j₀' j₁' = true)
    (hdescS : descendingB (Br (seg M j₀' j₁')) = true) :
    DTPS (Red (seg M j₀' j₁')) := by
  -- S := seg M j₀' j₁', N := Red S, k := entry M 0 j₀' - entry M 1 j₀'
  have hfacts := ancestor_slice_Red_IncrFirst M j₀' j₁' hMR hlt hj₁ hanc
  have hRedN : Red (Red (seg M j₀' j₁')) = Red (seg M j₀' j₁') := hfacts.1
  have hmonoN : monoT (Red (seg M j₀' j₁')) = true := hfacts.2.1
  have hread : seg M j₀' j₁' =
      IncrFirstN (entry M 0 j₀' - entry M 1 j₀') (Red (seg M j₀' j₁')) :=
    hfacts.2.2
  -- `N` は非空（読み戻しで `Lng N = Lng S > 0`）
  have hSpos : 0 < Lng (seg M j₀' j₁') := by
    rw [length_seg]
    omega
  have hNLng : Lng (Red (seg M j₀' j₁')) = Lng (seg M j₀' j₁') := by
    conv_rhs => rw [hread]
    rw [length_IncrFirstN]
  have hNT : TPS (Red (seg M j₀' j₁')) := by
    intro hnil
    have h0 : Lng (Red (seg M j₀' j₁')) = 0 := by rw [hnil]; rfl
    omega
  -- 簡約性: `Red N = N` かつ `N ≠ []`
  have hie : (Red (seg M j₀' j₁')).isEmpty = false := by
    cases hcase : Red (seg M j₀' j₁') with
    | nil => exact absurd hcase hNT
    | cons a l => rfl
  have hNred : reduced (Red (seg M j₀' j₁')) = true := by
    unfold reduced
    rw [hRedN, hie]
    simp
  -- `Br S = map (IncrFirstN k) (Br N)`、降順性を逆向きに輸送
  have hBrmap : Br (seg M j₀' j₁') =
      (Br (Red (seg M j₀' j₁'))).map
        (IncrFirstN (entry M 0 j₀' - entry M 1 j₀')) := by
    conv_lhs => rw [hread]
    exact Br_IncrFirstN_sm _ _ hNT
  have hdescN : descendingB (Br (Red (seg M j₀' j₁'))) = true := by
    apply descendingB_of_map_IncrFirstN_sm
      (entry M 0 j₀' - entry M 1 j₀') (Br (Red (seg M j₀' j₁')))
    · intro J hJ
      exact List.length_pos_of_ne_nil (Br_component_TPS _ J hNT hJ)
    · rw [← hBrmap]
      exact hdescS
  -- 組み立て
  rw [DTPS_iff]
  exact ⟨hNred, hmonoN, hdescN⟩

/-- §8.2 命題（標準形の直系先祖による切片の簡約化の強単項性）（原文 L3283）:
任意の `M ∈ ST_PS` と `j₀' < j₁' ≤ Lng M - 1` に対し、`(0,j₀') ≤_M (0,j₁')` ならば
`Red ((M_j)_{j=j₀'}^{j₁'})` は強単項である。 -/
theorem standard_slice_Red_strongmono (M : PS) (j₀' j₁' : ℕ)
    (hM : STPS M) (hlt : j₀' < j₁') (hj₁ : j₁' ≤ Lng M - 1)
    (hanc : leR M 0 j₀' j₁' = true) :
    DTPS (Red (seg M j₀' j₁')) :=
  standard_slice_Red_strongmono_of_Br_descending M j₀' j₁'
    (STPS_RTPS M hM) hlt hj₁ hanc
    (standard_slice_Br_descending_dep M j₀' j₁' hM hlt hj₁ hanc)

#print axioms cdomB_iff
#print axioms descendingB_iff
#print axioms DTPS_iff
#print axioms DTPS_TPS
#print axioms standard_slice_Red_strongmono_of_Br_descending
#print axioms standard_slice_Red_strongmono

end PSS
