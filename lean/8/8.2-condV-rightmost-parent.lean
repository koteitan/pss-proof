import «5».«5.1-ancestor-tree»
import «6».«6.3-adm-slice»
import «6».«6.4-mono-slice»
import «6».«6.5-monoT-Red»
import «6».«6.6-reduced-coeff»
import «6».«6.6-condAB-coeff»
import «6».«6.8-standard-slice-Br-descending»
import «8».«8.2-standard-slice-Red-strongmono»

/-!
# §8.2 補題（条件(V)の下での右端の親の基本性質）

- 原文: `tmp/content.md` L3602 付近（補題本体 L3602–L3618）
- 訂正: なし（同節 A9 は `LastStep` の添字曖昧性で、本補題は `LastStep` を使わない）
- Isabelle: `p_8_2_condV_rightmost_parent` (isabelle/pss_paper.thy:1588) の証明は
  `m_8_2_condV_rightmost_parent` (isabelle/layerB/pss_wip.thy:42048)。
  補助補題（Isabelle 名を保持）:
  - `wf21_Br_eq_seg` (isabelle/pss_mechanized.thy:43941)
  - `le0_monoT_seg_into_list` (isabelle/pss_mechanized.thy:4206)
  - `le0_above_parent` = `m_8_2_le0_above_parent` (isabelle/layerB/pss_wip.thy:35208)
  - `joint_row1_eq` = `m_8_2_joint_row1_eq` (isabelle/layerB/pss_wip.thy:34346)
  - `branch_col0_val` = `m_8_2_branch_col0_val` (isabelle/layerB/pss_wip.thy:35397)
  - `det_imp_joint_lt_TrMax` = `m_8_2_det_imp_joint_lt_TrMax`
    (isabelle/layerB/pss_wip.thy:35547)。その内部連鎖
    `m_8_2_e1_le_e1par_of_notnextR1` / `m_8_2_branch_row1_le_TrMax_of_notnextR` /
    `m_8_2_branch_row1_le_TrMax_J0` / `m_8_2_branch_row1_le_TrMax`
    (isabelle/layerB/pss_wip.thy:35240–35538) は private (`_cv`)。
  - Isabelle `Joints_nth`/`Joints_parent_nextR`/`monoT_hasParent0_last` は
    既存 Lean の `Joints_getD`/`Joints_nextR_FirstNodes`/`mono_hasParent_row0` を使用。
- 依存: `5.1-ancestor-tree`（`ancestor_basic_1`/`ancestor_tree_1`/`parent_exists_2` =
  le0 の値特徴付け）、`6.3-adm-slice`（`leR0_seg_adm`）、`6.4-mono-slice`
  （`idxSum_total`/`TrMax_trunk_step` 系）、`6.5-monoT-Red`
  （`entry_FirstNodes_eq_component_mr`/`Joints_nextR_FirstNodes`/`le_TrMax_intro_wd`）、
  `6.6-reduced-coeff`（`reduced_coeff`/`RTPS_condAB`）、`6.6-condAB-coeff`
  （`mono_hasParent_row0` ほか §6.6 condAB API）、
  `6.8-standard-slice-Br-descending`（`seg_of_seg_68`）、
  `8.2-standard-slice-Red-strongmono`（`DTPS`/`descendingB`/`cdomB` 語彙）
- 方針: Isabelle の rtrancl 経路分解は使わず、`le0` の値特徴付け
  （`ancestor_basic_1` + `nextR0_largest_below` + `parent_exists_*`）で全て構成する。
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## 補助（private, suffix `_cv`） -/

private theorem le0_index_mono_cv (M : PS) (a b : ℕ)
    (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_index_fseq h.2

private theorem leR0_bounds_cv (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-! ## `le0` の値特徴付けによる公開補助補題 -/

/-- Isabelle `le0_monoT_seg_into_list`: 単項な切片 `seg R bs be` の左端 `bs` は、
切片内の任意の点 `p`（ambient 座標）の行 0 直系先祖。 -/
theorem le0_monoT_seg_into_list (R : PS) (bs p be : ℕ) (hR : TPS R)
    (hmono : monoT (seg R bs be) = true)
    (hbsp : bs ≤ p) (hpbe : p ≤ be) (hbe : be < Lng R) :
    le0 R bs p = true := by
  have hmm := hmono
  simp only [monoT, Bool.and_eq_true] at hmm
  have hleS : leR (seg R bs be) 0 0 (Lng (seg R bs be) - 1) = true := hmm.2
  have hlen : Lng (seg R bs be) = be + 1 - bs := length_seg R bs be
  have hb1 : 0 < Lng (seg R bs be) := by omega
  have hb2 : Lng (seg R bs be) - 1 < Lng (seg R bs be) := by omega
  have htr := leR0_seg_adm R bs be 0 (Lng (seg R bs be) - 1)
    (by omega) hbe hb1 hb2
  rw [htr] at hleS
  have h2 : bs + (Lng (seg R bs be) - 1) = be := by omega
  rw [Nat.add_zero, h2] at hleS
  have hfinal := ancestor_tree_1 R bs p be hR hleS hbsp hpbe
  simpa [leR] using hfinal

/-- Isabelle `m_8_2_le0_above_parent`: 行 0 の（一意な）親を持つ列 `j` へ `le0` で
到達する `p ≠ j` は `parent M 0 j` 以下に留まる。 -/
theorem le0_above_parent (M : PS) (p j : ℕ)
    (hp0 : hasParent M 0 j = true) (hle : le0 M p j = true) (hne : p ≠ j) :
    p ≤ parent M 0 j := by
  have hb := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hM : TPS M :=
    List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le j) hb.1.2)
  have hplt : p < j := lt_of_le_of_ne (le0_index_mono_cv M p j hle) hne
  have hleR : leR M 0 p j = true := by simpa [leR] using hle
  have hgrow : entry M 0 p < entry M 0 j :=
    ancestor_basic_1 M p j j hM hplt (le_refl _) hleR
  exact nextR0_largest_below M (parent M 0 j) p j
    (hasParent_next_fseq M 0 j hp0) hplt hgrow

/-- Isabelle `wf21_Br_eq_seg`: 最後の枝ブロックは `M` の接尾切片
`seg M (FirstNodes M ! Jstar) (Lng M - 1)` そのもの。 -/
theorem wf21_Br_eq_seg (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    (Br M).getD ((Br M).length - 1) [] =
      seg M ((FirstNodes M).getD ((Br M).length - 1) 0) (Lng M - 1) := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
    simp [Br, hne]
  have hNlen : Lng (seg M (TrMax M + 1) (Lng M - 1)) = Lng M - 1 - TrMax M := by
    rw [length_seg]; omega
  have hNpos : 0 < Lng (seg M (TrMax M + 1) (Lng M - 1)) := by omega
  have hNT : TPS (seg M (TrMax M + 1) (Lng M - 1)) :=
    List.ne_nil_of_length_pos hNpos
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJlt : (Br M).length - 1 < (P (seg M (TrMax M + 1) (Lng M - 1))).length := by
    rw [← hBr]; omega
  -- ブロック = `N` の切片（`P_IdxSum`）、Br 語彙へ戻す
  have hcomp := P_IdxSum (seg M (TrMax M + 1) (Lng M - 1)) ((Br M).length - 1)
    hNT (by rw [← hBr])
  rw [← hBr] at hcomp
  -- 右端の読み出し: `IdxSum` の末端 = `Lng N`
  have hflat : (Br M).flatten = seg M (TrMax M + 1) (Lng M - 1) := by
    rw [hBr]; exact P_concat _
  have htotal := idxSum_total (Br M)
  rw [hflat] at htotal
  have hsucc : (Br M).length - 1 + 1 = (Br M).length := by omega
  have hrb : (IdxSum (Br M)).getD ((Br M).length - 1 + 1) 0 =
      Lng (seg M (TrMax M + 1) (Lng M - 1)) := by
    rw [hsucc]; exact htotal
  rw [hrb] at hcomp
  -- 左端の bound と `FirstNodes` の読み出し
  have hfn := FirstNodes_getD M ((Br M).length - 1) (by omega)
  have hblkpos : 0 < Lng ((Br M).getD ((Br M).length - 1) []) := by
    have h := P_component_nonempty (seg M (TrMax M + 1) (Lng M - 1))
      ((Br M).length - 1) hNT hJlt
    rw [← hBr] at h
    exact h
  have hdiff := idxSum_diff (Br M) ((Br M).length - 1) (by omega)
  rw [hrb] at hdiff
  -- 合成: `seg N a (Lng N - 1) = seg M (TrMax+1+a) (Lng M - 1)`
  rw [hcomp, seg_of_seg_68 M (TrMax M + 1) (Lng M - 1)
    ((IdxSum (Br M)).getD ((Br M).length - 1) 0)
    (Lng (seg M (TrMax M + 1) (Lng M - 1)) - 1) (by omega) (by omega)]
  have he1 : TrMax M + 1 + (IdxSum (Br M)).getD ((Br M).length - 1) 0 =
      (FirstNodes M).getD ((Br M).length - 1) 0 := by omega
  have he2 : TrMax M + 1 + (Lng (seg M (TrMax M + 1) (Lng M - 1)) - 1) =
      Lng M - 1 := by omega
  rw [he1, he2]

/-! ## §8.2 joint/branch-head の読み出し（Isabelle `m_8_2_*`） -/

/-- Isabelle `m_8_2_joint_row1_eq`: joint の行 1 値は枝ブロック先頭の行 0 値 - 1。 -/
theorem joint_row1_eq (M : PS) (J : ℕ) (hD : DTPS M)
    (hJ : J < (Br M).length) :
    entry M 1 ((Joints M).getD J 0) =
      entry ((Br M).getD J []) 0 0 - 1 := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hcol0 : entry M 0 0 = entry M 1 0 := RedCondB_head_eq M hM hB
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htoffj0 := trunk_entries_offset M hM hA ((Joints M).getD J 0) hgeom.1
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : (FirstNodes M).getD J 0 < Lng M :=
    (leR0_bounds_cv M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2
  have hpar0 : parent M 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 M _ _ hnxJ
  have hp0 : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    mono_hasParent_row0 M hM hmono _ (by omega) hfL
  have hcondA := RedCondA_apply M hA 0 ((FirstNodes M).getD J 0)
    (by omega) hfL hp0
  rw [hpar0] at hcondA
  have hc0 := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  omega

/-- Isabelle `m_8_2_branch_col0_val`: 枝 `J` の行 0 先頭値は
`M_{1,0} + Joints(M)_J + 1`。 -/
theorem branch_col0_val (M : PS) (J : ℕ) (hD : DTPS M)
    (hJ : J < (Br M).length) :
    entry ((Br M).getD J []) 0 0 =
      entry M 1 0 + (Joints M).getD J 0 + 1 := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hcol0 : entry M 0 0 = entry M 1 0 := RedCondB_head_eq M hM hB
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htoffj0 := trunk_entries_offset M hM hA ((Joints M).getD J 0) hgeom.1
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : (FirstNodes M).getD J 0 < Lng M :=
    (leR0_bounds_cv M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2
  have hpar0 : parent M 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 M _ _ hnxJ
  have hp0 : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    mono_hasParent_row0 M hM hmono _ (by omega) hfL
  have hcondA := RedCondA_apply M hA 0 ((FirstNodes M).getD J 0)
    (by omega) hfL hp0
  rw [hpar0] at hcondA
  have hc0 := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  omega

/-! ## §8.2 det ルート: 枝先頭の行 1 値の幹上界（Isabelle 35240–35538, private） -/

/-- Isabelle `nextR1_TrMax_fail`: 幹の右端では行 1 の隣接辺が立たない。 -/
private theorem nextR1_TrMax_fail_cv (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hx : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j < TrMax M + 1, nextR M 1 j (j + 1) = true := by
        intro j hj
        by_cases hlt : j < TrMax M
        · exact TrMax_trunk_step M j hM hlt
        · have hjeq : j = TrMax M := by omega
          rw [hjeq]
          exact hx
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

/-- Isabelle `wit_FirstNodes0`: 最初の枝の先頭は `TrMax M + 1`。 -/
private theorem wit_FirstNodes0_cv (M : PS) (hBrne : Br M ≠ []) :
    (FirstNodes M).getD 0 0 = TrMax M + 1 := by
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have h := FirstNodes_getD M 0 hBrpos
  have hidx : (IdxSum (Br M)).getD 0 0 = 0 := by
    have h0 := idxSum_getD (Br M) 0 (Nat.zero_le _)
    simpa using h0
  omega

/-- Isabelle `m_8_2_e1_le_e1par_of_notnextR1`: 行 0 の親が行 1 の親でないなら、
行 1 値は行 0 親の行 1 値以下。 -/
private theorem e1_le_e1par_of_notnextR1_cv (M : PS) (j : ℕ) (hM : TPS M)
    (hp0 : hasParent M 0 j = true) (hjL : j < Lng M)
    (hnotnx : nextR M 1 (parent M 0 j) j = false) :
    entry M 1 j ≤ entry M 1 (parent M 0 j) := by
  have hparR := hasParent_next_fseq M 0 j hp0
  have hplt : parent M 0 j < j := (nextR_implies_row0 M 0 _ j hparR).1
  have hleR : leR M 0 (parent M 0 j) j = true :=
    (nextR_implies_row0 M 0 _ j hparR).2
  by_contra hgt
  have helt : entry M 1 (parent M 0 j) < entry M 1 j := by omega
  obtain ⟨p1, hp1ge, hp1lt, hp1nx⟩ :=
    parent_exists_2 M (parent M 0 j) j hM hplt hjL helt hleR
  have hp1nx1 : nextrel1 M p1 j = true := by simpa [nextR] using hp1nx
  have hle0p1 : le0 M p1 j = true := by
    have hh := hp1nx1
    simp only [nextrel1, Bool.and_eq_true] at hh
    exact hh.1.2
  have hp1le : p1 ≤ parent M 0 j :=
    le0_above_parent M p1 j hp0 hle0p1 (by omega)
  have hp1eq : p1 = parent M 0 j := by omega
  rw [hp1eq] at hp1nx
  rw [hp1nx] at hnotnx
  exact Bool.noConfusion hnotnx

/-- Isabelle `m_8_2_branch_row1_le_TrMax_of_notnextR`: 幹右端の行 1 辺が立たない
枝先頭では行 1 値が幹右端で抑えられる。 -/
private theorem branch_row1_le_TrMax_of_notnextR_cv (M : PS) (J : ℕ)
    (hD : DTPS M) (hJ : J < (Br M).length)
    (hnotnx : nextR M 1 (TrMax M) ((FirstNodes M).getD J 0) = false) :
    entry M 1 ((FirstNodes M).getD J 0) ≤ entry M 1 (TrMax M) := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hcol0 : entry M 0 0 = entry M 1 0 := RedCondB_head_eq M hM hB
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htoffj0 := trunk_entries_offset M hM hA ((Joints M).getD J 0) hgeom.1
  have htofft := trunk_entries_offset M hM hA (TrMax M) (le_refl _)
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : (FirstNodes M).getD J 0 < Lng M :=
    (leR0_bounds_cv M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2
  have hpar0 : parent M 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 M _ _ hnxJ
  have hp0 : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    mono_hasParent_row0 M hM hmono _ (by omega) hfL
  have hcoeff : entry M 1 ((FirstNodes M).getD J 0) ≤
      entry M 0 ((FirstNodes M).getD J 0) :=
    reduced_coeff M hR _ hfL
  have hcondA := RedCondA_apply M hA 0 ((FirstNodes M).getD J 0)
    (by omega) hfL hp0
  rw [hpar0] at hcondA
  by_cases hlt : (Joints M).getD J 0 < TrMax M
  · omega
  · have hj0t : (Joints M).getD J 0 = TrMax M := by omega
    have hnotnx' : nextR M 1 (parent M 0 ((FirstNodes M).getD J 0))
        ((FirstNodes M).getD J 0) = false := by
      rw [hpar0, hj0t]
      exact hnotnx
    have hle := e1_le_e1par_of_notnextR1_cv M ((FirstNodes M).getD J 0)
      hM hp0 hfL hnotnx'
    rw [hpar0] at hle
    omega

/-- Isabelle `m_8_2_branch_row1_le_TrMax_J0`: 最初の枝（`J = 0`）は無条件。 -/
private theorem branch_row1_le_TrMax_J0_cv (M : PS) (hD : DTPS M)
    (hBrne : Br M ≠ []) :
    entry M 1 ((FirstNodes M).getD 0 0) ≤ entry M 1 (TrMax M) := by
  have hM : TPS M := DTPS_TPS M hD
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hf0 := wit_FirstNodes0_cv M hBrne
  have hnotnx : nextR M 1 (TrMax M) ((FirstNodes M).getD 0 0) = false := by
    rw [hf0]
    exact nextR1_TrMax_fail_cv M hM
  exact branch_row1_le_TrMax_of_notnextR_cv M 0 hD hBrpos hnotnx

/-- Isabelle `m_8_2_branch_row1_le_TrMax`: すべての枝先頭の行 1 値は幹右端で
抑えられる（境界 regime は `descendingB` の同点判定で `J = 0` に還元）。 -/
private theorem branch_row1_le_TrMax_cv (M : PS) (J : ℕ)
    (hD : DTPS M) (hJ : J < (Br M).length) :
    entry M 1 ((FirstNodes M).getD J 0) ≤ entry M 1 (TrMax M) := by
  obtain ⟨hR, hmono, hdesc⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hBrne : Br M ≠ [] := by
    intro h
    rw [h] at hJ
    simp at hJ
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htofft := trunk_entries_offset M hM hA (TrMax M) (le_refl _)
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : (FirstNodes M).getD J 0 < Lng M :=
    (leR0_bounds_cv M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2
  have hcoeff : entry M 1 ((FirstNodes M).getD J 0) ≤
      entry M 0 ((FirstNodes M).getD J 0) :=
    reduced_coeff M hR _ hfL
  have hc0FN := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  have hc0val := branch_col0_val M J hD hJ
  by_cases hlt : (Joints M).getD J 0 < TrMax M
  · omega
  · have hj0t : (Joints M).getD J 0 = TrMax M := by omega
    by_cases hJ0 : J = 0
    · rw [hJ0]
      exact branch_row1_le_TrMax_J0_cv M hD hBrne
    · -- 境界 regime: 枝 0 も幹右端に接続し、行 0 先頭が同点になる
      have hJpos : 0 < J := Nat.pos_of_ne_zero hJ0
      have hmonoJ : (Joints M).getD J 0 ≤ (Joints M).getD 0 0 :=
        (FirstNodes_Joints_mono M 0 J hM hmono hJpos hJ).2.1
      have hj00le : (Joints M).getD 0 0 ≤ TrMax M :=
        (FirstNodes_TrMax_Joints M 0 hM hmono hBrpos).1
      have hj00t : (Joints M).getD 0 0 = TrMax M := by omega
      have hc0val0 := branch_col0_val M 0 hD hBrpos
      have hrow0eq : entry ((Br M).getD 0 []) 0 0 =
          entry ((Br M).getD J []) 0 0 := by omega
      have hcd : cdomB ((Br M).getD 0 []) ((Br M).getD J []) = true :=
        (descendingB_iff (Br M)).mp hdesc 0 J (Nat.zero_le J) hJ
      have hrow1le : entry ((Br M).getD J []) 1 0 ≤
          entry ((Br M).getD 0 []) 1 0 :=
        ((cdomB_iff _ _).mp hcd).2 hrow0eq
      have hc1FN := entry_FirstNodes_eq_component_mr M J 1 hM hJ
      have hc1FN0 := entry_FirstNodes_eq_component_mr M 0 1 hM hBrpos
      have hb0le := branch_row1_le_TrMax_J0_cv M hD hBrne
      omega

/-- Isabelle `m_8_2_det_imp_joint_lt_TrMax`: `det`（joint の行 1 値 < 枝先頭の
行 1 値）は境界 regime（joint = 幹右端）を排除する。 -/
theorem det_imp_joint_lt_TrMax (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (det : entry M 1 ((Joints M).getD ((Br M).length - 1) 0) <
      entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) :
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, _⟩ := RTPS_condAB M hR
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1 : (Br M).length - 1 < (Br M).length := by omega
  have hj0le : (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M :=
    (FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ1).1
  have hbnd := branch_row1_le_TrMax_cv M ((Br M).length - 1) hD hJ1
  have htoffj0 := trunk_entries_offset M hM hA
    ((Joints M).getD ((Br M).length - 1) 0) hj0le
  have htofft := trunk_entries_offset M hM hA (TrMax M) (le_refl _)
  omega

/-! ## 本体: 補題（条件(V)の下での右端の親の基本性質） -/

/-- 補題（条件(V)の下での右端の親の基本性質）（§8.2, 原文 L3602）。
`M ∈ RT_PS ∩ PT_PS`、`Br M ≠ ()`、`j₁ := Lng M - 1`、`J₁ := Lng(Br M) - 1`、
`j₀' := Joints(M)_{J₁}`、`j₁' := FirstNodes(M)_{J₁}` とし、
「`m < j₀'`」または「`m = j₀'` かつ `M_{0,j₁'} = M_{1,j₁'}` かつ `Br M` が降順」
ならば、一意な `j₀` が存在して (1) `(0,j₀) <^Next_M (0,j₁)`、(2) `j₀' ≤ j₀`、
(3) `m < j₀` または `M_{0,j₁} = M_{1,j₁}`、(4) `m = j₀ → j₀ < TrMax M`。
Isabelle: `p_8_2_condV_rightmost_parent` / `m_8_2_condV_rightmost_parent`。 -/
theorem condV_rightmost_parent (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hyp : m < (Joints M).getD ((Br M).length - 1) 0 ∨
      (m = (Joints M).getD ((Br M).length - 1) 0 ∧
        entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
        descendingB (Br M) = true)) :
    ∃! j0 : ℕ,
      nextR M 0 j0 (Lng M - 1) = true ∧
      (Joints M).getD ((Br M).length - 1) 0 ≤ j0 ∧
      (m < j0 ∨ entry M 0 (Lng M - 1) = entry M 1 (Lng M - 1)) ∧
      (m = j0 → j0 < TrMax M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1 : (Br M).length - 1 < (Br M).length := by omega
  -- 幾何: `j₀' ≤ TrMax M < j₁' < Lng M`、`j₀' < j₁'`
  have hgeom := FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ1
  have hnxJ := Joints_nextR_FirstNodes M ((Br M).length - 1) hM hmono hJ1
  have hj0'lt : (Joints M).getD ((Br M).length - 1) 0 <
      (FirstNodes M).getD ((Br M).length - 1) 0 :=
    (nextR_implies_row0 M 0 _ _ hnxJ).1
  have hfL : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M :=
    (leR0_bounds_cv M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2
  have hL1 : 1 < Lng M := by omega
  -- 最終列の行 0 親（一意な証人）
  have hpj1 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnx0s : nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true :=
    hasParent_next_fseq M 0 (Lng M - 1) hpj1
  -- 最終枝の祖先性: `j₁' < j₁ → j₁' ≤ j₀`
  have facC : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 →
      (FirstNodes M).getD ((Br M).length - 1) 0 ≤ parent M 0 (Lng M - 1) := by
    intro hlt
    have hblk := wf21_Br_eq_seg M hM hBrne
    have hlenblk : Lng ((Br M).getD ((Br M).length - 1) []) =
        Lng M - 1 + 1 - (FirstNodes M).getD ((Br M).length - 1) 0 := by
      rw [hblk, length_seg]
    rcases Br_component_nonmulti M ((Br M).length - 1) hM hJ1 with hz | hmb
    · exfalso
      simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
      omega
    · have hsegmono : monoT (seg M ((FirstNodes M).getD ((Br M).length - 1) 0)
          (Lng M - 1)) = true := by
        rw [← hblk]
        exact hmb
      have hle0 := le0_monoT_seg_into_list M
        ((FirstNodes M).getD ((Br M).length - 1) 0) (Lng M - 1) (Lng M - 1)
        hM hsegmono (by omega) (le_refl _) (by omega)
      exact le0_above_parent M ((FirstNodes M).getD ((Br M).length - 1) 0)
        (Lng M - 1) hpj1 hle0 (by omega)
  -- (2) `j₀' ≤ j₀`
  have hC2 : (Joints M).getD ((Br M).length - 1) 0 ≤ parent M 0 (Lng M - 1) := by
    by_cases heq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
    · have hjp : (Joints M).getD ((Br M).length - 1) 0 =
          parent M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) :=
        Joints_getD M ((Br M).length - 1) hJ1
      rw [hjp, heq]
    · have hlt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
        omega
      have := facC hlt
      omega
  -- 右分岐（`m = j₀'` 側）の下では `j₀' < TrMax M`（det ルート）
  have hrightlt : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) →
      descendingB (Br M) = true →
      (Joints M).getD ((Br M).length - 1) 0 < TrMax M := by
    intro hE hdesc
    have hD : DTPS M := (DTPS_iff M).mpr ⟨hR, hmono, hdesc⟩
    have he1j0' := joint_row1_eq M ((Br M).length - 1) hD hJ1
    have he0j1' := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1
    have hc0val := branch_col0_val M ((Br M).length - 1) hD hJ1
    have hdet : entry M 1 ((Joints M).getD ((Br M).length - 1) 0) <
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by omega
    exact det_imp_joint_lt_TrMax M hD hBrne hdet
  -- (3)
  have hC3 : m < parent M 0 (Lng M - 1) ∨
      entry M 0 (Lng M - 1) = entry M 1 (Lng M - 1) := by
    rcases hyp with hlt | ⟨heq, hE, hdesc⟩
    · left
      omega
    · by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      · right
        rw [← hj1eq]
        exact hE
      · left
        have hlt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
          omega
        have := facC hlt
        omega
  -- (4)
  have hC4 : m = parent M 0 (Lng M - 1) → parent M 0 (Lng M - 1) < TrMax M := by
    intro hms
    rcases hyp with hlt | ⟨heq, hE, hdesc⟩
    · omega
    · have hlt' := hrightlt hE hdesc
      omega
  -- 一意存在の組み立て
  refine ⟨parent M 0 (Lng M - 1), ⟨hnx0s, hC2, hC3, hC4⟩, ?_⟩
  rintro y ⟨hy, -, -, -⟩
  exact (parent_eq_of_nextR0 M y (Lng M - 1) hy).symm

#print axioms le0_monoT_seg_into_list
#print axioms le0_above_parent
#print axioms wf21_Br_eq_seg
#print axioms joint_row1_eq
#print axioms branch_col0_val
#print axioms det_imp_joint_lt_TrMax
#print axioms condV_rightmost_parent

end PSS
