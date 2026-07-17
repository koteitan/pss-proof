import «8».«8.3-condII-masterCF-port»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»

/-!
# §8.3 条件(II) — `TV_R3LE`（`tvx_fn_row_bound`）: 最後の first node での行境界

Isabelle 対応:
* `tvx_fn_row_bound` (layerB/pss_wip.thy:110857, ~85 行) → `TV_R3LE_holds`
  （`TV_R3LE` Prop は «8».«8.3-condII-masterCF-port»:155 で既定義。house pattern で
  その Prop を型として drop-in 証明する）。

`CondII_masterCF` の `tailval` 連鎖の 6 残差
（`TV_Dichotomy`/`TV_TrunkLeg`/`TV_BoundaryLeg`/`TV_NotLdjLeg`/`TV_LDJB`/`TV_R3LE`）の
うち **R3LE を無条件で閉じる**。他の 5 本は別 wave。

## Isabelle 証明骨格（`tvx_fn_row_bound`）
`Rc := Red (seg K (Adm K (parent K 0 (Lng K-1))) (Lng K-2))`（= `tvx_Rc K`）を
`c2sx_reach` の到達性 `leab` と `standard_slice_Red_strongmono` で `DT_PS` に落とし、
最後の枝 first node `fn` で `entry Rc 1 fn ≤ entry Rc 0 fn` を示す:
* 行0下界: `joints_lt_branch_first` + `entry_FirstNodes_eq_component`
  で `entry Rc 0 0 + jL + 1 ≤ entry Rc 0 fn`。
* 行1上界: 行1辺 `(1,jL)<^Next(1,fn)` の場合分け（`RedCondA` / `e1_le_e1par_of_notnextR1`）
  で `entry Rc 1 fn ≤ entry Rc 1 jL + 1`。
* `offs`(`trunk_entries_offset`) + `diag00`(`RTPS_mono_head_eq`) で連結。

## 依存（すべて COMMITTED 緑）
* 既存公開: `standard_slice_Red_strongmono` / `FirstNodes_TrMax_Joints` /
  `trunk_entries_offset` / `RTPS_mono_head_eq`(=`kfwd_reduced_monoT_diag00`) /
  `entry_FirstNodes_eq_component_mr` / `Joints_nextR_FirstNodes`(=`Joints_parent_nextR`) /
  `nextR1_unique_mr` / `RTPS_condAB` / `condII_host_basic_holds` / `Marked_Pred_Adm` /
  `RTPS_Pred`(=`Pred_RT_PS`) / `entry_Pred` / `length_Pred` / `ancestor_basic_1` /
  `parent_exists_3` / `parent_eq_of_nextR0` / `RedCondA_apply` / `mono_slice_next` /
  `TrMax_trunk_step`(=`TrMax_in_S`) / `le0_above_parent` / `parent_exists_2` /
  `hasParent_next_fseq` / `nextR_implies_row0` / `DTPS_iff` / `DTPS_TPS`.
* 私的移植（`_r3`, 親が昇格すべき cross-scope 補題は "needs" 参照）:
  `trunk_row0_inc_r3`(=`trunk_row0_inc`) / `joints_lt_branch_first_r3`(=`joints_lt_branch_first`) /
  `a1_FN_hasParent_r3`(=`a1_FN_hasParent`) / `a1_FN_lt_r3`(=`a1_FN_lt`) /
  `e1_le_e1par_of_notnextR1_r3`(=`m_8_2_e1_le_e1par_of_notnextR1`) /
  `condII_reach_r3`（=`c2sx_reach` の `leab` 脚。`le0_prefix_agree`/`Pred_RT_PS` は
  値特徴付け `ancestor_basic_1`+`parent_exists_3`+`entry_Pred` で迂回）。

## 状態
✅ `TV_R3LE_holds : TV_R3LE`（sorry 0, 無条件, 公理 3 個）。
-/

namespace PSS

/-- `trunk_row0_inc` (pss_mechanized.thy:6104): 幹上（`j ≤ TrMax M`）では行0値が
少なくとも `j` だけ増える。`TrMax_trunk_step`(=`TrMax_in_S`) + `ancestor_basic_1`。 -/
private theorem trunk_row0_inc_r3 (M : PS) (hM : TPS M) :
    ∀ j, j ≤ TrMax M → j < Lng M → entry M 0 0 + j ≤ entry M 0 j := by
  intro j
  induction j with
  | zero => intro _ _; simp
  | succ j' ih =>
    intro hjt hjL
    have hjt' : j' < TrMax M := by omega
    have hstep := TrMax_trunk_step M j' hM hjt'
    have hle0 : le0 M j' (j' + 1) = true := by
      have hn1 : nextrel1 M j' (j' + 1) = true := by simpa [nextR] using hstep
      have h := hn1
      simp only [nextrel1, Bool.and_eq_true] at h
      exact h.1.2
    have hleR : leR M 0 j' (j' + 1) = true := by simpa [leR] using hle0
    have hinc : entry M 0 j' < entry M 0 (j' + 1) :=
      ancestor_basic_1 M j' (j' + 1) (j' + 1) hM (Nat.lt_succ_self j') (le_refl _) hleR
    have hIH := ih (by omega) (by omega)
    omega

/-- `joints_lt_branch_first` (pss_mechanized.thy:6205): 最後の枝成分の左端の行0値は
幹の対角上昇 + 親辺の跳躍で `entry M 0 0 + Joints!J + 1` を下回らない。 -/
private theorem joints_lt_branch_first_r3 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    entry M 0 0 + (Joints M).getD J 0 + 1 ≤ entry ((Br M).getD J []) 0 0 := by
  have hjtj := (FirstNodes_TrMax_Joints M J hM hmono hJ).1
  have htb := TrMax_bound M hM
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : (Joints M).getD J 0 < Lng M := by omega
  have htrunk := trunk_row0_inc_r3 M hM ((Joints M).getD J 0) hjtj hjL
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hstrict : entry M 0 ((Joints M).getD J 0) < entry M 0 ((FirstNodes M).getD J 0) := by
    have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
      simpa [nextR] using hnx
    have h := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  have hec := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  omega

/-- `a1_FN_hasParent` (pss_mechanized.thy:33161): 枝 first node は行0で親を持つ。
`mono_slice_next` + `FirstNodes_getD`。 -/
private theorem a1_FN_hasParent_r3 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    hasParent M 0 ((FirstNodes M).getD J 0) = true := by
  have htb := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hbr : Br M = [] := by simp [Br, heq]
    rw [hbr] at hJ; simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]; omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  exact hn.1

/-- `a1_FN_lt` (pss_mechanized.thy:33187): 枝 first node は範囲内。 -/
private theorem a1_FN_lt_r3 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnx
  have h := hn0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- `m_8_2_e1_le_e1par_of_notnextR1`: 行1辺 `(1,parent)<^Next(1,j)` が立たなければ
行1値は行0親で抑えられる（`8.2-condV-rightmost-parent` の私的 `_cv` の複製）。 -/
private theorem e1_le_e1par_of_notnextR1_r3 (M : PS) (j : ℕ) (hM : TPS M)
    (hp0 : hasParent M 0 j = true) (hjL : j < Lng M)
    (hnotnx : nextR M 1 (parent M 0 j) j = false) :
    entry M 1 j ≤ entry M 1 (parent M 0 j) := by
  have hparR := hasParent_next_fseq M 0 j hp0
  have hplt : parent M 0 j < j := (nextR_implies_row0 M 0 _ j hparR).1
  have hleR : leR M 0 (parent M 0 j) j = true := (nextR_implies_row0 M 0 _ j hparR).2
  by_contra hgt
  have helt : entry M 1 (parent M 0 j) < entry M 1 j := by omega
  obtain ⟨p1, hp1ge, hp1lt, hp1nx⟩ :=
    parent_exists_2 M (parent M 0 j) j hM hplt hjL helt hleR
  have hp1nx1 : nextrel1 M p1 j = true := by simpa [nextR] using hp1nx
  have hle0p1 : le0 M p1 j = true := by
    have hh := hp1nx1
    simp only [nextrel1, Bool.and_eq_true] at hh
    exact hh.1.2
  have hp1le : p1 ≤ parent M 0 j := le0_above_parent M p1 j hp0 hle0p1 (by omega)
  have hp1eq : p1 = parent M 0 j := by omega
  rw [hp1eq] at hp1nx
  rw [hp1nx] at hnotnx
  exact Bool.noConfusion hnotnx

/-- `c2sx_reach` (layerB/pss_wip.thy:87666) の到達性脚 `leab`:
`(Pred K, a) ∈ Marked` から `leR K 0 a (Lng K - 2)`。
Isabelle は `Pred_RT_PS` + `le0_prefix_agree` を rtrancl 帰納で回すが、ここでは値特徴付け
`ancestor_basic_1` + `parent_exists_3` + `entry_Pred`（前者切片との接尾一致）で迂回する。 -/
private theorem condII_reach_r3 (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
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

/-- `tvx_fn_row_bound` (layerB/pss_wip.thy:110857) の Lean 形。
`TV_R3LE` Prop（«8».«8.3-condII-masterCF-port»:155）を型として drop-in 証明する。 -/
theorem TV_R3LE_holds : TV_R3LE := by
  intro K hST hmono hj1 hII hBR
  have hKR : RTPS K := STPS_RTPS K hST
  have hKT : TPS K := RTPS_TPS K hKR
  have hL : 1 < Lng K := by omega
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds K hKR hmono hj1 hII
  -- 到達性: `leab` と反則インデックス `ab`
  have hab : Adm K (parent K 0 (Lng K - 1)) < Lng K - 2 := by omega
  have hmk : Marked (Pred K) (Adm K (parent K 0 (Lng K - 1))) :=
    Marked_Pred_Adm K hKT hL hp0
  have leab : leR K 0 (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2) = true :=
    condII_reach_r3 K (Adm K (parent K 0 (Lng K - 1))) hKR hL hmk hab
  have hbL2 : Lng K - 2 ≤ Lng K - 1 := by omega
  -- `Rc = tvx_Rc K` は `DT_PS`
  have hRcDT : DTPS (tvx_Rc K) :=
    standard_slice_Red_strongmono K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2)
      hST hab hbL2 leab
  have hRcRT : RTPS (tvx_Rc K) := ((DTPS_iff (tvx_Rc K)).mp hRcDT).1
  have hmonoRc : monoT (tvx_Rc K) = true := ((DTPS_iff (tvx_Rc K)).mp hRcDT).2.1
  have hRcT : TPS (tvx_Rc K) := DTPS_TPS (tvx_Rc K) hRcDT
  -- 枝の非空性と最終枝インデックス `BL`
  have hBrne : Br (tvx_Rc K) ≠ [] := hBR
  have hBLpos : 0 < (Br (tvx_Rc K)).length := List.length_pos_of_ne_nil hBrne
  have hBLlt : (Br (tvx_Rc K)).length - 1 < (Br (tvx_Rc K)).length := by omega
  -- joint ≤ TrMax、RedCondA、offs、diag00
  have hjle : (Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0 ≤ TrMax (tvx_Rc K) :=
    (FirstNodes_TrMax_Joints (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) hRcT hmonoRc hBLlt).1
  have hcondARc : RedCondA (tvx_Rc K) = true := (RTPS_condAB (tvx_Rc K) hRcRT).1
  obtain ⟨hoff0, hoff1⟩ := trunk_entries_offset (tvx_Rc K) hRcT hcondARc
    ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) hjle
  have hdiag := RTPS_mono_head_eq (tvx_Rc K) hRcRT hmonoRc
  -- 行0下界 `e0lb`
  have hjlb := joints_lt_branch_first_r3 (tvx_Rc K) ((Br (tvx_Rc K)).length - 1)
    hRcT hmonoRc hBLlt
  have hfneq : entry (tvx_Rc K) 0 (tvx_fn K)
      = entry ((Br (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) 0 hRcT hBLlt
  have he0lb : entry (tvx_Rc K) 0 0
      + (Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0 + 1
      ≤ entry (tvx_Rc K) 0 (tvx_fn K) := by
    rw [hfneq]; exact hjlb
  -- joint は fn の行0親
  have hnx0 : nextR (tvx_Rc K) 0
      ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) (tvx_fn K) = true :=
    Joints_nextR_FirstNodes (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) hRcT hmonoRc hBLlt
  have hfnL : tvx_fn K < Lng (tvx_Rc K) :=
    a1_FN_lt_r3 (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) hRcT hmonoRc hBLlt
  -- 行1上界 `e1ub`
  have he1ub : entry (tvx_Rc K) 1 (tvx_fn K)
      ≤ entry (tvx_Rc K) 1 ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) + 1 := by
    by_cases hcase : nextR (tvx_Rc K) 1
        ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) (tvx_fn K) = true
    · -- 行1辺あり: 行1親一意 (`nextR1_unique_mr`) + `RedCondA`
      have hp1 : hasParent (tvx_Rc K) 1 (tvx_fn K) = true := by
        apply (hasParent_iff_unique_fseq (tvx_Rc K) 1 (tvx_fn K)).mpr
        exact ⟨(Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0, hcase,
          fun q hq => nextR1_unique_mr (tvx_Rc K) q _ (tvx_fn K) hq hcase⟩
      have hApp := RedCondA_apply (tvx_Rc K) hcondARc 1 (tvx_fn K) (by omega) hfnL hp1
      have hp1eq : parent (tvx_Rc K) 1 (tvx_fn K)
          = (Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0 := by
        have hpr := hasParent_next_fseq (tvx_Rc K) 1 (tvx_fn K) hp1
        exact nextR1_unique_mr (tvx_Rc K) _ _ (tvx_fn K) hpr hcase
      rw [hp1eq] at hApp
      omega
    · -- 行1辺なし: `e1_le_e1par_of_notnextR1_r3`
      have hfalse : nextR (tvx_Rc K) 1
          ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) (tvx_fn K) = false := by
        cases hb : nextR (tvx_Rc K) 1
            ((Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0) (tvx_fn K) with
        | true => exact absurd hb hcase
        | false => rfl
      have hp0R : hasParent (tvx_Rc K) 0 (tvx_fn K) = true :=
        a1_FN_hasParent_r3 (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) hRcT hmonoRc hBLlt
      have hp0eq : parent (tvx_Rc K) 0 (tvx_fn K)
          = (Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0 :=
        parent_eq_of_nextR0 (tvx_Rc K) _ (tvx_fn K) hnx0
      have hnotnx : nextR (tvx_Rc K) 1 (parent (tvx_Rc K) 0 (tvx_fn K)) (tvx_fn K) = false := by
        rw [hp0eq]; exact hfalse
      have he1le := e1_le_e1par_of_notnextR1_r3 (tvx_Rc K) (tvx_fn K) hRcT hp0R hfnL hnotnx
      rw [hp0eq] at he1le
      omega
  -- 連結: `e1ub` + `offs` + `diag00` + `e0lb`
  omega

#print axioms TV_R3LE_holds

end PSS
