import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-step»
import «8».«8.1-diagSeq-Trans»
import «7».«7.3-Trans-IncrFirst-Red»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-P-condAB»

/-!
# §8.3 条件(II) — `TV_TrunkLeg`（`CondII_masterCF` の tailval 連鎖の幹脚）

## 目的

ビルド済み «8».«8.3-condII-masterCF-port»:121 の名前付き `Prop` `TV_TrunkLeg` を
house pattern で充足する。これは Isabelle `c2sx_tailval_trunk`
(layerB/pss_wip.thy:87720) の 1:1 移植で、`tvx_Rc M` が純粋な幹
（`TrMax = 最終添字`）である枝を扱う。純幹の簡約祖先切片は明示的に対角
`diagSeq` であり、tailval 値はその対角計算から直接出る。

## Isabelle 側の対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `wnx_trunk_diagSeq` | layerB/pss_wip.thy:80890 | `wnx_trunk_diagSeq`（公開） |
| `c2sx_slice_jm1_c1` | layerB/pss_wip.thy:87633 | `c2sx_slice_jm1_c1`（公開・橋渡し） |
| `c2sx_tailval_trunk` | layerB/pss_wip.thy:87720 | `TV_TrunkLeg_holds`（`TV_TrunkLeg` を drop-in） |

## 依存（ビルド済みのみ）

* «8».«8.3-condII-masterCF-port» — `TV_TrunkLeg` / `tvx_Rc` の定義
* «8».«8.3-condII-step» — 推移的に «8».«8.3-condII-masterCF»
  （`CondII_tailval` / `condII_t4` / `condII_ldj` / `condII_pj` /
  `condII_c1_shape_holds` / `condII_host_basic_holds`）
  ＋ «7».«7.4-Mark-Trans-repr»（`Mark_Trans_repr` / `seg_Pred_eq`）
  ＋ «6».«6.5-Red-le-core»（`trunk_entries_offset`）
  ＋ «6».«6.6-reduced-iff-condAB»（`RTPS_condAB`）
  ＋ «6».«6.8-standard-slice-Br-descending»（`seg_of_seg_68`）
* «8».«8.1-diagSeq-Trans» — `diagSeq_Trans`
* «7».«7.3-Trans-IncrFirst-Red» — `Trans_Red` / `Trans_IncrFirst`
* «6».«6.6-ancestor-slice-Red-IncrFirst» — `ancestor_slice_Red_IncrFirst`
* «6».«6.6-P-condAB» — `RedCondB_head_eq` / `no_parent_zero`

## 状態

* ✅ `wnx_trunk_diagSeq` … 無条件（純幹の簡約列は明示的 `diagSeq`）
* ✅ `c2sx_slice_jm1_c1` … 無仮定 `RTPS`＋`monoT`＋`transCondII`（橋渡し）
* 🤖 `TV_TrunkLeg_holds` … `TV_TrunkLeg`（`RTPS` 形。Isabelle と同じ仮定束）

🚨 仮定は `RTPS M`（`ST_PS` ではない）。`TV_TrunkLeg` の Lean 定義は Isabelle
`c2sx_tailval_trunk` の `M ∈ RT_PS`（＋ `M ∈ PT_PS` ＝ `monoT M`）に 1:1 で対応
（character-by-character 照合済）。
-/

namespace PSS

/-! ## 純幹 = 対角（Isabelle `wnx_trunk_diagSeq`, pss_wip.thy:80890）

簡約列 `R`（`RTPS R`）が純幹（`TrMax R = Lng R - 1`）ならば、`R` は明示的に
対角 `diagSeq (entry R 1 0) (entry R 1 0 + (Lng R - 1))` である。RedCondA が幹に
沿って両段を `+1` させ（`trunk_entries_offset`）、RedCondB が根で対角化する
（`RedCondB_head_eq`）。 -/
theorem wnx_trunk_diagSeq (R : PS) (hR : RTPS R) (htr : TrMax R = Lng R - 1) :
    R = diagSeq (entry R 1 0) (entry R 1 0 + (Lng R - 1)) := by
  have hT : TPS R := RTPS_TPS R hR
  obtain ⟨hA, hB⟩ := RTPS_condAB R hR
  have hpos : 0 < Lng R := List.length_pos_of_ne_nil hT
  have hcol0 : entry R 0 0 = entry R 1 0 := RedCondB_head_eq R hT hB
  apply List.ext_getElem
  · simp only [diagSeq, List.length_map, List.length_range']
    change Lng R = _
    omega
  · intro n hnR hnD
    have hnR' : n < Lng R := by simpa using hnR
    have hn : n ≤ TrMax R := by rw [htr]; omega
    have he := trunk_entries_offset R hT hA n hn
    have he0 : entry R 0 n = entry R 1 0 + n := by rw [he.1, hcol0]
    have he1 : entry R 1 n = entry R 1 0 + n := he.2
    have hRn : R[n] = (entry R 1 0 + n, entry R 1 0 + n) := by
      apply Prod.ext
      · simpa [entry, List.getElem?_eq_getElem hnR'] using he0
      · simpa [entry, List.getElem?_eq_getElem hnR'] using he1
    rw [hRn]
    simp [diagSeq, List.getElem_map, List.getElem_range']

#print axioms wnx_trunk_diagSeq

/-! ## 橋渡し（Isabelle `c2sx_slice_jm1_c1`, pss_wip.thy:87633）

条件(II) ホストの祖先切片 `seg M j₋₁ (Lng M - 2)` の `Trans` 値は、`Pred M` の
基点 `j₋₁ = Adm_M(j₀)` における `Mark` 値
（`= D_{va} t₂`、`c2sx_c1_shape` の結論 (1)）に一致する。`Mark_Trans_repr`
（基点の `Mark` は切片の `Trans`）＋ `seg_Pred_eq`（`Pred` は末尾のみ落とす）で出る。 -/
theorem c2sx_slice_jm1_c1 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    Trans (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))
      = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) (transT2 M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _e1z, _nadmj, _hj0pos, hjm1lt, hw2, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have mkP : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp0
  have jm1ltP : Adm M (parent M 0 (Lng M - 1)) < Lng (Pred M) - 1 := by
    rw [hpredLen]; omega
  have reprP : Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))
      = Trans (seg (Pred M) (Adm M (parent M 0 (Lng M - 1)))
          (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) _ mkP hpredR jm1ltP
  have h2 : Lng (Pred M) - 1 = Lng M - 2 := by rw [hpredLen]; omega
  have segP : seg (Pred M) (Adm M (parent M 0 (Lng M - 1))) (Lng (Pred M) - 1)
      = seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) := by
    rw [h2]
    exact seg_Pred_eq M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) hlen
      (by omega) (by omega)
  have C1 := (condII_c1_shape_holds M hR hmono hj1 hcond).1
  rw [← segP, ← reprP]
  exact C1

#print axioms c2sx_slice_jm1_c1

/-! ## 幾何・不変量の私的補題（`_tl`） -/

/-- 対角列の長さ。 -/
private theorem length_diagSeq_tl (u v : ℕ) : Lng (diagSeq u v) = v + 1 - u := by
  simp [diagSeq]

/-- 対角列の成分は `u + j`（両段共通）。 -/
private theorem entry_diagSeq_tl (u v i j : ℕ) (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v) i j = u + j := by
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

/-- `IncrFirst` は空でなさを保つ。 -/
private theorem TPS_IncrFirst_tl (X : PS) (hX : TPS X) : TPS (IncrFirst X) := by
  show IncrFirst X ≠ []
  simp only [IncrFirst, ne_eq, List.map_eq_nil_iff]
  exact hX

/-- `Trans` は `IncrFirstN` 不変（行 0 の一律増加は `Trans` を変えない）。 -/
private theorem Trans_IncrFirstN_tl (k : ℕ) (X : PS) (hX : TPS X) :
    Trans (IncrFirstN k X) = Trans X := by
  induction k generalizing X with
  | zero => simp [IncrFirstN]
  | succ k ih =>
      rw [IncrFirstN, ih (IncrFirst X) (TPS_IncrFirst_tl X hX)]
      exact Trans_IncrFirst X hX

/-- 切片は `IncrFirstN` と可換（範囲内）。 -/
private theorem seg_IncrFirstN_tl (sh : ℕ) (X : PS) (a b : ℕ) (hb : b < Lng X) :
    seg (IncrFirstN sh X) a b = IncrFirstN sh (seg X a b) := by
  apply List.ext_getElem
  · simp [IncrFirstN_eq_map]
  · intro i h1 h2
    have hib : i < b + 1 - a := by simpa using h1
    have hiX : a + i < Lng X := by omega
    have h2' : i < Lng (seg X a b) := by simp; omega
    rw [seg_getElem_68 (IncrFirstN sh X) a b i h1,
      entry_IncrFirstN_zero sh X (a + i) hiX, entry_IncrFirstN_one sh X (a + i)]
    simp only [IncrFirstN_eq_map, List.getElem_map]
    rw [seg_getElem_68 X a b i h2']

/-- `Dprin` の本体は単射（頭が一致すれば本体も一致）。 -/
private theorem Dprin_body_inj_tl {v : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin v b) : a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq] at h
  tauto

/-- 対角列の末尾切片は再び対角列（左端が `d` 桁だけ右へ）。 -/
private theorem segdrop_diagSeq_tl (u w d : ℕ) (hd : d < Lng (diagSeq u w)) :
    seg (diagSeq u w) d (Lng (diagSeq u w) - 1) = diagSeq (u + d) w := by
  have hd' : d < w + 1 - u := by rwa [length_diagSeq_tl] at hd
  apply List.ext_getElem
  · simp only [length_seg, length_diagSeq_tl]
    omega
  · intro n h1 h2
    have hdn : d + n < Lng (diagSeq u w) := by
      simp only [length_seg, length_diagSeq_tl] at h1
      rw [length_diagSeq_tl]
      omega
    rw [seg_getElem_68 (diagSeq u w) d (Lng (diagSeq u w) - 1) n h1,
      entry_diagSeq_tl u w 0 (d + n) hdn, entry_diagSeq_tl u w 1 (d + n) hdn]
    have hassoc : u + (d + n) = u + d + n := by omega
    rw [hassoc]
    simp [diagSeq, List.getElem_map, List.getElem_range']

/-! ## 幹脚本体（Isabelle `c2sx_tailval_trunk`, pss_wip.thy:87720）

`tvx_Rc M`（＝ ホストの簡約祖先切片 `R`）が純幹ならば、`R` は対角 `diagSeq u w`
（`wnx_trunk_diagSeq`）。`R` は `seg M j₋₁ (Lng M - 2)` の `IncrFirstN` 剥ぎ
（`ancestor_slice_Red_IncrFirst`）なので、行 1 成分と末尾切片の `Trans` が対角計算で
明示化される。`leftDj0`（＝`condII_ldj`）は `w' = v₀` を要求するが `d < Lng R - 1`
に反するので偽（`w' = u + (Lng R - 1) > u + d = v₀`）。したがって `t₄ = t₂`、
終切片の値は `D_{v₀} t₂ = D_{u+d}(D_{w'} 0)`。 -/
theorem TV_TrunkLeg_holds : TV_TrunkLeg := by
  intro M hR hmono hj1 hcond hTR
  simp only [tvx_Rc] at hTR
  unfold CondII_tailval
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _e1z, _nadmj, _hj0pos, hjm1lt, hw2, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  set j0 := parent M 0 (Lng M - 1) with hj0def
  set jm1 := Adm M j0 with hjm1def
  -- 添字の基本境界
  have hjm1_lt : jm1 < Lng M - 2 := by omega
  have hj0_lt : j0 < Lng M - 2 := by omega
  have hjm1_le_j0 : jm1 ≤ j0 := by rw [hjm1def]; exact Adm_le M j0
  -- 到達性 `leab`：`Pred M` の基点 → prefix 転送
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have mkP : Marked (Pred M) jm1 := Marked_Pred_Adm M hM hlen hp0
  have hle0M : le0 M jm1 (Lng M - 2) = true := by
    have hmkle : le0 (Pred M) jm1 (Lng (Pred M) - 1) = true := by
      simpa [leR] using mkP.2.2
    rw [hpredLen] at hmkle
    have he : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [he, Pred_eq_take M hlen] at hmkle
    rwa [le0_take_adm M (Lng M - 1) jm1 (Lng M - 2)
      (by omega) (by omega) (by omega)] at hmkle
  have hanc : leR M 0 jm1 (Lng M - 2) = true := by simpa [leR] using hle0M
  -- 簡約祖先切片 `R = Red S`, `S = IncrFirstN kk R`
  have hj1le : Lng M - 2 ≤ Lng M - 1 := by omega
  have hfacts := ancestor_slice_Red_IncrFirst M jm1 (Lng M - 2) hR hjm1_lt hj1le hanc
  simp only [] at hfacts
  set S := seg M jm1 (Lng M - 2) with hSdef
  set R := Red S with hRdef
  obtain ⟨hRedN, _hmonoN, hIF⟩ := hfacts
  set kk := entry M 0 jm1 - entry M 1 jm1 with hkdef
  -- 長さ・空でなさ・簡約性
  have hLS : Lng S = Lng M - 1 - jm1 := by rw [hSdef, length_seg]; omega
  have hLR : Lng R = Lng M - 1 - jm1 := by
    have hmap : Lng (IncrFirstN kk R) = Lng R := by simp [IncrFirstN_eq_map]
    have h2 := congrArg Lng hIF
    rw [hmap] at h2
    rw [← h2, hLS]
  have hRpos : 0 < Lng R := by omega
  have hRT : TPS R := List.ne_nil_of_length_pos hRpos
  have hSpos : 0 < Lng S := by omega
  have hST : TPS S := List.ne_nil_of_length_pos hSpos
  have hRTPS : RTPS R := by
    show reduced R = true
    have hne : R ≠ [] := hRT
    simp [reduced, hne, hRedN]
  -- 対角形
  have hdiag := wnx_trunk_diagSeq R hRTPS hTR
  set u := entry R 1 0 with hudef
  set w := u + (Lng R - 1) with hwdef
  set d := j0 - jm1 with hddef
  have hjm1d : jm1 + d = j0 := by rw [hddef]; omega
  have hd_lt : d < Lng R - 1 := by rw [hddef, hLR]; omega
  have huw : u < w := by rw [hwdef]; omega
  have hudw : u + d < w := by rw [hwdef]; omega
  -- 行 1 成分の読み出し
  have hvau : entry M 1 jm1 = u := by
    have e1 : entry S 1 0 = entry M 1 jm1 := by
      rw [hSdef, entry_seg M jm1 (Lng M - 2) 1 0 (by rw [length_seg]; omega)]; simp
    have e2 : entry S 1 0 = u := by
      rw [hIF, entry_IncrFirstN_one]
    rw [← e1, e2]
  have hv0 : entry M 1 j0 = u + d := by
    have e1 : entry S 1 d = entry M 1 j0 := by
      rw [hSdef, entry_seg M jm1 (Lng M - 2) 1 d (by rw [length_seg]; omega)]
      rw [hjm1d]
    have e2 : entry S 1 d = u + d := by
      rw [hIF, entry_IncrFirstN_one, hdiag,
        entry_diagSeq_tl u w 1 d (by rw [← hdiag]; omega)]
    rw [← e1, e2]
  -- 終切片の `Trans` 値（対角計算）
  have hmain : Trans (seg M j0 (Lng M - 2))
      = Dprin ((u + d : ℕ) : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    have hseg1 : seg M j0 (Lng M - 2) = seg S d (Lng R - 1) := by
      rw [hSdef,
        seg_of_seg_68 M jm1 (Lng M - 2) d (Lng R - 1) (by omega) (by omega)]
      rw [show jm1 + d = j0 from hjm1d, show jm1 + (Lng R - 1) = Lng M - 2 by omega]
    have hseg2 : seg S d (Lng R - 1) = IncrFirstN kk (seg R d (Lng R - 1)) := by
      rw [hIF]
      exact seg_IncrFirstN_tl kk R d (Lng R - 1) (by omega)
    have hseg3 : seg R d (Lng R - 1) = diagSeq (u + d) w := by
      rw [hdiag]
      exact segdrop_diagSeq_tl u w d (by rw [← hdiag]; omega)
    have hTPSdiag : TPS (diagSeq (u + d) w) := by
      apply List.ne_nil_of_length_pos
      simp only [length_diagSeq_tl]; omega
    rw [hseg1, hseg2, hseg3,
      Trans_IncrFirstN_tl kk (diagSeq (u + d) w) hTPSdiag,
      diagSeq_Trans (u + d) w hudw]
  -- 橋渡しで `t₂ = D_{w'} 0` を確定
  have hTransS_diag : Trans S = Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    rw [show Trans S = Trans R from by rw [hRdef]; exact Trans_Red S hST]
    rw [hdiag, diagSeq_Trans u w huw]
  have hbridge := c2sx_slice_jm1_c1 M hR hmono hj1 hcond
  rw [← hj0def, ← hjm1def, ← hSdef, hvau] at hbridge
  have hDeq : Dprin (u : ℕ∞) (transT2 M)
      = Dprin (u : ℕ∞) (Dprin (w : ℕ∞) BZero) := by
    rw [← hbridge]; exact hTransS_diag
  have ht2E : transT2 M = Dprin (w : ℕ∞) BZero := Dprin_body_inj_tl hDeq
  -- `leftDj0` の反証：`t₄ = t₂`
  have hPB : PB (Dprin (w : ℕ∞) BZero) = [Dprin (w : ℕ∞) BZero] := by
    simp [PB, Dprin, untrm]
  have hpj : condII_pj M = Dprin (w : ℕ∞) BZero := by
    unfold condII_pj
    rw [ht2E, hPB]
    rfl
  have hldj : condII_ldj M = false := by
    have hbp : bpHeadV (condII_pj M) = (w : ℕ∞) := by rw [hpj]; rfl
    have htj : entry M 1 (transJ0 M) = u + d := by
      have htj0 : transJ0 M = j0 := by
        simp only [transJ0, lastParent, lastIdx]; exact hj0def.symm
      rw [htj0]; exact hv0
    simp only [condII_ldj, hbp, htj]
    refine Bool.eq_false_iff.mpr ?_
    rw [ne_eq, beq_iff_eq]
    intro hc
    have hwd : w = u + d := by exact_mod_cast hc
    omega
  have ht4E : condII_t4 M = transT2 M := by simp [condII_t4, hldj]
  -- 組み立て
  rw [hmain, hv0, ht4E, ht2E]

#print axioms TV_TrunkLeg_holds

end PSS
