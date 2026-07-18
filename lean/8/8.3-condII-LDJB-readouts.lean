import «8».«8.3-condII-LDJB»
import «8».«8.3-condII-TrunkLeg»
import «8».«8.7-otpred-brickC0»
import «7».«7.3-Trans-IncrFirst-Red»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.2-mono-ancestor-slice»
import «7».«7.3-Trans-welldefined»
import «6».«6.3-admof-slice»

/-!
# §8.3 条件(II) — `TV_LDJB` の露出残差の読み出し（`ljx_RightNodes_*` / `pos1ldj`）

## 目的

ビルド済み «8».«8.3-condII-LDJB» が露出した 5 本の campaign-size 残差 `Prop` のうち、
Buchholz 項機構を使わずに閉じられる **2 本**を Isabelle の証明構造で無条件に discharge し、
残り 3 本を仮定に取る `TV_LDJB` 組み立てを green で bank する。

## Isabelle 対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル | 状態 |
|---|---|---|---|
| `ljx_RightNodes_pj_ldj`    | layerB/pss_wip.thy:114535 | `RN_ldj_pj_holds`     | ✅ 無条件 |
| `pos1ldj`(`ljx_LDJB` 内)   | layerB/pss_wip.thy:115180 | `TVX_pos1ldj_holds`   | ✅ 無条件 |
| `ljx_RightNodes_a0_trmax`  | layerB/pss_wip.thy:114607 | （未移植、`needs`）   | 🤖 |
| `ljx_RightNodes_a0_lt_trmax`| layerB/pss_wip.thy:114847 | （未移植、`needs`）   | 🤖 |
| `tvx_d_lt_TrMax`           | layerB/pss_wip.thy:110442 | （並列 VE agent 担当） | 🤖 |
| `ljx_LDJB` の組み立て       | layerB/pss_wip.thy:115131 | `TV_LDJB_of_three_lr` | ✅ 3 残差 modulo |

## 証明構造

### `RN_ldj_pj_holds`（= `ljx_RightNodes_pj_ldj`）

`Trans (tvx_Rc M) = Dprin (entry M 1 j₋₁) (transT2 M)` を橋 `c2sx_slice_jm1_c1`
（`8.3-condII-TrunkLeg`）と `Trans_Red`（`7.3-Trans-IncrFirst-Red`、`wnx_seg_transport`
の役割）で得て、`RightNodes (Dprin v a) = v.toNat :: RightNodes a` で展開。第 2 成分は
`condII_ldj`（`bpHeadV (condII_pj M) = entry M 1 (transJ0 M)`）＝ `transT2 M` の最後の
principal の頭部値、で同定（`rnsub_RightNodes_last` を concat 帰納で再現）。
`entry (tvx_Rc M) 1 0 = entry M 1 j₋₁`（`repr_entry1_shift_gen`）は
`ancestor_slice_Red_IncrFirst`（`6.6`）＋`entry_IncrFirstN_one`（`6.5`）で構成。

### `TVX_pos1ldj_holds`（= `ljx_LDJB` 内の `pos1ldj` 段）

`entry M 1 j₀ = entry (tvx_Rc M) 1 0 + tvx_d M`。`wnx_run_entries`
（`8.7-otpred-brickC0`）で非許容 run に沿った行 1 の一次性
`entry M 1 (j₋₁ + d) = entry M 1 j₋₁ + d` を得て、`j₋₁ + d = j₀`（`Adm ≤ j₀`）と
`e0`（上の `slice_e0_lr`）で連結。

## 依存（すべて COMMITTED 緑）

* «8».«8.3-condII-LDJB» — 露出 `Prop`（`RN_ldj_pj_ldjb` / `TVX_pos1ldj_ldjb` / …）／
  `TV_LDJB` / `TV_LDJB_of_readouts` / `tvx_Rc` / `tvx_d` / `condII_host_basic_holds` /
  `condII_pj` / `condII_ldj` / `transT2` / `transJ0`。
* «8».«8.3-condII-TrunkLeg» — `c2sx_slice_jm1_c1`（切片基点の `Trans` 表示）。
* «8».«8.7-otpred-brickC0» — `wnx_run_entries`（非許容 run の行 0/1 一次性）。
* «7».«7.3-Trans-IncrFirst-Red» — `Trans_Red`（`Red` は `Trans` 不変）。
* «6».«6.6-ancestor-slice-Red-IncrFirst» — `ancestor_slice_Red_IncrFirst`。
* «6».«6.2-mono-ancestor-slice» — `entry_seg`。
* «7».«7.3-Trans-welldefined» — `Marked_Pred_Adm`／`condII_reach_lr` の土台。
* «6».«6.3-admof-slice» — `Adm_le`。

## 状態

* ✅ `RN_ldj_pj_holds` / `TVX_pos1ldj_holds`（sorry 0、axiom = [propext, Classical.choice,
  Quot.sound]）。
* ✅ `TV_LDJB_of_three_lr`: `TV_LDJB` を残り 3 残差
  `RN_a0_trmax_ldjb` / `RN_a0_lt_trmax_ldjb` / `TVX_dstrict_ldjb` のみを仮定して閉じる
  （上の 2 本を `TV_LDJB_of_readouts` に配線）。
* 🤖 未移植 3 残差は `needs` に報告（`ljx_RightNodes_a0_trmax` は `Marked (tvx_Rc) (TrMax)`
  ＝ `ljx_lastblock_le0`（`wf21_Br_eq_seg`＋`Br_component_nonmulti`＋`le0_monoT_seg_into_list`）
  ＋幹対角 `segdiag`（`diag00`／`leR0`推移律 未移植）を要する重い脚。`ljx_RightNodes_a0_lt_trmax`
  は ~278 行の最重量。`tvx_d_lt_TrMax` は並列 VE agent が担当）。
-/

namespace PSS

/-! ## `RightNodes` / `PB` 展開の私的補題（`_lr`） -/

/-- `Dprin` の `RightNodes` 展開（`RightNodes (D_v a) = v.toNat :: RightNodes a`）。 -/
private theorem RightNodes_Dprin_lr (v : ℕ∞) (a : BT) :
    RightNodes (Dprin v a) = v.toNat :: RightNodes a := by
  simp only [Dprin, RightNodes, rightNodesList, rightNodesBP]

/-- Isabelle `rnsub_RightNodes_last`: `rightNodesList` は末尾 principal のみを見る。 -/
private theorem rnl_concat_lr (init : List BP) (p : BP) :
    rightNodesList (init ++ [p]) = rightNodesBP p := by
  induction init with
  | nil => rfl
  | cons a init ih =>
    cases init with
    | nil => rfl
    | cons b rest =>
      simp only [List.cons_append] at ih ⊢
      rw [show rightNodesList (a :: b :: (rest ++ [p]))
            = rightNodesList (b :: (rest ++ [p])) from rfl]
      exact ih

/-- `PB (Trm (ps ++ [p]))` の最後の成分は `Trm [p]`（`condII_pj` の閉形式）。 -/
private theorem pb_getD_last_lr (ps : List BP) (p : BP) :
    (PB (BT.trm (ps ++ [p]))).getD ((ps ++ [p]).length - 1) BZero = BT.trm [p] := by
  simp only [PB, untrm, List.map_append, List.map_cons, List.map_nil]
  rw [List.getD_eq_getElem?_getD]
  simp

/-- 全 `BT` は `Trm`（一構成子）: `Trm (untrm t) = t`。 -/
private theorem trm_untrm_lr (t : BT) : BT.trm (untrm t) = t := by
  cases t with | trm ps => rfl

/-! ## 到達性脚 `leab`（R3LE `condII_reach_r3` の逐語複製、private は module 跨ぎ不可） -/

/-- Isabelle `c2sx_reach`(1) の `leab` 脚。`Pred K` の基点性から `parent_exists_3` の
値特徴付け（`ancestor_basic_1`＋`entry_Pred`）で `le0`（したがって `leR`）を構成。 -/
private theorem condII_reach_lr (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
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

/-! ## `repr_entry1_shift_gen`（`k = 0`）: `tvx_Rc` の位置 0 は宿主の `j₋₁` の行 1 -/

/-- Isabelle `repr_entry1_shift_gen`(k=0) (layerB:12828): `entry (tvx_Rc M) 1 0
    = entry M 1 (Adm M j₀)`。`ancestor_slice_Red_IncrFirst` の `IncrFirstN` 復元と
`entry_IncrFirstN_one`（`IncrFirstN` は行 1 を保つ）で構成。 -/
private theorem slice_e0_lr (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    entry (tvx_Rc M) 1 0 = entry M 1 (Adm M (parent M 0 (Lng M - 1))) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _hE1z, _hNadm, _hParPos, hAdmLt, hParLt, _hCond, _hVI, _hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  have hb2 : Lng M - 2 ≤ Lng M - 1 := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp0
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    condII_reach_lr M (Adm M (parent M 0 (Lng M - 1))) hR hlen hmk hab
  have hIF : seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)
      = IncrFirstN (entry M 0 (Adm M (parent M 0 (Lng M - 1)))
            - entry M 1 (Adm M (parent M 0 (Lng M - 1))))
          (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))) :=
    (ancestor_slice_Red_IncrFirst M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)
      hR hab hb2 leab).2.2
  have hseg : entry (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) 1 0
      = entry M 1 (Adm M (parent M 0 (Lng M - 1))) := by
    have := entry_seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) 1 0
      (by rw [length_seg]; omega)
    simpa using this
  have htvx : tvx_Rc M = Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) := rfl
  rw [htvx]
  calc entry (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))) 1 0
      = entry (IncrFirstN (entry M 0 (Adm M (parent M 0 (Lng M - 1)))
            - entry M 1 (Adm M (parent M 0 (Lng M - 1))))
          (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)))) 1 0 :=
        (entry_IncrFirstN_one _ _ 0).symm
    _ = entry (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) 1 0 := by rw [← hIF]
    _ = entry M 1 (Adm M (parent M 0 (Lng M - 1))) := hseg

/-! ## (1) `RN_ldj_pj_holds` = Isabelle `ljx_RightNodes_pj_ldj` -/

/-- Isabelle `ljx_RightNodes_pj_ldj` (layerB/pss_wip.thy:114535) の 1:1 移植。
`ldj` 側の `RightNodes (Trans (tvx_Rc M))` の位置 0/1 読み出し。 -/
theorem RN_ldj_pj_holds : RN_ldj_pj_ldjb := by
  intro M hR hmono hj1 hcond hldj
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hp0, _hE1z, _hNadm, _hParPos, hAdmLt, hParLt, _hCond, _hVI, hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  have hb2 : Lng M - 2 ≤ Lng M - 1 := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp0
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    condII_reach_lr M (Adm M (parent M 0 (Lng M - 1))) hR hlen hmk hab
  have hSegT : TPS (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))
    rw [length_seg]; omega
  -- W1: `Trans (seg …) = Trans (tvx_Rc M)`（`wnx_seg_transport` の役割）
  have hW1 : Trans (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)) = Trans (tvx_Rc M) :=
    Trans_Red _ hSegT
  -- 橋: `Trans (seg …) = Dprin (entry M 1 j₋₁) (transT2 M)`
  have hbridge : Trans (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2))
      = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) (transT2 M) :=
    c2sx_slice_jm1_c1 M hR hmono hj1 hcond
  have hTRc : Trans (tvx_Rc M)
      = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) (transT2 M) :=
    hW1.symm.trans hbridge
  have he0 : entry (tvx_Rc M) 1 0 = entry M 1 (Adm M (parent M 0 (Lng M - 1))) :=
    slice_e0_lr M hR hmono hj1 hcond
  -- `transT2 M ≠ 0_B` から `untrm (transT2 M) ≠ []`、末尾 principal を分解
  have hps_ne : untrm (transT2 M) ≠ [] := by
    intro he
    apply hT2
    rw [← trm_untrm_lr (transT2 M), he]; rfl
  rcases List.eq_nil_or_concat (untrm (transT2 M)) with hnil | ⟨init, p, hcat⟩
  · exact absurd hnil hps_ne
  rw [List.concat_eq_append] at hcat
  cases p with
  | db u b =>
    have hT2form : transT2 M = BT.trm (init ++ [BP.db u b]) := by
      rw [← trm_untrm_lr (transT2 M), hcat]
    -- `RightNodes (transT2 M) = u.toNat :: RightNodes b`
    have hRNt2 : RightNodes (transT2 M) = u.toNat :: RightNodes b := by
      rw [hT2form]
      show rightNodesList (init ++ [BP.db u b]) = u.toNat :: RightNodes b
      rw [rnl_concat_lr]; rfl
    -- `condII_pj M = Trm [db u b]`
    have hpj : condII_pj M = BT.trm [BP.db u b] := by
      show (PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero = BT.trm [BP.db u b]
      rw [hT2form]
      have hlenPB : (PB (BT.trm (init ++ [BP.db u b]))).length
          = (init ++ [BP.db u b]).length := by simp [PB, untrm]
      rw [hlenPB]
      exact pb_getD_last_lr init (BP.db u b)
    -- `ldj` 読み出し: `bpHeadV (condII_pj M) = entry M 1 (transJ0 M)`
    have hldj' : bpHeadV (condII_pj M) = (entry M 1 (transJ0 M) : ℕ∞) := by
      have := hldj
      simp only [condII_ldj, beq_iff_eq] at this
      exact this
    have hu : u = (entry M 1 (transJ0 M) : ℕ∞) := by
      rw [hpj] at hldj'
      simpa [bpHeadV] using hldj'
    have hJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
    refine ⟨RightNodes b, ?_⟩
    rw [hTRc, RightNodes_Dprin_lr, hRNt2, he0, hu, hJ0]
    simp

/-! ## (2) `TVX_pos1ldj_holds` = Isabelle `ljx_LDJB` 内の `pos1ldj` 段 -/

/-- Isabelle `ljx_LDJB` の `pos1ldj` (layerB/pss_wip.thy:115180) の 1:1 移植。
`entry M 1 j₀ = entry (tvx_Rc M) 1 0 + tvx_d M`。 -/
theorem TVX_pos1ldj_holds : TVX_pos1ldj_ldjb := by
  intro M hR hmono hj1 hcond _hldj
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hp0, _hE1z, hNadm, _hParPos, hAdmLt, hParLt, _hCond, _hVI, _hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hj0L : parent M 0 (Lng M - 1) < Lng M := by omega
  have htd : tvx_d M = parent M 0 (Lng M - 1) - Adm M (parent M 0 (Lng M - 1)) := rfl
  -- `entry M 1 (Adm j₀ + d) = entry M 1 (Adm j₀) + d`（非許容 run に沿った一次性）
  have hrun := wnx_run_entries M hR (parent M 0 (Lng M - 1)) (tvx_d M) hj0L hNadm
    (by omega)
  have hAle : Adm M (parent M 0 (Lng M - 1)) ≤ parent M 0 (Lng M - 1) :=
    Adm_le M (parent M 0 (Lng M - 1))
  have hjm1d : Adm M (parent M 0 (Lng M - 1)) + tvx_d M = parent M 0 (Lng M - 1) := by
    omega
  have he0 : entry (tvx_Rc M) 1 0 = entry M 1 (Adm M (parent M 0 (Lng M - 1))) :=
    slice_e0_lr M hR hmono hj1 hcond
  have step1 : entry M 1 (parent M 0 (Lng M - 1))
      = entry M 1 (Adm M (parent M 0 (Lng M - 1)) + tvx_d M) := by rw [hjm1d]
  rw [step1, hrun.2, he0]

/-! ## `TV_LDJB` の組み立て（残り 3 残差 modulo） -/

/-- 上の 2 本を «8».«8.3-condII-LDJB» の `TV_LDJB_of_readouts` に配線し、`TV_LDJB` を
残り 3 本の露出残差だけを仮定して閉じる。 -/
theorem TV_LDJB_of_three_lr
    (htrm : RN_a0_trmax_ldjb) (hlt : RN_a0_lt_trmax_ldjb) (hdstrict : TVX_dstrict_ldjb) :
    TV_LDJB :=
  TV_LDJB_of_readouts RN_ldj_pj_holds htrm hlt TVX_pos1ldj_holds hdstrict

#print axioms RN_ldj_pj_holds
#print axioms TVX_pos1ldj_holds
#print axioms TV_LDJB_of_three_lr

end PSS
