import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-step»
import «6».«6.4-FirstNodes-TrMax-Joints»

/-!
# §8.3 条件(II) — `TV_BoundaryLeg` へ向けた境界データ・ブリック

## 目的

親ファイル «8».«8.3-condII-masterCF-port» の名前付き残差 `TV_BoundaryLeg`
（Isabelle `tvx_tailval_of_boundary`, layerB/pss_wip.thy:110527-110651）を閉じることが
最終目標だが、その証明は Lean 未移植の重機に依存する（下記「未閉」参照）。本ファイルは
`TV_BoundaryLeg` を**無条件には主張せず**、その証明チェーンの**冒頭で無条件に成立する
境界データ**（`hqx_condIIIV_of_DT` の入力仮定 `j0pos`、`m_8_2_standard_slice_Red_strongmono`
の reach 上界 `ab`、および値代数の左簡約 `cdx_Dpt_inj`）を green public brick として bank する。

## Isabelle 側の対応（名前＋行番号）

| brick | Isabelle | 位置 |
|---|---|---|
| `tvx_reach_jm1_ub` | `c2sx_reach`(3) の clause | layerB/pss_wip.thy:87669 |
| `tvx_reach_j0_ub`  | `c2sx_reach`(4) の clause | layerB/pss_wip.thy:87670 |
| `tvx_dpos`         | `tvx_tailval_of_boundary` 内 `have dpos` | layerB/pss_wip.thy:110552 |
| `tvx_j0pos`        | `tvx_tailval_of_boundary` 内 `have j0pos` | layerB/pss_wip.thy:110566 |
| `Dprin_inj`        | `cdx_Dpt_inj` | layerB/pss_wip.thy:90137 |

いずれも Isabelle では `c2sx_host_basic`（Lean `condII_host_basic_holds`, 移植済）の
clause (5) `Adm M j₀ < j₀` と (6) `j₀ + 1 < Lng M - 1` の純算術的帰結、または `Dprin`
コンストラクタの単射性。`tvx_j0pos` は crux 補題 `hqx_condIIIV_of_DT` の第 3 仮定
（`0 < Joints M ! (Lng (Br M) - 1)`）を `R_c` で instantiate したもの＝**critical path 上**。

## 依存

* «8».«8.3-condII-masterCF-port» — `tvx_d` / `tvx_jL` / `tvx_Rc` / `STPS_RTPS`
  ＋推移的に «8».«8.3-condII-masterCF»（`condII_host_basic_holds : CondII_host_basic`）。
* «8».«8.3-condII-step», «6».«6.4-FirstNodes-TrMax-Joints» — （primitives / 環境）。

## 状態

* ✅ `tvx_reach_jm1_ub` / `tvx_reach_j0_ub` / `tvx_dpos` / `tvx_j0pos` / `Dprin_inj`
  … いずれも**無条件**（`condII_host_basic_holds` ＋ omega、または構造帰納）。
* 🚫 `TV_BoundaryLeg`（=`tvx_tailval_of_boundary`）は**本ファイルでは閉じていない**。
  Isabelle の証明は下記の Lean 未移植重機を使う（`needs` に報告）:
    - `hqx_condIIIV_of_DT`（layerB:108722）— §8.2 condIIIV の存在一意（clause 1-5）。
      Lean は «8».«8.3-condIIIV-terminal-slice-Trans» で `VE2/VE3/VE4` 仮定版
      （`vgx_condIIIV_of_VE`）まで。台となる `vg2x_VE34`（≈14000 行）が未移植。
    - `wnx_seg_transport`（layerB:80767）— `Trans (seg M a b) = Trans (Red (seg M a b))`
      系（W1/W2/LRcpos）。Lean 未移植。
    - `repr_entry1_shift_gen`（layerB:12828）— `entry (Red (seg …)) 1 k = entry M 1 (a+k)`
      （e0/ed/vJeq）。Lean 未移植。
    - `c2sx_slice_jm1_c1`（layerB:87633）— スライス基点の Trans 表示（bridge）。Lean 未移植。
    - `tvx_d_lt_TrMax`（layerB:110442）— 境界 strictness（TRLT）。Lean 未移植。
    - `c2sx_reach`(1) `leab`（layerB:87668）— `leR M 0 (Adm M j₀) (Lng M - 2)`
      （`RcDT` の到達性仮定）。`Marked_Pred_Adm` / `le0_prefix_agree` 経由で未移植。
  仮定束は Isabelle と文字単位で一致（`STPS M`＋`monoT M = true` で `M ∈ PT_PS` を再構成、
  結論 `c2sx_tailval M` ∧ `c2sx_ldj M` = Lean `CondII_tailval M ∧ condII_ldj M = true`）＝
  **leaf は真**（vacuous ではない）。
-/

namespace PSS

/-! ## 境界データ（`condII_host_basic_holds` の純算術的帰結）

Isabelle の `tvx_tailval_of_boundary` は冒頭で
`note HB = c2sx_host_basic[OF MR MP j1gt condII]`（Lean `condII_host_basic_holds`）を引き、
その clause (5) `Adm M j₀ < j₀`・(6) `j₀ + 1 < Lng M - 1` から reach 上界と run 正値を得る。
仮定束は `RTPS`（`c2sx_reach` の `MR` に一致。`PT_PS = T_PS ∧ monoT` なので `RTPS`＋`monoT`）。 -/

/-- Isabelle `c2sx_reach`(3) (pss_wip.thy:87669) の clause／`tvx_tailval_of_boundary` の
`ab: ?jm1 < Lng M - 2`。`m_8_2_standard_slice_Red_strongmono` の上界仮定 `hlt` に
（`j₀' = Adm M (parent M 0 (Lng M - 1))`, `j₁' = Lng M - 2` で）そのまま入る。 -/
theorem tvx_reach_jm1_ub (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by
  obtain ⟨_, _, _, _, hjm1lt, hp6, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  omega

/-- Isabelle `c2sx_reach`(4) (pss_wip.thy:87670)／`qc: ?j0 < Lng M - 2`。 -/
theorem tvx_reach_j0_ub (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    parent M 0 (Lng M - 1) < Lng M - 2 := by
  obtain ⟨_, _, _, _, _, hp6, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  omega

/-- Isabelle `tvx_tailval_of_boundary` 内 `have dpos: 0 < ?d` (pss_wip.thy:110552)。
`?d = tvx_d M` は非許容 run の長さ。`c2sx_host_basic`(5)（許容化の狭義降下）から。 -/
theorem tvx_dpos (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    0 < tvx_d M := by
  obtain ⟨_, _, _, _, hjm1lt, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  unfold tvx_d
  omega

/-- Isabelle `tvx_tailval_of_boundary` 内 `have j0pos: 0 < ?jL` (pss_wip.thy:110566)。
`crux` 補題 `hqx_condIIIV_of_DT`（layerB:108722）の第 3 仮定
`0 < Joints M ! (Lng (Br M) - 1)` を `R_c` で instantiate した入力＝**critical path 上**。
境界 exactness `tvx_d M = tvx_jL M`（Lean `TV_BoundaryLeg` の `DEQ` 仮定）と `tvx_dpos` から。 -/
theorem tvx_j0pos (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true)
    (hDEQ : tvx_d M = tvx_jL M) :
    0 < tvx_jL M := by
  have hd : 0 < tvx_d M := tvx_dpos M hR hmono hj1 hcond
  omega

/-! ## 値代数の左簡約（`cdx_Dpt_inj`）

`tvx_tailval_of_boundary` の `T2EQ` で使う `Dpt`（Lean `Dprin`）の左簡約。
Isabelle `cdx_Dpt_inj: Dpt v a = Dpt v b ⟹ a = b`（layerB/pss_wip.thy:90137、`by simp`）。 -/

/-- Isabelle `cdx_Dpt_inj` (pss_wip.thy:90137)。`Dprin v a = Dprin v b → a = b`。 -/
theorem Dprin_inj {v : ℕ∞} {a b : BT} (h : Dprin v a = Dprin v b) : a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact h.2

#print axioms tvx_reach_jm1_ub
#print axioms tvx_reach_j0_ub
#print axioms tvx_dpos
#print axioms tvx_j0pos
#print axioms Dprin_inj

end PSS
