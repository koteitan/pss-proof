import «8».«8.3-condII-BoundaryLeg»
import «8».«8.3-condII-masterCF-port»

/-!
# §8.3 条件(II) — `TV_BoundaryLeg` の value-algebra 討伐（bank 継続）

## 原文 / Isabelle 対応

- 原文: `tmp/content.md` 4188–4243（§8.3 命題（条件(II)の下での `Trans` と基本列の
  交換関係）の `leftDj0`-leg = 境界の tail 値と `ldj`）。
- 逐語形の証明: Isabelle `tvx_tailval_of_boundary`
  (isabelle/layerB/pss_wip.thy:110527–110642)。結論 `c2sx_tailval M`（(1)）と
  `c2sx_ldj M`（(2)）= Lean `CondII_tailval M` ∧ `condII_ldj M = true`。
- 名前付き残差: `TV_BoundaryLeg`（«8».«8.3-condII-masterCF-port»:130）。
  `CondII_masterCF` の 4 本の tailval brick の 1 本で、`FseqDesc_exchII` /
  `OTdisp_exchII` の両柱が依存する。

## このファイルの内容（bank の続き）

ビルド済み «8».«8.3-condII-BoundaryLeg» は境界データの純算術 brick を bank したが、
`TV_BoundaryLeg` 本体は **Lean 未移植の §8.2 重機**に依存するため未閉だった。
本ファイルは Isabelle 証明を **value-algebra 段（110616–110641）** と
**transport/存在段（110569–110615）** に分け、前者を無条件に Lean 化し、後者
（6 本の深い補題の**転送後の正味の帰結**）を単一の名前付き Prop `TvxBoundaryData`
へ折り畳んで公開する（green-modulo）。

`TvxBoundaryData` は Isabelle 証明の中間事実
  `T2EQ`（110614: `transT2 M = fst t12 +ᴮ Dpt v₀ (fst t12 +ᴮ snd t12)`）
  ＋ tailval 側（110639: `Trans (seg M j₀ (Lng M-2)) = Dpt v₀ (fst t12 +ᴮ snd t12)`）
  ＋ `snd t12 ≠ 0ᴮ`（EX1 の conjunct）
をそのまま束ねたもの＝**Isabelle で証明済みの真の主張**（vacuous でない）。
折り畳んだ 6 本（すべて Isabelle 定理）:
  * `hqx_condIIIV_of_DT`（layerB:108722）— §8.2 condIIIV の EX1。
    Lean は «8».«8.2-condIIIV-terminal-slice-Trans» の VE 仮定版まで。
    台の `vg2x_VE34`（≈14000 行）が未移植＝**折り畳みの深い核**。
  * `wnx_seg_transport`（layerB:80767）— `Trans (seg …) = Trans (Red (seg …))`
    と剥ぎ切片版（W1/W2）。
  * `repr_entry1_shift_gen`（layerB:12828）— `entry (Red (seg …)) 1` の行不変。
  * `c2sx_slice_jm1_c1`（layerB:87633）— bridge。Lean は «8».«8.3-condII-TrunkLeg»
    で移植済（本ファイルの折り畳みに吸収）。
  * `tvx_d_lt_TrMax`（layerB:110442）— 境界 strictness（TRLT）。
  * `c2sx_reach`（layerB:87666）— reach 4-clause（leab/leam）。

## 依存

* «8».«8.3-condII-BoundaryLeg»（bank; tvx_* 境界 brick・`Dprin_inj`）を推移的に
  «8».«8.3-condII-masterCF»（`CondII_tailval` / `condII_ldj` / `condII_pj` /
  `condII_t4`）／«8».«8.3-condII-masterCF-port»（`TV_BoundaryLeg` / `tvx_*`）
  ／`PSS/Trans`（`transT2` / `transJ0` / `bpHeadV` / `bpHeadT`）
  ／`PSS/Buchholz`（`PB` / `addBT` / `Dprin` / `BZero`）まで。

## 状態

* ✅ `tv_boundaryleg_of_data : TvxBoundaryData → TV_BoundaryLeg`（house pattern）
  — value-algebra 段は**無条件**（sorry 0、axioms 正常）。
* 🚫 `TvxBoundaryData`（= 上記 6 本の転送後帰結）は**本ファイルでは閉じていない**
  （§8.2 `vg2x_VE34` ≈14000 行が未移植）＝`needs` に報告。真の主張であり
  vacuous ではない。
-/

namespace PSS

/-! ## value-algebra 補助 -/

/-- `PB (Trm (as ++ [p]))` の最後の principal は `Trm [p]`。
条件(II) tailval で `t₂ = fst +ᴮ Dpt v u` の最後の principal `Dpt v u` を読み出す
（Isabelle `PB_def`＋`SigmaB_snoc` の値レベル版、`8.2-subexpr-adm0-cores`
`PB_split_last_sc` の snoc 特化）。 -/
private theorem getD_last_map_snoc_bl2 (as : List BP) (x : BP) :
    (((as ++ [x]).map (fun p => BT.trm [p])).getD
        (((as ++ [x]).map (fun p => BT.trm [p])).length - 1) BZero) = BT.trm [x] := by
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil, List.length_append, List.length_map,
    List.length_cons, List.length_nil, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-! ## 折り畳んだ深い残差（Isabelle 6 本の転送後の正味の帰結） -/

/-- Isabelle `tvx_tailval_of_boundary` (pss_wip.thy:110527) の transport/存在段
（110569–110615）の**正味の帰結**。境界データの下で、条件(II) ホスト `M` の
追加ブロックの終切片の値が最後の枝 principal `Dpt v₀ (t₁ +ᴮ t₂)` になり、かつ
`t₂` の最後の principal が同じ `Dpt v₀ (t₁ +ᴮ t₂)`（`transT2 M` の snoc 分解）で
あること。ここで `v₀ = entry M 1 (parent M 0 (Lng M-1))`。

Isabelle では `hqx_condIIIV_of_DT`（EX1）＋`wnx_seg_transport`（W1/W2）＋
`repr_entry1_shift_gen`（e0/ed）＋`c2sx_slice_jm1_c1`（bridge）＋`tvx_d_lt_TrMax`
（TRLT）＋`c2sx_reach`（leab/leam）から得られる**定理**。仮定束は `TV_BoundaryLeg`
と 1:1（`STPS`＋`monoT`＋`transCondII`＋境界データ）。 -/
def TvxBoundaryData : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    Br (tvx_Rc M) ≠ [] →
    tvx_d M = tvx_jL M →
    entry (tvx_Rc M) 1 (tvx_fn M) < entry (tvx_Rc M) 0 (tvx_fn M) →
    tvx_finRc M →
    ∃ t1 t2 : BT,
      Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))
          = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (addBT t1 t2)
      ∧ transT2 M
          = addBT t1
              (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (addBT t1 t2))
      ∧ t2 ≠ BZero

/-! ## `TV_BoundaryLeg` の drop-in（house pattern） -/

/-- Isabelle `tvx_tailval_of_boundary` の value-algebra 段（110616–110641）の
Lean 化。折り畳んだ深い残差 `TvxBoundaryData` から `TV_BoundaryLeg` を**無条件に**
供給する。`ldj` 側（原文 (2)）は最後の principal の頭が `v₀ = M₁,ⱼ₀` であること
（`condII_ldj = true`）、`tailval` 側（原文 (1)）は `condII_t4 = t₁ +ᴮ t₂` で
`Trans (seg M j₀ (Lng M-2)) = D_{M₁,ⱼ₀} (t₁ +ᴮ t₂)`。 -/
theorem tv_boundaryleg_of_data (hData : TvxBoundaryData) : TV_BoundaryLeg := by
  intro M hST hmono hj1 hcond hBr hDEQ hGUARD hFin
  obtain ⟨t1, t2, hEQ1, hEQ2, _hne⟩ :=
    hData M hST hmono hj1 hcond hBr hDEQ hGUARD hFin
  obtain ⟨as⟩ := t1
  -- `transT2 M` の snoc 形
  have hT2 : transT2 M
      = BT.trm (as ++ [BP.db (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)
          (addBT (BT.trm as) t2)]) := by
    rw [hEQ2]; rfl
  -- 最後の principal `condII_pj M = Dpt v₀ (t₁ +ᴮ t₂)`
  have hpj : condII_pj M
      = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (addBT (BT.trm as) t2) := by
    unfold condII_pj
    rw [hT2]
    show (((as ++ [BP.db (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)
              (addBT (BT.trm as) t2)]).map (fun p => BT.trm [p])).getD
            (((as ++ [BP.db (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)
              (addBT (BT.trm as) t2)]).map (fun p => BT.trm [p])).length - 1) BZero)
          = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (addBT (BT.trm as) t2)
    rw [getD_last_map_snoc_bl2]
    rfl
  -- `transJ0 M = parent M 0 (Lng M - 1)`（定義展開）
  have hJ0 : transJ0 M = parent M 0 (Lng M - 1) := by
    simp [transJ0, lastParent, lastIdx]
  -- `ldj`（原文 (2)）: 最後の principal の頭が `v₀`
  have hldj : condII_ldj M = true := by
    simp only [condII_ldj, beq_iff_eq]
    rw [hpj, hJ0]
    rfl
  -- `t₄ = t₁ +ᴮ t₂`
  have ht4 : condII_t4 M = addBT (BT.trm as) t2 := by
    have hbT : bpHeadT (condII_pj M) = addBT (BT.trm as) t2 := by
      rw [hpj]; rfl
    simp only [condII_t4, hldj, if_true, hbT]
  refine ⟨?_, hldj⟩
  -- `tailval`（原文 (1)）
  show Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))
      = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M)
  rw [ht4]
  exact hEQ1

#print axioms tv_boundaryleg_of_data

end PSS
