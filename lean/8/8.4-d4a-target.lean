import «8».«8.4-exch84-d4a»
import «8».«8.4-oper5-residual»
import «8».«8.2-condV-VE-wnx»
import «8».«8.1-condI-masterCF»

/-!
# §8.4 交換パッケージ `d4a` 標的値 leaf の discharge（`NestScbD4aTargetValue`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: `NestScbD4aTargetValue`（«8».«8.4-exch84-d4a»:103 で def・narrowing 済の残差）
  = Isabelle `cpx_d4a_all` (layerB/pss_wip.thy:98511) の標的 slice 値 `valPNp'`。
  頭 `Dsym(M₁,ⱼ₋₂)`・共通 tail `WP = bpHeadT (Trans (Pred (s84x_N M)))` を持つ principal
  `Trans (Pred (s84x_Np M)) = D_{M₁,ⱼ₋₂} WP`。

## 移植構造（`crg_d4a_trunk`/`crx_d4a_dispatch` が消費する値事実 = `crg_slice_red_value_trunk`
   / `crx_slice_red_value` の M レベル出力 `valPNp` を、簡約host へ IncrFirst-transport する）

Isabelle の値エンジンは 2 枝（trunk = `crg_slice_value_of_trunk` 対角閉形式、regime =
`w84x_slice_value_of_reg` = VE terminal slice ＋ `cfbx_reg`）に分岐するが、**両枝とも
同じ IncrFirst-transport で M レベルの兄弟 slice 値**
`Trans (seg M j₋₂ (Lng M-2)) = D_{M₁,ⱼ₋₂} (bpHeadT (Trans (seg M j₋₃ (Lng M-2))))`
**へ組み上がり**、その M レベル値は既移植の transport bricks
（`wnx_seg_transport_W1/W2`＝`Trans_slice_eq_Red` / peeled-slice、`repr_entry1_shift_gen`＝
簡約 slice の行1 entry シフト）で **簡約host `R = Red (seg M j₋₃ (Lng M-2))` の相対
offset `m = j₋₂ - j₋₃` における slice 値**
`val0 : Trans (seg R m (Lng R-1)) = D_{R₁,ₘ} (bpHeadT (Trans R))` へ落ちる。

本ファイルは M→R の transport を完全証明し、`NestScbD4aTargetValue` を **1 残差**
`NestScbD4aReducedValue`（`val0`、Isabelle `w84x_slice_value_of_reg` /
`crg_slice_value_of_trunk` の簡約host 出力）へ narrowing する。到達性
（`le0 M j₋₂ (Lng M-2)` / `leR M 0 j₋₃ (Lng M-2)`）は公開資産
（`scx_le0_to_parent` で最終前線を剥ぎ・`parent_block_le0_68` で block 前身・
`row0_transitive` で連結・`adm_row1_ancestry`＋`row1_implies_row0` で j₋₃≤₀j₋₂）から
完全に組む。`Pred`↔`seg` 対応は `Pred_s84x_Np`（«8».«8.4-oper5-residual»）と blN。

## 残差（named Prop + needs）

`NestScbD4aReducedValue`（簡約host `R` の相対 offset `m` slice 値 `val0`）のみを残す。
これは Isabelle `w84x_slice_value_of_reg`（regime、`cfbx_reg`=VEReg 消費）/
`crg_slice_value_of_trunk`（trunk、対角閉形式）の出力そのもので、`cfbx_reg` 正則性
エンジンおよび VE terminal-slice/diag 値エンジンの簡約host 適用は本ファイルの範囲外。

- 依存（すべてビルド済み・committed at main 56b1dda）: «8».«8.4-exch84-d4a»
  （`NestScbD4aTargetValue` def・`s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・`Trans`/`Pred`/
  `bpHeadT`/`Dprin`・`transJ0`・`regs_jm2_lt_transJ0_holds`）、«8».«8.4-oper5-residual»
  （`Pred_s84x_Np`）、«8».«8.2-condV-VE-wnx»（`wnx_seg_transport_W1/W2/W3`・
  `repr_entry1_shift_gen`）、«8».«8.1-condI-masterCF»（`scx_le0_to_parent`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `NestScbD4aTargetValue` を **1 残差** `NestScbD4aReducedValue`（簡約host 値）へ narrowing。
- 訂正: なし。
- Private helper suffix: `_dt`。
-/

namespace PSS

/-! ## 1. 補助（Isabelle `s84c2_seg_butlast` の Lean 語彙移植、完全証明） -/

/-- Isabelle `s84c2_seg_butlast` (layerB/pss_wip.thy:54216): `dropLast (seg M a b) = seg M a (b-1)`。
（«8».«8.4-exch84-nest-scb» の private `seg_dropLast_ns` の複製；private は module 跨ぎ不可。） -/
private theorem seg_dropLast_dt (M : PS) (a b : ℕ) (hb : 1 ≤ b) :
    (seg M a b).dropLast = seg M a (b - 1) := by
  apply List.ext_getElem
  · simp only [List.length_dropLast, length_seg]; omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, seg, List.getElem_map, List.getElem_range']

/-! ## 2. 残差 named Prop（簡約host `R` の相対 offset `m` slice 値、Isabelle `val0`） -/

/-- 残差: 簡約host `R = Red (seg M (s84x_jm3 M) (Lng M - 2))` の相対 offset
`m = s84x_jm2 M - s84x_jm3 M` における terminal-slice 値。
`Trans (seg R m (Lng R - 1)) = D_{R₁,ₘ} (bpHeadT (Trans R))`。
Isabelle `w84x_slice_value_of_reg` (regime, layerB/pss_wip.thy:78815, `cfbx_reg`=VEReg 消費) /
`crg_slice_value_of_trunk` (trunk, layerB/pss_wip.thy:91399, 対角閉形式) の出力。
両者とも簡約host での VE terminal-slice / diag 値エンジンを消費するため named Prop。 -/
def NestScbD4aReducedValue : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    Trans (seg (Red (seg M (s84x_jm3 M) (Lng M - 2))) (s84x_jm2 M - s84x_jm3 M)
             (Lng (Red (seg M (s84x_jm3 M) (Lng M - 2))) - 1))
      = Dprin ((entry (Red (seg M (s84x_jm3 M) (Lng M - 2))) 1
                  (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (seg M (s84x_jm3 M) (Lng M - 2)))))

/-! ## 3. house pattern による `NestScbD4aTargetValue` の discharge -/

/-- house-pattern discharge: `NestScbD4aTargetValue`（«8».«8.4-exch84-d4a»:103、
= Isabelle `cpx_d4a_all` の値事実 `valPNp'`）を 1 残差 `NestScbD4aReducedValue`
（簡約host `R` の相対 offset slice 値）へ narrowing。M→R の IncrFirst-transport
（`wnx_seg_transport_W1/W2`・`repr_entry1_shift_gen`）と到達性 chain を完全証明する。 -/
theorem nestScbD4aTargetValue_holds (hVal : NestScbD4aReducedValue) :
    NestScbD4aTargetValue := by
  intro M hST hmono hp hj1 hcond
  -- 基本
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := STPS_TPS M hST
  have hlen : 1 < Lng M := by omega
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hjm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have hjm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt hjm3le hjm2lt
  -- 行0の親 j₀ = transJ0 M は Lng M - 1 より真に左、かつ j₋₂ < j₀
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hj0lt : transJ0 M < Lng M - 1 := by
    have h := parent_lt_of_hasParent M 0 (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hjm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp hj1 hcond
  have hjm2lt2 : s84x_jm2 M < Lng M - 2 := by omega
  have hjm3lt2 : s84x_jm3 M < Lng M - 2 := by omega
  -- Pred ↔ seg
  have blNp : Pred (s84x_Np M) = seg M (s84x_jm2 M) (Lng M - 2) := Pred_s84x_Np M hjm2lt
  have blN : Pred (s84x_N M) = seg M (s84x_jm3 M) (Lng M - 2) := by
    have hNlen : 1 < Lng (s84x_N M) := by simp only [s84x_N, length_seg]; omega
    have hdl : Pred (s84x_N M) = (s84x_N M).dropLast := by
      simp [Pred, Nat.not_le.mpr hNlen]
    rw [hdl]
    show (seg M (s84x_jm3 M) (Lng M - 1)).dropLast = _
    have harg : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [seg_dropLast_dt M (s84x_jm3 M) (Lng M - 1) (by omega), harg]
  -- 到達性 chain: le0 M j₋₂ (Lng M-2), leR M 0 j₋₃ (Lng M-2)
  have hnextrel0 : nextrel0 M (transJ0 M) (Lng M - 1) = true := by
    simpa [nextR] using hnextM
  have hle0jm2j1 : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  have hle0jm2j0 : le0 M (s84x_jm2 M) (transJ0 M) = true :=
    scx_le0_to_parent M (s84x_jm2 M) (transJ0 M) (Lng M - 1) hMT hle0jm2j1 hnextrel0
      (by omega)
  have hle0j0m2 : le0 M (transJ0 M) (Lng M - 2) = true := by
    have hraw := parent_block_le0_68 M (transJ0 M) (Lng M - 1)
      ((Lng M - 2) - transJ0 M) hMT hnextM (by omega)
    have hidx : transJ0 M + ((Lng M - 2) - transJ0 M) = Lng M - 2 := by omega
    rwa [hidx] at hraw
  have hleR_jm2j0 : leR M 0 (s84x_jm2 M) (transJ0 M) = true := by
    simpa [leR] using hle0jm2j0
  have hleR_j0m2 : leR M 0 (transJ0 M) (Lng M - 2) = true := by
    simpa [leR] using hle0j0m2
  have hleR_jm2m2 : leR M 0 (s84x_jm2 M) (Lng M - 2) = true :=
    row0_transitive M (s84x_jm2 M) (transJ0 M) (Lng M - 2) hMT hleR_jm2j0 hleR_j0m2
  have hle0jm2m2 : le0 M (s84x_jm2 M) (Lng M - 2) = true := by
    simpa [leR] using hleR_jm2m2
  have hle1_jm3jm2 : leR M 1 (s84x_jm3 M) (s84x_jm2 M) = true :=
    adm_row1_ancestry M (s84x_jm2 M) hMT (by omega)
  have hle0_jm3jm2 : leR M 0 (s84x_jm3 M) (s84x_jm2 M) = true :=
    row1_implies_row0 M (s84x_jm3 M) (s84x_jm2 M) hMT hle1_jm3jm2
  have hleR_jm3m2 : leR M 0 (s84x_jm3 M) (Lng M - 2) = true :=
    row0_transitive M (s84x_jm3 M) (s84x_jm2 M) (Lng M - 2) hMT hle0_jm3jm2 hleR_jm2m2
  -- transport bricks
  have ham : s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M) = s84x_jm2 M := by omega
  have hW1 : Trans (seg M (s84x_jm3 M) (Lng M - 2))
      = Trans (Red (seg M (s84x_jm3 M) (Lng M - 2))) :=
    wnx_seg_transport_W1 M (s84x_jm3 M) (Lng M - 2) hjm3lt2
  have hW3 : Lng (Red (seg M (s84x_jm3 M) (Lng M - 2))) - 1 = (Lng M - 2) - s84x_jm3 M :=
    wnx_seg_transport_W3 M (s84x_jm3 M) (Lng M - 2) hjm3lt2
  have hLR_pos : s84x_jm2 M - s84x_jm3 M
      < Lng (Red (seg M (s84x_jm3 M) (Lng M - 2))) := by omega
  have hW2 : Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 2))
      = Trans (seg (Red (seg M (s84x_jm3 M) (Lng M - 2))) (s84x_jm2 M - s84x_jm3 M)
                 (Lng (Red (seg M (s84x_jm3 M) (Lng M - 2))) - 1)) :=
    wnx_seg_transport_W2 M (s84x_jm3 M) (Lng M - 2) (s84x_jm2 M - s84x_jm3 M) hMR
      hjm3lt2 (by omega) hleR_jm3m2 (by omega) (by rw [ham]; exact hle0jm2m2)
  have hentry : entry (Red (seg M (s84x_jm3 M) (Lng M - 2))) 1 (s84x_jm2 M - s84x_jm3 M)
      = entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) :=
    repr_entry1_shift_gen M (s84x_jm3 M) (Lng M - 2) (s84x_jm2 M - s84x_jm3 M) hMR
      hjm3lt2 (by omega) hleR_jm3m2 hLR_pos
  -- 残差
  have hval := hVal M hST hmono hp hj1 hcond
  -- 目的の組み立て
  rw [blNp, blN]
  set R := Red (seg M (s84x_jm3 M) (Lng M - 2)) with hRdef
  calc Trans (seg M (s84x_jm2 M) (Lng M - 2))
      = Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 2)) := by rw [ham]
    _ = Trans (seg R (s84x_jm2 M - s84x_jm3 M) (Lng R - 1)) := hW2
    _ = Dprin ((entry R 1 (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞) (bpHeadT (Trans R)) := hval
    _ = Dprin ((entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) : ℕ) : ℕ∞)
          (bpHeadT (Trans R)) := by rw [hentry]
    _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) (bpHeadT (Trans R)) := by rw [ham]
    _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
          (bpHeadT (Trans (seg M (s84x_jm3 M) (Lng M - 2)))) := by rw [← hW1]

#print axioms nestScbD4aTargetValue_holds

end PSS
