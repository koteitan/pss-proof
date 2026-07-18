import «8».«8.2-condIIIV-VE34-reg»

/-!
# §8.2 条件(II)/(IV) VE34 後ろ剥がしキャンペーンの STEP（`vs2x_VE34_step`）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）の帰納ステップ。最終列が現最終枝の中に
  新しい枝を開く場合（`j₁' < j₁`、＝`VEj1p N < Lng N - 1`）の STEP を担う。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）: 体制機械 `8.2-condIIIV-VE34-reg`
  （訂正版体制 `vg4x_reg4`＝`VE34Reg4`、無条件 RPERS `vg4x_RPERS`、後ろ剥がし骨格
  `vg4x_VE34_backpeel`、BASE 幾何）の次のブリック。本ファイルは STEP スロットを供給する:
  - `vs2x_VE34_step` (96800) → `vs2x_VE34_step`（STEP の逐語移植。原文が省略する帰納
    ステップの結論 `vg2x_VE34 N`＝`VE34goal N` を、その二つの鋭い連言 VE3（成長）と
    VE4（頭シフト）に**再組立**するだけ。IH は消費しない――`vg2x_VE34` は `reg4` ホスト
    上で **POINTWISE** に成立（python/ve34_deep2.py 5/5 whole）、帰納法は原文の証明経路
    であって主張には不要。残差は局所的な VE3/VE4 の頭）。
  - `vs2x_VE34_step_of_residuals` (96837) → `vs2x_VE34_step_of_residuals`（STEP スロットを
    二つの普遍残差族 `VE3R`（成長）/`VE4R`（頭シフト）から放出する組立形。これを
    `vg4x_VE34_of_DT`（`8.2-condIIIV-VE34-reg` の `VE34_of_DT4`）へ渡すと `vg2x_VE34` が、
    ひいては `vgx_condIIIV_of_VE` の VE3/VE4 が、ガード付き＋非許容の全 regime ホスト上で
    ちょうど `{BASE, VE3R, VE4R}` modulo で成立する（RPERS は既に無条件））。
- **REFUTED（再挑戦するな）**: 素朴な帰納還元「終切片の principal 末尾が列 append で
  `+_B e` だけ延びる」（`bpHeadT (Trans (terminal (Pred N)))` が
  `bpHeadT (Trans (terminal N))` の PREFIX）は**偽** — python/ve34_deep2.py: 深いホスト
  （`Lng ≤ 12`）で 0/5。終切片は延長でなく再構成する（原文ケース(IV) content.md 3245–3247:
  内側末尾は `t₄ + c₁ × (n-1)` の算術ランプで、suffix append ではない）。したがって `N` での
  VE3 は `Pred N` での VE3 から prefix 論法では従わず、IH からの `{VE3, VE4}` の真の帰納的
  放出には §7.4 共有 scb-context 頭シフト（`m_7_4_Trans_Mark_Pred`＋`m_7_4_Mark_Trans_repr`）
  が要る。それが残差族 `VE3Residual`/`VE4Residual` の中身であり、本ファイルの射程外。
- 依存 module: `8.2-condIIIV-VE34-reg`（`VE34Reg4`/`VE34goal`/`VE34Step4`/`VE34Base4`/
  `VE34_of_DT4`/`VEj1p` と `Br`/`Joints`/`FirstNodes`/`LastStep`/`Trans`/`seg`/`bpHeadT`/
  `addBT`/`Dprin`/`entry`/`DTPS`/`TrMax` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。STEP の再組立と残差からの放出、および
  `VE34Step4` の残差からの放出を緑で供給。残差は名前付き Prop `{VE3Residual, VE4Residual}`
  （＝Isabelle の `VE3R`/`VE4R` 族）。これで VE34 キャンペーン全体が
  `{VE34Base4, VE3Residual, VE4Residual}` modulo に還元される（RPERS は無条件）。
  VE3/VE4 の実体（§7.4 頭シフト readback surgery）は本ファイルの射程外＝次のブリック。
-/

namespace PSS

/-! ## VE3/VE4 の頭（`vg2x_VE34` の二つの鋭い連言）

`VE34goal M`（Isabelle `vg2x_VE34 M`）は、成長成分 VE3（`∃ t₂` で束ねた）と頭シフト
成分 VE4（`t₂`-free）の連言そのもの。VE4 は `t₂` を含まないので、存在量化子はその外へ
くくり出せ、`VE34goal M ⟺ VE3goal M ∧ VE4goal M`。 -/

/-- **VE3（成長）**: 終切片の頭が接頭辞の頭を非零 `t₂` だけ超える。
`vg2x_VE34` の第一・第二連言（`condIIIV_terminal_slice_Trans_modVE` の `VE3` と
`t₂ ≠ 0_B`）を束ねた形。 -/
def VE3goal (M : PS) : Prop :=
  ∃ t2 : BT,
    bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1)))
      = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))) t2
    ∧ t2 ≠ BZero

/-- **VE4（頭シフト）**: `Trans M` の外側 context 方程式。`t₂`-free なので存在量化の
外側に置ける。`vg2x_VE34` の第三連言（`condIIIV_terminal_slice_Trans_modVE` の `VE4`）。 -/
def VE4goal (M : PS) : Prop :=
  bpHeadT (Trans M)
    = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))))
        (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1)))))

/-- `VE34goal M ⟺ VE3goal M ∧ VE4goal M`。VE4 は `t₂`-free なので存在量化子が VE3 側へ
くくり出せる、単なる `∃`-シャッフル（Isabelle `vs2x_VE34_step` の証明本体の同値）。 -/
theorem VE34goal_iff (M : PS) : VE34goal M ↔ VE3goal M ∧ VE4goal M := by
  constructor
  · rintro ⟨t2, hA, hB, hC⟩
    exact ⟨⟨t2, hA, hB⟩, hC⟩
  · rintro ⟨⟨t2, hA, hB⟩, hC⟩
    exact ⟨t2, hA, hB, hC⟩

/-! ## 残差族（Isabelle `VE3R` / `VE4R`）

いずれも STEP regime（`VE34Reg4 Q` かつ `VEj1p Q < Lng Q - 1`、＝
`vg4x_reg4 Q ∧ cfbx_j1p Q < Lng Q - 1`）上で普遍的に量化された頭。 -/

/-- **Isabelle `VE3R`（`vs2x_VE34_step_of_residuals` の第一残差族）**: STEP regime 上で
成長成分 VE3 が普遍的に成立する。 -/
def VE3Residual : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q < Lng Q - 1 → VE3goal Q

/-- **Isabelle `VE4R`（`vs2x_VE34_step_of_residuals` の第二残差族）**: STEP regime 上で
頭シフト成分 VE4 が普遍的に成立する。 -/
def VE4Residual : Prop :=
  ∀ Q : PS, VE34Reg4 Q → VEj1p Q < Lng Q - 1 → VE4goal Q

/-! ## STEP の再組立（Isabelle `vs2x_VE34_step`, layerB 96800） -/

/-- **Isabelle `vs2x_VE34_step` (layerB 96800)** の逐語移植。

最終列が新しい枝を開く STEP regime（`VEj1p N < Lng N - 1`）で、局所的な VE3（成長）と
VE4（頭シフト）から結論 `VE34goal N`（＝`vg2x_VE34 N`）を **再組立** する。IH は消費しない
（`VE34goal` は `reg4` ホスト上で POINTWISE に成立）。証明は `VE34goal_iff` の `∃`-シャッフル。 -/
theorem vs2x_VE34_step (N : PS) (reg : VE34Reg4 N) (lt : VEj1p N < Lng N - 1)
    (regP : VE34Reg4 (Pred N)) (IH : VE34goal (Pred N))
    (hVE3 : VE3goal N) (hVE4 : VE4goal N) : VE34goal N :=
  (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-- **Isabelle `vs2x_VE34_step_of_residuals` (layerB 96837)** の逐語移植。

STEP スロットを二つの普遍残差族 `VE3Residual`（成長）/`VE4Residual`（頭シフト）から
放出する。 -/
theorem vs2x_VE34_step_of_residuals (hVE3 : VE3Residual) (hVE4 : VE4Residual)
    (N : PS) (reg : VE34Reg4 N) (lt : VEj1p N < Lng N - 1)
    (regP : VE34Reg4 (Pred N)) (IH : VE34goal (Pred N)) : VE34goal N :=
  vs2x_VE34_step N reg lt regP IH (hVE3 N reg lt) (hVE4 N reg lt)

/-! ## `VE34Step4` の残差からの放出 -/

/-- `8.2-condIIIV-VE34-reg` の残差 Prop `VE34Step4`（`vg4x_VE34_backpeel` の第二仮定）を、
二つの普遍残差族 `{VE3Residual, VE4Residual}` から放出する。 -/
theorem VE34Step4_of_residuals (hVE3 : VE3Residual) (hVE4 : VE4Residual) : VE34Step4 :=
  fun N reg lt regP IH => vs2x_VE34_step_of_residuals hVE3 hVE4 N reg lt regP IH

/-! ## end-to-end 還元（RPERS 無条件・STEP 残差経由） -/

/-- VE34 キャンペーン全体を `{VE34Base4, VE3Residual, VE4Residual}` modulo に還元する
end-to-end 補題。`8.2-condIIIV-VE34-reg` の `VE34_of_DT4`（RPERS は無条件討伐済み）に、
本ファイルの `VE34Step4_of_residuals` で STEP を供給する。 -/
theorem VE34_of_DT4_of_VE3VE4 (hBase : VE34Base4) (hVE3 : VE3Residual) (hVE4 : VE4Residual)
    (M : PS) (hMD : DTPS M) (hBrne : Br M ≠ [])
    (hguard : entry M 1 (VEj1p M) < entry M 0 (VEj1p M))
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M) :
    VE34goal M :=
  VE34_of_DT4 hBase (VE34Step4_of_residuals hVE3 hVE4) M hMD hBrne hguard hj0pos hj0lt

/-! ## condIIIVts フィールドの締め（`vg7x_condIIIV_of_DT` の vg4x 版） -/

/-- **Isabelle `vg7x_condIIIV_of_DT` (layerB 97539) の vg4x 版**: 条件(II)/(IV) 終切片
命題の結論（`∃!t₁₂` の一意存在、`condIIIV_terminal_slice_Trans_modVE`）を、`DT_PS`
ホスト＋ガード＋非許容境界＋`VE2` から、ちょうど残差 `{VE34Base4, VE3Residual, VE4Residual}`
modulo で供給する（RPERS は無条件討伐済み、STEP は本ファイルの `VE34Step4_of_residuals`
経由）。本ファイルの `VE34_of_DT4_of_VE3VE4` で `VE34goal M` を作り、入口
`condIIIV_of_VE2_VE34` で `VE2goal M` と束ねる。

これで condIIIVts フィールド全体が `{VE2goal, VE34Base4, VE3Residual, VE4Residual}` modulo に
還元される（`descending` を運ぶ vg7x 精密版は別機構ファイルの担当）。 -/
theorem condIIIV_ts_of_residuals (hBase : VE34Base4) (hVE3 : VE3Residual) (hVE4 : VE4Residual)
    (M : PS) (hMD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hguard : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
            < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0))
    (hVE2 : VE2goal M) :
    ∃! t12 : BT × BT,
      Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                   ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            (addBT t12.1 t12.2) ∧
      t12.2 ≠ BZero ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t12.1 (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
          (addBT t12.1 t12.2))) :=
  condIIIV_of_VE2_VE34 M hMD hBrne hj0pos hj0lt hguard hVE2
    (VE34_of_DT4_of_VE3VE4 hBase hVE3 hVE4 M hMD hBrne hguard hj0pos hj0lt)

#print axioms VE34goal_iff
#print axioms vs2x_VE34_step
#print axioms vs2x_VE34_step_of_residuals
#print axioms VE34Step4_of_residuals
#print axioms VE34_of_DT4_of_VE3VE4
#print axioms condIIIV_ts_of_residuals

end PSS
