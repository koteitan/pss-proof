import «8».«8.2-condIIIV-basedeep»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel 続行 — 体制に `descending (Br)` を復元する（訂正）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel、原文 L3360 の
  「subexpr-component-`Pred`」補題）。`8.2-condIIIV-basedeep` はこの run 領域 BASE 脚を
  run-peel 帰納法で攻め、`condIIIVts` フィールドを残差束
  `{RunPeelPreserved_bd, VE3RunBase_bd, VE3RunStep_bd, PIN_bd, TSPIN_bd, VE3Step, VE4Step}`
  に還元した（`condIIIVterminalSlice_of_runpeel`）。

- **本ファイルの発見（🚨 訂正）**: その残差束の先頭 `RunPeelPreserved_bd` は **偽** である。
  原因は体制から `descending (Br N)`（`descendingB`）が落ちていること。フィールド
  `CondIIIVterminalSlice`（`8.3-condII-Boundary-close`）自体は **`DTPS M`**（＝
  `strongMono`＝`reduced ∧ monoT ∧ descendingB (Br)`）上で量化されているのに、その下流の
  VE34 残差鎖（`8.2-condIIIV-VE234` → `-ve34-base` → `-basedeep`）は残差を素の
  `VE34Reg4`（＝Isabelle `vg4x_reg4`＝`RTPS ∧ monoT ∧ Br≠[] ∧ guard ∧ 非許容 joint`）上で
  量化しており、**`descendingB (Br)` を捨てている**。Isabelle 側は r36 の反例
  `(0,0)(1,1)(2,2)(2,1)(2,2)(2,0)` を機械検出し、体制を
  `vg7x_reg4 N ≝ vg4x_reg4 N ∧ descending (Br N)`（＝`N ∈ DT_PS`）に補正して run-peel
  （`bfx_`/`hqx_`）を回している。Lean 版はこの補正を取り込み損ねていた。
  同じ r36 反例が `RunPeelPreserved_bd` の量化域（`VE34Reg4 ∧ BASE ∧ deep ∧ run-step`）に
  属し、その `Pred` は `VE34Reg4` を保たない（`RunPeelPreserved_bd_refuted_vc2` で機械証明、
  下記 `#guard` で数値裏付け）。よって `condIIIVterminalSlice_of_runpeel` は現状 **死んだ
  還元**（偽の仮定を要求）である。

- **本ファイルの修正**: 素の `VE34Reg4` に `descendingB (Br)` を足した補正体制
  `VE34Reg4D`（＝Isabelle `vg7x_reg4`）を導入し、run-peel の体制持続を **`descending` を
  保ったまま** 供給する:
  1. `RunPeelPreserved_bd_refuted_vc2 : ¬ RunPeelPreserved_bd` — 素の残差が偽であることを
     r36 反例で機械証明（＝現 basedeep 還元の死因の同定）。
  2. `dtps_Pred_of_runstep_vc2` — run-step BASE deep の `VE34Reg4D` ホストで
     `DTPS (Pred N) ∧ Br (Pred N) ≠ []` を **無条件討伐**（`descending_Br_Pred` 直撃、
     Isabelle `bfx_PredDT_base` の descending 半）。これが r36 修正の要石。
  3. 補正残差 `RunPeelPreservedD_vc2`（＝`descending` 込みの run-peel 持続）を、上記の
     DTPS 半（証明済み）＋残る Pred レベル幾何 `RunPeelGuardJointBase_vc2`（Isabelle
     `bfx_gtP_base`＝guard 転送／`bfx_Joints_Pred_last`＝JEQ joint 持続／単一列 base）
     一本に **還元**（`RunPeelPreservedD_of_geom_vc2`）。descending 半が閉じたので残差は
     guard/joint/base 幾何のみ。

- ⚠️ **未着手（次のブリック）**: フィールド `CondIIIVterminalSlice`（DTPS ホスト）から
  補正体制 `VE34Reg4D` 上の残差へ降ろす **field-level 再配線**（`condIIIVterminalSlice_of_*`
  を `VE34Reg4` から `VE34Reg4D` へ引き直す）は本ファイルの射程外。現行の
  `condIIIVterminalSlice_of_deep2`/`-runpeel` 等は `VE34Reg4` 残差を入力に取るため、
  補正済み `VE34Reg4D` 残差からは直接には供給できない（`VE34Reg4D ⊆ VE34Reg4` で向きが逆）。
  DTPS ホストは `descendingB (Br)` を持つので再配線は幾何的には自明（`VE34Reg4D_of_dtps_host`）
  だが、中間補題群を descending 体制で引き直す作業が要る。
  また `RunPeelGuardJointBase_vc2` の Pred レベル幾何を Isabelle `bfx_run_prev`/`bfx_JEQ`
  そのままの **N レベル run-squeeze**（`Pred` を含まない、keystone 非依存）に尖鋭化する
  のも次段（本ファイルはそれが `DTPS(Pred)` と両立することを数値検証済み）。

- 訂正: 本ファイルが同定した「`descendingB (Br)` の脱落」は Lean 移植側の欠陥であって
  原文の誤りではない（Isabelle 版は r36 で既に補正済み）。corrections.md への登録は不要。

- 依存 module: `8.2-condIIIV-basedeep`（`RunPeelPreserved_bd`/`VE3RunBase_bd`/`VE3RunStep_bd`/
  `PIN_bd`/`TSPIN_bd`/`condIIIVterminalSlice_of_runpeel`/`VE34Reg4`/`VEj1p`/`LastStep`/
  `descendingB`/`DTPS`/`DTPS_iff`/`descending_Br_Pred`/`FirstNodes_Pred_core`/
  `Joints_Pred_core`/`length_Pred`/`TrMax_Pred_nontrunk`/`RTPS_TPS`/`P_nonempty`/`entry_Pred`/
  `Br` を推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。`RunPeelPreserved_bd` 偽を機械証明、補正体制
  `VE34Reg4D` を導入、descending 持続半（`dtps_Pred_of_runstep_vc2`）を無条件討伐、
  補正残差 `RunPeelPreservedD_vc2` を単一 Pred 幾何 `RunPeelGuardJointBase_vc2` に還元。

- Private suffix: `_vc2`。
-/

namespace PSS

/-! ## 補正体制 `VE34Reg4D`（Isabelle `vg7x_reg4 = vg4x_reg4 ∧ descending (Br)`）

素の `VE34Reg4`（＝`vg4x_reg4`）に `descendingB (Br N) = true` を足す。`VE34Reg4` が
`RTPS N ∧ monoT N`（`VE34Reg` 経由）を含むので、`descendingB (Br N)` を足すと
`DTPS N`（＝`strongMono`）＋guard＋非許容 joint に一致する（Isabelle
`vg7x_reg4 N = N ∈ DT_PS` unpacked）。 -/

/-- **補正体制**（Isabelle `vg7x_reg4`）: 素の `VE34Reg4` に `descending (Br)` を復元。 -/
def VE34Reg4D (N : PS) : Prop := VE34Reg4 N ∧ descendingB (Br N) = true

instance (N : PS) : Decidable (VE34Reg4D N) := by unfold VE34Reg4D; infer_instance

/-- `VE34Reg4D N → VE34Reg4 N`（descending を落とす、向きは狭→広）。 -/
theorem VE34Reg4D_VE34Reg4 (N : PS) (h : VE34Reg4D N) : VE34Reg4 N := h.1

/-- `VE34Reg4D N → DTPS N`（Isabelle `vg7x_reg4_DT`）: 補正体制は `DTPS`（強単項）を含む。 -/
theorem VE34Reg4D_DTPS (N : PS) (h : VE34Reg4D N) : DTPS N := by
  obtain ⟨reg4, hdesc⟩ := h
  obtain ⟨⟨⟨hR, hmono, _hBrne⟩, _⟩, _, _⟩ := reg4
  exact (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩

/-- フィールド `CondIIIVterminalSlice`（`8.3-condII-Boundary-close`）の `DTPS` ホスト＋
guard＋非許容 joint 束から補正体制 `VE34Reg4D` を組む（＝descending 情報がフィールドで
実在することの確認、Isabelle の DT-consumer 配線に対応）。 -/
theorem VE34Reg4D_of_dtps_host (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hguard : entry M 1 (VEj1p M) < entry M 0 (VEj1p M)) :
    VE34Reg4D M := by
  obtain ⟨hR, hmono, hdesc⟩ := (DTPS_iff M).mp hD
  exact ⟨⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩, hdesc⟩

/-! ## `RunPeelPreserved_bd` は偽（🚨 現 basedeep 還元の死因）

Isabelle r36 反例 `N = (0,0)(1,1)(2,2)(2,1)(2,2)(2,0)`（非 descending）は
`RunPeelPreserved_bd` の量化域 `VE34Reg4 ∧ BASE ∧ deep ∧ run-step` に属するが、その
`Pred` は `VE34Reg4` すら保たない。`RunPeelPreserved_bd` の結論
`VE34Reg4 (Pred N) ∧ VEj1p (Pred N) = Lng (Pred N) - 1` は成立し得ない。 -/

/-- r36 反例（Isabelle: `vg4x_reg4` だが `descending (Br)` 偽）。 -/
def cexNonDesc_vc2 : PS := [(0,0),(1,1),(2,2),(2,1),(2,2),(2,0)]

-- **反例は補正残差の量化域に属し、`descendingB (Br)` が偽**（数値裏付け）。
#guard decide (VE34Reg4 cexNonDesc_vc2
  ∧ VEj1p cexNonDesc_vc2 = Lng cexNonDesc_vc2 - 1
  ∧ TrMax cexNonDesc_vc2 + 2 < Lng cexNonDesc_vc2
  ∧ LastStep cexNonDesc_vc2 < (Br cexNonDesc_vc2).length - 1
  ∧ ¬ (descendingB (Br cexNonDesc_vc2) = true)) = true

-- **`Pred` が体制を破る**（数値裏付け、`RunPeelPreserved_bd` の結論が偽）。
#guard decide (¬ VE34Reg4 (Pred cexNonDesc_vc2)) = true

/-- **🚨 `RunPeelPreserved_bd`（`8.2-condIIIV-basedeep`）は偽**。よって
`condIIIVterminalSlice_of_runpeel` は素の `VE34Reg4` 残差の上では死んだ還元。修正は補正
体制 `VE34Reg4D`（下記）で行う。 -/
theorem RunPeelPreserved_bd_refuted_vc2 : ¬ RunPeelPreserved_bd := by
  intro h
  have hcex := h cexNonDesc_vc2 (by decide) (by decide) (by decide) (by decide)
  exact absurd hcex.1 (by decide)

/-! ## 補正残差 `RunPeelPreservedD_vc2`（descending 込みの run-peel 持続）

`RunPeelPreserved_bd` を補正体制 `VE34Reg4D` の上で述べ直したもの（Isabelle
`bfx_RPERS_base` の Lean 対応）。反例 `cexNonDesc_vc2` は非 descending ゆえ量化域から
排除される。 -/

/-- **補正版 run-peel 体制持続**（Isabelle `bfx_RPERS_base`）: run-step BASE deep の
補正体制 `VE34Reg4D` ホストで `Pred` は補正体制と BASE を保つ。 -/
def RunPeelPreservedD_vc2 : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    VE34Reg4D (Pred N) ∧ VEj1p (Pred N) = Lng (Pred N) - 1

/-! ## descending 持続半の無条件討伐（Isabelle `bfx_PredDT_base` の descending 部）

run-step BASE deep の `VE34Reg4D` ホストで `DTPS (Pred N) ∧ Br (Pred N) ≠ []` を
`descending_Br_Pred`（`8.2-strongmono-props`）直撃で与える。これが r36 修正の要石
（素の `VE34Reg4` では descending が無く供給不能だった部分）。 -/

/-- **要石**: run-step BASE deep の補正体制で `Pred` は `DTPS` を保ち、枝は非空。 -/
theorem dtps_Pred_of_runstep_vc2 (N : PS) (regD : VE34Reg4D N)
    (_hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (_hrun : LastStep N < (Br N).length - 1) :
    DTPS (Pred N) ∧ Br (Pred N) ≠ [] := by
  obtain ⟨reg4, hdesc⟩ := regD
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, _hj0lt⟩ := reg4
  have hM : TPS N := RTPS_TPS N hR
  have hDN : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hL1 : 1 < Lng N := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hLPgt : 1 < Lng (Pred N) := by omega
  have hDP : DTPS (Pred N) := descending_Br_Pred N hDN hBrne hLPgt
  -- Br (Pred N) ≠ []: Pred も非幹（TrMax 不変・Lng が deep で 1 減っても幹に落ちない）
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
  have hneP : TrMax (Pred N) ≠ Lng (Pred N) - 1 := by rw [hTrP, hLP]; omega
  have hBrPne : Br (Pred N) ≠ [] := by
    rw [Br, if_neg hneP]; exact P_nonempty _
  exact ⟨hDP, hBrPne⟩

/-! ## 残る Pred レベル幾何（Isabelle `bfx_gtP_base`＝guard／`bfx_Joints_Pred_last`＝JEQ／
単一列 base）

descending 半（`dtps_Pred_of_runstep_vc2`）が閉じたので、補正残差 `RunPeelPreservedD_vc2`
に残るのは `Pred N` の guard・joint 境界・BASE 保存のみ。これは Isabelle の run-squeeze
（`bfx_run_prev`＋`bfx_JEQ`）に対応する純幾何で、keystone 非依存・数値検証で真。 -/

/-- **残差（Pred レベル run 幾何）**: run-step BASE deep の補正体制で `Pred N` の最終枝は
guard 付き・joint は `0 < · < TrMax (Pred N)`・BASE（`VEj1p (Pred N) = Lng (Pred N) - 1`）。
Isabelle `bfx_gtP_base`/`bfx_Joints_Pred_last`＋単一列 base の Lean 対応。 -/
def RunPeelGuardJointBase_vc2 : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    entry (Pred N) 1 (VEj1p (Pred N)) < entry (Pred N) 0 (VEj1p (Pred N))
    ∧ 0 < (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
    ∧ (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0 < TrMax (Pred N)
    ∧ VEj1p (Pred N) = Lng (Pred N) - 1

/-! ## キャップストーン: 補正残差 `RunPeelPreservedD_vc2` を単一幾何残差に還元 -/

/-- **narrowing キャップストーン**: descending 持続半（証明済み `dtps_Pred_of_runstep_vc2`）
＋残る Pred 幾何 `RunPeelGuardJointBase_vc2` から補正版 run-peel 持続を放出する。 -/
theorem RunPeelPreservedD_of_geom_vc2 (hgeom : RunPeelGuardJointBase_vc2) :
    RunPeelPreservedD_vc2 := by
  intro N regD hbase hdeep hrun
  obtain ⟨hDP, hBrPne⟩ := dtps_Pred_of_runstep_vc2 N regD hbase hdeep hrun
  obtain ⟨hRP, hmonoP, hdescP⟩ := (DTPS_iff (Pred N)).mp hDP
  obtain ⟨hg, hj0p, hj0l, hbaseP⟩ := hgeom N regD hbase hdeep hrun
  exact ⟨⟨⟨⟨⟨hRP, hmonoP, hBrPne⟩, hg⟩, hj0p, hj0l⟩, hdescP⟩, hbaseP⟩

/-! ## 転記の数値検証（補正体制の量化域が非空・持続が成立）

descending witness `W = (0,0)(1,1)(2,2)(2,0)(2,0)`（basedeep の run-step witness）は補正
体制 `VE34Reg4D` に属し、run-step BASE deep で `Pred` が補正体制と BASE を保つ
（`RunPeelPreservedD_vc2`／`RunPeelGuardJointBase_vc2` の量化域が非空、かつ結論が成立）。 -/

def witW_vc2 : PS := [(0,0),(1,1),(2,2),(2,0),(2,0)]

-- W は補正体制の run-step BASE deep ホスト。
#guard decide (VE34Reg4D witW_vc2
  ∧ VEj1p witW_vc2 = Lng witW_vc2 - 1
  ∧ TrMax witW_vc2 + 2 < Lng witW_vc2
  ∧ LastStep witW_vc2 < (Br witW_vc2).length - 1) = true

-- W で補正版持続の結論が成立（Pred が VE34Reg4D かつ BASE）。
#guard decide (VE34Reg4D (Pred witW_vc2)
  ∧ VEj1p (Pred witW_vc2) = Lng (Pred witW_vc2) - 1) = true

-- W で残る Pred 幾何（guard/joint/base）が成立。
#guard decide (entry (Pred witW_vc2) 1 (VEj1p (Pred witW_vc2))
      < entry (Pred witW_vc2) 0 (VEj1p (Pred witW_vc2))
  ∧ 0 < (Joints (Pred witW_vc2)).getD ((Br (Pred witW_vc2)).length - 1) 0
  ∧ (Joints (Pred witW_vc2)).getD ((Br (Pred witW_vc2)).length - 1) 0 < TrMax (Pred witW_vc2)
  ∧ VEj1p (Pred witW_vc2) = Lng (Pred witW_vc2) - 1) = true

#print axioms VE34Reg4D_DTPS
#print axioms VE34Reg4D_of_dtps_host
#print axioms RunPeelPreserved_bd_refuted_vc2
#print axioms dtps_Pred_of_runstep_vc2
#print axioms RunPeelPreservedD_of_geom_vc2

end PSS
