import «8».«8.3-condII-NotLdjReg-close»
import «8».«8.3-condII-TrunkLeg»

/-!
# §8.3 条件(II) — `TvxBoundaryData` を単一の §8.2 命題へ還元（transport 段の無条件化）

## 原文 / Isabelle 対応

- 原文: `tmp/content.md` 4188–4243（§8.3 命題（条件(II)の下での `Trans` と基本列の
  交換関係）の `leftDj0`-leg = 境界 tail 値と `ldj`）。
- 逐語の証明: Isabelle `tvx_tailval_of_boundary`
  (`isabelle/layerB/pss_wip.thy`:110527–110642)。その **transport/存在段**
  （110569–110615）を無条件に Lean 化する。
- 対象残差: `TvxBoundaryData`（ビルド済み «8».«8.3-condII-BoundaryLeg2»:90）。
  これを `condII_masterCF_of_boundaryData`（«8».«8.3-condII-NotLdjReg-close»:98）へ
  食わせれば `CondII_masterCF` が無条件化される。

## 何を閉じ、何が残るか（正直な還元）

Isabelle の `tvx_tailval_of_boundary` の存在段は、簡約祖先切片
`R_c = Red (seg M j₋₁ (Lng M-2))` 上で **`hqx_condIIIV_of_DT`**（§8.2 命題（条件(II)
か(IV)の下での終切片と `Trans` の関係）の EX1）を呼び出し、その clause を W1/W2 で
元の切片へ transport する。本ファイルは:

* **transport 段を完全に無条件で移植**（W1/W2/W3 = `wnx_seg_transport_*`、
  行1 entry の shift = `repr_entry1_shift_gen`、Mark-`Trans` bridge =
  `c2sx_slice_jm1_c1`、`R_c ∈ DT_PS` = `standard_slice_Red_strongmono`、
  `d < TrMax R_c` = `TVX_dstrict_ldjb_holds`、reach = `c2sx_reach_leab/leam`、
  `Dprin` 単射 = value-algebra）。
* 残差を **たった 1 本の named §8.2 命題** `CondIIIVterminalSlice`
  （= `p_8_2_condIIIV_terminal_slice_Trans` の無条件形、EX1 producer）へ折り畳む。

### `vcx_VE_all` を食わせても condIIIV EX1 は閉じない（検証結果）

Wave-O の blocker `hqx_condIIIV_of_DT` の 3 値入力は `vg3x_VE2`（VE2）と
`hqx_VE34_of_DT`（VE3/VE4 = `vg2x_VE34`）である。無条件 `vcx_VE_all`
（«8».«8.2-condV-VE-close»、条件(V) の VE）が消せるのは、`vg2x_VE34` の back-peel
帰納 `bgx_VE34_of_DT_modHEADEQ` の中の **HEADEQ0 brick 1 本**（`hqx_HEADEQ0`,
`isabelle/layerB/pss_wip.thy`:108441）のみ。VE2/VE3/VE4 自身は条件(V) の VE の
instance では**なく**、`isabelle/layerB/pss_wip.thy` 93171–108761（≈15590 行）の
condII/IV 専用 back-peel chain（`vg2x_*`/`vg3x_*`/`vg4x_*`/`vg7x_*`/`bfx_*`/`bgx_*`/
`hqx_*`）であって **Lean 未移植**。したがって `condIIIV_terminal_slice_Trans_modVE`
（«8».«8.2-condIIIV-terminal-slice-Trans»、VE2/VE3/VE4 仮定付き）を無条件化する
`CondIIIVterminalSlice` が真の残差であり、`needs` に報告する。

## 依存（すべて COMMITTED 緑、main db1f93c）

* «8».«8.3-condII-NotLdjReg-close» — `TvxBoundaryData` / `tv_boundaryleg_of_data` /
  `condII_masterCF_of_boundaryData`（推移的に BoundaryLeg2）、`vcx_VE_all`、
  `wnx_seg_transport_W1/_W2/_W3` / `repr_entry1_shift_gen` / `c2sx_reach_leab/_leam` /
  `TVX_dstrict_ldjb_holds`（wnx）、`condIIIV_terminal_slice_Trans_modVE` / `LastStep`
  （condIIIV）、`standard_slice_Red_strongmono` / `DTPS` / `DTPS_iff`、
  `condII_host_basic_holds`、`STPS_RTPS` / `Adm_le`。
* «8».«8.3-condII-TrunkLeg» — `c2sx_slice_jm1_c1`（Mark-`Trans` bridge）。

## 状態

* ✅ `tvxBoundaryData_of_condIIIV : CondIIIVterminalSlice → TvxBoundaryData`
  — transport/存在段は**無条件**（sorry 0、axioms 正常）。
* ✅ `tv_boundaryleg_of_condIIIV` / `condII_masterCF_of_condIIIV` — 上を
  ビルド済み drop-in へ配線。
* 🚫 `CondIIIVterminalSlice`（= §8.2 condII/IV 終切片命題の無条件形）は**本ファイル
  では閉じていない**（上記 ≈15590 行の condIIIV VE34 chain が未移植）＝`needs` に報告。
  真の主張であり vacuous でない（`condIIIV_terminal_slice_Trans_modVE` の非空虚性
  witness `witness_hyps_c24` を参照）。
-/

namespace PSS

/-! ## 私的補助（suffix `_bc2`） -/

/-- `Dprin` の内部項は `bpHeadT` で読み出せる。 -/
private theorem bpHeadT_Dprin_bc2 (v : ℕ∞) (a : BT) :
    bpHeadT (Dprin v a) = a := rfl

/-- `Dprin` は第 2 引数について単射（第 1 引数固定）。Isabelle `cdx_Dpt_inj`。 -/
private theorem Dprin_inj_bc2 {v : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin v b) : a = b := by
  have := congrArg bpHeadT h
  simpa [bpHeadT_Dprin_bc2] using this

/-! ## 露出した残差 `Prop`（Isabelle `p_8_2_condIIIV_terminal_slice_Trans` の無条件形）

Isabelle `hqx_condIIIV_of_DT`（`isabelle/layerB/pss_wip.thy`:108722）の 1:1。
ビルド済み `condIIIV_terminal_slice_Trans_modVE`（«8».«8.2-condIIIV-terminal-slice-Trans»）
から `VE2`/`VE3`/`VE4`/`t₂ ≠ 0_B` の 4 仮定を除いた無条件形。これらは condII/IV 専用の
VE chain（≈15590 行、Lean 未移植）が与える。空虚でないことは同ファイルの
`witness_hyps_c24`（`M = (0,0)(1,1)(2,2)(2,0)`）が保証する。 -/
def CondIIIVterminalSlice : Prop :=
  ∀ (M : PS), DTPS M → Br M ≠ [] →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    (Joints M).getD ((Br M).length - 1) 0 < TrMax M →
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) →
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
          (addBT t12.1 t12.2)))

/-! ## transport/存在段の無条件化（Isabelle `tvx_tailval_of_boundary` 110569–110615） -/

/-- Isabelle `tvx_tailval_of_boundary`（`isabelle/layerB/pss_wip.thy`:110527）の
transport/存在段を、単一の §8.2 命題 `CondIIIVterminalSlice` から**無条件に**
供給する。`R_c = Red (seg M j₋₁ (Lng M-2))` 上の EX1（clause 3/4/5）を W1/W2 で
元の切片へ戻し、`transT2 M` の snoc 表示（`T2EQ`）と境界 tail 値（conj1）を得る。 -/
theorem tvxBoundaryData_of_condIIIV (hEX1 : CondIIIVterminalSlice) :
    TvxBoundaryData := by
  intro M hST hmono hj1 hcond hBr hDEQ hGUARD _hFin
  have hR : RTPS M := STPS_RTPS M hST
  -- 事前に取り出す定理（transCondII ホストの基本性質・reach・strictness・bridge）
  obtain ⟨_, _, _, _, hAdmLt, hParLt, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hleab := c2sx_reach_leab M hR hmono hj1 hcond
  have hleam0 := c2sx_reach_leam M hR hmono hj1 hcond
  have hdstrict := TVX_dstrict_ldjb_holds M hR hmono hj1 hcond
  have hbridge := c2sx_slice_jm1_c1 M hR hmono hj1 hcond
  have hjm1le := Adm_le M (parent M 0 (Lng M - 1))
  -- tvx_ 定義を raw 形へ展開してから略記を fold
  simp only [tvx_Rc, tvx_d, tvx_jL, tvx_fn] at hBr hDEQ hGUARD hdstrict
  set j0 := parent M 0 (Lng M - 1) with hj0def
  set jm1 := Adm M j0 with hjm1def
  set b := Lng M - 2 with hbdef
  -- 幾何
  have hdpos : 0 < j0 - jm1 := by omega
  have hjm1d : jm1 + (j0 - jm1) = j0 := by omega
  have hab : jm1 < b := by omega
  have hbL : b ≤ Lng M - 1 := by omega
  have hamb : jm1 + (j0 - jm1) < b := by omega
  have hleam : le0 M (jm1 + (j0 - jm1)) b = true := by rw [hjm1d]; exact hleam0
  -- `R_c ∈ DT_PS`
  have hRcDT : DTPS (Red (seg M jm1 b)) :=
    standard_slice_Red_strongmono M jm1 b hST hab hbL hleab
  -- 切片の長さと行1 entry の shift（e0/ed）
  have hW3 : Lng (Red (seg M jm1 b)) - 1 = b - jm1 :=
    wnx_seg_transport_W3 M jm1 b hab
  have hLRcpos : 0 < Lng (Red (seg M jm1 b)) := by omega
  have hdlt : j0 - jm1 < Lng (Red (seg M jm1 b)) := by omega
  have he0 : entry (Red (seg M jm1 b)) 1 0 = entry M 1 jm1 := by
    have h := repr_entry1_shift_gen M jm1 b 0 hR hab hbL hleab hLRcpos
    rwa [Nat.add_zero] at h
  have hed : entry (Red (seg M jm1 b)) 1 (j0 - jm1) = entry M 1 j0 := by
    have h := repr_entry1_shift_gen M jm1 b (j0 - jm1) hR hab hbL hleab hdlt
    rwa [hjm1d] at h
  have hvJeq : entry (Red (seg M jm1 b)) 1
        ((Joints (Red (seg M jm1 b))).getD ((Br (Red (seg M jm1 b))).length - 1) 0)
      = entry M 1 j0 := by
    rw [← hDEQ]; exact hed
  -- Mark-`Trans` bridge を `R_c` へ transport
  have hW1 : Trans (seg M jm1 b) = Trans (Red (seg M jm1 b)) :=
    wnx_seg_transport_W1 M jm1 b hab
  have hTRc : Trans (Red (seg M jm1 b)) = Dprin (entry M 1 jm1 : ℕ∞) (transT2 M) :=
    hW1.symm.trans hbridge
  -- 幾何仮定を `R_c` の §8.2 命題へ供給
  have hj0pos : 0 < (Joints (Red (seg M jm1 b))).getD
      ((Br (Red (seg M jm1 b))).length - 1) 0 := hDEQ ▸ hdpos
  have hj0lt : (Joints (Red (seg M jm1 b))).getD
        ((Br (Red (seg M jm1 b))).length - 1) 0 < TrMax (Red (seg M jm1 b)) :=
    hDEQ ▸ hdstrict
  -- §8.2 condII/IV 終切片命題（EX1）を `R_c` で適用し存在を取る
  obtain ⟨t12, _hc1, _hc2, hc3, hc4, hc5⟩ :=
    (hEX1 (Red (seg M jm1 b)) hRcDT hBr hj0pos hj0lt hGUARD).exists
  -- W2': 末尾切片 tail value の transport
  have hW2 := wnx_seg_transport_W2 M jm1 b (j0 - jm1) hR hab hbL hleab hamb hleam
  rw [hjm1d, hDEQ] at hW2
  -- `T2EQ`（原文 (2) の value-algebra 入力 = conj2）
  rw [he0, hvJeq] at hc5
  have hT2EQ : transT2 M
      = addBT t12.1 (Dprin (entry M 1 j0 : ℕ∞) (addBT t12.1 t12.2)) :=
    Dprin_inj_bc2 (hTRc.symm.trans hc5)
  refine ⟨t12.1, t12.2, ?_, hT2EQ, hc4⟩
  -- conj1: 境界 tail value（原文 (1)）
  rw [hW2, hc3, hvJeq]

/-! ## ビルド済み drop-in への配線（house pattern） -/

/-- `CondIIIVterminalSlice` から `TV_BoundaryLeg`（«8».«8.3-condII-masterCF-port»:130）を
無条件に供給する（`tv_boundaryleg_of_data` を経由）。 -/
theorem tv_boundaryleg_of_condIIIV (hEX1 : CondIIIVterminalSlice) : TV_BoundaryLeg :=
  tv_boundaryleg_of_data (tvxBoundaryData_of_condIIIV hEX1)

/-- `CondIIIVterminalSlice` から `CondII_masterCF`（«8».«8.3-TransCondII-engine»:219）を
無条件に供給する（`condII_masterCF_of_boundaryData` を経由）。§8.2 condII/IV 終切片
命題が Lean 化されれば、これで condII 停止性フィールドが落ちる。 -/
theorem condII_masterCF_of_condIIIV (hEX1 : CondIIIVterminalSlice) : CondII_masterCF :=
  condII_masterCF_of_boundaryData (tvxBoundaryData_of_condIIIV hEX1)

#print axioms tvxBoundaryData_of_condIIIV
#print axioms tv_boundaryleg_of_condIIIV
#print axioms condII_masterCF_of_condIIIV

end PSS
