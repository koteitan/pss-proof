import «8».«8.2-condIIIV-ve-continue»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — 補正残差 `RunPeelGuardJointBase_vc2` を
  **Pred-free な N レベル run-squeeze** に尖鋭化する（ve-continue の次ブリック）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel、原文 L3360 の
  「subexpr-component-`Pred`」補題）。`8.2-condIIIV-ve-continue` は素の残差
  `RunPeelPreserved_bd` が **偽**（`descendingB (Br)` 脱落）であることを機械証明し、補正体制
  `VE34Reg4D`（＝Isabelle `vg7x_reg4`）を導入、descending 持続半
  （`dtps_Pred_of_runstep_vc2`）を無条件討伐、補正版 run-peel 持続 `RunPeelPreservedD_vc2` を
  **単一の Pred レベル幾何残差 `RunPeelGuardJointBase_vc2`** に還元した
  （`RunPeelPreservedD_of_geom_vc2`）。

- **本ファイルの前進（ve-continue が「次段」と明記した尖鋭化）**: その Pred レベル残差
  `RunPeelGuardJointBase_vc2`（結論に `Pred N` を含む）を、**`Pred` を一切含まない
  純 N レベルの run-squeeze 残差 `RunSqueeze_vn`** に落とす。`RunSqueeze_vn` は
  Isabelle の `bfx_run_prev`(104581)＝run 前枝ガード ＋ `bfx_JEQ`(104639)＝run 枝の joint
  共有 ＋ BASE 単一列幾何（最終枝が単項ゆえ前枝左端＝`Lng N - 2`）の三点を、すべて
  ホスト `N` 上で述べたもの（keystone 非依存・`Pred` 非依存）。両者の橋渡し
  `RunPeelGuardJointBase_of_squeeze_vn` は **run-peel の機械的 `Pred` 転送**
  （`FirstNodes_Pred_core`／`Joints_Pred_core`／`entry_Pred`／`TrMax_Pred_nontrunk`／
  `length_Pred`）と、BASE ホストで最終枝が単項ゆえ枝が 1 本減る事実
  `(Br (Pred N)).length = (Br N).length - 1`（`Br_Pred_core_nontrunk` ＋ `wf21_Br_eq_seg`
  で最終枝長＝1 を読み、Isabelle `bfx_BrLen_Pred_base` に対応）だけで、**無条件に**
  与える。すなわち補正 run-peel 持続の残る不確定性は Isabelle `bfx_run_prev`＋`bfx_JEQ`＋
  BASE 単一列幾何の三点のみに凝縮した。

- キャップストーン `RunPeelPreservedD_of_squeeze_vn`: 補正版 run-peel 持続
  `RunPeelPreservedD_vc2` を、この **単一 Pred-free 残差 `RunSqueeze_vn`** から直接放出する
  （ve-continue の `RunPeelPreservedD_of_geom_vc2` に本ファイルの橋渡しを合成）。

- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
  ⚠️ field-level 再配線（`CondIIIVterminalSlice` の DTPS ホストから補正体制
  `VE34Reg4D` 残差への降ろし）と、`RunSqueeze_vn` 三点の値証明本体
  （`bfx_run_prev`/`bfx_JEQ`＝nextrel0 valley squeeze／BASE 単一列幾何）は本ファイルの
  射程外＝次のブリック。naive prefix-append 帰納は反証済（禁止）。

- 依存 module: `8.2-condIIIV-ve-continue`（`VE34Reg4D`/`RunPeelGuardJointBase_vc2`/
  `RunPeelPreservedD_vc2`/`RunPeelPreservedD_of_geom_vc2`/`VEj1p`/`LastStep`/`Br`/`Joints`/
  `FirstNodes`/`TrMax`/`RTPS_TPS`/`length_Pred`/`TrMax_Pred_nontrunk`/`FirstNodes_Pred_core`/
  `Joints_Pred_core`/`Br_Pred_core_nontrunk`/`entry_Pred`/`wf21_Br_eq_seg`/`length_seg`/
  `getLastD_eq_getD_last_68` を推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。`RunPeelGuardJointBase_vc2`（Pred レベル）を Pred-free の
  N レベル残差 `RunSqueeze_vn` に無条件で尖鋭化し、補正版 run-peel 持続
  `RunPeelPreservedD_vc2` を `RunSqueeze_vn` 一本 modulo で供給。

- Private suffix: `_vn`。
-/

namespace PSS

/-! ## N レベル run-squeeze 残差（`Pred` を含まない、Isabelle `bfx_run_prev`＋`bfx_JEQ`＋
BASE 単一列幾何）

補正体制 `VE34Reg4D N`・BASE `VEj1p N = Lng N - 1`・非極小基底 `TrMax N + 2 < Lng N`・
run-step `LastStep N < (Br N).length - 1` のホスト `N` について、以下の三点を要求する:

1. **run 前枝ガード**（Isabelle `bfx_run_prev(2)`、BASE 単一列で `Lng N - 2` に固定）:
   `entry N 1 (Lng N - 2) < entry N 0 (Lng N - 2)`。
2. **JEQ**（Isabelle `bfx_JEQ`）: run の前枝（`J₁-1`）と最終枝（`J₁`）は joint を共有。
3. **BASE 単一列幾何**: 最終枝が単項ゆえ前枝の左端 `FirstNodes N ! (J₁-1)` は `Lng N - 2`。

いずれも `N` 上の純幾何で `Pred` を含まず、keystone 非依存。 -/
def RunSqueeze_vn : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    entry N 1 (Lng N - 2) < entry N 0 (Lng N - 2)
    ∧ (Joints N).getD ((Br N).length - 2) 0 = (Joints N).getD ((Br N).length - 1) 0
    ∧ (FirstNodes N).getD ((Br N).length - 2) 0 = Lng N - 2

/-! ## run-step BASE ホストでの枝数減少（Isabelle `bfx_BrLen_Pred_base`, 104718）

BASE（`VEj1p N = Lng N - 1`）では最終枝は単項（長さ 1）なので、`Pred N`（＝末尾列剥がし）は
最終枝を丸ごと落とし、枝が 1 本減る。 -/

/-- **最終枝は単項**（BASE）: `Lng ((Br N).getLastD []) = 1`。`wf21_Br_eq_seg` で最終枝＝
`seg N (VEj1p N) (Lng N - 1)`、BASE で `VEj1p N = Lng N - 1` ゆえ長さ 1。 -/
private theorem lastBr_singleton_vn (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hbase : VEj1p N = Lng N - 1) : Lng ((Br N).getLastD []) = 1 := by
  have hfneq : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
    simpa only [VEj1p] using hbase
  rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, hfneq,
    length_seg]
  omega

/-- **枝数減少**（Isabelle `bfx_BrLen_Pred_base`）: BASE run-step ホストで
`(Br (Pred N)).length = (Br N).length - 1`。 -/
private theorem BrLen_Pred_base_vn (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hL1 : 1 < Lng N) (htrne : TrMax N ≠ Lng N - 1) (hbase : VEj1p N = Lng N - 1) :
    (Br (Pred N)).length = (Br N).length - 1 := by
  rw [Br_Pred_core_nontrunk N hM hL1 htrne,
    if_pos (show Lng ((Br N).getLastD []) ≤ 1 by
      rw [lastBr_singleton_vn N hM hBrne hbase])]
  simp

/-! ## 尖鋭化: `RunPeelGuardJointBase_vc2` を Pred-free 残差 `RunSqueeze_vn` から放出

`RunSqueeze_vn` の三点を、run-peel の機械的 `Pred` 転送（`FirstNodes_Pred_core`／
`Joints_Pred_core`／`entry_Pred`）で `Pred N` 側に持ち上げ、`RunPeelGuardJointBase_vc2` の
四結論（`Pred N` のガード／joint 正／joint < TrMax／BASE 保存）を無条件に与える。 -/

/-- **橋渡し（本ファイルの主定理）**: Pred レベル残差 `RunPeelGuardJointBase_vc2` を
Pred-free の N レベル run-squeeze 残差 `RunSqueeze_vn` から放出する。転送は
Isabelle `bfx_head_Pred_base`(104787)/`bfx_Joints_Pred_last`(104946)/`bfx_gtP_base`(104809)/
`bfx_FN_Pred_LS_base`(104970) の Lean 対応（`_core` 転送＋`entry_Pred`）。 -/
theorem RunPeelGuardJointBase_of_squeeze_vn (hsq : RunSqueeze_vn) :
    RunPeelGuardJointBase_vc2 := by
  intro N regD hbase hdeep hrun
  -- N レベルの三点（`regD` を消費する前に取得）
  obtain ⟨hsg, hsjeq, hsbase⟩ := hsq N regD hbase hdeep hrun
  obtain ⟨reg4, hdesc⟩ := regD
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := reg4
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
  -- run-step ⇒ 枝は 2 本以上
  have hBrge2 : 2 ≤ (Br N).length := by omega
  -- 枝数減少と添字合わせ（`J₁-1` on Pred ↔ `J₁-2` on N）
  have hBrlen : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_vn N hM hBrne hL1 htrne hbase
  have hBrlen1 : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
  have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by rw [hBrlen]; omega
  -- `VEj1p (Pred N) = Lng N - 2`（FirstNodes 転送＋BASE 単一列幾何）
  have hVEjP : VEj1p (Pred N) = Lng N - 2 := by
    unfold VEj1p
    rw [hBrlen1, FirstNodes_Pred_core N hM hL1 htrne ((Br N).length - 2) hJpP, hsbase]
  -- `Pred N` の最終 joint ＝ `N` の最終 joint（JEQ ＋ Joints 転送）
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hBrlen1, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 2) hJpP, hsjeq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) ガード on Pred: `entry (Pred N) i (Lng N-2) = entry N i (Lng N-2)`
    rw [hVEjP, entry_Pred N 1 (Lng N - 2) (by omega), entry_Pred N 0 (Lng N - 2) (by omega)]
    exact hsg
  · -- (2) joint 正
    rw [hjointP]; exact hj0pos
  · -- (3) joint < TrMax (Pred N)
    rw [hjointP, hTrP]; exact hj0lt
  · -- (4) BASE 保存
    rw [hVEjP]; omega

/-! ## キャップストーン: 補正版 run-peel 持続を Pred-free 残差一本 modulo で供給 -/

/-- **narrowing キャップストーン**: 補正版 run-peel 持続 `RunPeelPreservedD_vc2` を、
**単一の Pred-free N レベル残差 `RunSqueeze_vn`** から放出する。ve-continue の
`RunPeelPreservedD_of_geom_vc2`（Pred レベル残差版）に本ファイルの尖鋭化を合成。 -/
theorem RunPeelPreservedD_of_squeeze_vn (hsq : RunSqueeze_vn) :
    RunPeelPreservedD_vc2 :=
  RunPeelPreservedD_of_geom_vc2 (RunPeelGuardJointBase_of_squeeze_vn hsq)

/-! ## 補正体制上の LIVE run-peel 帰納法（死んだ `VE3BaseDeep_of_residuals` の置換）

`8.2-condIIIV-basedeep` の `VE3BaseDeep_of_residuals` は **偽** の残差
`RunPeelPreserved_bd`（素の `VE34Reg4` 上）を仮定するため **死んだ還元**である
（ve-continue で機械証明）。ここでは同じ後ろ剥がし帰納法を **補正体制 `VE34Reg4D`** 上で
述べ直し、補正版 run-peel 持続 `RunPeelPreservedD_vc2`（本ファイルで `RunSqueeze_vn`
一本に還元済み）で `Pred N` に降りる **LIVE** 版を与える。leaf の VE3 残差
`{VE3RunBase_bd, VE3RunStep_bd}` と極小基底 `VE3_minbase_vb` は素の `VE34Reg4`
（`VE34Reg4D → VE34Reg4` で弱めて適用）で足りる（run-peel の regime 持続のみが
`descending` を要した）。 -/

/-- **補正体制上の VE3 非極小基底残差**（Isabelle `bfx_` run-peel、`VE34Reg4D` ホスト）。 -/
def VE3BaseDeepD : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N → VE3goal N

/-- **補正体制上の VE4 非極小基底残差**（`VE34Reg4D` ホスト、pointwise）。 -/
def VE4BaseDeepD : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N → VE4goal N

/-- **LIVE 版 VE3 run-peel 帰納法**（Isabelle `bfx_VE34_backpeel_fin3` の VE3 脚、補正体制版）。
`Lng N` 強帰納法。run-step では **補正版持続 `RunPeelPreservedD_vc2`** で `Pred N` の
補正体制と BASE を回復し、極小基底なら `VE3_minbase_vb`、さもなくば IH。leaf 残差
`{VE3RunBase_bd, VE3RunStep_bd}` は素の `VE34Reg4` で足りる。 -/
theorem VE3BaseDeepD_of_residuals
    (hpres : RunPeelPreservedD_vc2) (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd) :
    VE3BaseDeepD := by
  intro N reg hbase hdeep
  generalize hn : Lng N = n
  induction n using Nat.strong_induction_on generalizing N with
  | _ n ih =>
    subst hn
    have hBrne : Br N ≠ [] := reg.1.1.1.2.2
    have hLSle : LastStep N ≤ (Br N).length - 1 := by
      have := LastStep_lt_Lng_Br N hBrne; omega
    by_cases hrun : LastStep N = (Br N).length - 1
    · exact hRB N reg.1 hbase hdeep hrun
    · have hrunstep : LastStep N < (Br N).length - 1 := by omega
      obtain ⟨hregP, hbaseP⟩ := hpres N reg hbase hdeep hrunstep
      have hL1 : 1 < Lng N := by omega
      have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
      have hM : TPS N := RTPS_TPS N reg.1.1.1.1
      have htrne : TrMax N ≠ Lng N - 1 := by omega
      have hTrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
      have hVE3P : VE3goal (Pred N) := by
        by_cases hpmin : Lng (Pred N) = TrMax (Pred N) + 2
        · exact VE3_minbase_vb (Pred N) hregP.1 hbaseP hpmin
        · have hpdeep : TrMax (Pred N) + 2 < Lng (Pred N) := by
            rw [hLP, hTrP] at hpmin ⊢; omega
          exact ih (Lng (Pred N)) (by omega) (Pred N) hregP hbaseP hpdeep rfl
      exact hRS N reg.1 hbase hdeep hrunstep hVE3P

/-- **VE4 補正体制版**は素の `VE4BaseDeep`（`VE34Reg4` 上）を `VE34Reg4D → VE34Reg4` で
弱めるだけ（VE4 は IH 非消費の pointwise で run-peel の regime 持続を要さない）。 -/
theorem VE4BaseDeepD_of_BaseDeep (h : VE4BaseDeep) : VE4BaseDeepD := by
  intro N regD hbase hdeep
  exact h N regD.1 hbase hdeep

/-! ## narrowing キャップストーン: VE3 補正基底残差を Pred-free 残差一本＋leaf 残差から放出 -/

/-- **キャップストーン**: 補正体制上の VE3 非極小基底残差 `VE3BaseDeepD` を、本ファイルの
Pred-free run-squeeze 残差 `RunSqueeze_vn` と leaf 残差 `{VE3RunBase_bd, VE3RunStep_bd}` から
放出する。run-peel 持続の残る不確定性は `RunSqueeze_vn`（＝`bfx_run_prev`＋`bfx_JEQ`＋
BASE 単一列幾何）一本のみ。 -/
theorem VE3BaseDeepD_of_squeeze
    (hsq : RunSqueeze_vn) (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd) :
    VE3BaseDeepD :=
  VE3BaseDeepD_of_residuals (RunPeelPreservedD_of_squeeze_vn hsq) hRB hRS

/-! ## 転記の数値検証（run-squeeze 残差の量化域が非空・三点が成立）

witness `W = (0,0)(1,1)(2,2)(2,0)(2,0)`（ve-continue の `witW_vc2`）は補正体制 `VE34Reg4D`
の BASE run-step 非極小基底ホスト（`VEj1p = 4 = Lng - 1`、`TrMax + 2 = 4 < 5 = Lng`、
`LastStep = 0 < 1 = Br.length - 1`）であり、`RunSqueeze_vn` の三点
（run 前枝ガード／JEQ／BASE 単一列幾何）がすべて成立する。 -/

def witSq_vn : PS := [(0,0),(1,1),(2,2),(2,0),(2,0)]

-- W は run-step BASE 非極小基底ホスト。
#guard decide (VE34Reg4D witSq_vn
  ∧ VEj1p witSq_vn = Lng witSq_vn - 1
  ∧ TrMax witSq_vn + 2 < Lng witSq_vn
  ∧ LastStep witSq_vn < (Br witSq_vn).length - 1) = true

-- W で `RunSqueeze_vn` の三点（run 前枝ガード／JEQ／BASE 単一列幾何）が成立。
#guard decide (entry witSq_vn 1 (Lng witSq_vn - 2) < entry witSq_vn 0 (Lng witSq_vn - 2)
  ∧ (Joints witSq_vn).getD ((Br witSq_vn).length - 2) 0
      = (Joints witSq_vn).getD ((Br witSq_vn).length - 1) 0
  ∧ (FirstNodes witSq_vn).getD ((Br witSq_vn).length - 2) 0 = Lng witSq_vn - 2) = true

-- W では最終枝が単項（`Lng (lastBr) = 1`）で枝が 1 本減る。
#guard decide (Lng ((Br witSq_vn).getLastD []) = 1
  ∧ (Br (Pred witSq_vn)).length = (Br witSq_vn).length - 1) = true

#print axioms lastBr_singleton_vn
#print axioms BrLen_Pred_base_vn
#print axioms RunPeelGuardJointBase_of_squeeze_vn
#print axioms RunPeelPreservedD_of_squeeze_vn
#print axioms VE3BaseDeepD_of_residuals
#print axioms VE4BaseDeepD_of_BaseDeep
#print axioms VE3BaseDeepD_of_squeeze

end PSS
