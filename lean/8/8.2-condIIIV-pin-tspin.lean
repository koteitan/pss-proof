import «8».«8.2-condIIIV-basedeep»
import «8».«8.2-condIIIV-census-slice»
import «8».«8.2-condIIIV-headeq0-close»

/-!
# §8.2 条件(II)/(IV) VE34 — `PIN_bd` / `TSPIN_bd` の**反証**と D-体制の正しい代替

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係、
  原文 part(1)「brN」の pinned 形＝PIN と非許容 joint での Mark-surgery naturality＝TSPIN）。
  `8.2-condIIIV-basedeep` は `VE4BaseDeep`（`VE34Reg4` ホスト、pointwise）を二つの残差
  `{PIN_bd, TSPIN_bd}` に還元した（`VE4BaseDeep_of_pin_tspin`）。本ファイルはその
  discharge を試み、**素の体制 `VE34Reg4` 上ではこの還元自体が死んでいる**ことを機械反証する。

- 🚨 **反証（11 本目、`RunPeelPreserved_bd` の死と同型）**: `PIN_bd`/`TSPIN_bd` の量化域
  `VE34Reg4`（＝`vg4x_reg4`、`descending` を**含まない**）には非 descending ホスト
  `cexND_pt = (0,0)(1,1)(2,2)(2,1)(2,2)(2,0)` が属し、そこで `VE4goal` が**偽**
  （数値検証、`ve4b cexND_pt = false`）。ゆえに `VE4BaseDeep` は `VE34Reg4` 上で偽であり、
  その供給者 `PIN_bd ∧ TSPIN_bd` も同時に成立し得ない（`not_pin_tspin_pt`）。これは
  `RunPeelPreserved_bd` が非 descending で偽になった `pss-67` 系の死因（memo Wave AM/AL）と
  同型の設計欠陥＝**pointwise 還元が `descending` を落とした量化域に載っている**。

- **正しい体制は補正版 `VE34Reg4D`（＝`vg7x_reg4 = vg4x_reg4 ∧ descending`）**。D-体制の
  run-step / run-base 証人（`witRS_pv`, `hostBF`）では `VE4goal` は真（数値検証）。本ファイルは
  D-体制で PIN/TSPIN を述べ直し（`PIN_D_pt`/`TSPIN_D_pt`）、**run-base 脚を無条件討伐**、
  run-step 脚を単一の sharp 残差 `TransPinRunStepD_pt` に露出する。さらにこの残差から
  **LIVE な `VE4BaseDeepD`（`VE34Reg4D` ホスト）を run-base 込みで放出**（`VE4BaseDeepD_of_runstep_pt`）
  — これが停止性ゲートに接続すべき正しい VE4 側の姿である。

- **run-base 討伐の道具（すべて Wave AN–AQ で無条件化済み、本ファイルで組立）**:
  `BgxBaseFormNotleft_of_census_bf BgxNotleftRun0_cs2`（clause-2 sharp form、census で isleft
  非発火）＋`BgxMpForm_of_slice_bf BgxMpSliceData_cs2`（終切片 Adm0 閉形式）＋
  `bgx_front_run0_bg`（run-base 前切片 = `Pred N`）＋`headEq0All_holds`（HEADEQ0:
  `bpHeadT (Trans (Pred Mp)) = bpHeadT (Trans (Pred N))`）。組立は純 BT-代数
  （`bpHeadT (Dprin v a) = a`）。Isabelle `bgx_VE34_base_run0_mod` 106689 の逐語構造。

- **run-step 残差 `TransPinRunStepD_pt`**（＝pinned assembly、内部項 `a = bpHeadT (Trans Mp)`）:
  Isabelle では `bgx_VE34_base_step` (106565) が **IH の VE4（`vg2x_VE34 (Pred N)`）** を消費して
  discharge する（isleft selector が IH で発火→clause-4 form）。pointwise（IH 非消費）では
  閉じない＝これが `PIN_bd` を pointwise 化した時の真の障害。よって残差として露出し、
  最終的には統一 back-peel の `BaseRunStep_up`（IH 保持スロット）で吸収されるべきもの。

- 訂正: `PIN_bd`/`TSPIN_bd`（`8.2-condIIIV-basedeep`）は `VE34Reg4` 上で偽（本ファイルで機械反証）。
  停止性ゲートは `VE4BaseDeep_of_pin_tspin` 経由ではなく、D-体制 `VE4BaseDeepD`（本ファイルの
  `VE4BaseDeepD_of_runstep_pt`）経由で接続すること。

- 依存 module: `8.2-condIIIV-basedeep`（`PIN_bd`/`TSPIN_bd`/`VE4BaseDeep`/`VE4BaseDeep_of_pin_tspin`/
  `VE34Reg4`/`VEj1p`/`VE4goal`）, `8.2-condIIIV-census-slice`（`BgxNotleftRun0_cs2`/
  `BgxMpSliceData_cs2` ＋推移的に `BgxBaseFormNotleft_of_census_bf`/`BgxMpForm_of_slice_bf`/
  `bgx_front_run0_bg`/`VE34Reg4D`/`VE4BaseDeepD`）, `8.2-condIIIV-headeq0-close`（`headEq0All_holds`）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。`PIN_bd`/`TSPIN_bd` を機械反証、D-体制 `PIN_D_pt`/`TSPIN_D_pt`
  の run-base 脚と終切片 leadform を無条件討伐、`VE4BaseDeepD` を単一 run-step 残差
  `TransPinRunStepD_pt` modulo（run-base 込み）で放出。

- Private suffix: `_pt`。
-/

namespace PSS

/-! ## 私的補助（suffix `_pt`） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開）。 -/
private theorem bpHeadT_Dprin_pt (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- `Dprin` の内部項に関する単射性（`.trm [.db v ·]` の inj）。 -/
private theorem Dprin_inj_pt (v : ℕ∞) (x y : BT) (h : Dprin v x = Dprin v y) : x = y := by
  simpa [Dprin] using h

/-- **末尾 principal の内部項単射**（Isabelle `vg6x_addBT_split_lastD` の左因子共有版）:
`F +_B D_v a = F +_B D_v b ⟹ a = b`。`addBT (.trm fs) (.trm [.db v a]) = .trm (fs ++ [.db v a])`
の list 連結左簡約による。 -/
private theorem addBT_last_inj_pt (F : BT) (v : ℕ∞) (a b : BT)
    (h : addBT F (Dprin v a) = addBT F (Dprin v b)) : a = b := by
  obtain ⟨fs⟩ := F
  simp only [Dprin, addBT] at h
  have h2 : [BP.db v a] = [BP.db v b] := List.append_cancel_left (BT.trm.inj h)
  simp only [List.cons.injEq, BP.db.injEq, and_true] at h2
  exact h2.2

/-! ## 🚨 反証: `PIN_bd` / `TSPIN_bd` は `VE34Reg4` 上で偽

非 descending ホスト `cexND_pt` は `VE34Reg4 ∧ BASE ∧ deep ∧ run-step` に属すが、そこで
`VE4goal` が偽。`VE4BaseDeep_of_pin_tspin`（`8.2-condIIIV-basedeep`）は
`PIN_bd → TSPIN_bd → VE4BaseDeep` を与えるので、両者は同時に成立し得ない。 -/

/-- 非 descending の `VE34Reg4` 深 BASE run-step 反例（Isabelle r36 `cexNonDesc_vc2` と同一）。 -/
def cexND_pt : PS := [(0,0),(1,1),(2,2),(2,1),(2,2),(2,0)]

/-- **`PIN_bd` ∧ `TSPIN_bd` は偽**（機械反証）。非 descending ホスト `cexND_pt` で `VE4goal` が
偽であることから、`VE4BaseDeep_of_pin_tspin` 経由で矛盾。 -/
theorem not_pin_tspin_pt : ¬ (PIN_bd ∧ TSPIN_bd) := by
  rintro ⟨hP, hT⟩
  have hgoal : VE4goal cexND_pt :=
    VE4BaseDeep_of_pin_tspin hP hT cexND_pt (by decide) (by decide) (by decide)
  rw [VE4goal] at hgoal
  have hb : (bpHeadT (Trans cexND_pt) ==
      addBT (bpHeadT (Trans (seg cexND_pt 0 ((FirstNodes cexND_pt).getD (LastStep cexND_pt) 0 - 1))))
        (Dprin (entry cexND_pt 1 ((Joints cexND_pt).getD ((Br cexND_pt).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg cexND_pt ((Joints cexND_pt).getD ((Br cexND_pt).length - 1) 0)
            (Lng cexND_pt - 1)))))) = false := by decide
  rw [beq_iff_eq.mpr hgoal] at hb
  exact absurd hb (by decide)

/-! ## 終切片の leadform（Isabelle `kyx_terminal_slice_leadform` 99604、D-体制版）

`BgxMpForm_bg`（Adm0 閉形式、census-slice で無条件）から終切片 `Mp = seg N j₀' (Lng N-1)` の
外側 principal 形 `Trans Mp = D_{N₁,j₀'}(bpHeadT (Trans Mp))` を読む。 -/

/-- **`mpLeadForm_D_pt`**: 終切片 `Mp` は外側 principal `D_{N₁,j₀'}` で先頭固定される。 -/
theorem mpLeadForm_D_pt (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N) :
    Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))
      = Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))) := by
  have hMp := (BgxMpForm_of_slice_bf BgxMpSliceData_cs2) N regD hbase hdeep
  have hhead : bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
      = addBT (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))
          (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) := by rw [hMp, bpHeadT_Dprin_pt]
  rw [hhead]; exact hMp

/-! ## run-base pinned assembly（Isabelle `bgx_VE34_base_run0_mod` 106689、D-体制、無条件）

clause-2 sharp form ＋ Mp closed form ＋ front 同定 ＋ HEADEQ0 から `Trans N` の pinned 形
`D_{N₁,0}(F +_B D_{N₁,j₀'}(bpHeadT (Trans Mp)))`（`F = bpHeadT (Trans (front slice))`）を組む。 -/

/-- **`transPinRunBaseD_pt`**: D-体制 run-base 深 BASE ホストでの `Trans N` の pinned 形
（内部項 `a = bpHeadT (Trans Mp)`）。すべての入力（census / slice / front / HEADEQ0）は無条件。 -/
theorem transPinRunBaseD_pt (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (hrun : LastStep N = (Br N).length - 1) :
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))) := by
  have hL : 1 < Lng N := by omega
  have hform := (BgxBaseFormNotleft_of_census_bf BgxNotleftRun0_cs2) N regD hbase hdeep hrun
  have hMpHead : bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
      = addBT (bpHeadT (Trans (Pred N))) (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) := by
    have hMp := (BgxMpForm_of_slice_bf BgxMpSliceData_cs2) N regD hbase hdeep
    have hHE := headEq0All_holds N regD hbase hrun
    rw [hMp, bpHeadT_Dprin_pt, hHE]
  have hF : bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))
              = bpHeadT (Trans (Pred N)) := by rw [bgx_front_run0_bg N hL hbase hrun]
  rw [hform, hF, hMpHead]

/-! ## run-step 残差＋全域 pinned 形（run-base 込み）

run-step 脚は IH（`VE34goal (Pred N)`）を消費する（Isabelle `bgx_VE34_base_step`）ので pointwise
では閉じない。単一の sharp 残差として露出する。 -/

/-- **run-step pinned assembly 残差**（Isabelle `bgx_VE34_base_step` 106565 の VE4 側 pinned 形）:
D-体制 run-step 深 BASE ホストでの `Trans N` の pinned 形。IH で isleft selector が発火する
clause-4 form の内部項固定＝統一 back-peel の `BaseRunStep_up`（IH 保持スロット）が吸収する。 -/
def TransPinRunStepD_pt : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))))

/-- **全域 pinned 形**（run-base 無条件討伐、run-step 残差 modulo）: D-体制の全深 BASE ホストで
`Trans N` は pinned 形をとる。 -/
theorem transPinD_of_runstep_pt (hRS : TransPinRunStepD_pt) (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N) :
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))) := by
  have hBrne : Br N ≠ [] := regD.1.1.1.2.2
  have hLSle : LastStep N ≤ (Br N).length - 1 := by
    have := LastStep_lt_Lng_Br N hBrne; omega
  by_cases hrun : LastStep N = (Br N).length - 1
  · exact transPinRunBaseD_pt N regD hbase hdeep hrun
  · exact hRS N regD hbase hdeep (by omega)

/-! ## D-体制の PIN / TSPIN（`8.2-condIIIV-basedeep` の `PIN_bd`/`TSPIN_bd` の**正しい** 代替）

素の `VE34Reg4` を補正体制 `VE34Reg4D` に差し替えた版。run-base 脚は無条件、run-step 脚は
`TransPinRunStepD_pt` modulo。 -/

/-- **`PIN_D_pt`**（`PIN_bd` の D-体制版）: pinned 形の存在。 -/
def PIN_D_pt : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    ∃ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a))

/-- **`TSPIN_D_pt`**（`TSPIN_bd` の D-体制版）: pinned 形の内部項は終切片頭に一致。 -/
def TSPIN_D_pt : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    ∀ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a)) →
      a = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))

/-- **`PIN_D_pt` を run-step 残差から放出**（run-base 込み）。証人 `a = bpHeadT (Trans Mp)`。 -/
theorem PIN_D_of_runstep_pt (hRS : TransPinRunStepD_pt) : PIN_D_pt := by
  intro N regD hbase hdeep
  exact ⟨_, transPinD_of_runstep_pt hRS N regD hbase hdeep⟩

/-- **`TSPIN_D_pt` を run-step 残差から放出**（run-base 込み）。全域 pinned 形と仮定形を
外側 `Dprin` ＋末尾 principal で簡約。 -/
theorem TSPIN_D_of_runstep_pt (hRS : TransPinRunStepD_pt) : TSPIN_D_pt := by
  intro N regD hbase hdeep a hform
  have hpin := transPinD_of_runstep_pt hRS N regD hbase hdeep
  rw [hform] at hpin
  exact addBT_last_inj_pt _ _ _ _ (Dprin_inj_pt _ _ _ hpin)

/-! ## LIVE な VE4 側キャップストーン: `VE4BaseDeepD` を run-step 残差から（run-base 込み）

停止性ゲートに接続すべき正しい VE4 非極小基底残差（`VE34Reg4D` ホスト、pointwise）。
run-base は無条件討伐、run-step は `TransPinRunStepD_pt` modulo。 -/

/-- **`VE4BaseDeepD_of_runstep_pt`**: `VE4BaseDeepD`（`8.2-condIIIV-ve-next`）を run-step 残差
`TransPinRunStepD_pt` から放出する。`VE4goal N` は pinned 形の外側頭読み出し。 -/
theorem VE4BaseDeepD_of_runstep_pt (hRS : TransPinRunStepD_pt) : VE4BaseDeepD := by
  intro N regD hbase hdeep
  rw [VE4goal, transPinD_of_runstep_pt hRS N regD hbase hdeep, bpHeadT_Dprin_pt]

/-! ## 転記の数値検証（反証＋ D-体制での成立） -/

-- `cexND_pt` は `VE34Reg4 ∧ BASE ∧ deep ∧ run-step` かつ非 descending（反証量化域）。
#guard decide (VE34Reg4 cexND_pt
  ∧ VEj1p cexND_pt = Lng cexND_pt - 1
  ∧ TrMax cexND_pt + 2 < Lng cexND_pt
  ∧ LastStep cexND_pt < (Br cexND_pt).length - 1
  ∧ ¬ (descendingB (Br cexND_pt) = true)) = true

-- `cexND_pt` で `VE4goal`（pinned 頭方程式）は**偽**（`PIN_bd`/`TSPIN_bd` の死因）。
#guard (bpHeadT (Trans cexND_pt) ==
    addBT (bpHeadT (Trans (seg cexND_pt 0 ((FirstNodes cexND_pt).getD (LastStep cexND_pt) 0 - 1))))
      (Dprin (entry cexND_pt 1 ((Joints cexND_pt).getD ((Br cexND_pt).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg cexND_pt ((Joints cexND_pt).getD ((Br cexND_pt).length - 1) 0)
          (Lng cexND_pt - 1)))))) = false

-- D-体制 run-step 証人（`8.2-condIIIV-peel-values` の `witRS_pv` と同一）で `VE4goal` は**真**。
def witRS_pt : PS := [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
#guard decide (VE34Reg4D witRS_pt
  ∧ VEj1p witRS_pt = Lng witRS_pt - 1
  ∧ TrMax witRS_pt + 2 < Lng witRS_pt
  ∧ LastStep witRS_pt < (Br witRS_pt).length - 1) = true
#guard (bpHeadT (Trans witRS_pt) ==
    addBT (bpHeadT (Trans (seg witRS_pt 0 ((FirstNodes witRS_pt).getD (LastStep witRS_pt) 0 - 1))))
      (Dprin (entry witRS_pt 1 ((Joints witRS_pt).getD ((Br witRS_pt).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg witRS_pt ((Joints witRS_pt).getD ((Br witRS_pt).length - 1) 0)
          (Lng witRS_pt - 1)))))) = true

-- D-体制 run-base 証人（`hostBF`/`hostBG` と同一）で pinned assembly の shape が実 `Trans` に一致。
def hostBF_pt : PS := [(0,0),(1,1),(2,2),(2,2),(2,0)]
#guard decide (VE34Reg4D hostBF_pt
  ∧ VEj1p hostBF_pt = Lng hostBF_pt - 1
  ∧ TrMax hostBF_pt + 2 < Lng hostBF_pt
  ∧ LastStep hostBF_pt = (Br hostBF_pt).length - 1) = true
#guard (Trans hostBF_pt == Dprin (entry hostBF_pt 1 0 : ℕ∞)
    (addBT (bpHeadT (Trans (seg hostBF_pt 0 ((FirstNodes hostBF_pt).getD (LastStep hostBF_pt) 0 - 1))))
      (Dprin (entry hostBF_pt 1 ((Joints hostBF_pt).getD ((Br hostBF_pt).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg hostBF_pt ((Joints hostBF_pt).getD ((Br hostBF_pt).length - 1) 0)
          (Lng hostBF_pt - 1))))))) = true

#print axioms not_pin_tspin_pt
#print axioms mpLeadForm_D_pt
#print axioms transPinRunBaseD_pt
#print axioms transPinD_of_runstep_pt
#print axioms PIN_D_of_runstep_pt
#print axioms TSPIN_D_of_runstep_pt
#print axioms VE4BaseDeepD_of_runstep_pt

end PSS
