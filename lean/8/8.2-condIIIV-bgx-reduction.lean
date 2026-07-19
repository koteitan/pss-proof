import «8».«8.2-condIIIV-headeq0»
import «8».«8.2-condIIIV-unified-peel»

/-!
# §8.2 条件(II)/(IV) VE34 — **bgx reduction**（HEADEQ0 ⟹ VE34goal on all `VE34Reg4D`）

- 原文: `tmp/content.md` L1624/L3314 付近（命題「条件(II)か(IV)の下での終切片と `Trans` の
  関係」）。本ファイルは `8.2-condIIIV-headeq0` が名前付き Prop として宣言した残差
  **`BgxVE34RedHE0_hq`** を討伐する route を提供する。

- **目標**（`8.2-condIIIV-headeq0` 由来）:
  `BgxVE34RedHE0_hq := ∀ M, VE34Reg4D M → HEADEQ0All_hq → VE34goal M`。
  Isabelle 側の本体は `layerB/pss_wip.thy` の `bgx_VE34_of_reg_modHEADEQ` (107245):
  `bgx_notleft_run0` (106972、census で NOTLEFT0 を討伐) ＋
  `bgx_VE34_of_reg_modNOTLEFT_HEADEQ` (106728、統一 back-peel 強帰納法)。

- **本ファイルの設計**（統一 back-peel 帰納法 `VE34_backpeel_fin3_up` に RIDE する）:
  `8.2-condIIIV-unified-peel` の `VE34_backpeel_fin3_up` は、補正体制 `VE34Reg4D` の全ホストで
  `VE34goal` を、三スロット `{BaseRunBase_up, BaseRunStep_up, Step_up}` ＋ regime 持続
  `{RunStepGuardJoint_up, StepRegPres_up}` から供給する。Isabelle `bgx_VE34_of_reg_modHEADEQ`
  は同じ三スロットを、run-base BASE スロット (`BaseRunBase_up`) だけを HEADEQ0 依存に、
  残り (`BaseRunStep_up`/`Step_up`/regime 持続) を HEADEQ0 非依存に埋める。よって
  **HEADEQ0 が消費されるのは run-base BASE スロット 1 箇所のみ**であり、本ファイルの中核は
  そのスロットを HEADEQ0 ＋ 2 つの閉形式から放出する `bgx_VE34_base_run0_mod` の移植。

- **中核（新規証明）**: `bgx_VE34_base_run0_mod_bg`（Isabelle `bgx_VE34_base_run0_mod` 106689）。
  clause-2 sharp form (`bgx_base_form_notleft`＋census が NOTLEFT0 を供給)、terminal-slice
  closed form (`bgx_Mp_form`)、run-base front 同定 (`bgx_front_run0`)、HEADEQ0 を、
  純 BT-代数で組み `VE34goal N` を放出する。`bpHeadT (Dprin v a) = a`（定義展開）と
  `addBT` を記号的に扱うだけの自己完結な組立（`VE3goal`＝成長分割＋`w ≠ 0_B`、
  `VE4goal`＝外側 context 方程式）。

- **run-base front 同定（新規証明）**: `bgx_front_run0_bg`（Isabelle `bgx_front_run0` 106648）。
  run-base BASE では前切片 `seg N 0 (FirstNodes N ! LastStep N - 1)` は `Pred N`。
  `FirstNodes N ! LastStep N = VEj1p N = Lng N - 1`（run-base ＋ BASE）から
  `seg N 0 (Lng N - 2)`、これが `dropLast N = Pred N`（`seg0_Pred_bg`）。

- **残差（名前付き Prop で露出、~1000 行の §7.4/§8 surgery ゆえ本セッション射程外）**:
  - `BgxBaseFormNotleft_bg`（clause-2 sharp value form＝`bgx_base_form_notleft`＋
    census `bgx_notleft_run0`。Adm0 recursion の `transC2` explicit 形）。
  - `BgxMpForm_bg`（terminal-slice closed form＝`bgx_Mp_form`。slice `Mp` が自身の Adm0
    recursion を走る閉形式）。
  - `BaseRunStep_up`／`Step_up`／`RunStepGuardJoint_up`／`StepRegPres_up`（統一 peel と
    共有。HEADEQ0 非依存。他ファイルの残差集合と同一）。
  数値検証: 深い run-base BASE ホスト `[(0,0),(1,1),(2,2),(2,2),(2,0)]` 上で
  両閉形式と HEADEQ0 の shape を `#guard` で確認済（転記正当性）。

- 訂正: なし（Isabelle 済補題の逐語移植、または名前付き Prop 骨格）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。`BgxVE34RedHE0_hq` を、run-base BASE スロットを
  HEADEQ0＋2 閉形式へ還元し、統一 peel に RIDE して残差束 modulo で緑放出。中核の
  BT-代数組立 `bgx_VE34_base_run0_mod_bg` と front 同定 `bgx_front_run0_bg` は無条件討伐。

- 依存 module: `8.2-condIIIV-headeq0`（`HEADEQ0All_hq`/`BgxVE34RedHE0_hq`）,
  `8.2-condIIIV-unified-peel`（`BaseRunBase_up`/`BaseRunStep_up`/`Step_up`/
  `RunStepGuardJoint_up`/`StepRegPres_up`/`VE34_backpeel_fin3_up`/`finRun_up_all`）を、
  `VE34goal`/`VE3goal`/`VE4goal`/`VE34goal_iff`/`VE34Reg4D`/`VEj1p`/`Trans`/`Pred`/`seg`/
  `Joints`/`Br`/`FirstNodes`/`LastStep`/`entry`/`Dprin`/`addBT`/`bpHeadT`/`BZero` を推移的に。

- Private suffix: `_bg`。
-/

namespace PSS

/-! ## 私的補助（suffix `_bg`） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開）。BT-代数組立の唯一の
`Dprin` 消去補題。 -/
private theorem bpHeadT_Dprin_bg (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- **`seg0_Pred_bg`**: `1 < Lng N` で前切片 `seg N 0 (Lng N - 2)` は `Pred N`（＝`dropLast N`）。
Isabelle `fpx_seg0_self` ＋ `m_7_4_seg_Pred_eq` の合成に対応する自己完結な同定。 -/
private theorem seg0_Pred_bg (N : PS) (hL : 1 < Lng N) : seg N 0 (Lng N - 2) = Pred N := by
  have hpred : Pred N = N.dropLast := by
    unfold Pred; rw [if_neg (by omega)]
  rw [hpred]
  apply List.ext_getElem
  · simp only [List.length_dropLast, seg, List.length_map, List.length_range']
    unfold Lng at hL ⊢; omega
  · intro i _ h2
    have h2' : i < N.length - 1 := by rwa [List.length_dropLast] at h2
    have hi : i < N.length := by omega
    simp only [seg, List.getElem_map, List.getElem_range', List.getElem_dropLast,
      entry, Nat.zero_add, Nat.one_mul]
    rw [List.getElem?_eq_getElem hi]
    simp

/-! ## run-base front 同定（Isabelle `bgx_front_run0`, 106648） -/

/-- **`bgx_front_run0_bg`**: run-base BASE ホストで前切片は `Pred N`。
`FirstNodes N ! LastStep N = VEj1p N`（run-base）＝`Lng N - 1`（BASE）より
`seg N 0 (Lng N - 2) = Pred N`。 -/
theorem bgx_front_run0_bg (N : PS) (hL : 1 < Lng N)
    (hbase : VEj1p N = Lng N - 1) (hrun : LastStep N = (Br N).length - 1) :
    seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) = Pred N := by
  have hfn : (FirstNodes N).getD (LastStep N) 0 = Lng N - 1 := by
    rw [hrun]; exact hbase
  rw [hfn]
  have he : Lng N - 1 - 1 = Lng N - 2 := by omega
  rw [he]
  exact seg0_Pred_bg N hL

/-! ## 中核: run-base BASE スロットの BT-代数組立（Isabelle `bgx_VE34_base_run0_mod`, 106689）

clause-2 sharp form ＋ Mp closed form ＋ front 同定 ＋ HEADEQ0 から `VE34goal N` を放出。
`w = Dprin (entry N 1 (Lng N - 1)) 0_B` を成長証人 `t₂` に据える純代数。 -/

/-- **`bgx_VE34_base_run0_mod_bg`** (Isabelle `bgx_VE34_base_run0_mod` 106689): run-base BASE
ホストにおける VE34goal の組立。

- `hform`  : `bgx_base_form_notleft` の結論（NOTLEFT0 は census `bgx_notleft_run0` が供給済）。
- `hMpF`   : `bgx_Mp_form` の結論（終切片 `Mp = seg N j₀ (Lng N - 1)` の Adm0 閉形式）。
- `hfront` : `bgx_front_run0` の結論（前切片 = `Pred N`）。
- `hHE`    : HEADEQ0（`bpHeadT (Trans (Pred Mp)) = bpHeadT (Trans (Pred N))`）。

VE3（成長分割、証人 `w`）と VE4（外側 context 方程式）を `bpHeadT (Dprin v a) = a` の
機械的展開で組む。 -/
theorem bgx_VE34_base_run0_mod_bg (N : PS)
    (hform : Trans N = Dprin (entry N 1 0 : ℕ∞)
       (addBT (bpHeadT (Trans (Pred N)))
         (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
           (addBT (bpHeadT (Trans (Pred N)))
             (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)))))
    (hMpF : Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))
       = Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
         (addBT (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))
           (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)))
    (hfront : seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1) = Pred N)
    (hHE : bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))
             = bpHeadT (Trans (Pred N))) :
    VE34goal N := by
  -- front slice の頭 = Pred N の頭
  have hF : bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))
              = bpHeadT (Trans (Pred N)) := by rw [hfront]
  -- terminal slice の頭 = t₂N +B w （Mp closed form ＋ HEADEQ0）
  have hMpHead : bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
      = addBT (bpHeadT (Trans (Pred N))) (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) := by
    rw [hMpF, bpHeadT_Dprin_bg, hHE]
  refine (VE34goal_iff N).mpr ⟨⟨Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero, ?_, ?_⟩, ?_⟩
  · -- VE3 成長分割: bpHeadT (Trans Mp) = F +B w
    rw [hMpHead, hF]
  · -- 証人 w ≠ 0_B
    simp [Dprin, BZero]
  · -- VE4 外側 context 方程式
    rw [VE4goal, hform, bpHeadT_Dprin_bg, hMpHead, hF]

/-! ## 閉形式の名前付き残差（Isabelle `bgx_base_form_notleft` ＋ census / `bgx_Mp_form`）

いずれも補正体制 `VE34Reg4D` の run-base BASE / BASE ホスト上で普遍的に量化する
（~1000 行の Adm0 sharp value forms ＋ strong-monomiality census が本体、本セッション射程外）。 -/

/-- **`BgxBaseFormNotleft_bg`**（Isabelle `bgx_base_form_notleft` 106329 ＋ census
`bgx_notleft_run0` 106972 が NOTLEFT0 を供給）: run-base BASE ホストでの `Trans N` の
clause-2 sharp value form。census が isleft 非発火を保証するので NL 仮定は不要。 -/
def BgxBaseFormNotleft_bg : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N = (Br N).length - 1 →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
       (addBT (bpHeadT (Trans (Pred N)))
         (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
           (addBT (bpHeadT (Trans (Pred N)))
             (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero))))

/-- **`BgxMpForm_bg`**（Isabelle `bgx_Mp_form` 106407）: BASE ホストでの終切片
`Mp = seg N j₀ (Lng N - 1)` の Adm0 閉形式。slice の最終列の親が列 0（joint、許容的）ゆえ
`Mp` は条件(I)/(III) ホストとして単一の葉 `D_{N₁,j₁} 0` を `Trans (Pred Mp)` の全 body に付す。 -/
def BgxMpForm_bg : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))
      = Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
        (addBT (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))
          (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero))

/-! ## run-base BASE スロット（`BaseRunBase_up`）を HEADEQ0 ＋ 2 閉形式から -/

/-- **`BaseRunBase_of_bg`**: 統一 peel の run-base BASE スロット `BaseRunBase_up` を、HEADEQ0
（`HEADEQ0All_hq`）と 2 つの閉形式 `{BgxBaseFormNotleft_bg, BgxMpForm_bg}` から放出する。
front 同定は無条件 `bgx_front_run0_bg`、組立は `bgx_VE34_base_run0_mod_bg`。 -/
theorem BaseRunBase_of_bg (hform : BgxBaseFormNotleft_bg) (hMp : BgxMpForm_bg)
    (hHE0 : HEADEQ0All_hq) : BaseRunBase_up := by
  intro N regD _hfin hbase hdeep hrun
  have hL : 1 < Lng N := by omega
  exact bgx_VE34_base_run0_mod_bg N
    (hform N regD hbase hdeep hrun)
    (hMp N regD hbase hdeep)
    (bgx_front_run0_bg N hL hbase hrun)
    (hHE0 N regD hbase hrun)

/-! ## capstone: `BgxVE34RedHE0_hq` を残差束 modulo で緑放出 -/

/-- **`BgxVE34RedHE0_of_bricks_bg`**（Isabelle `bgx_VE34_of_reg_modHEADEQ` 107245 の Lean 対応）:
残差 `BgxVE34RedHE0_hq`（＝`∀ M, VE34Reg4D M → HEADEQ0All_hq → VE34goal M`）を、
run-base BASE の 2 閉形式 `{BgxBaseFormNotleft_bg, BgxMpForm_bg}`（＝HEADEQ0 依存スロット）と、
統一 peel と共有の HEADEQ0 非依存残差 `{BaseRunStep_up, Step_up, RunStepGuardJoint_up,
StepRegPres_up}` から放出する。HEADEQ0 は run-base BASE スロットのみで消費される。 -/
theorem BgxVE34RedHE0_of_bricks_bg
    (hform : BgxBaseFormNotleft_bg) (hMp : BgxMpForm_bg)
    (hBaseR : BaseRunStep_up) (hStep : Step_up)
    (hRSgj : RunStepGuardJoint_up) (hStepReg : StepRegPres_up) :
    BgxVE34RedHE0_hq := by
  intro M hM hHE0
  exact VE34_backpeel_fin3_up
    (BaseRunBase_of_bg hform hMp hHE0)
    hBaseR hStep hRSgj hStepReg M hM (finRun_up_all M)

/-! ## 転記の数値検証（深い run-base BASE ホストで両閉形式と HEADEQ0 の shape を確認）

`hostBG = (0,0)(1,1)(2,2)(2,2)(2,0)` は補正体制 `VE34Reg4D` の **deep run-base BASE** ホスト
（`VEj1p = 4 = Lng - 1`、`TrMax + 2 = 3 < 5`、`LastStep = 1 = Br.length - 1`）。
`j₀ = 1`、`Trans (Pred hostBG)` の頭 `= [D_2 0, D_2 0]`。 -/

def hostBG : PS := [(0,0),(1,1),(2,2),(2,2),(2,0)]

-- deep run-base BASE VE34Reg4D ホストであること。
#guard decide (VE34Reg4D hostBG
  ∧ VEj1p hostBG = Lng hostBG - 1
  ∧ TrMax hostBG + 2 < Lng hostBG
  ∧ LastStep hostBG = (Br hostBG).length - 1) = true

-- `BgxBaseFormNotleft_bg` の shape が実 `Trans hostBG` に一致（clause-2 sharp form）。
-- （BT 等号は `BEq` で評価; `DecidableEq BT` 非合成のため `==`。）
#guard (Trans hostBG == Dprin (entry hostBG 1 0 : ℕ∞)
   (addBT (bpHeadT (Trans (Pred hostBG)))
     (Dprin (entry hostBG 1 ((Joints hostBG).getD ((Br hostBG).length - 1) 0) : ℕ∞)
       (addBT (bpHeadT (Trans (Pred hostBG)))
         (Dprin (entry hostBG 1 (Lng hostBG - 1) : ℕ∞) BZero))))) = true

-- `BgxMpForm_bg` の shape が実 `Trans Mp` に一致（terminal-slice closed form）。
#guard (Trans (seg hostBG ((Joints hostBG).getD ((Br hostBG).length - 1) 0) (Lng hostBG - 1))
  == Dprin (entry hostBG 1 ((Joints hostBG).getD ((Br hostBG).length - 1) 0) : ℕ∞)
    (addBT (bpHeadT (Trans (Pred (seg hostBG ((Joints hostBG).getD ((Br hostBG).length - 1) 0) (Lng hostBG - 1)))))
      (Dprin (entry hostBG 1 (Lng hostBG - 1) : ℕ∞) BZero))) = true

-- HEADEQ0 が hostBG で成立（bpHeadT(Trans(Pred Mp)) = bpHeadT(Trans(Pred hostBG)))。
#guard (bpHeadT (Trans (Pred (seg hostBG ((Joints hostBG).getD ((Br hostBG).length - 1) 0) (Lng hostBG - 1))))
  == bpHeadT (Trans (Pred hostBG))) = true

#print axioms bgx_front_run0_bg
#print axioms bgx_VE34_base_run0_mod_bg
#print axioms BaseRunBase_of_bg
#print axioms BgxVE34RedHE0_of_bricks_bg

end PSS
