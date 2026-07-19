import «8».«8.2-condIIIV-bgx-reduction»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — **BASE-run-step / STEP スロットの値証明**
  (`BaseRunStep_up` を幾何 3 Props へ組立、run-step の `Pred` 転送幾何を移植)

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、run-peel（`j₁ - TrMax M` に関する帰納法）の **BASE-run-step 脚**（Isabelle
  `bgx_VE34_base_step` 106565）と **STEP 脚**（Isabelle `tsx_VE34_step` 104300）。

- **背景**: `8.2-condIIIV-unified-peel` の統一 back-peel 強帰納法 `VE34_backpeel_fin3_up` は
  補正体制 `VE34Reg4D` の全ホストで `VE34goal` を三スロット
  `{BaseRunBase_up, BaseRunStep_up, Step_up}`（＋regime 持続 2 本）から供給する。
  run-base BASE スロット `BaseRunBase_up` は `8.2-condIIIV-bgx-reduction` が HEADEQ0 経由で
  討伐済み。本ファイルは残る `BaseRunStep_up`/`Step_up` を攻める。

- **`BaseRunStep_up` の組立**: `8.2-condIIIV-unified-peel` の `BaseRunStep_of_leaves_up`
  （`{PIN_bd, TSPIN_bd, VE3RunStep_bd}` から）と `8.2-condIIIV-ve-values` の
  `VE3RunStep_of_reductions_vv`（`VE3RunStep_bd` を keystone modulo で幾何 3 Props
  `{TerminalSliceReady_vv, FrontPredBaseTransport_vv, TermPredBaseTransport_vv}` へ還元）を
  合成し、`BaseRunStep_up` を **`{PIN_bd, TSPIN_bd}` ＋ 幾何 3 Props** から放出する
  （`BaseRunStep_of_geom_pv`）。これで統一 peel の run-step 脚の VE3 分は keystone analytic
  ＋成長輸送（ve-values で proven）に落ち、残る不確定性は純 `Pred`-segment 幾何に凝縮する。

- **run-step `Pred` 転送幾何の移植**（Isabelle `bfx_front_Pred_base` 104988 /
  `bfx_term_Pred_base` 105021 の下段）:
  1. `BrLen_Pred_base_pv`（Isabelle `bfx_BrLen_Pred_base` 104718）: BASE run-step ホストで
     最終枝は単項ゆえ `Pred N`（末尾列剥がし）は枝を 1 本落とす＝
     `(Br (Pred N)).length = (Br N).length - 1`。
  2. `FN_Pred_LS_base_pv`（Isabelle `bfx_FN_Pred_LS_base` 104970）: `FirstNodes (Pred N)` は
     `LastStep N` 位置で `FirstNodes N` に一致（枝数減少＋`FirstNodes_Pred_core`）。**無条件**。
  3. **JEQ の無条件討伐（descending 体制）** `jeqBaseD_pv`（Isabelle `bfx_JEQ` 104639 の逐語
     移植）: run の前枝 `J₁-1` と最終枝 `J₁` は joint を共有する。run 前枝頭一致
     （`run_prev_head_pv` ＝ `bfx_run_prev`、descending 弱降順 squeeze ＋ `LastStep` 枝所属
     `LastStep_mem_pv`）＋`FirstNodes` 単調 ＋ nextrel0 valley の部分区間制限 ＋ 親一意性
     （`parent_eq_of_nextR0`）で示す。これにより終切片転送 `TermPredBaseTransportD_pv`
     （Isabelle `bfx_term_Pred_base` 105021）を descending 体制で **無条件**に得る
     （`hqx_Pred_seg_hq`＋`seg_Pred_eq`＋`Joints_Pred_core`＋`BrLen_Pred_base_pv`＋JEQ で
     drop/butlast 不要の直接同定）。

- 🚨 **発見（field-level 再配線）**: ve-values の幾何 3 Props（`TerminalSliceReady_vv` 等）と
  `VE3RunStep_bd`/`PIN_bd`/`TSPIN_bd` はすべて **`VE34Reg4`（descending なし）** で量化されるが、
  それらの Isabelle 原型（`bux_*`/`bfx_*`）は `vg7x_reg4`＝`VE34Reg4D`（descending 込み）を要する。
  `BaseRunStep_up` 自体は `VE34Reg4D N` を仮説に持つのに、`BaseRunStep_of_leaves_up` →
  `VE3RunStep_of_reductions_vv` が descending を捨てて `VE34Reg4` 版 transports を要求する
  ＝**lossy reduction**。JEQ は descending なしでは偽になり得る（`RunSqueeze_vn` 反例で JEQ 自体は
  成立するが、これは D ホストである）ので、`VE34Reg4` 版 transports は討伐不能。よって
  `8.2-condIIIV-unified-peel` ヘッダが記した「中間補題群の descending 体制での引き直し」
  （field-level 再配線）が必須であり、本ファイルはそれを `BaseRunStep_of_geomD_pv` として供給する
  （descending 保持、終切片転送を内部討伐、残差 2 本へ削減）。

- **`Step_up` の組立**: `Step_of_legs_pv`（＝`8.2-condIIIV-unified-peel` の `Step_of_legs_up`）で
  STEP pointwise 残差 `{VE3Step, VE4Step}` に還元。VE3Step/VE4Step の値証明（Isabelle
  `bpx_VE34_step`/`tsx_VE34_step` の §7.4 head-shift readback surgery）は研究フロンティア級で
  本ファイル射程外（`8.2-condV-VE-step` / `8.2-condV-VE-close` の条件(V) 双子が閉じているのに
  対し、condIIIV は IH を消費しない pointwise 形なのが未達の核）。

- ⚠️ **未達（次のブリック）**: BASE-run-step の残差（descending 体制 = 正しい配線）は
  `{PIN_bd, TSPIN_bd, TerminalSliceReadyD_pv, FrontPredBaseTransportD_pv}` の **4 本**
  （終切片転送 = `jeqBaseD_pv` で **討伐済**）。`FrontPredBaseTransportD_pv` は
  `bfx_LastStep_Pred_base`（find? 最小性転送）、`TerminalSliceReadyD_pv` は非初期切片の
  reduced 性（§6.4/§7.4）を要し別ブリック。STEP は `{VE3Step, VE4Step}`。
  （`VE34Reg4` 版 `{JEQBase_pv, TermPredBaseTransport_vv}` は上記発見の通り討伐不能ゆえ
  `TermPredBaseTransport_of_jeq_pv` は modulo 版として保持のみ。）

- 訂正: なし（Isabelle 済補題の逐語移植、または名前付き Prop 骨格）。

- 依存 module: `8.2-condIIIV-bgx-reduction`（`BaseRunStep_up`/`Step_up`/`BaseRunStep_of_leaves_up`/
  `Step_of_legs_up`/`VE3RunStep_of_reductions_vv`/`TerminalSliceReady_vv`/
  `FrontPredBaseTransport_vv`/`TermPredBaseTransport_vv`/`PIN_bd`/`TSPIN_bd`/`hqx_Pred_seg_hq`/
  `VE34Reg4`/`VEj1p`/`LastStep`/`Br`/`Joints`/`FirstNodes`/`seg`/`Pred` を推移的に。
  §6/§7 の `length_Pred`/`seg_Pred_eq`/`Joints_Pred_core`/`FirstNodes_Pred_core`/
  `Br_Pred_core_nontrunk`/`wf21_Br_eq_seg`/`getLastD_eq_getD_last_68`/`length_seg`/
  `TrMax_bound`/`RTPS_TPS`、JEQ 用に `entry_FirstNodes_eq_component_mr`/`FirstNodes_Joints_mono`/
  `FirstNodes_TrMax_Joints`/`Joints_nextR_FirstNodes`/`parent_eq_of_nextR0`/`descendingB`/`cdomB`/
  `keystoneShapes_vv`/`growth_transport_vv` も推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  `BaseRunStep_up` を 2 経路で組立: (A) `BaseRunStep_of_geom_pv`＝`{PIN_bd, TSPIN_bd}`＋
  `VE34Reg4` 版幾何 3 Props（既存 chain 経由）; (B) **`BaseRunStep_of_geomD_pv`**＝descending
  保持で `{PIN_bd, TSPIN_bd, TerminalSliceReadyD_pv, FrontPredBaseTransportD_pv}` の 4 本
  （**終切片転送は `jeqBaseD_pv` で無条件討伐**）。run-step `Pred` 転送の枝数減少
  （`BrLen_Pred_base_pv`）・`FirstNodes` 転送（`FN_Pred_LS_base_pv`）・JEQ（`jeqBaseD_pv`）を
  無条件討伐、`Step_up` を STEP pointwise 残差へ還元。

- Private/public suffix: `_pv`。
-/

namespace PSS

/-! ## private 補助（run-step BASE の枝数減少）— Isabelle `bfx_BrLen_Pred_base`, 104718 -/

/-- **最終枝は単項**（BASE）: `Lng ((Br N).getLastD []) = 1`。`wf21_Br_eq_seg` で最終枝＝
`seg N (VEj1p N) (Lng N - 1)`、BASE で `VEj1p N = Lng N - 1` ゆえ長さ 1
（`8.2-condIIIV-ve-next` `lastBr_singleton_vn` の再掲）。 -/
private theorem lastBr_singleton_pv (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hbase : VEj1p N = Lng N - 1) : Lng ((Br N).getLastD []) = 1 := by
  have hfneq : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
    simpa only [VEj1p] using hbase
  rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, hfneq,
    length_seg]
  omega

/-- **枝数減少**（Isabelle `bfx_BrLen_Pred_base` 104718）: BASE run ホストで
`(Br (Pred N)).length = (Br N).length - 1`（`8.2-condIIIV-ve-next` `BrLen_Pred_base_vn` の再掲）。 -/
theorem BrLen_Pred_base_pv (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hL1 : 1 < Lng N) (htrne : TrMax N ≠ Lng N - 1) (hbase : VEj1p N = Lng N - 1) :
    (Br (Pred N)).length = (Br N).length - 1 := by
  rw [Br_Pred_core_nontrunk N hM hL1 htrne,
    if_pos (show Lng ((Br N).getLastD []) ≤ 1 by
      rw [lastBr_singleton_pv N hM hBrne hbase])]
  simp

/-! ## `FirstNodes` の `Pred` 転送（Isabelle `bfx_FN_Pred_LS_base`, 104970）— 無条件 -/

/-- **`FN_Pred_LS_base_pv`** (Isabelle `bfx_FN_Pred_LS_base` 104970): run-step BASE ホストで
`FirstNodes (Pred N)` は `LastStep N` 位置で `FirstNodes N` に一致する。枝数減少
（`BrLen_Pred_base_pv`）で `LastStep N < (Br (Pred N)).length` を得て `FirstNodes_Pred_core` を
適用する。**無条件**（keystone/幾何残差非依存）。 -/
theorem FN_Pred_LS_base_pv (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hL1 : 1 < Lng N) (htrne : TrMax N ≠ Lng N - 1) (hbase : VEj1p N = Lng N - 1)
    (hrun : LastStep N < (Br N).length - 1) :
    (FirstNodes (Pred N)).getD (LastStep N) 0 = (FirstNodes N).getD (LastStep N) 0 := by
  have hBrlen : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_pv N hM hBrne hL1 htrne hbase
  have hLSlt' : LastStep N < (Br (Pred N)).length := by rw [hBrlen]; omega
  exact FirstNodes_Pred_core N hM hL1 htrne (LastStep N) hLSlt'

/-! ## 終切片の `Pred` 転送を JEQ 一本 modulo で（Isabelle `bfx_term_Pred_base`, 105021）

Isabelle `bfx_term_Pred_base` は `bfx_Joints_Pred_last`（＝JEQ ＋ `Joints_Pred_core`）＋
drop/butlast の可換性で証明する。Lean は `hqx_Pred_seg_hq`（`Pred (seg N a (Lng N-1)) =
seg N a (Lng N-2)`、`8.2-condIIIV-headeq0` で proven）＋`seg_Pred_eq`（`seg (Pred N) a b =
seg N a b`、`b < Lng N-1`）で drop/butlast を経由せず直接同定する。残る不確定性は run 枝の
joint 共有 `JEQBase_pv` 一本に凝縮する。 -/

/-- **`JEQBase_pv`**（Isabelle `bfx_JEQ` 104639 の結論）: run-step BASE ホストで run の前枝
（`J₁-1`）と最終枝（`J₁`）は joint を共有する。反例 `witCexRS`（`8.2-condIIIV-runsqueeze`）でも
成立する真の run-branch 幾何（refuted の `RunSqueeze_vn` の破れは第三連言＝BASE 単一列幾何で
あって JEQ ではない）。 -/
def JEQBase_pv : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    (Joints N).getD ((Br N).length - 2) 0 = (Joints N).getD ((Br N).length - 1) 0

/-- **`TermPredBaseTransport_of_jeq_pv`**（Isabelle `bfx_term_Pred_base` 105021）: 終切片転送
残差 `TermPredBaseTransport_vv`（`8.2-condIIIV-ve-values`）を JEQ 一本 `JEQBase_pv` から放出する。 -/
theorem TermPredBaseTransport_of_jeq_pv (hjeq : JEQBase_pv) : TermPredBaseTransport_vv := by
  intro N reg hbase hdeep hrun
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hBrlen : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_pv N hM hBrne hL1 htrne hbase
  have hBrlen1 : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
  have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by rw [hBrlen]; omega
  -- `j₀ < Lng N - 1`（joint 非許容 ＋ deep）
  have hj0lt1 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  -- `j₀P = j₀`（`Joints_Pred_core` ＋ JEQ）
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hBrlen1, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 2) hJpP]
    exact hjeq N ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ hbase hdeep hrun
  -- `Lng (Pred N) - 1 = Lng N - 2`
  have he : Lng (Pred N) - 1 = Lng N - 2 := by omega
  -- 組立
  rw [hjointP, he, hqx_Pred_seg_hq N ((Joints N).getD ((Br N).length - 1) 0) hL1 hj0lt1]
  exact seg_Pred_eq N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) hL1 (by omega) (by omega)

/-! ## JEQ の無条件討伐（descending 体制 `VE34Reg4D` 上、Isabelle `bfx_JEQ`, 104639）

`JEQBase_pv` の仮説は `VE34Reg4`（descending なし）だが、Isabelle `bfx_JEQ` は run 枝頭の
弱降順 squeeze を使うため descending が必須。よって JEQ は **`VE34Reg4D`（descending 込み）**
の上でのみ真であり得る（`VE34Reg4` 版は non-descending ホストで偽になり得る）。ここでは
descending 版 `JEQBaseD_pv` を無条件討伐する。これは `8.2-condIIIV-unified-peel` ヘッダが
「中間補題群の descending 体制での引き直しが要る」と記した field-level 再配線の中核である。 -/

/-- `descending (Br N)` の row-0 弱降順成分（`8.2-condIIIV-headeq0-close` `descendingB_row0_h0`
の再掲）: `J₀ ≤ J₁ < Q.length` で `(Q_J₁)₀,₀ ≤ (Q_J₀)₀,₀`。 -/
private theorem descendingB_row0_pv (Q : List PS) (h : descendingB Q = true)
    (J₀ J₁ : ℕ) (hle : J₀ ≤ J₁) (hlt : J₁ < Q.length) :
    entry (Q.getD J₁ []) 0 0 ≤ entry (Q.getD J₀ []) 0 0 := by
  simp only [descendingB, List.all_eq_true, List.mem_range] at h
  have hc := h J₁ hlt J₀ (by omega)
  simp only [cdomB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1

/-- 最終枝頭のガード `gtN`（Isabelle `bfx_gtN` 104527）: `entry (Br N ! J₁) 1 0 <
entry (Br N ! J₁) 0 0`。体制ガード `hguard`（`= entry N 1 (VEj1p N) < entry N 0 (VEj1p N)`）を
枝頭 `= entry N .. (FirstNodes N ! J₁)` に読み替える。 -/
private theorem gtN_pv (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N)) :
    entry ((Br N).getD ((Br N).length - 1) []) 1 0
      < entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  have hJ1 : (Br N).length - 1 < (Br N).length := by
    have := List.length_pos_of_ne_nil hBrne; omega
  have h0 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1
  have h1 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1
  rw [← h0, ← h1]
  simpa only [VEj1p] using hguard

/-- `LastStep N` の枝所属（Isabelle `bfx_run_prev` の `LSmem`）: 非対角ガード `gtN` の下で
`LastStep N` は `S`-述語（枝頭 row-0 が最終枝と一致 ∧ row-1 < row-0）を満たす。`find?` の
既定値・`some` 双方で `gtN` から従う。 -/
private theorem LastStep_mem_pv (N : PS) (hBrne : Br N ≠ [])
    (hgtN : entry ((Br N).getD ((Br N).length - 1) []) 1 0
          < entry ((Br N).getD ((Br N).length - 1) []) 0 0) :
    entry ((Br N).getD ((Br N).length - 1) []) 0 0
      = entry ((Br N).getD (LastStep N) []) 0 0
    ∧ entry ((Br N).getD (LastStep N) []) 1 0
      < entry ((Br N).getD (LastStep N) []) 0 0 := by
  have hLpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br N).length ≠ 0 := by omega
  have hnd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
           ≠ entry ((Br N).getD ((Br N).length - 1) []) 1 0 := by omega
  have hLSval : LastStep N
      = ((List.range (Br N).length).find? (fun J =>
          decide (entry ((Br N).getD ((Br N).length - 1) []) 0 0 = entry ((Br N).getD J []) 0 0) &&
          decide (entry ((Br N).getD J []) 1 0 < entry ((Br N).getD J []) 0 0))).getD
            ((Br N).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval]
  cases hfind : (List.range (Br N).length).find? (fun J =>
      decide (entry ((Br N).getD ((Br N).length - 1) []) 0 0 = entry ((Br N).getD J []) 0 0) &&
      decide (entry ((Br N).getD J []) 1 0 < entry ((Br N).getD J []) 0 0)) with
  | none =>
      rw [Option.getD_none]
      exact ⟨rfl, hgtN⟩
  | some c =>
      rw [Option.getD_some]
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp

/-- run 前枝頭 = 最終枝頭（Isabelle `bfx_run_prev(1)`, 104581）: descending の弱降順で
`LastStep ≤ J₁-1 ≤ J₁` の枝頭 row-0 を squeeze し、`LastStep` 所属で最終枝頭に一致させる。 -/
private theorem run_prev_head_pv (N : PS) (hBrne : Br N ≠ [])
    (hdesc : descendingB (Br N) = true)
    (hgtN : entry ((Br N).getD ((Br N).length - 1) []) 1 0
          < entry ((Br N).getD ((Br N).length - 1) []) 0 0)
    (hrun : LastStep N < (Br N).length - 1) :
    entry ((Br N).getD ((Br N).length - 2) []) 0 0
      = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  obtain ⟨hLS0, _hLS1⟩ := LastStep_mem_pv N hBrne hgtN
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  have hJmlt : (Br N).length - 2 < (Br N).length := by omega
  have d2a : entry ((Br N).getD ((Br N).length - 1) []) 0 0
           ≤ entry ((Br N).getD ((Br N).length - 2) []) 0 0 :=
    descendingB_row0_pv (Br N) hdesc ((Br N).length - 2) ((Br N).length - 1) (by omega) hJ1lt
  have d1a : entry ((Br N).getD ((Br N).length - 2) []) 0 0
           ≤ entry ((Br N).getD (LastStep N) []) 0 0 :=
    descendingB_row0_pv (Br N) hdesc (LastStep N) ((Br N).length - 2) (by omega) hJmlt
  omega

/-- **`JEQBaseD_pv`**（Isabelle `bfx_JEQ` 104639、descending 版）: descending 体制で run の
前枝と最終枝は joint を共有する。 -/
def JEQBaseD_pv : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    (Joints N).getD ((Br N).length - 2) 0 = (Joints N).getD ((Br N).length - 1) 0

/-- **`jeqBaseD_pv`**（Isabelle `bfx_JEQ` 104639 の逐語移植、descending 体制）: run の前枝
`J₁-1` の nextR 親が最終枝 `J₁` の joint に一致することを、run 前枝頭一致 ＋ `FirstNodes` 単調
＋ nextrel0 valley の部分区間制限 ＋ 親一意性で示す。 -/
theorem jeqBaseD_pv : JEQBaseD_pv := by
  intro N regD hbase hdeep hrun
  obtain ⟨reg4, hdesc⟩ := regD
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := reg4
  have hM : TPS N := RTPS_TPS N hR
  have hJ1lt : (Br N).length - 1 < (Br N).length := by omega
  have hJmlt : (Br N).length - 2 < (Br N).length := by omega
  have hJmltJ1 : (Br N).length - 2 < (Br N).length - 1 := by omega
  have hgtN := gtN_pv N hM hBrne hguard
  have h0eq := run_prev_head_pv N hBrne hdesc hgtN hrun
  -- nextR 親関係（最終枝 J₁ と前枝 Jm）
  have nx1 := Joints_nextR_FirstNodes N ((Br N).length - 1) hM hmono hJ1lt
  have nxm0 := Joints_nextR_FirstNodes N ((Br N).length - 2) hM hmono hJmlt
  have hn1 : nextrel0 N ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 1) 0) = true := by simpa [nextR] using nx1
  have hnm0 : nextrel0 N ((Joints N).getD ((Br N).length - 2) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true := by simpa [nextR] using nxm0
  -- J₁ の nextrel0 分解
  have hn1' := hn1
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn1'
  obtain ⟨⟨⟨⟨n1, _nB⟩, _nC⟩, n4⟩, hvalley⟩ := hn1'
  -- Jm の nextrel0 分解（`FirstNodes!Jm < Lng` を得る）
  have hnm0' := hnm0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnm0'
  obtain ⟨⟨⟨⟨_m1, c2⟩, _mC⟩, _m4⟩, _mvalley⟩ := hnm0'
  -- 枝頭 = FirstNodes 成分
  have e0m := entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 0 hM hJmlt
  have e01 := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1lt
  have eqFN : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0)
            = entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0) := by
    rw [e0m, e01]; exact h0eq
  -- FirstNodes 単調 / TrMax 幾何
  have hFNmono := FirstNodes_Joints_mono N ((Br N).length - 2) ((Br N).length - 1)
    hM hmono hJmltJ1 hJ1lt
  have hFNle : (FirstNodes N).getD ((Br N).length - 2) 0
             ≤ (FirstNodes N).getD ((Br N).length - 1) 0 := hFNmono.1
  have hgeom := FirstNodes_TrMax_Joints N ((Br N).length - 2) hM hmono hJmlt
  -- nextrel0 N (Joints!J1) (FirstNodes!Jm) を構築
  have c3 : (Joints N).getD ((Br N).length - 1) 0 < (FirstNodes N).getD ((Br N).length - 2) 0 := by
    have := hgeom.2; omega
  have c4 : entry N 0 ((Joints N).getD ((Br N).length - 1) 0)
          < entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) := by
    rw [eqFN]; exact n4
  have nxm' : nextrel0 N ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨n1, ?_⟩, c3⟩, c4⟩, ?_⟩
    · exact c2
    · -- valley: Jm の谷条件は J₁ の谷条件（`hvalley`）と `entry00(FN!Jm)=entry00(FN!J1)`
      -- （`eqFN`）で一致。範囲は `FN!Jm ≤ FN!J1`（`hFNle`）で J₁ の range に埋め込む。
      rw [List.all_eq_true]
      intro j hj
      have hjlt : j < (FirstNodes N).getD ((Br N).length - 2) 0 := by
        simpa using hj
      have hjmem : j ∈ List.range ((FirstNodes N).getD ((Br N).length - 1) 0) :=
        List.mem_range.mpr (by omega)
      have hval := (List.all_eq_true.mp hvalley) j hjmem
      rw [eqFN]
      exact hval
  -- nextR に戻して親一意性
  have nxmB : nextR N 0 ((Joints N).getD ((Br N).length - 1) 0)
      ((FirstNodes N).getD ((Br N).length - 2) 0) = true := by simpa [nextR] using nxm'
  have p1 := parent_eq_of_nextR0 N _ _ nxmB
  have p0 := parent_eq_of_nextR0 N _ _ nxm0
  rw [← p0, p1]

/-- **`TermPredBaseTransportD_pv`**（Isabelle `bfx_term_Pred_base` 105021、descending 版）:
`TermPredBaseTransport_vv` の結論を descending 体制で **無条件**に与える（JEQ を
`jeqBaseD_pv` で内部供給）。 -/
theorem TermPredBaseTransportD_pv (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (hrun : LastStep N < (Br N).length - 1) :
    seg (Pred N) ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0) (Lng (Pred N) - 1)
      = Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) := by
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩, _hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hBrlen : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_pv N hM hBrne hL1 htrne hbase
  have hBrlen1 : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
  have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by rw [hBrlen]; omega
  have hj0lt1 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  have hjointP : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hBrlen1, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 2) hJpP]
    exact jeqBaseD_pv N ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩, _hdesc⟩ hbase hdeep hrun
  have he : Lng (Pred N) - 1 = Lng N - 2 := by omega
  rw [hjointP, he, hqx_Pred_seg_hq N ((Joints N).getD ((Br N).length - 1) 0) hL1 hj0lt1]
  exact seg_Pred_eq N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) hL1 (by omega) (by omega)

/-! ## descending 体制での BASE-run-step 再配線（field-level re-drawing）

`8.2-condIIIV-unified-peel` ヘッダが「中間補題群の descending 体制での引き直しが要る」と記した
再配線を供給する。`BaseRunStep_up` は仮説に `VE34Reg4D N`（descending 込み）を持つが、
既存の `BaseRunStep_of_leaves_up` → `VE3RunStep_of_reductions_vv` は descending を捨てて
`VE34Reg4` 版の transports を要求する（`VE34Reg4` 版 transports は non-descending ホストで
偽になり得るため討伐不能）。ここでは descending を保持して VE3 run-step を組み、終切片転送
`TermPredBaseTransportD_pv` を **内部で無条件討伐**する。残る D 版 transports は
`{TerminalSliceReadyD_pv, FrontPredBaseTransportD_pv}` の 2 本（Isabelle `bux_terminal_slice_ready`
＝非初期切片の reduced 性、`bfx_front_Pred_base` ＝`bfx_LastStep_Pred_base` の find? 最小性転送）。 -/

/-- `bpHeadT (Dprin a b) = b`（`8.2-condIIIV-ve-values` `bpHeadT_Dprin_vv` の再掲、private ゆえ）。 -/
private theorem bpHeadT_Dprin_pv (a : ℕ∞) (b : BT) : bpHeadT (Dprin a b) = b := rfl

/-- `addBT` の結合律（`8.2-condIIIV-ve-values` `addBT_assoc_vv` の再掲、private ゆえ）。 -/
private theorem addBT_assoc_pv (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  obtain ⟨as⟩ := a; obtain ⟨bs⟩ := b; obtain ⟨cs⟩ := c
  simp [addBT, List.append_assoc]

/-- **`TerminalSliceReadyD_pv`**（`TerminalSliceReady_vv` の descending 版）: 終切片が
`keystone` を適用できる状態にあること（Isabelle `bux_terminal_slice_ready` 99317、
非初期切片の reduced 性を要する残差）。 -/
def TerminalSliceReadyD_pv : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    RTPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
    monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true ∧
    Br (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ [] ∧
    1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) - 1

/-- **`FrontPredBaseTransportD_pv`**（`FrontPredBaseTransport_vv` の descending 版）: 前置切片
`Pred` 転送（Isabelle `bfx_front_Pred_base` 104988、`bfx_LastStep_Pred_base` ＝find? 最小性
転送 modulo）。 -/
def FrontPredBaseTransportD_pv : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    seg (Pred N) 0 ((FirstNodes (Pred N)).getD (LastStep (Pred N)) 0 - 1)
      = seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)

/-- **`VE3RunStepD_pv`**（`VE3RunStep_bd` の descending 版）: run-step BASE で IH `VE3goal (Pred N)`
を成長輸送して `VE3goal N` を得る。 -/
def VE3RunStepD_pv : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 → VE3goal (Pred N) → VE3goal N

/-- **`VE3RunStepD_of_reductions_pv`**（Isabelle `bfx_VE3_base_step` 105113、descending 版）:
VE3 run-step を、keystone 二形（`keystoneShapes_vv`, proven）＋成長輸送（`growth_transport_vv`,
proven）＋ **無条件終切片転送 `TermPredBaseTransportD_pv`（本ファイルで proven）** ＋ 前置転送
`FrontPredBaseTransportD_pv` ＋ 終切片 ready `TerminalSliceReadyD_pv` から放出する。
`8.2-condIIIV-ve-values` `VE3RunStep_of_reductions_vv` の descending 版（`hterm` を内部討伐）。 -/
theorem VE3RunStepD_of_reductions_pv
    (hreadyD : TerminalSliceReadyD_pv) (hfrontD : FrontPredBaseTransportD_pv) :
    VE3RunStepD_pv := by
  intro N reg hbase hdeep hrun ihP
  obtain ⟨t2P, ihEq, ht2Pne⟩ := ihP
  have hfr := hfrontD N reg hbase hdeep hrun
  have htr := TermPredBaseTransportD_pv N reg hbase hdeep hrun
  rw [htr, hfr] at ihEq
  obtain ⟨hRr, hmr, hbrr, hgtr⟩ := hreadyD N reg hbase hdeep hrun
  rcases keystoneShapes_vv
      (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) hRr hmr hbrr hgtr with
    ⟨c, w, x, hTP, hTM⟩ | ⟨c, w, x, y, hTP, hTM⟩
  · have hc : c = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have := ihEq
      rw [hTP, bpHeadT_Dprin_pv] at this
      exact this
    refine ⟨addBT t2P (Dprin w x), ?_, ?_⟩
    · rw [hTM, bpHeadT_Dprin_pv, hc, addBT_assoc_pv]
    · obtain ⟨ds⟩ := t2P
      intro h
      have hnil : ds ++ [BP.db w x] = [] := BT.trm.inj h
      simp at hnil
  · have hEq : addBT c (Dprin w x)
        = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have := ihEq
      rw [hTP, bpHeadT_Dprin_pv] at this
      exact this
    obtain ⟨t2, ht2Eq, ht2ne⟩ := growth_transport_vv c
      (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P x y w hEq ht2Pne
    refine ⟨t2, ?_, ht2ne⟩
    rw [hTM, bpHeadT_Dprin_pv, ht2Eq]

/-- **`BaseRunStep_of_geomD_pv`**: descending を保持した BASE-run-step 組立。`BaseRunStep_up`
（仮説 `VE34Reg4D N`）を、`{PIN_bd, TSPIN_bd, TerminalSliceReadyD_pv, FrontPredBaseTransportD_pv}`
から放出する。**終切片転送はもはや残差ではなく、`jeqBaseD_pv` 経由で内部討伐される**。
`8.2-condIIIV-ve-values` `VE3RunStep_of_reductions_vv` が `VE34Reg4` 版 transports 3 本を要した
のに対し、本版は descending を活かして 1 本（終切片）を消し、残差を 2 本に削減する。 -/
theorem BaseRunStep_of_geomD_pv (hPIN : PIN_bd) (hTSPIN : TSPIN_bd)
    (hreadyD : TerminalSliceReadyD_pv) (hfrontD : FrontPredBaseTransportD_pv) :
    BaseRunStep_up := by
  intro N regD _hfin hbase hdeep hrunstep _regDP ihP
  have reg4 : VE34Reg4 N := VE34Reg4D_VE34Reg4 N regD
  have hVE4 : VE4goal N := VE4BaseDeep_of_pin_tspin hPIN hTSPIN N reg4 hbase hdeep
  have hVE3P : VE3goal (Pred N) := ((VE34goal_iff (Pred N)).mp ihP).1
  have hVE3 : VE3goal N :=
    VE3RunStepD_of_reductions_pv hreadyD hfrontD N regD hbase hdeep hrunstep hVE3P
  exact (VE34goal_iff N).mpr ⟨hVE3, hVE4⟩

/-! ## `BaseRunStep_up` の組立（Isabelle `bgx_VE34_base_step`, 106565） -/

/-- **`BaseRunStep_of_geom_pv`**: 統一 peel の BASE-run-step スロット `BaseRunStep_up` を、
`{PIN_bd, TSPIN_bd}` ＋ ve-values の幾何 3 Props `{TerminalSliceReady_vv,
FrontPredBaseTransport_vv, TermPredBaseTransport_vv}` から放出する。`VE3RunStep_bd` は
`VE3RunStep_of_reductions_vv`（keystone modulo）で幾何 3 Props に還元済み、VE4 は
`VE4BaseDeep_of_pin_tspin`（`BaseRunStep_of_leaves_up` 内）で供給。 -/
theorem BaseRunStep_of_geom_pv (hPIN : PIN_bd) (hTSPIN : TSPIN_bd)
    (hready : TerminalSliceReady_vv) (hfront : FrontPredBaseTransport_vv)
    (hterm : TermPredBaseTransport_vv) : BaseRunStep_up :=
  BaseRunStep_of_leaves_up hPIN hTSPIN
    (VE3RunStep_of_reductions_vv hready hfront hterm)

/-- **`BaseRunStep_of_geom_jeq_pv`**: 上の `TermPredBaseTransport_vv` を JEQ 一本
`JEQBase_pv`（`TermPredBaseTransport_of_jeq_pv` 経由）へ差し替えた版。BASE-run-step 脚は
`{PIN_bd, TSPIN_bd, TerminalSliceReady_vv, FrontPredBaseTransport_vv, JEQBase_pv}` から放出。 -/
theorem BaseRunStep_of_geom_jeq_pv (hPIN : PIN_bd) (hTSPIN : TSPIN_bd)
    (hready : TerminalSliceReady_vv) (hfront : FrontPredBaseTransport_vv)
    (hjeq : JEQBase_pv) : BaseRunStep_up :=
  BaseRunStep_of_geom_pv hPIN hTSPIN hready hfront (TermPredBaseTransport_of_jeq_pv hjeq)

/-! ## `Step_up` の組立（Isabelle `tsx_VE34_step`, 104300） -/

/-- **`Step_of_legs_pv`**（＝`8.2-condIIIV-unified-peel` `Step_of_legs_up`）: 統一 peel の STEP
スロット `Step_up` を STEP pointwise 残差 `{VE3Step, VE4Step}` から放出する（IH 非消費）。
VE3Step/VE4Step の値証明は §7.4 head-shift readback surgery で本ファイル射程外。 -/
theorem Step_of_legs_pv (hV3s : VE3Step) (hV4s : VE4Step) : Step_up :=
  Step_of_legs_up hV3s hV4s

/-! ## 転記の数値検証

`witRS_pv = (0,0)(1,1)(2,2)(2,0)(3,1)(2,0)`（runsqueeze の反例 `witCexRS` と同形）は
補正体制 `VE34Reg4D`（従って `VE34Reg4`）の **deep run-step BASE** ホスト
（`VEj1p = 4 = Lng - 1`、`TrMax + 2 = 4 < 5`、`LastStep = 0 < 1 = Br.length - 1`）。
枝長は `[2, 1]`。JEQ（`Joints ! (len-2) = Joints ! (len-1)`）は**成立**する（真の run-branch
幾何）が、BASE 単一列幾何は破れる（＝`RunSqueeze_vn` refuted の根拠は JEQ ではない）。 -/

def witRS_pv : PS := [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]

-- witRS_pv は deep run-step BASE の `VE34Reg4` ホスト（`TermPredBaseTransport_vv` 量化域が非空）。
#guard decide (VE34Reg4 witRS_pv
  ∧ VEj1p witRS_pv = Lng witRS_pv - 1
  ∧ TrMax witRS_pv + 2 < Lng witRS_pv
  ∧ LastStep witRS_pv < (Br witRS_pv).length - 1) = true

-- witRS_pv は descending 体制 `VE34Reg4D`（`jeqBaseD_pv` の量化域）に属す。
#guard decide (VE34Reg4D witRS_pv ∧ descendingB (Br witRS_pv) = true) = true

-- JEQ（run 枝の joint 共有）は witRS_pv で**成立**（`jeqBaseD_pv` の量化本体が真）。
#guard decide ((Joints witRS_pv).getD ((Br witRS_pv).length - 2) 0
  = (Joints witRS_pv).getD ((Br witRS_pv).length - 1) 0) = true

-- 枝数減少: `(Br (Pred witRS_pv)).length = (Br witRS_pv).length - 1`（`BrLen_Pred_base_pv`）。
#guard decide ((Br (Pred witRS_pv)).length = (Br witRS_pv).length - 1) = true

-- `FirstNodes` 転送: `FirstNodes (Pred witRS_pv) ! LastStep = FirstNodes witRS_pv ! LastStep`。
#guard decide ((FirstNodes (Pred witRS_pv)).getD (LastStep witRS_pv) 0
  = (FirstNodes witRS_pv).getD (LastStep witRS_pv) 0) = true

#print axioms BrLen_Pred_base_pv
#print axioms FN_Pred_LS_base_pv
#print axioms TermPredBaseTransport_of_jeq_pv
#print axioms jeqBaseD_pv
#print axioms TermPredBaseTransportD_pv
#print axioms VE3RunStepD_of_reductions_pv
#print axioms BaseRunStep_of_geomD_pv
#print axioms BaseRunStep_of_geom_pv
#print axioms BaseRunStep_of_geom_jeq_pv
#print axioms Step_of_legs_pv

end PSS
