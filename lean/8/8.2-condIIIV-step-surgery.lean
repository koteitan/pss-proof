import «8».«8.2-condIIIV-unified-peel»
import «8».«8.2-condIIIV-ve34-step»

/-!
# §8.2 条件(II)/(IV) VE34 後ろ剥がしの STEP スロット surgery（`tsx_`/`bpx_VE34_step` 移植）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）の **帰納ステップ**（最終列が現最終枝の中に
  新しい枝を開く場合 `VEj1p N < Lng N - 1`）。
- **戦略（`8.2-condIIIV-unified-peel` の `Step_of_legs_up` を置換）**: 統一 back-peel 強帰納法
  `VE34_backpeel_fin3_up` の STEP スロット `Step_up` は **IH `VE34goal (Pred N)` を持つ**。
  従来の `Step_of_legs_up` は IH を捨てて pointwise 残差 `{VE3Step, VE4Step}` を消費していたが、
  これらは pointwise（IH 非可用）ゆえ単独では閉じられない。本ファイルは Isabelle が
  実際に STEP を閉じた経路 `tsx_VE34_step` = `bpx_VE34_step_modTSPIN` + `tsx_TSPIN`
  （`isabelle/layerB/pss_wip.thy` 103023–104316、**sorry 0 で完全証明**）を移植し、
  IH を消費する `Step_up` を surgery 残差束から供給する。これで pointwise `{VE3Step, VE4Step}`
  は **不要** になり、STEP は Isabelle が実際に carry する残差へ置き換わる。
- **検証結果（mission の問い「bgx は tsx を回避するか？」への回答）**: **回避しない**。
  `bgx_VE34_of_reg_modNOTLEFT_HEADEQ` (106728) の `bfx_VE34_backpeel_fin3` dispatcher の
  STEP 脚 `ST` は `by (rule tsx_VE34_step[OF r l rP ih f])` で、bgx recursion は STEP を
  そのまま tsx へ委譲する。従って STEP surgery の本体は `tsx_`/`bpx_` であり、その単一の
  深い残差は `TSPIN`（非許容 joint での Mark-surgery naturality 頭輸送方程式）である。
- **移植の分解**（Isabelle 構造 1:1）:
  - `stepVE34_of_pieces_ss` ← `bpx_VE34_step_modTSPIN` (103234): pinned 形 + VE3 成長 + `TSPIN`
    から `VE34goal N`。純 `BT` 代数＋∃-シャッフル（緑）。
  - `StepVE3Growth_of_reductions_ss` ← `bpx_VE3_step` (103023): IH の VE3 を keystone 二形
    （`keystoneShapes_vv`, 移植済）＋成長輸送（`growth_transport_vv`, 移植済）で `VE3goal N` に。
    Isabelle `bfx_VE3_base_step` の run-step BASE 版（`VE3RunStep_of_reductions_vv`）の STEP 版
    ＝逐語同型。純 Pred/segment 幾何のみ残差（`{StepTerminalReady_ss, StepFrontPred_ss,
    StepTermPred_ss}`, BASE 版 `{TerminalSliceReady_vv, FrontPred/TermPredBaseTransport_vv}` と同種）。
  - `StepPinnedForm_of_ih_ss` ← `bpx_step_form_pinned` (103085): IH の VE4 を keystone（`keystone`,
    移植済）clause 3/4 に照合して pinned 形 `∃a, Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'} a)` を得る。
    `Trans_principal_head`（移植済）＋ addBT 末尾分割代数（本ファイルで無条件）＋純 Pred index
    残差 `StepPredIndex_ss`。
  - `TSPINStep_ss` ← `tsx_TSPIN` (104267): 単一の深い頭輸送方程式（§7.4 Mark-surgery naturality）。
    **これが STEP の唯一の研究フロンティア残差**。Isabelle では `tsx_assembly` (104073) で閉じるが、
    それは §7.4 共有 scb-context 頭シフト readback surgery（`m_7_4_Trans_Mark_Pred`＋
    `m_7_4_Mark_Trans_repr`, transC1/transC2 の parent-slice 転送）を要し本ファイル射程外。
- ⚠️ **REFUTED（再挑戦するな）**: 素朴な prefix-append 帰納（`bpHeadT (Trans (terminal (Pred N)))`
  が `bpHeadT (Trans (terminal N))` の PREFIX）は偽（python/ve34_deep2.py 0/5）。終切片は延長でなく
  再構成される。真の放出は IH からの keystone 二形経由（本ファイル）。
- 訂正: なし（Isabelle 側で sorry 0 で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- 依存 module: `8.2-condIIIV-unified-peel`（`Step_up`/`VE34Reg4D`/`VE34Reg4D_VE34Reg4`/
  `VE34_backpeel_fin3_up`/`BaseRunBase_of_leaves_up`/`BaseRunStep_of_leaves_up`/
  `RunStepGuardJoint_up`/`StepRegPres_up`/`PIN_bd`/`TSPIN_bd`/`VE3RunBase_bd`/`VE3RunStep_bd`/
  `finRun_up_all`/`keystoneShapes_vv`/`growth_transport_vv`/`keystone`/`Trans_principal_head`/
  `VE34goal`/`VE34goal_iff`/`VE3goal`/`VE4goal`/`VEj1p`）＋`8.2-condIIIV-ve34-step`
  （`veStep34Geom_vs3`）を推移的に。
- 状態: ⚠️ 部分（sorry 0、rc=0）。STEP surgery の assembly／VE3 成長／pinned 形を緑で移植し、
  IH 消費版 `Step_up` を surgery 残差束から供給。pointwise `{VE3Step, VE4Step}` を除去したキャップ
  ストーン `VE34goal_on_reg4D_of_step_surgery_ss` を供給。露出残差 = `{StepTerminalReady_ss,
  StepFrontPred_ss, StepTermPred_ss, StepPredIndex_ss（純 Pred/segment 幾何）, TSPINStep_ss
  （唯一の深い §7.4 頭輸送）}`。
- Private suffix: `_ss`。
-/

namespace PSS

/-! ## 純 `BT` 代数（keystone 非依存、principal リスト末尾分割） -/

/-- `addBT` 結合律（principal リスト連結の `List.append_assoc`）。 -/
private theorem addBT_assoc_ss (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  obtain ⟨as⟩ := a; obtain ⟨bs⟩ := b; obtain ⟨cs⟩ := c
  simp [addBT, List.append_assoc]

/-- `bpHeadT (Dprin a b) = b`（principal 項の内部項読み出し、`rfl`）。 -/
private theorem bpHeadT_Dprin_ss (a : ℕ∞) (b : BT) : bpHeadT (Dprin a b) = b := rfl

/-- 外側頭が等しい principal の内部項一致（Isabelle の `Dpt` 単射の Lean 版）。 -/
private theorem Dprin_inner_ss {v : ℕ∞} {a b : BT} (h : Dprin v a = Dprin v b) : a = b := by
  have h2 := congrArg bpHeadT h
  simpa only [bpHeadT_Dprin_ss] using h2

/-- **末尾 principal 分割**（Isabelle `vg6x_addBT_split_lastD`）: 末尾頭指標が等しければ
prefix と末尾内部項がともに一致。 -/
private theorem addBT_split_lastD_ss {p q a b : BT} {v : ℕ∞}
    (h : addBT p (Dprin v a) = addBT q (Dprin v b)) : p = q ∧ a = b := by
  obtain ⟨ps⟩ := p; obtain ⟨qs⟩ := q
  simp only [addBT, Dprin] at h
  have hl : ps ++ [BP.db v a] = qs ++ [BP.db v b] := BT.trm.inj h
  refine ⟨?_, ?_⟩
  · have hd := congrArg List.dropLast hl
    simpa [List.dropLast_concat] using hd
  · have hg := congrArg List.getLast? hl
    simp only [List.getLast?_concat, Option.some.injEq, BP.db.injEq] at hg
    exact hg.2

/-- **末尾頭指標一致**（Isabelle `vs3x_addBT_lastidx`）。 -/
private theorem addBT_lastidx_ss {p q a b : BT} {v1 v2 : ℕ∞}
    (h : addBT p (Dprin v1 a) = addBT q (Dprin v2 b)) : v1 = v2 := by
  obtain ⟨ps⟩ := p; obtain ⟨qs⟩ := q
  simp only [addBT, Dprin] at h
  have hl : ps ++ [BP.db v1 a] = qs ++ [BP.db v2 b] := BT.trm.inj h
  have hg := congrArg List.getLast? hl
  simp only [List.getLast?_concat, Option.some.injEq, BP.db.injEq] at hg
  exact hg.1

/-! ## STEP surgery の残差 Prop（Isabelle の building block に 1:1 対応）

いずれも補正体制 `VE34Reg4D N` ＋ STEP 条件 `VEj1p N < Lng N - 1` 上で量化する。
`{StepTerminalReady_ss, StepFrontPred_ss, StepTermPred_ss, StepPredIndex_ss}` は純 Pred/segment
幾何（BASE 版 `{TerminalSliceReady_vv, FrontPredBaseTransport_vv, TermPredBaseTransport_vv}` と
同種、`8.2-condIIIV-ve-values`）で、`TSPINStep_ss` が唯一の深い §7.4 頭輸送。 -/

/-- **終切片 keystone 適用可能性**（Isabelle `bux_terminal_slice_ready` の STEP 版）:
終切片 `Mp = seg N j₀' (Lng N-1)` が `keystoneShapes_vv` を適用できる状態。 -/
def StepTerminalReady_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    RTPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
    monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true ∧
    Br (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ [] ∧
    1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) - 1

/-- **前置切片 Pred 転送**（Isabelle `bpx_front_Pred` 102945 の STEP 版）: `Pred N` の前置切片は
`N` の前置切片に一致（`Pred` は末尾列を落とすだけで前置に触れない）。 -/
def StepFrontPred_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    seg (Pred N) 0 ((FirstNodes (Pred N)).getD (LastStep (Pred N)) 0 - 1)
      = seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)

/-- **終切片 Pred 転送**（Isabelle `bpx_term_Pred` 102981 の STEP 版）: `Pred N` の終切片は
`N` の終切片の `Pred` に一致（joint 共有ゆえ、`drop∘butlast = butlast∘drop`）。 -/
def StepTermPred_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    seg (Pred N) ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0) (Lng (Pred N) - 1)
      = Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))

/-- **Pred index 転送**（Isabelle `bpx_step_setup(13),(14)`）: 頭 `entry (Pred N) 1 0` と
最終 joint での `entry (Pred N) 1 (j₀')` が `N` の対応値に一致。 -/
def StepPredIndex_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    entry (Pred N) 1 0 = entry N 1 0 ∧
    entry (Pred N) 1 ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0)
      = entry N 1 ((Joints N).getD ((Br N).length - 1) 0)

/-- **STEP の TSPIN（唯一の深い残差）**（Isabelle `tsx_TSPIN` 104267）: pinned 形の内部項 `a` は
終切片頭 `bpHeadT (Trans (Mp))` に一致（非許容 joint での Mark-surgery naturality、原文 3360）。 -/
def TSPINStep_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    ∀ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a)) →
      a = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))

/-- **中間残差 — VE3 成長**（Isabelle `bpx_VE3_step` 103023 の結論）: STEP ホストで IH から
`VE3goal N` を放出する。下で `StepVE3Growth_of_reductions_ss` が keystone modulo で還元。 -/
def StepVE3Growth_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) → VE3goal N

/-- **中間残差 — pinned 形**（Isabelle `bpx_step_form_pinned` 103085 の結論）: STEP ホストで
IH から外側 principal pinned 形を放出する。下で `StepPinnedForm_of_ih_ss` が還元。 -/
def StepPinnedForm_ss : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) →
    ∃ a : BT, Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) a))

/-! ## STEP assembly（Isabelle `bpx_VE34_step_modTSPIN`, 103234）

pinned 形 + VE3 成長 + `TSPIN` から `VE34goal N`（= `VE3goal N ∧ VE4goal N`）を再組立。
純 `BT` 代数＋`VE34goal_iff` の ∃-シャッフルのみ。 -/

/-- **Isabelle `bpx_VE34_step_modTSPIN` (103234) の逐語移植**: STEP スロット `Step_up` を
中間残差 `{StepPinnedForm_ss, StepVE3Growth_ss, TSPINStep_ss}` から供給。 -/
theorem Step_up_of_pieces_ss
    (hForm : StepPinnedForm_ss) (hTSPIN : TSPINStep_ss) (hVE3 : StepVE3Growth_ss) :
    Step_up := by
  intro N regD _fin hlt regDP ihP
  -- VE3（成長）
  have hVE3goal : VE3goal N := hVE3 N regD hlt regDP ihP
  -- pinned 形
  obtain ⟨a, hform⟩ := hForm N regD hlt regDP ihP
  -- TSPIN で内部項を終切片頭に固定
  have haeq : a = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) :=
    hTSPIN N regD hlt a hform
  -- VE4（頭シフト）
  have hVE4goal : VE4goal N := by
    unfold VE4goal
    rw [hform, bpHeadT_Dprin_ss, haeq]
  exact (VE34goal_iff N).mpr ⟨hVE3goal, hVE4goal⟩

/-! ## VE3 成長の keystone modulo 還元（Isabelle `bpx_VE3_step`, 103023）

`VE3RunStep_of_reductions_vv`（`8.2-condIIIV-ve-values`, run-step BASE 版）の STEP 版
＝逐語同型。IH の VE3 を終切片 Pred 転送で `N` のスライスへ移し、keystone 二形と
成長輸送で `VE3goal N` を得る。 -/

/-- **Isabelle `bpx_VE3_step` (103023) の逐語移植**: 中間残差 `StepVE3Growth_ss` を、
移植済み `keystoneShapes_vv`／`growth_transport_vv` ＋純幾何残差
`{StepTerminalReady_ss, StepFrontPred_ss, StepTermPred_ss}` から放出。 -/
theorem StepVE3Growth_of_reductions_ss
    (hready : StepTerminalReady_ss) (hfront : StepFrontPred_ss) (hterm : StepTermPred_ss) :
    StepVE3Growth_ss := by
  intro N regD hlt _regDP ihP
  -- IH の VE3 成分
  obtain ⟨t2P, ihEq, ht2Pne⟩ := ((VE34goal_iff (Pred N)).mp ihP).1
  -- 前置/終切片の Pred 転送で IH を N のスライスへ移す
  have hfr := hfront N regD hlt
  have htr := hterm N regD hlt
  rw [htr, hfr] at ihEq
  -- keystone 二形（終切片 Mp N 上）
  obtain ⟨hRr, hmr, hbrr, hgtr⟩ := hready N regD hlt
  rcases keystoneShapes_vv
      (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) hRr hmr hbrr hgtr with
    ⟨c, w, x, hTP, hTM⟩ | ⟨c, w, x, y, hTP, hTM⟩
  · -- Shape A（keystone clause 1/2）: 成長は末尾 principal 追加
    have hc : c = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have h := ihEq
      rw [hTP, bpHeadT_Dprin_ss] at h
      exact h
    refine ⟨addBT t2P (Dprin w x), ?_, ?_⟩
    · rw [hTM, bpHeadT_Dprin_ss, hc, addBT_assoc_ss]
    · obtain ⟨ds⟩ := t2P
      intro h
      have hnil : ds ++ [BP.db w x] = [] := BT.trm.inj h
      simp at hnil
  · -- Shape B（keystone clause 3/4）: 成長輸送で末尾内部項を x → y に差し替え
    have hEq : addBT c (Dprin w x)
        = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have h := ihEq
      rw [hTP, bpHeadT_Dprin_ss] at h
      exact h
    obtain ⟨t2, ht2Eq, ht2ne⟩ := growth_transport_vv c
      (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P x y w hEq ht2Pne
    refine ⟨t2, ?_, ht2ne⟩
    rw [hTM, bpHeadT_Dprin_ss, ht2Eq]

/-! ## pinned 形の keystone modulo 還元（Isabelle `bpx_step_form_pinned`, 103085）

IH の VE4 を keystone（`keystone`, 移植済）clause 3/4 に照合。STEP 条件 `j₁' < Lng N-1`
（＝`VEj1p N < Lng N-1`）が clause 1/2（`j₁' = Lng N-1`）を排除するので clause 3/4 のみ。 -/

/-- **Isabelle `bpx_step_form_pinned` (103085) の逐語移植**: 中間残差 `StepPinnedForm_ss` を、
移植済み `keystone`／`Trans_principal_head` ＋ addBT 末尾分割代数 ＋純幾何残差
`{StepFrontPred_ss, StepTermPred_ss, StepPredIndex_ss}` から放出。 -/
theorem StepPinnedForm_of_ih_ss
    (hfront : StepFrontPred_ss) (hterm : StepTermPred_ss) (hidx : StepPredIndex_ss) :
    StepPinnedForm_ss := by
  intro N regD hlt regDP ihP
  -- 体制の展開（`reg` は後で `veStep34Geom_vs3` に渡すので破壊せず射影で取り出す）
  have reg : VE34Reg4 N := VE34Reg4D_VE34Reg4 N regD
  have hR : RTPS N := reg.1.1.1
  have hmono : monoT N = true := reg.1.1.2.1
  have hBrne : Br N ≠ [] := reg.1.1.2.2
  have regP : VE34Reg4 (Pred N) := VE34Reg4D_VE34Reg4 (Pred N) regDP
  have hRP : RTPS (Pred N) := regP.1.1.1
  have hmonoP : monoT (Pred N) = true := regP.1.1.2.1
  -- STEP 幾何: 2 < Lng N ⟹ 1 < Lng N - 1、そして j₁' ≠ Lng N - 1
  obtain ⟨_, _, _, _, hLng2, _, _, _, _, _, _, _⟩ := veStep34Geom_vs3 N reg hlt
  have hj1gt : 1 < Lng N - 1 := by omega
  have notj1eq : (FirstNodes N).getD ((Br N).length - 1) 0 ≠ Lng N - 1 := by
    -- VEj1p N = FirstNodes N ! (Br.len-1) < Lng N - 1
    have : VEj1p N < Lng N - 1 := hlt
    unfold VEj1p at this
    omega
  -- Pred index
  obtain ⟨he10P, hej0P⟩ := hidx N regD hlt
  -- 前置/終切片 Pred 転送
  have hfr := hfront N regD hlt
  have htr := hterm N regD hlt
  -- IH の VE4 を N のスライスへ移す
  have hVE4P := ((VE34goal_iff (Pred N)).mp ihP).2
  unfold VE4goal at hVE4P
  rw [hfr, htr, hej0P] at hVE4P
  -- Pred N の principal 頭形（e10P で頭指標を N に合わせる）
  have hprinc := Trans_principal_head (Pred N) hRP hmonoP
  rw [he10P, hVE4P] at hprinc
  -- keystone（N 上、STEP ゆえ clause 3/4）
  rcases keystone N hR hmono hBrne hj1gt with h1 | h2 | h3 | h4
  · exact absurd h1.1 notj1eq
  · exact absurd h2.1 notj1eq
  · -- clause 3: 頭 j₁'、IH 照合で j₁' = j₀' へ、prefix pin
    obtain ⟨t123, ⟨q3P, q3M⟩, _⟩ := h3
    have hinner := Dprin_inner_ss (q3P.symm.trans hprinc)
    have hidxeq := addBT_lastidx_ss hinner
    rw [hidxeq] at hinner q3M
    have hpin := (addBT_split_lastD_ss hinner).1
    refine ⟨t123.2.2, ?_⟩
    rw [q3M, hpin]
  · -- clause 4: 頭は既に j₀'
    obtain ⟨t123, ⟨q4P, q4M⟩, _⟩ := h4
    have hinner := Dprin_inner_ss (q4P.symm.trans hprinc)
    have hpin := (addBT_split_lastD_ss hinner).1
    refine ⟨t123.2.2, ?_⟩
    rw [q4M, hpin]

/-! ## STEP スロットの surgery 残差束からの供給（IH 消費、pointwise 不要） -/

/-- **STEP スロット `Step_up` を surgery 残差束から供給**（`Step_up_of_pieces_ss` に中間残差の
還元を差し込む）。pointwise `{VE3Step, VE4Step}` を **消費しない**。 -/
theorem Step_up_of_surgery_ss
    (hready : StepTerminalReady_ss) (hfront : StepFrontPred_ss) (hterm : StepTermPred_ss)
    (hidx : StepPredIndex_ss) (hTSPIN : TSPINStep_ss) : Step_up :=
  Step_up_of_pieces_ss
    (StepPinnedForm_of_ih_ss hfront hterm hidx)
    hTSPIN
    (StepVE3Growth_of_reductions_ss hready hfront hterm)

/-! ## キャップストーン: pointwise `{VE3Step, VE4Step}` を除去した補正体制全ホスト `VE34goal`

`8.2-condIIIV-unified-peel` の `VE34goal_on_reg4D_of_residuals_up` は STEP 脚に
`Step_of_legs_up (VE3Step)(VE4Step)` を差していた。本キャップストーンはそれを
`Step_up_of_surgery_ss`（IH 消費）に置換し、pointwise 二残差を STEP surgery 残差束へ
置き換える。 -/

/-- **STEP surgery 版キャップストーン**: 補正体制 `VE34Reg4D` の全ホストで `VE34goal` を、
BASE 残差束 `{RunStepGuardJoint_up, StepRegPres_up, PIN_bd, TSPIN_bd, VE3RunBase_bd,
VE3RunStep_bd}` ＋ STEP surgery 残差束 `{StepTerminalReady_ss, StepFrontPred_ss, StepTermPred_ss,
StepPredIndex_ss, TSPINStep_ss}` から供給する（`fin` は `finRun_up_all` で内部供給、
pointwise `{VE3Step, VE4Step}` は **不要**）。 -/
theorem VE34goal_on_reg4D_of_step_surgery_ss
    (hRSgj : RunStepGuardJoint_up) (hStepReg : StepRegPres_up)
    (hPIN : PIN_bd) (hTSPIN : TSPIN_bd)
    (hRB : VE3RunBase_bd) (hRS : VE3RunStep_bd)
    (hready : StepTerminalReady_ss) (hfront : StepFrontPred_ss) (hterm : StepTermPred_ss)
    (hidx : StepPredIndex_ss) (hTSPINstep : TSPINStep_ss)
    (M : PS) (hM : VE34Reg4D M) : VE34goal M :=
  VE34_backpeel_fin3_up
    (BaseRunBase_of_leaves_up hPIN hTSPIN hRB)
    (BaseRunStep_of_leaves_up hPIN hTSPIN hRS)
    (Step_up_of_surgery_ss hready hfront hterm hidx hTSPINstep)
    hRSgj hStepReg M hM (finRun_up_all M)

/-! ## 転記の数値検証（STEP 体制の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(2,1)(3,1)` は補正体制 `VE34Reg4D`（RTPS・monoT・Br≠[]・
ガード・非許容 joint・descending）に属し、STEP 条件 `VEj1p = 3 < 4 = Lng - 1` を満たす。 -/

#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,1),(3,1)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,1),(3,1)] < Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1) = true

#print axioms Step_up_of_pieces_ss
#print axioms StepVE3Growth_of_reductions_ss
#print axioms StepPinnedForm_of_ih_ss
#print axioms Step_up_of_surgery_ss
#print axioms VE34goal_on_reg4D_of_step_surgery_ss

end PSS
