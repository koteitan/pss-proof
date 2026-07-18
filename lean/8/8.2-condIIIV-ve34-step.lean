import «8».«8.2-condIIIV-VE234»

/-!
# §8.2 条件(II)/(IV) VE34 後ろ剥がしキャンペーンの STEP 幾何（`bpx_step_setup` 移植）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）の**帰納ステップ**（最終列が新しい枝を開く
  `VEj1p N < Lng N - 1`）。`8.2-condIIIV-deep3` は `condIIIVts` フィールドを四残差
  `{VE3Base, VE3Step, VE4Base, VE4Step}` に絞った。本ファイルは STEP 側二残差
  `{VE3Step, VE4Step}`（`VE34Reg4 Q ∧ VEj1p Q < Lng Q - 1 ⇒ VE3goal/VE4goal Q`）の
  攻略に必要な**共有 STEP 幾何**を無条件で供給する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植）。
- Isabelle（`isabelle/layerB/pss_wip.thy`, r45-BASESTEP, `bpx_` prefix, 102585–108722）:
  - `bpx_step_setup` (102730): STEP 体制の展開＋添字境界
    `j₀' < TrMax N < j₁' < Lng N - 1` → 本ファイル `veStep34Geom_vs3`。
  - `slice_Trans_principal_head`（`8.2-condIIIV-terminal-slice-Trans`）で三つの祖先切片
    `N = seg Q 0 m₁`／`N' = seg Q j₀' m₁`／`M' = seg Q j₀' (Lng Q-1)` の `Trans` を
    頭指標 principal 形に固定 → 本ファイル `Trans_{front,inner,lastBranch}Slice_form_vs3`。
  - `e2x_Trans_principal_head`（Isabelle）＝`Trans_principal_head`（`8.2-condV-...`）で
    ホスト `Trans Q` を外側 principal 形に固定 → 本ファイル `Trans_host_form_vs3`。
- **STEP 残差 `{VE3Step, VE4Step}` は本ファイルの射程外（研究フロンティア）**: Isabelle
  ですら STEP は単一の頭輸送方程式 `TSPIN`（`Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'} a) ⇒
  a = bpHeadT (Trans (seg N j₀' (Lng N-1)))`）modulo までしか閉じておらず、その `TSPIN`
  自体が「非許容 joint での `Trans` 再帰の Mark-surgery naturality（原文 content.md 3360
  の部分表現の単項成分と `Pred` の関係）」を要する**次ラウンドのコア**として carry されて
  いる。Lean 側でも `m_7_4_Trans_Mark_Pred`／`Mark_Trans_repr` は `Marked N m`（＝`adm N m`）
  を要求するが、体制の最終 joint は `0 < j₀' < TrMax N` ゆえ非許容（`adm_le_TrMax_cases`）で
  適用不能。加えて keystone（`kyx_terminal_slice_keystone`／`m_8_2_keystone`）は Lean 未移植。
  したがって本ファイルは STEP の**下準備幾何のみ**を緑で供給し、VE3Step/VE4Step の
  値方程式本体（§7.4 頭シフト readback surgery）は封じたまま名前付き Prop に残す。
  ⚠️ naive prefix-append 帰納は反証済（python/ve34_deep2.py 0/5、`8.2-condIIIV-VE34-step`
  ヘッダ）。
- 依存 module: `8.2-condIIIV-VE234`（`VE3Step`/`VE4Step`/`VE3goal`/`VE4goal`/`VE34Reg4`/
  `VEj1p`/`LastStep`/`slice_Trans_principal_head`/`m1_bounds`/`Trans_principal_head`/
  `FirstNodes_TrMax_Joints`/`mono_slice`/`RTPS_TPS`/`TrMax_bound`/`Br`/`Joints`/
  `FirstNodes`/`TrMax`/`entry`/`seg`/`Trans`/`bpHeadT`/`Dprin` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。STEP 体制の共有幾何と四つの `Trans` principal 形を
  無条件で供給。VE3Step/VE4Step は**未討伐**（上記フロンティア）。
- Private suffix: `_vs3`。
-/

namespace PSS

/-! ## STEP 体制の共有幾何（Isabelle `bpx_step_setup`, layerB 102730）

体制 `VE34Reg4 Q`（＝訂正版体制、最終 joint `j₀'` は非許容 `0 < j₀' < TrMax Q`）と
STEP 条件 `VEj1p Q < Lng Q - 1` から、後続 surgery が使う添字境界
`0 < j₀' < TrMax Q ≤ m₁ < Lng Q - 1`（`m₁ = FirstNodes Q ! (LastStep Q) - 1`）を
一括で取り出す。 -/

/-- **Isabelle `bpx_step_setup` (layerB 102730)** の逐語移植（幾何部）。

`VE34Reg4 Q ∧ VEj1p Q < Lng Q - 1` から、STEP surgery が消費する共有幾何を返す:
基本体制（`RTPS`/`monoT`/`Br ≠ []`/`2 < Lng Q`）、最終 joint の非許容境界
`0 < j₀' < TrMax Q`、幹右端 `TrMax Q < Lng Q - 1`、そして前置終端
`m₁ = FirstNodes Q ! (LastStep Q) - 1` の位置 `0 < j₀' < TrMax Q ≤ m₁ < Lng Q - 1`。 -/
theorem veStep34Geom_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    RTPS Q ∧ monoT Q = true ∧ Br Q ≠ [] ∧ TPS Q ∧ 2 < Lng Q ∧
    0 < (Joints Q).getD ((Br Q).length - 1) 0 ∧
    (Joints Q).getD ((Br Q).length - 1) 0 < TrMax Q ∧
    TrMax Q < Lng Q - 1 ∧
    0 < (FirstNodes Q).getD (LastStep Q) 0 - 1 ∧
    (Joints Q).getD ((Br Q).length - 1) 0 < (FirstNodes Q).getD (LastStep Q) 0 - 1 ∧
    TrMax Q ≤ (FirstNodes Q).getD (LastStep Q) 0 - 1 ∧
    (FirstNodes Q).getD (LastStep Q) 0 - 1 < Lng Q - 1 := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS Q := RTPS_TPS Q hR
  have hne : TrMax Q ≠ Lng Q - 1 := fun heq => hBrne (by simp [Br, heq])
  have hTrb : TrMax Q ≤ Lng Q - 1 := TrMax_bound Q hM
  have hTrlt : TrMax Q < Lng Q - 1 := lt_of_le_of_ne hTrb hne
  have hm1 := m1_bounds Q hM hmono hBrne
  refine ⟨hR, hmono, hBrne, hM, by omega, hj0pos, hj0lt, hTrlt, ?_, ?_, hm1.1, hm1.2⟩
  · omega
  · omega

/-! ## STEP 切片の単調性（`mono_slice`）

体制幾何から三つの祖先切片が単調であることを取り出す。以後の
`slice_Trans_principal_head` 適用の前提。 -/

/-- 前置切片 `N = seg Q 0 m₁` は単調（`m₁ = FirstNodes Q ! (LastStep Q) - 1`）。 -/
theorem monoT_frontSlice_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    monoT (seg Q 0 ((FirstNodes Q).getD (LastStep Q) 0 - 1)) = true := by
  obtain ⟨hR, hmono, _, hM, _, _, _, _, hm1pos, _, _, hm1lt⟩ := veStep34Geom_vs3 Q reg hlt
  exact mono_slice Q 0 _ hM hmono hm1pos (by omega) (Nat.zero_le _)

/-- 内側切片 `N' = seg Q j₀' m₁` は単調。 -/
theorem monoT_innerSlice_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    monoT (seg Q ((Joints Q).getD ((Br Q).length - 1) 0)
                 ((FirstNodes Q).getD (LastStep Q) 0 - 1)) = true := by
  obtain ⟨hR, hmono, _, hM, _, _, _, _, _, hjm1, _, hm1lt⟩ := veStep34Geom_vs3 Q reg hlt
  exact mono_slice Q _ _ hM hmono hjm1 (by omega) (le_refl _)

/-- 最終枝切片 `M' = seg Q j₀' (Lng Q - 1)` は単調。 -/
theorem monoT_lastBranchSlice_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    monoT (seg Q ((Joints Q).getD ((Br Q).length - 1) 0) (Lng Q - 1)) = true := by
  obtain ⟨hR, hmono, _, hM, _, _, hj0lt, hTrlt, _, _, _, _⟩ := veStep34Geom_vs3 Q reg hlt
  exact mono_slice Q _ _ hM hmono (by omega) (le_refl _) (le_refl _)

/-! ## STEP の四つの `Trans` principal 形

VE3goal/VE4goal に現れる四つの `Trans` を、頭指標 principal 形に固定する。
`slice_Trans_principal_head`（切片）と `Trans_principal_head`（ホスト）。これらは
STEP surgery が消費する「形」の下準備であって、値方程式そのものではない。 -/

/-- 前置切片 `N = seg Q 0 m₁` の `Trans` は頭指標 `Q₁,₀` の principal 形。 -/
theorem Trans_frontSlice_form_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    Trans (seg Q 0 ((FirstNodes Q).getD (LastStep Q) 0 - 1))
      = Dprin (entry Q 1 0 : ℕ∞)
          (bpHeadT (Trans (seg Q 0 ((FirstNodes Q).getD (LastStep Q) 0 - 1)))) := by
  obtain ⟨hR, hmono, _, hM, _, _, _, _, hm1pos, _, _, hm1lt⟩ := veStep34Geom_vs3 Q reg hlt
  exact slice_Trans_principal_head Q 0 _ hR hm1pos (by omega)
    (monoT_frontSlice_vs3 Q reg hlt)

/-- 内側切片 `N' = seg Q j₀' m₁` の `Trans` は頭指標 `Q₁,ⱼ'₀` の principal 形。 -/
theorem Trans_innerSlice_form_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    Trans (seg Q ((Joints Q).getD ((Br Q).length - 1) 0)
                 ((FirstNodes Q).getD (LastStep Q) 0 - 1))
      = Dprin (entry Q 1 ((Joints Q).getD ((Br Q).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg Q ((Joints Q).getD ((Br Q).length - 1) 0)
                                 ((FirstNodes Q).getD (LastStep Q) 0 - 1)))) := by
  obtain ⟨hR, hmono, _, hM, _, _, _, _, _, hjm1, _, hm1lt⟩ := veStep34Geom_vs3 Q reg hlt
  exact slice_Trans_principal_head Q _ _ hR hjm1 (by omega)
    (monoT_innerSlice_vs3 Q reg hlt)

/-- 最終枝切片 `M' = seg Q j₀' (Lng Q - 1)` の `Trans` は頭指標 `Q₁,ⱼ'₀` の principal 形。 -/
theorem Trans_lastBranchSlice_form_vs3 (Q : PS) (reg : VE34Reg4 Q)
    (hlt : VEj1p Q < Lng Q - 1) :
    Trans (seg Q ((Joints Q).getD ((Br Q).length - 1) 0) (Lng Q - 1))
      = Dprin (entry Q 1 ((Joints Q).getD ((Br Q).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg Q ((Joints Q).getD ((Br Q).length - 1) 0) (Lng Q - 1)))) := by
  obtain ⟨hR, hmono, _, hM, _, _, hj0lt, hTrlt, _, _, _, _⟩ := veStep34Geom_vs3 Q reg hlt
  exact slice_Trans_principal_head Q _ _ hR (by omega) (le_refl _)
    (monoT_lastBranchSlice_vs3 Q reg hlt)

/-- ホスト `Trans Q` は外側頭指標 `Q₁,₀` の principal 形（`Trans_principal_head`）。
VE4goal の左辺 `bpHeadT (Trans Q)` の下準備。 -/
theorem Trans_host_form_vs3 (Q : PS) (reg : VE34Reg4 Q) (hlt : VEj1p Q < Lng Q - 1) :
    Trans Q = Dprin (entry Q 1 0 : ℕ∞) (bpHeadT (Trans Q)) := by
  obtain ⟨hR, hmono, _, _, _, _, _, _, _, _, _, _⟩ := veStep34Geom_vs3 Q reg hlt
  exact Trans_principal_head Q hR hmono

/-! ## STEP 残差の露出（VE3Step / VE4Step は未討伐）

VE3goal/VE4goal の**値方程式本体**（頭の append 成長／外側 context 方程式）は
§7.4 頭シフト readback surgery（非許容 joint での Mark-surgery naturality＝`TSPIN`）に
帰着し、本ファイルの射程外。上の四つの principal 形はその surgery の入口の「形」を
無条件で固定するのみ。VE3Step/VE4Step は `8.2-condIIIV-VE234` の名前付き Prop のまま。 -/

/-! ## 転記の数値検証（STEP 体制の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(2,1)(3,1)` は訂正版体制 `VE34Reg4`（RTPS・monoT・Br ≠ []・
ガード `e₁ < e₀ at j₁'`・非許容 `0 < j₀' = 1 < 2 = TrMax`）に属し、かつ STEP 条件
`VEj1p = 3 < 4 = Lng - 1` を満たす（`veStep34Geom_vs3` 等の量化域が非空）。 -/

#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,1),(3,1)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,1),(3,1)] < Lng [(0,0),(1,1),(2,2),(2,1),(3,1)] - 1) = true

#print axioms veStep34Geom_vs3
#print axioms Trans_frontSlice_form_vs3
#print axioms Trans_innerSlice_form_vs3
#print axioms Trans_lastBranchSlice_form_vs3
#print axioms Trans_host_form_vs3

end PSS
