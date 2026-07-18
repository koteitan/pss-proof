import «8».«8.2-condIIIV-VE34-entry»
import «6».«6.5-Red-Pred-commute»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.2 条件(II)/(IV) VE34 後ろ剥がしキャンペーンの「体制機械」（訂正版体制＋RPERS 無条件）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）。
  原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）の後ろ剥がし帰納法。本ファイルはその
  **訂正版体制と体制持続（RPERS）** を供給する。
- 訂正: なし（Isabelle 側で証明済み補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）: 入口 `8.2-condIIIV-VE34-entry`
  （`vg2x_reg2`/`vg2x_VE34_backpeel`/`vg2x_VE34_of_reg`）の次のブリック。
  **無防備な `vg2x_reg2` 体制の `{BASE, STEP, RPERS}` は経験的に反証される**（wip 94467
  banner）。訂正版は二段階で防護節を足す:
  - `vg3x_reg3` (94469, definition) → `VE34Reg3`（非対角ガード
    `entry N 1 (FirstNodes N ! (Lng(Br N)-1)) < entry N 0 (FirstNodes N ! …)`、
    ＝`entry N 1 (VEj1p N) < entry N 0 (VEj1p N)` を `vg2x_reg2` に足す）
  - `vg4x_reg4` (95122, definition) → `VE34Reg4`（最終 joint の非許容性
    `0 < Joints N ! (Lng(Br N)-1) < TrMax N` を足す。`vgx_condIIIV_of_VE` が供給する
    `j0pos`/`j0lt` そのもの。`j₀' ≤ TrMax N` かつ `≤ TrMax N` の許容添字は `0` か
    `TrMax N` のみ、なので非許容 = `0 < j₀' < TrMax N`）
  - `vg3x_VE34_backpeel` (94480) / `vg4x_VE34_backpeel` (95133) → `VE34_backpeel4`
    （訂正版体制上の強帰納法骨格。入口 `VE34_backpeel` と構造同一）
  - **`vg4x_RPERS` (95186、無条件討伐)** → `VE34Rpers4_holds`（本ファイルの主定理）。
    `cfbx_j1p N < Lng N - 1` の生きた枝で訂正版体制が `Pred N` へ遺伝する。
    `Pred` は `RT_PS`/`PT_PS`/`Br ≠ []` を保存し、ガード（`j₁' < Lng N-1` の行値は
    `butlast` 不変）と `0 < j₀' < TrMax`（最終 joint と `TrMax` は `Pred` 不変）も
    逐語で運ばれる。
  - `vg4x_VE34_of_DT` (95296) → `VE34_of_DT4`（`DT_PS` ホスト＋ガード＋`j0pos`/`j0lt`
    から VE3/VE4 存在目標を、RPERS 内部消化して鋭い `{BASE, STEP}` 対に還元）
- 依存 module: `8.2-condIIIV-VE34-entry`（`VE34Reg`/`VE34goal`/`VE2goal`/`VEj1p` と
  条件(II)/(IV) 終切片命題）、`6.5-Red-Pred-commute`（`Pred` 下の
  `RTPS`/`monoT`/`TrMax`/`Br`/`FirstNodes`/`Joints`/`entry` 安定性）、
  `6.8-standard-slice-Br-descending`（`getLastD_eq_getD_last_68`）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。訂正版体制・後ろ剥がし骨格・**RPERS 無条件** と
  BASE 幾何事実を緑で供給。残差は名前付き Prop `{VE34Base4, VE34Step4}`
  （＝`vg4x_VE34_backpeel` の残る二仮定。BASE の実体は `bfx_*`/`bgx_*`/`hqx_*` の
  連鎖で本ファイルの射程外）。
-/

namespace PSS

/-! ## 私的補助（suffix `_vr`） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める。入口 `leR0_bounds_v34` の再掲。 -/
private theorem leR0_bounds_vr (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`）。入口 `FN_lt_v34` の再掲。 -/
private theorem FN_lt_vr (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_vr M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制の下で `VEj1p N < Lng N`（入口 `VEj1p_lt_v34` の `VE34Reg` 版）。 -/
private theorem VEj1p_lt_vr (N : PS) (hreg : VE34Reg N) : VEj1p N < Lng N := by
  obtain ⟨hR, hmono, hBrne⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_vr N _ hM hmono hJ

/-- `Lng (Pred N) = Lng N - 1`（`1 < Lng N` のとき）。 -/
private theorem Lng_Pred_vr (N : PS) (h : 1 < Lng N) :
    Lng (Pred N) = Lng N - 1 := by
  have hle : ¬ (Lng N ≤ 1) := by omega
  simp [Pred, hle, Lng]

/-- Isabelle `adm_trunk_interior_nadm` (wip 32280): 幹の内部添字 `0 < j < TrMax M` は
`M` 非許容。`8.2-condV-VE-base2` の `_vb2` 再証明の双子。 -/
private theorem adm_trunk_interior_nadm_vr (M : PS) (j : ℕ) (hM : TPS M)
    (hjpos : 0 < j) (hjlt : j < TrMax M) : adm M j = false := by
  have hs1 : nextR M 1 (j - 1) (j - 1 + 1) = true :=
    TrMax_trunk_step M (j - 1) hM (by omega)
  have hkeq : j - 1 + 1 = j := by omega
  rw [hkeq] at hs1
  have hs2 : nextR M 1 j (j + 1) = true := TrMax_trunk_step M j hM hjlt
  simp [adm, nadm, hs1, hs2]

/-- Isabelle `adm_le_TrMax_cases` (wip 32296): `TrMax M` 以下の `M` 許容な添字は
`0` か `TrMax M` のみ。`8.2-condV-VE-base2` の `_vb2` 再証明の双子。 -/
private theorem adm_le_TrMax_cases_vr (M : PS) (j : ℕ) (hM : TPS M)
    (ha : adm M j = true) (hjle : j ≤ TrMax M) : j = 0 ∨ j = TrMax M := by
  by_contra hnot
  have hj0 : j ≠ 0 := fun h => hnot (Or.inl h)
  have hjT : j ≠ TrMax M := fun h => hnot (Or.inr h)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjlt : j < TrMax M := lt_of_le_of_ne hjle hjT
  have hbad := adm_trunk_interior_nadm_vr M j hM hjpos hjlt
  rw [hbad] at ha
  exact Bool.false_ne_true ha

/-! ## 訂正版体制 `VE34Reg3` / `VE34Reg4`（Isabelle `vg3x_reg3` / `vg4x_reg4`） -/

/-- **Isabelle `vg3x_reg3` (layerB 94469)**: 非対角ガードを足した体制。
`vg2x_reg2`（`VE34Reg`）に、最終枝の左端 `j₁' = FirstNodes N ! (Lng(Br N)-1) = VEj1p N`
での行1値 < 行0値（＝最終列が対角でない）を加える。無防備な `VE34Reg` の
`{BASE, STEP, RPERS}` は反証されるので、この防護節が必要。 -/
def VE34Reg3 (N : PS) : Prop :=
  VE34Reg N ∧ entry N 1 (VEj1p N) < entry N 0 (VEj1p N)

instance (N : PS) : Decidable (VE34Reg3 N) := by
  unfold VE34Reg3; infer_instance

/-- **Isabelle `vg4x_reg4` (layerB 95122)**: 最終 joint の非許容性を足した体制。
`vg3x_reg3` に `0 < j₀' < TrMax N`（`j₀' = Joints N ! (Lng(Br N)-1)`）を加える。
常に `j₀' ≤ TrMax N`（`FirstNodes_TrMax_Joints`）で、`≤ TrMax N` の許容添字は
`0`/`TrMax N` のみ（`adm_le_TrMax_cases`）なので、これは `j₀'` の非許容性と同値
（`vgx_condIIIV_of_VE` が供給する `j0pos`/`j0lt` そのもの）。 -/
def VE34Reg4 (N : PS) : Prop :=
  VE34Reg3 N ∧
    0 < (Joints N).getD ((Br N).length - 1) 0 ∧
    (Joints N).getD ((Br N).length - 1) 0 < TrMax N

instance (N : PS) : Decidable (VE34Reg4 N) := by
  unfold VE34Reg4; infer_instance

/-! ### 転記の数値検証（体制判定を `decide` で照合） -/

-- witness `M = (0,0)(1,1)(2,2)(2,0)`（入口 `witness_c24`）: 最終枝の左端は列3、
-- `entry 1 3 = 0 < 2 = entry 0 3`（ガード成立）、`j₀' = 1`、`0 < 1 < 2 = TrMax`。
#guard decide (VE34Reg3 [(0,0),(1,1),(2,2),(2,0)]) = true
#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,0)]) = true
-- 幹（`Br = []`）は体制に属さない。
#guard decide (VE34Reg3 [(0,0),(1,1),(2,2)]) = false
#guard decide (VE34Reg4 [(0,0),(1,1),(2,2)]) = false

/-! ## 残差ブリック（Isabelle `vg4x_VE34_backpeel` の残る二仮定） -/

/-- `BASE`（`j₁' = j₁`、最終列が現最終枝の中）。Isabelle `vg4x_VE34_backpeel` の
第一仮定（訂正版体制）。 -/
def VE34Base4 : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → VE34goal N

/-- `STEP`（`j₁' < j₁`、帰納枝、IH `VE34goal (Pred N)` を消費）。
Isabelle `vg4x_VE34_backpeel` の第二仮定（訂正版体制）。 -/
def VE34Step4 : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N < Lng N - 1 →
    VE34Reg4 (Pred N) → VE34goal (Pred N) → VE34goal N

/-! ## 体制持続 RPERS（Isabelle `vg4x_RPERS`, layerB 95186、無条件討伐） -/

/-- **Isabelle `vg4x_RPERS` (layerB 95186)** の逐語移植（**無条件**）。

最終列が新しい枝を開く `VEj1p N < Lng N - 1` の生きた後ろ剥がし枝では、訂正版体制
`VE34Reg4` が `Pred N` へ遺伝する。`Pred` は `RT_PS`/`PT_PS`/`Br ≠ []` を保存し
（枝数は不変＝最終枝の長さ ≥ 2）、ガード（`j₁' < Lng N - 1` での行値は `butlast`
不変）と非許容境界 `0 < j₀' < TrMax`（最終 joint と `TrMax` は `Pred` 下不変）も
逐語で運ばれる。 -/
theorem VE34Rpers4_holds :
    ∀ N : PS, VE34Reg4 N → VEj1p N < Lng N - 1 → VE34Reg4 (Pred N) := by
  intro N reg hj1lt
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br N).length - 1 < (Br N).length := by omega
  have hgeom := FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ
  have hfnlt : (FirstNodes N).getD ((Br N).length - 1) 0 < Lng N - 1 := by
    simpa only [VEj1p] using hj1lt
  have hL3 : 2 < Lng N := by omega
  have hL : 1 < Lng N := by omega
  have hne : TrMax N ≠ Lng N - 1 := fun heq => hBrne (by simp [Br, heq])
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
  -- 最終枝の長さは 2 以上（`j₁' < Lng N - 1`）
  have hlastgt : 1 < Lng ((Br N).getLastD []) := by
    rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, length_seg]
    omega
  have hcore := Br_Pred_core_nontrunk N hM hL hne
  rw [if_neg (by omega : ¬Lng ((Br N).getLastD []) ≤ 1)] at hcore
  have hBrPlen : (Br (Pred N)).length = (Br N).length := by
    rw [hcore]; simp; omega
  have hBrPne : Br (Pred N) ≠ [] := by
    apply List.ne_nil_of_length_pos; rw [hBrPlen]; exact hBrpos
  have hJP : (Br N).length - 1 < (Br (Pred N)).length := by omega
  have hFNP : (FirstNodes (Pred N)).getD ((Br N).length - 1) 0 =
      (FirstNodes N).getD ((Br N).length - 1) 0 :=
    FirstNodes_Pred_core N hM hL hne _ hJP
  have hJNP : (Joints (Pred N)).getD ((Br N).length - 1) 0 =
      (Joints N).getD ((Br N).length - 1) 0 :=
    Joints_Pred_core N hM hmono hL hne _ hJP
  have htrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL hne
  have he0 := entry_Pred N 0 _ hfnlt
  have he1 := entry_Pred N 1 _ hfnlt
  -- `VEj1p (Pred N) = j₁'`（最終枝の左端は `Pred` 不変）
  have hVEjP : VEj1p (Pred N) = (FirstNodes N).getD ((Br N).length - 1) 0 := by
    unfold VEj1p; rw [hBrPlen, hFNP]
  refine ⟨⟨⟨hpredR, hmonoP, hBrPne⟩, ?_⟩, ?_, ?_⟩
  · -- ガードの遺伝
    show entry (Pred N) 1 (VEj1p (Pred N)) < entry (Pred N) 0 (VEj1p (Pred N))
    rw [hVEjP, he1, he0]
    simpa only [VEj1p] using hguard
  · -- `0 < j₀'(Pred N)`
    show 0 < (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
    rw [hBrPlen, hJNP]; exact hj0pos
  · -- `j₀'(Pred N) < TrMax (Pred N)`
    show (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0 < TrMax (Pred N)
    rw [hBrPlen, hJNP, htrP]; exact hj0lt

/-! ## 後ろ剥がし骨格（Isabelle `vg4x_VE34_backpeel`, layerB 95133） -/

/-- **Isabelle `vg4x_VE34_backpeel` (layerB 95133)** の逐語移植。

訂正版体制 `VE34Reg4` 上の `Lng` 強帰納法と二分岐 `VEj1p N ≤ Lng N - 1`
（`VEj1p_lt_vr`）を**無条件**で消化し、VE3/VE4 存在目標 `VE34goal` を
`{VE34Base4, VE34Step4}` の二つ組（RPERS は下で無条件討伐済み）へ還元する。
入口 `VE34_backpeel`（無防備体制）と構造は同一。 -/
theorem VE34_backpeel4 (hBase : VE34Base4) (hStep : VE34Step4)
    (hRpers : ∀ N : PS, VE34Reg4 N → VEj1p N < Lng N - 1 → VE34Reg4 (Pred N))
    (M : PS) (hM : VE34Reg4 M) : VE34goal M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
      subst hn
      have hreg : VE34Reg M := hM.1.1
      have hj1lt : VEj1p M < Lng M := VEj1p_lt_vr M hreg
      by_cases hbase : VEj1p M = Lng M - 1
      · exact hBase M hM hbase
      · have hlt : VEj1p M < Lng M - 1 := by omega
        have hL2 : 1 < Lng M := by omega
        have hregP : VE34Reg4 (Pred M) := hRpers M hM hlt
        have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_vr M hL2
        have hveP : VE34goal (Pred M) :=
          ih (Lng (Pred M)) (by omega) (Pred M) hregP rfl
        exact hStep M hM hlt hregP hveP

/-- 訂正版体制 `VE34Reg4` からの end-to-end 還元（RPERS 無条件討伐済み）。 -/
theorem VE34_of_reg4 (hBase : VE34Base4) (hStep : VE34Step4)
    (M : PS) (hM : VE34Reg4 M) : VE34goal M :=
  VE34_backpeel4 hBase hStep VE34Rpers4_holds M hM

/-- **Isabelle `vg4x_VE34_of_DT` (layerB 95296)** の逐語移植: `DT_PS` ホスト＋ガード
＋非許容境界 `0 < j₀' < TrMax` から VE3/VE4 存在目標を、RPERS 内部消化して鋭い
`{VE34Base4, VE34Step4}` 対に還元する。 -/
theorem VE34_of_DT4 (hBase : VE34Base4) (hStep : VE34Step4)
    (M : PS) (hMD : DTPS M) (hBrne : Br M ≠ [])
    (hguard : entry M 1 (VEj1p M) < entry M 0 (VEj1p M))
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M) :
    VE34goal M := by
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff M).mp hMD
  exact VE34_of_reg4 hBase hStep M ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩

/-! ## BASE 枝の幾何事実（Isabelle `vg4x_base_*`, layerB 95323–95469）

いずれも訂正版体制 `VE34Reg4` の後ろ剥がし基底 `VEj1p N = Lng N - 1`（＝`j₁' = j₁`）
での `Trans` 再帰データを固定し、キーストーン
`m_8_2_subexpr_component_Pred_Adm0_full` を発火させる前座。 -/

/-- **Isabelle `vg4x_base_transJ0` (layerB 95326)**: 基底では最終列の行0直近祖先は
最終 joint：`transJ0 N = j₀'`（`Joints_getD` を `j₁' = Lng N - 1` で使う）。 -/
theorem VE34_base_transJ0 (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) :
    transJ0 N = (Joints N).getD ((Br N).length - 1) 0 := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, _, _⟩ := reg
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hjnt := Joints_getD N ((Br N).length - 1) hJ
  simp only [VEj1p] at hbase
  unfold transJ0 lastParent lastIdx
  rw [hjnt, hbase]

/-- **Isabelle `vg4x_base_nadm` (layerB 95342)**: 最終 joint は `N` 非許容
（`0 < j₀' < TrMax N` は幹の内部）。 -/
theorem VE34_base_nadm (N : PS) (reg : VE34Reg4 N) :
    adm N ((Joints N).getD ((Br N).length - 1) 0) = false := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  exact adm_trunk_interior_nadm_vr N _ hM hj0pos hj0lt

/-- **Isabelle `vg4x_base_Adm0` (layerB 95362)**: 基底では `transJm1 N = 0`
（キーストーンの `Adm0` 枝）。`transJ0 N = j₀' < TrMax N`、`transJm1 = Adm N j₀'` は
許容（`Adm_adm`）かつ `≤ j₀' < TrMax N`（`Adm_le`）、`≤ TrMax N` の許容添字で
`< TrMax N` なのは `0` のみ（`adm_le_TrMax_cases`）。 -/
theorem VE34_base_Adm0 (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) : transJm1 N = 0 := by
  have hreg := reg
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have htj0 : transJ0 N = (Joints N).getD ((Br N).length - 1) 0 :=
    VE34_base_transJ0 N hreg hbase
  have hadmJ : adm N (transJm1 N) = true := by
    unfold transJm1; exact Adm_adm N (transJ0 N)
  have hleJ : transJm1 N ≤ transJ0 N := by
    unfold transJm1; exact Adm_le N (transJ0 N)
  have hjlt : transJm1 N < TrMax N := by rw [htj0] at hleJ; omega
  rcases adm_le_TrMax_cases_vr N (transJm1 N) hM hadmJ (by omega) with h0 | hT
  · exact h0
  · omega

/-- **Isabelle `vg4x_base_j1gt` (layerB 95382)**: 最終列は `1` を超える：
`Lng N - 1 = j₁' > TrMax N > j₀' ≥ 1`、よって `1 < Lng N - 1`。 -/
theorem VE34_base_j1gt (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) : 1 < Lng N - 1 := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hgeom := (FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ).2
  simp only [VEj1p] at hbase
  rw [hbase] at hgeom
  omega

/-- **Isabelle `vg4x_base_notCondA` (layerB 95408)**: 基底は条件(II)/(IV) ホスト
（`¬(I ∨ III ∨ V)`）。(I)/(III) は `adm N j₀'` を要するが偽（`VE34_base_nadm`）。
(V) は `N₁,j₀' + 1 = N₁,j₁` を要するが、`j₀' < TrMax N` は対角幹上
（`RTPS_mono_head_eq` + `trunk_entries_offset`：`N₀,j₀' = N₁,j₀'`）で行0辺 `j₀' → j₁`
は簡約済み（`RedCondA_apply`：`N₀,j₀' + 1 = N₀,j₁`）なので、(V) は `N₀,j₁ = N₁,j₁`
を強制しガード `N₀,j₁' > N₁,j₁'`（`j₁' = j₁`）に矛盾する。 -/
theorem VE34_base_notCondA (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) :
    ¬ (transCondI N = true ∨ transCondIII N = true ∨ transCondV N = true) := by
  have hreg := reg
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have condA : RedCondA N = true := (RTPS_condAB N hR).1
  have hL1 : 1 < Lng N := by
    have := VE34_base_j1gt N hreg hbase; omega
  -- ガード（基底 `j₁' = j₁`）: `entry N 1 (Lng N -1) < entry N 0 (Lng N -1)`
  have hfn : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
    simpa only [VEj1p] using hbase
  have hguardj1 : entry N 1 (Lng N - 1) < entry N 0 (Lng N - 1) := by
    have hg := hguard
    simp only [VEj1p] at hg
    rwa [hfn] at hg
  -- `parent N 0 (Lng N -1) = j₀'`
  have htj0 : transJ0 N = (Joints N).getD ((Br N).length - 1) 0 :=
    VE34_base_transJ0 N hreg hbase
  have hjp_eq : parent N 0 (Lng N - 1) = (Joints N).getD ((Br N).length - 1) 0 := by
    have hpt : transJ0 N = parent N 0 (Lng N - 1) := by
      unfold transJ0 lastParent lastIdx; rfl
    rw [← hpt]; exact htj0
  have hnadm_jp : adm N (parent N 0 (Lng N - 1)) = false := by
    rw [hjp_eq]; exact VE34_base_nadm N hreg
  have hjple : parent N 0 (Lng N - 1) ≤ TrMax N := by rw [hjp_eq]; omega
  -- 対角幹の等式 `N₀,j₀' = N₁,j₀'`
  have hdiag00 : entry N 0 0 = entry N 1 0 := RTPS_mono_head_eq N hR hmono
  have hoff := trunk_entries_offset N hM condA (parent N 0 (Lng N - 1)) hjple
  have hdiagjp :
      entry N 0 (parent N 0 (Lng N - 1)) = entry N 1 (parent N 0 (Lng N - 1)) := by
    obtain ⟨ho0, ho1⟩ := hoff; omega
  -- 簡約済み行0辺 `j₀' → j₁`
  have hp : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hedge : entry N 0 (parent N 0 (Lng N - 1)) + 1 = entry N 0 (Lng N - 1) :=
    RedCondA_apply N condA 0 (Lng N - 1) (by omega) (by omega) hp
  -- 各条件を潰す
  rintro (hI | hIII | hV)
  · -- 条件(I) は `adm N (lastParent N)` を要する
    rw [transCondI] at hI
    simp only [lastParent, lastIdx, hnadm_jp, Bool.and_false] at hI
    exact Bool.false_ne_true hI
  · -- 条件(III) も `adm N (lastParent N)` を要する
    rw [transCondIII] at hIII
    simp only [lastParent, lastIdx, hnadm_jp, Bool.and_false] at hIII
    exact Bool.false_ne_true hIII
  · -- 条件(V) はガードに矛盾する
    rw [transCondV] at hV
    simp only [lastParent, lastIdx, Bool.and_eq_true, beq_iff_eq] at hV
    obtain ⟨⟨_, hmid⟩, _⟩ := hV
    omega

#print axioms VE34Rpers4_holds
#print axioms VE34_backpeel4
#print axioms VE34_of_reg4
#print axioms VE34_of_DT4
#print axioms VE34_base_transJ0
#print axioms VE34_base_nadm
#print axioms VE34_base_Adm0
#print axioms VE34_base_j1gt
#print axioms VE34_base_notCondA

end PSS
