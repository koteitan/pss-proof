import «8».«8.2-condV-terminal-slice-Trans»
import «7».«7.4-Mark-Trans-repr»

/-!
# §8.2 値方程式 `VE` の後ろ剥がし骨格と基点による言い換え

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)の下での終切片と `Trans` の関係）の
  証明中、原文が**省略している**ステップ（L3676–L3708 が空白ブロック）。
  すなわち値方程式
  `VE : bpHeadT (Trans (seg M m (Lng M - 1))) = bpHeadT (Trans M)`。
- 訂正: なし（本ファイルの主張はいずれも Isabelle 側で証明済みの補題の逐語移植）。
- Isabelle:
  - `cfbx_reg` (isabelle/layerB/pss_wip.thy:63208) → `VEReg`
  - `cfbx_j1p` (同 63216) → `VEj1p`
  - `cfbx_VE` (同 63220、abbreviation) → `VEeq`
  - `cfbx_VE_backpeel` (同 63230) → `VE_backpeel`（⚠️ 下記の通り**旧**骨格）
  - `vbax_reg_TrMax_lt` (同 71995) → `VEReg_TrMax_le`
  - `vbax_base_eq` (同 72015) → `VEReg_base_j1p_eq`
  - `vbax_VE_backpeel` (同 72042) → `VE_backpeel_TrMax`（**原文の**骨格。
    `vcx_VE_all` (77076) が使うのはこちら）
  - `cfbx_VE_iff_Mark` (同 63285) → `VE_iff_Mark`
  - `cfbx_Mark0_Trans` (同 63302) → `Mark_index0_Trans`
  - `cfbx_VE_iff_Mark0` (同 63319) → `VE_iff_Mark0`
  - `vbx_base_VE_m0`（`m = 0` の自明枝）→ `VE_index0`
  - Isabelle `a1_FN_lt` (isabelle/pss_mechanized.thy:33186) は Lean では
    `Joints_nextR_FirstNodes` + `nextR_implies_row0` から復元（private `FN_lt_ve`）。
  - **未移植** `a0x_base_VE` (同 75701): 極小基底 `Lng N = TrMax N + 2` の `VE`。
    単一ファイルの射程外であることを確認済み（本ファイルの残差＝次のブリック）。
    実際の閉包は `a0x_base_VE = vbx_base_VE_modAdm0 (74476) [OF reg base
    a0x_base_VE_Adm0 (75453)]` で、
    * `a0x_base_VE_Adm0` は **IH 無しではない**：内部で
      `baseIH = vbax_base_baseIH[OF reg eq base]` を引く（⚠️ 72040 の注記
      「baseIH は不要」は `vbax_VE_backpeel` の STEP 領域についての話であって、
      `a0x_base_VE_Adm0` の内部構造の話ではない。混同するな）。
    * `vbx_base_VE_modAdm0` は非 `Adm0` 枝で `vbx_base_transJm1_zero_or_TrMax`
      (74487) を要する。
    * さらに `a0x_bpHeadT_transC2_eq` (75168) / `Trans_eq_transC2_Adm0` (19356) /
      `bpax_Trans_PredN_leR` / `bihx_base_mint` / `bihx_base_lerB` を要する。
    Lean 側に**双子が無い**依存（要新規移植）: `m_6_5_Lng_Red` (`Lng_Red`)、
    `m_7_4_Pred_Red_slice` (`Pred_Red_slice`)、`monoT_seg_of_le0`、
    `Trans_eq_transC2_Adm0` の公開形（`8.2-subexpr-adm0-cores` の
    `adm0_setup_sc` は private で clause 固有）。
    双子が**有る**依存: `Trans_Red` (7.3)、`seg_Pred_eq` (7.4)、
    `ancestor_slice_Red_IncrFirst` (6.6)、`Red_preserves_monoT` (6.5)、
    `mono_hasParent_row0` (6.6)。
- 依存: `8.2-condV-terminal-slice-Trans`（`condV_terminal_slice_Trans_modVE` の
  仮定 `hVE` がここでの `VEeq`。`descendingB`/`DTPS` 語彙もここから推移的に入る）、
  `7.4-Mark-Trans-repr`（`Mark_Trans_repr`）。
- 方針: Isabelle と同じ骨格。`VE_backpeel_TrMax` は `Lng` に関する強帰納法＋
  二分岐 `Lng N = TrMax N + 2` / `TrMax N + 2 < Lng N` を消化し、`VE` の残差を
  {BASE, STEP, RPERS} の 3 本に落とす。
  `VE_iff_Mark0` は `Mark_Trans_repr`（§7.4）で切片 `Trans` を `Mark` に読み替え、
  `VE` を「`Mark` の深部末尾の `m` 非依存性」に変換する。
  ⚠️ この言い換えは `adm M m`（`Marked M m`）が要る枝でのみ有効。
  regime 内の非許容 `m` では切片は `Mark` の像ではない
  （Isabelle の注記＝`python/_r19_cfb_bpeel.py`: MARKREFR は ADM とちょうど一致、
  133/291 + 41/203）。したがって `VE_iff_Mark0` は `VE` を**閉じない**。
- 数値検証: `VEReg`/`VEj1p` の転記は `python/_r19_cfb_bpeel.py` の `regime` と
  `#guard` 7 本で照合（`diagSeq` を `oper` で閉じた本物の標準形プール）。
  `VEReg_TrMax_le` は 203 例・`VEReg_base_j1p_eq` は 21 例で反例 0。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`VE` 本体（Isabelle `vcx_VE_all`, 77076）は**未達**。
  本ファイルが提供するのは骨格・体制の構造補題・基点言い換えのみで、
  残差は `VE_backpeel_TrMax` の 3 仮定 {BASE, STEP, RPERS}。
  次のブリック = BASE（Isabelle `a0x_base_VE`, 75701。上記の依存表を見よ）。
-/

namespace PSS

/-! ## 定義（Isabelle `cfbx_reg` / `cfbx_j1p` / `cfbx_VE` の逐語移植） -/

/-- Isabelle `cfbx_j1p` (layerB 63216): 最終枝の左端。 -/
def VEj1p (N : PS) : ℕ := (FirstNodes N).getD ((Br N).length - 1) 0

/-- Isabelle `cfbx_reg` (layerB 63208): 後ろ剥がし帰納法の体制（regime）。

Isabelle の `N ∈ RT_PS ∧ N ∈ PT_PS ∧ Br N ≠ [] ∧ …` に対応する。
`PT_PS = {M. M ∈ T_PS ∧ monoT M}` のうち `T_PS` の連言は `RT_PS` から
（`RTPS_TPS`）従うので、ここでは `RTPS N ∧ monoT N` と書く（同値）。 -/
def VEReg (m : ℕ) (N : PS) : Prop :=
  RTPS N ∧ monoT N = true ∧ Br N ≠ [] ∧
    (m < (Joints N).getD ((Br N).length - 1) 0 ∨
      (m = (Joints N).getD ((Br N).length - 1) 0 ∧
        entry N 0 (VEj1p N) = entry N 1 (VEj1p N) ∧
        descendingB (Br N) = true))

instance (m : ℕ) (N : PS) : Decidable (VEReg m N) := by
  unfold VEReg RTPS; infer_instance

/-- Isabelle `cfbx_VE` (layerB 63220): 値方程式そのもの。 -/
def VEeq (m : ℕ) (N : PS) : Prop :=
  bpHeadT (Trans (seg N m (Lng N - 1))) = bpHeadT (Trans N)

/-! ### 転記の数値検証（`python/_r19_cfb_bpeel.py` の `regime`/`FirstNodes` と照合）

以下のホストは `diagSeq` を `oper` で閉じた**本物の標準形プール**から取った
（`Lng = TrMax + 2` の極小基底ホスト）。`regime` の判定と `VEReg` の
`decide` が一致することを確認する。 -/

-- `M = (0,0)(1,1)(2,1)`: TrMax = 1, Lng = 3 = TrMax + 2, FirstNodes = [2,3],
-- Joints = [1]。python: regime ms = [0]。
#guard VEj1p [(0,0),(1,1),(2,1)] = 2
#guard decide (VEReg 0 [(0,0),(1,1),(2,1)]) = true
#guard decide (VEReg 1 [(0,0),(1,1),(2,1)]) = false

-- `M = (0,0)(1,1)(2,2)(3,2)`: TrMax = 2, Lng = 4 = TrMax + 2, FirstNodes = [3,4],
-- Joints = [2]。python: regime ms = [0,1]。
#guard VEj1p [(0,0),(1,1),(2,2),(3,2)] = 3
#guard decide (VEReg 0 [(0,0),(1,1),(2,2),(3,2)]) = true
#guard decide (VEReg 1 [(0,0),(1,1),(2,2),(3,2)]) = true
#guard decide (VEReg 2 [(0,0),(1,1),(2,2),(3,2)]) = false

/-! ## 私的補助（suffix `_ve`） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（Isabelle では `le0` の
定義から直接）。 -/
private theorem leR0_bounds_ve (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- Isabelle `adm_index0`: `0` は常に許容（`nadm` の両枝が `j = 0` で潰れる）。 -/
private theorem adm_index0_ve (M : PS) : adm M 0 = true := by
  simp only [adm, nadm, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff]
  refine ⟨by simp, ?_⟩
  left
  simp only [nextR, if_neg (by decide : ¬(1 = 0))]
  simp [nextrel1]

/-- Isabelle `a1_FN_lt` (pss_mechanized 33186): 枝の左端は `Lng` 未満。 -/
private theorem FN_lt_ve (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_ve M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制の下で `VEj1p N < Lng N`。 -/
private theorem VEj1p_lt_ve (m : ℕ) (N : PS) (hreg : VEReg m N) :
    VEj1p N < Lng N := by
  obtain ⟨hR, hmono, hBrne, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_ve N _ hM hmono hJ

/-- `Lng (Pred N) = Lng N - 1`（`1 < Lng N` のとき）。 -/
private theorem Lng_Pred_ve (N : PS) (h : 1 < Lng N) :
    Lng (Pred N) = Lng N - 1 := by
  have hle : ¬ (Lng N ≤ 1) := by omega
  simp [Pred, hle, Lng]

/-! ## 後ろ剥がし帰納法の骨格（Isabelle `cfbx_VE_backpeel`, 63230） -/

/-- Isabelle `cfbx_VE_backpeel` (layerB 63230)。

`BASE` = `j₁' = j₁` の枝（最終枝の右端が最終列。原文はここで `m = j₀'` を強制する）、
`STEP` = `j₁' < j₁` の帰納枝（IH `VE'(Pred N)` を消費）、
`RPERS` = `j₁' < j₁` の場合に体制が `Pred N` へ遺伝すること。

`Lng` に関する強帰納法と二分岐 `j₁' ≤ j₁`（`VEj1p_lt_ve`）はここで消化される。 -/
theorem VE_backpeel (m : ℕ)
    (BASE : ∀ N : PS, VEReg m N → VEj1p N = Lng N - 1 → VEeq m N)
    (STEP : ∀ N : PS, VEReg m N → VEj1p N < Lng N - 1 →
      VEReg m (Pred N) → VEeq m (Pred N) → VEeq m N)
    (RPERS : ∀ N : PS, VEReg m N → VEj1p N < Lng N - 1 → VEReg m (Pred N))
    (M : PS) (hM : VEReg m M) : VEeq m M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
      subst hn
      have hj1lt : VEj1p M < Lng M := VEj1p_lt_ve m M hM
      by_cases hbase : VEj1p M = Lng M - 1
      · exact BASE M hM hbase
      · have hlt : VEj1p M < Lng M - 1 := by omega
        have hL2 : 1 < Lng M := by omega
        have hregP : VEReg m (Pred M) := RPERS M hM hlt
        have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_ve M hL2
        have hveP : VEeq m (Pred M) :=
          ih (Lng (Pred M)) (by omega) (Pred M) hregP rfl
        exact STEP M hM hlt hregP hveP

/-! ## 原文の帰納法の骨格（Isabelle `vbax_VE_backpeel`, 72042）

⚠️ Isabelle の注記（72030–72040）によれば、上の `VE_backpeel`
（＝`cfbx_VE_backpeel`, 63230）の `j₁' = j₁` 基底は**原文の帰納法ではない**：
真の基底（`j₁ - TrMax = 1`、151/151 のホスト）と稀な非極小 `j₁' = j₁ ∧ j₁ - TrMax > 1`
ホスト（3 件）を混同しており、そのために不要な `baseIH` を強いる。
原文（LaTeX 4922「…を `j₁ - TrMax(M)` に関する数学的帰納法で示す」）の帰納法は
`Lng N = TrMax N + 2` で底を打つ下記の形であり、`vcx_VE_all` (77076) が使うのも
こちらである。以後の移植はこの骨格に接続すること。 -/

/-- Isabelle `vbax_reg_TrMax_lt` (layerB 71995): 体制の下で `TrMax N + 2 ≤ Lng N`。 -/
theorem VEReg_TrMax_le (m : ℕ) (N : PS) (hreg : VEReg m N) :
    TrMax N + 2 ≤ Lng N := by
  obtain ⟨hR, hmono, hBrne, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hgeom := (FirstNodes_TrMax_Joints N _ hM hmono hJ).2
  have hfnlt := FN_lt_ve N _ hM hmono hJ
  omega

/-- Isabelle `vbax_base_eq` (layerB 72015): 極小基底 `Lng N = TrMax N + 2` では
最終枝の左端は最終列：`VEj1p N = Lng N - 1`。 -/
theorem VEReg_base_j1p_eq (m : ℕ) (N : PS) (hreg : VEReg m N)
    (hbase : Lng N = TrMax N + 2) : VEj1p N = Lng N - 1 := by
  obtain ⟨hR, hmono, hBrne, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hgeom := (FirstNodes_TrMax_Joints N _ hM hmono hJ).2
  have hfnlt := FN_lt_ve N _ hM hmono hJ
  unfold VEj1p
  omega

/-- Isabelle `vbax_VE_backpeel` (layerB 72042): **原文の**後ろ剥がし帰納法。

`BASE` = `j₁ - TrMax = 1`（`Lng N = TrMax N + 2`）の IH 無し極小基底、
`STEP`/`RPERS` = 再帰領域 `TrMax N + 2 < Lng N`（`j₁' = j₁` と `j₁' < j₁` の
両方を一様に覆う）。 -/
theorem VE_backpeel_TrMax (m : ℕ)
    (BASE : ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → VEeq m N)
    (STEP : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N →
      VEReg m (Pred N) → VEeq m (Pred N) → VEeq m N)
    (RPERS : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N → VEReg m (Pred N))
    (M : PS) (hM : VEReg m M) : VEeq m M := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
      subst hn
      have hge : TrMax M + 2 ≤ Lng M := VEReg_TrMax_le m M hM
      by_cases hbase : Lng M = TrMax M + 2
      · exact BASE M hM hbase
      · have hlt : TrMax M + 2 < Lng M := by omega
        have hL2 : 1 < Lng M := by omega
        have hregP : VEReg m (Pred M) := RPERS M hM hlt
        have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_ve M hL2
        have hveP : VEeq m (Pred M) :=
          ih (Lng (Pred M)) (by omega) (Pred M) hregP rfl
        exact STEP M hM hlt hregP hveP

/-! ## `m = 0` の自明枝（Isabelle `vbx_base_VE_m0`） -/

/-- `seg N 0 (Lng N - 1) = N`（`N ≠ []`）。 -/
private theorem seg0_self_ve (N : PS) (hne : N ≠ []) :
    seg N 0 (Lng N - 1) = N := by
  have hL : 0 < Lng N := by
    cases N with
    | nil => exact absurd rfl hne
    | cons a t => simp [Lng]
  rw [seg_eq_take_drop_adm N 0 (Lng N - 1) (Nat.zero_le _) (by omega)]
  have hlast : Lng N - 1 + 1 - 0 = Lng N := by omega
  simp [hlast, Lng]

/-- Isabelle `vbx_base_VE_m0`: `m = 0` では `VE` は無条件（切片が `N` 自身）。 -/
theorem VE_index0 (N : PS) (hne : N ≠ []) : VEeq 0 N := by
  unfold VEeq
  rw [seg0_self_ve N hne]

/-! ## 基点による言い換え（Isabelle `cfbx_VE_iff_Mark` / `cfbx_Mark0_Trans` /
`cfbx_VE_iff_Mark0`） -/

/-- Isabelle `cfbx_VE_iff_Mark` (layerB 63285): `m` が許容（`Marked M m`）なら
§7.4 の `Mark_Trans_repr` が切片 `Trans` を `Mark M m` と同定するので、`VE` は
`Mark` 対 `Trans` の深部末尾の同一性になる。 -/
theorem VE_iff_Mark (M : PS) (m : ℕ) (hR : RTPS M) (hmk : Marked M m)
    (hlt : m < Lng M - 1) :
    VEeq m M ↔ bpHeadT (Mark M m) = bpHeadT (Trans M) := by
  unfold VEeq
  rw [Mark_Trans_repr M m hmk hR hlt]

/-- Isabelle `cfbx_Mark0_Trans` (layerB 63302): 左端の自明な基点は `Trans` を返す：
`Mark M 0 = Trans M`。

`Marked M 0` は単項簡約ホストでは無条件（許容性は `adm M 0`、`leR` の連言は
`monoT` の定義節そのもの）。 -/
theorem Mark_index0_Trans (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) : Mark M 0 = Trans M := by
  have hM : TPS M := RTPS_TPS M hR
  have hleR0 : leR M 0 0 (Lng M - 1) = true := by
    simp only [monoT, Bool.and_eq_true] at hmono
    exact hmono.2
  have hmk : Marked M 0 := ⟨hM, adm_index0_ve M, hleR0⟩
  have hne : M ≠ [] := by
    cases M with
    | nil => simp [Lng] at hL
    | cons a t => simp
  rw [Mark_Trans_repr M 0 hmk hR (by omega), seg0_self_ve M hne]

/-- Isabelle `cfbx_VE_iff_Mark0` (layerB 63319): 許容 `m` に対する `VE` は
`Mark` の深部末尾の `m` 非依存性そのもの。 -/
theorem VE_iff_Mark0 (M : PS) (m : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hmk : Marked M m) (hlt : m < Lng M - 1) :
    VEeq m M ↔ bpHeadT (Mark M m) = bpHeadT (Mark M 0) := by
  have hL : 1 < Lng M := by omega
  rw [Mark_index0_Trans M hR hmono hL]
  exact VE_iff_Mark M m hR hmk hlt

#print axioms VE_backpeel
#print axioms VEReg_TrMax_le
#print axioms VEReg_base_j1p_eq
#print axioms VE_backpeel_TrMax
#print axioms VE_index0
#print axioms VE_iff_Mark
#print axioms Mark_index0_Trans
#print axioms VE_iff_Mark0

end PSS
