import «8».«8.2-condV-VE-base»

/-!
# §8.2 値方程式 `VE` の後ろ剥がし帰納法 STEP／RPERS ディスパッチャ

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)下の終切片と `Trans` の関係）の
  証明中、原文が **省略している** 値方程式
  `VE : bpHeadT (Trans (seg N m (Lng N - 1))) = bpHeadT (Trans N)` の後ろ剥がし帰納法。
  原文 LaTeX 4922「…を `j₁ - TrMax(M)` に関する数学的帰納法で示す」の帰納法。
- 訂正: なし（本ファイルの主張はいずれも Isabelle 側で証明済みの補題の逐語移植）。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `vsx_VE_step_m0` (74144) → `vsx_VE_step_m0`
  - `vsx_VE_step` (74162) → `vsx_VE_step`
  - `vsx_RPERS` (74204) → `vsx_RPERS`
  - `vsx_terminal_slice_modResidualC` (74260) / `vcx_VE_all` (77076) の骨格
    → `vsx_VE_all_modResidual`
  - 露出する深部ブリック（本ファイルの残差、named Props として公開）:
    * `bpax_VE_step` (65663、六つの surgery discharger `six_lerR`(68371)
      `six_id2R`(68396) `six_id3R`(68402) `six_tneR`(68200) `six_intMR`(68225)
      `six_intNR`(68247) を **適用済み** の形) → `BpaxVEstep`
    * `bpax_RPERS` (65860) → `BpaxRPERS`
    * `vcx_VEj1eq` (77061、下層 `vjx_VEj1eq` + `vcx_collapse_VE`) → `VEj1eqResidual`
    * `vjx_RPj1eq` (74726) → `RPj1eqResidual`
    * `a0x_base_VE` (75701、極小基底 `Lng N = TrMax N + 2` の `VE`) → 本ファイルでは
      `vsx_VE_all_modResidual` の `BASE` 仮引数として露出。
- 依存: `8.2-condV-VE-base`（`VEReg`/`VEeq`/`VEj1p`/`VE_backpeel_TrMax`/`VE_index0`）。
  `Joints_nextR_FirstNodes`(6.5)、`nextR_implies_row0`(6.2)、`RTPS_TPS` は推移的に入る。
- 方針: Isabelle と同じディスパッチ。再帰領域 `TrMax N + 2 < Lng N` を
  `VEj1p N = Lng N - 1`（`j₁' = j₁`）／`VEj1p N < Lng N - 1`（`j₁' < j₁`）で二分岐する。
  * `j₁' < j₁`（最終列が新しい枝を開く）: `bpax_VE_step`/`bpax_RPERS` の領域。
  * `m = 0`: 切片は `N` 全体なので `VE` は反射（`VE_index0`）。
  * `j₁' = j₁` ∧ `m > 0`（最終枝が単一列）: 稀な残差 `VEj1eq`/`RPj1eq`。
    経験的に真だが surgery が退化するため専用議論を要する（Isabelle 74144-74162 の
    section note 参照。python/_r25_vestep*.py, _r26_vjx.py）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`vsx_VE_step`/`vsx_RPERS`/`vsx_VE_all_modResidual`
  は緑。`VE` 本体（Isabelle `vcx_VE_all`, 77076）は残差 5 本
  {`BpaxVEstep`, `VEj1eqResidual`, `BpaxRPERS`, `RPj1eqResidual`, `BASE`(=`a0x_base_VE`)}
  modulo で提供する。深部 surgery（`bpax_VE_step`/`bpax_RPERS`）と `j₁'=j₁` 残差
  （`vcx_VEj1eq`/`vjx_RPj1eq`）は本ファイルの射程外＝次のブリック。
-/

namespace PSS

/-! ## 露出する残差 Props（Isabelle の深部ブリックの型） -/

/-- Isabelle `bpax_VE_step` (layerB 65663) の、六つの surgery discharger
`six_lerR`/`six_id2R`/`six_id3R`/`six_tneR`/`six_intMR`/`six_intNR`
(68371/68396/68402/68200/68225/68247) を **適用済み** の形。
`j₁' < j₁`（`VEj1p N < Lng N - 1`）の再帰領域での STEP。 -/
def BpaxVEstep (m : ℕ) : Prop :=
  ∀ N : PS, VEReg m N → VEj1p N < Lng N - 1 →
    VEReg m (Pred N) → VEeq m (Pred N) → VEeq m N

/-- Isabelle `bpax_RPERS` (layerB 65860): `j₁' < j₁` の領域で体制が `Pred N` に遺伝。 -/
def BpaxRPERS (m : ℕ) : Prop :=
  ∀ N : PS, VEReg m N → VEj1p N < Lng N - 1 → VEReg m (Pred N)

/-- Isabelle `vcx_VEj1eq` (layerB 77061): `j₁' = j₁` ∧ `m > 0` の STEP 残差。 -/
def VEj1eqResidual (m : ℕ) : Prop :=
  ∀ Q : PS, VEReg m Q → VEj1p Q = Lng Q - 1 → TrMax Q + 2 < Lng Q →
    VEReg m (Pred Q) → VEeq m (Pred Q) → 0 < m → VEeq m Q

/-- Isabelle `vjx_RPj1eq` (layerB 74726): `j₁' = j₁` の体制遺伝残差。 -/
def RPj1eqResidual (m : ℕ) : Prop :=
  ∀ Q : PS, VEReg m Q → VEj1p Q = Lng Q - 1 → TrMax Q + 2 < Lng Q → VEReg m (Pred Q)

/-! ## 私的補助（suffix `_vs`、`8.2-condV-VE-base` の private 補題の再導出） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める。 -/
private theorem leR0_bounds_vs (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- Isabelle `a1_FN_lt`: 枝の左端は `Lng` 未満。 -/
private theorem FN_lt_vs (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_vs M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- 体制の下で `VEj1p N < Lng N`。 -/
private theorem VEj1p_lt_vs (m : ℕ) (N : PS) (hreg : VEReg m N) :
    VEj1p N < Lng N := by
  obtain ⟨hR, hmono, hBrne, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  exact FN_lt_vs N _ hM hmono hJ

/-- `TrMax N + 2 < Lng N` から `N ≠ []`。 -/
private theorem ne_nil_of_TrMax_lt_vs (N : PS) (lt : TrMax N + 2 < Lng N) :
    N ≠ [] := by
  have h0 : 0 < Lng N := by omega
  intro h; rw [h] at h0; simp [Lng] at h0

/-! ## `m = 0` の自明枝（Isabelle `vsx_VE_step_m0`, 74144） -/

/-- Isabelle `vsx_VE_step_m0` (layerB 74144): `m = 0` では終切片は `N` 全体なので
`VE` は `bpHeadT (Trans N)` の反射。 -/
theorem vsx_VE_step_m0 (N : PS) (lt : TrMax N + 2 < Lng N) : VEeq 0 N :=
  VE_index0 N (ne_nil_of_TrMax_lt_vs N lt)

/-! ## STEP ディスパッチャ（Isabelle `vsx_VE_step`, 74162） -/

/-- Isabelle `vsx_VE_step` (layerB 74162): 再帰領域 `TrMax N + 2 < Lng N` で
`VE m (Pred N)` から `VE m N` を導く STEP。`j₁' < j₁` は `bpax_VE_step`
(surgery 適用済み `BpaxVEstep`)、`m = 0` は切片同一性、`j₁' = j₁ ∧ m > 0` は
残差 `VEj1eqResidual` に落ちる。 -/
theorem vsx_VE_step (m : ℕ) (hstep : BpaxVEstep m) (hj1 : VEj1eqResidual m)
    (N : PS) (reg : VEReg m N) (lt : TrMax N + 2 < Lng N)
    (regP : VEReg m (Pred N)) (IH : VEeq m (Pred N)) : VEeq m N := by
  by_cases hjeq : VEj1p N = Lng N - 1
  · -- `j₁' = j₁`
    by_cases hm0 : m = 0
    · -- 自明枝: 切片は `N` 全体
      subst hm0
      exact VE_index0 N (ne_nil_of_TrMax_lt_vs N lt)
    · -- 稀な残差
      exact hj1 N reg hjeq lt regP IH (Nat.pos_of_ne_zero hm0)
  · -- `j₁' < j₁`: surgery 領域
    have hj1lt : VEj1p N < Lng N := VEj1p_lt_vs m N reg
    have hL1 : 1 < Lng N := by omega
    have hltj : VEj1p N < Lng N - 1 := by omega
    exact hstep N reg hltj regP IH

/-! ## RPERS ディスパッチャ（Isabelle `vsx_RPERS`, 74204） -/

/-- Isabelle `vsx_RPERS` (layerB 74204): 再帰領域で体制が `Pred N` に遺伝する。
`j₁' < j₁` は `bpax_RPERS`(`BpaxRPERS`)、`j₁' = j₁` は残差 `RPj1eqResidual`。 -/
theorem vsx_RPERS (m : ℕ) (hrp : BpaxRPERS m) (hj1 : RPj1eqResidual m)
    (N : PS) (reg : VEReg m N) (lt : TrMax N + 2 < Lng N) : VEReg m (Pred N) := by
  by_cases hjeq : VEj1p N = Lng N - 1
  · exact hj1 N reg hjeq lt
  · have hj1lt : VEj1p N < Lng N := VEj1p_lt_vs m N reg
    have hL1 : 1 < Lng N := by omega
    have hltj : VEj1p N < Lng N - 1 := by omega
    exact hrp N reg hltj

/-! ## キャップストーン（Isabelle `vcx_VE_all`, 77076 の骨格） -/

/-- 値方程式 `VE` を、後ろ剥がし帰納法（`VE_backpeel_TrMax`）と本ファイルの
STEP／RPERS ディスパッチャで、残差 5 本
{`BASE`(=Isabelle `a0x_base_VE`, 75701), `BpaxVEstep`, `VEj1eqResidual`,
`BpaxRPERS`, `RPj1eqResidual`} modulo に還元する。

Isabelle `vcx_VE_all` は同じ組み立てで、5 本すべてを無条件に閉じている。 -/
theorem vsx_VE_all_modResidual (m : ℕ)
    (BASE : ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → VEeq m N)
    (hstepBpax : BpaxVEstep m) (hstepJ1 : VEj1eqResidual m)
    (hrpBpax : BpaxRPERS m) (hrpJ1 : RPj1eqResidual m)
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  VE_backpeel_TrMax m BASE
    (vsx_VE_step m hstepBpax hstepJ1)
    (vsx_RPERS m hrpBpax hrpJ1)
    M hM

#print axioms vsx_VE_step_m0
#print axioms vsx_VE_step
#print axioms vsx_RPERS
#print axioms vsx_VE_all_modResidual

end PSS
