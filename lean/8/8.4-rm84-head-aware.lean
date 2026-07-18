import «8».«8.4-rightmost-exists»

/-!
# §8.4 補題（右端置き換えと `Trans`）存在部 `Rightmost84ReplaceExists` の HEAD-AWARE 還元

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は **DEFERRED**。
- 攻略対象: `«8».«8.4-rightmost-replace-close»` の存在部フィールド
  `rm84Exists : Rightmost84ReplaceExists`（同ファイル :43）。

## 背景（既存の 2 route が機械反証済み）

- 旧 c2hole transport（`8.4-c2hole-transport`, `C2HoleSliceTransport_ch`）は **偽**。
  条件(III)/(IV) では実際の `Trans (s84x_Np M)` は
  `Dprin (entry M 1 (s84x_jm2 M)) (transC2 M)` — c2hole エンジンの scb 文字列に
  対して **余分な外側 principal `D_{M₁,j₋₂}` が 1 段付く**。エンジンの `(s,b)` は
  この頭を持たないので transport の結論（共有 `(s,b)` の継承）が破綻する。
- 旧値リードバック（`8.4-rightmost-exists`, `rr84_shared_of_readback`）は
  `Trans (N') = D_V (T2 +_B D_β 0)` / `Trans (L') = D_V (T2 +_B D_γ 0)` の
  T2 閉形式を仮定するが、この形は条件(IV) の**入れ子**（`Trans` が multi 分岐に落ちる、
  例 `hostM30_rr` の `Trans = Dprin 0 (Σ …)` は multi-principal）で崩れ大域的に偽。

## 本ファイルの HEAD-AWARE 還元（正しい形）

反証が指す正しい形は、**外側に頭 `D_{M₁,j₋₂}` を露出したまま**、内側 `t`/`t'` を
共有 scb 文脈 `(s0,b0)` で分解する self-similar readback である。

`N' = s84x_Np M`、`L' = rrLp M = s84x_Lp M` は最終列の行1成分だけ（`β = M₁,j₁` vs
`γ = M₁,j₋₂`）で異なり、行0成分と前置切片 `Pred N' = Pred L'` を共有する。したがって
* `Trans (N') = D_γ t`（`t` は `D_β 0` を中心 `(s0,b0)` で分解）
* `Trans (L') = D_γ t'`（`t'` は `D_γ 0` を中心・**同一** `(s0,b0)` で分解）
の形で結べれば、外側 `D_γ` を `scb_compose_dprin` で被せて共有文脈
`(dsym γ :: s0, b0)` を得る（本ファイルの `rightmost84ReplaceExists_of_headShared`）。
この形は multi-principal でも崩れない（`t`/`t'` は任意 BT でよい）ため、旧 T2 形の
反証を回避する。残差 = 頭付き値リードバック `Rm84HeadShared`。

- 依存（ビルド済み・committed at main 44ce106）: «8».«8.4-rightmost-exists»
  （`Rightmost84ReplaceExists`/`s84x_Np`/`rrLp`/`s84x_jm2`/`rr84_shared_of_readback`/
  `Trans`/`STPS`/`monoT`/`hasParent`/`Lng`/`entry`/`Dprin`/`BZero`/`scb_decomp`/
  `isPTB_str`/`flatBT`/`Sym`/`rightmost84ReplaceCorrected_of_exists`）、推移的に
  «7».«7.2-scb-compose»（`scb_compose_dprin`）。 c2hole エンジン
  （`8.4-c2hole-engine`）は本ファイルの assembly では不要（`scb_compose_dprin` のみ）。
- 数値検証: `python/trans_model.py`。`hostM30_rr = (0,0)(1,1)(2,2)(2,1)`（条件(IV)）で
  `Trans (N') = Dprin 0 Y`, `Trans (L') = Dprin 0 Y'`、`Y`/`Y'` は最内 principal
  `D_1 0`/`D_0 0` だけで異なる multi-principal 項（`Y` は `(D_2 0, D_1 (D_2 0, D_1 0))`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  HEAD-AWARE 還元 `Rm84HeadShared → Rightmost84ReplaceExists` は無条件。
- Private suffix: `_ha`。
-/

namespace PSS

/-! ## 0. `Dprin`-of-nat 中心の `isPTB_str`（`8.4-rightmost-exists` の private の再掲） -/

private theorem dprin_isPTB_str_ha (v : ℕ∞) (hv : v ≠ ⊤) :
    isPTB_str (flatBT (Dprin v BZero)) := by
  have hbne : (v != ⊤) = true := bne_iff_ne.mpr hv
  refine ⟨.db v BZero, ?_, ?_⟩
  · simp [dfree_BP, BZero, dfree_BT, dfree_BPList, hbne]
  · simp [Dprin, flatBT]

/-! ## 1. HEAD-AWARE 値リードバック残差（正しい形） -/

/-- **頭付き共有リードバック残差**。各 `M`（標準形・単項・`hasParent M 1 j₁`・
`j₋₂+1 < j₁`）に対し、`Trans (N')` / `Trans (L')` がともに外側頭 `D_γ`（`γ = M₁,j₋₂`）
を持ち、その内側 `t`/`t'` が最内 principal `D_β 0`（`β = M₁,j₁`）/ `D_γ 0` だけで異なる
**共有 scb 文脈** `(s0,b0)` を持つ。旧 T2 形（条件(IV) で偽）と違い `t`/`t'` は任意 BT で
よいので multi-principal でも成立する（正しい head-aware 形）。 -/
def Rm84HeadShared : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
    ∃ (t t' : BT) (s0 b0 : List Sym),
      Trans (s84x_Np M) = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) t ∧
      Trans (rrLp M) = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) t' ∧
      scb_decomp t s0 (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) b0 ∧
      scb_decomp t' s0 (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) b0

/-! ## 2. 還元：頭付き共有リードバック残差 ⟹ 存在部 `Rightmost84ReplaceExists`

外側頭 `D_γ` を両分解に `scb_compose_dprin` で被せ、共有文脈を
`(dsym γ :: s0, b0)` に伸ばす。純 scb 代数のみ。 -/
theorem rightmost84ReplaceExists_of_headShared
    (h : Rm84HeadShared) : Rightmost84ReplaceExists := by
  intro M hST hmono hp hrng
  obtain ⟨t, t', s0, b0, hNp, hLp, hdt, hdt'⟩ := h M hST hmono hp hrng
  set γ : ℕ∞ := (entry M 1 (s84x_jm2 M) : ℕ∞) with hγ
  have hγne : γ ≠ ⊤ := by simp [hγ]
  have hβstr : isPTB_str (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) :=
    dprin_isPTB_str_ha _ (by simp)
  have hγstr : isPTB_str (flatBT (Dprin γ BZero)) :=
    dprin_isPTB_str_ha γ hγne
  refine ⟨(Sym.dsym γ :: s0, b0), ?_, ?_⟩
  · rw [hNp]
    exact scb_compose_dprin γ t s0
      (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) b0 hdt hβstr
  · rw [hLp]
    exact scb_compose_dprin γ t' s0 (flatBT (Dprin γ BZero)) b0 hdt' hγstr

/-- 訂正 A30 形 `Rightmost84ReplaceCorrected` への合成。 -/
theorem rightmost84ReplaceCorrected_of_headShared
    (h : Rm84HeadShared) : Rightmost84ReplaceCorrected :=
  rightmost84ReplaceCorrected_of_exists (rightmost84ReplaceExists_of_headShared h)

/-! ## 3. 非空虚性（`Rm84HeadShared` が条件(IV) host で充足可能）

旧 c2hole transport フィールド（`C2HoleSliceTransport_ch`）は **充足不能**だったため
即日撤回された。本 `Rm84HeadShared` はそれと異なり、条件(IV) の multi-principal host
`hostM30_rr = (0,0)(1,1)(2,2)(2,1)`（`s84x_jm2 = 0`, `s84x_Np = M`, `Trans = Dprin 0 Y`）
で実際に witness を持つ。`Y`/`Y'` は最内 principal `D_β 0`（β=1）/ `D_γ 0`（γ=0）だけで
異なり、共有文脈 `(s0_ha, b0_ha)` で同時に分解される。 -/

/-- `Trans (s84x_Np hostM30_rr)` の頭 `D_0` を剥がした内側項。 -/
def Y_ha : BT :=
  BT.trm [BP.db (2 : ℕ∞) BZero,
    BP.db (1 : ℕ∞) (BT.trm [BP.db (2 : ℕ∞) BZero, BP.db (1 : ℕ∞) BZero])]

/-- `Trans (rrLp hostM30_rr)` の頭 `D_0` を剥がした内側項（最内が `D_0 0`）。 -/
def Yp_ha : BT :=
  BT.trm [BP.db (2 : ℕ∞) BZero,
    BP.db (1 : ℕ∞) (BT.trm [BP.db (2 : ℕ∞) BZero, BP.db (0 : ℕ∞) BZero])]

/-- `Y`/`Y'` の共有 scb 前置文字列。 -/
def s0_ha : List Sym :=
  [Sym.lp, Sym.dsym (2 : ℕ∞), Sym.zero, Sym.cm,
   Sym.dsym (1 : ℕ∞), Sym.lp, Sym.dsym (2 : ℕ∞), Sym.zero, Sym.cm]

/-- `Y`/`Y'` の共有 scb 後置文字列。 -/
def b0_ha : List Sym := [Sym.rp, Sym.rp]

/-- **`Rm84HeadShared` は空虚でない**: 条件(IV) host `hostM30_rr` の頭付き共有
リードバックを明示 witness で満たす。 -/
theorem rm84HeadShared_nonvacuous_ha :
    Trans (s84x_Np hostM30_rr)
        = Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) Y_ha ∧
    Trans (rrLp hostM30_rr)
        = Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) Yp_ha ∧
    scb_decomp Y_ha s0_ha
        (flatBT (Dprin (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero)) b0_ha ∧
    scb_decomp Yp_ha s0_ha
        (flatBT (Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero)) b0_ha := by
  refine ⟨flatBT_injective (by decide), flatBT_injective (by decide),
    ⟨by decide, ?_, ?_⟩, ⟨by decide, ?_, ?_⟩⟩
  · intro _
    exact ⟨BP.db (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero, by decide, by decide⟩
  · intro x hx; fin_cases hx <;> rfl
  · intro _
    exact ⟨BP.db (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero, by decide, by decide⟩
  · intro x hx; fin_cases hx <;> rfl

#print axioms rightmost84ReplaceExists_of_headShared
#print axioms rightmost84ReplaceCorrected_of_headShared
#print axioms rm84HeadShared_nonvacuous_ha

end PSS
