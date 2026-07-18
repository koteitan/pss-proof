import «8».«8.4-rightmost-exists»
import «8».«8.4-c2hole-engine»

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

## scb 組立の無条件 discharge（本 wave の前進）

`Rm84HeadShared` の 4 部（値 2 本 ＋ scb 分解 2 本）のうち **scb 分解 2 本は無条件で
discharge 済**。核は、`Trans (s84x_Np M)` / `Trans (rrLp M)` の外側頭が `D_{transV M}`
ではなく `D_γ`（`γ = M₁,j₋₂`）である点。したがって共有 scb 文脈は c2hole の
`transV` 頭を剥がした内側 `bpHeadT (c2hole_ch M a)` を印付ける（頭剥がしエンジン
`c2holeInner_scb_ha` ＝ `c2hole_scb_ch` ＋ `scb_decomp_strip_dprin_ha`）。これで残差は
**値リードバック 2 本のみ**（`Rm84HeadValue`、さらに `Rm84NpValue`/`Rm84LpValue` に分割）
に絞られ、`Rm84HeadValue → Rightmost84ReplaceExists` が無条件で立つ
（`rightmost84ReplaceExists_of_value` / `..._of_valueParts`）。

残差 `Rm84HeadValue` の攻め筋（未実装・次 wave）:
* `Rm84NpValue`: `condV_terminal_slice_Trans`（`8.2-condV-terminal-slice-Trans-close`、
  CLOSED）を `m = s84x_jm2 M` と `m = transJm1 M` の 2 回適用 → 同一内側 `t₁` を
  `bridgeA`（`Trans (seg M (transJm1 M) (Lng M-1)) = transC2 M`）＋ `transV M = M₁,transJm1`
  で `t₁ = bpHeadT (transC2 M)` と同定。`hreg` 供給 = `standard_slice_Red_strongmono` /
  `rightmost_nonadm_ancestor`。条件(V) は `condV_bridge_hp_jm2` で潰れ、
  `8.5-exchV-nadm-atomics` の `hNp` に一致。
* `Rm84LpValue`: `Trans (rrLp M)` の既知ブロッカー（非単項値、`8.4-rightmost-readback`。
  塔 `s84x_L` 第2段 `Mark` 表現 `Mark (s84x_L M 2) (s84x_ms M 2) = Trans (rrLp M)` まで到達済）。

- 依存（ビルド済み・committed at 79f75ff）: «8».«8.4-rightmost-exists»
  （`Rightmost84ReplaceExists`/`s84x_Np`/`rrLp`/`s84x_jm2`/`rr84_shared_of_readback`/
  `Trans`/`STPS`/`monoT`/`hasParent`/`Lng`/`entry`/`Dprin`/`BZero`/`scb_decomp`/
  `isPTB_str`/`flatBT`/`Sym`/`rightmost84ReplaceCorrected_of_exists`）、
  «8».«8.4-c2hole-engine»（`c2hole_ch`/`c2hole_at_j1_ch`/`c2hole_scb_ch`/`transC2`/
  `transV`/`transJ1`/`transT1`/`STPS_TPS`/`RTPS_Pred`/`Trans_Mark_invariant`）、推移的に
  «7».«7.2-scb-compose»（`scb_compose_dprin`）。
- 数値検証: `python/trans_model.py`。`hostM30_rr = (0,0)(1,1)(2,2)(2,1)`（条件(IV)）で
  `Trans (N') = Dprin 0 Y`, `Trans (L') = Dprin 0 Y'`、`Y`/`Y'` は最内 principal
  `D_1 0`/`D_0 0` だけで異なる multi-principal 項（`Y` は `(D_2 0, D_1 (D_2 0, D_1 0))`）。
  `bpHeadT (transC2 hostM30_rr) = Y_ha`・`bpHeadT (c2hole_ch … γ) = Yp_ha`（defeq、
  `rm84HeadValue_nonvacuous_ha` で確認）＝値残差 `Rm84HeadValue` は真。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  scb 組立無条件 ＋ `Rm84HeadValue → Rightmost84ReplaceExists` 無条件。残 = 値 2 本。
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

/-! ## 4. `Rm84HeadShared` の scb 組立を無条件で discharge（残差＝値リードバックのみ）

上の `Rm84HeadShared` は 4 部（値 2 本 ＋ scb 分解 2 本）だが、scb 分解 2 本は
`8.4-c2hole-engine` の穴エンジン `c2hole_scb_ch` の**頭剥がし版**で無条件に供給できる。
`Trans (s84x_Np M)` / `Trans (rrLp M)` の外側頭は `D_{transV M}` ではなく
`D_γ`（`γ = M₁,j₋₂`）なので、共有 scb 文脈は c2hole の内側（`transV` 頭を剥がした
`bpHeadT (c2hole_ch M a)`）を印付ける。これで残差は**値リードバック 2 本だけ**
（`Rm84HeadValue`）に絞られる。 -/

/-- 外側 `D_v` 頭の除去。`scb_compose_dprin` の逆。`Dprin v t` の scb 分解
（前置 `dsym v :: w`）から内側 `t` の分解を無条件に取り出す。 -/
private theorem scb_decomp_strip_dprin_ha (v : ℕ∞) (t : BT) (w c w' : List Sym)
    (h : scb_decomp (Dprin v t) (Sym.dsym v :: w) c w') :
    scb_decomp t w c w' := by
  obtain ⟨hflat, hp, htail⟩ := h
  refine ⟨?_, ?_, htail⟩
  · have h2 : Sym.dsym v :: flatBT t = Sym.dsym v :: (w ++ c ++ w') := by
      simpa only [Dprin, flatBT, flatBP, List.cons_append] using hflat
    exact ((List.cons.injEq _ _ _ _).mp h2).2
  · intro _
    exact hp (by simp [Dprin, BZero])

/-- `c2hole_ch M a` は常に `D_{transV M}` 頭を持つ単項なので、内側 = `bpHeadT`。 -/
private theorem c2hole_head_ha (M : PS) (a : ℕ) :
    c2hole_ch M a = Dprin (transV M) (bpHeadT (c2hole_ch M a)) := by
  unfold c2hole_ch
  split_ifs <;> rfl

/-- `setup_sd_ch`（`8.4-c2hole-engine` の private）の複製: `transT1 M ≠ 0_B`。 -/
private theorem setup_sd_ha {N : PS} (hR : RTPS N) (hj1 : 1 < Lng N - 1) :
    transT1 N ≠ BZero := by
  have hlen : 1 < Lng N := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := by
    simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred N) = false := by
    simp [zeroT, hLP]; omega
  have T1' : Trans (Pred N) ≠ BZero :=
    (Trans_Mark_invariant (Pred N) (RTPS_Pred N hR)).2.1 nzP
  simpa [transT1] using T1'

/-- **頭剥がし穴エンジン**。`c2hole_scb_ch` の共有 `(w,w')` から、外側 `D_{transV M}`
を剥がした `bpHeadT (c2hole_ch M a)` の共有 scb 分解を produce する。 -/
theorem c2holeInner_scb_ha (M : PS) (hR : RTPS M) (hM : TPS M) (hmono : monoT M = true)
    (hj1 : 0 < transJ1 M) (ht1 : transT1 M ≠ BZero) :
    ∃ w w' : List Sym, ∀ a : ℕ,
      scb_decomp (bpHeadT (c2hole_ch M a)) w (flatBT (Dprin (a : ℕ∞) BZero)) w' := by
  obtain ⟨w, w', W⟩ := c2hole_scb_ch M hR hM hmono hj1 ht1
  refine ⟨w, w', fun a => ?_⟩
  apply scb_decomp_strip_dprin_ha (transV M) (bpHeadT (c2hole_ch M a)) w
    (flatBT (Dprin (a : ℕ∞) BZero)) w'
  rw [← c2hole_head_ha M a]
  exact W a

/-- **頭付き値リードバック残差（値のみ）**。`Rm84HeadShared` の scb 部を
`c2holeInner_scb_ha` で discharge した後に残る、`Trans (s84x_Np M)` / `Trans (rrLp M)` の
**外側頭 `D_γ` を露出した閉形式値**の 2 本。内側は c2hole の `transV` 頭剥がし
（`bpHeadT (transC2 M)` ＝ 穴 `β`、`bpHeadT (c2hole_ch M γ)` ＝ 穴 `γ`）。
`hostM30_rr`（条件(IV)）で `bpHeadT (transC2 M) = Y_ha`・
`bpHeadT (c2hole_ch M γ) = Yp_ha` なので、これは `rm84HeadShared_nonvacuous_ha`
の witness と一致する真の残差。 -/
def Rm84HeadValue : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
      Trans (s84x_Np M)
          = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) (bpHeadT (transC2 M)) ∧
      Trans (rrLp M)
          = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞)
              (bpHeadT (c2hole_ch M (entry M 1 (s84x_jm2 M))))

/-- **値残差 ⟹ 共有残差**。scb 分解 2 本を頭剥がしエンジンで供給し、値 2 本を
`Rm84HeadValue` から取る。純 scb 代数のみ（無条件）。 -/
theorem rm84HeadShared_of_value (hv : Rm84HeadValue) : Rm84HeadShared := by
  intro M hST hmono hp hrng
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  have hj1 : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have ht1 : transT1 M ≠ BZero := setup_sd_ha hR (by omega)
  obtain ⟨w, w', W⟩ := c2holeInner_scb_ha M hR hM hmono hj1 ht1
  obtain ⟨hNp, hLp⟩ := hv M hST hmono hp hrng
  refine ⟨bpHeadT (transC2 M), bpHeadT (c2hole_ch M (entry M 1 (s84x_jm2 M))),
    w, w', hNp, hLp, ?_, ?_⟩
  · -- `transC2 M` は `c2hole_ch M (entry M 1 (lastIdx M))` に defeq、`lastIdx M` は
    -- `Lng M - 1` に defeq なので `bpHeadT (transC2 M)` = 穴 β の内側。
    exact W (entry M 1 (Lng M - 1))
  · exact W (entry M 1 (s84x_jm2 M))

/-- **値残差 ⟹ 存在部** `Rightmost84ReplaceExists`。 -/
theorem rightmost84ReplaceExists_of_value (hv : Rm84HeadValue) :
    Rightmost84ReplaceExists :=
  rightmost84ReplaceExists_of_headShared (rm84HeadShared_of_value hv)

/-- **値残差 ⟹ 訂正 A30 形** `Rightmost84ReplaceCorrected`。 -/
theorem rightmost84ReplaceCorrected_of_value (hv : Rm84HeadValue) :
    Rightmost84ReplaceCorrected :=
  rightmost84ReplaceCorrected_of_exists (rightmost84ReplaceExists_of_value hv)

/-! ## 5. 値残差の 2 分割（Np 値・Lp 値）

`Rm84HeadValue` を独立に攻略できるよう 2 本に分ける。
* `Rm84NpValue`（`Trans (s84x_Np M)` の頭付き閉形式）は終切片ルート
  （`condV_terminal_slice_Trans` を `m = s84x_jm2 M` と `m = transJm1 M` の 2 回適用し、
  同一内側 `t₁` を `bridgeA`（`Trans (seg M (transJm1 M) (Lng M-1)) = transC2 M`）と
  `transV M = M₁,transJm1` で `t₁ = bpHeadT (transC2 M)` と同定）で攻める。`hreg` の供給は
  `standard_slice_Red_strongmono` / `rightmost_nonadm_ancestor`。条件(V) は
  `condV_bridge_hp_jm2` で `s84x_jm2 M = transJ0 M` に潰れ、`8.5-exchV-nadm-atomics` の
  `hNp`（＝ `exchV_deadm` ＋ `bridgeA_na`）と一致する。
* `Rm84LpValue`（`Trans (rrLp M)` ＝ 右端置換列の値）は既知のブロッカー
  （`8.4-rightmost-readback` header: 非単項値、塔 `s84x_L` 第2段 `Mark` で無条件表現
  `Mark (s84x_L M 2) (s84x_ms M 2) = Trans (rrLp M)` まで到達済み）。 -/
def Rm84NpValue : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
      Trans (s84x_Np M)
          = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) (bpHeadT (transC2 M))

def Rm84LpValue : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
      Trans (rrLp M)
          = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞)
              (bpHeadT (c2hole_ch M (entry M 1 (s84x_jm2 M))))

/-- 2 分割の再合成: `Rm84NpValue ∧ Rm84LpValue ⟹ Rm84HeadValue`。 -/
theorem rm84HeadValue_of_parts (hNp : Rm84NpValue) (hLp : Rm84LpValue) :
    Rm84HeadValue := fun M hST hmono hp hrng =>
  ⟨hNp M hST hmono hp hrng, hLp M hST hmono hp hrng⟩

/-- 2 分割 ⟹ 存在部 `Rightmost84ReplaceExists`。 -/
theorem rightmost84ReplaceExists_of_valueParts
    (hNp : Rm84NpValue) (hLp : Rm84LpValue) : Rightmost84ReplaceExists :=
  rightmost84ReplaceExists_of_value (rm84HeadValue_of_parts hNp hLp)

/-- **`Rm84HeadValue` は空虚でない**（条件(IV) host `hostM30_rr` で充足）。頭剥がし形が
`rm84HeadShared_nonvacuous_ha` の `Y_ha`/`Yp_ha` witness に一致することの確認。 -/
theorem rm84HeadValue_nonvacuous_ha :
    Trans (s84x_Np hostM30_rr)
        = Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞)
            (bpHeadT (transC2 hostM30_rr)) ∧
    Trans (rrLp hostM30_rr)
        = Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞)
            (bpHeadT (c2hole_ch hostM30_rr
              (entry hostM30_rr 1 (s84x_jm2 hostM30_rr)))) := by
  obtain ⟨hNp, hLp, _, _⟩ := rm84HeadShared_nonvacuous_ha
  -- `bpHeadT (transC2 hostM30_rr)` は `Y_ha` に、`bpHeadT (c2hole_ch … γ)` は `Yp_ha`
  -- に defeq（計算により reduce）。よって witness はそのまま流用できる。
  exact ⟨hNp, hLp⟩

#print axioms rightmost84ReplaceExists_of_headShared
#print axioms rightmost84ReplaceCorrected_of_headShared
#print axioms rm84HeadShared_nonvacuous_ha
#print axioms c2holeInner_scb_ha
#print axioms rm84HeadShared_of_value
#print axioms rightmost84ReplaceExists_of_value
#print axioms rm84HeadValue_of_parts
#print axioms rightmost84ReplaceExists_of_valueParts
#print axioms rm84HeadValue_nonvacuous_ha

end PSS
