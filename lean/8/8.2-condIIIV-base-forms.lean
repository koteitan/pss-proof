import «8».«8.2-condIIIV-bgx-reduction»

/-!
# §8.2 条件(II)/(IV) VE34 — **base forms**（`BgxBaseFormNotleft_bg` / `BgxMpForm_bg`）

- 原文: `tmp/content.md` L1624/L3314 付近（命題「条件(II)か(IV)の下での終切片と `Trans` の
  関係」）。本ファイルは親 `8.2-condIIIV-bgx-reduction` が名前付き `Prop` として宣言した 2 つの
  閉形式残差 **`BgxBaseFormNotleft_bg`**（Isabelle `bgx_base_form_notleft` wip:106329 clause-2
  sharp value form ＋ census `bgx_notleft_run0` 106972）と **`BgxMpForm_bg`**（Isabelle
  `bgx_Mp_form` 106407 terminal-slice Adm0 closed form）を討伐する route を提供する。

- **中核（無条件討伐）**:
  - `adm0_setup_bf`（Isabelle `Trans_eq_transC2_Adm0` 19356 の Lean 化 `adm0_setup_sc` の
    自己完結コピー）: run-base BASE ホストの `Adm0` 分岐で `Trans (Pred M) = D_{M₁,0} t₂`、
    `Trans M = transC2 M`、`transV M = M₁,0`。
  - `clause1_sharp_bf` / `clause2_sharp_bf`: `transC2Core` の clause-1（条件(I)/(III)/(V)）
    ／ clause-2（¬(I∨III∨V)∧¬VI∧t₂≠0∧¬leftDj₀）分岐の **sharp value form**。いずれも
    `t₂ = bpHeadT (Trans (Pred M))` に書き換えた原文形。

- **BASE 閉形式の還元**:
  - `BgxBaseFormNotleft_of_census_bf`: `BgxBaseFormNotleft_bg` を **census 残差
    `BgxNotleftRun0_bf`**（＝Isabelle `bgx_notleft_run0` の結論 = `isleft` selector 非発火）
    modulo で放出。regime データ（`VE34_base_Adm0` / `VE34_base_notCondA` / `notVI_Adm0`
    / `t2ne_notAVI` / `VE34_base_transJ0`）＋ `clause2_sharp_bf` で組む。
  - `BgxMpForm_of_slice_bf`: `BgxMpForm_bg` を **slice geometry 残差 `BgxMpSliceData_bf`**
    （＝終切片 `Mp` の `parent Mp 0 (Lng Mp - 1) = 0`（許容的 joint）と条件(I)/(III)/(V)
    ホスト性）modulo で放出。`Mp ∈ DT_PS`（`strongmono_slice`＝`vg8x_terminal_slice_DT`）と
    長さ `1 < Lng Mp - 1` は無条件、`clause1_sharp_bf` を `Mp` に適用し `entry_seg` で
    宿主 `N` の座標へ転送。

- **残差（本セッション射程外の ~1000 行の census / slice surgery）**:
  - `BgxNotleftRun0_bf`（Isabelle `bgx_notleft_run0` 106972 = strong-monomiality census。
    trunk corner ＋ branching の 3 clause dispatch。`subexpr_component_strongmono` は移植済
    だが `bgx_trunk_Trans`／`bgx_headedge`／`entry_FirstNodes_eq_component_gen`／
    `bgx_lastPB`／`vgx_LastStep_elsecase` 系の補助が未移植）。
  - `BgxMpSliceData_bf`（`Mp` の joint 親同定＝`rcpb_nextR_seg` 型 nextR-seg 転送、条件ホスト
    性＝`row1_last_bound` 型 row-1 valley 境界。いずれも未移植の private 補助に依存）。

- 訂正: なし（Isabelle 済補題の逐語移植、または名前付き `Prop` 骨格）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。両閉形式を、regime データと sharp-form 組立で
  最小残差（census / slice geometry）modulo に緑放出。中核の BT-代数 `adm0_setup_bf`
  ／`clause{1,2}_sharp_bf` は無条件討伐。

- 依存 module: `8.2-condIIIV-bgx-reduction`（`BgxBaseFormNotleft_bg` / `BgxMpForm_bg` の
  `Prop` 定義、および推移的に `subexpr_component_Pred_Adm0_clause{2,4}_core` /
  `notVI_Adm0` / `t2ne_notAVI` / `VE34_base_*` / `subexpr_component_strongmono` /
  `strongmono_slice` / `sxsm_factA_uncond_holds` / `sxsm_factB_holds` /
  `Mark_zero_eq_Trans` / `Mark_transJm1_eq_transC2` / `Trans_mono_leftend_form` /
  `transC1_single_principal` / `principal_reconstruct` / `Marked_Pred` /
  `entry_Pred_zero` / `Trans_preserves_zeroT` / `DTPS_iff` / `length_seg` / `entry_seg` /
  `mono_hasParent_row0` / `Adm_le` / `adm_zero` / `FirstNodes_TrMax_Joints` を推移的に）。

- Private suffix: `_bf`。
-/

namespace PSS

open Classical

/-! ## 私的補助（suffix `_bf`） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開）。 -/
private theorem bpHeadT_Dprin_bf (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-! ## `Adm0` setup（Isabelle `Trans_eq_transC2_Adm0` 19356 ／ Lean `adm0_setup_sc` の
自己完結コピー） -/

/-- **`adm0_setup_bf`**: `Adm0` 分岐で `Trans (Pred M) = D_{M₁,0} (transT2 M)`、
`Trans M = transC2 M`、`transV M = M₁,0`。 -/
private theorem adm0_setup_bf (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (transT2 M) ∧
    Trans M = transC2 M ∧
    transV M = (entry M 1 0 : ℕ∞) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hzPred : zeroT (Pred M) = false := by
    have hne : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, hne]
  have ht1 : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT (Pred M) hPredT).mpr h0
    rw [hzPred] at hz
    simp at hz
  have hleR00 : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hMk0 : Marked M 0 := ⟨hM, adm_zero M, hleR00⟩
  have hMzT : Mark M 0 = Trans M := Mark_zero_eq_Trans M hR hMk0
  have hMc2 : Mark M (transJm1 M) = transC2 M :=
    Mark_transJm1_eq_transC2 M hR hmono hlen ht1
  rw [hAdm0] at hMc2
  have hTc2 : Trans M = transC2 M := by rw [← hMzT, hMc2]
  have hMkP0 : Marked (Pred M) 0 := Marked_Pred M 0 hM hlen hMk0 (by omega)
  have hc1 : transC1 M = Trans (Pred M) := by
    show Mark (Pred M) (transJm1 M) = Trans (Pred M)
    rw [hAdm0]
    exact Mark_zero_eq_Trans (Pred M) hpredR hMkP0
  have hmonoP : monoT (Pred M) = true := by
    simp [monoT, hzPred, hMkP0.2.2]
  obtain ⟨t, ht⟩ : ∃ t, Trans (Pred M)
      = Dprin (entry (Pred M) 1 0 : ℕ∞) t := by
    rcases Trans_mono_leftend_form (Pred M) hpredR hmonoP with h0 | h
    · exact absurd h0 ht1
    · exact h
  have hEPred : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hlen
  have hV : transV M = (entry M 1 0 : ℕ∞) := by
    show bpHeadV (transC1 M) = (entry M 1 0 : ℕ∞)
    rw [hc1, ht, hEPred]
    simp [bpHeadV, Dprin]
  have hJ1pos : 0 < transJ1 M := by
    show 0 < Lng M - 1
    omega
  have hT1ne : transT1 M ≠ BZero := ht1
  have pc1 : (PB (transC1 M)).length = 1 :=
    transC1_single_principal M hR hmono hJ1pos hT1ne
  have hc1D : transC1 M = Dprin (transV M) (transT2 M) :=
    principal_reconstruct pc1
  have hTPeq : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (transT2 M) := by
    rw [← hc1, hc1D, hV]
  exact ⟨hTPeq, hTc2, hV⟩

/-- **`transT2_eq_bpHeadT_bf`**: `Adm0` では `bpHeadT (Trans (Pred M)) = transT2 M`
（`Trans (Pred M)` は単一 principal `D_{M₁,0} (transT2 M)`）。 -/
private theorem transT2_eq_bpHeadT_bf (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    bpHeadT (Trans (Pred M)) = transT2 M := by
  obtain ⟨hTP, _, _⟩ := adm0_setup_bf M hR hmono hj1gt hAdm0
  rw [hTP, bpHeadT_Dprin_bf]

/-! ## clause-1 / clause-2 の sharp value form（`transC2Core` 分岐） -/

/-- **`clause1_sharp_bf`**（条件(I)/(III)/(V) ホスト）: `Trans M = D_{M₁,0}
(bpHeadT (Trans (Pred M)) +_B D_{M₁,Lng-1} 0)`。 -/
private theorem clause1_sharp_bf (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hcond : (transCondI M || transCondIII M || transCondV M) = true) :
    Trans M = Dprin (entry M 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (Pred M)))
        (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
  obtain ⟨hTP, hTc2, hV⟩ := adm0_setup_bf M hR hmono hj1gt hAdm0
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_pos hcond, hV]
    rfl
  have hbp : bpHeadT (Trans (Pred M)) = transT2 M :=
    transT2_eq_bpHeadT_bf M hR hmono hj1gt hAdm0
  rw [hTc2, hc2, hbp]

/-- **`clause2_sharp_bf`**（¬(I∨III∨V)∧¬VI∧t₂≠0∧¬leftDj₀ ホスト）: clause-2 sharp form
`Trans M = D_{M₁,0}(t₂ +_B D_{M₁,j₀}(t₂ +_B D_{M₁,Lng-1} 0))`、`t₂ = bpHeadT (Trans (Pred M))`。
`j₀ = transJ0 M = lastParent M`。 -/
private theorem clause2_sharp_bf (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hnA : (transCondI M || transCondIII M || transCondV M) = false)
    (hnVI : transCondVI M = false)
    (ht₂ : transT2 M ≠ BZero)
    (hnotleft :
      bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        ≠ (entry M 1 (transJ0 M) : ℕ∞)) :
    Trans M = Dprin (entry M 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (Pred M)))
        (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (bpHeadT (Trans (Pred M)))
            (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
  obtain ⟨hTP, hTc2, hV⟩ := adm0_setup_bf M hR hmono hj1gt hAdm0
  have hnA' : ¬((transCondI M || transCondIII M || transCondV M) = true) := by
    simp [hnA]
  have hnVI' : ¬(transCondVI M = true) := by simp [hnVI]
  have ht₂' : ¬((transT2 M == BZero) = true) := by simpa using ht₂
  have hleft' : ¬((bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1)
        BZero) == (entry M 1 (lastParent M) : ℕ∞)) = true) := by
    simpa [transJ0] using hnotleft
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT (transT2 M)
                (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_neg hnA', if_neg hnVI', if_neg ht₂', if_neg hleft', if_neg hleft', hV]
    rfl
  have hbp : bpHeadT (Trans (Pred M)) = transT2 M :=
    transT2_eq_bpHeadT_bf M hR hmono hj1gt hAdm0
  rw [hTc2, hc2, hbp]

/-! ## BASE 閉形式の census 還元（Isabelle `bgx_base_form_notleft` 106329 ＋ `bgx_notleft_run0`
106972） -/

/-- **`bgx_base_form_notleft_bf`**（Isabelle `bgx_base_form_notleft` 106329 の逐語移植）:
run-base BASE ホストでの `Trans N` の clause-2 sharp value form。`notleft`（isleft 非発火）を
仮定に取る（原文でも census `bgx_notleft_run0` は別補題）。regime データ
（`VE34_base_Adm0` / `VE34_base_notCondA` / `notVI_Adm0` / `t2ne_notAVI`）＋ `clause2_sharp_bf`、
`transJ0 N = j₀'`（`VE34_base_transJ0`）で中央 index を joint 形に書き換え。 -/
theorem bgx_base_form_notleft_bf (N : PS) (hReg4 : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1)
    (hnotleft : bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
        ≠ (entry N 1 (transJ0 N) : ℕ∞)) :
    Trans N = Dprin (entry N 1 0 : ℕ∞)
       (addBT (bpHeadT (Trans (Pred N)))
         (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
           (addBT (bpHeadT (Trans (Pred N)))
             (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)))) := by
  have hReg4' := hReg4
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, _hj0lt⟩ := hReg4
  have hAdm0 : transJm1 N = 0 := VE34_base_Adm0 N hReg4' hbase
  have hnA : ¬(transCondI N = true ∨ transCondIII N = true ∨ transCondV N = true) :=
    VE34_base_notCondA N hReg4' hbase
  have hj1gt : 1 < Lng N - 1 := VE34_base_j1gt N hReg4' hbase
  have hL : 1 < Lng N := by omega
  have hnVI : transCondVI N = false := notVI_Adm0 N hR hmono hBrne hj1gt hAdm0
  have hnA' : (transCondI N || transCondIII N || transCondV N) = false := by
    cases hc1 : transCondI N <;> cases hc2 : transCondIII N <;> cases hc3 : transCondV N <;>
      simp_all
  have ht₂ : transT2 N ≠ BZero := t2ne_notAVI N hR hmono hL hj1gt hnA hnVI
  have htj0 : transJ0 N = (Joints N).getD ((Br N).length - 1) 0 :=
    VE34_base_transJ0 N hReg4' hbase
  have hsharp := clause2_sharp_bf N hR hmono hj1gt hAdm0 hnA' hnVI ht₂ hnotleft
  rw [htj0] at hsharp
  exact hsharp

/-- **`BgxNotleftRun0_bf`**（Isabelle `bgx_notleft_run0` 106972 の結論）: run-base BASE ホストで
`isleft` selector は発火しない——`Trans (Pred N)` の body の最終 principal の頭値は
`> N₁,j₀'`。census（strong-monomiality）が本体。 -/
def BgxNotleftRun0_bf : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N = (Br N).length - 1 →
    bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
      ≠ (entry N 1 (transJ0 N) : ℕ∞)

/-- **`BgxBaseFormNotleft_of_census_bf`**: `BgxBaseFormNotleft_bg` を census 残差
`BgxNotleftRun0_bf` modulo で放出（`bgx_base_form_notleft_bf` ＋ census）。 -/
theorem BgxBaseFormNotleft_of_census_bf (hcen : BgxNotleftRun0_bf) :
    BgxBaseFormNotleft_bg := by
  intro N hRegD hbase hdeep hrun
  obtain ⟨hReg4, hdesc⟩ := hRegD
  exact bgx_base_form_notleft_bf N hReg4 hbase (hcen N ⟨hReg4, hdesc⟩ hbase hdeep hrun)

/-! ## 終切片閉形式の slice-geometry 還元（Isabelle `bgx_Mp_form` 106407） -/

/-- **`BgxMpSliceData_bf`**（Isabelle `bgx_Mp_form` の geometry core）: BASE ホストの終切片
`Mp = seg N j₀' (Lng N - 1)` は、その最終列の直近祖先が列 `0`（joint、許容的）ゆえ
`Adm0`（`transJm1 Mp = 0`）かつ条件(I)/(III)/(V) ホスト。`parent Mp 0 (Lng Mp - 1) = 0`
（`rcpb_nextR_seg` 型 nextR-seg 転送）と row-1 valley 境界（`row1_last_bound` 型）が本体。 -/
def BgxMpSliceData_bf : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    transJm1 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = 0 ∧
    (transCondI (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ||
     transCondIII (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ||
     transCondV (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) = true

/-- **`BgxMpForm_of_slice_bf`**: `BgxMpForm_bg` を slice-geometry 残差 `BgxMpSliceData_bf`
modulo で放出。`Mp ∈ DT_PS`（`strongmono_slice`＝`vg8x_terminal_slice_DT`）と長さ
`1 < Lng Mp - 1` は無条件、`clause1_sharp_bf` を `Mp` に適用し `entry_seg` で宿主座標へ転送。 -/
theorem BgxMpForm_of_slice_bf (hslice : BgxMpSliceData_bf) : BgxMpForm_bg := by
  intro N hRegD hbase hdeep
  obtain ⟨hReg4, hdesc⟩ := hRegD
  have hReg4' := hReg4
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, _hj0pos, hj0lt⟩ := hReg4
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  -- 宿主の長さ下界
  have hL : 1 < Lng N := by omega
  have hj0ltL : j0 < Lng N - 1 := by omega
  -- `Mp ∈ DT_PS`（`set Mp` 前に確立して書き換える）
  have hND : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hMpDT0 : DTPS (seg N j0 (Lng N - 1)) :=
    strongmono_slice N j0 (Lng N - 1) hND hj0ltL (le_refl _) (le_of_eq hj0def)
  set Mp := seg N j0 (Lng N - 1) with hMpdef
  obtain ⟨hMpR, hMpmono, _hMpdesc⟩ := (DTPS_iff Mp).mp hMpDT0
  -- `Mp` の長さ
  have hLngMp : Lng Mp = Lng N - j0 := by
    rw [hMpdef, length_seg]; omega
  have hMpj1gt : 1 < Lng Mp - 1 := by omega
  have hMpL : 0 < Lng Mp := by omega
  have hMpLm1 : Lng Mp - 1 < Lng Mp := by omega
  have hidx1 : j0 + (Lng Mp - 1) = Lng N - 1 := by omega
  -- slice-geometry 残差（Adm0 ＋ 条件ホスト性）
  obtain ⟨hMpAdm0, hMpcond⟩ := hslice N ⟨hReg4', hdesc⟩ hbase hdeep
  -- clause-1 sharp form on `Mp`
  have hform := clause1_sharp_bf Mp hMpR hMpmono hMpj1gt hMpAdm0 hMpcond
  -- entry transports（`entry_seg`）
  have he0 : entry Mp 1 0 = entry N 1 j0 := by
    have hh := entry_seg N j0 (Lng N - 1) 1 0 (by rw [← hMpdef]; exact hMpL)
    rw [← hMpdef] at hh
    rw [hh, Nat.add_zero]
  have he1 : entry Mp 1 (Lng Mp - 1) = entry N 1 (Lng N - 1) := by
    have hh := entry_seg N j0 (Lng N - 1) 1 (Lng Mp - 1) (by rw [← hMpdef]; exact hMpLm1)
    rw [← hMpdef] at hh
    rw [hh, hidx1]
  rw [he0, he1] at hform
  exact hform

/-! ## 転記の数値検証（深い run-base BASE ホストで両残差の shape を確認）

`hostBF = (0,0)(1,1)(2,2)(2,2)(2,0)` は補正体制 `VE34Reg4D` の deep run-base BASE ホスト
（親 `8.2-condIIIV-bgx-reduction` の `hostBG` と同一）。census 残差（isleft 非発火）と
slice 残差（終切片 Adm0 ＋ 条件ホスト）が実値で成立することを確認。 -/

def hostBF : PS := [(0,0),(1,1),(2,2),(2,2),(2,0)]

-- deep run-base BASE VE34Reg4D ホストであること。
#guard decide (VE34Reg4D hostBF
  ∧ VEj1p hostBF = Lng hostBF - 1
  ∧ TrMax hostBF + 2 < Lng hostBF
  ∧ LastStep hostBF = (Br hostBF).length - 1) = true

-- `BgxNotleftRun0_bf`（isleft selector 非発火）が hostBF で成立。
#guard (bpHeadV ((PB (transT2 hostBF)).getD ((PB (transT2 hostBF)).length - 1) BZero)
    == (entry hostBF 1 (transJ0 hostBF) : ℕ∞)) = false

-- `BgxMpSliceData_bf`（終切片 Adm0 ＋ 条件(I)/(III)/(V) ホスト）が hostBF で成立。
#guard (transJm1 (seg hostBF ((Joints hostBF).getD ((Br hostBF).length - 1) 0) (Lng hostBF - 1))
    == 0) = true
#guard (transCondI (seg hostBF ((Joints hostBF).getD ((Br hostBF).length - 1) 0) (Lng hostBF - 1))
    || transCondIII (seg hostBF ((Joints hostBF).getD ((Br hostBF).length - 1) 0) (Lng hostBF - 1))
    || transCondV (seg hostBF ((Joints hostBF).getD ((Br hostBF).length - 1) 0) (Lng hostBF - 1)))
    = true

#print axioms bgx_base_form_notleft_bf
#print axioms BgxBaseFormNotleft_of_census_bf
#print axioms BgxMpForm_of_slice_bf

end PSS
