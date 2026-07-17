import «8».«8.2-subexpr-component-strongmono»
import «8».«8.2-subexpr-component-Pred»
import «8».«8.2-subexpr-admpos-engine»
import «8».«8.2-condV-rightmost-parent»
import «8».«8.1-diagSeq-Trans»
import «6».«6.5-Red-Pred-commute»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.4-RightAnces-RightNodes»
import «7».«7.4-RightNodes-Mark»
import «7».«7.3-two-column»
import «8».«8.2-subexpr-wid»
import «8».«8.2-subexpr-adm0-ctx»
import «8».«8.2-subexpr-adm0-cores»
import «8».«8.2-subexpr-gB»
import «6».«6.6-reduced-coeff»
import «6».«6.6-P-condAB»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-monoT-Red»
import «6».«6.5-Red-welldefined»
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»

/-!
# §8.2 `SXSM_factA_uncond` / `SXSM_factB` の放電

- 原文: `tmp/content.md` 3454（§8.2 補題（強単項性の下での部分表現の単項成分の
  基本性質））の下界 (2)/(3)/(4) の本体。忠実形は
  `isabelle/pss_paper.thy:1563`（`p_8_2_subexpr_component_strongmono`）。
- 本ファイルは `8.2-subexpr-component-strongmono` が green-modulo で受け取っている
  2 本の名前付き `Prop` を実体化する。

## 訂正（A 番号）

**該当なし**（`8.2-subexpr-component-strongmono` / `8.2-subexpr-final` と同一の判断。
§8.2 に触れる `A9` は `LastStep` の定義文への軽微補正で、本補題には現れない）。

## Isabelle 対応（`isabelle/layerB/pss_wip.thy`）

| Lean | Isabelle | 行 |
|---|---|---|
| `joint_idx_mono` | `m_8_2_joint_idx_mono` | 34417 |
| `thrmono` | `m_8_2_thrmono` | 34390 |
| `descending_Br_Pred` | `descending_Br_Pred` | 33958 |
| `Br_Pred_len_map_smp` | `wid_JPm1_map` / `wid_BrLen_Pred` | 33529 |
| `FNJ_Pred_at_JPm1_smp` | `wid_FNJ_Pred_at_JPm1` | 33544 |
| `factA_base_smp` | `m_8_2_factA_base` | 34448 |
| **`newdom`** | **`m_8_2_newdom`** | **34670** |
| **`factA`** | `m_8_2_factA` ＋ `m_8_2_factA_uncond` | 34540 / 35084 |
| `branch_row1_le_TrMax_smp` | `m_8_2_branch_row1_le_TrMax` | 35459 |
| `widH_base2_smp` | `m_8_2_widH_base2` | 35804 |
| **`widH`** | **`m_8_2_widH`** | **35857** |
| `alltrunk_base_thr_smp` | `m_8_2_factB_base` | 35008 |
| `factB_base2_smp` | `m_8_2_factB_base2` | 36142 |
| `branch_row1_tiebreak_smp` | `m_8_2_branch_row1_tiebreak` | 34990 付近 |
| `FN_Suc_lt_smp` | `wid_FN_Suc_lt` | 36099 |
| **`factB`** | **`m_8_2_factB`** | **36200** |

`m_8_2_factA_step` (34212) / `m_8_2_factB_step` (35130) は別途移植していない。
両者は抽象エンジン `wit_step_thr`（`8.2-subexpr-component-strongmono` で公開済、
無条件）の閾値インスタンス（factA は `thr = M₁,j′₀`、factB は
`thr = thr′ = M₁,j′₁` で `thrmono` が反射律）にすぎないため、直接 `wit_step_thr`
を呼んでいる。

## 依存（ビルド済ツールボックス）

- `keystone` / `baseU_Br_empty_TrMax` / `baseU_alltrunk_diag_entry` /
  `baseU_alltrunk_Trans_RN1` / `j0_eq_TrMax` / `scbOuterSurgerySplit_holds`
  （`8.2-subexpr-component-Pred` — 本日無条件化）
- `wit_step_thr`（`8.2-subexpr-component-strongmono`）
- `wid_step`（`8.2-subexpr-admpos-engine`）
- `keystone_imp_wid` / `wid_iff` / `ft_transport`（`8.2-subexpr-wid`）
- `notVI_Adm0` / `j1eq_Adm0` / `gA_Adm0` / `condII_or_condIV` / `e0gt_e1zero` /
  `e0gt_condIV`（`8.2-subexpr-adm0-ctx`）、`gB_Adm0_condA`（`8.2-subexpr-gB`）、
  `subexpr_component_Pred_Adm0_clause1_keystone`（`8.2-subexpr-adm0-cores`）
- `DTPS` / `DTPS_iff` / `descendingB_iff` / `cdomB_iff`
  （`8.2-standard-slice-Red-strongmono` 経由）
- `joint_row1_eq` / `branch_col0_val` / `wf21_Br_eq_seg`（`8.2-condV-rightmost-parent`）
- `diagSeq_Trans`（`8.1-diagSeq-Trans`）、`two_column_Trans`（`7.3-two-column`）

## 状態

**本ファイル単独で green（`sorry` 0、仮定 0）。`SXSM_factA_uncond` /
`SXSM_factB` の両方を discharge 済**（`sxsm_factA_uncond_holds` /
`sxsm_factB_holds`。house pattern ＝ `Prop` を定理の型に取って elaborator に
drop-in を保証させている）。これで
`8.2-subexpr-component-strongmono` の `subexpr_component_strongmono` は無条件化
され、§8.2 の補題（強単項性の下での部分表現の単項成分の基本性質）が閉じる。

`branch_row1_le_TrMax_smp` は `8.2-condV-rightmost-parent` に `private`
(`branch_row1_le_TrMax_cv`) で存在するが公開されていないため、同一証明を本ファイル
に再掲した（当該ファイルはスコープ外なので触らない）。同様に
`m_8_2_subexpr_leftend_unique` / `wit_PB_relax` / `PB_Dpt_single` / `leBT_Dpt0_iff` /
`rn1_outer_inner_trailing` の Lean 版も `8.2-subexpr-component-strongmono` で
`private` なので複製している。

公開: `joint_idx_mono` / `thrmono` / `descending_Br_Pred` / `newdom` / `factA` /
`widH` / `factB` / `sxsm_factA_uncond_holds` / `sxsm_factB_holds`。
私的補助は suffix `_smp`。
-/

namespace PSS

/-! ## 閾値／添字の単調性（Isabelle `m_8_2_thrmono` 34390 ／
`m_8_2_joint_idx_mono` 34417）

`descending (Br M)` の第 0 行の内容そのもの。`branch_col0_val`
（`(Br M)_J` の行 0 左端 `= M₁,₀ + Joints(M)_J + 1`）で両辺を joint の添字に
翻訳すると、`cdom` の第 1 成分がそのまま添字の不等式になる。 -/

/-- Isabelle `m_8_2_joint_idx_mono` (`layerB/pss_wip.thy:34417`)。**無条件**。 -/
theorem joint_idx_mono (M : PS) (JN J1 : ℕ) (hD : DTPS M)
    (hJNJ1 : JN ≤ J1) (hJ1Br : J1 < (Br M).length) :
    (Joints M).getD J1 0 ≤ (Joints M).getD JN 0 := by
  obtain ⟨-, -, hdesc⟩ := (DTPS_iff M).mp hD
  have hJNBr : JN < (Br M).length := by omega
  have hcd := (cdomB_iff _ _).mp ((descendingB_iff (Br M)).mp hdesc JN J1 hJNJ1 hJ1Br)
  have h1 := branch_col0_val M J1 hD hJ1Br
  have h2 := branch_col0_val M JN hD hJNBr
  have := hcd.1
  omega

/-- Isabelle `m_8_2_thrmono` (`layerB/pss_wip.thy:34390`)。**無条件**。 -/
theorem thrmono (M : PS) (JN J1 : ℕ) (hD : DTPS M)
    (hJNJ1 : JN ≤ J1) (hJ1Br : J1 < (Br M).length) :
    entry M 1 ((Joints M).getD J1 0) ≤ entry M 1 ((Joints M).getD JN 0) := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, -⟩ := RTPS_condAB M hR
  have hJNBr : JN < (Br M).length := by omega
  have h1 := (FirstNodes_TrMax_Joints M J1 hM hmono hJ1Br).1
  have h2 := (FirstNodes_TrMax_Joints M JN hM hmono hJNBr).1
  have o1 := (trunk_entries_offset M hM hA _ h1).2
  have o2 := (trunk_entries_offset M hM hA _ h2).2
  have hidx := joint_idx_mono M JN J1 hD hJNJ1 hJ1Br
  omega

/-! ## `Pred` 側の構造（Isabelle `wid_JPm1_map` 33529 ／
`wid_FNJ_Pred_at_JPm1` 33544 ／`descending_Br_Pred` 33958）

`Br_Pred_core_nontrunk`（`Br (Pred M) = (Br M).dropLast ++ [最終ブロックの dropLast]`、
最終ブロックが単項なら末尾成分ごと落ちる）が全ての土台。 -/

private theorem getD_default_smp {α : Type} (l : List α) (n : ℕ) (d d' : α)
    (h : n < l.length) : l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

private theorem getLastD_cons_eq_smp {α : Type} :
    ∀ (l : List α) (a d : α), (a :: l).getLastD d = (a :: l).getD l.length d := by
  intro l
  induction l with
  | nil => intro a d; rfl
  | cons b bs ih =>
      intro a d
      have hstep : (a :: b :: bs).getLastD d = (b :: bs).getLastD a := rfl
      rw [hstep, ih b a]
      simp only [List.length_cons, List.getD_cons_succ]
      exact getD_default_smp (b :: bs) bs.length a d (by simp)

private theorem getLastD_eq_getD_smp {α : Type} (l : List α) (d : α) (hl : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simpa using getLastD_cons_eq_smp as a d

private theorem getD_append_left_smp {α : Type} (l r : List α) (J : ℕ) (d : α)
    (h : J < l.length) : (l ++ r).getD J d = l.getD J d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_single_smp {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD]
  simp

private theorem getD_dropLast_smp {α : Type} (l : List α) (J : ℕ) (d : α)
    (h : J < l.length - 1) : l.dropLast.getD J d = l.getD J d := by
  have hJl : J < l.length := by omega
  have h1 : J < l.dropLast.length := by rw [List.length_dropLast]; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hJl]
  simp [List.getElem_dropLast]

private theorem entry_dropLast_smp (l : PS) (i j : ℕ) (hj : j < Lng l - 1) :
    entry l.dropLast i j = entry l i j := by
  rw [List.dropLast_eq_take]
  exact entry_take l (l.length - 1) i j hj

/-- `Br M ≠ []` から `TrMax M ≠ Lng M - 1`（Isabelle は `Br_def` の場合分け）。 -/
private theorem trmax_ne_of_Brne_smp (M : PS) (hBrne : Br M ≠ []) :
    TrMax M ≠ Lng M - 1 := by
  intro heq
  exact hBrne (by simp [Br, heq])

/-- 最終枝ブロックの長さ（`wf21_Br_eq_seg` の読み出し）。 -/
private theorem lastBr_len_smp (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    Lng ((Br M).getLastD []) =
      Lng M - (FirstNodes M).getD ((Br M).length - 1) 0 := by
  have hbl := getLastD_eq_getD_smp (Br M) ([] : PS) hBrne
  have hseg := wf21_Br_eq_seg M hM hBrne
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  rw [hbl, hseg, length_seg]
  omega

/-- Isabelle `wid_BrLen_Pred` 相当: `Br (Pred M)` の長さ。 -/
private theorem Br_Pred_length_smp (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) :
    (Br (Pred M)).length =
      (if Lng ((Br M).getLastD []) ≤ 1 then (Br M).length - 1 else (Br M).length) := by
  have hne := trmax_ne_of_Brne_smp M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  rw [Br_Pred_core_nontrunk M hM hlen hne]
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase, if_pos hcase]
    have hl : ((Br M).dropLast ++ ([] : List PS)).length = (Br M).length - 1 := by simp
    rw [hl]
  · rw [if_neg hcase, if_neg hcase]
    have hl : ((Br M).dropLast ++ [((Br M).getLastD []).dropLast]).length
        = (Br M).length - 1 + 1 := by simp
    rw [hl]
    omega

/-- Isabelle `wid_JPm1_map` (`layerB/pss_wip.thy:33529`)。 -/
private theorem Br_Pred_len_map_smp (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    (Br (Pred M)).length - 1 =
      (if (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
        then (Br M).length - 1 - 1 else (Br M).length - 1) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hset := subexpr_component_Pred_setup M hR hmono hBrne hj1gt
  have hj1lt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M := hset.1
  have hlast := lastBr_len_smp M hM hBrne
  have hlenP := Br_Pred_length_smp M hM hlen hBrne
  by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
  · rw [if_pos hj1eq]
    have hle1 : Lng ((Br M).getLastD []) ≤ 1 := by rw [hlast, hj1eq]; omega
    rw [if_pos hle1] at hlenP
    omega
  · rw [if_neg hj1eq]
    have hnle : ¬ Lng ((Br M).getLastD []) ≤ 1 := by rw [hlast]; omega
    rw [if_neg hnle] at hlenP
    omega

/-- `Br (Pred M)` の各成分は `Br M` の同添字成分と行 0/行 1 の左端が一致する
（Isabelle `wid_Br_Pred_col0_agree`）。 -/
private theorem Br_Pred_col0_agree_smp (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) (J : ℕ) (hJ : J < (Br (Pred M)).length) (i : ℕ) :
    entry ((Br (Pred M)).getD J []) i 0 = entry ((Br M).getD J []) i 0 := by
  have hne := trmax_ne_of_Brne_smp M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hcore := Br_Pred_core_nontrunk M hM hlen hne
  have hlenP := Br_Pred_length_smp M hM hlen hBrne
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase] at hlenP
    rw [hcore, if_pos hcase]
    simp only [List.append_nil]
    exact congrArg (fun q => entry q i 0) (getD_dropLast_smp (Br M) J [] (by omega))
  · rw [if_neg hcase] at hlenP
    rw [hcore, if_neg hcase]
    by_cases hJlt : J < (Br M).length - 1
    · rw [getD_append_left_smp _ _ _ _ (by rw [List.length_dropLast]; omega)]
      exact congrArg (fun q => entry q i 0) (getD_dropLast_smp (Br M) J [] hJlt)
    · have hJeq : J = (Br M).length - 1 := by omega
      have hdl : (Br M).dropLast.length = (Br M).length - 1 := by simp
      rw [hJeq, ← hdl, getD_append_single_smp]
      rw [hdl, ← getLastD_eq_getD_smp (Br M) [] hBrne]
      exact entry_dropLast_smp ((Br M).getLastD []) i 0 (by omega)

/-- Isabelle `descending_Br_Pred` (`layerB/pss_wip.thy:33958`)。**無条件**。 -/
theorem descending_Br_Pred (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hLp : 1 < Lng (Pred M)) : DTPS (Pred M) := by
  obtain ⟨hR, hmono, hdesc⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  have hne := trmax_ne_of_Brne_smp M hBrne
  have htb := TrMax_bound M hM
  have hlen : 1 < Lng M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hlen3 : 2 < Lng M := by omega
  have hlenP := Br_Pred_length_smp M hM hlen hBrne
  have hlenle : (Br (Pred M)).length ≤ (Br M).length := by
    by_cases hcase : Lng ((Br M).getLastD []) ≤ 1 <;>
      simp only [hcase, if_true, if_false] at hlenP <;> omega
  refine (DTPS_iff (Pred M)).mpr ⟨RTPS_Pred M hR, monoT_Pred_long M hM hmono hlen3, ?_⟩
  rw [descendingB_iff]
  intro J₀ J₁ h01 hJ₁
  have hJ₀ : J₀ < (Br (Pred M)).length := by omega
  have hJ₁M : J₁ < (Br M).length := by omega
  have hcd := (cdomB_iff _ _).mp ((descendingB_iff (Br M)).mp hdesc J₀ J₁ h01 hJ₁M)
  rw [cdomB_iff,
    Br_Pred_col0_agree_smp M hM hlen hBrne J₀ hJ₀ 0,
    Br_Pred_col0_agree_smp M hM hlen hBrne J₁ hJ₁ 0,
    Br_Pred_col0_agree_smp M hM hlen hBrne J₀ hJ₀ 1,
    Br_Pred_col0_agree_smp M hM hlen hBrne J₁ hJ₁ 1]
  exact hcd

/-- Isabelle `wid_FNJ_Pred_at_JPm1` (`layerB/pss_wip.thy:33544`)。 -/
private theorem FNJ_Pred_at_JPm1_smp (M : PS) (hM : TPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hlen : 1 < Lng M) (hBrPne : Br (Pred M) ≠ []) :
    (FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0 =
        (FirstNodes M).getD ((Br (Pred M)).length - 1) 0 ∧
      (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 =
        (Joints M).getD ((Br (Pred M)).length - 1) 0 := by
  have hne := trmax_ne_of_Brne_smp M hBrne
  have hJ : (Br (Pred M)).length - 1 < (Br (Pred M)).length := by
    have := List.length_pos_of_ne_nil hBrPne; omega
  exact ⟨FirstNodes_Pred_core M hM hlen hne _ hJ,
    Joints_Pred_core M hM hmono hlen hne _ hJ⟩

/-! ## `PB` / `leBT` の小道具（`8.2-subexpr-component-strongmono` の私的層の複製）

`PB_Dpt_single` / `leBT_Dpt0_iff` は当該ファイルで `private` なのでここに再掲する。 -/

private theorem PB_Dprin_single_smp (v : ℕ∞) (t : BT) : PB (Dprin v t) = [Dprin v t] := by
  simp [PB, Dprin, untrm]

private theorem lessBT_BZero_iff_smp (c : BT) : lessBT BZero c = true ↔ c ≠ BZero := by
  rcases c with ⟨cs⟩
  cases cs with
  | nil => simp [BZero, lessBT, lessBPList]
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-- Isabelle `leBT_Dpt0_iff`: `D_u 0 ≤_B D_v c ⟺ u ≤ v`。 -/
private theorem leBT_Dprin0_iff_smp (u v : ℕ∞) (c : BT) :
    leBT (Dprin u BZero) (Dprin v c) = true ↔ u ≤ v := by
  rw [leBT]
  simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
    Bool.false_eq_true, and_false, or_false, decide_eq_true_eq, beq_iff_eq,
    BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true]
  constructor
  · rintro ((hlt | ⟨heq, -⟩) | ⟨heq, -⟩)
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · exact le_of_eq heq
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (Or.inl hlt)
    · by_cases hc : c = BZero
      · exact Or.inr ⟨heq, hc.symm⟩
      · exact Or.inl (Or.inr ⟨heq, (lessBT_BZero_iff_smp c).mpr hc⟩)

/-! ## 全幹の `Trans`（`baseU_alltrunk_Trans_RN1` 内部の 2 段塔の切り出し） -/

/-- 全幹（`TrMax Q = Lng Q - 1`）の簡約単項列 `Q` は対角列なので
`Trans Q = D_{Q₁,₀}(D_{Q₁,ᴸⁿᵍ⁻¹} 0)`。 -/
private theorem alltrunk_Trans_tower_smp (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (htr : TrMax Q = Lng Q - 1) (hL : 1 < Lng Q) :
    Trans Q = Dprin ((entry Q 1 0 : ℕ) : ℕ∞)
      (Dprin ((entry Q 1 (Lng Q - 1) : ℕ) : ℕ∞) BZero) := by
  have hub : entry Q 1 0 < entry Q 1 0 + (Lng Q - 1) := by omega
  have heq : Q = diagSeq (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) := by
    apply List.ext_getElem
    · have hbridge : List.length Q = Lng Q := rfl
      simp [diagSeq]
      omega
    · intro i hiQ _
      have hiL : i < Lng Q := hiQ
      obtain ⟨hd0, hd1⟩ := baseU_alltrunk_diag_entry Q i hR hmono htr hiL
      have hQi : Q[i] = (entry Q 0 i, entry Q 1 i) := by
        have h0 : entry Q 0 i = Q[i].1 := by
          simp [entry, List.getElem?_eq_getElem hiL]
        have h1 : entry Q 1 i = Q[i].2 := by
          simp [entry, List.getElem?_eq_getElem hiL]
        rw [h0, h1]
      rw [hQi, hd0, hd1]
      simp [diagSeq, List.getElem_map, List.getElem_range']
  have hlast : entry Q 1 (Lng Q - 1) = entry Q 1 0 + (Lng Q - 1) :=
    (baseU_alltrunk_diag_entry Q (Lng Q - 1) hR hmono htr (by omega)).2
  rw [hlast]
  conv_lhs => rw [heq]
  exact diagSeq_Trans (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) hub

/-! ## factA の基底（Isabelle `m_8_2_factA_base` 34448）

`Br (Pred M) = []` すなわち `Pred M` は全幹＝対角列 `diagSeq u (u + TrMax M)`。
`Trans (Pred M) = D_u (D_{u+TrMax M} 0)` は単一 principal なので IH の下界
（閾値 `thr' = u + TrMax M`）は自明。あとは抽象エンジン `wit_step_thr` に
`thr = M₁,j′₀` で流し込むだけ。 -/

/-- Isabelle `m_8_2_factA_base` (`layerB/pss_wip.thy:34448`)。 -/
private theorem factA_base_smp (M : PS) (a : BT) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hBrPe : Br (Pred M) = [])
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hnewdom : entry M 1 ((Joints M).getD ((Br M).length - 1) 0)
        ≤ (RightNodes (Trans M)).getD 1 0) :
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p
        = true := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, -⟩ := RTPS_condAB M hR
  have hne := trmax_ne_of_Brne_smp M hBrne
  have htb := TrMax_bound M hM
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
  have hj0le := (FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ1Br).1
  have hLge3 : 2 < Lng M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M (by omega)
  have hTrP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM (by omega) hne
  have hTrPe : TrMax (Pred M) = Lng (Pred M) - 1 := baseU_Br_empty_TrMax (Pred M) hBrPe
  have hLPg1 : 1 < Lng (Pred M) := by omega
  obtain ⟨hPR, hPmono, -⟩ := (DTPS_iff (Pred M)).mp (descending_Br_Pred M hD hBrne hLPg1)
  have huP : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 (by omega)
  have htower := alltrunk_Trans_tower_smp (Pred M) hPR hPmono hTrPe hLPg1
  have hvlast : entry (Pred M) 1 (Lng (Pred M) - 1) = entry M 1 0 + TrMax M := by
    have hd :=
      (baseU_alltrunk_diag_entry (Pred M) (Lng (Pred M) - 1) hPR hPmono hTrPe (by omega)).2
    omega
  have predW : Trans (Pred M) =
      Dprin (entry M 1 0 : ℕ∞) (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero) := by
    rw [htower, huP, hvlast]
  have ihA : ∀ r ∈ PB (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero),
      leBT (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero) r = true := by
    intro r hr
    rw [PB_Dprin_single_smp] at hr
    rw [List.mem_singleton.mp hr]
    exact (leBT_Dprin0_iff_smp _ _ _).mpr le_rfl
  have hthr : entry M 1 ((Joints M).getD ((Br M).length - 1) 0) ≤ entry M 1 0 + TrMax M := by
    have hoff := (trunk_entries_offset M hM hA _ hj0le).2
    omega
  exact wit_step_thr M a (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero)
    (entry M 1 ((Joints M).getD ((Br M).length - 1) 0)) (entry M 1 0 + TrMax M)
    aW predW ihA hthr hnewdom (keystone M hR hmono hBrne (by omega))

/-! ## `newdom`（Isabelle `m_8_2_newdom` 34670）

factA のキーストーン case (1) が要求する「新 head の支配」
`M₁,j′₀ ≤ RightNodes(Trans M)₁`。`Lng` に関する強帰納法。

1. `Pred` 側の下界 `M₁,j′₀ ≤ RightNodes(Trans (Pred M))₁` を先に立てる
   （全幹なら対角の読み出し、さもなくば IH ＋ `thrmono`）。
2. `Admpos`（`transJm1 M > 0`）: `RightNodes` は `Pred` から保存される（`wid_step`）。
3. `Adm0`: キーストーンの 4 分岐。(2)/(4) は `RightNodes₁ = M₁,j′₀` で自明、
   (3) は `Pred` と末尾 head を共有するので 1. で閉じる。(1) は
   `j′₁ = j₁` かつ `transJm1 M = 0` から joint の非許容性が出て、行 0 = 行 1 が
   `j′₁` で成立、よって joint の行 1 値は leaf の値 -1 以下。 -/

private theorem rn1_outer_inner_trailing_smp (a b : ℕ) (pre s : BT) :
    (RightNodes (Dprin (a : ℕ∞) (addBT pre (Dprin (b : ℕ∞) s)))).getD 1 0 = b := by
  rw [RightNodes_Dprin, RightNodes_addBT_Dprin]
  simp

/-- Isabelle `m_8_2_newdom` (`layerB/pss_wip.thy:34670`)。**無条件**。 -/
theorem newdom (M : PS) (hD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0) :
    entry M 1 ((Joints M).getD ((Br M).length - 1) 0) ≤ (RightNodes (Trans M)).getD 1 0 := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hn
    obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
    have hM : TPS M := RTPS_TPS M hR
    obtain ⟨hA, -⟩ := RTPS_condAB M hR
    have hne := trmax_ne_of_Brne_smp M hBrne
    have htb := TrMax_bound M hM
    have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
    have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
    have hj0le := (FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ1Br).1
    have hLge3 : 2 < Lng M := by omega
    have hj1gt : 1 < Lng M - 1 := by omega
    have he1j0 := (trunk_entries_offset M hM hA _ hj0le).2
    have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M (by omega)
    have hLPg1 : 1 < Lng (Pred M) := by omega
    have hpredDT := descending_Br_Pred M hD hBrne hLPg1
    obtain ⟨hPR, hPmono, -⟩ := (DTPS_iff (Pred M)).mp hpredDT
    have hPT : TPS (Pred M) := RTPS_TPS (Pred M) hPR
    have he10P : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 (by omega)
    have hnzP : zeroT (Pred M) = false := by
      simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      exact Or.inl (by omega)
    have ht1ne : Trans (Pred M) ≠ BZero := by
      intro hz
      rw [(Trans_preserves_zeroT (Pred M) hPT).mpr hz] at hnzP
      exact Bool.noConfusion hnzP
    -- 1. `Pred` 側の下界
    have hbound : entry M 1 ((Joints M).getD ((Br M).length - 1) 0)
        ≤ (RightNodes (Trans (Pred M))).getD 1 0 := by
      by_cases hBrPe : Br (Pred M) = []
      · have hTrPe : TrMax (Pred M) = Lng (Pred M) - 1 :=
          baseU_Br_empty_TrMax (Pred M) hBrPe
        have hTrP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM (by omega) hne
        have hRNP := baseU_alltrunk_Trans_RN1 (Pred M) hPR hPmono hTrPe hLPg1
        have hdiag :=
          (baseU_alltrunk_diag_entry (Pred M) (Lng (Pred M) - 1) hPR hPmono hTrPe
            (by omega)).2
        omega
      · have hBrPne : Br (Pred M) ≠ [] := hBrPe
        have hBrPL : 0 < (Br (Pred M)).length := List.length_pos_of_ne_nil hBrPne
        have hmap := Br_Pred_len_map_smp M hR hmono hBrne hj1gt
        have hJNleJ1 : (Br (Pred M)).length - 1 ≤ (Br M).length - 1 := by
          split at hmap <;> omega
        have hidxle := joint_idx_mono M ((Br (Pred M)).length - 1) ((Br M).length - 1) hD
          hJNleJ1 hJ1Br
        have hj0N : 0 < (Joints M).getD ((Br (Pred M)).length - 1) 0 := by omega
        have hFNJ := FNJ_Pred_at_JPm1_smp M hM hmono hBrne (by omega) hBrPne
        have hj0Npred : 0 < (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 := by
          rw [hFNJ.2]; exact hj0N
        have ihP := ih (Lng (Pred M)) (by omega) (Pred M) hpredDT hBrPne hj0Npred rfl
        have hJNlt : (Br (Pred M)).length - 1 < (Br M).length := by omega
        have hjNleTr := (FirstNodes_TrMax_Joints M ((Br (Pred M)).length - 1) hM hmono
          hJNlt).1
        have hentryAgree :
            entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
              entry M 1 ((Joints M).getD ((Br (Pred M)).length - 1) 0) := by
          rw [hFNJ.2]
          exact entry_Pred M 1 _ (by omega)
        have hthrm := thrmono M ((Br (Pred M)).length - 1) ((Br M).length - 1) hD
          hJNleJ1 hJ1Br
        omega
    -- 2./3. `Adm0` / `Admpos` の分岐
    by_cases hAdm0 : transJm1 M = 0
    · -- joint の行 1 読み出しと first node の行 0 同定
      have hrow1j0 := joint_row1_eq M ((Br M).length - 1) hD hJ1Br
      have hc0FN := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1Br
      rcases keystone M hR hmono hBrne hj1gt with A | A | A | A
      · -- keystone (1)
        obtain ⟨hj1eq, -, hor, hex⟩ := A
        obtain ⟨t1, ⟨-, hT⟩, -⟩ := hex
        have hrn1 : (RightNodes (Trans M)).getD 1 0 =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
          rw [hT]; exact rn1_outer_inner_trailing_smp _ _ _ _
        have hjeq : (Joints M).getD ((Br M).length - 1) 0 = transJ0 M := by
          rw [Joints_getD M _ hJ1Br, hj1eq]
          rfl
        have hnadm : adm M ((Joints M).getD ((Br M).length - 1) 0) = false := by
          by_contra hcon
          have hadm : adm M ((Joints M).getD ((Br M).length - 1) 0) = true := by
            simpa using hcon
          have hAdmeq : Adm M (transJ0 M) = (Joints M).getD ((Br M).length - 1) 0 := by
            rw [← hjeq, Adm, if_pos hadm]
          rw [transJm1, hAdmeq] at hAdm0
          omega
        have he0e1 : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
          rcases hor with h | h
          · exact h
          · rw [hnadm] at h; exact absurd h Bool.false_ne_true
        omega
      · -- keystone (2)
        obtain ⟨-, -, -, hex⟩ := A
        obtain ⟨t12, ⟨-, hT⟩, -⟩ := hex
        have hrn1 : (RightNodes (Trans M)).getD 1 0 =
            entry M 1 ((Joints M).getD ((Br M).length - 1) 0) := by
          rw [hT]; exact rn1_outer_inner_trailing_smp _ _ _ _
        omega
      · -- keystone (3): `Pred` と末尾 head を共有
        obtain ⟨t123, ⟨hC, hT⟩, -⟩ := A
        have hrn1M : (RightNodes (Trans M)).getD 1 0 =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
          rw [hT]; exact rn1_outer_inner_trailing_smp _ _ _ _
        have hrn1P : (RightNodes (Trans (Pred M))).getD 1 0 =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
          rw [hC]; exact rn1_outer_inner_trailing_smp _ _ _ _
        omega
      · -- keystone (4)
        obtain ⟨t123, ⟨-, hT⟩, -⟩ := A
        have hrn1 : (RightNodes (Trans M)).getD 1 0 =
            entry M 1 ((Joints M).getD ((Br M).length - 1) 0) := by
          rw [hT]; exact rn1_outer_inner_trailing_smp _ _ _ _
        omega
    · -- `Admpos`: `RightNodes` は `Pred` から保存される
      have hRNeq := wid_step scbOuterSurgerySplit_holds M hR hmono hj1gt
        (by omega) ht1ne
      omega

/-! ## factA 本体（Isabelle `m_8_2_factA` 34540 ／`m_8_2_factA_uncond` 35084）

`Lng` に関する強帰納法。全幹の基底は `factA_base_smp`、再帰段は `Pred M` 上の IH を
抽象エンジン `wit_step_thr`（＝ Isabelle `m_8_2_factA_step` の一般形）に流し込む。
側条件 2 本は `thrmono` ＋ 添字翻訳（`Br_Pred_len_map_smp` /
`FNJ_Pred_at_JPm1_smp`）と、無条件化された `newdom`。 -/

/-- Isabelle `m_8_2_subexpr_leftend_unique` (`layerB/pss_wip.thy:14900`)。
`8.2-subexpr-component-strongmono` では `private` なのでここに再掲する。 -/
private theorem leftend_unique_smp (M : PS) (hMD : DTPS M) :
    ∃! t' : BT, Trans M = Dprin (entry M 1 0 : ℕ∞) t' := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := DTPS_TPS M hMD
  have hzf : zeroT M = false := by
    unfold monoT at hmono
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmono
    exact hmono.1
  have htne : Trans M ≠ BZero := by
    intro hz
    have := (Trans_preserves_zeroT M hM).mpr hz
    rw [this] at hzf
    exact Bool.noConfusion hzf
  rcases Trans_mono_leftend_form M hR hmono with hzero | ⟨t, ht⟩
  · exact absurd hzero htne
  · refine ⟨t, ht, ?_⟩
    intro y hy
    rw [ht] at hy
    simpa [Dprin] using hy.symm

/-- Isabelle `m_8_2_factA` (`layerB/pss_wip.thy:34540`) ＋
`m_8_2_factA_uncond` (35084)。**無条件**（Isabelle の `newdomH` は
`newdom` で放電済み）。 -/
theorem factA (M : PS) (a : BT) (hD : DTPS M) (hBrne : Br M ≠ [])
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0) :
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p
        = true := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M a with
  | _ n ih =>
    subst hn
    obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
    have hM : TPS M := RTPS_TPS M hR
    have hne := trmax_ne_of_Brne_smp M hBrne
    have htb := TrMax_bound M hM
    have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
    have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
    have hLge2 : 1 < Lng M := by omega
    by_cases hBrPe : Br (Pred M) = []
    · exact factA_base_smp M a hD hBrne hBrPe aW hj0pos (newdom M hD hBrne hj0pos)
    · have hBrPne : Br (Pred M) ≠ [] := hBrPe
      have hBrPL : 0 < (Br (Pred M)).length := List.length_pos_of_ne_nil hBrPne
      have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hLge2
      have hPT : TPS (Pred M) := Pred_TPS M hM
      have hLP0 : 0 < Lng (Pred M) := List.length_pos_of_ne_nil hPT
      have hTrPne := trmax_ne_of_Brne_smp (Pred M) hBrPne
      have htbP := TrMax_bound (Pred M) hPT
      have hLPg1 : 1 < Lng (Pred M) := by omega
      have hj1gt : 1 < Lng M - 1 := by omega
      have hLPlt : Lng (Pred M) < Lng M := by omega
      have hpredDT := descending_Br_Pred M hD hBrne hLPg1
      have he10P : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hLge2
      obtain ⟨aP, hpredW0, -⟩ := leftend_unique_smp (Pred M) hpredDT
      have predW : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) aP := by
        rw [hpredW0, he10P]
      -- 添字翻訳 `JN = Lng (Br (Pred M)) - 1 ∈ {J₁, J₁ - 1}`
      have hmap := Br_Pred_len_map_smp M hR hmono hBrne hj1gt
      have hJNleJ1 : (Br (Pred M)).length - 1 ≤ (Br M).length - 1 := by
        split at hmap <;> omega
      have hidxle := joint_idx_mono M ((Br (Pred M)).length - 1) ((Br M).length - 1) hD
        hJNleJ1 hJ1Br
      have hj0N : 0 < (Joints M).getD ((Br (Pred M)).length - 1) 0 := by omega
      have hFNJ := FNJ_Pred_at_JPm1_smp M hM hmono hBrne hLge2 hBrPne
      have hj0Npred : 0 < (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 := by
        rw [hFNJ.2]; exact hj0N
      have ihA := ih (Lng (Pred M)) hLPlt (Pred M) aP hpredDT hBrPne hpredW0 hj0Npred rfl
      -- 閾値の単調性
      have hJNlt : (Br (Pred M)).length - 1 < (Br M).length := by omega
      have hjNleTr := (FirstNodes_TrMax_Joints M ((Br (Pred M)).length - 1) hM hmono
        hJNlt).1
      have htrlt : TrMax M < Lng M - 1 := by omega
      have hentryAgree :
          entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
            entry M 1 ((Joints M).getD ((Br (Pred M)).length - 1) 0) := by
        rw [hFNJ.2]
        exact entry_Pred M 1 _ (by omega)
      have hthrm := thrmono M ((Br (Pred M)).length - 1) ((Br M).length - 1) hD
        hJNleJ1 hJ1Br
      have hthr : entry M 1 ((Joints M).getD ((Br M).length - 1) 0) ≤
          entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) := by
        omega
      exact wit_step_thr M a aP (entry M 1 ((Joints M).getD ((Br M).length - 1) 0))
        (entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0))
        aW predW ihA hthr (newdom M hD hBrne hj0pos)
        (keystone M hR hmono hBrne hj1gt)

/-! ## Prop の放電（house pattern） -/

/-- `8.2-subexpr-component-strongmono` の名前付き `Prop` `SXSM_factA_uncond`
（Isabelle `m_8_2_factA_uncond`, `layerB/pss_wip.thy:35084`）を閉じる。 -/
theorem sxsm_factA_uncond_holds : SXSM_factA_uncond := by
  intro M a hMD hBrne haW hj0pos
  exact factA M a hMD hBrne haW hj0pos

/-! ## `branch_row1_le_TrMax`（Isabelle `m_8_2_branch_row1_le_TrMax` 35459）

`8.2-condV-rightmost-parent` に `private` (`_cv`) で存在するが公開されていないので、
同じ証明をここに再掲する（suffix `_smp`）。widH の `Admpos ∧ j′₁ = j₁` 分岐と
factB の全幹基底の閾値がこれを要求する。 -/

private theorem leR0_bounds_smp (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の先頭は列内（Isabelle `a1_FN_lt`）。 -/
private theorem FN_lt_smp (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M := by
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  exact (leR0_bounds_smp M _ _ (nextR_implies_row0 M 0 _ _ hnxJ).2).2

private theorem nextR1_TrMax_fail_smp (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hx : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j < TrMax M + 1, nextR M 1 j (j + 1) = true := by
        intro j hj
        by_cases hlt : j < TrMax M
        · exact TrMax_trunk_step M j hM hlt
        · have hjeq : j = TrMax M := by omega
          rw [hjeq]
          exact hx
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

private theorem wit_FirstNodes0_smp (M : PS) (hBrne : Br M ≠ []) :
    (FirstNodes M).getD 0 0 = TrMax M + 1 := by
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have h := FirstNodes_getD M 0 hBrpos
  have hidx : (IdxSum (Br M)).getD 0 0 = 0 := by
    have h0 := idxSum_getD (Br M) 0 (Nat.zero_le _)
    simpa using h0
  omega

private theorem e1_le_e1par_of_notnextR1_smp (M : PS) (j : ℕ) (hM : TPS M)
    (hp0 : hasParent M 0 j = true) (hjL : j < Lng M)
    (hnotnx : nextR M 1 (parent M 0 j) j = false) :
    entry M 1 j ≤ entry M 1 (parent M 0 j) := by
  have hparR := hasParent_next_fseq M 0 j hp0
  have hplt : parent M 0 j < j := (nextR_implies_row0 M 0 _ j hparR).1
  have hleR : leR M 0 (parent M 0 j) j = true :=
    (nextR_implies_row0 M 0 _ j hparR).2
  by_contra hgt
  have helt : entry M 1 (parent M 0 j) < entry M 1 j := by omega
  obtain ⟨p1, hp1ge, hp1lt, hp1nx⟩ :=
    parent_exists_2 M (parent M 0 j) j hM hplt hjL helt hleR
  have hp1nx1 : nextrel1 M p1 j = true := by simpa [nextR] using hp1nx
  have hle0p1 : le0 M p1 j = true := by
    have hh := hp1nx1
    simp only [nextrel1, Bool.and_eq_true] at hh
    exact hh.1.2
  have hp1le : p1 ≤ parent M 0 j :=
    le0_above_parent M p1 j hp0 hle0p1 (by omega)
  have hp1eq : p1 = parent M 0 j := by omega
  rw [hp1eq] at hp1nx
  rw [hp1nx] at hnotnx
  exact Bool.noConfusion hnotnx

private theorem branch_row1_le_TrMax_of_notnextR_smp (M : PS) (J : ℕ)
    (hD : DTPS M) (hJ : J < (Br M).length)
    (hnotnx : nextR M 1 (TrMax M) ((FirstNodes M).getD J 0) = false) :
    entry M 1 ((FirstNodes M).getD J 0) ≤ entry M 1 (TrMax M) := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hcol0 : entry M 0 0 = entry M 1 0 := RedCondB_head_eq M hM hB
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htoffj0 := trunk_entries_offset M hM hA ((Joints M).getD J 0) hgeom.1
  have htofft := trunk_entries_offset M hM hA (TrMax M) (le_refl _)
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hfL : (FirstNodes M).getD J 0 < Lng M := FN_lt_smp M J hM hmono hJ
  have hpar0 : parent M 0 ((FirstNodes M).getD J 0) = (Joints M).getD J 0 :=
    parent_eq_of_nextR0 M _ _ hnxJ
  have hp0 : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    mono_hasParent_row0 M hM hmono _ (by omega) hfL
  have hcoeff : entry M 1 ((FirstNodes M).getD J 0) ≤
      entry M 0 ((FirstNodes M).getD J 0) :=
    reduced_coeff M hR _ hfL
  have hcondA := RedCondA_apply M hA 0 ((FirstNodes M).getD J 0)
    (by omega) hfL hp0
  rw [hpar0] at hcondA
  by_cases hlt : (Joints M).getD J 0 < TrMax M
  · omega
  · have hj0t : (Joints M).getD J 0 = TrMax M := by omega
    have hnotnx' : nextR M 1 (parent M 0 ((FirstNodes M).getD J 0))
        ((FirstNodes M).getD J 0) = false := by
      rw [hpar0, hj0t]
      exact hnotnx
    have hle := e1_le_e1par_of_notnextR1_smp M ((FirstNodes M).getD J 0)
      hM hp0 hfL hnotnx'
    rw [hpar0] at hle
    omega

private theorem branch_row1_le_TrMax_J0_smp (M : PS) (hD : DTPS M)
    (hBrne : Br M ≠ []) :
    entry M 1 ((FirstNodes M).getD 0 0) ≤ entry M 1 (TrMax M) := by
  have hM : TPS M := DTPS_TPS M hD
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hf0 := wit_FirstNodes0_smp M hBrne
  have hnotnx : nextR M 1 (TrMax M) ((FirstNodes M).getD 0 0) = false := by
    rw [hf0]
    exact nextR1_TrMax_fail_smp M hM
  exact branch_row1_le_TrMax_of_notnextR_smp M 0 hD hBrpos hnotnx

/-- Isabelle `m_8_2_branch_row1_le_TrMax` (`layerB/pss_wip.thy:35459`)。 -/
private theorem branch_row1_le_TrMax_smp (M : PS) (J : ℕ)
    (hD : DTPS M) (hJ : J < (Br M).length) :
    entry M 1 ((FirstNodes M).getD J 0) ≤ entry M 1 (TrMax M) := by
  obtain ⟨hR, hmono, hdesc⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hA, hB⟩ := RTPS_condAB M hR
  have hBrne : Br M ≠ [] := by
    intro h
    rw [h] at hJ
    simp at hJ
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hgeom := FirstNodes_TrMax_Joints M J hM hmono hJ
  have htofft := trunk_entries_offset M hM hA (TrMax M) (le_refl _)
  have hfL : (FirstNodes M).getD J 0 < Lng M := FN_lt_smp M J hM hmono hJ
  have hcoeff : entry M 1 ((FirstNodes M).getD J 0) ≤
      entry M 0 ((FirstNodes M).getD J 0) :=
    reduced_coeff M hR _ hfL
  have hc0FN := entry_FirstNodes_eq_component_mr M J 0 hM hJ
  have hc0val := branch_col0_val M J hD hJ
  by_cases hlt : (Joints M).getD J 0 < TrMax M
  · omega
  · have hj0t : (Joints M).getD J 0 = TrMax M := by omega
    by_cases hJ0 : J = 0
    · rw [hJ0]
      exact branch_row1_le_TrMax_J0_smp M hD hBrne
    · have hJpos : 0 < J := Nat.pos_of_ne_zero hJ0
      have hmonoJ : (Joints M).getD J 0 ≤ (Joints M).getD 0 0 :=
        (FirstNodes_Joints_mono M 0 J hM hmono hJpos hJ).2.1
      have hj00le : (Joints M).getD 0 0 ≤ TrMax M :=
        (FirstNodes_TrMax_Joints M 0 hM hmono hBrpos).1
      have hj00t : (Joints M).getD 0 0 = TrMax M := by omega
      have hc0val0 := branch_col0_val M 0 hD hBrpos
      have hrow0eq : entry ((Br M).getD 0 []) 0 0 =
          entry ((Br M).getD J []) 0 0 := by omega
      have hcd : cdomB ((Br M).getD 0 []) ((Br M).getD J []) = true :=
        (descendingB_iff (Br M)).mp hdesc 0 J (Nat.zero_le J) hJ
      have hrow1le : entry ((Br M).getD J []) 1 0 ≤
          entry ((Br M).getD 0 []) 1 0 :=
        ((cdomB_iff _ _).mp hcd).2 hrow0eq
      have hc1FN := entry_FirstNodes_eq_component_mr M J 1 hM hJ
      have hc1FN0 := entry_FirstNodes_eq_component_mr M 0 1 hM hBrpos
      have hb0le := branch_row1_le_TrMax_J0_smp M hD hBrne
      omega

/-! ## `widH`（Isabelle `m_8_2_widH` 35857）

factB が要求する「新 head の支配」の first-node 版
`M₁,j′₁ ≤ RightNodes(Trans M)₁`。`newdom` と同じく `Lng` の強帰納法。 -/

/-- Isabelle `m_8_2_widH_base2` (`layerB/pss_wip.thy:35804`)。 -/
private theorem widH_base2_smp (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (hL2 : Lng Q = 2) (hBrne : Br Q ≠ []) :
    entry Q 1 ((FirstNodes Q).getD ((Br Q).length - 1) 0) ≤
      (RightNodes (Trans Q)).getD 1 0 := by
  have hQT : TPS Q := RTPS_TPS Q hR
  have htb := TrMax_bound Q hQT
  have hne := trmax_ne_of_Brne_smp Q hBrne
  have hTr0 : TrMax Q = 0 := by omega
  have hBrL : 0 < (Br Q).length := List.length_pos_of_ne_nil hBrne
  have hJ1Br : (Br Q).length - 1 < (Br Q).length := by omega
  have hFNlo := (FirstNodes_TrMax_Joints Q _ hQT hmono hJ1Br).2
  have hFNhi := FN_lt_smp Q _ hQT hmono hJ1Br
  have hFN1 : (FirstNodes Q).getD ((Br Q).length - 1) 0 = 1 := by omega
  rw [hFN1, two_column_Trans Q hR hmono hL2, RightNodes_Dprin, RightNodes_Dprin]
  simp

/-- Isabelle `m_8_2_widH` (`layerB/pss_wip.thy:35857`)。**無条件**。 -/
theorem widH (M : PS) (hD : DTPS M) (hBrne : Br M ≠ []) (hL : 1 < Lng M) :
    entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ≤
      (RightNodes (Trans M)).getD 1 0 := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hn
    obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
    have hM : TPS M := RTPS_TPS M hR
    obtain ⟨hA, -⟩ := RTPS_condAB M hR
    have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
    have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
    by_cases hlen3 : 2 < Lng M
    · have hj1gt : 1 < Lng M - 1 := by omega
      rcases (wid_iff M).mp (keystone_imp_wid M (keystone M hR hmono hBrne hj1gt))
        with hj1side | hj0side
      · omega
      · by_cases hAdm0 : transJm1 M = 0
        · have hnotVI := notVI_Adm0 M hR hmono hBrne hj1gt hAdm0
          have hj1eqK := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
          by_cases hcond : (transCondI M || transCondIII M || transCondV M) = true
          · obtain ⟨-, -, -, hex⟩ :=
              subexpr_component_Pred_Adm0_clause1_keystone M hR hmono hj1gt hAdm0 hcond
                hj1eqK (gA_Adm0 M hR hmono hBrne hj1gt hAdm0)
                (gB_Adm0_condA M hR hmono hBrne hj1gt hAdm0 hcond)
            obtain ⟨t1, ⟨-, hT⟩, -⟩ := hex
            have hrn1 : (RightNodes (Trans M)).getD 1 0 =
                entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
              rw [hT]; exact rn1_outer_inner_trailing_smp _ _ _ _
            omega
          · have hnotA : ¬(transCondI M = true ∨ transCondIII M = true ∨
                transCondV M = true) := by
              intro h
              exact hcond (by simp only [Bool.or_eq_true]; tauto)
            have he0gt : entry M 1 (Lng M - 1) < entry M 0 (Lng M - 1) := by
              rcases condII_or_condIV M hR hmono (by omega) hnotA hnotVI with hII | hIV
              · have he1z : entry M 1 (Lng M - 1) = 0 := by
                  simp only [transCondII, Bool.and_eq_true, beq_iff_eq] at hII
                  simpa [lastIdx] using hII.1
                exact e0gt_e1zero M hM hmono (by omega) he1z
              · exact e0gt_condIV M hR hmono (by omega) hIV
            rw [← hj1eqK] at he0gt
            have hrow1j0 := joint_row1_eq M ((Br M).length - 1) hD hJ1Br
            have hc0FN := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1Br
            omega
        · by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
          · have hj0t := j0_eq_TrMax M hR hmono hBrne hj1gt (by omega) hj1eq
            rw [hj0t] at hj0side
            have hbnd := branch_row1_le_TrMax_smp M ((Br M).length - 1) hD hJ1Br
            omega
          · have hne := trmax_ne_of_Brne_smp M hBrne
            have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M (by omega)
            have hLPg1 : 1 < Lng (Pred M) := by omega
            have hpredDT := descending_Br_Pred M hD hBrne hLPg1
            obtain ⟨hPR, hPmono, -⟩ := (DTPS_iff (Pred M)).mp hpredDT
            have hPT : TPS (Pred M) := RTPS_TPS (Pred M) hPR
            have hnzP : zeroT (Pred M) = false := by
              simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
              exact Or.inl (by omega)
            have ht1ne : Trans (Pred M) ≠ BZero := by
              intro hz
              rw [(Trans_preserves_zeroT (Pred M) hPT).mpr hz] at hnzP
              exact Bool.noConfusion hnzP
            have hRNeq := wid_step scbOuterSurgerySplit_holds M hR hmono hj1gt
              (by omega) ht1ne
            by_cases hBrPe : Br (Pred M) = []
            · have hTrPe := baseU_Br_empty_TrMax (Pred M) hBrPe
              have hRNP := baseU_alltrunk_Trans_RN1 (Pred M) hPR hPmono hTrPe hLPg1
              have hdiag :=
                (baseU_alltrunk_diag_entry (Pred M) (Lng (Pred M) - 1) hPR hPmono hTrPe
                  (by omega)).2
              have hTrP := TrMax_Pred_nontrunk M hM (by omega) hne
              have he10P := entry_Pred_zero M 1 (by omega)
              have hbnd := branch_row1_le_TrMax_smp M ((Br M).length - 1) hD hJ1Br
              have htofft := (trunk_entries_offset M hM hA (TrMax M) (le_refl _)).2
              omega
            · have hBrPne : Br (Pred M) ≠ [] := hBrPe
              have ihP := ih (Lng (Pred M)) (by omega) (Pred M) hpredDT hBrPne hLPg1 rfl
              have hft := ft_transport M hR hmono hBrne hj1gt hBrPne hj1eq
              omega
    · exact widH_base2_smp M hR hmono (by omega) hBrne

/-! ## factB（Isabelle `m_8_2_factB` 36200）

原文 (2) の側条件 `C(M)`（`j′₀ = 0` または `M₀,j′₁ = M₁,j′₁`）の下での leaf 下界。
`Lng` の強帰納法。基底は `Lng M = 2`（`factB_base2_smp`）と全幹 `Pred`
（`alltrunk_base_thr_smp`、閾値は `branch_row1_le_TrMax_smp`、新 head 支配は
`widH`）。再帰段は `wit_step_thr`（閾値は leaf に固定＝`thrmono` は反射律）で、
IH が `prefixB` を供給する。 -/

private theorem PB_mem_Dprin_smp {a r : BT} (hr : r ∈ PB a) : ∃ v c, r = Dprin v c := by
  simp only [PB, List.mem_map] at hr
  obtain ⟨p, -, rfl⟩ := hr
  rcases p with ⟨v, c⟩
  exact ⟨v, c, rfl⟩

/-- Isabelle `wit_PB_relax` (`layerB/pss_wip.thy:33742`)。 -/
private theorem wit_PB_relax_smp (a : BT) (thr thr' : ℕ)
    (L : ∀ r ∈ PB a, leBT (Dprin (thr' : ℕ∞) BZero) r = true) (hle : thr ≤ thr') :
    ∀ r ∈ PB a, leBT (Dprin (thr : ℕ∞) BZero) r = true := by
  intro r hr
  obtain ⟨v, c, rfl⟩ := PB_mem_Dprin_smp hr
  have h1 : (thr' : ℕ∞) ≤ v := (leBT_Dprin0_iff_smp _ _ _).mp (L _ hr)
  have h2 : (thr : ℕ∞) ≤ (thr' : ℕ∞) := by exact_mod_cast hle
  exact (leBT_Dprin0_iff_smp _ _ _).mpr (le_trans h2 h1)

/-- 全幹 `Pred` の基底、閾値を一般化した形（`factA_base_smp` /
Isabelle `m_8_2_factB_base` 35008 の共通骨格）。 -/
private theorem alltrunk_base_thr_smp (M : PS) (a : BT) (thr : ℕ) (hD : DTPS M)
    (hBrne : Br M ≠ []) (hBrPe : Br (Pred M) = []) (hLge3 : 2 < Lng M)
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (hthr : thr ≤ entry M 1 0 + TrMax M)
    (hnewdom : thr ≤ (RightNodes (Trans M)).getD 1 0) :
    ∀ p ∈ PB a, leBT (Dprin (thr : ℕ∞) BZero) p = true := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hD
  have hM : TPS M := RTPS_TPS M hR
  have hne := trmax_ne_of_Brne_smp M hBrne
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M (by omega)
  have hTrP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM (by omega) hne
  have hTrPe : TrMax (Pred M) = Lng (Pred M) - 1 := baseU_Br_empty_TrMax (Pred M) hBrPe
  have hLPg1 : 1 < Lng (Pred M) := by omega
  obtain ⟨hPR, hPmono, -⟩ := (DTPS_iff (Pred M)).mp (descending_Br_Pred M hD hBrne hLPg1)
  have huP : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 (by omega)
  have htower := alltrunk_Trans_tower_smp (Pred M) hPR hPmono hTrPe hLPg1
  have hvlast : entry (Pred M) 1 (Lng (Pred M) - 1) = entry M 1 0 + TrMax M := by
    have hd :=
      (baseU_alltrunk_diag_entry (Pred M) (Lng (Pred M) - 1) hPR hPmono hTrPe (by omega)).2
    omega
  have predW : Trans (Pred M) =
      Dprin (entry M 1 0 : ℕ∞) (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero) := by
    rw [htower, huP, hvlast]
  have ihA : ∀ r ∈ PB (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero),
      leBT (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero) r = true := by
    intro r hr
    rw [PB_Dprin_single_smp] at hr
    rw [List.mem_singleton.mp hr]
    exact (leBT_Dprin0_iff_smp _ _ _).mpr le_rfl
  exact wit_step_thr M a (Dprin ((entry M 1 0 + TrMax M : ℕ) : ℕ∞) BZero) thr
    (entry M 1 0 + TrMax M) aW predW ihA hthr hnewdom
    (keystone M hR hmono hBrne (by omega))

/-- Isabelle `m_8_2_factB_base2` (`layerB/pss_wip.thy:36142`)。 -/
private theorem factB_base2_smp (M : PS) (a : BT) (hR : RTPS M) (hmono : monoT M = true)
    (hL2 : Lng M = 2) (hBrne : Br M ≠ [])
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a) :
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p
        = true := by
  have hMT : TPS M := RTPS_TPS M hR
  have htb := TrMax_bound M hMT
  have hne := trmax_ne_of_Brne_smp M hBrne
  have hTr0 : TrMax M = 0 := by omega
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
  have hFNlo := (FirstNodes_TrMax_Joints M _ hMT hmono hJ1Br).2
  have hFNhi := FN_lt_smp M _ hMT hmono hJ1Br
  have hFN1 : (FirstNodes M).getD ((Br M).length - 1) 0 = 1 := by omega
  have hT := two_column_Trans M hR hmono hL2
  have haeq : a = Dprin (entry M 1 1 : ℕ∞) BZero := by
    rw [aW] at hT; simpa [Dprin] using hT
  intro p hp
  rw [haeq, PB_Dprin_single_smp] at hp
  rw [List.mem_singleton.mp hp, hFN1]
  exact (leBT_Dprin0_iff_smp _ _ _).mpr le_rfl

/-- Isabelle `m_8_2_branch_row1_tiebreak` (`layerB/pss_wip.thy:34990` 付近)。
`descending (Br M)` の第 2 成分（行 0 同点なら行 1 も降順）。 -/
private theorem branch_row1_tiebreak_smp (M : PS) (JN J1 : ℕ) (hD : DTPS M)
    (hJNJ1 : JN ≤ J1) (hJ1Br : J1 < (Br M).length)
    (tie : entry ((Br M).getD JN []) 0 0 = entry ((Br M).getD J1 []) 0 0) :
    entry ((Br M).getD J1 []) 1 0 ≤ entry ((Br M).getD JN []) 1 0 := by
  obtain ⟨-, -, hdesc⟩ := (DTPS_iff M).mp hD
  exact ((cdomB_iff _ _).mp ((descendingB_iff (Br M)).mp hdesc JN J1 hJNJ1 hJ1Br)).2 tie

/-- Isabelle `wid_FN_Suc_lt` (`layerB/pss_wip.thy:36099`)。枝成分は非空なので
`FirstNodes` は狭義単調。 -/
private theorem FN_Suc_lt_smp (M : PS) (hM : TPS M) (J : ℕ)
    (hSuc : J + 1 < (Br M).length) :
    (FirstNodes M).getD J 0 < (FirstNodes M).getD (J + 1) 0 := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    rw [show Br M = [] by simp [Br, heq]] at hSuc
    simp at hSuc
  have htb := TrMax_bound M hM
  have hBrseg : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hsegT : TPS (seg M (TrMax M + 1) (Lng M - 1)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M (TrMax M + 1) (Lng M - 1))
    rw [length_seg]
    omega
  have hpos : 0 < Lng ((Br M).getD J []) := by
    rw [hBrseg]
    exact P_component_nonempty _ J hsegT (by rw [← hBrseg]; omega)
  have h1 := FirstNodes_getD M J (by omega)
  have h2 := FirstNodes_getD M (J + 1) hSuc
  have h3 := idxSum_diff (Br M) J (by omega)
  omega

/-- Isabelle `m_8_2_factB` (`layerB/pss_wip.thy:36200`)。**無条件**。 -/
theorem factB (M : PS) (a : BT) (hD : DTPS M) (hBrne : Br M ≠ [])
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (hC : (Joints M).getD ((Br M).length - 1) 0 = 0 ∨
      entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) :
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p
        = true := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M a with
  | _ n ih =>
    subst hn
    obtain ⟨hR, hmono, hdesc⟩ := (DTPS_iff M).mp hD
    have hM : TPS M := RTPS_TPS M hR
    obtain ⟨hA, -⟩ := RTPS_condAB M hR
    have hne := trmax_ne_of_Brne_smp M hBrne
    have htb := TrMax_bound M hM
    have htrlt : TrMax M < Lng M - 1 := by omega
    have hLge2 : 1 < Lng M := by omega
    have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
    have hJ1Br : (Br M).length - 1 < (Br M).length := by omega
    have hj1'lt := FN_lt_smp M ((Br M).length - 1) hM hmono hJ1Br
    by_cases hlen3 : 2 < Lng M
    · have hj1gt : 1 < Lng M - 1 := by omega
      have hwidH := widH M hD hBrne hLge2
      by_cases hBrPe : Br (Pred M) = []
      · have hthr : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
            ≤ entry M 1 0 + TrMax M := by
          have hb := branch_row1_le_TrMax_smp M ((Br M).length - 1) hD hJ1Br
          have ho := (trunk_entries_offset M hM hA (TrMax M) (le_refl _)).2
          omega
        exact alltrunk_base_thr_smp M a _ hD hBrne hBrPe hlen3 aW hthr hwidH
      · have hBrPne : Br (Pred M) ≠ [] := hBrPe
        have hBrPL : 0 < (Br (Pred M)).length := List.length_pos_of_ne_nil hBrPne
        have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hLge2
        have hPT : TPS (Pred M) := Pred_TPS M hM
        have hLP0 : 0 < Lng (Pred M) := List.length_pos_of_ne_nil hPT
        have hTrPne := trmax_ne_of_Brne_smp (Pred M) hBrPne
        have htbP := TrMax_bound (Pred M) hPT
        have hLPg1 : 1 < Lng (Pred M) := by omega
        have hLPlt : Lng (Pred M) < Lng M := by omega
        have hpredDT := descending_Br_Pred M hD hBrne hLPg1
        have he10P : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hLge2
        obtain ⟨aP, hpredW0, -⟩ := leftend_unique_smp (Pred M) hpredDT
        have predW : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) aP := by
          rw [hpredW0, he10P]
        have hmap := Br_Pred_len_map_smp M hR hmono hBrne hj1gt
        have hJNleJ1 : (Br (Pred M)).length - 1 ≤ (Br M).length - 1 := by
          split at hmap <;> omega
        have hJNlt : (Br (Pred M)).length - 1 < (Br M).length := by omega
        have hFNJ := FNJ_Pred_at_JPm1_smp M hM hmono hBrne hLge2 hBrPne
        have hbrvalJN := branch_col0_val M ((Br (Pred M)).length - 1) hD hJNlt
        have hbrvalJ1 := branch_col0_val M ((Br M).length - 1) hD hJ1Br
        have hc0JN := entry_FirstNodes_eq_component_mr M ((Br (Pred M)).length - 1) 0 hM hJNlt
        have hc1JN := entry_FirstNodes_eq_component_mr M ((Br (Pred M)).length - 1) 1 hM hJNlt
        have hc0J1 := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 0 hM hJ1Br
        have hc1J1 := entry_FirstNodes_eq_component_mr M ((Br M).length - 1) 1 hM hJ1Br
        have hjtJNleTr :=
          (FirstNodes_TrMax_Joints M ((Br (Pred M)).length - 1) hM hmono hJNlt).1
        have hjtJNltLM : (Joints M).getD ((Br (Pred M)).length - 1) 0 < Lng M - 1 := by omega
        have prefixB : ∀ r ∈ PB aP,
            leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero) r = true := by
          by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
          · -- CASE B: `JN = J₁ - 1`、leaf は右端
            have hlast := lastBr_len_smp M hM hBrne
            have hBrLenP : (Br (Pred M)).length = (Br M).length - 1 := by
              have hh := Br_Pred_length_smp M hM hLge2 hBrne
              rw [if_pos (by rw [hlast, hj1eq]; omega)] at hh
              exact hh
            have hSucJN : (Br (Pred M)).length - 1 + 1 = (Br M).length - 1 := by omega
            have hfnJNlt := FN_Suc_lt_smp M hM ((Br (Pred M)).length - 1) (by omega)
            rw [hSucJN] at hfnJNlt
            have hfnJNltLM : (FirstNodes M).getD ((Br (Pred M)).length - 1) 0 < Lng M - 1 := by
              omega
            have hcd := (cdomB_iff _ _).mp
              ((descendingB_iff (Br M)).mp hdesc ((Br (Pred M)).length - 1)
                ((Br M).length - 1) hJNleJ1 hJ1Br)
            have hrow0ge := hcd.1
            by_cases hstrict : entry ((Br M).getD ((Br M).length - 1) []) 0 0 <
                entry ((Br M).getD ((Br (Pred M)).length - 1) []) 0 0
            · -- STRICT: `Pred M` 上の factA（joint が正）
              have hj0Npos' : 0 < (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 := by
                rw [hFNJ.2]; omega
              have hihA := factA (Pred M) aP hpredDT hBrPne hpredW0 hj0Npos'
              have hthr_ihA :
                  entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
                    entry M 1 ((Joints M).getD ((Br (Pred M)).length - 1) 0) := by
                rw [hFNJ.2]
                exact entry_Pred M 1 _ (by omega)
              rw [hthr_ihA] at hihA
              have he1jtJN := (trunk_entries_offset M hM hA _ hjtJNleTr).2
              have hcoeffJ1 : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ≤
                  entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) :=
                reduced_coeff M hR _ hj1'lt
              exact wit_PB_relax_smp aP _ _ hihA (by omega)
            · -- TIE: tie-break で閾値、`C(Pred M)` で IH
              have htieEq : entry ((Br M).getD ((Br (Pred M)).length - 1) []) 0 0 =
                  entry ((Br M).getD ((Br M).length - 1) []) 0 0 := by omega
              have htie1 := branch_row1_tiebreak_smp M ((Br (Pred M)).length - 1)
                ((Br M).length - 1) hD hJNleJ1 hJ1Br htieEq
              have hcoeffJN : entry M 1 ((FirstNodes M).getD ((Br (Pred M)).length - 1) 0) ≤
                  entry M 0 ((FirstNodes M).getD ((Br (Pred M)).length - 1) 0) :=
                reduced_coeff M hR _ (FN_lt_smp M _ hM hmono hJNlt)
              have hCP : (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 = 0 ∨
                  entry (Pred M) 0
                      ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
                    entry (Pred M) 1
                      ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) := by
                rcases hC with h | h
                · left
                  rw [hFNJ.2]
                  omega
                · right
                  rw [hFNJ.1,
                    entry_Pred M 0 ((FirstNodes M).getD ((Br (Pred M)).length - 1) 0)
                      hfnJNltLM,
                    entry_Pred M 1 ((FirstNodes M).getD ((Br (Pred M)).length - 1) 0)
                      hfnJNltLM]
                  omega
              have ihres := ih (Lng (Pred M)) hLPlt (Pred M) aP hpredDT hBrPne hpredW0 hCP rfl
              have hthr_ih :
                  entry (Pred M) 1
                      ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
                    entry M 1 ((FirstNodes M).getD ((Br (Pred M)).length - 1) 0) := by
                rw [hFNJ.1]
                exact entry_Pred M 1 _ hfnJNltLM
              rw [hthr_ih] at ihres
              exact wit_PB_relax_smp aP _ _ ihres (by omega)
          · -- CASE A: `JN = J₁`、条件がそのまま転送される
            have hJNJ1 : (Br (Pred M)).length - 1 = (Br M).length - 1 := by
              rw [hmap, if_neg hj1eq]
            have hj1'lt2 : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
              omega
            have hfnP : (FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0 =
                (FirstNodes M).getD ((Br M).length - 1) 0 := by
              rw [hFNJ.1, hJNJ1]
            have he0P := entry_Pred M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) hj1'lt2
            have he1P := entry_Pred M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) hj1'lt2
            have hCP : (Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0 = 0 ∨
                entry (Pred M) 0 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
                  entry (Pred M) 1
                    ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) := by
              rcases hC with h | h
              · left; rw [hFNJ.2, hJNJ1]; exact h
              · right; rw [hfnP, he0P, he1P]; exact h
            have ihres := ih (Lng (Pred M)) hLPlt (Pred M) aP hpredDT hBrPne hpredW0 hCP rfl
            have hthr_ih :
                entry (Pred M) 1 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
                  entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
              rw [hfnP, he1P]
            rw [hthr_ih] at ihres
            exact ihres
        exact wit_step_thr M a aP _ _ aW predW prefixB (le_refl _) hwidH
          (keystone M hR hmono hBrne hj1gt)
    · exact factB_base2_smp M a hR hmono (by omega) hBrne aW

/-- `8.2-subexpr-component-strongmono` の名前付き `Prop` `SXSM_factB`
（Isabelle `m_8_2_factB`, `layerB/pss_wip.thy:36200`）を閉じる。 -/
theorem sxsm_factB_holds : SXSM_factB := by
  intro M a hMD hBrne haW hC
  exact factB M a hMD hBrne haW hC

#print axioms joint_idx_mono
#print axioms thrmono
#print axioms descending_Br_Pred
#print axioms newdom
#print axioms factA
#print axioms widH
#print axioms factB
#print axioms sxsm_factA_uncond_holds
#print axioms sxsm_factB_holds

end PSS
