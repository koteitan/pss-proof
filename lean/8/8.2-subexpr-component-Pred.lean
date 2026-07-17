import «8».«8.2-subexpr-final»
import «8».«8.2-subexpr-adm0-full»
import «8».«8.2-subexpr-admpos-wfin»
import «8».«8.2-subexpr-of-wid»
import «7».«7.2-scb-outer-surgery-split»
import «8».«8.1-diagSeq-Trans»
import «7».«7.3-two-column»
import «6».«6.6-reduced-slice»
import «6».«6.6-P-condAB»
import «6».«6.2-P-additivity»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-welldefined»
import «5».«5.1-ancestor-basic»

/-!
# §8.2 補題（部分表現の単項成分と `Pred` の関係）— **キーストーン無条件化**

- 原文: `tmp/content.md` 3360（§8.2 補題（部分表現の単項成分と `Pred` の関係））、
  および 3432–3435（`j₁ - TrMax(M)` に関する帰納法＝ w-identification）。
  忠実形は `p_8_2_subexpr_component_Pred`（`isabelle/pss_paper.thy:1523`）。
- 訂正: **該当なし**。§8.2 に触れる訂正は `A9`（`LastStep` の添字 `J₁` の範囲外参照
  [軽微]）のみで、これは §8.2「強単項性」節の写像 `LastStep` の定義文に対する補正。
  本ファイルは `J₁ = Lng (Br M) - 1` を `Br M ≠ []` の下でのみ使うため影響しない
  （`8.2-subexpr-setup` / `8.2-subexpr-final` と同一の判断）。

## 本ファイルの位置づけ

`8.2-subexpr-final` は §8.2 キーストーンを 5 本の `SXP_*` Prop に対する
green-modulo で証明していた。本ファイルは**その 5 本すべてを実体化**し、
`keystone`（Isabelle `m_8_2_keystone`）を**無条件**で得る。
うち `SXP_wid_cpU` / `SXP_wid_baseU` は Isabelle `m_8_2_wid` (29605) 自身が
`assumes` として残す 2 本の真正残差であり、Isabelle はそれを下流で放電している。
その連鎖を移植したのが本ファイルの主内容である。

## Isabelle 対応（`isabelle/layerB/pss_wip.thy`）

| Lean | Isabelle | 行 |
|---|---|---|
| `transJ0_eq_TrMax` | `m_8_2_transJ0_eq_TrMax` | 32316 |
| `joints_all_TrMax` | `m_8_2_joints_all_TrMax` | 32350 |
| `branchHigh` | `m_8_2_branchHigh` | 32391 |
| `branchPar` | `m_8_2_branchPar` | 32434 |
| `TrMax_ge_1` | `m_8_2_TrMax_ge_1` | 31683 |
| `descAdm_of_premises` | `m_8_2_descAdm_of_premises` | 31725 |
| `chainOK`（def） | `chainOK`（`function`） | 30726 |
| `chainOK_of_descAdm` | `m_8_2_chainOK_of_descAdm` | 31113 |
| `chainOK_of_branchPar` | `m_8_2_chainOK_of_branchPar` | 31764 |
| `baseU_Br_empty_TrMax` | 同名 | 29985 |
| `baseU_alltrunk_diag_entry` | 同名 | 29996 |
| `baseU_alltrunk_Trans_RN1` | 同名 | 30086 |
| `baseU_twoseg_monoT` | 同名 | 30140 |
| `baseU_caseI_geom` | 同名 | 30155 |
| `baseU` | `m_8_2_baseU` | 30183 |
| `chainOK_imp_widTrM` | `m_8_2_chainOK_imp_widTrM` | 30747 |
| `j0_eq_TrMax` | `m_8_2_j0_eq_TrMax` | 29887 |
| `cpU_rhs_eq` | `m_8_2_cpU_rhs_eq` | 29918 |
| `cpU_of_widTrMaxM` | `m_8_2_cpU_of_widTrMaxM` | 29946 |
| `cpU_of_chainOK` | `m_8_2_cpU_of_chainOK` | 30841 |
| `wid_uncond` | `m_8_2_wid_uncond` | 30460 |
| `subexpr_component_Pred_final` | `m_8_2_subexpr_component_Pred_final` | 30518 |
| `subexpr_component_Pred_via_chainOK` | 同名（`m_8_2_` 落ち） | 30864 |
| `subexpr_component_Pred_done` | 同名（`m_8_2_` 落ち） | 31789 |
| **`keystone`** | **`m_8_2_keystone`** | **32461** |
| `keystone_faithful` | `p_8_2_subexpr_component_Pred` | paper 1523 |

## 証明の骨格（残差 2 本の放電）

* **`SXP_wid_baseU`** ← `baseU`（30183）。`m_8_2_wid` の帰納基底。
  `Br (Pred M) = []`（`Pred M` は全幹＝対角列 → `Trans` は 2 段の塔）または
  `Lng M = 3`（`two_column_Trans`）。どちらも `wid_step` で `M` 側へ運ぶ。
* **`SXP_wid_cpU`** ← `branchPar` → `descAdm` → `chainOK` → `widTrM` → `cpU`。
  素朴な局所条件 `Admpos M ∧ j₁eq M ⟹ widTrM M` は**偽**（Isabelle 30713 の
  反例 `M = (0,0)(1,0)(1,1)(2,0)`）。正しい道具は再帰述語 `chainOK`
  （「`Pred`-降下が `Br (Pred ..) = []` まで `Admpos` ＋ `good` を保つ」）で、
  これを平坦な `descAdm`（幹を超える全接頭辞の `transJm1 > 0`）に潰し、
  さらに純粋に幾何的な `branchPar`（幹を超える列の行 0 の親は幹右端以降）へ還元する。
  `branchPar` 自体は `joints_all_TrMax` ＋ `branchHigh` ＋ `nextR0_largest_below`
  で**無条件**に落ちる。

## 依存（ビルド済ツールボックス）

- `8.2-subexpr-final`（`wid_holds` / `subexpr_component_Pred` / `SXP_*` の 5 Prop）
- `8.2-subexpr-adm0-full`（`subexpr_component_Pred_Adm0_full` 無条件、
  `subexpr_component_Pred_Admpos_of_wid`、`TransAdmposBodySplitWfin`）
- `8.2-subexpr-admpos-wfin`（`trans_admpos_body_split_wfin`）／`8.2-subexpr-of-wid`
- `8.2-subexpr-admpos-engine`（`ScbOuterSurgerySplit` / `wid_step` / `wid_of_predwid`）
  ＋ `7.2-scb-outer-surgery-split`（`scb_outer_surgery_split` がそれを放電）
- `8.2-subexpr-wid`（`wid` / `wid_iff` / `jt_transport` / `ft_transport`）
- `8.1-diagSeq-Trans`（`diagSeq_Trans`）, `7.3-two-column`（`two_column_Trans`）,
  `7.3-Trans-preserves-zeroT`, `6.6-reduced-iff-condAB`（`RTPS_condAB`）,
  `6.6-P-condAB`（`mono_hasParent_row0`）, `6.5-Red-Pred-commute`
  （`RTPS_Pred` / `length_Pred` / `entry_Pred` / `TrMax_Pred_nontrunk` /
  `monoT_Pred_long` / `Pred_eq_take`）, `6.4`（`TrMax_bound` / `Joints_getD` /
  `FirstNodes_getD` / `FirstNodes_TrMax_Joints` / `FirstNodes_Joints_mono` /
  `Joints_nextR_FirstNodes` / `branch_component_le0` / `nextR0_largest_below` /
  `idxSum_getD`）, `6.3`（`Adm_adm` / `Adm_le` / `Adm_max` / `admof_slice` /
  `nextR_seg_adm`）, `5.1-ancestor-basic`（`ancestor_basic_1`）。

## 罠（本ファイルで実際に踏んだもの）

- `Lng Q` と `List.length Q` は **omega の別アトム**（`baseU_alltrunk_Trans_RN1` の
  `List.ext_getElem` 長さ枝で `have : List.length Q = Lng Q := rfl` の橋渡しが必要）。
- `ℕ∞` の塔から `RightNodes` を読むとき、指数が**複合式**だと `simp` が
  `↑(a + b)` を `↑a + ↑b` に押し込んで `toNat` が潰せなくなる。
  値を `entry Q 1 (Lng Q - 1)` のような**アトムのまま**保って `rw` すること。
- `nextrel1` の谷条件は `le0` ガード付き。omega に渡す前に `simp [hak', hle0k]` で
  ガードを潰す（omega は `le0 .. = true` を扱えない）。
- `omega` は合同性を持たない: `hJeq : J = n` があっても `(Joints M).getD J 0` を
  `(Joints M).getD n 0` には**しない**。先に `rw [hJeq]`。

## 敵対的数値監査（`python/audit_82_chainOK.py`）

実標準形プール 14,618 形（`diagSeq`→`oper` 閉包＋祖先切片 `Red`＋`Pred` 閉包、
maxlen 15／成分 ≤ 19。`audit_82_subexpr` の検証済ヘルパ層を再利用）で
**反例 0**。主な非空虚数: `keystone` の読み出し（`wid M`）14,566／
`chainOK_of_descAdm` 8,316／`chainOK_imp_widTrM` 8,254／`baseU` 102／
`branchPar` 系 80／`cpU` 系 18。
負制御も想定通り: ①素朴な局所条件 `Admpos ∧ good ⟹ widTrM` は 14,417 例中
**3,000 反例**（＝プールが `chainOK` の存在理由である非局所性を実際に検出している）
②`chainOK ⟺ good ∧ TrMax ≥ 1 ∧ descAdm` は 14,618/**0 不一致**（Isabelle wip 31108 と一致）。

⚠️ **監査の発見（健全性ではない）**: Isabelle wip 30713 のコメントは
「`Admpos M ∧ j₁eq M ⟹ widTrM M` は偽、反例 `(0,0)(1,0)(1,1)(2,0)`」と書くが、
この反例は **`j₁eq` を満たさない**（`FirstNodes[J₁] = 2 ≠ 3 = Lng - 1`）。
実際に反証されるのは `Admpos ∧ good ⟹ widTrM` の方で、**Isabelle 側コメントの
前提集合が不正確**（数学は無傷: `widTrM` は確かに非局所で `chainOK` は必要、
引用された列も確かに反例＝より弱い主張に対する）。整合的に
`Admpos ∧ j₁eq ⟹ widTrM` はプール 80/80 で成立する——本ファイルが
`j₁eq ∧ Admpos ∧ good ∧ Br (Pred M) ≠ [] ⟹ chainOK M ⟹ widTrM M` を
**証明している**のだから当然である。

## 状態

✅ **`keystone` / `keystone_faithful` 無条件**（`check_lean.py` rc=0、sorry 0、
公開定理 33 本すべての axioms は `[propext, Classical.choice, Quot.sound]`）。
**§8.2 キーストーンはこれで閉じる**（キャンペーンの green-modulo は全廃）。
私的補助は suffix `_ck`。
-/

namespace PSS

/-! ## 私的補助層（suffix `_ck`） -/

/-- 行 1 の幹ステップは `TrMax M` で必ず破れる（wip `nextR1_TrMax_fail` 20680）。 -/
private theorem nextR1_TrMax_fail_ck (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hst : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j, j < TrMax M + 1 → nextR M 1 j (j + 1) = true := by
        intro j hj
        rcases Nat.lt_or_ge j (TrMax M) with h | h
        · exact TrMax_trunk_step M j hM h
        · have hje : j = TrMax M := by omega
          rw [hje]; exact hst
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

/-- Isabelle `adm_TrMax` (wip 20705): 幹の右端は `M` 許容。 -/
private theorem adm_TrMax_ck (M : PS) (hM : TPS M) : adm M (TrMax M) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_ck M hM
  have hno : ¬ Lng M < TrMax M := by omega
  simp [adm, nadm, hnostep, hno]

/-- Isabelle `adm_trunk_interior_nadm` (wip 32280): 幹の内部添字 `0 < j < TrMax M` は
`M` 非許容（行 1 の幹ステップが両側で成立するので `nadm` の第 2 選言が発火）。 -/
private theorem adm_trunk_interior_nadm_ck (M : PS) (j : ℕ) (hM : TPS M)
    (hjpos : 0 < j) (hjlt : j < TrMax M) : adm M j = false := by
  have hs1 : nextR M 1 (j - 1) (j - 1 + 1) = true :=
    TrMax_trunk_step M (j - 1) hM (by omega)
  have hkeq : j - 1 + 1 = j := by omega
  rw [hkeq] at hs1
  have hs2 : nextR M 1 j (j + 1) = true := TrMax_trunk_step M j hM hjlt
  simp [adm, nadm, hs1, hs2]

/-- Isabelle `adm_le_TrMax_cases` (wip 32296): `TrMax M` 以下の `M` 許容な添字は
`0` か `TrMax M` のみ。 -/
private theorem adm_le_TrMax_cases_ck (M : PS) (j : ℕ) (hM : TPS M)
    (ha : adm M j = true) (hjle : j ≤ TrMax M) : j = 0 ∨ j = TrMax M := by
  by_contra hnot
  have hj0 : j ≠ 0 := fun h => hnot (Or.inl h)
  have hjT : j ≠ TrMax M := fun h => hnot (Or.inr h)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjlt : j < TrMax M := lt_of_le_of_ne hjle hjT
  have := adm_trunk_interior_nadm_ck M j hM hjpos hjlt
  rw [this] at ha
  exact Bool.false_ne_true ha

/-- `Br M ≠ []` なら幹は `M` の内部で終わる。 -/
private theorem trmax_lt_of_Brne_ck (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    TrMax M < Lng M - 1 := by
  have hb := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq; exact hBrne (by simp [Br, heq])
  omega

/-! ## `branchPar` の連鎖（Isabelle wip 32316–32460） -/

/-- Isabelle `m_8_2_transJ0_eq_TrMax` (wip 32316): `j₁eq` の幾何と `Admpos` の下で
最終枝の joint（＝最終列の行 0 の親）はちょうど幹の右端。 -/
theorem transJ0_eq_TrMax (M : PS) (hmono : monoT M = true) (hM : TPS M)
    (hBrne : Br M ≠ []) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1) :
    transJ0 M = TrMax M := by
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hlastL : (Br M).length - 1 < (Br M).length := by omega
  -- 最終 joint は `transJ0 M`
  have hjeq : (Joints M).getD ((Br M).length - 1) 0 = transJ0 M := by
    rw [Joints_getD M _ hlastL, hj1eq]; rfl
  have hjle : (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M :=
    (FirstNodes_TrMax_Joints M _ hM hmono hlastL).1
  have hgle : transJ0 M ≤ TrMax M := by rw [← hjeq]; exact hjle
  -- `Adm M (transJ0 M)` は許容・正・`≤ TrMax M`
  have hpos : 0 < Adm M (transJ0 M) := hAdmpos
  have hadmA : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
  have hAle : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
  have hAleTr : Adm M (transJ0 M) ≤ TrMax M := by omega
  rcases adm_le_TrMax_cases_ck M (Adm M (transJ0 M)) hM hadmA hAleTr with h | h
  · omega
  · omega

/-- Isabelle `m_8_2_joints_all_TrMax` (wip 32350): `j₁eq`/`Admpos` の下では
**すべての**枝の joint が幹の右端に一致する。 -/
theorem joints_all_TrMax (M : PS) (J : ℕ) (hmono : monoT M = true) (hM : TPS M)
    (hBrne : Br M ≠ []) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hJBr : J < (Br M).length) :
    (Joints M).getD J 0 = TrMax M := by
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hlastL : (Br M).length - 1 < (Br M).length := by omega
  -- 最終 joint = `TrMax M`
  have hjlast : (Joints M).getD ((Br M).length - 1) 0 = TrMax M := by
    rw [Joints_getD M _ hlastL, hj1eq]
    exact transJ0_eq_TrMax M hmono hM hBrne hAdmpos hj1eq
  -- 上界
  have hle : (Joints M).getD J 0 ≤ TrMax M :=
    (FirstNodes_TrMax_Joints M J hM hmono hJBr).1
  -- 下界（joint は枝添字に関して広義単調減少）
  have hge : TrMax M ≤ (Joints M).getD J 0 := by
    by_cases hJeq : J = (Br M).length - 1
    · rw [hJeq]; omega
    · have hJlt : J < (Br M).length - 1 := by omega
      have hmono2 := FirstNodes_Joints_mono M J ((Br M).length - 1) hM hmono hJlt hlastL
      have := hmono2.2.1
      omega
  omega

/-- Isabelle `m_8_2_branchHigh` (wip 32391): 幹を超える各列の行 0 成分は
幹の右端の行 0 成分を真に上回る。 -/
theorem branchHigh (M : PS) (b : ℕ) (hmono : monoT M = true) (hM : TPS M)
    (hBrne : Br M ≠ []) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hbgt : TrMax M < b) (hble : b ≤ Lng M - 1) :
    entry M 0 (TrMax M) < entry M 0 b := by
  obtain ⟨J, hJBr, hleFNb⟩ := branch_component_le0 M b hM hmono hbgt hble
  have hjeqTr : (Joints M).getD J 0 = TrMax M :=
    joints_all_TrMax M J hmono hM hBrne hAdmpos hj1eq hJBr
  have hnx : nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true :=
    Joints_nextR_FirstNodes M J hM hmono hJBr
  rw [hjeqTr] at hnx
  -- 枝成分の左端で真に増える
  have hefn : entry M 0 (TrMax M) < entry M 0 ((FirstNodes M).getD J 0) := by
    have hh : nextrel0 M (TrMax M) ((FirstNodes M).getD J 0) = true := by
      simpa [nextR] using hnx
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  -- 左端から `b` へは広義増加
  have hle0fb : le0 M ((FirstNodes M).getD J 0) b = true := by simpa [leR] using hleFNb
  have hfnle : (FirstNodes M).getD J 0 ≤ b := le0_index_fseq hle0fb
  have hefb : entry M 0 ((FirstNodes M).getD J 0) ≤ entry M 0 b := by
    by_cases heq : (FirstNodes M).getD J 0 = b
    · rw [heq]
    · have hflt : (FirstNodes M).getD J 0 < b := by omega
      exact le_of_lt (ancestor_basic_1 M _ b b hM hflt le_rfl hleFNb)
  omega

/-- Isabelle `m_8_2_branchPar` (wip 32434): `m_8_2_subexpr_component_Pred_done` の
唯一の幾何残差。幹を超える各列の行 0 の親は幹の右端以降にある。 -/
theorem branchPar (M : PS) (b : ℕ) (hmono : monoT M = true) (hM : TPS M)
    (hBrne : Br M ≠ []) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hbgt : TrMax M < b) (hble : b ≤ Lng M - 1) :
    TrMax M ≤ parent M 0 b := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hbpos : 0 < b := by omega
  have hp : hasParent M 0 b = true :=
    mono_hasParent_row0 M hM hmono b hbpos (by omega)
  have hparR : nextR M 0 (parent M 0 b) b = true := nextR_parent0_of_hasParent M b hp
  have hentlt : entry M 0 (TrMax M) < entry M 0 b :=
    branchHigh M b hmono hM hBrne hAdmpos hj1eq hbgt hble
  exact nextR0_largest_below M (parent M 0 b) (TrMax M) b hparR hbgt hentlt

/-! ## `descAdm`（`chainOK` の平坦化仮説）の供給（Isabelle wip 31683–31756） -/

/-- Isabelle `m_8_2_TrMax_ge_1` (wip 31683): `j₁eq` の幾何と `Admpos` から
幹は非自明（`1 ≤ TrMax M`）。（`j₁eq` は必須: `Admpos ∧ good` だけでは
`(0,0)(1,0)(2,0)` が `TrMax = 0` の反例。） -/
theorem TrMax_ge_1 (M : PS) (hmono : monoT M = true) (hM : TPS M)
    (hBrne : Br M ≠ []) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1) :
    1 ≤ TrMax M := by
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJBr : (Br M).length - 1 < (Br M).length := by omega
  have hjeq : (Joints M).getD ((Br M).length - 1) 0 = transJ0 M := by
    rw [Joints_getD M _ hJBr, hj1eq]; rfl
  have hjle : (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M :=
    (FirstNodes_TrMax_Joints M _ hM hmono hJBr).1
  have hj0le : transJ0 M ≤ TrMax M := by rw [← hjeq]; exact hjle
  have hadmle : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
  have hpos : 0 < Adm M (transJ0 M) := hAdmpos
  omega

/-- 行 0 の親の接頭辞切片への転送（Isabelle `repr_parent_M_to_seg` の行 0 形。
`8.1-part4-mid` の私的 `parent0_seg_pm` の再証明）。 -/
private theorem parent0_seg_ck (M : PS) (m j₁ : ℕ)
    (hj₁ : j₁ < Lng M) (hmp : m ≤ parent M 0 j₁)
    (hp : hasParent M 0 j₁ = true) :
    hasParent (seg M m j₁) 0 (j₁ - m) = true ∧
      parent (seg M m j₁) 0 (j₁ - m) = parent M 0 j₁ - m := by
  have hnextM : nextR M 0 (parent M 0 j₁) j₁ = true := hasParent_next_fseq M 0 j₁ hp
  have hpLt : parent M 0 j₁ < j₁ := parent_lt_of_hasParent M 0 j₁ hp
  have hmpl : m + (parent M 0 j₁ - m) = parent M 0 j₁ := by omega
  have hmjl : m + (j₁ - m) = j₁ := by omega
  have hjlS : j₁ - m < Lng (seg M m j₁) := by simp; omega
  have hplS : parent M 0 j₁ - m < Lng (seg M m j₁) := by simp; omega
  have hnextS : nextR (seg M m j₁) 0 (parent M 0 j₁ - m) (j₁ - m) = true := by
    rw [nextR_seg_adm M m j₁ 0 _ _ (by omega) hj₁ hplS hjlS, hmpl, hmjl]
    exact hnextM
  have huniq : ∀ q, nextR (seg M m j₁) 0 q (j₁ - m) = true → q = parent M 0 j₁ - m :=
    fun q hq => row0_parent_unique (seg M m j₁) q _ (j₁ - m) hq hnextS
  exact ⟨(hasParent_iff_unique_fseq (seg M m j₁) 0 (j₁ - m)).mpr ⟨_, hnextS, huniq⟩,
    parent_eq_of_unique_fseq (seg M m j₁) 0 (j₁ - m) _ hnextS huniq⟩

/-- Isabelle `transJm1_seg0_eq_Adm`: 接頭辞切片 `(M_j)_{j=0}^{b}` の `Admpos` 証人は
`M` 側の `Adm_M(parent_M(0,b))` に等しい（`m_6_3_Adm_prefix_slice` ＝ `admof_slice`
の `s = 0` 特殊化と行 0 の親の転送の合成）。 -/
private theorem transJm1_seg0_eq_Adm_ck (M : PS) (b : ℕ) (hM : TPS M)
    (hp : hasParent M 0 b = true) (hpb : parent M 0 b < b) (hble : b ≤ Lng M - 1) :
    transJm1 (seg M 0 b) = Adm M (parent M 0 b) := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hbL : b < Lng M := by omega
  have hLseg : Lng (seg M 0 b) = b + 1 := by simp
  -- `transJ0 (seg M 0 b) = parent M 0 b`
  have hs := parent0_seg_ck M 0 b hbL (Nat.zero_le _) hp
  have hpar : parent (seg M 0 b) 0 b = parent M 0 b := by
    have h2 := hs.2; simpa using h2
  have htJ0 : transJ0 (seg M 0 b) = parent M 0 b := by
    show parent (seg M 0 b) 0 (lastIdx (seg M 0 b)) = parent M 0 b
    show parent (seg M 0 b) 0 (Lng (seg M 0 b) - 1) = parent M 0 b
    rw [hLseg]; simpa using hpar
  -- `Adm` の接頭辞不変性（`admof_slice` の `s = 0`）
  have hAdm : Adm (seg M 0 b) (parent M 0 b) = Adm M (parent M 0 b) := by
    have h := admof_slice M 0 (parent M 0 b) b hM (Nat.zero_le _) hpb hble
    simpa using h
  show Adm (seg M 0 b) (transJ0 (seg M 0 b)) = Adm M (parent M 0 b)
  rw [htJ0, hAdm]

/-- Isabelle `m_8_2_descAdm_of_premises` (wip 31725): 唯一の幾何残差 `branchPar` から
`chainOK` の 2 入力（`1 ≤ TrMax M` と `descAdm`）を供給する。 -/
theorem descAdm_of_premises (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbrP : Br (Pred M) ≠ [])
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hbranchPar : ∀ b, TrMax M < b → b ≤ Lng M - 1 → TrMax M ≤ parent M 0 b) :
    1 ≤ TrMax M ∧
      ∀ b, TrMax M < b → b ≤ Lng M - 1 → 0 < transJm1 (seg M 0 b) := by
  have hM : TPS M := RTPS_TPS M hR
  have hTR1 : 1 ≤ TrMax M := TrMax_ge_1 M hmono hM hBrne hAdmpos hj1eq
  have hadmTr : adm M (TrMax M) = true := adm_TrMax_ck M hM
  refine ⟨hTR1, ?_⟩
  intro b hbgt hble
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hbpos : 0 < b := by omega
  have hp : hasParent M 0 b = true :=
    mono_hasParent_row0 M hM hmono b hbpos (by omega)
  have hpb : parent M 0 b < b := parent_lt_of_hasParent M 0 b hp
  have hred : transJm1 (seg M 0 b) = Adm M (parent M 0 b) :=
    transJm1_seg0_eq_Adm_ck M b hM hp hpb hble
  have hpge : TrMax M ≤ parent M 0 b := hbranchPar b hbgt hble
  have hle : TrMax M ≤ Adm M (parent M 0 b) := Adm_max M (TrMax M) _ hadmTr hpge
  omega

/-! ## `chainOK`（Isabelle wip 30726 の `function` 定義） -/

/-- Isabelle `chainOK` (wip 30726) の逐語移植:

    `chainOK M = (if transJm1 M > 0 ∧ Br M ≠ [] ∧ Lng M - 1 > 1`
    `             then Br (Pred M) = [] ∨ chainOK (Pred M) else False)`

「`Pred`-降下が `Br (Pred ..) = []` に達するまで `Admpos` ＋ `good` を保つ」。
測度 `Lng` で整礎（`Lng (Pred M) < Lng M`）。 -/
def chainOK (M : PS) : Prop :=
  if h : 0 < transJm1 M ∧ Br M ≠ [] ∧ 1 < Lng M - 1 then
    Br (Pred M) = [] ∨ chainOK (Pred M)
  else False
termination_by Lng M
decreasing_by
  have hlen : 1 < Lng M := by omega
  rw [length_Pred M hlen]
  omega

/-- `chainOK` の 1 段展開（Isabelle `chainOK.simps` の `[of M]` インスタンス）。 -/
theorem chainOK_unfold (M : PS) :
    chainOK M ↔
      (if 0 < transJm1 M ∧ Br M ≠ [] ∧ 1 < Lng M - 1 then
        Br (Pred M) = [] ∨ chainOK (Pred M)
      else False) := by
  rw [chainOK]
  by_cases h : 0 < transJm1 M ∧ Br M ≠ [] ∧ 1 < Lng M - 1
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

/-! ### `chainOK` の平坦化還元（Isabelle `m_8_2_chainOK_of_descAdm`, wip 31113）

再帰述語 `chainOK M` を `M` だけについての**平坦・非再帰**な仮説
「幹を超えるすべての接頭辞 `seg M 0 b` が `transJm1 > 0`」に潰す。
`k` 段目の `Pred` 反復が接頭辞 `seg M 0 (Lng M - 1 - k)` に等しい（`Pred = dropLast`）
ことによる。降下 1 段の転送は純粋なリスト等式（`take_take`）で、許容性の議論は不要。 -/

/-- 接頭辞切片 = `take`（Isabelle `seg_0_eq_take` の Lean 形）。 -/
private theorem seg0_eq_take_ck (M : PS) (b : ℕ) (hb : b < Lng M) :
    seg M 0 b = M.take (b + 1) := by
  simpa using seg_eq_take_drop_adm M 0 b (Nat.zero_le _) hb

/-- 全体の接頭辞は自分自身。 -/
private theorem seg0_last_ck (M : PS) (hpos : 0 < Lng M) :
    seg M 0 (Lng M - 1) = M := by
  rw [seg0_eq_take_ck M (Lng M - 1) (by omega)]
  have h : Lng M - 1 + 1 = Lng M := by omega
  rw [h, List.take_length]

/-- 降下 1 段の接頭辞転送（純粋なリスト等式）。 -/
private theorem seg0_Pred_ck (M : PS) (b : ℕ) (hlen : 1 < Lng M) (hb : b ≤ Lng M - 2) :
    seg (Pred M) 0 b = seg M 0 b := by
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hbP : b < Lng (Pred M) := by omega
  have hbM : b < Lng M := by omega
  rw [seg0_eq_take_ck (Pred M) b hbP, seg0_eq_take_ck M b hbM,
    Pred_eq_take M hlen, List.take_take]
  congr 1
  omega

/-- Isabelle `m_8_2_chainOK_of_descAdm` (`layerB/pss_wip.thy:31113`)。 -/
theorem chainOK_of_descAdm (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hTR1 : 1 ≤ TrMax M)
    (hdescAdm : ∀ b, TrMax M < b → b ≤ Lng M - 1 → 0 < transJm1 (seg M 0 b)) :
    chainOK M := by
  induction hn : Lng M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  subst hn
  have hM : TPS M := RTPS_TPS M hR
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hlen : 1 < Lng M := by omega
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq; exact hBrne (by simp [Br, heq])
  have htrlt : TrMax M < Lng M - 1 := by
    have := TrMax_bound M hM; omega
  -- `Admpos M`: `b = Lng M - 1` インスタンス（全体の接頭辞は `M` 自身）
  have hAdmpos : 0 < transJm1 M := by
    have h := hdescAdm (Lng M - 1) htrlt le_rfl
    rwa [seg0_last_ck M hMpos] at h
  have hcond : 0 < transJm1 M ∧ Br M ≠ [] ∧ 1 < Lng M - 1 := ⟨hAdmpos, hBrne, hj1gt⟩
  rw [chainOK_unfold M, if_pos hcond]
  by_cases hbase : Br (Pred M) = []
  · exact Or.inl hbase
  · right
    have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
    have hpredR : RTPS (Pred M) := RTPS_Pred M hR
    have hpredT : TPS (Pred M) := RTPS_TPS _ hpredR
    have hTRP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM hlen hne
    have hTRP1 : 1 ≤ TrMax (Pred M) := by omega
    have hneP : TrMax (Pred M) ≠ Lng (Pred M) - 1 := by
      intro heq; exact hbase (by simp [Br, heq])
    have htrltP : TrMax (Pred M) < Lng (Pred M) - 1 := by
      have := TrMax_bound (Pred M) hpredT; omega
    have hLP2 : 1 < Lng (Pred M) - 1 := by omega
    have hmonoP : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
    -- 降下仮説は `Pred M` に逐語的に制限される
    have hdescP : ∀ b, TrMax (Pred M) < b → b ≤ Lng (Pred M) - 1 →
        0 < transJm1 (seg (Pred M) 0 b) := by
      intro b hbgt hble
      have hble2 : b ≤ Lng M - 2 := by omega
      rw [seg0_Pred_ck M b hlen hble2]
      exact hdescAdm b (by omega) (by omega)
    exact ih (Lng (Pred M)) (by omega) (Pred M) hpredR hmonoP hbase hLP2 hTRP1 hdescP rfl

/-- Isabelle `m_8_2_chainOK_of_branchPar` (`layerB/pss_wip.thy:31764`): `branchPar`
＋ 残差前提から `chainOK M`。`descAdm_of_premises`（`1 ≤ TrMax M` と `descAdm` を
供給）を `chainOK_of_descAdm` に合成したもの。 -/
theorem chainOK_of_branchPar (M : PS)
    (hbranchPar : ∀ b, TrMax M < b → b ≤ Lng M - 1 → TrMax M ≤ parent M 0 b)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M) (hbrP : Br (Pred M) ≠ [])
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1) :
    chainOK M := by
  obtain ⟨hTR1, hdd⟩ :=
    descAdm_of_premises M hR hmono hBrne hj1gt hAdmpos hbrP hj1eq hbranchPar
  exact chainOK_of_descAdm M hR hmono hBrne hj1gt hTR1 hdd

/-! ## 全幹＝対角列（Isabelle `baseU_*` 支援群, wip 29985–30140）

`baseU` と `chainOK_imp_widTrM` の**共通基底**。枝が空な簡約単項列は対角列であり、
その `Trans` は 2 段の塔 `D_{Q₁,₀}(D_{Q₁,j₁} 0_B)` になる。 -/

/-- Isabelle `baseU_Br_empty_TrMax` (wip 29985): 枝が空なら幹が右端まで伸びている。 -/
theorem baseU_Br_empty_TrMax (Q : PS) (hbr : Br Q = []) : TrMax Q = Lng Q - 1 := by
  by_contra hne
  have h : Br Q = P (seg Q (TrMax Q + 1) (Lng Q - 1)) := by simp [Br, hne]
  exact P_nonempty (seg Q (TrMax Q + 1) (Lng Q - 1)) (by rw [← h, hbr])

/-- Isabelle `baseU_alltrunk_diag_entry` (wip 29996): 全幹の簡約単項列は
両段とも `Q₁,₀ + j` という対角の値を取る。長さに関する帰納法で、
各段の親の一意性（幹ステップ＋谷条件）と条件 (A) から 1 ずつ上げる。 -/
theorem baseU_alltrunk_diag_entry (Q : PS) (k : ℕ) (hR : RTPS Q)
    (hmono : monoT Q = true) (htr : TrMax Q = Lng Q - 1) (hk : k < Lng Q) :
    entry Q 0 k = entry Q 1 0 + k ∧ entry Q 1 k = entry Q 1 0 + k := by
  have hQT : TPS Q := RTPS_TPS Q hR
  have hcondA : RedCondA Q = true := (RTPS_condAB Q hR).1
  induction k with
  | zero =>
      refine ⟨?_, by simp⟩
      simpa using RTPS_mono_head_eq Q hR hmono
  | succ k ih =>
      have hkL : k < Lng Q := by omega
      obtain ⟨he0k, he1k⟩ := ih hkL
      have hkTr : k < TrMax Q := by omega
      -- 行 1: 幹ステップ ＋ 谷条件で親は一意に `k`
      have hnr1 : nextR Q 1 k (k + 1) = true := TrMax_trunk_step Q k hQT hkTr
      have hnrel1 : nextrel1 Q k (k + 1) = true := by simpa [nextR] using hnr1
      have hh1 := hnrel1
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hh1
      have he1lt : entry Q 1 k < entry Q 1 (k + 1) := hh1.1.1.2
      have hle0k : le0 Q k (k + 1) = true := hh1.1.2
      have huniq1 : ∀ a, nextR Q 1 a (k + 1) = true → a = k := by
        intro a ha
        have hna : nextrel1 Q a (k + 1) = true := by simpa [nextR] using ha
        have hha := hna
        simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hha
        have halt : a < k + 1 := hha.1.1.1.2
        by_contra hak
        have hak' : a < k := by omega
        -- 谷条件を `jj = k` で使う（ガード `a < k` と `le0 Q k (k+1)` を供給）
        have hs := hha.2 k (List.mem_range.mpr hkL)
        simp [hak', hle0k] at hs
        omega
      have hp1 : hasParent Q 1 (k + 1) = true :=
        (hasParent_iff_unique_fseq Q 1 (k + 1)).mpr ⟨k, hnr1, huniq1⟩
      have hpar1 : parent Q 1 (k + 1) = k :=
        parent_eq_of_unique_fseq Q 1 (k + 1) k hnr1 huniq1
      have he1sk : entry Q 1 (k + 1) = entry Q 1 0 + (k + 1) := by
        have h := RedCondA_apply Q hcondA 1 (k + 1) (by omega) (by omega) hp1
        rw [hpar1, he1k] at h
        omega
      -- 行 0: 隣接 `le0` から `nextrel0`、同様に親は一意に `k`
      have hnrel0 : nextrel0 Q k (k + 1) = true := le0_adjacent Q k hle0k
      have hnr0 : nextR Q 0 k (k + 1) = true := by simpa [nextR] using hnrel0
      have huniq0 : ∀ a, nextR Q 0 a (k + 1) = true → a = k :=
        fun a ha => row0_parent_unique Q a k (k + 1) ha hnr0
      have hp0 : hasParent Q 0 (k + 1) = true :=
        (hasParent_iff_unique_fseq Q 0 (k + 1)).mpr ⟨k, hnr0, huniq0⟩
      have hpar0 : parent Q 0 (k + 1) = k :=
        parent_eq_of_unique_fseq Q 0 (k + 1) k hnr0 huniq0
      have he0sk : entry Q 0 (k + 1) = entry Q 1 0 + (k + 1) := by
        have h := RedCondA_apply Q hcondA 0 (k + 1) (by omega) (by omega) hp0
        rw [hpar0, he0k] at h
        omega
      exact ⟨he0sk, he1sk⟩

/-- Isabelle `baseU_alltrunk_Trans_RN1` (wip 30086): 全幹の簡約単項列 `Q` は対角列
`diagSeq Q₁,₀ (Q₁,₀ + j₁)` に一致するので、その `Trans` は 2 段の塔になり、
`RightNodes` の第 2 成分は最終列の行 1 成分。 -/
theorem baseU_alltrunk_Trans_RN1 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (htr : TrMax Q = Lng Q - 1) (hL : 1 < Lng Q) :
    (RightNodes (Trans Q)).getD 1 0 = entry Q 1 (Lng Q - 1) := by
  have hQT : TPS Q := RTPS_TPS Q hR
  have hub : entry Q 1 0 < entry Q 1 0 + (Lng Q - 1) := by omega
  -- `Q = diagSeq Q₁,₀ (Q₁,₀ + j₁)`
  have heq : Q = diagSeq (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) := by
    apply List.ext_getElem
    · -- 罠: `Lng Q` と `List.length Q` は omega の別アトム。橋渡しを渡す。
      have hbridge : List.length Q = Lng Q := rfl
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
  -- 塔の値。右端の値を**アトムのまま**保つ（複合式だと simp が ℕ∞ のキャストを
  -- 内側に押し込んで `toNat` が潰せなくなる）。
  have htransv : Trans Q =
      Dprin ((entry Q 1 0 : ℕ) : ℕ∞)
        (Dprin ((entry Q 1 (Lng Q - 1) : ℕ) : ℕ∞) BZero) := by
    rw [hlast]
    conv_lhs => rw [heq]
    exact diagSeq_Trans (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) hub
  rw [htransv, RightNodes_Dprin, RightNodes_Dprin]
  simp

/-! ## `chainOK ⟹ widTrM`（Isabelle `m_8_2_chainOK_imp_widTrM`, wip 30747）

`Lng` に関する整礎帰納法。
* 基底 `Br (Pred M) = []`: `Pred M` は全幹＝対角列なので `RightNodes` 第 2 成分は
  `(Pred M)₁,ᴸⁿᵍ⁻¹ = M₁,ᴸⁿᵍ⁻²`、降下 `wid_step` がそれを `M` 側へ運び、
  `TrMax M = Lng M - 2` で `widTrM` が閉じる。
* ステップ `Br (Pred M) ≠ []`: `chainOK (Pred M)` から IH、`wid_step` と
  `TrMax (Pred M) = TrMax M` ＋行 1 の `Pred` 一致で押し上げる。 -/

/-- Isabelle `m_8_2_chainOK_imp_widTrM` (`layerB/pss_wip.thy:30747`)。
`widTrM M`＝「`M` は自身の幹右端の基点に着地する」。 -/
theorem chainOK_imp_widTrM (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hcOK : chainOK M) (hR : RTPS M) (hmono : monoT M = true) :
    (RightNodes (Trans M)).getD 1 0 = entry M 1 (TrMax M) := by
  induction hn : Lng M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  subst hn
  have hM : TPS M := RTPS_TPS M hR
  -- `chainOK M` をちょうど 1 段展開
  rw [chainOK_unfold M] at hcOK
  by_cases hcond : 0 < transJm1 M ∧ Br M ≠ [] ∧ 1 < Lng M - 1
  · rw [if_pos hcond] at hcOK
    obtain ⟨hAdmpos, hBrne, hj1gt⟩ := hcond
    have hlen : 1 < Lng M := by omega
    have hne : TrMax M ≠ Lng M - 1 := by
      intro heq; exact hBrne (by simp [Br, heq])
    have htrlt : TrMax M < Lng M - 1 := by
      have := TrMax_bound M hM; omega
    -- `Pred M` の設定
    have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
    have hLP2 : 1 < Lng (Pred M) := by omega
    have hpredR : RTPS (Pred M) := RTPS_Pred M hR
    have hpredT : TPS (Pred M) := RTPS_TPS _ hpredR
    have hmonoP : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
    have hnzP : zeroT (Pred M) = false := by
      simp [zeroT]; intro h; omega
    have ht1ne : Trans (Pred M) ≠ BZero := by
      intro hz
      have := (Trans_preserves_zeroT (Pred M) hpredT).mpr hz
      rw [hnzP] at this
      exact Bool.false_ne_true this
    have hrnstep : (RightNodes (Trans M)).getD 1 0 =
        (RightNodes (Trans (Pred M))).getD 1 0 :=
      wid_step hsplit M hR hmono hj1gt hAdmpos ht1ne
    have hTRP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM hlen hne
    rcases hcOK with hbase | hstep
    · -- 基底: `Pred M` は全幹＝対角列
      have htrPred : TrMax (Pred M) = Lng (Pred M) - 1 := baseU_Br_empty_TrMax _ hbase
      have hrnPred : (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1 (Lng (Pred M) - 1) :=
        baseU_alltrunk_Trans_RN1 (Pred M) hpredR hmonoP htrPred hLP2
      have hidx : Lng (Pred M) - 1 = Lng M - 2 := by omega
      have heagree : entry (Pred M) 1 (Lng M - 2) = entry M 1 (Lng M - 2) :=
        entry_Pred M 1 (Lng M - 2) (by omega)
      have htrMeq : TrMax M = Lng M - 2 := by omega
      rw [hrnstep, hrnPred, hidx, heagree, htrMeq]
    · -- ステップ: `chainOK (Pred M)` に IH
      have hIH : (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1 (TrMax (Pred M)) :=
        ih (Lng (Pred M)) (by omega) (Pred M) hstep hpredR hmonoP rfl
      have heagree : entry (Pred M) 1 (TrMax M) = entry M 1 (TrMax M) :=
        entry_Pred M 1 (TrMax M) (by omega)
      rw [hrnstep, hIH, hTRP, heagree]
  · rw [if_neg hcond] at hcOK
    exact absurd hcOK not_false

/-! ## `cpU` の閉包（Isabelle wip 29887–29982, 30841） -/

/-- Isabelle `m_8_2_j0_eq_TrMax` (`layerB/pss_wip.thy:29887`): `j₁eq`/`Admpos` の下で
最終 joint は幹の右端。 -/
theorem j0_eq_TrMax (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1) :
    (Joints M).getD ((Br M).length - 1) 0 = TrMax M := by
  have hM : TPS M := RTPS_TPS M hR
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  exact joints_all_TrMax M _ hmono hM hBrne hAdmpos hj1eq (by omega)

/-- Isabelle `m_8_2_cpU_rhs_eq` (`layerB/pss_wip.thy:29918`): `cpU` の目標の右辺は、
無条件の joints 転送 `jt_transport` と幹右端への固定 `j0_eq_TrMax` により
`entry M 1 (TrMax M)` に還元される。 -/
theorem cpU_rhs_eq (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbrP : Br (Pred M) ≠ [])
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1) :
    entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
      entry M 1 (TrMax M) := by
  rw [jt_transport M hR hmono hBrne hj1gt hAdmpos hbrP,
    j0_eq_TrMax M hR hmono hBrne hj1gt hAdmpos hj1eq]

/-- Isabelle `m_8_2_cpU_of_widTrMaxM` (`layerB/pss_wip.thy:29946`): 降下 `wid_step`
と右辺還元 `cpU_rhs_eq` を合わせると、`cpU` は単一の着地等式 `widTrM` から従う。 -/
theorem cpU_of_widTrMaxM (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbrP : Br (Pred M) ≠ [])
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hsplit : ScbOuterSurgerySplit)
    (hwidTrM : (RightNodes (Trans M)).getD 1 0 = entry M 1 (TrMax M)) :
    (RightNodes (Trans (Pred M))).getD 1 0 =
      entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS _ hpredR
  have hnzP : zeroT (Pred M) = false := by
    simp [zeroT]; intro h; omega
  have ht1ne : Trans (Pred M) ≠ BZero := by
    intro hz
    have := (Trans_preserves_zeroT (Pred M) hpredT).mpr hz
    rw [hnzP] at this
    exact Bool.false_ne_true this
  have hstep : (RightNodes (Trans M)).getD 1 0 =
      (RightNodes (Trans (Pred M))).getD 1 0 :=
    wid_step hsplit M hR hmono hj1gt hAdmpos ht1ne
  rw [← hstep, hwidTrM, cpU_rhs_eq M hR hmono hBrne hj1gt hAdmpos hbrP hj1eq]

/-- Isabelle `m_8_2_cpU_of_chainOK` (`layerB/pss_wip.thy:30841`): `chainOK ⟹ widTrM`
と `widTrM ⟹ cpU` の合成。§8.2 キーストーン残差を単一の述語事実
`j₁eq ⟹ chainOK` に固定する。 -/
theorem cpU_of_chainOK (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbrP : Br (Pred M) ≠ [])
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hcOK : chainOK M) :
    (RightNodes (Trans (Pred M))).getD 1 0 =
      entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) :=
  cpU_of_widTrMaxM M hR hmono hBrne hj1gt hAdmpos hbrP hj1eq hsplit
    (chainOK_imp_widTrM hsplit M hcOK hR hmono)

/-! ## `baseU`（Isabelle `m_8_2_baseU`, wip 30183）

`m_8_2_wid` の帰納基底（`Pred M` にキーストーン IH が使えない場合）。 -/

/-- 行 0 祖先関係の反射性（`5.1-ancestor-tree` の私的 `le0_refl_at` の再証明）。 -/
private theorem le0Aux_refl_ck (M : PS) (fuel a : ℕ) : le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le0_refl_ck (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 0 a a = true := by
  simp [leR, le0, ha, le0Aux_refl_ck]

/-- 長さ 1 の列は複項でない（`6.5-Red-Pred-commute` の私的
`multiT_length_one_false` の再証明）。 -/
private theorem multiT_len1_false_ck (N : PS) (hL : Lng N = 1) : multiT N = false := by
  by_cases hz : zeroT N = true
  · simp [multiT, hz]
  · have hz' : zeroT N = false := Bool.eq_false_of_not_eq_true hz
    have hle : leR N 0 0 (Lng N - 1) = true := by
      rw [show Lng N - 1 = 0 by omega]
      exact le0_refl_ck N 0 (by omega)
    simp [multiT, monoT, hz', hle]

/-- Isabelle `baseU_twoseg_monoT` (wip 30140): 行 0 が真に増える 2 列は単項。 -/
theorem baseU_twoseg_monoT (N : PS) (hlt : entry N 0 0 < entry N 0 1) (hL2 : Lng N = 2) :
    monoT N = true := by
  have hnz : zeroT N = false := by simp [zeroT, hL2]
  have hnr : nextR N 0 0 1 = true := by
    simp [nextR, nextrel0, hL2, hlt]
  have hleR : leR N 0 0 (Lng N - 1) = true := by
    rw [show Lng N - 1 = 1 by omega]
    exact nextR0_leR N 0 1 hnr
  simp [monoT, hnz, hleR]

/-- Isabelle `baseU_caseI_geom` (wip 30155): `TrMax M = Lng M - 2` のレジームの
単項最終枝の幾何。`Br M` は（最終列だけの）単一成分なので `FirstNodes M₀ = j₁`、
かつ `Admpos` の下で `Joints M₀ = transJ₀ M = TrMax M`。 -/
theorem baseU_caseI_geom (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (htrM : TrMax M = Lng M - 2) :
    (Br M).length = 1 ∧ (FirstNodes M).getD 0 0 = Lng M - 1 ∧
      (Joints M).getD 0 0 = TrMax M := by
  have hM : TPS M := RTPS_TPS M hR
  have hne : TrMax M ≠ Lng M - 1 := by omega
  have ha1 : TrMax M + 1 = Lng M - 1 := by omega
  -- 幹の右の切片は単一列
  have hsegL : Lng (seg M (TrMax M + 1) (Lng M - 1)) = 1 := by simp; omega
  have hsegnm : multiT (seg M (TrMax M + 1) (Lng M - 1)) = false :=
    multiT_len1_false_ck _ hsegL
  have hBrval : Br M = [seg M (TrMax M + 1) (Lng M - 1)] := by
    rw [show Br M = P (seg M (TrMax M + 1) (Lng M - 1)) by simp [Br, hne]]
    exact P_nonmulti_eq _ hsegnm
  have hBrL : (Br M).length = 1 := by rw [hBrval]; rfl
  have hJ0 : 0 < (Br M).length := by omega
  -- `FirstNodes M₀ = TrMax M + 1 + 0 = j₁`
  have hIdx0 : (IdxSum (Br M)).getD 0 0 = 0 := by
    simpa using idxSum_getD (Br M) 0 (Nat.zero_le _)
  have hFN0 : (FirstNodes M).getD 0 0 = Lng M - 1 := by
    rw [FirstNodes_getD M 0 hJ0, hIdx0]; omega
  -- `Joints M₀ = transJ₀ M = TrMax M`
  have hJ0eq : (Joints M).getD 0 0 = transJ0 M := by
    rw [Joints_getD M 0 hJ0, hFN0]; rfl
  have hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 := by
    rw [hBrL]; exact hFN0
  exact ⟨hBrL, hFN0, by rw [hJ0eq]; exact transJ0_eq_TrMax M hmono hM hBrne hAdmpos hj1eq⟩

/-- Isabelle `m_8_2_baseU` (`layerB/pss_wip.thy:30183`) ＝ `8.2-subexpr-final` の
`SXP_wid_baseU`。`m_8_2_wid` の帰納基底: `Pred M` にキーストーン IH が使えない
（`Br (Pred M) = []`、すなわち `Pred M` は全幹＝対角列、または `Lng M = 3`）場合の
`wid M`。いずれも `RightNodes (Trans M)` の第 2 成分は `Trans (Pred M)` のそれに
等しく（`wid_step`）、最終幹の行 1 の値として読み出せ、`M` の最終枝の
`FirstNodes` または `Joints` の項に着地する。 -/
theorem baseU (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbasecond : Br (Pred M) = [] ∨ ¬ (1 < Lng (Pred M) - 1)) :
    wid M := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq; exact hBrne (by simp [Br, heq])
  have htrlt : TrMax M < Lng M - 1 := by
    have := TrMax_bound M hM; omega
  -- `Pred M` の設定
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLP2 : 1 < Lng (Pred M) := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS _ hpredR
  have hmonoP : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
  have hnzP : zeroT (Pred M) = false := by simp [zeroT]; intro h; omega
  have ht1ne : Trans (Pred M) ≠ BZero := by
    intro hz
    have := (Trans_preserves_zeroT (Pred M) hpredT).mpr hz
    rw [hnzP] at this
    exact Bool.false_ne_true this
  have hrnstep : (RightNodes (Trans M)).getD 1 0 =
      (RightNodes (Trans (Pred M))).getD 1 0 :=
    wid_step hsplit M hR hmono hj1gt hAdmpos ht1ne
  rw [wid_iff]
  by_cases hA : Br (Pred M) = []
  · -- 場合 A: `Pred M` は全幹＝対角列
    have htrPred : TrMax (Pred M) = Lng (Pred M) - 1 := baseU_Br_empty_TrMax _ hA
    have hrnPred : (RightNodes (Trans (Pred M))).getD 1 0 =
        entry (Pred M) 1 (Lng (Pred M) - 1) :=
      baseU_alltrunk_Trans_RN1 (Pred M) hpredR hmonoP htrPred hLP2
    have hidx : Lng (Pred M) - 1 = Lng M - 2 := by omega
    have heagree : entry (Pred M) 1 (Lng M - 2) = entry M 1 (Lng M - 2) :=
      entry_Pred M 1 (Lng M - 2) (by omega)
    have hrn1val : (RightNodes (Trans M)).getD 1 0 = entry M 1 (Lng M - 2) := by
      rw [hrnstep, hrnPred, hidx, heagree]
    have hTRP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hM hlen hne
    have htrMeq : TrMax M = Lng M - 2 := by omega
    obtain ⟨hBrL, _, hJ0tr⟩ := baseU_caseI_geom M hR hmono hBrne hj1gt hAdmpos htrMeq
    right
    rw [hrn1val, show (Br M).length - 1 = 0 by omega, hJ0tr, htrMeq]
  · -- 場合 B: `Lng M = 3`（`Lng (Pred M) = 2`）
    have hnotIH : ¬ (1 < Lng (Pred M) - 1) := by tauto
    have hL3 : Lng M = 3 := by omega
    have hL2pred : Lng (Pred M) = 2 := by omega
    have htransPred : Trans (Pred M) =
        Dprin ((entry (Pred M) 1 0 : ℕ) : ℕ∞)
          (Dprin ((entry (Pred M) 1 1 : ℕ) : ℕ∞) BZero) :=
      two_column_Trans (Pred M) hpredR hmonoP hL2pred
    have hrnPred1 : (RightNodes (Trans (Pred M))).getD 1 0 = entry (Pred M) 1 1 := by
      rw [htransPred, RightNodes_Dprin, RightNodes_Dprin]; simp
    have he11 : entry (Pred M) 1 1 = entry M 1 1 := entry_Pred M 1 1 (by omega)
    have hrn1B : (RightNodes (Trans M)).getD 1 0 = entry M 1 1 := by
      rw [hrnstep, hrnPred1, he11]
    have htrMle1 : TrMax M < 2 := by omega
    rcases Nat.lt_or_ge (TrMax M) 1 with hB0 | hB1
    · -- B0: `TrMax M = 0` — 行 0 の親が `1` なので枝は 2 列の単一成分
      have htr0 : TrMax M = 0 := by omega
      have hMpos : 0 < Lng M := by omega
      have hp : hasParent M 0 (Lng M - 1) = true :=
        mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
      have hnxt : nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true :=
        hasParent_next_fseq M 0 (Lng M - 1) hp
      have hplt : parent M 0 (Lng M - 1) < Lng M - 1 :=
        parent_lt_of_hasParent M 0 (Lng M - 1) hp
      -- `Admpos` は親 `= 0` を排除するので親は `1`
      have hpne0 : parent M 0 (Lng M - 1) ≠ 0 := by
        intro h0
        have htJ0 : transJ0 M = 0 := h0
        have hadm0 : adm M 0 = true := adm_zero M
        have : transJm1 M = 0 := by
          show Adm M (transJ0 M) = 0
          rw [htJ0]
          simp [Adm, hadm0]
        omega
      have hp1 : parent M 0 (Lng M - 1) = 1 := by omega
      have he01 : entry M 0 1 < entry M 0 2 := by
        have hnr : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
          simpa [nextR] using hnxt
        rw [hp1, show Lng M - 1 = 2 by omega] at hnr
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnr
        exact hnr.1.2
      -- 枝領域 `seg M 1 2` は単項なので単一成分
      have hsegL2 : Lng (seg M 1 2) = 2 := by simp
      have hse0 : entry (seg M 1 2) 0 0 = entry M 0 1 := by
        have := entry_seg M 1 2 0 0 (by rw [hsegL2]; omega); simpa using this
      have hse1 : entry (seg M 1 2) 0 1 = entry M 0 2 := by
        have := entry_seg M 1 2 0 1 (by rw [hsegL2]; omega); simpa using this
      have hsegmono : monoT (seg M 1 2) = true :=
        baseU_twoseg_monoT _ (by rw [hse0, hse1]; exact he01) hsegL2
      have hsegnm : multiT (seg M 1 2) = false := by simp [multiT, hsegmono]
      have hBrval : Br M = [seg M 1 2] := by
        rw [show Br M = P (seg M (TrMax M + 1) (Lng M - 1)) by simp [Br, hne]]
        rw [htr0, show Lng M - 1 = 2 by omega, show (0 : ℕ) + 1 = 1 from rfl]
        exact P_nonmulti_eq _ hsegnm
      have hBrL : (Br M).length = 1 := by rw [hBrval]; rfl
      have hJ0 : 0 < (Br M).length := by omega
      have hIdx0 : (IdxSum (Br M)).getD 0 0 = 0 := by
        simpa using idxSum_getD (Br M) 0 (Nat.zero_le _)
      have hFN0 : (FirstNodes M).getD 0 0 = 1 := by
        rw [FirstNodes_getD M 0 hJ0, hIdx0, htr0]
      left
      rw [hrn1B, show (Br M).length - 1 = 0 by omega, hFN0]
    · -- B1: `TrMax M = 1 = Lng M - 2`
      have htr1 : TrMax M = 1 := by omega
      have htrMeq : TrMax M = Lng M - 2 := by omega
      obtain ⟨hBrL, _, hJ0tr⟩ := baseU_caseI_geom M hR hmono hBrne hj1gt hAdmpos htrMeq
      right
      rw [hrn1B, show (Br M).length - 1 = 0 by omega, hJ0tr, htr1]

/-! ## §8.2 キーストーンの段階的還元と無条件化（Isabelle wip 30460–32509）

`8.2-subexpr-final` の 5 本の `SXP_*` を、本ファイルと既ビルドの兄弟ファイルから
すべて実体化する。 -/

/-- `8.2-subexpr-admpos-engine` の `ScbOuterSurgerySplit`（Isabelle
`scb_outer_surgery_split`, wip 26412）は `7.2-scb-outer-surgery-split` で証明済。 -/
theorem scbOuterSurgerySplit_holds : ScbOuterSurgerySplit := scb_outer_surgery_split

/-- `SXP_subexpr_component_Pred_Adm0_full` ← `8.2-subexpr-adm0-full`（無条件）。 -/
theorem sxp_Adm0_full_holds : SXP_subexpr_component_Pred_Adm0_full :=
  fun M hR hmono hBrne hj1gt hAdm0 =>
    subexpr_component_Pred_Adm0_full M hR hmono hBrne hj1gt hAdm0

/-- `SXP_wid_of_predwid` ← `8.2-subexpr-admpos-engine` の `wid_of_predwid`
（外科分割は `scb_outer_surgery_split` で放電）。 -/
theorem sxp_wid_of_predwid_holds : SXP_wid_of_predwid :=
  fun M hR hmono hj1gt hAdmpos ht1ne predwid jt ft cp =>
    wid_of_predwid scbOuterSurgerySplit_holds M hR hmono hj1gt hAdmpos ht1ne predwid jt ft cp

/-- `8.2-subexpr-of-wid` の `Admpos_of_wid_hyp` ← `8.2-subexpr-adm0-full` の
`subexpr_component_Pred_Admpos_of_wid`（有限性は `8.2-subexpr-admpos-wfin`）。 -/
theorem admpos_of_wid_hyp_holds : Admpos_of_wid_hyp :=
  fun M hR hmono hj1gt hAdmpos ht1ne hwid =>
    subexpr_component_Pred_Admpos_of_wid M
      (trans_admpos_body_split_wfin scbOuterSurgerySplit_holds)
      hR hmono hj1gt hAdmpos ht1ne hwid

/-- `SXP_subexpr_component_Pred_of_wid` ← `8.2-subexpr-of-wid`。 -/
theorem sxp_of_wid_holds : SXP_subexpr_component_Pred_of_wid :=
  fun M hR hmono hBrne hj1gt hwid =>
    subexpr_component_Pred_of_wid subexpr_component_Pred_Adm0_full
      admpos_of_wid_hyp_holds M hR hmono hBrne hj1gt hwid

/-- **`SXP_wid_baseU` を放電**（Isabelle `m_8_2_baseU`, wip 30183）。 -/
theorem sxp_wid_baseU_holds : SXP_wid_baseU :=
  fun M hR hmono hBrne hj1gt hAdmpos hbase =>
    baseU scbOuterSurgerySplit_holds M hR hmono hBrne hj1gt hAdmpos hbase

/-- **`SXP_wid_cpU` を放電**: `branchPar`（無条件）→ `chainOK` → `widTrM` → `cpU`。 -/
theorem sxp_wid_cpU_holds : SXP_wid_cpU :=
  fun M hR hmono hBrne hj1gt hAdmpos hbrP hj1eq =>
    cpU_of_chainOK scbOuterSurgerySplit_holds M hR hmono hBrne hj1gt hAdmpos hbrP hj1eq
      (chainOK_of_branchPar M
        (fun b hbgt hble =>
          branchPar M b hmono (RTPS_TPS M hR) hBrne hAdmpos hj1eq hbgt hble)
        hR hmono hBrne hj1gt hAdmpos hbrP hj1eq)

/-- Isabelle `m_8_2_wid_uncond` (`layerB/pss_wip.thy:30460`): `m_8_2_wid` の 2 本の
普遍残差のうち、帰納基底 `baseU` を無条件に放電したもの。真正の結合 `cpU` のみが
前提として残る（`m_8_2_wid` より真に強い）。 -/
theorem wid_uncond (cpU : SXP_wid_cpU)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    wid M :=
  wid_holds sxp_Adm0_full_holds sxp_wid_of_predwid_holds cpU sxp_wid_baseU_holds
    M hR hmono hBrne hj1gt

/-- Isabelle `m_8_2_subexpr_component_Pred_final` (`layerB/pss_wip.thy:30518`):
§8.2 キーストーンで `baseU` を放電した形。残る前提は `cpU` のみ。 -/
theorem subexpr_component_Pred_final (cpU : SXP_wid_cpU)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    -- (1)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
    -- (2)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
    -- (3)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
    -- (4)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) :=
  subexpr_component_Pred sxp_Adm0_full_holds sxp_wid_of_predwid_holds sxp_of_wid_holds
    cpU sxp_wid_baseU_holds M hR hmono hBrne hj1gt

/-- Isabelle `m_8_2_subexpr_component_Pred_via_chainOK` (`layerB/pss_wip.thy:30864`):
§8.2 キーストーンを唯一の残差 `j₁eq ⟹ chainOK` に還元した形。 -/
theorem subexpr_component_Pred_via_chainOK
    (chainOKres : ∀ M' : PS, RTPS M' → monoT M' = true → Br M' ≠ [] → 1 < Lng M' - 1 →
      0 < transJm1 M' → Br (Pred M') ≠ [] →
      (FirstNodes M').getD ((Br M').length - 1) 0 = Lng M' - 1 → chainOK M')
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    -- (1)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
    -- (2)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
    -- (3)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
    -- (4)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) :=
  subexpr_component_Pred_final
    (fun M' hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq' =>
      cpU_of_chainOK scbOuterSurgerySplit_holds M' hR' hmono' hBrne' hj1gt' hAdmpos'
        hbrP' hj1eq'
        (chainOKres M' hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq'))
    M hR hmono hBrne hj1gt

/-- Isabelle `m_8_2_subexpr_component_Pred_done` (`layerB/pss_wip.thy:31789`):
`branchPar` を各キーストーン定義域 `M'` に供給すると `chainOKres` が放電され、
§8.2 キーストーン全体が幾何残差 `branchPar` のみに条件付けられる。 -/
theorem subexpr_component_Pred_done
    (branchParAll : ∀ (M' : PS) (b : ℕ), RTPS M' → monoT M' = true → Br M' ≠ [] →
      1 < Lng M' - 1 → 0 < transJm1 M' → Br (Pred M') ≠ [] →
      (FirstNodes M').getD ((Br M').length - 1) 0 = Lng M' - 1 →
      TrMax M' < b → b ≤ Lng M' - 1 → TrMax M' ≤ parent M' 0 b)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    -- (1)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
    -- (2)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
    -- (3)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
    -- (4)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) :=
  subexpr_component_Pred_via_chainOK
    (fun M' hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq' =>
      chainOK_of_branchPar M'
        (fun b hbgt hble =>
          branchParAll M' b hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq' hbgt hble)
        hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq')
    M hR hmono hBrne hj1gt

/-! ## §8.2 キーストーン — **無条件**（Isabelle `m_8_2_keystone`, wip 32461）

`m_8_2_subexpr_component_Pred_done` の普遍残差 `branchParAll` を、各キーストーン
定義域 `M'` について `branchPar`（本ファイルで無条件に証明済）が放電する。
**これで §8.2 が閉じる。** -/

/-- Isabelle `m_8_2_keystone` (`layerB/pss_wip.thy:32461`) ＝ 原文 §8.2
補題（部分表現の単項成分と `Pred` の関係）（`tmp/content.md` 3360、
paper `p_8_2_subexpr_component_Pred`, `isabelle/pss_paper.thy:1523`）の
**無条件形**。

`j₁ = Lng M - 1`, `J₁ = Lng (Br M) - 1`, `j′₀ = Joints(M)_{J₁}`,
`j′₁ = FirstNodes(M)_{J₁}`（Isabelle の `defines` は inline 済）。 -/
theorem keystone
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    -- (1)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
    -- (2)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
    -- (3)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
    -- (4)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) :=
  subexpr_component_Pred_done
    (fun M' b hR' hmono' hBrne' hj1gt' hAdmpos' hbrP' hj1eq' hbgt hble =>
      branchPar M' b hmono' (RTPS_TPS M' hR') hBrne' hAdmpos' hj1eq' hbgt hble)
    M hR hmono hBrne hj1gt

/-- 原文忠実形（`p_8_2_subexpr_component_Pred`, `isabelle/pss_paper.thy:1523`
＝ `tmp/content.md` 3360）の **無条件版**。`8.2-subexpr-final` の
`subexpr_component_Pred_faithful` に、本ファイルで実体化した 5 本の `SXP_*` を
差し込んだもの。Isabelle 側 `defines`（`j₁`/`J₁`/`j′₀`/`j′₁`）は inline 済なので
`keystone` と主張は一致する。 -/
theorem keystone_faithful
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    -- (1)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
    -- (2)
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
    -- (3)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
    -- (4)
    (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) :=
  subexpr_component_Pred_faithful sxp_Adm0_full_holds sxp_wid_of_predwid_holds
    sxp_of_wid_holds sxp_wid_cpU_holds sxp_wid_baseU_holds M hR hmono hBrne hj1gt


#print axioms transJ0_eq_TrMax
#print axioms joints_all_TrMax
#print axioms branchHigh
#print axioms branchPar
#print axioms TrMax_ge_1
#print axioms descAdm_of_premises
#print axioms chainOK_unfold
#print axioms chainOK_of_descAdm
#print axioms chainOK_of_branchPar
#print axioms baseU_Br_empty_TrMax
#print axioms baseU_alltrunk_diag_entry
#print axioms baseU_alltrunk_Trans_RN1
#print axioms chainOK_imp_widTrM
#print axioms j0_eq_TrMax
#print axioms cpU_rhs_eq
#print axioms cpU_of_widTrMaxM
#print axioms cpU_of_chainOK
#print axioms baseU_twoseg_monoT
#print axioms baseU_caseI_geom
#print axioms baseU
#print axioms scbOuterSurgerySplit_holds
#print axioms sxp_Adm0_full_holds
#print axioms sxp_wid_of_predwid_holds
#print axioms admpos_of_wid_hyp_holds
#print axioms sxp_of_wid_holds
#print axioms sxp_wid_baseU_holds
#print axioms sxp_wid_cpU_holds
#print axioms wid_uncond
#print axioms subexpr_component_Pred_final
#print axioms subexpr_component_Pred_via_chainOK
#print axioms subexpr_component_Pred_done
#print axioms keystone
#print axioms keystone_faithful

end PSS
