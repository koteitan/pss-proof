import «8».«8.2-standard-slice-Red-strongmono»
import «7».«7.4-RightNodes-Mark»
import «7».«7.4-RightAnces-RightNodes»
import «7».«7.3-Trans-preserves-zeroT»

/-!
# §8.2 補題（強単項性の下での部分表現の単項成分の基本性質）

- 原文: `tmp/content.md` 3454（§8.2 補題（強単項性の下での部分表現の単項成分の基本性質））。
  「\(t'\)の各単項成分は \(D_x 0\) 以上」は `∀ p ∈ PB t', leBT (Dprin x BZero) p = true`
  としてモデル化する（`PB t'` の要素は既に principal 成分そのもの）。
- 忠実形: `isabelle/pss_paper.thy:1563`（`p_8_2_subexpr_component_strongmono`）。
  Isabelle の `defines`（`J₁ = Lng (Br M) - 1`, `j′₀ = Joints(M)_{J₁}`,
  `j′₁ = FirstNodes(M)_{J₁}`）は本ファイルでは全て inline した。

## 訂正（A 番号）

**該当なし**。§8.2 に触れる訂正は `A9`（LastStep の添字 `J₁` の範囲外参照 [軽微]）
のみ。`A9` は §8.2「強単項性」節の写像 `LastStep` の定義文に対する添字範囲の補正で
あり、`LastStep` は本補題の主張にも証明にも一切現れない（本補題が使う添字は
`J₁ = Lng (Br M) - 1` のみで、`Br M ≠ []` の下でのみ用いるため既に訂正後の形）。
`8.2-subexpr-setup` / `8.2-subexpr-final` の判断と同一。

## Isabelle 対応（`isabelle/layerB/pss_wip.thy`）

- `subexpr_component_strongmono_of_witness` ← `m_8_2_subexpr_component_strongmono_of_witness`
  (33330–33379)
- `subexpr_component_strongmono_of_factAB`  ← `m_8_2_subexpr_component_strongmono_of_factAB`
  (34014–34071)
- `subexpr_component_strongmono`            ← `m_8_2_subexpr_component_strongmono` (34924)
  ＋ `m_8_2_subexpr_component_strongmono_uncond` (36477)。
  Isabelle の 34924 は `factBlem` を仮定に取り、`factA` を内部で
  `m_8_2_newdom` (34670) ＋ `m_8_2_factA` (34540) から作る。36477 は `factBlem` を
  `m_8_2_factB` (36200) で discharge する。本ファイルでは **factA / factB の両方**を
  名前付き `Prop`（`SXSM_*`）として受け取る＝ 36477 の green-modulo 形。
- 私的 `subexpr_leftend_unique_sm2` ← `m_8_2_subexpr_leftend_unique` (14900–14926)。
  **無条件に証明済**（本ファイル内、仮定なし）。
- `wit_step_thr` ← `m_8_2_wit_step_thr` (34088–34212)。**無条件に証明済**。
  主定理は使わないが、未移植の `m_8_2_factA_step` (34212) と `m_8_2_factB_step`
  (35130) が共通に使う抽象エンジンで、ビルド済ツリーに存在しないため同梱した
  （`SXSM_*` を閉じる際の再利用を意図）。私的支援:
  `wit_PB_relax_sm2` ← `wit_PB_relax` (33742)、
  `wit_PB_tail_bound_sm2` ← `wit_PB_tail_bound` (33765)、
  `rn1_outer_inner_trailing_sm2` ← `rn1_outer_inner_trailing` (28912)、
  および `PB_addBT_app` / `PB_Dpt_single` / `leBT_Dpt0_iff` の Lean 版
  （`PB_addBT_app_sm2` / `PB_Dprin_single_sm2` / `leBT_Dprin0_iff_sm2`）。
  `wit_step_thr` の `key` は `8.2-subexpr-final` の `subexpr_component_Pred` の
  結論と**同一の形**に書いてあるので drop-in で渡せる。

## 依存（ビルド済ツールボックス）

- `DTPS` / `DTPS_iff` / `DTPS_TPS`（`8.2-standard-slice-Red-strongmono`）
- `Trans_mono_leftend_form`（`7.4-RightNodes-Mark`:80）
- `Trans_preserves_zeroT`（`7.3-Trans-preserves-zeroT`:23）

## GREEN-MODULO

`m_8_2_factA_uncond` (35084) と `m_8_2_factB` (36200) は Lean 未移植（それぞれ
`m_8_2_newdom`/`m_8_2_factA_step`/`m_8_2_factA_base`、および
`m_8_2_widH`/`m_8_2_factB_base`/`m_8_2_factB_base2`/`m_8_2_factB_step`/
`m_8_2_wit_step_thr` の連鎖 ≈ 1500 行）。両者を `SXSM_factA_uncond` /
`SXSM_factB` として 1:1 宣言し、そこから組み上げる。

## 状態

本ファイル単独で green（sorry 0）。スコープ = 上記 2 本の `SXSM_*` に対する
green-modulo。`subexpr_leftend_unique_sm2`（＝一意性の全て、原文の主張 (1)）と
`wit_step_thr` は**無条件**。私的補助は suffix `_sm2`。

公開: `subexpr_component_strongmono_of_witness` / `..._of_factAB` /
`subexpr_component_strongmono` / `wit_step_thr`。
-/

namespace PSS

/-! ## Green-modulo brick 宣言（`SXSM_*`）

いずれも Isabelle の当該 lemma の主張を 1:1 で転記したもの。
`Lng (Br M) - 1` は `(Br M).length - 1`、`Joints M ! J₁` は
`(Joints M).getD J₁ 0`、`0_B` は `BZero`、`Dpt (enat x)` は `Dprin (x : ℕ∞)`。 -/

/-- Isabelle `m_8_2_factA_uncond` (`layerB/pss_wip.thy:35084`)。

`M ∈ DT_PS`, `Br M ≠ []`, 左端証拠 `Trans M = D_{M₁,₀} a`, `0 < j′₀` の下で、
`a` の各単項成分は `D_{M₁,j′₀} 0` 以上（＝原文 (3)/(4) の共通の下界）。

Isabelle 側は `m_8_2_newdom` (34670) ＋ `m_8_2_factA` (34540) で無条件に証明済み。 -/
def SXSM_factA_uncond : Prop :=
  ∀ (M : PS) (a : BT), DTPS M → Br M ≠ [] →
    Trans M = Dprin (entry M 1 0 : ℕ∞) a →
    0 < (Joints M).getD ((Br M).length - 1) 0 →
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p = true

/-- Isabelle `m_8_2_factB` (`layerB/pss_wip.thy:36200`)。

`M ∈ DT_PS`, `Br M ≠ []`, 左端証拠 `Trans M = D_{M₁,₀} a`, および原文 (2) の条件
`C`（`j′₀ = 0` または `M₀,j′₁ = M₁,j′₁`）の下で、`a` の各単項成分は
`D_{M₁,j′₁} 0` 以上。

Isabelle 側は `Lng M` に関する強帰納法で無条件に証明済み。 -/
def SXSM_factB : Prop :=
  ∀ (M : PS) (a : BT), DTPS M → Br M ≠ [] →
    Trans M = Dprin (entry M 1 0 : ℕ∞) a →
    ((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
      entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
    ∀ p ∈ PB a,
      leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞) BZero) p = true

/-! ## 左端分解の一意性（Isabelle `m_8_2_subexpr_leftend_unique` 14900）

原文の主張 (1)「一意な `t' ∈ T_B` が存在して `Trans M = D_{M₁,₀} t'`」の本体。
`monoT M`（`DT_PS` より）から `¬ zeroT M`、よって `Trans M ≠ 0_B`
（`Trans_preserves_zeroT`）。ここで `Trans_mono_leftend_form` が
`Trans M = D_{M₁,₀} t` を与える。一意性は `Trm [DB v ·]` の単射性。 -/

/-- Isabelle `m_8_2_subexpr_leftend_unique` (`layerB/pss_wip.thy:14900`)。**無条件**。 -/
private theorem subexpr_leftend_unique_sm2 (M : PS) (hMD : DTPS M) :
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

/-! ## 証拠からの構成（Isabelle `m_8_2_subexpr_component_strongmono_of_witness` 33330）

存在は証拠 `a` とその 3 本の下界 `w2`/`w3`/`w4` をそのまま束ねるだけ。一意性は
主張 (1) の成分（＝`subexpr_leftend_unique_sm2`）だけで決まる（(2)–(4) は
含意の形なので `t'` を制約しない）。 -/

/-- Isabelle `m_8_2_subexpr_component_strongmono_of_witness`
(`layerB/pss_wip.thy:33330`)。 -/
theorem subexpr_component_strongmono_of_witness
    (M : PS) (a : BT) (hMD : DTPS M) (_hBrne : Br M ≠ [])
    (w1 : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (w2 : ((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
          ∀ p ∈ PB a,
            leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero) p = true)
    (w3 : (0 < (Joints M).getD ((Br M).length - 1) 0 ∧
            (Joints M).getD ((Br M).length - 1) 0 < TrMax M ∧
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
              entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
          ∀ p ∈ PB a,
            leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero) p = true)
    (w4 : (0 < (Joints M).getD ((Br M).length - 1) 0 ∧
            (Joints M).getD ((Br M).length - 1) 0 = TrMax M) →
          ∀ p ∈ PB a,
            leBT (Dprin (entry M 1 (TrMax M) : ℕ∞) BZero) p = true) :
    ∃! t' : BT,
      Trans M = Dprin (entry M 1 0 : ℕ∞) t' ∧
      (((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
          entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 < TrMax M ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 = TrMax M) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 (TrMax M) : ℕ∞) BZero) p = true) := by
  obtain ⟨b, -, hb⟩ := subexpr_leftend_unique_sm2 M hMD
  refine ⟨a, ⟨w1, w2, w3, w4⟩, ?_⟩
  rintro t' ⟨hc1, -, -, -⟩
  rw [hb t' hc1, hb a w1]

/-! ## factA/factB からの構成（Isabelle `..._of_factAB` 34014）

`w3` / `w4` はいずれも `0 < j′₀` しか使わないので `factA` から直ちに出る
（`w4` は `j′₀ = TrMax M` を書き換えるだけ）。 -/

/-- Isabelle `m_8_2_subexpr_component_strongmono_of_factAB`
(`layerB/pss_wip.thy:34014`)。 -/
theorem subexpr_component_strongmono_of_factAB
    (M : PS) (a : BT) (hMD : DTPS M) (hBrne : Br M ≠ [])
    (w1 : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (factA : 0 < (Joints M).getD ((Br M).length - 1) 0 →
      ∀ p ∈ PB a,
        leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
          BZero) p = true)
    (factB : ((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
        entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
      ∀ p ∈ PB a,
        leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
          BZero) p = true) :
    ∃! t' : BT,
      Trans M = Dprin (entry M 1 0 : ℕ∞) t' ∧
      (((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
          entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 < TrMax M ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 = TrMax M) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 (TrMax M) : ℕ∞) BZero) p = true) := by
  refine subexpr_component_strongmono_of_witness M a hMD hBrne w1 factB ?_ ?_
  · rintro ⟨hpos, -, -⟩
    exact factA hpos
  · rintro ⟨hpos, hEq⟩
    rw [← hEq]
    exact factA hpos

/-! ## 主定理（Isabelle `m_8_2_subexpr_component_strongmono` 34924
／`..._uncond` 36477）

原文 3454 の忠実形（`isabelle/pss_paper.thy:1563` = `p_8_2_subexpr_component_strongmono`）。
Isabelle の `defines j₁/J₁/j′₀/j′₁` は全て inline したので、paper 版と主張が一致する。 -/

/-- 原文 §8.2 補題（強単項性の下での部分表現の単項成分の基本性質）
（`tmp/content.md` 3454、`isabelle/pss_paper.thy:1563`）。

`J₁ = Lng (Br M) - 1`, `j′₀ = Joints(M)_{J₁}`, `j′₁ = FirstNodes(M)_{J₁}`
（inline 済）。`M ∈ DT_PS`（強単項）かつ `Br M ≠ []` のとき、一意な `t' ∈ T_B` が
存在して

- (1) `Trans M = D_{M₁,₀} t'`;
- (2) `j′₀ = 0` または `M₀,j′₁ = M₁,j′₁` ならば `t'` の各単項成分は `D_{M₁,j′₁} 0` 以上;
- (3) `0 < j′₀ < TrMax M` かつ `M₀,j′₁ > M₁,j′₁` ならば各単項成分は `D_{M₁,j′₀} 0` 以上;
- (4) `0 < j′₀ = TrMax M` ならば各単項成分は `D_{M₁,TrMax M} 0` 以上。

一意性（(1) の `∃!`）は無条件に証明済み（`subexpr_leftend_unique_sm2`）。
下界 (2)–(4) は Isabelle の `m_8_2_factB` / `m_8_2_factA_uncond` に対する
green-modulo。 -/
theorem subexpr_component_strongmono
    (hfactA : SXSM_factA_uncond) (hfactB : SXSM_factB)
    (M : PS) (hMD : DTPS M) (hBrne : Br M ≠ []) :
    ∃! t' : BT,
      Trans M = Dprin (entry M 1 0 : ℕ∞) t' ∧
      (((Joints M).getD ((Br M).length - 1) 0 = 0 ∨
          entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
            entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 < TrMax M ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero) p = true) ∧
      ((0 < (Joints M).getD ((Br M).length - 1) 0 ∧
          (Joints M).getD ((Br M).length - 1) 0 = TrMax M) →
        ∀ p ∈ PB t',
          leBT (Dprin (entry M 1 (TrMax M) : ℕ∞) BZero) p = true) := by
  obtain ⟨a, ha, -⟩ := subexpr_leftend_unique_sm2 M hMD
  exact subexpr_component_strongmono_of_factAB M a hMD hBrne ha
    (fun hpos => hfactA M a hMD hBrne ha hpos)
    (fun hC => hfactB M a hMD hBrne ha hC)

/-! ## §8.2 証拠持ち上げエンジン（Isabelle `wit_PB_relax` 33742 ／
`wit_PB_tail_bound` 33765 ／`m_8_2_wit_step_thr` 34088）

上の主定理は使わないが、未移植の `m_8_2_factA_step` (34212) と
`m_8_2_factB_step` (35130) が**共通に**使う抽象エンジン。ビルド済ツリーに存在
しないのでここで移植しておく（`SXSM_factA_uncond` / `SXSM_factB` を閉じる際の
再利用を意図）。 -/

/-- `PB` は `+_B` 上で連結に分配する（Isabelle `PB_addBT_app`）。 -/
private theorem PB_addBT_app_sm2 (a b : BT) : PB (addBT a b) = PB a ++ PB b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  simp [PB, addBT, untrm]

/-- principal 項の `PB` は単元リスト（Isabelle `PB_Dpt_single`）。 -/
private theorem PB_Dprin_single_sm2 (v : ℕ∞) (t : BT) : PB (Dprin v t) = [Dprin v t] := by
  simp [PB, Dprin, untrm]

private theorem lessBT_BZero_iff_sm2 (c : BT) : lessBT BZero c = true ↔ c ≠ BZero := by
  rcases c with ⟨cs⟩
  cases cs with
  | nil => simp [BZero, lessBT, lessBPList]
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-- Isabelle `leBT_Dpt0_iff`: `D_u 0 ≤_B D_v c ⟺ u ≤ v`。 -/
private theorem leBT_Dprin0_iff_sm2 (u v : ℕ∞) (c : BT) :
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
      · exact Or.inl (Or.inr ⟨heq, (lessBT_BZero_iff_sm2 c).mpr hc⟩)

/-- Isabelle `rn1_outer_inner_trailing` (28912)。 -/
private theorem rn1_outer_inner_trailing_sm2 (v : ℕ∞) (x : ℕ) (pre s : BT) :
    (RightNodes (Dprin v (addBT pre (Dprin (x : ℕ∞) s)))).getD 1 0 = x := by
  rw [RightNodes_Dprin, RightNodes_addBT_Dprin]
  simp

private theorem PB_mem_Dprin_sm2 {a r : BT} (hr : r ∈ PB a) : ∃ v c, r = Dprin v c := by
  simp only [PB, List.mem_map] at hr
  obtain ⟨p, -, rfl⟩ := hr
  rcases p with ⟨v, c⟩
  exact ⟨v, c, rfl⟩

/-- Isabelle `wit_PB_relax` (`layerB/pss_wip.thy:33742`): 閾値の緩和。 -/
private theorem wit_PB_relax_sm2 (a : BT) (thr thr' : ℕ)
    (L : ∀ r ∈ PB a, leBT (Dprin (thr' : ℕ∞) BZero) r = true) (hle : thr ≤ thr') :
    ∀ r ∈ PB a, leBT (Dprin (thr : ℕ∞) BZero) r = true := by
  intro r hr
  obtain ⟨v, c, rfl⟩ := PB_mem_Dprin_sm2 hr
  have h1 : (thr' : ℕ∞) ≤ v := (leBT_Dprin0_iff_sm2 _ _ _).mp (L _ hr)
  have h2 : (thr : ℕ∞) ≤ (thr' : ℕ∞) := by exact_mod_cast hle
  exact (leBT_Dprin0_iff_sm2 _ _ _).mpr (le_trans h2 h1)

/-- Isabelle `wit_PB_tail_bound` (`layerB/pss_wip.thy:33765`): 末尾 principal の追加。 -/
private theorem wit_PB_tail_bound_sm2 (p q : BT) (thr x : ℕ)
    (L : ∀ r ∈ PB p, leBT (Dprin (thr : ℕ∞) BZero) r = true) (hc : thr ≤ x) :
    ∀ r ∈ PB (addBT p (Dprin (x : ℕ∞) q)), leBT (Dprin (thr : ℕ∞) BZero) r = true := by
  intro r hr
  rw [PB_addBT_app_sm2, PB_Dprin_single_sm2] at hr
  rcases List.mem_append.mp hr with h | h
  · exact L r h
  · rw [List.mem_singleton.mp h]
    exact (leBT_Dprin0_iff_sm2 _ _ _).mpr (by exact_mod_cast hc)

/-- Isabelle `m_8_2_wit_step_thr` (`layerB/pss_wip.thy:34088`)。

キーストーン 4 分岐 `key`（＝`8.2-subexpr-final` の `subexpr_component_Pred` の
結論と同一の形）の**どの枝でも** `a = p +_B D_x q₂` かつ `PB p ⊆ PB aP` になる、
という一様な事実だけを使って、`Pred M` 側の下界 `thr'` を `M` 側の下界 `thr` へ
持ち上げる。側条件は `thr ≤ thr'`（閾値単調性）と
`thr ≤ RightNodes(Trans M)₁`（新 head の支配）の 2 本のみ。 -/
theorem wit_step_thr (M : PS) (a aP : BT) (thr thr' : ℕ)
    (aW : Trans M = Dprin (entry M 1 0 : ℕ∞) a)
    (predW : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) aP)
    (ihA : ∀ r ∈ PB aP, leBT (Dprin (thr' : ℕ∞) BZero) r = true)
    (thrmono : thr ≤ thr')
    (newdom : thr ≤ (RightNodes (Trans M)).getD 1 0)
    (key :
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
      (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
              (addBT t123.1
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t123.1
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t123.2.2))) ∨
      (∃! t123 : BT × BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
              (addBT t123.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t123.2.1)) ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t123.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t123.2.2)))) :
    ∀ r ∈ PB a, leBT (Dprin (thr : ℕ∞) BZero) r = true := by
  -- 一様な末尾閉包ブロック: `a = p +_B D_x q₂`、prefix は IH が覆う
  have close : ∀ (p q2 : BT) (x : ℕ), a = addBT p (Dprin (x : ℕ∞) q2) →
      (∀ r ∈ PB p, r ∈ PB aP) →
      ∀ r ∈ PB a, leBT (Dprin (thr : ℕ∞) BZero) r = true := by
    intro p q2 x had hsub
    have onp1 : ∀ r ∈ PB p, leBT (Dprin (thr' : ℕ∞) BZero) r = true :=
      fun r hr => ihA r (hsub r hr)
    have onp2 : ∀ r ∈ PB p, leBT (Dprin (thr : ℕ∞) BZero) r = true :=
      wit_PB_relax_sm2 p thr thr' onp1 thrmono
    have rn : (RightNodes (Trans M)).getD 1 0 = x := by
      rw [aW, had]
      exact rn1_outer_inner_trailing_sm2 _ _ _ _
    have thx : thr ≤ x := by rw [rn] at newdom; exact newdom
    rw [had]
    exact wit_PB_tail_bound_sm2 p q2 thr x onp2 thx
  rcases key with A | A | A | A
  · -- 分岐 (1): `aP = t₁`, `a = t₁ +_B D_{M₁,j′₁} 0`
    obtain ⟨t₁, ⟨hC, hT⟩, -⟩ := A.2.2.2
    have had : a = addBT t₁ (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
        BZero) := by rw [aW] at hT; simpa [Dprin] using hT
    have haP : aP = t₁ := by rw [predW] at hC; simpa [Dprin] using hC
    exact close _ _ _ had (by rw [haP]; exact fun r hr => hr)
  · -- 分岐 (2): `aP = t12.1`, `a = t12.1 +_B D_{M₁,j′₀} t12.2`
    obtain ⟨t12, ⟨hC, hT⟩, -⟩ := A.2.2.2
    have had : a = addBT t12.1 (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
        t12.2) := by rw [aW] at hT; simpa [Dprin] using hT
    have haP : aP = t12.1 := by rw [predW] at hC; simpa [Dprin] using hC
    exact close _ _ _ had (by rw [haP]; exact fun r hr => hr)
  · -- 分岐 (3): `aP = t123.1 +_B D_{M₁,j′₁} t123.2.1`（`a` と同 head）
    obtain ⟨t123, ⟨hC, hT⟩, -⟩ := A
    have had : a = addBT t123.1
        (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞) t123.2.2) := by
      rw [aW] at hT; simpa [Dprin] using hT
    have haP : aP = addBT t123.1
        (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞) t123.2.1) := by
      rw [predW] at hC; simpa [Dprin] using hC
    refine close _ _ _ had ?_
    intro r hr
    rw [haP, PB_addBT_app_sm2]
    exact List.mem_append_left _ hr
  · -- 分岐 (4): `aP = t123.1 +_B D_{M₁,j′₀} t123.2.1`（`a` と同 head）
    obtain ⟨t123, ⟨hC, hT⟩, -⟩ := A
    have had : a = addBT t123.1
        (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) t123.2.2) := by
      rw [aW] at hT; simpa [Dprin] using hT
    have haP : aP = addBT t123.1
        (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) t123.2.1) := by
      rw [predW] at hC; simpa [Dprin] using hC
    refine close _ _ _ had ?_
    intro r hr
    rw [haP, PB_addBT_app_sm2]
    exact List.mem_append_left _ hr

#print axioms subexpr_component_strongmono_of_witness
#print axioms subexpr_component_strongmono_of_factAB
#print axioms subexpr_component_strongmono
#print axioms wit_step_thr

end PSS
