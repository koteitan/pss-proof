import «8».«8.2-subexpr-wid»

/-!
# §8.2 補題（部分表現の単項成分と `Pred` の関係）— TOP WIRING

- 原文: `tmp/content.md` 3360（§8.2 補題（部分表現の単項成分と `Pred` の関係））、
  および 3432–3435（`j₁ - TrMax(M)` に関する帰納法＝ w-identification）。
- 訂正: **該当なし**。§8.2 に触れる訂正は `A9`（LastStep の添字 `J₁` の範囲外参照
  [軽微]）のみで、これは §8.2「強単項性」節の写像 `LastStep` の定義文に対する
  添字範囲の補正である。本ファイルの補題は `J₁ = Lng (Br M) - 1` を
  `Br M ≠ []` の下でのみ使い、既に訂正後の添字で書かれているため影響しない。
  （`8.2-subexpr-setup` の判断と同一。）

## Isabelle 対応（`isabelle/layerB/pss_wip.thy`）

- `wid_holds`               ← `m_8_2_wid` (29605–29701)
- `subexpr_component_Pred`  ← `m_8_2_subexpr_component_Pred` (29702–29886)
- `subexpr_component_Pred_faithful` ← 原文忠実形
  `p_8_2_subexpr_component_Pred`（`isabelle/pss_paper.thy:1523`）。
  Isabelle 側 `defines` (`j₁`/`J₁`/`j′₀`/`j′₁`) を全て inline したため、
  `subexpr_component_Pred` と主張は一致する（前提 `cpU`/`baseU` も原典の
  `m_8_2_wid` がそのまま残す真正の残差であり、paper 版はそれを `sorry` に
  している）。ここでは残差を明示した仮定形で導出する。

## GREEN-MODULO（本 wave の兄弟ファイルが並行執筆中で import 不可）

未ビルドの brick は `def SXP_<IsaName> : Prop := ∀ ...` として 1:1 で宣言し、
それを仮定として組み上げる。親が兄弟ファイルに対して discharge する。

- `SXP_subexpr_component_Pred_Adm0_full` ← `m_8_2_subexpr_component_Pred_Adm0_full`
  (27019)。`Adm0` 枝を無条件で閉じる。
- `SXP_wid_of_predwid`  ← `m_8_2_wid_of_predwid` (29038)。`Admpos` の帰納ステップ
  （内部で未移植の `m_8_2_wid_step` (28837) ＝ `trans_admpos_body_split` (26573)
  外科機構を使う）。
- `SXP_subexpr_component_Pred_of_wid` ← `m_8_2_subexpr_component_Pred_of_wid`
  (28627)。`wid` からキーストーン 4 分岐へ。

加えて、Isabelle `m_8_2_wid` **自身**が残す 2 本の真正残差（兄弟 brick ではなく
原典未証明の側条件）を同名で宣言する:

- `SXP_wid_cpU`   ← `m_8_2_wid` の `cpU`（`j₁eq ⟹ JOINTS 節選択` の結合、
  経験的に 291/291）
- `SXP_wid_baseU` ← `m_8_2_wid` の `baseU`（`Pred M` に IH が使えない帰納基底）

## 依存（ビルド済ツールボックス）

- `wid` / `wid_iff` / `keystone_imp_wid` / `ft_transport` / `jt_transport`
  （`8.2-subexpr-wid`）
- `subexpr_component_Pred_setup`（`8.2-subexpr-setup`）: `RTPS (Pred M)`,
  `Trans (Pred M) ≠ BZero`, `TrMax M < Lng M - 1` を一括供給
- `length_Pred` / `TrMax_Pred_nontrunk` / `monoT_Pred_long`
  （`6.5-Red-Pred-commute`）, `RTPS_TPS`（`6.6-reduced-leftend`）

## 状態

本ファイル単独で green（sorry 0）。スコープ = 上記 5 本の `SXP_*` に対する
green-modulo。私的補助は suffix `_fin`。
-/

namespace PSS

/-! ## Green-modulo brick 宣言（`SXP_*`）

いずれも Isabelle の当該 lemma の主張を 1:1 で転記したもの。
`M ∈ RT_PS ∧ M ∈ PT_PS` は Lean 綴りで `(hR : RTPS M) (hmono : monoT M = true)`。 -/

/-- Isabelle `m_8_2_subexpr_component_Pred_Adm0_full` (`layerB/pss_wip.thy:27019`)。
`transJm1 M = 0`（`Adm0`）枝でキーストーン 4 分岐を無条件に与える。 -/
def SXP_subexpr_component_Pred_Adm0_full : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → Br M ≠ [] → 1 < Lng M - 1 →
    transJm1 M = 0 →
    (((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
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
                t123.2.2))))

/-- Isabelle `m_8_2_wid_of_predwid` (`layerB/pss_wip.thy:29038`)。
`Admpos` 枝の帰納ステップ: `Pred M` の `wid`（＋ `jt`/`ft` 転送と `cp` 結合）から
`M` の `wid` を出す。`JN = Lng (Br (Pred M)) - 1`, `J₁ = Lng (Br M) - 1`。 -/
def SXP_wid_of_predwid : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → 0 < transJm1 M →
    Trans (Pred M) ≠ BZero →
    ((RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) ∨
        (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0)) →
    (entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
      entry M 1 ((Joints M).getD ((Br M).length - 1) 0)) →
    ((FirstNodes M).getD ((Br M).length - 1) 0 ≠ Lng M - 1 →
      entry (Pred M) 1 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
        entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)) →
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 →
      (RightNodes (Trans (Pred M))).getD 1 0 =
        entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0)) →
    wid M

/-- Isabelle `m_8_2_subexpr_component_Pred_of_wid` (`layerB/pss_wip.thy:28627`)。
w-identification `wid M` からキーストーン 4 分岐へ。 -/
def SXP_subexpr_component_Pred_of_wid : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → Br M ≠ [] → 1 < Lng M - 1 →
    wid M →
    (((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
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
                t123.2.2))))

/-! ### Isabelle `m_8_2_wid` 自身が残す 2 本の残差

これらは兄弟 brick ではなく、Isabelle 側でも未証明の側条件である
（`m_8_2_wid` (29605) / `m_8_2_subexpr_component_Pred` (29702) の
`assumes cpU` / `assumes baseU` をそのまま転記）。 -/

/-- Isabelle `m_8_2_wid` の `cpU`: `j₁eq`（最終枝が単項最終列）の幾何の下で
`Pred M` の `RightNodes` 第 2 成分は JOINTS 節を選ぶ、という結合。
経験的に 291/291（`python/_cpU_*.py`）。 -/
def SXP_wid_cpU : Prop :=
  ∀ M' : PS, RTPS M' → monoT M' = true → Br M' ≠ [] → 1 < Lng M' - 1 →
    0 < transJm1 M' → Br (Pred M') ≠ [] →
    (FirstNodes M').getD ((Br M').length - 1) 0 = Lng M' - 1 →
    (RightNodes (Trans (Pred M'))).getD 1 0 =
      entry (Pred M') 1 ((Joints (Pred M')).getD ((Br (Pred M')).length - 1) 0)

/-- Isabelle `m_8_2_wid` の `baseU`: `Pred M'` に帰納法の仮定が使えない基底
（`Br (Pred M') = []`、または `Lng (Pred M') - 1 ≤ 1` すなわち `Lng M' = 3`）での
`wid M'`。 -/
def SXP_wid_baseU : Prop :=
  ∀ M' : PS, RTPS M' → monoT M' = true → Br M' ≠ [] → 1 < Lng M' - 1 →
    0 < transJm1 M' →
    (Br (Pred M') = [] ∨ ¬ (1 < Lng (Pred M') - 1)) →
    wid M'

/-! ## `wid` の帰納法（Isabelle `m_8_2_wid` 29605）

測度 `Lng M - 1 - TrMax M`（`= j₁ - TrMax(M)`）に関する強帰納法。
`Adm0` 枝は `SXP_subexpr_component_Pred_Adm0_full` ＋ `keystone_imp_wid` で
IH 不要・残差不要に閉じる。`Admpos` 枝では `Pred M` の測度が真に減る
（`TrMax (Pred M) = TrMax M`（`TrMax_Pred_nontrunk`）かつ
`Lng (Pred M) = Lng M - 1`、`TrMax M < Lng M - 1`）ので IH が `predwid` を供給し、
証明済の `jt_transport` / `ft_transport` と `cpU` を添えて `SXP_wid_of_predwid`
で閉じる。IH が使えない基底が `baseU`。 -/

/-- 測度 `Lng M - 1 - TrMax M ≤ n` に関する累積帰納法の本体。 -/
private theorem wid_aux_fin
    (hAdm0full : SXP_subexpr_component_Pred_Adm0_full)
    (hstep : SXP_wid_of_predwid)
    (cpU : SXP_wid_cpU) (baseU : SXP_wid_baseU) :
    ∀ (n : ℕ) (M : PS), Lng M - 1 - TrMax M ≤ n → RTPS M → monoT M = true →
      Br M ≠ [] → 1 < Lng M - 1 → wid M := by
  intro n
  induction n with
  | zero =>
      intro M hmeas hR hmono hBrne hj1gt
      -- 測度 0 は `Br M ≠ []`（⟹ `TrMax M < Lng M - 1`）と矛盾
      have hset := subexpr_component_Pred_setup M hR hmono hBrne hj1gt
      have htrlt : TrMax M < Lng M - 1 := hset.2.2.2.2.2.2.2.2.2
      exfalso
      omega
  | succ n ih =>
      intro M hmeas hR hmono hBrne hj1gt
      have hset := subexpr_component_Pred_setup M hR hmono hBrne hj1gt
      have htrlt : TrMax M < Lng M - 1 := hset.2.2.2.2.2.2.2.2.2
      have hpredR : RTPS (Pred M) := hset.2.2.2.2.2.2.1
      have ht1ne : Trans (Pred M) ≠ BZero := hset.2.2.2.2.2.2.2.2.1
      have hMT : TPS M := RTPS_TPS M hR
      have hlen : 1 < Lng M := by omega
      by_cases hAdm0 : transJm1 M = 0
      · -- `Adm0` 枝: 無条件（IH も残差も不要）
        exact keystone_imp_wid M (hAdm0full M hR hmono hBrne hj1gt hAdm0)
      · -- `Admpos` 枝
        have hAdmpos : 0 < transJm1 M := Nat.pos_of_ne_zero hAdm0
        have hne : TrMax M ≠ Lng M - 1 := by omega
        have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
        have htrP : TrMax (Pred M) = TrMax M := TrMax_Pred_nontrunk M hMT hlen hne
        by_cases hbrP : Br (Pred M) = []
        · exact baseU M hR hmono hBrne hj1gt hAdmpos (Or.inl hbrP)
        · by_cases hLpgt : 1 < Lng (Pred M) - 1
          · -- IH が使える: `Pred M` の測度は真に小さい
            have hmonoP : monoT (Pred M) = true :=
              monoT_Pred_long M hMT hmono (by omega)
            have hmeasP : Lng (Pred M) - 1 - TrMax (Pred M) ≤ n := by
              rw [hLP, htrP]; omega
            have hpw : wid (Pred M) := ih (Pred M) hmeasP hpredR hmonoP hbrP hLpgt
            exact hstep M hR hmono hj1gt hAdmpos ht1ne ((wid_iff (Pred M)).mp hpw)
              (jt_transport M hR hmono hBrne hj1gt hAdmpos hbrP)
              (fun h => ft_transport M hR hmono hBrne hj1gt hbrP h)
              (fun h => cpU M hR hmono hBrne hj1gt hAdmpos hbrP h)
          · exact baseU M hR hmono hBrne hj1gt hAdmpos (Or.inr hLpgt)

/-- Isabelle `m_8_2_wid` (`layerB/pss_wip.thy:29605`)。

`M ∈ RT_PS ∩ PT_PS`, `Br M ≠ []`, `j₁ = Lng M - 1 > 1` の下で
w-identification `wid M` が成り立つ:
`RightNodes (Trans M)` の第 2 成分は、最終枝の first node `j′₁` の行 1 成分か、
最終 joint `j′₀` の行 1 成分のいずれかである。 -/
theorem wid_holds
    (hAdm0full : SXP_subexpr_component_Pred_Adm0_full)
    (hstep : SXP_wid_of_predwid)
    (cpU : SXP_wid_cpU) (baseU : SXP_wid_baseU)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
    wid M :=
  wid_aux_fin hAdm0full hstep cpU baseU (Lng M - 1 - TrMax M) M le_rfl
    hR hmono hBrne hj1gt

/-! ## §8.2 キーストーン（Isabelle `m_8_2_subexpr_component_Pred` 29702）

`wid_holds` ＋ `SXP_subexpr_component_Pred_of_wid` の合成。 -/

/-- Isabelle `m_8_2_subexpr_component_Pred` (`layerB/pss_wip.thy:29702`)
＝ §8.2 補題（部分表現の単項成分と `Pred` の関係）（`tmp/content.md` 3360）。

`j₁ = Lng M - 1`, `J₁ = Lng (Br M) - 1`, `j′₀ = Joints(M)_{J₁}`,
`j′₁ = FirstNodes(M)_{J₁}`（Isabelle の `defines` は inline 済）。
4 分岐 (1)–(4) のいずれかが成り立ち、各分岐が `Trans (Pred M)` と `Trans M` を
`T_B`-項の一意な組で確定させる。 -/
theorem subexpr_component_Pred
    (hAdm0full : SXP_subexpr_component_Pred_Adm0_full)
    (hstep : SXP_wid_of_predwid)
    (hofwid : SXP_subexpr_component_Pred_of_wid)
    (cpU : SXP_wid_cpU) (baseU : SXP_wid_baseU)
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
  hofwid M hR hmono hBrne hj1gt
    (wid_holds hAdm0full hstep cpU baseU M hR hmono hBrne hj1gt)

/-! ## 原文忠実形（`isabelle/pss_paper.thy:1523` = `p_8_2_subexpr_component_Pred`）

原文 §8.2 補題（部分表現の単項成分と `Pred` の関係）（article 3360）の転写。
paper 版は `defines j1/J1/j0'/j1'` を持つが、Lean では全て inline したので
`subexpr_component_Pred` と同一の主張になる（残差 `cpU`/`baseU` は原典
`m_8_2_wid` がそのまま残すもので、paper 側は `sorry`）。訂正 `A9` は
`LastStep` の添字補正であり本補題には無関係。 -/

/-- 原文忠実形（`p_8_2_subexpr_component_Pred`, `isabelle/pss_paper.thy:1523`）。 -/
theorem subexpr_component_Pred_faithful
    (hAdm0full : SXP_subexpr_component_Pred_Adm0_full)
    (hstep : SXP_wid_of_predwid)
    (hofwid : SXP_subexpr_component_Pred_of_wid)
    (cpU : SXP_wid_cpU) (baseU : SXP_wid_baseU)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) :
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
                t123.2.2))) :=
  subexpr_component_Pred hAdm0full hstep hofwid cpU baseU M hR hmono hBrne hj1gt

#print axioms wid_holds
#print axioms subexpr_component_Pred
#print axioms subexpr_component_Pred_faithful

end PSS
