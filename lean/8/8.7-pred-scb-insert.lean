import «8».«8.7-Pred-oper0-general»
import «8».«8.3-condII-masterCF»
import «7».«7.3-c1-c2-order»

/-!
# §8.7 補題（`Pred` と `[0]` の関係）— 構造残差 `TransPredScbInsert_pg` の攻略

- 原文: `tmp/content.md` article 6018–6058（簡約性→条件(A)(B)→scb 置換可能性→
  条件(I)–(VI) 分析）。姉妹ファイル `8.7-Pred-oper0-general.lean` が
  `TransPredScbInsert_pg` を単一の構造残差として露出し、既存ネスト零化
  `trailing_principal_annihilable`（`8.6`）で一般形 `PredOper0_pg` へ**無条件**還元済み。
  本ファイルはその**構造残差そのもの**を、`Trans M` と `Trans (Pred M)` の
  共有 scb 文脈（master key `Trans_c1_c2_decomp`, `8.3-condII-masterCF`）から
  **条件分岐ごと**に討伐する。
- Isabelle: `p_8_7_Pred_oper0`（`pss_paper.thy:2298`, `sorry` のまま）＝Isabelle は
  この構造事実を**一度も証明していない**（`p_8_7_OT_tail_annihilable` scb 逐語形も
  `sorry`）。従って本ファイルは Isabelle corpus を**超える**。数値監査
  `python/audit_87_pred_oper0.py` は `maxlen=6 maxval=4` で 806/806（反例ゼロ）。

## 攻略の骨子（枝 (I)/(III)/(V)）

`monoT M`・`reduced M`・`j₁ ≠ 0`・`Trans (Pred M) ≠ 0` の主枝では
`Trans M = replaceScb (Trans (Pred M)) c₁ c₂`（`c₁ = transC1 M`, `c₂ = transC2 M`）。
master key `Trans_c1_c2_decomp` は**条件非依存**に共有文脈 `(s, b)` を与える：

  `flatBT (Trans (Pred M)) = s ++ flatBT (transC1 M) ++ b`
  `flatBT (Trans M)        = s ++ flatBT (transC2 M) ++ b`

さらに `transC1 M = D_{v₀} t₂`（`transC1_single_principal` + `principal_reconstruct`,
`7.3-c1-c2-order`）であり、**条件 (I)∨(III)∨(V) のとき** `transC2Core` の第 1 枝が
発火して

  `transC2 M = D_{v₀}(t₂ +ᴮ D_{w} 0)`（`w = entry M 1 j₁`）

となる。これはまさに `TransPredScbInsert_pg` が要求する「共有 scb 文脈での末尾単項
`D_w 0` 挿入」である。従って枝 (I)/(III)/(V) では構造残差は master key から直ちに従う。

## 枝 (II)/(IV) の残差（明示）＋ 全体還元

条件 (II)/(IV) では `transC2Core` の第 1 枝が発火せず、`transC2 M` は**ネストした**
形（`D_{v₀}(D_{j'}(D_{j₁} 0))` 等）になる。単一挿入形 `TransPredScbInsert_pg` は
`Trans (Pred M)` を「外側 1 段の scb 文脈で末尾単項を落とした形」としか表せないため、
条件 (II)/(IV) の**二段ネスト零化**（`D_{j₁} 0` を `D_{j'}` の内側で潰し、その後
`D_{j'} 0` を `D_{v₀}` の内側で潰す）は捕捉できない（flat 文字列の照合が破れることを
確認済み）。これが原文 6018–6058 の hard core である。従って本ファイルは II/IV を
`TransPredScbInsert_pg` へは還元せず、**結論そのもの**を名前付き残差
`PredOper0_nestedCond_residual_psi`（下記）へ封じ込める。

さらに `Trans (Pred M) = 0` の退化枝（`t₁ = 0`。`Trans M = D_0(D_{j₁} 0)`）も
単一挿入形では表せないため、別の名前付き残差 `PredOper0_t1zero_residual_psi` に
分離する。**全体還元** `p_8_7_Pred_oper0_of_residuals_psi` は、条件網羅
（`condII_or_condIV`, `8.2-subexpr-adm0-ctx`）と本ファイルの枝 (I)/(III)/(V) 討伐を
合成し、一般形 `PredOper0_pg` をこの 2 残差だけへ還元する。

## 依存（ビルド済みのみ import）

`8.7-Pred-oper0-general`（`TransPredScbInsert_pg`, `p_8_7_Pred_oper0_of_scbInsert_pg`）、
`8.3-condII-masterCF`（`Trans_c1_c2_decomp`；推移的に `7.3-Trans-welldefined` の
`Trans_mem_T_B`/`transC2Core_properties`/`replaceScb_spec` ほか）、
`7.3-c1-c2-order`（`transC1_single_principal`/`principal_reconstruct`）。

## private helper suffix: `_psi`
-/

namespace PSS

/-! ## 1. 枝 (I)/(III)/(V)：構造残差を master key から討伐 -/

/-- 主枝（`monoT`・`Trans (Pred M) ≠ 0`）かつ条件 (I)∨(III)∨(V) のとき、`Trans M` は
`Trans (Pred M)` の共有 scb 文脈の中で末尾単項 `D_w 0` を挿入しただけの形をもつ
＝構造残差 `TransPredScbInsert_pg M` が成り立つ。 -/
theorem transPredScbInsert_condIIIV_psi (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hlen : 1 < Lng M)
    (ht₁ : Trans (Pred M) ≠ BZero)
    (hcls : (transCondI M || transCondIII M || transCondV M) = true) :
    TransPredScbInsert_pg M := by
  -- master key：共有 scb 文脈 (s, b)
  obtain ⟨s, b, dPM, dWM⟩ := Trans_c1_c2_decomp M hR hmono hlen ht₁
  -- `c₁` は単項 principal `D_{v₀} t₂`、`t₂ ∈ T_B`
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have c1TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have hj1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hc1len := transC1_single_principal M hR hmono hj1pos (by exact ht₁)
  have hc1eqTV : transC1 M = Dprin (transV M) (transT2 M) := by
    simpa [transV, transT2] using principal_reconstruct hc1len
  have hsplit : transV M ≠ ⊤ ∧ transT2 M ∈ T_B := by
    have h := c1TB
    rw [hc1eqTV] at h
    change dfree_BT (.trm [.db (transV M) (transT2 M)]) = true at h
    simp only [dfree_BT, dfree_BPList, dfree_BP, Bool.and_eq_true, bne_iff_ne] at h
    exact ⟨h.1.1, h.1.2⟩
  obtain ⟨v0, hv0⟩ := ENat.ne_top_iff_exists.mp hsplit.1
  have ht2TB : transT2 M ∈ T_B := hsplit.2
  have c1E : transC1 M = Dprin (v0 : ℕ∞) (transT2 M) := by rw [hc1eqTV, ← hv0]
  -- `c₂` の形（条件 (I)∨(III)∨(V)）
  have c2E : transC2 M =
      Dprin (v0 : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)) := by
    rw [transC2, transC2Core]
    simp only [hcls, if_true]
    rw [hv0]
  -- 組み立て
  refine ⟨s, b, transT2 M, v0, entry M 1 (lastIdx M), ?_, ?_, ?_, ?_⟩
  · exact Trans_mem_T_B M hR
  · exact ht2TB
  · rw [← c2E]; exact dWM
  · rw [← c1E]; exact dPM.1

/-! ## 2. 端から端まで：枝 (I)/(III)/(V) の一般形結論 -/

/-- 枝 (I)/(III)/(V) の host で `∃ k, Trans(M)[0]^k = Trans (Pred M)` を
（構造残差 → 既存ネスト零化 `p_8_7_Pred_oper0_of_scbInsert_pg`）で導く。 -/
theorem p_8_7_Pred_oper0_condIIIV_psi (M : PS)
    (hR : RTPS M) (hmono : monoT M = true) (hlen : 1 < Lng M)
    (ht₁ : Trans (Pred M) ≠ BZero)
    (hcls : (transCondI M || transCondIII M || transCondV M) = true) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M) :=
  p_8_7_Pred_oper0_of_scbInsert_pg M
    (transPredScbInsert_condIIIV_psi M hR hmono hlen ht₁ hcls)

/-! ## 3. 枝 (II)/(IV) と `t₁ = 0` を名前付き残差へ封じ込め、全体を還元 -/

/-- 枝 (II)/(IV) の残差（結論そのもの）。単一挿入形 `TransPredScbInsert_pg` では
表せない二段ネスト零化。原文 6018–6058 の hard core（Isabelle も `sorry`）。 -/
def PredOper0_nestedCond_residual_psi : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M →
    Trans (Pred M) ≠ BZero →
    (transCondII M = true ∨ transCondIV M = true) →
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M)

/-- 退化枝 `t₁ = Trans (Pred M) = 0`（`Trans M = D_0(D_{j₁} 0)`）の残差。 -/
def PredOper0_t1zero_residual_psi : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M →
    Trans (Pred M) = BZero →
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M)

/-- **全体還元**：一般形 `PredOper0_pg`（`8.7-Pred-oper0-general`）を、枝 (II)/(IV) の
残差 `PredOper0_nestedCond_residual_psi` と退化枝 `PredOper0_t1zero_residual_psi`
だけへ還元する。枝 (I)/(III)/(V) は本ファイルの `p_8_7_Pred_oper0_condIIIV_psi` で
討伐済み。条件網羅は `condII_or_condIV` を再構成して得る。 -/
theorem p_8_7_Pred_oper0_of_residuals_psi
    (Hnest : PredOper0_nestedCond_residual_psi)
    (Hzero : PredOper0_t1zero_residual_psi) :
    PredOper0_pg := by
  intro M h1 _h2 h3 h4 h5 _h6
  have hL : 1 < Lng M := by omega
  by_cases ht₁ : Trans (Pred M) = BZero
  · exact Hzero M h1 h3 hL ht₁
  · by_cases hA : (transCondI M = true ∨ transCondIII M = true ∨ transCondV M = true)
    · have hcls : (transCondI M || transCondIII M || transCondV M) = true := by
        rcases hA with h | h | h <;> simp [h]
      exact p_8_7_Pred_oper0_condIIIV_psi M h1 h3 hL ht₁ hcls
    · rcases condII_or_condIV M h1 h3 hL hA h5 with hII | hIV
      · exact Hnest M h1 h3 hL ht₁ (Or.inl hII)
      · exact Hnest M h1 h3 hL ht₁ (Or.inr hIV)

#print axioms transPredScbInsert_condIIIV_psi
#print axioms p_8_7_Pred_oper0_condIIIV_psi
#print axioms p_8_7_Pred_oper0_of_residuals_psi

end PSS
