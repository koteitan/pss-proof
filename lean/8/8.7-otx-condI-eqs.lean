import «8».«8.1-Trans-fseq-condI»
import «8».«8.7-Trans-preserves-OT»

/-!
# §8.7 OT 柱 — 条件 (I) 交換等式 2 本の**無条件**クローズ

- 原文: `tmp/content.md` 2827（§8.1）/ 6122（§8.7）。**本ファイルは新しい記事命題を
  主張しない**。`«8».«8.7-Trans-preserves-OT»`（同 :81–157）が露出した 12 本の
  名前付き `Prop`（`OTdisp_*`）のうち条件 (I) 系 2 本を、**仮定ゼロ**で閉じる。
  訂正: なし（A 番号の該当なし）。

## 閉じた `Prop`（2 本、いずれも無条件）

| `OTdisp_*` | Isabelle | 行 |
|---|---|---|
| `OTdisp_Trans_fseq_condI_n1` | `m_8_1_Trans_fseq_condI_n1` | `layerB/pss_wip.thy`:33271 |
| `OTdisp_condI_j1eq1_eq` | `otx_condI_j1eq1_eq` | `layerB/pss_wip.thy`:85516 |

いずれも Isabelle 側は**無仮定**（`RT_PS`/`PT_PS`/長さ/条件(I) のみ）で証明済み。
仮定束は Lean の `Prop` と**文字単位で一致**することを確認済み:

* `m_8_1_Trans_fseq_condI_n1`: `MR: M ∈ RT_PS`, `MP: M ∈ PT_PS`,
  `j1: Lng M - 1 > 1`, `condI: transCondI M` ＝ Lean の
  `RTPS M → monoT M = true → 1 < Lng M - 1 → transCondI M = true`。
* `otx_condI_j1eq1_eq`: `MR`, `MP`, `L2: Lng M = 2`, `cond: transCondI M`,
  `n2: 2 ≤ n` ＝ Lean の `RTPS M → monoT M = true → Lng M = 2 →
  transCondI M = true → 2 ≤ n`。`if` の分岐（`entry M 1 0 = 0` で `n-2`、
  それ以外で `n-1`）も Isabelle の `u = 0` / `u ≠ 0` 場合分けと一致。

## `Trans_fseq_condI_n1`（`n = 1` 基底）— private の再導出

`8.1-Trans-fseq-condI`:303 に**無仮定の Lean twin `Trans_fseq_condI_n1_ci` が既に
存在する**が `private` のため参照できない（`8.7-Trans-preserves-OT-props`:89 の
申し送り事項）。そこで本ファイルは同 :217–303 の private 連鎖
（`condI_transJm1_eq_ci` / `shared_scb_condI_ci` / `Trans_ne_zero_ci` /
`domTagBP_succ_body_ci` / `operB_numBT0_Pred_ci`）を `_oci` 接尾辞で**私的に再導出**
する。数学は同一（Isabelle `m_8_1_operB_numBT0_Pred` (:33088) →
`m_8_1_Trans_fseq_condI_n1` (:33271)）。これにより
`8.7-Trans-preserves-OT-props`:138 の 3 本 modulo 版
（`CondI_masterCF` ＋ `FseqDesc_operI_j0zero_trans_mult` ＋
`FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1`）は**不要になる**。

## `condI_j1eq1_eq`（`Lng M = 2` 境界）— 親が公開した 3 本で開通

`1 < Lng M - 1` が偽なので `condI_exchange1` は適用不可。親が
`oper_len2_fd`（`8.7-fseq-descend`:362）/ `parent_one_zero_fd`（同 :249）/
`operB_succ_body_ci`（`8.1-Trans-fseq-condI`:204）を公開したので、Isabelle
`otx_condI_j1eq1_eq` の算術がそのまま通る:

* 条件(I) ＋ `Lng M = 2` で `entry M 1 1 = 0` → `idx1 M 1 = 0` → `oper` の増分は
  `d₀ = d₁ = 0` → `oper_len2_fd` で **`M[n] = ((u,u))ⁿ`**（`u = entry M 1 0`、
  `RTPS_mono_head_eq` で `entry M 0 0 = u`）;
* `Trans (M[n])` ＝ `const00_Trans`（`8.7-const00-Trans`:195、Isabelle
  `m_8_7_const00_Trans`）で `u = 0` なら `(D_u 0) ×_B (n-1)`、そうでなければ
  `(D_u 0) ×_B n`;
* `Trans M` ＝ `two_column_Trans`（`7.3-two-column`:482）で `D_u (D_0 0)`、
  その基本列は `operB_succ_body_ci` の `t₂ := 0_B` 特殊化（Isabelle
  `m_8_1_operB_condI_c2_value`）で `operB (Trans M) (numBT k) = (D_u 0) ×_B (k+1)`。

`2 ≤ n` より `(n-2)+1 = n-1` / `(n-1)+1 = n` で両辺一致。

## 未閉鎖: `OTdisp_condI_j0z_eq`（本ファイルには入れない）

Isabelle `otx_condI_j0z_eq` (:85292) は `n = 1` 脚（＝上記）＋ `n ≥ 2` 脚
＝ `m_8_1_Trans_replicate_pred_condI` (:37059) で、後者は
**`operI_j0zero_trans_mult` (:36977)** と
**`m_8_2_subexpr_component_Pred_Adm0_clause1` (:19436)** を呼ぶ。この 2 本は
Lean では `FseqDesc_operI_j0zero_trans_mult` /
`FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1`（`8.7-fseq-descend`:109/117）
＝ **`TerminationResidual` 自身の別の leaf**（`8.7-termination`:245/247）である。
したがって `OTdisp_condI_j0z_eq` を無条件化するには**別 leaf を 2 本先に閉じる
必要**があり、本 wave の範囲外。既存の 3 本 modulo 配線
（`8.7-Trans-preserves-OT-props`:150）が現状の最良。

- 依存（ビルド済みのみ import）: `8.1-Trans-fseq-condI`
  （`operB_succ_body_ci`、および推移的に `7.4-Trans-Mark-Pred` の
  `Trans_Mark_Pred`、`7.4-Mark-Trans-repr` の `Mark_transJm1_eq_transC2`、
  `7.3-c1-c2-order` の `transC1_single_principal`/`principal_reconstruct`、
  `7.2-scb-fseq` の `operB_scb_spine`、`8.7-fseq-descend` の
  `oper_len2_fd`/`parent_one_zero_fd`、`8.7-const00-Trans` の `const00_Trans`、
  `7.3-two-column` の `two_column_Trans`、`6.6-reduced-leftend` の
  `RTPS_mono_head_eq`、`6.6-P-condAB` の `mono_hasParent_row0`、
  `5.3-pred-is-oper1` の `pred_is_oper1`）、`8.7-Trans-preserves-OT`
  （`OTdisp_*` の定義）。
  **`8.7-Trans-preserves-OT-props` は import しない**（配線は素集合）。
- 状態: ✅ GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  2 本とも**無条件**。
-/

namespace PSS

/-! ## 私的補題（`_oci` 接尾辞） -/

/-- 行 0 に親があれば末尾成分は正。`nextrel0` の `entry M 0 j₀ < entry M 0 j₁` 脚。 -/
private theorem entry0_pos_of_hasParent_oci (M : PS) (j : ℕ)
    (hp : hasParent M 0 j = true) : 0 < entry M 0 j := by
  have hn := hasParent_next_fseq M 0 j hp
  have hh : nextrel0 M (parent M 0 j) j = true := by simpa [nextR] using hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  omega

/-- 条件(I) は `j₀` の許容性を含むので `j₋₁ = Adm_M(j₀) = j₀`。
（`8.1-Trans-fseq-condI`:217 `condI_transJm1_eq_ci` の複製。） -/
private theorem condI_transJm1_eq_oci (M : PS) (hI : transCondI M = true) :
    transJm1 M = transJ0 M := by
  simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
  simp [transJm1, transJ0, Adm, hI.2]

/-- 条件(I) の共有 scb 分解（`8.1-Trans-fseq-condI`:224 `shared_scb_condI_ci` の複製）。
基点 `j₋₁ = j₀` なので §7.4 の `Trans_Mark_Pred` が直接効く。 -/
private theorem shared_scb_condI_oci (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (hI : transCondI M = true) :
    ∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (Mark M (transJm1 M))) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hjm : transJm1 M = transJ0 M := condI_transJm1_eq_oci M hI
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hadm : adm M (transJ0 M) = true := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [transJ0] using hI.2
  have hle : leR M 0 (transJ0 M) (Lng M - 1) = true := by
    have hnx : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
      simpa [transJ0, lastParent, lastIdx] using
        hasParent_next_fseq M 0 (Lng M - 1) hp
    exact nextR0_leR M _ _ hnx
  have hmk : Marked M (transJm1 M) := by
    rw [hjm]; exact ⟨hM, hadm, hle⟩
  obtain ⟨⟨s, b⟩, ⟨hd1, hd2⟩, _⟩ :=
    Trans_Mark_Pred M (transJm1 M) hmk hR (by omega)
  exact ⟨s, b, hd1, hd2⟩

/-- `Lng M > 1` なら `Trans M ≠ 0_B`（`8.1-Trans-fseq-condI`:253 の複製）。 -/
private theorem Trans_ne_zero_oci (M : PS) (hM : TPS M) (hlen : 1 < Lng M) :
    Trans M ≠ BZero := by
  intro h0
  have hz : zeroT M = true := (Trans_preserves_zeroT M hM).mpr h0
  simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
  omega

/-- 末尾 principal が `domTagList` を決める（`8.1-Trans-fseq-condI`:172
`domTagList_snoc_ci` の複製。各ファイルが自前の接尾辞で持つ house 慣習）。 -/
private theorem domTagList_snoc_oci (ps : List BP) (p : BP) :
    domTagList (ps ++ [p]) = domTagBP p := by
  induction ps with
  | nil => simp [domTagList]
  | cons q qs ih =>
      cases qs with
      | nil => simp [domTagList]
      | cons r rs => simpa [domTagList] using ih

/-- `D_v(t₂ +_B D₀0)` の domain tag は `naturals`（`8.1-Trans-fseq-condI`:211 の複製）。 -/
private theorem domTagBP_succ_body_oci (t₂ : BT) (v : ℕ∞) :
    domTagBP (.db v (addBT t₂ (Dprin 0 BZero))) = .naturals := by
  rcases t₂ with ⟨ps₂⟩
  simp [addBT, Dprin, BZero, domTagBP, domTag, domTagList_snoc_oci]

/-- Isabelle `m_8_1_operB_numBT0_Pred` (`layerB/pss_wip.thy`:33088):
条件(I) の下で `Trans(M)[0] = Trans(Pred M)`。
（`8.1-Trans-fseq-condI`:261 `operB_numBT0_Pred_ci` の複製。） -/
private theorem operB_numBT0_Pred_oci (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) (hI : transCondI M = true) :
    operB (Trans M) (numBT 0) = Trans (Pred M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hj1 : 0 < transJ1 M := by simp [transJ1, lastIdx]; omega
  have hT1 : transT1 M ≠ BZero := by simpa [transT1] using ht₁
  have he1z : entry M 1 (lastIdx M) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI; exact hI.1
  obtain ⟨s, b, hd1, hd2⟩ := shared_scb_condI_oci M hR hmono hlen hI
  rw [Mark_transJm1_eq_transC2 M hR hmono hlen ht₁] at hd2
  have hc1 : transC1 M = Dprin (transV M) (transT2 M) :=
    principal_reconstruct (transC1_single_principal M hR hmono hj1 hT1)
  have hc2 : transC2 M =
      Dprin (transV M) (addBT (transT2 M) (Dprin 0 BZero)) := by
    simp [transC2, transC2Core, hI, he1z]
  set v := transV M with hv
  set t₂ := transT2 M with ht₂
  let p : BP := .db v (addBT t₂ (Dprin 0 BZero))
  let p' : BP := .db v t₂
  have hocc : flatBT (Trans M) = s ++ flatBP p ++ b := by
    have := hd2.1; rw [hc2] at this; simpa [p, Dprin, flatBT] using this
  have hdfp : dfree_BP p = true := by
    have hipt := hd2.2.1 (Trans_ne_zero_oci M hM hlen)
    rw [hc2] at hipt
    obtain ⟨q, hq, hqf⟩ := hipt
    have hqp : q = p :=
      flatBP_injective (p := q) (q := p)
        (by simpa [p, Dprin, flatBT] using hqf.symm)
    rwa [hqp] at hq
  have hop : operB (.trm [p]) (numBT 0) = .trm [p'] := by
    have h := operB_succ_body_ci t₂ v 0
    simpa [p, p', Dprin, multBT, addBT, BZero] using h
  obtain ⟨_, hflat⟩ :=
    operB_scb_spine hocc hd2.2.2 hdfp (domTagBP_succ_body_oci t₂ v) hop
  apply flatBT_injective
  rw [hflat]
  have := hd1.1
  rw [hc1] at this
  simpa [p', Dprin, flatBT] using this.symm

/-! ## (1) `OTdisp_Trans_fseq_condI_n1` — 無条件

Isabelle `m_8_1_Trans_fseq_condI_n1` (`layerB/pss_wip.thy`:33271)。 -/

theorem OTdisp_Trans_fseq_condI_n1_holds : OTdisp_Trans_fseq_condI_n1 := by
  intro M hR hmono hj1 hI
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have ht₁ : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz : zeroT (Pred M) = true :=
      (Trans_preserves_zeroT (Pred M) (RTPS_TPS _ (RTPS_Pred M hR))).mpr h0
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    rw [length_Pred M hlen] at hz
    omega
  rw [← pred_is_oper1 M hM hlen]
  exact (operB_numBT0_Pred_oci M hR hmono hlen ht₁ hI).symm

#print axioms OTdisp_Trans_fseq_condI_n1_holds

/-! ## (2) `OTdisp_condI_j1eq1_eq` — 無条件

Isabelle `otx_condI_j1eq1_eq` (`layerB/pss_wip.thy`:85516)。 -/

theorem OTdisp_condI_j1eq1_eq_holds : OTdisp_condI_j1eq1_eq := by
  intro M n hR hmono hL2 hI hn
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hj1 : Lng M - 1 = 1 := by omega
  -- 条件(I) の第 1 脚
  have e1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq, lastIdx] at hI
    exact hI.1
  have he11z : entry M 1 1 = 0 := by rw [hj1] at e1z; exact e1z
  -- 行 0 の親（`monoT`）と末尾非零
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have he01pos : 0 < entry M 0 1 := by
    have := entry0_pos_of_hasParent_oci M (Lng M - 1) hp0
    rwa [hj1] at this
  have hnz1 : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by omega
  have hi1 : idx1 M 1 = 0 := by simp [idx1, he11z]
  have hp1 : hasParent M (idx1 M 1) 1 = true := by
    rw [hi1]; rw [hj1] at hp0; exact hp0
  have hdiag : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
  -- `M[n] = ((u,u))ⁿ`
  have hop : oper M n = List.replicate n (entry M 1 0, entry M 1 0) := by
    rw [oper_len2_fd M hL2 hnz1 hp1 0 0 (by simp [hi1]) (by simp [hi1])]
    rw [hdiag]
    simp [List.map_const']
  -- Buchholz 側: `Trans M = D_u (D_0 0)`、基本列は `(D_u 0) ×_B (k+1)`
  have hTM : Trans M = Dprin (entry M 1 0 : ℕ∞) (Dprin 0 BZero) := by
    rw [two_column_Trans M hR hmono hL2, he11z]
    rfl
  have hRHS : ∀ k : ℕ, operB (Trans M) (numBT k) =
      multBT (Dprin (entry M 1 0 : ℕ∞) BZero) (k + 1) := by
    intro k
    have h := operB_succ_body_ci BZero (entry M 1 0 : ℕ∞) k
    rw [hTM]
    simpa [addBT, BZero] using h
  -- `n = m + 1`、`1 ≤ m`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  rw [hop, const00_Trans (entry M 1 0) m]
  by_cases hu : entry M 1 0 = 0
  · rw [if_pos hu, if_pos hu, hRHS, show m + 1 - 2 + 1 = m from by omega]
  · rw [if_neg hu, if_neg hu, hRHS, show m + 1 - 1 + 1 = m + 1 from by omega]

#print axioms OTdisp_condI_j1eq1_eq_holds

end PSS
