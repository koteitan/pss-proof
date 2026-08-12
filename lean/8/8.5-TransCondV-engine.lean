import «5».«5.3-pred-is-oper1»
import «6».«6.7-standard-prefix»
import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «Buchholz-1986».«Buchholz-1986-3.2-descent»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Pred-Trans-descend»
import «8».«8.7-fseq-descend»

/-!
# §8.5 条件(V) — 降下エンジン

- 原文: `tmp/content.md` §8.5（命題「条件(V) の下での `Trans` と基本列の交換関係」）。
  本ファイルの担当は**降下エンジン**（交換則 `exch` ＋ `Trans M ∈ OT_B` から
  `Trans (M[n]) < Trans M` を出す還元）ただ 1 本。交換則そのもの／降下の結論形は
  ビルド済みの «8».«8.5-Trans-fseq-condV»（`Trans_oper_exchange_condV` /
  `Trans_oper_descend_condV`）の担当であり、本ファイルは名前・主張とも重複しない。

- Isabelle: `m_8_5_TransCondV_oper_descend_engine` (isabelle/layerB/pss_wip.thy:37496)
  — 本ファイルの `TransCondV_oper_descend_engine`（**無仮定で完全証明**）。
  その `n = 1` 脚は Isabelle では inline（`m_8_4_oper1_eq_Pred` ＋
  `m_7_3_Pred_Trans_descend`）だが、条件(II) 版 (`m_8_3_TransCondII_oper1_descend`,
  同 :26336) に倣って `TransCondV_oper1_descend` として切り出した。

- 構造（Isabelle と 1:1）: `Lng M - 1 > 1` ⟹ `Lng M ≠ 1` ⟹ `¬ zeroT M` ⟹
  `Trans M ≠ 0_B`（`m_7_3_Trans_zeroT`）。`n = 1` 脚は `M[1] = Pred M` による純
  `Pred` 降下（**条件(V) は不要**＝Isabelle の注記どおり）。`n > 1` 脚は交換則が
  与える `operB` 一歩を [Buc1] Lemma 3.2(a) で狭義降下させる。
  条件(II) 版との**唯一の差**は、条件(V) が**等式ではなく不等式レジーム**である点:
  `exch` は `Trans (M[n]) ≤_B operB (Trans M) (numBT k)` しか与えないので、
  `leBT` を `lessBT ∨ =` に分解して `lessBT_linear_trans` で繋ぐ
  （＝ Isabelle の `by (metis lessBT_trans)` の段。条件(VI) 版
  `m_8_6_TransCondVI_oper_descend_engine` と同じ処理）。

- 依存（ビルド済みのみ import）: `5.3-pred-is-oper1`（`pred_is_oper1`
  ＝ `m_8_4_oper1_eq_Pred`）、`6.7-standard-prefix`（`STPS_TPS` ＝ `ST_PS_T_PS`）、
  `Buchholz-1986-2.1-order`（`lessBT_linear_trans` ＝ `lessBT_trans`）、
  `Buchholz-1986-3.2-descent`（`buchholz_fseq_lt` ＝ `m_buc1_3_2a_fseq_lt`
  ＝ [Buc1] Lemma 3.2(a)）、`7.3-Trans-preserves-zeroT`（`Trans_preserves_zeroT`
  ＝ `m_7_3_Trans_zeroT`）、`7.3-Pred-Trans-descend`（`Pred_Trans_descend`
  ＝ `m_7_3_Pred_Trans_descend`）、`8.7-fseq-descend`（drop-in 先の `Prop`）。

- 訂正: 該当なし（A 番号なし）。Isabelle 側の注記のとおり本補題は
  「proven facts ＋ 正当な外部 [Buc1] 3.2(a)」のみを引用し、`p_8_5_*` への
  循環参照はない。

- 状態: ✅ **GREEN・無仮定**（`FseqDesc_m_8_5_TransCondV_oper_descend_engine` を
  **仮定なしで**充足）。sorry 0、axioms = propext/Classical.choice/Quot.sound。

- ✅ **空虚性の所見（`python/audit_85_condV_engine.py`）— 条件(II) とは対照的に
  条件(V) は空虚でない**。条件(II) 版のヘッダ（«8».«8.3-TransCondII-engine»）は
  「条件(II) は `ST_PS` 上に 1 例も存在しない（32056 本中 0 本）＝エンジンは
  健全だが空虚の疑い」と報告しているので、移植前に条件(V) を同じ pool idiom で
  監査した。結果: 標準形 2527 本（`diagSeq u<4, v<u+6` を `oper n∈[1..4]` で
  6 ラウンド閉包、`Lng ≤ 12`、成分最大 14）のうち **条件(V) ホストは 87 本**
  （`monoT` ＋ `1 < Lng M - 1` 込み。最小例 `(0,0)(1,1)(1,1)`）。その 87 本上で
  - `Trans M ∈ OT_B`（`hOT` 前提）… 87/87 成立、
  - `TransCondV_oper1_descend`（`n = 1` 脚）… 87/87 成立、
  - `hexch` 前提の充足可能性（`∃ k < 6. Trans (M[n]) ≤_B operB (Trans M) (numBT k)`）
    … 172/172 成立（＝**前提が偽の空約束ではない**）、
  - エンジンの結論 `Trans (M[n]) <_B Trans M` … 259/259 成立
  で**反例 0**。`PSS_AUDIT_FULL=1` で full scale（`diagSeq u<5, v<u+8`, 8 ラウンド,
  `Lng ≤ 16`）に切り替わる。なお監査は移植の健全性の根拠ではない
  （証明は空虚性に依存しない）が、本エンジンが下流で**実際に発火する**ことの確認。

## Isabelle との仮定の対応

Isabelle の `MP : M ∈ PT_PS` はビルド済み 8.7 側の `Prop` と同じく `monoT M = true`
で表す。Isabelle の `MR : M ∈ RT_PS`（`m_7_3_Trans_zeroT` 用）は Lean の
`Trans_preserves_zeroT` が `TPS` で足りるため不要（`STPS_TPS` から直接落ちる）。
`hmono` / `hcond` は原文の主張形を写すためだけに置く（Isabelle 版と同じく、
この還元自身は使わない）。
-/

namespace PSS

/-! ## `Trans M ≠ 0_B`（Isabelle の `notz`/`Tne` 段）

`j₁ = Lng M - 1 > 1` から `Lng M ≠ 1`、よって `¬ zeroT M`。`m_7_3_Trans_zeroT`
（Lean `Trans_preserves_zeroT`）の対偶で `Trans M ≠ 0_B`。 -/

private theorem Trans_ne_BZero_of_len_c5e
    (M : PS) (hT : TPS M) (hj₁ : 1 < Lng M - 1) : Trans M ≠ BZero := by
  have hzero : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; omega
  intro h
  have hz := (Trans_preserves_zeroT M hT).mpr h
  rw [hz] at hzero
  exact Bool.noConfusion hzero

/-! ## 条件(V) の `n = 1` 脚

`M[1] = Pred M` なので、降下は §7.3 の `Pred` 降下そのもの。
条件(V)/`monoT` は原文の主張形を写すためだけに置く（この脚では使わない）。 -/

/-- 条件(V) 降下エンジンの `n = 1` 脚（Isabelle では
`m_8_5_TransCondV_oper_descend_engine` の `case True` に inline、
条件(II) 版 `m_8_3_TransCondII_oper1_descend` (pss_wip.thy:26336) と同型）。 -/
theorem TransCondV_oper1_descend
    (M : PS) (hST : STPS M) (_hmono : monoT M = true)
    (hj₁ : 1 < Lng M - 1) (_hcond : transCondV M = true) :
    lessBT (Trans (oper M 1)) (Trans M) = true := by
  have hT : TPS M := STPS_TPS M hST
  have hlen : 1 < Lng M := by omega
  rw [← pred_is_oper1 M hT hlen]
  exact Pred_Trans_descend M hT hlen

/-! ## 条件(V) 降下エンジン -/

/-- Isabelle `m_8_5_TransCondV_oper_descend_engine` (pss_wip.thy:37496)。

交換則 `hexch`（条件(V) は**不等式**レジーム: `≤_B` しか出ない）と
`Trans M ∈ OT_B` を与えれば、全ての `n > 0` で `Trans (M[n]) <_B Trans M`。 -/
theorem TransCondV_oper_descend_engine
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondV M = true) (hn : 0 < n)
    (hOT : Trans M ∈ OT_B)
    (hexch : 1 < n → ∃ k, leBT (Trans (oper M n)) (operB (Trans M) (numBT k)) = true) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hT : TPS M := STPS_TPS M hST
  have hTne : Trans M ≠ BZero := Trans_ne_BZero_of_len_c5e M hT hj₁
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · -- `n > 1`: Buchholz 側の基本列一歩は [Buc1] 3.2(a) で狭義降下。
    -- 条件(V) は不等式レジームなので `leBT` を分解して繋ぐ。
    obtain ⟨k, hk⟩ := hexch h1
    have hlt := buchholz_fseq_lt (Trans M) k hOT hTne
    simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with hk | hk
    · exact lessBT_linear_trans _ _ _ hk hlt
    · rw [hk]; exact hlt
  · -- `n = 1`: `Pred` 降下
    have hn1 : n = 1 := by omega
    subst hn1
    exact TransCondV_oper1_descend M hST hmono hj₁ hcond

/-! ## `FseqDesc_m_8_5_TransCondV_oper_descend_engine` の drop-in

ビルド済み «8».«8.7-fseq-descend» の `Prop` を**無仮定で**充足する
（house pattern: `Prop` を型として与え、elaborator に一致を証明させる）。 -/

theorem TransCondV_oper_descend_engine_fseqdesc_form :
    FseqDesc_m_8_5_TransCondV_oper_descend_engine :=
  fun M n hST hmono hj₁ hcond hn hOT hexch =>
    TransCondV_oper_descend_engine M n hST hmono hj₁ hcond hn hOT hexch

#print axioms TransCondV_oper1_descend
#print axioms TransCondV_oper_descend_engine
#print axioms TransCondV_oper_descend_engine_fseqdesc_form

end PSS
