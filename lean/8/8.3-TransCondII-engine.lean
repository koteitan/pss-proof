import «5».«5.3-pred-is-oper1»
import «6».«6.7-standard-prefix»
import «6».«6.7-standard-reduced»
import «7».«7.1-buchholz-fseq-lt»
import «7».«7.2-scb-fseq»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Pred-Trans-descend»
import «8».«8.7-fseq-descend»

/-!
# §8.3 条件(II) — 交換則 `exchII` と条件(II)降下エンジン

- 原文: `tmp/content.md` 3958（§8.3 命題（条件(II)の下での `Trans` と基本列の交換関係））。
  逐語形は `p_8_3_TransCondII_oper_descend` (isabelle/pss_paper.thy:1863)。
  **ツリー項目 `8.3-Trans-fseq-condII` は本ファイルの担当ではない**: それは降下
  dispatcher の系であり、ビルド済みの «8».«8.7-fseq-descend» が既に
  `p_8_3_TransCondII_oper_descend` を出している。本ファイルの担当は
  **交換則そのもの**と、**それを使う降下エンジン**の 2 本。

- Isabelle:
  - `m_8_3_TransCondII_oper_descend_engine` (isabelle/layerB/pss_wip.thy:28563)
    — 本ファイルの `TransCondII_oper_descend_engine`（**無仮定で完全証明**）。
    その `n = 1` 脚 `m_8_3_TransCondII_oper1_descend` (同 :26336) も移植
    （`TransCondII_oper1_descend`）。
  - `c2sx_exchange_ex_condII_of_tailval` (同 :87577) — exchII の Isabelle 供給元。
    その本体は `c2ex_exch_of_lhs_closed_ex` (同 :70717)
    ＋ `operB_marked_scb_value` (同 :37100) ＋ `c2sx_condII_masterCF` (同 :87430)。
    前二者は本ファイルで移植済（`exch_of_lhs_closed_ex_c2` /
    `operB_marked_scb_value_c2`）。**未移植の残差は `c2sx_condII_masterCF` ただ 1 本**で、
    名前付き `Prop` `CondII_masterCF` として露出した（green-modulo）。
    Isabelle 側では `TV : c2sx_tailval M` は `y3j_condII_tailval`
    (isabelle/layerC/pss_scratch.thy:17079) が**無条件に**落とすので、
    `CondII_masterCF` は Isabelle では定理＝空虚な仮定ではない。

- 訂正: **A36 は取り下げ済み**（`corrections-old.md:138`）。`c2ex_exch_of_lhs_closed_ex`
  の Isabelle 注釈は「A36-CORRECTED EXISTENTIAL form」と称するが、A36 の取り下げ理由は
  「原文はそもそも \(m_n := n-1\) または \(n-2\) と著者自身が場合分けを明示しており、
  存在量化は著者が既に行っていること」＝**存在形が正しい**という確認である。よって
  存在形 (`∃ k`) の移植は原文に忠実であり、取り下げは本ファイルの主張を損なわない。
  （`FseqDesc_exchII` 自身もビルド済み 8.7 側で `∃ k` 形で述べられている。）

- 依存（ビルド済みのみ import）: `5.3-pred-is-oper1`（`pred_is_oper1`
  ＝ `m_8_4_oper1_eq_Pred`）、`6.7-standard-prefix`（`STPS_TPS`）、
  `6.7-standard-reduced`（`STPS_RTPS` ＝ `m_6_7_ST_PS_subseteq_RT_PS`）、
  `7.1-buchholz-fseq-lt`（`buchholz_fseq_lt` ＝ `m_buc1_3_2a_fseq_lt`
  ＝ [Buc1] Lemma 3.2(a)）、`7.2-scb-fseq`（`scb_fseq_decomp`
  ＝ `m_7_2_scb_fseq_scb`）、`7.3-Trans-welldefined`（`unflatBT_flat`,
  `Trans_mem_T_B`）、`7.3-Trans-preserves-zeroT`（`Trans_preserves_zeroT`
  ＝ `m_7_3_Trans_zeroT`）、`7.3-Pred-Trans-descend`（`Pred_Trans_descend`
  ＝ `m_7_3_Pred_Trans_descend`）、`8.7-fseq-descend`（`FseqDesc_*` の drop-in 用）。

- 状態:
  - `TransCondII_oper_descend_engine` … ✅ **GREEN・無仮定**
    （`FseqDesc_m_8_3_TransCondII_oper_descend_engine` を充足）。
  - `exchII_of_masterCF` … 🤖 GREEN-MODULO（残差 `CondII_masterCF` 1 本のみ）。
    `FseqDesc_exchII` を `CondII_masterCF` から充足する。
  - sorry 0、axioms = propext/Classical.choice/Quot.sound。

- 🚨 **空虚性の所見（`python/audit_83_condII_engine.py`）**: 条件(II) は
  `ST_PS`（＝対角列を基本列で閉じた最小述語 = Lean `PSS/Standard.lean:16`）
  **上に 1 例も見つからない**。標準形 **32056 本**（`diagSeq u<5, v<u+8` を
  `oper n∈[1..5]` で 8 ラウンド閉包、`Lng ≤ 16`、**成分最大 19**＝memo の
  「成分 6〜9 に反例が潜む」警告の範囲を超える）を走査して、
  `entry M 1 (Lng M - 1) = 0` かつ row-0 親を持つものが **8298 本**、
  そのうち `¬adm(parent)` は **0 本**。すなわち標準形では
  `entry M 1 (Lng M -1) = 0` が `adm (parent M 0 (Lng M -1))` を**強制する**ように
  見え、条件(I) が条件(II) の想定ケースを全て吸収している。
  （`monoT` ホストは `mono_hasParent_row0`（6.6-P-condAB）により row-0 親を必ず
  持つので、この census に取りこぼしはない。）
  ビルド済み 8.7 側の独立監査 (`python/audit_8_7_trans_preserves_OT.py`) も
  標準形 18318 本で 0 件を報告し、`OTdisp_exchII` を "not covered by pool" として
  未検証扱いにしている（＝8.7 ヘッダの「全 16 本 #guard 検証済み＝空虚ではない」は
  exchII については**過大主張**）。
  したがって `FseqDesc_exchII` / 本ファイルの条件(II) 系は
  **`ST_PS` 上で空虚である可能性が高い**。ただし `RT_PS` 上には実例がある
  （`(0,0)(1,1)(2,2)(2,0)` は reduced・monoT・`1 < Lng-1`・条件(II)）。
  Isabelle の `c2sx_condII_masterCF` も仮定は `RT_PS` なので、
  `CondII_masterCF` 自体は**空虚な仮定ではない**: 監査は RT_PS 条件(II) ホスト
  （`Lng ≤ 4`・成分 < 6 の全数列挙で **1 本**＝`(0,0)(1,1)(2,2)(2,0)`、
  Isabelle 側の "canonical condition-(II) member" と一致）の上で
  Isabelle の witness (`s,b,va,v0,t3,t4`) を構成し、`masterCF` の結論
  （`scb_decomp` ＋ `lhs_ex`）・`operB_marked_scb_value_c2`・`exchII` の結論・
  エンジンの結論を**すべて反例 0 で確認**した（RT プールは 1 本と薄い点は留保）。
  これは**エンジンの証明の健全性には影響しない**（証明は空虚性に依存しない）が、
  `CondII_masterCF`（Isabelle 側 ~1500 行の `c2sx_*` 連鎖）を移植する
  **優先度の評価**には直結する。詳細は報告の `needs` を参照。
-/

namespace PSS

/-! ## 条件(II) の `n = 1` 脚（`m_8_3_TransCondII_oper1_descend`, wip:26336）

原文の基底段 (content.md 4038)。`M[1] = Pred M` なので、降下は §7.3 の
`Pred` 降下そのもの。条件(II)/`monoT` は原文の主張形を写すためだけに置く
（Isabelle 側の注記と同じく、この脚では使わない）。 -/

theorem TransCondII_oper1_descend
    (M : PS) (hST : STPS M) (_hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (_hcond : transCondII M = true) :
    lessBT (Trans (oper M 1)) (Trans M) = true := by
  have hT : TPS M := STPS_TPS M hST
  have hlen : 1 < Lng M := by omega
  rw [← pred_is_oper1 M hT hlen]
  exact Pred_Trans_descend M hT hlen

/-! ## 条件(II) 降下エンジン（`m_8_3_TransCondII_oper_descend_engine`, wip:28563）

Isabelle の構造をそのまま:
`Lng M - 1 > 1` ⟹ `Lng M ≠ 1` ⟹ `¬ zeroT M` ⟹ `Trans M ≠ 0_B`
（`m_7_3_Trans_zeroT`）。`n = 1` は上の `oper1` 脚、`n > 1` は交換則 `exch` が
与える `operB` 一歩を [Buc1] Lemma 3.2(a) で降下させる。 -/

/-- `1 < Lng M - 1` の下で `Trans M ≠ 0_B`（Isabelle の `notz`/`Tne` 段）。 -/
private theorem Trans_ne_BZero_of_len_c2
    (M : PS) (hT : TPS M) (hj1 : 1 < Lng M - 1) : Trans M ≠ BZero := by
  have hzero : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; omega
  intro h
  have hz := (Trans_preserves_zeroT M hT).mpr h
  rw [hz] at hzero
  exact Bool.noConfusion hzero

/-- Isabelle `m_8_3_TransCondII_oper_descend_engine` (pss_wip.thy:28563).
交換則 `hexch` と `Trans M ∈ OT_B` を与えれば、全ての `n > 0` で降下する。 -/
theorem TransCondII_oper_descend_engine
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn : 0 < n)
    (hOT : Trans M ∈ OT_B)
    (hexch : 1 < n → ∃ k, Trans (oper M n) = operB (Trans M) (numBT k)) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hT : TPS M := STPS_TPS M hST
  have hTne : Trans M ≠ BZero := Trans_ne_BZero_of_len_c2 M hT hj1
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · -- `m_n ≥ 0` 枝 (n > 1): Buchholz 側の基本列一歩は [Buc1] 3.2(a) で狭義降下
    obtain ⟨k, hk⟩ := hexch h1
    rw [hk]
    exact buchholz_fseq_lt (Trans M) k hOT hTne
  · -- `m_n = -1` 枝 (n = 1): `Pred` 降下
    have hn1 : n = 1 := by omega
    subst hn1
    exact TransCondII_oper1_descend M hST hmono hj1 hcond

/-! ## `FseqDesc_m_8_3_TransCondII_oper_descend_engine` の drop-in

ビルド済み «8».«8.7-fseq-descend» の `Prop` を**無仮定で**充足する。 -/

theorem TransCondII_oper_descend_engine_fseqdesc_form :
    FseqDesc_m_8_3_TransCondII_oper_descend_engine :=
  fun M n hST hmono hj1 hcond hn hOT hexch =>
    TransCondII_oper_descend_engine M n hST hmono hj1 hcond hn hOT hexch

/-! ## 交換則 exchII

Isabelle の供給連鎖:
`c2sx_condII_masterCF` (87430) → `c2ex_exch_of_lhs_closed_ex` (70717)
→ `c2sx_exchange_ex_condII_of_tailval` (87577)。
下の 2 本は後段の移植。残差は `CondII_masterCF` のみ。 -/

/-- Isabelle `operB_marked_scb_value` (pss_wip.thy:37100)。
条件(II) の marked principal `D_u (t₀ +B D_v (t₁ +B D_0 0))` で scb 分解された
`t` の基本列は、末尾の `D_0 0` を潰して内側 principal を `n+1` 回に畳む。
中身は `m_7_2_scb_fseq_scb`（Lean `scb_fseq_decomp`）を `unflatBT_flat` で読み戻すだけ。 -/
private theorem operB_marked_scb_value_c2 {t₀ t₁ t : BT} {u v n : ℕ} {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b) :
    operB t (numBT n)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b) := by
  have hd2 := scb_fseq_decomp (n := n) ht₀ ht₁ ht hd
  have hfe : flatBT (operB t (numBT n))
      = s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b := hd2.1
  calc operB t (numBT n)
      = unflatBT (flatBT (operB t (numBT n))) := (unflatBT_flat _).symm
    _ = _ := by rw [hfe]

/-- Isabelle `c2ex_exch_of_lhs_closed_ex` (pss_wip.thy:70717)。
閉形式 `lhs_ex`（数え上げ `c ≥ 1` は**存在量化**: A36 取り下げ理由のとおり、
原文自身が `m_n := n-1` / `n-2` と場合分けしている）から、Buchholz 側を
`operB_marked_scb_value_c2` で畳んで `Trans (M[n])` を単一の `operB` 一歩として読む。 -/
private theorem exch_of_lhs_closed_ex_c2
    {M : PS} {n u v : ℕ} {t₀ t₁ : BT} {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (htT : Trans M ∈ T_B)
    (hd : scb_decomp (Trans M) s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b)
    (hlhs : ∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b))
    (hn : 1 < n) :
    ∃ k, Trans (oper M n) = operB (Trans M) (numBT k) := by
  obtain ⟨c, hc1, hlc⟩ := hlhs n hn
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  refine ⟨k, ?_⟩
  rw [hlc, operB_marked_scb_value_c2 (n := k) ht₀ ht₁ htT hd]

/-! ## 露出した残差 `Prop`（green-modulo, Isabelle 名 1:1） -/

/-- Isabelle `c2sx_condII_masterCF` (pss_wip.thy:87430)。
Isabelle 側の仮定 `TV : c2sx_tailval M` は `y3j_condII_tailval`
(layerC/pss_scratch.thy:17079) が `ST_PS`/`PT_PS`/`1 < Lng M - 1`/条件(II) から
**無条件に**落とすので、ここでは `TV` を持たない形で露出する
（＝Isabelle では定理。空虚な仮定ではない）。

`ST_PS` ではなく `RT_PS` 上で述べるのは Isabelle の `masterCF` と同じ
（`MR : M ∈ RT_PS`）。`exchII` 側の `STPS` からは `STPS_RTPS` で落ちる。 -/
def CondII_masterCF : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    ∃ (s b : List Sym) (u v : ℕ) (t₀ t₁ : BT), t₀ ∈ T_B ∧ t₁ ∈ T_B ∧
      scb_decomp (Trans M) s
        (flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b ∧
      (∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
        = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
            (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b))

/-- Isabelle `c2sx_exchange_ex_condII_of_tailval` (pss_wip.thy:87577) の Lean 版。
`CondII_masterCF` から `FseqDesc_exchII` を出す。 -/
theorem exchII_of_masterCF (hCF : CondII_masterCF) : FseqDesc_exchII := by
  intro N m hST hmono hj1 hcond hm
  have hR : RTPS N := STPS_RTPS N hST
  have htT : Trans N ∈ T_B := Trans_mem_T_B N hR
  obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, hlhs⟩ := hCF N hR hmono hj1 hcond
  exact exch_of_lhs_closed_ex_c2 ht₀ ht₁ htT hd hlhs hm

#print axioms TransCondII_oper1_descend
#print axioms TransCondII_oper_descend_engine
#print axioms TransCondII_oper_descend_engine_fseqdesc_form
#print axioms CondII_masterCF
#print axioms exchII_of_masterCF

end PSS
