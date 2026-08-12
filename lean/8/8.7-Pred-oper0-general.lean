import «8».«8.6-trailing-principal-annihilable»
import «7».«7.2-scb-unique»
import PSS.Trans
import PSS.Red
import PSS.Mono

/-!
# §8.7 補題（`Pred` と `[0]` の関係）— **一般形の攻略**

- 原文: `tmp/content.md` article 6014「補題（\(\textrm{Pred}\)と\([0]\)の関係）」。
  （原文は \(M \in RT_{\textrm{PS}} \cap PT_{\textrm{B}}\) と書くが、`PT_B` は
  `PT_PS` の誤植。`isabelle/pss_paper.thy:2298` `p_8_7_Pred_oper0` の注記どおり
  `PT_PS = {M. M ∈ T_PS ∧ monoT M}` と読む。）
- Isabelle: `p_8_7_Pred_oper0`（`pss_paper.thy:2298`、`sorry` のまま）。
- 姉妹ファイル `lean/8/8.7-Pred-oper0.lean` は「記録された反例 \((0,0)(1,1)(2,1)\) が
  実は反例でない」ことを機械証明し、一般形 `PredOper0` を**名前付き Prop として露出のみ**
  していた（証明は無し）。本ファイルはその**一般形を還元する**。

## 訂正の履歴（重要）

「`Pred_oper0` は標準入力上で偽」という記録は **stale**。訂正 A27（＝この補題を偽と
する訂正案）は **2026-07-13 に取り下げ済み**（`corrections-old.md:69`）。取り下げ理由は
A23（基本列 \(([\ ].4)(\mathrm{ii})\) の誤読）で、`operB` を誤実装していた間だけ原文が
偽に見えていた、というもの。訂正後の正しい `operB` の下で本補題は**真**である
（数値監査 `python/audit_87_pred_oper0.py` は `maxlen=6 maxval=4` で **806/806**、
枝別 I 410 / II 65 / III 96 / IV 64 / V 171、反例ゼロ、最大 \(k = 18\)）。

## 🎯 本ファイルの成果：一般形を **単一の構造残差**へ還元

原文の証明は「順序数項の**末尾単項の零化可能性**」を scb 分解の**ネストした位置**に
適用する。姉妹ファイルの旧ヘッダは「Lean 側にはネスト形が無い（top-level 形だけ）」と
記していたが、これは **asset-blindness**（本プロジェクト 12 回目）。ネスト形は既に
`8.6-trailing-principal-annihilable.lean` に **無条件・green** で存在する：

  `trailing_principal_annihilable`
    : `t ∈ T_B → t' ∈ T_B →`
      `scb_decomp t s (flatBT (D_u (t' +ᴮ D_v 0))) b →`
      `∃ k, 0 < k ∧ k ≤ v+1 ∧ scb_decomp ([0]^k t) s (flatBT (D_u t')) b`

これがまさに原文の零化補題（前置 `s`・後置 `b`・任意の入れ子頭 `D_u`）である。従って
一般形 `PredOper0` に残っているのは**零化そのものではなく**、`Trans(M)` と
`Trans(Pred M)` が

  `Trans(M)     = s₁ · D_v(t₂ +ᴮ D_w 0) · b₁`（scb 分解）
  `Trans(Pred M)= s₁ · D_v t₂ · b₁`

という**共有 scb 文脈の中で末尾単項 \(D_w 0\) の挿入だけで異なる**という
**構造事実**（`TransPredScbInsert_pg`）だけである。これは原文の「簡約性と係数の関係」＋
「scb 分解の置換可能性」＋条件 (I)〜(VI) 分析に対応し、Isabelle 側でも
`p_8_7_OT_tail_annihilable`（scb 逐語形）が `sorry` のまま残っている**唯一の hard core**。

本ファイルは
* 還元 `p_8_7_Pred_oper0_of_scbInsert_pg`（**無条件**、既存ネスト零化を使用）、
* 定義域込みの全体還元 `p_8_7_Pred_oper0_of_residual_pg`、
* 構造残差の**具体的な充足**（枝 III の \((0,0)(1,1)(2,1)\) と枝 I の
  \((0,0)(1,0)(1,0)\)）から結論を端から端まで導く `..._closed`
を green で与える。

## 依存（ビルド済みのみ import）

`8.6-trailing-principal-annihilable`（`trailing_principal_annihilable`；推移的に
`Buchholz-1986 および Buchholz-rel-ord`/`PSS.Scb`/`PSS.Flat`）、`7.2-scb-unique`（`flatBT_injective`；
`PSS.Flat`）、`PSS.Trans`（`Trans`/`transCondVI`）、`PSS.Red`（`RTPS`）、
`PSS.Mono`（`monoT`）。

## private helper suffix: `_pg`
-/

namespace PSS

/-! ## 1. 原文の主張（忠実形） -/

/-- 補題（`Pred` と `[0]` の関係）(§8.7, 原文 6014) の忠実形。
Isabelle `p_8_7_Pred_oper0`（`pss_paper.thy:2298`）の逐語形（`PT_PS` を展開）。
内部記号 \(t_1\) は `Trans (Pred M)`。 -/
def PredOper0_pg : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → 1 < Lng M - 1 →
    transCondVI M = false → Trans M ∈ OT →
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M)

/-! ## 2. 構造残差 — `Trans(M)` と `Trans(Pred M)` の共有 scb 文脈

原文の証明本体（`content.md` 6018–6058）を単一の述語に凝縮したもの。`Trans(M)` は
scb 分解 \((s_1, D_v(t_2 +ᴮ D_w 0), b_1)\) を持ち、`Trans(Pred M)` は同じ文脈で
中身の末尾単項 \(D_w 0\) を落とした \((s_1, D_v t_2, b_1)\) と一致する。 -/
def TransPredScbInsert_pg (M : PS) : Prop :=
  ∃ (s1 b1 : List Sym) (t2 : BT) (v w : ℕ),
    Trans M ∈ T_B ∧ t2 ∈ T_B ∧
    scb_decomp (Trans M) s1
      (flatBT (Dprin (v : ℕ∞) (addBT t2 (Dprin (w : ℕ∞) BZero)))) b1 ∧
    flatBT (Trans (Pred M)) = s1 ++ flatBT (Dprin (v : ℕ∞) t2) ++ b1

/-! ## 3. 還元 — 構造残差から零化で結論（**無条件**） -/

/-- **一般形の核**：共有 scb 文脈さえ与えられれば、`8.6` のネスト零化補題
`trailing_principal_annihilable` で `[0]` 反復が `Trans(Pred M)` に到達する。
零化する末尾単項 \(D_w 0\) は本体 `0` なので、前置 `s₁`・後置 `b₁` のもとで
`D_v(t₂ +ᴮ D_w 0)` が `D_v t₂` に潰れ、`flatBT` の単射性で等式が確定する。 -/
theorem p_8_7_Pred_oper0_of_scbInsert_pg (M : PS)
    (h : TransPredScbInsert_pg M) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M) := by
  obtain ⟨s1, b1, t2, v, w, hTB, ht2, hd, hpred⟩ := h
  obtain ⟨k, _, _, hk⟩ :=
    trailing_principal_annihilable (Trans M) t2 s1 b1 v w hTB ht2 hd
  exact ⟨k, flatBT_injective (by rw [hk.1, hpred])⟩

/-! ## 4. 定義域込みの全体還元 -/

/-- 構造残差が定義域全体で成り立つ、という命題（原文の証明本体そのもの）。 -/
def PredOper0Residual_pg : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → 1 < Lng M - 1 →
    transCondVI M = false → Trans M ∈ OT → TransPredScbInsert_pg M

/-- 全体還元：構造残差（原文証明本体）が示せれば一般形 `PredOper0_pg` が従う。 -/
theorem p_8_7_Pred_oper0_of_residual_pg (H : PredOper0Residual_pg) :
    PredOper0_pg := by
  intro M h1 h2 h3 h4 h5 h6
  exact p_8_7_Pred_oper0_of_scbInsert_pg M (H M h1 h2 h3 h4 h5 h6)

/-! ## 5. 構造残差の具体的な充足 — 還元が空虚でないことの確認

構造残差 `TransPredScbInsert_pg` を 2 つの枝で明示的に充足し、還元
`p_8_7_Pred_oper0_of_scbInsert_pg` を通して結論 `∃ k. Trans(M)[0]^k = Trans(Pred M)`
を端から端まで導く。零化する末尾単項 \(D_w 0\) の本体 `t₂` が
`0`（枝 III）と `≠ 0`（枝 I）の両方を試す。 -/

/-- 枝 (III) の証人（記録された「反例」＝実は反例でない）。 -/
def Mcex_pg : PS := [(0, 0), (1, 1), (2, 1)]

/-- 枝 (I) の証人。 -/
def MI_pg : PS := [(0, 0), (1, 0), (1, 0)]

private theorem trans_Mcex_pg :
    Trans Mcex_pg = Dprin 0 (Dprin 1 (Dprin 1 BZero)) := rfl
private theorem trans_pred_Mcex_pg :
    Trans (Pred Mcex_pg) = Dprin 0 (Dprin 1 BZero) := rfl
private theorem trans_MI_pg :
    Trans MI_pg = Dprin 0 (BT.trm [.db 0 BZero, .db 0 BZero]) := rfl
private theorem trans_pred_MI_pg :
    Trans (Pred MI_pg) = Dprin 0 (Dprin 0 BZero) := rfl

/-- 枝 (III)：\(M = (0,0)(1,1)(2,1)\)。共有 scb 文脈 \(s_1 = D_0\!\cdot,\ b_1 = []\)、
外側 \(v = 1\)、内側 \(w = 1\)、本体 \(t_2 = 0\)。
すなわち `D_0(D_1(D_1 0))` の中の末尾 `D_1 0` を落として `D_0(D_1 0)` に至る。 -/
theorem transPredScbInsert_Mcex_pg : TransPredScbInsert_pg Mcex_pg := by
  refine ⟨[Sym.dsym 0], [], BZero, 1, 1, ?_, ?_, ?_, ?_⟩
  · -- `Trans Mcex ∈ T_B`
    rw [trans_Mcex_pg]
    simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList]
  · -- `t₂ = 0 ∈ T_B`
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  · -- scb 分解
    refine ⟨?_, ?_, ?_⟩
    · rw [trans_Mcex_pg]; rfl
    · intro _
      exact ⟨.db 1 (addBT BZero (Dprin 1 BZero)), by
        simp [Dprin, BZero, addBT, dfree_BP, dfree_BT, dfree_BPList], rfl⟩
    · intro x hx; simp at hx
  · -- `Trans (Pred Mcex)` が同じ文脈で末尾を落とした形と一致
    rw [trans_pred_Mcex_pg]; rfl

/-- 枝 (I)：\(M = (0,0)(1,0)(1,0)\)。共有 scb 文脈 \(s_1 = [],\ b_1 = []\)、
外側 \(v = 0\)、内側 \(w = 0\)、本体 \(t_2 = D_0 0 \neq 0\)。
すなわち `D_0((D_0 0)(D_0 0))` の中の末尾 `D_0 0` を落として `D_0(D_0 0)` に至る。 -/
theorem transPredScbInsert_MI_pg : TransPredScbInsert_pg MI_pg := by
  refine ⟨[], [], Dprin 0 BZero, 0, 0, ?_, ?_, ?_, ?_⟩
  · rw [trans_MI_pg]
    simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList]
  · simp [T_B, Dprin, BZero, dfree_BT, dfree_BP, dfree_BPList]
  · refine ⟨?_, ?_, ?_⟩
    · rw [trans_MI_pg]; rfl
    · intro _
      exact ⟨.db 0 (addBT (Dprin 0 BZero) (Dprin 0 BZero)), by
        simp [Dprin, BZero, addBT, dfree_BP, dfree_BT, dfree_BPList], rfl⟩
    · intro x hx; simp at hx
  · rw [trans_pred_MI_pg]; rfl

/-- 枝 (III) の証人で結論を端から端まで（還元 → 既存ネスト零化）導く。 -/
theorem p_8_7_Pred_oper0_Mcex_closed :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans Mcex_pg) = Trans (Pred Mcex_pg) :=
  p_8_7_Pred_oper0_of_scbInsert_pg Mcex_pg transPredScbInsert_Mcex_pg

/-- 枝 (I) の証人で結論を端から端まで導く。 -/
theorem p_8_7_Pred_oper0_MI_closed :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans MI_pg) = Trans (Pred MI_pg) :=
  p_8_7_Pred_oper0_of_scbInsert_pg MI_pg transPredScbInsert_MI_pg

#print axioms p_8_7_Pred_oper0_of_scbInsert_pg
#print axioms p_8_7_Pred_oper0_of_residual_pg
#print axioms transPredScbInsert_Mcex_pg
#print axioms transPredScbInsert_MI_pg
#print axioms p_8_7_Pred_oper0_Mcex_closed
#print axioms p_8_7_Pred_oper0_MI_closed

end PSS
