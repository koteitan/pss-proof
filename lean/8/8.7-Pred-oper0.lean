import PSS.Defs
import PSS.Red
import PSS.Mono
import PSS.Trans
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»

/-!
# §8.7 補題（`Pred` と `[0]` の関係）— 記録された「反例」の機械的否認

原文: content.md 6014「補題（\(\textrm{Pred}\)と\([0]\)の関係）」。
（原文は \(M \in RT_{\textrm{PS}} \cap PT_{\textrm{B}}\) と書くが、`PT_B` は `PT_PS` の
誤植。`isabelle/pss_paper.thy` の注記どおり `PT_PS` と読む。）

Isabelle: `isabelle/pss_paper.thy:2298` `p_8_7_Pred_oper0`（`sorry` のまま）。
Isabelle 側の注記どおり、`Trans` の再帰的定義中の内部記号 \(t_1\) は
`Trans (Pred M)` そのものなので、ここでもその形で露出する。

## 🚨 本ファイルの主結論：**記録の方が誤っていた**

本タスクは「`Pred_oper0` は標準入力上で**偽**、反例 \(M = (0,0)(1,1)(2,1)\)」という
記録に基づき、その反例を Lean で機械証明することを目的に開始された。**その記録は
stale であり、反例は反例ではない。**

* 訂正 A27（＝この補題を偽とする訂正案）は **2026-07-13 に取り下げ済み**
  (`corrections-old.md:69`)。取り下げ理由は A23（基本列 \(([\ ].4)(\mathrm{ii})\) の
  誤読）で、`operB` を誤って実装していた間だけ原文が偽に見えていた、というもの。
* 訂正後の正しい `operB`（`Buchholz-1986/ および Buchholz-rel-ord/`、A23 反映済み）の下では、当の
  \(M = (0,0)(1,1)(2,1)\) は
  \(\textrm{Trans}(M) = D_0 D_1 D_1 0 \to D_0 D_1 D_0 0 \to D_0 D_1 0 = t_1\)
  と **k = 2 でちょうど結論を満たす**。本ファイルはこれを機械証明する
  (`p_8_7_Pred_oper0_alleged_cex_not_a_counterexample`)。
* 従って**訂正は不要**であり、A27 は取り下げられたままでよい。新規 A 番号も要らない。

### stale な記録の所在（本ファイルの担当範囲外・親が修正すること）

`Pred_oper0` を「偽」と記す以下の 3 箇所は、A27 取り下げ前の記述が残ったもの：

* `isabelle/memo.md:67`（REFUTED registry の `Pred_oper0(A27)` 行）
* `lean/memo.md:601`
* `lean/8/8.7-termination.lean:136`–`142`（「死路」節。ただし**当該ファイルの
  健全性には影響しない**：停止性は Σ_B 降下和ルートで、`Pred_oper0` を経由しない。
  誤っているのは理由付けの文だけで、迂回という判断自体は正しい）

## 数値的裏付け

`python/audit_87_pred_oper0.py`（本タスクで追加）。忠実な定義域
\(M \in RT_{\textrm{PS}} \cap PT_{\textrm{PS}}\)、\(j_1 > 1\)、条件 (VI) 不成立、
\(\textrm{Trans}(M) \in OT_{\textrm{B}}\) 上の全数走査：

* `maxlen=5 maxval=3`: **143/143**（条件 I 79 / II 9 / III 15 / IV 9 / V 31）
* `maxlen=6 maxval=3`: **593/593**（条件 I 325 / II 46 / III 55 / IV 38 / V 129）、
  観測された最大 \(k\) は 18

反例ゼロ。既存の `python/_s8_real_orbit.py` は標準形ホストかつ条件 I/III/V 枝しか
見ていなかった（71/71）ので、本スクリプトで定義域と枝を原文どおりに広げてある。
⚠️ 固定深さの経験検証は本プロジェクトで 13 回の偽陽性を出しているので、これは
「反例が無い」ことの証拠であって証明ではない。一般形は未証明（下記）。

## 状態

* ✅ green（`sorry` 0）。`p_8_7_Pred_oper0_alleged_cex_not_a_counterexample` と
  条件 I / V の証人 2 本は**無条件・機械証明済**。
* 🚨 一般形 `PredOper0` は **未証明**（名前付き Prop として露出のみ）。原文の証明は
  「順序数項の末尾単項の零化可能性」を **scb 分解のネストした位置**に適用するが、
  Lean 側にあるのは `8.7-OT-tail-annihilable` の
  `toplevel_OT_tail_annihilate_uncond`（**top-level 形**）だけで、
  ネスト形（Isabelle `p_8_7_OT_tail_annihilable`、これも `sorry`）が無い。
  本補題は停止性連鎖に**不要**（`TerminationResidual` の 27 本にも含まれない）ため、
  ここでは露出に留める。

## 依存（ビルド済みのみ import）

`PSS.Defs`（`PS` / `TPS` / `Lng` / `Pred`）、`PSS.Red`（`reduced` / `RTPS`）、
`PSS.Mono`（`monoT`）、`PSS.Trans`（`Trans` / `transCondVI`）、
`Buchholz-1986 および Buchholz-rel-ord`（`operB` / `numBT` / `OT` / `Dprin` / `BZero`）。

## 移植上の注意

`decide` はこの命題には効かない。`bOperCore` が整礎再帰なのでカーネル簡約が
`Acc.rec` で止まる（`unseal` でも駄目）。一方 `Trans` は燃料による構造的再帰なので
`rfl` で計算できる。従って本ファイルの型は「`Trans` は `rfl`、`operB` は
`simp [bOperCore, …]` の等式補題」という二段構えになっている。
-/

namespace PSS

/-! ## 原文の主張（忠実形） -/

/-- 補題（`Pred` と `[0]` の関係）(§8.7, 原文 6014) の忠実形。

Isabelle `p_8_7_Pred_oper0` (`pss_paper.thy:2298`) の逐語形。
`PT_PS = {M. M ∈ T_PS ∧ monoT M}` (`pss_defs.thy:240`) を展開してある
（Lean 側に `PTPS` は無いので、新しい公開名を作らずに展開した）。
内部記号 \(t_1\) は `Trans (Pred M)`。

**未証明**（本ファイルは反例不在の機械的証拠のみを与える）。 -/
def PredOper0 : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → 1 < Lng M - 1 →
    transCondVI M = false → Trans M ∈ OT →
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M)

/-! ## 記録された「反例」 -/

/-- `isabelle/memo.md` / `lean/memo.md` / `8.7-termination.lean` が
`Pred_oper0` の反例として記録している標準形ペア数列。実際には反例ではない。
条件 (III) 枝のホスト。 -/
def Mcex_po : PS := [(0, 0), (1, 1), (2, 1)]

/-- `Trans` は燃料による構造的再帰なのでカーネルで計算できる。 -/
private theorem trans_Mcex_po : Trans Mcex_po = Dprin 0 (Dprin 1 (Dprin 1 BZero)) := rfl

/-- 内部記号 \(t_1 = \textrm{Trans}(\textrm{Pred}(M))\) の値。 -/
private theorem trans_pred_Mcex_po : Trans (Pred Mcex_po) = Dprin 0 (Dprin 1 BZero) := rfl

/-- \(\textrm{Trans}(M)[0]^2 = t_1\)。訂正 A23 後の正しい基本列での 2 歩：
\(D_0 D_1 D_1 0 \to D_0 D_1 D_0 0 \to D_0 D_1 0\)。 -/
private theorem orbit_Mcex_po :
    ((fun a => operB a (numBT 0))^[2]) (Trans Mcex_po) = Trans (Pred Mcex_po) := by
  rw [trans_Mcex_po, trans_pred_Mcex_po]
  simp [Function.iterate_succ_apply,
        operB, bOperCore, Dprin, numBT, BZero, domTag, domTagBP, domTagList,
        numNat, addBT, multBT]

/-- **記録された「反例」は反例ではない。**

\(M = (0,0)(1,1)(2,1)\) は `p_8_7_Pred_oper0` の仮定を**すべて**満たし
（`RT_PS`・`T_PS`・`monoT`＝`PT_PS`・\(j_1 = 2 > 1\)・条件 (VI) 不成立・
\(\textrm{Trans}(M) \in OT\)）、かつ結論を \(k = 2\) で**満たす**。

すなわち訂正 A27 の取り下げ（`corrections-old.md:69`、2026-07-13）は正しく、
これを「偽」とする `isabelle/memo.md:67` / `lean/memo.md:601` /
`8.7-termination.lean:136` の記述は stale である。 -/
theorem p_8_7_Pred_oper0_alleged_cex_not_a_counterexample :
    RTPS Mcex_po ∧ TPS Mcex_po ∧ monoT Mcex_po = true ∧ 1 < Lng Mcex_po - 1 ∧
      transCondVI Mcex_po = false ∧ Trans Mcex_po ∈ OT ∧
      ((fun a => operB a (numBT 0))^[2]) (Trans Mcex_po) = Trans (Pred Mcex_po) :=
  ⟨rfl, by simp [TPS, Mcex_po], rfl, by decide, rfl, rfl, orbit_Mcex_po⟩

/-! ## 他の枝の証人（枝ごとの非空虚性）

条件 (III) 以外の枝でも原文の結論が成立することを示す。条件 (II)/(IV) は最小の
証人でも \(k = 6, 7\) と軌道が長いので、ここでは数値監査
(`python/audit_87_pred_oper0.py`) に委ね、安価な (I)/(V) のみ機械証明する。 -/

/-- 条件 (I) 枝の証人。 -/
def MI_po : PS := [(0, 0), (1, 0), (1, 0)]

/-- 条件 (V) 枝の証人。 -/
def MV_po : PS := [(0, 0), (1, 1), (1, 1)]

private theorem trans_MI_po :
    Trans MI_po = Dprin 0 (BT.trm [.db 0 BZero, .db 0 BZero]) := rfl

private theorem trans_pred_MI_po : Trans (Pred MI_po) = Dprin 0 (Dprin 0 BZero) := rfl

private theorem trans_MV_po :
    Trans MV_po = Dprin 0 (BT.trm [.db 1 BZero, .db 1 BZero]) := rfl

private theorem trans_pred_MV_po : Trans (Pred MV_po) = Dprin 0 (Dprin 1 BZero) := rfl

/-- 条件 (I) 枝：\(M = (0,0)(1,0)(1,0)\) で仮定が成立し、結論が \(k = 1\) で成立する。 -/
theorem p_8_7_Pred_oper0_condI_witness :
    RTPS MI_po ∧ TPS MI_po ∧ monoT MI_po = true ∧ 1 < Lng MI_po - 1 ∧
      transCondVI MI_po = false ∧ Trans MI_po ∈ OT ∧
      ((fun a => operB a (numBT 0))^[1]) (Trans MI_po) = Trans (Pred MI_po) := by
  refine ⟨rfl, by simp [TPS, MI_po], rfl, by decide, rfl, rfl, ?_⟩
  rw [trans_MI_po, trans_pred_MI_po]
  simp [Function.iterate_succ_apply,
        operB, bOperCore, Dprin, numBT, BZero, domTag, domTagBP, domTagList,
        numNat, addBT, multBT]

/-- 条件 (V) 枝：\(M = (0,0)(1,1)(1,1)\) で仮定が成立し、結論が \(k = 2\) で成立する。 -/
theorem p_8_7_Pred_oper0_condV_witness :
    RTPS MV_po ∧ TPS MV_po ∧ monoT MV_po = true ∧ 1 < Lng MV_po - 1 ∧
      transCondVI MV_po = false ∧ Trans MV_po ∈ OT ∧
      ((fun a => operB a (numBT 0))^[2]) (Trans MV_po) = Trans (Pred MV_po) := by
  refine ⟨rfl, by simp [TPS, MV_po], rfl, by decide, rfl, rfl, ?_⟩
  rw [trans_MV_po, trans_pred_MV_po]
  simp [Function.iterate_succ_apply,
        operB, bOperCore, Dprin, numBT, BZero, domTag, domTagBP, domTagList,
        numNat, addBT, multBT]

/-! ## 訂正の要否

原文は（正しい `operB` の下で）**真に見える**。593/593 で反例なし。
従って**訂正案は不要**で、A27 は取り下げられたままでよい。新しい A 番号も不要。
残るのは「原文が真であることの一般証明」であって、原文の誤りではない。 -/

#print axioms p_8_7_Pred_oper0_alleged_cex_not_a_counterexample
#print axioms p_8_7_Pred_oper0_condI_witness
#print axioms p_8_7_Pred_oper0_condV_witness

end PSS
