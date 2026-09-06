import Bijectivity.«14-order-linearity»
import Bijectivity.«19-alphabet-below-bound»
import Bijectivity.«23-trans-bijectivity»

/-!
# 監査 — 原文 23 項目の依存公理を固定する

Isabelle 側の `isabelle/8/audit.thy` にあたるビルド時ゲート。原文の 23 項目の
それぞれについて `#print axioms` の出力を `#guard_msgs` で固定してあるので、

* どれかが `sorry` に依存し始めたら（`sorryAx` が現れる）
* 新しい公理が紛れ込んだら

**ビルドが落ちる**。緑ビルド＝この監査に合格である。

## 🎉 23 項目すべてが `propext` / `Classical.choice` / `Quot.sound` のみ

**`sorryAx` も外部引用の `axiom` も、どこにも現れない。**

* 原文の言明が偽である `05`/`11` の逐語形は、未証明で残さず**その否定**
  （`not_ltExpPS_ltPS` / `not_seg_ltExpPS`、訂正 `B1`/`B2`）を証明してある。
* 評価写像 \(o\) と \(\psi_0\psi_\omega0\) は公理ではなく、`OT_B` の整礎性
  （`OTB-well-founded-syntactic`）から**構成**してある。
* 原文が [Buc1] / [Buc2] / [3] から引く事実（Lemma 2.1 / 2.2(c) / 加法標準形 /
  Theorem 1.4(a) ＝ 基本列の共終性 / 命題 11）は**すべて本リポジトリ内で証明済み**。
  共終性は `OTB-well-founded-syntactic-cofinality.lean` の `y4_bachmann`
  （Buchholz–Schütte の distinguished-sets 経路の cardinal-free 版）を使う。
-/

/-! ## 01 系（辞書式的順序が辞書式順序であること） -/

/--
info: 'Bijectivity.ltPS_iff_ltLex' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltPS_iff_ltLex


/-! ## 02 系（辞書式的順序の線形性） -/

/--
info: 'Bijectivity.ltPS_irrefl' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltPS_irrefl

/--
info: 'Bijectivity.ltPS_trans' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltPS_trans

/--
info: 'Bijectivity.ltPS_trichotomy' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltPS_trichotomy

/--
info: 'Bijectivity.lePS_refl' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_refl

/--
info: 'Bijectivity.lePS_trans' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_trans

/--
info: 'Bijectivity.lePS_antisymm' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_antisymm

/--
info: 'Bijectivity.lePS_total' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_total


/-! ## 03 命題（基本列的順序が推移性） -/

/--
info: 'Bijectivity.leExpPS_trans' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_trans

/--
info: 'Bijectivity.ltExpPS_trans' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltExpPS_trans


/-! ## 04 命題（基本列の辞書式的縮小性） -/

/--
info: 'Bijectivity.oper_ltPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.oper_ltPS


/-! ## 05 命題（辞書式的順序が基本列的順序を含意すること）— 逐語形の否定を証明（訂正 X-1） -/

/--
info: 'Bijectivity.not_ltExpPS_ltPS' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.not_ltExpPS_ltPS

/--
info: 'Bijectivity.ltExpPS_ltPS_of_lng' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltExpPS_ltPS_of_lng


/-! ## 06 命題（基本列の切片の不変性） -/

/--
info: 'Bijectivity.oper_seg_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.oper_seg_invariance


/-! ## 07 命題（展開と Pred の関係） -/

/--
info: 'Bijectivity.oper_take_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.oper_take_pred


/-! ## 08 補題（最左列の不変性） -/

/--
info: 'Bijectivity.leExpPS_head' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_head


/-! ## 09 補題（標準形と基本列的順序の関係） -/

/--
info: 'Bijectivity.stps_iff_leExpPS' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.stps_iff_leExpPS


/-! ## 10 命題（可算な標準形の起源） -/

/--
info: 'Bijectivity.ctps_iff_leExpPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ctps_iff_leExpPS


/-! ## 11 補題（標準形の始切片への経路）— 逐語形の否定を証明（訂正 Y-5） -/

/--
info: 'Bijectivity.not_seg_ltExpPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.not_seg_ltExpPS

/--
info: 'Bijectivity.seg_leExpPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.seg_leExpPS


/-! ## 12 命題（基本列的順序が辞書式的順序を含意すること） -/

/--
info: 'Bijectivity.ltPS_ltExpPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.ltPS_ltExpPS


/-! ## 13 系（順序の等価性） -/

/--
info: 'Bijectivity.lePS_iff_leExpPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_iff_leExpPS


/-! ## 14 系（順序の線形性） -/

/--
info: 'Bijectivity.lePS_refl_ctps' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_refl_ctps

/--
info: 'Bijectivity.lePS_antisymm_ctps' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_antisymm_ctps

/--
info: 'Bijectivity.lePS_trans_ctps' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_trans_ctps

/--
info: 'Bijectivity.lePS_total_ctps' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.lePS_total_ctps

/--
info: 'Bijectivity.leExpPS_refl' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_refl

/--
info: 'Bijectivity.leExpPS_antisymm_ctps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_antisymm_ctps

/--
info: 'Bijectivity.leExpPS_trans_ctps' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_trans_ctps

/--
info: 'Bijectivity.leExpPS_total_ctps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.leExpPS_total_ctps


/-! ## 15 命題（後続な項の基本列） -/

/--
info: 'Bijectivity.successor_fseq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.successor_fseq


/-! ## 16 補題（基本列の関係） -/

/--
info: 'Bijectivity.fseq_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.fseq_relation


/-! ## 17 命題（基本列の収束性） -/

/--
info: 'Bijectivity.fseq_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.fseq_convergence


/-! ## 18 命題（Trans が順序を保つこと） -/

/--
info: 'Bijectivity.trans_lessBT_of_ltPS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.trans_lessBT_of_ltPS


/-! ## 19 補題（対応する項の上界未満の字母） -/

/--
info: 'Bijectivity.OT_iff_OT_B_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.OT_iff_OT_B_of_lt


/-! ## 20 命題（対応する項の上界） -/

/--
info: 'Bijectivity.trans_lt_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.trans_lt_bound

/--
info: 'Bijectivity.exists_trans_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.exists_trans_gt


/-! ## 21 命題（変換写像の順序数への全単射性） -/

/--
info: 'Bijectivity.oTrans_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.oTrans_bijOn


/-! ## 22 系（ペア数列の解析） -/

/--
info: 'Bijectivity.analysis_ordinal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.analysis_ordinal

/--
info: 'Bijectivity.analysis_ordinal_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.analysis_ordinal_lt

/--
info: 'Bijectivity.analysis_term' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.analysis_term

/--
info: 'Bijectivity.analysis_term_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.analysis_term_lt


/-! ## 23 定理（変換写像の全単射性） -/

/--
info: 'Bijectivity.trans_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.trans_bijOn

/--
info: 'Bijectivity.trans_order_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Bijectivity.trans_order_iso

