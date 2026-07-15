# 進捗管理（Lean 版）

<!--
## 注意事項
- **ツリーの 1 行 = 原文の命題 1 つ = Lean ファイル 1 つ**（`lean/<章>/<節>-<name>.lean`）。
  行末の `<節>-<name>` がそのままファイル名。構造の仕様は spec.md、手順は step.md。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**（司令マーカー）。
  - 🚨🤖 ＝ workflow エージェント作業中
  - 📘 ＝ [Buc1] 引用（外部結果。原文も証明せず引用のみ）
  - ⛔ X ＝ X 待ち（X が解けるまでこの項目は解けない）
  - ❌ ＝ 原文偽（訂正 Axx）かつ停止性に不要（迂回・証明対象外の死枝。✅ でも 🚨 でもない）
- **✅ を付けてよいのは step.md §1 の 3 条件を全部満たしたときだけ**。
  `lake build` が通っただけでは駄目（Lean は `sorry` を warning で通す）。
  `python3 python/check_lean.py <file>` が **rc=0**、かつ `#print axioms` に **`sorryAx` 無し**、
  かつ**主張が原文（訂正後）と一致**していること。
- **進捗ツリーを編集するときは task.md と memo.md の両方を同じように編集する**
  （同一アイテム名・同一ツリー構造を保つ。task.md=骨格のみ、memo.md=同じツリー＋詳細注釈）。
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**。
  訂正番号・Isabelle の対応補題名・難易度・計画は **memo.md** に書く。
- 子がすべて ✅ のノードは子を畳む（子を書かない）。
- **🚨 行に ✅(done部) を inline 禁止**。done と未done が混在したら ✅子/🚨子 に分割する。
- **ラウンド消費数 `[rN]`**：そのアイテムに何ラウンド費やしたかを末尾に付ける。
  分岐時は消費済みを子へ配分、子孫が全て ✅ になったら合計して畳む。
-->

## 進捗ツリー

- ✅ **定義層 `PSS/`**（§5 定式化。命題は置かない。移植元 `isabelle/pss_defs.thy`）[r8]
  - ✅ ペア数列 `T_PS` / `Lng` / 親子関係 / 直系先祖 / `Pred` / 基本列 `oper` / `IncrFirst` — `PSS/Defs.lean`[r1]
  - ✅ 単項性 `monoT` / 単項成分 `P` / 幹と枝 `Br`,`Joints`,`TrMax`,`FirstNodes` — `PSS/Mono.lean`[r1]
  - ✅ 許容性 `adm` / 許容化 / 基点 `Marked` — `PSS/Adm.lean`[r1]
  - ✅ 簡約化 `Red` / 簡約性 `RT_PS` — `PSS/Red.lean`[r1]
  - ✅ 標準形 `ST_PS` — `PSS/Standard.lean`[r1]
  - ✅ Buchholz の表記系 `T_B`,`<_B`,基本列,`dom`,`OT_B` — `PSS/Buchholz.lean`[r1]
  - ✅ scb 分解（Σ 上の文字列） — `PSS/Scb.lean`[r1]
  - ✅ 翻訳写像 `Trans` / `Mark` — `PSS/Trans.lean`[r1]

- ✅ **§5 定式化**[r6]
  - ✅ §5.1 命題（親の存在の判定条件） — `5.1-parent-exists`[r1]
  - ✅ §5.1 命題（親の基本性質） — `5.1-parent-basic`[r1]
  - ✅ §5.1 系（直系先祖の基本性質） — `5.1-ancestor-basic`[r1]
  - ✅ §5.1 系（直系先祖の木構造） — `5.1-ancestor-tree`[r1]
  - ✅ §5.3 命題（`Pred` が `[1]` で表されること） — `5.3-pred-is-oper1`[r1]
  - ✅ §5.4 命題（ペア数列システム `F` の well-defined 性） — `5.4-F-welldefined`[r1]

- 🚨 **§6 ペア数列の基本性質**
  - ✅ §6.1 命題（`≤_M` の `IncrFirst` 不変性） — `6.1-le-IncrFirst-invariance`[r1]
  - ✅ §6.2 単項性[r8]
  - ✅ §6.3 許容性[r3]
  - ✅ §6.4 幹と枝[r7]
  - 🚨 §6.5 簡約化
    - ✅ 命題（`Red` の well-defined 性） — `6.5-Red-welldefined`[r2]
    - ✅ 命題（`Red` の `IncrFirst` 不変性） — `6.5-Red-IncrFirst-invariance`[r2]
    - ✅ 命題（`Lng` の `Red` 不変性） — `6.5-Lng-Red-invariance`[r1]
    - ✅ 系（`Red` が零項性を保つこと） — `6.5-Red-preserves-zeroT`[r1]
    - 🚨 系（直系先祖の `Red` 不変性） — `6.5-Red-le-invariance`
    - ✅ 系（`Red` が単項性を保つこと） — `6.5-Red-preserves-monoT`[r1]
    - ✅ 系（`P` の `Red` 同変性） — `6.5-P-Red-equivariance`[r1]
    - ✅ 命題（単項性と `Red` の関係） — `6.5-monoT-Red`[r1]
    - ✅ 命題（`Red` の冪等性） — `6.5-Red-idempotence`[r1]
    - 🚨 命題（`Red` と `Pred` の可換性） — `6.5-Red-Pred-commute`
    - 🚨 命題（`Red` と基本列の可換性） — `6.5-Red-fseq-commute`
    - 🚨 命題（`Red` が許容性を保つこと） — `6.5-Red-preserves-adm`
    - 🚨 系（許容化の `Red` 不変性） — `6.5-admof-Red-invariance`
    - 🚨 系（`Red` が基点を保つこと） — `6.5-Red-preserves-marked`
  - 🚨 §6.6 簡約性
    - 🚨 命題（簡約性の切片への遺伝性） — `6.6-reduced-slice`
    - ✅ 命題（`P` が簡約性を保つこと） — `6.6-P-preserves-reduced`[r1]
    - 🚨 命題（簡約性が基本列で保たれること） — `6.6-reduced-fseq`
    - 🚨 命題（簡約性と係数の関係） — `6.6-reduced-iff-condAB`
    - ✅ 補題（`Red` と左端の関係） — `6.6-Red-leftend`[r1]
    - 🚨 補題（簡約性と係数の基本性質） — `6.6-reduced-coeff`
    - ✅ 補題（簡約性と左端の関係） — `6.6-reduced-leftend`[r1]
    - ✅ 補題（条件(A)と(B)と係数の基本性質） — `6.6-condAB-coeff`[r1]
    - 🚨 系（直系先祖による切片と `Red` と `IncrFirst` の関係） — `6.6-ancestor-slice-Red-IncrFirst`
    - ✅ 系（`1` 列ペア数列の基本性質） — `6.6-one-column`[r1]
    - ✅ `RT_PS` と `Red` の像の関係 — `6.6-RT-image-of-Red`[r1]
  - 🚨 §6.7 標準形
    - 🚨 命題（標準形の簡約性） — `6.7-standard-reduced`
    - ✅ 命題（標準形の単項成分が標準形であること） — `6.7-standard-P-components`[r1]
    - ✅ 命題（標準形の始切片への遺伝性） — `6.7-standard-prefix`[r1]
  - 🚨 §6.8 降順性
    - 🚨 命題（標準形の切片と `Br` の降順性の関係） — `6.8-standard-slice-Br-descending`
    - 🚨 命題（標準形の単項成分が降順であること） — `6.8-standard-P-descending`

- 🚨 **§7 Buchholz の表記系への翻訳**
  - 🚨 §7.1 Buchholz の表記系
    - ✅ 命題（`<_B` が狭義線形順序であること） — `7.1-lessBT-linear-order`[r1]
    - ✅ 命題（順序数項の単項成分の基本性質） — `7.1-term-components`[r1]
    - ✅ 命題（順序数項のカッコの個数が左右で等しいこと） — `7.1-paren-balance`[r1]
    - 📘 [Buc1] Lemma 2.2（`OT_B` の整礎性） — `7.1-buchholz-wf`
    - ✅ [Buc1] Lemma 3.2a（基本列の狭義減少性） — `7.1-buchholz-fseq-lt`[r1]
    - ✅ [Buc1] Lemma 3.2（`OT_B` の基本列閉包） — `7.1-buchholz-fseq-closed`[r1]
  - 🚨 §7.2 scb 分解
    - ✅ 命題（scb分解の置換可能性） — `7.2-scb-replaceable`[r1]
    - ✅ 命題（scb分解の合成則） — `7.2-scb-compose`[r1]
    - ✅ 命題（scb分解の自明性の判定条件） — `7.2-scb-triviality`[r1]
    - ✅ 命題（scb分解の一意性） — `7.2-scb-unique`[r3]
    - ✅ 系（加法とscb分解の関係） — `7.2-add-scb`[r1]
    - ✅ 命題（scb分解と基本列の関係） — `7.2-scb-fseq`[r1]
    - ✅ 命題（`RightNodes` と部分表現の関係） — `7.2-RightNodes-subexpr`[r1]
  - 🚨 §7.3 翻訳写像
    - 🚨 命題（`Trans` の well-defined 性） — `7.3-Trans-welldefined`
    - ✅ 命題（`2` 列ペア数列の基本性質） — `7.3-two-column`[r1]
    - 🚨 命題（`Trans` の `(IncrFirst,Red)` 不変 `P` 同変性） — `7.3-Trans-IncrFirst-Red`
    - 🚨 命題（`Mark` の `(IncrFirst,Red,P)` 不変性） — `7.3-Mark-IncrFirst-Red`
    - 🚨 命題（`Trans` が零項性を保つこと） — `7.3-Trans-preserves-zeroT`
    - 🚨 命題（`c₁` と `c₂` の大小関係） — `7.3-c1-c2-order`
    - 🚨 命題（`Pred` の `Trans` に関する降下性） — `7.3-Pred-Trans-descend`
    - 🚨 命題（右端第 `1` 基点の `Mark` の基本性質） — `7.3-Mark-rightmost1`
    - 🚨 命題（`Trans` が単項性を保つこと） — `7.3-Trans-preserves-monoT`
  - 🚨 §7.4 許容的親子関係
    - 🚨 命題（`Adm_M` と `<^NextAdm` の関係） — `7.4-Adm-nextAdm`
    - 🚨 命題（`Trans` と `<^NextAdm` の関係） — `7.4-Trans-nextAdm`
    - 🚨 系（`Mark` と `<^NextAdm` の関係） — `7.4-Mark-nextAdm`
    - 🚨 系（`Trans` の `Mark` と `Pred` による表示） — `7.4-Trans-Mark-Pred`
    - 🚨 命題（`Mark` の `Trans` による表示） — `7.4-Mark-Trans-repr`
    - 🚨 系（`Trans` の `Mark` と切片による表示） — `7.4-Trans-Mark-seg`
    - 🚨 系（`RightNodes` と `Mark` の関係） — `7.4-RightNodes-Mark`
    - 🚨 命題（`RightNodes` と `RightAnces` の関係） — `7.4-RightAnces-RightNodes`
    - 🚨 系（非零項の `RightAnces` が非空であること） — `7.4-RightAnces-zeroT`

- 🚨 **§8 停止性**
  - 🚨 §8.1 条件(I)の下での展開規則
    - ✅ 補題（公差 `(1,1)` のペア数列の `Trans` の基本性質） — `8.1-diagSeq-Trans` [r1]
    - ✅ 系（`Pred` と公差 `(1,1)` のペア数列の `Trans` の基本性質） — `8.1-Pred-diagSeq-Trans` [r1]
    - 🚨 補題（条件(I)か(III)の下での `c₁` 前後の具体表示） — `8.1-condI-III-c1-around`
    - 🚨 命題（条件(I)の下での `Trans` と基本列の交換関係） — `8.1-Trans-fseq-condI`
  - 🚨 §8.2 強単項性
    - 🚨 命題（標準形の直系先祖による切片の簡約化の強単項性） — `8.2-standard-slice-Red-strongmono`
    - 🚨 補題（強単項性の切片への遺伝性） — `8.2-strongmono-slice`
    - 🚨 補題（部分表現の単項成分と `Pred` の関係） — `8.2-subexpr-component-Pred`
    - 🚨 補題（強単項性の下での部分表現の単項成分の基本性質） — `8.2-subexpr-component-strongmono`
    - 🚨 補題（条件(V)の下での右端の親の基本性質） — `8.2-condV-rightmost-parent`
    - 🚨 補題（条件(V)の下での終切片と `Trans` の関係） — `8.2-condV-terminal-slice-Trans`
    - 🚨 命題（条件(II)か(IV)の下での終切片と `Trans` の関係） — `8.2-condIIIV-terminal-slice-Trans`
  - 🚨 §8.3 条件(II)の下での展開規則
    - 🚨 補題（第 `0` 種型基本列の基本不等式） — `8.3-kind0-base-ineq`
    - 🚨 補題（第 `0` 種型基本列の基本分岐規則） — `8.3-kind0-branch-rule`
    - 🚨 補題（第 `0` 種型基本列の基本基点関係） — `8.3-kind0-base-basepoint`
    - 🚨 命題（条件(II)の下での `Trans` と基本列の交換関係） — `8.3-Trans-fseq-condII`
  - 🚨 §8.4 条件(III)か(IV)の下での展開規則
    - 🚨 命題（条件(III)か(IV)の下での `Trans` と基本列の交換関係） — `8.4-Trans-fseq-condIII-IV`
    - 🚨 補題（右端の非許容直系先祖の基本性質） — `8.4-rightmost-nonadm-ancestor`
    - 🚨 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係） — `8.4-rightmost-replace-Trans`
    - 🚨 補題（条件(III)～(VI)の下での展開規則の基本性質） — `8.4-oper-basic`
    - 🚨 補題群（条件(III)～(VI)の下での各種 scb 分解） — `8.4-scb-decompositions`
  - 🚨 §8.5 条件(V)の下での展開規則
    - 🚨 命題（条件(V)の下での `Trans` と基本列の交換関係） — `8.5-Trans-fseq-condV`
    - 🚨 補題（条件(V)の下での `Joints` と `FirstNodes` と `t₂` の基本性質） — `8.5-Joints-FirstNodes-basic`
    - 🚨 補題（条件(V)の下での各種 scb 分解） — `8.5-scb-decompositions`
    - 🚨 補題（条件(V)の下での基本列の scb 分解） — `8.5-fseq-scb-decomposition`
  - 🚨 §8.6 条件(VI)の下での展開規則
    - 🚨 補題（公差 `(1,0)` のペア数列の `Trans` の基本性質） — `8.6-const2nd-Trans`
    - 🚨 補題（公差 `(1,1)` のペア数列の `Trans` の展開規則） — `8.6-diagSeq-Trans-fseq`
    - 🚨 補題（順序数項の末尾単項の零化可能性） — `8.6-trailing-principal-annihilable`
    - 🚨 命題（条件(VI)の下での `Trans` と基本列の交換関係） — `8.6-Trans-fseq-condVI`
  - 🚨 §8.7 主結果
    - 🚨 補題（公差 `(0,0)` のペア数列の `Trans` の基本性質） — `8.7-const00-Trans`
    - 🚨 補題（基本列の降下性） — `8.7-fseq-descend`
    - 🚨 補題（順序数項の再帰構造） — `8.7-OT-scb-recursive`
    - 🚨 補題（順序数項の共終数の遺伝性） — `8.7-OT-dom-hereditary`
    - 🚨 補題（順序数項の末尾項の零化可能性） — `8.7-OT-tail-annihilable`
    - 🚨 補題（`Pred` と `[0]` の関係） — `8.7-Pred-oper0`
    - 🚨 補題（順序数項の基本例） — `8.7-OT-examples`
    - 🚨 補題（`Trans` が標準形を保つこと） — `8.7-Trans-preserves-OT`
    - 🚨 **定理（標準形ペア数列システムの停止性）** — `8.7-termination`
