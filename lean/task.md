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

- ✅ **定義層 `PSS/`**（§5 定式化。命題は置かない。移植元 `isabelle/pss_defs.thy`）[r9]

- ✅ **§5 定式化**[r6]

- ✅ **§6 ペア数列の基本性質**
  - ✅ §6.1 命題（`≤_M` の `IncrFirst` 不変性） — `6.1-le-IncrFirst-invariance`[r1]
  - ✅ §6.2 単項性[r8]
  - ✅ §6.3 許容性[r3]
  - ✅ §6.4 幹と枝[r7]
  - ✅ §6.5 簡約化[r16]
  - ✅ §6.6 簡約性[r17]
  - ✅ §6.7 標準形[r3]
  - ✅ §6.8 降順性[r6]

- ✅ **§7 Buchholz の表記系への翻訳**
  - ✅ §7.1 Buchholz の表記系[r6]
  - ✅ §7.2 scb 分解[r9]
  - ✅ §7.3 翻訳写像[r12]
  - ✅ §7.4 許容的親子関係[r10]

- 🚨 **§8 停止性**
  - ✅ §8.1 条件(I)の下での展開規則[r9]
  - 🚨 §8.2 強単項性
    - ✅ 命題（標準形の直系先祖による切片の簡約化の強単項性） — `8.2-standard-slice-Red-strongmono`[r2]
    - ✅ 補題（強単項性の切片への遺伝性） — `8.2-strongmono-slice`[r1]
    - ✅ 補題（部分表現の単項成分と `Pred` の関係） — `8.2-subexpr-component-Pred`[r5]
    - ✅ 補題（強単項性の下での部分表現の単項成分の基本性質） — `8.2-subexpr-component-strongmono`[r2]
    - ✅ 補題（条件(V)の下での右端の親の基本性質） — `8.2-condV-rightmost-parent`[r1]
    - ✅ 補題（条件(V)の下での終切片と `Trans` の関係） — `8.2-condV-terminal-slice-Trans-close`
    - 🚨 命題（条件(II)か(IV)の下での終切片と `Trans` の関係） — `8.2-condIIIV-terminal-slice-Trans`
  - 🚨 §8.3 条件(II)の下での展開規則
    - ✅ 補題（第 `0` 種型基本列の基本不等式） — `8.3-kind0-base-ineq`[r1]
    - ✅ 補題（第 `0` 種型基本列の基本分岐規則） — `8.3-kind0-branch-rule`[r1]
    - ✅ 補題（第 `0` 種型基本列の基本基点関係） — `8.3-kind0-base-basepoint`[r1]
    - 🚨 命題（条件(II)の下での `Trans` と基本列の交換関係） — `8.3-Trans-fseq-condII` ⛔8.7-fseq-descend
  - 🚨 §8.4 条件(III)か(IV)の下での展開規則
    - 🚨 命題（条件(III)か(IV)の下での `Trans` と基本列の交換関係） — `8.4-Trans-fseq-condIII-IV`
    - ✅ 補題（右端の非許容直系先祖の基本性質） — `8.4-rightmost-nonadm-ancestor`[r1]
    - 🚨 補題（条件(III)か(IV)の下での基本列の基本性質） — `8.4-fseq-basic`[r1]
    - 🚨 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係） — `8.4-rightmost-replace-Trans`[r1]
    - 🚨 補題（条件(III)～(VI)の下での展開規則の基本性質） — `8.4-oper-basic`
    - 🚨 補題群（条件(III)～(VI)の下での各種 scb 分解） — `8.4-scb-decompositions`
  - 🚨 §8.5 条件(V)の下での展開規則
    - 🚨 命題（条件(V)の下での `Trans` と基本列の交換関係） — `8.5-Trans-fseq-condV`
    - ✅ 補題（条件(V)の下での `Joints` と `FirstNodes` と `t₂` の基本性質） — `8.5-Joints-FirstNodes-basic`[r1]
    - ✅ 補題（条件(V) admissible 底3値と non-admissible 導出層） — `8.5-exchV-values-close`
    - 🚨 補題（条件(V)の下での各種 scb 分解） — `8.5-scb-decompositions`
    - 🚨 補題（条件(V)の下での基本列の scb 分解） — `8.5-fseq-scb-decomposition`
  - 🚨 §8.6 条件(VI)の下での展開規則
    - ✅ 補題（公差 `(1,0)` のペア数列の `Trans` の基本性質） — `8.6-const2nd-Trans` [r1]
    - ✅ 補題（公差 `(1,1)` のペア数列の `Trans` の展開規則） — `8.6-diagSeq-Trans-fseq` [r1]
    - ✅ 補題（順序数項の末尾単項の零化可能性） — `8.6-trailing-principal-annihilable` [r1]
    - 🚨 命題（条件(VI)の下での `Trans` と基本列の交換関係） — `8.6-Trans-fseq-condVI`
  - 🚨 §8.7 主結果
    - ✅ 補題（公差 `(0,0)` のペア数列の `Trans` の基本性質） — `8.7-const00-Trans`[r1]
    - 🚨 補題（基本列の降下性） — `8.7-fseq-descend`
    - ✅ 補題（順序数項の再帰構造） — `8.7-OT-scb-recursive`[r1]
    - ✅ 補題（順序数項の共終数の遺伝性） — `8.7-OT-dom-hereditary`[r1]
    - ✅ 補題（順序数項の末尾項の零化可能性、top-level 値形） — `8.7-OT-tail-annihilable`[r1]
    - 🚨 補題（`Pred` と `[0]` の関係） — `8.7-Pred-oper0`[r1]
    - ✅ 補題（順序数項の基本例） — `8.7-OT-examples`[r1]
    - 🚨 補題（`Trans` が標準形を保つこと） — `8.7-Trans-preserves-OT`
    - 🚨 **定理（標準形ペア数列システムの停止性）** — `8.7-termination`
