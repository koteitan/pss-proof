# spec.md — Lean 版のディレクトリ／ファイル構造

このファイルは **Lean 化プロジェクトの構造仕様**である。作業手順は [step.md](step.md)、
進捗は [task.md](task.md)、設計メモは [memo.md](memo.md)、Lean サーバは [kimina.md](kimina.md)。

---

## 0. 何を Lean 化するのか

原典は P進大好きbot 氏の記事「ペア数列の停止性」（Googology Wiki）。
リポジトリ直下の `tmp/content.md`（`original.html` から再生成）が原文の正本。

Isabelle 版（`isabelle/`）は既に **停止性定理を仮定ゼロ・sorry ゼロで証明済み**であり、
そこで判明した **原文の誤り 30 件** は `corrections.md` に、
**我々の側の誤りだった取り下げ 17 件** は `corrections-old.md` にまとまっている。

Lean 版が移植するのは **「訂正後の正しい主張とその証明」** である。
原文そのままの（偽を含む）主張を全部転記した Isabelle の `pss_paper.thy` に相当する層は作らない。
ただし **原文の命題 1 つ = Lean ファイル 1 つ**という対応は保ち、各ファイルの冒頭に
「原文のどの命題か」「どの訂正が効いているか」をヘッダで明記する（§3）。

---

## 1. ディレクトリ構造

```
git/
├── corrections.md          ← 原文の誤り 30 件（Lean 側でも正本。原文と Lean 文の差はすべてここに帰着する）
├── corrections-old.md      ← 取り下げ 17 件（我々の誤り。参考）
├── python/                 ← 反例探索・数値検証モデル（red_model.py / trans_model.py が正本）
├── tools/                  ← 原文処理（make_content.py で tmp/content.md を再生成）
├── tmp -> ..               ← 親ディレクトリへの symlink（原文 HTML など repo 外資産）
│
├── isabelle/               ← 【完了済・凍結】Isabelle/HOL 版。ROOT, pss_defs.thy, pss_paper.thy,
│   ├── task.md             │  pss_mechanized.thy, layerB/, layerC/。停止性定理を証明済。
│   └── memo.md             │  Lean 化の「証明の設計図」として読む（§5）。
│
└── lean/                   ← 【本プロジェクト】Lean 4 版
    ├── spec.md             ← このファイル（構造仕様）
    ├── step.md             ← 作業手順（1 命題を片付ける手続き）
    ├── task.md             ← 進捗ツリー（🚨/✅。原文の命題 1 つ = ツリーの 1 行 = ファイル 1 つ）
    ├── memo.md             ← 設計メモ（task.md と同じツリー＋詳細注釈。Isabelle の plan.md 相当）
    ├── kimina.md           ← kimina-lean-server の使い方（workflow / sub-agent からの検証）
    │
    ├── lakefile.lean       ← Lake 設定。章ディレクトリを lean_lib として登録（§2）
    ├── lean-toolchain      ← leanprover/lean4:v4.30.0（kimina の repl と一致させること）
    ├── lake-manifest.json  ← mathlib v4.30.0 を pin
    │
    ├── PSS.lean            ← PSS/ 以下の import まとめ
    ├── PSS/                ← 【定義層】§5 の定式化。命題は置かない
    │   ├── Defs.lean       │  ペア数列 T_PS, Lng, 親子関係, 直系先祖, Pred, 基本列 oper, IncrFirst
    │   ├── Mono.lean       │  単項性 monoT, 単項成分 P, 幹と枝 Br/Joints/TrMax/FirstNodes
    │   ├── Adm.lean        │  許容性 adm, 許容化, 基点 Marked
    │   ├── Red.lean        │  簡約化 Red, 簡約性 reduced (RT_PS)
    │   ├── Standard.lean   │  標準形 ST_PS
    │   ├── Scb.lean        │  scb 分解（Σ 上の文字列としての項）
    │   └── Trans.lean      │  翻訳写像 Trans / Mark
    │
    ├── Buchholz-1986/      ← [Buc1] の定義・補題。subsection ごとに .lean / .md
    ├── Buchholz-1987/      ← 1987 年論文 §2 の W_v 構成
    ├── Buchholz-rel-ord/   ← 未公刊 [Buc2] p.6 Definition 6
    ├── OTB-well-founded-syntactic/
    │                       ← 順序数意味論を使わない (OT_B, <) の整礎性証明
    │
    ├── 5/                  ← §5 定式化 の命題
    ├── 6/                  ← §6 ペア数列の基本性質 の命題
    ├── 7/                  ← §7 Buchholz の表記系への翻訳 の命題
    └── 8/                  ← §8 停止性 の命題
```

`5.lean` / `6.lean` / `7.lean` / `8.lean`（各章の import まとめ）を `lean/` 直下に置く。

---

## 2. 命題ファイルの命名規則と Lean の制約

### 規則

```
lean/<章>/<節>-<english-theorem-name>.lean
```

例:

```
lean/7/7.2-scb-unique.lean
lean/7/7.4-Mark-Trans-repr.lean
lean/8/8.7-termination.lean
```

- `<章>` = 原文の章番号（`5`,`6`,`7`,`8`）。ディレクトリ。
- `<節>` = 原文の節番号（`7.2` など）。ファイル名の先頭。同じ節に命題が複数あればファイルが複数並ぶ。
- `<english-theorem-name>` = 命題の英語名。ケバブケース。原則 `isabelle/pss_paper.thy` の補題名
  （`p_7_2_scb_unique` など）から機械的に導く。

### Lean 側の制約（**検証済み**：この構造はそのままビルドできる）

Lean 4 の識別子は数字始まり・`.`・`-` を含めないが、**フレンチクォート `«...»` で囲めば通る**。
Lake はモジュール名 `«7».«7.2-scb-unique»` を `7/7.2-scb-unique.lean` にマップする。

したがって:

- **ファイル内の宣言（`theorem` 名）に `-` や数字始まりは使わない**。
  ファイル名だけが `7.2-scb-unique`、中の定理は `PSS.scb_unique` のように普通の名前にする。
- **import は必ずフレンチクォートで書く**:

  ```lean
  import PSS.Scb
  import «7».«7.2-scb-unique»      -- ← 他の命題ファイルを使うとき
  ```

- 章ディレクトリを Lake に見せるため、`lakefile.lean` で章ごとに `lean_lib` を宣言している:

  ```lean
  @[default_target] lean_lib «7» where
    srcDir := "."
    globs := #[Glob.andSubmodules `«7»]
  ```

  新しい章を足すときは lakefile に 1 ブロック追加する。**ファイルを足すだけなら lakefile は触らなくてよい**
  （`Glob.andSubmodules` が自動で拾う）。

---

## 3. 命題ファイルの中身（テンプレート）

**すべての命題ファイルはこの形にする。** ヘッダは機械可読なので勝手に項目を減らさないこと。

**`import` は必ずファイルの一番上**（ドキュメントコメントより前）。Lean はそれ以外を受け付けない
（`invalid 'import' command, it must be used in the beginning of the file`）。

```lean
import PSS.Scb
import «7».«7.2-scb-compose»

/-!
# §7.2 命題（scb分解の一意性）

- 原文: `tmp/content.md` L982 付近（「命題（scb分解の一意性）」）
- 訂正: なし   ／ 訂正: A13（系(3) の出現位置は同一とは限らない）
- Isabelle: `p_7_2_scb_unique` (isabelle/pss_paper.thy:989) の証明は
            `m_7_2_scb_unique` (isabelle/pss_mechanized.thy:NNNN)
- 依存: PSS.Scb, «7».«7.2-scb-compose»
- 状態: 🚨 未証明   ／ ✅ 証明済（sorry 0）
-/

namespace PSS

/-- 原文（訂正 A13 適用後）の主張をそのまま述べる。 -/
theorem scb_unique ... := by
  sorry

end PSS
```

ルール:

1. **1 ファイル = 原文の 1 命題**。原文が「命題(1)(2)(3)」と枝分かれしていれば、
   Lean 側も 1 ファイルの中に `theorem foo_1`, `foo_2`, `foo_3` を並べる（ファイルは分けない）。
2. 証明に必要な補助補題は**そのファイル内に private で置く**。他の命題ファイルからも使うと分かった時点で
   `PSS/` の適切なモジュールに昇格させる。
3. **`sorry` を残したままコミットしてよい**（未証明は `task.md` で 🚨 として管理する）。
   ただし `sorry` を含むファイルの状態欄は必ず 🚨 のままにする。**緑＝ビルドが通る、ではない**。
   Lean はビルドが通っても `sorry` を warning で通す。**✅ の判定は §step.md の「緑の定義」に従う**。
4. 原文が偽の命題（`corrections.md` の A4/A16/A45/A46/A47 など）は、
   **訂正後の主張を主定理として書き、原文版が偽であることの反例定理を同じファイルに併記する**
   （`theorem foo_original_false : ¬ (...) := by decide` の形）。

---

## 4. 証明 Markdown ファイルの仕様

`.md` は `.lean` の短い紹介ではなく、**形式化とほぼ同じ粒度をもつ日本語の数学的証明**である。
読者が形式化や tactic を見なくても、仮定から結論までの各段階を検査できるように書く。

### 4.1 ファイルと基本構造

命題ファイル `lean/<章>/<節>-<name>.lean` に日本語証明を用意するときは、同じ場所に
同じ basename の `<節>-<name>.md` を置く。文献別ディレクトリでも同様に `.lean` と `.md` を対にする。

```markdown
[← Back](README.md)

# 日本語の定理名

<a id="scope-section-name"></a>
## 命題 [SCOPE-SECTION-NAME]

（仮定を省略しない命題文）

## 証明

（日本語と MathJax による証明）
```

- 本文は日本語で書く。原文と数学だけが存在するものとして記述し、Lean、tactic、宣言名、
  `simp` などの実装上の操作には言及しない。
- ただし証明方法、補題依存、帰納法、場合分け、証人の選び方は対応する形式化に沿わせる。
- MathJax は数式に使う。定理・補題の識別記号そのものは MathJax に入れず、ASCII の本文として書く。
- 完成した証明に `sorry`、「証明略」、「同様に従う」だけの穴を残さない。

### 4.2 命題記号

**定理、補題、系など、後から引用しうる全ての命題に一意な ASCII 記号を付ける。**
記号はリポジトリの `lean/**/*.md` 全体で重複させない。

記法は次の通りとする。

```text
<範囲>-<位置>-<短い意味名>[-<枝>]
```

- 使用文字は ASCII の大文字 `A-Z`、数字 `0-9`、ハイフン `-` のみ。
- 範囲には `PSS`、`BUC86`、`BUC87`、`BUC-REL-ORD`、`OTB` などを用いる。
- 原文の節番号はピリオドを使わず、`5-1`、`2-4B` のように埋め込む。
- 同じ定理の枝には `-1`、`-2`、`-NAT`、`-T` など、内容が分かる suffix を付ける。
- 数式番号 `(11)` や `(*)` はそのファイル内だけの番号であり、命題記号にはしない。
- 実装の履歴に由来する名前（例: `y4_bachmann_domB`）は使わず、数学的内容から安定した名前を付ける。

例:

```text
PSS-5-1-PARENT-EXISTS
BUC87-2-4B
OTB-BC-NAT
OTB-BC-T
OTB-WF
```

命題の直前には、記号を小文字化した明示的な ASCII anchor と、記号を含む見出しを置く。
見出しでは日本語の命題名を先に書き、ASCII 記号は末尾の角括弧内に置く。
日本語見出しから自動生成される anchor は、表記変更で壊れるため引用先に使わない。

```markdown
<a id="scope-section-name-branch"></a>
### 命題の枝 [SCOPE-SECTION-NAME-BRANCH]
```

定理記号を `\tag{...}`、下付き文字、ギリシャ文字などで組み立ててはならない。
証明途中の数式に、そのファイル内だけで使う `\tag{11}` のような番号を付けることはできる。

### 4.3 別ファイルの命題を引用する方法

**証明本文から別の `.md` にある命題を使う場合は、命題記号と、その命題の anchor への相対リンクを
必ず同時に書く。** ファイル先頭だけへのリンク、命題名だけ、局所的な式番号だけでは不可。

同じディレクトリの場合:

```markdown
Bachmann 共終性定理
[OTB-BC-NAT](OTB-well-founded-syntactic-cofinality.md#otb-bc-nat) より、……。
```

別のディレクトリの場合（例えば `OTB-well-founded-syntactic/` から
`Buchholz-1987/` を引用するとき）:

```markdown
[BUC87-2-4B](../Buchholz-1987/Buchholz-1987-2.4-2.8.md#buc87-2-4b)
の加法閉包を用いる。
```

同一ファイル内の命題も `[OTB-BC-W-NAT](#otb-bc-w-nat)` のように引用してよい。
章 README の `[lean]` / `[md]` は目次用のナビゲーションであり、この論理的引用規則の対象外とする。

### 4.4 証明の粒度

証明は、対応する形式化が本質的に行っている数学的推論を追跡できる粒度で書く。
コードの一行ごとの翻訳は不要だが、次の内容は省略しない。

1. 定理の全ての仮定と、実際に示す結論。
2. 使用する別命題の記号とリンク、およびそのどの結論を使うか。
3. 帰納法の対象、帰納法の強さ、帰納法の仮定、基底と各帰納段階。
4. 場合分けの基準と全ての分岐。分岐が尽くされている理由。
5. 存在命題の証人の構成と、その証人が各条件を満たす確認。
6. 定義の展開、等号による置換、不等式の推移、閉包性の適用など、結論へ進む非自明な一段。
7. 背理法では、仮定からどの式を経て何と矛盾するか。
8. 補助集合や関係を導入する場合、その定義、示すべき閉包条件、最終結論への接続。

例えば、次だけでは証明にならない。

> $`W_u`$ の最小不動点帰納法を用いれば従う。

少なくとも、可到達な項の集合 $`Y`$ を定め、$`A_u(Y)\subseteq Y`$ を示すことを宣言し、
零・数項定義域・$`T_m`$ 定義域の各生成分岐で、任意の前者が可到達になることを証明し、
最小性から $`W_u\subseteq Y`$ を結論するところまで書く。

一方、次のものは数学的内容を失わない範囲で省略またはまとめてよい。

- tactic の選択、型推論、名前空間、構文上だけ必要な型注釈。
- 命題としての真偽と Boolean 値 `= true` の間の定型的な変換。
- 同一の定義計算の機械的な反復。ただし、最初の一回は使った定義と計算結果を書く。
- 完全に同型な分岐。ただし対応関係と、変更される変数・仮定を明記する。

「明らか」「直ちに」「同様に」だけで非自明な推論を飛ばしてはならない。その語を使う場合も、
直後に根拠となる定義、既出式、または命題記号を書く。

### 4.5 完成時の点検

- 命題文が対応する `.lean` の定理と同じ仮定・量化・結論を持つ。
- 形式化の主要な補助補題、帰納法、場合分け、証人が Markdown でも追える。
- 別ファイルの命題参照が全て `[ASCII記号](相対パス#ascii-anchor)` になっている。
- 全命題に ASCII 記号と明示 anchor があり、記号が重複していない。
- MathJax の区切りが閉じており、リンク先が存在する。
- 実装名や tactic への言及、証明の省略、古いファイル名への参照が残っていない。

---

## 5. Isabelle 版との対応（移植元の探し方）

| 探すもの | 見る場所 |
|---|---|
| 原文の命題の**正確な文** | `tmp/content.md`（正本）／`isabelle/pss_paper.thy`（逐語転記＋英訳コメント） |
| その命題の**訂正** | `corrections.md`（30 件。A 番号で引く） |
| **我々の証明** | `isabelle/pss_mechanized.thy`（`m_*`）、`isabelle/layerB/pss_wip.thy`、`isabelle/layerC/pss_scratch.thy` |
| **証明の設計・死路** | `isabelle/memo.md`、`isabelle/docs/*.md`、`~/.claude/.../memory/*.md` |
| **反例・数値検証** | `python/red_model.py`, `python/trans_model.py`（正本）＋ `python/_*.py`（使い捨て調査） |

`isabelle/pss_paper.thy` の補題名は `p_<章>_<節>_<name>` という規則なので、
Lean のファイル名 `<節>-<name>.lean` と 1 対 1 に対応する。**これが移植の索引**。
