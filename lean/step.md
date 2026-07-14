# step.md — 作業手順

構造は [spec.md](spec.md)、進捗は [task.md](task.md)、設計は [memo.md](memo.md)、
Lean サーバは [kimina.md](kimina.md)。**このファイルは「1 命題を片付ける手続き」を定める。**

---

## 0. セッション開始時（毎回やる）

```sh
cd ~/proofs/pss-proof/git

# 1) Lean プロジェクトが緑か
cd lean && lake build && cd ..

# 2) kimina サーバが上がっているか（上がっていなければ起動）
pgrep -f "python -m server" >/dev/null || \
  (cd ../kimina-lean-server && setsid nohup .venv/bin/python -m server > /tmp/kimina-pss.log 2>&1 &)

# 3) 疎通
python3 python/check_lean.py -  <<< 'import PSS.Defs
#check @PSS.Lng'
```

`lean/task.md` を読んで 🚨 の中から次の標的を選ぶ。**上から順に潰す**（下流は上流に依存する）。

---

## 1. 「緑」の定義（★ここを間違えると全部無駄になる）

Isabelle 版で最も高くついた事故は **「緑＝証明できた」と誤認すること**だった。Lean はもっと危ない:
**`sorry` を含むファイルでも `lake build` は成功する**（warning にしかならない）。

**✅ の条件は次の 3 つを全部満たすこと:**

1. `python3 python/check_lean.py lean/<file>.lean` の **終了コードが 0**
   （= error 0 件 **かつ** `sorry` 0 件。`grep sorry` では `sorryAx` を経由した依存を見逃す）。
2. `#print axioms <定理名>` が **`sorryAx` を含まない**。
   ```lean
   #print axioms PSS.scb_unique
   -- 'PSS.scb_unique' depends on axioms: [propext, Classical.choice, Quot.sound]  ← これならOK
   -- ... [sorryAx] を含んだら未証明
   ```
   **これが Isabelle の ML 監査に相当する唯一の防御線**。各ファイルの末尾に必ず 1 行置く。
3. **主張が原文（訂正後）と一致している**。
   別の命題を正しく証明しても価値はゼロ。`tmp/content.md` と `corrections.md` を突き合わせる。

`lake build` が通っただけでは 1 も 2 も保証されない。**`lake build` を根拠に ✅ を付けてはならない。**

---

## 2. 1 命題を片付ける手順

### (a) 標的を決める

`lean/task.md` の 🚨 から 1 つ。ツリーの行が Lean のファイル 1 つに対応している。

### (b) 原文の主張を取る

```sh
grep -n "命題（scb分解の一意性）" tmp/content.md      # 原文の位置
grep -n "p_7_2_scb_unique" isabelle/pss_paper.thy    # 逐語転記＋英訳コメント
grep -n "A13" corrections.md                          # 訂正が効いているか
```

**必ず `corrections.md` を見る。** 原文には 30 件の誤りがあり、そのままの主張は偽のことがある。
訂正が効く命題は「訂正後の主張」を Lean に書く。

### (c) 我々の証明を読む

```sh
grep -n "m_7_2_scb_unique" isabelle/pss_mechanized.thy isabelle/layerB/*.thy isabelle/layerC/*.thy
```

Isabelle 側の証明は **設計図として読む**（タクティクの逐語移植はできない）。見るべきは
「どの補題に還元したか」「どの帰納法を回したか」「どの罠を避けたか」。
死路の記録は `isabelle/memo.md` と `isabelle/docs/*.md` にある。**同じ死路を再走するな。**

### (d) 書く

`lean/<章>/<節>-<name>.lean` を spec.md §3 のテンプレートで作る。ヘッダは必須。

### (e) 検証する

```sh
python3 python/check_lean.py lean/7/7.2-scb-unique.lean   # rc=0 でなければ ✅ にしない
```

`lake build` はファイルを増やしたとき／統合時にだけ回せばよい（遅い）。**日常の試行錯誤は kimina。**

### (f) 記録する

- `lean/task.md` の該当行を 🚨 → ✅ にする（**task.md と memo.md の両方**を同じコミットで直す）。
- 原文の誤りを新しく見つけたら `corrections.md` に追記する（A 番号は連番、既存の番号を再利用しない）。
  形式は corrections.md 冒頭の注意事項に従う（**原文＝逐語引用、訂正案＝置き換え後の本文そのもの**）。
- コミットする（緑のときだけ）。push は自由。

---

## 3. 数値検証（証明を書く前にやる）

**怪しい命題は先に反例を探す。** 原文の誤り 30 件のうち多くは、証明を書き始める前に
`python/` のモデルを回していれば数分で分かった。

```sh
python3 -c "
from python.red_model import Red, reduced   # 正本
..."
```

- 正本は `python/red_model.py`（`Red` は **タプルのリスト**を返す。リストのリストと比較すると
  黙って全部不一致になる — 実際に踏んだ）と `python/trans_model.py`。
- **成分の上限を小さく取るな。** 反例の 4 件は「成分 < 3」「成分 < 4」で走査したせいで見逃していた。
  **成分は 8 以上、長さは 6 以上**まで回す。加えて **本物の標準形**（`diagSeq` を基本列で閉じたもの）
  を混ぜる。ランダムなペア数列はほぼ簡約形にならないので、乱択だけでは検証にならない。

---

## 4. 並列化（workflow）

**Agent ツールは使わない。並列化は `Workflow` のみ**（CLAUDE.md）。
各エージェントは `lake build` ではなく kimina を使う（[kimina.md §4](kimina.md)）。

1 ラウンド = 独立な命題を 4〜8 本、`pipeline(port → verify)` で流す。**verify フェーズを省くな**:
Isabelle 版で頻発した事故は「未緑なのに緑と自己申告」と「**別の命題**を証明していた」の 2 つで、
どちらも verify エージェントに `check_lean.py` の生出力と原文の突き合わせを要求すれば止まる。

エージェントが触ってよいのは **自分の担当ファイル 1 つだけ**。
`lean/task.md` / `lean/memo.md` / `corrections.md` / `PSS/*.lean` は**親だけが編集する**
（`PSS/` を各エージェントに書かせると衝突して全滅する）。
共有補題が必要になったらエージェントは「PSS/Red.lean に ○○ が要る」と**報告する**だけにする。

---

## 5. Isabelle 側（`isabelle/`）

停止性定理は **証明済・凍結**。触る必要は原則ない。ビルドを確認したいときだけ:

```sh
cd isabelle && isbman build -d . -v PSS_C
grep -c 'Finished PSS_C' <ログ>   # == 1、かつ '^\*\*\*' が 0、かつ 'AUDIT FAILED' が 0 で緑
```

`tail` で緑を判定してはいけない（実際にエラー行を切り落として誤判定した）。
