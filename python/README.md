# python/ — ペア数列システムの忠実な実行モデル

`pss_defs.thy` の定義を Python に 1:1 移植した**実行可能モデル**と、それを使って
論文（「ペア数列の停止性」）の命題を**経験的に検証**するスクリプト群。Isabelle で
証明に着手する前に、反例の発見・成立域の見積もりに使う。

ペア数列は `[(a,b), ...]`（`a`=行0, `b`=行1）のタプルのリスト。列がペア＝2行
バシク行列の各列に対応する。

## ファイル

| file | 役割 |
|---|---|
| `red_model.py` | **コア**。`pss_defs.thy` の忠実移植：`entry`/`Lng`、`nextrel0/1`・`le0/le1/leR`、`zeroT`/`monoT`/`multiT`、`Pcut`/`P`、`TrMax`/`Br`/`FirstNodes`/`Joints`、`diagSeq`/`IncrFirst`、`oper`(M[n])、`Pred`、`Red`。補助：`reduced`(=RT_PS)、`is_standard`(yaBMS 経由)、`red_le_holds`、`Red_trace`(再帰引数を記録)、`fmt` |
| `red_audit.py` | §6.5/§6.6 の各命題を全 `T_PS`(Lng≤4,成分≤2) で検証し、偽な命題を最小反例つきで列挙 |
| `red_anchor2.py` | `Red_le` 等5命題を**先祖係留切片**(`le0(S,a,b)` の `seg(S,a,b)`) で検証（標準形ソース／簡約+単項ソース） |
| `red_domain.py` | 成立域候補（標準形/簡約済の切片、行0シフト同一視）の sound 性・閉包性を比較 |
| `red_charac.py` | `RedCondA`/`RedCondB`(=簡約性) による `Red_le` の特徴付け |
| `red_mono.py` | `Red_le` 失敗を zero/mono/multi 別に集計 |

## 実行

```bash
cd python
python3 red_model.py        # 自己テスト（Red_le の反例 (0,0)(0,1) を表示）
python3 red_audit.py        # T_PS 上で偽な命題の一覧
python3 red_anchor2.py      # 係留切片での5命題の sound 性
```

`is_standard` は外部 C ツール **yaBMS**（`bms -s`）に委譲する（このモデルとは独立な
標準形判定オラクル）。既定パスは `../tmp/yaBMS/c/bms`。別の場所にあるなら環境変数で：

```bash
BMS_BIN=/path/to/bms python3 red_audit.py
```

yaBMS を使わないスクリプト（`red_anchor2.py` の標準形は対角線からの展開＝定義上
`ST_PS`、`red_mono.py`、`red_charac.py`）は yaBMS 不要。

## 主要な知見（このモデルで確定したこと）

- 論文 §6.5 の **`Red_le`（直系先祖の Red 不変性）と派生系
  `Red_monoT`/`P_Red`/`Red_idem`/`Red_oper` は、論文が言明する `T_PS` 全体では偽**。
  最小反例 `Red((0,0)(0,1)) = (0,0)(1,1)`（行0祖先木が変わる）。amendment **A4**。
- 一方これらは **「標準形（または簡約+単項）の先祖係留切片」`(0,a)≤_M(0,b)`**
  上では成立（検証範囲で失敗ゼロ）。これは §7 が実際に Red 系を適用する `N` の類
  （命題1422 の前提）と一致。詳細は [`../docs/red-le-domain.md`](../docs/red-le-domain.md)。

## 限界

経験的・有界列挙（網羅は Lng≤4・成分≤2、それ以上は展開でサンプル）。**証明ではない**。
反例の発見は確実、成立側は検証範囲での強い証拠。最終的な保証は Isabelle 側の証明で与える。
</content>
