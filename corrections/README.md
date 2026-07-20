# corrections/ — 機械検査済みの反例・経験検証資料

停止性証明と原文命題カバレッジの依存木から独立した、反例および経験検証の Isabelle/HOL 資料。
`PSS_CORRECTIONS` は `PSS_A` を親に持つ独立セッションで、通常の `PSS_C` ビルドには含まれない。

| theory | 内容 | 移動した名前付き事実 |
|---|---|---:|
| `C_7_3_Red_Admissibility_Counterexample` | Red² による許容性保存ルートの反例 | 36 |
| `C_7_4_Mark_NextAdm_Counterexample` | §7.4 Mark / NextAdm 系の反例と機械計算 | 96 |

handoff の100事実に加え、それらへ依存していた停止性非到達の `y3z_*` 2事実と `y6B*` 30事実も、
ライブ木に重複を残さないため逆依存閉包として移動した（合計132事実）。

```sh
cd isabelle
isbman build -d . -d ../corrections -v PSS_CORRECTIONS
```
