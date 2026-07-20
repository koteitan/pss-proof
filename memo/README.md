# memo/ — 停止性証明に採用しなかった証明キャンペーン

`wds_collapse` に対する r52–r67 の distinguished-set / Buchholz–Schütte Fundierung 攻略を、
停止性のライブ依存木から分離して機械検査し続けるための Isabelle/HOL 資料。
実際に採用された整礎性証明は `bwl_` + `y4_bachmann` 経路である。

`PSS_MEMO` は `PSS_CORRECTIONS` を親に持つ独立セッションで、通常の `PSS_C` ビルドには含まれない。

| theory | 接頭辞 | handoff 事実数 |
|---|---|---:|
| `M_8_Wf_Bounded_Chain_Reductions` | `wfpx_`, `wfpd_` | 37 |
| `M_8_7_Wfs_Semantic_Rank` | `wfs_` | 38 |
| `M_8_7_Wfj_Level_Jump` | `wfj_` | 30 |
| `M_8_7_Wfc_Component_Jumps` | `wfc_` | 24 |
| `M_8_7_Wds_Distinguished_Sets` | `wds_` | 31 |
| `M_8_7_Wcl_Collapse_Obstruction` | `wcl_`, `wtw_` | 21 |
| `M_8_7_Bwo_Well_Ordering_Residue` | `bwo_` | 5 |

handoff の186事実に加え、相互帰納コマンドから不可分な `wfc_GBP_antitone` と
`wds_finite_GBP` も同行する。18件の `must_stay` はすべて `PSS_A` に残る。

```sh
cd isabelle
isbman build -d . -d ../corrections -d ../memo -v PSS_MEMO
```
