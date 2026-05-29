# dag.md — 証明依存関係 DAG (pair sequence system termination)

全命題・補題・定理を 1 つの DAG にしたもの。矢印は**論理含意の向き**：
`A → B` = 「A を使って B を証明」（A が前提・B が結論; A は B の依存先）。
基礎が最上段、最終目標 **§8.7 停止性定理** が最下段（sink）。

- 色: 🟩 緑 = 証明済 / 🟥 赤 = 未証明 / 🟧 橙 = 作業中・再定式化済
- §7/§8 のノード内エッジは粗く（節間依存のみ）。critical path・§6.5・§6.8 は詳細。

**▶ 拡大縮小できる対話版（dark mode）: [`dag.html`](dag.html)** をブラウザで開く
（ホイール=ズーム / ドラッグ=移動 / Fit・100% ボタン）。静的プレビュー ↓

![PSS proof dependency DAG](dag.svg)

> 図のソースは [`dag.dot`](dag.dot)（dark 配色）。更新フロー:
> ```
> unflatten -f -l 14 -c 2 dag.dot | dot -Tsvg -o dag.svg      # 静的(dark)
> unflatten -f -l 14 -c 2 dag.dot | dot -Tpng -Gdpi=90 -o dag.png
> python3 tools/build_dag_html.py    # dag.svg→ zoom 可能な dag.html を再生成
> ```
> dag.md にソースは置かない。節は箱を廃しラベル接頭辞（§x.y）で識別、幅 9022→5215pt(3:1)。

---

## critical path（人間用の要約）

```
基礎(§5,§6.1-6.4) → §6.2/§6.4/§6.7 → §6.8 prop1 → §8.2 切片Red強単項 → §8.7 停止性
                                          ↑
                              [d0pos 枝のみ未] ← d0pos infra Z5-Z9
```

- ★律速 = §6.8 prop1 の **d0pos 枝**（base/caseA/B/C 済）。Z1-Z4 ✅、Z5-Z9 残。
- 別系統 §6.5 Red: keystone `先祖Red不変` が T_PS で偽（A4）、`IncrFirst不変`/`Red·Pred可換`
  が **死枝[20]** 共有障壁。
- §7/§8 のノード内エッジは粗い（節間のみ）。詳細化は各命題の証明着手時に。
