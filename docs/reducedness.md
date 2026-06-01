# §6.6 簡約性 (Reducedness, RT_PS = Im(Red))

簡約 = `Red M = M`; `RT_PS = {M ∈ T_PS | Red M = M} = Im(Red)`.
命題（簡約性と係数の関係）: `M` reduced ⟺ `RedCondA M ∧ RedCondB M` (pss_defs:
`RedCondA` 422, `RedCondB` 426). 設計記録 (understand workflow, 2026-06-01).

## 依存マップ — A4非依存 vs §6.5-blocked

| §6.6 fact | article 依存 | 分類 |
|---|---|---|
| (a) 補題（Red と左端の関係） | Red 定義 unfold のみ | **A4非依存**（(1) は `m_6_6_Red_leftend_1` 既green; (2) 対角前置の値） |
| (b) 補題（簡約性と係数の基本性質）reduced⟹M₀ⱼ≥M₁ⱼ | — | **微妙**: Red 直接 unfold だと mono非core m10>0 が branch[17]/[19]/[20]→`p_6_5_Red_monoT`(A4)。(c) 経由なら回避可 |
| (c) 補題（条件(A)(B)と係数の基本性質） | nextrel/hasParent/parent 一意性のみ（**Red 不使用**） | **A4非依存（確実）**。keystone の workhorse |
| (e) 補題（簡約性と左端の関係） | (a)(2) + Red の IncrFirst/対角前置不変性（既green族） | **A4非依存** |
| **(d) 命題（簡約性と係数の関係）= reduced⟺RedCondA∧RedCondB** | (a)(b)(c)(e) + Red 定義 + IncrFirst不変 + P 定義（**Red_le/Red_monoT/P_Red 非引用**） | **A4非依存（agent A 主張、877/0）** ← §6.5 が必要とする keystone |
| (f) 簡約性の切片への遺伝性 | Red_Pred (§6.5) + **A5 域補正**（22 literal 反例） | **blocked** |
| (g) P が簡約性を保つ | P_Red (§6.5 A4) | **blocked** |
| (h) 簡約性が基本列で保たれる | Red_idem + Red_oper (§6.5 A4) | **blocked** |

## 🔑 決定的な lead: RedCondA ⟹ red_le (877/0, 全 T_PS)

経験的に **`RedCondA M ⟹ (leR M = leR (Red M))` が全 T_PS で 877/0**（BC より強い）。
§6.5 の 5 core-nontrunk breaker（`(0,0)(1,1)(1,2)(2,2)` 等）は**全て RedCondA 違反**＝
RedCondA が正確に分離。よって keystone (d) が証明できれば:
**reduced ⊆ RedCondA ⟹ red_le** で、§6.5 Red_le が固定不変量 pinduct 無しで従う
（既存 `RedCondA⟹BC` / `le0end_imp_brle` 連鎖経由）。§6.6 keystone が §6.5 bottleneck を解く。

## 証明プログラム（A4非依存、bottom-up）

1. (a) Red と左端の関係 — (1) 既green、(2) 対角前置の値を追加。
2. (c) **条件(A)(B)と係数の基本性質**（純 nextrel、Red 不使用、両エージェント一致でA4非依存）
   = `M_{0,j}≤j`; `M0=(0,0)∧RedCondA∧RedCondB ⟹ M_{0,j}≥M_{1,j}`; 非le0証人下で `M_{i,j}<j`。
   §6.4 idxsum parent 一意性を再利用。**最初に着手すべき安全な基盤**。
3. (e) 簡約性と左端の関係 — (a)(2) + IncrFirst不変族。
4. (b) reduced⟹row0≥row1 — (c)(2) + keystone 経由（直接 unfold の A4 を回避）。
5. **(d) keystone reduced⟺RedCondA∧RedCondB** — j₁ 帰納、(a)(c)(e)+Red定義+IncrFirst不変+P定義。
   BACKWARD 方向は auxiliary (＊)（content.md 1224）で mono非core を core へ引き戻す。
   ⚠️ agent B 警告: 直接 unfold は A4 に当たる。agent A の core 引き戻しが A4 を回避するか
   **統合時に自己引用監査必須**（§6.5 fan-out の循環偽証明の再発防止）。

## green 済
- `m_6_6_rebase_row0_ge_row1`（branch-6 rebase 出力の row0≥row1、純代数、A4非依存）。
  branch-6 が fire した後（p_6_5_Red_monoT 後）に reduced_coeff の最難ケースを modus ponens で閉じる部品。

経験: `RedCondA⟹red_le` 877/0、reduced⟹RedCondA 286/0、reduced⟹RedCondB 286/0、
(A∧B)∧¬reduced 0、死枝[20] 0/7380。

## 7. 構造的発見 (2026-06-01): §6.5/§6.6 は dead-branch[20] で循環

(c) `m_6_6_condAB_coeff` は既 green（A4非依存、純 nextrel）と確認。残るは keystone (d)
と前提 (a)(2)/(e)。だが **§6.5/§6.6 cluster は循環的に絡む**:

```
Red_le ──needs──▶ RedCondA ──needs──▶ keystone(d) reduced⟺RedCondA∧RedCondB
  ▲                                          │ backward 方向
  │                                          ▼ (mono非core m10>0 を Red 展開)
  └──────── dead-branch[20]不到達 ◀──needs── Red_monoT (= productive branch fires)
            (= p_6_5_monoT_Red, 経験的真 344/0)
```

- keystone (d) の backward (RedCondA∧RedCondB ⟹ reduced) は mono非core m10>0 で Red を
  展開し branch[17]/[18] が fire する＝`p_6_5_Red_monoT`（dead-branch[20]不到達）に依存
  （agent B の警告、agent A は core 引き戻しで回避と主張＝**未決着**）。
- dead-branch[20]不到達 (`p_6_5_monoT_Red`) は §6.5 で Red_le を必要とする。
- Red_le は RedCondA を必要とする（lead: RedCondA⟹red_le 877/0）。

**循環を破る直接エントリが必要**（新しい数学的アイデア。brute fan-out では循環偽証明を
生むだけ＝§6.5 fan-out の既知失敗）。候補:
- **(α)** dead-branch[20]不到達 を coefficient 構造から直接証明（Red_le 経由せず）。(c)
  condAB_coeff の係数限界 `M_{0,j}≤j`, `M_{1,j}<j` で seg(N,m10,jN) の monoT 性
  （=productive 条件）を直接導けるか。
- **(β)** keystone backward を mono非core で condAB_coeff の係数限界経由で閉じ、Red_monoT
  を迂回（agent A 主張の精査）。
- どちらか1つが A4非依存で閉じれば循環全体が解ける。

→ 次: (α)/(β) の実現可能性を read-only で精査（proving 前に循環回避を確認）。
