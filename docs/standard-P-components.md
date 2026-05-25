# §6.7 標準形の単項成分が標準形であること — 証明設計

`p_6_7_standard_P_components`: `M ∈ SkT_PS k ⟹ ∀J < Lng (P M). P M ! J ∈ SkT_PS k`
（同ランク `S_k`）。**原文証明はバグ**（corrections.md A6、content.md 1392 行は `S_{k-1}`
止まりで `S_k` に届かない）。命題自体は真（経験的に `python/sk_67_audit.py` で k≤5 違反0）。

## 全体構造：T と R を fold した同時帰納（辞書式測度 (k, Lng)）

**設計指針＝`bms-paper/tmp/simultaneous_induction_playbook.md`**: 相互依存する clause を
standalone に切り出すと同レベル循環で詰む（"IH が弱すぎる"病巣）。→ **連言 1 本・1 回の帰納**、
**level × 展開（=Lng）の辞書式測度**、index は `arbitrary:` で一般化。

当初 (R) を standalone 補題（`row1z_take_Pcut`, agent a12c）にしたが、(R) は T と末尾再帰
`P(M')_{J₀}[n]` を共有するので standalone は循環の恐れ。**playbook に従い (R) を T の第2連言に
fold-in**（a12c は停止）。verify-first（`python/sk_fold.py`）で fold した Φ は全 S_k 違反0、
唯一の新規 obligation（nonmulti-oper_1 の `Row1Zero(Pred M')`）も成立を確認済。

**fold した述語**（`X` を `arbitrary:` に、`k`×`Lng X` の辞書式で帰納）:
```
Φ(k, X) ≡  X ∈ SkT_PS k ⟶
            (T) (∀J < Lng (P X). P X ! J ∈ SkT_PS k)
          ∧ (R) (∀J < Lng (P X) - 1. Row1Zero (P X ! J))
```
IH は `∀(k',X'). (k',Lng X') <lex (k,Lng X) ⟶ Φ(k',X')`（leading は k'=k-1 で、末尾は同 k で
Lng 減少）。

補助補題（fold に使う道具）:
- **段1 `row1z_P_component`**（済, fa3db3b）: `Row1Zero M ⟹ Row1Zero (P M ! J)`。
- **(U) `SkT_row1z_up`**（agent aaf6, 継続）: `M∈SkT_PS k ⟹ Row1Zero M ⟹ M∈SkT_PS (Suc k)`。
  ＝ leading 成分 `∈S_{k'}`(IH の T) を `Row1Zero`(IH の R)＋(U) で `S_k` に持ち上げる道具。独立。

## Base k=0
`X = diagSeq u v`（u≤v）。`monoT (diagSeq u v)`（`monoT_diagSeq_append` 一般化）⟹ `¬multiT`
⟹ `poper_P_nonmulti`: `P X = [X]`。よって J=0 のみ、`P X!0 = X ∈ SkT_PS 0`。✓

## Step k = Suc k'  （IH_k: T(k') 成立）
`X ∈ SkT_PS(Suc k')` ⟹ `X = M'[n]`, `M'∈SkT_PS k'`, `1≤n`。
inner: `Lng X` 強帰納（IH_L: より短い `SkT_PS(Suc k')` の元で T が成立）。

### (a) M' が nonmulti（`P M' = [M']`）
nonmulti 基本列関係（`m_6_2_nonmulti_oper_1/2`）:
- **oper_2**（`¬((0,0)<^Next(0,j1))` または `M'_{1,j1}>0`）: `P(M'[n]) = [M'[n]] = [X]`。
  `P X!0 = X = M'[n] ∈ SkT_PS(Suc k')`。✓
- **oper_1**（`(0,0)<^Next(0,j1) ∧ M'_{1,j1}=0`）: `P(M'[n]) = (Pred M')` の n 個コピー。
  各成分 = `Pred M' = M'[1]`（`m_5_3_pred_is_oper1`, Lng M'>1）。`M'∈SkT_PS k', 1≤1`
  ⟹ `M'[1] ∈ SkT_PS(Suc k')`。✓  ← **(R)(U) 不要**。

### (b) M' が multiT（`P M'` が ≥2 成分、`J_0 := Lng(P M')-1 ≥ 1`）
最後の成分 `P M'!J_0` の長さで分岐（`poper` 関係(1)/(2)）。`P M'!J`（J<J_0）は **P M' の非末尾成分**。
- **先頭部分 `P M'!J`（J<J_0）の処理（両分岐共通）**:
  IH_k で `P M'!J ∈ SkT_PS k'`。(R)（multiT M' に適用、`butlast(P M')=P(take(Pcut M')M')`）
  ＋段1 で `Row1Zero (P M'!J)`。(U) で `P M'!J ∈ SkT_PS(Suc k')`。✓
- **(1) `Lng(P M'!J_0)=1`**: `P X = butlast(P M') = [P M'!0,…,P M'!(J_0-1)]`（全部先頭部分）。上で済。✓
- **(2) `Lng(P M'!J_0)>1`**: `P X = [P M'!0,…,P M'!(J_0-1)] @ P((P M'!J_0)[n])`。
  - 先頭部分: 上で済（(R)+(U)）。
  - 末尾 `P((P M'!J_0)[n])`: `P M'!J_0 ∈ SkT_PS k'`（IH_k）⟹ `(P M'!J_0)[n] ∈ SkT_PS(Suc k')`（1≤n）。
    `J_0≥1` ゆえ先頭部分は非空、`X = (concat 先頭) @ (P M'!J_0)[n]` より
    `Lng((P M'!J_0)[n]) < Lng X`。よって **IH_L**（inner 強帰納）を `(P M'!J_0)[n]` に適用、
    その P 成分が `SkT_PS(Suc k')`。✓  ← 末尾再帰は Lng で整礎。

## R 連言の per-case obligation（同じ場合分けで同時に閉じる）
- base k=0: `P X=[X]` 単成分 ⟹ 非末尾なし、R vacuous。
- nonmulti oper_2: `P X=[X]` 単成分 ⟹ R vacuous。
- **nonmulti oper_1**: `P X=[Pred M']×n`、非末尾＝`Pred M'`。**`Row1Zero(Pred M')`** が要る
  （verify-first で oper_1 条件下 3/3 成立）。← R の唯一の非自明 obligation。詰まれば focused agent。
- multiT (1): 非末尾 = `P M'` の非末尾 → IH の R(M') で Row1Zero。
- multiT (2): 非末尾 = `P M'` 非末尾（IH R(M')）＋ 末尾 `P((M')_{J₀}[n])` の非末尾（Lng 減少, 同 k の IH R）。

## 必要な道具（既証明）
`poper_P_multi`/`poper_P_nonmulti`/`poper_last_P_multi`（last/butlast 構造）、
`m_6_2_nonmulti_oper_1/2`、`m_5_3_pred_is_oper1`（`Pred M = M[1]`）、`poper_oper_*`、
関係(2)の `P(M'[n]) = butlast(P M') @ P((P M'!J_0)[n])` を与える poper 補題（要特定 or 組立）、
`monoT_diagSeq_append`（base）、append の nth（`nth_append`）でインデックス処理。

## 統合順序
agent a12c (R) と aaf6 (U) が緑で戻る → 親が行範囲抽出して main へ → `Finished PSS` 検証 →
T(k)（本ファイルの構造）を `m_6_7_standard_P_components` として書き、`p_6_7_standard_P_components`
を discharge。push は明示指示時のみ。
