# §6.7 標準形の単項成分が標準形であること — 証明設計

`p_6_7_standard_P_components`: `M ∈ SkT_PS k ⟹ ∀J < Lng (P M). P M ! J ∈ SkT_PS k`
（同ランク `S_k`）。**原文証明はバグ**（corrections.md A6、content.md 1392 行は `S_{k-1}`
止まりで `S_k` に届かない）。命題自体は真（経験的に `python/sk_67_audit.py` で k≤5 違反0）。

## 全体構造：単調性 `SkT_PS_mono` を使った `k × Lng` 辞書式帰納（Row1Zero 不要）

> **重要な経緯**: 当初「単調性 $`S_{k-1}\subseteq S_k`$ は偽」と誤判断し、Row1Zero 経由の補強 (R)/(U) を
> 設計した（playbook で T と fold する計画）。しかし**単調性は真**（私の経験検証が truncation
> アーティファクトだった）。agent が `SkT_PS_mono` を発見・私が完成（緑、0669768）。
> **単調性があれば Row1Zero は丸ごと不要**。corrections.md A6 も訂正済。

**証明済の鍵補題 `SkT_PS_mono: SkT_PS k ⊆ SkT_PS (Suc k)`**（`pss_mechanized.thy`）。
base 証人 `diagSeq u v = (diagSeq u (Suc v))[1] = Pred(diagSeq u (Suc v))`、一般 k は帰納。

**T(k)** := `∀X∈SkT_PS k. ∀J<Lng(P X). P X!J ∈ SkT_PS k`。`k` の外帰納 × Suc 内の `Lng X` 強帰納
（`X` を `arbitrary:`）。leading 成分は IH(k-1) で `∈S_{k-1}`、**`SkT_PS_mono` で `S_k` に持ち上げ**。
末尾は `Lng` 減少で内側 IH。

道具:
- `SkT_PS_mono`（済）: `S_{k-1} ⊆ S_k`。leading 成分の持ち上げに使う唯一の鍵。
- 基本列関係（既証明 `poper_*` / `m_6_2_nonmulti_oper_1/2` / `m_5_3_pred_is_oper1`）。
- ~~段1 `row1z_P_component`, `Row1Zero`, (R), (U)~~ → **単調性により不要**（`row1z_P_component`/`Row1Zero`
  は現状 dead code、後で除去可）。

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
  IH_k で `P M'!J ∈ SkT_PS k'`。**`SkT_PS_mono` で `P M'!J ∈ SkT_PS(Suc k')`**。✓（Row1Zero 不要）
- **(1) `Lng(P M'!J_0)=1`**: `P X = butlast(P M') = [P M'!0,…,P M'!(J_0-1)]`（全部先頭部分）。上で済。✓
- **(2) `Lng(P M'!J_0)>1`**: `P X = [P M'!0,…,P M'!(J_0-1)] @ P((P M'!J_0)[n])`。
  - 先頭部分: 上で済（IH_k + mono）。
  - 末尾 `P((P M'!J_0)[n])`: `P M'!J_0 ∈ SkT_PS k'`（IH_k）⟹ `(P M'!J_0)[n] ∈ SkT_PS(Suc k')`（1≤n）。
    `J_0≥1` ゆえ先頭部分は非空、`X = (concat 先頭) @ (P M'!J_0)[n]` より
    `Lng((P M'!J_0)[n]) < Lng X`。よって **IH_L**（inner 強帰納）を `(P M'!J_0)[n]` に適用、
    その P 成分が `SkT_PS(Suc k')`。✓  ← 末尾再帰は Lng で整礎。

## 必要な道具（既証明）
`SkT_PS_mono`（leading 持ち上げ）、`poper_P_multi`/`poper_P_nonmulti`/`poper_last_P_multi`（last/butlast 構造）、
`m_6_2_nonmulti_oper_1/2`、`m_5_3_pred_is_oper1`（`Pred M = M[1]`）、`poper_oper_*`、
関係(2)の `P(M'[n]) = butlast(P M') @ P((P M'!J_0)[n])` を与える poper 補題（要特定 or 組立）、
append の nth（`nth_append`）でインデックス処理。

## 実装順序
`SkT_PS_mono`（済, 0669768）の上で T(k) を `m_6_7_standard_P_components` として書き、
`p_6_7_standard_P_components` を discharge。push は明示指示時のみ。
（`Row1Zero`/`row1z_P_component` は単調性により dead code。後で除去可。）
