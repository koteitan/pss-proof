# §7.3 翻訳写像 Trans / Mark — 設計メモ

ペア数列 → Buchholz 表記系への翻訳写像 `Trans` と、その部分文字列計算補助
`Mark` の定義（原文 content.md **2044–2180**「翻訳写像」）の形式化設計。
本プロジェクト最複雑の定義（task #4）。`Red` 同様、停止性は後回し（`domintros`）。

## シグネチャ

```
Trans :: pairseq ⇒ BT                    -- Trans M
Mark  :: pairseq ⇒ nat ⇒ BT              -- Mark M m   （(M,m) ∈ T_PS^Marked 上）
```

相互再帰（`Trans` が `Mark` を呼び、`Mark` が `Trans`/`Mark` を呼ぶ）。原文の
不変条件は `(Trans M, Mark M m) ∈ T_B^Marked`（= `MarkedB`、§7.2 で定義済）。

## 依存（すべて形式化済み）

| 記号 | Isabelle | 所在 |
|---|---|---|
| `0` (Buchholz) | `0⇩B = Trm []` | pss_paper §7.1 |
| `D_v t` | `Trm [DB v t]`（`v :: enat`） | pss_paper §7.1 |
| `a + b` | `addBT` (`+⇩B`) | pss_paper §7.1 |
| `P_B`, `Σ_B` | `PB`, `SigmaB` | pss_paper §7.1 |
| scb分解 | `scb_decomp` / `scb_kind0/1` | pss_paper §7.2 |
| `T_B^Marked` | `MarkedB` | pss_paper §7.2 |
| `Adm_M(j)` | `Adm M j`（`adm`/`AdmSet`） | pss_defs §6.3 |
| `Red`, `Pred`, `P`, `seg` | 同名 | pss_defs |
| `RT_PS`, monoT/multiT/zeroT | 同名 | pss_defs |
| `i_1 = idx1`, `j_0 = parent`, `≤_M = leR` | 同名 | pss_defs |

注意: `D_v` の添字 `v` は `enat`（Buchholz は超限）。ペア数列側の係数 `M_{1,j}`
は `nat` なので `enat` への埋め込み（`enat (M_{1,j})`）が要る。

## 定義の場合分け（原文忠実、Lng M 帰納）

`j1 := Lng M - 1`。

### (A) `M ∈ RT_PS ∧ j1 = 0`（簡約・長さ1）
- `M_0 = (0,0)`: `Trans M = 0`,  `Mark M m = 0`。
- `M_0 ≠ (0,0)`: `Trans M = D_{M_{1,0}} 0`,  `Mark M m = D_{M_{1,0}} 0`。

### (B) `M ∈ RT_PS ∧ monoT M ∧ j1 > 0`（簡約・単項）
`t1 := Trans (Pred M)`。
- **t1 = 0**: `Trans M = D_0 D_{M_{1,j1}} 0`;
  `Mark M m = (if m = 0 then D_0 D_{M_{1,j1}} 0 else D_{M_{1,j1}} 0)`。
- **t1 ≠ 0**: 補助量
  - `i1 := idx1 M j1`（= max{i∈{0,1}|M_{i,j1}>0}）, `j0 := parent M (?) j1`
    （原文 `j0 := max{j<j1 | (0,j)≤_M(0,j1)}` = row-0 の直近祖先）, `j_{-1} := Adm M j0`。
  - 排反条件 (I)–(VI)（原文 2096–2106）:
    - (I)  `M_{1,j1}=0 ∧ adm M j0`
    - (II) `M_{1,j1}=0 ∧ ¬adm M j0`
    - (III) `M_{1,j1}>0 ∧ M_{1,j0}≥M_{1,j1} ∧ adm M j0`
    - (IV) `M_{1,j1}>0 ∧ M_{1,j0}≥M_{1,j1} ∧ ¬adm M j0`
    - (V)  `M_{1,j1}>0 ∧ M_{1,j0}+1=M_{1,j1} ∧ j0+1<j1`
    - (VI) `M_{1,j1}>0 ∧ M_{1,j0}+1=M_{1,j1} ∧ j0+1=j1`
  - `c1 := Mark (Pred M) j_{-1}`。`(t1,c1)∈MarkedB ∧ t1≠0` より scb分解一意 (1)
    で `(s1,b1)` 一意: `(s1, c1, b1)` は `t1` の scb分解。`c1 = D_v t2` と置く。
    `J1 := Lng (PB t2) - 1`。
  - `c2` を条件で:
    - (I)/(III)/(V): `c2 := D_v (t2 + D_{M_{1,j1}} 0)`
    - (II)/(IV): `t2=0` なら `c2 := D_v D_{M_{1,j0}} D_{M_{1,j1}} 0`;
      `t2≠0` なら `PB(t2)_{J1}` の左端が `D_{M_{1,j0}}` か否かで
      `t3,t4` を定め（左端 `D_{M_{1,j0}}`: `t3:=Σ_B (PB(t2)_J)_{J=0}^{J1-1}`,
      `PB(t2)_{J1}=D_{M_{1,j0}} t4`; 否: `t3:=t2`, `t4:=t2`）、
      `c2 := D_v (t3 + D_{M_{1,j0}}(t4 + D_{M_{1,j1}} 0))`
    - (VI): `c2 := D_v D_{M_{1,j1}} 0`
  - `Trans M := s1 c2 b1`（連接 = `SigmaB`/`addBT` 表現要）。
  - `Mark M m`:
    - `m < j1`: `c0 := Mark (Pred M) m`。
      `(c0,c1)∈MarkedB` なら `(s0,b0)` で `(s0,c0,b0)` が `t1` の scb分解、
      `(s_{-1},b_{-1})` で `(s_{-1},c1,b_{-1})` が `c0` の scb分解、
      `Mark M m := s_{-1} c2 b_{-1}`。
      `(c0,c1)∉MarkedB` なら `Mark M m := D_{M_{1,j1}} 0`。
    - `m = j1`: `Mark M m := D_{M_{1,j1}} 0`。

### (C) `M ∈ RT_PS ∧ multiT M`（簡約・複項）
`J1 := Lng (P M) - 1`, `j0 := j1 - Lng (P(M)_{J1}) + 1`。
- `P(M)_{J1} = ((0,0))`:
  `Trans M = Trans (seg M 0 (j0-1)) + D_0 0`,  `Mark M m = D_0 0`。
- 否:
  `Trans M = Trans (seg M 0 (j0-1)) + Trans (P(M)_{J1})`,
  `Mark M m = Mark (P(M)_{J1}) (m - j0)`。

### (D) `M ∉ RT_PS`（非簡約）
`Trans M = Trans (Red M)`,  `Mark M m = Mark (Red M) m`。

## 停止性（測度）

原文「Lng(M) に関する数学的帰納法より即座」。Isabelle では `Red`/`operB` と
同じく **`function (domintros)` で定義し termination を後回し**にするのが安全。
測度の見立て（`lex` on `(reduced?, Lng M)` のような）:
- (D) 非簡約 → `Red M`（簡約、Lng 同じ）: 「非簡約 > 簡約」の第1成分で減少。
- (A) 再帰なし。
- (B) `Pred M`（Lng 減）。`Mark` の `m<j1` は `Pred M`（Lng 減）。
- (C) `seg M 0 (j0-1)`（Lng 減, j0≥1 要確認）, `P(M)_{J1}`（成分, Lng 減）。
よって測度 `(¬RedCond? の 0/1, Lng M)` の辞書式で減少。`Red` の `Red_dom`✅と
同様に `Trans_dom`/`Mark_dom` を後で証明（または `domintros` のまま条件付き使用）。

連接 `s1 c2 b1` の表現: `s1,b1 ∈ Σ^{<ω}`（記号列）。当方は `BT` で扱うので、
原文の「`t` の scb分解 `(s,c,b)` に対し `s c' b`」を **`BT` レベルの操作**
（`c1=D_v t2` の `t2` を `c2`-由来の項で置換）として実装する必要がある。
具体的には `Trans M = s1 c2 b1` は「`t1` の最右主部 `c1=D_v t2` を `c2` で
置換した項」に相当（scb分解の定義 §7.2 と突き合わせて確定する）。**ここが
形式化の要注意点**: 記号列 `Σ^{<ω}` ベースの連接を `BT` の構造操作へ翻訳する。

## 形式化の段取り（worktree）

1. `D` 記法（`abbreviation Dpt v t ≡ Trm [DB v t]` 等）と `enat` 埋め込みヘルパ。
2. 条件 (I)–(VI) を `bool` 述語として定義（`condI M … condVI M`）。
3. scb分解の一意性（§7.2 命題、要証明 or 仮定）から `(s1,b1)` 取り出しヘルパ。
   → `s1 c2 b1` を `BT` 操作で実装する `scb_subst c1 c2`（最右主部置換）等。
4. `function (domintros) Trans / Mark` を相互再帰で定義。
5. `Trans_dom` 整礎測度（`(¬reduced, Lng)` 辞書式）で termination（後回し可）。
6. §7.3/7.4 命題を pss_paper に sorry 転記（定義確定後に解禁）。

## 忠実性論点（要確認）

- `j0` の定義: 原文 `max{j<j1|(0,j)≤_M(0,j1)}` は `parent M (idx1 M j1) j1` と
  一致するか（row-0 parent。§6.2 の `parent` と突合）。**確認要**。
- scb分解一意性 (1)/(B) は §7.2 命題（未証明）。Trans 定義はこれに依存するので、
  定義段階では `scb_decomp` の存在のみ使い、一意性は別途。
- `s1 c2 b1` の `BT` 表現（上記）。
- (B) の `Mark` の `(c0,c1)∈MarkedB` 分岐の `s_{-1},b_{-1}`。

## 形式化済み（2026-05-27, main 統合・緑）

`Trans`/`Mark` を pss_paper.thy §7.3 に**相互再帰 `function`** として定義（緑）。
termination は `by pat_completeness auto` で後回し（`RightNodes`/`Red`/`domB` 同様、
条件付き `Trans.psimps`/`Mark.psimps` のまま）。追加した補助:
- `Dpt v t = Trm [DB v t]`（`D_v t`、`v::enat`、ペア側係数は `enat (entry M 1 j)`）。
- `transCondI..transCondVI`（条件 (I)–(VI)、`j_0 = parent M 0 j_1` でモデル）。
- `unflatBT xs = (THE t. flatBT t = xs)`（`s c b` 連接＝`flat` 単射性で一意な BT）。
- `bpHeadV`/`bpHeadT`（主部 `D_v t` の `v`/`t` 抽出、`c_1=D_v t_2` と `P_B(t_2)_{J_1}`
  の左端判定に使用）。
- `scb` 分解の `(s,b)` 取り出しは `SOME sb. scb_decomp … (fst sb) (flat c1) (snd sb)`。

**未証明（次の段階）**: 命題（Trans の well-defined 性, 2182）= 定義が一意に存在
（termination ＋ THE/SOME が正しい項を選ぶこと）。§7.3 の残り命題群・§7.4・§8 の
statement 転記はこの定義の上で解禁。**残る忠実性確認**: `j_0` の `parent` モデル、
`s1 c2 b1` の `unflatBT` 表現が原文の意図（最右主部 `c_1` を `c_2` に置換）と一致するか。
