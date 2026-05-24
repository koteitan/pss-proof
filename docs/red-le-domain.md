# §6.5 `Red_le`（直系先祖の Red 不変性）ほかの定義域問題

論文 §6.5 の系「直系先祖の $\textrm{Red}$ 不変性」（= `p_6_5_Red_le`）

> 任意の $M \in T_{\textrm{PS}}$ に対し、$\le_M$ と $\le_{\textrm{Red}(M)}$ は一致する。
> 証明: Lng の Red 不変性と Red の再帰的定義により、$\textrm{Lng}(M)$ に関する
> 数学的帰納法から即座に従う。

の**前提 $T_{\textrm{PS}}$ は広すぎ**、命題は文字通りには偽。proposed correction **A4**
（`corrections.md`）参照。本ドキュメントは Python 忠実モデル（`python/red_model.py`,
`Red`/`leR` を `pss_defs.thy` どおり実装）+ yaBMS 標準形判定による経験的調査の記録。

> ⚠️ 最終的な定義域・証明は **保留中**（有界列挙による経験的結論、use-site 監査も一部未完）。

## 1. 事実: どの系が $T_{\textrm{PS}}$ で偽か

全 $T_{\textrm{PS}}$（$\textrm{Lng}\le 4$, 各成分 $\le 2$、7380 個）を網羅（`python/red_audit.py`）:

| 系 (§) | $T_{\textrm{PS}}$ で | 最小反例 |
|---|---|---|
| 直系先祖の Red 不変性 `Red_le` (918) | **偽** (3551/7380) | $(0,0)(0,1)$ |
| Red が単項性を保つ `Red_monoT` (926) | **偽** (1490) | $(0,0)(0,1)$ |
| $P$ の Red 同変性 `P_Red` (938) | **偽** (3545) | $(0,0)(0,1)$ |
| Red の冪等性 `Red_idem` (960) | **偽** (1099) | $(0,0)(0,2)$ |
| Red と基本列の可換性 `Red_oper` (976) | **偽** (2149) | $(0,0)(0,1)[2]$ |
| Red が許容性を保つ `Red_adm` (992) | **偽** | $(0,0)(0,1)(0,2)$ |
| 許容化の Red 不変性 `admof_Red` (1000) | **偽** | $(0,0)(0,1)(0,2)$ |
| Red が基点を保つ `Red_marked` (1008) | **偽** | $(0,0)(0,1)(1,2)$ |
| Lng の Red 不変性 / Red が零項性を保つ / Red と Pred の可換性 / Red の IncrFirst 不変性 | 真 | — |

（adm 系3つは `python/red_adm_audit.py`、他5つは `python/red_audit.py`。計 **8 系が $T_{\textrm{PS}}$ で偽**。）

最小反例 $M=(0,0)(0,1)$: 複項で $\textrm{Red}\,M=(0,0)(1,1)$。$(0,0)\le_M(0,1)$ は偽
（$0<0$ 不成立）だが $(0,0)\le_{\textrm{Red}(M)}(0,1)$ は真。直観: $\textrm{Red}$ は係数を
正規化するだけだが、正規化が祖先比較を**反転**させると tree が変わり崩れる。論文の
「$\textrm{Lng}$ 帰納で即座」も $\textrm{Lng}=2$ で命題が偽なので原理的に不成立。

## 2. ST_PS への制限は不適切

`ST_{\textrm{PS}} \subset RT_{\textrm{PS}}$（標準形は簡約済、line 1348）より、標準形 $M$ では
$\textrm{Red}\,M = M$（実証: `python/red_anchor2.py` の生成標準形すべてで成立）。よって
**ST_PS 上では上記5系は $\textrm{Red}=\mathrm{id}$ で自明**になり、§7 が実際に適用する
**非標準・非簡約の切片 $N$**（$\textrm{Red}\,N \ne N$）を覆えない（論文 line 99–101 も
非標準・非簡約列を使う必要があると明言）。

## 3. 正しい定義域（暫定）: 先祖係留切片

| 候補 $D$ | sound ($D\Rightarrow$ 8系) | 補足 |
|---|---|---|
| $T_{\textrm{PS}}$ | ✗ | §1 の反例 |
| $ST_{\textrm{PS}}$ | ✓ だが自明 | $\textrm{Red}=\mathrm{id}$、§7 を覆えない |
| 標準形の**任意**切片 | ✗ | 反例 $(2,0)(1,1)$（標準形 $(0,0)(1,1)(2,1)(3,1)(2,0)\cdots$ の切片） |
| 標準形/簡約+単項の**先祖係留**切片 | ✓（失敗0） | 下記 |

**先祖係留切片** = ある $S \in ST_{\textrm{PS}}$（または $S \in RT_{\textrm{PS}}\cap PT_{\textrm{PS}}$）と
$a\le b$ で $(0,a)\le_S(0,b)$ なるものに対する $M=(S_j)_{j=a}^{b}$。命題「標準形の切片と
$\textrm{Br}$ の降順性の関係」(line 1422) の前提と同型。実証（`python/red_anchor2.py` + `red_adm_audit.py`）:

- 標準形ソースの先祖係留切片: **8系すべて成立**（`Red_le` ほか5系 2694 切片、adm系3つ 失敗0）。
- 簡約+単項ソースの先祖係留切片: **8系すべて成立**（103 切片、失敗0）。

## 4. use-site 監査（§7 が当てる $N$ は係留切片か）

`corrections.md`/§7 の各使用箇所で8系が適用される $N$ を確認（`python/` で検証）:

- §6.5 内部（content.md 936/944/958/998/1006/1014/1044/1052）: 証明中の**同じ $M$** に適用
  → 系の定義域を絞れば一緒に絞れる。
- §7 Trans/Mark（4255〜5816 等）: $N=(M_j)_{j=lo}^{j_1}$（$M\in ST_{\textrm{PS}}\cap PT_{\textrm{PS}}$ か
  $RT_{\textrm{PS}}\cap PT_{\textrm{PS}}$ の切片）。$lo$ は $j_1$ の親/先祖/許容先祖:
  - 行0親 → $(0,lo)\le_M(0,j_1)$ 直接。
  - 行1親 → `nextrel1` が `le0` を要求するので行0先祖も含意。
  - $\textrm{Adm}_M(\text{親})$ → 命題（$\textrm{Adm}_M$ と $<^{\textrm{NextAdm}}$ の関係, line 2596）と
    $<^{\textrm{NextAdm}}\subseteq\le_M$ より行0先祖。
  → いずれも係留 $(0,lo)\le_M(0,j_1)$。先祖係留切片で十分。

**未監査**: content.md 6461（`Red_marked`, 前提が基点付き列で別系統）、`Red_adm`/`admof_Red`
（許容性 `adm` を絡める系、上記5系に未含）。

## 5. 帰結（証明戦略・保留中）

- 形式化では5系の前提を「先祖係留切片」へ補正し、当面は言明のみ（`sorry`）。
- 無仮定 $\textrm{Lng}$ 帰納は不可（$\textrm{Lng}=2$ で偽）。証明には再帰不変な補助仮定の特定
  または tree（`nextR` 親子）保存の大域議論が要る——本プロジェクト最難（論文も実質未証明）。
- 定義域の最終的な形・閉性・全 use-site 確認は **保留中**。

## モデル（`python/`）

- `red_model.py` — `Red`/`leR`/`oper` ほかの忠実実装（`Red_trace` は再帰引数を記録、`is_standard` は yaBMS）。
- `red_audit.py` — 全 $T_{\textrm{PS}}$ 上の命題検証（§1 の表）。
- `red_anchor2.py` — 先祖係留切片での5系検証（§3）。
- `red_domain.py` / `red_charac.py` / `red_mono.py` — 定義域探索・特徴付け・失敗分類。
</content>
