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

## 5. 証明計画 (2026-06-01, understand+design ワークフロー)

`Red_le` を `anchored_slice` (pss_defs 463-466) 上で証明する分解。設計2案
(judge-panel) が収束した結論。

**鍵となる単純化 — 域内に multi は無い**: `m_6_2_mono_ancestor_slice` より
**任意の anchored_slice は zeroT か monoT**（決して multiT でない）。よって article の
帰納が破綻する multi ケース `Red M = ⊕_J Red(P M_J)` のブロック連結は**域内で
発生しない（vacuous）**。これが A4 の本質: 反例 `(0,0)(0,1)` はまさに multi。

**帰納**: `Red.pinduct`（`Red_dom` は GREEN = ν/coreReduce 測度）。bare Lng 帰納は
Lng=2 で偽なので不可。閉じた不変量 **`monoT M ∧ descending(Br M)`** を IH で持ち回る
（`anchored_slice` 自体は coreReduce 引数で閉じない: shift/Br成分は anchored=381/381,
739/739 だが coreReduce 引数は 0/1066。一方 monoT∧descending(Br) は閉じる:
coreReduce 引数は 1066/1066 mono かつ全て (0,0) 始まりで core 枝のみ再帰）。

**分解** (L1-L5 は LOW risk = 数百行の自己完結 reshape、既存 GREEN slice 補題使用):
- **L0** 域入口: `anchored ⟹ zeroT ∨ (monoT ∧ descending(Br))`。monoT は
  `m_6_2_mono_ancestor_slice`、descending(Br) は `m_6_8_standard_slice_Br_descending`
  （ST_PS源）/ slice 変種（RT_PS∩PT_PS源）。le0 アンカーを使うのはここだけ。
- **L1** zeroT 基底: `Red M=[(0,0)]`、両辺自明。
- **L2** 長さ一致: `m_6_5_Lng_Red`（GREEN）で j-range 一致。
- **L3** core-trunk (m00=m10=0, TrMax=Lng-1): `Red M = diagSeq 0 (Lng M-1)`。対角上
  le0⟺a≤b, le1⟺a=b。`entry_diagSeq` + monoT trunk。
- **L4** m10=0 shift: `Red M = Red(shiftRow0 M)`。L4a 行0一様シフト不変性（新規 le0/le1
  合同補題）+ IH。
- **L5** m10>0 coreReduce: `coreReduce M = diagSeq 0 (m10-1) @ IncrFirst^m10 M`、
  `Red M = seg N m10 (Lng N-1)` 再基底。**今証明した `m_6_5_monoT_Red_fact1_Lng`
  (長さ) + `m_6_5_monoT_Red_fact2a_leR_shift` (添字シフト ≤_M⟺≤_{coreReduce M}) を直接
  使う**。+ IH + `m_6_6_Red_leftend_1`（再基底オフセット）+ `p_6_5_monoT_Red`（[19]/[20]
  死枝が発火しない＝suffix∈PT_PS）。
- **L6** core-nontrunk（**唯一の難所 = ボトルネック**）:
  `Red M = diagSeq 0 (TrMax M) @ ⊕_J IncrFirst^{e_J}(Red N_J)`。
  - descending(Br) は**必要だが不十分**: 反例 `(0,0)(1,1)(1,2)(2,2)`（monoT・全adm・
    descending(Br) でも i=1,j0=2,j1=3 で Red_le 偽）。不足は**アンカー**で n_J を M の
    真の row-1 親に固定すること。
  - BC0 (row-0): trunk diagSeq が M の row-0 祖先 spine を [0..TrMax] で再現
    (`idxsum_leftend_lmin` + trunk 単調性)、各ブロックは同一 IncrFirst シフトなので
    nextrel0 が境界忠実。
  - BC1 (row-1, **最難**): n_J = M の row-1 親（article 注[12]）。IncrFirst は行0のみ
    なので行1鎖 + n_J-link が M の nextrel1 鎖を厳密再現。非アンカー反例では n_J が
    ill-formed（block leftend の row-1 値に le0 を満たす真の trunk 親が無い）。
    **弾薬**: §6.8 `oper_d1pos_anchor_coincide_*` 群（~15000-18000行）がまさにこの
    n_J 一致を slice の Br に対し既に grind 済。両行・両 le0/le1 の Red_le へ再組立。

**use-site 再利用**: §6.4 `idxsum_*`, `m_6_4_FirstNodes_TrMax_Joints`, §6.6
`m_6_6_Red_leftend_1`, §6.8 `m_6_8_*`/`oper_d1pos_branch_anchor`/`Br_seg_reshape`,
slice transfer `adm_le0_seg`/`adm_nextR1_seg`/`adm_le1_seg`(新)。

**リスク**: L6/BC1 が真のボトルネック（複数週相当、§6.8 d1pos アンカー機構が正しい弾薬
だが両側 Red_le への再組立は未証明）。L1-L5 は低リスク。域閉性は monoT∧descending(Br)
不変量で解決（coreReduce 引数 20/1066 の非descending(Br) は core 枝で Red_le-ok を別途
確認、経験 1066/1066）。経験的確信は HIGH（Red_le 776/0 anchored, 1066/1066 coreReduce
引数, multi 不在）。

## 6. 重大な設計結論 (2026-06-01): 固定不変量 pinduct は不可

§5 の GLUE 試行（2 workflow, 6 agent, ~1.3M token）で判明した**根本障害**:

**`Red_le` を anchored_slice 上で証明する Red.pinduct は、いかなる固定不変量 Φ でも
閉じない。** 必要なのは Φ が (a) 全 Red sub-call で閉じ、かつ (b) core-nontrunk
ノードで L6/BC 同値を含意すること。だが:

- **`descending(Br M)` は閉だが弱すぎ**（(b) 不成立）: 反例
  **`(0,0)(1,1)(1,2)(2,2)`** — core・monoT・descending(Br)=真・全 NJ も descending
  なのに `Red M = (0,0)(1,1)(1,1)(2,2)` が row-1 辺を反転（`leR M 1 2 3`=偽 vs
  `leR(Red M) 1 2 3`=真）。全 T_PS で 2198 反例、core-nontrunk monoT+descending で
  188中5反例。
- **`RedCondA`（§6.6 簡約性: 一意親辺は+1増分）は BC を含意**し5反例を正確に分離
  （descending∧RedCondA → BC 37/0、RedCondA∧RedCondB → 50/0）が、**sub-call で閉じない**
  （anchored seed から到達する 72 個の coreReduce 引数 Narg=diagSeq@IncrFirst^m10 M が
  RedCondA を破る）。
- **`descending(Br)` 自体が NJ 再ルートで閉じない**（776反例、C-NJ補題は偽）。
- **真のガードは reachability**（M が anchored_slice の Red-sub-call 子孫）。これが
  大域定理 `m_6_5_Red_le_anchored` を真にするが（到達集合で BC 0反例、5破壊項は
  到達不能）、reachability は pinduct 非閉。

**閉な C-shift/C-core は真**（`descending_Br_shiftRow0` 15904/0,
`descending_Br_coreArg` 4338/0、ただし未証明）。**反例再現**: `python/glue_verify.py`
（`python3 glue_verify.py brute 5 3`）。

**正しい証明構造（次の研究対象）**: 固定不変量 pinduct を捨て、anchored slice 上で
**直接** `redle_anchored_core` / `redle_anchored_noncore`（共に経験的真 263/0, 346/0）を
証明する。recursion の productive ステップごとに RedCondA(簡約性)を**再確立**する機構か、
§7 use-site の anchoring（article 注[12]）を陽に使う。§6.6 簡約性の成果に依存する可能性大
→ **§6.5 Red_le は §6.6 の後に回すのが自然**。multi-week 級。main には sorry を入れない
（5 green ブリックは sorry-free で済）。

## 7. 循環の精査 (2026-06-01): β は循環、α が唯一の突破口

§6.5/§6.6 循環を破る2ルートを read-only 精査（workflow wy3p446qv）した結論。

### β (keystone backward 経由) = 循環（却下）
keystone(d) backward (RedCondA∧RedCondB⟹reduced) の A4非依存証明は load-bearing に
`p_6_5_Red_IncrFirst`(Red∘IncrFirst=Red) を要する。だが **Red_IncrFirst の m10>0 ケースは
dead-branch[20] と論理的に等価**:
- m10>0 で死枝が発火すると Red M = M、Red(IncrFirst M)=IncrFirst M、両者は異なる(M≠IncrFirst M)
  → Red_IncrFirst が偽。
- Red_IncrFirst は真(7381/0)なので死枝は不到達。だが**その証明は死枝不到達を示さねば閉じない**
  （productive 分岐では IH で N_M=N_IM が一致し equivariance 成立だが、dead 分岐は M≠IncrFirst M で
  閉じない）。
- ∴ **Red_IncrFirst(m10>0) ⟺ dead-branch[20]不到達**。β は循環を relocate するだけ。

### α (monoT_Red 経由) = 真の scope 縮小（採用）
monoT_Red(dead-branch[20]) は **green ステップのみ**で次の唯一の既約義務へ帰着:
**`le0 A m10 jA ⟹ le0 (Red A) m10 jN`**（A=coreReduce M=diagSeq 0 (m10-1)@IncrFirst^m10 M、
jA=Lng A-1、jN=Lng(Red A)-1）。これは **Red_le の row-0・forward・single-anchor 断片**:
- 全 Red_le(T_PS で偽)より真に弱い。row-1 反例 `(0,0)(1,1)(1,2)(2,2)` は **row-1(le1)** の flip
  なので **row-0(le0) 断片は回避**。
- anchored 域で 11916/0 + 6896/0（非空、multi A4 族は anchored で vacuous）。到達 A は常に mono
  (coreReduce_monoT 344/0)。
- = **BC0**（L6 block-connection の row-0 半分、red-termination.md の easier half）。

green ステップ(α): Step1 monoT(seg)⟺le0 N m10 jN [adm_le0_seg]; Step2 le0 A m10 jA
[fact2a]; Step4 rebase productive [redle_branch5_rebase]。**Step3 = 上記 BC0 断片が唯一の穴**。
係数 bypass は反例で否定（flat `(0,0)(0,0)(0,0)` が condAB 全充足でも le0 N m10 jN 偽、104/241）。

### 結論
§6.5/§6.6 cluster は **dead-branch[20]不到達 (`p_6_5_monoT_Red`) を中心に密に循環**。唯一の
A4非依存な突破口は **α の BC0 断片 `le0 A m10 jA ⟹ le0 (Red A) m10 jN`**（row-0 forward
anchored、Red.pinduct で multi vacuous）。ただし pinduct の core-nontrunk 子再帰で死枝に
再突入しないかは要精査（NJ ブロックが m10>0 になり得る）。これが解ければ monoT_Red→
dead-branch[20]→Red_IncrFirst/Red_Pred→keystone(d)→RedCondA⟹red_le で cluster 全体が解ける。
**次の単一目標: α の BC0 断片**（red-termination.md §7a の forward/row-0 半分への scope 縮小）。
