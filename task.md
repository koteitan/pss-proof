# 進捗管理

凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**（司令マーカー）。
装飾（任意）: 🚨🚧＝未証明だが本質的障壁で停滞 / 🚨🤖＝未証明だが agent 作業中 / 🚫＝真に偽で訂正不能。
（🚫=論文の言明が真に偽で訂正不能のもの。論文の言明が偽でも定義域を訂正すれば真になるものは 🚨＋〔correction Ax〕で示す＝訂正版は未証明。）

## いまの作業配置 (live, 2026-05-25 更新)
**🚨→✅ 削減フェーズ**: 独立・自己完結な未証明 🚨 を team で並列討伐中（緑 main ベース・ガードレール: 未証明 p_* 引用禁止／経験的真偽確認／相互独立のみ）。
| actor | ターゲット | 状態 |
|---|---|---|
| ✅ agent `a8c0…` | `m_6_7_ST_eq_Union_SkT`（`ST_PS=⋃SkT_PS`） | **統合済（緑）** |
| ✅ agent `acf1…` | `m_6_6_Red_leftend_1`（Red が行1左端固定） | **統合済（緑）** |
| ✅ agent `abba09…` | `m_6_7_standard_prefix`（標準形の始切片遺伝＋helper `ST_PS_T_PS`） | **統合済（緑）** |
| ✅ agent `a97a…` | `m_6_6_condAB_coeff`（§6.6 条件A/Bと係数、3部構成・最難）＋helper `nextR1_unique`/`condAB_row1_noparent_zero` | **統合済（緑, a5287ab）**。build23 で収束（async yield だが最終緑）。a7d9 の partial を出発点に part3 の greedy intro と bounded-∀ 不整合を修正 |
| 🚨(β) `m_6_7_standard_P_components`（親直轄） | 原文命題=`S_kT_PS`(同ランク)。原文証明は `S_{k-1}` 止まり＝**原文証明はバグ**。経験的検証で命題自体は真(k≤5,違反0)。**証明構造判明**: `T(k):全P成分∈S_k` を補助 `A(k):非末尾P成分∈S_{k+1}` と同時帰納すれば case(1,J₁=0)→直接, 先頭(=P(M')非末尾)→A, 末尾(case2)→T(k)+[n]+構造帰納 で閉じる。**ただし A(k) の帰納ステップが S_{k+1}↔S_{k+2} で閉じず、A の正しい不変量を要確定**（audit5 で rank柔軟性を調査中） |
| 👤 親セッション（私） | team 統合（1つずつ緑ビルド確認）＋次の独立補題選定 | — |

reducedness クラスタ（reduced_iff_cond/P_reduced/reduced_oper/reduced_slice/reduced_coeff/oneColumn）は**相互依存＋Red 絡み**で並列化すると循環偽証明リスク → **逐次**で扱う。§7.1+ は命題が `sorry` 未転記なので並列対象外。

### 保留中: m_6_5_Red_IncrFirst（worktree adb8、未commit）
**lexical 11＋証明バグ ~55件 修正**済、zeroT/multiT/core/noncore-m10z/**m10>0-trunk まで通過**、`Red_m10pos_unfold`(a2c4由来)統合済。**残り＝m10>0 の死枝[20]**（下記）。`Red_Pred`(a4ed,停止) も case 6 が同障壁。

### 🔴 共通ボトルネック: 死枝[20]
`seg (Red (coreReduce M)) (entry M 1 0) (Lng(Red(coreReduce M))−1) ∈ PT_PS`（=Red 出力の枝部が単項）。
**Red_IncrFirst の m10>0 ケース（claim A・B 計4箇所）と Red_Pred の case 6 の双方がこれに帰着**。
既存補題に無く、`m_6_5_Lng_Red` は両ケース処理で**回避**（条件を証明していない）。§6.6/6.7 レベルの構造定理が必要＝独立した大仕事。
エージェントの元 Red_IncrFirst 証明はこの箇所を `by simp` で誤魔化しており**真には未完成**だった。

数式は MathJax 記法（`$...$`）で書く。

- 🚨 定理（標準形ペア数列システムの停止性）[§8.7 主結果]
  - ✅ §5 定式化
    - ✅ §5.1 親子関係
      - ✅ 命題（親の存在の判定条件）
      - ✅ 命題（親の基本性質）
      - ✅ 系（直系先祖の基本性質）
      - ✅ 系（直系先祖の木構造）
    - ✅ §5.3 基本列
      - ✅ 命題（$\textrm{Pred}$ が $[1]$ で表されること）
    - ✅ §5.4 ペア数列システム
      - ✅ 命題（$F_M$ と基本列の関係）〔原文訂正: corrections.md A1〕
  - 🚨 §6 ペア数列の基本性質
    - ✅ §6.1 最上行のインクリメント
      - ✅ 命題（$\leq_M$ の $\textrm{IncrFirst}$ 不変性）
    - ✅ §6.2 単項性
      - ✅ 命題（複項性の判定条件）
      - ✅ 系（単項性の始切片への遺伝性）
      - ✅ 命題（単項性の直系先祖による切片への遺伝性）
      - ✅ 命題（$P$ の $\textrm{IncrFirst}$ 同変性）
      - ✅ 命題（$P$ の各成分の非複項性）
      - ✅ 命題（$P$ の加法性）
      - ✅ 命題（$P$ と基本列の関係）
      - ✅ 命題（非複項性と基本列の関係）
    - ✅ §6.3 許容性
      - ✅ 命題（許容性の切片への遺伝性）
      - ✅ 命題（許容化の切片への遺伝性）
      - ✅ 命題（基点の切片への遺伝性）
    - ✅ §6.4 幹と枝
      - ✅ 命題（$P$ と $\textrm{IdxSum}$ の関係）
      - ✅ 系（$P$ と $\textrm{IdxSum}$ の合成の特徴付け）
      - ✅ 命題（$P$ の各成分の左端の単調性）
      - ✅ 命題（切片の単項成分と $<_M^{\textrm{Next}}$ の関係）
      - ✅ 命題（$\textrm{FirstNodes}$ と $\textrm{TrMax}$ と $\textrm{Joints}$ の関係）
      - ✅ 系（$\textrm{FirstNodes}$ と $\textrm{Joints}$ の単調性）〔(1)(2)(3) 証明済。(4) 厳密減少は**偽**（反例 `(0,0)(1,1)(2,1)(3,1)(2,0)`、標準形、joint 一致）→ correction A3 で paper を (1)(2)(3) に訂正〕
      - ✅ 系（単項性の切片への遺伝性）
    - 🚨 §6.5 簡約化 〔**注意: 下記8系は論文の前提 $T_{\textrm{PS}}$ では偽**（correction A4 / `docs/red-le-domain.md`）。
      定義域＝「先祖係留切片」で真（保留中）。**前提を `anchored_slice` に補正済**（`pss_defs.thy` に定義、
      8系は `M∈anchored_slice` 前提へ、偽の公理を解消、commit 063927d）。`anchored_slice⊆T_PS` 証明済
      (`anchored_slice_imp_T_PS`)。fan-out agent の T_PS 版証明は偽命題依存で破棄。〕
      - ✅ 命題（$\textrm{Red}$ の well-defined 性）〔`m_6_5_Red_welldef`: 測度 ν での整礎帰納＋`Red.domintros`。基礎補題群(diagSeq・`Lng_Br_le`・`TrMax_diagSeq_append_ge`・`coreReduce`/`betaM`・`coreReduce_nonmulti`・`NJ_nonmulti`・`nu`/`muMono`・per-case descent)を経て完成。設計 docs/red-termination.md〕
      - 🚨🚧 命題（$\textrm{Red}$ の $\textrm{IncrFirst}$ 不変性）〔`m_6_5_Red_IncrFirst`。worktree adb8 で ~55件修正し zeroT/multiT/core/noncore-m10z/**m10>0-trunk まで通過**。`Red_m10pos_unfold` 統合済。**m10>0 の最終段が死枝[20]に帰着**（上記）→ 死枝[20]補題が要る。真理値: 死枝[20]が常に真なら T_PS で真。〕
      - ✅ 命題（$\textrm{Lng}$ の $\textrm{Red}$ 不変性）〔`m_6_5_Lng_Red`、§6.5 下流の linchpin〕
      - ✅ 系（$\textrm{Red}$ が零項性を保つこと）〔`m_6_5_Red_zeroT`。T_PS で真。Lng=1 へ帰着(`m_6_5_Lng_Red`)＋helper `rz_Red_entry1_nz`。agent 由来、統合済〕
      - 🚨 系（直系先祖の $\textrm{Red}$ 不変性）〔**keystone**: `m_6_5_Red_le`。**T_PS で偽**(反例 `(0,0)(0,1)`)→先祖係留切片で真(保留中)。A4〕
      - 🚨 系（$\textrm{Red}$ が単項性を保つこと）〔`m_6_5_Red_monoT`。T_PS で偽 → 係留切片で真(保留中)。A4〕
      - 🚨 系（$P$ の $\textrm{Red}$ 同変性）〔`m_6_5_P_Red`。T_PS で偽 → 係留切片で真(保留中)。A4〕
      - 🚨 命題（単項性と $\textrm{Red}$ の関係）〔`m_6_5_monoT_Red`、前提 $PT_{\textrm{PS}}$（[19][20]死枝）〕
      - 🚨 命題（$\textrm{Red}$ の冪等性）〔`m_6_5_Red_idem`。T_PS で偽(反例 `(0,0)(0,2)`) → 係留切片で真(保留中)。A4〕
      - 🚨🚧 命題（$\textrm{Red}$ と $\textrm{Pred}$ の可換性）〔`m_6_5_Red_Pred`。**T_PS で真**。agent a4ed は case 1-5 を詰めたが **case 6 が死枝[20]に帰着**して停止（Red_IncrFirst と同一障壁）。〕
      - 🚨 命題（$\textrm{Red}$ と基本列の可換性）〔`m_6_5_Red_oper`。T_PS で偽 → 係留切片で真(保留中)。A4〕
      - 🚨 命題（$\textrm{Red}$ が許容性を保つこと）〔`m_6_5_Red_adm`。T_PS で偽(反例 `(0,0)(0,1)(0,2)`) → 係留切片で真(保留中)。A4〕
      - 🚨 系（許容化の $\textrm{Red}$ 不変性）〔`m_6_5_admof_Red`。T_PS で偽 → 係留切片で真(保留中)。A4〕
      - 🚨 系（$\textrm{Red}$ が基点を保つこと）〔`m_6_5_Red_marked`。T_PS で偽(反例 `(0,0)(0,1)(1,2)`) → 係留切片で真(保留中)。A4〕
    - 🚨 §6.6 簡約性 〔経験的監査 `python/red_66_audit.py`: 下記の通り大半 T_PS で真〕
      - 🚨 命題（簡約性の切片への遺伝性）〔`p_6_6_reduced_slice`。article 前提 $j'_0\le\textrm{TrMax}$ は**偽**(反例 標準形 `(0,0)(1,1)(1,0)`)→ $j'_0=0$ に補正済(保留中)。**correction A5**〕
      - 🚨 命題（$P$ が簡約性を保つこと）〔`p_6_6_P_reduced`。**T_PS で真**〕
      - 🚨 命題（簡約性が基本列で保たれること）〔`p_6_6_reduced_oper`。**T_PS で真**〕
      - 🚨 命題（簡約性と係数の関係）〔`p_6_6_reduced_iff_cond`: 簡約 ⟺ 条件A∧B。**T_PS で真**〕
      - ✅ 補題（$\textrm{Red}$ と左端の関係）(1)〔`m_6_6_Red_leftend_1`: `entry (Red M) 1 0 = entry M 1 0`。Red.pinduct 5分岐、m10>0 は `coreReduce_monoT_m10_pos`+`TrMax_diagSeq_append_ge` で（未証明 leftend_2 に依存せず）。agent acf1 由来、統合済〕
      - 🚨 補題（簡約性と係数の基本性質）
      - 🚨 補題（簡約性と左端の関係）
      - 🚨 補題（条件 (A) と (B) と係数の基本性質）
      - 🚨 系（直系先祖による切片と $\textrm{Red}$ と $\textrm{IncrFirst}$ の関係）
      - 🚨 系（$1$ 列ペア数列の基本性質）
    - 🚨 §6.7 標準形
      - ✅ 命題（標準形の階層和による表示）〔`m_6_7_ST_eq_Union_SkT`: `ST_PS = ⋃k SkT_PS k`。純帰納的集合等式、Red 非依存。agent a8c0 由来、統合済〕
      - 🚨 命題（標準形の簡約性）
      - 🚨🚧 命題（標準形の単項成分が標準形であること）〔`p_6_7_standard_P_components`: `M∈SkT_PS k ⟹ P成分∈SkT_PS k`(同ランク)。**原文(content.md 1366)は S_k を主張するが原文証明(1386,1392)は S_{k-1} しか示さない＝原文内部ギャップ**。経験的に S_k も小範囲で真。**決定=(β) S_k のまま証明**(article 証明が足りない hard ケース)。用途上は ST_PS 和集合版で足りる(S_{k-1}⊆ST_PS via m_6_7_ST_eq_Union_SkT)〕
      - ✅ 命題（標準形の始切片への遺伝性）〔`m_6_7_standard_prefix`: `seg M 0 j' ∈ ST_PS`。ST_PS 帰納＋`less_induct`、`_[1]=Pred` で短縮。helper `ST_PS_T_PS`(ST_PS⊆T_PS) も証明。agent abba09 由来、統合済〕
    - 🚨 §6.8 降順性
      - 🚨 命題（標準形の切片と $\textrm{Br}$ の降順性の関係）
      - 🚨 命題（標準形の単項成分が降順であること）
  - 🚨 §7 Buchholzの表記系への翻訳
    - 🚨 §7.1 Buchholzの表記系
      - 🚨 命題（順序数項のカッコの個数が左右で等しいこと）
      - 🚨 命題（順序数項の単項成分の基本性質）
      - 🚨 命題（部分表現の不等式の延長性）
    - 🚨 §7.2 scb分解
      - 🚨 命題（scb分解の置換可能性）
      - 🚨 命題（scb分解の合成則）
      - 🚨 命題（scb分解の自明性の判定条件）
      - 🚨 命題（scb分解の一意性）
      - 🚨 系（加法と scb分解の関係）
      - 🚨 命題（scb分解と基本列の関係）
      - 🚨 命題（$\textrm{RightNodes}$ と部分表現の関係）
    - 🚨 §7.3 翻訳写像
      - 🚨 命題（$\textrm{Trans}$ の well-defined 性）
      - 🚨 命題（$2$ 列ペア数列の基本性質）
      - 🚨 命題（$\textrm{Trans}$ の $(\textrm{IncrFirst},\textrm{Red})$ 不変 $P$ 同変性）
      - 🚨 命題（$\textrm{Mark}$ の $(\textrm{IncrFirst},\textrm{Red},P)$ 不変性）
      - 🚨 命題（$\textrm{Trans}$ が零項性を保つこと）
      - 🚨 命題（$c_1$ と $c_2$ の大小関係）
      - 🚨 命題（$\textrm{Pred}$ の $\textrm{Trans}$ に関する降下性）
      - 🚨 命題（右端第 $1$ 基点の $\textrm{Mark}$ の基本性質）
      - 🚨 系（$\textrm{Mark}$ の左端の基本性質）
      - 🚨 系（条件 (II) か (IV) の下で $t_2$ が $0$ でないこと）
      - 🚨 命題（右端第 $2$ 基点の $\textrm{Mark}$ の基本性質）
      - 🚨 命題（$\textrm{Trans}$ の最左単項成分の左端の基本性質）
      - 🚨 命題（$\textrm{Trans}$ が単項性を保つこと）
      - 🚨 系（$\textrm{Trans}$ と非可算基数の関係）
      - 🚨 系（左端第 $1$ 基点の $\textrm{Mark}$ の基本性質）
      - 🚨 系（$s_1$ と $b_1$ の空性と基点の関係）
      - 🚨 命題（$\textrm{Mark}$ が順序関係を保つこと）
      - 🚨 系（$s_{-1}$ と $b_{-1}$ の空性と基点の関係）
      - 🚨 命題（$\textrm{Mark}$ の $\textrm{Trans}$ による表示）
    - 🚨 §7.4 許容的親子関係
      - ✅ 命題（$\textrm{Adm}_M$ と $<_M^{\textrm{NextAdm}}$ の関係）
      - 🚨 命題（$\textrm{Trans}$ と $<_M^{\textrm{NextAdm}}$ の関係）
      - 🚨 系（$\textrm{Mark}$ と $<_M^{\textrm{NextAdm}}$ の関係）
      - 🚨 系（$\textrm{Trans}$ の $\textrm{Mark}$ と $\textrm{Pred}$ による表示）
      - 🚨 系（$\textrm{Trans}$ の $\textrm{Mark}$ と切片による表示）
      - 🚨 系（$\textrm{RightNodes}$ と $\textrm{Mark}$ の関係）
      - 🚨 命題（$\textrm{RightNodes}$ と $\textrm{RightAnces}$ の関係）
      - 🚨 系（非零項の $\textrm{RightAnces}$ が非空であること）
  - 🚨 §8 停止性
    - 🚨 §8.1 条件 (I) の下での展開規則
      - 🚨 命題（条件 (I) の下での $\textrm{Trans}$ と基本列の交換関係）
      - 🚨 補題（公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）
      - 🚨 系（$\textrm{Pred}$ が公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）
      - 🚨 補題（条件 (I) か (III) の下での $c_1$ 前後の具体表示）
    - 🚨 §8.2 強単項性
      - 🚨 命題（標準形の直系先祖による切片の簡約化の強単項性）
      - 🚨 命題（条件 (II) か (IV) の下での終切片と $\textrm{Trans}$ の関係）
      - 🚨 補題（強単項性の切片への遺伝性）
      - 🚨 補題（部分表現の単項成分と $\textrm{Pred}$ の関係）
      - 🚨 補題（強単項性の下での部分表現の単項成分の基本性質）
      - 🚨 補題（条件 (V) の下での右端の親の基本性質）
      - 🚨 補題（条件 (V) の下での終切片と $\textrm{Trans}$ の関係）
    - 🚨 §8.3 条件 (II) の下での展開規則
      - 🚨 命題（条件 (II) の下での $\textrm{Trans}$ と基本列の交換関係）
      - 🚨 補題（第 $0$ 種型基本列の基本不等式）
      - 🚨 補題（第 $0$ 種型基本列の基本分岐規則）
      - 🚨 補題（第 $0$ 種型基本列の基本基点関係）
    - 🚨 §8.4 条件 (III) か (IV) の下での展開規則
      - 🚨 命題（条件 (III) か (IV) の下での $\textrm{Trans}$ と基本列の交換関係）
      - 🚨 補題（右端の非許容直系先祖の基本性質）
      - 🚨 補題（条件 (III)〜(V) の下での右端の置き換えと $\textrm{Trans}$ の関係）
      - 🚨 補題（条件 (III)〜(VI) の下での展開規則の基本性質）
      - 🚨 補題（条件 (III)〜(VI) の下での $\textrm{Trans}$ と scb分解の関係）
      - 🚨 補題（条件 (III)〜(V) の下での切片の scb分解）
      - 🚨 補題（条件 (III)〜(V) の下での各種 scb分解）
      - 🚨 補題（条件 (III) か (IV) の下での各種 scb分解）
      - 🚨 補題（条件 (III) か (IV) の下での基本列の基本性質）
    - 🚨 §8.5 条件 (V) の下での展開規則
      - 🚨 命題（条件 (V) の下での $\textrm{Trans}$ と基本列の交換関係）
      - 🚨 補題（条件 (V) の下での $\textrm{Joints}$ と $\textrm{FirstNodes}$ と $t_2$ の基本性質）
      - 🚨 補題（条件 (V) の下での各種 scb分解）
    - 🚨 §8.6 条件 (VI) の下での展開規則
      - 🚨 命題（条件 (VI) の下での $\textrm{Trans}$ と基本列の交換関係）
      - 🚨 補題（公差 $(1,0)$ のペア数列の $\textrm{Trans}$ の基本性質）
      - 🚨 補題（公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の展開規則）
      - 🚨 補題（順序数項の末尾単項の零化可能性）
    - 🚨 §8.7 主結果
      - 🚨 補題（公差 $(0,0)$ のペア数列の $\textrm{Trans}$ の基本性質）
      - 🚨 補題（基本列の降下性）
      - 🚨 補題（順序数項の再帰構造）
      - 🚨 補題（順序数項の共終数の遺伝性）
      - 🚨 補題（順序数項の末尾項の零化可能性）
      - 🚨 補題（$\textrm{Pred}$ と $[0]$ の関係）
      - 🚨 補題（順序数項の基本例）
      - 🚨 補題（$\textrm{Trans}$ が標準形を保つこと）
