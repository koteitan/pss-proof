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

## 8. 循環は破れた (2026-06-02): keystone (d) は真の multi-lemma program

**(α) が成功**＝`m_6_5_monoT_Red_m10pos`(green, dead-branch[20]不到達, m10>0) が **Red_le を
経由せず値単調性で証明済**。よって §7 の循環は解消。keystone (d) `reduced⟺RedCondA∧RedCondB`
を非循環に証明できる状態。だが並列 fan-out で **(d) は1補題でなく multi-lemma program** と判明
（K-fwd/K-bwd 両 agent が blocker 報告、self-contained 1補題に収まらず）。

### scout 前提の訂正（agent が経験的に検出）
- **誤**: 「multiT 枝は reduced で vacuous（Red 出力は concat≠M）」。
- **正**: reduced の **multiT が支配的**（reduced 417件中 267件=64%が multiT。例 (0,0)(0,0),
  (1,1)(0,0)）。`Red(concat)=concat` は各ブロックが reduced なら成立する。Route 2（Red N は常に
  reduced）も不可: red_model で **Red は冪等でない**（Red(Red M)≠Red M, 1919/11748）、Im(Red)
  は RedCondA を満たさない（1919/11748）。よって M 自身の Red 枝での substitution route が必須。

### keystone (d) を構成する未 green sub-lemma（両方向で共有）
1. **parent block-locality**（基盤・独立 leaf）: ブロック J 内ノードの parent はブロック J 内
   （419/419 in-block）。§6.4 idxsum/nextR の純構造。fwd/bwd 両方の multiT 枝の土台。
2. **m_6_6_RedCond_P_block**（blockwise 継承, bwd 用）: `RedCondA M∧RedCondB M ⟹
   RedCondA(P M!J)∧RedCondB(P M!J)`（644/644）。#1 に依存。
3. **concat-lifting**（fwd 用）: blockwise A∧B ⟹ 全体 A∧B（+ ブロック境界 RedCondB:
   各ブロック先頭は row-0 parent 無し ⟹ entry M 0 j=entry M 1 j）。#1 に依存。
4. **P-stability**（fwd 用）: `Red M=M ⟹ Red(P M!J)=P M!J`（644/644）。Lng_Red で長さ一致
   ＋ concat 単射。
5. **core-trunk 対角 pinning**: `RedCondA M ⟹ M=diagSeq 0 (Lng M-1)`（TrMax=Lng-1 枝）。
   condAB_coeff は `M0j≤j` まで、**対角への等号**は no-row0-parent⟹entry=0 連鎖が追加で要る。
6. **shift 枝**（m10=0, M0≠(0,0)）: A∧B が m00=0 を強制する到達可能部分の構造論。**未明瞭・要研究**。
7. **m10>0 rebase pinning**: rebase 出力係数が M に一致（condAB_coeff + 内側 N の IH + brick guard）。

→ 次: #1(parent block-locality), #5(core-trunk pinning) を独立 leaf として並列証明（土台）。
green 後 #2/#3/#4 を次ラウンド、最後に fwd/bwd 組立て。#6 shift は別途精査。

## 9. keystone 組立ての壁 (2026-06-03): 原文証明ルートは anchored ドメイン依存

土台が全て green（#1 `m_6_4_parent_in_block`, #2 `m_6_6_RedCond_P_block`, #3
`m_6_6_RedCond_concat_lift`, #4 `m_6_6_Red_P_stable`, #5 `m_6_6_RedCondA_core_diag`,
`m_6_6_P_reduced`）。fwd/bwd 組立てを試行したが **mono の2枝で blocker**:

- **multiT / zeroT / core-trunk / shift は閉じる**（shift は両方向で vacuous: fwd は
  shift M が never reduced、bwd は RedCondB⟹m00=m10=0 が m00>0 と矛盾）。
- **core-nontrunk と m10>0 が未解決**。

### 決定的発見
1. **m10>0 枝の再帰引数 N=Red(diagSeq 0(m10-1)@IncrFirst^m10 M) は長さ Lng M+m10
   ＝ M より長い**。よって **Lng 帰納の IH が届かない**。Red 自身の整礎測度
   ＝ **Red.pinduct で帰納**すべき（Lng 帰納でも単純 Red 再帰でも不可）。
2. keystone iff `reduced⟺RedCondA∧RedCondB` は **全 T_PS={M≠[]} で真**
   （型正規化後 0 fail; maxlen3,val3 4368件）。先の検証スクリプトの「131 fail」は
   list-vs-tuple 型不一致バグ（教訓: [[verify-rank-depth]] 同様、経験検証は型に注意）。
3. だが**原文の keystone 証明ルート**（簡約性と係数の関係の証明, content.md 1130-)
   は **補題(e)簡約性と左端の関係(1084) + 簡約性の切片への遺伝性(1026) + Pred 帰納**
   を使い、(e)/遺伝性はいずれも **Red 冪等性(960)** に依存。そして **Red 冪等性は
   全 T_PS で偽**（820/4368 fail、**全て is_standard=False の非標準列**; 標準列では
   0 fail）＝既に **A4 で `p_6_5_Red_idem` は `anchored_slice` に制限済**。
4. よって keystone を**原文どおり**証明するには anchored/標準ドメインの
   冪等性・(e)・遺伝性が要る。一方 keystone 自体は全 T_PS で真なので、
   **冪等性を経由しない直接証明**（core-nontrunk/m10>0 の reproduction を condAB_coeff
   構造から Red.pinduct で直接）も原理的に可能だが、原文に対応証明が無い＝原創作業。

### 分岐（要方針判断）
- **(A) 原文ルート**: `p_6_5_Red_idem`(anchored, 根) → (e) → slice遺伝性 → keystone。
  原文が証明を与える（"Lng帰納で即座"）が4命題の連鎖＝multi-round。冪等性自体も
  m10>0 longer-arg で Red.pinduct 要。
- **(B) 直接ルート**: keystone を全 T_PS で Red.pinduct 直接証明。core-nontrunk/m10>0
  の reproduction 補題を condAB_coeff から直接。原文に無い＝原創、難。
- **(C) 一旦保留**し §6.7/§7/§8 等の独立タスクへ。keystone は §6.6/§6.7 の後続を
  block するが §6.8(green)経由の §8 critical path とは別。

## 10. (A)ルート採用→冪等性も同一コアに収束 (2026-06-03)

ユーザーが (A) 原文ルート採用。根 `p_6_5_Red_idem`(anchored) を Red.pinduct で攻めた結果:
- green ブリック `idem_anchored_not_multi`（anchored slice は never multiT, commit 34d9831）
  で multiT 枝を除去。冪等性は `idem_nonmulti: M∈T_PS ⟹ ¬multiT M ⟹ Red(Red M)=Red M`
  （全 T_PS で 0-fail）に帰着。
- Red.pinduct で **zeroT/core-trunk/shift の3枝は IH で close**（shift は coreReduce_nonmulti
  ＋ IH で Red M=Red core=Red(Red core)）。
- **残り2枝＝keystone と同一の壁**（idempotency も keystone-bwd も §6.6(e) も全部ここに収束）:
  - **B1 (core-nontrunk)**: 外側 Red が `diagSeq 0 t @ concat(map(λJ. IncrFirst^eJ(RNJ J)))`
    （各 RNJ J 簡約）を固定する njA 整合の**再分解補題**。
  - **B2 (m10>0)**: IH で N:=Red(diagSeq 0(m10-1)@IncrFirst^m10 M) が**簡約**(Red N=N)と判明。
    更に Red M = seg N m10 jN（rebase shift=0: entry N 0 m10=entry N 1 m10, 756/0）、
    N_K=N。よって B2 は**単一の式**に帰着:
    **`Red(diagSeq 0(m10-1) @ IncrFirst^m10 (seg N m10 jN)) = N`**（N 簡約 mono-core, 756/0）。
    これは **Red_IncrFirst 級 equivariance**（§9 の #7 rebase-pinning）＝ §6.5 の
    cut-anchored relation engine（cutP/bumpAt/locale cut_bump、W1 で多日と判定）に依存しうる。

**結論**: Red_IncrFirst・冪等性・keystone は全て **B1(再分解) + B2(Red_IncrFirst engine instance)**
という単一コアに収束。これが §6.5後半/§6.6 の真のボトルネック。次: B1/B2 を独立並列で
直接攻め（既存 redB_*/njA_* で閉じるか、engine が要るか判定）。engine 必須なら deliberate に
cut-anchored relation engine を段階構築。

## 11. 確定: 全クラスタは cut-anchored Red_IncrFirst engine に収束 (2026-06-03)

B1/B2 を直接攻めた結果、**両方とも同一の engine に blocker**:
- **B1** 残差 = `Red(NJ(Red M)J) = Red(NJ M J)`（NJ(Red M)J≠NJ(M)J が 529/3169、入力は違うが
  Red が collapse）= `Red(IncrFirst X)=Red X` のインスタンス = 未証明 `p_6_5_Red_IncrFirst`。
- **B2** = `Red(coreReduce(Red M)) = Red(coreReduce M)`。2引数は **Lng/TrMax/le0/full nextR
  を共有**し、raw row-1 と branch row-0 head のみ**非一様に**異なる(597/756)が Red が collapse。
  tail_bump は row1_eq 必須＋値写像が uniform `bumpv n`(+1) なので**不適**。

**4つの独立解析（W1, idem-crux, B1, B2）が全て同一結論**: §6.5後半/§6.6 の全命題
（Red_IncrFirst・冪等性・(e)簡約性と左端の関係・簡約性の切片への遺伝性・keystone）は
**単一の cut-anchored relation engine に収束**。本質は «Red は nextR(祖先構造)で決まる»:
`nextR M = nextR M' ∧ Lng一致 ∧ le0一致(等) ⟹ Red M = Red M'`。IncrFirst/coreReduce-of-Red
は nextR を保つので Red を collapse する。

engine 実装案（W1 設計 + tail_bump テンプレ@25718）:
- (A) `cutP`/`bumpAt` 定義 + `bumpAt_nextrel0_eq`/`nextrel1` 不変性。**非一様値写像**を許容
  （tail_bump の uniform bumpv を一般化）。
- (B) locale `cut_bump`（tail_bump の cut 版）で le0/le1/nextR/leR/TrMax/zeroT/monoT/multiT/Pcut 共有。
- (C) `Red_IncrFirst_joint` を Red.pinduct で → `p_6_5_Red_IncrFirst`(t=0)。
- 以後 B1/B2/idem/(e)/遺伝性/keystone は短い組立てで落ちる。

→ 残る唯一のボトルネック。deliberate に段階構築（multi-day）。設計駆動（fan-out でない）。

## 12. Red_IncrFirst engine 完成 → cascade は interlocking cluster (2026-06-03)

**`p_6_5_Red_IncrFirst` green**（commit ed43f8e）: cut_bump locale + `fin_cut_bump_Red`
(Red.pinduct, cut量化, ~490行) + B2。プロジェクト最難の multi-week ボトルネック解消。

だが cascade は即座でない。idempotency `idem_nonmulti` を Red.pinduct で攻めると、
**3枝(zeroT/core-trunk/shift)は green**(commit 711ed24)だが残り2枝は **Red_IncrFirst とは
別の engine 義務**:
- **B1(idem) core-nontrunk**: 外側 Red の**再分解**（出力 `diagSeq@concat(IncrFirst^eJ(Red NJ))`
  を Red が固定）。残差 `Red(NJ(Red M)J)=Red(NJ M J)` は Red_IncrFirst で落ちるが、**outer
  re-decomposition alignment が未構築**。かつ idem IH は ¬multiT 限定で NJ M J が multiT
  になりうるため不適 → **full idempotency**（multiT 込み）が要り、その multiT 枝は
  `P(Red M)=map Red(P M)`(= p_6_5_P_Red, §6.5 sorry)に依存。
- **B2(idem) m10>0**: `Red(coreReduce(Red M))=Red(coreReduce M)` の**非一様 cut**（row-1 head
  597/756 で非一様）。uniform bumpv の fin_cut_bump_Red 不適。general «Red は nextR で決まる»
  congruence が要る（cut_bump は IncrFirst の uniform 特殊例）。

→ idem/keystone は interlocking cluster（idem ↔ P_Red ↔ Red_Pred ↔ outer-redecomp ↔
非一様-cut）。**もう一段の engine フェーズ**（general nextR-congruence もしくは個別 pinning 群）。
keystone backward の mono 枝も同じ機構を要求。
