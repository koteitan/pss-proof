import «6».«6.8-d1pos-final»
import «7».«7.1-buchholz-wf»
import «7».«7.3-Trans-leftmost»
import «8».«8.5-exchV-props»
import «8».«8.7-OT-examples»
import «8».«8.7-OT-scb-recursive»
import «8».«8.7-OT-dom-hereditary»
import «8».«8.7-OT-tail-annihilable»
import «8».«8.7-const00-Trans»
import «8».«8.7-Trans-preserves-OT»
import «8».«8.7-fseq-descend»
import «8».«8.7-fseq-descend-props»
import «8».«8.7-fseq-descend-props2»

/-!
# §8.7 定理（標準形ペア数列システムの停止性） — 主定理

**このファイルは本プロジェクトの終端の地図である。**

- 原文: `tmp/content.md` 5851（§8.7「主結果」）:
  「定理（標準形ペア数列システムの停止性）: \(ST_{PS} \times \mathbb{N}_+ \subset
  \mathrm{Dom}(F)\) である。」
  逐語形は `p_8_7_termination` (isabelle/pss_paper.thy:2329)。
  **訂正: なし**（`corrections.md` / `corrections-old.md` とも §8.7 の本定理を
  対象とする項目は無い。A26/A27/A38 は §8.7 の**補題**に対する取り下げ済み項目で、
  本定理には無関係）。
- Isabelle:
  * `y5_Fdom` (isabelle/layerC/pss_scratch.thy:14344) — 原文形（`Fdom f M n`）。
  * `y5_PSS_wf` (同 :14197) — 我々の形（`wf y3_PSSrel`）。
  * `y5_PSS_acc` (同 :14200)、`y5_Trans_OT_B` (同 :14205)、
    `y5_Trans_descend` (同 :14208)。
  * 組み立ての本体は `y4_PSS_wf_of_KK` (同 :13806)。
  Isabelle 側は **仮定ゼロ・sorry ゼロ**で閉じている。
- 状態: 🤖 **GREEN-MODULO 22**（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  下の `TerminationResidual` の 22 フィールドが、Lean 版の停止性定理と
  **無条件**の停止性定理を隔てる**全て**である。

## 組み立て（Isabelle `y4_PSS_wf_of_KK` / `y5_Fdom` と 1:1）

停止性定理は 2 本柱＋順序数側の整礎性の 3 点から出る。**3 点目は既に無条件**:

| 部品 | Lean | 仮定 |
|---|---|---|
| 整礎性 `wf(OT_B, <_B)` | `buchholz_wf` (`7.1-buchholz-wf`:230) | **ゼロ** |
| OT 柱 `Trans(ST_PS) ⊆ OT_B` | `Trans_preserves_OT` (`8.7-Trans-preserves-OT`:489) | `OTdisp_*` 12 本 |
| 降下柱 `Trans(M[n]) < Trans(M)` | `p_8_7_fseq_descend` (`8.7-fseq-descend`:808) | `FseqDesc_*` 16 本 |

`buchholz_wf` は [Buc1] 補題 2.2 **そのものではない**（あちらは意味論的主張で
ここでは表現できない）。ここで必要なのは `(OT_B, <_B)` の整礎性という
**構文的主張**だけで、それは `7.1-buchholz-wf` が仮定ゼロで与えている。
これは Isabelle の `y4_buc1_2_2_OT_B_wf` (pss_scratch.thy:13700) と同じ立場である
（「引用の retire」）。

降下柱の 16 本は `8.7-fseq-descend-props` / `-props2` が配線済み:

| `FseqDesc_*` | 配線 | 残差 |
|---|---|---|
| `m_8_2_subexpr_component_Pred_Adm0_clause1` | `..._holds` (props) | **0** |
| `m_8_6_TransCondVI_oper_descend_engine` | `..._holds` (props) | **0** |
| `m_6_2_P_oper_2` | `..._holds` (props) | **0** |
| `m_8_6_rcseq_Trans` | `..._holds` (props2) | **0** |
| `m_8_3_TransCondII_oper_descend_engine` | `..._holds` (props2) | **0** |
| `Trans_preserves_OT` | `..._of_OTdisp` (props) | OT 柱 12 本（＝再利用） |
| `exchIII` / `exchIV` | `..._of_Exch84` (props) | `Exch84_*` 2 本 |
| `exchVI` | `..._of_CondVI` (props) | `CondVI*` 2 本 ＋ `TransPreservesOT` |
| `exchI` | `..._of_CondI` (props2) | `CondI_masterCF` 1 本 |
| `exchII` | `..._of_CondII` (props2) | `CondII_masterCF` 1 本 |
| `exchV` / `m_8_5_TransCondV_oper_descend_engine` | `..._of_ExchV` (props2) | `ExchV_*` 6 本 → **2 本**（下記） |
| `operI_j0zero_trans_mult` | **未配線** | 自身 |
| `f7x_Trans_append_Pblocks` | **未配線** | 自身 |
| `m_7_3_Trans_leftmost_2` | **本ファイルで配線**（下記） | **0** |

🎯 **本ファイルで残差が 27 → 22 に減った 2 点**（props / props2 の執筆時点では
ツリーに無かった／見落とされていた資産。**name-grep ではなく content-grep で発見**）:

- **`m_7_3_Trans_leftmost_2` は落ちる（27 → 26）**。props2 のヘッダは
  「ビルド済みツリーに twin 無し＝実移植が要る（content-grep 済）」と書いているが、
  **これは現状では誤り**: `«7».«7.3-Trans-leftmost»`（ビルド済み）が
  `m_7_3_Trans_leftmost_2_dropin` (:405) を公開しており、`FseqDesc_m_7_3_Trans_leftmost_2`
  と**型が一致する**（同ファイル :395 の注記は「props 側で 1 行書けば delta 展開で
  通る」＝まさにこれ）。§7 → §8 の import 方向のため 7.3 側が `FseqDesc_…` の名前を
  参照できず、props2 側が拾い損ねていた。本ファイルが両者を import して接続する。
- **`ExchV_*` は 6 本 → 2 本（26 → 22）**。`«8».«8.5-exchV-props»（ビルド済み）が
  `ExchV_condV_setup` / `ExchV_scbdec_c1_shape` / `ExchV_t2_nonzero_condV` /
  `ExchV_scbdec_fseq_condV` の **4 本を無条件に discharge** 済みで、
  `ExchV_scbdec_adm_forms` を `ExchVres_adm_M_tower`（塔の閉形式のみ）に削減している。
  残るのは `ExchVres_adm_M_tower` と `ExchV_nf3x`（§8.4 クラスタ、8.5 の scope 外）。

**削減できなかったもの**（調査済み。カウントが減らないので採らなかった）:
`«8».«8.3-condII-masterCF»` は `CondII_masterCF`(1 本) を `CondII_step` ＋
`CondII_TailvalAll`(2 本) に**増やす**ので不採用。`«8».«8.6-condVI-close»` の
`condVIAdmTowerScb_of_scbforms_v6` / `condVIExchNadm_of_scbforms_v6` は
`CondVI*` 2 本を `CondVI_scbdec_*_forms_v6` 2 本に置き換えるだけ（1:1）なので不採用。
`OTdisp_*` 12 本・`CondI_masterCF`・`Exch84_*` 2 本・`operI_j0zero_trans_mult` ・
`f7x_Trans_append_Pblocks` には**ツリー内に discharger が無い**（全 Prop について
content-grep で確認済み）。

🎯 **`TransPreservesOT`（`8.6-Trans-fseq-condVI`:247）は本ファイルで消える**:
OT 柱の `Trans_preserves_OT` と**同一形**（`∀ M, STPS M → Trans M ∈ OT_B`）なので、
`OTdisp_*` 12 本から供給できる（`8.7-Trans-preserves-OT` は 8.6 を import すると
循環するので自分では落とせなかった）。**したがって降下柱と OT 柱の残差は合流し、
残差は 22 本**（OT 12 ＋ condI 1 ＋ condII 1 ＋ Exch84 2 ＋ ExchV 2 ＋ CondVI 2
＋ 未配線 2）であって 28 本ではない。

## Isabelle 版より短くなった点

Isabelle の `y5_Fdom` は `ST_PS` 列の非空性のために `y5_take_concat_ne` /
`y5_Lng_Pred_pos` / `y5_Lng_oper_pos` / `y5_ST_PS_Lng_pos`（`oper` の 3 枝を
展開する ~120 行）を要した。Lean では §6.7 の `ST_PS ⊆ RT_PS`（`STPS_RTPS`）と
`RT_PS ⊆ T_PS`（`RTPS_TPS`）が既にあり、`TPS M ≡ M ≠ []` なので
`Lng_pos_term` の 2 行で済む。`oper` を展開する必要は無い。

## 空虚性（この定理は空虚に緑ではないか？）

条件付き定理は仮定が充足不能なら無価値なので、22 本の出所を確認した。
**結論: `TerminationResidual` は空虚な仮定の束ではない。** ただし 2 点留保がある。

- 22 本は**すべて Isabelle 側で証明済み**（各フィールドの docstring に
  `pss_wip.thy` の行番号を付した）。証明済みの主張は充足可能なので、
  束としても充足可能である。
- 数値監査も家ごとに存在する: `OTdisp_*` 12 本 →
  `python/audit_8_7_trans_preserves_OT.py`（標準形 18318 本）、`CondI_masterCF` →
  `python/audit_81_condI.py`、`CondII_masterCF` → `python/audit_83_condII_masterCF.py`、
  `ExchV_*` → `python/audit_85_condV_engine.py`。
  `Exch84_*` / `CondVI*` / 未配線 2 本には専用監査が**無い**（留保 1）。
- 🚨 **留保 2 — `8.7-fseq-descend`:50 のヘッダは過大主張**。「全 16 本は標準形
  プール上で `#guard` 数値検証済み＝空虚ではない」とあるが、当該ファイルの
  `#guard` は 1 本しかなく、`8.3-TransCondII-engine`:73 が後から
  **exchII については過大主張**と明記している（`OTdisp_exchII` は
  `audit_8_7_trans_preserves_OT.py` が "not covered by pool" として未検証扱い。
  条件 (II) は `ST_PS` 上に 1 例も見つからない＝ST_PS 上では空虚の可能性が高い）。
  **これは本定理の健全性には影響しない**: `CondII_masterCF` の仮定は `ST_PS`
  ではなく `RT_PS` で、そこには実例がある（`(0,0)(1,1)(2,2)(2,0)`）ので
  仮定として空虚ではない。条件 (II) 枝が `ST_PS` 上で空回りするだけである。

## 🚨 `Pred_oper0` は使っていない（死路）

`8.7-Pred-oper0` は未証明で、Isabelle は `Pred_oper0` が**標準入力上で偽**である
ことを記録している（反例 `M = (0,0)(1,1)(2,1)`、`isabelle/memo.md`）。原文 §8 の
証明にはこの gap があるが**定理自体は健全**で、Isabelle は Σ_B 降下和ルートで
迂回している。本ファイルもそのルート（`p_8_7_fseq_descend` の dispatcher）で、
`Pred_oper0` を経由しない。

## 依存（ビルド済みのみ import）

`7.1-buchholz-wf`（`buchholz_wf`）、`8.7-Trans-preserves-OT`
（`OTdisp_*` 12 本 / `Trans_preserves_OT`）、`8.7-fseq-descend`
（`FseqDesc_*` 16 本 / `p_8_7_fseq_descend`）、`8.7-fseq-descend-props`＋`-props2`
（配線 13 本）、`7.3-Trans-leftmost`（`m_7_3_Trans_leftmost_2_dropin`: 未配線
`FseqDesc_*` の 1 本を落とす）、`8.5-exchV-props`（`condV_setup_holds` /
`c1_shape_holds` / `t2_nonzero_condV_holds` / `fseq_condV_holds` / `adm_forms_holds`
/ `ExchVres_adm_M_tower`: `ExchV_*` を 6 本 → 2 本に削減）、
`6.8-d1pos-final`（`rankSuccD1posLeg_proved`: `RankSuccD1posLeg` を
閉じ、残差リストから外すため）、`8.7-OT-examples` / `-OT-scb-recursive` /
`-OT-dom-hereditary` / `-OT-tail-annihilable` / `8.7-const00-Trans`
（§8.7 の補題群。主定理では使わないが、**§8.7 全体が同時 import 可能である
ことの検証**を兼ねる＝名前衝突の早期検出）。

名前衝突の監査は `python/audit_8_7_termination.py`（import 閉包を歩いて
同名別主張を検出し、残差 `Prop` を列挙する）。
-/

namespace PSS

/-! ## 0. ヘッダ健全性の canary

§8.7 の全ファイル ＋ §6.8 ＋ §7.1 ＋ §8.5 の brick 群を同時 import している。
**同名別主張の二重宣言はエラーを出さずにヘッダを毒する**（`trivial` すら
Unknown identifier になる）ので、素の `trivial` と import 先の識別子の両方を
canary として置く。ここが通れば import 閉包に名前衝突は無い。 -/

private example : True := trivial
private example : RankSuccD1posLeg := rankSuccD1posLeg_proved

/-! ## 1. 展開関係（Isabelle `y3_PSSrel`, pss_scratch.thy:11604）

`y3_PSSrel = {(N, M). M ∈ ST_PS ∧ 1 < Lng M ∧ (∃n. 1 ≤ n ∧ N = M[n])}`。
Isabelle の `(x, y) ∈ r` は「`x` が小さい」なので、Lean の `WellFounded` の
引数順（`r a b` ＝ `a` が小さい）と一致する。 -/

/-- ペア数列システムの 1 手関係: 非退化な標準形 `M` から `M[n]`（`n ≥ 1`）へ。 -/
def PSSstep (N M : PS) : Prop :=
  STPS M ∧ 1 < Lng M ∧ ∃ n, 1 ≤ n ∧ N = oper M n

/-! ## 2. 残差（22 本）

停止性定理と我々を隔てる**全て**。各フィールドは既存ファイルが公開している
名前付き `Prop` そのもの（新しい主張は 1 つも導入していない）。
Isabelle 側では全て証明済みなので、移植すればそのまま外れる。 -/

/-- **§8.7 停止性定理の残差 22 本**。これが潰れた瞬間、停止性定理は無条件になる。

内訳: OT 柱 12（`OTdisp_*`）＋ 条件 (I) 1 ＋ 条件 (II) 1 ＋ 条件 (III)/(IV) 2
＋ 条件 (V) 2（`ExchVres_adm_M_tower` / `ExchV_nf3x`）＋ 条件 (VI) 2
＋ 未配線 `FseqDesc_*` 2。 -/
structure TerminationResidual : Prop where
  /-- OT 柱 (1/12)。Isabelle `exchI`（`scx_condI_exchange1` が供給）。 -/
  otExchI : OTdisp_exchI
  /-- OT 柱 (2/12)。Isabelle `exchII`（`c2sx_exchange_ex_condII_of_tailval`）。 -/
  otExchII : OTdisp_exchII
  /-- OT 柱 (3/12)。Isabelle `OTint`（条件 (III)/(IV)/(V) の内部枝）。 -/
  otInt : OTdisp_OTint
  /-- OT 柱 (4/12)。Isabelle `OTpred`（`opx_OTpred_of_residuals`）。 -/
  otPred : OTdisp_OTpred
  /-- OT 柱 (5/12)。Isabelle `OTmulti`（`opx_OTmulti`）。 -/
  otMulti : OTdisp_OTmulti
  /-- OT 柱 (6/12)。Isabelle `otx_zerocol_predval` (pss_wip.thy:85474)。 -/
  otZeroCol : OTdisp_zerocol_predval
  /-- OT 柱 (7/12)。Isabelle `m_8_1_Trans_fseq_condI_n1`。 -/
  otCondIn1 : OTdisp_Trans_fseq_condI_n1
  /-- OT 柱 (8/12)。Isabelle `otx_condI_j0z_eq` (pss_wip.thy:85292)。 -/
  otCondIj0 : OTdisp_condI_j0z_eq
  /-- OT 柱 (9/12)。Isabelle `otx_condI_j1eq1_eq` (pss_wip.thy:85516)。 -/
  otCondIj1 : OTdisp_condI_j1eq1_eq
  /-- OT 柱 (10/12)。Isabelle `otx_condVI_j1eq1_eq` (pss_wip.thy:85582)。 -/
  otCondVIj1 : OTdisp_condVI_j1eq1_eq
  /-- OT 柱 (11/12)。Isabelle `otx_condVI_adm_eq` (pss_wip.thy:85236)。 -/
  otCondVIadm : OTdisp_condVI_adm_eq
  /-- OT 柱 (12/12)。Isabelle `otx_condVI_nadm_eq` (pss_wip.thy:85260)。 -/
  otCondVInadm : OTdisp_condVI_nadm_eq
  /-- 条件 (I) の交換則の核。Isabelle `scx_condI_j0pos_masterCF` (pss_wip.thy:83639)。 -/
  condI : CondI_masterCF
  /-- 条件 (II) の交換則の核。Isabelle `c2sx_condII_masterCF` (pss_wip.thy:87430)。 -/
  condII : CondII_masterCF
  /-- 条件 (III)/(IV) の交換則 (1/2)。`8.4-Trans-fseq-condIII-IV`:121。 -/
  exch84producer : Exch84_condIIIIV_producer
  /-- 条件 (III)/(IV) の交換則 (2/2)。`8.4-Trans-fseq-condIII-IV`:152。 -/
  exch84noParent : Exch84_condIIIIV_noParent
  /-- 条件 (V) (1/2)。`8.5-exchV-props`:412 の `ExchVres_adm_M_tower`
  ＝ Isabelle `m_8_5_scbdec_adm_forms` (pss_wip.thy:57556) の結論 (4)(5) のみ
  （塔の閉形式 ＝ `m_8_4_oper_props_5` 同 :54005 ＋ `s84x_L` 帰納）。
  もとの `ExchV_scbdec_adm_forms` は `adm_forms_holds` がこれから供給する
  （(1)(2)(3) は `add_scb_marked` ＋ `fseq_condV_holds` で既に落ちている）。 -/
  exchVresAdmTowers : ExchVres_adm_M_tower
  /-- 条件 (V) (2/2)。`8.5-Trans-fseq-condV`:138。Isabelle `atx_nf3x`
  (pss_wip.thy:86273)。§8.4 クラスタ側の brick で、`8.5-exchV-props` の
  scope 外として唯一残ったもの。 -/
  exchVnf3x : ExchV_nf3x
  /-- 条件 (VI) の許容枝。`8.6-Trans-fseq-condVI`:220。 -/
  condVIadmTower : CondVIAdmTowerScb
  /-- 条件 (VI) の非許容枝。`8.6-Trans-fseq-condVI`:236。 -/
  condVInadm : CondVIExchNadm
  /-- 未配線 (1/3)。Isabelle `operI_j0zero_trans_mult` (pss_wip.thy:36977)。
  ⚠️ `8.1-Trans-fseq-condI` は**これを消費する側**であって供給しない。 -/
  operIj0zeroMult : FseqDesc_operI_j0zero_trans_mult
  /-- 未配線 (2/2)。Isabelle `f7x_Trans_append_Pblocks` (pss_wip.thy:51888)。 -/
  transAppendPblocks : FseqDesc_f7x_Trans_append_Pblocks

/-! ## 3. OT 柱 — `Trans(ST_PS) ⊆ OT_B`（Isabelle `y5_Trans_OT_B`） -/

/-- Isabelle `y5_Trans_OT_B` (pss_scratch.thy:14205)。
原文「補題（`Trans` が標準形を保つこと）」(§8.7, 原文 6122)。
`8.7-Trans-preserves-OT`:489 の `Trans_preserves_OT` に残差の 12 本を渡すだけ。 -/
theorem Trans_STPS_OT_B (H : TerminationResidual) (M : PS) (hM : STPS M) :
    Trans M ∈ OT_B :=
  Trans_preserves_OT H.otExchI H.otExchII H.otInt H.otPred H.otMulti H.otZeroCol
    H.otCondIn1 H.otCondIj0 H.otCondIj1 H.otCondVIj1 H.otCondVIadm H.otCondVInadm
    M hM

/-- `8.6-Trans-fseq-condVI`:247 の名前付き仮定 `TransPreservesOT` は OT 柱と
**同一形**なので、残差の 12 本から供給できる（＝独立な残差ではない）。 -/
private theorem transPreservesOT_term (H : TerminationResidual) : TransPreservesOT :=
  fun M hM => Trans_STPS_OT_B H M hM

/-! ## 4. 降下柱 — `Trans(M[n]) < Trans(M)`（Isabelle `y5_Trans_descend`）

`8.7-fseq-descend` の 16 本を、props / props2 の配線と残差 27 本で埋める。
5 本は配線が**無条件**なので残差に現れない。 -/

/-- 条件 (V) の 6 本のうち 4 本は `8.5-exchV-props` が**無条件**で discharge
済み（`condV_setup_holds` / `c1_shape_holds` / `t2_nonzero_condV_holds` /
`fseq_condV_holds`）、`ExchV_scbdec_adm_forms` は `adm_forms_holds` が
`ExchVres_adm_M_tower` から供給する。残差に出るのは `ExchVres_adm_M_tower` と
`ExchV_nf3x` の 2 本だけ。 -/
private theorem exchVadmForms_term (H : TerminationResidual) :
    ExchV_scbdec_adm_forms :=
  adm_forms_holds H.exchVresAdmTowers

private theorem fseqDescTOT_term (H : TerminationResidual) :
    FseqDesc_Trans_preserves_OT :=
  FseqDesc_Trans_preserves_OT_of_OTdisp H.otExchI H.otExchII H.otInt H.otPred
    H.otMulti H.otZeroCol H.otCondIn1 H.otCondIj0 H.otCondIj1 H.otCondVIj1
    H.otCondVIadm H.otCondVInadm

/-- Isabelle `y5_Trans_descend` (pss_scratch.thy:14208)。
原文「補題（基本列の降下性）」(§8.7, 原文 5869)。 -/
theorem Trans_fseq_descend (H : TerminationResidual) (M : PS) (n : ℕ)
    (hM : STPS M) (hn : 1 ≤ n) (hL : 1 < Lng M) :
    lessBT (Trans (oper M n)) (Trans M) = true :=
  p_8_7_fseq_descend
    (fseqDescTOT_term H)
    (FseqDesc_exchI_of_CondI H.condI)
    (FseqDesc_exchII_of_CondII H.condII)
    (FseqDesc_exchIII_of_Exch84 H.exch84producer H.exch84noParent)
    (FseqDesc_exchIV_of_Exch84 H.exch84producer H.exch84noParent)
    (FseqDesc_exchV_of_ExchV (exchVadmForms_term H) c1_shape_holds
      condV_setup_holds t2_nonzero_condV_holds H.exchVnf3x fseq_condV_holds)
    (FseqDesc_exchVI_of_CondVI H.condVIadmTower H.condVInadm
      (transPreservesOT_term H))
    H.operIj0zeroMult
    FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds
    FseqDesc_m_8_6_rcseq_Trans_holds
    FseqDesc_m_8_3_TransCondII_oper_descend_engine_holds
    (FseqDesc_m_8_5_TransCondV_oper_descend_engine_of_ExchV
      (exchVadmForms_term H) c1_shape_holds condV_setup_holds
      t2_nonzero_condV_holds H.exchVnf3x fseq_condV_holds)
    FseqDesc_m_8_6_TransCondVI_oper_descend_engine_holds
    FseqDesc_m_6_2_P_oper_2_holds
    H.transAppendPblocks
    m_7_3_Trans_leftmost_2_dropin
    M n hM hn hL

/-! ## 5. 停止性（我々の形）— `wf y3_PSSrel`（Isabelle `y5_PSS_wf`）

Isabelle `y4_PSS_wf_of_KK` (pss_scratch.thy:13806) の `wf_subset ∘ wf_inv_image`
を Lean の `Subrelation.wf ∘ InvImage.wf` に置き換えただけ。 -/

/-- Isabelle `y4_PSS_wf_of_KK` の `sub`（`y3_PSSrel ⊆ inv_image {…} Trans`,
pss_scratch.thy:13823）。3 つの成分がちょうど 2 本柱に対応する:
`Trans (M[n]) ∈ OT_B`（OT 柱）、`Trans M ∈ OT_B`（OT 柱）、
`Trans (M[n]) <_B Trans M`（降下柱）。 -/
private theorem PSSstep_invImage_term (H : TerminationResidual) {N M : PS}
    (h : PSSstep N M) :
    InvImage (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) Trans N M := by
  obtain ⟨hST, hL, n, hn, rfl⟩ := h
  show Trans (oper M n) ∈ OT_B ∧ Trans M ∈ OT_B
    ∧ lessBT (Trans (oper M n)) (Trans M) = true
  exact ⟨Trans_STPS_OT_B H _ (STPS.oper hST n hn), Trans_STPS_OT_B H M hST,
    Trans_fseq_descend H M n hST hn hL⟩

/-- Isabelle `y5_PSS_wf` (pss_scratch.thy:14197): `wf y3_PSSrel`。

`PSSstep` を `Trans` で `(OT_B, <_B)` に引き戻す（Isabelle の
`wf_subset[OF wf_inv_image[OF wfR] sub]`）。整礎性 `buchholz_wf` は**仮定ゼロ**
なので、この定理の仮定は 2 本柱の残差 `H` だけである。 -/
theorem PSS_wf (H : TerminationResidual) : WellFounded PSSstep := by
  have hinv : WellFounded
      (InvImage (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) Trans) :=
    InvImage.wf Trans buchholz_wf
  refine ⟨fun M => ?_⟩
  induction M using hinv.induction with
  | _ x IH => exact Acc.intro x (fun y hy => IH y (PSSstep_invImage_term H hy))

/-- Isabelle `y5_PSS_acc` (pss_scratch.thy:14200)。
`STPS M` は Isabelle 版との 1:1 のために取るが、Lean では不要
（`PSS_wf` が全ての `M` について `Acc` を与える）。 -/
theorem PSS_acc (H : TerminationResidual) (M : PS) (_hM : STPS M) :
    Acc PSSstep M :=
  (PSS_wf H).apply M

/-! ## 6. 停止性（原文の形）— `ST_PS × ℕ₊ ⊆ Dom(F)`（Isabelle `y5_Fdom`）

Isabelle `y5_Fdom` (pss_scratch.thy:14344) の `acc` 帰納をそのまま写す。
Isabelle が必要とした `ST_PS` 列の非空性（`y5_ST_PS_Lng_pos`、`oper` の 3 枝の
展開 ~120 行）は、Lean では §6.7 の `ST_PS ⊆ RT_PS ⊆ T_PS` から 2 行で出る。 -/

/-- Isabelle `y5_ST_PS_Lng_pos` (pss_scratch.thy:14327) に対応。
`STPS M → RTPS M → TPS M ≡ M ≠ []` の連鎖で済むので、`oper` の展開は不要。 -/
private theorem Lng_pos_term (M : PS) (hM : STPS M) : 1 ≤ Lng M :=
  List.length_pos_of_ne_nil (RTPS_TPS M (STPS_RTPS M hM))

/-- **主定理（原文形）**。原文 §8.7「定理（標準形ペア数列システムの停止性）」
(`tmp/content.md` 5851): \(ST_{PS} \times \mathbb{N}_+ \subset \mathrm{Dom}(F)\)。
逐語形は `p_8_7_termination` (isabelle/pss_paper.thy:2329)、
証明は `y5_Fdom` (isabelle/layerC/pss_scratch.thy:14344)。

補助写像 \(f : \mathbb{N}_+ \to \mathbb{N}_+\)（原文 346）は正値性
`1 ≤ k → 1 ≤ f k` でモデル化する（Isabelle と同一の綴り）。 -/
theorem p_8_7_termination (H : TerminationResidual) (f : ℕ → ℕ) (M : PS) (n : ℕ)
    (hM : STPS M) (hn : 1 ≤ n) (hf : ∀ k, 1 ≤ k → 1 ≤ f k) :
    Fdom f M n := by
  have MAIN : ∀ x : PS, Acc PSSstep x → STPS x → ∀ m, 1 ≤ m → Fdom f x m := by
    intro x hacc
    induction hacc with
    | intro y _hy IH =>
      intro hyST m hm
      by_cases hL : 1 < Lng y
      · -- 展開枝: `y[m]` は 1 手小さい標準形。`f m ≥ 1` で IH が回る。
        exact Fdom.step hL
          (IH (oper y m) ⟨hyST, hL, m, hm, rfl⟩ (STPS.oper hyST m hm)
            (f m) (hf m hm))
      · -- 停止枝: `Lng y = 1`。`ST_PS` 列は空でないので `Lng y ≥ 1`。
        exact Fdom.base (by have := Lng_pos_term y hyST; omega)
  exact MAIN M (PSS_acc H M hM) hM n hn

/-- 原文の集合包含 \(ST_{PS} \times \mathbb{N}_+ \subset \mathrm{Dom}(F)\) を
集合の言葉でそのまま述べたもの（`p_8_7_termination` の言い換え）。 -/
theorem STPS_prod_pos_subset_Fdom (H : TerminationResidual) (f : ℕ → ℕ)
    (hf : ∀ k, 1 ≤ k → 1 ≤ f k) :
    {p : PS × ℕ | STPS p.1 ∧ 1 ≤ p.2} ⊆ {p : PS × ℕ | Fdom f p.1 p.2} :=
  fun p hp => p_8_7_termination H f p.1 p.2 hp.1 hp.2 hf

#print axioms Trans_STPS_OT_B
#print axioms Trans_fseq_descend
#print axioms PSS_wf
#print axioms PSS_acc
#print axioms p_8_7_termination
#print axioms STPS_prod_pos_subset_Fdom

end PSS
