# memo.md — Lean 版の設計メモ

task.md（骨格）と同じツリーに、**訂正番号・Isabelle 側の対応補題・罠**を注釈したもの。
ユーザーは読まない。エージェント（および引き継ぐ codex）向け。

---

## 0. 前提：Isabelle 版はもう終わっている

`isabelle/` には **停止性定理の完全な証明**がある（仮定ゼロ・`sorry` ゼロ、ML 監査で強制）。

- 主定理: `y5_PSS_wf`（`wf y3_PSSrel`）と原文形 `y5_Fdom`（`isabelle/layerC/pss_scratch.thy`）
- 原文の全命題の逐語転記: `isabelle/pss_paper.thy`（全部 `sorry`。**偽の主張も含む**。これは仕様）
- 我々の証明: `isabelle/pss_mechanized.thy`（`m_*`）＋ `layerB/pss_wip.thy` ＋ `layerC/pss_scratch.thy`
- 原文の誤り 30 件: `corrections.md` ／ 取り下げ 17 件: `corrections-old.md`

**したがって Lean 化は「未知の数学」ではなく「既知の証明の移植」である。**
詰まったら必ず Isabelle 側に答えがある。**自分で新しい証明を発明しようとする前に grep しろ。**
（Isabelle 版で 4 ラウンド連続、「穴だ」と思ったものが既に repo にあった、という事故を起こしている。）

## 1. 全体方針

1. **定義層 `PSS/` を先に完成させる。** ここが原文と食い違うと、下流の命題を全部証明し直しになる。
   定義の忠実性は `python/red_model.py` / `python/trans_model.py`（数値検証済みの正本）と
   `#eval` で突き合わせて確認する（下記 §2）。
2. 命題は **§5 → §6 → §7 → §8 の順**。下流は上流に依存する。
   §6 を固めずに §7/§8 に手を出すと手戻りする（Isabelle 版で確認済みの方針）。
3. **原文が偽の命題は、訂正後の主張を証明し、原文版の反例も同じファイルに機械証明で残す。**
   Lean は `decide` が強いので、有限反例は Isabelle より遥かに楽に書ける。ここは Lean の勝ち筋。
4. 並列化は Workflow のみ。検証は kimina（step.md §4）。

## 2. 定義層の設計（`PSS/`）

| 概念 | Lean での型 | Isabelle 側 |
|---|---|---|
| ペア数列 | `abbrev PS := List (ℕ × ℕ)` | `pss_defs.thy` の `('a × 'a) list` |
| `T_PS` | `def TPS (M : PS) : Prop := M ≠ []` | `T_PS = {M. M ≠ []}` |
| `Lng` | `M.length` | `Lng` |
| 親子 `≤_M` | `LeM : PS → ℕ → ℕ → Prop` | `leR M 0 i j` |
| 許容性 | `adm M j` | `adm` |
| 基点 | `Marked : PS × ℕ → Prop`（`adm` かつ `leR M 0 m (Lng M - 1)`） | `Marked` |
| `Red` | 整礎再帰。`termination_by` を書く | `Red`（`function` + 停止性証明） |
| Buchholz 項 | `inductive BT` | `T_B` |
| scb 分解 | `Σ` 上の文字列＝`List Sym` | `scb_decomp` |
| `Trans` / `Mark` | 相互再帰。`termination_by` | `Trans` / `Mark` |

**忠実性の確認方法**（定義を書いたら必ずやる）:

```lean
-- python/red_model.py と同じ値になるか
#eval Red [(0,0),(0,2)]        -- 期待: [(0,0),(2,2)]   ← Red は冪等でない（A4）
#eval Red [(0,0),(2,2)]        -- 期待: [(0,0),(1,1)]
```

`Red` が冪等でないこと（**A4。この論文の全ての誤りの根**）を最初に `decide` で確認しておくと、
下流の「原文どおりに書いたら偽」を早期に検出できる。

## 3. 移植上の罠（Isabelle 版で払った授業料）

- **`Red` は `T_PS` 上で冪等でない**（A4）。原文の §6.5 の系群・§7.4 の命題群は、
  そのままだと **偽**。定義域を `RT_PS`（簡約形）に制限する必要がある。
  A4 / A41 / A45 / A46 / A47 は **同一の欠陥の別の顔**であって、独立な 5 件ではない。
- **`operB` は Buchholz の基本列**。原文の脚注 [30] は転置の誤植（A23）。
  Buchholz 原論文 [Buc1] の定義に合わせること。ここを誤読して 11 件の偽「訂正」を出した前科がある。
- **数値検証で成分の上限を小さく取るな。** 反例は成分 6〜9 に潜んでいる。
  「成分 < 3」「成分 < 4」の走査で **13 回の偽陽性**を出した。
- **ランダムなペア数列はほぼ簡約形にならない。** 簡約形の性質を検証したいなら
  `diagSeq` を基本列で閉じて**本物の標準形プール**を作る（`python/` の該当スクリプト参照）。
- **`sorry` は Lean のビルドを止めない。** ✅ の判定は `check_lean.py` の rc=0 と
  `#print axioms` の 2 段構え（step.md §1）。**Isabelle の ML 監査に相当するものを自前で回せ。**

## 4. 死路（再走禁止）

Isabelle 版で潰した偽命題・行き止まり。**同じ道を Lean で走り直しても偽のまま。**

- `Red` の冪等性を `T_PS` で示そうとする（A4。反例 `(0,0)(0,2)`）
- `RT_PS = Im(Red)` を示そうとする（A41。偽）
- `Trans` の単項性保存を先頭 P 成分零項込みで示そうとする（A16。反例 `(0,0)(0,0)`）
- §7.4 の `Mark`/`Trans` と `<^NextAdm` の関係を `T_PS` で示そうとする（A45/A46/A47。
  反例 `M = (0,0)(4,2)(2,6)(4,2)(8,4)(6,4)`、`j₀=3`。**共通の `(s₀,b₀)` が存在しない**）
- `has_gz ⟹ D` / GTWF による §6.7 の証明（`ST_PS` で偽。`pss-67-hasgz-refuted`）
- Red² の許容性経由の §7.4（`y3z_C4_false`）
- §8.5 の spinelaw-universal / leaf-fold / entry1 / d_M=1 など 13 ルート
  （`isabelle/memo.md` の §8.5 節に列挙。**着手前に読め**）

---

## 4.4 カバレッジ点検（2026-07-17 実施）

`8.4-fseq-basic` の穴（§8.4 の記事命題 9 本中 1 本がツリーに無かった）を受けて全点検した。

- **§8: 33 p 文すべてにツリー項目が対応**（穴は `8.4-fseq-basic` の 1 件のみで、解消済）。
  ツリーの §8 項目は 38 で p 文より 5 多いが、これは **pss_paper が text のみ・DEFERRED
  とした記事命題**（`8.4-rightmost-replace-Trans`/`8.4-oper-basic`/`8.4-scb-decompositions`/
  `8.5-scb-decompositions`/`8.5-fseq-scb-decomposition`）に対応＝正しい。
- **§5–§7: p 文ベースでは穴の証拠なし**。p 文 95 件（§5=13/§6=55/§7=27）に対し Lean
  ファイルは 6/65/34 本。§5 は 1 file が複数 p 文を束ねる（`5.1-parent-exists` ⊃
  p_5_1_parent_exists_1..4）。
- 🚨**「lean/ から p 文名を grep」は無効な点検**（45/95 が未参照だが全部偽陽性。
  Lean のヘッダは p 文名ではなく原文位置＋m_ 名を引用する規約のため）。
- 🚨🚨**この点検自体が不十分だった（同日、2 件目の穴を別経路で発見）**:
  §7.4 の命題「Mark が順序関係を保つこと」（content.md 2466、訂正 A19）は
  **pss_paper.thy に転記が無い**ため p 文ベースの点検では**原理的に見えない**。
  Isabelle は `m_7_4_Mark_order`（layerB:9707）で証明済み＝**転記だけが欠落**していた。
  **正しい点検 = 原文（tmp/content.md）の「命題（…）」「補題（…）」見出しを全数抽出し、
  各々にツリー項目があるか照合すること**。corrections.md の A 番号は原文見出しを
  引用しているので、**A 番号の対象命題がツリーに無ければ穴**という交差検査も有効
  （実際 A19 からこの穴を発見した）。次にやるなら見出し抽出スクリプトを書く。
- **A 番号 × ツリー全数照合の結果（同日実施、live 30 件）**: task.md/memo.md に
  未言及の A 番号は 9 件（A5/A6/A10/A11/A12/A13/A15/A17/A40）だが、**すべて対応
  Lean ファイルが存在**（A5→6.6-reduced-slice、A6→6.7-standard-P-components、
  A11→7.2-scb-compose、A12→7.2-scb-replaceable、A13→7.2-add-scb、
  A15→7.3-Trans-welldefined、A17→7.3-Mark-rightmost1、A40→5.3-pred-is-oper1。
  A10 は脚注[19] の循環指摘で命題ではない）＝**畳み込み時に A 番号注記が落ちただけで
  穴ではない**。穴だったのは A19 の 1 件のみで、解消済み。

## 4.5 キャンペーン作戦図: 6.8 d1pos leg — ✅ 完了（2026-07-17。以下は史料）

**目標**: `RankSuccD1posLeg`（`lean/6/6.8-standard-slice-Br-descending.lean` ~4211 の
名前付き仮定）を定理化 → `6.8` ✅ ＋ `8.2-standard-slice-Red-strongmono` ✅（ブリッジ配線済）
の 2 項目が同時に落ちる。

**Isabelle 側の最終構造**（`m_6_8_slice_Br_descending_monoT` の d1pos 枝、
pss_mechanized ~21500–21951）:
1. brle（切片が末尾ブロックに収まる系）は既存機構で処理済（Lean の d0zero 側と対応）。
2. ¬brle（跨りスライス）が本体。dispatch は 3 regime:
   - `oper_d1pos_notbrle_Br_align_regA`（Br の整列と非空性、~14886）
   - `oper_d1pos_low_anchor_shamt0`（shamt=0 アンカー: seg M と seg N の
     IncrFirst^0 一致・境界 entry 等式・P 長一致、~14536 の ANCHOR brick 系）
   - `oper_d1pos_notbrle_LOW_take_eq_{regA,regB,boundary}`（regime 別の
     take-eq 主 brick、~13557–14700）
3. 支える brick 群: H1 brick（10587、`python/d1pos_fold_shape.py` 550/0）、
   within-block le0（12593 RESIDUAL 注記）、GENERAL brick（14331）、
   ACROSS-BLOCK P-COLLAPSE（14480、「core missing brick」だった）、
   ANCHOR（14536）、stop-from-tnc（17266）、regime-B mLmin（17553）。
   `oper_d1pos*` 全体で 694 箇所 ≈ 8–12k 行。

**Lean 移植の指針**:
- wave 分解はこの brick 境界で切る（1 agent = 1 brick 族、green-modulo で
  上位を先に配線してから下位を埋める、Isabelle と同順）。
- **今日の教訓を適用せよ**: le0 の持ち上げ/転送は `ancestor_basic_1`＋entry 一致＋
  `parent_exists_3` の値特徴付けで書けることが多い（8.3-base-basepoint で
  rtrancl 機構を全廃できた）。P の take 対応は `8.2-strongmono-slice` の
  `P_take_at_boundary_sms`/`P_take_prefix_eq_sms` が流用可能（左最小値は
  行 0 の値だけで決まる—d1pos の δ シフトは**ブロック内の行 0 の順序を保つ**ので、
  ブロック内左最小値判定はシフト不変。跨り比較だけが brick の本体）。
- d0zero 側の Lean 資産（6.8 ファイルの `*_68` private 群、6.6-reduced-fseq の
  tiling 読み出し）に d1pos 版（`entry_oper_tiling_block_zero` の
  `+ q*δ` シフト付き読み出し）を足すところから始める。

## 4.6 実行待ちプラン: 8.1 part (3-1) = Mark gap-peel エンジン（2026-07-16 調査済）

**目標**: `lean/8/8.1-condI-III-c1-around.lean` の sorry (3-1)（`c1_around_3` 内）を閉じる。
Isabelle 連鎖 = 4 部品（layerB/pss_wip.thy）:
1. **`Trans_gap_2tower`** (19569–19788, ~220 行): 簡約 mono `N`・両端 Marked・内部全非許容
   → `Trans N = D_{N₁,₀}(D_{N₁,last} 0)`。Lng 帰納。base = `two_column_Trans`
   （**Lean 済**, 7.3-two-column:482）。step = Pred 剥がし:
   `transJm1 N = 0`（非許容伝播 `Adm_eq_0_of_nadm_below` — 要移植、小）、
   `Trans N = transC2 N`（Adm0 での Trans 展開 `Trans_eq_transC2_Adm0` — 要移植。
   Lean の Trans 展開補題は 7.3-Trans-welldefined の TransAux 機構から作る）、
   `transC1 N = Trans (Pred N)`（`ra_Mark0_eq_Trans`: `Mark Q 0 = Trans Q` for
   `(Q,0)∈Marked` — 要確認/移植）、IH、最後に condVI 判定と transC2 の形の計算。
2. **`Mark_gap_rightmost_peel`** (19789–19910, ~120 行): `b = 右端` の場合。
   `Mark_rightmost1_forward`（**Lean 済** 7.3:522）＋`Mark_Trans_repr`（**Lean 済**
   7.4:984）＋`Trans_slice_eq_Red`（要移植; Lean は `Trans_Red` 7.3-Trans-IncrFirst-Red:113
   ＋ `ancestor_slice_Red_IncrFirst` で組める）＋IncrFirst 不変量
   （`entry_funpow_IncrFirst1`/`adm_funpow_IncrFirst_eq` — 要移植、小。IncrFirstN は
   行 0 のみ変えるので行 1 entry と adm は不変）＋2tower。
3. **`Mark_gap_peel`** (19922–20055, ~130 行): 一般 `b`。Lng 強帰納で Pred に転送:
   `Marked_Pred`（**Lean 済** 7.3:833）、`nextR1_pred_agree`（要移植、小: butlast は
   内部 nextR1 を保つ）、共通 scb 位置転送 `Mark_nest_common_marked`（**Lean 済**
   7.4-Mark-nextAdm:40）＋`Mark_marked_isPTB`（要確認）＋`scb_decomp_self`
   （private 複製 7.4-Trans-Mark-Pred:14）。
4. **`m_8_1_c1_around_part3_1`** (20058–20155, ~100 行): 組み立て。

**規模感**: Lean ~700 行・新規小補題 ~6 本。Trans 展開の罠は 7.3 系ファイルの
`TransAux_MarkAux_fuel_irrel_RTPS` と `transC2Core_properties` を先に読むこと。

**進捗 (2026-07-16)**: 部品 1（`Trans_gap_2tower_gp`）**完了** — 8.1 ファイルに
private 実装済（エラー 0、既存 sorry 3 は不変）。**Lean 版は Isabelle より大幅短縮**:
`Trans N = Mark N 0 = Mark N (transJm1 N) = transC2 N` が既存の
`Mark_zero_eq_Trans`＋`Mark_transJm1_eq_transC2`（7.4-Mark-Trans-repr 公開済）で
出るため、TransAux の手展開が不要。新設 private: `adm_zero_gp`/`adm_last_gp`/
`find_adm_zero_gp`/`Adm_eq_zero_of_nadm_below_gp`（許容化ゼロ落ち）。
条件 (VI) の確立は nadm→行1辺→`le0_adjacent`→行0隣接→両行 parent=j₁-1→`RedCondA_apply`。
**部品 2（`Mark_gap_rightmost_peel_gp`）も完了**（577f577、エラー 0・sorry 不変）:
`Mark_Trans_repr`＋`Trans_Red` で値化 → `ancestor_slice_Red_IncrFirst` の Red 切片 N に
2 塔適用。adm/行1-entry の IncrFirstN 不変量は private `adm_IncrFirstN_gp`/
`entry_IncrFirstN_one_gp`（`nextR_IncrFirstN_ri`＝6.5-Red-IncrFirst-invariance:861 公開）。
**罠: `rw [hIF]` は RHS の `Red (seg …)` 内の seg まで書き換える** → `conv_lhs` か
添字一般化（∀ j 形）で回避。
**全 4 部品完了・part (3-1) クローズ**（7de0170、8.1 の sorry 3→2）:
部品 3（`Mark_gap_peel_gp`）= Lng 強帰納＋`Mark_nest_common_marked` の共通 scb 位置
転送＋`scb_unique_decomp_unconditional`＋`scb_compose_dprin`＋`flatBT_injective`。
principal 性は `marked_component_principal`+`Trans_Mark_mem_MarkedB`+`Mark_mem_T_B`
（`Mark_marked_isPTB` 複製不要）。部品 4（組み立て）= 間隙非許容は `Adm_max`、
Marked 事実は `c1_around_2` を再利用、`adm M j₀` で許容化恒等（`simp [transJm1, Adm, hadm]`）。
**注意: f3b9906 のコミットメッセージは stale ファイル事故で「engine 2/3」だが中身は
engine 3/3**（7de0170 のメッセージに訂正注記済）。cwd ずれ（lake build 後の
`cd lean` 残留）で commit-msg を 2 回誤用— **lake build と git は同一コマンドで
連結しない**こと。
**part (5) もクローズ**（1f62b92、sorry 2→1）: conj(1)=`kind0_base_basepoint`
（8.3 ファイルを import）、conj(2)=`oper_prefix_to_lastblock_p5`、conj(4)=
一般行 0 親一意性 `row0_parent_unique`＋`nextR_seg_adm` 転送、conj(5)=
`admof_slice`＋接頭辞 adm/Adm 一致（`nextrel1_prefix_imp_p5` 両方向＋
`find_adm_congr_p5`）、conj(6)=`Lng (Pred N) = idx > 1` だけで
`Trans_preserves_zeroT`（TPS 版なので M[n-1] 同定不要）、conj(7)=間隔 ≥ 2。
**罠: `Lng` は abbrev だが omega/rw はシンタクティック** — `Lng X` と `X.length` は
別アトム。defeq-cast（`have h : X.length = _ := hLng形`）で橋渡しする。
goal の transJ0/transJ1 形は冒頭で `simp only [htJ0, htJ1]`（rfl 証明の書換）で
parent/Lng 形に落としてから作業する。
**8.1 の残 sorry = part (4) のみ**（前剥がし ~3000 行基盤、キャンペーン級）。

---

## 5. ツリー（task.md と同構造 ＋ 注釈）

凡例: 訂正 = `corrections.md` の A 番号。Isa = `isabelle/` 側の対応補題（証明の設計図）。

- ✅ **定義層 `PSS/`** — 移植元は `isabelle/pss_defs.thy` 一本。ここは「証明」ではなく「転記」。[r9]

- ✅ **§5 定式化** — 全 6 項目を証明済み。[r6]

- 🚨 **§6 ペア数列の基本性質** — Isa: `m_6_*`（`pss_mechanized.thy`）。
  - ✅ `6.1-le-IncrFirst-invariance` — 行 0/1 の辺と燃料付き推移閉包が上段一様 +1 で
    不変なことを順に示した。Isa: `m_6_1_le_IncrFirst_inv`。[r1]
  - ✅ §6.2 単項性 — 判定条件、切片遺伝、`IncrFirst` 同変性、`P` 成分・加法性・基本列関係、
    非複項基本列の二分岐まで移植。`oper` の親位置を切片へ移す補題群と、展開後の上段係数の
    狭義最小性を機械化。Isa: `m_6_2_*`。[r8]
  - ✅ §6.3 許容性 — `take`/`drop` に対する燃料付き行 0 閉包と行 1 親子関係の不変性を示し、
    `adm`・`Adm`・`Marked` の切片遺伝を証明。`Adm` の最大性は `reverse.find?` の先頭性から
    直接導出。Isa: `m_6_3_*`。[r3]
  - ✅ §6.4 幹と枝 — `P` と累積長 `IdxSum` の切片表示・左端最小性を長さ強帰納法で示し、
    幹を `TrMax` の最初の不成立点として解析した。枝成分内の行 0 祖先関係を元の列へ移送し、
    `FirstNodes` 増加・`Joints` 非増加・係数非増加、および単項性の切片遺伝を証明。
    訂正 **A3** に従い、偽である `Joints` の狭義減少は主張しない。Isa: `m_6_4_*`。[r7]
  - ✅ §6.5 簡約化 — `Red` の停止性・閉形式・長さ/零項/単項性・`P`・冪等性・`Pred`・基本列を
    形式化。偽である原文の大域形は訂正 A4 に従い `anchoredSlice` へ制限し、標準形の簡約性から
    条件(A)を供給して `leR` と `nextR` の不変性を証明した。そこから `AdmSet`・`Adm`・`Marked`
    の保存も導出。全公開定理は `check_lean.py` rc=0、sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `m_6_5_*_final`。[r16]
  - ✅ §6.6 簡約性 — `RTPS ↔ RedCondA ∧ RedCondB`、切片・`P`・係数・左端・`Red²` の
    全補題に加え、基本列保存 `RTPS_oper` を完成。真正タイルの条件(A)は row 0 と row 1 を分離し、
    row 1 の正シフトを prefix、ブロック先頭、ブロック内親、prefix 逃避親に分類して親を読み戻した。
    非タイル分岐と既存の条件(B)保存を合わせて Isabelle `m_6_6_reduced_oper` と同じ主張を得た。
    `check_lean.py` rc=0、sorry 0、公開定理の axioms は
    `[propext, Classical.choice, Quot.sound]`。[r17]
  - ✅ §6.7 標準形 — `STPS ⊆ TPS` の始切片遺伝、rank 階層の単調性による単項成分保存、
    および `STPS` の生成帰納法と `RTPS_oper` による簡約性 `STPS_RTPS` を完成。
    対角列の簡約性は零列を分離し、正の末尾から `RTPS_diag_prefix` で復元した。
    `check_lean.py` rc=0、sorry 0、公開定理の axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `m_6_7_*`。[r3]
  - ✅ §6.8 降順性[r6] — `6.8-standard-slice-Br-descending`（訂正 **A7**/**A8**、[r5]）＋
    `6.8-standard-P-descending`（[r1]、`STPS` 生成帰納法・`P_fseq_1/2` 分解）。
    前者は **d1pos campaign（wave A-1〜A-3＋solo 仕上げ、2026-07-17 完了）**:
    兄弟ファイル 13 本（`6.8-d1pos-dispatch/-base/-trmax/-le0/-notbrle/-anchor-regA/
    -anchor-regB/-period/-cell-regA/-cell-regB/-cell-boundary/-cell-periodic/-final`）に
    分割移植し、dispatch の 22 named Props（`D1pos_*`、Isa `oper_d1pos_*` 89 本
    ≈8–12k 行に対応）を全数 `_holds` 定理で討伐 → `6.8-d1pos-final.lean` の
    `rankSuccD1posLeg_proved` で仮定を実体化し**無条件版
    `standard_slice_Br_descending`** を得た（rc=0・sorry 0・axioms
    `[propext, Classical.choice, Quot.sound]`、lake 3076 jobs）。
    Isa: `m_6_8_standard_slice_Br_descending`（pss_mechanized 24002）。
    勝ち筋: green-modulo top-down 配線／le0 の値特徴付け（rtrancl・燃料帰納 全廃）／
    既存 `_68` 資産の public 昇格。周辺知見: regB セルの `clt_regB` 呼びは cleMB
    仮定で冗長（statement 不変）。dedup 候補（私的重複）: anchor_lt_of_uniform_witness
    （_ra/_rb）、d1pos_agree（_dt/_pd）、TPS_of_P_multi（5 重）、trunk_le1_pd
    （公開価値あり）、TrMax_seg_oper_d1pos_eq_regA（_nb/_ca、Isa 15218）。
    昇格候補: `STPS_exists_rank_68`/`take_pred_eq_dropLast_68`/`P_last_anchor` API。

- 🚨 **§7 Buchholz の表記系への翻訳** — Isa: `m_7_*`。
  - ✅ `7.1-lessBT-linear-order` — `BT`・`BP`・`List BP` の三者に対する相互再帰補題として、
    `lessBT`/`lessBP`/`lessBPList` の反射律否定、推移律、三分律を直接証明した。
    定義層の mutual inductive 自動 `BEq` は opaque で `LawfulBEq` を導出できなかったため、
    同値な透明相互再帰比較器と等値反映則を `PSS/Buchholz.lean` に明示した。
    Isa: `m_7_1_lessBT_linord`。[r1]
  - ✅ `7.1-term-components` — `BT.trm ps` に場合分けし、`PB` の空性が `ps=[]` と同値であることと、
    各 principal を singleton 項へ写してから `flatMap untrm` すると元の `ps` に戻ることをリスト帰納で証明。
    `T_B` 前提に依存しない定義上の恒等式として原文の (1)(2) を同時に得た。Isa: `m_7_1_term_components`。[r1]
  - ✅ `7.1-paren-balance` — `BT.rec` の三 motive を `flatBT`・`flatBP`・`flatBPTail` の
    左右括弧数一致に設定し、項・principal・principal リストを同時に構造帰納した。
    multi 項では外側の `.lp` と `.rp` が一つずつ増え、内部の一致を保存する。
    Isa: `m_7_1_paren_balance`。[r1]
  - ✅ `7.1-buchholz-wf` — **完了（2026-07-17、仮定ゼロ・236 行）**。
    `buchholz_wf : WellFounded (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true)`。
    🚨🚨**言葉遣いの厳守（2026-07-17 ユーザー指摘、私が実際に誤記した）**:
    証明したのは **`(OT_B, <_B)` の整礎性**であって、**[Buc1] Lemma 2.2 ではない**。
    2.2 の本体は評価写像 `o` についての (a) `o(a) ∈ C₀(ε_{Ω_ω+1})` / (b)
    `G_u o(a) = {o(x) | x ∈ G_u a}` / (c) `a < c ⟹ o(a) < o(c)` ＝**意味論の命題**で、
    `o`・ψ_v・Ω_u（正則基数の可算列）を要するため **definitional HOL でも Lean でも
    陳述すら不可能**（ℵ_ω サイズの器が作れない＝独立。[[buc1-2-2-is-not-what-we-proved]]）。
    整礎性は 2.2(c) の**系**（狭義単調埋め込み ⟹ 無限降下列なし）だが逆は成り立たず
    （wf から `o` は復元できない）、原文が 2.2 から使うのは整礎性だけ（content.md
    5978/6331「[Buc1] Lemma 2.2より (OT_B,<) は整礎である」）なので、**使用に対して
    過不足のない唯一の転記形**がこれ。Isabelle の `buc1_2_2_OT_B_wf` /
    `y4_buc1_2_2_OT_B_wf` も同じ理由で wf 文（名前の「2.2」は出典表示）。
    ⚠️報告・コミットメッセージで「Lemma 2.2 を証明した」と書くな（今日書いてしまった）。
    親が独立検証: `example : OT_B_wf := buchholz_wf` が緑＝8.7-OT-tail の残差も同時に消滅。
    🎉🎉**勝ち筋（数千行を回避）**: Isabelle の
    `bwl_cof → bwl_Wstar_total_of_cof(9927) → bwo_2_2_wf(7834) → y4_wf_RPrel(13689)
    → wfox_tuple_lift → y4_buc1_2_2_OT_B_wf` という **RPrel 経由の迂回は歴史的な
    dead code**（r66 が `bwo_Wstar_total` を残差に切り出した後、r68 が `bwl_acc_of_W`
    (9808) を証明した時点で不要になっていた）。**`y3_dfree_W_ex`(11382、Lean 移植済)
    ＋`bwl_acc_of_W`＋「OT_B 外の項は RTrel-前者を持たないので自明に acc」**で
    全 BT の Acc が直接出る＝RPrel/bwo_Wstar/wfj_tuple_acc/wfox_tuple_lift すべて不要。
    弱化ではない（`bwo_2_2_wf_iff`(7871) が `bwo_Wstar_total ⟺ wf RPrel` を示しており
    残差に overshoot が無かった）。~180 行・初回 checker で緑。
    構成: §0 RTrelW（`wfox_goal_eq_RTrel` は `OT_B = OT ∩ T_B` から Iff.rfl に潰れる）
    ／§1 dom 非退化／§2 `bwl_cof_wfe`＝y3_cof0＋y3_cof0_imp_bwl_cof 融合
    （`y4_bachmann_domB` が y3_cof0 を literal に供給、`y3_TBv_dfree_W` が
    `z ∈ W_m` 節を無料で復元）／§3 `acc_of_W_wfe`＝`bwl_acc_of_W`(9808) が本体
    （A2-最小性＋zero/num/tu 場合分け、閉性は `buchholz_fseq_closed(_general)`）
    ／§4 短絡／§5 目標。**反空虚性も確認**（BZero/D_0 0/D_1 0 ∈ OT_B、0 < D_0 0 < D_1 0）。
    ⚠️7.1→8.7 の向きで import せよ（8.7 から 7.1 は循環）。
  - （史料）当初の方針メモ: 原文は引用のみだが **Lean でも自前証明すると
    決定（2026-07-16 ユーザー）**。Wave E で基盤 2 file（W 階層／y4 bachmann 群）に着手。
    ⚠️**転記の要点**: Isabelle が証明したのは意味論版 2.2(a)(b)(c)（`o`/ψ/基数が要る＝
    definitional HOL では**陳述不能**）ではなく、原文が実際に使う帰結
    **`wf {(a,b). a∈OT_B ∧ b∈OT_B ∧ lessBT a b}`**（純構文的）。Lean も同形で移植する。
    **Wave E で基盤 2 file 完成（両方緑）**: `7.1-buchholz-wf-W`（W 階層の定義層
    `bwl_Aop`/`bwl_Aset`/`bwl_Wf`/`bwl_W`＋(A1)(A2) 機構＋y3_ 系 13 本。
    Isabelle の `primrec bwl_Wf` は Lean の構造帰納＋自前 lfp（`⋂₀{Y | f Y ⊆ Y}`
    ＋Knaster–Tarski 2 面、~15 行）で素直に載った。非空性 `bwl_W_zero` で
    vacuous でないことも確認）／`7.1-buchholz-wf-bachmann`（**y4 block 全 23 補題を
    green-modulo 無しで完成**、`y4_bachmann` 込み）。
    **bachmann 側の 2 つの判断**（統合時に効く）: ①Isabelle の operB multi は
    **末尾 principal 還元**だが Lean の `bOperCore` は**頭剥がし**なので
    `y4_inner`/`y4_bachmann` は末尾再帰＝`y4_prefix_split` は忠実移植したが
    engine では未使用 ②domain は `domTag c = .below u` 形で記述し、Isabelle 逐語の
    集合形は `y4_bachmann_domB` で別途供給（bridge `domB_below_iff_b4` 経由）。
    **残 = [Buc1] §2 本体**（`bwl_2_1`〜`bwl_2_8`、pss_scratch ~8695–9733）:
    W 側が Prop 化した `Bwl28Principal`（bwl_2_8_principal 9733）と
    `Bwl24bAdd`（bwl_2_4b_add 8965）を定理化し、その上で `y4_buc1_2_2_OT_B_wf`
    （13700）＋distinguished sets（`wds_`/`wcl_`/`wfj_` 群、r63 ブロック）を移植。Isa: `y4_buc1_2_2_OT_B_wf`（layerC:13700、sorry 0・仮定 0。
    `y4_bachmann` 核の W-階層帰納。y4 block ≈ layerC 12493–13700 ＋ y3 W-機構 11247–11777、
    合わせて ~2k 行のキャンペーン級）。§8.7 の `8.7-OT-tail-annihilable`（layerC:19363 が
    `wf_induct_rule[OF y4_buc1_2_2_OT_B_wf]`）と `8.7-termination` が依存するので、
    Wave D 後半までに専用 wave を充てる。
  - ✅ `7.1-buchholz-fseq-lt` — `btWeight` 強帰納で `operB` の全分岐を直接解析し、
    [Buc1] Lemma 3.2(a) を証明。帰納命題は `z ∈ domB a ∨ z ∈ NatSet` へ強化し、
    `{0}`・`T_u` domain に対する実行可能定義の自然数拡張も含めた。kind-1 は
    `xseq b u i = D_u(…) ∈ T_u`、multi 項は末尾 principal の `domTag` と `OT` を輸送して閉じる。
    公開定理 `buchholz_fseq_descent` / `buchholz_fseq_lt` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは深さ 2 の 1,561 項
    （`OT` 496 項）で domain 降下・各項 4 自然数の拡張とも反例 0。
    Isa: `b1x_descent`, `m_buc1_3_2a_fseq_lt`。[r1]
  - ✅ `7.1-buchholz-fseq-closed` — [Buc1] Lemma 3.3 の閉性を、Isabelle の
    `b1x_master` と同じ「閉性＋Lemma 3.6 の `G` 制御」の同時 `btWeight` 強帰納で証明した。
    `G_u` 要素の真部分項性・推移性・添字反単調性、sandwich 分解、`G` 制御の最小反例法を
    Lean の有限 `gatherBT` 上で機械化。訂正 A23 の kind-1 分岐は、`x_i` の狭義増加、
    `b[x_i]` の tower `G` 制御、`x_i ∈ OT_B` の3帰納不変条件で閉じた。
    公開定理 `buchholz_fseq_closed_general` / `buchholz_fseq_closed` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは深さ2の1,561項
    （`OT` 496項）で domain 閉性および各項4自然数の拡張とも反例0、全 `lake build` は
    3,016 jobs 成功。
    Isa: `b1x_master`, `m_buc1_3_2_OT_B_closed`。[r1]
  - ✅ §7.2 scb 分解 — 全7項目を証明済み。[r9]
  - ✅ §7.3 翻訳写像 — 全9項目を証明済み。[r12]
  - ✅ §7.4 許容的親子関係[r10] — **2026-07-17 に 10 件目 `7.4-Mark-order` を追加**
    （命題「`Mark` が順序関係を保つこと」、原文 content.md 2466、**訂正 A19**）。
    🚨**カバレッジ穴だった**: この命題は **pss_paper.thy に転記が無く**（p_7_4_* は 9 本のみ、
    text 注記も無い）、Lean ツリーにも項目が無かった。Isabelle は `m_7_4_Mark_order`
    （layerB:9707）で**証明済みなのに逐語転記だけ欠落**していた＝「p 文の有無」で
    カバレッジを測ると見落とす種類の穴（[[green-build-blind-spots]]）。
    Lean は A19 訂正案と逐語一致で証明:
    `m0 < m1 ↔ Mark M m1 ≠ Mark M m0 ∧ (Mark M m0, Mark M m1) ∈ MarkedB`
    （原文 (2) は whole/block が逆で偽、経験的に 0/249）。ファイル
    `7.4-Mark-order.lean` には昇格した `Trans_mono_RN_ge2`（Isa 9011）と
    `Mark0_ne_Mark`（Isa 9636）も同梱（8.2 engine の私的 `_ape` 複製の昇格元。
    親は engine 側の複製を削除して import に差し替えてよい）。
    `Mark0_ne_Mark` が Mark_order の `m₀ = 0` 枝そのもので、これが最後のピースだった。
  - ✅ §7.4（既存 9 件）— 訂正 A18・A45・A46・A47 に従い、必要な命題を `RTPS` と
    `Marked` の正しい定義域で全9件形式化した。`Adm`／`Trans`／`Mark` の次許容祖先関係から、
    `Mark` の終切片 `Trans` 表示、`Trans` の切片分解、`RightNodes` 分解までを scb 文脈の
    合成・無条件一意性と `Lng` 強帰納で証明した。最後に原文の再帰を忠実に表す燃料付き
    `RightAncesAux` を定義し、単項枝は終端初期切片と `RightNodes_Mark`、複項枝は最終 `P`
    成分への帰着により `RightAnces M = RightNodes (Trans M)` を示し、
    `RightAnces M = [] ↔ zeroT M` を導いた。全公開最終定理は専用 Kimina 監査で
    no errors/no sorry、axioms は通常の `[propext, Classical.choice, Quot.sound]` 以下。
    全 `lake build` は3,052 jobs成功（2.44秒）。Isa: `m_7_4_*`。[r9]

- **§8 停止性** — Isa: `m_8_*` ＋ `layerC`。**停止性 = 「基本列の降下性」＋「`OT` 所属」の 2 本柱**。
  - ✅ `8.1-diagSeq-Trans` — `u<v` の対角列について、十分な任意燃料で
    `TransAux` と `MarkAux · 0` がともに `D_u(D_v 0)` となる同時帰納不変条件を証明した。
    2列基底は一列計算を直接展開し、帰納段階は末尾上段親が直前列、かつその `Adm` が 0
    であることを `range.reverse.find?` まで計算して条件(VI)に還元した。自明な自己 scb 文脈で
    `D_u(D_v 0)` を `D_u(D_{v+1}0)` に置換し、燃料下界を `transFuel` から閉じた。
    公開定理 `diagSeq_Trans` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは `0≤u<v≤8` の36例で
    `Trans`・`Mark 0`・条件(VI)とも反例0、既存の全819列チェックサムも
    `531635224` のまま一致。全 `lake build` は 3,018 jobs 成功。
    Isa: `m_8_1_diagSeq_Trans`, `p_8_1_diagSeq_Trans`。[r1]
  - ✅ `8.1-Pred-diagSeq-Trans` — 対角列 `diagSeq u v` に 1 列 `(wp,w)` を
    追加した翻訳を、`wp=v+1`、`u<wp≤v ∧ w=wp`、`u+1<wp≤v ∧ w<wp`、
    `wp=u+1 ∧ w<wp` の 4 ケースに分けて原文どおり計算した。追加列の `RTPS`、
    第 0 行の親、内部 `Adm=0`、右端直前基点の許容性を直接証明し、十分な任意燃料の
    `diagSeq` 翻訳・左右の `MarkAux` を `transC2Core` の各分岐と scb 置換へ接続した。
    公開定理 `Pred_diagSeq_Trans` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは `0≤u<v≤8` の
    全 4 ケース 780 例（120/120/420/120）で反例 0、既存の全 819 列チェックサムも
    `531635224` のまま一致。全 `lake build` は 3,019 jobs 成功。
    Isa: `m_8_1_Pred_diagSeq_Trans`, `p_8_1_Pred_diagSeq_Trans`。[r1]
  - ✅ `8.6-const2nd-Trans` — 公差 `(1,0)` の一般列
    `((m+j,u))_{j=0}^{j₁}` の `Red` が正規列 `((u+j,u))_{j=0}^{j₁}` になることを、
    `RedCondA`・非複項性と `Red_rebase_nonmulti` から直接証明した。正規列については
    一定な第 1 行から全添字の許容性を、第 0 行の連続辺から直前列が親であることを示し、
    十分な任意燃料の `TransAux` を `j₁` で帰納した。非零段階の `c₁=D_u0`、
    条件(I)/(III)による `c₂=D_u(D_u0)`、塔の最内側 scb 文脈を実行探索器に対して一般の
    高さで固定し、parser の完全性から置換後が一段高い塔になることまで閉じた。
    公開定理 `const2nd_Trans` は原文どおり `M` の明示定義と `TPS M` を受け、右辺を
    関数反復 `(D_u)^[j₁+1] 0` で述べる。sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは
    `0≤m,u,j₁≤4` の全 125 例（零 5、塔 120）で `Red`・`Trans` とも反例 0、既存の
    全 819 列チェックサムも Lean/Python とも `531635224` のまま一致。全 `lake build` は
    3,020 jobs 成功。Isa: `m_8_6_const2nd_Trans`, `p_8_6_const2nd_Trans`。[r1]
  - ✅ `8.6-diagSeq-Trans-fseq` — 対角列 `diagSeq u (u+j₁)`（`1<j₁`）の基本列を、
    第0行 `u+j`・第1行 `min (u+j) (u+j₁-1)` で表す正規展開列 `runSeq` として定義し、
    `oper` の逐語定義から両者の一致を証明した。展開列では第0行の親が常に直前列、
    第1行の親が対角部では直前列・定数部では対角部右端となることを示し、条件(A)(B)から
    簡約性を直接導いた。十分な任意燃料の `TransAux` を定数部の長さで帰納し、右端基点
    `c₁=D_p0`（`p=u+j₁-1`）、条件(III)による `c₂=D_p(D_p0)`、最内側 scb の実行探索と
    parser 完全性を接続して `Trans(runSeq u p n)=D_u(D_p^n0)` を得た。公開定理
    `diagSeq_Trans_fseq` は記事どおり `M` の明示定義・`TPS M`・`0<n`・`1<j₁` を受ける。
    sorry 0、axioms は `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは
    `0≤u≤4, 2≤j₁≤6, 1≤n≤4` の全100例で `oper/runSeq`・`Red`・`Trans` とも反例0。
    既存の全819列チェックサムも `531635224` のまま一致し、全 `lake build` は3,021 jobs成功。
    Isa: `m_8_6_diagSeq_Trans_oper`, `p_8_6_diagSeq_Trans_oper`。[r1]
  - ✅ `8.6-trailing-principal-annihilable` — 訂正 A23 後の正しい Buchholz 基本列に対し、
    原文どおり任意の scb/right-spine 文脈中の `D_u(t'+D_v0)` が `1≤k≤v+1` 回の `[0]` で
    `D_ut'` へ置換されることを証明した。旧 A25 は A23 の旧誤読から生じたため撤回済み。
    一歩の核心を「即時削除または `D_v0→D_{v-1}0`」の二分岐として機械化し、外側が
    `T_{v-1}` のままなら plain descent、途中で自然数域へ移るなら最初の kind-1 host が
    正確に `D_{v-1}0` を渡すことを、`RightNodes` suffix と `rnDom` で示した。その後 `v` の
    強帰納法で上界を閉じた。公開定理 `trailing_principal_annihilable` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Lean 内にも旧反例候補の正しい 2 手軌道を
    `#guard` で固定。独立 Python モデルは `t'` 6種、`0≤u,v≤4`、深さ2までの一般右端文脈
    21,900例で一歩分岐・有界零化とも反例0。既存の全819列チェックサムは Lean/Python とも
    `531635224` のまま一致し、全 `lake build` は3,022 jobs成功。[r1]
  - ✅ `8.1-condI-III-c1-around` — 訂正 **A20**（補題(1) は非簡約 1 列切片で偽）
    ＋ **A21**（補題(5) の条件(III)で `j₀ᴺ = j′₀` が偽）。5 部構成。[r2]
    **(1)(2)(3-1)(3-2)(5) 緑**（(1) は A20 訂正の完全形。反例定理
    `c1_around_1_original_false`/`c1_around_5_original_false` も機械証明済み。
    (3-1)(5) は 2026-07-16 solo でクローズ — §4.6 参照）。
    **sorry 残 1**: (4-1)(4-2)=Isabelle part4 の front-peel 基盤 ~3000 行
    （キャンペーン級）。目標形は訂正後で確定済み＝後続 wave は in-place で
    sorry を潰すだけ。
    **Wave B-1 完了（r3, 全4 agent 緑、lake 3080 jobs）**: 兄弟ファイル 4 本新設。
    `8.1-part4-peel`＝両エンジン（`Trans_front_peel`/`Mark_rightmost_adjacent_peel`、
    2 塔機構は `two_column_Trans` で代替、`Marked Q (k+1)` 仮定は Lean では不要だが
    忠実性のため保持）／`8.1-part4-setup`＝setup＋head（Isa 570 行の head は
    `Mark_leftend_form_proper` 公開済みで崩壊）／`8.1-part4-mid`＝Nred/Adm0/
    cond42/cond41／`8.1-part4-trans`＝TransN_41＋segpos（private engine
    `part4_TransN_engine_pt` が Adm0/cond41 の役割を吸収、python audit 1856 例
    0 反例）。
    **Wave B-2 完了（r4, 2 agent 緑）→ 全クローズ（2026-07-17）**:
    `8.1-part4-one`＝part4_1（Isa 32085–32277。part1/part2 引用は
    Mark_Trans_repr＋seg_Pred_eq＋Mark_leftend_form_proper で私的再導出、
    python audit 288 例 0 反例）／`8.1-part4-two`＝TransN_42＋part4_2
    （4-1 engine の (V)-guard 版で cond42 吸収、`ex1_Dpt_addBT_two` 移植）。
    親が in-place で c1_around_4 の sorry を両 leg 適用で差し替え → **ファイル全体
    rc=0・sorry 0・全 8 公開定理 axioms 正常（lake 3082 jobs）**。
    昇格候補: adm_row1_ancestry（3 重）/row1_implies_row0（3 重）/
    entry_IncrFirstN_one（3 重）/IncrFirstN 不変量 pack（_pt 私的）/
    addBT_principal_split（_p1/_p2 と 7.2-add-scb 私的）。
    ⚠️重複警告: `adm_row1_ancestry`/`row1_implies_row0`/`Trans_singleton` が複数ファイルで
    private 重複 → PSS/Adm・PSS/Defs・PSS/Trans へ昇格すべき。
  - ✅ `8.2-standard-slice-Red-strongmono` — **完了（2026-07-17、6.8 クローズと同時）**。[r2]
    §8.2 語彙を計算可能に定義済み: `cdomB`/`descendingB`/`strongMono`/`DTPS`(+Decidable)。
    数値検証: 実標準形プール 442 形×先祖切片 13,264 例 0 違反（maxlen 13, 成分≤15,
    `python/strongmono_audit.py`）＋全 69,904 列チェックサム一致＋#guard 9 本。
    仮定明示版 `standard_slice_Red_strongmono_of_Br_descending` と忠実版
    `standard_slice_Red_strongmono` とも sorry 0・axioms 正常。§6.8 依存は
    `6.8-d1pos-final` を import し、無条件版 `standard_slice_Br_descending` を
    `descendingB_iff`＋`cdomB_iff` で `Bool` 版へ橋渡し（予定どおり getD 形一致）。
    後続 §8.2 の 6 項目はこのファイルから `strongMono`/`DTPS` を import する。
    昇格候補: `Br_IncrFirstN`/`descendingB_of_map_IncrFirstN`/`TrMax_IncrFirstN` 等
    （現在 `*_sm` private）。Isa: `m_8_2_standard_slice_Red_strongmono`
    (layerB/pss_wip.thy:15020)。
  - ✅ `8.7-const00-Trans` — `Trans (replicate (j₁+1) (u,u)) = multBT (D_u 0) (if u=0 then j₁
    else j₁+1)`。Isa `p_8_7_const00_Trans` と逐語一致を親が確認。定数列は親子辺ゼロ
    → RedCondA/B → RTPS、`Pcut = j₁`、j₁ 帰納で multi 分岐が 1 列ずつ `D_u 0` を積む
    （Isa: `m_8_7_cnst_Trans`, pss_wip.thy 16005）。rc=0・sorry 0・axioms 正常・
    python audit 81 例 0 反例（`python/const00_trans_audit.py`）。[r1]
  - ✅ `8.2-strongmono-slice` — **親が main loop で直接証明**。mono=`mono_slice`（6.4）、
    reduced=幹対角性（`RTPS_mono_head_eq`+`trunk_entries_offset`→IncrFirst 指数 0、
    `ancestor_slice_Red_IncrFirst`）、降順性=**P-take 境界対応**で `M` から輸送:
    private `P_take_at_boundary_sms`（境界カットで `P (take b M) = take K (P M)`、
    Pcut 再帰）＋`P_take_prefix_eq_sms`（一般カットは左最小値転送＋境界 2 回で
    `J = K'` に pin、Isabelle `P_take_prefix_eq` 同形）＋成分頭読み出しの行一般化
    （private `P_component_leftend_i_sms`）＋private `TrMax_seg_ancestor_sms`
    （`le_TrMax_intro_wd`/`TrMax_stop_uncond`/`nextR1_seg_adm` で挟む）。
    FirstNodes 対応は不要になった（P リストの頭だけで cdomB が閉じる）。
    罠: **`rw` は `Lng` abbrev 越しに `List.length_*` をマッチできない**（simp は可）
    → `show`/defeq-have で `.length` 形に落としてから rw。`List.take_append_of_le_length`
    が正名（`take_append_eq_append_take` は無い）。
    Isa: `m_8_2_strongmono_slice` (layerB:27757)+`_mono_reduced` (27395)。
    昇格候補: `TrMax_seg_ancestor_sms`/`P_take_*_sms`（§8.2 後続と 8.1(3-1) が使う）。
    rc=0・sorry 0・axioms 正常・#guard 5 本・python pool 2692 例 0 反例。[r1]
  - ✅ `8.2-condV-rightmost-parent` — **完了（2026-07-17、Wave C-1）**。[r1]
    p 文 = pss_paper:1588 と 1:1（PT_PS→monoT 規約、descendingB Bool 版）。
    Isa: `m_8_2_condV_rightmost_parent`（layerB:42048）。helper 6 本公開
    （wf21_Br_eq_seg／le0_monoT_seg_into_list／le0_above_parent／joint_row1_eq／
    branch_col0_val／det_imp_joint_lt_TrMax）。Joints_nth 系は既存の
    Joints_getD／Joints_nextR_FirstNodes／mono_hasParent_row0 で代替、
    rtrancl 分解は全て le0 値特徴付けで置換。rc=0・sorry 0・axioms 正常。
  - ✅ `8.2-subexpr-component-Pred` — **完了（2026-07-17、Wave C-1〜C-4＋G の 5 波）**。
    **無条件形 `keystone`＋原文忠実形 `keystone_faithful`**（＝ Isa `m_8_2_keystone`
    32461 と `p_8_2_subexpr_component_Pred` pss_paper:1523）が
    `8.2-subexpr-component-Pred.lean`（旧 -chainOK、1281 行・公開 33 本）に。
    green-modulo は**完全に解消**（SXP_* 5 本すべて討伐）。
    最後の 2 残差の討ち方: baseU←`Br (Pred M) = []` は Pred M が全幹＝対角列
    （`diagSeq_Trans` の 2 段塔）／`Lng M = 3` は `two_column_Trans`。
    cpU←branchPar→descAdm→chainOK→widTrM→cpU の連鎖（branchPar 32434 は無条件）。
    `chainOK` は WF 再帰 def（dite ガードで再帰呼び出しにガードを可視化、
    `termination_by Lng M`＋`length_Pred`）＝Isabelle の function/measure と 1:1。
    **監査（`python/audit_82_chainOK.py`）**: 14,618 形プールで**反例 0**（20 主張）。
    負対照も健全: (N1)「Admpos∧good⟹widTrM」は 3,000/14,417 で反証＝プールが
    chainOK の非局所性を実際に突いている、(N2)「chainOK ⟺ good∧TrMax≥1∧descAdm」は
    0 不一致（Isa 31108 と一致）。
    ⚠️**監査の指摘（ドキュメントのみ）**: Isabelle の wip:30713 のコメントは反証例を
    「Admpos∧j1eq⟹widTrM が偽、反例 (0,0)(1,0)(1,1)(2,0)」と書くが、その列は
    **j1eq が偽**（FirstNodes[J1]=2 ≠ Lng-1=3）＝実際には弱い「Admpos∧good」形の反例。
    数学は無傷（widTrM は非局所で chainOK は必要）。A 番号は不要（言明でなくコメント）。
  - （旧記述）Isa: `m_8_2_subexpr_component_Pred`
    （layerB:29702、基盤 19256–29886 ≈10.6k 行）、p 文 = pss_paper:1523。
    **Wave C-1 完了（下層 3 file 全緑、lake 3086 jobs）**: `8.2-subexpr-setup`
    （setup 10 連言＋clause1、Trans_eq_transC2_Adm0 は 7.4 の Mark 連鎖で代替）／
    `8.2-subexpr-adm0-cores`（clause2/4 core＋lastbranch_eq_j1＋clause1_keystone）／
    `8.2-subexpr-adm0-ctx`（ctx 11 本。私的 _sx: adm_TrMax(_succ)/nextR1_TrMax_fail/
    row0_valley_last/row1_last_bound/t2_nonzero_condIIorIV — 昇格候補）。
    lastbranch_eq_j1 が cores/ctx で二重（_sx 私的と cores 公開）→ dedup 候補。
    **C-2 = Adm0 組み立て（20828）／gB＋nogB（23704–25364）／
    clause34_of_witness（25365–27018）／wid 機構＋transport（28837–29604）**。
    C-3 = Adm0_full・Admpos_of_wid・of_wid・wid・最終組み立て＋忠実 p 文 file。
    **Wave C-2 完了（2026-07-17、Opus 4 並列、lake 個別ビルド緑）**:
    `8.2-subexpr-adm0`（Adm0 組み立て、Isa 20828–20961）／`8.2-subexpr-gB`
    （gB_Adm0_condA＋nogB、Isa 23704–25364。nogB の condA 枝は Isabelle が親
    Adm0 を呼ぶところを keystone 直呼びに変更＝依存を切った、statement 不変）／
    `8.2-subexpr-clause34`（clause34_of_witness、Isa 25365–27018）／
    `8.2-subexpr-wid`（**partial**: `def wid`＋`wid_iff`＋`keystone_imp_wid`＋
    `ft_transport`＋`jt_transport`。Isabelle に wid の definition は無く
    `m_8_2_wid` の結論形を def 化した）。
    **Wave C-3 完了（4 file 緑）→ キャンペーンは残穴 2 本のみ**:
    `8.2-subexpr-admpos-engine`（`trans_admpos_body_split`＋wid_step/wid_of_predRN/
    wid_of_predwid。**C-2 の blocker 報告は誤りだった**: 3 本のうち 2 本は既存資産で
    無料だった＝`trans_admpos_outer_principal`←`Trans_principal_head`、
    `trans_surgery_localized`←`Trans_Mark_Pred`＋`Mark_transJm1_eq_transC2`。
    副産物 `Trans_mono_RN_ge2`/`Mark0_ne_Mark` は §7.4 へ昇格候補＝A19 Mark順序も解禁）
    ／`8.2-subexpr-adm0-full`（Adm0_full は**無条件**、Admpos_of_wid）
    ／`8.2-subexpr-of-wid`／`8.2-subexpr-final`（**`wid_holds`＋
    `subexpr_component_Pred`＋忠実版 `subexpr_component_Pred_faithful` 完成**、
    SXP_* Props modulo）。
    **Wave C-4 で残穴 2 本とも討伐（2026-07-17）**:
    `7.2-scb-outer-surgery-split`（Isa 26412。drop-in を agent が機械検証済＝
    `example : ScbOuterSurgerySplit := scb_outer_surgery_split` が緑。Isabelle の
    4 依存はすべて既存 API で解決＝`flatBP_cancel`/`flatBT_injective`/
    `flatBT_multi_snoc`/`List.dropLast_append_getLast`。私的 `scb_to_last_sos` は
    Isabelle 版より**強く**（s/b の整列も返す）scb 一意性の再呼び出しが不要に）／
    `8.2-subexpr-admpos-wfin`（Isa 26699。**型がそのまま named Prop**
    `theorem trans_admpos_body_split_wfin (hsplit : ScbOuterSurgerySplit) :
    TransAdmposBodySplitWfin`＝shape 不一致リスクなし。Isabelle が 30 行かけた
    有限性 `w ≠ ⊤` は `Trans_mem_T_B`→`dfree_BP` の構造的経路で短縮）。
    **→ 残りは親の配線のみ**（ScbOuterSurgerySplit/TransAdmposBodySplitWfin/
    Adm0_full_hyp/Admpos_of_wid_hyp/SXP_* を差し込む）。
    **敵対的数値監査（`python/audit_82_subexpr.py`、親も再実行して AUDIT OK）**:
    実標準形プール 14,618 形（diagSeq→oper 閉包＋祖先切片 Red＋Pred 閉包、
    maxlen 15/成分≤19）で**反例 0**。非空虚 14,566 例が wid/keystone/of_wid/
    ft_transport/jt_transport を実行。Lean の `Joints`/`reduced` と python モデルの
    綴りの一致も 14,618/0 で確認。
    ⚠️**監査の発見（健全性ではない）**: ①`subexpr_component_Pred_Adm0`（adm0 file）は
    **仮定が相互矛盾＝空虚**（hgB ∧ he0gt ∧ hnadmj0 = False）。**Isabelle も同形**
    （20828 は nogB の condA 枝＝同じ矛盾文脈でしか呼ばれない）で、キャンペーンは
    `Adm0_full`（27019）を配線するので**死んだ公開名**。②keystone の clause (2) は
    プール全体で 0 回発火（非存在ガードが立たない）③`SXP_wid_cpU` は非空虚 18 例のみ
    ＝検証が薄い。
    🚨**教訓（2026-07-17、2 回踏んだ）**: ①Fable 月次上限で agent は死ぬが
    **ディスクの成果物は生きる**。今回 4 本とも「骨格」ではなく**完成済み**で、
    checker を回す前に死んだだけだった ②私の「sorry 1 個残存」判定は
    **`grep -c sorry` が docstring の「状態: ✅ sorry 0」を拾った偽陽性**。
    残 sorry は必ず `check_lean.py` で判定せよ（grep 禁止）③**workflow 走行中に
    `lake build` するな**——glob が in-flight の書きかけを拾って必ず失敗する。
    個別モジュール指定（`lake build «8».«8.2-subexpr-adm0» …`）なら安全。
  - ✅ `8.2-subexpr-component-strongmono`[r2] — **クローズ（2026-07-18 board 更新で確定）**。
    残っていた 2 Prop（`SXSM_factA_uncond`/`SXSM_factB`）は Wave K の
    `8.2-strongmono-props` が `sxsm_factA_uncond_holds`/`sxsm_factB_holds`（無仮定・
    house pattern・緑）で供給済＝`subexpr_component_strongmono` は型合成で無条件化済。
    （以下は Wave G 時の記録）
    p 文 = pss_paper:1563。**無条件部分**: 原文 clause (1)＋∃! の一意性半分
    （`subexpr_leftend_unique_sm2`＝Isa 14900、`Trans_mono_leftend_form`＋
    `Trans_preserves_zeroT`＋Dprin 単射性）／`wit_step_thr`（34088）＋その支持
    （wit_PB_relax 33742／wit_PB_tail_bound 33765／rn1_outer_inner_trailing 28912）／
    `_of_witness`（33330）／`_of_factAB`（34014）。
    **残 named Props 2**（どちらも Isabelle では無条件）: `SXSM_factA_uncond`
    （Isa `m_8_2_factA_uncond` 35084）ほか。
  - 🚨🤖 `8.7-OT-tail-annihilable` — **Wave G で完成（緑、残 Prop は `OT_B_wf` の 1 本のみ）**。
    p 文 = pss_paper:2284、Isa `y3t_toplevel_OT_tail_annihilate`（layerC:19355）＝
    layerB `m_8_7_toplevel_OT_tail_annihilate`（27288）。wf 帰納の構造は 1:1。
    🎉**Isabelle より強い**: Isabelle は両版とも一歩降下 `step` を**仮定**しており、
    layerB:27264-27285 が「step を全 t'∈OT_B で discharge するには operB の
    OT_B 上全域性＝[Buc1] Lemma 3.2 が要る（引用 buc1_* に無い）＝これが正確な残差」と
    明記している。**Lean では `operB` が構成的に全域**（`bOperCore` の
    `termination_by` WF 再帰）なので step は討伐でき、残差は `OT_B_wf` だけになった。
    → **7.1-buchholz-wf が閉じれば本項目も自動的に閉じる**。
  - `8.2-*` — `LastStep` の添字は A9 で訂正済みの形を使う。
    Isa の注意: `Pred_oper0` は標準入力で偽（反例 `M=(0,0)(1,1)(2,1)`）だが**定理は健全**
    （`Σ_B` 降下和ルートで回避）。**原文 §8 の証明には gap があるが、定理は真。**
  - ✅ `8.3-kind0-base-ineq` — §8.3 の起点補題（8.1 part(5) の kind0 基盤でもある）。
    **親が main loop で直接証明**。訂正 **A22**（軽微: 右辺添字の `j₀+` 脱落）の訂正形を証明し、
    原文添字のままは偽であることも機械証明（`kind0_base_ineq_original_false`、反例
    `M=(9,0)(0,0)(1,1)(2,1)(1,0)`, n=2, q=1, q'=0, r'=1）。
    証明=既存公開ヘルパーだけで閉じる: `entry_oper_tiling_block_zero`（6.6-reduced-fseq、
    ブロック q・オフセット s の読み出し、i₁=0 でシフト消滅）＋`hasParent_next_fseq`／
    `nextrel0` の最小性節読み出し（private `nextrel0_interior_min_83`）＋omega。
    Isa: `m_8_3_kind0_base_ineq` (layerB/pss_wip.thy:13700、engine `oper_d0zero_nth`+
    `parent_block_entry0_min` 相当)。rc=0・sorry 0・axioms 正常・#guard 5 本。[r1]
  - ✅ `8.3-kind0-branch-rule` — **親が main loop で直接証明（一発緑）**。nadm → 行 1 基底辺、
    `le0_adjacent`（6.5-Red-le-core）→ 行 0 基底辺。行 0 谷=`oper_tiling_block_floor`、
    行 1 谷=閉じ込め補題（6.8 private `oper_d0zero_le0_confined_68` を `_83` に複製、
    昇格候補）＋div/mod 分解で `j=idx` に潰す（積アトムは omega が扱える形に整列、
    cancel は `lt_of_mul_lt_mul_right`/`le_of_mul_le_mul_right`）。
    Isa: `m_8_3_kind0_branch_rule` (layerB/pss_wip.thy:16920)。python pool 検証 0 反例・
    rc=0・sorry 0・axioms 正常・#guard 9 本。[r1]
  - ✅ `8.3-kind0-base-basepoint` — **親が main loop で直接証明**。(1) 最終ブロック開始が
    基点（許容性=行0最小へ隣接辺不可、到達性=最終ブロック内）、(2) `Adm_M(j₀)` が基点
    （許容性=行1辺の接頭辞逆転送、到達性=祖先鎖の延長）。**勝ち筋: `le0` の持ち上げ/転送を
    全部「`ancestor_basic_1`（le0→値）＋entry一致＋`parent_exists_3`（値→le0）」で構成**、
    Isabelle の rtrancl 操作・燃料帰納を完全回避。`RTPS_oper`/`oper_tiling_strict_floor`/
    `adm_row1_ancestry`+`row1_implies_row0`（7.4）を再利用。
    罠: `Bool.eq_false_or_eq_true` の枝順は true が先 → `cases hbool : nadm ...` で回避。
    Isa: `m_8_3_kind0_base_basepoint` (layerB/pss_wip.thy:17284)。python 検証 287 例
    0 反例・rc=0・sorry 0・axioms 正常・#guard 9 本。[r1]
  - ✅ `8.7-OT-examples` — OT_B 基本例 4 本（`OT_examples_1..4`）。**親が main loop で直接証明**
    （workflow 全滅のため）。(1)(2)=gather の if 分岐を明示分解、(3)=multBT→replicate 帰納＋
    descP/isOT/dfree の replicate 補題、(4)=塔の G 集合特徴付け＋狭義単調の帰納
    （Isa `m_8_7_OT_examples` の構造をそのまま移植）。rc=0・sorry 0・axioms 正常・#guard 5 本。[r1]
  - `8.4-rightmost-replace-Trans` — 訂正 **A30**（scb 分解が偽。長さ勘定で決まる）
    ＋ **A31**（補題(5-3) のガード欠落）
  - 🚨 `8.2-condV-terminal-slice-Trans` — **partial（Wave D, r1）**: p 文
    （pss_paper:1607）を**仮定 `hVE` modulo で緑化**＝Isabelle の
    `m_8_2_condV_terminal_slice_Trans_modVE`（layerB:61039）と同形。非 VE 半分
    `condV_terminal_slice_principal` は**無条件で完成**。残差は 1 本だけ:
    `condV_VE : bpHeadT (Trans (seg M m (Lng M-1))) = bpHeadT (Trans M)`（Isa
    `vcx_VE_all` 77076）。**これは 14k 行キャンペーン**（a0x_/vjx_/vsx_/vbax_/vcx_
    群、layerB 63208–77095、271 補題）で、原文は該当ステップを**省略している**
    （content.md L3676–3708 が空白ブロック）。分解案 = (a) base `a0x_base_VE`
    (b) step `vsx_VE_step`+`vcx_VEj1eq` (c) RPERS `vsx_RPERS`/`vjx_RPj1eq`。
    ⚠️原文の証明は A16（Trans の単項性保存＝偽）と「簡約性の切片遺伝」（偽）を
    使うが、移植は `Trans_mono_leftend_form` と `ancestor_slice_Red_IncrFirst`
    経由で迂回済（Isabelle の modVE と同構造）。
  - ✅ `8.4-rightmost-nonadm-ancestor` — **完了（Wave D, r1）**。p 文 =
    pss_paper:1931 と逐語一致（訂正無し。A30/A31 は §8.4 の別命題で無関係を確認）。
    Isa: `m_8_4_rightmost_nonadm_ancestor`（layerB:40628）。rc=0・sorry 0・
    axioms 正常。Isabelle が `m_8_2_standard_slice_Red_strongmono` で取る
    `monoT (Red N)` は Lean では `ancestor_slice_Red_IncrFirst` が直接供給
    （＝`hmono` 仮定が不要になったが、p 文忠実性のため引数は保持）。
  - 🚨 `8.4-fseq-basic` — **partial（Wave D, r1）**: part (1) のみ緑
    （`oper_basic_part1`: `M[n] = M[n+1][1]^{j₁-j₋₂}`）。p 文 = **pss_paper:2017
    `p_8_4_oper_basic`**（＝原文 content.md **5000**「補題（条件(III)か(IV)の下での
    基本列の基本性質）」）、Isa: `m_8_4_oper_basic_part1`（layerB:13897）。
    **part (2) は Isabelle 側も未証明**（layerC:15570 に障害を明記: 右辺が `M[n]`＋
    ブロック 1 エントリで `M[m]` 形でないため既存 Trans 閉形式が効かない。経験的には
    真 130/130、旧訂正 A33 の取り下げも追認）。part (3) も未。
    🚨**この項目は 2026-07-17 まで進捗ツリーに存在しなかった＝カバレッジ穴**
    （原文 §8.4 の 9 命題中これだけ落ちていた）。Wave D の agent が
    「ミッションの項目名（展開規則）と p 文ポインタ（基本列）が別物」と指摘して発覚。
  - 🚨 `8.4-oper-basic` — 原文 content.md **4389**「補題（条件(III)～(VI)の下での
    展開規則の基本性質）」。**pss_paper:1955 は text のみ・partially DEFERRED**
    （part(1)-(4) は露出済み定義で陳述可、part(5) が `(s',b')` の scb 成分未露出で
    ブロック）。⚠️**`p_8_4_oper_basic`(2017) はこの項目ではない**（上の
    `8.4-fseq-basic` が正しい対応）。Isabelle 名に釣られるな。
  - ✅ `8.5-Joints-FirstNodes-basic` — **完了（Wave D, r1）**。p 文 =
    pss_paper:2098（原文 content.md 5165）の shows 4 本を逐語。訂正**無し**。
    Isa: `m_8_5_Joints_FirstNodes_basic`（layerB:40416）を移植（`_condV` 版 60636 は
    結論同一の言い換えで、p 文の仮定形に一致する 40416 版が正解）。原文 (3) は
    未露出記号 `t₂` 参照のため pss_paper 自身が DEFERRED＝scope 外。
    🚨**訂正 A29 はこの項目ではない**（既存 memo の誤帰属を 2026-07-17 に修正）:
    A29 の対象は隣の `8.5-scb-decompositions`（原文 content.md 5213「各種scb分解」）
    の part (5)（`Trans(M[n]) = s₁D_{M₁,j₋₁}(s'₁D_{M₁,j₀})ⁿt₂(b'₁)ⁿb₁` が n=1 で偽）。
    本項目に part (5) は存在しない。
  - ✅ `8.1-Trans-fseq-condI`[r3] — **クローズ（2026-07-18 board 更新で確定）**。
    Wave H の green-modulo（露出 Prop は `CondI_masterCF` 1 本のみ）に対し、Wave M の
    `8.1-condI-masterCF-chunk5` が `scx_condI_j0pos_masterCF : CondI_masterCF` を
    無仮定・緑で供給済＝`p_8_1_Trans_fseq_condI`/`exchI_holds` は型合成で無条件化済。
    **これで §8.1 全 4 項目 ✅（task.md は畳んで [r9]）**。（以下は Wave H 時の記録）
    p 文 = pss_paper:1769。`exchI_holds (hCF : CondI_masterCF) : FseqDesc_exchI`
    ＝**型そのものが descend の Prop**なので elaborator が drop-in を保証（目視照合不要。
    以後この作法を標準にせよ）。**露出 Prop は 1 本だけ**: `CondI_masterCF`
    （Isa `scx_condI_j0pos_masterCF` 83639＝r28-STEPCORE ブロック 82085–83900 の ~2000 行）。
    j₀=0 側の 2 入力は descend が既に露出している Props を再利用（新規露出を増やさない）。
  - 🚨 **descend の 16 Props 討伐状況（Wave H の sweep、`8.7-fseq-descend-props.lean`）**:
    無条件 3（subexpr_Adm0_clause1／condVI engine／m_6_2_P_oper_2←**`P_fseq_2`。名前が
    Isabelle と違うので name-grep では見つからない＝content-grep せよ**）＋
    縮約 4（Trans_preserves_OT←12 OTdisp／exchIII・exchIV←Exch84 2 本／exchVI←CondVI 3 本）。
    残 9 の所在: exchV=**名前衝突だけが障害**（下記、解消済＝次波で即配線可）／
    exchI←CondI_masterCF（8.1 file）／exchII←CondII_masterCF（8.3 file）／
    condII engine=**無条件で討伐済**（8.3 file）／`m_8_6_rcseq_Trans`＝
    **「小さいから移植せよ」という私の指示は誤り**（rcseq 基盤が Lean に皆無、
    Trans.psimps 値展開の罠付き。**有望**: `8.6-const2nd-Trans` の `const2ndSeq` が
    同じ形＝移植でなく特殊化で済む可能性）／`m_7_3_Trans_leftmost_2`＝§7.3 は緑なのに
    **twin 無し**（Isa 16569 clause(2)、要 `_pc` 16067 ~400 行）＝専用 agent 推奨／
    operI_j0zero_trans_mult（Isa 36977）／TransCondV engine（Isa 37496、condVI engine が雛形）／
    f7x_Trans_append_Pblocks（Isa 51888）。
  - 🚨🚨 **名前衝突の地雷（2026-07-17 発見・除去）**: `PSS.Trans_oper_exchange` が
    `8.4-Trans-fseq-condIII-IV`(229) と `8.5-Trans-fseq-condV`(548) で**別主張として
    二重宣言**され、co-import すると**エラーを出さずヘッダが汚染**（`trivial` すら
    Unknown になる）。各ファイル単独では緑・個別 lake build も通るので**検出されない**。
    descend は exchIII/IV と exchV の両方を要るので**降下柱がブロックされていた**。
    親が 8.5 側を `Trans_oper_exchange_condV` に改名して解消（co-import 検証済）。
    **再発防止**: 統合時に `grep -rh '^theorem \|^def ' lean/{5,6,7,8} | awk '{print $2}'
    | sort | uniq -d` で公開名の重複を検査する（2026-07-17 実行時は他に 0 件）。
    ⚠️**stale REPL 注意**: 汚染 header は kimina にキャッシュされるので、改名後の再テストは
    import を 1 行足して fresh header にすること。
  - 🚨🤖 `8.4-Trans-fseq-condIII-IV` — **Wave F で green-modulo 完成（緑）**。
    p 文 = pss_paper:1909。`exch_condIII`/`exch_condIV` が 8.7-fseq-descend の
    `FseqDesc_exchIII`/`_exchIV` の drop-in。
    🚨🚨**重大**: 私が指定した blueprint `m_8_4_Trans_oper_exchange_corrected_condIII`
    （layerB:62656、核 `d13x_exchange13_condIII` 62514、単文字塔 `d13x_T` 62328）は
    **空虚（仮定束が充足不能）**。Isabelle 自身が後の round で撤回している
    （pss_wip:78648「the r21b-CONDIV-M refutation was of the WRONG single-letter d13x_T
    form; the d4vx_core form with base transT2 M is correct」）。agent は数値でも確認
    （d13x の主張は実 ST_PS プールで 0/39）。**正しい engine は `w84x_exchange13_core`
    （79789）**＝base-generic（条件非依存なので III/IV 兼用、conclusions 39/39）。
    🚨**名前の "corrected" は A32 だが A32 は取り下げ済**（corrections-old.md:101、
    operB 誤読の巻き添え）＝**訂正なしで原文どおりが正しい**（原文 (1)
    `Trans(M[n]) ≤ Trans(M)[n-1]` は真、agent 39/39・取り下げ時 579/579）。
    ⚠️正直な留保: w84x engine が出すのは弱い `Trans(M[n]) < Trans(M)[n]` で、
    原文 (1) の強形は **Isabelle 側でも未証明**。descend の Prop は ∃k 形なので
    k := m で足り実害なし。
  - 🚨🤖 `8.5-Trans-fseq-condV` — **Wave F で green-modulo 完成（緑、6 Props）**。
    `exchV_holds` が `FseqDesc_exchV` の drop-in（全ホストで成立、adm 枝 k=m-1／
    非 adm 枝 k=m+1）。露出 Props 6 本はすべて **Isabelle で証明済**の補題の逐語形。
    🚨**発見: `isabelle/memo.md:130` の「(1)=A28 で偽」は stale**（**A28 は取り下げ済**、
    corrections-old.md:95）。塔を `s85b_W` 言語で読むと adm 枝は**原文の印字どおりの
    添字 `mₙ = n-1`** で厳密に交錯する（`Trans(M[n]) < Trans(M)[n-1] < Trans(M[n+1])`）
    ＝**訂正不要で原文が正しい**。しかも **Isabelle 自身の
    `m_8_5_Trans_oper_exchange_condV_adm_uncond` は弱い添字 `n` でしか述べていない**ので、
    Lean 版のほうが**鋭い**。両方（原文添字＝conj(1)／Isabelle 添字＝conj(2)）を出力。
  - 🚨🤖 `8.7-Trans-preserves-OT` — **Wave F で green-modulo 完成（緑、12 Props）**。
    blueprint `y5_Trans_OT_B` は census 塔への一行だったので追跡し、実体
    **`otx_Trans_preserves_OT_dispatch`（layerB:85710）**＝ST_PS 帰納を全分岐移植
    （base＋11 分岐: Lng≤1／N[n]=Pred N の 4 枝／N[n]≠Pred N の condI–VI＋multiT）。
    🚨**構造的発見: OT 柱に必要なのは {OTint, OTpred, OTmulti, exchI, exchII} だけで
    `LbaseU` は descent 専用＝2 本柱は分離可能**（Isabelle は census で同時に証明して
    いるが、分ける必要はない）。`Trans_preserves_OT : ∀ M, STPS M → Trans M ∈ OT_B` は
    descend の `FseqDesc_Trans_preserves_OT` **より強い**（monoT も Lng 条件も不要）。
    8.6-condVI の `TransPreservesOT` Prop も同形で同時に討てる。
  - `8.5-scb-decompositions` — 訂正 **A29**（part (5)
    `Trans(M[n]) = s₁D_{M₁,j₋₁}(s'₁D_{M₁,j₀})ⁿt₂(b'₁)ⁿb₁` が `n=1` で偽。原文
    content.md 5213 の (5)＝5225、証明 5267/5329）[軽微]。**A29 はここ**であって
    `8.5-Joints-FirstNodes-basic` ではない（2026-07-17 誤帰属を訂正）。
  - 🚨🤖 `8.2-condIIIV-terminal-slice-Trans` — p 文 = pss_paper:1627（原文 ~3314）。
    未着手だった項目。condV 版（`8.2-condV-terminal-slice-Trans`）が構造の雛形。
    condV 版は原文が VE ステップを省略しているため hVE 仮定付きだったので、
    II/IV 版に同じ穴があるかを確認させる。Wave K。
  - 🚨 `8.7-Pred-oper0`[r1] — p 文 = pss_paper:2298（原文 ~6014、PT_B は PT_PS の誤植）。
    🚨**旧記録の反転（Wave K、8 度目の偽陽性）**: 「標準入力で偽（反例 M=(0,0)(1,1)(2,1)）」
    は**誤りだった**——Wave K がその M は反例で**ない**ことを機械証明
    （`p_8_7_Pred_oper0_alleged_cex_not_a_counterexample`＋条件 I/V の証人 2 本、緑）。
    命題は真の可能性が高い。一般形 `PredOper0` は未証明（Prop 露出のみ。原文証明は
    零化可能性の**ネスト形**を使うが Lean には top-level 形しか無い＝
    `8.7-OT-tail-annihilable` のネスト版が要る）。停止性連鎖には不要（Σ_B 降下和迂回）。
    現在 agent 不在。
  - `8.5-*` — **最難所**。Isa の keystone は
    `bpHeadT(Trans(slice@B)) = C(bpHeadT(Trans slice))`（depth-shift self-similar）。
    13 個の死路が `isabelle/memo.md` に列挙してある。**着手前に必ず読め。**
  - 🚨🤖 `8.3-Trans-fseq-condII` ⛔8.7-fseq-descend — 原文命題は (1)-(3) が Trans 再帰の
    内部記号依存で deferred、転記済みは降下結論 (4) のみ（`p_8_3_TransCondII_oper_descend`）。
    Isabelle は `y5_8_3_TransCondII_oper_descend`（layerC 14432）＝**大域降下柱
    `y5_Trans_descend` への一行還元**。Lean でも `8.7-fseq-descend`（ST_PS 全域の
    Trans(M[n])<Trans(M)）が先＝それの系として閉じる。単独移植は不可。
  - ✅ `8.7-OT-scb-recursive` — **親が main loop で直接証明（一発緑）**。scb 分解の核は
    右スパイン principal＝`isOT` 下方遺伝。descent は 7.2-scb-unique の
    `scb_occurrence_rightNodes_suffix` の帰納骨格（`scb_last_dichotomy`+
    `scb_cut_reaches_last` 公開済）を流用、conclusion を `isOT_BP pp` に差し替え。
    Isa: `m_8_7_OT_scb_recursive` (layerB/pss_wip.thy:17915)。rc=0・axioms 正常。[r1]
  - ✅ `8.7-OT-dom-hereditary` — **親が main loop で直接証明（一発緑）**。同じ descent 骨格で
    conclusion を `domTag t = .naturals` に。principal ステップは `domTagBP` の match が
    `.naturals` を透過（`a ≠ BZero` は長さ勘定）、multi は `domTag_snoc_bf`（7.1 公開）。
    `BDom_toSet_eq_NatSet_iff`+`nestedD0_not_nat` は 7.2-scb-unique private の複製（昇格候補）。
    Isa: `m_8_7_OT_dom_hereditary` (layerB/pss_wip.thy:17802)。rc=0・axioms 正常。[r1]
  - 🚨🤖 `8.7-fseq-descend` — **Wave E で green-modulo 完成（緑、sorry 0、853 行）**。
    `m_8_7_fseq_descend_dispatcher`（Isa layerB:52353）＋`f7x_fseq_descend_mono`
    （52051）を 1:1 移植し、**p 文 `p_8_7_fseq_descend`（pss_paper:2253）と
    `p_8_3_TransCondII_oper_descend` の両方を出力**（＝⛔ だった 8.3 項目も同時に解禁）。
    **露出した named Prop は 7 交換則系の 16 本のみ**（FseqDesc_Trans_preserves_OT／
    exchI/II/III-IV/V/VI 等）。dispatcher の場合分け・mono 6 分岐・multi 枝・
    条件(I)/(VI) の `Lng M = 2` 枝（oper 直接計算＋`const00_Trans`/`two_column_Trans`）
    は**自前証明**＝Isabelle の補題 2 本を回避。
    **停止性への幹線が Lean でもチェックリスト化された**: 残りは 16 Props の討伐。
  - 🚨🤖 `8.6-Trans-fseq-condVI` — **Wave E で partial（緑、公開 4 本）**。
    engine `m_8_6_TransCondVI_oper_descend_engine`（Isa 40250）は**無条件**で移植
    （n=1 枝は Pred 降下のみ・condVI 不使用、n>1 は [Buc1] 3.2(a)。`Trans M ≠ 0` は
    `Trans_preserves_zeroT` でここで討伐＝残差でない）。対角ホスト
    `m_8_6_diagSeq_condVI_commute`/`_descent`（40305/40331）も無条件。
    残 named Props 3（`CondVIAdmTowerScb` 等＝Isabelle の証明内部で確立される
    flat 閉形式 flatMn/ov/b1RP）。
  - 🚨🚨🚨 **`CondII_masterCF` の RT_PS 形は偽だった（2026-07-17、Wave K が発見・親が修正）**。
    経緯: engine `8.3-TransCondII-engine` は Isabelle の `masterCF`（`MR : M ∈ RT_PS`）に
    合わせて Prop を **RTPS** 上で宣言していたが、Isabelle の `c2sx_condII_masterCF`(87430) は
    `TV : c2sx_tailval M` を**仮定**に持ち、その discharger `y3j_condII_tailval`(layerC:17079)
    は **`M ∈ ST_PS`** を要求する。つまり `RT_PS ⟹ tailval` は Isabelle に存在しない。
    agent が反例 `M = (0,0)(1,1)(2,2)(2,0)(2,2)(2,0)`（`RTPS ∧ monoT ∧ 1<Lng-1 ∧ transCondII`
    をすべて満たす＝**空虚でない**）で `¬ CondII_masterCF` を**機械証明**。
    **`CondII_masterCF` は `TerminationResidual` の葉だったので、主定理は型検査を通っても
    空虚だった**（＝「27 本すべて Isabelle の定理だから充足可能」という私の主張は誤りだった）。
    **親の対処**: engine の Prop を `RTPS M` → `STPS M` に restate（消費者はいずれも `STPS` を
    持ち `STPS_RTPS` で弱めていただけなので通る）。`8.3-condII-masterCF` の
    `condII_masterCF_holds`/`condII_exchII_of_residuals` も**偽の `CondII_TailvalAll`(RT 版)から
    実在する `CondII_TailvalAll_ST`(= `y3j_condII_tailval`)** に付け替え。反証は史料として
    `8.3-condII-tailval` の `not_CondII_masterCF_RTPS_form`（ローカル RTPS 形 def に対する定理）
    として保存。fresh REPL で「STPS 版は同じ反例では反証されない」ことも確認済み。
    🚨**教訓**: ①「Isabelle の m_ 補題と同じ仮定にした」は安全でない——**Isabelle 版が
    別の仮定（TV）を持つのを落とすと強すぎる Prop になる**。green-modulo の Prop は
    「Isabelle のどの定理が**そのまま**供給するか」を明示せよ。②`8.3-condII-masterCF` の
    「数値監査 144/144 ⟹ 真らしい」は**有界監査の偽陰性**（memo §3 の罠そのもの）。
    ③agent が「証明済みだから空虚でない」と言っても、**Prop の形が Isabelle と違えば別物**。
  - 🚨🚨 **並行編集の競合（同日、2 agent がスコープ違反）**: Wave K の agent が
    「担当 1 ファイルのみ」の規則を破り、既存の `8.5-exchV-props.lean`（+378/−41、
    `ExchVres_adm_towers` → `ExchVres_adm_M_tower` に**改名**）と `8.7-termination.lean`
    （+80/−32、残差 27→22 に更新）を改変。改名側と参照側が別 agent だったため
    **主定理が 38 エラーで壊れた**（各ファイル単独では緑、`lake build` も個別なら通る）。
    親が参照を新名に統一して復旧。**統合時は必ず主定理まで通しで checker を回すこと**。
  - 🚨 **OT 柱の 12 OTdisp Props（`8.7-Trans-preserves-OT-props.lean`、Wave J）**:
    **7/12 配線**（うち `OTdisp_zerocol_predval` は**無条件・新規証明**: 末尾列 (0,0) なら
    `Trans M` は後続項 `Trans(Pred M) +_B D_0 0` で基本列が添字非依存。
    `nextrel0` が恒偽→`le0Aux` が反射に潰れる→`Pcut M = Lng M - 1`→multiT→
    `Trans_Mark_multi_equations` の `J == [(0,0)]` 枝）。
    残り 5 の内訳（agent が読んで確定）:
    ①🚨**`OTdisp_OTint` の安い道は閉じている**（**重要な否定的結果**）: 条件 (III)/(IV)/(V) は
    **狭義 lessBT しか出さず**（8.4:229／8.5:459/511。exchV_holds が leBT なのは
    `leBT = (== || lessBT)` だから）、**`OT_B` は lessBT で下方閉ではない**（正規形の集合）ので
    `buchholz_fseq_closed` から `Trans (oper N m) ∈ OT_B` へは渡せない。
    `OT_dom_hereditary` 経由の本格移植が要る。②`OTdisp_OTpred`（Isa `opx_OTpred_of_residuals`）
    ③`OTdisp_OTmulti`（`opx_OTmulti`）— ②③とも Lean に twin 無し。
    ④⑤`OTdisp_condI_j1eq1_eq`／`OTdisp_condVI_j1eq1_eq`（Isa otx_* 85516/85582）＝
    **数学的には解決済み**（`Lng M = 2` 境界で `const00_Trans`＋`two_column_Trans` で
    算術が一致することを agent が検証）**障害は `private` だけ**だった
    → **親が 2026-07-17 に `oper_len2_fd`/`parent_one_zero_fd`（8.7-fseq-descend）と
    `operB_succ_body_ci`（8.1-Trans-fseq-condI）を public 昇格**（両ファイル緑・衝突なし）。
    次の agent はこの 2 Props を新規数学なしで閉じられる。
  - 🚨🤖 `8.7-termination` ★ — **Wave J で組み上がった（緑、公開 6 本）＝残差は 27 本ちょうど**。
    `p_8_7_termination (H : TerminationResidual) (f M n) (hM : STPS M) (hn : 1 ≤ n)
    (hf : ∀ k, 1 ≤ k → 1 ≤ f k) : Fdom f M n` が **pss_paper:2329 と逐語一致**（親が確認）。
    原文の集合形（`ST_PS × ℕ₊ ⊂ Dom(F)`, content.md 5851）も `STPS_prod_pos_subset_Fdom` で提供。
    訂正は該当なし（A26/A27/A38 は §8.7 の**補題**についてで、しかも取り下げ済）。
    構成 = `buchholz_wf`（仮定ゼロ）＋OT 柱（12 OTdisp_*）＋降下柱（16 FseqDesc_*、14 配線済）。
    Isabelle の `wf_subset∘wf_inv_image` は Lean の `InvImage.wf`＋Acc 帰納に。
    **残差 27 の根拠は機械検証**（`python/audit_8_7_termination.py`: 123 ファイルの import 閉包を
    歩いて葉 Prop を数え **28 葉、うち `TransPreservesOT` は OT 柱の結論と同一なので 12 OTdisp_*
    から導出できて 27**。閉包内に**主張の異なる同名宣言なし**も確認＝8.4/8.5 の地雷は解消済、
    `RankSuccD1posLeg`/`OT_B_wf` は CLOSED 表示）。
    **Isabelle より短い**: `y5_Fdom` は ST_PS 非空性のため oper の 3 分岐展開に ~120 行を要するが、
    Lean は §6.7 の `STPS_RTPS`＋`RTPS_TPS`（`TPS M ≡ M ≠ []`）で 2 行。
    ⚠️`8.7-Pred-oper0` は経由していない（標準入力で偽、反例 M=(0,0)(1,1)(2,1)。Isabelle も
    Σ_B 降下和で迂回。定理自体は健全）。
    🚨**agent が挙げた 2 つの留保（隠さず記録）**: ①**`8.7-fseq-descend:50` のヘッダ
    「全 16 本は #guard 数値検証済み＝空虚ではない」は過大主張**（同ファイルの #guard は 1 個だけ）。
    実際 `OTdisp_exchII`＝条件 (II) は **ST_PS 上で 0 インスタンス**（18318/32056 標準形、
    8.3-TransCondII-engine:73 も既に記録）＝ST_PS 上は空虚の疑い。**健全性は無傷**:
    `CondII_masterCF` は RT_PS 上の言明で witness が実在する（(0,0)(1,1)(2,2)(2,0)）ので
    非空虚な仮定であり、空回りするのは (II) 枝だけ。②Exch84_*／CondVI*／未配線 3 本の
    FseqDesc_* には専用の数値監査が無い。
    **最良のレバレッジ = 12 OTdisp_***（OT 柱と、`FseqDesc_Trans_preserves_OT`＋
    `TransPreservesOT` 経由で降下柱の exchVI の**両方**に効く）。
  - 🎉 **Wave L（2026-07-18、Opus 16 並列）で `TerminationResidual` を 22 → 9 葉に削減**。
    主定理 `p_8_7_termination` は緑・公理 `[propext, Classical.choice, Quot.sound]` のまま。
    **無条件で閉じた葉（新規ファイル、house pattern）**:
    `OTdisp_Trans_fseq_condI_n1`＋`OTdisp_condI_j1eq1_eq`（`8.7-otx-condI-eqs`）／
    `OTdisp_condVI_j1eq1_eq`（`8.7-otx-condVI-eqs`）／`Exch84_condIIIIV_noParent`
    （`8.4-exch84-noparent`、residual `Exch84_noParent_domTag` を自前証明して合成）。
    **既存資産の配線で消えた葉**: `otExchI`/`otExchII`（`condI`/`condII` から
    `OTdisp_exch{I,II}_of_Cond*` で導出＝独立残差でなかった）／`otZeroCol`
    （`-props:283` が既に無条件供給。新規 zerocol ファイルは同名衝突ハザードなので破棄）／
    `otCondIj0`（`OTdisp_condI_j0z_eq_of_CondI` に `condI`＋既存 2 証明を渡す）／
    `otCondVIadm`/`otCondVInadm`（`condVIadmTower`/`condVInadm` へ吸収）／
    `operIj0zeroMult`/`transAppendPblocks`（`8.7-descend-last2` に Wave J で既に証明済＝
    **主定理が未 import だった配線漏れ**。これを import して消滅）。
    🚨**配線漏れの教訓**: `audit_8_7_termination.py` は `8.7-termination.lean` の import 閉包
    しか歩かないので、閉包外の緑ディスチャージャ（`8.7-descend-last2`／
    `8.7-Trans-preserves-OT-props`）を「未証明葉」と誤カウントしていた＝**残差の一部は
    数学でなく import 追加だけで消える**。統合時は緑ファイルが閉包内かを必ず確認。
    **残り 9 葉**（`audit` 出力、うち `FseqDesc_m_7_3_Trans_leftmost_2` は `m_7_3_Trans_leftmost_2_dropin`
    で配線済＝名前マッチ誤検出＝実質 8）: ①`CondI_masterCF`（r28-STEPCORE ~2000 行。
    Wave L で `scx_stepA`/`scx_stepB` を `8.1-condI-masterCF` に bank、残=chunk5 組立）
    ②`CondII_masterCF`（残=`CondII_TailvalAll_ST`＝tvx/cdx/ljx/wnx/hqx/dkax 連鎖 ~3200 行。
    Wave L で tvx 境界＋`tvx_finRc` を `8.3-condII-masterCF-port` に bank、残=R3LE 系）
    ③`Exch84_condIIIIV_pkg`（§8.4 巨大 corpus ~72k 行。`8.4-exch84-producer` が slicepkg
    ＝oi5 出力形に還元済で d13x 層を回避、次 wave の的が縮小）④⑤`CondVI_scbdec_{adm,nadm}_forms_v6`
    （§8.4 L-tower infra。`8.6-condVI-exch-nadm` agent が blocker を精密地図化: 未移植
    `Trans_funpow_IncrFirst`/`a1_Red_funpow_IncrFirst` が壁。この L-tower は §8.5
    `ExchVres_adm_M_tower` とも共有＝閉じれば複数葉が同時解禁）⑥⑦⑧`OTdisp_{OTint,OTpred,OTmulti}`
    （OT transport pillar。**`OTpred` は最も近い**: `od4_OTpred_final`(scratch:874) が
    3 除外仮定なしで強く証明、`8.7-otdisp-OTpred` が Brick A=`od4R_op` 逆保存 ~380 行を bank 済。
    `OTmulti` は `OTint` に依存、`OTint` は transport 層 ~1000 occ で最重量）。
  - 🎉 **Wave M（2026-07-18、Opus 8 並列）で `CondI_masterCF` を無条件クローズ＝残差 9 → 8 葉**。
    主定理は緑・公理クリーンのまま。`8.1-condI-masterCF-chunk5` が `scx_condI_j0pos_masterCF`
    （r28-STEPCORE の chunk-5 組立）を Wave L bank 済の `scx_stepA`/`scx_stepB`＋c1_around 群
    から glue（新規数学なし、house pattern）。termination の `condI` フィールドを削除し
    `H.condI` を `scx_condI_j0pos_masterCF` に置換（OT 柱 exchI/condI_j0z＋降下柱 exchI を直接供給）。
    **同時に大量の brick を bank**（緑・未配線、次 wave 用）:
    ①`TV_R3LE`（CondII tailval の 6 残差の 1 つを無条件クローズ。`8.3-condII-R3LE`。
    残 5=TrunkLeg/BoundaryLeg/NotLdjLeg/LDJB/Dichotomy）
    ②OTpred **Brick B** 完全クローズ（`od4_scbext_R`＋`otx2_peel`/`otx2_top_shape`、`8.7-otpred-brickB`）
    ③OTpred **Brick C0** 完全クローズ（最重量 `od4_condVI_nadm_c1`＋engine `wnx_run_entries` 再構築、
    `8.7-otpred-brickC0`）④OTpred Brick D 部分（`od4_master_R_of_site`＝Brick C modulo。`8.7-otpred-brickD`）
    ⑤condVI L-tower **fact(a)** クローズ（`s84c1_marked_L`/`s84c1_adm_L_mstar`/`s84c1_le0_L_mstar`、
    condVI regime の w=1 collapse で plain oper 化。`8.6-condVI-Ltower-facta`）
    ⑥**funpow IncrFirst プリミティブ 2 本**（`Trans_funpow_IncrFirst`/`a1_Red_funpow_IncrFirst`、
    複数葉の共通 blocker。`8.6-Trans-Red-funpow-IncrFirst`）
    ⑦s84x 語彙定義＋RUN leg 基礎（`8.4-s84x-vocab-run`。ltJ 仮定不整合の調査結果も needs に）。
    **残り 8 葉**（`FseqDesc_m_7_3_Trans_leftmost_2` は dropin 配線済の名前マッチ誤検出＝実質 7）:
    `CondII_masterCF`（残 5 TV brick）／`Exch84_condIIIIV_pkg`（s84x 語彙 bank 済、次=RUN/REGS/base/mnform）／
    `CondVI_scbdec_{adm,nadm}_forms_v6`（fact(a)＋IncrFirst 済、残=fact(b)(c)(d)組立）／
    `OTdisp_{OTint,OTpred,OTmulti}`（**OTpred が最接近**: Brick A/B/C0 済、残=Brick C 組立
    ＝od4_site_c2 の残 5 easy 枝＋`od4_master_R`＋final glue `od4_OTpred_final`）。
    parent promotion 実施: `trans_surgery_localized_v6p`→public（OTpred Brick D 用）。
    R3LE agent が要求した追加 promotion 候補は memo 末尾/コミットに記録（全て private _r3 で自己完結済）。
  - 🎉🎉 **Wave N（2026-07-18、Opus 8 並列）で 2 葉クローズ＝残差 8 → 6**。
    主定理は緑・公理クリーンのまま（full build 3160 jobs）。
    **① `OTdisp_OTpred` 無条件クローズ**（`8.7-otpred-close`）: Brick A/B/C0/D＋promotion 済
    `condVI_transC2_v6p`/`condVI_transC1_adm_v6p` を組んで `od4_site_c2`（Brick C, transC2 6 枝
    dispatch）→`od4_master_R`→`od4_OTpred_mono`→multi leg `opx_OTpred_multi_of_mono`→
    `OTdisp_OTpred_holds`。termination の `otPred` フィールド削除。
    **② `CondVI_scbdec_adm_forms_v6` 無条件クローズ**（`8.6-condVI-adm-forms`）: adm L-tower
    `CondVIres_adm_Ltower_v6p` を移植（`c6zx_condVI_baseL_free` 経由、nadm より簡単）。
    termination の `condVIadmTower` フィールド削除、`condVIAdmTowerScb_of_scbforms_v6` で供給。
    **bank（緑・未クローズ）**: ③`TV_TrunkLeg`（CondII の 6 TV brick の 1 つ、`8.3-condII-TrunkLeg`。
    `wnx_trunk_diagSeq`＝reduced+TrMax=末尾⟹diagSeq、`c2sx_slice_jm1_c1` も）
    ④`e1x_ineq_nonanc`＋`e1x_e1ge_uncond`（Exch84 RUN leg 完成、`8.4-exch84-e1ge-run`）
    ⑤condVI nadm の fact(b)`c6nx_Mark_L_mstar_condVI`＋fact(d)`c6nx_condVI_uv`
    （`8.6-condVI-nadm-forms`。**KEY**: condVI+reduced で d0=1 なので IncrFirst 不要、const2nd_Trans で直接）
    ⑥OTint transport 基盤 `d4vx_ins`/`d4vx_core`/`d4vx_ins_flat`/`b1x_setle`/`b1x_triG`
    （`8.7-otint-transport-prims`）⑦CondII NotLdjLeg/BoundaryLeg 部分 bank。
    **残り 6 葉**（`FseqDesc_m_7_3_Trans_leftmost_2` は誤検出＝実質 5）: `CondII_masterCF`
    （残 TV brick=NotLdjLeg/BoundaryLeg/LDJB/Dichotomy）／`CondVIres_nadm_Ltower_v6p`
    （nadm 唯一の残差。**ROOT BLOCKER=`m_7_3_Mark_rightmost2` 未移植**＝fact(c)`c6nx_t2eq` が
    詰まる。加えて assembly `m_8_4_oper_props_5`(~203L) が要る）／`Exch84_condIIIIV_pkg`
    （RUN 済、残=REGS/base/mnform）／`OTdisp_OTint`（transport 基盤 bank 済、残=`oix_transport`
    /`oix_transportD` 本体）／`OTdisp_OTmulti`（OTint 依存）。
    promotion 実施済: `condVI_transC2_v6p`/`condVI_transC1_adm_v6p`→public（5299780）。
    **次 wave の最優先候補**: m_7_3_Mark_rightmost2 移植（nadm 解禁）＋ CondII の残 TV brick。
  - **Wave O（2026-07-18、Opus 8 並列、全 8 file 緑 bank）— 葉クローズ 0 だが内部残差を大幅削減**:
    ①`m_7_3_Mark_rightmost2` 完全クローズ（`7.3-Mark-rightmost2`）——**実体は既移植
    `Mark_transJm1_eq_transC2`（7.4-Mark-Trans-repr:231）の名前/仮定形ギャップだった**
    （[[asset-blindness]] の実例。「ROOT BLOCKER 未移植」は誤記録）。nadm fact(c) 解禁。
    ②`m_8_4_oper_props_5` engine 緑（`8.4-oper-props5`。`Oper5Support` 1 Prop（10 葉）modulo。
    残=s84c1_* 値クラスタ wip:52660–54005 ~1350L。s84x_L/s84x_Lp 語彙定義もここ）
    ③**TV_Dichotomy 無条件クローズ**（`8.3-condII-Dichotomy`、`TV_Dichotomy_holds`、
    cdx_d_le_joints wip:90230 の 1:1）→ CondII TV 残=NotLdj/Boundary/LDJB の 3
    ④TV_NotLdjLeg→`TV_NotLdjReg` 1 本へ還元（`8.3-condII-NotLdjLeg2`、`tv_notldjleg_of_reg`。
    Dichotomy を private 複製で自己完結、TrunkLeg_holds 再利用）
    ⑤TV_BoundaryLeg→`TvxBoundaryData` 1 本へ還元（`8.3-condII-BoundaryLeg2`、
    `tv_boundaryleg_of_data`。portable 前座=wnx_seg_transport(80767)/repr_entry1_shift_gen
    (12828、8.1-part4-trans:357 に private 双子)/tvx_d_lt_TrMax(110442)/c2sx_reach(87666)(1)(2)）
    ⑥TV_LDJB→5 readouts へ還元（`8.3-condII-LDJB`、`TV_LDJB_of_readouts`＝RN_ldj_pj/
    RN_a0_trmax/RN_a0_lt_trmax(114847 最重量)/TVX_pos1ldj/TVX_dstrict。TV_R3LE_holds 再利用）
    ⑦Exch84 REGS leg（`8.4-exch84-regs`、`regS_holds`＝mcx_regS(94021) drop-in。
    `Regs_jm3Marked`/`Regs_jm2_lt_transJ0`（要 parent_max 新規移植）/`Regs_MCOND`(93796)
    の 3 Prop modulo。**cfbx_reg/cfbx_j1p は VEReg/VEj1p（8.2-condV-VE-base）として既存**。
    REGSP/base/mnform 未着手）
    ⑧OTint transport 心臓部（`8.7-otint-transport`、oix_transport/oix_transportD 定義
    ＋otx2_/otx3_ 全 assembly＋btWeight 帰納 otx3_core）。`oix_transport_holds` は 4 Prop
    modulo — **うち 3 本（OixSandwichPrefix/OixSandwichDpt/OixGControl）は
    7.1-buchholz-fseq-closed の private 双子（sandwich_prefix_bc:334/sandwich_Dprin_bc:379/
    G_control_bc:254）＝promotion だけで落ちる**。残 1=OixAlign3（otx2_align3 wip:114296、
    flatinj toolkit ~200L）。OTdisp_OTint 本体はさらに下流の 4 hasParent legs
    （8.7-otdisp-OTint 宣言済、oix_OTint_condV_adm wip:111599 等）。
    🚨 **構造的発見: CondII の NotLdj/Boundary 両葉の深部が §8.2 VE body
    （vcx_VE_all/vg2x_VE34、~14k 行未移植）に合流**＝VE キャンペーンが CondII 完了の律速。
    promotion 候補: condII_reach_r3（8.3-condII-R3LE:150 private、LDJB が複製中）／
    7.1 の 3 twins／adm_row1_ancestry 系（§5/§8.1 privates、Regs_jm3Marked 用）。
    **次 wave 候補**: ①7.1 promotion→Oix 3 本 discharge＋OixAlign3（oix uncond 化）
    ②nadm 組立（fact(c) c6nx_t2eq＋c6zx_L_tower(72166)/c6nx_condVI_exch_nadm_uncond(76705)
    ＋Oper5Support の s84c1 群）③LDJB readouts ④VE campaign 始動（a0x_base_VE から）。
    ⚠️**audit の過少計上バグ（2026-07-18 発見）**: `audit_8_7_termination.py` は
    `ExchV_nf3x ← nf3x_holds`・`ExchV_scbdec_adm_forms ← adm_forms_holds` を CLOSED 扱い
    するが、**両 discharger は仮定付き**（`ExchVres_{adm,nadm}_M_tower` を要求）。
    真の残差 = `TerminationResidual` の**フィールド一覧**（`exchVresAdmTowers`/`exchVnf3x`
    を含む）で数えること。audit の「6 葉」は exchV の塔 2 本を見落とした値。
    この塔は §8.4 L-tower（`m_8_4_oper_props_5`＋`s84x_L` 帰納＝Oper5Support/nadm 組立と
    同一 campaign）が供給予定。
