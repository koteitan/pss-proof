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

- ✅ **§6 ペア数列の基本性質**[r61] — 全 8 節 ✅（詳細注釈は畳み込みで削除、
  各節の勝ち筋・罠は §3/§4/§4.5 と git 履歴 d96fb0b 以前の本ファイルを参照）。Isa: `m_6_*`。

- ✅ **§7 Buchholz の表記系への翻訳**[r37] — 全 4 節＋[Buc1] 3.2a/3.2 ✅、`7.1-buchholz-wf` も
  自前証明済（仮定 0）。詳細は git 履歴参照。Isa: `m_7_*`。

- **§8 停止性** — Isa: `m_8_*` ＋ `layerC`。**停止性 = 「基本列の降下性」＋「`OT` 所属」の 2 本柱**。
  - ✅ **§8.2 強単項性**[r49] — 全 7 項目 ✅（詳細注釈は畳み込みで削除、git 履歴参照。condIIIV 終切片=Wave AH〜AV+配線 `condIIIVterminalSlice_holds`、condV 終切片=codex close）
  - ✅ **§8.3 条件(II)の下での展開規則**[r22] — 全 4 項目 ✅（kind0 3 本＋p ファイル `8.3-Trans-fseq-condII`=Wave AX 新設。結論(4) 逐語・(1)-(3) は Isabelle p 文と同じ modelling note で内部局所量として deferred。A36 は取り下げ済で原文のまま）
  - ✅ **§8.6 条件(VI)の下での展開規則**[r11] — 全 4 項目 ✅（`p_8_6_Trans_fseq_condVI_uncond` = 8.6-Trans-fseq-condVI-close、3 named Props を公開供給で落とした無条件 twin）
  - ✅ **§8.5 条件(V)の下での展開規則**[r15] — 全 5 項目 ✅（condV 交換則 `_vc` twins／scb分解 part(5)=A29 訂正形の無条件＋原文形の機械反証／基本列 scb 分解=非許容枝 `p_8_5_fseq_scb_decomp_nadm_uncond`（pss_paper 2128 は DEFERRED、Lean は statable 分を転記＝parity 超過。許容枝・一意性節は原文どおり 未転記で Isabelle parity）。旧詳細は git 履歴）
  - ✅ `8.4-oper-basic`[r1] — Wave AY 新設。part(1) 両枝/part(2)簡約/part(5)full（A31 guard）を既存資産へ委譲＋s84c1 port。parts(2-mono)(3)(4) は pss_paper:1955 DEFERRED と同一 scope＝未転記（header に明記）。名前 crossover 回避（`oper_rule_basic_*`）
  - ✅ `8.4-scb-decompositions`[r1] — Wave AY 新設、公開 7 本（dec1 engine で存在残差 も討伐）。(4)(5)閉形式・六つ組・一意性節は pss_paper:1968-1999 DEFERRED と同一 scope＝未転記（header に明記）
  - 🚨 `8.7-Pred-oper0`[r4] — 一般形は真（806/806、旧偽判定は反転済み）。 `8.7-Pred-oper0-general` が一般文 `PredOper0_pg` を単一残差 `TransPredScbInsert_pg`（Trans/Trans∘Pred の scb 文脈共有＝原文 6018-6058 の本体、 Isabelle 側も未証明）へ無条件還元＋具体 2 系列で end-to-end 実証。 零化側は `trailing_principal_annihilable` が既在（asset-blindness 13 回目）
  - 🚨 `8.4-fseq-basic` — part(1)[r1]/part(3)=`8.4-fseq-basic-close`[r1] 無条件。 part(2)=`8.4-fseq-basic-part2` が operB 側 leg (A) を無条件討伐し、残差を `L6TransSliceClosed_p2`（L6 slice engine=m_8_4_various_scb_IIIIV_from_slice wip:60034 の port、producer 座標）1 本へ尖鋭化
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
  - ✅ `8.7-const00-Trans` — `Trans (replicate (j₁+1) (u,u)) = multBT (D_u 0) (if u=0 then j₁
    else j₁+1)`。Isa `p_8_7_const00_Trans` と逐語一致を親が確認。定数列は親子辺ゼロ
    → RedCondA/B → RTPS、`Pcut = j₁`、j₁ 帰納で multi 分岐が 1 列ずつ `D_u 0` を積む
    （Isa: `m_8_7_cnst_Trans`, pss_wip.thy 16005）。rc=0・sorry 0・axioms 正常・
    python audit 81 例 0 反例（`python/const00_trans_audit.py`）。[r1]
  - ✅ `8.7-OT-tail-annihilable` — **Wave G で本体完成後、`OT_B_wf` も閉じて無条件化済み**。[r1]
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
  - ✅ `8.7-OT-examples` — OT_B 基本例 4 本（`OT_examples_1..4`）。**親が main loop で直接証明**
    （workflow 全滅のため）。(1)(2)=gather の if 分岐を明示分解、(3)=multBT→replicate 帰納＋
    descP/isOT/dfree の replicate 補題、(4)=塔の G 集合特徴付け＋狭義単調の帰納
    （Isa `m_8_7_OT_examples` の構造をそのまま移植）。rc=0・sorry 0・axioms 正常・#guard 5 本。[r1]
  - ✅ `8.4-rightmost-replace-Trans`[r8] — Wave R で A30/A31 の反例を機械証明＋訂正形を
    green-modulo Prop `Rightmost84ReplaceCorrected` として露出（原文 DEFERRED、8.5-scb-dec 方式）。
    残=訂正形の universal 証明。訂正 **A30**（scb 分解が偽。長さ勘定で決まる）
    ＋ **A31**（補題(5-3) のガード欠落）
  - ✅ `8.4-rightmost-nonadm-ancestor` — **完了（Wave D, r1）**。p 文 =
    pss_paper:1931 と逐語一致（訂正無し。A30/A31 は §8.4 の別命題で無関係を確認）。
    Isa: `m_8_4_rightmost_nonadm_ancestor`（layerB:40628）。rc=0・sorry 0・
    axioms 正常。Isabelle が `m_8_2_standard_slice_Red_strongmono` で取る
    `monoT (Red N)` は Lean では `ancestor_slice_Red_IncrFirst` が直接供給
    （＝`hmono` 仮定が不要になったが、p 文忠実性のため引数は保持）。
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
  - ✅ `8.4-Trans-fseq-condIII-IV`[r18] — **Wave F で green-modulo 完成（緑）**。
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
  - ✅ `8.7-Trans-preserves-OT`[r38] — **無条件クローズ（2026-07-21 Wave AW）**: `Trans_STPS_OT_B`（8.7-termination）が仮定 0。OT 柱 38 ファイルの合流。（旧記録: Wave F で green-modulo 完成（緑、12 Props）。）
    blueprint `y5_Trans_OT_B` は census 塔への一行だったので追跡し、実体
    **`otx_Trans_preserves_OT_dispatch`（layerB:85710）**＝ST_PS 帰納を全分岐移植
    （base＋11 分岐: Lng≤1／N[n]=Pred N の 4 枝／N[n]≠Pred N の condI–VI＋multiT）。
    🚨**構造的発見: OT 柱に必要なのは {OTint, OTpred, OTmulti, exchI, exchII} だけで
    `LbaseU` は descent 専用＝2 本柱は分離可能**（Isabelle は census で同時に証明して
    いるが、分ける必要はない）。`Trans_preserves_OT : ∀ M, STPS M → Trans M ∈ OT_B` は
    descend の `FseqDesc_Trans_preserves_OT` **より強い**（monoT も Lng 条件も不要）。
    8.6-condVI の `TransPreservesOT` Prop も同形で同時に討てる。
  - `8.5-*` — **最難所**。Isa の keystone は
    `bpHeadT(Trans(slice@B)) = C(bpHeadT(Trans slice))`（depth-shift self-similar）。
    13 個の死路が `isabelle/memo.md` に列挙してある。**着手前に必ず読め。**
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
  - ✅ `8.7-fseq-descend`[r4] — **無条件クローズ（2026-07-21）**: `Trans_fseq_descend`（8.7-termination）が仮定 0。（旧記録: Wave E で green-modulo 完成（緑、sorry 0、853 行）。）
    `m_8_7_fseq_descend_dispatcher`（Isa layerB:52353）＋`f7x_fseq_descend_mono`
    （52051）を 1:1 移植し、**p 文 `p_8_7_fseq_descend`（pss_paper:2253）と
    `p_8_3_TransCondII_oper_descend` の両方を出力**（＝⛔ だった 8.3 項目も同時に解禁）。
    **露出した named Prop は 7 交換則系の 16 本のみ**（FseqDesc_Trans_preserves_OT／
    exchI/II/III-IV/V/VI 等）。dispatcher の場合分け・mono 6 分岐・multi 枝・
    条件(I)/(VI) の `Lng M = 2` 枝（oper 直接計算＋`const00_Trans`/`two_column_Trans`）
    は**自前証明**＝Isabelle の補題 2 本を回避。
    **停止性への幹線が Lean でもチェックリスト化された**: 残りは 16 Props の討伐。
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
  - ✅ `8.7-termination`[r1] ★ — 🎉🎉 **無条件達成（2026-07-21、Wave AW 統合）**: `p_8_7_termination` 仮定 0・sorry 0・axioms = propext/Classical.choice/Quot.sound。`TerminationResidual` 構造ごと削除、audit VERDICT=0。（旧記録: Wave J で組み上がった（緑、公開 6 本）＝残差は 27 本ちょうど。）
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
  - 🎉🎉 **Wave P（2026-07-18、Opus 8 並列、全 8 file 緑）で残差 6 → 5 葉（真のフィールド 7 → 6）**。
    主定理は緑・公理クリーンのまま（full build 3176 jobs、termination 再配線済）。
    **① `CondVIres_nadm_Ltower_v6p` 無条件クローズ**（`8.6-condVI-nadm-close`、
    `CondVIres_nadm_Ltower_holds_nc`）: adm 兄弟の w=1-collapse ルートを踏襲し
    **`m_8_4_oper_props_5` 非依存**で閉じた。fact(c)=`c6nx_t2eq` は `m_7_3_Mark_rightmost2`
    を Pred M に適用（corner Lng=3 は `two_column_Mark`）。連鎖で `CondVIExchNadm`／
    `CondVI_scbdec_nadm_forms_v6` が落ち、termination の `condVInadm` フィールド削除。
    **② `oix_transport` 無条件化**（`8.7-otint-uncond`、`oix_transport_uncond`）:
    3 twins（promotion 済）＋ `OixAlign3` 移植（otx2_peel/top_shape は 8.7-otpred-brickB
    の公開分を再利用、join3/align3 に拡張）。b1x_triG↔triGBC は defeq 確認済。
    **③ Exch84 大進撃**: REGS の 3 残差全滅（`Regs_jm3Marked_holds`/`Regs_MCOND_holds`
    =`8.4-exch84-mcond`、`regs_jm2_lt_transJ0_holds`=`8.4-parent-max`。
    **⚠️memo 旧記録の訂正: parent_max の新規移植は不要だった**——公開済み
    `nextR0_largest_below`+`ancestor_basic_1` で値レベル閉じ）＝`regS_holds` 無条件化。
    さらに `Exch84_condIIIIV_pkg_holds : slicepkg → pkg`（`8.4-exch84-regsp`）で
    termination フィールドを producer→**slicepkg** に細化。Regsp/Base0/Base1p/Mnform の
    忠実 Prop 定義と membership scaffolding（`Regsp_of_disj_sharp`）も bank。
    **④ Oper5Support 7/10 クローズ**（`8.4-oper5-support`、`oper5Support_holds` は
    `Oper5Residual`（§7.4-Mark 依存の 3 葉: marked_L/Mark_L_mstar/interior regime）modulo。
    oper_succ_append 恒等式 = M[m+1]=L_m++tail が新基盤）
    **⑤ LDJB readouts 3/5**: `RN_ldj_pj_holds`+`TVX_pos1ldj_holds`（`8.3-condII-LDJB-readouts`）
    ＋`TVX_dstrict_ldjb_holds`（⑥内）→ `TV_LDJB` 残= RN_a0_trmax/RN_a0_lt_trmax の 2 本
    （roadmap は readouts ファイルの needs に詳細）
    **⑥ VE 周縁 7 本公開**（`8.2-condV-VE-wnx`）: `repr_entry1_shift_gen`（public 化）／
    `wnx_seg_transport_W1/W2/W3`／`c2sx_reach_leab/leam`／`TVX_dstrict_ldjb_holds`。
    wnx_run_entries は 8.7-otpred-brickC0 に既公開（重複回避）。
    **残 5 葉（実質 4）**: `CondII_masterCF`（TV 残= NotLdjReg[VE 依存]/TvxBoundaryData
    [VE 依存]/LDJB 2 readouts）／`Exch84_condIIIIV_slicepkg`（disj_sharp/Base0/Base1p/
    Mnform/oi5 組立）／`OTdisp_OTint`（**oix uncond 済→残= 8.7-otdisp-OTint の 4 hasParent
    legs**: oix_OTint_condV_adm wip:111599/condV_nadm 112041/oi8_condIII scratch:3716/
    condIV 3774）／`OTdisp_OTmulti`（OTint 待ち）＋ audit 見落とし分 §8.5 塔
    `ExchVres_adm_M_tower`/`ExchV_nf3x`（`ExchV_M_tower` 1 本に還元済（props2）、
    実体= m_8_4_oper_props_5＋s84x_L 帰納＝④の campaign と同根）。
  - 🎉 **Wave Q（2026-07-18、並走していた別セッションが起動→PC 再起動で中断→本セッションが
    回収統合）— 残差フィールド 6 → 5、OTint 陥落**。中断死した wave の遺留 8 ファイルは
    **全て緑**（rc=0・sorry 0・公理クリーン）で全回収:
    ①`8.7-otdisp-OTint-condV`: condV 両 leg（`OTint_hp_condV_{adm,nadm}_holds`、
    条件(V)塔残差から）②`8.7-otdisp-OTint-condIIIIV`: condIII/IV leg
    （slicepkg＋新残差 `OTintIIIIV_transportData`=Isabelle OTA1_ltJ/SETLE1_ltJ 対）
    ③`8.5-exchV-M-tower`: `exchV_M_tower_of_residual`（残差 `ExchVMTowerResidual`
    ＝L 塔 7.4-Mark fact 束、Oper5Residual と同族）④`8.2-condV-VE-base2`+`8.2-condV-VE-step`:
    **VE campaign の BASE/STEP/RPERS**＋`vsx_VE_all_modResidual`（VEj1eq/RPj1eq 残差 modulo）
    ⑤`8.3-condII-LDJB-a0trmax`: `RN_a0_trmax_holds`（TV_LDJB 残=RN_a0_lt_trmax のみ）
    ⑥`8.4-exch84-base0`: `Base0_condIIIIV_holds` ⑦`8.4-oper5-residual`: torso
    （private 群のみ・書きかけ。継続 agent はこのファイルを拡張せよ）。
    **termination 配線替え（本セッション）**: `otInt` フィールド削除（4 legs 組立
    `OTdisp_OTint_of_legs`＋`otInt_term` で導出）、`exchVresAdmTowers`/`exchVnf3x` の
    2 フィールドを `exchVMres : ExchVMTowerResidual` 1 本に置換。
    **現フィールド 5**: `otMulti`／`otIIIIVdata`／`condII`／`exch84slicepkg`／`exchVMres`。
    audit は 4 葉表示（exchV 過少計上バグ込み、下記）。
  - **VE34 continue（condIIIVts、`8.2-condIIIV-ve-next`、全緑・公理クリーン）— 補正 run-peel 持続を
    Pred-free 残差一本に尖鋭化＋LIVE 帰納法**: ve-continue の Pred レベル残差
    `RunPeelGuardJointBase_vc2` を、`Pred` を含まない純 N レベル残差 **`RunSqueeze_vn`**
    ＝{`bfx_run_prev`(2)ガード `entry N 1 (Lng-2) < entry N 0 (Lng-2)` ／ `bfx_JEQ`
    `Joints N!(Br.len-2)=Joints N!(Br.len-1)` ／ BASE 単一列幾何 `FirstNodes N!(Br.len-2)=Lng-2`}
    に無条件で還元（`RunPeelGuardJointBase_of_squeeze_vn`）。橋渡しは機械的 `Pred` 転送
    （`FirstNodes/Joints_Pred_core`＋`entry_Pred`）＋枝数減少 `bfx_BrLen_Pred_base`
    （`Br_Pred_core_nontrunk`＋`wf21_Br_eq_seg` で最終枝長=1 を読む＝`BrLen_Pred_base_vn`）のみ。
    キャップストーン `RunPeelPreservedD_of_squeeze_vn`（補正 run-peel 持続を `RunSqueeze_vn`
    一本 modulo）。さらに **死んだ `VE3BaseDeep_of_residuals`（偽の `RunPeelPreserved_bd` 依存）を
    補正体制 `VE34Reg4D` 上の LIVE 版 `VE3BaseDeepD_of_residuals` に置換**（leaf 残差
    `{VE3RunBase_bd, VE3RunStep_bd}`＋`VE3_minbase_vb` は素 `VE34Reg4` で足りる）→
    `VE3BaseDeepD_of_squeeze`（VE3goal を `RunSqueeze_vn`＋leaf 2 本から）／`VE4BaseDeepD`
    （素 `VE4BaseDeep` の弱化）。**残**={`RunSqueeze_vn`（=descending squeeze＋nextrel0 valley
    squeeze＋単一列幾何の値証明）, `VE3RunBase_bd`/`VE3RunStep_bd`/`PIN_bd`/`TSPIN_bd`（§7.4 surgery）,
    field-level 再配線（DTPS→`VE34Reg4D`で `VE3/4BaseDeepD` を場に接続、dead `condIIIVterminalSlice_of_runpeel` 退役）}。
  - 🎯 **Wave BA（2026-07-21、Opus 2、全緑）— 残 2 葉の縮退が深部フロンティアに到達（wave 一旦停止）**:
    ①L6: op1pow 橋を完全 port（y3l_op1pow_take: op1 反復=take）。残る底読出し 3 葉は
    `L6BaseReadoutsResidual` に束ね、**cfbx_reg 正則性（REGS/REGSP 未 port、
    MnformResidual と同じ壁。MnformBottomResidual は偽=Wave Y）が真のブロッカー**と確定
    （`8.4-l6-base-readouts`。`oper_basic_part2_br` で part(2) は本残差 1 本 modulo）
    ②Pred-oper0: **t1=0 隅 完全クローズ**（`PredOper0_t1zero_residual_holds_pc`、
    Isabelle-sorry の片方撃破。D_0(D_j1 0)→D_0 0→0 の 2 段）。condII/IV 隅は
    数値モデル訂正（2 段でなく kind-1 カスケード、k≤13）の上で唯一残差
    `PredOper0_scbCtx_residual_pc` に還元＝**原文 p_8_7_OT_tail_annihilable の scb 形
    ＝Isabelle 自身も sorry の一般 scb 尾部零化**（trailing_principal_annihilable の
    ~200 行一般化＋condIV RTPS 閉形式が要る）（`8.7-pred-oper0-corners`）。
    **状態: 主定理無条件・ツリーは 2 葉（part(2)/Pred-oper0）のみ open、どちらも
    多 wave 級の新キャンペーン（cfbx_reg port／beyond-Isabelle 零化）。weekly 90% 到達
    のため wave 停止・保守運用へ。**
  - 🎯 **Wave AZ（2026-07-21、Opus 2、全緑）— 最終 2 葉の本体攻略**:
    ①L6: **塔帰納 `l6_tower_l6` port 完了**（oper_rule_basic_part5 を単段に、
    scb_unique_decomp_unconditional で穴 pin、condV 塔テンプレ流用）＋operB 側 flat。
    残差は `L6TowerResidual`＝底読出し 4 葉 {op1pow 橋 (y3l_L_eq_op1pow)/ub_eq/
    base depth-1 (base5、twins=LEAF3・hL1flat)/lpv (s84d_dec*)} に縮退。数値 164/164
    （`8.4-l6-slice-close`）
    ②Pred-oper0: **I/III/V 枝討伐（677/806）**——master key は `Trans_c1_c2_decomp`
    （条件非依存の共有 (s,b)）＋transC2Core 第1枝。一般定理は残差 2 本
    {`PredOper0_nestedCond_residual_psi`（condII/IV の 2 段入れ子零化＝原文 6018-6058
    の核、Isabelle も sorry。単一挿入述語では表現不能を flat 不一致で確証）,
    `PredOper0_t1zero_residual_psi`（t1=0 隅、top-level 零化要）} へ
    （`8.7-pred-scb-insert`）。
  - 🎯 **Wave AY（2026-07-21、Opus 6、全緑）— 最終カバレッジ掃討: 4 討伐＋2 尖鋭化、残 2 葉**:
    ①`8.4-oper-basic` ✅（新設、crossover 回避。part1 両枝/2r/5-A31。3/4 は pss_paper DEFERRED parity）
    ②`8.4-scb-decompositions` ✅（新設 7 本、dec1 engine で存在残差討伐。deferred 節は header 明記）
    ③`8.5-scb-decompositions` ✅（既存ファイル発見＝asset-blindness、A29 訂正形を無条件化
    `scbdec_condV_part5_corrected_uncond`＋原文形 n=1 偽の機械反証維持）
    ④`8.5-fseq-scb-decomposition` ✅（新設。nadm 枝 3 分解、親が nf3x 供給で
    `_uncond` 化。⚠️原文の証人 t'₀ は自身の (5)' と矛盾（指数 n+2 vs n+1）＝header 記録、
    機械化塔 e5x_bodyM の t'=t₂ が正）→ **§8.5[r15] 畳み**
    ⑤part(2): operB 側 leg (A) 無条件討伐、残差を `L6TransSliceClosed_p2` 1 本へ
    ⑥`8.7-Pred-oper0`: 一般文を単一残差 `TransPredScbInsert_pg` へ無条件還元＋
    数値 806/806＋具体 2 系列 end-to-end。零化側は既存 `trailing_principal_annihilable`
    で完結（asset-blindness 13 回目）。
    **残り open = {`L6TransSliceClosed_p2`, `TransPredScbInsert_pg`} の 2 葉のみ。**
  - 🎯 **Wave AX（2026-07-21、Opus 4、全緑）— 原文カバレッジ 4 連戦: 3 完落＋1 分割**:
    ①`8.5-Trans-fseq-condV` ✅（instantiation close、公開 5 定理の無条件 twin）
    ②`8.3-Trans-fseq-condII` ✅（p ファイル新設、Trans_fseq_descend の系として 1 行証明。
    A36 取り下げ確認）③`8.6-Trans-fseq-condVI` ✅（「未移植ブリック 3 本」は stale＝
    全て既存公開定理で供給可、`p_8_6_Trans_fseq_condVI_uncond`）→ **§8.3[r22]/§8.6[r11]
    全 ✅ で畳み**。④`8.4-fseq-basic`: part(3) 完全 port（y3h engine、scbext_reflect＋
    core_TB_of_flat。親が `oper_basic_part3_uncond` 追記で無条件化）、part(2) は緑 modulo
    `Oper84BasicPart2Residual`（L6 slice 閉形式、Isabelle y3i）＝唯一の残差。
    ⚠️agent が board を勝手に編集し part(2) 残差付きで ✅ 宣言→親が分割修正
    （🚨行 inline ✅ 禁止規則）。**残り open = 8.4 part(2)/oper-basic/scb-decomp×2(8.4,8.5)/
    8.5-fseq-scb-decomp/8.7-Pred-oper0 の 6 つ＝全て停止性に不要のカバレッジ**。
  - 🎉🎉🎉 **Wave AW＋最終統合（2026-07-21）— `p_8_7_termination` 無条件化達成（Lean 移植の主目標完遂）**:
    ①condII interior 脚 `OTmulti_interior_condII_on` を**独立 2 route が同時完全証明**
    （`8.7-otmulti-condII-close`=Route A 採用・`8.7-otmulti-condII-blueprint`=Route B 保険。
    骨子一致: CondII_masterCF 無条件化→FseqDesc_exchII の**等式**→OT_B operB 閉包＋
    buchholz_fseq_lt。Lng=2 隅は lastParent=parent M 0 1=0（hasParent 不要の新補題）＋
    `adm_zero` で transCondII=false＝空虚を機械証明）
    ②親統合: `otMultiIntCond_term`（narrow 還元＋otInt_term＋exchIII/IV/V 脚＋①）で
    最終フィールド陥落 → **`TerminationResidual` 構造ごと削除、全 `_term` helper と
    公開 6 定理（`Trans_STPS_OT_B`/`Trans_fseq_descend`/`PSS_wf`/`PSS_acc`/
    `p_8_7_termination`/`STPS_prod_pos_subset_Fdom`）が仮定 0 に**。
    build 3301 jobs 緑・checker rc=0・axioms = propext/Classical.choice/Quot.sound・
    audit VERDICT=0。板: `8.7-termination`[r1]/`8.7-fseq-descend`[r4]/
    `8.7-Trans-preserves-OT`[r38] ✅、8.3 の ⛔ 解消。
    **残り＝原文カバレッジのみ**: `8.3-Trans-fseq-condII`（p ファイル新規作成、
    exchII 等式は既に無条件）/`8.5-Trans-fseq-condV`（instantiation close、供給 6 Props
    全て無条件化済み）/`8.4-fseq-basic`(2)(3)/`8.4-oper-basic`/`8.4-scb-decompositions`/
    `8.5-scb-decompositions`/`8.5-fseq-scb-decomposition`/`8.6-Trans-fseq-condVI`/
    `8.7-Pred-oper0`（一般形）。停止性連鎖には全て不要。
  - 🎉 **Wave AV＋最終配線（2026-07-21、Opus 3＋親、全緑）— `condIIIVts` field 陥落・§8.2 condII/IV 命題 ✅**:
    ①スライス自然性 `tsx_c1_eq_sn`/`tsx_c2_eq_sn` 完全 port（`8.2-condIIIV-slice-nat`。
    Mark/Trans の fuel head を unfold しない calc+congrArg 流儀が鍵）
    ②`tspinGeomIH_of_slicenat_gi`＋`tspinAssemblyIH_of_slicenat_gi`（`8.2-condIIIV-geomih`。
    tsx_t1_identified port。tsx_jp_geom 系は c1/c2_eq の内部でのみ必要と判明＝不要）
    ③🎉 **VE2Residual 無条件クローズ**（`8.2-condIIIV-ve2`。asset-blindness 逆転:
    deep4/5/6 に VE2 チェーンが既在、真の残りは EqdiagMlevel だけ→port 完了）
    ④親配線 `8.2-condIIIV-close`: **`condIIIVterminalSlice_holds` 無条件・公理クリーン**
    → `8.7-termination` の `condIIIVts` field 削除（3 use sites を差し替え）。
    **残差フィールドは `otMultiIntCond` ただ 1 本**（audit VERDICT=1）。
    攻め筋: `8.7-otmulti-narrow` が condII 脚 `OTmulti_interior_condII_on` だけに還元済み
    → FseqDesc_exchII の**等式**形（condII_masterCF 経由、今や無条件）＋
    OT_B operB 閉包（private 4 箇所に既在）＋ Lng L = 2 隅の空虚性で閉じる。
    Isabelle 藍図 = opx_OTmulti（pss_wip 115556）の condII 枝。
  - 🎯 **Wave AU（2026-07-21、Opus 2、全緑）— capstone 一本化＋tsx_assembly 深部 scb コア陥落**:
    ①capstone 組み直し完了: `baseRunStep_up_cw : BaseRunStep_up` **無条件**＋
    `ve34_on_reg4D_cw : TspinAssemblyIH_tc → ∀ M ∈ VE34Reg4D, VE34goal M`（残差 1 本）。
    **ボーナス成功: termination field まで合成到達**
    `condIIIVterminalSlice_of_assembly_cw : TspinAssemblyIH_tc → VE2Residual →
    CondIIIVterminalSlice`（DTPS ホスト経由で descending を確保し VE2 だけに
    ギャップを封じ込め）。**新顕在ギャップ = `VE2Residual`**（Isabelle vg3x_VE2 94418
    = {VE2TrunkLeg（純幹 closed form crg_slice_value_of_trunk）, VE2RegLeg（cfbx_reg
    back-peel）}）（`8.2-condIIIV-capstone`）
    ②tsx_assembly の**深部 scb コア完全 port** `tsx_assembly_scb_core_as`（104073 の
    r46 深部。F=0/F≠0 両ケース）＋`tsx_scb_Dpt_lift_as`（唯一の真欠落工具 103577）。
    🚨**asset-blindness 12 回目**: 「欠落 4 工具」中 3 つは公開双子が既存
    （Trans_unflat_transC2→`Trans_c1_c2_decomp`(8.3-condII-masterCF)/
    scbimg_image_BT→`principal_replacement_image`(7.2-scb-replaceable)/
    m_7_3_Trans_Mark_MarkedB→`Trans_Mark_mem_MarkedB`(7.3-Trans-welldefined)）。
    残差=`TspinGeomIH_as`（スライス自然性: tsx_c1_eq 103771/tsx_c2_eq 103971/
    tsx_t1_identified 104001＋bpx_step_setup/tsx_jp_geom/tsx_parent_slice/
    tsx_Adm_slice。深部 scb はゼロ。部分双子= transC1_Red_terminal_slice:610/
    transC2_congr_74:623 in 7.4-Mark-Trans-repr）（`8.2-condIIIV-assembly`）。
    **残 Props = {TspinGeomIH_as, VE2TrunkLeg, VE2RegLeg}——全て routine 領域、
    深部（研究フロンティア）は消滅。**
  - 🎯 **Wave AT（2026-07-21、Opus 2、全緑）— run-step 柱 完全陥落・残差は tsx_assembly 1 本に**:
    ①`TransPinRunStepD_pt` も点wise では証明不能（bgx_VE34_base_step の t2eq/isleft が
    ihVE4 を本質使用。数値では形は真＝12 個目の反証ではない）→ **IH-carrying
    `transPinRunStepIH_rp` として完全 port（残差ゼロ）**＋live 読出し
    `VE4goal_runstep_of_IH_rp`（`8.2-condIIIV-runstep-pin`）
    ②STEP 柱の IH-carrying 化完了: leadform 無条件 port
    （`tspinCanonicalIH_of_assembly_tc`）＋`step_up_of_assembly_tc :
    TspinAssemblyIH_tc → Step_up`。**残差 = `TspinAssemblyIH_tc`
    （=tsx_assembly 104073 の結論 Trans N = D_{N1,0}(F +_B Trans Mp)、IH 付き）唯一本**。
    port には 4 scb 工具が必要: Trans_unflat_transC2（無）/scbimg_image_BT
    （private twin=principal_replacement_image, 8.7-otint-transport-prims）/
    m_7_3_Trans_Mark_MarkedB（無）/tsx_scb_Dpt_lift（無）。
    scb_addBT_left_74・scb_unique_decomp_unconditional は private
    （`8.2-condIIIV-tspin-close`）。
    **次の配線: capstone を {BaseRunStep_up 無条件（IH ルート）＋
    step_up_of_assembly_tc} で組み直し→ ve34_on_reg4D は modulo TspinAssemblyIH_tc
    のみ→ tsx_assembly port で全クローズ。**
  - 🎯 **Wave AS（2026-07-21、Opus 2、全緑）— 残差が正確に 2 本に確定（機械保証付き）**:
    ①幾何 STEP quartet {StepTerminalReady/StepPredIndex/StepTermPred/StepFrontPred}_ss
    **全討伐**（bpx_step_setup 系 port。STEP は分岐数保存で BASE より単純＝JEQ 不要）＋
    **capstone `ve34_on_reg4D_modulo_gm : TransPinRunStepD_pt → TSPINStep_ss →
    ∀ M, VE34Reg4D M → VE34goal M`**——全 slot の生き配線を機械検証
    （refuted PIN/TSPIN/点wise VE3/VE4Step 非依存。step-surgery の旧 capstone は
    un-instantiable と判明→本 capstone が置換）。VE3 run-base SPLIT0 も独立再証明
    （`ve3RunBaseD_gm`）（`8.2-condIIIV-geometry`）
    ②TSPIN: 下半分 port `tspinStep_of_canonical_tp` で単一等式残差 `TspinCanonical_tp`
    （=tsx_assembly∘leadform の正準 pinned 形）に還元。数値検証 7/7 STEP witness 成立。
    ⚠️**点wise TSPINStep_ss は IH `VE34goal (Pred N)` なしでは証明不能**
    （tsx_t1_identified の ihVE4 step が本質使用）→ **配線指示: TSPINStep_ss を
    IH-carrying に再定式化**（Step_up_of_pieces_ss は regDP/ihP を既に scope に持つ）
    （`8.2-condIIIV-tspin`）。
    **残 = {TransPinRunStepD_pt（bgx_VE34_base_step isleft-selector 未 port）,
    TspinCanonical_tp（IH 付き tsx_assembly port）}＋TSPIN IH 化の配線＋最終組立接続。**
  - **Wave AR（2026-07-21 未明、Opus 2、全緑）— 🚨11 個目の反証＋STEP の正ルート確立**:
    ①🚨**点wise {PIN_bd, TSPIN_bd} は偽**（descending 落ちドメインの再発。cex=
    (0,0)(1,1)(2,2)(2,1)(2,2)(2,0)。`not_pin_tspin_pt`）——**生きた置換を同時構築**:
    run-base pinned 組立 `transPinRunBaseD_pt` 無条件＋VE4 側は
    `VE4BaseDeepD_of_runstep_pt` で単一残差 `TransPinRunStepD_pt`（IH 消費型＝
    unified peel の BaseRunStep_up slot で吸収）に（`8.2-condIIIV-pin-tspin`）
    ②**検証結果: bgx は STEP を tsx へ委譲**（回避不可）。IH-carrying tsx/bpx ルートを port し
    `Step_up_of_surgery_ss` で**点wise VE3/VE4Step を連鎖から排除**。残差=
    {`TSPINStep_ss`(唯一の深部 §7.4 head-transport＝tsx_assembly), 幾何 4
    {StepTerminalReady/FrontPred/TermPred/PredIndex}_ss}（`8.2-condIIIV-step-surgery`）。
    **無条件化までの残**: TransPinRunStepD（=BaseRunStep IH slot）＋TSPINStep＋幾何 Props
    ＋最終組立の配線替え（VE4 chain と Step slot の差し替え）。
  - 🎉🎉 **Wave AQ（2026-07-20 深夜、Opus 2、全緑）— 具体 4 brick 全討伐＝残り surgery 4 本**:
    ①**census＋slice-data 両方無条件**（`BgxNotleftRun0_cs2`=260 行 census 完全 port、
    `BgxMpSliceData_cs2`。`8.2-condIIIV-census-slice`）→ 閉形式 2 brick
    （BgxBaseFormNotleft/BgxMpForm）が無条件化 ②**TerminalSliceReadyD＋
    FrontPredBaseTransportD 両方無条件**（LastStep 転送 bfx_LastStep_Pred_base 込み。
    `8.2-condIIIV-frontpred`）。
    **無条件停止性定理までの残 = §7.4 head-shift surgery 4 本のみ**:
    {`PIN_bd`, `TSPIN_bd`}（BaseRunStep の最後の 2 入力）＋{`VE3Step`, `VE4Step`}
    （STEP slot、tsx_/bpx_VE34_step——研究フロンティア級）。
  - 🎉 **Wave AP（2026-07-20 夜、Opus 3、全緑）— regime 持続 2 本無条件討伐＋残 brick 再編**:
    ①🎉**`stepRegPres_up_holds`＋`runStepGuardJoint_up_holds` 無条件**（vg7x_RPERS＋
    bfx_gtP_base/Joints_Pred_last。`8.2-condIIIV-reg-pres`）②peel-values: JEQ を D-regime で
    完全 port（jeqBaseD_pv）＋TermPred transport 討伐＋**構造発見: 旧 reduction は descending を
    捨てる lossy 設計→D 保存版 `BaseRunStep_of_geomD_pv` が正**（`8.2-condIIIV-peel-values`）
    ③base-forms: 組立無条件＋残差 2 に縮小 {`BgxNotleftRun0_bf`(census 106972、
    strongmono は済・bgx_trunk_Trans 等 5 brick 要), `BgxMpSliceData_bf`(transJm1(slice)=0＋
    cond(I|III|V)、nextR-seg/row1_last_bound の public 化要)}（`8.2-condIIIV-base-forms`）。
    **無条件化までの残 brick 6**: {BgxNotleftRun0, BgxMpSliceData, TerminalSliceReadyD,
    FrontPredBaseTransportD(←bfx_LastStep_Pred_base), VE3Step, VE4Step(=研究フロンティア級)}。
  - 🎉 **Wave AO（2026-07-20 夕、Opus 2、全緑）— `HEADEQ0All` 討伐（最終 2 Props の片方）**:
    ①🎉**`headEq0All_holds` 無条件**（hqx_HEADEQ0 完全 port: trunk corner=diagSeq 閉形式、
    branching=VEReg 構築→vcx_VE_all。未移植とされた 5 brick 中 3 は公開双子あり
    （kfwd=RTPS_mono_head_eq／bfx_TrMax_Pred_base=TrMax_Pred_nontrunk／
    Joints_parent_nextR=Joints_nextR_FirstNodes）。`8.2-condIIIV-headeq0-close`）
    ②bgx 還元: 統一 peel に載せる設計が正解と検証——HEADEQ0 消費は run-base BASE slot のみ。
    `BgxVE34RedHE0_of_bricks_bg` で**残差 6 本に分解**: HEADEQ0 依存の閉形式 2
    {`BgxBaseFormNotleft_bg`(106329+census 106972), `BgxMpForm_bg`(106407)}＋
    HEADEQ0 非依存の peel slot 4 {BaseRunStep_up(106565), Step_up(tsx), RunStepGuardJoint_up,
    StepRegPres_up(vg7x_RPERS)}（`8.2-condIIIV-bgx-reduction`）。
    **無条件化までの残 = この 6 本**。
  - 🎉 **Wave AN（2026-07-20 午後、Opus 2、全緑）— HEADEQ0 capstone 組立＋統一帰納完成**:
    ①**HEADEQ0 campaign 入口**（`8.2-condIIIV-headeq0`）: hqx_/bgx_ 完全地図＋
    `hqx_VE34_of_DT_hq` capstone を **{`BgxVE34RedHE0_hq`(bgx 還元 ~1000 行),
    `HEADEQ0All_hq`(hqx_HEADEQ0 240 行)} の 2 Props modulo で組立**。vcx_VE_all 討伐済の
    検証結果=HEADEQ0 の branching case の深部値のみ供給（trunk corner=diagSeq closed form、
    glue が要る）。未移植 brick: bgx_headedge/bfx_gtN/bfx_TrMax_Pred_base/
    kfwd_reduced_monoT_diag00/diagSeq_getElem rename。名前対応表も確立
    （vg2x_VE34=VE34goal 等）②**統一 backpeel 帰納完成**（`8.2-condIIIV-unified-peel`、
    bfx_VE34_backpeel_fin3 の正しい frame、BASE 保存なし、9 定理緑）。
    **condIIIVts への 2 経路**: (A) hqx 経路={BgxVE34RedHE0, HEADEQ0All}（本命）
    (B) 統一帰納経路={PIN/TSPIN/VE3RunBase/RunStep(→幾何3Props)/VE3/4Step}。
  - **Wave AM（2026-07-20 昼、Opus 2、全緑）— 🚨10 個目の反証＋真の閉路が HEADEQ0 と判明**:
    ①🚨**`RunSqueeze_vn`／`RunPeelPreservedD_vc2` は偽**（cex=(0,0)(1,1)(2,2)(2,0)(3,1)(2,0):
    BASE の peel 後 Pred が STEP になる＝**BASE 保存という設計自体が欠陥**。正=Isabelle
    bfx_VE34_backpeel_fin3(105252) の**統一 BASE-or-STEP 強帰納**（BASE 保存不要）。
    `8.2-condIIIV-runsqueeze` に機械反証）②**stale 訂正: §8.2 keystone は移植済み**
    （`keystone` in 8.2-subexpr-component-Pred！）→ `VE3RunStep_of_reductions_vv` が
    幾何 3 Props modulo で討伐（`8.2-condIIIV-ve-values`）③**戦略転換情報**: bfx_ の
    carried residuals（SPLIT0/PIN/TSPIN）の真の閉路は **hqx_/bgx_ HEADEQ0 ルート
    （wip 106236–108686、~2450 行）＝これ 1 本で VE3All/VE4All 全部が閉じる**。
    **次の計画**: ①統一 backpeel 帰納の再設計（BASE 保存撤去）②HEADEQ0 campaign
    （bgx_ 還元→hqx_HEADEQ0 討伐→hqx_VE34_of_DT）③幾何 3 Props。
  - 🎉🎉 **Wave AL（2026-07-20 午前、Opus 2、全緑）— `otSetleCore` フィールド陥落＝残差 2**:
    ①**corner census 再配管の決着**: 偽 wrapper は**そもそも不要だった**——唯一の消費先
    （ox5_census の scbext_triG 経由 G-control）は無条件の `tri0CruxConcrete_holds` で直接供給可。
    z=D_∞ 変種 `ox5_body_driver_cc2` で組立→`otSetleCore_of_parts_cc2 : A0OTNub →
    SetleCensusSpine → otSetleCore`、両入力は Wave AK 討伐済＝**otSetleCore 無条件化**
    （termination から削除、フィールド 3→2）。（`8.7-corner-census`）
    ②VE: run-peel 修正チェーン前進——Pred-free `RunSqueeze_vn` 3 conjunct に尖鋭化＋
    dead ルート（refuted RunPeelPreserved_bd）の置換 `VE3BaseDeepD_of_residuals`
    （`8.2-condIIIV-ve-next`）。
    **現フィールド 2**: `otMultiIntCond`（condII のみ＝condIIIVts 陥落で自動）／`condIIIVts`
    （残={RunSqueeze_vn, VE3RunBase/RunStep, PIN/TSPIN, Step 系, field 再配管}）＝
    **実質 VE34 一本勝負**。
  - 🎉 **Wave AK（2026-07-20 朝、Opus 3、全緑）— spine gap 討伐＋A0OTNub 完結＋🚨9 個目の反証**:
    ①**`a0otNub_holds` 無条件**（NubGControl は OixGControl_holds パターンの bridge で即閉。
    `8.7-a0otnub-assembly`）②🎉**`setleCensusSpine_holds_a3c` 無条件**（Isabelle 側も deferred
    だった align3 gap を**新規 node-count monovariant（nodesBT）ルート**で討伐——数値 4M+ 事前検証。
    `8.7-align3-close`）③🚨**`SetleCensusWrapperCondIVCorner_wc` は偽**（corner 24/24 が
    degenerate 形＝shape refinement 仮説の真逆。障害は Lean 内で純粋証明
    `corner_wrapper_conclusion_unsat_cs`: A₀=1 principal vs ins 0_B=2 principals で
    wrapper 共有は構造的に不可能。**census 側の corner 義務を別 pivot（body/D_e3 レベル等）に
    再配管する再設計が必要**。`8.7-corner-shape`）。
    **otSetleCore 残**=corner census 再設計 1 点のみ（spine/A0OT/Tri0/Provenance/Wrapper-ltJ 全て済）。
  - 🎉 **Wave AJ（2026-07-20 未明、Opus 4、全緑）— Tri0Crux 無条件討伐**:
    ①**`tri0CruxConcrete_holds` 無条件**（ltJ/corner 再 dispatch。corner 側は collapse で
    scb wrapper 不要＝新残差ゼロ。`8.7-tri0-dispatch`）②wrapper condIV: ltJ 側完全討伐→
    残差=admeq corner のみ `SetleCensusWrapperCondIVCorner_wc`（**degenerate 形なら構造的に偽
    ＝corner⇒nested 形の shape refinement（c4dx_condIV_c2body_shape admeq 版）が正しい的**。
    `8.7-wrapper-condiv`）③spine align3: family 地図＋peel 前半 port→単一 Prop に還元
    （`8.7-spine-align3`）④VE continue: basedeep 残差束の latent bug 発見・修正込み前進
    （`8.2-condIIIV-ve-continue`）。
    **otSetleCore 残**={NubGControl([Buc1]3.4 generic), SpineSurgery census 具体化,
    WrapperCondIVCorner(shape refinement), （A0OT/Tri0/Provenance/RegimeE3 は済）}。
  - 🎉 **Wave AI（2026-07-19 深夜、Opus 4、全緑）— CensusProvenance・A0OT 討伐**:
    ①**`censusProvenance_holds_cp` 無条件**（live mnform 連鎖の完全配線）＋wrapper condIII 討伐
    （condIV 側=新残差 `SetleCensusWrapperCondIV_cp`。`8.7-census-provenance`）
    ②**`A0OT_holds_ac` 討伐**（CensusProvenance 帰着＝実質無条件。ot1_A0OT 完全 port、
    ltJ guard 回避の transport 設計。NubRegimeE3 も討伐。`8.7-a0ot-close`）
    ③tri0 両枝配線＋spine を真の gap `SpineSurgeryTransportCensus_ts`（=ox7_align3_track、
    Isabelle STATUS §7）に還元（`8.7-tri0-spine`。⚠️**stale 注意: tri0CruxConcrete_of_pkg_ts は
    反証済みの Exch84_scbDecompPkg を仮定に取る**——ltJ 領域では exch84ScbDecompPkgLtJ_holds_sp2
    で供給可、corner 側は別配線が要る＝次 wave で dispatch 修正）
    ④otMultiIntCond→condII 限定 `OTmulti_interior_condII_on`（III-V 討伐。`8.7-otmulti-narrow`）。
    **otSetleCore 残**={Tri0Crux 供給の corner 側, SetleCensusWrapperCondIV, SpineSurgery(真 gap)}。
    **otMultiIntCond**→condII のみ（condIIIVts 陥落で自動）。
  - 🎉 **Wave AH（2026-07-19 夜、Opus 4、全緑）— `cornerNpValue` フィールド陥落＝残差 3**:
    ①🎉**`cornerNpSliceValue_holds_cnv` 無条件**（np_c2decomp の valNp 連鎖を全 slice へ、
    `8.4-corner-np-value`）→ **旧 slicepkg 系フィールド完全消滅（4→3）**
    ②census: `censusPin_tc`（provenance で抽象 binder を具体値に pin する機構）＋setleCensus の
    0<v1 討伐→otSetleCore は {A0OT_an(真の未知), CensusProvenance(←mnform 連鎖で供給可),
    Tri0CruxConcrete, SetleCensusWrapper, SetleCensusSpine, NubRegimeE3/NubGControl} 構造に
    （`8.7-otint-tri0-census`＋`8.7-otint-a0ot-nub`）③VE BaseDeep 前進（`8.2-condIIIV-basedeep`）。
    **現フィールド 3**: `otMultiIntCond`(空虚)/`otSetleCore`/`condIIIVts`。
  - 🎉 **Wave AG（2026-07-19 夕、Opus 4、全緑）— slicepkg フィールドが単一原子に**:
    ①**Np_c2decomp 無条件討伐＋連鎖組立**（`8.4-np-c2decomp`: C7Rightend/SliceExtTupleEngines/
    SliceExtTupleResidual も同時に無条件化、`exch84slicepkg_of_cornerReadouts_nc2` で
    **slicepkg 全体が CornerCoreReadouts_cc 1 本 modulo に**）②corner readouts: LEAF3/5 討伐、
    LEAF4 は `CornerNpSliceValue_cr2` 1 本に還元（505/505 数値検証。閉じ方=Red(s84x_N M)
    全 slice 版の regsp-strictlt 類似。`8.4-corner-readouts`）→**termination の exch84slicepkg
    フィールドを `cornerNpValue : CornerNpSliceValue_cr2` に置換**（原子 1 本）
    ③VE Base: 最小 base（Lng=TrMax+2）両討伐→残差を run-region 限定 `VE3/VE4BaseDeep` に尖鋭化
    （`8.2-condIIIV-ve34-base`）④VE Step: 幾何準備のみ（**bpx_ round は Isabelle でも
    研究フロンティア級**の注記。`8.2-condIIIV-ve34-step`）。
    **現フィールド 4**: `otMultiIntCond`(空虚)/`otSetleCore`(census 3 葉)/
    `condIIIVts`({VE3/4 BaseDeep, VE3/4 Step})/`cornerNpValue`(1 値等式)。
  - 🎉 **Wave AF（2026-07-19 午後、Opus 4、全緑）— Kind1Shape・L1SliceData 陥落＋condIIIVts は VE3/VE4 のみ**:
    ①corner: `Base1pCorner`＋`CornerC2Kind1` 討伐（RightAnces chain 不要の condIV pin 技。
    残=`CornerCoreReadouts_cc` のみ=d4vx_core 塔（c4cx2_condIV_mnform_of_slice）。`8.4-corner-deep`）
    ②🎉**`kind1Shape_holds` 無条件**（812 行、s84c3_RightAnces_chain 55372 の完全 port。
    set N/Q で rewrite loop 回避。`8.4-kind1-shape`）③🎉**`l1SliceData_holds` 無条件**
    （L1 幾何を条件非依存に再導出、s84d_c2hole_L1 を成分別合同で迂回。`8.4-l1-slice-data`）
    ④deep3→**deep2 相当**: EqdiagMlevel 討伐（ROW10=既存 reduced_coeff で Min/Max 機構不要）→
    **condIIIVts 残={VE3Base, VE3Step, VE4Base, VE4Step}**（§7.4 head-shift readback surgery。
    ⚠️naive prefix-append 帰納は反証済→m_7_4_Trans_Mark_Pred＋Mark_Trans_repr で。
    `8.2-condIIIV-deep3`）。
    **slicepkg 残差**: SliceExt→{Np_c2decomp_sc3}（Kind1/L1/C7 済）＋CornerCoreReadouts＋
    （Base 系は corner 済で dispatch 完結間近）。**otSetleCore=census 3 葉が最後の山**。
  - 🎉 **Wave AE（2026-07-19 午後、Opus 4、全緑）— `rm84Exists` フィールド陥落＝残差 4**:
    ①🎉**`rm84RFacts_holds` 無条件**（s84c2_R_facts 完全 port、iff1 は factor-by-factor 構築で
    fragility 回避）→`rightmost84ReplaceExists_rc2` 無条件→**termination の rm84Exists 削除
    （フィールド 5→4）**（`8.4-rm84-rfacts-close`）②Base0/1p 両 leg 討伐（ltJ/corner dispatch、
    残=既存 MnformCornerResidual＋新 `Base1pCorner_bl3` 1 本。`8.4-base-legs`）
    ③C7Rightend→rm84 に統合（rc2 で即閉）＋`Np_c2decomp_sc3`（w84x_d4b_dispatch 79198。
    残深部=Kind1Shape(s84c3_RightAnces_chain 55372)/L1SliceData(s84d_L1_data 59295)。
    `8.4-slice-ext-close`）④deep4 前進（VE2 prefix geom 討伐、`8.2-condIIIV-deep4`）。
    **現フィールド 4**: `otMultiIntCond`(空虚)/`otSetleCore`(census 3 葉)/`condIIIVts`(deep4)/
    `exch84slicepkg`(残={SliceExt 3 深部, CornerCore 2, Base1pCorner, MnformCornerCore 5 葉})。
  - **Wave AD（2026-07-19 昼、Opus 4、全緑）— 🚨scbDecompPkg 反証（8 個目）＋R-facts 3 conjunct 化**:
    ①rfacts: Frame 全 5 部を討伐/還元→残差 `Rm84RFacts`（dich/RTPS(R)/adm 一致の 3 conjunct、
    閉じ方の詳細ルートを needs に文書化済——nextrel1 boolean 構築の fragility 対策込み。
    `8.4-rm84-rfacts`）②🚨**`Exch84_scbDecompPkg` は偽**（corner で dP が長さ矛盾＝
    NestScbCornerTriple 反証の系。**ltJ guard 付き版 `exch84ScbDecompPkgLtJ_holds_sp2` は
    無条件討伐**。Base0/1p は pkg 経由でなく ltJ/corner dispatch で再証明要——配線案は
    ファイルヘッダに。`8.4-scbdecomp-pkg`）③SliceExtTupleEngines→3 tight Props（L1 flat 討伐、
    `8.4-slice-ext-engines`）④**deep5→deep4**（VE2RegPrefixReg 上部討伐、
    `condIIIVterminalSlice_of_deep4`＋`condII_masterCF_of_deep4`、`8.2-condIIIV-deep5`）。
  - **Wave AC（2026-07-19 朝、Opus 4、全緑）— 🎉d4a transport 完全無条件化＋rm84 surgery frame**:
    ①🎉**`nestScbD4aReducedValue_holds`＋`nestScbD4aTransport_dk` 無条件**（regime 側=slx37＋
    vcx_VE_all 転送、trunk 側=crg_slice_value_of_trunk port。`8.4-d4a-trunk`）→
    **slicepkg dispatch 残り 4**: {SliceExtTupleEngines_st, corner(→CornerC2Kind1_cc＋
    CornerCoreReadouts_cc), Base0/1p（共通鍵=Exch84_scbDecompPkg）}
    ②rm84 surgery: 正ルートの上部構造 port＋**残差 `Rm84SurgeryFrame` は 45/45＋cex＋A30 で
    数値検証済（死残差でない）**（`8.4-rm84-surgery`。core-swap は Red(s84x_Np M) への
    c2hole 適用で Wave-Y 反証を回避。残=R-facts 系 L4 part(2)(3)）
    ③corner core: 5 葉→{CornerC2Kind1_cc, CornerCoreReadouts_cc}＋TransC2HoleDecomp_md 再利用
    （`8.4-corner-core`）④VE deep6→**deep5**（VE2TrunkLeg 討伐、`condIIIVterminalSlice_of_deep5`、
    `8.2-condIIIV-deep6`）。
  - **Wave AB（2026-07-19 朝、Opus 4、全緑）— 🎉StrictLt 討伐＝slx37 無条件化＋🚨value ルート死路確定**:
    ①🎉**`RegspStrictlt_holds`＋`Regsp_slx37_regSP_holds` 無条件**（public Pred-branch cores＋
    Regs_MCOND＋DTPS tie-break＋trunk 対角の完全 port、`8.4-regsp-strictlt`）→
    **REGSP slicepkg leg 解禁**。D4aReducedValue の regime 側も解禁（残=trunk 側
    crg_slice_value_of_trunk 91399 のみ）②🚨**Rm84Np/Lp/HeadValue 全て偽**（cex=(0,0)(1,1)(2,1)
    condIII: c2-hole 内側 readback は jm2≠j0 で 1 principal ずれる。Wave AA の value 分解は
    condV/hostM30 の一致点だけで成立していた＝**7 個目の反証**。`8.4-rm84-np-value`+
    `8.4-rm84-lp-value` に機械反証）。**正ルート=Rm84HeadShared（存在 scb 形、無傷）または
    surgery（Isabelle m_8_4_rightend_Trans）**。termination フィールドは rm84Exists（真形）の
    ままなので無事 ③VE234: 3 値残差を**regime 分離 6 深残差**に還元
    （`condIIIVterminalSlice_of_deep6`、`8.2-condIIIV-VE234`）。
    **次の的**: rm84=Rm84HeadShared/surgery 直撃（m_8_4_rightend_Trans を grep）／
    slicepkg=D4a trunk 側＋corner core 5 葉＋SliceExtTupleEngines＋Base 残／
    condIIIVts=deep6／otSetleCore=census 3 葉。
  - **Wave AA（2026-07-19 未明、Opus 4、全緑）— 3 フィールドの残差が値レベルまで尖鋭化**:
    ①rm84: head-stripped エンジン `c2holeInner_scb_ha` で scb 側 2 義務を無条件討伐→
    残差は**純値 2 等式 `Rm84HeadValue`**（Np 半分=closed condV terminal-slice ×2 適用＋bridgeA、
    Lp 半分=非単項 readback＝既知 blocker。`8.4-rm84-head-aware` に攻め筋文書化済）
    ②slx37: mcx_regSP_of_diag＋DIAG sandwich port→残差は**単一 tie-break `RegspStrictlt_sx`**
    （=slx37_strictlt_eqd 97052。閉じ方=8.2-strongmono-props の private Pred-branch 転送
    （Br/FirstNodes/Joints_Pred_core）の index-level 再導出＋Regs_MCOND_holds。`8.4-regsp-slx37`）
    ③corner engine: 10 conjunct 中 5＋k1 配線を無条件討伐→残差 `MnformCornerCoreResidual_ce`
    5 葉（`8.4-corner-engine`）④**VE34 組立 capstone 完成**: `condIIIVterminalSlice_of_residuals`
    （=vg7x backpeel 形）＋`condIIIVterminalSlice_of_VE`（=hqx 形）→ condIIIVts は
    {VE34Base4, VE2/VE3/VE4 Residual} に還元（`8.2-condIIIV-VE34-assembly`）。
    **残フィールド 5 の残差スタック**: rm84={NpValue, LpValue}／slicepkg={StrictLt, CornerCore 5 葉,
    SliceExtTupleEngines, Base0/1p 残}／otSetleCore=census 3 葉／condIIIVts={VE2,VE3,VE4,Base4}／
    otMultiIntCond=供給待ち。**promotion 候補: 8.2-strongmono-props の Pred-branch core 3 本**。
  - **Wave Z（2026-07-19 深夜〜、Opus 4、3 完走＋1 が 5h limit で mid-run 死→遺留緑回収）**:
    ①**OixCoreTri 討伐**（otx3 tri-core 全再帰を _cl で再導出、`8.7-otint-census-leaves`）→
    `otSetleCore_of_3leaves`＝otSetleCore は {A0OTNub, Tri0Census, setleCensus} の 3 葉に。
    3 葉とも census 具体 provenance が要る（抽象からは導出不能と検証済み）＝§8.4 producer 系
    campaign。②**TransC2HoleDecomp_md 討伐**（c2hole_scb_ch 経由の直撃、`8.4-slicepkg-residuals`）。
    (2)corner mnform=c4dx_condIV_k1 系未移植、(3)D4aReducedValue=**Regsp_slx37_regSP
    （slx37_regSP_uncond）に帰着**（slice_Trans_principal_head の body 保存に VEReg 必要）
    ③VE34 STEP: `vs2x_VE34_step` は純再組立（VE34goal⟺VE3∧VE4）と判明（`8.2-condIIIV-VE34-step`）
    ④rm84-head-aware: agent は limit 死だが**遺留ファイル緑（8 宣言）で回収**（`8.4-rm84-head-aware`、
    checkpoint 規律の勝利。続きは同ファイル拡張で）。
    **残フィールド 5 の攻略地図が完全化**: rm84=head-aware 続行／slicepkg={D4a(→slx37), corner
    engine, BottomExt(→SliceExtTupleEngines), Base0/1p}／otSetleCore=census 3 葉／
    condIIIVts=VE34（reg/RPERS/BASE/STEP 済、残=BASE-geom 続き＋backpeel 組立＋hqx 接続）／
    otMultiIntCond=他フィールド供給待ち（空虚）。**slx37_regSP が 2 残差の共通鍵**。
  - **Wave Y（2026-07-19、Opus 4、全緑）— 🚨反証 2 件（危険回避）＋slicepkg 再配線＋setle 還元**:
    ①🚨**`C2HoleSliceTransport_ch` は偽**（cex M=(0,0)(1,1)(2,1) condIII: Trans(s84x_Np M) が
    余分な外側 principal D_{M1,jm2} を持つ。c2hole 設計は暗黙に condV を仮定していた。
    **`Rightmost84ReadbackShared` も同根で偽**＝termination の rm84Readback フィールドが
    充足不能だった→**即日 `rm84Exists : Rightmost84ReplaceExists`（真）に戻した**。
    正しい閉じ方=head-aware 還元: condIII/IV では Trans(s84x_Np M)=Dprin(M1,jm2)(transC2 M)、
    condV でのみ head 併合。93/93 condIII で transport 破綻を数値確認。`8.4-c2hole-transport`）
    ②**slicepkg 再配線完了**（`8.4-mnform-corner-dispatch`。MnformBottomResidual 自体も偽と判明
    →生きている下流 ∀M MnformResidual M を ltJ/corner dispatch で供給、
    `exch84slicepkg_of_dispatch_md` が新ルート。残={NestScbD4aTransport_ns(→ReducedValue),
    TransC2HoleDecomp_md, MnformBottomExtResidual(→SliceExtTupleEngines_st),
    MnformCornerResidual_md(=oi5_bodyOT), Base0/Base1p}）
    ③setle 側完全組立（`8.7-otint-setle-assembly`: `otSetleCore_of_leaves` で otSetleCore は
    {OixCoreTri, A0OTNub, Tri0Census, OTintIIIIV_setleCensus} の 4 葉に還元）
    ④VE34 続行（`8.2-condIIIV-VE34-reg`: 修正 regime 機構＋無条件 RPERS＋BASE 幾何、
    wip 94469–95469）。
    **現フィールド 5**: `otMultiIntCond`/`otSetleCore`(4 葉)/`condIIIVts`(VE34)/
    `exch84slicepkg`(新 dispatch 経由 6 残差)/`rm84Exists`(head-aware 再設計待ち)。
  - **Wave X（2026-07-19 深夜、Opus 6、全緑）— c2hole エンジン完成＋ox census 討伐＋🚨nestScbTriple 全体が偽**:
    ①**c2hole エンジン完全 port**（`8.4-c2hole-engine`、s84d_c2hole/corepair 系 1:1、hole 定義は
    transC2Core と defeq）→ `rightmost84ReplaceExists_of_transport_ch` で rm84 フィールドは
    `C2HoleSliceTransport_ch` 1 本に還元。⚠️**agent の「p_8_2_condV_terminal_slice_Trans 未証明に
    gate」判定は STALE**——それは codex が閉じた（8.2-condV-terminal-slice-Trans-close ✅）。
    **次 wave 最優先: closed terminal-slice で C2HoleSliceTransport_ch を discharge**
    ②**ox5 census 討伐**（`8.7-otint-ox5-census`、[Buc1] 3.5 congruence 系も再導出。
    残=census wrapper 事実（oi5 pkg 系、配線時に hflat から供給可の見込み））
    ③KKraw: 抽象降下エンジン緑（`8.7-otint-kkraw`、census 具体化が残）
    ④SliceExtTuple→`SliceExtTupleEngines_st` ⑤d4a-target 討伐→`NestScbD4aReducedValue`
    ⑥🚨**`exch84_nestScbTriple_false_cr : ¬Exch84_nestScbTriple`**（corner の反証を全体に持ち上げ）
    ＋正しい corner Prop `CornerCollapse_cr` は**証明済み**（`8.4-corner-redesign`）。
    **帰結: nestScbTriple 経由の mnform 配線（mnformBottomResidual_holds の第1仮定）は死路**＝
    次 wave で CornerCollapse ベースの dispatch に mnform/scbDecompPkg 系を配線し直せ。
    フィールド 5 は不変（rm84Readback の swap は transport discharge と同時に実施予定）。
  - **Wave W（2026-07-19、Opus 6、全緑）— 深部原子の攻略＋🚨反証 1 件**:
    ①readback: **T2 形は condIV で大域的に偽**（普遍 readback 補題は存在しない）＝値ルートでなく
    **c2-hole エンジン（s84d_c2hole/s84d_corepair_* wip 52658–54005 ~1400 行）が忠実ルート**。
    rm84Exists→`Rightmost84ReadbackShared` に配線替え済（`8.4-rightmost-readback`。
    `mark_tower2_eq_trans_rrLp` 無条件も獲得）②ox 完結: `ox10_SETLE1_close_oc` が SETLE1 を
    setle core の形で産出（残=census 2 葉 ox5(4974)/KKraw(8539)。`8.7-otint-ox-close`）
    ③MnformBottomExt→`SliceExtTupleResidual`（from_slice port、`8.4-exch84-from-slice`）
    ④d4a 討伐 modulo `NestScbD4aTargetValue`（`8.4-exch84-d4a`）
    ⑤🚨**`NestScbCornerTriple_ns` は偽と機械証明**（corner で dP の要求 scb 分解が不成立、
    `8.4-exch84-corner` に反証。**`8.4-exch84-nest-scb` の corner 枝は言明の再設計が必要**＝
    exch84_nestScbTriple_holds の corner 側仮定は充足不能。次 wave で jm3eq ルートの正しい形を
    Isabelle から採り直せ）⑥**VE34 入口完成**: family 地図＋`VE34_backpeel`/`VE34_of_reg`/
    `condIIIV_of_VE2_VE34` 骨格（`8.2-condIIIV-VE34-entry`、wip 92559–108722 の 2 本柱地図付き）。
    **現フィールド 5**: `otMultiIntCond`/`otSetleCore`/`condIIIVts`/`exch84slicepkg`/`rm84Readback`。
  - **Wave V（2026-07-19、Opus 6、全緑）— `c2l1NotLD` フィールド討伐（6→5）＋深部原子の地図完成**:
    ①**`nadmC2L1NotLD_holds` 無条件**（atx_notLD/atx_condV_nadm_t2_components の完全 port、
    `8.5-exchV-notld`）→ termination の `c2l1NotLD` フィールド削除。
    ②nestScbTriple 討伐 modulo {`NestScbD4aTransport_ns`(=cpx_d4a_all 98511、cfbx_reg 正則性
    エンジン要), `NestScbCornerTriple_ns`(condIV admeq corner 78636)}（`8.4-exch84-nest-scb`。
    s84d_dec2_nest_scb 本体は完全 port 済）③MnformBottom→`MnformBottomExtResidual`
    （ubeq 無条件・c2-c5 は triple から。残=hflat/c1/c7/L1flat/M1flat=
    m_8_4_various_scb_IIIIV_from_slice 60034、`8.4-exch84-mnform-bottom`）
    ④rm84Exists **blocked だが core 完成**: `rr84_shared_of_readback`（値 2 本が既知なら機械組立）。
    残=Trans(N')/Trans(L') の自己相似 readback 2 値（`8.4-rightmost-exists`）
    ⑤A0OT→{`OixCoreTri`(otx3_core_tri 2517), `A0OTNub`(ot1_A0OT 4762=真の未知), `Tri0Census`(4081)}
    （`8.7-otint-a0ot`）⑥ox5–ox10 engine 前半 port（ox8_rsub/ox9_holeD 系緑、
    残=`Ox10SETLE1Residual_ox` の 3 入力、`8.7-otint-ox-engine`）。
    **現フィールド 5**: `otMultiIntCond`(空虚)/`otSetleCore`/`condIIIVts`(VE34)/
    `exch84slicepkg`/`rm84Exists`。残る深部=VE34 back-peel/cfbx_reg 正則性/ox 後半/A0OT nub/
    readback 2 値/from_slice エンジン。
  - **Wave U（2026-07-19、Opus 6、全緑）— 2 討伐＋4 絞り込み（配線替えは未実施・次セッション冒頭で）**:
    ①`nadmW2nostr_holds` **無条件討伐**（`8.5-exchV-nadm-w2nostr`、VE 資産をフル活用）
    ②otMultiNotCondI→`OTmulti_interior_intCond_nc1` 1 本（condVI 全枝＋zero-leg クローズ。
    残=II–V の interior OT 所属＝他フィールドから供給可能・経験的空虚。`8.7-otmulti-notcondI`）
    ③NadmC2L1→`NadmC2L1NotLD`（=atx_notLD 86198。値組立・congruence 層は無条件。`8.5-exchV-nadm-c2l1`）
    ④Rightmost84Corrected⟺`Rightmost84ReplaceExists`（∃! の一意性半分は無条件討伐。
    `8.4-rightmost-replace-close`）⑤MnformResidual→`MnformBottomResidual`（=cpx_various_scb_IIIIV
    @m=1 の生 scb タプル。`8.4-exch84-mnform-residual`）⑥Cnv 2 本無条件討伐＋
    scbDecompPkg→`Exch84_nestScbTriple`（=s84d_dec2_nest_scb 系。`8.4-exch84-scbdecomp`）。
    **次セッション冒頭の配線替え（未実施）**: otMultiNotCondI→intCond 1:1／exchVMnadmAtomic→
    {Rightmost84ReplaceExists, NadmC2L1NotLD}（w2nostr 済）／exch84slicepkg→
    {MnformBottomResidual, Exch84_nestScbTriple}（cnv/base 済）。実質原子=intCond(空虚)/
    otSetleCore 2 原子/condIIIVts(VE34)/mnformBottom/nestScbTriple/rm84Exists/c2l1NotLD。
  - **Wave T（2026-07-19 未明、Opus 6、全緑）— 3 フィールド 1:1 絞り込み＋slicepkg legs 前進**:
    ①condII→`CondIIIVterminalSlice`（`8.3-condII-Boundary-close`。**重要発見: vcx_VE_all は
    VE2/VE3/VE4 を供給しない**——それらは condII/IV 用 VE34 back-peel（wip 93171–108761、
    ~15.6k 行未移植、vg2x_/vg3x_/vg4x_/vg7x_/bfx_/bgx_/hqx_）。vcx_VE_all が閉じるのは
    HEADEQ0(108441) だけ。**VE34 campaign が condII の律速**）②otSetle→`OTintIIIIV_otSetleCore`
    （OTA1 の G 条件は閉じた。残 2 原子=isOT_BT(ins A0)（ot1_A0OT scratch:4762）＋SETLE1
    （ox10_SETLE1_ltJ scratch:10995、ox5–ox10 spine-descent ~1000 行未移植）。`8.7-otint-setle`）
    ③otMultiInterior→`OTmulti_interior_notCondI_om2`（条件(I) 完全クローズ。**実ホスト 220/220 が
    条件(I)＝残差領域は経験的に空虚**。`8.7-otmulti-interior`＋audit script）
    ④mnform 両 leg 討伐 modulo `MnformResidual`（塔帰納は無条件、`8.4-exch84-mnform`）
    ⑤Base1p＋Base0_A0bridge 討伐 modulo `Exch84_scbDecompPkg`/`Cnv_c2_shape_condIV`/
    `Cnv_nested_hole_pair`（`8.4-exch84-base1p`）⑥nadm 原子→`Rightmost84ReplaceCorrected`＋
    `NadmW2nostr`＋`NadmC2L1` の 3 分解（`8.5-exchV-nadm-atomics`）。
    **現フィールド 5（全て絞り込み後）**: `otMultiNotCondI`/`otSetleCore`/`condIIIVts`/
    `exch84slicepkg`/`exchVMnadmAtomic`。**残る深部キャンペーン**: VE34 back-peel（最大）／
    ox5–ox10＋ot1_A0OT／MnformResidual＋scbDecompPkg 群／NadmW2nostr・NadmC2L1。
  - 🎉 **Wave R（2026-07-18 夜、Opus 8、全緑）— Oper5 完全クローズ＋TV_LDJB 陥落＋3 フィールド絞り込み**:
    ①`8.4-oper5-residual` 拡張完了: `oper5Residual_holds`/`oper5Support_unconditional`/
    `oper_props_5_unconditional`（§8.4 part(5) 無条件）②`8.3-condII-LDJB-lttrmax`:
    **`tv_ldjb_holds : TV_LDJB` 無条件**（CondII TV 残=NotLdjReg/TvxBoundaryData の 2、共に VE 待ち）
    ③otIIIIVdata→`OTintIIIIV_otSetleResidual`（OTA1_ltJ/SETLE1_ltJ 対のみ。T_B 側 2 conjunct
    無条件化、`8.7-otint-transport-data`。otx3_core_tri/otx3_pOT の実装名は docstring と異なり
    private のまま）④exchVMres→`ExchVMCoreResidual`（4 conjunct、bridge 2 本無条件、
    `8.5-exchV-M-tower-close`。⚠️core の conjunct(3)=∀n Oper5Residual は①で落とせる＝次に絞れ）
    ⑤otMulti→`OTmulti_interior_om2`（multi 構造分解完了、残=mono 末尾成分 6-way interior、
    `8.7-otdisp-OTmulti2`）⑥VE: RPj1eq 討伐＋**訂正: VE_all の残差は 5 だった**→現残=
    {BASE-triple(8.2-condV-VE-base2), BpaxVEstep(65663), VEj1eqResidual(77061, 要 bpx2_BASE 等),
    BpaxRPERS(65860)}（`8.2-condV-VE-close`）⑦slicepkg: `exch84slicepkg_holds` modulo 4 legs
    （`ltJ_or_IVadmeq_sp` 無条件。残=Mnform_condIIIIV(98605)/Mnform_condIV_admeq_sp/
    Base0_A0bridge/Base1p_condIIIIV(oy1 layerC:979/1086)。`8.4-exch84-slicepkg`）
    ⑧`8.4-rightmost-replace-Trans`[r1]: A30/A31 反例機械証明＋訂正形 green-modulo（板は 🚨 へ）。
    **termination 配線替え: フィールド 5 のまま全て絞り込み**
    （`otMultiInterior`/`otSetle`/`condII`/`exch84slicepkg`/`exchVMcore`、main 緑・公理クリーン、
    build 3191 jobs）。audit 3 葉表示（exchV 過少計上込み）。
    ⚠️**audit の過少計上バグ（2026-07-18 発見）**: `audit_8_7_termination.py` は
    `ExchV_nf3x ← nf3x_holds`・`ExchV_scbdec_adm_forms ← adm_forms_holds` を CLOSED 扱い
    するが、**両 discharger は仮定付き**（`ExchVres_{adm,nadm}_M_tower` を要求）。
    真の残差 = `TerminationResidual` の**フィールド一覧**（`exchVresAdmTowers`/`exchVnf3x`
    を含む）で数えること。audit の「6 葉」は exchV の塔 2 本を見落とした値。
    この塔は §8.4 L-tower（`m_8_4_oper_props_5`＋`s84x_L` 帰納＝Oper5Support/nadm 組立と
    同一 campaign）が供給予定。
  - 🎉 **Codex 継続（2026-07-18）**: ① `8.2-condV-VE-base2` の
    `baseMLtTrMax_holds` を公開済み rightmost-parent 3補題から無条件証明。② `8.4-oper5-residual` の
    `oper5Residual_holds` を `8.5-exchV-M-tower-close` へ配線し、旧
    `ExchVMCoreResidual`（4連言）を `ExchVMValueResidual`（`PredNp`/`Lpv`/`L1v` の
    3値式）へ縮約。`TerminationResidual` の第5フィールド名は `exchVMvalues`。
    ③ audit を修正し、正本5フィールドと named-Prop 下位葉を分けて表示。
    ④ strict/collapse 共通の BASE ブリック `baseMint_holds` / `baseLeR_holds` /
    `basePredVE_holds` を無条件化。⑤ `Pred N` の対角列形と
    `Pred_diagSeq_Trans` の直接計算で `BaseVEStrict` / `BaseVEAdm0` も無条件化し、
    `a0x_base_VE_vb2` の残差引数を 0 にした。⑥ `bpax_RPERS` も `Pred` の
    枝数・最終 joint/first-node 保存から無条件化。⑦ Isabelle `bpax_VE_step`
    の6 discharger（`lerR`/`id2R`/`id3R`/`tneR`/`intMR`/`intNR`）と scb surgery heart
    を移植し、`bpaxVEstep_holds` も無条件化。Lean 側は
    `scb_unique_decomp_unconditional` と実行可能 `unflatBT` parser を使い、Isabelle の
    principal-image/非零仮定を要しない短縮証明になった。
    ⑧ `VEj1eqResidual` の deepen/collapse 両枝も閉じ、無条件
    `vcx_VE_all` を公開。対象 build 3065 jobs は完走、追加ブリックも sorry 0・公理
    `[propext, Classical.choice, Quot.sound]` のみ。⑨これを
    `8.2-condV-terminal-slice-Trans-close` へ配線し、原文の条件(V)終切片定理を
    無条件化。⑩ `wnx_seg_transport_W1/W2` と VE を合成して
    `tv_notldjreg_holds` / `tv_notldjleg_holds` を閉じた。既閉の Dichotomy / Trunk /
    LDJB / R3LE と合わせた `condII_masterCF_of_boundaryData` により、CondII の残差は
    **`TvxBoundaryData` 1本のみ**。
    ⑪ ExchV の公開再利用層として `transC2_condV_eq` / `trans_surgery_shared_xv`
    （`8.5-exchV-props`）、`s84x_L_eq_append` / `RTPS_s84x_L` /
    `nextrel0_row0_congr` / `le0_row0_congr` / `seg_to_last_eq_drop`
    （`8.4-oper5-residual`）を追加。⑫ `8.5-exchV-values-close` で Isabelle の
    admissible 経路を移植し、`exchV_Np_adm` / `exchV_PredNp_adm` /
    `exchV_Lp_adm` / `exchV_L1_decomp_adm` を経て `exchV_values_adm` が
    `PredNp` / `Lpv` / `L1v` の3値を一括で閉じる。元の
    `ExchVMValueResidual` は `exchVMvalues_of_nadm` により、訂正済み §8.4 の
    `Rightmost84ReplaceCorrected` と non-admissible 枝だけの
    `ExchVMNadmValueResidual` へ縮約。対象 build 3040 jobs 完走、sorry 0・公理は
    `[propext, Classical.choice, Quot.sound]` のみ。
    ⑬ 続けて Isabelle `nf2x_Lpv` / `nf2x_L1v` を移植。
    `exchV_Lp_of_Np` は `Np` 値から `Lpv` を adm 非依存で導出し、
    `exchV_L1_decomp_of_c2` は `L₁` と host の `Pred` / `j₀` / `Adm(j₀)` を
    接頭辞一致で同定して `c₂(L₁)` から `L1v` を導出する。これにより
    `ExchVMNadmValueResidual` を原子3値 `PredNp` / `Np` / `c₂(L₁)` の
    `ExchVMNadmAtomicResidual` へ縮約。§8.4 訂正済み右端置換と束ねた
    `ExchVMNadmAtomicPackage` を `TerminationResidual.exchVMnadmAtomic` へ配線し、
    旧 `exchVMvalues : ExchVMValueResidual` を置換した。停止性 target build は
    **3125 jobs 完走**、主定理群は sorry 0・公理
    `[propext, Classical.choice, Quot.sound]` のみ。audit 正本は引き続き5フィールド、
    条件(V)フィールド内部だけが4原子（右端置換 + 3 slice 値）へ細化した。
