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
  - 🚨 `7.1-buchholz-wf` — [Buc1] Lemma 2.2。原文は引用のみだが **Lean でも自前証明すると
    決定（2026-07-16 ユーザー）**。Isa: `y4_buc1_2_2_OT_B_wf`（layerC:13700、sorry 0・仮定 0。
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
  - ✅ §7.4 許容的親子関係 — 訂正 A18・A45・A46・A47 に従い、必要な命題を `RTPS` と
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
  - 🚨🤖 `8.2-subexpr-component-Pred` — Isa: `m_8_2_subexpr_component_Pred`
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
    **wid 残 3 本（wid_step/wid_of_predRN/wid_of_predwid）の blocker**:
    Admpos body-split engine `trans_admpos_body_split`（layerB:26573）が Lean 未移植
    → C-3 で先に移植する。
    🚨**教訓（2026-07-17、2 回踏んだ）**: ①Fable 月次上限で agent は死ぬが
    **ディスクの成果物は生きる**。今回 4 本とも「骨格」ではなく**完成済み**で、
    checker を回す前に死んだだけだった ②私の「sorry 1 個残存」判定は
    **`grep -c sorry` が docstring の「状態: ✅ sorry 0」を拾った偽陽性**。
    残 sorry は必ず `check_lean.py` で判定せよ（grep 禁止）③**workflow 走行中に
    `lake build` するな**——glob が in-flight の書きかけを拾って必ず失敗する。
    個別モジュール指定（`lake build «8».«8.2-subexpr-adm0» …`）なら安全。
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
  - 🚨🤖 `8.2-condV-terminal-slice-Trans` — p 文 = pss_paper:1607、Isa:
    `m_8_2_condV_terminal_slice_Trans`（layerB:77102、~49 行。`_modVE` 版 61039 も）。
    今日 ✅ の `condV_rightmost_parent` を消費する自然な次項目。Wave D で agent。
  - 🚨🤖 `8.4-rightmost-nonadm-ancestor` — p 文 = pss_paper:1931、Isa:
    `m_8_4_rightmost_nonadm_ancestor`（layerB:40628、~256 行）。Wave D。
  - 🚨🤖 `8.4-oper-basic` — p 文 = pss_paper:2017、Isa: `m_8_4_oper_basic_part1`
    （layerB:13897、~60 行）＋後続 part。Wave D。
  - 🚨🤖 `8.5-Joints-FirstNodes-basic` — 訂正 **A29**（補題(5) が `n=1` で偽）。
    p 文 = pss_paper:2098、Isa: `m_8_5_Joints_FirstNodes_basic`（layerB:40416、
    ~212 行）＋`_condV` 版（60636）。Wave D。
  - `8.5-*` — **最難所**。Isa の keystone は
    `bpHeadT(Trans(slice@B)) = C(bpHeadT(Trans slice))`（depth-shift self-similar）。
    13 個の死路が `isabelle/memo.md` に列挙してある。**着手前に必ず読め。**
  - 🚨 `8.3-Trans-fseq-condII` ⛔8.7-fseq-descend — 原文命題は (1)-(3) が Trans 再帰の
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
  - `8.7-fseq-descend` — Isa: `m_8_7_fseq_descend_dispatcher`（7 つの交換則に還元される）
  - `8.7-termination` ★ — Isa: `y5_PSS_wf` / `y5_Fdom`。ここに全部が集まる。
