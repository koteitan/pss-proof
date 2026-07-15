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

## 5. ツリー（task.md と同構造 ＋ 注釈）

凡例: 訂正 = `corrections.md` の A 番号。Isa = `isabelle/` 側の対応補題（証明の設計図）。

- ✅ **定義層 `PSS/`** — 移植元は `isabelle/pss_defs.thy` 一本。ここは「証明」ではなく「転記」。[r9]
  - ✅ `PSS/Defs.lean` — `T_PS`,`Lng`,`entry`,親子(`nextrel0/1`),直系先祖(`le0/le1`),`Pred`,`Derp`,
    `idx1`,`hasParent`,`parent`,基本列 `oper`,`seg`,`FTrace`/`Fdom`/`Fval`,`IncrFirst`。
    `Fval` は停止トレース上の値を読み、停止域外のみ `0` で全域化。その他は **`Bool` 値＝計算可能**。
    `≤_M` は `Relation.ReflTransGen` ではなく**燃料 `Lng M` の再帰**（辺は必ず添字を増やすので十分）。
    **忠実性検証済**: `oper` が `python/red_model.py` と一致。成分 `< 4`・長さ `≤ 4` の
    **全 69,904 列 × n=0..3 = 279,616 回**の評価でチェックサム一致（`142031081`）。
    定義を変えたらこの検証をやり直すこと（`scratchpad/opersum.lean` と同型のチェックサム比較）。
  - ✅ `PSS/Mono.lean` — `zeroT`,`monoT`,`multiT`,`Pcut`,`P`,`IdxSum`,`TrMax`,`Br`,`FirstNodes`,`Joints`。
    `P` の再帰も燃料 `Lng M`（1 段で長さが真に減る）。
    **忠実性検証済**（成分 `< 4`・長さ `≤ 4` の全 69,904 列でチェックサム一致）:
    `monoT`/`multiT`/`P`/`TrMax`/`Br`/`FirstNodes` は全列で一致、`Joints` は
    **定義される 10,224 列**で一致（原文/Isabelle の `THE` は親が一意でないとき未定義。
    「定義されるか」の判定自体も python と完全一致）。
  - ✅ `PSS/Adm.lean` — `nadm`,`adm`,`AdmSet`,`Adm`,`nextAdm`,`Marked`。[r2]
    **忠実性検証済**（`adm`/`Adm` とも全 69,904 列でチェックサム一致）。
  - ✅ `PSS/Red.lean` — `diagSeq`,`Red`,`reduced`(`RT_PS`),`RedCondA`,`RedCondB`。
    Isabelle の停止性測度 `betaM` / `coreReduce` / `muMono` / `nu` を移植し、
    `Red M = RedAux (nu M + 1) M` という燃料方式で全域化した。燃料 0 の戻り値は入力自身。
    `T_PS` 上で燃料が尽きないことは §6.5 `Red-welldefined` で証明する。
    **忠実性検証済**: 成分 `< 4`・長さ `≤ 4` の全 69,904 列で Python 正本と一致
    （チェックサム `505375848`; `python/red_checksum.lean`）。A4 の反例も `#guard` 3 本で固定:
    `Red [(0,0),(0,2)] = [(0,0),(2,2)]`, `Red [(0,0),(2,2)] = [(0,0),(1,1)]`,
    よって `Red` は `T_PS` 上で冪等でない。[r1]
  - ✅ `PSS/Standard.lean` — `STPS`, rank 階層 `SkTPS`, 訂正 A4 用の `anchoredSlice`。
    Isabelle の `inductive_set ST_PS` と `SkT_PS` を直接移植。`anchoredSlice` は
    標準形または簡約単項列の、上段直系先祖に沿った切片として原定義どおりに置いた。[r1]
  - ✅ `PSS/Buchholz.lean` — 相互帰納型 `BT`/`BP`, 辞書式順序, `G_u`, `T_B`, `OT_B`,
    `domB`, 基本列 `operB`, `xseq`, `PB`/`SigmaB`。`dom` は内部で四値タグ `BDom`
    （`∅`/`{0}`/`ℕ`/`T_u`）として計算し、公開時に集合へ戻す。`operB`/`xseq` は
    `(部分項の重み, 呼出し相, xseq 添字)` の辞書式測度で停止性を証明済み。A23 の転置を
    訂正した `x_{i+1}=D_u(b[x_i])` を採用。**忠実性検証済**: 有限指標 0–2、深さ 2、
    principal 数 ≤ 2 の全 1,561 項で Python 正本と一致。定義群チェックサム `177483501`、
    全 2,436,721 項対の順序チェックサム `877667618`（`python/buchholz_checksum.lean`）。[r1]
  - ✅ `PSS/Scb.lean` — `Sym`, `flatBT`/`flatBP`, `RightNodes`, `isPTB_str`,
    `scb_decomp`, 第 0/1 種分解, `MarkedB`。flatten と右端 spine は相互構造再帰、
    principal 項の存在量化を含む分解条件は `Prop` として原定義を直接移植した。[r1]
  - ✅ `PSS/Flat.lean` — 重み付き prefix 非負性から `flatBP` の prefix-free 性を示し、
    `flatBT` の単射性と完全項文字列に付加できる接尾辞が空であることを証明。[r1]
  - ✅ `PSS/Trans.lean` — 実行可能な `unflatBT`/scb 文脈選択、条件 (I)–(VI)、
    燃料付き相互再帰 `Trans`/`Mark` を移植。A9 訂正後の添字を採用。
    **忠実性検証済**: 成分 `< 3`・長さ `≤ 3` の全 819 列について `Trans`、全添字の
    `Mark`、条件 (I)–(VI) が Python 正本と一致（チェックサム `531635224`;
    `python/trans_checksum.{py,lean}`）。kimina はエラー・sorry なし、全 `lake build` 成功。[r1]

- ✅ **§5 定式化** — 全 6 項目を証明済み。[r6]
  - ✅ `5.1-parent-exists` — 燃料付き `le0Aux`/`le1Aux` の添字単調性、行 0 の区間閉性・
    推移性を局所補題として示し、4 分岐を証明。Isa: `m_5_1_parent_exists_1`–`_4`。[r1]
  - ✅ `5.1-parent-basic` — `nextrel0`/`nextrel1` の中間点に対する最小性条件を直接展開して証明。[r1]
  - ✅ `5.1-ancestor-basic` — `le0Aux`/`le1Aux` の鎖に沿う係数増加を燃料帰納法で証明。
    行 1 では行 0 の区間閉性を親存在 (3) から構成。Isa: `m_5_1_ancestor_basic_1`, `_2`。[r1]
  - ✅ `5.1-ancestor-tree` — 行 0 の区間閉性・推移性、行 1 祖先から行 0 祖先への包含を示し、
    行 0/1 の木構造を証明。Isa: `m_5_1_ancestor_tree_1`, `_2`。[r1]
  - ✅ `5.3-pred-is-oper1` — 親あり分岐の `n=1` ブロックを `drop`/`take_add` で始切片へ戻し、
    `Pred M = M.take (Lng M - 1)` と一致させた。A40 は付随型主張のみ。[r1]
  - ✅ `5.4-F-welldefined` — 訂正 **A1**（第 2 引数 `n` → `f(n)`）。停止トレースの
    先頭 1 段を除く操作として domain 同値と値保存を証明。Isa: `m_5_4_F_oper_dom/_val`。[r1]
  - なお §5.3 の型主張 `G ∈ T_PS` は `j₀=0` で偽（訂正 **A40**）。定義層で回避する。

- **§6 ペア数列の基本性質** — Isa: `m_6_*`（`pss_mechanized.thy`）。§6 は全部証明済み。
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
  - §6.5 簡約化 — **ここが A4 の震源**。
    - ✅ `6.5-Red-welldefined` — `P` 成分・`N_J`・`coreReduce` の全再帰先で `nu` の厳密減少を
      証明し、`nu M` より大きい任意の燃料に対する `RedAux` の値の一致と存在一意性を証明。[r2]
    - ✅ `6.5-Red-IncrFirst-invariance` — cut 以上の上段値だけを 1 増加する `bumpAt` を導入し、
      親子・幹・枝・`P`・`redNJ` の対応と三種の再帰 cut 継承を証明。到達する再帰先がすべて
      非複項であることを使う `nu` 強帰納法で `Red (bumpAt X n) = Red X` を示し、
      `coreReduce (IncrFirst M) = bumpAt (coreReduce M) m₁₀` から最終定理を導いた。[r2]
    - ✅ `6.5-Lng-Red-invariance` — `RedAux` の全燃料に一般化し、複項成分・枝成分・
      `coreReduce` の全分岐で長さ保存を帰納証明。[r1]
    - ✅ `6.5-Red-preserves-zeroT` — 長さ1の非零項について `m₁>0` 分岐を直接解析し、
      簡約後の下段左端が非零のままであることから両方向を証明。[r1]
    - ✅ `6.5-monoT-Red` — `coreReduce` の正の `m₁₀` 対角アンカーについて、Red 後の
      branch tail の row-0 値がすべてアンカーより真に大きいことを証明。左端最小性、
      `np ≤ joint+1`、`m₁₀ ≤ joint` を組み合わせ、終切片が `TPS ∧ monoT` であることを導いた。[r1]
    - ✅ `6.5-Red-idempotence` — **原文は `T_PS` で偽（A4）**なので `RT_PS` 上に制限。
      `RTPS M` から定義展開だけで `Red M = M` を取り出して冪等性を示した。原文版の反例
      `M=(0,0)(0,2)` は `by decide` で機械証明し、`Red(Red M) ≠ Red M` を固定した。[r1]
    - `6.5-Red-le-invariance` / `6.5-Red-preserves-monoT` / `6.5-P-Red-equivariance`
      — 同じく `T_PS` では偽。訂正 A4 の `anchoredSlice` に制限。Isa: `m_6_5_Red_le_final`,
        `m_6_5_monoCong`（勝ち筋＝閉形式 `Red M = rebase(M)` に持ち込む）
    - ✅ `6.5-Red-preserves-monoT` — A4 の正確な訂正版に従い `anchoredSlice` 上の同値を証明。
      A4 非依存の前向き定理は `nu` 強帰納法で、core 非 trunk の枝ブロック下界、row-0 shift の
      再帰、正の `m₁₀` 分岐の `monoT_Red_m10pos` を組み合わせた。係留切片が零項または単項で
      あることから逆向きを導き、原文 `TPS` 版の反例 `(0,0)(0,1)` も `decide` で固定した。[r1]
    - ✅ `6.5-P-Red-equivariance` — `anchoredSlice` とその `Red` がともに非複項であることを上の
      零項・単項分解と単項性保存から示し、`P_nonmulti_eq` で両辺を `[Red M]` に簡約した。
      原文 `TPS` 版の同じ反例 `(0,0)(0,1)` も `decide` で固定した。[r1]
    - ✅ `6.5-Red-Pred-commute` — `Pred` による最終列削除を `P` 成分、`coreReduce`、`TrMax`、
      `Br`、`Joints`、`redNJ` へ順に輸送した。core 非 trunk では枝ブロック列の最後だけが、
      長さ 1 なら消滅し、長さ 2 以上なら `Pred` される残差補題を証明。`nu` 強帰納法で複項の
      最終 `P` 成分、各 `redNJ`、非 core の `coreReduce` に帰納仮定を適用し、全分岐を閉じた。
      公開定理 `Red_Pred` は sorry 0、axioms は
      `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは長さ4・成分0..2の全7,380列で
      反例0。全 `lake build` は3,023 jobs成功（キャッシュ済み4.50秒）。
      Isa: `m_6_5_Red_Pred`。[r1]
    - 🚧 `6.5-Red-le-invariance` — `rebaseRow0` による親子関係不変性、係数条件(A)の切片・枝への
      遺伝、core の trunk/非-trunk 復元、正の `m₁₀` の枝ブロック値と終切片再構成を完成。
      長さ強帰納法で Isabelle `m_6_5_Red_rebase` に対応する
      `Red_rebase_nonmulti` を証明し、`RedCondA + nonmulti` 下の `leR` 不変性まで接続済み。
      A4 の無条件 `anchoredSlice` 形に残るのは、§6.6 reduced 及び §6.7 standard の
      `RedCondA` 前提鏖のみ。[r0]
  - ✅ `6.6-one-column` — 任意の単要素に対し `Red [(a,b)] = [(b,b)]` を閉形式から導き、
    長1の簡約形が対角単要素と一致することを証明。Isa: `m_6_6_oneColumn`。[r1]
  - ✅ `6.6-reduced-slice` — `Red_Pred` から簡約形の `Pred` 閉性 `RTPS_Pred` を導き、
    `Pred` の反復が `take (Lng M-k)` と一致することを帰納証明した。訂正 A5 の始点 `j₀=0`
    の下で始切片を反復 `Pred` と同定し、簡約性を輸送。実際には任意の非空始切片について成立する。
    公開定理 `RTPS_slice` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルの簡約始切片447件で反例0。
    全 `lake build` は3,024 jobs成功（キャッシュ済み2.24秒）。
    Isa: `herd_6_6_reduced_slice`。[r1]
  - `6.6-ancestor-slice-Red-IncrFirst` — 訂正 **A2**（指数の添字 `m` が未定義 → `j'₀`）
    ＋ 訂正 **A5**（前提 `j′₀ ≤ TrMax` が弱すぎる。反例 113 件）
  - ✅ `6.6-RT-image-of-Red` — 訂正 **A41** に従い、`Red` を `T_PS` に制限した像を
    `RedImage` として定義し、成立する包含 `RT_PS ⊆ RedImage` を証明。逆包含は
    `(0,0)(0,2)` の像 `(0,0)(2,2)` が非簡約である反例を `decide` で固定した。[r1]
  - 🚧 `6.6-reduced-iff-condAB` — §6.6 のキーストーン。Isa: `reduced ⟺ RedCondA ∧ RedCondB`（無条件）。Lean では逆向き `RedCondA∧RedCondB → RTPS` を完成済み。複項は全 `P` 成分が真に短いことから長さ強帰納し、非複項は `Red_rebase_nonmulti` へ落とした。併せて、末尾未満の `take` が `nextR` と親を保つことから `RedCondA_Pred` / `RedCondB_Pred` を証明済み（sorry 0）。残りは順向き `RTPS → RedCondA∧RedCondB` の mono/core 部分。
    `6.6-P-condAB` で `P` ブロック左端を親辺が越えないことを
    `P_leftend_lmin + ancestor_basic_1` から証明し、親のオフセット対応、
    `RedCondAB_P_component`, `RedCondAB_of_P_components` を完成。A3 の
    `RTPS_iff_P_components` と組み合わせ、多成分の再帰粘合補題
    `RTPS_iff_condAB_multi` まで接続済み。残件は非零単項の前向き
    `RTPS → RedCondA`。[r0]
  - ✅ `6.6-condAB-coeff` — 親なし上段係数の零性を `parent_exists_1`、親なし下段係数の零性を
    `P` 成分の左端と成分内単項性から証明。燃料付き `le1Aux` の親辺延長も機械化し、条件(A)下の
    上段添字上界、条件(B)を加えた上下段比較、祖先関係に欠損がある場合の狭義添字上界を
    強帰納法でまとめた。Isa: `m_6_6_condAB_coeff`, `condAB_row1_noparent_zero`。[r1]
  - ✅ `6.6-Red-leftend` — `nu` 強帰納法で `Red` の零・複項・core・row-0 shift・正係数の全分岐を
    解析し、row-1 左端の保存を証明。先頭対角 prefix については `coreReduce` 上の連続 row-1 辺を
    構成して `TrMax` まで持ち上げ、正係数出力の添字を直接計算して prefix の最終列を固定した。
    Isa: `m_6_6_Red_leftend_1`, `_2`。[r1]
  - ✅ `6.6-reduced-leftend` — `bumpAt` の cut 不変性を対角 prefix より右だけに反復して
    `Red (diagSeq 0 (m₁₀-1) ++ M) = diagSeq 0 (m₁₀-1) ++ Red M` を証明。
    `Red (coreReduce M)` の対角 prefix / `Red M` suffix 分解、一般の guarded prefix の単項性、
    prefix 左端が正の場合の共通対角 prefix 消去を組み合わせ、訂正後の
    `RTPS_diag_prefix` を完成した。Isa: `m_6_6_Red_diag_prefix`, `m_6_6_reduced_leftend`。[r1]
  - ✅ `6.6-P-preserves-reduced` — 複項分岐の `Red M = flatten (map Red (P M))` と `P_concat`を
    組み合わせ、`Lng_Red_invariance` が与えるブロック長プロファイルから連結前のリストを
    復元する補題を証明。`Red_P_stable` と
    `RTPS M ↔ ∀ J < (P M).length, RTPS ((P M).getD J [])` の両方向を完成した。
    Isa: `m_6_6_Red_P_stable`, `m_6_6_P_reduced`。[r1]
  - ✅ `6.6-Red2` — Isabelle `y3r_RED2` を移植。非複項入力の `Red` に対し、
    対角幹、枝ブロック、`TrMax` / `Br` / `Joints` / `branchNP` / `redNJ` の二回目不変性を
    構成し、子枝の強帰納から `Red_nonmulti_RTPS` を完成した。また非複項・内部狭義
    row-0 最小・左端非増加ブロック列を `P` が元の境界で再分解する補題と、
    `Red M` の全 `P` 成分が対角左端を持つ不変条件 (D) を接続。公開定理
    `Red2 : TPS M → RTPS (Red (Red M))` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `y3r_RED2`。[r1]
  - ✅ `6.7-standard-prefix` — `STPS ⊆ TPS` を生成規則で証明し、欠落列数に関する強帰納法を実装。
    真の始切片で `Pred M = oper M 1` を使って標準形を一段下げ、`Pred = take (Lng-1)` により
    元と一段下の始切片が一致することを示した。Isa: `m_6_7_standard_prefix`。[r1]
  - ✅ `6.7-standard-P-components` — rank 階層の単調性 `SkTPS k M → SkTPS (k+1) M` を、
    対角列を一列延長して `Pred = oper _ 1` とする基底証人から証明。rank の外帰納と長さの
    内強帰納を組み合わせ、非複項分岐は `nonmulti_fseq_1/2`、複項分岐は `P_fseq_1/2` で処理した。
    末尾再帰では `Pcut > 0` から先頭ブロック列の正長さを導き、厳密な長さ減少を確立した。
    Isa: `SkT_PS_mono`, `m_6_7_standard_P_components`。[r1]
  - `6.7-standard-reduced` — `ST_PS ⊆ RT_PS`。Isa: `m_6_7_*`（e096355）。
    **`has_gz⟹D` / GTWF ルートは偽。escape readback で gate-free 化したのが正解**
  - `6.8-standard-slice-Br-descending` — 訂正 **A7**（「`M′` が標準形」は偽。`Br(M′)` が降順が正）
    ＋ 訂正 **A8**（`j₁` の式が off-by-one）

- **§7 Buchholz の表記系への翻訳** — Isa: `m_7_*`。§7 全節証明済み。
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
  - `7.1-buchholz-wf` 📘 — [Buc1] Lemma 2.2。原文も引用のみ。**Lean でも引用（`axiom`）でよいか要判断**。
    Isabelle 版は `sorry` 引用のまま（停止性定理はこれに依存しない形になっている）。
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
  - ✅ `7.2-scb-compose` — principal 成分内の scb 分解を外側へ結合する第 1 主張を、
    文字列連結の結合則と右括弧 tail の閉性から直接証明。第 2 主張は訂正 A11 に従い
    `isPTB_str c` を仮定した `scb_compose_dprin` として証明し、無条件版が
    `t=0, c=[.zero]` で偽になる反例も固定した。Isa: `m_7_2_scb_compose`, `scbcomp_compose2_PT`。[r1]
  - ✅ `7.2-scb-triviality` — `MarkedB` の witness と `flatBT` 単射性を使い、`t=c`、
    全分解の前後文脈が空であること、空前置部の分解が存在することの三条件を同値化。
    接尾辞側の逆向きは完全項文字列の prefix-free 性で閉じた。Isa: `m_7_2_scb_triviality`。[r1]
  - ✅ `7.2-scb-unique` — 固定した `c` に対する `(s,b)` の一意性を末尾の連続右括弧数で証明。
    `RightNodes` suffix の開始位置を、kind0 では長さ2、kind1 では「末尾未満となる最後の index」から
    固定し、両種の分解全体の一意性と非零項での排他性を得た。定義域側は有限タグ `rnDom` を導入し、
    `T_B` 上で `domTag t = rnDom (RightNodes t)` を相互構造帰納、四タグの集合値の相異を具体的 witness
    で証明した。任意の右端 suffix の scb occurrence 実現と、自然数形の再帰的な kind0/kind1 構成を
    結合して `domB t = NatSet ↔ scb_kind0_able t ∨ scb_kind1_able t` を閉じた。訂正 A14 に従い
    非零条件を明記し、零項で両種が成立する原文反例も固定。Isa: `m_7_2_scb_unique_*`。[r3]
  - ✅ `7.2-scb-replaceable` — `flatBP` の prefix 重みで符号境界をまたぐ occurrence を排除し、
    項・principal・principal 列の相互構造帰納で任意の完全 principal 文字列の置換手術を証明。
    訂正 A12 に従い「置換後が principal、または全体が零文字列」の形を閉じ、原文の
    `t₀=c₀=0`・multi `c₁` 反例も固定した。Isa: `gensurg_main`, `y3u_p_7_2_scb_replaceable`。[r1]
  - ✅ `7.2-add-scb` — 加法を principal リスト連結として解析し、末尾 principal の marked 性と
    同じ scb 文脈での末尾置換を証明。一般置換手術で外側 `D_v(t+c)` の像を構成し、訂正 A13 の
    occurrence alignment 前提下で第 3 主張を閉じた。非 alignment 原文の具体反例も証明。
    Isa: `m_7_2_add_scb_conj1/2/3_uncond`。[r1]
  - ✅ `7.2-RightNodes-subexpr` — 右端 principal spine の底の零引数だけを置換する `spineSub` を
    項・principal・principal 列の相互構造再帰で定義。flatten の最後の `.zero` を挟む canonical
    prefix/suffix 分解を同じ構造帰納で証明し、全 `.rp` tail との位置合わせから置換後も同じ
    `(s,b)` 文脈を持つことを示した。`T_B`、最上位 principal 数 `numNat = Lng (PB ·)`、および
    `RightNodes (spineSub t₀ t) = RightNodes t₀ ++ RightNodes t` の保存則を結合し、`[v]` の前後を
    なす pair の存在一意性まで閉じた。Isa: `m_7_2_RightNodes_subexpr`。[r1]
  - `7.2-scb-*` — 訂正 **A12**（選言が零項で空回り）、**A13**（系(3) 出現位置は同一とは限らない）
  - ✅ `7.2-scb-fseq` — (1-1) の末尾 successor-body 計算を `bOperCore` の再帰式から直接証明し、
    (1-2) は scb occurrence を囲む任意の右端 spine を保存する `NatSet` domain 輸送として閉じた。
    第 3 主張では `T_{v-1}` domain 用の同型輸送と、訂正 **A23** の
    `x_{i+1}=D_{v-1}(body[x_i])` 塔を証明。原文の二重 scb 仮定だけから marked principal
    `c₂=D_u(body)`、`u<v`、`domTag body=.below(v-1)` を `RightNodes` の kind-1 境界条件で復元し、
    記事どおり `(s₀D_{v-1})^(n+1) 0 b₀^(n+1)` を得た。途中の塔単体は `n` 層だが、
    `operB body` が最後の 1 層を加えるため **A24 による指数変更は不要**。独立 Python モデルで
    記事式 112/112（一方が非空の文脈 60 例を含む）一致、塔単体式は同文脈で 0/60 と確認した。
    `bOperCore` の再帰式と `rnDom`/末尾 scb 構文補題を再利用可能 API として公開（定義値は不変）。
    Isa: `m_7_2_scb_fseq_succ`, `m_7_2_scb_fseq_scb`,
    `m_7_2_scb_fseq_kind1_general`。[r1]
  - ✅ `7.3-two-column` — `RTPS_mono_head_eq` で先頭を `(v,v)` に固定し、燃料付き
    `TransAux` / `MarkAux` の一列計算と自明 scb 文脈を直接評価して、原文の五結論
    （`Trans`、両列の `Marked`、`Mark 0`、`Mark 1`）を証明した。一般の未完成な
    `RTPS → RedCondA` は使わず、`RTPS_diag_prefix` で `0,…,v` を左へ補った簡約核列を作り、
    `v<b` の場合は末尾が幹上にあることと `Red_core_prefix_diag` から専用係数則
    `b=v+1` を導いた。公開定理 `two_column` / `two_column_Trans` /
    `two_column_Marked` / `two_column_Mark` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Python 正本では成分 `<6` の全二列から得た
    `RTPS ∧ monoT` 20件で五結論・専用係数則とも反例0、既存の全819列チェックサムも
    `531635224` のまま一致。全 `lake build` は 3,017 jobs 成功。
    Isa: `m_7_3_twoColumn_Trans`, `m_7_3_twoColumn_Marked`,
    `m_7_3_twoColumn_Mark`, `p_7_3_twoColumn`。[r1]
  - ✅ `7.3-Trans-welldefined` — 訂正 **A15** の簡約核部分として、実行可能 parser の完全性と
    `unflatBT (flatBT t) = t`、scb 文脈選択の健全性、置換後の `T_B` / principal /
    `MarkedB` 保存を証明。`Pred` と複項の始切片・右端成分の長さが真に
    減少することから、`TransAux` / `MarkAux` の十分な燃料間での値の一意性を
    同時強帰納で閉じた。さらに単列、単項の零/非零 `Trans Pred`、複項の
    全分岐で値不変条件 `Trans_Mark_invariant`を証明し、`Trans M ∈ T_B`、
    `Mark M m ∈ T_B`、`(Trans M, Mark M m) ∈ MarkedB` を `RTPS` 上で公開定理化。
    sorry 0、axioms は `[propext, Classical.choice, Quot.sound]`。`scbContexts` の比較を
    命題的等値比較に強化した後も、Python/Lean の全 819 列チェックサムは
    `531635224` で一致。全 `lake build` は 3,025 jobs 成功（7.31秒）。
    RED2 完成後、`TransAux` / `MarkAux` を同時に二段展開し、同長の `Red` 軌道から
    `Red (Red M)` の簡約核へ輸送。公開定理 `Trans_Mark_welldefined` により、
    原文の非簡約再帰式を全 `TPS` で満たす一意な値を得た。sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `m_7_3_Trans_welldef`,
    `m_7_3_Mark_welldef`, `Trans_Mark_invariant_aux`。[r3]
  - ✅ `7.3-Trans-IncrFirst-Red` — 訂正 **A16** の先頭 `P` 成分非零条件下で、
    `P M = P (take (Pcut M) M) ++ [drop (Pcut M) M]` に沿う長さ強帰納を行い、
    `Trans M = SigmaB ((P M).map transPComponent)` を証明した。複項枝では始切片の
    `RTPS`、右端成分の `RTPS` と `zeroT J ↔ J=[(0,0)]` を使って公開再帰式へ接続する。
    (1) の `Red` / `IncrFirst` 不変性は、1回目の `Red` が未簡約でも燃料を2段展開して
    同じ `Red (Red M)` 上の値へ帰着する証明を `Red2` と接続し、全 `TPS` で成立させた。
    公開定理 `Trans_Red` / `Trans_IncrFirst` / `Trans_IncrFirst_Red` /
    `Trans_P_equivariance` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `m_7_3_Trans_Red`,
    `m_7_3_Trans_IncrFirst`, `m_7_3_Trans_P_equivariance`。[r1]
  - ✅ `7.3-Mark-IncrFirst-Red` — `TransAux_MarkAux_fuel_irrel_RTPS` の `MarkAux` 側を
    RED2 軌道の二段展開に接続し、全 `TPS` 上で `Mark_Red` と
    `Mark_IncrFirst` を証明。P 成分式は簡約形の複項入力に対し、最終成分を
    `drop (Pcut M) M`、添字 offset を `Pcut M` とする訂正形で完成した。原文の
    `Lng M - Lng(component) - 1` は off-by-one。公開定理は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。Isa: `m_7_3_Mark_Red`,
    `m_7_3_Mark_IncrFirst`, `m_7_3_Mark_P_invariance`。[r1]
  - ✅ `7.3-Trans-preserves-zeroT` — 順向きは `Trans_Red` と `Red_zero_mr` で
    `[(0,0)]` の直接計算へ帰着。逆向きは `Red_preserves_zeroT` を二回適用し、
    RED2 で得た簡約核の `Trans_Mark_invariant` が与える非零性に反証させた。
    `Trans_preserves_zeroT : TPS M → (zeroT M = true ↔ Trans M = BZero)` は
    sorry 0、axioms は `[propext, Classical.choice, Quot.sound]`。
    Isa: `m_7_3_Trans_zeroT`。[r1]
  - ✅ `7.3-c1-c2-order` — `c₂` の全定義枝が単一 principal であることと、非零 `t₁` の
    marked scb 成分から `c₁` の単項性を復元した。狭義不等式の条件(I)/(III)/(V)枝と通常枝は
    Buchholz 項の辞書式順序・加法で閉じ、条件(VI)枝には `flatIdx` と suffix 最大値
    `row1Bound` を導入。`Mark` の長さ強帰納により、置換 scb 内を含む全 `D` 添字が
    対応する第1行 suffix の最大値以下であることを証明し、`Adm` から右端親までの
    `nextrel1` 連鎖と `j′+1=j₁` により先頭添字の狭義比較へ落とした。公開定理
    `transC1_lessBT_transC2_full` と記事の3結論を束ねる `c1_c2_order` は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは成分 `<3`・長さ `≤3` の
    対象21例で反例0、既存の全819列チェックサムも Lean/Python とも `531635224` で一致。
    全 `lake build` は3,030 jobs成功（6.10秒）。Isa: `p_7_3_c1_c2`,
    `transC1_lessBT_transC2_full`, `NAbound_holds`。[r2]
  - ✅ `7.3-Pred-Trans-descend` — まず flatten の一意可読性に沿う BT/BP/principal-list の
    同時構造帰納法により、任意の完全 principal code を狭義に大きい code へ置換すれば
    包含項全体も狭義増加する `flat_principal_replacement_lt` を証明した（記事の
    `scbext_lessBT` より強く、共通 suffix の all-`)` 条件を実際には要しない）。単項分岐は
    `Trans_Mark_mono_equations` の零枝を直接計算し、非零枝を `replaceScb_spec` と完成済み
    `transC1_lessBT_transC2_full` で閉じた。複項分岐は `P_Pred_multi` から、末尾 `P` 成分
    `J` の長さが 1 より大きいとき `Trans(Pred M)=Trans A+Trans(Pred J)`（零成分時は
    `D₀0`）を復元し、`Lng J` の強帰納法と `addBT_lt_right_bf` を適用した。これで
    `RTPS` 版を得た後、`Red_Pred`、`Trans_Red`、`Red2` により記事どおり任意の `TPS` へ
    持ち上げた。公開定理 `Pred_Trans_descend` / `m_7_3_Pred_Trans_descend` は sorry 0、
    axioms は `[propext, Classical.choice, Quot.sound]`。独立 Python モデルは成分 `<3`・
    長さ `≤4` の対象7,371列で反例0、Lean 内監査も長さ `≤3` の対象810列で反例0。
    全819列の既存 Trans/Mark チェックサムは Lean/Python とも `531635224` のまま一致し、
    全 `lake build` は3,031 jobs成功（3.70秒）。Isa: `Trans_Pred_multi_last`,
    `m_7_3_Pred_Trans_descend`, `scbext_lessBT`。[r1]
  - ✅ `7.3-Mark-rightmost1` — 訂正 **A17**。まず `m≤m'` の簡約基点に対して
    `(Mark M m, Mark M m')∈MarkedB` となる入れ子補題を長さ強帰納で証明した。mono の
    surgery 枝では、`Pred M` 上の帰納仮定から `c₁` の scb 文脈が必ず存在することを示し、
    二つの `replaceScb_spec` を `scb_compose` と固定中央文字列の一意性で同期した。右端枝は
    `c₂` に最終列の `D` が現れることを全4定義枝で構成した。これを使い、`c₂` の body が
    常に非零、したがって flatten 長が3以上であることから、右端より前の `Mark` が長さ2の
    `D_(entry M 1 m) 0` にはなれない `Mark_tail_nonzero` を得た。順向きは mono の公開再帰式と
    multi の最終 `P` 成分への強帰納で閉じ、補正済み iff
    `m_7_3_Mark_rightmost1` を完成。原文が `[(0,0)]` で失敗することも形式的反例として固定した。
    公開定理は sorry 0、axioms は `[propext, Classical.choice, Quot.sound]`。独立 Python 監査は
    成分 `<3`・長さ `≤4` の簡約286列、基点509件、入れ子770件で反例0。Lean 内監査は全819列
    （簡約62列、基点101件、入れ子144件）で全4検査が反例0。既存の全819列チェックサムも
    Lean/Python とも `531635224` のまま一致し、全 `lake build` は3,032 jobs成功（5.8秒）。
    Isa: `Mark_MarkedB_nest`, `Mark_rightmost1_forward`, `Mark_tail_nonzero`,
    `m_7_3_Mark_rightmost1`。[r1]
  - ✅ `7.3-Trans-preserves-monoT` — 訂正 **A16**。原文は先頭 `P` 成分が零項のとき偽だが、
    `RTPS M` かつ `zeroT ((P M).getD 0 []) = false` の訂正域では
    `monoT M ↔ Lng (PB (Trans M)) = 1` を証明した。順向きの中核
    `Trans_monoT_principal` は長さ強帰納で、mono の零前駆枝を直接 principal とし、surgery 枝では
    `Pred M` の単項性を `monoT_Pred_long` へ下ろし、帰納仮定の principal `t₁` に
    `replaceScb_principal` を適用した。逆向きは対偶を取り、multi 再帰式
    `Trans M = Trans A + (D₀0 または Trans J)` の左右がとも非零であることを先頭 `P` 非零条件と
    `Trans_preserves_zeroT` から示し、`PB` 長が2以上になるため1と矛盾させた。原文反例
    `M=[(0,0),(0,0)]`（非 mono だが `Trans M=D₀0`）も kernel 計算で固定した。公開定理は sorry 0、
    axioms は `[propext, Classical.choice, Quot.sound]`。独立 Python 監査は成分 `<3`・長さ `≤4` の
    簡約286列中の訂正対象267列で反例0、Lean 内監査も全819列中の簡約62列・対象57列で反例0。
    全819列チェックサムは `531635224` のまま、全 `lake build` は3,033 jobs成功（2.7秒）。
    Isa: `Trans_PT_single`, `m_7_3_Trans_monoT`。[r1]
  - ✅ `7.4-Adm-nextAdm` — Isabelle の `nextAdm` を「許容な真の祖先で、中間に許容な
    祖先がない」という有限 Bool 関係として `PSS/Adm.lean` に追加した。構造補題として
    `Adm M j` が `j` の第1行祖先となる `adm_row1_ancestry` と、第1行祖先が第0行祖先でもある
    `row1_implies_row0` を公開し、親へ至る祖先鎖と親の最大性から原文どおり
    `Adm_nextAdm` を証明した。公開3定理は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python 監査は成分 `<3`・長さ `≤4` の
    全7,380列、親を持つ5,440件（第0行4,023・第1行1,417）で反例0。Lean 内監査も全819列、
    対象508件（第0行378・第1行130）で反例0。全 `lake build` は3,034 jobs成功（定義層からの
    再構築を含め約12秒）。Isa: `m_7_4_Adm_nextAdm`。[r1]
  - ✅ `7.4-Trans-nextAdm` — 訂正 **A45**。一意な最終列の `nextAdm` 親を
    `Classical.choose` で取り、`nextAdm` の4条件からその列が `Marked` かつ最終列未満であることを
    展開して、完成済み `Trans_Mark_Pred` へ直接帰着した。原文 `TPS` 版の反例
    `[(0,0),(0,1),(1,2),(1,0)]` は、親が一意に `1` であること、4個の `Trans`/`Mark` 値、
    `Pred` 側の一意な scb 文脈を kernel 計算で固定し、同じ文脈が `M` 側の flatten 等式と
    矛盾するところまで形式証明した。公開定理と反例は sorry 0、axioms は
    `[propext, Classical.choice, Quot.sound]`。独立 Python 監査は成分 `<3`・長さ `≤4` の
    全7,380列中、簡約286列・一意親188件で反例0。Lean 内監査も全819列・一意親35件で反例0、
    同じ非簡約反例の共通 scb 文脈が0件であることを確認した。Isa:
    `m_7_4_Trans_nextAdm`。[r1]
  - `7.4-Mark-nextAdm` — 訂正 **A18**（祖先 `j` に `(M,j) ∈ Marked` が要る）
    ＋ **A47**（原文の `T_PS` 版は偽）。Isa: `y6z_7_4_Mark_nextAdm_TPS_false`
  - ✅ `7.4-Trans-Mark-Pred` — 訂正 **A46**。`Lng M` の強帰納法で共通 scb 文脈の存在を
    証明した。mono の零前駆枝は自己分解、非零 surgery 枝は `c₁→c₂` の外側・内側の
    `replaceScb_spec` を `scb_compose` と無条件一意性で同期した。multi 枝では最終 `P` 成分 `J`
    へ帰納し、`Mark_Pred_multi_last` を新たに証明して `Trans_Pred_multi_last` と揃え、
    `Trans A` が零なら文脈をそのまま輸送、非零なら `scb_addBT_left_74` で両側へ同じ prefix を
    持ち上げた。最後の一意性は `Trans(Pred M)` 側の固定中央文字列一意性だけで閉じた。
    公開定理は sorry 0、axioms は `[propext, Classical.choice, Quot.sound]`。独立 Python 監査は
    簡約286列の proper marked 224件、Lean 内監査は39件で反例0。A45 と共通の非簡約反例も
    Lean の `Trans_nextAdm_original_counterexample` が形式的に排除する。全 `lake build` は
    3,036 jobs成功（キャッシュ済み1.00秒）。Isa: `Mark_Pred_multi_last`,
    `scb_addBT_left`, `m_7_4_Trans_Mark_Pred`。[r1]
  - `7.4-Mark-Trans-repr` — §7.4 のキーストーン。Isa: `m_7_4_Mark_Trans_repr`（無仮定・`sorry`0）
  - **§7.4 の `Mark` は簡約形の全列で principal-or-zero**（Isa: `y3y_Mark_princ`）。
    これは原文にない我々の補題だが、§7.4 を `RT_PS` 上で回すのに効く。**Lean でも先に用意しろ。**

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
  - `8.1-condI-III-c1-around` — 訂正 **A20**（補題(1) は非簡約 1 列切片で偽）
    ＋ **A21**（補題(5) の条件(III)で `j₀ᴺ = j′₀` が偽）
  - `8.2-*` — `LastStep` の添字は A9 で訂正済みの形を使う。
    Isa の注意: `Pred_oper0` は標準入力で偽（反例 `M=(0,0)(1,1)(2,1)`）だが**定理は健全**
    （`Σ_B` 降下和ルートで回避）。**原文 §8 の証明には gap があるが、定理は真。**
  - `8.3-kind0-base-basepoint` — 訂正 **A22**（1 文に誤植 3 つ。反例あり）
  - `8.4-rightmost-replace-Trans` — 訂正 **A30**（scb 分解が偽。長さ勘定で決まる）
    ＋ **A31**（補題(5-3) のガード欠落）
  - `8.5-Joints-FirstNodes-basic` — 訂正 **A29**（補題(5) が `n=1` で偽）
  - `8.5-*` — **最難所**。Isa の keystone は
    `bpHeadT(Trans(slice@B)) = C(bpHeadT(Trans slice))`（depth-shift self-similar）。
    13 個の死路が `isabelle/memo.md` に列挙してある。**着手前に必ず読め。**
  - `8.7-fseq-descend` — Isa: `m_8_7_fseq_descend_dispatcher`（7 つの交換則に還元される）
  - `8.7-termination` ★ — Isa: `y5_PSS_wf` / `y5_Fdom`。ここに全部が集まる。
