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

- ✅ **定義層 `PSS/`** — 移植元は `isabelle/pss_defs.thy` 一本。ここは「証明」ではなく「転記」。[r8]
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
  - ✅ `PSS/Adm.lean` — `nadm`,`adm`,`AdmSet`,`Adm`,`Marked`。
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
    - `6.5-Red-idempotence` — **原文は `T_PS` で偽（A4）**。`RT_PS` 上でのみ真。
      反例 `Red((0,0)(0,2)) = (0,0)(2,2)`, `Red((0,0)(2,2)) = (0,0)(1,1)`。
      **Lean では `decide` で反例定理を書ける。最初にこれを書け**（下流の議論の土台になる）。
    - `6.5-Red-le-invariance` / `6.5-Red-preserves-monoT` / `6.5-P-Red-equivariance`
      — 同じく `T_PS` では偽。定義域を `RT_PS` に制限（A4）。Isa: `m_6_5_Red_le_final`,
        `m_6_5_monoCong`（勝ち筋＝閉形式 `Red M = rebase(M)` に持ち込む）
  - `6.6-ancestor-slice-Red-IncrFirst` — 訂正 **A2**（指数の添字 `m` が未定義 → `j'₀`）
    ＋ 訂正 **A5**（前提 `j′₀ ≤ TrMax` が弱すぎる。反例 113 件）
  - `6.6-RT-image-of-Red` — 訂正 **A41**（`RT_PS = Im(Red)` は偽）。Isa: `m_6_6_*`
  - `6.6-reduced-iff-condAB` — §6.6 のキーストーン。Isa: `reduced ⟺ RedCondA ∧ RedCondB`（無条件）
  - `6.7-standard-reduced` — `ST_PS ⊆ RT_PS`。Isa: `m_6_7_*`（e096355）。
    **`has_gz⟹D` / GTWF ルートは偽。escape readback で gate-free 化したのが正解**
  - `6.8-standard-slice-Br-descending` — 訂正 **A7**（「`M′` が標準形」は偽。`Br(M′)` が降順が正）
    ＋ 訂正 **A8**（`j₁` の式が off-by-one）

- **§7 Buchholz の表記系への翻訳** — Isa: `m_7_*`。§7 全節証明済み。
  - `7.1-buchholz-wf` 📘 — [Buc1] Lemma 2.2。原文も引用のみ。**Lean でも引用（`axiom`）でよいか要判断**。
    Isabelle 版は `sorry` 引用のまま（停止性定理はこれに依存しない形になっている）。
  - `7.1-buchholz-fseq-lt` / `-closed` — Isa: `m_buc1_3_2a_*`, `b1x_operB_dom_all`（完全証明済み）
  - `7.2-scb-triviality` — 訂正 **A11**（前提に単項性が要る）
  - `7.2-scb-*` — 訂正 **A12**（選言が零項で空回り）、**A13**（系(3) 出現位置は同一とは限らない）
  - `7.2-scb-fseq` — 訂正 **A23**（脚注[30] の基本列の転置）。Isa: `m_7_2_scb_fseq_kind1_general`
  - `7.3-Trans-welldefined` — 訂正 **A15**（原文の測度は下がらない）。
    Isa: `Trans_Mark_invariant_aux`（停止性＋値域 `(Trans,Mark) ∈ T_B^Marked`、域は `RT_PS`）
  - `7.3-Mark-rightmost1` — 訂正 **A17**（零項基底で例外。反例あり）
  - `7.3-Trans-preserves-monoT` — **原文は偽（A16）**。反例 `(0,0)(0,0)`。
    ❌ 停止性には不要。反例だけ機械証明して先に進む。
  - `7.4-Mark-nextAdm` — 訂正 **A18**（祖先 `j` に `(M,j) ∈ Marked` が要る）
    ＋ **A46/A47**（原文の `T_PS` 版は偽）。Isa: `y6z_7_4_Mark_nextAdm_TPS_false`
  - `7.4-Trans-nextAdm` — 訂正 **A45**（`T_PS` で偽）
  - `7.4-Mark-Trans-repr` — §7.4 のキーストーン。Isa: `m_7_4_Mark_Trans_repr`（無仮定・`sorry`0）
  - **§7.4 の `Mark` は簡約形の全列で principal-or-zero**（Isa: `y3y_Mark_princ`）。
    これは原文にない我々の補題だが、§7.4 を `RT_PS` 上で回すのに効く。**Lean でも先に用意しろ。**

- **§8 停止性** — Isa: `m_8_*` ＋ `layerC`。**停止性 = 「基本列の降下性」＋「`OT` 所属」の 2 本柱**。
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
