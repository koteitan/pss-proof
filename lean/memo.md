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
  - `6.8-standard-slice-Br-descending` — 訂正 **A7**（「`M′` が標準形」は偽。`Br(M′)` が降順が正）
    ＋ 訂正 **A8**（`j₁` の式が off-by-one）

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
  - ✅ §7.2 scb 分解 — 全7項目を証明済み。[r9]
  - ✅ §7.3 翻訳写像 — 全9項目を証明済み。[r12]
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
  - ✅ `7.4-Mark-nextAdm` — 訂正 **A18**（祖先 `j` に `(M,j) ∈ Marked` が要る）
    ＋ **A47**（原文の `T_PS` 版は偽）。両列 `m≤m'` の共通 scb 位置を示す
    `Mark_nest_common_marked` を公開した。`m=m'` は `Mark` が principal-or-zero であることから
    自己分解し、`m<m'` は両端の `Trans_Mark_Pred` 文脈に
    `Mark_MarkedB_nest` を合成し、無条件 scb 一意性で `Pred M` 側と `M` 側の位置を
    同期した。本体は一意な `nextAdm` 親が `Marked` で最終列未満であることを定義から
    取り出し、第0行祖先関係を自然数順序に落として補助定理へ帰着した。
    A18 の簡約反例 `[(0,0),(1,1),(2,2),(3,1)]` は列 `1` が親 `2` の祖先だが
    未許容であること、A47 の非簡約反例
    `[(0,0),(4,2),(2,6),(4,2),(8,4),(6,4)]` は中心 `Mark _ 3` が一致する一方で
    外側 `Mark _ 0` が異なるため共通文脈が存在しないことまで Lean 定理で固定した。
    公開定理と両反例は sorry 0、axioms は通常の
    `[propext, Classical.choice, Quot.sound]`（A18 反例は choice 不要）。独立 Python 監査は
    成分 `<3`・長さ `≤4` の全7,380列中、簡約286列の入れ子260件・本体224件で
    反例0。Lean 内監査は全819列の入れ子43件・本体39件で反例0。
    Kimina も no errors/no sorry、全 `lake build` は3,037 jobs成功（2.75秒）。
    Isa: `Mark_nest_common_marked`, `m_7_4_Mark_nextAdm`,
    `y6z_7_4_Mark_nextAdm_TPS_false`。[r1]
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
