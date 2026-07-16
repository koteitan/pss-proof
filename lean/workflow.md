# workflow.md — Lean 移植の workflow 並列作業計画（/clear 後の再開手順）

**読む順**: このファイル → `lean/task.md`（進捗ツリー） → `lean/memo.md`
（§4.5/§4.6 = キャンペーン作戦図、§3/§4 = 罠と死路） → `lean/step.md`（緑の定義） →
`lean/kimina.md`（検証サーバ）。Isabelle 側は完了・凍結（`isabelle/`、証明の設計図として grep する）。

## 0. 現在地（2026-07-17 時点・全緑 push 済）

- ✅ 済: 定義層 / §5 / **§6 全節（6.8 d1pos campaign 完了、Wave A クローズ）** /
  §7（7.1-buchholz-wf 除く）/ §8.1 diagSeq 2 本 / §8.2 standard-slice-Red-strongmono
  ＋ strongmono-slice / §8.3（keystone 除く 3 本）/ §8.6 3 本 /
  §8.7 の const00・OT-examples・OT-scb-recursive・OT-dom-hereditary。
- 🚨 残（**全てキャンペーン級**）: 下の Wave 計画参照（Wave A は ✅ 済）。
- `8.1-condI-III-c1-around` は sorry 残 1（part (4) のみ。(1)(2)(3-1)(3-2)(5) は緑）。
- `7.1-buchholz-wf` は自前証明に決定（下記「決定済み」参照、Wave E 相当）。

## 1. 実行ルール（ユーザー指示）

- **Workflow ツールで並列 fan-out。モデルは全 agent `fable`。1 wave ≤ 4 agent。**
- Agent ツール（Task/agent teams）は使わない（CLAUDE.md 明記）。
- 分類器に spawn をブロックされたら**同一セッションで再試行しない**（probe も
  「回避試行」と判定され前例が自己強化する。2026-07-16 に実証）。その場合は
  solo main-loop 移植に切替（1 補題 5–15% コンテキストで回る。実績: 1 日 8 件 ✅）。
- commit/push は自由（緑のみ）。task.md/memo.md は**親のみ**編集、agent 割当時に
  🚨→🚨🤖、クローズで ✅[rN]（hook が強制）。ターン末尾は 🤖/👤 マーカー。

## 2. インフラ（wave 起動前チェックリスト）

1. **kimina サーバ稼働確認**: `curl -s http://localhost:12345/health` → `{"status":"ok"}`。
   落ちていたら `cd ~/proofs/pss-proof/kimina-lean-server && nohup .venv/bin/python -m server > /tmp/kimina-pss.log 2>&1 &`
2. スモークテスト: `printf 'import PSS.Defs\n#eval PSS.entry [(1,2)] 0 0\n' | python3 python/check_lean.py -`
   （`Unknown identifier PSS.*` が出たら REPL キャッシュが stale → サーバ再起動。
   **PSS/ 配下を lake build した後は必ず再起動**）
3. 検証は `python3 python/check_lean.py <file>`（rc=0 = エラー 0 かつ sorry 0）。
   **agent に lake build をさせない**（.lake 並列破損）。lake build は親が統合時に 1 回。
4. ✅ の 3 条件（step.md §1）: rc=0 ／ `#print axioms` が
   `[propext, Classical.choice, Quot.sound]` のみ（sorryAx・ofReduceBool 不可、
   つまり native_decide 禁止）／ 主張が原文（訂正後）と一致。

## 3. Agent プロンプト雛形（自己完結、コピペで使う）

```
You are porting one proposition of P進大好きbot's pair-sequence-system termination
article to Lean 4. Repo root: /home/koteitan/proofs/pss-proof/git — cd there first.

HARD RULES:
- Your ONLY deliverable is <FILE>. Optionally ONE python audit script python/<name>.py.
  Touch NOTHING else (no lean/PSS/*, no task.md/memo.md, no other lean files).
  If you need a shared lemma, prove it privately (private theorem, unique suffix)
  and list its statement in the "needs" field of your report.
- NEVER run `lake build` / `lake env lean`. The ONLY checker:
  python3 python/check_lean.py <your-file>   (rc=0 = no errors AND no sorry).
- No native_decide. Allowed axioms exactly [propext, Classical.choice, Quot.sound].
  End the file with one "#print axioms <thm>" per public theorem.
- File header (module docstring, AFTER imports): 原文 location / 訂正 A-numbers /
  Isabelle lemma names / 依存 / 状態. See lean/8/8.3-kind0-base-basepoint.lean for style.

METHOD (in this order):
1. lean/spec.md §3, lean/step.md, lean/memo.md (§3 罠, §4 死路, and the §4.5/§4.6
   campaign maps if your task belongs to them).
2. The article statement in tmp/content.md, then corrections.md for A-numbers.
3. The Isabelle statement in isabelle/pss_paper.thy and OUR PROOF (grep the m_/y-name
   in isabelle/pss_mechanized.thy, isabelle/layerB/pss_wip.thy,
   isabelle/layerC/pss_scratch.thy). Extract the proof STRUCTURE, not tactics.
   Do not invent a new mathematical route before reading the Isabelle one.
4. Grep the existing lean/ tree for public lemmas BEFORE writing anything
   (§6.2/6.4/6.6-reduced-fseq/6.8/7.2-scb-unique/7.4-Mark-Trans-repr are rich).
5. Numeric validation FIRST when the claim is nontrivial: python/red_model.py,
   python/trans_model.py (entries ≤8, length ≤6, real standard forms).

LEAN PITFALLS (all hit in this project — lean/memo.md §3/§4.5/§4.6 has more):
- rw does NOT match List.length_* through the `Lng` abbrev; simp does. Bridge with
  defeq-`have`/`show` to the .length form. `Lng X` and `X.length` are DIFFERENT
  omega atoms.
- rw [h] rewrites ALL occurrences incl. inside Red(seg ...) on the RHS — use conv_lhs
  or a ∀-generalized transfer lemma.
- Bool case splits: use `cases hb : expr with | false | true` (never rely on the
  disjunct order of Bool.eq_false_or_eq_true).
- le0/leR lifting between entry-agreeing lists: use the VALUE characterization
  (ancestor_basic_1 : le0→values; parent_exists_3 : values→le0) — no fuel induction.
- omega atomizes products/divisions syntactically: keep q*w spelled identically
  across hypotheses; relate (n-1)*w to n*w via `cases n; simp [Nat.succ_mul]`.

HONESTY: if sorry remains or rc≠0, report status "partial"/"blocked" with the exact
stuck goal. checker_tail must be the verbatim tail of your final check run.
The parent re-runs the checker.
```

Workflow スクリプト構造は過去 wave のものを再利用可
（`/home/koteitan/.claude/projects/-home-koteitan-proofs-pss-proof-git/8b6b910e-60c9-4662-aff1-4806ad270a61/workflows/scripts/lean-port-wave1b-strongmono-wf_e55eee93-8eb.js`
が単発 port の完全な雛形。schema: file/status/summary/sorry_count/checker_tail/needs）。

## 4. Wave 計画（優先順）

### Wave A — 6.8 d1pos leg — ✅ 完了（2026-07-17。A-1〜A-3＋solo 仕上げ、以下は史料）
**閉じると `6.8` と `8.2-standard-slice-Red-strongmono` の 2 項目が同時に ✅**
（後者はブリッジ配線済み）。目標 = `lean/6/6.8-standard-slice-Br-descending.lean` の
名前付き仮定 `RankSuccD1posLeg`（~4211 行目）を定理化。
作戦図: **lean/memo.md §4.5**。Isabelle 側 dispatch は
`m_6_8_slice_Br_descending_monoT` の d1pos 枝（pss_mechanized ~21500–21951）:
`oper_d1pos_notbrle_Br_align_regA` → `oper_d1pos_low_anchor_shamt0` →
`oper_d1pos_notbrle_LOW_take_eq_{regA,regB,boundary}`。brick 群は
pss_mechanized 9302–21950（`oper_d1pos*` 694 箇所 ≈ 8–12k 行）。
- agent 分割案（green-modulo で上から）: ①dispatch＋Br_align（上位を named-仮定
  modulo で先に配線）②anchor_shamt0 系 ③LOW_take_eq regA ④regB/boundary。
- **今回の新兵器を使え**: P-take 境界対応（`lean/8/8.2-strongmono-slice.lean` の
  `P_take_at_boundary_sms`/`P_take_prefix_eq_sms`、左最小値は行 0 値のみで決まり
  d1pos の δ シフトはブロック内順序を保つ）、値特徴付け le0 転送。
- 複数 wave 前提（1 wave で終わる規模ではない）。

### Wave B — 8.1 part (4)（front-peel）
`lean/8/8.1-condI-III-c1-around.lean` の最後の sorry（`c1_around_4`）。
Isabelle: `m_8_1_c1_around_part4_setup/_Nred/_Adm0/_cond41/_cond42/_TransN_41/
_TransN_42/_segpos` → `part4_1`/`part4_2`（layerB、~3000 行）。
`Trans_front_peel`（layerB:18435）と `Mark_rightmost_adjacent_peel`（18558）が中核。
既に Lean 側にある部品: gap-peel 3 エンジン（同ファイル内 private）・
part(5) の接頭辞転送層・`Mark_Trans_repr` 一式。

### Wave C — §8.2 残り
- `8.2-condV-rightmost-parent`（Isa layerB:42048）: 不足 helper 8 本
  （monoT_hasParent0_last=**Lean 済**(6.6-P-condAB)、wf21_Br_eq_seg、
  le0_monoT_seg_into_list、m_8_2_le0_above_parent、joint_row1_eq、branch_col0_val、
  det_imp_joint_lt_TrMax、Joints_parent_nextR/Joints_nth）。中量級。
- `8.2-subexpr-component-Pred`/`-strongmono`（Isa 19256–36477、~17k 行）: 最大級。
  Isabelle の残差分解（setup→clause 別→witness→uncond）に沿って多 wave。
- terminal-slice 系 2 本は Trans 交換則キャンペーン（Wave E）と同時期。

### Wave D — §8.7 降下柱（停止性への幹線）
`8.7-fseq-descend`（Isa: `m_8_7_fseq_descend_dispatcher` = 7 つの交換則前提の
dispatcher。先に dispatcher を named-仮定 modulo で移植し、交換則
（8.1-Trans-fseq-condI / 8.3-condII / 8.4 / 8.5 / 8.6-condVI）を順に差し込む）→
`8.7-Trans-preserves-OT`（Isa: `y5_Trans_OT_B`、layerC）→ `8.7-termination`
（Isa: `y5_PSS_wf`/`y5_Fdom`）。`8.3-Trans-fseq-condII` は fseq-descend の系
（⛔ マーク済み）。`8.7-OT-tail-annihilable` は wf 帰納
（`y3t_toplevel_OT_tail_annihilate`、layerC:19355）を使うので ↓ の決定後。

### 決定済み（2026-07-16 ユーザー）
- **`7.1-buchholz-wf`（[Buc1] Lemma 2.2 = OT_B 整礎性）は Lean でも自前証明する**。
  Isabelle の y4 campaign（`y4_buc1_2_2_OT_B_wf`、layerC:13700、`y4_bachmann` 核の
  W-階層帰納。y4 block ≈ layerC 12493–13700 ＋ y3 W-機構 11247–11777、~2k 行）を移植。
  §8.7 の wf 帰納系（tail-annihilable・termination）が依存するため、
  **Wave D 後半までに専用 wave（Wave E 相当）を充てる**。axiom 引用はしない
  （最終定理の axioms を `[propext, Classical.choice, Quot.sound]` のまま保つ）。

## 5. 統合手順（親、wave 完了ごと）

1. agent 報告の checker_tail を信用せず `check_lean.py` を再実行（rc=0）。
2. `#print axioms` 確認（sorryAx/ofReduceBool 無し）。
3. 主張が原文（訂正後）・Isabelle の p_ 文と一致するか目視。
4. `cd lean && lake build`（1 回）→ **その後 git 操作の前に必ず repo root に戻る**
   （cwd 残留で commit-msg 誤用事故が 2 回起きた。lake build と git を同一コマンドで
   連結しない）。PSS/ を触った場合は kimina 再起動。
5. task.md＋memo.md を同時更新（🚨🤖→✅[rN]）→ commit（英語メッセージ、
   `commit-msg.txt` 経由）→ push。
