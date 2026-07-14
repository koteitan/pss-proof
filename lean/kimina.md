# kimina.md — kimina-lean-server の使い方（本リポジトリ向け）

Lean 4 の証明片を **HTTP 経由で高速・並列にチェック**するためのサーバ
（[kimina-lean-server](https://github.com/project-numina/kimina-lean-server)）の運用メモ。

`lake build` は 1 ファイル変えるたびに依存を辿るので遅い。kimina は **REPL を常駐させて
import 済みの環境を使い回す**ので、`sorry` を潰す試行錯誤（特に **workflow の並列エージェント**）
が桁で速くなる。これが本サーバを使う唯一の理由。

> **鉄則**: credential・絶対パス・IP を**コミットしない**。マシン固有の値はすべて
> `kimina-lean-server/.env`（gitignore 済み・repo 外）に置く。このファイルには実値を書かない。

---

## 0. 配置

```
~/proofs/pss-proof/
├── git/                     ← 本リポジトリ（Lean プロジェクトは git/lean）
└── kimina-lean-server/      ← サーバ本体（repo 外。独自 .git / .env / .venv / repl を持つ）
```

- `.venv` … Python 依存（構築済み）
- `repl/.lake/build/bin/repl` … Lean REPL バイナリ（**Lean v4.30.0 でビルド済み**）
- `.env` … このマシン用に設定済み（PORT / PROJECT_DIR / REPL_PATH）

**Lean のバージョンは repl と `lean/lean-toolchain` で一致していること**（現在 `v4.30.0`）。
ずれると REPL が起動しない。

---

## 1. 起動

```sh
cd ~/proofs/pss-proof/kimina-lean-server
nohup .venv/bin/python -m server > /tmp/kimina-pss.log 2>&1 &
```

起動確認（`Application startup complete.` が出れば OK）:

```sh
grep -m1 'startup complete' /tmp/kimina-pss.log
```

**前提**: Lean プロジェクトが**ビルド済み**であること（REPL が olean を読む）。

```sh
cd ~/proofs/pss-proof/git/lean && lake build
```

`lake build` していない／`.env` の `LEAN_SERVER_PROJECT_DIR` が実体とずれていると、
起動はするがチェック時に `{"detail":"Failed to start REPL"}` になる。

### ハマりどころ（実際に踏んだもの）

- **`LEAN_SERVER_MAX_REPL_MEM` は 28G にしてある。下げるな。**
  kimina は snippet の import 行を **`import Mathlib`（全体）に正規化して** REPL に流す。
  Mathlib 全体の olean は数 GB を mmap するので、REPL に掛ける `RLIMIT_AS`（＝仮想メモリ）が
  既定の 12G だと **`Failed to run header on REPL` → HTTP 500** で落ちる。
  症状が「Lean 単体（`lake env lean`）では通るのに kimina だと 500」ならこれ。
- サーバは `lake env <repl>` を `cwd = LEAN_SERVER_PROJECT_DIR` で起動する。
  つまり **REPL は必ず本リポジトリの Lean プロジェクトを見る**。`PSS.*` がそのまま import できる。
- 初回の `import Mathlib` は 5 秒ほどかかるが、REPL は使い回されるので 2 回目以降は速い。
- ★**`PSS/*.lean` を編集したら `cd lean && lake build` してから kimina を再起動する。**
  REPL は **header 単位でキャッシュされ、`LEAN_SERVER_MAX_REPL_USES=-1` なので永久に使い回される**。
  再起動しないと **`lake build` 済みの新しい定義が snippet から見えない**
  （`Unknown identifier PSS.oper` が出る。実際に踏んだ）。命題ファイル（`5/`…`8/`）を
  編集するだけなら再起動は不要 — snippet は本文をそのまま流すので常に最新。

  ```sh
  cd ~/proofs/pss-proof/git/lean && lake build
  pkill -f "python -m server"
  cd ../../kimina-lean-server && setsid nohup .venv/bin/python -m server > /tmp/kimina-pss.log 2>&1 &
  ```

## 2. ヘルスチェック

エンドポイントは `POST /api/check`、ボディは `{"snippets":[{"id":..,"code":..}]}`。
ポートは `.env` の `LEAN_SERVER_PORT`（8000/8080 は使わない）。

```sh
PORT=$(grep '^LEAN_SERVER_PORT=' ~/proofs/pss-proof/kimina-lean-server/.env | cut -d= -f2)
curl -s -X POST http://localhost:$PORT/api/check \
  -H 'Content-Type: application/json' \
  -d '{"snippets":[{"id":"t1","code":"import PSS.Defs\n#check @PSS.Lng"}]}'
```

プロジェクトの定義が引ければ連携 OK。

## 3. 停止

```sh
pkill -f "python -m server"     # 他エージェントも動いていることがある。PID を確かめてから
```

---

## 4. workflow / sub-agent からの使い方 ★

**CLAUDE.md により並列化は Agent ツールではなく `Workflow` を使う。**
各 workflow エージェントは `lake build` を**呼ばず**、kimina に snippet を投げて検証する。
理由は 3 つ:

1. **速い** — REPL が mathlib と `PSS.*` を import 済みのまま常駐する。
2. **競合しない** — `lake build` を並列に走らせると `.lake` を奪い合って壊れる。
   kimina は読み取り専用に olean を使うので、N エージェントが同時に叩いても安全。
3. **worktree が要らない** — snippet はファイルに書かずに検証できるので、
   エージェントごとに git worktree を切る必要がない（Isabelle 時代の運用と違う点）。

### 4.1 エージェントに渡す定型（プロンプトにこのまま貼る）

> 検証は `lake build` ではなく kimina-lean-server を使え。ポートは
> `~/proofs/pss-proof/kimina-lean-server/.env` の `LEAN_SERVER_PORT` を読め。
> 証明を書いたら、**そのファイルの全文**（import 行を含む）を snippet として投げ、
> `messages` に `error` が 1 つも無く、かつ `sorry` の warning も無いことを確認してから
> 「証明できた」と報告せよ。**自己申告は信用されない。上記の JSON レスポンスを貼れ。**

### 4.2 検証スクリプト（`python/check_lean.py` として置いてある）

```sh
# ファイルをそのまま検証する（import 行込みで送る）
python3 python/check_lean.py lean/7/7.2-scb-unique.lean

# 出力: OK / ERROR / SORRY と、messages のダンプ
```

エージェントはこれを呼ぶだけでよい。終了コードは **0=証明済（error も sorry も無し）**、
**1=sorry 残り**、**2=error**。

### 4.3 Workflow の書き方（雛形）

```js
export const meta = {
  name: 'lean-port-round',
  description: 'Port N propositions to Lean in parallel, verify each via kimina',
  phases: [{ title: 'Port' }, { title: 'Verify' }],
}

const TARGETS = args   // 例: ["6/6.5-Red-idempotence", "6/6.6-reduced-slice", ...]

const results = await pipeline(
  TARGETS,
  t => agent(
    `Port the article proposition to Lean.  File: lean/${t}.lean
     - 原文と訂正は git/corrections.md、証明の設計図は isabelle/pss_mechanized.thy を読め。
     - lean/spec.md のテンプレートに従え（ヘッダ必須）。
     - 検証は kimina（lean/kimina.md §4）。lake build は使うな。
     - sorry が残ったら正直に残ったと報告し、どこで詰まったかを書け。`,
    { label: `port:${t}`, phase: 'Port', schema: PORT_SCHEMA }),
  (r, t) => agent(
    `Adversarially verify lean/${t}.lean.  Run python3 python/check_lean.py lean/${t}.lean
     and paste the raw output.  Then check: does the theorem statement actually match
     the article (tmp/content.md) as corrected by corrections.md?  A proof of the WRONG
     statement is the failure mode we care about.  Default to refuted=true if unsure.`,
    { label: `verify:${t}`, phase: 'Verify', schema: VERDICT_SCHEMA })
)
```

**verify フェーズを省略しないこと。** Isabelle 版で最も高くついた事故は
「エージェントが緑と自己申告したが実は未緑」と「正しく証明されたが**別の命題**だった」の 2 つ。

---

## 5. セキュリティ

- 本サーバは **任意の Lean コードを実行する REPL** を公開する。`LEAN_SERVER_HOST` は
  `localhost` に固定し、`0.0.0.0` にはバインドしない。
- `.env` と起動ログ（絶対パス・PID を含む）はバージョン管理に入れない。
