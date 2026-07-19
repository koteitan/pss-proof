[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# lean/ — Lean 4 移植のファイル構成

ペア数列システムの停止性の Lean 4 版。**1 論文命題 = 1 ファイル**。状態は**作業中**
（停止性の主定理 `p_8_7_termination` は無条件・`sorry`-free で達成済み。
`#print axioms` は `propext / Classical.choice / Quot.sound` のみ）。

## ディレクトリ構成

```
lean/
├── lakefile.lean           パッケージ定義（default_target: PSS, «5» «6» «7» «8»）
├── lean-toolchain          leanprover/lean4:v4.30.0
├── PSS/                     共有層：定義＋再利用ヘルパ
│   ├── Defs.lean            §5 定義
│   ├── Mono.lean            単調性 / IncrFirst
│   ├── Adm.lean             許容性
│   ├── Red.lean             §6.5 Red 簡約
│   ├── Standard.lean        ST_PS / RT_PS
│   ├── Scb.lean             scb（部分列）
│   ├── Flat.lean            平坦化
│   ├── Trans.lean           Trans（Buchholz 表記への翻訳）
│   └── Buchholz.lean        §7 [Buc1] 表記系
├── PSS.lean                 PSS/ の集約 import
├── 5/ 6/ 7/ 8/              章ディレクトリ（1 命題 1 ファイル）
│                            例: 8/8.7-termination.lean（主定理）
├── 5.lean 6.lean 7.lean 8.lean  各章の集約 import
├── spec.md                  構成仕様
├── step.md                  手順（緑の定義）
├── task.md                  進捗ツリー
├── memo.md                  設計・死路
├── kimina.md                Lean チェックサーバの使い方
└── workflow.md              wave 計画
```

## 章ディレクトリの規模

| 章 | ファイル数 |
|---|---|
| `5/` | 6 |
| `6/` | 65 |
| `7/` | 38 |
| `8/` | 250 |

命題数より多いのは、大きな証明を複数ファイルに分解しているため。

## 命名

- ファイル名 `<§>.<sub>-<slug>.lean`（例: `7.2-scb-unique.lean`, `8.7-termination.lean`）。
- モジュール名は guillemet で囲む：`«8».«8.7-termination»`（ドットや数字始まりを許すため）。

## ビルド・検証

- フルビルド：`cd lean && lake build`（全 `default_target`）。
- ただし `lake build` は `sorry` を warning でしか報告しない。命題の緑判定は
  [step.md](step.md) に従い `python3 python/check_lean.py <file>`（kimina サーバ経由、
  rc=0 ＋ `#print axioms` に `sorryAx` 無し ＋ 主張が原文（訂正後）と一致）。
