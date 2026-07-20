# 進捗管理（Isabelle レイアウト reorg — lean/ 同型化）

<!--
- この件: isabelle/ を lean/ と同型へ再編（章ディレクトリ 5/6/7/8 ＋ 1命題1ファイル ＋ 共有 PSS/ 層）。
- 仕様書: isabelle/REORG-PLAN.md（branch codex）。設計の核心=usage-chapter set でヘルパを共有/章ローカルに分割。
- 不変条件: 0 sorry / ML AUDIT pass / 元の注釈を全部移送＋参照修正 / 章ごと green gate / 移設(複製でなく移動)。
- 承認: 夜間ユーザー不在のため supervisor(Claude) が各 phase を自律承認。auto-approve は codex-autoapprove.sh(二層)。
- マーカー: ✅=完了+supervisor 検証 / 🚨🤖=codex 作業中 / 🚨=未着手 / ❌=原文偽(該当なし)
- 旧 lean/task.md(Lean 移植 §5-§8 全✅) は git 3daca28 に退避。復元 `git show 3daca28:lean/task.md`。
-->

## 進捗ツリー

- ✅ **Phase 0（依存 DAG 分析、ファイル無変更）** — `Thm_Deps.thm_deps` で fact 単位 DAG(4353 facts, 非巡回)。章グラフ非巡回・上位 import 0。共有 PSS/ 2288 / 章ローカル 1283。上三角の実エッジ 0(22 候補は命名アーティファクト)。unmapped 8(§7:2, §8:6)。baseline green+audit。commit 35c2cc3
- ✅ **§5（13命題）パイロット** — sorry 0・内容移設・注釈保存＋参照修正。PSS_A/B/C green+audit。commit 1baf7bb
- ✅ **§6（55命題; exact54+corrected1）** — 移設(pss_mechanized −569, pss_paper −119 行)。sorry regression なし(pss_scratch 33=33)。corrected は 6/P_6_6_reduced_leftend guarded 形。green+audit。commit 667a3c2
- ✅ **§7（27命題; exact17+corrected8+unmapped2）** — unmapped 2 を Red-stability family から忠実再構成(stub せず)。移設(pss_wip −31595, pss_mechanized −4909)。sorry 0・regression なし・green+audit。commit 46a9841
- 🚨🤖 **§8（33命題; exact25+corrected2+unmapped6）** — codex 作業中(最終章)。**構造は完成: 命題ファイル 33/33＋`8/audit.thy`(ML AUDIT 移設済)生成、`fail` 残ゼロ**。実 sorry は §8.1 の documented stub 1件のみ。最終厳密検証中・未commit
  - 🚨 §8.1（4: exact3+❌1）— condI_III_c1_around=❌原文偽(A20 part1/A21 part5)。**documented stub 適用済**(原文どおりの文, `8/P_8_1_condI_III_c1_around.thy:80`)＋proven parts(m_8_1_c1_around_part*, main:pss_wip)複製。supervisor 判断: 訂正を発明せず main を忠実複製(2026-07-20 夜)
  - 🚨 §8.2（7: exact6+unmapped1）— unmapped: condIIIV_terminal_slice_Trans
  - 🚨 §8.3（4: exact3+corrected1）— corrected: kind0_base_ineq
  - 🚨 §8.4（3: exact2+corrected1）— corrected: Trans_oper_exchange
  - 🚨 §8.5（2: exact2）
  - 🚨🤖 §8.6（4: exact2+unmapped2）— codex 作業中: Trans_fseq_condVI を修正→一時セッションで厳密検証中。trailing_principal_annihilable も同経路
  - 🚨🤖 §8.7（9: exact7+unmapped2）— ★主定理 p_8_7_termination 含む。修正理論を §8.6 と同期検証中。unmapped: OT_tail_annihilable, Pred_oper0(⚠️原文で偽/一般形未証明の既知難物)
- 🚨 **仕上げ** — 全章後: ROOT/CLAUDE.md 整合・docs/TOC 再生成・独立フル rebuild で最終 green 検証
