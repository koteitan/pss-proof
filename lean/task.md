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
- ✅ **§8（33命題; exact25+corrected2+unmapped6）** — codex 完了・commit d6ddac4。**命題ファイル 33/33＋`8/audit.thy`(ML AUDIT を PSS_A 末尾へ移設、all_sorries を新モジュール名で全面書換)**。supervisor 検証: **命題文 33/33 が main と逐語一致**／実 sorry 8件=[Buc1]引用3(pss_paper)＋§8 documented stub 5、main(135)からの regression なし／注釈 5896 行を全数照合し欠落 0(差分12件は `@{thm [source]}`→`@{text}` の参照修正と A26 撤回反映の正当な書換)／`m_8_7_OT_examples` 二重定義は main 由来の既存物
  - ✅ §8.1（4: exact3+❌1）— condI_III_c1_around=❌原文偽(A20 part1/A21 part5)。**documented stub 適用済**(原文どおりの文, `8/P_8_1_condI_III_c1_around.thy:80`)＋proven parts(m_8_1_c1_around_part*, main:pss_wip)複製。supervisor 判断: 訂正を発明せず main を忠実複製(2026-07-20 夜)
  - ✅ §8.2（7: exact6+unmapped1）— unmapped: condIIIV_terminal_slice_Trans
  - ✅ §8.3（4: exact3+corrected1）— corrected: kind0_base_ineq
  - ✅ §8.4（3: exact2+corrected1）— corrected: Trans_oper_exchange
  - ✅ §8.5（2: exact2）
  - ✅ §8.6（4: exact2+unmapped2）— unmapped: Trans_fseq_condVI, trailing_principal_annihilable = documented stub。証明済み制限版は Support_8_B に保持
  - ✅ §8.7（9: exact7+unmapped2）— ★主定理 p_8_7_termination 含む。unmapped: OT_tail_annihilable, Pred_oper0 = **原文は真・main でも未証明**（A26/A27 は corrections-old.md で【取り下げ】＝A23 誤読由来の我々の誤り。❌ではなく 🚨 未証明。停止性は不要で迂回）。main 同様 documented stub。**陳腐化コメント是正済**: `8/P_8_7_OT_tail_annihilable.thy` ヘッダは撤回を明記、`Support_8_C` の register も更新、`python/audit_87_OT_tail_annihilable.py` の旧 pss_wip 行番号参照も修正
- 🚨🤖 **仕上げ** — **独立クリーン全ビルド 緑(isbman ed4ce4, `-c PSS_A PSS_B PSS_C`, 48分)**: `Finished PSS_A/B/C` 各1行・`***` 0・`AUDIT FAILED` 0・`oops` 0 ＝ゼロから建て直して ML AUDIT 合格。docs/TOC(37/37 §8ファイル)も再生成済。supervisor 追加是正: `CLAUDE.md` を新レイアウトへ更新／`pss_paper.thy` ヘッダの陳腐化記述を訂正。**残=再検証ビルド(isbman bsi2zjxsu)→commit→main へマージ・push→codex に「以後 main で作業」通知**
