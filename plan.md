# plan.md — 作業計画・詳細メモ

task.md のユーザー向け骨格に対する、作業側の詳細版。ユーザーは読まない前提の自由記述。

## 編集方針（自分用）
- **エージェントが作業中のアイテムには 🚨🤖 を書く**（該当ラウンドで agent が討伐対象にしている 🚨 アイテムに 🤖 を付ける。統合したら 🚨→✅ か、作業継続なら 🚨🤖 のまま）。
- **進捗ツリーを編集するときは task.md と plan.md の両方を同じように編集する**（同一アイテム名・同一ツリー構造。task.md=骨格のみ、plan.md=同じツリー+詳細注釈。状態変更・分岐・畳み込みは同じコミットで両方に反映）。
- **ツリーは task.md とアイテム名を一致させる**（grep で相互参照できるように）。
- 各アイテムに書いてよいもの: thy 対応（討伐補題名）、modulo 残差の正確な内容(Isar)、経験検証の分数と corpus 深さ、勝ち筋/死路、他アイテムとの依存関係、担当 front/worktree、難易度所感、次の一手。
- task.md で畳んだ ✅ ノードも、こちらでは子を残してよい（履歴として有用なら）。
- ツリー以外のセクション（ラウンド状態・残差census・REFUTED registry・運用手順）を自由に追加・改廃する。
- 詳細が肥大したら docs/ か memory に移してポインタだけ残す。

## 現在のラウンド状態（2026-07-04 更新）
- **並列度制限: 2 front/wave(2026-07-11 ユーザー指示——月次spend limitで4並列waveが毎回途中死するため半減)**。旧: 3 front/wave（r29 6同時が session limit 全滅 → ユーザー指示で半減）。**モデル: Fable 残8%→ほぼ Opus 4.8+xhigh へ移行**(ユーザー switch 済)。
- **r29a wave-1 統合済**(main HEAD=6f491a2): ✅condV非adm交換 完全無条件化(descent condV leg 完了) / ✅condII 閉形式(残=tailval leftDj0枝) / ✅condIII 6→3残差(REGS/REGSP/M0RUN)。CIIIREG は session limit で死んだが6緑コミット全回収。
- **次 wave 予定**: OTRES(OTint/OTpred/OTmulti) / HBWIRE(condIV HB+d1-d3配線) / DISPATCH(dsx_fseq_descend_master+termination残差census)。**+新規: CIIIREGIME(REGS/REGSP/M0RUN) / CONDIITAIL(tailval leftDj0=p_8_2_condIIIV)**。Opus なので鋭い単文残差に削って投入、3 front/wave 厳守。
- worktree 同期: wave-1 の wt-f7/wt-s4a/wt-s4b は 6f491a2 へ reset 要(未実施なら次 spawn 前に)。
- 統合手順: `git/tools/extract_block.py` で base 相対 clean-append 検証 → 連結 → solo `isbman build -v PSS_C` → literal "Finished PSS_C"==1 + real-error grep 0 + sorry/oops テキストのみ確認 → python 資産回収 → commit+push → task.md/plan.md 両更新 → worktree 同期 → 次wave。

## 今後の戦略（2026-07-04 策定、Fable週間残14%→枯渇後は Opus 4.8 のみ）

**モデル資源の前提**: Fable は週間制限の残り 14% のみ。枯渇後は有料化で完全に使えなくなり、以後は Opus 4.8(+xhigh) が唯一の深reasoningモデル。Opus は r14-r27 の全ラウンド(VE' 完全クローズ含む)を担った実績があるので、質的に詰むことはない — ただし Fable より押し切り力が落ちるので、**残差を「鋭い単文残差」まで削ってから投げる**運用を徹底する。

### Fable 残 14% の使い途（優先順位）
1. **実行中の wave-1(CIIIREG/ATOMS/CONDII) を完走させる** — 現在まさに最難の3コア(regS/regB、c2L1、tailval)に Fable を投入中。これが 14% の主用途。
2. wave-1 が Fable 枯渇で死んだ場合: 緑コミットを回収(commit-early 徹底済)→ 残りは Opus で継続。fossil 回収手順は確立済。
3. wave-1 後に Fable が残っていた場合のみ: wave-1 で割れなかった単一の最難残差(候補: regS の構造帰納 or OTint)に **1-agent 集中投下**(3並列はしない)。それ以外の用途に Fable を使わない。

### Opus 時代の運用（wave-1 統合後〜）
- 3 front/wave・Opus4.8+xhigh・empirical-first(cap≥30000/Lng≥10/brute straddle)は不変。
- **wave-2(配線系、Opus で十分)**: OTRES(OTpred→OTmulti→OTint の順に易→難) / HBWIRE(HB+d1-d3配線) / DISPATCH(dsx_fseq_descend_master+termination残差census)。scratchpad/pss-r29.mjs の該当3面を model 指定だけ変えて流用。
- 以後のラウンドは census の残差リストを上から潰す。**2ラウンド抵抗した残差は必ず再分割**(reduce→validate→close の r22-r28 パターン。一点突破を Opus に強要しない)。

### 残差の難易度見立てと着手順
1. 【wave-1 中】regS/regB(構造帰納・中難)、tailval(W=D_v0 t4・中難)、c2L1(緑済・統合のみ)
2. 【wave-2、易〜中】OTpred(1 leg は plain descent)、OTmulti(P分解 lift)、HB(condV 類似の写経)、d1-d3 配線(機械的)、DISPATCH(機械的だが census 価値大)
3. 【中難】base0H/base1H/A0ltH(right-spine head bound、dbbodyH の姉妹)、OTint(閉形式→isOT/descP snoc 機械化)
4. 【後回し・要判定】§8.2 condII/IV 終切片命題 — **停止性 critical path 上か先に判定**(w84x/c4dx route は既にこれを迂回している可能性大。迂回済なら paper 完全性のみの問題として deferred)
5. 【監査・安価】§8.5 keystone surgery-spine subtree — 原典route(scbdec)が condV 交換を閉じた今、**obsolete の可能性大。丸ごと ❌/不要 化できるか audit**(ツリー大幅整理)
6. 【外部のまま維持】buc1_2_2 unbounded-depth(ψ collapsing) — Buchholz ψ の整礎性形式化は独立大プロジェクト。**停止性は「buc1_2_2 modulo」で完成宣言**し、深追いしない(depth断片+同値尖鋭化まで済んでいるので外部引用の正当性は十分文書化済)

### 終盤の完成形（目標）
- `dsx_termination_residual_census`: 停止性定理 = {残差アトム全列挙} modulo buc1_2_2 — census が空になった時点で **「ペア数列停止性、[Buc1] Lemma 2.2 のみ外部引用で完全形式証明」達成**。
- その後: pss_paper の p_* sorry を m_*/w84x/scx… で discharge する機械的 sweep → layer 凍結(scratch→seg 化) → README/docs 整備。

## §8 残差 census（r30後）
- 降下柱: condI ✅ / condVI ✅ / **condV(adm+nadm) ✅** / condII→{p_8_2_condIIIV={VE2,VE3,VE4}, DIAG} / condIII→{JGE, M0RUN, REGSP-bypass} / condIV→{HB✅, regS(=JGE), regSP-bypass, admeq}
- OT柱: {exchI ✅, exchII(=condII), OTint, OTpred, OTmulti}
- 整礎柱: buc1_2_2 のみ外部(depth断片✅)
- capstone: `m_8_termination_modulo_CF` → DISPATCH で census 化予定
- **残差の実体(r30後、共有関係が重要)**:
  - **{VE2,VE3,VE4}**(=p_8_2_condIIIV、LastStep切片幾何) — condII と §8.2命題 の共有底。**最高レバレッジ**。障害=LastStep basics 未発達。
  - **JGE**(TrMax(Red N)≤Joints(Red N)!last、単一枝+boundary) — condIII-REGS と condIV-regS の共有。
  - **REGSP-bypass**(純trunk枝の kousa-(1,1)閉形式) — condIII と condIV 共有。REFUTED registry 参照。
  - **M0RUN**(nextR、adm j-2⟺全trunk) / **DIAG**(eq-BAD⟹leftDj0) / **admeq**(condIV gate)
  - OT柱: OTint/OTpred/OTmulti / 外部: buc1_2_2
- **次の優先**: VE2/VE3/VE4(LastStep幾何を先に整備) > JGE(共有・単一不等式) > REGSP-bypass(共有) > OT残差 > M0RUN/DIAG/admeq(小)。

## REFUTED registry（再挑戦禁止・引用禁止の死没route）
- W1/W2/WRAP'/reach-WRAP'(de-adm、~adm域で偽; dkfx_/dkbx_ vacuous) [r25-r26]
- universal KER(RT_PS&monoT量化で偽; vmlx_*_of_kernel vacuous) [r27]
- stepval(A38; m_8_7_Trans_preserves_OT_via_closure/svx_* vacuous) [r28]
- len2/redB(ST_PSで偽19/131; shx_*_of_len2_redB は端点として死没) [r28]
- d13x_T形 condIII organize(innerU 0/426; cfax_/e3x_/corrected_condIII vacuous) [r28]
- **REGSP原文形(condIII/condIV共通)**: cfbx_reg at Red(Pred(s84x_N)) は Red(Pred N) 純trunk時に Br≠[] conjunct 不成立で偽(~15%host、CEX (0,0)(1,1)(2,2)(3,2)) [r30]。→ 証明せず d4a レベルで kousa-(1,1)閉形式 bypass。crx_/c4hx_ の regSP assume はこの純trunk枝では充足不能。
- Pred_oper0(A27) / 零化一般(A25/A26) / has_gz⟹D系(§6.7) / 固定count condII(A36)
- **leBT q qp(spine qp-descent、slotTail)**: ST_PS で偽 33/33(方向が逆: Pred は trailing deposit を縮める、qp<q)。stx_..._from_descent の descent 仮定は充足不能=DEAD route [r45]
- **STRAT-n(lvP 版、buc1)**: n≥1 で偽(witness D_0(D_k 0) < D_1 0)。層化は head-index で行う(wfj_strat_hd) [r52]
- **長さ指標 joint 帰納(r46/r47 エンジン)**: 証明不可能(EDGE-1/EDGE-2 が長さ非有界、a5/長さIH と矛盾——asx_ 監査)。stage-first も a5/Pred で対称に失敗。接地は stage 帰納+補正 readback(route A)のみ [r48]
- **OKH(=ox9_ok)/leafcond**: **両方とも偽**(8/542 純ST_PS census host、maxlen20・400歩乱歩)。witness は body が surgery filler pX=D_ub X0 を右spine外に含み、**等号で落ちる**。⟹**r69 の oi9_census_OKH は空虚**。r69 の緑は maxlen24 でも head<v1 を持つ host が3件しかなく **~99%空虚**だった。**HD(KK を index0 の head 比較で決める)も偽**(40/1700、walk が等しい principal で tie して右へ進む=KK は walk-level の事実)。**12件目の偽陽性** [r70]
- **fseq 対応の等式化 Trans(M[n])=operB (Trans M)(numBT k)**: **偽**(condIII 72/196、condIV 0/4、condV 0/70。Trans(M[n]) は fseq の**孫**で連続2成員の厳密な間)。非数値 z への一般化でも等式は増えない。既証明 exchange slot が leBT のみ/厳密< であることとも整合。**cofinality は不可避** [r70]
- **ox9_hge(census body の head が全て ≥v1)**: **偽**(2/425 deep 標準host、例 M=(0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,0)(6,1)(7,2)(8,0)(7,1)(8,1)、v1=1 で body 内に D_0 0)。r69 の初commit a6da3a8 はこれを仮定していたため該当hostで **vacuous**(05dfd96 で ox9_ok へ弱めて修復)。⚠️**深さ警告**: ox9_hge は maxlen 15 では 427/427 で真に見え、maxlen 22 で初めて死んだ——**固定深さの経験検証は安全な証拠にならない(本プロジェクト8件目の偽陽性)**。OKH も深く stress-test してから証明に投資せよ [r69]
- **r68「X1 の hole 上の spine level は全て純chain」**: **偽**(14/427 host が wide hole level、15 が非単調 width 語、危険枝(C)は 13/1117 peel level で実際に起きる)。r68 の組立スケッチは成立しない。真の brick は all-heads/ox9_ok 側 [r69]
- **SETLE1 spineH の position-0 head route(ox7_hole_right_spine_terminal)**: 「全 matched-hole tx′∈GBT u X1 で bpHeadV t′<bpHeadV X1(=hole head ub へ落ちる)」は**偽**。matched-hole 集合は hole の**全上位 right-spine 祖先**を含み、上位のは head=bpHeadV X1 で始まる→first-diff がより深く bpHeadV t′=bpHeadV X1(等号)。標準形CEX M=(0,0)(1,1)(2,2)(3,3)(4,1)(5,0)(6,1)(7,1)(8,1)、tx′=D_1(D_0(D_0 0))。90/332 fail。**真の残差は lessBT tx′ X1 の deep first-diff descent**(bpHeadV t′≤bpHeadV X1・leBT t′ X1 は 0-fail 真)。ot7_SETLE1_ltJ_of_head は green だが HEAD 仮定 discharge 不能=dead。position-0 head 分離を追うな [r67]
- **SETLE1 spineH の L1/L2(右spine)route**: restricted spineH(leBT t′ X1)は body の **右spine ではなく第1 principal(左端)head bpHeadV(body)** が支配。pass⟺bpHeadV(body)≥v1。task の L1/L2 は向きが逆(t′ 外head=ub<X1 外head=v1)で無用な逆 leBT X1 t′ を導く。scb_kind1_def は RightNodes 節のみ→r63 ox7_RightNodes_body_ge_v1(右spine≥v1)は bpHeadV(body) を証明不可能=右spine machinery は本義務に不十分。真の残差=左端 head 下界 bpHeadV(body)≥v1(Trans M∈OT_B G-cond 由来) or engine 再スレッド(deeper GBT 元支配)。python 130 host census: spineH 45/130 偽・b1x_setle 43/130 偽(non-real host) [r64]
- **naive 再帰 frame-descent(devchain depth≥2)**: 「Trans(norm(last(Br M))) の body が (prev,dep) で終わる」は 0/22 反証 [r48]
- **sliceV0 witness route for ps=[]**(depdom): Dpt v0 (Dpt x q)=Trans M 自身のため shorter witness 不在(0/1721、忠実性矛盾) [r48]
- **slice-only slotAppg 還元(depOT⟹qcore/Gcore)**: 純含意として不可能(機械検証 CEX: q=Trm[DB 5 0],x=2 で qcore 偽/q=Trm[DB 1(Dpt 9 0)],x=2,v0=0 で Gcore 偽)。deposit-OT は isOT_BT q と GBT-x 半分しか与えない [r47]
- **from-joint deposit 同定(r44 C1)**: 挿入主項 D_x q = Trans(seg M j0'(Lng M-1)) は偽(33/33、slice Trans は D_{M10}-tree 全体)。正=原文 P(N)_J1[n] 枝成分 [r45]
- **⚰️SUPERSEDED(不要化、r63削除)**: deep-insertion OT所属 keystone{resid,multiD}(orx_OTint/rgx_/m_8_7_Trans_OT_step_keystone)+stepval route。OTint は census route(oi5/oi8、tri0塔)で達成、oi8 は orx_/rgx_ を一切参照せず→旧keystone route 丸ごと obsolete。task.md/plan.md ツリーから削除(slotNewOT/slotAppg/slotTail/slotHeadWB/multiD/devpair/branchwit/transfer一般形/deposit-host等)。詳細は git 履歴+REFUTED registry(leBT q qp/slice-only slotAppg/stepval)参照 [r63]
- **⚰️SUPERSEDED(不要化、r64削除)**: 4-case dispatcher〔`m_8_7_OT_keystone_step`〕+帰納 infra〔`m_8_7_Trans_preserves_OT`(strong-Lng induction)/`m_8_7_Trans_OT_step_keystone`〕。**依存BFS検証**: `m_8_7_OT_keystone_step` の実推移的祖先=18個(全て orx_/rgx_/otx_*_of_keystone/asx_ deep-insertion route)、live census 柱 `oi8_census_final_ivadmeq`/`oi5_OTint_condIII`/`otx_Trans_preserves_OT_dispatch` は一切不使用。⚠️naïve grep BFS では 626個祖先に見えるが全て `@{thm [source] ...}` ドキュメント参照の誤検出(text cartouche 除去で 626→18)。live OT所属 は `otx_Trans_preserves_OT_dispatch`(置換capstone, keystone-free) 経由。code(layerB frozen)は残置、tree tracking のみ削除 [r64]
- **抽象 all-u SETLE1(OTint、r59)**: b1x_setle(GBT u A1)(insert X1(GBT u X1)) は base0/base1 満たす一般 OT A0 で偽(53669/119877 fail、CEX A0=[D_2[D_4 0]],u=0)。d4vx_ins wrapper nest で spine-body head transV が非有界。真になるのは実 A0=bpHeadT(Trans(Pred slice)) の §7.3/7.4 右spine head 構造のみ。base0/base1/tri0 だけからは証明不可 [r59]
- **SETLE1 head-bound「A0右spine head≤ub」(OTint、r62)**: 偽 477/477(実際 RightNodes(A0)∋transV>ub)。真の bound は逆向き外wrapper RightNodes(bpHeadT(Trans(s84x_N M)))≥v1。A0内側の head で殺す route は死 [r62]
- **FINRC=A9 fin-form、root=LastStep_def(condII、r62 精密化)**: census FINRC slot(tvx_finRc K)は証明不能=total-nth artifact。**r62 発見: 有界化を fin 仮定に threading する当初計画は不十分**——fin の唯一消費点は pss_wip:90481 `Min ?S≤?J1`(Min_le)で、LastStep_def(pss_defs.thy:521)自体が非有界 binder に Min 適用。有界 finiteness は Min(unbounded) に効かない。**真の A9 fix=root: LastStep_def の Min binder に guard J<Lng(Br M) 追加**(定義の自コメント A9 が既に指摘)→以後 fin/FIN/FINr/FINRC カスケード全体が vacuous(削除可)。消費点の post-correction body 2本=ot_finRc_LastStep_bounded_lt/ot_finRc_LastStep_guard_bounded_lt(fin無、緑)。**⚠️真scope(r63確認): fin/finM は §8.2 VE カスケードの約53補題(90000-108100)に threading=front B の10補題見積りは過小、大規模 refactor**。値は不変(else節は必ず J1∈bounded set なので bounded Min=unbounded Min、safe)、LastStep_def unfold は pss_wip 2箇所のみ(90448/90461)。編集計画= pss_defs.thy:521 LastStep_def の Min binder に guard J<Lng(Br M)→PSS_A 再ビルド(~11分)→**約53補題の fin/finM 仮定を削除+全 call site(vgx_LastStep_lt_of_guard 呼出だけで90506/90723/92437/92503/93885/96072/102296/102325 等)修正**→tvx_finRc_def 削除→ot_finRc_bounded/guard_bounded_lt(consumer body 済)で discharge→corrections.md A9(fin-form 補足済)。**dedicated 集中 effort 要、tail-of-turn 不可。1補題ずつでなく全編集→1回再ビルド→エラーから修正が効率的だが careful に**。ot_finRc_reduce が単一 A9 前提に局所化済 [r62,scope r63]
- 経験検証の教訓: oper-only corpus と小cap(8000)は偽陽性を生む。brute straddle + cap≥30000 + Lng≥10 必須。

## 進捗ツリー（詳細注釈付き）
- ✅ §5 定式化
- ✅ §6 ペア数列の基本性質 〔全節完了(2026-06-11)。docs `reducedness.md`/`red-le-domain.md`/`slice-Br-descending.md`〕
- ✅ §7 Buchholzの表記系への翻訳 
- 🚨 §8 停止性 〔r18: capstone `m_8_termination_modulo_CF`=停止性は CF-META(原典Pred同時帰納)+`buc1_2_2`整礎 の2点に崩壊。CF が唯一の Fable target〕
  - ✅ [Buc1] 引用sorry 討伐(Lemma 2.1/3.2a+3.3/2.2 全て自前証明)〔**⚠️訂正(2026-07-12): 一度「不要」としてツリーから消したのは誤り**。ユーザー指摘「§8の子に[Buc1]が入っていると §8 には [Buc1] が真であることが必要という意味になる。必要なの、必要じゃないの?」→**必要**。停止性は (OT_B,<) の整礎性を要する。**そして r71 front B がそれを証明した**: Buchholz[1]§3 の **≪_k step-down 関係**を写経(y4_bachmann/y4_xseq_cof/y4_inner/y4_bump 等)し **y4_cof0("y3_cof0") → y4_bwl_cof("bwl_cof") → y4_wf_RPrel("wf RPrel") → `y4_buc1_2_2_OT_B_wf`("wf {(a,b). a∈OT_B ∧ b∈OT_B ∧ lessBT a b}")**。最後の文は **pss_paper の cited sorry `buc1_2_2_OT_B_wf` と verbatim 同一** ⟹ **[Buc1] Lemma 2.2 は我々の定理になった**。**循環監査を build に焼き込み済**(ML block、違反すれば error でビルドが落ちる=**緑ビルドそのものが監査**): y4_buc1_2_2_OT_B_wf/y4_wf_RPrel/y4_cof0/y4_bwl_cof は **sorry 依存ゼロ**(特に置換対象の pss_paper.buc1_2_2_OT_B_wf に依存しない=非循環)。**削除したサブツリーの記録**: 自前証明の道程 wfs_(level-0 acc+rank)[r2]/wfj_(head-index STRAT)[r1]/wfc_(bookkeeping消去)[r1]/wds_(distinguished sets)[r1]/bwl_(r68: Buchholz[1]§2 2.4-2.8 を lfp 化で無条件証明=全D_ω-free項がW*)/y3_(r70: W-帰納 engine)/y4_(r71: [1]§3 ≪_k で仕上げ)。❌死枠(再挑戦禁止): minimal-bad/head-level tower(wcl_upper)/lvP-STRAT/acc-based bwl_Wlev/fseq対応の等式化〕[r14]
  - ✅ 停止性チェーンの sorry 除去〔**達成(r71)**: 停止性定理 `y4_PSS_acc_of_KK` と census `oi10_census_KK` は **pss_paper の 131個の sorry すべてに非依存**。**ビルド強制監査**(ML block、違反すれば error=緑ビルドそのものが監査)+**negative control で検証済**(sorry を意図的に使う Route A `y3_PSS_wf_of_KK_buc1` を監査対象に足すとビルドが正しく落ちる=監査は空虚でない)。**修正内容**: 最後の sorry `pss_paper.buc1_3_2a_fseq_lt`([Buc1]3.2a 基本列降下)は**陳腐**——同文が `m_buc1_3_2a_fseq_lt` として証明済だったのに、layerB の7消費者のうち5つが証明より**前の行**にありスコープ外だった。`leBT_trans`(4行・layerB依存ゼロ)+`b1x_` ブロック(466行、b1x_descent と m_buc1_3_2a_fseq_lt を含む)を最初の消費者の直前(27786行)へ**前方移動**し7箇所差替。移動ブロックの依存閉包が挿入点以降に届かないことを検証済。PSS_B+PSS_C 再ビルド緑(5:43/0:33)〕[r1]
  - 🚨 §8.1 条件 (I) の下での展開規則
    - 🚨 命題（条件 (I) の下での $\textrm{Trans}$ と基本列の交換関係）
      - ✅ 交換則(1)本体〔`scx_condI_exchange1` 完全無条件(j0=0+j0>0、marking-nesting二重帰納)〕[r4]
      - ✅ 降下(2) OT-free〔`scx_condI_descent`(d2x scbext route、OT柱回避)〕[r1]
      - 🚨 OT所属 (⛔ §8.7「Transが標準形を保つ」補題)
    - ✅ 補題（公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）〔`m_8_1_diagSeq_Trans`〕
    - ✅ 系（$\textrm{Pred}$ が公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）〔`m_8_1_Pred_diagSeq_Trans`〕
    - ✅ 補題（条件 (I) か (III) の下での $c_1$ 前後の具体表示）（A20/A21）〔part(1)-(5)+(4-1)(4-2) `m_8_1_c1_around_part4_1`/`_part4_2`〕
  - ✅ §8.2 強単項性[r39][1.775][2.52h]〔🎉r48完結。命題（標準形の直系先祖による切片の簡約化の強単項性）=`m_8_2_standard_slice_Red_strongmono`。命題（条件(II)か(IV)の下での終切片とTransの関係）=`hqx_condIIIV_of_DT`(pss_paper 1624 4-clause exists-unique、fin threading のみ、r24[1.775][2.52h]。系譜=scaffold/LastStep幾何/VE2(ROW10)/VE3-VE4(back-peel→bridgesU→{BASE,STEP}→TSPIN(tsx)→BASEf(bfx/bgx)→HEADEQ0(hqx=r27 vcx_VE_all 適用)))。補題5本=切片遺伝/keystone m_8_2_subexpr_component_Pred/単項成分基本性質/条件V右端親/条件V終切片[r15]。⚠️fin=un-dischargeable nth-artifact、consumer は thread(bpx_fin_Pred 式)。fin(Rc) 問題は §8.3 TVall配線で追跡〕
  - 🚨 §8.3 条件 (II) の下での展開規則
    - 🚨 命題（条件 (II) の下での $\textrm{Trans}$ と基本列の交換関係）
      - ✅ 降下⟸exch+OT〔`m_8_3_TransCondII_oper_descend_engine`〕
      - ✅ OT柱回避の直接降下〔`d2x_exchange2_condII`、kind0残差modulo〕[r1]
      - ✅ exch(FINRC threading)[r16][1.026][1.21h]〔🎉r53完結: condII exchange 完全化=存在量化count+step還元[r2]/base2+per-step surgery[r2]/tailval[r12](not-leftDj0[r1]+REGSP slx37[r5]+TVall配線[r6]: ldj-leg=tvx_tailval_of_boundary(hqx@Rc+境界厳格性無条件)+R3LE=tvx_fn_row_bound+**LDJB=ljx_LDJB**(r52 draft修理: diagSeq map/upt の bare simp→diagSeq_nth 凍結形。right-spine route: RightNodes position-1 の構造読出し(jL<TrMax、adm Rc fn=row-0親一意性 vs nextrel1 le0 conjunct、I/III=trunk内部非許容で殺し、VI=jL+1<fn、diag-at-fn は RedCondA⟹condV で排除)vs ldj 側 adm-run 読出し(va+d)→d=jL 強制、V枝 va+jL+1/TrMax枝 va+TrMax は矛盾。guard=R3LE+対角排除)[r2][0.523][0.60h])。`ljx_TVall_of_fin`=TVall modulo FINRC のみ。⚠️FINRC=nth-artifact(§8.2 finと同格)。Isar教訓: the1_equality 全飽和OFは大項で発散(620s+)→部分飽和[OF ex1]+simp/unfolding parent_def は内部 parent も展開し unification 破壊→THE等式を別建てして trans/RedCondA 有界∀抽出は spec[OF …,of 0]+simp(blast不可)〕
      - 🚨 OT所属 (⛔ §8.7「Transが標準形を保つ」補題)
    - ✅ 補題（第 $0$ 種型基本列の基本不等式）〔`m_8_3_kind0_base_ineq`(A22訂正)〕
    - ✅ 補題（第 $0$ 種型基本列の基本分岐規則）〔`m_8_3_kind0_branch_rule`〕
    - ✅ 補題（第 $0$ 種型基本列の基本基点関係）〔`m_8_3_kind0_base_basepoint`〕
  - ✅ §8.4 条件 (III) か (IV) の下での展開規則[r56][1.122][2.89h]〔🎉r45完結。condIII exchange=`cpx_condIII_exchange_uncond`(hasParent枝)+`npx_exchIII_slot_uncond`(¬hasParent枝: N[m]=Pred N ∀m、operB(Trans N)(numBT 0)=Trans(Pred N) 等式=k=0、domB(Trans N)=T_{e-1} via 最大low-ancestor対偶 npx_le0_last_entry_ge、¬hasParent枝は等式のみで strict は Trans レベルで偽)。condIV exchange=`cnv_condIV_exchange_final` 完全無条件(MST,MPT,hp,cIV,n≥1)——勝ち筋: r39 condIII route は jm3-slice anchored で branch+ltJ のみ要(admeq不要)、non-admeq では ltJ が Adm-maximality(adm_Adm_max+jm2<j0)から直に出て、kind1 anchor u=e1jm3<v1 は無条件→縮退 e1jm1=v1 host も u=v fseq 不要で被覆(cnv_ 10補題、cIII専用 bricks は1段深い nest mirror cnv_A0lt_of_nest/cnv_base1_of_nest/cnv_base0_of_run で置換、uniform deep hole pair+scb_unique_sb)。旧樹: 命題[r46]=(2)降下r1/(1)(3)r1/condIV枝r1/mnform r3/組立r12(producer r1+HB r1+regime r10=cpx r8[0.314][1.29h]+brick r1[0.250][1.04h]+nonadmeq r1[0.279][0.28h])/❌d13x r2/condIII再構築r26(engine r6+BT r1+REGS r4+M0RUN r7+trunk r1+slx37 r5+compose r1+noParent r1[0.279][0.28h])。補題8本[r10]。¬hasParent-condIV corner は §8.7 dispatcher 配線で要否判定(wave-2)〕
  - ✅ §8.5 条件 (V) の下での展開規則[r33]
    <!-- 詳細: 命題(交換)=adm `m_8_5_Trans_oper_exchange_condV_adm_uncond`[r3]+nadm `atx_Trans_oper_exchange_condV_nonadm_uncond`[r14, scbdec原典route]で全host無条件。
         non-adm c2L1=原典t2成分下界route `atx_condV_nadm_t2_components`→`atx_notLD`→`atx_c2L1`(atomA/atomB不要化、SHARP/s2x chainは consumerless死枝)。交換route=`wnx_nf3x`(W2nostr両消費点`wnx_W2nostr_c1/c2`)。
         ❌REFUTED: de-adm/WRAP route[r6]、universal KER、len2/redB(→REFUTED registry参照)。
         ⚰️SUPERSEDED(不要化): surgery spine-descent/keystone subtree(R1/R2/fold-C/netfold橋/leR成分…、[[pss-85-surgery-masterkey]]) — 交換命題がscbdec原典routeで閉じたため丸ごとobsolete。N3/Fのq非依存/基底前提discharge等は放棄。
         補題 Joints/FirstNodes/t2 = `m_8_5_Joints_FirstNodes_basic` parts(1)(2)。 -->
  - ✅ §8.6 条件 (VI) の下での展開規則〔交換(1)(2)(3)全host無条件: adm=`c613x_condVI_exch_adm`/nadm=`c6nx_condVI_exch_nadm_uncond`(A34/A37)。零化一般領域のみ❌A25(clean=`m_8_6_trailing_principal_peel`で足りる)〕[r6]
  - ✅ §8.7 主結果[r49]〔🎉**r72 完全達成**。KK を **記号数(symbol count)論法**で証明: hole principal は `ox12_szP (DB v 0)=1`、右spine を1段降りるだけで `ox12_szT (ox8_rsub t k) < ox12_szT t`(`ox12_sz_rsub_lt`)、よって `ox12_safe_of_size: szP p=1 ⟹ szT Z < szT W ⟹ ox11_safe`。**lex walk が hole に届かないのは「左辺が右辺より純粋に小さい木だから」**——位置解析も OT も guard も不要だった(r71 の位置版 transport `ox11_TT` が受け皿)。連鎖: `ox12_KK`/`ox12_KK_free`(無条件 KK) → `oi12_census`(両柱無条件) → `y5_Trans_OT_B`(=p_8_7_Trans_preserves_OT)/`y5_Trans_descend`/`y5_PSS_wf`(**仮定ゼロ**)/`y5_PSS_acc`/`y5_Fdom`(=**原文形 p_8_7_termination**)。全て build 強制監査 `assert_clean` に登録+`y5_PSS_wf` の閉性(前提/自由変数/schematic なし)も ML で assert。**緑ビルド=sorry非依存の証明**。cross-check: r72 front B は独立に KK を bottom guard へ還元し、「小さい body は存在しない」不変量を**反証**(43/680 の census-body principal が firsthead(b)<w、witness 記録済)、正しくは「低い head は必ず LEAF」と訂正——同じ機構の別描像で整合〕
