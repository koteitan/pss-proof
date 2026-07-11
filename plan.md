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
- **naive 再帰 frame-descent(devchain depth≥2)**: 「Trans(norm(last(Br M))) の body が (prev,dep) で終わる」は 0/22 反証 [r48]
- **sliceV0 witness route for ps=[]**(depdom): Dpt v0 (Dpt x q)=Trans M 自身のため shorter witness 不在(0/1721、忠実性矛盾) [r48]
- **slice-only slotAppg 還元(depOT⟹qcore/Gcore)**: 純含意として不可能(機械検証 CEX: q=Trm[DB 5 0],x=2 で qcore 偽/q=Trm[DB 1(Dpt 9 0)],x=2,v0=0 で Gcore 偽)。deposit-OT は isOT_BT q と GBT-x 半分しか与えない [r47]
- **from-joint deposit 同定(r44 C1)**: 挿入主項 D_x q = Trans(seg M j0'(Lng M-1)) は偽(33/33、slice Trans は D_{M10}-tree 全体)。正=原文 P(N)_J1[n] 枝成分 [r45]
- **抽象 all-u SETLE1(OTint、r59)**: b1x_setle(GBT u A1)(insert X1(GBT u X1)) は base0/base1 満たす一般 OT A0 で偽(53669/119877 fail、CEX A0=[D_2[D_4 0]],u=0)。d4vx_ins wrapper nest で spine-body head transV が非有界。真になるのは実 A0=bpHeadT(Trans(Pred slice)) の §7.3/7.4 右spine head 構造のみ。base0/base1/tri0 だけからは証明不可 [r59]
- 経験検証の教訓: oper-only corpus と小cap(8000)は偽陽性を生む。brute straddle + cap≥30000 + Lng≥10 必須。

## 進捗ツリー（詳細注釈付き）
- ✅ §5 定式化
- ✅ §6 ペア数列の基本性質 〔全節完了(2026-06-11)。docs `reducedness.md`/`red-le-domain.md`/`slice-Br-descending.md`〕
- ✅ §7 Buchholzの表記系への翻訳 
- 🚨 §8 停止性 〔r18: capstone `m_8_termination_modulo_CF`=停止性は CF-META(原典Pred同時帰納)+`buc1_2_2`整礎 の2点に崩壊。CF が唯一の Fable target〕
  - 🚨 [Buc1] 引用sorry
    - ✅ Lemma 2.1 lessBT 狭義線形順序〔`lessBT_irrefl`/`lessBT_trans`/`lessBT_total`(既存 layerB)〕
    - ✅ Lemma 3.2a+3.3 OT閉包の直接証明〔`m_buc1_3_2a_fseq_lt`/`m_buc1_3_2_OT_B_closed`、副産物`b1x_operB_dom_all`〕[r1]
    - 🚨 Lemma 2.2 `(OT_B,<)` 整礎性 `buc1_2_2_OT_B_wf`〔停止性の最終外部引用。順序型 ψ₀(ε_{Ω_ω+1})=真の external-grade〕
      - ✅ principal順序への還元〔`m_buc1_2_2_OT_B_wf_via_principal`、多重集合層証明済・両方向同値〕[r1]
      - 🚨 `wf RPrel`(principal lessBP 整礎)
        - ✅ depth有界断片(無限・無条件)〔`wfpd_wf_goal_dep`、norm断片⊂depth断片、wf⟺unbounded-depth chain無〕[r2]
        - 🚨 unbounded-depth chain排除→level jump 1本化〔r51 で構造確定〕
          - ✅ level-0 acc無条件+goal≡wfs_level_jump+wellorder/rank基盤(wfs_)〔r51 Fable: **wfs_level0_acc 無条件**(ε₀級 base case)=STRAT-0(level-0 の下方閉性、size 帰納のみ・G条件不要)+DEPTH-MONO-0(level 0 では order が depth を bound)+既証 depth 断片 wfpd_wf_RPrel_dep。**goal wf(OT_B,<)≡単一残差 wfs_level_jump**(level n acc⟹level n+1 acc、wfs_wf_RPrel_of_level_jump/wfs_OT_B_wf_of_level_jump)。基盤: wf_ordLess は Main で使用可(<o 記法は無効、定数 ordLess2)/wfs_accord=accessible part 上の Well_order/semantic rank wfs_rk=前者制限、RPrel で ordLess 単調。⚠️**DEPTH-MONO は level≥1 で偽**(D_0(D_1 0) の下に無限深 D_0 塔)→depth-断片吸収 trick は jump に lift 不可(再走禁止)。⚠️罠2件: fun-simps が =0 iff より先に発火(wfs_max_eq0 を simp に)/acc_downward+blast は発散(OF/rule で)。順序数算術(oexp/osum)は Main に無い——rank は predecessor-restriction で回避済〕[r2][0.423][0.73h]
          - 🚨 wfs_level_jump→collapse_core再尖鋭化〔r52 で構造刷新〕
            - ✅ lvP-STRAT反証→head-index STRAT+frag+G-set/tuple-acc bricks(wfj_)〔r52 Fable(+salvage): **STRAT-n(lvP版)は n≥1 で反証**(witness D_0(D_k 0)<D_1 0——低 head の下で max-index は跳ねる、REFUTED registry 入り)→真の層化=**head-index STRAT**(wfj_hd_le/wfj_strat_hd)。head-index fragments wfj_frag(下方閉・単調)+per-level wf goals。⚠️frag_0=ψ₀-collapse 済全 segment=易しい base は無い。**残差再尖鋭化: `wfj_collapse_core`**(secured-coefficient principal が acc)+size 帰納 bootstrap で collapse_core⟺wf RPrel⟺wfs_level_jump、[Buc1]2.2 readback 済。G-set bricks(G_v 元は真 OT+dfree 部分項)+tuple-acc(wfj_NoBad_acc/wfj_tuple_acc/wfj_secT_tuple_acc、chunk4 は post-green pre-commit salvage)〕[r1][0.284][0.25h]
            - ✅ bookkeeping全消去+非可述性確定+staged ladder(wfc_)〔r53: **head/tuple/secured の簿記を全消去**——同head枝=`wfc_principal_acc_of_body`(RTrel acc-帰納)、head再帰=`wfc_wf_of_pbody_hyp`(有限 head index 強帰納 via wfj_strat_hd)→**残差≡wfc_pbody_acc(body accessibility)≡wf RPrel**。tuple 反射 `wfc_tuple_acc_iff`。lvP-staged bootstrap: `wfc_jump_step n`(level-n acc⟹core up to head n+1=[Buc1]2.2 の超限再帰 step そのもの)+`wfc_wf_of_jump_steps`。🚩**非可述性確定**: accI step の strict-head 枝 q=D_u w(u<v)の body w は完全に無制約(lessBP は head 先行比較)——v=1 で既に frag_0(ψ₀-collapse 済全 segment、lv 非有界)全体の acc を要求→**(v,tuple) 上のいかなる wf 帰納も不可**。route: (a)**Buchholz-Schütte distinguished sets(Fundierung、HOL の非可述内包で十分、見積4-8R)**(b)surrogate-Ω 意味論(HOL wellorder、Ω_v=非可算共終度)。Isar教訓: 汎用 wf_iff_acc+blast 発散→rule [THEN iffD1]/GBP if-guard 下の bex witness は auto 不可→明示 UN_I〕[r1][0.239][0.35h]
            - 🚨 pbody-acc本体(distinguished sets route)
              - ✅ 定義+Mset+D1 union+acc bridge+基本閉包(wds_)〔r54(緑1+post-green salvage 1): **Buchholz-Schütte distinguished sets の定義が通った**(本丸の20%)——distinguished 述語+線形性経由の比較可能性+Mset=⋃{X. distinguished}+union 補題(D1)+acc bridge+下方閉包〕[r1][0.233][0.21h]
              - 🚨 collapse補題(D3)+ladder接続〔D_v の collapse(secured body over M_{v+1}→M_v)の statement+証明、wds_pbody_of_collapse で wfc_pbody_acc→[Buc1]2.2 へ接続〕[r0]
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
  - 🚨 §8.7 主結果
    - ✅ 補題（公差 $(0,0)$ のペア数列の $\textrm{Trans}$ の基本性質）〔`m_8_7_const00_Trans`〕
    - 🚨 補題（基本列の降下性）〔`fseq_descend`〕
      - ✅ dispatcher〔`m_8_7_fseq_descend_dispatcher`、7 named交換前提modulo、6439/6439〕[r1]
      - ✅ condV脚(adm+nadm)discharge〔adm=`m_8_7_fseq_descend_dispatcher_admV`/nadm=`atx_fseq_descend_dispatcher_Vclosed`〕[r2]
      - ✅ condI脚discharge〔`scx_condI_exchange1`+`scx_condI_descent`(j0=0/j0>0両方)〕[r1]
      - ✅ 全交換slot discharge+census(dpx_、exchIV/VI無条件化込)〔r46 Fable: `dpx_fseq_descend_census`=基本列の降下性 modulo **正確に{TOT,TVall}のみ**。6 slot 全discharge: exchI=scx/exchII=c2sx(modulo TVall のみと確認)/exchIII=npx_exchIII_slot_uncond/exchIV=**新`dpx_exchIV_slot_uncond`**(hasParent=cnv_condIV_exchange_final k=m strict、noParent=`dpx_exchIV_noParent` k=0 readback via cnv_c2_shape_condIV 二分、w≥e が condIV 不等式そのもの)/exchV=atx_nf3x/exchVI=**新`dpx_exchVI_slot_uncond`**(c613x adm+c6nx nadm)。condIV-noParent corner: transCondIV⟹hasParent は T_PS で偽(CEX (1,1)(2,2)(3,3)(3,1) 非reduced)、RT_PS∩PT_PS では経験的に空(0/163 deep)だが構造証明で閉(空でも有効)。⚠️seed draft の偽 empirics 主張(CEX を reduced と誤記)を python 再検証で訂正してから commit〕[r1][0.306][0.31h]
      - ✅ assembly census(asx_、長さ帰納不可能を証明、fseqD/TOT消去)〔r48 Fable 中心結果: **長さ指標 joint 帰納は r46/r47 エンジンでは証明不可能**——EDGE-1(mdx_P_allpairs の生成帰納は fseqD を「生成祖先の最終P成分」で消費、最終 host 長で非有界・stage 有界のみ)+EDGE-2(dpr_dev 鎖も長さ非有界)+a5/長さIH は測度の長さ単調性を強制→矛盾。stage-first も Pred=M[1] が stage を跨ぎ a5 が全長域量化で対称に失敗。原文(6127-6360)の k₀ 帰納は A38(反証済)に乗る——mechanized rgx が length-first なのはそれが理由。**成果 `asx_termination_census`**: 両柱(全標準 M の OT+strict 降下)を modulo **正確に {slotNewOT,slotTail,slotAppg,slotHeadWB(r47形verbatim), TVall(r46形), AP}**——fseqD/TOT は census 出力から導出し消去(knot を Isar で明示: asx_fseqD_derived/asx_allpairs_of_fseqD)。`asx_devchain_takeover`=devchain は census 出力を入力に slotNewOT+slotTail を discharge(post-knot でのみ使用可、EDGE-2 ゆえ census 内に折込不可)。n=1 の fseqD 使用は Pred-dischargeable(m_7_3_Pred_Trans_descend)、n≥2 のみ genuine〕[r1][0.219][0.18h]
      - ✅ AP接地+census{OTint,OTpred,OTmulti,TVall}化(apx_、otx dispatcher route)〔r49 Fable: route-A(補正A38 reachability)は **r28 で反証済だった**(otx_stepval_refuted: Trans(M[1]) が Trans M の full fseq-closure に無い、host (0,0)(1,1)(2,2)(3,2)(4,2))→逆向きに knot を切断: **r28 世代 dispatcher otx_Trans_preserves_OT_dispatch は AP-free な OT 柱**で、その exchange 残差は今や閉(exchI=scx、exchII=c2sx modulo TVall)。鎖: {OTint,OTpred,OTmulti,TVall}⟹OT-all(ST_PS.induct=stage帰納そのもの、apx_Trans_OT_all_of_otx_slots)⟹global descent(apx_descent_of_otx_slots、TOT定理化)⟹fseqD(apx_fseqD_grounded)⟹AP(mdx 経由)。capstone `apx_termination_final`=**両柱 modulo {OTint,OTpred,OTmulti,TVall}——AP と rgx 4 slots は census から消去**。抽象1残差版 `apx_termination_final_of_step`(modulo {OTstep,TVall})も。multiD keystone 接地(apx_multiD_grounded)〕[r1][0.181][0.14h]
      - 🚨 残=census modulo{SETLE1_ltJ,FINRC}(oi8_census_final_ivadmeq、両柱)〔r55: oi6_termination_census が両停止性の柱(∀M∈ST_PS. Trans M∈OT_B / 基本列 lessBT 降下)を **{OTA1,SETLE1,IVADMEQ,IVNP,FINRC} のみ modulo** に成立。DEEPOT/NOBR は od4(front B)で discharge 済、otIII/otIV は 4事実へ還元済。残る5残差=一ブロック塔 isOT_BP/setle 計算4本(OTA1/SETLE1/IVADMEQ/IVNP)+FINRC(nth-artifact、§8.2 fin と同格)。🚩**循環警告**(過去): orx_ 経由 multiD 接地は循環不可、独立 closure は per-condition 値形(§8.5 masterkey/scbdec)。OT柱は §8.7 補題（Trans が標準形を保つこと）配下で追跡〕[r0]
    - ✅ 補題（順序数項の再帰構造）〔`m_8_7_OT_scb_recursive`〕
    - ✅ 補題（順序数項の共終数の遺伝性）〔`m_8_7_OT_dom_hereditary`〕
    - ✅ 補題（順序数項の末尾項の零化可能性）〔top-level=`m_8_7_toplevel_OT_tail_annihilate`。一般化のみ❌A26(operB全域性)〕
    - ❌ 補題（$\textrm{Pred}$ と $[0]$ の関係）〔A27、6325ルート迂回〕
    - ✅ 補題（順序数項の基本例）〔`m_8_7_OT_examples`〕
    - 🚨 補題（$\textrm{Trans}$ が標準形を保つこと）= OT所属〔残=R2 dstep+R3 newOT/gbt+帰納組立〕
      - ✅ clean部（rank0/T_B/単項leaf）〔`m_8_7_Trans_*`〕
      - ✅ 還元 isOT⟸R1/R2/R3〔`m_8_7_OT_via_body`+`descP_snoc`/`m_8_7_isOT_BT_snoc_leBT`〕
      - ✅ 4-case dispatcher〔`m_8_7_OT_keystone_step`、step→{det,[Buc1]}〕
      - ✅ wid/det〔=§8.2 widH、`m_8_2_widH`/`m_8_2_det`〕
      - ✅ 帰納 infra〔`m_8_7_Pred_ST_PS`/`m_8_7_Trans_OT_step_keystone`〕
      - ❌ stepval(交換value恒等式)route〔A38: `otx_stepval_refuted`(充足不能、原文6216はA25-A27帰結で偽)。`_via_closure`/r21 svx系はvacuous死没〕[r2]
      - ✅ 置換capstone〔`otx_Trans_preserves_OT_dispatch`(ST_PS.induct)、modulo{exchI,exchII,OTint,OTpred,OTmulti}、exchI/exchII=降下dispatcherと共有〕[r1]
      - ✅ per-branch true legs〔`otx_stepval_condVI_adm/_nadm`/`_condI_j0z/_n1`/`_j1eq1`×2/`_zerocol`、exchI j0=0半分discharge〕[r1]
      - ✅ dispatcher slots discharge(orx_)〔`orx_OTint/OTpred/OTmulti`+`orx_Trans_preserves_OT`。ただしm_8_7_Trans_preserves_OT_modulo経由=下記{resid,multiD}に依存〕[r1]
      - ✅ local-OTint keystone-free(condI/condVI/condV-adm-e=0)〔`otlx_OTint_local`+`cfvx_OTint_local_condVadm_corrected`。**cfVadm(condV-adm op0-tower)はe>0で偽**(r34、CEX (0,0)(1,1)(2,2)(3,1)(4,2)(4,2))→e=0のみkeystone-free。cf0(e=0 op0-tower)はnamed、証明可〕[r2]
      - 🚨 OTint(値形OT-step)〔r51 で condV 完了、残=transport 核+III/IV〕
        - ✅ condV脚(adm+nadm)閉 modulo oix_transport(oix_、band-exclusion)〔r51 Fable: A24補正値形(m_8_5_scbdec_adm_forms/nfx_NFall)で Trans(N[Suc k]) と operB(Trans N)(numBT n) を**同一 (s1,b1) hole の塔** D_h(block^k(t2))/D_h(block^n(D_e 0)) として表示(fun oix_twr、nadm の e5x cores も文字通り同塔)。sandwich W_k≤V_k≤W_{k+1}、donor は [Buc1]3.2 閉包+slot 自身の IH で OT。newOT=新 brick `oix_G_prefix_lt`(host 自身の OT3 guard から G_e t2<t2 を band-exclusion で抽出)/nadm は rebase head u≤e を G-antitonicity で。setle は仮定なし。`oix_OTint_condV_adm`/`oix_OTint_condV_nadm`(後者 modulo {PredNp,Lpv,L1v}=§8.2 系降下柱既 carry 3点)。⚠️STEP-0 PART B の python condV 判定にバグ(t2=0 誤分類)——本質結論は r34 CEX host で個別検証済だが再走せず(spend 配慮)〕[r1][0.322][0.47h]
        - ✅ oix_transport定理化(otx2_ bricks+otx3_組立、condV脚無残差)〔r52 bricks(otx2_ 12本)+r53 組立(otx3_core=size t' 強帰納 along align3、不変量=sandwich順序+[Buc1] triG G-control。insert-aLo corner は「左G集合は u>w で消滅」で新empirics不要(r52 STEP-0 15934/15934済)。各level guard=b1x_G_control、descP-last=HIGH donor、prefix=LOW donor、OT組立=m_8_7_isOT_BT_snoc_leBT)。`otx3_transport`無条件定理→`otx3_OTint_condV`(adm脚 residual-free)/`otx3_OTint_condV_nadm`(modulo {PredNp,Lpv,L1v})〕[r2][0.523][0.60h]
        - ✅ base3{PredNp,Lpv,L1v}討伐(oi4_+oc4_L1v、nadm脚無残差)〔r54 salvage(緑コミット fcf6434): {PredNp,Lpv,L1v} を wnx/nf3x/nf2x/atx 降下 bricks から定理化(oc4 の PredNp route 分析と独立に閉じた)。condV-nadm OTint 脚無残差、OTint slot modulo {otIII,otIV} のみ〕[r1][0.233][0.21h]
        - 🚨 otIII/otIV脚(一ブロック塔4事実へ還元)〔r55 front A(Fable、緑到達後 spend limit で死亡→salvage、heap-verified 緑 draft を Opus が回収統合、c6a41b0→9b97c72)。otIII/otIV=host-level deep-insertion を **一ブロック塔の isOT_BP/setle 計算 4事実** {OTA1(condIII/IV共通 d4vx_ins 塔の isOT_BP)、SETLE1(同塔の GBT setle)、IVADMEQ(condIV adm=transJm1 隅)、IVNP(condIV no-parent 隅)} へ還元。machinery=oi5_OTint_condIII/condIV(oi4_OTint_slot_IIIIV に注入)。cpx_condIII_mnform/cnv_c2_shape_condIV/oi5_regime/oi5_d4vx_* 経由。census 系(oi5_termination_census)は {4事実,DEEPOT,NOBR,FINRC} modulo〕
          - ✅ 還元machinery(oi5_OTint_condIII/condIV)〔host-level→一ブロック塔4事実。oi5_IIIIV_pkg/oi5_OTint_IIIIV_hp 経由、oi4_OTint_slot_IIIIV で slot 化〕[r1][0.775][2.06h]
          - 🚨 {OTA1,SETLE1}(condIII/IV共通塔isOT_BP/setle計算)〔d4vx_ins s0 (e-1) b0 (bpHeadT(Trans(Pred(s84x_N P)))) の isOT_BP と GBT setle。両者 STEP-0 で真(899/899)。**setle_body は偽(u=0)→naive otx3_core route 死、otx3_core_tri+tri0 を使う**〕
            - ✅ tri0 CRUX(scbext_triG engine+crx/cnv_tri0_of_nest、ltJ不要)〔r57 front A: scbext_triG=b1x_triG の fixed-z wrapper lift(right-spine align3+Dpt/addBT、b all-RP で right-spine-pinned なので各context levelが b1x_triG_Dpt+b1x_triG_addBT 1つずつ、join不要)。ot1_triG_grow/ot1_triG_add=trivial-base成長制御。crx_tri0_of_nest(condIII)/cnv_tri0_of_nest(condIV)=crx/cnv_base1_of_nest と同一前提(ltJ不要)で共有(u1,v1w)wrapper 再exposeして lift。tri0=b1x_triG z A0 X1〕[r1][0.297][0.65h]
            - ✅ ltJ再スレッド+oi8 census(OTA1を単一A0OTへ還元)〔**構造発見(r57)**: census OTA1/SETLE1 は forall-P だが oi5_OTint_IIIIV_hp は ltJ host でのみ適用(condIII=常時ltJ/condIV-admeq→IVADMEQ/condIV-not-admeq→cnv_condIV_ltJ/no-parent→IVNP)。forall-P が唯一の障害(admeq で ltJ 偽)。**r58 front A: oi8_ chain(oi8_OTint_IIIIV_hp/condIII/condIV/census を ltJ付き OTA1/SETLE1 に書換)で census を {OTA1_ltJ,SETLE1_ltJ,IVADMEQ,FINRC} に**。さらに OTA1_ltJ を単一事実 **A0OT=isOT_BT(bpHeadT(Trans(Pred(s84x_N N))))** へ還元(ot1_OTA1_reduce→{nub,tri0}/ot1_tri0_census=tri0討伐/ot1_nub_from_A0OT=nub←A0OT via otx3_pOT/ot1_OTA1_from_A0OT)。capstone **oi8_census_via_A0OT=両柱 modulo {A0OT,SETLE1_ltJ,IVADMEQ,FINRC}**〕[r1][0.284][0.59h]
            - ✅ A0OT(=isOT_BT(bpHeadT(Trans(Pred(s84x_N N))))、OTA1柱完結)〔**crack**: od4_OTpred_mono は ST_PS を 809-811行(MR:RT_PS/MP:PT_PS 導出)にしか使わない→od4_OTpred_mono_RT(RT_PS+PT_PS版)。**訂正(r59)**: raw slice s84x_N N は一般に reduced でない(adm≠対角条件)ので、**RN=Red(s84x_N N)∈RT_PS(slice と Trans値共有)経由**で od4_OTpred_mono_RT を RN に適用し m_7_4_Trans_PredN で戻す。Trans RN∈OT_B=census kind-1 scb-subterm D_e3 body を m_8_7_OT_scb_recursive(+e2x_Trans_principal_head/m_6_6_Red_leftend_1 で head同定)→bpHeadT=otx_bpHeadT_OT。ot1_A0OT+capstone oi8_census_final(両柱 modulo {SETLE1_ltJ,IVADMEQ,FINRC})〕[r1][0.230][0.56h]
            - 🚨🤖 SETLE1_ltJ(engine ox6_setle_scbext済、残=§7.4 ancestor head bound)〔**NEGATIVE(r59)**: 抽象 all-u setle は一般 OT A0 で偽(REFUTED registry)。真は実 A0=bpHeadT(Trans(Pred slice)) の右spine head 構造による。**r60 front A: head bound を実host 146/146 で検証(真)**+SETLE analogue engine `ox6_setle_scbext`(scbext_triG の setle版、right-spine 帰納 measure_induct+otx2_align3 で target を hole/shared/spine の3 escape family に分解、hole=ox6_holeH(base1+ox5_body_driver)/shared=GBT u X1 に無条件 discharge)。ox6_setle_wrapped/ox6_SETLE1_reduce で census 残差を **ancestor bound(spineH: 各右spine ancestor body lbA=d4vx_ins の flatBT sc@D_ub A0@bc に leBT lbA X1)** に局所化。⚠️engine の spineH は universal 形で stronger-than-true(小tree で大head index 可能)——真は ancestor-RESTRICTED bound のみ。残=①ox6_setle_scbext を suffix/prefix 制限付きに再スレッド(align3 peel の hole-position cancellation)+②§7.4 Mark/RightAnces(m_7_4_Mark_Trans_repr/RightAnces_dom_RT/Mark_leftend_form)で実ancestor の head bound 証明。target は ANTITONE(X1≤A1≤X2 なのに A1 escapes は X1-bounded)なので triG-of-A1 では閉じない〕[r2][0.481][1.13h]
          - ✅ IVNP(condIV no-parent隅=Pred除去、ot2_IVNP)〔condIV∧¬hasParent は P[m]=Pred P(M1j1>0)なので純 OTpred step。r56 front B(Opus): ot2_IVNP=od4_OTpred_final[OF NST ihOT L](condIV/no-parent 仮定は捨てる、無仮定 master)。STEP-0 admeq corner 96/96 真〕[r1][0.257][0.65h]
          - ✅ IVADMEQ(condIV adm-eq隅、SETLE-free tower engine+Red-slice regime、ot2_IVADMEQ)〔Adm P (s84x_jm2 P)=transJm1 P、**標準condIVの47/48がこれ**。r57 ltJ-free admeq mnform c4cx2_condIV_mnform_of_slice(clean hole transT2 P)+r58 NEWOT engine(ot2_tower_newOT/inv、TRI route=SETLE不要)→残差{d1,d2,d3,HB}。**r60 front B クローズ**: ot2_transT2_OT(=isOT_BT transT2、ltJ-free の ot1_A0OT mirror、c4dx_condIV_k1 admeq kind-1+Trans(Red(s84x_N))→od4_OTpred_mono_RT)+cnv_tri0_transT2(hole tri0 直接、c2body dichotomy+ot2_dins_addBT_of_shape)+ot2_IVADMEQ_of_pkg_free(SETLE-free、otx3_core_tri at head e3)+{d1,d2,d3,HB}=Red-slice regime(mcx_regS/slx37_regSP jm3<jm2 guard、admeq corner jm3=jm2 は cpx_d2/d3_condIV が内部 case-split で吸収=新variant不要)。capstone oi8_census_final_ivadmeq=両柱 modulo {SETLE1_ltJ,FINRC}〕[r4][1.074][2.60h]
      - ✅ OTpred(with-parent Pred corner OT-step、無仮定master od4_OTpred_mono→od4_OTpred_final無残差)〔r53 keystone 4-clause分析(opx_: fresh閉 opx_OT_removal/multi junction=m_7_3_Pred_Trans_descend/corners閉)[r2][0.262][0.30h]→r55 front B: r54 draft修理(od4_R_cons切除=死コード+cases構文エラー源、od4_transfer を forall形に書換=幽霊case束縛エラー根治)+**無仮定 master `od4_OTpred_mono`**(mono ST host、1<Lng、Trans M∈OT_B⟹Trans(Pred M)∈OT_B、Br/cond/shape仮定なし——DEEPOT/NOBR は verbatim 系、od4_DEEPOT の hW/pW 仮定は vacuous)。エンジン=trans_surgery_localized 共有(s1,b1)wrapper+od4_site_c2(全transC2枝: I/III/V=drop、else=drop/deep+drop(PB/ΣBリスト代数)、condVI adm=t2:0(c6gx)、condVI nadm=新形状補題 od4_condVI_nadm_c1: Mark-Trans repr+wnx_run_entries+rebase→diagSeq+m_8_1_diagSeq_Trans で t2=D_{M1j0}0 triv)+un-insertion順序代数(od4_R 3-clause/od4_transfer_all=共通prefix peel+size argument/od4_GBT_sz=G_B escape縮小/od4_scbext_R=otx2_align3 lift)。経験検証(od4_r55_check.py 再走): brute reduced-mono 550+ST_PS BFS 654=1204 hosts、MASTER/SITE/OT保存 0fail、condVI t2形状 adm 136/136+nadm 21/21。census v4(base視点)={OTint,TVall,ordIntC}→main視点残={otIII,otIV,FINRC}。wt-s4b commits e181e2f+e55d40a、緑独立検証済〕[r4][0.817][1.41h]
      - 🚨 OTmulti(⛔OTint残差 SETLE1_ltJ のみ: oi5_OTmulti還元済)[r3][0.495][0.51h]〔r53 opx_OTmulti(operB局所化、junction-free 脚I/II/VI、replicate=m_8_1)[r2][0.262][0.30h]+r54 oc4_ordIntC **クローズ**(strict lessBT を全6枝で閉じた exchange 定理群から: III=cpx(2)/III-noParent=npx+3.2a/IV=cnv(2)/IV-noParent=dpx+le_less_trans/V=m_8_5 adm+atx nadm)+`oc4_OTmulti`=slot modulo {OTint,TVall} のみ→r55: oi5_OTmulti が OTint と同じ4事実 modulo に還元(⛔OTint slot 解消、4事実共有待ち)。**r55 synthesis: oi6_termination_census が od4_DEEPOT/od4_NOBR で DEEPOT/NOBR を discharge → 両停止性の柱が {OTA1,SETLE1,IVADMEQ,IVNP,FINRC} のみ modulo**〕
      - 🚨 deep-insertion OT所属(keystone{resid,multiD}、r49でcritical path外)〔r35: 4脚→単一 keystone {resid,multiD}(`orx_OTint`)。r40b(Fable): **resid を deep検証(真、1468/0、最大Lng43、pcompPrefix と違い偽陽性でない)+4slot分解**。keystone `m_8_7_Trans_OT_step_keystone` の resid slot が強IH+Trans(Pred M)∈OT_B を受領する形に再構築(`rgx_Trans_preserves_OT_of_slots`)。反証registry: operB(term z)/最右spine scb-substitution/pcompPrefix 偽〕[r5]
        - ✅ resid deep検証+4slot分解(rgx_、C3 prefix半分クローズ)〔`rgx_resid_of_parts`(MASTER: resid C1∧C2∧C3 ⟸ {newOT,tailEH,appg,headWB}+Pred-OT、m_8_2_keystone 再走+snoc realign)。C3 prefix半分は `rgx_between_extends`([Buc1]辞書順区間)+`rgx_gbt_prefix_restrict`(b1x_GBT_size)で無条件クローズ、C3⟸appg(`rgx_gbt_of_appg`)。C2 whole-body Admpos 閉、`rgx_dstep_*` dispatcher〕[r1]
        - 🚨 slotNewOT(C1: isOT_BP(DB x q))〔r44発見: 挿入主項 D_x q = **from-joint 終切片 Trans**(seg M j0'(Lng M-1)、j0'=Joints M!(Lng(Br M)-1))。a6-scb transport は DEAD(deposit は Trans(Pred M) の scb-subterm でない 3/34)→唯一の筋は Lng-IH a5 を deposit-slice(短い標準列)に適用〕
          - ✅ shorter-slice IH還元(snx_)〔`snx_newOT_of_sliceTrans`=「N∈ST_PS, Lng N<Lng M, Trans N=Dpt(enat x)q ⟹ isOT_BP(DB(enat x)q)」を a5+isOT_BT→isOT_BP 展開で。`snx_slotNewOT_modSlice`=正確8仮定 modulo packaged deposit-slice存在。両 green〕[r1][0.193][0.32h]
          - 🚨 deposit-host存在(=devpair、slotTail側と共有)〔r46: `dvx_two_slots_of_devpair` により slotNewOT の slice 残差は devpair の EX-N 半とマージ——devpair 1本の討伐で本項も閉じる〕[r0]
        - 🚨 slotAppg(C3: G_B-bound)〔r44: appg 真 984/984(deep Lng≥20:21/21)。`rgx_appg_split`で {qlt,Gq} 分割、v0>x(空G_B集合)/q=0B(自明)は無条件 discharge〕
          - ✅ guarded還元(sax_modcore、v0>x/q=0 discharge)〔`sax_slotAppg_modcore`=正確結論を rgx_appg_split 経由、genuine 内容を q≠0B∧entry M 1 0≤x の2残差 sax_qcore/sax_Gcore に隔離。green〕[r1][0.193][0.32h]
          - ✅ modDom/modSliceGaps緑frame(hgx_、slice-only還元は反証)〔r47 Fable: **slice-only 還元(depOT⟹cores)は機械検証 CEX 2件で不可能と確定**(q=Trm[DB 5 0],x=2: isOT_BP 成立でも qcore 偽/q=Trm[DB 1(Dpt 9 0)],x=2,v0=0: headgap 込でも Gcore 偽=G_B-escape に独自 bound 要)。緑 frame: route A `hgx_slotAppg_modDom`=slot束 modulo {depdom,deple}(depdom=∀y∈GBT v0 (Dpt x q). lessBT y (Dpt x q)=isOT_BP(DB v0 …)の G_B 半分、1580/1580 empirical。deple=C2 結論、rgx_resid_of_parts 順で acyclic)/route B modulo {slice(snx と同形),headgap,gextdom,deple}。`hgx_depdom_of_sliceV0`=v0-rooted witness(Trans N=Dpt v0 (Dpt x q))から depdom 全量(ps≠[] 向き)。slotHeadWB: `hgx_slotHeadWB_of_deple` は存在するが **wiring 循環**(corner の deple は headWB から導かれる)→独立 deple 源(§8.2 keystone witness/m_8_5_basecut_residual route)が要る〕[r1][0.406][0.51h]
          - ✅ ps=[]主要部還元(ddx_、pred-depdom無料+transfer append形)〔r48 Fable: STEP-0 で地図刷新——**ps=[] が 99.1%(1721/1737) で、そこで Dpt v0 (Dpt x q)=Trans M 自身→sliceV0 witness route は ps=[] で DEAD**(0/1721、忠実性と矛盾するため)。ps=[] では keystone が常に deepened case(3)/(4)+pred body=単一同 head 主項(1721/1721)→**pred 側 depdom は a6 から無料**(`ddx_preddom_of_predOT`)。`ddx_keystone_realign`(fresh 1/2 vs deepened 3/4)+`ddx_transfer_append`(top-level append 形 q=q'+B Dpt w 0B, w≤x での transfer 証明済=condI/III/V/VI anchored _c2 形)+`ddx_depdom_modResid`+`ddx_slotAppg`(modulo {freshdom,preddomNE,transfer}+deple)〕[r1][0.219][0.18h]
          - 🚨 transfer一般形(keystone強化、r49でcritical path外)〔r49 front は月次limit で recon 中に死亡・成果なし。apx census 昇格により rgx slot 塔(deep-insertion)は critical path 外へ——ただし OTint 値形 closure が ddx/hgx bricks を再利用する可能性はあり、保存〕[r1][0.181][0.14h]
        - 🚨 slotTail(C2: leBT q qb、真)〔r44 偽チェック=TRUE(0-fail)。r45: 比較相手は M 内部の前枝 deposit qb であって Pred 残余 qp ではない(r44 が混同)〕
          - ✅ proper-prefix半還元(stx_→qp-descent、後にroute死)〔`stx_slotTail_properprefix_from_descent` は緑のまま残るが descent 仮定 leBT q qp が r45 で反証され DEAD route〕[r1][0.193][0.32h]
          - ✅ qp-descent反証(33/33逆向き)+slot束→devel単一残差化(spx_modDevel)〔r45 Fable: **leBT q qp は ST_PS で偽 33/33**(yaBMS標準確認済CEX: M=(0,0)(1,1)(2,1)(1,1)(2,1) q=D_1(0),qp=0_B 等3件)。真の向きは逆=Pred は trailing deposit を縮める。**併せて r44 C1 from-joint 同定も反証**: Trans(seg M j0'(Lng M-1)) は D_{M10} 全体であって deposit でない(33/33 mismatch)、正 witness=原文 P(N)_J1[n] 枝成分。緑: `spx_slotTail_eqhead_of_deposit_hosts`(same-head strip core)+`spx_slotTail_modDevel`=slotTail slot 束(proper-prefix+whole-body 両枝=rgx dispatcher の tailEH slot)を単一 packaged 残差 devel に還元。devel=∃N N'∈ST_PS 短Lng: Trans N=Dpt x q ∧ Trans N'=Dpt hdv qb ∧ (N=N' ∨ lessBT(Trans N)(Trans N'))。EX-N 半は snx C1 slice 残差と一致(1 witness pair が両 slot に効く)〕[r1][0.279][0.28h]
          - 🚨 devel残差〔r46 で devpair に尖鋭化〕
            - ✅ devpair尖鋭化+2slot同時consumer(dvx_、成分標準性+A16同定)〔r46 Fable: 緑bricks=`dvx_standard_component`(P成分の標準性、m_6_7 経由 ST=⋃SkT lift)/`dvx_standard_last_component`/`dvx_multi_last_principal`(A16補正 last-principal 同定)/witness 生成器(原文 a_2=Trans(P(N)_J1[n]) 機構、content 6287)。`dvx_devel_of_devpair`+consumer `dvx_two_slots_of_devpair`=**devpair 1 witness で slotTail+slotNewOT 両方閉**。⚠️無条件枝 readoff Dpt x q=Trans(last(Br M)) は吸収 D_0 0_B corner で偽(1/44、host (0,0)(1,0)(1,0)、witness は (0,0)(0,0)型)→witness レベルに留める。⚠️bms -s は枝 witness の標準性 oracle に不適((0,0) root 要求)〕[r1][0.306][0.31h]
            - ✅ D_0 0_B corner閉+devchain弱化(dpr_、単一step版unsafe)〔r47 Fable: corner(iii)完全クローズ=[(0,0),(0,0)]∈ST_PS を具体導出鎖 diagSeq 0 1→[2]→[2] で証明(dpr_corner_host_ST)+Trans 値→`dpr_devpair_corner`/`dpr_two_slots_corner`(降下柱 modulo のみ)。**単一step devpair は unsafe**(6/17 strict host で探索 fiber 内に単一step witness 無し、witness recipe=IncrFirst down-shift of Br M!(|Br|-2)、n∈{1,2,3})——**反証ではない**(fiber 非有界、深 [0]^k-zeroing witness 未探索)→REFUTED registry には入れない。残差を **devchain**(多step development 鎖、帰納 dpr_dev、ST所属は ST_PS.oper 閉包で無料、lessBT は降下+trans)に弱化、consumer 全再配線(dpr_two_slots_of_devchain が dvx 版を包摂)。🚩**原文 readback**: 原文(content 6190-6255)は深 witness pair を使わず mono host を Trans(N[n])=Trans(N)[m_n][0]^k+[Buc1]3.3 で処理——**ただし A38 で値等式そのものは反証済**、✅済の補正版零化(scb-decomp 形)を使う mono-host fseq route が本命〕[r1][0.406][0.51h]
            - ✅ IncrFirst正規化witness+corner框架(dcx_、modulo claim S+branchwit)〔r48 Fable: **r46 枝標準性障害を IncrFirst 正規化で解消(modulo claim S)**: `dcx_shift_standard_Trans`=Trans((IncrFirst^^k) N)=Trans N for 標準 N(ST⊆RT+Trans_funpow_IncrFirst)+`dcx_branch_Lng`=枝は host より真に短い(idxsum)。`dcx_devchain`=devchain を「non-corner branchwit」(∃j k N'. Br M!j=(IncrFirst^^k) N'∧N'∈ST_PS∧Trans N'=Dpt hdv qb∧…)から導出、corner は dpr_devpair_corner で処理。empirics: claim S(正規化枝の標準性)131/145 未反証・transport 145/145、witness recipe 43 host 中 corner7+浅部14、**深部(deposit 深さ≥2)22 host 未解決**(naive 再帰 frame-descent は 0/22 反証済——再走禁止)〕[r1][0.219][0.18h]
            - 🚨 branchwit(claim S機械化、r49でcritical path外・bwx brick回収)〔r49 front は 728行 bwx_ block(funpow IncrFirst 基盤/oper 退化 unfold/shiftstd intro)を書き上げた直後に月次 limit で死亡→親が検証ビルドで回収(緑なら統合)。critical path は apx census 昇格で otx slots へ移動〕[r1][0.181][0.14h]  ← r49末: 728行 bwx draft は回収を試みたが**未検証 draft に真の証明ギャップ4件**(70250: corner 値等式 x=hdv 前提落ち/70137: Br(M[n]) membership 直 by/69974: trunk-suffix 非空/69768: IncrFirst 下の idx1-hasParent transport)+ハング2件(P.simps ループ auto、blast——親が修理済)。draft+error log は `../bwx-draft-r49.patch`/`scratchpad/bwx-draft-errors.log` に保管、worktree は掃除済。将来の branchwit round はここから再開
        - 🚨 slotHeadWB(C2: deple読出しhgx_あり、要独立deple源)〔r47: `hgx_slotHeadWB_of_deple`(x≤hdv を deple から読出し)は緑だが、rgx_dstep_wholebody_case は corner の deple を headWB から導く=**この向きの wiring は循環**。独立 deple 源=§8.2 keystone witness/m_8_5_basecut_residual route が要る。真の内容は host-level order(局所 slot data の外)〕[r0]
        - 🚨 multiD(⛔ 基本列の降下性=fseqD)[r1][0.406][0.51h]〔r47 で降下柱の instance に解消(mdx_、slot消去): route=multiD→comple→all-pairs 隣接P成分降下 `mdx_P_allpairs_leBT_modFseq`(ST_PS 生成帰納)、P構造 bricks 全緑(m_6_2_P_oper_1/2 等)。唯一の残差 fseqD=mono leBT 降下=降下柱 keystone 弱形→降下柱(AP knot 経由)が閉じれば無料。consumer frame `mdx_Trans_preserves_OT_of_slots`(multiD slot 消去済)。⚠️E-mono が mono fseq を genuinely 埋め込む(79/79)→降下柱回避 route 再試行禁止。検証 349/349〕
