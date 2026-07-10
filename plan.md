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
- **並列度制限: 3 front/wave**（r29 6同時が session limit 全滅 → ユーザー指示で半減）。**モデル: Fable 残8%→ほぼ Opus 4.8+xhigh へ移行**(ユーザー switch 済)。
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
- **from-joint deposit 同定(r44 C1)**: 挿入主項 D_x q = Trans(seg M j0'(Lng M-1)) は偽(33/33、slice Trans は D_{M10}-tree 全体)。正=原文 P(N)_J1[n] 枝成分 [r45]
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
        - 🚨 unbounded-depth chain排除〔=ψ collapsing本体、非初等。外部`buc1_2_2`が唯一の残外部引用〕[r0]
  - 🚨 §8.1 条件 (I) の下での展開規則
    - 🚨 命題（条件 (I) の下での $\textrm{Trans}$ と基本列の交換関係）
      - ✅ 交換則(1)本体〔`scx_condI_exchange1` 完全無条件(j0=0+j0>0、marking-nesting二重帰納)〕[r4]
      - ✅ 降下(2) OT-free〔`scx_condI_descent`(d2x scbext route、OT柱回避)〕[r1]
      - 🚨 OT所属 (⛔ §8.7「Transが標準形を保つ」補題)
    - ✅ 補題（公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）〔`m_8_1_diagSeq_Trans`〕
    - ✅ 系（$\textrm{Pred}$ が公差 $(1,1)$ のペア数列の $\textrm{Trans}$ の基本性質）〔`m_8_1_Pred_diagSeq_Trans`〕
    - ✅ 補題（条件 (I) か (III) の下での $c_1$ 前後の具体表示）（A20/A21）〔part(1)-(5)+(4-1)(4-2) `m_8_1_c1_around_part4_1`/`_part4_2`〕
  - 🚨 §8.2 強単項性
    - ✅ 命題（標準形の直系先祖による切片の簡約化の強単項性）〔`m_8_2_standard_slice_Red_strongmono`〕
    - 🚨 命題（条件 (II) か (IV) の下での終切片と $\textrm{Trans}$ の関係）〔`p_8_2_condIIIV_terminal_slice_Trans`(pss_paper 1624)=condVのVE'のcondII/IV版〕
      - ✅ scaffold還元(∃!→{VE2,VE3,VE4})〔`cdx_condIIIV_scaffold`+`vgx_condIIIV_of_VE`(paper verbatim modulo {VE2,VE3,VE4,fin})〕[r1]
      - ✅ LastStep切片幾何基礎〔`vgx_LastStep_*`/`vgx_m1_bounds`/`vgx_slice_*_mono`/`vgx_slice_princ`。r30未発達だったのをゼロから整備。A39=LastStep Min-landmine発見〕[r1]
      - ✅ VE2(無条件、ROW10討伐)〔`vg3x_VE2`(=vg2x_VE2でROW10内部discharge)。`vg3x_ROW10`←`vg3x_row1_le_row0`(entry M 1 j≤entry M 0 j、任意reduced M、RedCondA/B only、monoT不要でm_6_6_condAB_coeffより一般、強帰納)〕[r3]
      - 🚨 VE3/VE4
        - ✅ back-peel skeleton(guarded、vg4x_reg4訂正)〔**r33のvg3x_reg3 BASEも偽**(vg2x_VE34は 0<j0'<TrMax=非admj0' が必要、CEX (0,0)(1,1)(2,2)(3,0)[j0'=TrMax]/(0,0)(1,1)(1,0)[j0'=0])。だが `vgx_condIIIV_of_VE` は既に j0pos+j0lt 供給→`vg4x_reg4` に訂正、`vg4x_VE34_backpeel`〕[r3]
        - ✅ RPERS〔`vg4x_RPERS`(STEPでPredは最終枝を短縮するのみ→j0'/TrMax/guard-node安定)〕[r1]
        - ✅ regime修正(vg7x⟺DT_PS、descending Pred保存)〔r37: `vg7x_reg4=vg4x_reg4∧descending(Br)⟺DT_PS`+`vg7x_VE34_of_DT`+`vg7x_RPERS`(`descending_Br_Pred`)+`vg7x_condIIIV_of_DT`。r36 CEX 排除〕[r1]
        - ✅ BASE/STEP形+全dispatcher還元→bridgesU(vg8x/vs3x)〔r38: BASE(`vg8x_BASE_of_bridgesR`/`vg8x_VE34_of_DT_modBridgesR`)+STEP(`vs3x_step_transM_form`=m_8_2_keystone clause3 で STEP-host Trans form/`vs3x_VE34_of_DT_modBridges`)。**BASE と STEP が同一残差 bridgesU に集約**、dispatcher 全体(RPERS 込)が bridgesU のみに依存〕[r5]
        - ✅ terminal-slice setup(bux_terminal_slice_ready、keystone4前提)〔r39: 全 vg7x_reg4 host で終切片 M'=seg N j0'(Lng N-1) が DT_PS/RT_PS/PT_PS∧Br≠[]∧Lng-1>1(keystone の4幾何前提、無条件)。`vg8x_terminal_slice_DT`+`TrMax_seg_ancestor`+`baseU_Br_empty_TrMax`〕[r1]
        - 🚨 bridgesU 終切片readback(readoff⟺VE34判明→残=article {BASE,STEP} back-peel)〔bridgesU=原文§8.2 終切片 term-readback。128/128 deep。r39発見の keystone RightNodes値残差を r40 で DISSOLVED し dispatcher を「readoff」残差 `kyx_VE34_of_DT_modReadoff` に還元していた〕
          - ✅ readoff⟺{BASE,STEP}還元(rdx_, modReadoff interface閉)〔r43発見: **readoff は vg2x_VE34 と論理的に等価**(既証 `vg6x_base_bridges_iff_VE34` 経由)→ keystone+leadform だけでは閉じない(t1/tau 同定に VE4=vg2x_VE34 本体が要り循環)。非循環還元: `rdx_bridgesU_readoff` は readoff を {BASE,STEP}(=原文 j1-TrMax 上の Pred 帰納=`vg7x_VE34_of_DT` obligation)+fin artifact から証明、`rdx_VE34_of_DT` が kyx_VE34_of_DT_modReadoff の readoff 仮定を discharge。両方 green。exhaustive L=6 で readoff 真 90/90(front(1)/terminal(3)/split 各90/90)〕[r3][0.259][0.93h]
          - 🚨 {BASE,STEP} back-peel(article Pred-induction on j1-TrMax)〔r30-r43抵抗の壁。r45でSTEP側が単一方程式に崩落〕
            - ✅ STEP slot閉 modulo TSPIN(bpx_、VE3+front-pin+fin Pred不変 全緑)〔r45 Fable: `bpx_VE34_step_modTSPIN`=vg7x_VE34_of_DT の STEP slot を {fin(host), TSPIN} だけに還元。緑15補題: VE3成長=r40 keystone `kyx_terminal_slice_keystone` 経由 transport(append=addBT-assoc、last-subtree-replacement=新 strict-prefix 補題 `bpx_growth_transport`)/front切片 Pred不変(`bpx_finset_Pred_eq`=LastStep Min-set が文字通り等しい: 枝頭 entry 全 index Pred-stable `bpx_Br_head_entries_Pred`+範囲外 `bpx_nth_overflow`)/t1 pin=IH VE4 の snoc-split(`bpx_step_form_pinned`)/fin Pred不変(`bpx_fin_Pred`)→capstone `bpx_VE34_of_DT_modBASE_TSPIN`(VE34 modulo {BASEf,TSPIN}+fin M、consumer vgx_condIIIV_of_VE は fin M を既に carry するので interface 拡大なし)。⚠️vg7x の fin-free slot 原形は多分 discharge 不能(LastStep Min-set の有限性が fin なしで出ない)→bpx_ dispatcher は per-host fin を thread〕[r1][0.279][0.28h]
            - 🚨🤖 TSPIN(終切片transport、非許容jointでのMark-surgery naturality)〔単一方程式: Trans N=Dpt(N10)(F +B Dpt(N1j0') a) ⟹ a=bpHeadT(Trans(seg N j0'(Lng N-1)))。経験的に真(=brMp readback、_r36/_r39/_r43 deep 0-fail と同値)。障害: m_8_2_keystone は clause(3)/(4)成分を opaque EX1 t123 でしか出さず、m_7_4_Mark_Trans_repr+Trans_Mark_Pred は m=j0' で Marked が adm N m を要求するのに regime が非許容を強制(0<j0'<TrMax)、m=Adm N j0' では一段下で再発。**非許容 joint での Trans 再帰の Mark-surgery naturality(content.md 3360)が本体**。r46 単独 target 推奨〕[r0]
            - 🚨🤖 BASEf(TSPIN kernel+same-head branch-run帰納)〔BASE(cfbx_j1p N=Lng N-1)は TSPIN kernel に加え、descending_def が弱降下ゆえ same-head branch run(LastStep<J1 が r38 corpus 8/8 で実在)の上の第2帰納(原文の run 帰納、未機械化)が要る〕[r0]
    - ✅ 補題（強単項性の切片への遺伝性）〔`m_8_2_strongmono_slice`〕
    - ✅ 補題（部分表現の単項成分と $\textrm{Pred}$ の関係）(§8.2 keystone)〔`m_8_2_keystone` = 無条件 `p_8_2_subexpr_component_Pred`〕
    - ✅ 補題（強単項性の下での部分表現の単項成分の基本性質）〔`m_8_2_subexpr_component_strongmono_uncond`〕
    - ✅ 補題（条件 (V) の下での右端の親の基本性質）〔`m_8_2_condV_rightmost_parent`〕
    - ✅ 補題（条件 (V) の下での終切片と $\textrm{Trans}$ の関係）〔`m_8_2_condV_terminal_slice_Trans` 無条件=p_8_2 verbatim、`vcx_VE_all`(backpeel×a0x_base_VE×VEj1eq×RPj1eq)〕[r15]
  - 🚨 §8.3 条件 (II) の下での展開規則
    - 🚨 命題（条件 (II) の下での $\textrm{Trans}$ と基本列の交換関係）
      - ✅ 降下⟸exch+OT〔`m_8_3_TransCondII_oper_descend_engine`〕
      - ✅ OT柱回避の直接降下〔`d2x_exchange2_condII`、kind0残差modulo〕[r1]
      - 🚨 exch
        - ✅ 存在量化count+step還元〔`c2ex_exchange2_condII_ex`(A36)+`c2lx_lhs_ex_of_step`〕[r2]
        - ✅ base2+per-step surgery(閉形式)〔`c2sx_condII_masterCF`(scx二重帰納、opaque W)。exchII配線`c2sx_exchII_leg_of_tailval`(両dispatcher共有)〕[r2]
        - 🚨 tailval残差
          - ✅ not-leftDj0脚(guard)modulo DIAG〔`cdx_d_le_joints`+`cdx_tailval_notldj`〕[r1]
          - 🚨 p_8_2_condIIIV(=§8.2命題、VE3/VE4残)〔同一物。scaffold+LastStep+VE2(ROW10込)✅、残=guarded VE3/VE4(BASE/STEP/RPERS)+fin〕[r2]
          - ✅ REGSP strictlt-eqd(slx37無条件)〔r37 **クローズ**: `slx37_strictlt_eqd`(d=jlp ガード付 strictlt を strictlt仮定無しで証明: wid_*_Pred transport で RN'=Pred RN 最終枝 first-node/joint を RN に戻し、descending+trunk row-0 厳増+d≤last-joint(`mcx_d_le_last_joint`)で d=jl強制、`mcx_MCOND_RN`で対角化、butlast で RN'座標へ)→`slx37_regSP_uncond`=REGSP(cfbx_reg) 無条件。condIII/IV REGSP 完全discharge。consumer 再配線(dgx/lb2x call site→slx37)は親の統合手順〕[r5]
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
      - 🚨🤖 残交換前提discharge(condII/III/IV)〔exchII=condII tailval / exchIII=condIII regime残差 / exchIV=condIV HB。exchVI=✅済〕
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
      - 🚨 deep-insertion OT所属(keystone{resid,multiD}、resid真)〔r35: 4脚→単一 keystone {resid,multiD}(`orx_OTint`)。r40b(Fable): **resid を deep検証(真、1468/0、最大Lng43、pcompPrefix と違い偽陽性でない)+4slot分解**。keystone `m_8_7_Trans_OT_step_keystone` の resid slot が強IH+Trans(Pred M)∈OT_B を受領する形に再構築(`rgx_Trans_preserves_OT_of_slots`)。反証registry: operB(term z)/最右spine scb-substitution/pcompPrefix 偽〕[r5]
        - ✅ resid deep検証+4slot分解(rgx_、C3 prefix半分クローズ)〔`rgx_resid_of_parts`(MASTER: resid C1∧C2∧C3 ⟸ {newOT,tailEH,appg,headWB}+Pred-OT、m_8_2_keystone 再走+snoc realign)。C3 prefix半分は `rgx_between_extends`([Buc1]辞書順区間)+`rgx_gbt_prefix_restrict`(b1x_GBT_size)で無条件クローズ、C3⟸appg(`rgx_gbt_of_appg`)。C2 whole-body Admpos 閉、`rgx_dstep_*` dispatcher〕[r1]
        - 🚨 slotNewOT(C1: isOT_BP(DB x q))〔r44発見: 挿入主項 D_x q = **from-joint 終切片 Trans**(seg M j0'(Lng M-1)、j0'=Joints M!(Lng(Br M)-1))。a6-scb transport は DEAD(deposit は Trans(Pred M) の scb-subterm でない 3/34)→唯一の筋は Lng-IH a5 を deposit-slice(短い標準列)に適用〕
          - ✅ shorter-slice IH還元(snx_)〔`snx_newOT_of_sliceTrans`=「N∈ST_PS, Lng N<Lng M, Trans N=Dpt(enat x)q ⟹ isOT_BP(DB(enat x)q)」を a5+isOT_BT→isOT_BP 展開で。`snx_slotNewOT_modSlice`=正確8仮定 modulo packaged deposit-slice存在。両 green〕[r1][0.193][0.32h]
          - 🚨🤖 deposit-host存在(P(N)_J1[n] witness、devel EX-N半と共有、from-joint同定は反証)〔r45 spine 反証: deposit=Trans(seg M j0'(Lng M-1)) は誤り(33/33、slice Trans は D_{M10} 全体)。正 witness=原文の枝成分 a2=Trans(P(N)_J1[n])。devel(slotTail) の EX-N 半と同一物→1 witness で slotNewOT modSlice と slotTail modDevel の両方が発火。旧⛔ {BASE,STEP} 依存は解消(witness 経路が変わった)〕[r0]
        - 🚨 slotAppg(C3: G_B-bound)〔r44: appg 真 984/984(deep Lng≥20:21/21)。`rgx_appg_split`で {qlt,Gq} 分割、v0>x(空G_B集合)/q=0B(自明)は無条件 discharge〕
          - ✅ guarded還元(sax_modcore、v0>x/q=0 discharge)〔`sax_slotAppg_modcore`=正確結論を rgx_appg_split 経由、genuine 内容を q≠0B∧entry M 1 0≤x の2残差 sax_qcore/sax_Gcore に隔離。green〕[r1][0.193][0.32h]
          - 🚨 head-gap x≥head(q)(局所導出不可・WGAP系REFUTED)〔qcore=lessBT q(Trm ps+_B Dpt x q) は deposited head が body head を支配 x≥head(q) に還元(diag 185/185)。これは「Trans M∈OT」自体の断片で、**局所仮定(predOT/newOT/descP/IH)から導出不可**を明示 OT CEX(q=Trm[DB 5 0],x=0,ps=[] は局所全成立だが lessBT q(Dpt 0 q) 偽)で証明。plan.md REFUTED の unconditional strictlt/WGAP/ANC0 head-gap 系と一致→大域 OT 不変量が要る〕[r0]
        - 🚨 slotTail(C2: leBT q qb、真)〔r44 偽チェック=TRUE(0-fail)。r45: 比較相手は M 内部の前枝 deposit qb であって Pred 残余 qp ではない(r44 が混同)〕
          - ✅ proper-prefix半還元(stx_→qp-descent、後にroute死)〔`stx_slotTail_properprefix_from_descent` は緑のまま残るが descent 仮定 leBT q qp が r45 で反証され DEAD route〕[r1][0.193][0.32h]
          - ✅ qp-descent反証(33/33逆向き)+slot束→devel単一残差化(spx_modDevel)〔r45 Fable: **leBT q qp は ST_PS で偽 33/33**(yaBMS標準確認済CEX: M=(0,0)(1,1)(2,1)(1,1)(2,1) q=D_1(0),qp=0_B 等3件)。真の向きは逆=Pred は trailing deposit を縮める。**併せて r44 C1 from-joint 同定も反証**: Trans(seg M j0'(Lng M-1)) は D_{M10} 全体であって deposit でない(33/33 mismatch)、正 witness=原文 P(N)_J1[n] 枝成分。緑: `spx_slotTail_eqhead_of_deposit_hosts`(same-head strip core)+`spx_slotTail_modDevel`=slotTail slot 束(proper-prefix+whole-body 両枝=rgx dispatcher の tailEH slot)を単一 packaged 残差 devel に還元。devel=∃N N'∈ST_PS 短Lng: Trans N=Dpt x q ∧ Trans N'=Dpt hdv qb ∧ (N=N' ∨ lessBT(Trans N)(Trans N'))。EX-N 半は snx C1 slice 残差と一致(1 witness pair が両 slot に効く)〕[r1][0.279][0.28h]
          - 🚨🤖 devel残差(deposit-host同定P(N)_J1[n]+development構造+短Lng降下)〔discharge=(i)deposit-host 同定(原文 P(N)_J1 枝成分、raw from-joint route は反証済) (ii)ST_PS 枝反復/development 構造(最終枝=前枝の development) (iii)短Lng での lessBT 降下(m_8_7_fseq_descend_dispatcher interface、強IH a5 下で使用可)〕[r0]
        - 🚨 slotHeadWB(C2: transJm1=0角、WB⟹equal-head)〔非空虚(小corpus 17/17 で transJm1=0, x=hdv=0)。Pred側 RightNodes 値読出し or 「WB⟹x=hdv(等頭)」補題が最短kill候補。Admpos を WB で仮定しないこと〕[r0]
        - 🚨 multiD(pcompPrefix反証→別ルート要)〔`otkx_multiD_of_pcomp_prefix` は pcompPrefix(ST_PS で反証済)依存で dead 条件補題。multiT junction 降下の別ルート要〕[r0]
