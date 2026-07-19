import «8».«8.2-condIIIV-pin-tspin»
import «8».«8.2-condIIIV-frontpred»

/-!
# §8.2 条件(II)/(IV) VE34 — **run-step D-体制の pinned assembly**（Isabelle `bgx_VE34_base_step`）

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係、part(1)
  「brN」の pinned 形＝PIN と非許容 joint での Mark-surgery naturality＝TSPIN）。本ファイルは
  `8.2-condIIIV-pin-tspin` が単一残差として露出した **run-step 脚**を、Isabelle
  `bgx_VE34_base_step`（isabelle/layerB/pss_wip.thy 106565、`isleft` selector 経路）の逐語移植で
  討伐する。run-base 脚（`transPinRunBaseD_pt`、pin-tspin）の isleft 非発火（NOTLEFT/clause-2）経路
  と対をなす、isleft 発火（clause-4）経路である。

- 🚨 **`TransPinRunStepD_pt`（pin-tspin の pointwise Prop、IH 非保持）は無条件では証明不能**:
  Isabelle `bgx_VE34_base_step` は `isleft` selector の発火に **IH の VE4**（`vg2x_VE34 (Pred N)`）を
  本質的に消費する（`t2eq : transT2 N = F +_B D_{N₁,j₀'} uP` は `ihVE4` からのみ得られる。`transT2 N =
  bpHeadT (Trans (Pred N))`〔Adm0〕ゆえ、その pinned 形＝Pred N の VE4 そのもの）。pointwise では
  `isleft` を確立できず閉じない。数値検証では pinned 形は run-step D-体制 domain 上で**真**
  （`python/audit_runstep_pin.py`、証人 `witRS`＋手構築 5 件で成立、反証なし）だが、その真理は
  IH 経由でしか機械証明できない。

- **正しい姿＝IH 保持版 `transPinRunStepIH_rp`**: 仮説に `ihP : VE34goal (Pred N)` を持つ pinned
  assembly。消費側 `baseRunStep_up_gm`（`8.2-condIIIV-geometry`、`BaseRunStep_up` スロット）は
  `ihP : VE34goal (Pred N)` を**既に scope に持つ**ので、これで足りる（memo Wave AS の TSPIN
  再定式化指示と同型: 「IH-carrying に再定式化——消費側は regDP/ihP を既に scope に持つ」）。
  無条件化の**配線指示（本ファイル射程外、親が geometry/pin-tspin で実施）**:
  `VE4BaseDeepD_of_runstep_pt hRS`／`baseRunStep_up_gm hRS` を、`hRS : TransPinRunStepD_pt`
  依存から本ファイルの `transPinRunStepIH_rp N regD hbase hdeep hrunstep ihP` 直呼びへ差し替え、
  capstone `ve34_on_reg4D_modulo_gm` の第 1 残差 `TransPinRunStepD_pt` を落とす。

- **移植の骨格**（Isabelle `bgx_VE34_base_step` 106565 の `TransN` 導出＝行 106615–106633）:
  1. IH VE4 clause（`ihP` の第 3 連言）を宿主 `N` の座標へ輸送:
     front 転送 `frontPredBaseTransportD_holds`、終切片転送 `TermPredBaseTransportD_pv`、
     joint 転送（`jeqBaseD_pv`＋`Joints_Pred_core`）＋`entry_Pred`。→
     `bpHeadT (Trans (Pred N)) = F +_B D_{N₁,j₀'} uP`（`F` = 前切片頭、`uP = bpHeadT (Trans (Pred Mp))`）。
  2. Adm0 setup（`adm0_setup_rp`、base-forms `adm0_setup_bf` の自己完結コピー）:
     `transT2 N = bpHeadT (Trans (Pred N))`＝`F +_B D_{N₁,j₀'} uP`。
  3. 末尾 principal 切出し（`PB_split_last_rp`）＋左因子共有単射で `isleft` 発火を確立。
  4. clause-4 sharp value form（`clause4_sharp_rp`、subexpr-adm0-cores `clause4_core` の
     transC2Core-unfold を sharp に取り出したもの）: `Trans N = D_{N₁,0}(F +_B D_{N₁,j₀'}(uP +_B
     D_{N₁,Lng-1} 0))`。
  5. 終切片閉形式 `BgxMpForm_of_slice_bf BgxMpSliceData_cs2`（census-slice、無条件）で内部項
     `uP +_B D_{N₁,Lng-1} 0 = bpHeadT (Trans Mp)` に畳んで pinned 形へ。

- 依存 module: `8.2-condIIIV-pin-tspin`（`TransPinRunStepD_pt` / `VE34goal` / `VE4goal` /
  `BgxMpForm_of_slice_bf` / `BgxMpSliceData_cs2`、および推移的に `VE34_base_*` / `notVI_Adm0` /
  `t2ne_notAVI` / adm0 の 7.x/6.x 公開補題群 / `TermPredBaseTransportD_pv` / `jeqBaseD_pv` /
  `BrLen_Pred_base_pv` / `Joints_Pred_core` / `entry_Pred`）, `8.2-condIIIV-frontpred`
  （`frontPredBaseTransportD_holds`）。

- 状態: ✅（sorry 0、rc=0）。IH 保持版 `transPinRunStepIH_rp` を無条件討伐。pointwise
  `TransPinRunStepD_pt` は上記の理由で本ファイルでは閉じず（配線残）。

- Private suffix: `_rp`。
-/

namespace PSS

open Classical

/-! ## 私的補助（suffix `_rp`） -/

/-- `bpHeadT (Dprin v a) = a`（`Dprin v a = .trm [.db v a]` の定義展開）。 -/
private theorem bpHeadT_Dprin_rp (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- `bpHeadV (Dprin v a) = v`（同上）。 -/
private theorem bpHeadV_Dprin_rp (v : ℕ∞) (a : BT) : bpHeadV (Dprin v a) = v := rfl

/-- `Dprin` の単射性（`Dprin_inj_sc` の再掲、private ゆえ）。 -/
private theorem Dprin_inj_rp {v w : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin w b) : v = w ∧ a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact h

/-- `t +_B D_v b = t' +_B D_{v'} b' ⟹ t = t' ∧ v = v' ∧ b = b'`（`addBT_snoc_Dprin_inj_sc` の
再掲、private ゆえ）。 -/
private theorem addBT_snoc_Dprin_inj_rp {t t' : BT} {v v' : ℕ∞} {b b' : BT}
    (h : addBT t (Dprin v b) = addBT t' (Dprin v' b')) :
    t = t' ∧ v = v' ∧ b = b' := by
  rcases t with ⟨as⟩
  rcases t' with ⟨bs⟩
  simp only [addBT, Dprin, BT.trm.injEq] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, BP.db.injEq, and_true] at h2
  exact ⟨congrArg BT.trm h1, h2.1, h2.2⟩

/-- `SigmaB (map (Trm[·]) l) = Trm l`（`SigmaB_map_singleton_sc` の再掲、private ゆえ）。 -/
private theorem SigmaB_map_singleton_rp (l : List BP) :
    SigmaB (l.map (fun p => BT.trm [p])) = BT.trm l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      have ihl : ((ps.map (fun p => BT.trm [p])).flatMap untrm) = ps := by
        simpa [SigmaB, BT.trm.injEq] using ih
      simp [SigmaB, untrm, ihl]

/-- 末尾 principal の切出し `t = SigmaB(prefix) +_B D_v u`（`PB_split_last_sc` の再掲、private ゆえ）。 -/
private theorem PB_split_last_rp (t : BT) (ht : t ≠ BZero) :
    ∃ (v : ℕ∞) (u : BT),
      (PB t).getD ((PB t).length - 1) BZero = Dprin v u ∧
      t = addBT (SigmaB ((PB t).take ((PB t).length - 1))) (Dprin v u) := by
  rcases t with ⟨ps⟩
  have hne : ps ≠ [] := by
    intro h
    exact ht (by simp [h, BZero])
  have hpos : 0 < ps.length := List.length_pos_of_ne_nil hne
  have hidx : ps.length - 1 < ps.length := by omega
  have hPB : PB (BT.trm ps) = ps.map (fun p => BT.trm [p]) := rfl
  have hlenPB : (PB (BT.trm ps)).length = ps.length := by simp [hPB]
  rcases hlast : ps[ps.length - 1] with ⟨v, u⟩
  refine ⟨v, u, ?_, ?_⟩
  · have h1 : (PB (BT.trm ps)).getD ((PB (BT.trm ps)).length - 1) BZero
        = (ps.map (fun p => BT.trm [p]))[ps.length - 1]'(by simpa using hidx) := by
      rw [hlenPB, hPB]
      exact getD_eq_getElem_idx _ BZero (by simpa using hidx)
    rw [h1]
    simp [List.getElem_map, hlast, Dprin]
  · have htake : (PB (BT.trm ps)).take ((PB (BT.trm ps)).length - 1)
        = (ps.take (ps.length - 1)).map (fun p => BT.trm [p]) := by
      rw [hlenPB, hPB, ← List.map_take]
    rw [htake, SigmaB_map_singleton_rp]
    show BT.trm ps = addBT (BT.trm (ps.take (ps.length - 1))) (BT.trm [BP.db v u])
    have hsplit : ps.take (ps.length - 1) ++ [ps[ps.length - 1]] = ps := by
      conv_rhs => rw [← List.take_append_drop (ps.length - 1) ps]
      congr 1
      rw [List.drop_eq_getElem_cons hidx]
      have hsucc : ps.length - 1 + 1 = ps.length := by omega
      rw [hsucc, List.drop_length]
    rw [hlast] at hsplit
    simp only [addBT, BT.trm.injEq]
    exact hsplit.symm

/-! ## Adm0 setup（Isabelle `Trans_eq_transC2_Adm0` 19356 ／ base-forms `adm0_setup_bf` の
自己完結コピー） -/

/-- **`adm0_setup_rp`**: `Adm0` 分岐で `Trans (Pred M) = D_{M₁,0} (transT2 M)`、
`Trans M = transC2 M`、`transV M = M₁,0`。 -/
private theorem adm0_setup_rp (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (transT2 M) ∧
    Trans M = transC2 M ∧
    transV M = (entry M 1 0 : ℕ∞) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hzPred : zeroT (Pred M) = false := by
    have hne : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, hne]
  have ht1 : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT (Pred M) hPredT).mpr h0
    rw [hzPred] at hz
    simp at hz
  have hleR00 : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hMk0 : Marked M 0 := ⟨hM, adm_zero M, hleR00⟩
  have hMzT : Mark M 0 = Trans M := Mark_zero_eq_Trans M hR hMk0
  have hMc2 : Mark M (transJm1 M) = transC2 M :=
    Mark_transJm1_eq_transC2 M hR hmono hlen ht1
  rw [hAdm0] at hMc2
  have hTc2 : Trans M = transC2 M := by rw [← hMzT, hMc2]
  have hMkP0 : Marked (Pred M) 0 := Marked_Pred M 0 hM hlen hMk0 (by omega)
  have hc1 : transC1 M = Trans (Pred M) := by
    show Mark (Pred M) (transJm1 M) = Trans (Pred M)
    rw [hAdm0]
    exact Mark_zero_eq_Trans (Pred M) hpredR hMkP0
  have hmonoP : monoT (Pred M) = true := by
    simp [monoT, hzPred, hMkP0.2.2]
  obtain ⟨t, ht⟩ : ∃ t, Trans (Pred M)
      = Dprin (entry (Pred M) 1 0 : ℕ∞) t := by
    rcases Trans_mono_leftend_form (Pred M) hpredR hmonoP with h0 | h
    · exact absurd h0 ht1
    · exact h
  have hEPred : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hlen
  have hV : transV M = (entry M 1 0 : ℕ∞) := by
    show bpHeadV (transC1 M) = (entry M 1 0 : ℕ∞)
    rw [hc1, ht, hEPred]
    simp [bpHeadV, Dprin]
  have hJ1pos : 0 < transJ1 M := by
    show 0 < Lng M - 1
    omega
  have hT1ne : transT1 M ≠ BZero := ht1
  have pc1 : (PB (transC1 M)).length = 1 :=
    transC1_single_principal M hR hmono hJ1pos hT1ne
  have hc1D : transC1 M = Dprin (transV M) (transT2 M) :=
    principal_reconstruct pc1
  have hTPeq : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (transT2 M) := by
    rw [← hc1, hc1D, hV]
  exact ⟨hTPeq, hTc2, hV⟩

/-! ## clause-4（`isleft` 発火）の sharp value form（Isabelle `bgx_base_form_left`／
subexpr-adm0-cores `clause4_core` の transC2Core-unfold） -/

/-- **`clause4_sharp_rp`**（¬(I∨III∨V)∧¬VI∧t₂≠0∧`isleft` 発火 ホスト）: clause-4 sharp form
`Trans M = D_{M₁,0}(Σ(prefix) +_B D_{M₁,j₀}(bpHeadT(末尾 PB) +_B D_{M₁,Lng-1} 0))`。
`j₀ = transJ0 M = lastParent M`。 -/
private theorem clause4_sharp_rp (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hnA : (transCondI M || transCondIII M || transCondV M) = false)
    (hnVI : transCondVI M = false) (ht₂ : transT2 M ≠ BZero)
    (hisleft :
      bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        = (entry M 1 (transJ0 M) : ℕ∞)) :
    Trans M = Dprin (entry M 1 0 : ℕ∞)
      (addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
        (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero))
            (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
  obtain ⟨_hTP, hTc2, hV⟩ := adm0_setup_rp M hR hmono hj1gt hAdm0
  have hnA' : ¬((transCondI M || transCondIII M || transCondV M) = true) := by simp [hnA]
  have hnVI' : ¬(transCondVI M = true) := by simp [hnVI]
  have ht₂' : ¬((transT2 M == BZero) = true) := by simpa using ht₂
  have hleftB : ((bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        == (entry M 1 (lastParent M) : ℕ∞)) = true) := by simpa [transJ0] using hisleft
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT (bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero))
                (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_neg hnA', if_neg hnVI', if_neg ht₂', if_pos hleftB, if_pos hleftB, hV]
    rfl
  rw [hTc2, hc2]

/-! ## run-step pinned assembly（IH 保持版、Isabelle `bgx_VE34_base_step` 106565 の `TransN`） -/

/-- **`transPinRunStepIH_rp`**（Isabelle `bgx_VE34_base_step` 106565 の VE4 側 pinned 形）:
D-体制 run-step 深 BASE ホストでの `Trans N` の pinned assembly。**IH `VE34goal (Pred N)` を消費**
（isleft selector が IH で発火する clause-4 form の内部項固定）。消費側 `baseRunStep_up_gm`
（geometry、`BaseRunStep_up` スロット）は `ihP` を scope に持つので、無条件 pointwise
`TransPinRunStepD_pt`（証明不能）を経由せず本補題を直呼びして残差を落とせる。 -/
theorem transPinRunStepIH_rp (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (hrunstep : LastStep N < (Br N).length - 1)
    (ihP : VE34goal (Pred N)) :
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
          (bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))) := by
  have reg4 : VE34Reg4 N := regD.1
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩, hdesc⟩ := regD
  have hM : TPS N := RTPS_TPS N hR
  have hL1 : 1 < Lng N := by omega
  have hj1gt : 1 < Lng N - 1 := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hj0ltL : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  -- 体制データ
  have hAdm0 : transJm1 N = 0 := VE34_base_Adm0 N reg4 hbase
  have hnAor : ¬ (transCondI N = true ∨ transCondIII N = true ∨ transCondV N = true) :=
    VE34_base_notCondA N reg4 hbase
  have hnA : (transCondI N || transCondIII N || transCondV N) = false := by
    cases hc1 : transCondI N <;> cases hc2 : transCondIII N <;> cases hc3 : transCondV N <;>
      simp_all
  have hnVI : transCondVI N = false := notVI_Adm0 N hR hmono hBrne hj1gt hAdm0
  have ht2ne : transT2 N ≠ BZero := t2ne_notAVI N hR hmono hL1 hj1gt hnAor hnVI
  have htj0 : transJ0 N = (Joints N).getD ((Br N).length - 1) 0 := VE34_base_transJ0 N reg4 hbase
  -- Adm0 setup: transT2 N = bpHeadT (Trans (Pred N))
  obtain ⟨hTP, _hTc2, _hV⟩ := adm0_setup_rp N hR hmono hj1gt hAdm0
  have ht2eqP : transT2 N = bpHeadT (Trans (Pred N)) := by rw [hTP, bpHeadT_Dprin_rp]
  -- IH VE4 clause の宿主座標への輸送（front / term / joint / entry）
  have hfront := frontPredBaseTransportD_holds N ⟨reg4, hdesc⟩ hbase hdeep hrunstep
  have hterm := TermPredBaseTransportD_pv N ⟨reg4, hdesc⟩ hbase hdeep hrunstep
  have hBrlen : (Br (Pred N)).length = (Br N).length - 1 :=
    BrLen_Pred_base_pv N hM hBrne hL1 htrne hbase
  have hBrlen1 : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
  have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by rw [hBrlen]; omega
  have hje : (Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0
      = (Joints N).getD ((Br N).length - 1) 0 := by
    rw [hBrlen1, Joints_Pred_core N hM hmono hL1 htrne ((Br N).length - 2) hJpP]
    exact jeqBaseD_pv N ⟨reg4, hdesc⟩ hbase hdeep hrunstep
  have hentP : entry (Pred N) 1 ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0)
      = entry N 1 ((Joints N).getD ((Br N).length - 1) 0) := by
    rw [hje]; exact entry_Pred N 1 ((Joints N).getD ((Br N).length - 1) 0) hj0ltL
  obtain ⟨_t2P, _hAP, _hBPne, hVE4P⟩ := ihP
  rw [hfront, hterm, hentP] at hVE4P
  -- transT2 N = F +_B D_{N₁,j₀'} uP
  have ht2eq : transT2 N
      = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
          (Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
            (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))) := by
    rw [ht2eqP, hVE4P]
  -- 末尾 principal 切出し ＋ 左因子共有単射
  obtain ⟨v, u, hlast, hsplit⟩ := PB_split_last_rp (transT2 N) ht2ne
  obtain ⟨hSig, hv, hu⟩ := addBT_snoc_Dprin_inj_rp (hsplit.symm.trans ht2eq)
  -- isleft の発火（IH 経由）
  have hisleft : bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
      = (entry N 1 (transJ0 N) : ℕ∞) := by
    rw [hlast, bpHeadV_Dprin_rp, hv, htj0]
  -- clause-4 sharp form
  have hTM := clause4_sharp_rp N hR hmono hj1gt hAdm0 hnA hnVI ht2ne hisleft
  rw [hSig, htj0] at hTM
  have hbTlast : bpHeadT ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
      = bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))) := by
    rw [hlast, bpHeadT_Dprin_rp, hu]
  rw [hbTlast] at hTM
  -- 終切片閉形式で内部項を bpHeadT (Trans Mp) に畳む
  have hMp := (BgxMpForm_of_slice_bf BgxMpSliceData_cs2) N ⟨reg4, hdesc⟩ hbase hdeep
  have hMpHead :
      addBT (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))
          (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)
        = bpHeadT (Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) := by
    rw [hMp, bpHeadT_Dprin_rp]
  rw [hMpHead] at hTM
  exact hTM

/-! ## run-step 残差を IH 保持版から放出（配線例、pin-tspin `VE4BaseDeepD_of_runstep_pt` の
IH 保持置換） -/

/-- **`VE4goal_runstep_of_IH_rp`**: run-step 深 BASE ホストで `VE4goal N` を IH 保持 pinned 形の
外側頭読み出しで得る（消費側が `ihP` を scope に持つ場合の LIVE 経路）。pin-tspin の pointwise
`VE4BaseDeepD_of_runstep_pt`（`TransPinRunStepD_pt` modulo）の IH 保持・無条件版。 -/
theorem VE4goal_runstep_of_IH_rp (N : PS) (regD : VE34Reg4D N)
    (hbase : VEj1p N = Lng N - 1) (hdeep : TrMax N + 2 < Lng N)
    (hrunstep : LastStep N < (Br N).length - 1)
    (ihP : VE34goal (Pred N)) : VE4goal N := by
  rw [VE4goal, transPinRunStepIH_rp N regD hbase hdeep hrunstep ihP, bpHeadT_Dprin_rp]

/-! ## 転記の数値検証（run-step D-体制証人で pinned 形が実 `Trans` に一致） -/

-- D-体制 run-step 証人（pin-tspin `witRS_pt` と同一）。in-domain。
#guard decide (VE34Reg4D [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
  ∧ VEj1p [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] - 1
  ∧ TrMax [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] + 2 < Lng [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
  ∧ LastStep [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] < (Br [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).length - 1)
  = true

-- pinned 形が実 `Trans` に一致（`transPinRunStepIH_rp` の結論 shape）。
#guard (Trans [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] == Dprin (entry [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] 1 0 : ℕ∞)
    (addBT (bpHeadT (Trans (seg [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] 0
        ((FirstNodes [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).getD (LastStep [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]) 0 - 1))))
      (Dprin (entry [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] 1
          ((Joints [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).getD ((Br [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).length - 1) 0) : ℕ∞)
        (bpHeadT (Trans (seg [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]
            ((Joints [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).getD ((Br [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)]).length - 1) 0)
            (Lng [(0,0),(1,1),(2,2),(2,0),(3,1),(2,0)] - 1))))))) = true

#print axioms transPinRunStepIH_rp
#print axioms VE4goal_runstep_of_IH_rp

end PSS
