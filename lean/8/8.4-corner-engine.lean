import «8».«8.4-mnform-corner-dispatch»
import «8».«8.6-condVI-props»
import «8».«8.5-exchV-props»
import «8».«8.7-otint-transport-prims»
import «5».«5.3-pred-is-oper1»

/-!
# §8.4 交換パッケージ condIV admeq 隅の CORNER SURGERY ENGINE
（`MnformCornerResidual_md` の discharge）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-mnform-corner-dispatch»:141 が宣言した named 残差
  `MnformCornerResidual_md`（隅 mnform データ、transC2/transC1 語彙）。dispatch の corner
  枝 `mnformResidualCorner_holds_md` がこれを collapse 恒等式で `MnformResidual M` へ戻す。

- Isabelle（設計図）: condIV admeq 隅 `c4dx_condIV_k1`（layerB/pss_wip.thy:84541、`k1`）
  ＋ `oi5_bodyOT`（layerC/pss_scratch.thy:1520-1554、`isOT_BT (bpHeadT …)`）。隅では切片が
  潰れるので、`trans_surgery_localized`（wip:23638）＝ Lean 済 `trans_surgery_localized_v6p`
  （«8».«8.6-condVI-props»:214）が共有 scb 対 `(s₁,b₁)` を出し、`c1_shape`（`transV`/`transC1`
  形）＋ `transC2` の principal 頭（`transC2Core` は全枝 `D_v(·)`）で `k1`（分解半分）と
  `M[1]` 平坦式を無条件に組む。

## 本ファイルの成果（house green-modulo）

`trans_surgery_localized_v6p`（共有対 `(s₁,b₁)`、無条件）＋ `c1_shape_holds`
（«8».«8.5-exchV-props»、`transV M = M_{1,j₋₁}` / `transC1 M = D_{M₁,ⱼ₋₁}(transT2)`）を核に:

* **無条件討伐**（隅 mnform データ 10 連言のうち 5 本）: 挿入段 `ins`/`hflat`（外科手術像・全 `X`、
  Isabelle `d4vx_ins`。inner の wrap から `surg_image_ce`）／`b₀` 全 `RP`（inner の右尾）／
  `b₁` 全 `RP`（共有対の右尾）／`ubeq`（`entry M 1 (s84x_jm2 M) = entry M 1 (Lng M-1) - 1`、
  RedCondA ランプ）／`M[1]` 平坦式（`Trans (M[1]) = Trans (Pred M)` を `c₁` で切る、`pred_is_oper1`）。
  さらに `k1` の scb 分解半分（共有対 `hd2`）と穴書き換え（隅の要 `s84x_jm3 M = transJm1 M`＝admeq
  で `flatBT (transC2 M) = flatBT (D_{e₃}(bpHeadT transC2))`）を無条件に供給。
* **named 残差 `MnformCornerCoreResidual_ce` へ縮約**（真に §8.4 condIV c2-body ＋ §7.4 Mark を
  要する 5 葉）: inner（`bpHeadT (transC2 M)` の穴 `D_{v₁}0`、`c4dx_condIV_c2body_shape`/`dbbody`
  wip:84387/84477）＋ `k1` の第 1 種述語（同 c2-body、`c4dx_condIV_k1` wip:84541）＋ 底スライス
  平坦式 `L₁`/`Lp`/`Pred Np`（§7.4 Mark = `Oper5Residual` 葉、`s84c1_Mark_L_mstar`/
  `s84c1_Mark_Mn_mstar`）。共有対 `(s₁,b₁)` を入力に取るので witness は完全に threaded。

- 依存（すべてビルド済み・main 79f75ff）: «8».«8.4-mnform-corner-dispatch»
  （`MnformCornerResidual_md` の Prop 本体・transC1/transC2/s84x_jm2/s84x_jm3/s84x_N/s84x_Np/
  s84x_L/s84x_Lp・`transC2Core`/`transV`/`transC1`/`transT2`/`transJm1`/`transJ1`/`transT1`・
  `Dprin`/`BZero`/`flatBT`/`flatBP`/`bpHeadT`/`scb_decomp`/`scb_kind1`・`STPS_RTPS`/`RTPS_TPS`/
  `RTPS_Pred`/`Trans_Mark_invariant`）、«8».«8.6-condVI-props»（`trans_surgery_localized_v6p`）、
  «8».«8.5-exchV-props»（`c1_shape_holds`）、«8».«8.7-otint-transport-prims»（`d4vx_ins`）、
  «5».«5.3-pred-is-oper1»（`pred_is_oper1`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 `MnformCornerCoreResidual_ce`（`needs`）1 本。
- Private helper suffix: `_ce`。
-/

namespace PSS

/-! ## 0. 補助（`transC2` の principal 頭 / `ubeq` / 隅 setup、既存 private の `_ce` 複製） -/

/-- `transC2Core` は全枝 `D_v(·)`。«8».«8.2-subexpr-admpos-engine» private `transC2_outer_ape`
／«8».«8.7-otpred-brickD» private `transC2_eq_Dprin_bD` の再掲。 -/
private theorem transC2_eq_Dprin_ce (M : PS) :
    ∃ body, transC2 M = Dprin (transV M) body := by
  unfold transC2 transC2Core
  split_ifs <;> exact ⟨_, rfl⟩

/-- `transC2 M` は先頭指標 `transV M` の principal。 -/
private theorem transC2_head_ce (M : PS) :
    transC2 M = Dprin (transV M) (bpHeadT (transC2 M)) := by
  obtain ⟨body, hb⟩ := transC2_eq_Dprin_ce M
  rw [hb]; simp [bpHeadT, Dprin]

/-- `transC2 M` は単一 principal（`trans_surgery_localized_v6p` の入力）。 -/
private theorem transC2_principal_ce (M : PS) : ∃ p, transC2 M = .trm [p] := by
  obtain ⟨body, hb⟩ := transC2_eq_Dprin_ce M
  exact ⟨.db (transV M) body, by rw [hb]; rfl⟩

/-- `ubeq`（Isabelle `cpx_condIII_mnform` の `ubeq`、RedCondA ランプ）の無条件討伐。
«8».«8.4-mnform-corner-dispatch» private `ubeq_md` と同じ。 -/
private theorem ubeq_ce (M : PS) (hST : STPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1 := by
  have condA : RedCondA M = true := (RTPS_condAB M (STPS_RTPS M hST)).1
  have hLM : Lng M - 1 < Lng M := by omega
  simp only [RedCondA, List.all_eq_true] at condA
  have hbody := condA 1 (by decide) (Lng M - 1) (List.mem_range.mpr hLM)
  rw [hp] at hbody
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hbody
  have ramp : entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) := hbody
  omega

/-- 隅 setup: `0 < transJ1 M`（`J1pos`）と `transT1 M ≠ 0_B`（`T1`）。«8».«8.4-corner-redesign»
の setup 段と同一構成。 -/
private theorem corner_setup_ce (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
    0 < transJ1 M ∧ transT1 M ≠ BZero := by
  have hlen : 1 < Lng M := by omega
  refine ⟨by simp only [transJ1, lastIdx]; omega, ?_⟩
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1' : Trans (Pred M) ≠ BZero :=
    (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
  simpa [transT1] using T1'

/-! ## 0b. 外科手術像（`d4vx_ins` の flat 則を全 `X` に、`dfree` 制約なし）
     «8».«8.4-exch84-from-slice» private `surg_image_fs` 系の `_ce` 複製。 -/

/-- `Wpre`: 末尾 principal より前の包み。 -/
private def preOf_ce : List BP → List Sym
  | [] => []
  | p :: rest => .lp :: flatComponentRun (p :: rest)

/-- 末尾 principal より後ろの包み。 -/
private def postOf_ce : List BP → List Sym
  | [] => []
  | _ :: _ => [.rp]

private theorem postOf_allRP_ce (qs : List BP) :
    ∀ x ∈ postOf_ce qs, x = .rp := by
  cases qs with
  | nil => intro x hx; simp [postOf_ce] at hx
  | cons p rest =>
      intro x hx
      simp [postOf_ce] at hx
      exact hx

/-- `flatBT_multi_last` の Lean 版。 -/
private theorem flat_snoc_ce (qs : List BP) (lastp : BP) :
    flatBT (.trm (qs ++ [lastp])) =
      preOf_ce qs ++ flatBP lastp ++ postOf_ce qs := by
  cases qs with
  | nil => simp [preOf_ce, postOf_ce, flatBT]
  | cons p rest =>
      rw [flatBT_multi_snoc p rest lastp]
      simp [preOf_ce, postOf_ce, List.append_assoc]

/-- 右括弧尾部を持つ principal occurrence は末尾 top-level 成分の内部に閉じ込め
られ、前置部・尾部の整列も返す（`scb_to_last_component`）。 -/
private theorem scb_to_last_ce {qs : List BP} {lastp pr : BP} {s b : List Sym}
    (h : flatBT (.trm (qs ++ [lastp])) = s ++ flatBP pr ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ sc bc, flatBP lastp = sc ++ flatBP pr ++ bc ∧ (∀ x ∈ bc, x = .rp) ∧
      s = preOf_ce qs ++ sc ∧ b = bc ++ postOf_ce qs := by
  cases qs with
  | nil =>
      refine ⟨s, b, ?_, hb, by simp [preOf_ce], by simp [postOf_ce]⟩
      simpa [flatBT] using h
  | cons p rest =>
      have hcut := scb_cut_reaches_last p rest lastp pr s b h hb
      have hshape := flat_snoc_ce (p :: rest) lastp
      have h' : preOf_ce (p :: rest) ++ flatBP lastp ++ postOf_ce (p :: rest)
          = s ++ flatBP pr ++ b := hshape.symm.trans h
      have hprelen : (preOf_ce (p :: rest)).length ≤ s.length := by
        simp only [preOf_ce, List.length_cons]
        omega
      have h'' : preOf_ce (p :: rest) ++ (flatBP lastp ++ postOf_ce (p :: rest))
          = s ++ (flatBP pr ++ b) := by
        simpa [List.append_assoc] using h'
      rcases scb_last_dichotomy h' hb (postOf_allRP_ce (p :: rest)) hprelen with
        ⟨hlen, hpq, hbpost⟩ | ⟨u, a, s₂, b₂, hq, ha, hb₂, hslen⟩
      · have hs : preOf_ce (p :: rest) = s := List.append_inj_left h'' hlen.symm
        exact ⟨[], [], by simp [hpq], by simp, by simp [hs], by simp [hbpost]⟩
      · subst hq
        refine ⟨.dsym u :: s₂, b₂, ?_, hb₂, ?_, ?_⟩
        · simp [flatBP, ha]
        · have hrew : preOf_ce (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_ce (p :: rest))
              = (preOf_ce (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_ce (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_ce (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          exact (List.append_inj h'' hlen2).1.symm
        · have hrew : preOf_ce (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_ce (p :: rest))
              = (preOf_ce (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_ce (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_ce (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          have := (List.append_inj h'' hlen2).2
          exact (List.append_cancel_left this).symm

private theorem bpListWeight_nil_ce : bpListWeight [] = 0 := by
  simp [bpListWeight]

private theorem bpListWeight_cons_ce (q : BP) (xs : List BP) :
    bpListWeight (q :: xs) = bpWeight q + bpListWeight xs + 1 := by
  simp [bpListWeight]

private theorem bpWeight_lt_snoc_ce (qs : List BP) (p : BP) :
    bpWeight p < bpListWeight (qs ++ [p]) := by
  induction qs with
  | nil =>
      rw [List.nil_append, bpListWeight_cons_ce, bpListWeight_nil_ce]
      omega
  | cons q rest ih =>
      rw [List.cons_append, bpListWeight_cons_ce]
      omega

/-- 右括弧尾部を持つ complete principal occurrence の置換は `flatBT` の像に留まる
（`scbimg_image_BT`）。置換 principal `pr'` に dfree 制約は不要。 -/
private theorem surg_ce : ∀ (n : ℕ) (t : BT), btWeight t ≤ n →
    ∀ (pr pr' : BP) (s b : List Sym),
      flatBT t = s ++ flatBP pr ++ b → (∀ x ∈ b, x = .rp) →
      ∃ t', flatBT t' = s ++ flatBP pr' ++ b := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      rcases t with ⟨ps⟩
      simp only [btWeight] at ht
      omega
  | succ n ih =>
      intro t ht pr pr' s b h hb
      rcases t with ⟨ps⟩
      by_cases hps : ps = []
      · exfalso
        subst hps
        have hlen := congrArg List.length h
        have h2 := flatBP_length_ge_two pr
        simp only [flatBT, List.length_cons, List.length_nil, List.length_append] at hlen
        omega
      · obtain ⟨qs, lastp, rfl⟩ : ∃ qs lastp, ps = qs ++ [lastp] :=
          ⟨ps.dropLast, ps.getLast hps, (List.dropLast_append_getLast hps).symm⟩
        obtain ⟨sc, bc, hlast, hbc, hs, hb'⟩ := scb_to_last_ce h hb
        rcases lastp with ⟨u, a⟩
        cases hsc : sc with
        | nil =>
            rw [hsc, List.nil_append] at hlast
            have hcancel : flatBP (BP.db u a) ++ [] = flatBP pr ++ bc := by
              simpa using hlast
            obtain ⟨_, hbc0⟩ := flatBP_cancel hcancel
            refine ⟨.trm (qs ++ [pr']), ?_⟩
            rw [flat_snoc_ce qs pr']
            rw [hs, hb', hsc, ← hbc0]
            simp
        | cons x sc' =>
            have hx : x = .dsym u := by
              have h0 := congrArg List.head? hlast
              rw [hsc] at h0
              simp [flatBP] at h0
              exact h0.symm
            subst hx
            have hchild : flatBT a = sc' ++ flatBP pr ++ bc := by
              rw [hsc] at hlast
              simpa [flatBP] using hlast
            have hwt : btWeight a ≤ n := by
              have hb1 := bpWeight_lt_snoc_ce qs (BP.db u a)
              simp only [btWeight] at ht
              simp only [bpWeight] at hb1
              omega
            obtain ⟨a', ha'⟩ := ih a hwt pr pr' sc' bc hchild hbc
            refine ⟨.trm (qs ++ [BP.db u a']), ?_⟩
            rw [flat_snoc_ce qs (BP.db u a')]
            rw [hs, hb', hsc]
            simp only [flatBP, ha']
            simp [List.append_assoc]

private theorem surg_image_ce {t : BT} {pr pr' : BP} {s b : List Sym}
    (h : flatBT t = s ++ flatBP pr ++ b) (hb : ∀ x ∈ b, x = .rp) :
    ∃ t', flatBT t' = s ++ flatBP pr' ++ b :=
  surg_ce (btWeight t) t le_rfl pr pr' s b h hb

/-! ## 1. 露出する named 残差（真に §8.4 condIV c2-body ＋ §7.4 Mark を要する葉） -/

/-- **隅 mnform の core 残差**。共有対 `(s₁,b₁)`（`trans_surgery_localized_v6p` の出力、
`Trans (M[1])` を `c₁`・`Trans M` を `c₂` で切る 1 対）を入力に取り、隅 mnform の
**genuinely-missing 部**だけを要求する（挿入段 `ins`/`hflat` は本ファイルが inner から
外科手術像で無条件に組むので残差に含まない）:

* inner（`bpHeadT (transC2 M)` の末尾 principal `D_{v₁}0` の scb 分解、Isabelle
  `c4dx_condIV_c2body_shape`/`c4dx_condIV_dbbody` wip:84387/84477）。`s0`/`b0` の witness。
* `k1`（`Trans M` の第 1 種分解、穴 `flatBT (transC2 M)`。Isabelle `c4dx_condIV_k1` wip:84541
  の第 1 種述語部）。
* 底スライスの平坦式 `L₁`/`Lp`/`Pred Np`（§7.4 Mark = `Oper5Residual` 葉、`s84c1_Mark_L_mstar`
  /`s84c1_Mark_Mn_mstar`）。

`e₃ = M_{1,j₋₃}`、`e₂ = M_{1,j₋₂}`、`v₁ = M_{1,Lng M-1}`、`ub = v₁ - 1`。 -/
def MnformCornerCoreResidual_ce : Prop :=
  ∀ (M : PS) (s1 b1 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    scb_decomp (Trans (oper M 1)) s1 (flatBT (transC1 M)) b1 →
    scb_decomp (Trans M) s1 (flatBT (transC2 M)) b1 →
    ∃ s0 b0 : List Sym,
      scb_decomp (bpHeadT (transC2 M)) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 ∧
      scb_kind1 (Trans M) s1 (flatBT (transC2 M)) b1 ∧
      flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ b0 ++ b1 ∧
      flatBT (Trans (s84x_Lp M))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ b0) ∧
      flatBT (Trans (Pred (s84x_Np M)))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: flatBT (bpHeadT (transC1 M))

/-! ## 2. `MnformCornerResidual_md` の discharge（共有対 + c1_shape + collapse 頭書き換え） -/

/-- **`MnformCornerResidual_md`（«8».«8.4-mnform-corner-dispatch»:141）の drop-in**。
`trans_surgery_localized_v6p` で共有対 `(s₁,b₁)` を出し、`ubeq`／`b₁` 全 `RP`／`M[1]` 平坦式／
`k1` の穴書き換え（`s84x_jm3 = transJm1` ＋ `transC2` principal 頭）を無条件に足して、
残差 `MnformCornerCoreResidual_ce` から隅 mnform データを組む。 -/
theorem mnformCornerResidual_holds_ce (hcore : MnformCornerCoreResidual_ce) :
    MnformCornerResidual_md := by
  intro M hST hmono hp hj1 hIV hadmeq
  -- setup
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlen : 1 < Lng M := by omega
  obtain ⟨J1pos, hT1⟩ := corner_setup_ce M hMR hj1
  -- `c1_shape`: `transV`/`transC1` 形
  obtain ⟨hV, hc1eq, _ht2TB, _hjm1lt⟩ := c1_shape_holds M hMR hMT hmono J1pos hT1
  -- 共有 scb 対 `(s₁,b₁)`（`Trans (Pred M)` を `c₁`・`Trans M` を `c₂` で切る 1 対）
  obtain ⟨s1, b1, hd1P, hd2⟩ :=
    trans_surgery_localized_v6p M hMR hmono J1pos hT1 (transC2_principal_ce M)
  have hoper : oper M 1 = Pred M := (pred_is_oper1 M hMT hlen).symm
  have hd1 : scb_decomp (Trans (oper M 1)) s1 (flatBT (transC1 M)) b1 := by
    rw [hoper]; exact hd1P
  -- 隅の要 `s84x_jm3 M = transJm1 M`（admeq、defeq）
  have hjm3 : s84x_jm3 M = transJm1 M := hadmeq
  -- 残差から core を得る
  obtain ⟨s0, b0, hinner, hk1, hL1, hLp, hPN⟩ :=
    hcore M s1 b1 hST hmono hp hj1 hIV hadmeq hd1 hd2
  have hb0rp : ∀ x ∈ b0, x = Sym.rp := hinner.2.2
  -- 挿入段 `ins = d4vx_ins s0 (v₁-1) b0`（Isabelle `d4vx_ins`）
  set ins := d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 with hins_def
  -- inner の wrap 形（`flatBP` 版）
  have hwrap : flatBT (bpHeadT (transC2 M))
      = s0 ++ flatBP (BP.db ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero) ++ b0 := by
    have h := hinner.1; simpa [Dprin, flatBT] using h
  -- `k1` の穴書き換え: `flatBT (transC2 M) = flatBT (D_{e₃}(bpHeadT transC2))`
  have hhole : Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) (bpHeadT (transC2 M)) = transC2 M := by
    have h1 : ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) = transV M := by rw [hjm3, hV]
    rw [h1]; exact (transC2_head_ce M).symm
  -- 組み立て
  refine ⟨ins, s0, b0, s1, b1, ?_, hb0rp, hd2.2.2, hinner, ?_,
    ubeq_ce M hST hp hj1, ?_, hL1, hLp, hPN⟩
  · -- `hflat`（A）: 外科手術で全 `X` を無条件討伐
    intro X
    obtain ⟨tX, htX⟩ := surg_image_ce (t := bpHeadT (transC2 M))
      (pr := BP.db ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)
      (pr' := BP.db ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) X)
      hwrap hb0rp
    have hinsX : ins X = tX := by
      rw [hins_def]; unfold d4vx_ins
      have harg : s0 ++ flatBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) X) ++ b0
          = flatBT tX := by rw [htX]; simp [Dprin, flatBT, flatBP]
      rw [harg, unflatBT_flat]
    rw [hinsX, htX]; simp [flatBP, List.append_assoc]
  · -- `k1`（E）
    rw [hhole]; exact hk1
  · -- `M[1]`（G）
    have hbpT1 : bpHeadT (transC1 M) = transT2 M := by rw [hc1eq]; simp [Dprin, bpHeadT]
    have hfc1 : flatBT (transC1 M)
        = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: flatBT (bpHeadT (transC1 M)) := by
      rw [hbpT1, hc1eq, hjm3]; simp [Dprin, flatBT, flatBP]
    rw [hd1.1, hfc1]

#print axioms mnformCornerResidual_holds_ce

end PSS
