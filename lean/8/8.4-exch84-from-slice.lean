import «8».«8.4-exch84-mnform-bottom»
import «8».«8.7-otint-transport-prims»
import «7».«7.2-scb-unique»
import «8».«8.3-condII-masterCF»
import «5».«5.3-pred-is-oper1»

/-!
# §8.4 `MnformBottomExtResidual` の底タプル導出（`m_8_4_various_scb_IIIIV_from_slice`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係、
  補題（条件(III)か(IV)の下での各種 scb 分解）content.md 4802 の L6）。
- 対象: ビルド済み «8».«8.4-exch84-mnform-bottom» が露出した tight named 残差
  `MnformBottomExtResidual`（= Isabelle `m_8_4_various_scb_IIIIV_from_slice`
  @ `n = 1` の 5 連言 `hflat`/`c1`/`c7`/`L₁`/`M[1]`、isabelle/layerB/pss_wip.thy:60034）を
  4 つのスライス分解（`dP`/`d2`/`d4c2`/`d4a`、`Exch84_scbDecompPkg` の共有 witness
  `u1 u2 v1 v2`）から導出する。

## 導出の内訳（Isabelle `m_8_4_various_scb_IIIIV_from_slice` 対応）

| 連言 | 本ファイルの導出 |
|---|---|
| `hflat` | 挿入段 `ins = d4vx_ins (u1++u2) (e₁ⱼ₁-1) (v2++v1)`（«8».«8.7-otint-transport-prims»）の
  flat 則を**無条件**（全 `X`）に討伐。`d4vx_ins_flat`（`T_B` 版）は `X∈T_B` を要するので使わず、
  `d2`+`d4c2` から `Trans N` の principal body `bodyN`（`flatBT bodyN = (u1++u2)++flatBP(D_{e₁ⱼ₁}0)++(v2++v1)`）を作り、
  忠実な `T_B`-free 外科手術 `surg_image_fs`（Isabelle `scbimg_image_BT` の像存在、
  «7».«7.2-scb-outer-surgery-split» の private `surg_image_sos` を本ファイルへ再移植）で
  `D_{e₁ⱼ₁}0 → D_{e₁ⱼ₁-1} X` 置換の像を取り、`unflatBT_flat` で読み戻す |
| `M[1]` | `pred_is_oper1`（`oper M 1 = Pred M`、§5.3）＋ `Trans_c1_c2_decomp`（`dc1`、§8.3）＋
  `scb_compose`（`c1`+`d2` → `Trans M` の合成）＋ `scb_unique_decomp_unconditional`
  （`s₁ = u0 ++ D_{e₃}::u1`, `b₁ = v1 ++ v0` の pin）から**無条件** |

残る 3 連言（`c1` = `Trans M` の第 1 種分解／`c7` = `Trans (Lp)` の分解／`L₁` 平坦式）は
Isabelle `s84d_dec1_Trans_N_scb`（dec1 エンジン）・`m_8_4_rightend_Trans`＋`d4b`（右端置換、`d4b`
は本残差の入力に無い）・`s84d_c2hole_L1`/`s84d_L1_data`（塔基底の c2hole エンジン）を消費する
未移植部なので、共有 witness `u0 v0` を束ねる tight named Prop `SliceExtTupleResidual` として残す。

- 依存（すべてビルド済み）: «8».«8.4-exch84-mnform-bottom»（`MnformBottomExtResidual` def・
  `s84x_N`/`s84x_Np`/`s84x_L`/`s84x_Lp`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transC2`・`Trans`/`oper`/
  `Pred`/`entry`/`Lng`・`scb_decomp`/`scb_kind1`・`flatBT`/`flatBP`/`Dprin`/`BZero`・`STPS`/`RTPS`/
  `Trans_Mark_invariant`/`RTPS_Pred`/`STPS_RTPS`/`RTPS_TPS`）、«8».«8.7-otint-transport-prims»
  （`d4vx_ins`・`unflatBT_flat`）、«7».«7.2-scb-unique»（`flatComponentRun`・`flatBT_multi_snoc`・
  `flatBP_length_ge_two`・`scb_cut_reaches_last`・`scb_last_dichotomy`・`scb_compose`・
  `scb_unique_decomp_unconditional`・`flatBP_cancel`）、«8».«8.3-condII-masterCF»
  （`Trans_c1_c2_decomp`）、«5».«5.3-pred-is-oper1»（`pred_is_oper1`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `hflat`（外科手術・全 `X`）と `M[1]` 平坦式を**無条件**に討伐。残差 = `SliceExtTupleResidual`
  （本ファイル露出、`needs` 参照）＝ dec1/c7-rightend/L₁-c2hole の未移植エンジン束。
- Private helper suffix: `_fs`。
-/

namespace PSS

/-! ## 1. `T_B`-free 外科手術の像存在（Isabelle `scbimg_image_BT` の再移植、完全証明）

«7».«7.2-scb-outer-surgery-split» の private `surg_image_sos`（+ 補助 `preOf_sos`/`postOf_sos`/
`flat_snoc_sos`/`scb_to_last_sos`/`surg_sos`）を、公開補題（`flatComponentRun`/`flatBT_multi_snoc`/
`flatBP_length_ge_two`/`scb_cut_reaches_last`/`scb_last_dichotomy`/`flatBP_cancel`）の上で
`_fs` 接尾辞で再移植する。置換 principal `pr'` に dfree 制約が無い（`d4vx_ins_flat` の `T_B` 版と違い
全 `X` で使える）ことが `hflat` の全称化に必須。 -/

/-- `Wpre`: 末尾 principal より前の包み。 -/
private def preOf_fs : List BP → List Sym
  | [] => []
  | p :: rest => .lp :: flatComponentRun (p :: rest)

/-- 末尾 principal より後ろの包み。 -/
private def postOf_fs : List BP → List Sym
  | [] => []
  | _ :: _ => [.rp]

private theorem postOf_allRP_fs (qs : List BP) :
    ∀ x ∈ postOf_fs qs, x = .rp := by
  cases qs with
  | nil => intro x hx; simp [postOf_fs] at hx
  | cons p rest =>
      intro x hx
      simp [postOf_fs] at hx
      exact hx

/-- `flatBT_multi_last` の Lean 版。 -/
private theorem flat_snoc_fs (qs : List BP) (lastp : BP) :
    flatBT (.trm (qs ++ [lastp])) =
      preOf_fs qs ++ flatBP lastp ++ postOf_fs qs := by
  cases qs with
  | nil => simp [preOf_fs, postOf_fs, flatBT]
  | cons p rest =>
      rw [flatBT_multi_snoc p rest lastp]
      simp [preOf_fs, postOf_fs, List.append_assoc]

/-- 右括弧尾部を持つ principal occurrence は末尾 top-level 成分の内部に閉じ込め
られ、前置部・尾部の整列も返す（`scb_to_last_component`）。 -/
private theorem scb_to_last_fs {qs : List BP} {lastp pr : BP} {s b : List Sym}
    (h : flatBT (.trm (qs ++ [lastp])) = s ++ flatBP pr ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ sc bc, flatBP lastp = sc ++ flatBP pr ++ bc ∧ (∀ x ∈ bc, x = .rp) ∧
      s = preOf_fs qs ++ sc ∧ b = bc ++ postOf_fs qs := by
  cases qs with
  | nil =>
      refine ⟨s, b, ?_, hb, by simp [preOf_fs], by simp [postOf_fs]⟩
      simpa [flatBT] using h
  | cons p rest =>
      have hcut := scb_cut_reaches_last p rest lastp pr s b h hb
      have hshape := flat_snoc_fs (p :: rest) lastp
      have h' : preOf_fs (p :: rest) ++ flatBP lastp ++ postOf_fs (p :: rest)
          = s ++ flatBP pr ++ b := hshape.symm.trans h
      have hprelen : (preOf_fs (p :: rest)).length ≤ s.length := by
        simp only [preOf_fs, List.length_cons]
        omega
      have h'' : preOf_fs (p :: rest) ++ (flatBP lastp ++ postOf_fs (p :: rest))
          = s ++ (flatBP pr ++ b) := by
        simpa [List.append_assoc] using h'
      rcases scb_last_dichotomy h' hb (postOf_allRP_fs (p :: rest)) hprelen with
        ⟨hlen, hpq, hbpost⟩ | ⟨u, a, s₂, b₂, hq, ha, hb₂, hslen⟩
      · have hs : preOf_fs (p :: rest) = s := List.append_inj_left h'' hlen.symm
        exact ⟨[], [], by simp [hpq], by simp, by simp [hs], by simp [hbpost]⟩
      · subst hq
        refine ⟨.dsym u :: s₂, b₂, ?_, hb₂, ?_, ?_⟩
        · simp [flatBP, ha]
        · have hrew : preOf_fs (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_fs (p :: rest))
              = (preOf_fs (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_fs (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_fs (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          exact (List.append_inj h'' hlen2).1.symm
        · have hrew : preOf_fs (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_fs (p :: rest))
              = (preOf_fs (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_fs (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_fs (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          have := (List.append_inj h'' hlen2).2
          exact (List.append_cancel_left this).symm

private theorem bpListWeight_nil_fs : bpListWeight [] = 0 := by
  simp [bpListWeight]

private theorem bpListWeight_cons_fs (q : BP) (xs : List BP) :
    bpListWeight (q :: xs) = bpWeight q + bpListWeight xs + 1 := by
  simp [bpListWeight]

private theorem bpWeight_lt_snoc_fs (qs : List BP) (p : BP) :
    bpWeight p < bpListWeight (qs ++ [p]) := by
  induction qs with
  | nil =>
      rw [List.nil_append, bpListWeight_cons_fs, bpListWeight_nil_fs]
      omega
  | cons q rest ih =>
      rw [List.cons_append, bpListWeight_cons_fs]
      omega

/-- 右括弧尾部を持つ complete principal occurrence の置換は `flatBT` の像に留まる
（`scbimg_image_BT`）。置換 principal `pr'` に dfree 制約は不要。 -/
private theorem surg_fs : ∀ (n : ℕ) (t : BT), btWeight t ≤ n →
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
        obtain ⟨sc, bc, hlast, hbc, hs, hb'⟩ := scb_to_last_fs h hb
        rcases lastp with ⟨u, a⟩
        cases hsc : sc with
        | nil =>
            rw [hsc, List.nil_append] at hlast
            have hcancel : flatBP (BP.db u a) ++ [] = flatBP pr ++ bc := by
              simpa using hlast
            obtain ⟨_, hbc0⟩ := flatBP_cancel hcancel
            refine ⟨.trm (qs ++ [pr']), ?_⟩
            rw [flat_snoc_fs qs pr']
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
              have hb1 := bpWeight_lt_snoc_fs qs (BP.db u a)
              simp only [btWeight] at ht
              simp only [bpWeight] at hb1
              omega
            obtain ⟨a', ha'⟩ := ih a hwt pr pr' sc' bc hchild hbc
            refine ⟨.trm (qs ++ [BP.db u a']), ?_⟩
            rw [flat_snoc_fs qs (BP.db u a')]
            rw [hs, hb', hsc]
            simp only [flatBP, ha']
            simp [List.append_assoc]

private theorem surg_image_fs {t : BT} {pr pr' : BP} {s b : List Sym}
    (h : flatBT t = s ++ flatBP pr ++ b) (hb : ∀ x ∈ b, x = .rp) :
    ∃ t', flatBT t' = s ++ flatBP pr' ++ b :=
  surg_fs (btWeight t) t le_rfl pr pr' s b h hb

/-- `flatBT t = D_u :: rest` なら `t` は単一 principal `D_u a`。 -/
private theorem flatBT_head_dsym_fs {t : BT} {u : ℕ∞} {rest : List Sym}
    (h : flatBT t = .dsym u :: rest) : ∃ a, t = .trm [.db u a] := by
  rcases t with ⟨ps⟩
  match ps with
  | [] => simp [flatBT] at h
  | [BP.db u' a] =>
      refine ⟨a, ?_⟩
      have : Sym.dsym u' = Sym.dsym u := by
        simpa [flatBT, flatBP] using congrArg List.head? h
      simp_all
  | p :: q :: ps => simp [flatBT] at h

/-! ## 2. 未移植エンジン束の残差（named Prop） -/

/-- 残差: `c1`（`Trans M` の第 1 種分解、Isabelle `s84d_dec1_Trans_N_scb`）＋
`c7`（`Trans (Lp)` の分解、Isabelle `m_8_4_rightend_Trans`＋`d4b`）＋ `L₁` 平坦式
（塔基底、Isabelle `s84d_c2hole_L1`/`s84d_L1_data`）を、共有 witness `u0 v0` で束ねる。
これらは Red 正則性エンジン・右端置換・c2hole 塔基底を消費するため Lean 未移植。 -/
def SliceExtTupleResidual : Prop :=
  ∀ (M : PS) (u1 u2 v1 v2 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans (Pred (s84x_N M)))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 →
    scb_decomp (transC2 M) u2
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 →
    scb_decomp (Trans (Pred (s84x_Np M)))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    ∃ u0 v0 : List Sym,
      -- `c1`: `Trans M` の kind1 分解（穴 `Trans N`）
      scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 ∧
      -- `c7`: `Trans (Lp)` の分解（穴 `D_{e₂}0`）
      scb_decomp (Trans (s84x_Lp M))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
        (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1) ∧
      -- `L₁` 平坦式（塔深さ 1）
      flatBT (Trans (s84x_L M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ (v2 ++ v1) ++ v0

/-! ## 3. 導出本体（house pattern、`hflat`/`M[1]` 無条件討伐） -/

/-- **`MnformBottomExtResidual` の drop-in**（house pattern）。`SliceExtTupleResidual`
から `u0 v0`・`c1`・`c7`・`L₁` を取り、`hflat`（外科手術・全 `X`）と `M[1]` 平坦式を
無条件に足して底タプルを組む。 -/
theorem mnformBottomExtResidual_holds (hTuple : SliceExtTupleResidual) :
    MnformBottomExtResidual := by
  intro M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  obtain ⟨u0, v0, hc1, hc7, hL1⟩ :=
    hTuple M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  -- 準備: `v2 ++ v1` は全 RP
  have hb_rp : ∀ x ∈ (v2 ++ v1), x = Sym.rp := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact d4c2.2.2 x h
    · exact d2.2.2 x h
  -- `flatBT (transC2 M) = u2 ++ flatBP (D_{e₁ⱼ₁}0) ++ v2`
  have hc2flat : flatBT (transC2 M)
      = u2 ++ flatBP (BP.db ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero) ++ v2 := by
    have h := d4c2.1
    simpa [Dprin, flatBT] using h
  -- `Trans N` は単一 principal `D_{e₃} bodyN`
  have hTNhead : flatBT (Trans (s84x_N M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (u1 ++ flatBT (transC2 M) ++ v1) := by
    have h := d2.1
    simpa [List.cons_append] using h
  obtain ⟨bodyN, hTNeq⟩ := flatBT_head_dsym_fs hTNhead
  have hbody0 : flatBT bodyN = u1 ++ flatBT (transC2 M) ++ v1 := by
    have hfe : flatBT (BT.trm [BP.db ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) bodyN])
        = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: flatBT bodyN := by
      simp [flatBT, flatBP]
    rw [hTNeq] at hTNhead
    rw [hfe] at hTNhead
    exact (List.cons.inj hTNhead).2
  have hbodyflat : flatBT bodyN
      = (u1 ++ u2) ++ flatBP (BP.db ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)
          ++ (v2 ++ v1) := by
    rw [hbody0, hc2flat]
    simp [List.append_assoc]
  refine ⟨d4vx_ins (u1 ++ u2) (entry M 1 (Lng M - 1) - 1) (v2 ++ v1), u0, v0,
    ?_, hc1, hc7, hL1, ?_⟩
  · -- `hflat`: 外科手術で全 `X` を無条件討伐
    intro X
    obtain ⟨tX, htX⟩ := surg_image_fs (t := bodyN)
      (pr := BP.db ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)
      (pr' := BP.db ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) X)
      hbodyflat hb_rp
    have hins : d4vx_ins (u1 ++ u2) (entry M 1 (Lng M - 1) - 1) (v2 ++ v1) X = tX := by
      unfold d4vx_ins
      have harg : (u1 ++ u2)
          ++ flatBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) X) ++ (v2 ++ v1)
          = flatBT tX := by
        rw [htX]; simp [Dprin, flatBT, flatBP]
      rw [harg, unflatBT_flat]
    rw [hins, htX]
    simp [flatBP, List.append_assoc]
  · -- `M[1]` 平坦式
    have hMR : RTPS M := STPS_RTPS M hST
    have hMT : TPS M := RTPS_TPS M hMR
    have hlen : 1 < Lng M := by omega
    have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
    have nzP : zeroT (Pred M) = false := by simp [zeroT, hLP]; omega
    have hT1 : Trans (Pred M) ≠ BZero :=
      (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
    obtain ⟨s1, b1, dc1, dc2M⟩ := Trans_c1_c2_decomp M hMR hmono hlen hT1
    have hc0N : ∃ p, Trans (s84x_N M) = BT.trm [p] := ⟨_, hTNeq⟩
    have comp1 := scb_compose (Trans M) (Trans (s84x_N M)) u0
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1)
      (flatBT (transC2 M)) v1 v0 hc0N hc1.1 d2
    have pin := scb_unique_decomp_unconditional (Trans M) s1
      (u0 ++ (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1))
      (flatBT (transC2 M)) b1 (v1 ++ v0) dc2M comp1
    obtain ⟨hs1, hb1⟩ := pin
    have hPredflat : flatBT (Trans (Pred M))
        = (u0 ++ (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1))
            ++ flatBT (transC1 M) ++ (v1 ++ v0) := by
      have h := dc1.1
      rw [hs1, hb1] at h
      exact h
    have hoper : oper M 1 = Pred M := (pred_is_oper1 M hMT hlen).symm
    rw [hoper, hPredflat]
    simp [List.cons_append, List.append_assoc]

#print axioms mnformBottomExtResidual_holds

end PSS
