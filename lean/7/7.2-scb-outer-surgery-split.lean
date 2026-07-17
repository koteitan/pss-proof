import PSS.Flat
import «7».«7.2-scb-unique»

/-!
# §7.2 外側 principal の scb 外科手術の分解

- Isabelle: `scb_outer_surgery_split` (`isabelle/layerB/pss_wip.thy`:26412–26573)
  - 補助（いずれも本ファイルへ private 移植、接尾辞 `_sos`）:
    - `scb_to_last_component` (pss_wip.thy:1429) → `scb_to_last_sos`
      （Lean 版は「最終成分への閉じ込め」だけでなく **s/b の整列** も同時に返すので、
      Isabelle が別途使う一意性 `m_7_2_scb_unique_sb` の呼び出しが不要になる）
    - `scbimg_image_BT` / `scbimg_image_BP` (pss_wip.thy:913、153 行) → `surg_sos`
      （Lean は `btWeight` の強帰納で `scbimg_join` 等の補助を全廃、大幅短縮）
    - `flatBT_multi_last` (pss_wip.thy:22796) → 既存の `flatBT_multi_snoc`
      （`«7».«7.2-scb-unique»`）で代替、`Wpre` は `preOf_sos` に対応
    - `flatinj_flatBP_cancel` → 既存の `flatBP_cancel`（`PSS.Flat`）
    - `BT_split_last_principal` (pss_wip.thy:26360) → `List.dropLast_append_getLast`
      による直接分解（`SigmaB`/`PB` を経由しない）
- 依存: `PSS.Flat`（`flatBP_cancel` / `flatBT_injective` / `flatBP_injective`）、
  `«7».«7.2-scb-unique»`（`flatComponentRun` / `flatBT_multi_snoc` /
  `flatBP_length_ge_two` / `scb_cut_reaches_last` / `scb_last_dichotomy`）。
  `PS` / `Trans` / `Mark` には一切依存しない純粋な `BT`/`Sym` 組合せ論。
- 状態: sorry 0、公開定理 `scb_outer_surgery_split` の axioms は
  `[propext, Classical.choice, Quot.sound]`。
  文は `lean/8/8.2-subexpr-admpos-engine.lean` の名前付き仮定 `ScbOuterSurgerySplit`
  と逐語一致（drop-in 用）。
-/

namespace PSS

/-! ## 末尾 principal への分解（`flatBT_multi_last` / `Wpre` に対応） -/

/-- `Wpre`: 末尾 principal より前の包み。`qs = []` なら包みはない。 -/
private def preOf_sos : List BP → List Sym
  | [] => []
  | p :: rest => .lp :: flatComponentRun (p :: rest)

/-- 末尾 principal より後ろの包み。 -/
private def postOf_sos : List BP → List Sym
  | [] => []
  | _ :: _ => [.rp]

private theorem postOf_allRP_sos (qs : List BP) :
    ∀ x ∈ postOf_sos qs, x = .rp := by
  cases qs with
  | nil => intro x hx; simp [postOf_sos] at hx
  | cons p rest =>
      intro x hx
      simp [postOf_sos] at hx
      exact hx

/-- `flatBT_multi_last` の Lean 版。`qs = []` の退化も同じ形で書ける。 -/
private theorem flat_snoc_sos (qs : List BP) (lastp : BP) :
    flatBT (.trm (qs ++ [lastp])) =
      preOf_sos qs ++ flatBP lastp ++ postOf_sos qs := by
  cases qs with
  | nil => simp [preOf_sos, postOf_sos, flatBT]
  | cons p rest =>
      rw [flatBT_multi_snoc p rest lastp]
      simp [preOf_sos, postOf_sos, List.append_assoc]

/-! ## 最終成分への閉じ込め（`scb_to_last_component`） -/

/-- 右括弧尾部を持つ principal occurrence は末尾 top-level 成分の内部に閉じ込め
られる。さらに Lean 版は前置部・尾部の整列 `s = Wpre ++ sc`, `b = bc ++ POST`
も返す（Isabelle はここで別途 scb 分解の一意性を使う）。 -/
private theorem scb_to_last_sos {qs : List BP} {lastp pr : BP} {s b : List Sym}
    (h : flatBT (.trm (qs ++ [lastp])) = s ++ flatBP pr ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    ∃ sc bc, flatBP lastp = sc ++ flatBP pr ++ bc ∧ (∀ x ∈ bc, x = .rp) ∧
      s = preOf_sos qs ++ sc ∧ b = bc ++ postOf_sos qs := by
  cases qs with
  | nil =>
      refine ⟨s, b, ?_, hb, by simp [preOf_sos], by simp [postOf_sos]⟩
      simpa [flatBT] using h
  | cons p rest =>
      have hcut := scb_cut_reaches_last p rest lastp pr s b h hb
      have hshape := flat_snoc_sos (p :: rest) lastp
      have h' : preOf_sos (p :: rest) ++ flatBP lastp ++ postOf_sos (p :: rest)
          = s ++ flatBP pr ++ b := hshape.symm.trans h
      have hprelen : (preOf_sos (p :: rest)).length ≤ s.length := by
        simp only [preOf_sos, List.length_cons]
        omega
      have h'' : preOf_sos (p :: rest) ++ (flatBP lastp ++ postOf_sos (p :: rest))
          = s ++ (flatBP pr ++ b) := by
        simpa [List.append_assoc] using h'
      rcases scb_last_dichotomy h' hb (postOf_allRP_sos (p :: rest)) hprelen with
        ⟨hlen, hpq, hbpost⟩ | ⟨u, a, s₂, b₂, hq, ha, hb₂, hslen⟩
      · have hs : preOf_sos (p :: rest) = s := List.append_inj_left h'' hlen.symm
        exact ⟨[], [], by simp [hpq], by simp, by simp [hs], by simp [hbpost]⟩
      · subst hq
        refine ⟨.dsym u :: s₂, b₂, ?_, hb₂, ?_, ?_⟩
        · simp [flatBP, ha]
        · have hrew : preOf_sos (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_sos (p :: rest))
              = (preOf_sos (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_sos (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_sos (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          exact (List.append_inj h'' hlen2).1.symm
        · have hrew : preOf_sos (p :: rest) ++ (flatBP (BP.db u a)
              ++ postOf_sos (p :: rest))
              = (preOf_sos (p :: rest) ++ (.dsym u :: s₂))
                ++ (flatBP pr ++ (b₂ ++ postOf_sos (p :: rest))) := by
            simp [flatBP, ha, List.append_assoc]
          rw [hrew] at h''
          have hlen2 : (preOf_sos (p :: rest) ++ (Sym.dsym u :: s₂)).length
              = s.length := by
            simp only [List.length_append, List.length_cons]
            omega
          have := (List.append_inj h'' hlen2).2
          exact (List.append_cancel_left this).symm

/-! ## 像の存在（`scbimg_image_BT` / `scbimg_image_BP`） -/

private theorem bpListWeight_nil_sos : bpListWeight [] = 0 := by
  simp [bpListWeight]

private theorem bpListWeight_cons_sos (q : BP) (xs : List BP) :
    bpListWeight (q :: xs) = bpWeight q + bpListWeight xs + 1 := by
  simp [bpListWeight]

private theorem bpWeight_lt_snoc_sos (qs : List BP) (p : BP) :
    bpWeight p < bpListWeight (qs ++ [p]) := by
  induction qs with
  | nil =>
      rw [List.nil_append, bpListWeight_cons_sos, bpListWeight_nil_sos]
      omega
  | cons q rest ih =>
      rw [List.cons_append, bpListWeight_cons_sos]
      omega

/-- 右括弧尾部を持つ complete principal occurrence の置換は `flatBT` の像に留まる
（`scbimg_image_BT`）。`btWeight` の強帰納で、末尾成分への閉じ込めを繰り返す。 -/
private theorem surg_sos : ∀ (n : ℕ) (t : BT), btWeight t ≤ n →
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
        obtain ⟨sc, bc, hlast, hbc, hs, hb'⟩ := scb_to_last_sos h hb
        rcases lastp with ⟨u, a⟩
        cases hsc : sc with
        | nil =>
            rw [hsc, List.nil_append] at hlast
            have hcancel : flatBP (BP.db u a) ++ [] = flatBP pr ++ bc := by
              simpa using hlast
            obtain ⟨_, hbc0⟩ := flatBP_cancel hcancel
            refine ⟨.trm (qs ++ [pr']), ?_⟩
            rw [flat_snoc_sos qs pr']
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
              have hb1 := bpWeight_lt_snoc_sos qs (BP.db u a)
              simp only [btWeight] at ht
              simp only [bpWeight] at hb1
              omega
            obtain ⟨a', ha'⟩ := ih a hwt pr pr' sc' bc hchild hbc
            refine ⟨.trm (qs ++ [BP.db u a']), ?_⟩
            rw [flat_snoc_sos qs (BP.db u a')]
            rw [hs, hb', hsc]
            simp only [flatBP, ha']
            simp [List.append_assoc]

private theorem surg_image_sos {t : BT} {pr pr' : BP} {s b : List Sym}
    (h : flatBT t = s ++ flatBP pr ++ b) (hb : ∀ x ∈ b, x = .rp) :
    ∃ t', flatBT t' = s ++ flatBP pr' ++ b :=
  surg_sos (btWeight t) t le_rfl pr pr' s b h hb

/-! ## 先頭記号からの読み戻し -/

private theorem flatBT_Dprin_sos (u : ℕ∞) (a : BT) :
    flatBT (Dprin u a) = .dsym u :: flatBT a := by
  simp [Dprin, flatBT, flatBP]

private theorem flatBT_head_dsym_sos {t : BT} {u : ℕ∞} {rest : List Sym}
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

/-! ## 主定理 -/

/-- STEP 1 ENGINE（Isabelle `scb_outer_surgery_split`）。
外側 principal `X = D_{e10} BP`（`BP ≠ 0`）の scb 手術部位 `D_v t₂` が真に内側
（`X ≠ D_v t₂`）で、置換 `D_v body₂`（dfree principal）の結果が `Y` であるとき、
手術は `BP` の**最終 top 成分**に閉じ込められる。したがって共通の接頭辞 `pre` と
共通の末尾成分頭 `w` が存在して `BP = pre +_B D_w u₂`、`Y = D_{e10}(pre +_B D_w u₃)`。 -/
theorem scb_outer_surgery_split :
    ∀ (e10 v : ℕ∞) (BP body2 t2 Y : BT) (s1 b1 : List Sym),
      BP ≠ BZero →
      scb_decomp (Dprin e10 BP) s1 (flatBT (Dprin v t2)) b1 →
      dfree_BP (.db v body2) = true →
      Dprin e10 BP ≠ Dprin v t2 →
      flatBT Y = s1 ++ flatBT (Dprin v body2) ++ b1 →
      ∃ pre w u2 u3,
        BP = addBT pre (Dprin w u2) ∧ Y = Dprin e10 (addBT pre (Dprin w u3)) := by
  intro e10 v X body2 t2 Y s1 b1 hXne hd _hdfv hne hY
  -- 手術部位・尾部の基本形
  have hXflat : flatBT (Dprin e10 X) = s1 ++ flatBP (.db v t2) ++ b1 := by
    simpa [Dprin, flatBT] using hd.1
  have hb1 : ∀ x ∈ b1, x = .rp := hd.2.2
  have hYflat : flatBT Y = s1 ++ flatBP (.db v body2) ++ b1 := by
    simpa [Dprin, flatBT] using hY
  have hhead : flatBT (Dprin e10 X) = .dsym e10 :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  -- s₁ ≠ [] （さもなくば X = D_v t₂）
  obtain ⟨s1', rfl⟩ : ∃ s1', s1 = .dsym e10 :: s1' := by
    cases hs : s1 with
    | nil =>
        exfalso
        rw [hs] at hXflat
        have hcancel : flatBP (.db e10 X) ++ [] = flatBP (.db v t2) ++ b1 := by
          simpa [Dprin, flatBT] using hXflat
        obtain ⟨hfl, _⟩ := flatBP_cancel hcancel
        exact hne (by simp [Dprin, flatBP_injective hfl])
    | cons x xs =>
        refine ⟨xs, ?_⟩
        have hx : Sym.dsym e10 = x := by
          rw [hs] at hXflat
          simpa [hhead] using congrArg List.head? (hhead.symm.trans hXflat)
        exact congrArg (fun y => y :: xs) hx.symm
  have hXdec : flatBT X = s1' ++ flatBP (.db v t2) ++ b1 := by
    have := hhead.symm.trans hXflat
    simpa using this
  -- X の最終 top 成分への分解
  obtain ⟨ps, rfl⟩ : ∃ ps, X = .trm ps := ⟨untrm X, by rcases X with ⟨ps⟩; rfl⟩
  have hps : ps ≠ [] := by
    intro h
    exact hXne (by simp [h, BZero])
  obtain ⟨qs, lastp, rfl⟩ : ∃ qs lastp, ps = qs ++ [lastp] :=
    ⟨ps.dropLast, ps.getLast hps, (List.dropLast_append_getLast hps).symm⟩
  obtain ⟨sc, bc, hlast, hbc, hs, hb'⟩ := scb_to_last_sos hXdec hb1
  rcases lastp with ⟨w, u2⟩
  -- 像の存在: 最終成分の内部で D_v t₂ を D_v body₂ に置換
  obtain ⟨t', ht'⟩ :=
    surg_image_sos (t := .trm [BP.db w u2]) (pr := .db v t2) (pr' := .db v body2)
      (by simpa [flatBT] using hlast) hbc
  -- 像の先頭記号は w
  have ht'head : ∃ rest, flatBT t' = .dsym w :: rest := by
    cases hsc : sc with
    | nil =>
        rw [hsc, List.nil_append] at hlast
        have hcancel : flatBP (BP.db w u2) ++ [] = flatBP (.db v t2) ++ bc := by
          simpa using hlast
        obtain ⟨hfl, _⟩ := flatBP_cancel hcancel
        have hwv : w = v := by
          have := flatBP_injective hfl
          injection this with h1 _
        refine ⟨flatBT body2, ?_⟩
        rw [ht', hsc, hwv]
        obtain ⟨_, hbc0⟩ := flatBP_cancel hcancel
        rw [← hbc0]
        simp [flatBP]
    | cons x sc' =>
        have hx : x = .dsym w := by
          have h0 := congrArg List.head? hlast
          rw [hsc] at h0
          simp [flatBP] at h0
          exact h0.symm
        refine ⟨sc' ++ flatBP (.db v body2) ++ bc, ?_⟩
        rw [ht', hsc, hx]
        simp
  obtain ⟨rest, hrest⟩ := ht'head
  obtain ⟨u3, rfl⟩ := flatBT_head_dsym_sos hrest
  have hlc : flatBP (BP.db w u3) = sc ++ flatBP (.db v body2) ++ bc := by
    simpa [flatBT] using ht'
  -- 像の本体 BM' = pre +_B D_w u₃
  refine ⟨.trm qs, w, u2, u3, ?_, ?_⟩
  · simp [addBT, Dprin]
  · have hBM : flatBT (.trm (qs ++ [BP.db w u3]))
        = s1' ++ flatBP (.db v body2) ++ b1 := by
      rw [flat_snoc_sos qs (BP.db w u3), hlc, hs, hb']
      simp [List.append_assoc]
    have hYeq : flatBT Y = flatBT (Dprin e10 (.trm (qs ++ [BP.db w u3]))) := by
      rw [flatBT_Dprin_sos, hBM, hYflat]
      simp [List.append_assoc]
    have := flatBT_injective hYeq
    rw [this]
    simp [addBT, Dprin]

#print axioms scb_outer_surgery_split

end PSS
