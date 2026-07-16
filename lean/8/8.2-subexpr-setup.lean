import «6».«6.4-mono-slice-next»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-reduced-leftend»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-RightNodes-Mark»

/-!
# §8.2 部分表現の単項成分と `Pred` — setup ＋ Adm-zero clause (1)

- 原文: `tmp/content.md` 3360–3453 付近（§8.2 の 4 節場合分けの前の無条件
  準備事実と、`Adm`-zero 枝の clause (1) の値核）。
- 訂正: なし（A9 は `LastStep` の添字 `J₁ = Lng(Br M) - 1` の範囲補正で、
  本補題は既に訂正後の添字を使っており影響しない）。
- Isabelle: `m_8_2_subexpr_component_Pred_setup`
  （`isabelle/layerB/pss_wip.thy:19256`）,
  `m_8_2_subexpr_component_Pred_Adm0_clause1`（同 :19436）。
- 公開定理: `subexpr_component_Pred_setup`, `subexpr_component_Pred_Adm0_clause1`。
- 依存: `FirstNodes_TrMax_Joints`/`FirstNodes_getD`/`Joints_getD`/`TrMax_bound`
  （6.4）, `mono_slice_next`（6.4）, `nextR_parent0_of_hasParent`（6.4）,
  `RTPS_Pred`/`length_Pred`/`entry_Pred_zero`（6.5）, `RTPS_TPS`（6.6）,
  `Marked_Pred`（7.3）, `Trans_preserves_zeroT`（7.3）,
  `Mark_zero_eq_Trans`/`Mark_transJm1_eq_transC2`（7.4）,
  `Trans_mono_leftend_form`（7.4）。
- 方針: Isabelle の `Trans_eq_transC2_Adm0` は Lean では
  `Trans M = Mark M 0 = Mark M (transJm1 M) = transC2 M`（7.4 公開補題の連鎖、
  `transJm1 M = 0` を代入）で置き換える（8.1-part4-trans の TransN engine と
  同じ勝ち筋）。`c₁` の単主要項形は `Trans_mono_leftend_form` を `Pred M` に
  適用して直接読み取る（`transC1_single_principal`＋`principal_reconstruct` の
  手展開は不要）。
- 状態: ✅ sorry 0（本ファイル単独で green）。
-/

namespace PSS

/-! ## 私的補題層（suffix `_ss`） -/

private theorem adm_zero_ss (M : PS) : adm M 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

/-! ## setup: 記事の 4 節場合分けの前の無条件準備事実

`J₁ = Lng(Br M) - 1`, `j′₀ = Joints(M)_{J₁}`, `j′₁ = FirstNodes(M)_{J₁}` に
ついて (a) `j′₁ < Lng M`（従って `j′₁ ≤ j₁`）, (b) `j′₀ ≤ TrMax M < j′₁`,
(c) `j′₀ = parent M 0 j′₁` と `nextR M 0 j′₀ j′₁`, (d) `Pred M ∈ RT_PS`・
非零項・`Trans (Pred M) ≠ 0`, (e) `TrMax M < j₁`。 -/
theorem subexpr_component_Pred_setup (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1 : 1 < Lng M - 1) :
    (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M ∧
      (FirstNodes M).getD ((Br M).length - 1) 0 ≤ Lng M - 1 ∧
      (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M ∧
      TrMax M < (FirstNodes M).getD ((Br M).length - 1) 0 ∧
      (Joints M).getD ((Br M).length - 1) 0 =
        parent M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
      nextR M 0 ((Joints M).getD ((Br M).length - 1) 0)
        ((FirstNodes M).getD ((Br M).length - 1) 0) = true ∧
      RTPS (Pred M) ∧
      zeroT (Pred M) = false ∧
      Trans (Pred M) ≠ BZero ∧
      TrMax M < Lng M - 1 := by
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  set J1 := (Br M).length - 1 with hJ1def
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1 : J1 < (Br M).length := by omega
  -- (b) `j′₀ ≤ TrMax M < j′₁`
  have htj := FirstNodes_TrMax_Joints M J1 hMT hmono hJ1
  -- (e) `TrMax M < Lng M - 1`（枝が非空）
  have htb := TrMax_bound M hMT
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have htrlt : TrMax M < Lng M - 1 := by omega
  -- (c) `hasParent` at `j′₁`, then `nextR` via `parent`
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
    simp [Br, hne]
  have hJQ : J1 ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]
  have hmsn := mono_slice_next M (TrMax M + 1) J1 hMT hmono
    (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J1 hJ1
  rw [← hBr, ← hfn] at hmsn
  have hhp : hasParent M 0 ((FirstNodes M).getD J1 0) = true := hmsn.1
  have hnext := nextR_parent0_of_hasParent M ((FirstNodes M).getD J1 0) hhp
  have hjoint := Joints_getD M J1 hJ1
  have hnextJ : nextR M 0 ((Joints M).getD J1 0)
      ((FirstNodes M).getD J1 0) = true := by
    rw [hjoint]
    exact hnext
  -- (a) `j′₁ < Lng M` from the `nextR` edge
  have hn0 : nextrel0 M (parent M 0 ((FirstNodes M).getD J1 0))
      ((FirstNodes M).getD J1 0) = true := by
    simpa [nextR] using hnext
  have hfnL : (FirstNodes M).getD J1 0 < Lng M := by
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn0
    exact hn0.1.1.1.2
  -- (d) `Pred M` facts
  have hPR : RTPS (Pred M) := RTPS_Pred M hR
  have hlp : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hzP : zeroT (Pred M) = false := by
    have h1 : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, h1]
  have hPT : TPS (Pred M) := RTPS_TPS (Pred M) hPR
  have hTne : Trans (Pred M) ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT (Pred M) hPT).mpr h
    rw [hzP] at hz
    exact Bool.false_ne_true hz
  exact ⟨hfnL, by omega, htj.1, htj.2, hjoint, hnextJ, hPR, hzP, hTne, htrlt⟩

/-! ## clause (1): Adm-zero 枝の値核（cond I/III/V）

`transJm1 M = 0` なら scb 文字列が潰れて `c₁ = t₁ = Trans (Pred M)` かつ
`Trans M = transC2 M`。cond I/III/V では `c₂` の本体が
`D_v (t₂ + D_{M_{1,j₁}} 0)` なので、`t₁ := t₂` を証人に原文 clause (1) の
右辺が一意に得られる。 -/
theorem subexpr_component_Pred_Adm0_clause1 (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1)
    (hAdm0 : transJm1 M = 0)
    (hcond : (transCondI M || transCondIII M || transCondV M) = true) :
    ∃! t₁, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t₁ (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  -- `Pred M` facts: reduced, nonzero, `Trans (Pred M) ≠ 0`
  have hPR : RTPS (Pred M) := RTPS_Pred M hR
  have hPT : TPS (Pred M) := RTPS_TPS (Pred M) hPR
  have hlp : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hzP : zeroT (Pred M) = false := by
    have h1 : Lng (Pred M) ≠ 1 := by omega
    simp [zeroT, h1]
  have ht₁ : Trans (Pred M) ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT (Pred M) hPT).mpr h
    rw [hzP] at hz
    exact Bool.false_ne_true hz
  -- `Marked M 0` and `Marked (Pred M) 0`
  have hle : leR M 0 0 (Lng M - 1) = true := by
    have hm := hmono
    simp only [monoT, Bool.and_eq_true] at hm
    exact hm.2
  have hM0 : Marked M 0 := ⟨hMT, adm_zero_ss M, hle⟩
  have hP0 : Marked (Pred M) 0 := Marked_Pred M 0 hMT hlen hM0 (by omega)
  have hmonoP : monoT (Pred M) = true := by
    simp [monoT, hzP, hP0.2.2]
  -- (a) scb 文字列の潰れ: `c₁ = t₁ = Trans (Pred M)`
  have hMz : Mark (Pred M) 0 = Trans (Pred M) :=
    Mark_zero_eq_Trans (Pred M) hPR hP0
  have hc1 : transC1 M = Trans (Pred M) := by
    simp [transC1, hAdm0, hMz]
  -- (b)(c) `c₁` は単主要項 `D_{M_{1,0}} t₂`（左端読み取り）
  have hlf := Trans_mono_leftend_form (Pred M) hPR hmonoP
  rcases hlf with h0 | ⟨t, ht⟩
  · exact absurd h0 ht₁
  have he10 : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hlen
  rw [he10] at ht
  -- `transV M` / `transT2 M` の読み取り
  have hV : transV M = (entry M 1 0 : ℕ∞) := by
    simp [transV, hc1, ht, Dprin, bpHeadV]
  have hT2 : transT2 M = t := by
    simp [transT2, hc1, ht, Dprin, bpHeadT]
  -- (e) `Trans M = transC2 M`（`Mark` 連鎖、`transJm1 M = 0` を代入）
  have hTM : Trans M = transC2 M := by
    have h2 := Mark_transJm1_eq_transC2 M hR hmono hlen ht₁
    rw [hAdm0] at h2
    rw [← Mark_zero_eq_Trans M hR hM0, ← h2]
  -- cond I/III/V の `c₂` 本体
  have hc2val : transC2 M = Dprin (entry M 1 0 : ℕ∞)
      (addBT t (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    unfold transC2 transC2Core
    rw [hV, hT2]
    simp [hcond, lastIdx]
  -- 存在＋一意性
  refine ⟨t, ⟨ht, by rw [hTM, hc2val]⟩, ?_⟩
  rintro t' ⟨h1', _h2'⟩
  have hh := ht.symm.trans h1'
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq,
    true_and, and_true] at hh
  exact hh.symm

#print axioms subexpr_component_Pred_setup
#print axioms subexpr_component_Pred_Adm0_clause1

end PSS
