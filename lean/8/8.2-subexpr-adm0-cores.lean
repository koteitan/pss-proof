import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-RightNodes-Mark»
import «7».«7.3-c1-c2-order»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-zeroT»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-leftend»
import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Red-welldefined»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-mono-slice»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «5».«5.1-ancestor-basic»

/-!
# §8.2 部分表現の単項成分と `Pred` — Adm0 clause cores ＋ keystone

- 原文: `tmp/content.md` L3360 付近（§8.2 補題「部分表現の単項成分と Pred の関係」、
  4 clause の場合分け）。訂正 A9 (LastStep の添字) は本補題群には触れない。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `m_8_2_subexpr_component_Pred_Adm0_clause2_core` (20167)
    → `subexpr_component_Pred_Adm0_clause2_core`
  - `m_8_2_subexpr_component_Pred_Adm0_clause4_core` (20290)
    → `subexpr_component_Pred_Adm0_clause4_core`
  - `m_8_2_lastbranch_eq_j1` (20470) → `lastbranch_eq_j1`
  - `m_8_2_subexpr_component_Pred_Adm0_clause1_keystone` (20532)
    → `subexpr_component_Pred_Adm0_clause1_keystone`
- 依存（全て built 済の公開定理）: `Mark_zero_eq_Trans` / `Mark_transJm1_eq_transC2`
  （7.4-Mark-Trans-repr）, `Trans_mono_leftend_form`（7.4-RightNodes-Mark）,
  `transC1_single_principal` / `principal_reconstruct`（7.3-c1-c2-order）,
  `Marked_Pred`（7.3-Trans-welldefined）, `Trans_preserves_zeroT`（7.3）,
  `mono_hasParent_row0`（6.6-P-condAB）, `RTPS_TPS`（6.6-reduced-leftend）,
  `RTPS_Pred` / `length_Pred` / `entry_Pred_zero`（6.5-Red-Pred-commute）,
  `Joints_nextR_FirstNodes`（6.5-Red-welldefined）,
  `TrMax_bound` / `FirstNodes_TrMax_Joints`（6.4-FirstNodes-TrMax-Joints）,
  `FirstNodes_Joints_mono` / `nextR_parent0_of_hasParent` / `nextR0_largest_below`
  （6.4-FirstNodes-Joints-mono）, `branch_component_le0`（6.4-mono-slice）,
  `adm_zero`（6.3-admof-slice）, `ancestor_basic_1`（5.1-ancestor-basic）。
- 私的再証明（並列 agent の scope 19256–20166 に相当、suffix `_sc`）:
  - `adm0_setup_sc` = Isabelle `Trans_eq_transC2_Adm0` (19356) ＋ clause 共通の
    値化パック。Lean では `s₁b₁` 空性が不要:
    `Trans M = Mark M 0 = Mark M (transJm1 M) = transC2 M`
    （`Mark_zero_eq_Trans`＋`Mark_transJm1_eq_transC2`＋`transJm1 M = 0`）、
    `transC1 M = Mark (Pred M) 0 = Trans (Pred M)` が同じ 2 定理で出る。
  - `subexpr_component_Pred_Adm0_clause1_sc`
    = Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause1` (19436)。
- Isabelle の `M ∈ PT_PS` は sibling 8.x file の慣例どおり
  `(hR : RTPS M) (hmono : monoT M = true)` に開いて受ける（`TPS` は `RTPS` から）。
- 状態: 本 wave で完成（sorry 0 を checker で確認）。
-/

namespace PSS

/-! ## 私的補助: `Dprin`/`addBT` の単射性（Isabelle は `Dpt` 単射＋
`append_eq_append_conv`; 8.1-part4 の `_p1`/`_p2` パターンの複製） -/

private theorem Dprin_inj_sc {v w : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin w b) : v = w ∧ a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact h

private theorem addBT_snoc_Dprin_inj_sc {t t' : BT} {v v' : ℕ∞} {b b' : BT}
    (h : addBT t (Dprin v b) = addBT t' (Dprin v' b')) :
    t = t' ∧ v = v' ∧ b = b' := by
  rcases t with ⟨as⟩
  rcases t' with ⟨bs⟩
  simp only [addBT, Dprin, BT.trm.injEq] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, BP.db.injEq, and_true] at h2
  exact ⟨congrArg BT.trm h1, h2.1, h2.2⟩

/-! ## 私的補助: 最終 principal の切り出し（Isabelle `SigmaB_snoc`＋
`principal_reconstruct` の値レベル版） -/

private theorem SigmaB_map_singleton_sc (l : List BP) :
    SigmaB (l.map (fun p => BT.trm [p])) = BT.trm l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      have ihl : ((ps.map (fun p => BT.trm [p])).flatMap untrm) = ps := by
        simpa [SigmaB, BT.trm.injEq] using ih
      simp [SigmaB, untrm, ihl]

private theorem PB_split_last_sc (t : BT) (ht : t ≠ BZero) :
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
    rw [htake, SigmaB_map_singleton_sc]
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

/-! ## 私的補助: Adm0 共通値化パック
（Isabelle `Trans_eq_transC2_Adm0` (layerB 19356) ＋ clause 共通部
(19436/20167/20290 の (a)–(e))。Lean 側の勝ち筋 (memo §4.6):
`Trans M = Mark M 0 = Mark M (transJm1 M) = transC2 M`、
`transC1 M = Mark (Pred M) (transJm1 M) = Mark (Pred M) 0 = Trans (Pred M)`
が `Mark_zero_eq_Trans`＋`Mark_transJm1_eq_transC2` で直接出るため、
`m_7_3_s1_b1_empty` 相当は不要。） -/

private theorem adm0_setup_sc (M : PS) (hR : RTPS M) (hmono : monoT M = true)
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

/-! ## 私的補助: clause (1) 値 core
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause1`, layerB 19436。
並列 agent の scope のため私的に再証明。） -/

private theorem subexpr_component_Pred_Adm0_clause1_sc (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hcond : (transCondI M || transCondIII M || transCondV M) = true) :
    ∃! t₁ : BT,
      Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t₁ (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
  obtain ⟨hTP, hTc2, hV⟩ := adm0_setup_sc M hR hmono hj1gt hAdm0
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_pos hcond, hV]
    rfl
  have hTM : Trans M = Dprin (entry M 1 0 : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) := by
    rw [hTc2, hc2]
  refine ⟨transT2 M, ⟨hTP, hTM⟩, ?_⟩
  rintro t ⟨htP, -⟩
  exact (Dprin_inj_sc (htP.symm.trans hTP)).2

/-! ## 公開定理 1/4: clause (2) 値 core
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause2_core`, layerB 20167）

Adm-zero ＋ ¬(I∨III∨V) ＋ ¬VI ＋ `t₂ ≠ 0` ＋ ¬leftDj₀ の分岐で、
一意な `(t₁, t₂')` が `Trans (Pred M) = D_{M_{1,0}} t₁` と
`Trans M = D_{M_{1,0}}(t₁ + D_{M_{1,j₀}} t₂')` を満たす（`j₀ = transJ0 M`）。 -/

theorem subexpr_component_Pred_Adm0_clause2_core (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hnA : (transCondI M || transCondIII M || transCondV M) = false)
    (hnVI : transCondVI M = false)
    (ht₂ : transT2 M ≠ BZero)
    (hnotleft :
      bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        ≠ (entry M 1 (transJ0 M) : ℕ∞)) :
    ∃! t12 : BT × BT,
      Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t12.1 (Dprin (entry M 1 (transJ0 M) : ℕ∞) t12.2)) := by
  obtain ⟨hTP, hTc2, hV⟩ := adm0_setup_sc M hR hmono hj1gt hAdm0
  have hnA' : ¬((transCondI M || transCondIII M || transCondV M) = true) := by
    simp [hnA]
  have hnVI' : ¬(transCondVI M = true) := by simp [hnVI]
  have ht₂' : ¬((transT2 M == BZero) = true) := by simpa using ht₂
  have hleft' : ¬((bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1)
        BZero) == (entry M 1 (lastParent M) : ℕ∞)) = true) := by
    simpa using hnotleft
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT (transT2 M)
                (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_neg hnA', if_neg hnVI', if_neg ht₂', if_neg hleft', if_neg hleft', hV]
    rfl
  have hTM : Trans M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT (transT2 M)
                (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    rw [hTc2, hc2]
  refine ⟨(transT2 M,
      addBT (transT2 M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)),
    ⟨hTP, hTM⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨haP, haM⟩
  have ha : a = transT2 M := (Dprin_inj_sc (haP.symm.trans hTP)).2
  subst ha
  have h2 := (Dprin_inj_sc (haM.symm.trans hTM)).2
  have h3 := (addBT_snoc_Dprin_inj_sc h2).2.2
  simp only [Prod.mk.injEq, true_and]
  exact h3

/-! ## 公開定理 2/4: clause (4) 値 core
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause4_core`, layerB 20290）

Adm-zero ＋ ¬(I∨III∨V) ＋ ¬VI ＋ `t₂ ≠ 0` ＋ leftDj₀ の分岐で、
`t₂ = Σ(prefix) + D_{M_{1,j₀}} u` と分解され、一意な三つ組
`(Σ(prefix), u, u + D_{M_{1,j₁}} 0)` が clause (4) の両表示を満たす。 -/

theorem subexpr_component_Pred_Adm0_clause4_core (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hnA : (transCondI M || transCondIII M || transCondV M) = false)
    (hnVI : transCondVI M = false)
    (ht₂ : transT2 M ≠ BZero)
    (hisleft :
      bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        = (entry M 1 (transJ0 M) : ℕ∞)) :
    ∃! t123 : BT × BT × BT,
      Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
        (addBT t123.1 (Dprin (entry M 1 (transJ0 M) : ℕ∞) t123.2.1)) ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t123.1 (Dprin (entry M 1 (transJ0 M) : ℕ∞) t123.2.2)) := by
  obtain ⟨hTP, hTc2, hV⟩ := adm0_setup_sc M hR hmono hj1gt hAdm0
  have hnA' : ¬((transCondI M || transCondIII M || transCondV M) = true) := by
    simp [hnA]
  have hnVI' : ¬(transCondVI M = true) := by simp [hnVI]
  have ht₂' : ¬((transT2 M == BZero) = true) := by simpa using ht₂
  have hleftB : ((bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1)
        BZero) == (entry M 1 (lastParent M) : ℕ∞)) = true) := by
    simpa using hisleft
  -- 最終 principal の切り出し `t₂ = pref + D_v u`（leftDj₀ から `v = M_{1,j₀}`）
  obtain ⟨v, u, hgetD, hsplit⟩ := PB_split_last_sc (transT2 M) ht₂
  have hveq : v = (entry M 1 (transJ0 M) : ℕ∞) := by
    rw [hgetD] at hisleft
    simpa [bpHeadV, Dprin] using hisleft
  have hbT : bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
      = u := by
    rw [hgetD]
    simp [bpHeadT, Dprin]
  -- `transC2` の leftDj₀ 分岐
  have hc2 : transC2 M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT u (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    show transC2Core M (transV M) (transT2 M) = _
    simp only [transC2Core]
    rw [if_neg hnA', if_neg hnVI', if_neg ht₂', if_pos hleftB, if_pos hleftB,
      hbT, hV]
    rfl
  have hTM : Trans M
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
            (Dprin (entry M 1 (transJ0 M) : ℕ∞)
              (addBT u (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))) := by
    rw [hTc2, hc2]
  have hTP' : Trans (Pred M)
      = Dprin (entry M 1 0 : ℕ∞)
          (addBT (SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)))
            (Dprin (entry M 1 (transJ0 M) : ℕ∞) u)) := by
    have h := hTP
    rw [hsplit] at h
    rw [hveq] at h
    exact h
  refine ⟨(SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)), u,
      addBT u (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)),
    ⟨hTP', hTM⟩, ?_⟩
  rintro ⟨a, b, c⟩ ⟨haP, haM⟩
  have h1 := (Dprin_inj_sc (haP.symm.trans hTP')).2
  obtain ⟨ha, -, hb⟩ := addBT_snoc_Dprin_inj_sc h1
  subst ha
  subst hb
  have h2 := (Dprin_inj_sc (haM.symm.trans hTM)).2
  have hc := (addBT_snoc_Dprin_inj_sc h2).2.2
  simp only [Prod.mk.injEq, true_and]
  exact hc

/-! ## 公開定理 3/4: 幾何ブリッジ（最終枝の一列性）
（Isabelle `m_8_2_lastbranch_eq_j1`, layerB 20470）

`parent M 0 (Lng M - 1) ≤ TrMax M` の下で、最終枝の first node は最終列に一致:
`FirstNodes(M)_{J₁} = Lng M - 1`。背理法: そうでなければ最終列を含む枝成分の
左端 `f` は `f < Lng M - 1` かつ行 0 で最終列に到達（`branch_component_le0`）、
`ancestor_basic_1` の狭義増加と `nextR0_largest_below` から
`parent M 0 (Lng M - 1) ≥ f > TrMax M` — 仮定に矛盾。 -/

theorem lastbranch_eq_j1 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1)
    (hparTr : parent M 0 (Lng M - 1) ≤ TrMax M) :
    (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hBrpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJBr : (Br M).length - 1 < (Br M).length := by omega
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    apply hBrne
    simp [Br, heq]
  have htrlt : TrMax M < Lng M - 1 := by omega
  -- 最終枝 first node の上界: `Joints → FirstNodes` の行 0 辺から
  have hnx := Joints_nextR_FirstNodes M ((Br M).length - 1) hM hmono hJBr
  have hj1lt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M := by
    have hh : nextrel0 M ((Joints M).getD ((Br M).length - 1) 0)
        ((FirstNodes M).getD ((Br M).length - 1) 0) = true := by
      simpa [nextR] using hnx
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.2
  -- 最終列を行 0 で覆う枝成分の左端 `f = FirstNodes(M)_J`
  obtain ⟨J, hJlen, hle⟩ := branch_component_le0 M (Lng M - 1) hM hmono
    htrlt (le_refl _)
  have hfJlt : (FirstNodes M).getD J 0 < Lng M := by
    have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJlen
    have hh : nextrel0 M ((Joints M).getD J 0)
        ((FirstNodes M).getD J 0) = true := by
      simpa [nextR] using hnxJ
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.2
  by_cases hfJ : (FirstNodes M).getD J 0 = Lng M - 1
  · -- 左端が最終列そのもの → `FirstNodes` の単調性で最終枝も最終列
    by_cases hJlast : J = (Br M).length - 1
    · rw [← hJlast]
      exact hfJ
    · have hJlt : J < (Br M).length - 1 := by omega
      obtain ⟨hle01, -, -⟩ :=
        FirstNodes_Joints_mono M J ((Br M).length - 1) hM hmono hJlt hJBr
      omega
  · -- 左端が内部 → 行 0 狭義増加 → 親は `f` 以上 → `TrMax` 越え、矛盾
    exfalso
    have hfJlt2 : (FirstNodes M).getD J 0 < Lng M - 1 := by omega
    have hentlt : entry M 0 ((FirstNodes M).getD J 0)
        < entry M 0 (Lng M - 1) :=
      ancestor_basic_1 M ((FirstNodes M).getD J 0) (Lng M - 1) (Lng M - 1) hM
        hfJlt2 (le_refl _) hle
    have hp : hasParent M 0 (Lng M - 1) = true :=
      mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
    have hnext : nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true :=
      nextR_parent0_of_hasParent M (Lng M - 1) hp
    have hlb : (FirstNodes M).getD J 0 ≤ parent M 0 (Lng M - 1) :=
      nextR0_largest_below M (parent M 0 (Lng M - 1))
        ((FirstNodes M).getD J 0) (Lng M - 1) hnext hfJlt2 hentlt
    obtain ⟨-, htrJ⟩ := FirstNodes_TrMax_Joints M J hM hmono hJlen
    omega

/-! ## 公開定理 4/4: clause (1) keystone（組み立て）
（Isabelle `m_8_2_subexpr_component_Pred_Adm0_clause1_keystone`, layerB 20532）

値 core (clause1) を幾何ブリッジ `j₁' = j₁`（仮定 `hj1eq`、Adm0 分岐では
`lastbranch_eq_j1`＋H3 で別途 discharge される）で `entry M 1 j₁'` 表示に持ち上げ、
ガード `gA`/`gB`（仮定）と束ねて keystone clause (1) の 4 連言を得る。 -/

theorem subexpr_component_Pred_Adm0_clause1_keystone (M : PS)
    (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0)
    (hcond : (transCondI M || transCondIII M || transCondV M) = true)
    (hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1)
    (hgA : TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (hgB : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
        ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true) :
    (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
    ∧ (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    ∧ (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
        ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
    ∧ ∃! t₁ : BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
          (addBT t₁ (Dprin
            (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            BZero)) := by
  have core := subexpr_component_Pred_Adm0_clause1_sc M hR hmono hj1gt hAdm0 hcond
  refine ⟨hj1eq, hgA, hgB, ?_⟩
  rw [hj1eq]
  exact core

#print axioms subexpr_component_Pred_Adm0_clause2_core
#print axioms subexpr_component_Pred_Adm0_clause4_core
#print axioms lastbranch_eq_j1
#print axioms subexpr_component_Pred_Adm0_clause1_keystone

end PSS
