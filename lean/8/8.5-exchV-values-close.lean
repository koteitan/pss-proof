import «8».«8.5-exchV-M-tower-close»
import «8».«8.4-oper5-residual»
import «8».«8.4-rightmost-replace-Trans»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Mark-rightmost2»
import «7».«7.2-scb-compose»
import «7».«7.2-add-scb»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.5 ExchV 底値の無条件化

`ExchVMValueResidual` の `PredNp` / `Lpv` / `L1v` を、許容枝と非許容枝に分ける。
許容枝は3値すべてを閉じ、非許容枝は Isabelle `nf2x_Lpv` / `nf2x_L1v` により
`PredNp` / `Np` / `c₂(L₁)` の原子3値だけへ縮約する。
-/

namespace PSS

/-! ## `L₁` の共有構造 -/

/-- admissible 条件(V) host の `L₁ := s84x_L M 1` に必要な構造束。
Isabelle `s85b_L1_decomp_adm` の列幾何部分を分離したもの。 -/
private theorem exchV_L1_structure_adm (M : PS) (hST : STPS M)
    (hmono : monoT M = true) (hcond : transCondV M = true)
    (hadm : adm M (transJ0 M) = true) :
    let L1 := s84x_L M 1
    RTPS L1 ∧ monoT L1 = true ∧ Lng L1 = Lng M ∧ Pred L1 = Pred M ∧
      transJ0 L1 = transJ0 M ∧ transJm1 L1 = transJ0 M ∧
      Marked L1 (transJ0 M) ∧
      seg L1 (transJ0 M) (Lng L1 - 1) = s84x_Lp M := by
  dsimp only
  let L1 := s84x_L M 1
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj1pos
    omega
  have hjm2 : s84x_jm2 M = transJ0 M :=
    (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hp1 : hasParent M 1 (Lng M - 1) = true :=
    (condV_bridge_hp_jm2 M hM hmono hcond).1
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hj1 : 1 < Lng M - 1 := by omega
  have hjm2lt : s84x_jm2 M < Lng M - 1 :=
    (s84c1_jm2_basic M hp1).1
  have hlejm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [leR] using (s84c1_jm2_basic M hp1).2.2
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1)
      hM hjm2lt (le_refl _) hlejm2
  have hsum : entry M 0 (s84x_jm2 M)
        + (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
      = entry M 0 (Lng M - 1) := by omega
  have hL1form : L1 = Pred M ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))] := by
    rw [show L1 = s84x_L M 1 from rfl, s84x_L_eq_append,
      ← pred_is_oper1 M hM hlen]
    simp [hsum]
  have hPredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLngL1 : Lng L1 = Lng M := by
    rw [hL1form]
    simp only [List.length_append, List.length_cons, List.length_nil, hPredLen]
    omega
  have hPredL1 : Pred L1 = Pred M := by
    rw [Pred_eq_take L1 (by rw [hLngL1]; omega), hL1form]
    have htake : (Pred M ++
        [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]).take (Lng M - 1)
        = Pred M := by
      rw [← hPredLen]
      exact List.take_left' rfl
    simpa [hLngL1] using htake
  have hpairPrefix : ∀ j, j < Lng M - 1 →
      L1.getD j (0, 0) = M.getD j (0, 0) := by
    intro j hj
    have hjP : j < Lng (Pred M) := by rw [hPredLen]; exact hj
    have hjM : j < Lng M := by omega
    rw [hL1form, Pred_eq_take M hlen]
    have hjTake : j < (M.take (Lng M - 1)).length := by simp; omega
    change ((M.take (Lng M - 1) ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))])[j]?).getD (0, 0)
        = (M[j]?).getD (0, 0)
    rw [List.getElem?_append_left hjTake, List.getElem?_take]
    simp [hj]
  have hentry0 : ∀ j, j < Lng M → entry L1 0 j = entry M 0 j := by
    intro j hj
    by_cases hjp : j < Lng M - 1
    · rw [hL1form, entry_append_left_mr (Pred M) _ 0 j (by rw [hPredLen]; exact hjp),
        Pred_eq_take M hlen, entry_take M (Lng M - 1) 0 j hjp]
    · have hjlast : j = Lng M - 1 := by omega
      subst j
      rw [hL1form, entry_append_right_mr (Pred M) _ 0 (Lng M - 1)
        (by rw [hPredLen]), hPredLen]
      simp [entry]
  have hmonoL1 : monoT L1 = true := by
    have hleM : le0 M 0 (Lng M - 1) = true := by
      have h := hmono
      simp only [monoT, Bool.and_eq_true] at h
      simpa [leR] using h.2
    have hleL : le0 L1 0 (Lng L1 - 1) = true := by
      rw [hLngL1]
      rw [le0_row0_congr M L1 id hLngL1.symm strictMono_id
        (by intro j hj; simpa using hentry0 j hj)]
      exact hleM
    have hzL : zeroT L1 = false := by
      simp [zeroT, hLngL1]
      omega
    simp [monoT, hzL, leR, hleL]
  have hRT : RTPS L1 := by
    simpa [L1] using RTPS_s84x_L M 1 hST hp1 hj1 (by omega)
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hnext0eq (a b : ℕ) : nextR L1 0 a b = nextR M 0 a b := by
    simp only [nextR]
    exact nextrel0_row0_congr M L1 id hLngL1.symm strictMono_id
      (by intro j hj; simpa using hentry0 j hj) a b
  have hnextL : nextR L1 0 (transJ0 M) (Lng L1 - 1) = true := by
    rw [hLngL1, hnext0eq]
    exact hnextM
  obtain ⟨p, hp, huniq⟩ := (hasParent_iff_unique_fseq M 0 (Lng M - 1)).mp hp0
  have hpj0 : p = transJ0 M := by
    exact (huniq (transJ0 M) hnextM).symm
  subst p
  have huniqL : ∀ y, nextR L1 0 y (Lng L1 - 1) = true → y = transJ0 M := by
    intro y hy
    apply huniq
    have hy' : nextR L1 0 y (Lng M - 1) = true := by
      simpa [hLngL1] using hy
    rw [hnext0eq] at hy'
    exact hy'
  have hparentL : parent L1 0 (Lng L1 - 1) = transJ0 M :=
    parent_eq_of_unique_fseq L1 0 (Lng L1 - 1) (transJ0 M) hnextL huniqL
  have hj0L : transJ0 L1 = transJ0 M := by
    simpa [transJ0, lastParent, lastIdx] using hparentL
  have hnextA : nextR L1 1 (transJ0 M - 1) (transJ0 M)
      = nextR M 1 (transJ0 M - 1) (transJ0 M) :=
    nextR_prefix_agree_68 L1 M (Lng M - 2) 1 (transJ0 M - 1) (transJ0 M)
      (by intro j hj; exact hpairPrefix j (by omega))
      (by rw [hLngL1]; omega) (by omega) (by omega) (by omega)
  have hnextB : nextR L1 1 (transJ0 M) (transJ0 M + 1)
      = nextR M 1 (transJ0 M) (transJ0 M + 1) :=
    nextR_prefix_agree_68 L1 M (Lng M - 2) 1 (transJ0 M) (transJ0 M + 1)
      (by intro j hj; exact hpairPrefix j (by omega))
      (by rw [hLngL1]; omega) (by omega) (by omega) (by omega)
  have hnadm : nadm L1 (transJ0 M) = nadm M (transJ0 M) := by
    simp only [nadm, hLngL1, hnextA, hnextB]
  have hadmL : adm L1 (transJ0 M) = true := by
    simpa [adm, hnadm] using hadm
  have hjm1L : transJm1 L1 = transJ0 M := by
    simp [transJm1, hj0L, Adm, hadmL]
  have hmkL : Marked L1 (transJ0 M) :=
    ⟨RTPS_TPS L1 hRT, hadmL, nextR0_leR L1 _ _ hnextL⟩
  have hPredDrop : (Pred M).drop (transJ0 M) =
      seg M (transJ0 M) (Lng M - 2) := by
    rw [← seg_to_last_eq_drop (Pred M) (transJ0 M) (by rw [hPredLen]; omega)]
    have hseg := seg_Pred_eq M (transJ0 M) (Lng M - 2) hlen (by omega) (by omega)
    simpa [hPredLen] using hseg
  have hsegL : seg L1 (transJ0 M) (Lng L1 - 1) = s84x_Lp M := by
    rw [seg_to_last_eq_drop L1 (transJ0 M) (by rw [hLngL1]; omega), hL1form,
      List.drop_append_of_le_length (by change transJ0 M ≤ Lng (Pred M); rw [hPredLen]; omega),
      hPredDrop]
    simp [s84x_Lp, hjm2]
  exact ⟨hRT, hmonoL1, hLngL1, hPredL1, hj0L, hjm1L, hmkL, hsegL⟩

/-- Isabelle `m_8_5_scbdec_Np_condV_adm` の値結論。
許容枝では `s84x_Np M` が `M` の marked terminal slice であり、値は条件(V) の
`transC2` 閉形式になる。 -/
theorem exchV_Np_adm (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hadm : adm M (transJ0 M) = true) :
    Trans (s84x_Np M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨hV, _hc1, _ht2, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hjm1 : transJm1 M = transJ0 M := by
    simp [transJm1, Adm, hadm]
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnext0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hmk : Marked M (transJ0 M) :=
    ⟨hM, hadm, nextR0_leR M _ _ hnext0⟩
  have hrepr : Mark M (transJ0 M) =
      Trans (seg M (transJ0 M) (Lng M - 1)) :=
    Mark_Trans_repr M (transJ0 M) hmk hR (by omega)
  have hjm2 : s84x_jm2 M = transJ0 M :=
    (condV_bridge_hp_jm2 M hM hmono hcond).2
  calc
    Trans (s84x_Np M) = Mark M (transJ0 M) := by
      rw [hrepr, s84x_Np, hjm2]
    _ = transC2 M := by
      rw [← hjm1]
      exact m_7_3_Mark_rightmost2 M hR hmono hj1pos ht1ne
    _ = Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
      rw [transC2_condV_eq M hcond, hV, hjm1]

/-- Isabelle `m_8_5_scbdec_PredNp_condV_adm` の値結論。
許容枝では `j₋₁ = j₀` なので、`Pred (s84x_Np M)` は `Pred M` の marked terminal
slice そのものであり、`Mark_Trans_repr` から `transC1 M = D_{M₁,j₀} t₂` を読む。 -/
theorem exchV_PredNp_adm (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hadm : adm M (transJ0 M) = true) :
    Trans (Pred (s84x_Np M)) =
      Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, hc1, _ht2, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hjm1 : transJm1 M = transJ0 M := by
    simp [transJm1, Adm, hadm]
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmk0 : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp0
  have hadm0 : adm M (parent M 0 (Lng M - 1)) = true := by
    simpa [transJ0, lastParent, lastIdx] using hadm
  have hAdm0 : Adm M (parent M 0 (Lng M - 1)) = parent M 0 (Lng M - 1) := by
    simp [Adm, hadm0]
  have hmk : Marked (Pred M) (transJ0 M) := by
    rw [hAdm0] at hmk0
    simpa [transJ0, lastParent, lastIdx] using hmk0
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hrepr : Mark (Pred M) (transJ0 M) =
      Trans (seg (Pred M) (transJ0 M) (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (transJ0 M) hmk hpredR (by rw [hpredLen]; omega)
  have hsegPred :
      seg (Pred M) (transJ0 M) (Lng (Pred M) - 1) =
        seg M (transJ0 M) (Lng M - 2) := by
    rw [hpredLen]
    exact seg_Pred_eq M (transJ0 M) (Lng M - 2) hlen (by omega) (by omega)
  have hjm2 : s84x_jm2 M = transJ0 M :=
    (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hpredNp : Pred (s84x_Np M) = seg M (transJ0 M) (Lng M - 2) := by
    rw [Pred_s84x_Np M (by rw [hjm2]; omega), hjm2]
  calc
    Trans (Pred (s84x_Np M))
        = Trans (seg M (transJ0 M) (Lng M - 2)) := by rw [hpredNp]
    _ = Mark (Pred M) (transJ0 M) := by rw [← hsegPred, ← hrepr]
    _ = transC1 M := by simp [transC1, hjm1]
    _ = Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) := by rw [hc1, hjm1]

/-- Isabelle `nf2x_Lpv`。`Np` の値だけを入力に、§8.4 の訂正済み右端置換対で
`N'` の最終 principal を置換し、同じ scb 文脈を `D_e` の内側へ持ち上げて
`Trans L'` を読み戻す。この本体は `adm` に依存しない。 -/
theorem exchV_Lp_of_Np (hrr : Rightmost84ReplaceCorrected) (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true)
    (hNp : Trans (s84x_Np M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M)
        (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))) :
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc1, ht2TB, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hjm2 : s84x_jm2 M = transJ0 M :=
    (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hp1 : hasParent M 1 (Lng M - 1) = true :=
    (condV_bridge_hp_jm2 M hM hmono hcond).1
  have hrng : s84x_jm2 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [hjm2]
    simpa [transJ0, lastParent, lastIdx] using h.2
  let dv1 := Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero
  let de := Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero
  have hzeroTB : BZero ∈ T_B := by
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hdv1TB : dv1 ∈ T_B :=
    Dprin_mem_T_B (by simp) hzeroTB
  have hdeTB : de ∈ T_B :=
    Dprin_mem_T_B (by simp) hzeroTB
  have hdv1P : ∃ p, dv1 = .trm [p] :=
    ⟨.db (entry M 1 (transJ1 M) : ℕ∞) BZero, rfl⟩
  have hdeP : ∃ p, de = .trm [p] :=
    ⟨.db (entry M 1 (transJ0 M) : ℕ∞) BZero, rfl⟩
  obtain ⟨s0, b0, hd0⟩ :=
    add_scb_marked (transT2 M) dv1 ht2TB hdv1TB hdv1P
  have hdv1str : isPTB_str (flatBT dv1) := by
    refine ⟨.db (entry M 1 (transJ1 M) : ℕ∞) BZero, ?_, ?_⟩
    · simp [dfree_BP, BZero, dfree_BT, dfree_BPList]
    · simp [dv1, Dprin, flatBT]
  have hwit : scb_decomp (Trans (s84x_Np M))
      (.dsym (entry M 1 (transJ0 M) : ℕ∞) :: s0) (flatBT dv1) b0 := by
    have hcomp := scb_compose_dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) dv1) s0 (flatBT dv1) b0 hd0 hdv1str
    simpa [dv1, hNp] using hcomp
  obtain ⟨sb, hpair, _huniq⟩ := hrr M hST hmono hp1 hrng
  have hpartNp := hpair.1
  have hpartLp := hpair.2
  have hpartNp' : scb_decomp (Trans (s84x_Np M)) sb.1 (flatBT dv1) sb.2 := by
    simpa [dv1, transJ1, lastIdx] using hpartNp
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (s84x_Np M))
    sb.1 (.dsym (entry M 1 (transJ0 M) : ℕ∞) :: s0) (flatBT dv1) sb.2 b0
    hpartNp' hwit
  have hdLp : scb_decomp (Trans (s84x_Lp M))
      (.dsym (entry M 1 (transJ0 M) : ℕ∞) :: s0) (flatBT de) b0 := by
    rw [hs] at hpartLp
    rw [hb] at hpartLp
    simpa [rrLp, s84x_Lp, de, hjm2] using hpartLp
  have hdSub : scb_decomp (addBT (transT2 M) de) s0 (flatBT de) b0 :=
    add_scb_replace_last (transT2 M) dv1 de s0 b0 ht2TB hdv1TB hdv1P
      hdeTB hdeP hd0
  have hdeStr : isPTB_str (flatBT de) := by
    refine ⟨.db (entry M 1 (transJ0 M) : ℕ∞) BZero, ?_, ?_⟩
    · simp [dfree_BP, BZero, dfree_BT, dfree_BPList]
    · simp [de, Dprin, flatBT]
  have htarget : scb_decomp
      (Dprin (entry M 1 (transJ0 M) : ℕ∞) (addBT (transT2 M) de))
      (.dsym (entry M 1 (transJ0 M) : ℕ∞) :: s0) (flatBT de) b0 :=
    scb_compose_dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) de) s0 (flatBT de) b0 hdSub hdeStr
  apply flatBT_injective
  rw [hdLp.1, htarget.1]

/-- Isabelle `m_8_5_scbdec_Lp_condV_adm` の admissible 特殊化。 -/
theorem exchV_Lp_adm (hrr : Rightmost84ReplaceCorrected) (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hadm : adm M (transJ0 M) = true) :
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) :=
  exchV_Lp_of_Np hrr M hST hmono hcond
    (exchV_Np_adm M hST hmono hcond hadm)

/-! ## non-admissible `L₁` surgery の共有構造 -/

/-- `adm` が `≤ j` で一致すれば、`Adm` も一致する。 -/
private theorem find_adm_congr_xv (A B : PS) :
    ∀ (l : List ℕ), (∀ k ∈ l, adm A k = adm B k) →
      l.find? (fun j' => adm A j') = l.find? (fun j' => adm B j')
  | [], _ => rfl
  | x :: xs, h => by
      have hx : adm A x = adm B x := h x (by simp)
      have ih := find_adm_congr_xv A B xs
        (fun k hk => h k (List.mem_cons_of_mem _ hk))
      cases hpx : adm B x with
      | true =>
          rw [List.find?_cons_of_pos (by rw [hx]; exact hpx),
            List.find?_cons_of_pos hpx]
      | false =>
          rw [List.find?_cons_of_neg (by rw [hx, hpx]; simp),
            List.find?_cons_of_neg (by rw [hpx]; simp), ih]

private theorem Adm_eq_of_adm_below_xv (A B : PS) (j : ℕ)
    (h : ∀ k, k ≤ j → adm A k = adm B k) : Adm A j = Adm B j := by
  unfold Adm
  rw [h j (le_refl j)]
  cases hj : adm B j with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true, if_false]
      congr 1
      apply find_adm_congr_xv
      intro k hk
      have hkj : k < j := List.mem_range.mp (List.mem_reverse.mp hk)
      exact h k (by omega)

/-- `L₁ := s84x_L M 1` の `adm` 非依存部分。`Pred`・行0親・接頭辞を host と共有する。 -/
private theorem exchV_L1_prefix_structure (M : PS) (hST : STPS M)
    (hmono : monoT M = true) (hcond : transCondV M = true) :
    let L1 := s84x_L M 1
    RTPS L1 ∧ monoT L1 = true ∧ Lng L1 = Lng M ∧ Pred L1 = Pred M ∧
      transJ0 L1 = transJ0 M ∧
      (∀ j, j < Lng M - 1 → L1.getD j (0, 0) = M.getD j (0, 0)) := by
  dsimp only
  let L1 := s84x_L M 1
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  obtain ⟨hj1pos, _ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj1pos
    omega
  have hjm2 : s84x_jm2 M = transJ0 M :=
    (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hp1 : hasParent M 1 (Lng M - 1) = true :=
    (condV_bridge_hp_jm2 M hM hmono hcond).1
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hj1 : 1 < Lng M - 1 := by omega
  have hjm2lt : s84x_jm2 M < Lng M - 1 :=
    (s84c1_jm2_basic M hp1).1
  have hlejm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [leR] using (s84c1_jm2_basic M hp1).2.2
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1)
      hM hjm2lt (le_refl _) hlejm2
  have hsum : entry M 0 (s84x_jm2 M)
        + (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
      = entry M 0 (Lng M - 1) := by omega
  have hL1form : L1 = Pred M ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))] := by
    rw [show L1 = s84x_L M 1 from rfl, s84x_L_eq_append,
      ← pred_is_oper1 M hM hlen]
    simp [hsum]
  have hPredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLngL1 : Lng L1 = Lng M := by
    rw [hL1form]
    simp only [List.length_append, List.length_cons, List.length_nil, hPredLen]
    omega
  have hPredL1 : Pred L1 = Pred M := by
    rw [Pred_eq_take L1 (by rw [hLngL1]; omega), hL1form]
    have htake : (Pred M ++
        [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]).take (Lng M - 1)
        = Pred M := by
      rw [← hPredLen]
      exact List.take_left' rfl
    simpa [hLngL1] using htake
  have hpairPrefix : ∀ j, j < Lng M - 1 →
      L1.getD j (0, 0) = M.getD j (0, 0) := by
    intro j hj
    rw [hL1form, Pred_eq_take M hlen]
    have hjTake : j < (M.take (Lng M - 1)).length := by simp; omega
    change ((M.take (Lng M - 1) ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))])[j]?).getD (0, 0)
        = (M[j]?).getD (0, 0)
    rw [List.getElem?_append_left hjTake, List.getElem?_take]
    simp [hj]
  have hentry0 : ∀ j, j < Lng M → entry L1 0 j = entry M 0 j := by
    intro j hj
    by_cases hjp : j < Lng M - 1
    · rw [hL1form, entry_append_left_mr (Pred M) _ 0 j (by rw [hPredLen]; exact hjp),
        Pred_eq_take M hlen, entry_take M (Lng M - 1) 0 j hjp]
    · have hjlast : j = Lng M - 1 := by omega
      subst j
      rw [hL1form, entry_append_right_mr (Pred M) _ 0 (Lng M - 1)
        (by rw [hPredLen]), hPredLen]
      simp [entry]
  have hmonoL1 : monoT L1 = true := by
    have hleM : le0 M 0 (Lng M - 1) = true := by
      have h := hmono
      simp only [monoT, Bool.and_eq_true] at h
      simpa [leR] using h.2
    have hleL : le0 L1 0 (Lng L1 - 1) = true := by
      rw [hLngL1]
      rw [le0_row0_congr M L1 id hLngL1.symm strictMono_id
        (by intro j hj; simpa using hentry0 j hj)]
      exact hleM
    have hzL : zeroT L1 = false := by
      simp [zeroT, hLngL1]
      omega
    simp [monoT, hzL, leR, hleL]
  have hRT : RTPS L1 := by
    simpa [L1] using RTPS_s84x_L M 1 hST hp1 hj1 (by omega)
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hnext0eq (a b : ℕ) : nextR L1 0 a b = nextR M 0 a b := by
    exact nextrel0_row0_congr M L1 id hLngL1.symm strictMono_id
      (by intro j hj; simpa using hentry0 j hj) a b
  have hnextL : nextR L1 0 (transJ0 M) (Lng L1 - 1) = true := by
    rw [hLngL1, hnext0eq]
    exact hnextM
  obtain ⟨p, hp, huniq⟩ := (hasParent_iff_unique_fseq M 0 (Lng M - 1)).mp hp0
  have hpj0 : p = transJ0 M := (huniq (transJ0 M) hnextM).symm
  subst p
  have huniqL : ∀ y, nextR L1 0 y (Lng L1 - 1) = true → y = transJ0 M := by
    intro y hy
    apply huniq
    have hy' : nextR L1 0 y (Lng M - 1) = true := by
      simpa [hLngL1] using hy
    rw [hnext0eq] at hy'
    exact hy'
  have hparentL : parent L1 0 (Lng L1 - 1) = transJ0 M :=
    parent_eq_of_unique_fseq L1 0 (Lng L1 - 1) (transJ0 M) hnextL huniqL
  have hj0L : transJ0 L1 = transJ0 M := by
    simpa [transJ0, lastParent, lastIdx] using hparentL
  exact ⟨hRT, hmonoL1, hLngL1, hPredL1, hj0L, hpairPrefix⟩

/-- Isabelle `nf2x_L1v`。`c₂(L₁)` の値だけから host と共有する scb wrapper を
`Trans L₁` へ移す。`adm` の真偽には依存しない。 -/
theorem exchV_L1_decomp_of_c2 (M : PS) (s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hd1 : scb_decomp (Trans (oper M 1)) s1
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b1)
    (hc2L1 : transC2 (s84x_L M 1) =
      Dprin (entry M 1 (transJm1 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))))) :
    scb_decomp (Trans (s84x_L M 1)) s1
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))))) b1 := by
  let L1 := s84x_L M 1
  obtain ⟨hL1R, hL1mono, hLngL1, hPredL1, hj0L1, hprefix⟩ :=
    exchV_L1_prefix_structure M hST hmono hcond
  have hL1R' : RTPS L1 := by simpa [L1] using hL1R
  have hL1mono' : monoT L1 = true := by simpa [L1] using hL1mono
  have hLngL1' : Lng L1 = Lng M := by simpa [L1] using hLngL1
  have hPredL1' : Pred L1 = Pred M := by simpa [L1] using hPredL1
  have hj0L1' : transJ0 L1 = transJ0 M := by simpa [L1] using hj0L1
  have hprefix' : ∀ j, j < Lng M - 1 →
      L1.getD j (0, 0) = M.getD j (0, 0) := by simpa [L1] using hprefix
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, hc1M, _ht2, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hadmAgree : ∀ k, k ≤ transJ0 M → adm L1 k = adm M k := by
    intro k hk
    have hnextA : nextR L1 1 (k - 1) k = nextR M 1 (k - 1) k :=
      nextR_prefix_agree_68 L1 M (Lng M - 2) 1 (k - 1) k
        (by intro j hj; exact hprefix' j (by omega))
        (by rw [hLngL1']; omega) (by omega) (by omega) (by omega)
    have hnextB : nextR L1 1 k (k + 1) = nextR M 1 k (k + 1) :=
      nextR_prefix_agree_68 L1 M (Lng M - 2) 1 k (k + 1)
        (by intro j hj; exact hprefix' j (by omega))
        (by rw [hLngL1']; omega) (by omega) (by omega) (by omega)
    simp [adm, nadm, hLngL1', hnextA, hnextB]
  have hAdm : Adm L1 (transJ0 M) = Adm M (transJ0 M) :=
    Adm_eq_of_adm_below_xv L1 M (transJ0 M) hadmAgree
  have hjm1L1 : transJm1 L1 = transJm1 M := by
    simp [transJm1, hj0L1', hAdm]
  have hJ1L1 : 0 < transJ1 L1 := by
    simp [transJ1, lastIdx, hLngL1']
    omega
  have hT1L1 : transT1 L1 ≠ BZero := by
    simpa [transT1, hPredL1'] using ht1ne
  have hc1share : transC1 L1 = transC1 M := by
    simp [transC1, hjm1L1, hPredL1']
  have hc2P : ∃ p, transC2 L1 = .trm [p] := by
    refine ⟨.db (entry M 1 (transJm1 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))), ?_⟩
    simpa [L1, Dprin] using hc2L1
  obtain ⟨s, b, hdP, hdL⟩ :=
    trans_surgery_shared_xv L1 hL1R' hL1mono' hJ1L1 hT1L1 hc2P
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj1pos
    omega
  have hd1M : scb_decomp (Trans (Pred M)) s1 (flatBT (transC1 M)) b1 := by
    rw [pred_is_oper1 M hM hlen, hc1M]
    exact hd1
  have hd1L : scb_decomp (Trans (Pred L1)) s1 (flatBT (transC1 L1)) b1 := by
    simpa [hPredL1', hc1share] using hd1M
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (Pred L1))
    s s1 (flatBT (transC1 L1)) b b1 hdP hd1L
  rw [hs, hb] at hdL
  simpa [L1, hc2L1] using hdL

/-- Isabelle `s85b_L1_decomp_adm` の surgery 中核。
`L₁` は `Pred` と `c₁` の scb 文脈を host と共有し、固有の `c₂` は `Trans L'`。 -/
theorem exchV_L1_decomp_adm (hrr : Rightmost84ReplaceCorrected) (M : PS)
    (s1 b1 : List Sym) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hadm : adm M (transJ0 M) = true)
    (hd1 : scb_decomp (Trans (oper M 1)) s1
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M))) b1) :
    scb_decomp (Trans (s84x_L M 1)) s1
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))) b1 := by
  let L1 := s84x_L M 1
  obtain ⟨hL1R, hL1mono, hLngL1, hPredL1, hj0L1, hjm1L1, hmkL1, hsegL1⟩ :=
    exchV_L1_structure_adm M hST hmono hcond hadm
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, hc1M, _ht2, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hjm1M : transJm1 M = transJ0 M := by
    simp [transJm1, Adm, hadm]
  rw [hjm1M] at hc1M
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj1pos
    omega
  have hPredL1' : Pred L1 = Pred M := by simpa [L1] using hPredL1
  have hLngL1' : Lng L1 = Lng M := by simpa [L1] using hLngL1
  have hjm1L1' : transJm1 L1 = transJ0 M := by simpa [L1] using hjm1L1
  have hmkL1' : Marked L1 (transJ0 M) := by simpa [L1] using hmkL1
  have hsegL1' : seg L1 (transJ0 M) (Lng L1 - 1) = s84x_Lp M := by
    simpa [L1] using hsegL1
  have hL1R' : RTPS L1 := by simpa [L1] using hL1R
  have hL1mono' : monoT L1 = true := by simpa [L1] using hL1mono
  have hJ1L1 : 0 < transJ1 L1 := by
    simp [transJ1, lastIdx, hLngL1']
    omega
  have hT1L1 : transT1 L1 ≠ BZero := by
    simpa [transT1, hPredL1'] using ht1ne
  have hc1share : transC1 L1 = transC1 M := by
    simp [transC1, hjm1L1', hjm1M, hPredL1']
  have hreprL1 : Mark L1 (transJ0 M) =
      Trans (seg L1 (transJ0 M) (Lng L1 - 1)) :=
    Mark_Trans_repr L1 (transJ0 M) hmkL1' hL1R' (by rw [hLngL1']; omega)
  have hLp := exchV_Lp_adm hrr M hST hmono hcond hadm
  let target := Dprin (entry M 1 (transJ0 M) : ℕ∞)
    (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))
  have hc2L1 : transC2 L1 = target := by
    calc
      transC2 L1 = Mark L1 (transJm1 L1) :=
        (m_7_3_Mark_rightmost2 L1 hL1R' hL1mono' hJ1L1 hT1L1).symm
      _ = Mark L1 (transJ0 M) := by rw [hjm1L1']
      _ = Trans (seg L1 (transJ0 M) (Lng L1 - 1)) := hreprL1
      _ = Trans (s84x_Lp M) := by rw [hsegL1']
      _ = target := by simpa [target] using hLp
  have hc2P : ∃ p, transC2 L1 = .trm [p] := by
    refine ⟨.db (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)), ?_⟩
    simpa [target, Dprin] using hc2L1
  obtain ⟨s, b, hdP, hdL⟩ :=
    trans_surgery_shared_xv L1 hL1R' hL1mono' hJ1L1 hT1L1 hc2P
  have hd1M : scb_decomp (Trans (Pred M)) s1 (flatBT (transC1 M)) b1 := by
    rw [pred_is_oper1 M hM hlen, hc1M]
    exact hd1
  have hd1L : scb_decomp (Trans (Pred L1)) s1 (flatBT (transC1 L1)) b1 := by
    simpa [hPredL1', hc1share] using hd1M
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (Pred L1))
    s s1 (flatBT (transC1 L1)) b b1 hdP hd1L
  rw [hs, hb] at hdL
  simpa [L1, target, hc2L1] using hdL

/-- `ExchVMValueResidual` の admissible 枝を全て閉じる。
結論は `PredNp` / `Lpv` / `L1v` の 3 値そのもの。 -/
theorem exchV_values_adm (hrr : Rightmost84ReplaceCorrected) (M : PS)
    (s0 s1 b0 b1 : List Sym) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hadm : adm M (transJ0 M) = true)
    (hd0 : scb_decomp
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s0 (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b0)
    (hd1 : scb_decomp (Trans (oper M 1)) s1
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b1) :
    Trans (Pred (s84x_Np M)) =
        Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) ∧
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) ∧
    flatBT (Trans (s84x_L M 1))
      = s1 ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: (List.replicate (exchV_tail M 1)
                (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (exchV_tail M 1) b0).flatten ++ b1 := by
  have hjm1 : transJm1 M = transJ0 M := by
    simp [transJm1, Adm, hadm]
  have hd1' : scb_decomp (Trans (oper M 1)) s1
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M))) b1 := by
    simpa [hjm1] using hd1
  have hPredNp := exchV_PredNp_adm M hST hmono hcond hadm
  have hLp := exchV_Lp_adm hrr M hST hmono hcond hadm
  have hdL1 := exchV_L1_decomp_adm hrr M s1 b1 hST hmono hcond hadm hd1'
  let dv1 := Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero
  let de := Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc1, ht2TB, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hzeroTB : BZero ∈ T_B := by
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hdv1TB : dv1 ∈ T_B := Dprin_mem_T_B (by simp) hzeroTB
  have hdeTB : de ∈ T_B := Dprin_mem_T_B (by simp) hzeroTB
  have hdv1P : ∃ p, dv1 = .trm [p] :=
    ⟨.db (entry M 1 (transJ1 M) : ℕ∞) BZero, rfl⟩
  have hdeP : ∃ p, de = .trm [p] :=
    ⟨.db (entry M 1 (transJ0 M) : ℕ∞) BZero, rfl⟩
  have hd0' : scb_decomp (addBT (transT2 M) dv1) s0 (flatBT dv1) b0 := by
    simpa [dv1] using hd0
  have hdSub : scb_decomp (addBT (transT2 M) de) s0 (flatBT de) b0 :=
    add_scb_replace_last (transT2 M) dv1 de s0 b0 ht2TB hdv1TB hdv1P
      hdeTB hdeP hd0'
  have hdSub' : scb_decomp
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) s0
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) b0 := by
    simpa [de] using hdSub
  have houter : flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))
      = Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
        flatBT (addBT (transT2 M)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) := by
    simp [Dprin, flatBT, flatBP]
  have hflat : flatBT (Trans (s84x_L M 1)) =
      s1 ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
        (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)]) ++
        [Sym.zero] ++ b0 ++ b1 := by
    rw [hdL1.1]
    rw [houter, hdSub'.1]
    simp [Dprin, BZero, flatBT, flatBP, List.append_assoc]
  have htail : exchV_tail M 1 = 1 := by
    simp [exchV_tail, hadm]
  refine ⟨hPredNp, hLp, ?_⟩
  rw [hjm1, htail]
  simpa [List.append_assoc] using hflat

/-! ## admissible 枝を除去した値残差 -/

/-- `ExchVMValueResidual` のうち non-admissible host だけを要求する狭い残差。 -/
def ExchVMNadmValueResidual : Prop :=
  ∀ (M : PS) (s0 s1 b0 b1 : List Sym), STPS M → monoT M = true →
    transCondV M = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s0 (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b0 →
    scb_decomp (Trans (oper M 1)) s1
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b1 →
    adm M (transJ0 M) = false →
    Trans (Pred (s84x_Np M)) =
        Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) ∧
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) ∧
    flatBT (Trans (s84x_L M 1))
      = s1 ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: (List.replicate (exchV_tail M 1)
                (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (exchV_tail M 1) b0).flatten ++ b1

/-- Isabelle `nf2x_NFall` の原子入力版。non-admissible 枝で仮定するのは
`PredNp` / `Np` / `c₂(L₁)` の3つの slice 値だけで、`Lpv` と `L1v` は含めない。 -/
def ExchVMNadmAtomicResidual : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = false →
    Trans (Pred (s84x_Np M)) =
        Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) ∧
    Trans (s84x_Np M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M)
          (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) ∧
    transC2 (s84x_L M 1) = Dprin (entry M 1 (transJm1 M) : ℕ∞)
        (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (transT2 M)
            (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))))

/-- 停止性主定理へ渡す条件(V)の最小パッケージ。§8.4 の訂正済み右端置換と、
non-admissible の原子3値だけを束ねる。 -/
def ExchVMNadmAtomicPackage : Prop :=
  Rightmost84ReplaceCorrected ∧ ExchVMNadmAtomicResidual

/-- 原子3値から non-admissible の `PredNp` / `Lpv` / `L1v` を復元する。 -/
theorem exchV_nadm_values_of_atomic (hrr : Rightmost84ReplaceCorrected)
    (hatom : ExchVMNadmAtomicResidual) : ExchVMNadmValueResidual := by
  intro M s0 s1 b0 b1 hST hmono hcond hd0 hd1 hnadm
  obtain ⟨hPredNp, hNp, hc2L1⟩ := hatom M hST hmono hcond hnadm
  have hLp := exchV_Lp_of_Np hrr M hST hmono hcond hNp
  have hdL1 := exchV_L1_decomp_of_c2 M s1 b1 hST hmono hcond hd1 hc2L1
  let dv1 := Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero
  let de := Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero
  let ddeep := Dprin (entry M 1 (transJ0 M) : ℕ∞) (addBT (transT2 M) de)
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc1, ht2TB, _hjm1lt⟩ :=
    c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hzeroTB : BZero ∈ T_B := by
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hdv1TB : dv1 ∈ T_B := Dprin_mem_T_B (by simp) hzeroTB
  have hdeTB : de ∈ T_B := Dprin_mem_T_B (by simp) hzeroTB
  have hdv1P : ∃ p, dv1 = .trm [p] :=
    ⟨.db (entry M 1 (transJ1 M) : ℕ∞) BZero, rfl⟩
  have hdeP : ∃ p, de = .trm [p] :=
    ⟨.db (entry M 1 (transJ0 M) : ℕ∞) BZero, rfl⟩
  have hd0' : scb_decomp (addBT (transT2 M) dv1) s0 (flatBT dv1) b0 := by
    simpa [dv1] using hd0
  have hdSub : scb_decomp (addBT (transT2 M) de) s0 (flatBT de) b0 :=
    add_scb_replace_last (transT2 M) dv1 de s0 b0 ht2TB hdv1TB hdv1P
      hdeTB hdeP hd0'
  have hddeepTB : ddeep ∈ T_B :=
    Dprin_mem_T_B (by simp) (addBT_mem_T_B ht2TB hdeTB)
  have hddeepP : ∃ p, ddeep = .trm [p] :=
    ⟨.db (entry M 1 (transJ0 M) : ℕ∞) (addBT (transT2 M) de), rfl⟩
  have hdDeep : scb_decomp (addBT (transT2 M) ddeep) s0 (flatBT ddeep) b0 :=
    add_scb_replace_last (transT2 M) dv1 ddeep s0 b0 ht2TB hdv1TB hdv1P
      hddeepTB hddeepP hd0'
  have hflatDeep : flatBT ddeep =
      Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
        (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)]) ++
        [Sym.zero] ++ b0 := by
    rw [show flatBT ddeep = Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
      flatBT (addBT (transT2 M) de) by simp [ddeep, Dprin, flatBT, flatBP]]
    rw [hdSub.1]
    simp [de, Dprin, BZero, flatBT, flatBP, List.append_assoc]
  have hflat : flatBT (Trans (s84x_L M 1)) =
      s1 ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) ::
        (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)]) ++
        (s0 ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)]) ++
        [Sym.zero] ++ b0 ++ b0 ++ b1 := by
    rw [hdL1.1]
    rw [show flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))))) =
      Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) ::
        flatBT (addBT (transT2 M) ddeep) by simp [ddeep, de, Dprin, flatBT, flatBP]]
    rw [hdDeep.1, hflatDeep]
    simp [List.append_assoc]
  have htail : exchV_tail M 1 = 2 := by
    simp [exchV_tail, hnadm]
  refine ⟨hPredNp, hLp, ?_⟩
  rw [htail]
  simpa [List.append_assoc] using hflat

/-- 訂正済み §8.4 右端置換と non-admissible 値残差から、元の 3 値残差を復元する。 -/
theorem exchVMvalues_of_nadm (hrr : Rightmost84ReplaceCorrected)
    (hnadm : ExchVMNadmValueResidual) : ExchVMValueResidual := by
  intro M s0 s1 b0 b1 hST hmono hcond hd0 hd1
  cases ha : adm M (transJ0 M) with
  | false => exact hnadm M s0 s1 b0 b1 hST hmono hcond hd0 hd1 ha
  | true => exact exchV_values_adm hrr M s0 s1 b0 b1 hST hmono hcond ha hd0 hd1

/-- 訂正済み §8.4 右端置換と non-admissible 原子3値から、元の値残差を復元する。 -/
theorem exchVMvalues_of_nadm_atomic (hrr : Rightmost84ReplaceCorrected)
    (hatom : ExchVMNadmAtomicResidual) : ExchVMValueResidual :=
  exchVMvalues_of_nadm hrr (exchV_nadm_values_of_atomic hrr hatom)

theorem exchVMvalues_of_nadm_package
    (h : ExchVMNadmAtomicPackage) : ExchVMValueResidual :=
  exchVMvalues_of_nadm_atomic h.1 h.2

#print axioms exchV_PredNp_adm
#print axioms exchV_Np_adm
#print axioms exchV_Lp_of_Np
#print axioms exchV_Lp_adm
#print axioms exchV_L1_decomp_of_c2
#print axioms exchV_L1_decomp_adm
#print axioms exchV_values_adm
#print axioms exchV_nadm_values_of_atomic
#print axioms exchVMvalues_of_nadm
#print axioms exchVMvalues_of_nadm_atomic
#print axioms exchVMvalues_of_nadm_package

end PSS
