import «8».«8.1-part4-setup»
import «8».«8.1-part4-mid»
import «8».«8.1-part4-trans»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-RightNodes-Mark»
import «7».«7.3-Mark-rightmost1»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-IncrFirst-Red»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.2-scb-unique»
import «7».«7.2-scb-compose»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»
import «6».«6.6-reduced-leftend»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-P-IdxSum-characterization»
import «6».«6.3-marked-slice»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.2-P-fseq»
import «6».«6.2-P-additivity»
import «5».«5.1-ancestor-tree»

/-!
# §8.1 part (4-2) — back-slice depth-2 `Trans` 形と (4-2) capstone

- 原文: `tmp/content.md` L3021–3036（part (4) の (4-2) 主張）
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `m_8_1_c1_around_part4_TransN_42` (32629) → `c1_around_part4_TransN_42`
  - `m_8_1_c1_around_part4_2`         (32827–33071) → `c1_around_part4_2`
- 依存（wave B-1 の公開定理を消費）:
  `c1_around_part4_setup`（8.1-part4-setup）,
  `c1_around_part4_Nred` / `c1_around_part4_Adm0`（8.1-part4-mid）,
  `c1_around_part4_segpos`（8.1-part4-trans）,
  `Mark_Trans_repr` / `seg_Pred_eq` / `Mark_zero_eq_Trans` /
  `Mark_transJm1_eq_transC2`（7.4-Mark-Trans-repr）,
  `Mark_leftend_form_proper` / `Trans_mono_leftend_form`（7.4-RightNodes-Mark）,
  `Mark_rightmost1_forward`（7.3-Mark-rightmost1）,
  `Marked_Pred` / `principal_flat_properties` / `Dprin_mem_T_B`
  （7.3-Trans-welldefined）, `Trans_Red`（7.3-Trans-IncrFirst-Red）,
  `Trans_preserves_zeroT`（7.3-Trans-preserves-zeroT）,
  `scb_unique_decomp_unconditional`（7.2-scb-unique）,
  `scb_compose_dprin`（7.2-scb-compose）,
  `ancestor_slice_Red_IncrFirst`（6.6）, `nextR_IncrFirstN_ri`（6.5）,
  `admof_slice` / `nextR_seg_adm` / `marked_slice`（6.3）,
  `row0_parent_unique`（6.4）, `parent_eq_of_unique_fseq` /
  `hasParent_iff_unique_fseq` / `hasParent_next_fseq`（6.2）,
  `ancestor_tree_1` / `row0_transitive`（5.1）, `flatBT_injective`（PSS/Flat）。
  Isabelle 側の part1/part2 引用は（4-1 capstone と同様）`Mark_Trans_repr`＋
  `seg_Pred_eq`（`c₁` の切片値）, `Mark_leftend_form_proper`（`c₁` の単項性）,
  `marked_slice`（切片 Marked）で私的に再導出する（part1/part2 の主張全体は不要）。
- 方針: TransN_42 は 8.1-part4-trans の `part4_TransN_engine_pt`（4-1 エンジン）と
  同型の私的エンジンで、条件 (I)/(III)/(V)/(VI) を全て否定して `transC2Core` の
  最終分岐（深さ 2 頭）へ落とす。`t₂ = 0` の枝は `addBT 0 x = x` で同形に吸収
  （Isabelle の `m_8_2_t2ne_notAVI` は不要）。capstone は Isabelle
  `m_8_1_c1_around_part4_2` の深さ 2 splice: 内層（`t₄`）と外層（`t₃`）の
  末尾整列を `scb_compose_dprin` で 2 段持ち上げ、共通 scb 位置
  （`c1_around_part4_segpos`）＋`scb_unique_decomp_unconditional`＋
  `flatBT_injective` で葉 `D_{M_{1,j₀}}0` を `c₁` に貼り替える。
- 私的補助（接尾辞 `_p2`）: `Dprin_trm_p2` / `flatBT_singleton_p2` /
  `flatBT_Dprin_p2`（flatten 変形）, `flatBPTail_append_singleton_p2`＋
  `addBT_principal_split_p2`（Isabelle `addBT_trailing_align`）,
  `addBT_zero_left_p2`, `addBT_right_cancel_p2`＋`addBT_snoc_inj_p2`＋
  `ex1_Dprin_addBT_two_p2`（Isabelle `ex1_Dpt_addBT_two`）,
  `IncrFirstN` 転送束（8.1-part4-trans の private 複製）,
  `part4_TransN42_engine_p2`（深さ 2 エンジン）。
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## 私的補助: flatten 変形 -/

private theorem Dprin_trm_p2 (v : ℕ∞) (a : BT) :
    Dprin v a = .trm [.db v a] := rfl

private theorem flatBT_singleton_p2 (p : BP) :
    flatBT (.trm [p]) = flatBP p := by
  simp [flatBT]

private theorem flatBT_Dprin_p2 (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = .dsym v :: flatBT a := by
  simp [Dprin, flatBT, flatBP]

/-! ## 私的補助: 末尾整列（Isabelle `addBT_trailing_align`, layerB 31857） -/

private theorem flatBPTail_append_singleton_p2 (xs : List BP) (p : BP) :
    flatBPTail (xs ++ [p]) = flatBPTail xs ++ (.cm :: flatBP p) := by
  induction xs with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

private theorem addBT_principal_split_p2 (t : BT) :
    ∃ pre post : List Sym,
      (∀ x ∈ post, x = .rp) ∧
      ∀ p : BP,
        flatBT (addBT t (.trm [p])) = pre ++ flatBP p ++ post := by
  rcases t with ⟨xs⟩
  cases xs with
  | nil =>
      exact ⟨[], [], by simp, by intro p; simp [addBT, flatBT]⟩
  | cons q qs =>
      refine ⟨.lp :: (flatBP q ++ flatBPTail qs) ++ [.cm], [.rp], by simp, ?_⟩
      intro p
      cases qs with
      | nil => simp [addBT, flatBT, flatBPTail]
      | cons r rs =>
          change
            (.lp :: (flatBP q ++ flatBPTail ((r :: rs) ++ [p])) ++ [.rp]) =
              (.lp :: (flatBP q ++ flatBPTail (r :: rs)) ++ [.cm]) ++
                flatBP p ++ [.rp]
          rw [flatBPTail_append_singleton_p2]
          simp [List.append_assoc]

/-! ## 私的補助: `addBT` の左零元と一意性の包装
（Isabelle `ex1_Dpt_addBT_two`, layerB 18772） -/

private theorem addBT_zero_left_p2 (x : BT) : addBT BZero x = x := by
  rcases x with ⟨xs⟩
  simp [addBT, BZero]

private theorem addBT_right_cancel_p2 {a b c : BT}
    (h : addBT a c = addBT b c) : a = b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp only [addBT, BT.trm.injEq] at h
  exact congrArg BT.trm (List.append_cancel_right h)

private theorem addBT_snoc_inj_p2 {t t' : BT} {q q' : BP}
    (h : addBT t (.trm [q]) = addBT t' (.trm [q'])) : t = t' ∧ q = q' := by
  rcases t with ⟨as⟩
  rcases t' with ⟨bs⟩
  simp only [addBT, BT.trm.injEq] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  refine ⟨congrArg BT.trm h1, ?_⟩
  simpa using h2

private theorem ex1_Dprin_addBT_two_p2 {X c : BT} (v w : ℕ∞) (t₃ t₄ : BT)
    (h : X = Dprin v (addBT t₃ (Dprin w (addBT t₄ c)))) :
    ∃! t34 : BT × BT,
      X = Dprin v (addBT t34.1 (Dprin w (addBT t34.2 c))) := by
  refine ⟨(t₃, t₄), h, ?_⟩
  rintro ⟨a, b⟩ hab
  have hab' : X = Dprin v (addBT a (Dprin w (addBT b c))) := hab
  have heq : Dprin v (addBT a (Dprin w (addBT b c)))
      = Dprin v (addBT t₃ (Dprin w (addBT t₄ c))) := hab'.symm.trans h
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true,
    true_and] at heq
  obtain ⟨h3, hq⟩ := addBT_snoc_inj_p2 heq
  have h4 : addBT b c = addBT t₄ c := by
    simpa using hq
  have hb4 : b = t₄ := addBT_right_cancel_p2 h4
  simp only [Prod.mk.injEq]
  exact ⟨h3, hb4⟩

/-! ## 私的補題層: `IncrFirstN` 転送（8.1-part4-trans の private 複製） -/

private theorem Lng_IncrFirstN_p2 (n : ℕ) (X : PS) :
    Lng (IncrFirstN n X) = Lng X := by
  rw [IncrFirstN_eq_map]
  simp

private theorem entry_IncrFirstN_one_p2 (n : ℕ) (X : PS) (j : ℕ)
    (hj : j < Lng X) :
    entry (IncrFirstN n X) 1 j = entry X 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

private theorem adm_IncrFirstN_p2 (n : ℕ) (X : PS) (j : ℕ) :
    adm (IncrFirstN n X) j = adm X j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem Adm_IncrFirstN_p2 (n : ℕ) (X : PS) (j : ℕ) :
    Adm (IncrFirstN n X) j = Adm X j := by
  have hfun : (fun j' => adm (IncrFirstN n X) j') = (fun j' => adm X j') :=
    funext (fun j' => adm_IncrFirstN_p2 n X j')
  unfold Adm
  rw [adm_IncrFirstN_p2 n X j, hfun]

private theorem parents_IncrFirstN_p2 (n : ℕ) (X : PS) (i j : ℕ) :
    parents (IncrFirstN n X) i j = parents X i j := by
  simp only [parents, Lng_IncrFirstN_p2, nextR_IncrFirstN_ri]

private theorem parent_IncrFirstN_p2 (n : ℕ) (X : PS) (i j : ℕ) :
    parent (IncrFirstN n X) i j = parent X i j := by
  simp only [parent, parents_IncrFirstN_p2]

private theorem hasParent_IncrFirstN_p2 (n : ℕ) (X : PS) (i j : ℕ) :
    hasParent (IncrFirstN n X) i j = hasParent X i j := by
  simp only [hasParent, parents_IncrFirstN_p2]

private theorem adm_zero_p2 (M : PS) : adm M 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

/-! ## 私的エンジン: part (4-2) back-slice の深さ 2 `Trans` 形

`a < p`, `p + 1 < b`, `a = Adm M p`, `M_{1,b} ≤ M_{1,p}` の設定で
`Trans ((M_j)_{j=a}^{b}) = D_{M_{1,a}}(t₃ + D_{M_{1,p}}(t₄ + D_{M_{1,b}} 0))`。
8.1-part4-trans の 4-1 エンジンと同じ `Red` 切片転送を使い、条件
(I)/(III)/(V)/(VI) を全て否定して `transC2Core` の最終分岐（深さ 2 頭）に
落とす。`transT2 = 0` の枝は `addBT 0 x = x` で同じ形に吸収する。 -/

private theorem part4_TransN42_engine_p2 (M : PS) (a b p : ℕ)
    (hR : RTPS M) (hbL : b ≤ Lng M - 1)
    (hanc : leR M 0 a b = true)
    (hpar : nextR M 0 p b = true)
    (hap : a < p) (hgap : p + 1 < b)
    (hAdmp : Adm M p = a)
    (hguard : entry M 1 b ≤ entry M 1 p) :
    ∃ t₃ t₄, Trans (seg M a b)
      = Dprin (entry M 1 a : ℕ∞)
          (addBT t₃ (Dprin (entry M 1 p : ℕ∞)
            (addBT t₄ (Dprin (entry M 1 b : ℕ∞) BZero)))) := by
  have hM : TPS M := RTPS_TPS M hR
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hpb : p < b := by omega
  have hab : a < b := by omega
  have hbLM : b < Lng M := by omega
  have hLN : Lng (seg M a b) = b + 1 - a := length_seg M a b
  have hNT : TPS (seg M a b) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg M a b)
    simp only [length_seg]
    omega
  -- 簡約プロキシ `R = Red (seg M a b)`
  have hfacts := ancestor_slice_Red_IncrFirst M a b hR hab hbL hanc
  have hRedR : Red (Red (seg M a b)) = Red (seg M a b) := hfacts.1
  have hmonoR : monoT (Red (seg M a b)) = true := hfacts.2.1
  have hIF : seg M a b
      = IncrFirstN (entry M 0 a - entry M 1 a) (Red (seg M a b)) := hfacts.2.2
  have hLR : Lng (Red (seg M a b)) = Lng (seg M a b) :=
    Lng_Red_invariance (seg M a b) hNT
  have hLRval : Lng (Red (seg M a b)) = b + 1 - a := by rw [hLR, hLN]
  have hRT : TPS (Red (seg M a b)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (Red (seg M a b))
    omega
  have hRRT : RTPS (Red (seg M a b)) := by
    show reduced (Red (seg M a b)) = true
    have hne : Red (seg M a b) ≠ [] := hRT
    simp [reduced, hne, hRedR]
  have hIdx : lastIdx (Red (seg M a b)) = b - a := by
    show Lng (Red (seg M a b)) - 1 = b - a
    omega
  -- 親の転送: `parent R 0 (b-a) = p-a`
  have hnextN : nextR (seg M a b) 0 (p - a) (b - a) = true := by
    have h := nextR_seg_adm M a b 0 (p - a) (b - a) (by omega) hbLM
      (by simp only [length_seg]; omega) (by simp only [length_seg]; omega)
    rw [h]
    have e1 : a + (p - a) = p := by omega
    have e2 : a + (b - a) = b := by omega
    rw [e1, e2]
    exact hpar
  have huniqN : ∀ y, nextR (seg M a b) 0 y (b - a) = true → y = p - a := by
    intro y hy
    have hyL : y < Lng (seg M a b) := by
      have hh : nextrel0 (seg M a b) y (b - a) = true := by
        simpa [nextR] using hy
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.1.1.1.1
    have h := nextR_seg_adm M a b 0 y (b - a) (by omega) hbLM hyL
      (by simp only [length_seg]; omega)
    rw [h] at hy
    have e2 : a + (b - a) = b := by omega
    rw [e2] at hy
    have := row0_parent_unique M (a + y) p b hy hpar
    omega
  have hparN : parent (seg M a b) 0 (b - a) = p - a :=
    parent_eq_of_unique_fseq (seg M a b) 0 (b - a) (p - a) hnextN huniqN
  have hparR : parent (Red (seg M a b)) 0 (b - a) = p - a := by
    rw [hIF, parent_IncrFirstN_p2] at hparN
    exact hparN
  have hPar : lastParent (Red (seg M a b)) = p - a := by
    show parent (Red (seg M a b)) 0 (lastIdx (Red (seg M a b))) = p - a
    rw [hIdx]
    exact hparR
  -- `transJm1 R = 0`
  have hAdmN : Adm (seg M a b) (p - a) = 0 := by
    have h := admof_slice M a p b hM (by omega) hpb hbL
    rw [hAdmp] at h
    simpa using h
  have hAdmR : Adm (Red (seg M a b)) (p - a) = 0 := by
    rw [hIF, Adm_IncrFirstN_p2] at hAdmN
    exact hAdmN
  have hJm1 : transJm1 (Red (seg M a b)) = 0 := by
    simp only [transJm1, transJ0]
    rw [hPar]
    exact hAdmR
  -- 行 1 entry の転送
  have hE1 : ∀ x, x < b + 1 - a →
      entry (Red (seg M a b)) 1 x = entry M 1 (a + x) := by
    intro x hx
    have h1 : entry (seg M a b) 1 x = entry (Red (seg M a b)) 1 x := by
      conv_lhs => rw [hIF]
      exact entry_IncrFirstN_one_p2 (entry M 0 a - entry M 1 a)
        (Red (seg M a b)) x (by omega)
    have h2 : entry (seg M a b) 1 x = entry M 1 (a + x) :=
      entry_seg M a b 1 x (by simp only [length_seg]; omega)
    rw [← h1, h2]
  have hE0 : entry (Red (seg M a b)) 1 0 = entry M 1 a := by
    have h := hE1 0 (by omega)
    simpa using h
  have hEb : entry (Red (seg M a b)) 1 (b - a) = entry M 1 b := by
    have h := hE1 (b - a) (by omega)
    have e2 : a + (b - a) = b := by omega
    rw [e2] at h
    exact h
  have hEp : entry (Red (seg M a b)) 1 (p - a) = entry M 1 p := by
    have h := hE1 (p - a) (by omega)
    have e1 : a + (p - a) = p := by omega
    rw [e1] at h
    exact h
  -- 行 0 の親は非 `R` 許容（`Adm R (p-a) = 0 ≠ p-a`）
  have hadmF : adm (Red (seg M a b)) (p - a) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have hAv : Adm (Red (seg M a b)) (p - a) = p - a := by
      simp [Adm, h]
    rw [hAdmR] at hAv
    omega
  -- 条件 (I)/(III)/(V)/(VI) の全否定
  have hnotI : transCondI (Red (seg M a b)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at h
    have h2 := h.2
    rw [hPar, hadmF] at h2
    simp at h2
  have hnotIII : transCondIII (Red (seg M a b)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h
    have h2 := h.2
    rw [hPar, hadmF] at h2
    simp at h2
  have hnotV : transCondV (Red (seg M a b)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [transCondV, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rw [hIdx, hPar, hEb, hEp] at h
    omega
  have hnotVI : transCondVI (Red (seg M a b)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [transCondVI, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rw [hIdx, hPar, hEb, hEp] at h
    omega
  have hnA : ¬((transCondI (Red (seg M a b)) || transCondIII (Red (seg M a b))
      || transCondV (Red (seg M a b))) = true) := by
    rw [hnotI, hnotIII, hnotV]
    simp
  have hnVI : ¬(transCondVI (Red (seg M a b)) = true) := by
    rw [hnotVI]
    simp
  -- `transC2Core` の最終分岐（深さ 2 頭）
  have hcore : ∀ (v : ℕ∞) (t₂ : BT), ∃ t₃ t₄,
      transC2Core (Red (seg M a b)) v t₂
        = Dprin v (addBT t₃
            (Dprin (entry (Red (seg M a b)) 1
                (lastParent (Red (seg M a b))) : ℕ∞)
              (addBT t₄
                (Dprin (entry (Red (seg M a b)) 1
                    (lastIdx (Red (seg M a b))) : ℕ∞) BZero)))) := by
    intro v t₂
    by_cases ht2 : (t₂ == BZero) = true
    · refine ⟨BZero, BZero, ?_⟩
      simp only [transC2Core]
      rw [if_neg hnA, if_neg hnVI, if_pos ht2,
        addBT_zero_left_p2, addBT_zero_left_p2]
    · simp only [transC2Core]
      rw [if_neg hnA, if_neg hnVI, if_neg ht2]
      exact ⟨_, _, rfl⟩
  -- 値化: `Trans (seg M a b) = Trans R = transC2 R`
  have hleR00 : leR (Red (seg M a b)) 0 0 (Lng (Red (seg M a b)) - 1) = true := by
    have hh := hmonoR
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hMk0 : Marked (Red (seg M a b)) 0 := ⟨hRT, adm_zero_p2 _, hleR00⟩
  have hLR1 : 1 < Lng (Red (seg M a b)) := by omega
  have hPredR : RTPS (Pred (Red (seg M a b))) :=
    RTPS_Pred (Red (seg M a b)) hRRT
  have hLPred : Lng (Pred (Red (seg M a b))) = Lng (Red (seg M a b)) - 1 :=
    length_Pred (Red (seg M a b)) hLR1
  have hPredT : TPS (Pred (Red (seg M a b))) := RTPS_TPS _ hPredR
  have hzPred : zeroT (Pred (Red (seg M a b))) = false := by
    have hne : Lng (Pred (Red (seg M a b))) ≠ 1 := by omega
    simp [zeroT, hne]
  have ht1 : Trans (Pred (Red (seg M a b))) ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT (Pred (Red (seg M a b))) hPredT).mpr h0
    rw [hzPred] at hz
    simp at hz
  have hTransSeg : Trans (seg M a b) = Trans (Red (seg M a b)) :=
    Trans_Red (seg M a b) hNT
  have hMz : Mark (Red (seg M a b)) 0 = Trans (Red (seg M a b)) :=
    Mark_zero_eq_Trans (Red (seg M a b)) hRRT hMk0
  have hMc2 : Mark (Red (seg M a b)) (transJm1 (Red (seg M a b)))
      = transC2 (Red (seg M a b)) :=
    Mark_transJm1_eq_transC2 (Red (seg M a b)) hRRT hmonoR hLR1 ht1
  rw [hJm1] at hMc2
  have hTc2 : Trans (Red (seg M a b)) = transC2 (Red (seg M a b)) := by
    rw [← hMz, hMc2]
  -- `transV R = M_{1,a}`
  have hMkP0 : Marked (Pred (Red (seg M a b))) 0 :=
    Marked_Pred (Red (seg M a b)) 0 hRT hLR1 hMk0 (by omega)
  have hmonoP : monoT (Pred (Red (seg M a b))) = true := by
    simp [monoT, hzPred, hMkP0.2.2]
  have hMzP : Mark (Pred (Red (seg M a b))) 0
      = Trans (Pred (Red (seg M a b))) :=
    Mark_zero_eq_Trans (Pred (Red (seg M a b))) hPredR hMkP0
  obtain ⟨t, ht⟩ : ∃ t, Trans (Pred (Red (seg M a b)))
      = Dprin (entry (Pred (Red (seg M a b))) 1 0 : ℕ∞) t := by
    rcases Trans_mono_leftend_form (Pred (Red (seg M a b))) hPredR hmonoP with
      h0 | h
    · exact absurd h0 ht1
    · exact h
  have hEPred : entry (Pred (Red (seg M a b))) 1 0
      = entry (Red (seg M a b)) 1 0 :=
    entry_Pred (Red (seg M a b)) 1 0 (by omega)
  have hV : transV (Red (seg M a b)) = (entry M 1 a : ℕ∞) := by
    show bpHeadV (transC1 (Red (seg M a b))) = (entry M 1 a : ℕ∞)
    have hc1 : transC1 (Red (seg M a b)) = Trans (Pred (Red (seg M a b))) := by
      show Mark (Pred (Red (seg M a b))) (transJm1 (Red (seg M a b)))
          = Trans (Pred (Red (seg M a b)))
      rw [hJm1]
      exact hMzP
    rw [hc1, ht, hEPred, hE0]
    simp [bpHeadV, Dprin]
  -- 組み立て
  obtain ⟨t₃, t₄, hsh⟩ :=
    hcore (transV (Red (seg M a b))) (transT2 (Red (seg M a b)))
  have hsh2 : transC2 (Red (seg M a b))
      = Dprin (transV (Red (seg M a b)))
          (addBT t₃
            (Dprin (entry (Red (seg M a b)) 1
                (lastParent (Red (seg M a b))) : ℕ∞)
              (addBT t₄
                (Dprin (entry (Red (seg M a b)) 1
                    (lastIdx (Red (seg M a b))) : ℕ∞) BZero)))) := hsh
  rw [hPar, hIdx, hEp, hEb, hV] at hsh2
  refine ⟨t₃, t₄, ?_⟩
  rw [hTransSeg, hTc2, hsh2]

/-! ## 公開定理 1/2: part (4-2) back-slice の深さ 2 `Trans` 形
（Isabelle `m_8_1_c1_around_part4_TransN_42`, layerB 32629） -/

/-- part (4-2) back-slice: (4-2) ガード `j′₋₁ < j′₀ ∧ M_{1,j′₀} ≥ M_{1,j₀}` の下で
`∃ t₃ t₄, Trans((M_j)_{j=j′₋₁}^{j₀})
  = D_{M_{1,j′₋₁}}(t₃ + D_{M_{1,j′₀}}(t₄ + D_{M_{1,j₀}} 0))`。 -/
theorem c1_around_part4_TransN_42 (M : PS) (j₀' : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M)
    (hguard : Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀') :
    ∃ t₃ t₄, Trans (seg M (Adm M j₀') (transJ0 M))
      = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
          (addBT t₃ (Dprin (entry M 1 j₀' : ℕ∞)
            (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))) := by
  obtain ⟨hanc, _, _, _, _, _⟩ :=
    c1_around_part4_Nred M j₀' hR hmono hadm hj1 np
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hlen : 1 < Lng M := by omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    rw [htJ0]
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp
  exact part4_TransN42_engine_p2 M (Adm M j₀') (transJ0 M) j₀' hR
    (by omega) hanc np hguard.1 hadj rfl hguard.2

#print axioms c1_around_part4_TransN_42

/-! ## 公開定理 2/2: part (4-2) capstone
（Isabelle `m_8_1_c1_around_part4_2`, layerB 32827）

(4-2) ガードの下で、一意な `(t′₃, t′₄)` が存在して
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}}(t′₃ + D_{M_{1,j′₀}}(t′₄ + c₁))`。

経路: back-slice 表示 `Mark (Pred M) j′₋₁ = Trans((M_j)_{j=j′₋₁}^{j₁-1})`
（`Mark_Trans_repr`＋`seg_Pred_eq`）、TransN_42 の深さ 2 頭
`Trans((M_j)_{j=j′₋₁}^{j₀}) = D_{M_{1,j′₋₁}}(t₃ + D_{M_{1,j′₀}}(t₄ + D_{M_{1,j₀}}0))`、
segpos の共通 scb 位置で葉 `D_{M_{1,j₀}}0` を `c₁` に貼り替える（interior 枝、
整列は内層 `t₄`・外層 `t₃` の 2 段）。`j₀ = j₁ - 1` の boundary 枝では
`c₁` 自身が右端値 `D_{M_{1,j₀}}0`。一意性は `ex1_Dprin_addBT_two_p2`。 -/

theorem c1_around_part4_2 (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M)
    (hguard : Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀') :
    ∃! t34 : BT × BT, Mark (Pred M) (Adm M j₀')
      = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
          (addBT t34.1 (Dprin (entry M 1 j₀' : ℕ∞)
            (addBT t34.2 (transC1 M)))) := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_hjm1, hc1, _haLe, hj0'lt, hj0j1, hj1L, haj0, hj0ub, hpredA, hpredJ0⟩ :=
    c1_around_part4_setup M j₀' hR hmono hadm hj1 hge np
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLP : Lng (Pred M) - 1 = transJ1 M - 1 := by omega
  -- back-slice 表示: `Mark (Pred M) j′₋₁ = Trans((M_j)_{j=j′₋₁}^{j₁-1})`
  have hlt : Adm M j₀' < Lng (Pred M) - 1 := by omega
  have hrepr : Mark (Pred M) (Adm M j₀') =
      Trans (seg (Pred M) (Adm M j₀') (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (Adm M j₀') hpredA hpredR hlt
  have hsegeq : seg (Pred M) (Adm M j₀') (transJ1 M - 1) =
      seg M (Adm M j₀') (transJ1 M - 1) :=
    seg_Pred_eq M (Adm M j₀') (transJ1 M - 1) hlen (by omega) (by omega)
  have hreprM : Mark (Pred M) (Adm M j₀') =
      Trans (seg M (Adm M j₀') (transJ1 M - 1)) := by
    rw [hrepr, hLP, hsegeq]
  -- TransN_42: 深さ 2 頭と末尾葉 `D_{M_{1,j₀}} 0`
  obtain ⟨t₃, t₄, ht42⟩ :=
    c1_around_part4_TransN_42 M j₀' hR hmono hadm hj1 np hadj hguard
  -- Nred: back-slice 祖先 `leR M 0 j′₋₁ j₀`
  obtain ⟨hleMaj0, _, _, _, _, _⟩ :=
    c1_around_part4_Nred M j₀' hR hmono hadm hj1 np
  -- `j₀` の最終列への行 0 祖先性
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    rw [htJ0]
    exact hasParent_next_fseq M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M _ _ hnpar
  -- 切片の貼り替え:
  -- `∃ t₃' t₄', Trans((M_j)_{j=j′₋₁}^{j₁-1})
  --    = D_{M_{1,j′₋₁}}(t₃' + D_{M_{1,j′₀}}(t₄' + c₁))`
  have hslice : ∃ t₃' t₄', Trans (seg M (Adm M j₀') (transJ1 M - 1)) =
      Dprin (entry M 1 (Adm M j₀') : ℕ∞)
        (addBT t₃' (Dprin (entry M 1 j₀' : ℕ∞)
          (addBT t₄' (transC1 M)))) := by
    by_cases hjlt : transJ0 M < transJ1 M - 1
    · -- interior 枝: `j₀ < j₁ - 1`
      have hlt0 : transJ0 M < Lng (Pred M) - 1 := by omega
      -- `c₁` の切片値（Isabelle part1 第 3 主張の私的再導出）
      have hreprJ0 : Mark (Pred M) (transJ0 M) =
          Trans (seg (Pred M) (transJ0 M) (Lng (Pred M) - 1)) :=
        Mark_Trans_repr (Pred M) (transJ0 M) hpredJ0 hpredR hlt0
      have hsegeqJ0 : seg (Pred M) (transJ0 M) (transJ1 M - 1) =
          seg M (transJ0 M) (transJ1 M - 1) :=
        seg_Pred_eq M (transJ0 M) (transJ1 M - 1) hlen (by omega) (by omega)
      have hc1part1 : Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M := by
        rw [hc1, hreprJ0, hLP, hsegeqJ0]
      -- `c₁` の単項性（Isabelle part1 第 5 主張の私的再導出）
      obtain ⟨tc, htc⟩ :=
        Mark_leftend_form_proper (Pred M) (transJ0 M) hpredJ0 hpredR hlt0
      have hc1P : transC1 M =
          Dprin (entry (Pred M) 1 (transJ0 M) : ℕ∞) tc := by
        rw [hc1, htc]
      -- 切片 Marked（Isabelle part2 第 3 主張の私的再導出）
      have hmarkedJ0M : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
      have hSmMk : Marked (seg M (Adm M j₀') (transJ1 M - 1))
          (transJ0 M - Adm M j₀') :=
        marked_slice M (transJ0 M) (Adm M j₀') (transJ1 M - 1) hmarkedJ0M
          (by omega) (by omega) (by omega)
      -- 祖先連鎖
      have hlej0j1m1 : leR M 0 (transJ0 M) (transJ1 M - 1) = true :=
        ancestor_tree_1 M (transJ0 M) (transJ1 M - 1) (Lng M - 1) hM hleJ0
          (by omega) (by omega)
      have hleMaj1m1 : leR M 0 (Adm M j₀') (transJ1 M - 1) = true :=
        row0_transitive M _ _ _ hM hleMaj0 hlej0j1m1
      -- 共通 scb 位置
      obtain ⟨s, b, P1, P2⟩ := c1_around_part4_segpos M (Adm M j₀')
        (transJ0 M) (transJ1 M) (transC1 M) hR hmono haj0 hjlt hj1L hj1
        hleMaj0 hleMaj1m1 hSmMk hc1part1
      -- 末尾整列: 内層 `t₄` と外層 `t₃` の共通 `pre`/`post`
      obtain ⟨pre1, post1, hpost1, hflat1⟩ := addBT_principal_split_p2 t₄
      obtain ⟨pre2, post2, hpost2, hflat2⟩ := addBT_principal_split_p2 t₃
      -- 葉は principal 文字列
      have hiptc : isPTB_str
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) :=
        (principal_flat_properties
          (Dprin_mem_T_B (by simp)
            (by simp [T_B, BZero, dfree_BT, dfree_BPList]))
          ⟨_, rfl⟩).1
      -- 葉位置の scb 分解を 2 段持ち上げ（内層 → `D_{M_{1,j′₀}}` → 外層 → `D_{M_{1,j′₋₁}}`）
      have hal1lf : flatBT (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) =
          pre1 ++ flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero) ++ post1 := by
        rw [Dprin_trm_p2, flatBT_singleton_p2]
        exact hflat1 _
      have hd1 : scb_decomp
          (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) pre1
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) post1 :=
        ⟨hal1lf, fun _ => hiptc, hpost1⟩
      have hd2 := scb_compose_dprin (entry M 1 j₀' : ℕ∞) _ pre1 _ post1 hd1 hiptc
      have hal2 : flatBT (addBT t₃ (Dprin (entry M 1 j₀' : ℕ∞)
          (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))) =
          pre2 ++ flatBT (Dprin (entry M 1 j₀' : ℕ∞)
            (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))) ++ post2 := by
        rw [Dprin_trm_p2, flatBT_singleton_p2]
        exact hflat2 _
      have hd3 : scb_decomp (addBT t₃ (Dprin (entry M 1 j₀' : ℕ∞)
          (addBT t₄ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))))
          (pre2 ++ .dsym (entry M 1 j₀' : ℕ∞) :: pre1)
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))
          (post1 ++ post2) := by
        refine ⟨?_, fun _ => hiptc, ?_⟩
        · rw [hal2, hd2.1]
          simp [List.append_assoc]
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hpost1 x h
          · exact hpost2 x h
      have hd4 := scb_compose_dprin (entry M 1 (Adm M j₀') : ℕ∞) _ _ _ _ hd3 hiptc
      have hDleaf : scb_decomp (Trans (seg M (Adm M j₀') (transJ0 M)))
          (.dsym (entry M 1 (Adm M j₀') : ℕ∞) ::
            (pre2 ++ .dsym (entry M 1 j₀' : ℕ∞) :: pre1))
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))
          (post1 ++ post2) := by
        rw [ht42]
        exact hd4
      obtain ⟨hs, hb⟩ :=
        scb_unique_decomp_unconditional _ _ _ _ _ _ P1 hDleaf
      -- 長い切片の flatten を共通位置で読み出す
      have hflatlong : flatBT (Trans (seg M (Adm M j₀') (transJ1 M - 1))) =
          (.dsym (entry M 1 (Adm M j₀') : ℕ∞) ::
            (pre2 ++ .dsym (entry M 1 j₀' : ℕ∞) :: pre1)) ++
            flatBT (transC1 M) ++ (post1 ++ post2) := by
        have hP2 := P2.1
        rw [hs, hb] at hP2
        exact hP2
      -- 貼り替え先の flatten
      have hal1c1 : flatBT (addBT t₄ (transC1 M)) =
          pre1 ++ flatBT (transC1 M) ++ post1 := by
        rw [hc1P, Dprin_trm_p2, flatBT_singleton_p2]
        exact hflat1 _
      have hal2c1 : flatBT (addBT t₃ (Dprin (entry M 1 j₀' : ℕ∞)
          (addBT t₄ (transC1 M)))) =
          pre2 ++ flatBT (Dprin (entry M 1 j₀' : ℕ∞)
            (addBT t₄ (transC1 M))) ++ post2 := by
        rw [Dprin_trm_p2, flatBT_singleton_p2]
        exact hflat2 _
      have hflatnew : flatBT (Dprin (entry M 1 (Adm M j₀') : ℕ∞)
          (addBT t₃ (Dprin (entry M 1 j₀' : ℕ∞)
            (addBT t₄ (transC1 M))))) =
          (.dsym (entry M 1 (Adm M j₀') : ℕ∞) ::
            (pre2 ++ .dsym (entry M 1 j₀' : ℕ∞) :: pre1)) ++
            flatBT (transC1 M) ++ (post1 ++ post2) := by
        rw [flatBT_Dprin_p2, hal2c1, flatBT_Dprin_p2, hal1c1]
        simp [List.append_assoc]
      refine ⟨t₃, t₄, ?_⟩
      apply flatBT_injective
      rw [hflatlong, hflatnew]
    · -- boundary 枝: `j₀ = j₁ - 1`、`c₁` は右端値 `D_{M_{1,j₀}} 0`
      have hjeq : transJ0 M = transJ1 M - 1 := by omega
      have hj0Pm1 : transJ0 M = Lng (Pred M) - 1 := by omega
      have hnzP : zeroT (Pred M) = false := by
        cases hzq : zeroT (Pred M) with
        | false => rfl
        | true =>
            exfalso
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzq
            omega
      have hmarkrm : Mark (Pred M) (Lng (Pred M) - 1) =
          Dprin (entry (Pred M) 1 (Lng (Pred M) - 1) : ℕ∞) BZero :=
        Mark_rightmost1_forward (Pred M) hpredR hnzP
      have he1P : entry (Pred M) 1 (transJ0 M) = entry M 1 (transJ0 M) := by
        rw [Pred_eq_take M hlen]
        exact entry_take M (Lng M - 1) 1 (transJ0 M) (by omega)
      have hc1leaf : transC1 M =
          Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := by
        rw [hc1, hj0Pm1, hmarkrm, ← hj0Pm1, he1P]
      refine ⟨t₃, t₄, ?_⟩
      have hsegB : seg M (Adm M j₀') (transJ1 M - 1) =
          seg M (Adm M j₀') (transJ0 M) := by
        rw [hjeq]
      rw [hsegB, ht42, hc1leaf]
  -- 組み立て: 表示＋貼り替え → 一意存在
  obtain ⟨t₃', t₄', ht'⟩ := hslice
  have hMark : Mark (Pred M) (Adm M j₀') =
      Dprin (entry M 1 (Adm M j₀') : ℕ∞)
        (addBT t₃' (Dprin (entry M 1 j₀' : ℕ∞)
          (addBT t₄' (transC1 M)))) := by
    rw [hreprM, ht']
  exact ex1_Dprin_addBT_two_p2 _ _ t₃' t₄' hMark

#print axioms c1_around_part4_2

end PSS
