import «5».«5.1-ancestor-tree»
import «6».«6.2-P-fseq»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-P-IdxSum-characterization»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-preserves-marked»
import «6».«6.5-Red-Pred-commute»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-reduced-leftend»
import «6».«6.6-reduced-coeff»
import «7».«7.3-Trans-IncrFirst-Red»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Trans-welldefined»
import «7».«7.4-Trans-Mark-seg»
import «7».«7.4-RightNodes-Mark»

/-!
# §8.1 part (4) — back-slice `Trans` shape (4-1) and the common scb position

- 原文: `tmp/content.md` L2933 付近（part (4) の前剥がし層）。
- Isabelle: `m_8_1_c1_around_part4_TransN_41`（`isabelle/layerB/pss_wip.thy:31445`）,
  `m_8_1_c1_around_part4_segpos`（同 :31903）。
- 公開定理: `c1_around_part4_TransN_41`, `c1_around_part4_segpos`。
- 依存: `ancestor_slice_Red_IncrFirst`（6.6）, `Red_preserves_marked`（6.5）,
  `Trans_Red`/`Trans_IncrFirst`（7.3）, `Trans_Mark_seg_exists`/`Mark_Trans_repr`/
  `Mark_zero_eq_Trans`/`Mark_transJm1_eq_transC2`（7.4）, `Trans_mono_leftend_form`（7.4）,
  `admof_slice`/`nextR_seg_adm`（6.3）, `row0_parent_unique`/`parent_eq_of_unique_fseq`（6.4/6.2）,
  `RedCondA_apply`/`RTPS_mono_head_eq`/`reduced_coeff`（6.5/6.6）,
  `nextR_IncrFirstN_ri`（6.5）。
- 方針: Isabelle の `repr_*` 束（TransAux 手展開）は不要。`IncrFirstN` が
  `nextR`/`adm`/`Adm`/`parent`/行 1 entry を変えないこと（関数レベル
  `nextR_IncrFirstN_ri`）と `Trans N = Mark N 0 = Mark N (transJm1 N) = transC2 N`
  （7.4 公開補題）で `Red` 切片へ直接転送する（part (3-1) 移植の勝ち筋、
  `lean/memo.md` §4.6）。
- 状態: ✅ sorry 0（本ファイル単独で green）。統計的監査:
  `python/audit_81_part4_trans.py`（canonical model、TransN_41 445 例・
  segpos 1411 例、反例 0）。
-/

namespace PSS

/-! ## 私的補題層（suffix `_pt`）: `IncrFirstN`・切片の転送 -/

private theorem Lng_IncrFirstN_pt (n : ℕ) (X : PS) :
    Lng (IncrFirstN n X) = Lng X := by
  rw [IncrFirstN_eq_map]
  simp

private theorem TPS_IncrFirstN_pt (n : ℕ) (X : PS) (hX : TPS X) :
    TPS (IncrFirstN n X) := by
  have h0 : 0 < Lng (IncrFirstN n X) := by
    rw [Lng_IncrFirstN_pt n X]
    exact List.length_pos_of_ne_nil hX
  exact List.ne_nil_of_length_pos h0

private theorem entry_IncrFirstN_one_pt (n : ℕ) (X : PS) (j : ℕ)
    (hj : j < Lng X) :
    entry (IncrFirstN n X) 1 j = entry X 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

private theorem entry_IncrFirstN_zero_pt (n : ℕ) (X : PS) (j : ℕ)
    (hj : j < Lng X) :
    entry (IncrFirstN n X) 0 j = entry X 0 j + n := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

private theorem Trans_IncrFirstN_pt (n : ℕ) (X : PS) (hX : TPS X) :
    Trans (IncrFirstN n X) = Trans X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
      have hXI : TPS (IncrFirst X) := by
        have h0 : 0 < Lng (IncrFirst X) := by
          have : Lng (IncrFirst X) = Lng X := by simp [IncrFirst]
          rw [this]
          exact List.length_pos_of_ne_nil hX
        exact List.ne_nil_of_length_pos h0
      calc
        Trans (IncrFirstN (n + 1) X) = Trans (IncrFirstN n (IncrFirst X)) := rfl
        _ = Trans (IncrFirst X) := ih (IncrFirst X) hXI
        _ = Trans X := Trans_IncrFirst X hX

private theorem adm_IncrFirstN_pt (n : ℕ) (X : PS) (j : ℕ) :
    adm (IncrFirstN n X) j = adm X j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem Adm_IncrFirstN_pt (n : ℕ) (X : PS) (j : ℕ) :
    Adm (IncrFirstN n X) j = Adm X j := by
  have hfun : (fun j' => adm (IncrFirstN n X) j') = (fun j' => adm X j') :=
    funext (fun j' => adm_IncrFirstN_pt n X j')
  unfold Adm
  rw [adm_IncrFirstN_pt n X j, hfun]

private theorem parents_IncrFirstN_pt (n : ℕ) (X : PS) (i j : ℕ) :
    parents (IncrFirstN n X) i j = parents X i j := by
  simp only [parents, Lng_IncrFirstN_pt, nextR_IncrFirstN_ri]

private theorem parent_IncrFirstN_pt (n : ℕ) (X : PS) (i j : ℕ) :
    parent (IncrFirstN n X) i j = parent X i j := by
  simp only [parent, parents_IncrFirstN_pt]

private theorem hasParent_IncrFirstN_pt (n : ℕ) (X : PS) (i j : ℕ) :
    hasParent (IncrFirstN n X) i j = hasParent X i j := by
  simp only [hasParent, parents_IncrFirstN_pt]

private theorem seg_getElem_pt (M : PS) (a b k : ℕ)
    (hk : k < Lng (seg M a b)) :
    (seg M a b)[k] = (entry M 0 (a + k), entry M 1 (a + k)) := by
  simp [seg, List.getElem_range']

private theorem seg_seg_pt (M : PS) (a b c d : ℕ) (hd : a + d ≤ b) :
    seg (seg M a b) c d = seg M (a + c) (a + d) := by
  apply List.ext_getElem
  · show Lng (seg (seg M a b) c d) = Lng (seg M (a + c) (a + d))
    simp only [length_seg]
    omega
  · intro k hk1 hk2
    have hk1' : k < Lng (seg (seg M a b) c d) := hk1
    have hk2' : k < Lng (seg M (a + c) (a + d)) := hk2
    have hkd : k < d + 1 - c := by simpa [length_seg] using hk1'
    have hck : c + k < Lng (seg M a b) := by
      simp only [length_seg]
      omega
    rw [seg_getElem_pt (seg M a b) c d k hk1',
        seg_getElem_pt M (a + c) (a + d) k hk2',
        entry_seg M a b 0 (c + k) hck, entry_seg M a b 1 (c + k) hck]
    have heq : a + (c + k) = a + c + k := by omega
    rw [heq]

private theorem seg_IncrFirstN_pt (n : ℕ) (X : PS) (a b : ℕ)
    (hb : b < Lng X) :
    seg (IncrFirstN n X) a b = IncrFirstN n (seg X a b) := by
  rw [IncrFirstN_eq_map n (seg X a b)]
  apply List.ext_getElem
  · simp only [length_seg, List.length_map]
  · intro k hk1 hk2
    have hk1' : k < Lng (seg (IncrFirstN n X) a b) := hk1
    have hkb : k < b + 1 - a := by
      have := hk1'
      simp only [length_seg] at this
      omega
    have hak : a + k < Lng X := by omega
    have hkS : k < Lng (seg X a b) := by
      simp only [length_seg]
      omega
    rw [seg_getElem_pt (IncrFirstN n X) a b k hk1',
        entry_IncrFirstN_zero_pt n X (a + k) hak,
        entry_IncrFirstN_one_pt n X (a + k) hak,
        List.getElem_map, seg_getElem_pt X a b k hkS]

/-! ## 私的補題層 2: 行 1 許容化祖先（`adm_row1_ancestry` の再証明）と `adm M 0` -/

private theorem adm_zero_pt (M : PS) : adm M 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem le1Aux_chain_pt (M : PS) (a : ℕ) (b fuel : ℕ)
    (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → nextrel1 M (j - 1) j = true)
    (hfuel : b - a ≤ fuel) : le1Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by omega
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      by_cases heq : a = b
      · subst b
        simp [le1Aux]
      · have hablt : a < b := lt_of_le_of_ne hab heq
        rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        refine ⟨b - 1, by omega, hstep b hablt (le_refl _), ?_⟩
        apply ih (b := b - 1)
        · omega
        · intro j haj hjb
          exact hstep j haj (by omega)
        · omega

private theorem adm_row1_ancestry_pt (M : PS) (j : ℕ)
    (hM : TPS M) (hj : j ≤ Lng M - 1) :
    leR M 1 (Adm M j) j = true := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : j < Lng M := by omega
  have haLe : Adm M j ≤ j := Adm_le M j
  have haL : Adm M j < Lng M := haLe.trans_lt hjL
  have hstep : ∀ k, Adm M j < k → k ≤ j →
      nextrel1 M (k - 1) k = true := by
    intro k hak hkj
    have hkadm : adm M k = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M k j hk hkj
      omega
    have hnadm : nadm M k = true := by
      simpa [adm] using hkadm
    have hkL : k < Lng M := hkj.trans_lt hjL
    have hpair : nextR M 1 (k - 1) k = true ∧
        nextR M 1 k (k + 1) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · exact hn
    simpa [nextR] using hpair.1
  have haux : le1Aux M (Lng M) (Adm M j) j = true :=
    le1Aux_chain_pt M (Adm M j) j (Lng M) haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_refl_pt (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_row0_pt (M : PS) (fuel : ℕ) (a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_pt]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_pt]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

private theorem row1_row0_pt (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_row0_pt M (Lng M) a b hM hh.1.2 hh.2

/-! ## 私的エンジン: part (4-1) back-slice の深さ 1 `Trans` 形

`a ≤ p`, `p + 1 < b`, `a = Adm M p`, `p = parent(b)` の設定で
`Trans ((M_j)_{j=a}^{b}) = D_{M_{1,a}}(t₂ + D_{M_{1,b}} 0)`。
Isabelle の `repr_*` 束の代わりに: `R = Red (seg M a b)` へ `IncrFirstN`
不変量で `parent`/`Adm`/行 1 entry を転送し、`transJm1 R = 0` と条件
(I)/(III)/(V) を直接判定、`Trans R = Mark R 0 = Mark R (transJm1 R) = transC2 R`
（7.4 公開補題）で値化する。 -/

private theorem part4_TransN_engine_pt (M : PS) (a b p : ℕ)
    (hR : RTPS M) (hbL : b ≤ Lng M - 1)
    (hanc : leR M 0 a b = true)
    (hpar : nextR M 0 p b = true)
    (hap : a ≤ p) (hgap : p + 1 < b)
    (hAdmp : Adm M p = a)
    (hguard : a = p ∨ entry M 1 p + 1 = entry M 1 b) :
    ∃ t₂, Trans (seg M a b)
      = Dprin (entry M 1 a : ℕ∞)
          (addBT t₂ (Dprin (entry M 1 b : ℕ∞) BZero)) := by
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
  have hhasN : hasParent (seg M a b) 0 (b - a) = true :=
    (hasParent_iff_unique_fseq (seg M a b) 0 (b - a)).mpr
      ⟨p - a, hnextN, huniqN⟩
  have hparR : parent (Red (seg M a b)) 0 (b - a) = p - a := by
    rw [hIF, parent_IncrFirstN_pt] at hparN
    exact hparN
  have hhasR : hasParent (Red (seg M a b)) 0 (b - a) = true := by
    rw [hIF, hasParent_IncrFirstN_pt] at hhasN
    exact hhasN
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
    rw [hIF, Adm_IncrFirstN_pt] at hAdmN
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
      exact entry_IncrFirstN_one_pt (entry M 0 a - entry M 1 a)
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
  -- 条件 (I)/(III)/(V)
  have hcond : (transCondI (Red (seg M a b)) || transCondIII (Red (seg M a b))
      || transCondV (Red (seg M a b))) = true := by
    by_cases hB : entry M 1 p + 1 = entry M 1 b
    · -- (V): `M_{1,p} + 1 = M_{1,b}` かつ間隙 `p+1 < b`
      have hEp : entry (Red (seg M a b)) 1 (p - a) = entry M 1 p := by
        have h := hE1 (p - a) (by omega)
        have e1 : a + (p - a) = p := by omega
        rw [e1] at h
        exact h
      have hV : transCondV (Red (seg M a b)) = true := by
        simp only [transCondV, hIdx, hPar, hEb, hEp]
        have h1 : 0 < entry M 1 b := by omega
        have h2 : p - a + 1 < b - a := by omega
        simp [h1, h2, hB]
      simp [hV]
    · -- 4-1 ガードの左枝: `a = p`
      have hA : a = p := hguard.resolve_right hB
      subst hA
      have hPar0 : lastParent (Red (seg M a b)) = 0 := by
        rw [hPar]
        omega
      by_cases hz : entry M 1 b = 0
      · -- (I)
        have hI : transCondI (Red (seg M a b)) = true := by
          simp only [transCondI, hIdx, hPar0, hEb]
          simp [hz, adm_zero_pt]
        simp [hI]
      · -- (III): 簡約性の鎖 `M_{1,b} ≤ M_{1,a} + 1` と `≠` から `≤`
        have hcoeff : entry (Red (seg M a b)) 1 (b - a)
            ≤ entry (Red (seg M a b)) 0 (b - a) :=
          reduced_coeff (Red (seg M a b)) hRRT (b - a) (by omega)
        have hAR : RedCondA (Red (seg M a b)) = true :=
          (RTPS_condAB (Red (seg M a b)) hRRT).1
        have hstepA : entry (Red (seg M a b)) 0
              (parent (Red (seg M a b)) 0 (b - a)) + 1
            = entry (Red (seg M a b)) 0 (b - a) :=
          RedCondA_apply (Red (seg M a b)) hAR 0 (b - a) (by omega)
            (by omega) hhasR
        have hpar0 : parent (Red (seg M a b)) 0 (b - a) = 0 := by
          rw [hparR]
          omega
        rw [hpar0] at hstepA
        have hhead : entry (Red (seg M a b)) 0 0
            = entry (Red (seg M a b)) 1 0 :=
          RTPS_mono_head_eq (Red (seg M a b)) hRRT hmonoR
        have hIII : transCondIII (Red (seg M a b)) = true := by
          simp only [transCondIII, hIdx, hPar0, hEb, hE0]
          have h1 : 0 < entry M 1 b := by omega
          have h2 : entry M 1 b ≤ entry M 1 a := by omega
          simp [h1, h2, adm_zero_pt]
        simp [hIII]
  -- clause (1) 型の値化
  have hleR00 : leR (Red (seg M a b)) 0 0 (Lng (Red (seg M a b)) - 1) = true := by
    have hh := hmonoR
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hMk0 : Marked (Red (seg M a b)) 0 := ⟨hRT, adm_zero_pt _, hleR00⟩
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
  have hshape : transC2 (Red (seg M a b))
      = Dprin (transV (Red (seg M a b)))
          (addBT (transT2 (Red (seg M a b)))
            (Dprin (entry (Red (seg M a b)) 1
                (lastIdx (Red (seg M a b))) : ℕ∞) BZero)) := by
    simp only [transC2, transC2Core]
    rw [if_pos hcond]
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
  refine ⟨transT2 (Red (seg M a b)), ?_⟩
  rw [hTransSeg, hTc2, hshape, hV, hIdx, hEb]

/-! ## 公開定理 1/2: part (4-1) back-slice `Trans` 形
（`m_8_1_c1_around_part4_TransN_41`） -/

theorem c1_around_part4_TransN_41 (M : PS) (j₀' : ℕ)
    (hR : RTPS M) (hmono : monoT M = true)
    (_hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M)
    (hguard : Adm M j₀' = j₀' ∨ entry M 1 j₀' + 1 = entry M 1 (transJ0 M)) :
    ∃ t₂, Trans (seg M (Adm M j₀') (transJ0 M))
      = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
          (addBT t₂ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) := by
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hj1' : 1 < Lng M - 1 := by omega
  have hlen : 1 < Lng M := by omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    rw [htJ0]
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hle0' : leR M 0 j₀' (transJ0 M) = true := nextR0_leR M _ _ np
  have haLe : Adm M j₀' ≤ j₀' := Adm_le M j₀'
  have hj0'lt : j₀' < transJ0 M := by omega
  have hle1a : leR M 1 (Adm M j₀') j₀' = true :=
    adm_row1_ancestry_pt M j₀' hM (by omega)
  have hle0a : leR M 0 (Adm M j₀') j₀' = true :=
    row1_row0_pt M _ _ hM hle1a
  have hanc : leR M 0 (Adm M j₀') (transJ0 M) = true :=
    row0_transitive M _ _ _ hM hle0a hle0'
  exact part4_TransN_engine_pt M (Adm M j₀') (transJ0 M) j₀' hR
    (by omega) hanc np haLe hadj rfl hguard

#print axioms c1_around_part4_TransN_41

/-! ## 公開定理 2/2: part (4) 共通 scb 位置（`m_8_1_c1_around_part4_segpos`）

`RN = Red ((M_j)_{j=j′₋₁}^{j₁-1})` 上で `Trans_Mark_seg` を適用し、
接頭辞切片と `Mark` の両表示を `IncrFirstN` 転送で `M` の切片翻訳へ引き戻す。 -/

theorem c1_around_part4_segpos (M : PS) (jm1' j0 j1 : ℕ) (c1 : BT)
    (hR : RTPS M) (hmono : monoT M = true)
    (hjm1'ltj0 : jm1' < j0) (hjlt : j0 < j1 - 1)
    (hj1ltL : j1 < Lng M) (hj1gt : 1 < j1)
    (_hleMaj0 : leR M 0 jm1' j0 = true)
    (hleMaj1m1 : leR M 0 jm1' (j1 - 1) = true)
    (hSmMk : Marked (seg M jm1' (j1 - 1)) (j0 - jm1'))
    (hc1part1 : Trans (seg M j0 (j1 - 1)) = c1) :
    ∃ s b,
      scb_decomp (Trans (seg M jm1' j0)) s
          (flatBT (Dprin (entry M 1 j0 : ℕ∞) BZero)) b ∧
        scb_decomp (Trans (seg M jm1' (j1 - 1))) s (flatBT c1) b := by
  have hM : TPS M := RTPS_TPS M hR
  -- 切片 `S = seg M jm1' (j1-1)` の基礎量
  have hLS : Lng (seg M jm1' (j1 - 1)) = (j1 - 1) + 1 - jm1' :=
    length_seg M jm1' (j1 - 1)
  have hST : TPS (seg M jm1' (j1 - 1)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg M jm1' (j1 - 1))
    simp only [length_seg]
    omega
  -- 簡約プロキシ `RN = Red S`
  have hfacts := ancestor_slice_Red_IncrFirst M jm1' (j1 - 1) hR
    (by omega) (by omega) hleMaj1m1
  have hRedRN : Red (Red (seg M jm1' (j1 - 1))) = Red (seg M jm1' (j1 - 1)) :=
    hfacts.1
  have hIF : seg M jm1' (j1 - 1)
      = IncrFirstN (entry M 0 jm1' - entry M 1 jm1')
          (Red (seg M jm1' (j1 - 1))) := hfacts.2.2
  have hLRN : Lng (Red (seg M jm1' (j1 - 1))) = Lng (seg M jm1' (j1 - 1)) :=
    Lng_Red_invariance (seg M jm1' (j1 - 1)) hST
  have hRNT : TPS (Red (seg M jm1' (j1 - 1))) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (Red (seg M jm1' (j1 - 1)))
    rw [hLRN, hLS]
    omega
  have hRNRT : RTPS (Red (seg M jm1' (j1 - 1))) := by
    show reduced (Red (seg M jm1' (j1 - 1))) = true
    have hne : Red (seg M jm1' (j1 - 1)) ≠ [] := hRNT
    simp [reduced, hne, hRedRN]
  -- `S` は anchored slice、`Marked` は `Red` を通る
  have hanch : anchoredSlice (seg M jm1' (j1 - 1)) := by
    refine ⟨M, jm1', j1 - 1, Or.inr ⟨hR, hM, hmono⟩, by omega, by omega, ?_, rfl⟩
    simpa [leR] using hleMaj1m1
  have hmkRN : Marked (Red (seg M jm1' (j1 - 1))) (j0 - jm1') :=
    Red_preserves_marked (seg M jm1' (j1 - 1)) (j0 - jm1') hanch hSmMk
  -- `Trans_Mark_seg` を `RN` に適用
  have hmmpos : 0 < j0 - jm1' := by omega
  have hmmlt : j0 - jm1' < Lng (Red (seg M jm1' (j1 - 1))) - 1 := by
    rw [hLRN, hLS]
    omega
  obtain ⟨s, b, hdSeg, hdM⟩ := Trans_Mark_seg_exists
    (Red (seg M jm1' (j1 - 1))) (j0 - jm1') hmkRN hRNRT hmmpos hmmlt
  -- (i) 行 1 entry の転送: `entry RN 1 mm = entry M 1 j0`
  have heRN : entry (Red (seg M jm1' (j1 - 1))) 1 (j0 - jm1') = entry M 1 j0 := by
    have h1 : entry (seg M jm1' (j1 - 1)) 1 (j0 - jm1')
        = entry (Red (seg M jm1' (j1 - 1))) 1 (j0 - jm1') := by
      conv_lhs => rw [hIF]
      exact entry_IncrFirstN_one_pt (entry M 0 jm1' - entry M 1 jm1')
        (Red (seg M jm1' (j1 - 1))) (j0 - jm1') (by rw [hLRN, hLS]; omega)
    have h2 : entry (seg M jm1' (j1 - 1)) 1 (j0 - jm1')
        = entry M 1 (jm1' + (j0 - jm1')) :=
      entry_seg M jm1' (j1 - 1) 1 (j0 - jm1') (by rw [hLS]; omega)
    have h3 : jm1' + (j0 - jm1') = j0 := by omega
    rw [← h1, h2, h3]
  -- (ii) 接頭辞切片の `Trans` 転送: `Trans (seg RN 0 mm) = Trans (seg M jm1' j0)`
  have hTr : Trans (seg (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1'))
      = Trans (seg M jm1' j0) := by
    have hseg1 : seg (seg M jm1' (j1 - 1)) 0 (j0 - jm1') = seg M jm1' j0 := by
      have h := seg_seg_pt M jm1' (j1 - 1) 0 (j0 - jm1') (by omega)
      have h3 : jm1' + (j0 - jm1') = j0 := by omega
      rw [h, Nat.add_zero, h3]
    have hseg2 : seg (seg M jm1' (j1 - 1)) 0 (j0 - jm1')
        = IncrFirstN (entry M 0 jm1' - entry M 1 jm1')
            (seg (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1')) := by
      conv_lhs => rw [hIF]
      exact seg_IncrFirstN_pt (entry M 0 jm1' - entry M 1 jm1')
        (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1') (by rw [hLRN, hLS]; omega)
    have hTPSseg : TPS (seg (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1')) := by
      apply List.ne_nil_of_length_pos
      simp only [length_seg]
      omega
    calc
      Trans (seg (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1'))
          = Trans (IncrFirstN (entry M 0 jm1' - entry M 1 jm1')
              (seg (Red (seg M jm1' (j1 - 1))) 0 (j0 - jm1'))) :=
        (Trans_IncrFirstN_pt _ _ hTPSseg).symm
      _ = Trans (seg (seg M jm1' (j1 - 1)) 0 (j0 - jm1')) := by rw [← hseg2]
      _ = Trans (seg M jm1' j0) := by rw [hseg1]
  -- (iii) `Mark RN mm = c1`
  have hMark : Mark (Red (seg M jm1' (j1 - 1))) (j0 - jm1') = c1 := by
    have hLval : Lng (Red (seg M jm1' (j1 - 1))) - 1 = (j1 - 1) - jm1' := by
      rw [hLRN, hLS]
      omega
    have hrepr : Mark (Red (seg M jm1' (j1 - 1))) (j0 - jm1')
        = Trans (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1')
            (Lng (Red (seg M jm1' (j1 - 1))) - 1)) :=
      Mark_Trans_repr (Red (seg M jm1' (j1 - 1))) (j0 - jm1') hmkRN hRNRT hmmlt
    rw [hLval] at hrepr
    have hsegtr : seg (seg M jm1' (j1 - 1)) (j0 - jm1') ((j1 - 1) - jm1')
        = IncrFirstN (entry M 0 jm1' - entry M 1 jm1')
            (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1') ((j1 - 1) - jm1')) := by
      conv_lhs => rw [hIF]
      exact seg_IncrFirstN_pt (entry M 0 jm1' - entry M 1 jm1')
        (Red (seg M jm1' (j1 - 1))) (j0 - jm1') ((j1 - 1) - jm1')
        (by rw [hLRN, hLS]; omega)
    have hsegSeq : seg (seg M jm1' (j1 - 1)) (j0 - jm1') ((j1 - 1) - jm1')
        = seg M j0 (j1 - 1) := by
      have h := seg_seg_pt M jm1' (j1 - 1) (j0 - jm1') ((j1 - 1) - jm1')
        (by omega)
      have h3 : jm1' + (j0 - jm1') = j0 := by omega
      have h4 : jm1' + ((j1 - 1) - jm1') = j1 - 1 := by omega
      rw [h3, h4] at h
      exact h
    have hTPSseg : TPS (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1')
        ((j1 - 1) - jm1')) := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1') ((j1 - 1) - jm1'))
      simp only [length_seg]
      omega
    calc
      Mark (Red (seg M jm1' (j1 - 1))) (j0 - jm1')
          = Trans (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1')
              ((j1 - 1) - jm1')) := hrepr
      _ = Trans (IncrFirstN (entry M 0 jm1' - entry M 1 jm1')
              (seg (Red (seg M jm1' (j1 - 1))) (j0 - jm1') ((j1 - 1) - jm1'))) :=
        (Trans_IncrFirstN_pt _ _ hTPSseg).symm
      _ = Trans (seg (seg M jm1' (j1 - 1)) (j0 - jm1') ((j1 - 1) - jm1')) := by
        rw [← hsegtr]
      _ = Trans (seg M j0 (j1 - 1)) := by rw [hsegSeq]
      _ = c1 := hc1part1
  -- (iv) 全体 `Trans` の転送
  have hTrS : Trans (seg M jm1' (j1 - 1)) = Trans (Red (seg M jm1' (j1 - 1))) :=
    Trans_Red (seg M jm1' (j1 - 1)) hST
  -- 組み立て
  refine ⟨s, b, ?_, ?_⟩
  · rw [← hTr, ← heRN]
    exact hdSeg
  · rw [hTrS, ← hMark]
    exact hdM

#print axioms c1_around_part4_segpos

end PSS
