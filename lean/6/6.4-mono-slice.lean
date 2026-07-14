import «6».«6.2-mono-ancestor-slice»
import «6».«6.4-FirstNodes-Joints-mono»

/-!
# §6.4 系（単項性の切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_mono_slice`
- 訂正: なし
- Isabelle: `m_6_4_mono_slice`
- 依存: §6.4 の幹・枝補題、`6.2-mono-ancestor-slice`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem le0Aux_refl_ms (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_ms (M : PS) (j : ℕ) (hj : j < Lng M) :
    leR M 0 j j = true := by
  simp [leR, le0, hj, le0Aux_refl_ms]

theorem TrMax_trunk_step (M : PS) (j : ℕ) (hM : TPS M)
    (hj : j < TrMax M) : nextR M 1 j (j + 1) = true := by
  let q := fun x => !nextR M 1 x (x + 1)
  have hMpos := List.length_pos_of_ne_nil hM
  unfold TrMax at hj
  change j < ((List.range (Lng M)).find? q).getD (Lng M - 1) at hj
  cases hf : (List.range (Lng M)).find? q with
  | none =>
      have hjL : j < Lng M := by
        simp only [hf, Option.getD_none] at hj
        omega
      have hn := (List.find?_eq_none.mp hf) j (List.mem_range.mpr hjL)
      change ¬q j = true at hn
      change nextR M 1 j (j + 1) = true
      cases hx : nextR M 1 j (j + 1) <;> simp [q, hx] at hn ⊢
  | some c =>
      have hjc : j < c := by simpa only [hf, Option.getD_some] using hj
      have hf' : (List.range' 0 (Lng M)).find? q = some c := by simpa using hf
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 j (Nat.zero_le j) hjc
      change (!q j) = true at hmin
      change nextR M 1 j (j + 1) = true
      simpa [q] using hmin

theorem trunk_le0 (M : PS) (a b : ℕ) (hM : TPS M)
    (hab : a ≤ b) (hb : b ≤ TrMax M) : leR M 0 a b = true := by
  have hMpos := List.length_pos_of_ne_nil hM
  have hT := TrMax_bound M hM
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact leR0_refl_ms M 0 hMpos
  | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        exact leR0_refl_ms M (b + 1) (by omega)
      · have hab' : a ≤ b := by omega
        have hbT : b < TrMax M := by omega
        have hleft := ih a hab' hbT.le
        have hs := TrMax_trunk_step M b hM hbT
        have hs1 : nextrel1 M b (b + 1) = true := by simpa [nextR] using hs
        have hstep0 : leR M 0 b (b + 1) = true := by
          have hh := hs1
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
          simpa [leR] using hh.1.2
        exact row0_transitive M a b (b + 1) hM hleft hstep0

theorem idxSum_total (Q : List PS) :
    (IdxSum Q).getD Q.length 0 = Lng Q.flatten := by
  rw [idxSum_getD Q Q.length (le_refl _)]
  simp [List.length_flatten]

theorem idxSum_locate (Q : List PS) (k : ℕ)
    (hk : k < (IdxSum Q).getD Q.length 0) :
    ∃ J, J < Q.length ∧
      (IdxSum Q).getD J 0 ≤ k ∧
      k < (IdxSum Q).getD (J + 1) 0 := by
  let S := (Finset.range (Q.length + 1)).filter
    (fun J => (IdxSum Q).getD J 0 ≤ k)
  have hzidx : (IdxSum Q).getD 0 0 = 0 := by
    simpa using idxSum_getD Q 0 (Nat.zero_le _)
  have hzero : 0 ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨by simp, by rw [hzidx]; omega⟩
  have hSne : S.Nonempty := ⟨0, hzero⟩
  let J := S.max' hSne
  have hJS : J ∈ S := Finset.max'_mem S hSne
  have hJL : J ≤ Q.length := by
    have := (Finset.mem_filter.mp hJS).1
    simp only [Finset.mem_range] at this
    omega
  have hJidx : (IdxSum Q).getD J 0 ≤ k := (Finset.mem_filter.mp hJS).2
  have hJlt : J < Q.length := by
    by_contra hnot
    have hJeq : J = Q.length := by omega
    rw [hJeq] at hJidx
    omega
  have hnext : k < (IdxSum Q).getD (J + 1) 0 := by
    by_contra hnot
    have hmem : J + 1 ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨by simp; omega, Nat.le_of_not_gt hnot⟩
    have hle := Finset.le_max' S (J + 1) hmem
    omega
  exact ⟨J, hJlt, hJidx, hnext⟩

theorem branch_component_le0 (M : PS) (k : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (htr : TrMax M < k) (hkL : k ≤ Lng M - 1) :
    ∃ J, J < (Br M).length ∧
      leR M 0 ((FirstNodes M).getD J 0) k = true := by
  have hMpos := List.length_pos_of_ne_nil hM
  have hbound := TrMax_bound M hM
  have htrlt : TrMax M < Lng M - 1 := by omega
  let s := TrMax M + 1
  let N := seg M s (Lng M - 1)
  let Q := P N
  let kp := k - s
  have hsL : s ≤ Lng M - 1 := by simp [s]; omega
  have hlastL : Lng M - 1 < Lng M := by omega
  have hNlen : Lng N = Lng M - s := by simp [N]; omega
  have hNpos : 0 < Lng N := by rw [hNlen]; simp [s]; omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hBr : Br M = Q := by simp [Br, Q, N, s]; omega
  have hkpN : kp < Lng N := by simp [kp, hNlen, s]; omega
  have htotal : (IdxSum Q).getD Q.length 0 = Lng N := by
    rw [idxSum_total]
    simpa [Q] using congrArg Lng (P_concat N)
  have hkpTotal : kp < (IdxSum Q).getD Q.length 0 := by
    rw [htotal]
    exact hkpN
  obtain ⟨J, hJQ, haK, hkNext⟩ := idxSum_locate Q kp hkpTotal
  let a := (IdxSum Q).getD J 0
  let nxt := (IdxSum Q).getD (J + 1) 0
  let b := nxt - 1
  let C := Q.getD J []
  have hdiff : nxt = a + Lng C := by simpa [nxt, a, C] using idxSum_diff Q J hJQ
  have hCpos : 0 < Lng C := by
    simpa [Q, C] using P_component_nonempty N J hNT (by simpa [Q] using hJQ)
  have hnextTotal : nxt ≤ (IdxSum Q).getD Q.length 0 :=
    idxSum_mono Q (J + 1) Q.length (by omega) (le_refl _)
  have haN : a < Lng N := by rw [← htotal]; omega
  have hnxtPos : 0 < nxt := by rw [hdiff]; omega
  have hbN : b < Lng N := by
    rw [htotal] at hnextTotal
    simp only [b]
    omega
  have hab : a ≤ b := by simp [b]; rw [hdiff]; omega
  have hcomp : C = seg N a b := by
    simpa [Q, C, a, b, nxt] using P_IdxSum N J hNT (by simpa [Q] using (show J ≤ Q.length - 1 by omega))
  have hleN : leR N 0 a kp = true := by
    by_cases heq : a = kp
    · rw [← heq]
      exact leR0_refl_ms N a haN
    · have hak : a < kp := by omega
      let p := kp - a
      have hpPos : 0 < p := by simp [p]; omega
      have hpC : p < Lng C := by
        change kp < nxt at hkNext
        rw [hdiff] at hkNext
        simp [p]
        omega
      have hget : C = Q[J] := getD_eq_getElem_idx Q [] hJQ
      have hmem : C ∈ P N := by
        rw [hget]
        simpa [Q] using List.getElem_mem hJQ
      have hzm := P_components_nonmulti N hNT C hmem
      have hCmono : monoT C = true := by
        rcases hzm with hz | hm
        · have hh := hz
          simp [zeroT] at hh
          omega
        · exact hm
      have hCfull : leR C 0 0 (Lng C - 1) = true := by
        have hh := hCmono
        simp only [monoT, Bool.and_eq_true] at hh
        exact hh.2
      have hCT : TPS C := by
        intro hnil
        have : Lng C = 0 := by simp [hnil]
        omega
      have hCp := ancestor_tree_1 C 0 p (Lng C - 1) hCT hCfull
        (Nat.zero_le _) (by omega)
      have h0seg : 0 < Lng (seg N a b) := by rw [← hcomp]; exact hCpos
      have hpseg : p < Lng (seg N a b) := by rw [← hcomp]; exact hpC
      have htrans := leR0_seg_adm N a b 0 p hab hbN h0seg hpseg
      have hh : leR (seg N a b) 0 0 p = true := by
        rw [← hcomp]
        exact hCp
      rw [htrans] at hh
      have hap : a + p = kp := by simp [p]; omega
      simpa [hap] using hh
  have htransM := leR0_seg_adm M s (Lng M - 1) a kp hsL hlastL haN hkpN
  have hleM : leR M 0 (s + a) (s + kp) = true := by
    rw [← htransM]
    exact hleN
  have hfn : (FirstNodes M).getD J 0 = s + a := by
    have hh := FirstNodes_getD M J (by simpa [hBr] using hJQ)
    simpa [s, a, hBr] using hh
  have habsk : s + kp = k := by simp [kp, s]; omega
  refine ⟨J, by simpa [hBr] using hJQ, ?_⟩
  rw [hfn, ← habsk]
  exact hleM

theorem slice_le0_to_index (M : PS) (j₀ k : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hBr : Br M ≠ [])
    (hj₀ : j₀ ≤ (Joints M).getD ((Br M).length - 1) 0)
    (hjk : j₀ < k) (hkL : k ≤ Lng M - 1) :
    leR M 0 j₀ k = true := by
  let last := (Br M).length - 1
  have hlast : last < (Br M).length := by
    have := List.length_pos_of_ne_nil hBr
    simp [last]
    omega
  have hlastTr := (FirstNodes_TrMax_Joints M last hM hmono hlast).1
  have hj₀Tr : j₀ ≤ TrMax M := by simpa [last] using hj₀.trans hlastTr
  by_cases hkTr : k ≤ TrMax M
  · exact trunk_le0 M j₀ k hM hjk.le hkTr
  · have hTrk : TrMax M < k := Nat.lt_of_not_ge hkTr
    obtain ⟨J, hJ, hFNk⟩ := branch_component_le0 M k hM hmono hTrk hkL
    have hJle : J ≤ last := by simp [last]; omega
    have hlastLeJ : (Joints M).getD last 0 ≤ (Joints M).getD J 0 := by
      by_cases heq : J = last
      · subst J
        exact le_refl _
      · have hJl : J < last := by omega
        exact (FirstNodes_Joints_mono M J last hM hmono hJl hlast).2.1
    have hj₀a : j₀ ≤ (Joints M).getD J 0 := by
      simpa [last] using hj₀.trans hlastLeJ
    have haTr := (FirstNodes_TrMax_Joints M J hM hmono hJ).1
    have hja := trunk_le0 M j₀ ((Joints M).getD J 0) hM hj₀a haTr
    have hbound := TrMax_bound M hM
    have hne : TrMax M ≠ Lng M - 1 := by omega
    let N := seg M (TrMax M + 1) (Lng M - 1)
    have hBrP : Br M = P N := by simp [N, Br, hne]
    have hJP : J ≤ (P N).length - 1 := by rw [← hBrP]; omega
    have hs := mono_slice_next M (TrMax M + 1) J hM hmono
      (by omega) (by omega) (by simpa [N] using hJP)
    have hfn := FirstNodes_getD M J hJ
    have habs : TrMax M + 1 + (IdxSum (P N)).getD J 0 =
        (FirstNodes M).getD J 0 := by simpa [hBrP] using hfn.symm
    have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true := by
      rw [← habs]
      simpa [N] using hs.1
    have hnxp := nextR_parent0_of_hasParent M ((FirstNodes M).getD J 0) hhas
    have hjoint := Joints_getD M J hJ
    have hnx : nextR M 0 ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
      rw [hjoint]
      exact hnxp
    have haFN := nextR0_leR M _ _ hnx
    exact row0_transitive M j₀ (Joints M |>.getD J 0) k hM hja
      (row0_transitive M _ _ k hM haFN hFNk)

theorem mono_slice (M : PS) (j₀ j₁ : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hlt : j₀ < j₁) (hj₁ : j₁ ≤ Lng M - 1)
    (hj₀ : j₀ ≤ (Joints M).getD ((Br M).length - 1) 0) :
    monoT (seg M j₀ j₁) = true := by
  have hanc : leR M 0 j₀ j₁ = true := by
    by_cases hBr : Br M = []
    · have htr : TrMax M = Lng M - 1 := by
        by_contra hne
        have : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
        rw [hBr] at this
        exact P_nonempty _ this.symm
      exact trunk_le0 M j₀ j₁ hM hlt.le (by omega)
    · exact slice_le0_to_index M j₀ j₁ hM hmono hBr hj₀ hlt hj₁
  exact mono_ancestor_slice M j₀ j₁ hM hlt hanc

#print axioms mono_slice

end PSS
