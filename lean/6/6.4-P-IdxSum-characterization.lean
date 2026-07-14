import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»
import «5».«5.1-ancestor-tree»
import «6».«6.4-P-IdxSum»

/-!
# §6.4 系（`P` と `IdxSum` の合成の特徴付け）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_P_IdxSum_char_1`, `_2`
- 訂正: なし
- Isabelle: `m_6_4_P_IdxSum_char_1`, `_2`
- 依存: `6.4-P-IdxSum`, §5.1
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem P_leftend_lmin (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) :
    (IdxSum (P M)).getD J 0 ≤ Lng M - 1 ∧
      ∀ j, j < (IdxSum (P M)).getD J 0 →
        entry M 0 ((IdxSum (P M)).getD J 0) ≤ entry M 0 j := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M J with
  | h n ih =>
      by_cases hm : multiT M = true
      · have hlen := multi_length_fseq M hM hm
        let c := Pcut M
        let Mp := M.take c
        have hc := Pcut_props M hlen
        have hcpos : 0 < c := by simpa [c] using hc.1
        have hcL : c < Lng M := by simp [c]; omega
        have hMpLen : Lng Mp = c := by simp [Mp, Nat.min_eq_left hcL.le]
        have hMpT : TPS Mp := by
          intro heq
          have : Lng Mp = 0 := by simp [heq]
          omega
        have hstep : P M = P Mp ++ [M.drop c] := by
          simpa [Mp, c] using P_multi_step M hm hlen
        let q := (P Mp).length
        have hPMlen : (P M).length = q + 1 := by simp [hstep, q]
        have hsum : ((P Mp).map Lng).sum = c := by
          have hf := congrArg Lng (P_concat Mp)
          simpa [List.length_flatten, hMpLen] using hf
        by_cases hJpre : J < q
        · have htake : (P M).take J = (P Mp).take J := by
            rw [hstep]
            simp [q, hJpre.le]
          have hidx : (IdxSum (P M)).getD J 0 =
              (IdxSum (P Mp)).getD J 0 := by
            rw [idxSum_getD (P M) J hJ.le, idxSum_getD (P Mp) J (by simpa [q] using hJpre.le),
              htake]
          have hih := ih (Lng Mp) (by omega) Mp J hMpT (by simpa [q] using hJpre) rfl
          constructor
          · rw [hidx]
            omega
          · intro j hj
            have hidxLt : (IdxSum (P Mp)).getD J 0 < c := by
              have := hih.1
              rw [hMpLen] at this
              omega
            have hjMp : j < (IdxSum (P Mp)).getD J 0 := by
              rw [← hidx]
              exact hj
            have hjc : j < c := hjMp.trans hidxLt
            rw [hidx]
            rw [← entry_take M c 0 ((IdxSum (P Mp)).getD J 0) hidxLt,
              ← entry_take M c 0 j hjc]
            simpa [Mp] using hih.2 j hjMp
        · have hJeq : J = q := by omega
          have hidx : (IdxSum (P M)).getD J 0 = c := by
            rw [idxSum_getD (P M) J hJ.le, hJeq, hstep]
            simp [q, hsum]
          constructor
          · rw [hidx]
            omega
          · intro j hj
            rw [hidx] at hj ⊢
            exact Pcut_left_min M hM hm hlen j (by simpa [c] using hj)
      · have hmf : multiT M = false := by simpa using hm
        have hP : P M = [M] := P_nonmulti_eq M hmf
        have hJeq : J = 0 := by simp [hP] at hJ; omega
        simp [hP, hJeq, IdxSum]

theorem P_lmin_leftend (M : PS) (k : ℕ) (hM : TPS M)
    (hk : k ≤ Lng M - 1)
    (hmin : ∀ j, j < k → entry M 0 k ≤ entry M 0 j) :
    ∃ J, J < (P M).length ∧ (IdxSum (P M)).getD J 0 = k := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M k with
  | h n ih =>
      by_cases hm : multiT M = true
      · have hlen := multi_length_fseq M hM hm
        let c := Pcut M
        let Mp := M.take c
        have hc := Pcut_props M hlen
        have hcpos : 0 < c := by simpa [c] using hc.1
        have hcL : c < Lng M := by simp [c]; omega
        have hMpLen : Lng Mp = c := by simp [Mp, Nat.min_eq_left hcL.le]
        have hMpT : TPS Mp := by
          intro heq
          have : Lng Mp = 0 := by simp [heq]
          omega
        have hstep : P M = P Mp ++ [M.drop c] := by
          simpa [Mp, c] using P_multi_step M hm hlen
        let q := (P Mp).length
        have hPMlen : (P M).length = q + 1 := by simp [hstep, q]
        have hsum : ((P Mp).map Lng).sum = c := by
          have hf := congrArg Lng (P_concat Mp)
          simpa [List.length_flatten, hMpLen] using hf
        have hkc : k ≤ c := by
          by_contra hnot
          have hck : c < k := by omega
          have hgrowth := ancestor_basic_1 M c k (Lng M - 1) hM hck hk
            (by simpa [c] using hc.2.2)
          have hreverse := hmin c hck
          omega
        by_cases hkeq : k = c
        · refine ⟨q, by omega, ?_⟩
          rw [idxSum_getD (P M) q (by omega), hstep]
          simp [q, hsum, hkeq]
        · have hkcLt : k < c := by omega
          have hkMp : k ≤ Lng Mp - 1 := by rw [hMpLen]; omega
          have hminMp : ∀ j, j < k → entry Mp 0 k ≤ entry Mp 0 j := by
            intro j hj
            rw [entry_take M c 0 k hkcLt, entry_take M c 0 j (by omega)]
            exact hmin j hj
          obtain ⟨J, hJL, hJidx⟩ :=
            ih (Lng Mp) (by omega) Mp k hMpT hkMp hminMp rfl
          refine ⟨J, by simpa [hPMlen, q] using hJL.trans (Nat.lt_succ_self q), ?_⟩
          have htake : (P M).take J = (P Mp).take J := by
            rw [hstep]
            simp [q, hJL.le]
          rw [idxSum_getD (P M) J (by omega), htake,
            ← idxSum_getD (P Mp) J hJL.le]
          exact hJidx
      · have hmf : multiT M = false := by simpa using hm
        have hP : P M = [M] := P_nonmulti_eq M hmf
        have hkzero : k = 0 := by
          by_contra hnot
          have hkpos : 0 < k := by omega
          have hkL : k < Lng M := by
            have hMpos := List.length_pos_of_ne_nil hM
            omega
          have hgrowth := (multi_criterion_12 M hM).mp hmf k hkpos hkL
          have hreverse := hmin 0 hkpos
          omega
        refine ⟨0, by simp [hP], ?_⟩
        simp [hP, IdxSum, hkzero]

theorem row0_parent_unique (M : PS) (a b k : ℕ)
    (ha : nextR M 0 a k = true) (hb : nextR M 0 b k = true) : a = b := by
  by_contra hne
  have ha0 : nextrel0 M a k = true := by simpa [nextR] using ha
  have hb0 : nextrel0 M b k = true := by simpa [nextR] using hb
  have hha := ha0
  have hhb := hb0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hha hhb
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hs := hha.2 b (List.mem_range.mpr hhb.1.1.2)
    have hle : entry M 0 k ≤ entry M 0 b := by simpa [hab] using hs
    omega
  · have hs := hhb.2 a (List.mem_range.mpr hha.1.1.2)
    have hle : entry M 0 k ≤ entry M 0 a := by simpa [hba] using hs
    omega

private theorem no_row0_parent_iff_lmin (M : PS) (k : ℕ) (hM : TPS M)
    (hk : k < Lng M) :
    (¬ ∃! j₀, nextR M 0 j₀ k = true) ↔
      ∀ j, j < k → entry M 0 k ≤ entry M 0 j := by
  have hexiff : (∃! j₀, nextR M 0 j₀ k = true) ↔
      ∃ j₀, nextR M 0 j₀ k = true := by
    constructor
    · rintro ⟨j, hj, _⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, hj, fun y hy => row0_parent_unique M y j k hy hj⟩
  rw [hexiff]
  constructor
  · intro hno j hj
    by_contra hnot
    have hlt : entry M 0 j < entry M 0 k := by omega
    obtain ⟨p, _, _, hp⟩ := parent_exists_1 M j k hM hj hk hlt
    exact hno ⟨p, hp⟩
  · intro hmin ⟨p, hp⟩
    have hp0 : nextrel0 M p k = true := by simpa [nextR] using hp
    have hh := hp0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hreverse := hmin p hh.1.1.2
    omega

theorem P_IdxSum_char_1 (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J ≤ (P M).length - 1) :
    ¬ ∃! j₀, nextR M 0 j₀ ((IdxSum (P M)).getD J 0) = true := by
  have hQpos := List.length_pos_of_ne_nil (P_nonempty M)
  have hJL : J < (P M).length := by omega
  have hlmin := P_leftend_lmin M J hM hJL
  have hkL : (IdxSum (P M)).getD J 0 < Lng M := by
    have hMpos := List.length_pos_of_ne_nil hM
    have hpred : Lng M - 1 + 1 = Lng M :=
      Nat.sub_add_cancel (show 1 ≤ Lng M from hMpos)
    omega
  exact (no_row0_parent_iff_lmin M _ hM hkL).mpr hlmin.2

theorem P_IdxSum_char_2 (M : PS) (j : ℕ) (hM : TPS M)
    (hj : j ≤ Lng M - 1)
    (hno : ¬ ∃! j₀, nextR M 0 j₀ j = true) :
    ∃ J, J ≤ (P M).length - 1 ∧ j = (IdxSum (P M)).getD J 0 := by
  have hMpos := List.length_pos_of_ne_nil hM
  have hpred : Lng M - 1 + 1 = Lng M :=
    Nat.sub_add_cancel (show 1 ≤ Lng M from hMpos)
  have hjL : j < Lng M := by omega
  have hlmin := (no_row0_parent_iff_lmin M j hM hjL).mp hno
  obtain ⟨J, hJL, hidx⟩ := P_lmin_leftend M j hM hj hlmin
  exact ⟨J, by omega, hidx.symm⟩

#print axioms P_IdxSum_char_1
#print axioms P_IdxSum_char_2

end PSS
