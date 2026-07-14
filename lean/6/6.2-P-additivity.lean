import PSS.Mono
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»
import «5».«5.1-ancestor-tree»
import «6».«6.2-multi-criterion»
import «6».«6.2-mono-ancestor-slice»

/-!
# §6.2 命題（`P` の加法性）

- 原文: `isabelle/pss_paper.thy` の `p_6_2_P_additive`
- 訂正: なし
- Isabelle: `m_6_2_P_additive`
- 依存: §5.1 親存在・祖先基本性質・木構造, §6.2 複項性判定・祖先切片
- 状態: ✅ 証明済み
-/

namespace PSS

private theorem le0Aux_refl_add (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

theorem Pcut_props (M : PS) (hlen : 1 < Lng M) :
    0 < Pcut M ∧ Pcut M ≤ Lng M - 1 ∧
      leR M 0 (Pcut M) (Lng M - 1) = true := by
  let q : ℕ → Bool := fun j =>
    (0 < j) && (j ≤ Lng M - 1) && leR M 0 j (Lng M - 1)
  have hi : Lng M - 1 < Lng M := by omega
  have hq : q (Lng M - 1) = true := by
    have hp : 0 < Lng M - 1 := by omega
    have hr : leR M 0 (Lng M - 1) (Lng M - 1) = true := by
      simp [leR, le0, hi, le0Aux_refl_add]
    simp [q, hp, hr]
  have hsome : ∃ c, (List.range (Lng M)).find? q = some c := by
    cases hf : (List.range (Lng M)).find? q with
    | none =>
        have hn := (List.find?_eq_none.mp hf) (Lng M - 1) (by simp [hi])
        simp [hq] at hn
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hsome
  have hqc : q c = true := List.find?_some hc
  have hpc : Pcut M = c := by
    unfold Pcut
    change ((List.range (Lng M)).find? q).getD (Lng M - 1) = c
    rw [hc]
    rfl
  rw [hpc]
  simp [q] at hqc
  exact ⟨hqc.1.1, hqc.1.2, hqc.2⟩

theorem Pcut_not_candidate (M : PS) (hlen : 1 < Lng M)
    (j : ℕ) (hj : j < Pcut M) :
    ((0 < j) && (j ≤ Lng M - 1) &&
      leR M 0 j (Lng M - 1)) = false := by
  let q : ℕ → Bool := fun k =>
    (0 < k) && (k ≤ Lng M - 1) && leR M 0 k (Lng M - 1)
  unfold Pcut at hj
  change j < ((List.range (Lng M)).find? q).getD (Lng M - 1) at hj
  change q j = false
  cases hf : (List.range (Lng M)).find? q with
  | none =>
      have hjL : j < Lng M := by
        simp only [hf, Option.getD_none] at hj
        omega
      have hn := (List.find?_eq_none.mp hf) j (List.mem_range.mpr hjL)
      simpa using hn
  | some c =>
      have hjc : j < c := by simpa only [hf, Option.getD_some] using hj
      have hf' : (List.range' 0 (Lng M)).find? q = some c := by simpa using hf
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 j (Nat.zero_le j) hjc
      simpa using hmin

private theorem next0_le_add (M : PS) (a b : ℕ)
    (hab : nextR M 0 a b = true) : leR M 0 a b = true := by
  have hn : nextrel0 M a b = true := by simpa [nextR] using hab
  have hh := hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
  have haL : a < Lng M := hh.1.1.1.1
  have hbL : b < Lng M := hh.1.1.1.2
  have hablt : a < b := hh.1.1.2
  have haux : le0Aux M (Lng M) a b = true := by
    cases heq : Lng M with
    | zero => omega
    | succ fuel =>
        simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        exact ⟨a, hablt, hn, le0Aux_refl_add M fuel a⟩
  simp [leR, le0, haL, hbL, haux]

theorem Pcut_left_min (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) (hlen : 1 < Lng M) :
    ∀ j, j < Pcut M → entry M 0 (Pcut M) ≤ entry M 0 j := by
  intro j hj
  by_contra hnot
  have hlt : entry M 0 j < entry M 0 (Pcut M) := by omega
  have hc := Pcut_props M hlen
  rcases hc with ⟨hcpos, hcle, hanc⟩
  have hcL : Pcut M < Lng M := by omega
  obtain ⟨p, hjp, hpc, hpnext⟩ :=
    parent_exists_1 M j (Pcut M) hM hj hcL hlt
  have hpcle : leR M 0 p (Pcut M) = true := next0_le_add M p (Pcut M) hpnext
  have hplast : leR M 0 p (Lng M - 1) = true :=
    row0_transitive M p (Pcut M) (Lng M - 1) hM hpcle hanc
  by_cases hp0 : p = 0
  · subst p
    have hmfalse : multiT M = false := by
      have hz : zeroT M = false := by
        have ht := hmulti
        simp [multiT] at ht
        exact ht.1
      simp [multiT, monoT, hz, hplast]
    simp [hmulti] at hmfalse
  · have hppos : 0 < p := Nat.pos_of_ne_zero hp0
    have hpbound : p ≤ Lng M - 1 := by omega
    have hfalse := Pcut_not_candidate M hlen p hpc
    simp [hppos, hpbound, hplast] at hfalse

private theorem pAux_succ_eq_add (fuel : ℕ) (M : PS)
    (hbound : Lng M ≤ fuel) : PAux (fuel + 1) M = PAux fuel M := by
  induction fuel generalizing M with
  | zero =>
      have hlen : Lng M = 0 := by omega
      change (if multiT M && decide (1 < Lng M) then
        PAux 0 (M.take (Pcut M)) ++ [M.drop (Pcut M)] else [M]) = [M]
      rw [if_neg (by simp [hlen])]
  | succ fuel ih =>
      by_cases hs : (multiT M && decide (1 < Lng M)) = true
      · have hsplit : multiT M = true ∧ 1 < Lng M := by simpa using hs
        have hlen : 1 < Lng M := hsplit.2
        have hc := Pcut_props M hlen
        have hclt : Pcut M < Lng M := by omega
        have hprelen : Lng (M.take (Pcut M)) = Pcut M := by
          simp [Nat.min_eq_left hclt.le]
        have hprebound : Lng (M.take (Pcut M)) ≤ fuel := by omega
        change (if multiT M && decide (1 < Lng M) then
            PAux (fuel + 1) (M.take (Pcut M)) ++ [M.drop (Pcut M)] else [M]) =
          (if multiT M && decide (1 < Lng M) then
            PAux fuel (M.take (Pcut M)) ++ [M.drop (Pcut M)] else [M])
        rw [if_pos hs, if_pos hs, ih (M.take (Pcut M)) hprebound]
      · change (if multiT M && decide (1 < Lng M) then
            PAux (fuel + 1) (M.take (Pcut M)) ++ [M.drop (Pcut M)] else [M]) =
          (if multiT M && decide (1 < Lng M) then
            PAux fuel (M.take (Pcut M)) ++ [M.drop (Pcut M)] else [M])
        rw [if_neg hs, if_neg hs]

theorem PAux_stable (fuel : ℕ) (M : PS)
    (hbound : Lng M ≤ fuel) : PAux fuel M = PAux (Lng M) M := by
  induction fuel with
  | zero =>
      have hlen : Lng M = 0 := by omega
      simp [hlen]
  | succ fuel ih =>
      by_cases heq : Lng M = fuel + 1
      · simp [heq]
      · have hb : Lng M ≤ fuel := by omega
        calc
          PAux (fuel + 1) M = PAux fuel M := pAux_succ_eq_add fuel M hb
          _ = PAux (Lng M) M := ih hb

theorem P_nonmulti_eq (M : PS) (hm : multiT M = false) :
    P M = [M] := by
  unfold P
  cases Lng M <;> simp [PAux, hm]

theorem P_multi_step (M : PS) (hm : multiT M = true)
    (hlen : 1 < Lng M) :
    P M = P (M.take (Pcut M)) ++ [M.drop (Pcut M)] := by
  have hs : (multiT M && decide (1 < Lng M)) = true := by simp [hm, hlen]
  have hc := Pcut_props M hlen
  have hclt : Pcut M < Lng M := by omega
  have hprelen : Lng (M.take (Pcut M)) = Pcut M := by
    simp [Nat.min_eq_left hclt.le]
  have hbound : Lng (M.take (Pcut M)) ≤ Lng M - 1 := by omega
  unfold P
  cases heq : Lng M with
  | zero => omega
  | succ fuel =>
      rw [PAux, if_pos hs]
      have hstable := PAux_stable fuel (M.take (Pcut M)) (by simpa [heq] using hbound)
      simpa using congrArg (fun xs => xs ++ [M.drop (Pcut M)]) hstable

theorem drop_eq_seg (M : PS) (k : ℕ) (hk : k < Lng M) :
    M.drop k = seg M k (Lng M - 1) := by
  apply List.ext_getElem
  · have hpred : Lng M - 1 + 1 = Lng M := by omega
    simp [seg, hpred]
  · intro j hj₁ hj₂
    have hkj : k + j < Lng M := by
      simp only [List.length_drop] at hj₁
      exact Nat.add_lt_of_lt_sub' hj₁
    simp [seg, List.getElem_range', entry, hkj]

theorem P_drop_ancestor (M : PS) (c : ℕ) (hM : TPS M)
    (hcpos : 0 < c) (hcle : c ≤ Lng M - 1)
    (hanc : leR M 0 c (Lng M - 1) = true) :
    P (M.drop c) = [M.drop c] := by
  have hcL : c < Lng M := by omega
  have hnonmulti : multiT (M.drop c) = false := by
    by_cases heq : c = Lng M - 1
    · have hpred : Lng M - (Lng M - 1) = 1 := by omega
      have hlen : Lng (M.drop c) = 1 := by simpa [heq] using hpred
      by_cases hz : zeroT (M.drop c) = true
      · simp [multiT, hz]
      · have hm : monoT (M.drop c) = true := by
          simp [monoT, hz, hlen, leR, le0, le0Aux_refl_add]
        simp [multiT, hz, hm]
    · have hlt : c < Lng M - 1 := by omega
      have hmseg := mono_ancestor_slice M c (Lng M - 1) hM hlt hanc
      have hmdrop : monoT (M.drop c) = true := by
        rw [drop_eq_seg M c hcL]
        exact hmseg
      simp [multiT, hmdrop]
  exact P_nonmulti_eq (M.drop c) hnonmulti

theorem entry_take (M : PS) (k i j : ℕ) (hj : j < k) :
    entry (M.take k) i j = entry M i j := by
  unfold entry
  rw [List.getElem?_take_of_lt hj]

theorem entry_drop (M : PS) (k i j : ℕ) :
    entry (M.drop k) i j = entry M i (k + j) := by
  unfold entry
  rw [List.getElem?_drop]

private theorem P_additive_take_drop (M : PS) (j₀ : ℕ) (hM : TPS M)
    (hjpos : 0 < j₀) (hjlast : j₀ ≤ Lng M - 1)
    (hmin : ∀ j, j < j₀ → entry M 0 j₀ ≤ entry M 0 j) :
    P M = P (M.take j₀) ++ P (M.drop j₀) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M j₀ with
  | h n ih =>
      have hlen : 1 < Lng M := by omega
      by_cases hmulti : multiT M = true
      · have hc := Pcut_props M hlen
        rcases hc with ⟨hcpos, hcle, hanc⟩
        have hcL : Pcut M < Lng M := by omega
        have hcutmin := Pcut_left_min M hM hmulti hlen
        have hjc : j₀ ≤ Pcut M := by
          by_contra hnot
          have hcj : Pcut M < j₀ := by omega
          have hgrowth := ancestor_basic_1 M (Pcut M) j₀ (Lng M - 1)
            hM hcj hjlast hanc
          have hreverse := hmin (Pcut M) hcj
          omega
        have hstep := P_multi_step M hmulti hlen
        have hdrop := P_drop_ancestor M (Pcut M) hM hcpos hcle hanc
        by_cases heq : j₀ = Pcut M
        · subst j₀
          rw [hstep, hdrop]
        · have hjltc : j₀ < Pcut M := lt_of_le_of_ne hjc heq
          let Mp := M.take (Pcut M)
          have hMplen : Lng Mp = Pcut M := by
            simp [Mp, Nat.min_eq_left hcL.le]
          have hMp : TPS Mp := by
            intro hnil
            have : Lng Mp = 0 := by simp [hnil]
            omega
          have hMpmin : ∀ j, j < j₀ → entry Mp 0 j₀ ≤ entry Mp 0 j := by
            intro j hj
            rw [entry_take M (Pcut M) 0 j₀ hjltc,
              entry_take M (Pcut M) 0 j (hj.trans hjltc)]
            exact hmin j hj
          have hIH₁ : P Mp = P (Mp.take j₀) ++ P (Mp.drop j₀) := by
            apply ih (Lng Mp) (by omega) Mp j₀ hMp
            · exact hjpos
            · omega
            · exact hMpmin
            · rfl
          let Ms := M.drop j₀
          have hjL : j₀ < Lng M := by omega
          have hMslen : Lng Ms = Lng M - j₀ := by simp [Ms]
          have hMs : TPS Ms := by
            intro hnil
            have : Lng Ms = 0 := by simp [hnil]
            omega
          let d := Pcut M - j₀
          have hdpos : 0 < d := by simp [d]; omega
          have hdlast : d ≤ Lng Ms - 1 := by simp [d, hMslen]; omega
          have hsum : j₀ + d = Pcut M := by simp [d, Nat.add_sub_of_le hjc]
          have hMsmin : ∀ j, j < d → entry Ms 0 d ≤ entry Ms 0 j := by
            intro j hj
            rw [entry_drop M j₀ 0 d, entry_drop M j₀ 0 j, hsum]
            apply hcutmin
            omega
          have hIH₂ : P Ms = P (Ms.take d) ++ P (Ms.drop d) := by
            apply ih (Lng Ms) (by omega) Ms d hMs hdpos hdlast hMsmin
            rfl
          have ht : Mp.take j₀ = M.take j₀ := by
            simp [Mp, List.take_take, Nat.min_eq_left hjc]
          have hd : Mp.drop j₀ = Ms.take d := by
            simp [Mp, Ms, d, List.drop_take]
          have hdd : Ms.drop d = M.drop (Pcut M) := by
            simp [Ms, d, List.drop_drop, Nat.add_sub_of_le hjc]
          calc
            P M = P Mp ++ [M.drop (Pcut M)] := hstep
            _ = (P (M.take j₀) ++ P (Ms.take d)) ++ [M.drop (Pcut M)] := by
              rw [hIH₁, ht, hd]
            _ = P (M.take j₀) ++
                (P (Ms.take d) ++ P (M.drop (Pcut M))) := by
              rw [hdrop]
              simp only [List.append_assoc]
            _ = P (M.take j₀) ++ P Ms := by rw [hIH₂, hdd]
      · have hnm : multiT M = false := by simpa using hmulti
        have hgrowth := (multi_criterion_12 M hM).mp hnm j₀ hjpos (by omega)
        have hreverse := hmin 0 hjpos
        omega

theorem take_eq_seg (M : PS) (j₀ : ℕ)
    (hjpos : 0 < j₀) (hjlast : j₀ ≤ Lng M - 1) :
    M.take j₀ = seg M 0 (j₀ - 1) := by
  apply List.ext_getElem
  · have hjle : j₀ ≤ Lng M := by omega
    have hpred : j₀ - 1 + 1 = j₀ := by omega
    simp [seg, Nat.min_eq_left hjle, hpred]
  · intro j hj₁ hj₂
    have hjmin : j < min j₀ (Lng M) := by simpa only [List.length_take] using hj₁
    have hjbounds : j < j₀ ∧ j < Lng M := Nat.lt_min.mp hjmin
    simp [seg, List.getElem_range', entry, hjbounds.2]

theorem P_additivity (M : PS) (j₀ : ℕ) (hM : TPS M)
    (hjpos : 0 < j₀) (hjlast : j₀ ≤ Lng M - 1)
    (hmin : ∀ j, j < j₀ → entry M 0 j₀ ≤ entry M 0 j) :
    P M = P (seg M 0 (j₀ - 1)) ++ P (seg M j₀ (Lng M - 1)) := by
  rw [← take_eq_seg M j₀ hjpos hjlast,
    ← drop_eq_seg M j₀ (by omega)]
  exact P_additive_take_drop M j₀ hM hjpos hjlast hmin

#print axioms P_additivity
#print axioms PAux_stable
#print axioms P_multi_step

end PSS
