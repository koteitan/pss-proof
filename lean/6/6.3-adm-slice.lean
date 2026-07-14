import PSS.Adm
import «6».«6.2-P-fseq»

/-!
# §6.3 命題（許容性の切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_3_adm_slice`
- 訂正: なし
- Isabelle: `m_6_3_adm_slice`
- 依存: `PSS.Adm`, `6.2-P-fseq`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem nextrel0_take_adm (M : PS) (n a b : ℕ)
    (hn : n ≤ Lng M) (ha : a < n) (hb : b < n) :
    nextrel0 (M.take n) a b = nextrel0 M a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.length_take, Nat.min_eq_left hn]
  constructor
  · rintro ⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨by omega, by omega⟩, hab⟩, ?_⟩, ?_⟩
    · simpa [entry_take M n 0 a ha, entry_take M n 0 b hb] using he
    · intro k hk
      have hkb : k < b := List.mem_range.mp hk
      have hs := hall k hk
      simpa [entry_take M n 0 b hb,
        entry_take M n 0 k (hkb.trans hb)] using hs
  · rintro ⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hall⟩
    refine ⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, ?_⟩
    · simpa [entry_take M n 0 a ha, entry_take M n 0 b hb] using he
    · intro k hk
      have hkb : k < b := List.mem_range.mp hk
      have hs := hall k hk
      simpa [entry_take M n 0 b hb,
        entry_take M n 0 k (hkb.trans hb)] using hs

private theorem le0Aux_take_fwd_adm (M : PS) (n fuel a b : ℕ)
    (hn : n ≤ Lng M) (hb : b < n)
    (h : le0Aux (M.take n) fuel a b = true) :
    le0Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero => simpa [le0Aux] using h
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · right
        have hpN : p < n := hpb.trans hb
        have hpnext' : nextrel0 M p b = true := by
          simpa only [nextrel0_take_adm M n p b hn hpN hb] using hpnext
        exact ⟨p, hpb, hpnext', ih p hpN hap⟩

private theorem le0Aux_take_bwd_adm (M : PS) (n fuel a b : ℕ)
    (hn : n ≤ Lng M) (hb : b < n)
    (h : le0Aux M fuel a b = true) :
    le0Aux (M.take n) fuel a b = true := by
  induction fuel generalizing b with
  | zero => simpa [le0Aux] using h
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h ⊢
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · exact Or.inl h
      · right
        have hpN : p < n := hpb.trans hb
        have hpnext' : nextrel0 (M.take n) p b = true := by
          simpa only [nextrel0_take_adm M n p b hn hpN hb] using hpnext
        exact ⟨p, hpb, hpnext', ih p hpN hap⟩

theorem le0_take_adm (M : PS) (n a b : ℕ)
    (hn : n ≤ Lng M) (ha : a < n) (hb : b < n) :
    le0 (M.take n) a b = le0 M a b := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hh := h
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq,
      List.length_take, Nat.min_eq_left hn] at hh ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hf := le0Aux_take_fwd_adm M n n a b hn hb hh.2
    exact le0Aux_mono_fseq M n (Lng M) a b hn hf
  · intro h
    have hh := h
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq,
      List.length_take, Nat.min_eq_left hn] at hh ⊢
    refine ⟨⟨ha, hb⟩, ?_⟩
    have hsmall := le0Aux_bound_fseq M (Lng M) a b hh.2
    have ht := le0Aux_take_bwd_adm M n (b + 1) a b hn hb hsmall
    exact le0Aux_mono_fseq (M.take n) (b + 1) n a b (by omega) ht

private theorem nextrel1_take_adm (M : PS) (n a b : ℕ)
    (hn : n ≤ Lng M) (ha : a < n) (hb : b < n) :
    nextrel1 (M.take n) a b = nextrel1 M a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.length_take, Nat.min_eq_left hn]
  constructor
  · rintro ⟨⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hle⟩, hall⟩
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, hab⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [entry_take M n 1 a ha, entry_take M n 1 b hb] using he
    · simpa only [le0_take_adm M n a b hn ha hb] using hle
    · intro k hk
      by_cases hak : a < k
      · by_cases hkle : le0 M k b = true
        · have hkb : k ≤ b := le0_index_fseq hkle
          have hkN : k < n := lt_of_le_of_lt hkb hb
          have hkleT : le0 (M.take n) k b = true := by
            simpa only [le0_take_adm M n k b hn hkN hb] using hkle
          have hs := hall k (List.mem_range.mpr hkN)
          simpa [hak, hkle, hkleT, entry_take M n 1 b hb,
            entry_take M n 1 k hkN] using hs
        · simp [hak, hkle]
      · simp [hak]
  · rintro ⟨⟨⟨⟨⟨ha', hb'⟩, hab⟩, he⟩, hle⟩, hall⟩
    refine ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa [entry_take M n 1 a ha, entry_take M n 1 b hb] using he
    · simpa only [le0_take_adm M n a b hn ha hb] using hle
    · intro k hk
      have hkN : k < n := List.mem_range.mp hk
      have hs := hall k (List.mem_range.mpr (hkN.trans_le hn))
      by_cases hak : a < k
      · by_cases hkle : le0 (M.take n) k b = true
        · have hkleM : le0 M k b = true := by
            simpa only [le0_take_adm M n k b hn hkN hb] using hkle
          simpa [hak, hkle, hkleM, entry_take M n 1 b hb,
            entry_take M n 1 k hkN] using hs
        · simp [hak, hkle]
      · simp [hak]

private theorem nextR1_take_adm (M : PS) (n a b : ℕ)
    (hn : n ≤ Lng M) (ha : a < n) (hb : b < n) :
    nextR (M.take n) 1 a b = nextR M 1 a b := by
  simp [nextR, nextrel1_take_adm M n a b hn ha hb]

private theorem seg_eq_take_drop_adm (M : PS) (s e : ℕ)
    (hse : s ≤ e) (he : e < Lng M) :
    seg M s e = (M.drop s).take (e + 1 - s) := by
  apply List.ext_getElem
  · simp [hse, Nat.min_eq_left (by simp; omega : e + 1 - s ≤ Lng M - s)]
  · intro k hk₁ hk₂
    have hk : k < e + 1 - s := by simpa using hk₁
    have hsk : s + k < Lng M := by omega
    have hget := List.getElem?_eq_getElem (l := M) hsk
    simp [seg, List.getElem_range', entry, hget]

theorem nextR1_seg_adm (M : PS) (s e a b : ℕ)
    (hse : s ≤ e) (he : e < Lng M)
    (ha : a < Lng (seg M s e)) (hb : b < Lng (seg M s e)) :
    nextR (seg M s e) 1 a b = nextR M 1 (s + a) (s + b) := by
  let D := M.drop s
  let len := e + 1 - s
  have hlen : len ≤ Lng D := by
    have hh := Nat.sub_le_sub_right (show e + 1 ≤ Lng M by omega) s
    simpa [len, D] using hh
  have haLen : a < len := by simpa [len] using ha
  have hbLen : b < len := by simpa [len] using hb
  have haD : a < Lng M - s := by
    have : a < Lng D := haLen.trans_le hlen
    simpa [D] using this
  have hbD : b < Lng M - s := by
    have : b < Lng D := hbLen.trans_le hlen
    simpa [D] using this
  calc
    nextR (seg M s e) 1 a b = nextR (D.take len) 1 a b := by
      rw [seg_eq_take_drop_adm M s e hse he]
    _ = nextR D 1 a b := nextR1_take_adm D len a b hlen haLen hbLen
    _ = nextR M 1 (s + a) (s + b) := nextR_drop M s 1 a b haD hbD

theorem leR0_seg_adm (M : PS) (s e a b : ℕ)
    (hse : s ≤ e) (he : e < Lng M)
    (ha : a < Lng (seg M s e)) (hb : b < Lng (seg M s e)) :
    leR (seg M s e) 0 a b = leR M 0 (s + a) (s + b) := by
  let D := M.drop s
  let len := e + 1 - s
  have hlen : len ≤ Lng D := by
    have hh := Nat.sub_le_sub_right (show e + 1 ≤ Lng M by omega) s
    simpa [len, D] using hh
  have haLen : a < len := by simpa [len] using ha
  have hbLen : b < len := by simpa [len] using hb
  have haD : a < Lng M - s := by
    have : a < Lng D := haLen.trans_le hlen
    simpa [D] using this
  have hbD : b < Lng M - s := by
    have : b < Lng D := hbLen.trans_le hlen
    simpa [D] using this
  calc
    leR (seg M s e) 0 a b = leR (D.take len) 0 a b := by
      rw [seg_eq_take_drop_adm M s e hse he]
    _ = leR D 0 a b := by simp [leR, le0_take_adm D len a b hlen haLen hbLen]
    _ = leR M 0 (s + a) (s + b) := leR_drop M s 0 a b haD hbD

theorem adm_slice (M : PS) (s j e : ℕ) (hM : TPS M)
    (hsj : s ≤ j) (hje : j ≤ e) (he : e ≤ Lng M - 1) :
    (adm M j = true ∨ s = j ∨ j = e) ↔
      adm (seg M s e) (j - s) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have heM : e < Lng M := by omega
  let N := seg M s e
  have hNlen : Lng N = e + 1 - s := by simp [N]
  by_cases hboundary : s = j ∨ j = e
  · constructor
    · intro _
      rcases hboundary with hsjEq | hjeEq
      · have hidx0 : j - s = 0 := by omega
        have hnadm : nadm N 0 = false := by
          simp [nadm, nextR, nextrel1]
        change adm N (j - s) = true
        rw [hidx0]
        simp only [adm, hnadm, Bool.not_false]
      · have hidx : j - s = Lng N - 1 := by rw [hNlen]; omega
        have hNpos : 0 < Lng N := by rw [hNlen]; omega
        have hnext : nextR N 1 (j - s) (j - s + 1) = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          have hh : nextrel1 N (j - s) (j - s + 1) = true := by
            simpa [nextR] using ht
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
          omega
        have hnotgt : ¬ Lng N < j - s := by omega
        have hnadm : nadm N (j - s) = false := by
          simp [nadm, hnext, hnotgt]
        change adm N (j - s) = true
        simp only [adm, hnadm, Bool.not_false]
    · intro _
      exact Or.inr hboundary
  · have hsj' : s < j := by omega
    have hje' : j < e := by omega
    have hse : s ≤ e := hsj.trans hje
    have h₁a : j - s - 1 < Lng N := by rw [hNlen]; omega
    have h₁b : j - s < Lng N := by rw [hNlen]; omega
    have h₂b : j - s + 1 < Lng N := by rw [hNlen]; omega
    have hc₁ := nextR1_seg_adm M s e (j - s - 1) (j - s)
      hse heM h₁a h₁b
    have hc₂ := nextR1_seg_adm M s e (j - s) (j - s + 1)
      hse heM h₁b h₂b
    have hs₁ : s + (j - s - 1) = j - 1 := by omega
    have hs₂ : s + (j - s) = j := by omega
    have hs₃ : s + (j - s + 1) = j + 1 := by omega
    have hc₁' : nextR N 1 (j - s - 1) (j - s) =
        nextR M 1 (j - 1) j := by simpa [N, hs₁, hs₂] using hc₁
    have hc₂' : nextR N 1 (j - s) (j - s + 1) =
        nextR M 1 j (j + 1) := by simpa [N, hs₂, hs₃] using hc₂
    simp only [hboundary, or_false]
    change adm M j = true ↔ adm N (j - s) = true
    have hjM : j ≤ Lng M := by omega
    have hjN : j - s ≤ Lng N := by rw [hNlen]; omega
    simp [adm, nadm, hjM, hjN, hc₁', hc₂']

#print axioms adm_slice

end PSS
