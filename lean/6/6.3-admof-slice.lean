import «6».«6.3-adm-slice»

/-!
# §6.3 命題（許容化の切片への遺伝性）

- 原文: `isabelle/pss_paper.thy` の `p_6_3_admof_slice`
- 訂正: なし
- Isabelle: `m_6_3_admof_slice`
- 依存: `6.3-adm-slice`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem adm_zero (M : PS) : adm M 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem Adm_find_some (M : PS) (j : ℕ) (hj : adm M j = false) :
    ∃ a, ((List.range j).reverse.find? (fun k => adm M k)) = some a := by
  have hjpos : 0 < j := by
    by_contra heq
    have : j = 0 := by omega
    subst j
    simp [adm_zero] at hj
  cases hf : (List.range j).reverse.find? (fun k => adm M k) with
  | some a => exact ⟨a, rfl⟩
  | none =>
      have hnone := List.find?_eq_none.mp hf 0
        (by simp [List.mem_reverse, hjpos])
      exact False.elim (hnone (adm_zero M))

theorem Adm_adm (M : PS) (j : ℕ) : adm M (Adm M j) = true := by
  by_cases hj : adm M j = true
  · simp [Adm, hj]
  · have hjf : adm M j = false := by simpa using hj
    obtain ⟨a, ha⟩ := Adm_find_some M j hjf
    have haa : adm M a = true := List.find?_some ha
    simp [Adm, hjf, ha, haa]

theorem Adm_le (M : PS) (j : ℕ) : Adm M j ≤ j := by
  by_cases hj : adm M j = true
  · simp [Adm, hj]
  · have hjf : adm M j = false := by simpa using hj
    obtain ⟨a, ha⟩ := Adm_find_some M j hjf
    have hamem := List.mem_of_find?_eq_some ha
    have halt : a < j := by simpa [List.mem_reverse] using hamem
    simp [Adm, hjf, ha]
    omega

theorem Adm_max (M : PS) (k j : ℕ)
    (hkadm : adm M k = true) (hkj : k ≤ j) : k ≤ Adm M j := by
  by_cases hj : adm M j = true
  · simp [Adm, hj, hkj]
  · have hjf : adm M j = false := by simpa using hj
    have hkjlt : k < j := by
      by_contra hnot
      have : k = j := by omega
      subst k
      simp [hkadm] at hjf
    obtain ⟨a, ha⟩ := Adm_find_some M j hjf
    have hfind := List.find?_eq_some_iff_getElem.mp ha
    rcases hfind with ⟨haadm, i, hi, hieq, hbefore⟩
    have hia : j - 1 - i = a := by
      have hrev := List.getElem_reverse (l := List.range j) hi
      rw [hrev, List.getElem_range] at hieq
      simpa using hieq
    have hka : k ≤ a := by
      by_contra hnot
      have hak : a < k := by omega
      let q := j - 1 - k
      have hq : q < (List.range j).reverse.length := by simp [q]; omega
      have hqval : ((List.range j).reverse)[q] = k := by
        rw [List.getElem_reverse]
        simp [q]
        omega
      have hqi : q < i := by simp [q]; omega
      have hfalse := hbefore q hqi
      rw [hqval] at hfalse
      simp [hkadm] at hfalse
    simp [Adm, hjf, ha]
    exact hka

theorem admof_slice (M : PS) (s j e : ℕ) (hM : TPS M)
    (hs : s ≤ Adm M j) (hje : j < e) (he : e ≤ Lng M - 1) :
    Adm (seg M s e) (j - s) = Adm M j - s := by
  let N := seg M s e
  let am := Adm M j
  let aN := Adm N (j - s)
  have hamle : am ≤ j := Adm_le M j
  have hamadm : adm M am = true := Adm_adm M j
  have hsj : s ≤ j := hs.trans hamle
  have hame : am ≤ e := by omega
  have hamN : adm N (am - s) = true := by
    have hiff := adm_slice M s am e hM hs hame he
    exact hiff.mp (Or.inl hamadm)
  have hamj : am - s ≤ j - s := Nat.sub_le_sub_right hamle s
  have hge : am - s ≤ aN := Adm_max N (am - s) (j - s) hamN hamj
  have haNle : aN ≤ j - s := Adm_le N (j - s)
  have haNadm : adm N aN = true := Adm_adm N (j - s)
  have hle : aN ≤ am - s := by
    by_contra hnot
    have hgt : am - s < aN := by omega
    have hsumj : aN + s ≤ j := by omega
    have hsume : aN + s ≤ e := by omega
    have hiff := adm_slice M s (aN + s) e hM (by omega) hsume he
    have hright : adm N ((aN + s) - s) = true := by simpa using haNadm
    have hdisj := hiff.mpr hright
    have hsumadm : adm M (aN + s) = true := by
      rcases hdisj with h | hleft | hright
      · exact h
      · have : aN = 0 := by omega
        omega
      · omega
    have hmax : aN + s ≤ am := Adm_max M (aN + s) j hsumadm hsumj
    omega
  change aN = am - s
  omega

#print axioms admof_slice

end PSS
