import «5».«5.1-parent-basic»
import «6».«6.4-P-leftend-mono»

/-!
# §6.4 命題（切片の単項成分と `<^Next` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_mono_slice_next`
- 訂正: なし
- Isabelle: `m_6_4_mono_slice_next`
- 依存: `6.4-P-leftend-mono`, §5.1
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem parent_eq_of_nextR0 (M : PS) (p k : ℕ)
    (hp : nextR M 0 p k = true) : parent M 0 k = p := by
  have hp0 : nextrel0 M p k = true := by simpa [nextR] using hp
  have hpL : p < Lng M := by
    have hh := hp0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.1
  have huniq : ∃! q, nextR M 0 q k = true :=
    ⟨p, hp, fun q hq => row0_parent_unique M q p k hq hp⟩
  have hhas : hasParent M 0 k = true :=
    (hasParent_iff_unique_fseq M 0 k).mpr huniq
  have hlen : (parents M 0 k).length = 1 := by
    simpa [hasParent] using hhas
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp hlen
  have hpmem : p ∈ parents M 0 k := by simp [parents, hpL, hp]
  have hpq : p = q := by simpa [hq] using hpmem
  simp [parent, hq, hpq]

theorem mono_slice_next (M : PS) (j₀ J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hj₀pos : 0 < j₀) (hj₀ : j₀ ≤ Lng M - 1)
    (hJ : J ≤ (P (seg M j₀ (Lng M - 1))).length - 1) :
    hasParent M 0 (j₀ + (IdxSum (P (seg M j₀ (Lng M - 1)))).getD J 0) = true ∧
      parent M 0 (j₀ + (IdxSum (P (seg M j₀ (Lng M - 1)))).getD J 0) < j₀ := by
  let N := seg M j₀ (Lng M - 1)
  let Q := P N
  let k := (IdxSum Q).getD J 0
  have hMpos := List.length_pos_of_ne_nil hM
  have hj₀L : j₀ < Lng M := by omega
  have hNlen : Lng N = Lng M - j₀ := by simp [N]; omega
  have hNpos : 0 < Lng N := by rw [hNlen]; omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hQpos := List.length_pos_of_ne_nil (P_nonempty N)
  have hJ' : J ≤ (P N).length - 1 := by simpa [N] using hJ
  have hJLN : J < (P N).length := by omega
  have hJL : J < Q.length := by simpa [Q] using hJLN
  have hlmin := P_leftend_lmin N J hNT (by simpa [Q] using hJL)
  have hkN : k < Lng N := by
    have hpred : Lng N - 1 + 1 = Lng N :=
      Nat.sub_add_cancel (show 1 ≤ Lng N from hNpos)
    simpa [k, Q] using (show (IdxSum (P N)).getD J 0 < Lng N by omega)
  have habsL : j₀ + k < Lng M := by rw [hNlen] at hkN; omega
  have hlminM : ∀ j', j₀ ≤ j' → j' < j₀ + k →
      entry M 0 (j₀ + k) ≤ entry M 0 j' := by
    intro j' hj'₀ hj'k
    let j := j' - j₀
    have hjk : j < k := by simp [j]; omega
    have hjN : j < Lng N := hjk.trans hkN
    have heJ : entry N 0 j = entry M 0 j' := by
      rw [entry_seg M j₀ (Lng M - 1) 0 j hjN]
      congr
      simp [j]
      omega
    have hek : entry N 0 k = entry M 0 (j₀ + k) :=
      entry_seg M j₀ (Lng M - 1) 0 k hkN
    have hh := hlmin.2 j hjk
    change entry N 0 k ≤ entry N 0 j at hh
    rw [hek, heJ] at hh
    exact hh
  have hfull : leR M 0 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hstartlt : entry M 0 0 < entry M 0 (j₀ + k) :=
    ancestor_basic_1 M 0 (j₀ + k) (Lng M - 1) hM
      (by omega) (by omega) hfull
  obtain ⟨p, _, hpk, hp⟩ :=
    parent_exists_1 M 0 (j₀ + k) hM (by omega) habsL hstartlt
  have hparent : parent M 0 (j₀ + k) = p := parent_eq_of_nextR0 M p _ hp
  have hhas : hasParent M 0 (j₀ + k) = true :=
    (hasParent_iff_unique_fseq M 0 _).mpr
      ⟨p, hp, fun q hq => row0_parent_unique M q p _ hq hp⟩
  have hpentry : entry M 0 p < entry M 0 (j₀ + k) := by
    have hh : nextrel0 M p (j₀ + k) = true := by simpa [nextR] using hp
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hpj₀ : p < j₀ := by
    by_contra hnot
    have hj₀p : j₀ ≤ p := Nat.le_of_not_gt hnot
    have := hlminM p hj₀p hpk
    omega
  constructor
  · simpa [N, Q, k] using hhas
  · change parent M 0 (j₀ + k) < j₀
    rw [hparent]
    exact hpj₀

#print axioms mono_slice_next

end PSS
