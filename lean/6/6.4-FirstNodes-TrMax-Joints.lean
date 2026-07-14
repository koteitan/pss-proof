import «6».«6.4-mono-slice-next»

/-!
# §6.4 命題（`FirstNodes` と `TrMax` と `Joints` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_FirstNodes_TrMax_Joints`
- 訂正: 枝が空のときの自然数減算を避け、`J < (Br M).length` とする
- Isabelle: `m_6_4_FirstNodes_TrMax_Joints`
- 依存: `6.4-mono-slice-next`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem TrMax_bound (M : PS) (hM : TPS M) : TrMax M ≤ Lng M - 1 := by
  have hMpos := List.length_pos_of_ne_nil hM
  unfold TrMax
  cases hfind : (List.range (Lng M)).find? (fun j => !nextR M 1 j (j + 1)) with
  | none => simp
  | some j =>
      have hjmem := List.mem_of_find?_eq_some hfind
      have hjL : j < Lng M := by simpa using hjmem
      simp [hfind]
      omega

theorem FirstNodes_getD (M : PS) (J : ℕ) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 =
      TrMax M + 1 + (IdxSum (Br M)).getD J 0 := by
  have hI : J < (IdxSum (Br M)).length := by simp [IdxSum]; omega
  have hF : J < (FirstNodes M).length := by simp [FirstNodes, IdxSum]; omega
  rw [getD_eq_getElem_idx (FirstNodes M) 0 hF,
    getD_eq_getElem_idx (IdxSum (Br M)) 0 hI]
  simp [FirstNodes, List.getElem_map]

theorem Joints_getD (M : PS) (J : ℕ) (hJ : J < (Br M).length) :
    (Joints M).getD J 0 = parent M 0 ((FirstNodes M).getD J 0) := by
  have hK : J < (Joints M).length := by simp [Joints]; omega
  rw [getD_eq_getElem_idx (Joints M) 0 hK]
  simp [Joints, List.getElem_map]

theorem FirstNodes_TrMax_Joints (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) :
    (Joints M).getD J 0 ≤ TrMax M ∧
      TrMax M < (FirstNodes M).getD J 0 := by
  have hbound := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have : Br M = [] := by simp [Br, heq]
    rw [this] at hJ
    simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
    simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]
    omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono
    (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  have hjoint := Joints_getD M J hJ
  constructor
  · rw [hjoint, hfn, hBr]
    omega
  · rw [hfn]
    omega

#print axioms FirstNodes_TrMax_Joints

end PSS
