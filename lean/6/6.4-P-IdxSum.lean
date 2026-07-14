import «6».«6.2-P-fseq»
import «6».«6.3-adm-slice»

/-!
# §6.4 命題（`P` と `IdxSum` の関係）

- 原文: `isabelle/pss_paper.thy` の `p_6_4_P_IdxSum`
- 訂正: なし
- Isabelle: `m_6_4_P_IdxSum`
- 依存: `6.2-P-fseq`, `6.3-adm-slice`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

theorem getD_eq_getElem_idx {α : Type} (l : List α) (d : α)
    {n : ℕ} (hn : n < l.length) : l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rfl

theorem idxSum_getD (Q : List PS) (J : ℕ) (hJ : J ≤ Q.length) :
    (IdxSum Q).getD J 0 = ((Q.take J).map Lng).sum := by
  have hidx : J < (IdxSum Q).length := by simp [IdxSum]; omega
  rw [getD_eq_getElem_idx (IdxSum Q) 0 hidx]
  simp [IdxSum, List.getElem_map, List.getElem_range]

theorem idxSum_diff (Q : List PS) (J : ℕ) (hJ : J < Q.length) :
    (IdxSum Q).getD (J + 1) 0 =
      (IdxSum Q).getD J 0 + Lng (Q.getD J []) := by
  rw [idxSum_getD Q (J + 1) (by omega), idxSum_getD Q J hJ.le]
  have hget : Q.getD J [] = Q[J] := getD_eq_getElem_idx Q [] hJ
  have htake : Q.take (J + 1) = Q.take J ++ [Q.getD J []] := by
    rw [List.take_succ]
    simp [List.getElem?_eq_getElem hJ, hget]
  rw [htake]
  simp

private theorem flatten_block (Q : List PS) (J : ℕ) (hJ : J < Q.length) :
    Q.getD J [] =
      (Q.flatten.drop (((Q.take J).map Lng).sum)).take (Lng (Q.getD J [])) := by
  have hget : Q.getD J [] = Q[J] := getD_eq_getElem_idx Q [] hJ
  have hdrop : Q.drop J = Q.getD J [] :: Q.drop (J + 1) := by
    rw [List.drop_eq_getElem_cons hJ, hget]
  have hdecomp : Q.flatten = (Q.take J).flatten ++
      Q.getD J [] ++ (Q.drop (J + 1)).flatten := by
    calc
      Q.flatten = (Q.take J ++ Q.drop J).flatten := by
        congr 1
        exact (List.take_append_drop J Q).symm
      _ = (Q.take J).flatten ++ (Q.drop J).flatten := List.flatten_append
      _ = (Q.take J).flatten ++
          (Q.getD J [] ++ (Q.drop (J + 1)).flatten) := by rw [hdrop]; simp
      _ = (Q.take J).flatten ++ Q.getD J [] ++
          (Q.drop (J + 1)).flatten := by simp [List.append_assoc]
  have hlen : Lng (Q.take J).flatten = ((Q.take J).map Lng).sum := by
    simp [List.length_flatten]
  rw [hdecomp, ← hlen]
  simp

theorem P_component_nonempty (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J < (P M).length) : 0 < Lng ((P M).getD J []) := by
  have hget : (P M).getD J [] = (P M)[J] :=
    getD_eq_getElem_idx (P M) [] hJ
  have hmem : (P M).getD J [] ∈ P M := by
    rw [hget]
    exact List.getElem_mem hJ
  rcases P_components_nonmulti M hM ((P M).getD J []) hmem with hz | hm
  · have hlen : Lng ((P M).getD J []) = 1 := by
      have hh := hz
      simp [zeroT] at hh
      exact hh.1
    omega
  · have hh := hm
    simp only [monoT, Bool.and_eq_true] at hh
    have hle := hh.2
    have hle0 : le0 ((P M).getD J []) 0
        (Lng ((P M).getD J []) - 1) = true := by simpa [leR] using hle
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hle0
    exact hle0.1.1

theorem P_IdxSum (M : PS) (J : ℕ) (hM : TPS M)
    (hJ : J ≤ (P M).length - 1) :
    (P M).getD J [] = seg M
      ((IdxSum (P M)).getD J 0)
      ((IdxSum (P M)).getD (J + 1) 0 - 1) := by
  let Q := P M
  have hQne : Q ≠ [] := P_nonempty M
  have hJQ : J ≤ Q.length - 1 := by simpa [Q] using hJ
  have hJL : J < Q.length := by
    have hQpos := List.length_pos_of_ne_nil hQne
    omega
  let a := (IdxSum Q).getD J 0
  let len := Lng (Q.getD J [])
  let b := (IdxSum Q).getD (J + 1) 0 - 1
  have hdiff : (IdxSum Q).getD (J + 1) 0 = a + len := by
    simpa [a, len] using idxSum_diff Q J hJL
  have hblockQ := flatten_block Q J hJL
  have ha : a = ((Q.take J).map Lng).sum := by
    simpa [a] using idxSum_getD Q J hJL.le
  have hconcat : Q.flatten = M := by simpa [Q] using P_concat M
  have hblock : Q.getD J [] = (M.drop a).take len := by
    simpa [ha, hconcat, len] using hblockQ
  have hlenpos : 0 < len := by
    simpa [Q, len] using P_component_nonempty M J hM (by simpa [Q] using hJL)
  have hlenEq := congrArg Lng hblock
  have habound : a + len ≤ Lng M := by
    simp only [List.length_take, List.length_drop] at hlenEq
    change len = min len (Lng M - a) at hlenEq
    omega
  have hbform : b = a + len - 1 := by
    exact congrArg (fun x => x - 1) hdiff
  have hab : a ≤ b := by rw [hbform]; omega
  have hbM : b < Lng M := by rw [hbform]; omega
  have hseg := seg_eq_take_drop_adm M a b hab hbM
  rw [hseg]
  have hseglen : b + 1 - a = len := by rw [hbform]; omega
  rw [hseglen]
  exact hblock

#print axioms P_IdxSum

end PSS
