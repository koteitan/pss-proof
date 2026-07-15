import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-idempotence»

/-!
# §6.6 命題（`P` が簡約性を保つこと）

- 原文: `tmp/content.md` の「命題（簡約性の切片と基本列への遺伝性）」
- 訂正: なし
- Isabelle: `m_6_6_Red_P_stable`, `m_6_6_P_reduced`
- 依存: §6.5 `Lng_Red_invariance`, §6.4 `P_IdxSum`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-- 各ブロックの長さが固定されていれば、連結結果からブロック列を復元できる。 -/
private theorem flatten_eq_of_map_length_eq {alpha : Type}
    (xs ys : List (List alpha))
    (hflat : xs.flatten = ys.flatten)
    (hlen : xs.map List.length = ys.map List.length) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hxylen : x.length = y.length := by
            injection hlen
          have htaillen : xs.map List.length = ys.map List.length := by
            injection hlen
          have hxyeq : x = y := by
            have htake := congrArg (List.take x.length) hflat
            simpa [hxylen] using htake
          subst y
          have htailflat : xs.flatten = ys.flatten := by
            exact List.append_cancel_left hflat
          rw [ih ys htailflat htaillen]

private theorem P_member_TPS_pr (M Q : PS) (hM : TPS M)
    (hQ : Q ∈ P M) : TPS Q := by
  obtain ⟨J, hJ, hget⟩ := List.mem_iff_getElem.mp hQ
  have hpos := P_component_nonempty M J hM hJ
  have heq : (P M).getD J [] = Q := by
    rw [getD_eq_getElem_idx (P M) [] hJ]
    exact hget
  rw [heq] at hpos
  exact List.ne_nil_of_length_pos hpos

private theorem Red_multi_pr (M : PS) (hM : TPS M)
    (hmulti : multiT M = true) : Red M = (P M).flatMap Red := by
  have hz : zeroT M ≠ true := by
    intro hz
    simp [multiT, hz] at hmulti
  unfold Red
  rw [RedAux, if_neg hz, if_pos hmulti]
  apply List.flatMap_congr
  intro Q hQ
  have hQT := P_member_TPS_pr M Q hM hQ
  apply RedAux_stable Q hQT (nu M)
  exact nu_Pblock_lt M Q hM hmulti hQ

/-- 簡約形の `P` ブロックは `Red` で固定される。 -/
theorem Red_P_stable (M : PS) (hM : TPS M)
    (hred : Red M = M) (J : ℕ) (hJ : J < (P M).length) :
    Red ((P M).getD J []) = (P M).getD J [] := by
  by_cases hmulti : multiT M = true
  · have hflat : ((P M).map Red).flatten = (P M).flatten := by
      change (P M).flatMap Red = (P M).flatten
      calc
        (P M).flatMap Red = Red M := (Red_multi_pr M hM hmulti).symm
        _ = M := hred
        _ = (P M).flatten := (P_concat M).symm
    have hlen : ((P M).map Red).map Lng = (P M).map Lng := by
      rw [List.map_map]
      apply List.map_congr_left
      intro Q hQ
      simp only [Function.comp_apply]
      exact Lng_Red_invariance Q (P_member_TPS_pr M Q hM hQ)
    have hblocks : (P M).map Red = P M :=
      flatten_eq_of_map_length_eq ((P M).map Red) (P M) hflat hlen
    have hget := congrArg (fun Q : List PS => Q.getD J []) hblocks
    have hmapget : ((P M).map Red).getD J [] =
        Red ((P M).getD J []) := by
      rw [getD_eq_getElem_idx ((P M).map Red) [] (by simpa using hJ),
        getD_eq_getElem_idx (P M) [] hJ]
      simp
    exact hmapget.symm.trans hget
  · have hmulti' : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
    have hP := P_nonmulti_eq M hmulti'
    have hJ0 : J = 0 := by simpa [hP] using hJ
    subst J
    simpa [hP] using hred

/-- `M` が簡約であることと、その全 `P` ブロックが簡約であることは同値。 -/
theorem RTPS_iff_P_components (M : PS) (hM : TPS M) :
    RTPS M ↔
      ∀ J, J < (P M).length → RTPS ((P M).getD J []) := by
  constructor
  · intro hR J hJ
    have hQT : TPS ((P M).getD J []) :=
      List.ne_nil_of_length_pos (P_component_nonempty M J hM hJ)
    have hfix := Red_P_stable M hM (Red_eq_self_of_RTPS M hR) J hJ
    have hpair : (P M).getD J [] ≠ [] ∧
        Red ((P M).getD J []) = (P M).getD J [] := ⟨hQT, hfix⟩
    simpa [RTPS, reduced] using hpair
  · intro hblocks
    have hfix : Red M = M := by
      by_cases hmulti : multiT M = true
      · have hblockeq : (P M).map Red = P M := by
          apply List.ext_getElem
          · simp
          · intro J hJL hJR
            have hJ : J < (P M).length := by simpa using hJR
            have hRJ := Red_eq_self_of_RTPS ((P M).getD J [])
              (hblocks J hJ)
            rw [getD_eq_getElem_idx (P M) [] hJ] at hRJ
            simpa only [List.getElem_map] using hRJ
        have hflat : (P M).flatMap Red = (P M).flatten := by
          change ((P M).map Red).flatten = (P M).flatten
          rw [hblockeq]
        calc
          Red M = (P M).flatMap Red := Red_multi_pr M hM hmulti
          _ = (P M).flatten := hflat
          _ = M := P_concat M
      · have hmulti' : multiT M = false := Bool.eq_false_of_not_eq_true hmulti
        have hP := P_nonmulti_eq M hmulti'
        have hPpos : 0 < (P M).length := by simp [hP]
        have hR := hblocks 0 hPpos
        simpa [hP] using Red_eq_self_of_RTPS ((P M).getD 0 []) hR
    have hpair : M ≠ [] ∧ Red M = M := ⟨hM, hfix⟩
    simpa [RTPS, reduced] using hpair

#print axioms Red_P_stable
#print axioms RTPS_iff_P_components

end PSS
