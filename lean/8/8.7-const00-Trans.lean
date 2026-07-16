import «6».«6.6-reduced-iff-condAB»
import «7».«7.3-Trans-welldefined»

/-!
# §8.7 補題（公差 `(0,0)` のペア数列の `Trans` の基本性質）

- 原文: `tmp/content.md` L5857 付近（「補題（公差\((0,0)\)のペア数列の\(\textrm{Trans}\)の基本性質）」）
- 訂正: なし
- Isabelle: `p_8_7_const00_Trans` (isabelle/pss_paper.thy:2243) の証明は
            `m_8_7_const00_Trans` / `m_8_7_cnst_Trans` (isabelle/layerB/pss_wip.thy:16005)
- 依存: «6».«6.6-reduced-iff-condAB», «7».«7.3-Trans-welldefined»
- 状態: ✅ 証明済（sorry 0）

定数列 `((u,u))_{j=0}^{j₁}` は両行とも定数なので親子辺を全く持たず、`j₁ > 0` では複項。
`Trans` の複項分岐が 1 列ずつ `D_u 0` を積み上げ、`(D_u 0) ×_B (j₁+1)`（`u = 0` では
左端の `(0,0)` が `0` を寄与するので `(D_0 0) ×_B j₁`）になる。
-/

namespace PSS

/-- 公差 `(0,0)` の定数列 `((u,u))_{j=0}^{j₁} = replicate (j₁+1) (u,u)`。 -/
private def cnst (u j₁ : ℕ) : PS := List.replicate (j₁ + 1) (u, u)

private theorem Lng_cnst (u j₁ : ℕ) : Lng (cnst u j₁) = j₁ + 1 := by
  simp [cnst]

private theorem TPS_cnst (u j₁ : ℕ) : TPS (cnst u j₁) := by
  simp [TPS, cnst]

private theorem entry_cnst (u j₁ i j : ℕ) (hj : j < j₁ + 1) :
    entry (cnst u j₁) i j = u := by
  simp [entry, cnst, hj]

/-! 定数列はどの行にも親子辺を持たない（両行とも狭義増加が不可能）。 -/

private theorem nextrel0_cnst (u j₁ a b : ℕ) :
    nextrel0 (cnst u j₁) a b = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨haL, hbL⟩, -⟩, hlt⟩, -⟩ := h
  rw [Lng_cnst] at haL hbL
  rw [entry_cnst u j₁ 0 a haL, entry_cnst u j₁ 0 b hbL] at hlt
  omega

private theorem nextrel1_cnst (u j₁ a b : ℕ) :
    nextrel1 (cnst u j₁) a b = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨haL, hbL⟩, -⟩, hlt⟩, -⟩, -⟩ := h
  rw [Lng_cnst] at haL hbL
  rw [entry_cnst u j₁ 1 a haL, entry_cnst u j₁ 1 b hbL] at hlt
  omega

private theorem nextR_cnst (u j₁ i a b : ℕ) :
    nextR (cnst u j₁) i a b = false := by
  by_cases hi : i = 0 <;> simp [nextR, hi, nextrel0_cnst, nextrel1_cnst]

private theorem hasParent_cnst (u j₁ i j : ℕ) :
    hasParent (cnst u j₁) i j = false := by
  have hnil : parents (cnst u j₁) i j = [] := by
    unfold parents
    simp [nextR_cnst]
  simp [hasParent, hnil]

/-! 簡約性: 親が無いので条件(A)は空虚に、条件(B)は両行が等しいので成立。 -/

private theorem RedCondA_cnst (u j₁ : ℕ) : RedCondA (cnst u j₁) = true := by
  simp [RedCondA, hasParent_cnst]

private theorem RedCondB_cnst (u j₁ : ℕ) : RedCondB (cnst u j₁) = true := by
  simp only [RedCondB, List.all_eq_true, List.mem_range]
  intro j hj
  rw [Lng_cnst] at hj
  have hjL : j < j₁ + 1 := by omega
  simp [hasParent_cnst, entry_cnst u j₁ 0 j hjL, entry_cnst u j₁ 1 j hjL]

private theorem RTPS_cnst (u j₁ : ℕ) : RTPS (cnst u j₁) :=
  RTPS_of_condAB _ (TPS_cnst u j₁) (RedCondA_cnst u j₁) (RedCondB_cnst u j₁)

/-! 行 0 の祖先関係は反射のみ（辺が無い）。従って `j₁ > 0` で複項、`Pcut = j₁`。 -/

private theorem le0Aux_cnst (u j₁ : ℕ) (f a b : ℕ) :
    le0Aux (cnst u j₁) f a b = (a == b) := by
  induction f generalizing a b with
  | zero => rfl
  | succ f ih =>
      have hany : ((List.range b).any fun j =>
          nextrel0 (cnst u j₁) j b && le0Aux (cnst u j₁) f a j) = false := by
        simp [nextrel0_cnst]
      simp only [le0Aux]
      rw [hany, Bool.or_false]

private theorem leR0_cnst_eq (u j₁ a b : ℕ)
    (h : leR (cnst u j₁) 0 a b = true) : a = b := by
  have h' : le0 (cnst u j₁) a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true] at h'
  have haux := h'.2
  rw [le0Aux_cnst] at haux
  exact beq_iff_eq.mp haux

private theorem multiT_cnst (u k : ℕ) : multiT (cnst u (k + 1)) = true := by
  have hz : zeroT (cnst u (k + 1)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, -⟩ := h
    rw [Lng_cnst] at h1
    omega
  have hm : monoT (cnst u (k + 1)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [monoT, Bool.and_eq_true] at h
    have hle := h.2
    have := leR0_cnst_eq u (k + 1) _ _ hle
    rw [Lng_cnst] at this
    omega
  simp [multiT, hz, hm]

private theorem Pcut_cnst (u k : ℕ) : Pcut (cnst u (k + 1)) = k + 1 := by
  have hlen : 1 < Lng (cnst u (k + 1)) := by rw [Lng_cnst]; omega
  obtain ⟨-, -, hanc⟩ := Pcut_props (cnst u (k + 1)) hlen
  have heq := leR0_cnst_eq u (k + 1) _ _ hanc
  rw [Lng_cnst] at heq
  omega

private theorem take_cnst (u k : ℕ) :
    List.take (k + 1) (cnst u (k + 1)) = cnst u k := by
  show List.take (k + 1) (List.replicate (k + 1 + 1) (u, u)) =
    List.replicate (k + 1) (u, u)
  rw [List.take_replicate, Nat.min_eq_left (by omega : k + 1 ≤ k + 1 + 1)]

private theorem drop_cnst (u k : ℕ) :
    List.drop (k + 1) (cnst u (k + 1)) = [(u, u)] := by
  show List.drop (k + 1) (List.replicate (k + 1 + 1) (u, u)) = [(u, u)]
  rw [List.drop_replicate, show k + 1 + 1 - (k + 1) = 1 by omega,
    List.replicate_one]

/-! 一列の基底値。 -/

private theorem Trans_cnst_zero (u : ℕ) :
    Trans (cnst u 0) = if u = 0 then BZero else Dprin (u : ℕ∞) BZero := by
  have hR : RTPS (cnst u 0) := RTPS_cnst u 0
  have h1 : cnst u 0 = [(u, u)] := rfl
  have hred : reduced [(u, u)] = true := by rw [← h1]; exact hR
  rw [Trans_eq_lengthAux _ hR, h1]
  by_cases hu : u = 0
  · subst hu
    simp [TransAux, hred, lastIdx]
  · have hbeqp : (((u, u) : ℕ × ℕ) == ((0, 0) : ℕ × ℕ)) = false := by
      cases u with
      | zero => exact absurd rfl hu
      | succ k => rfl
    simp [TransAux, hred, lastIdx, entry, hu, hbeqp]

/-! 主計算: `j₁` に関する帰納法。複項分岐が 1 列ずつ `D_u 0` を積む。 -/

private theorem Trans_cnst_key (u j₁ : ℕ) :
    Trans (cnst u j₁) =
      if u = 0 then multBT (Dprin (u : ℕ∞) BZero) j₁
      else multBT (Dprin (u : ℕ∞) BZero) (j₁ + 1) := by
  induction j₁ with
  | zero =>
      rw [Trans_cnst_zero]
      by_cases hu : u = 0
      · subst hu
        simp [multBT]
      · simp [hu, multBT, addBT, BZero, Dprin]
  | succ k ih =>
      have hR : RTPS (cnst u (k + 1)) := RTPS_cnst u (k + 1)
      have hmulti : multiT (cnst u (k + 1)) = true := multiT_cnst u k
      have heq := (Trans_Mark_multi_equations (cnst u (k + 1)) hR hmulti).1
      rw [Pcut_cnst u k, take_cnst u k, drop_cnst u k] at heq
      by_cases hu : u = 0
      · subst hu
        rw [heq]
        simp [ih, multBT]
      · have hbeq : (([(u, u)] : PS) == ([(0, 0)] : PS)) = false := by
          cases u with
          | zero => exact absurd rfl hu
          | succ k => rfl
        rw [hbeq] at heq
        simp only [Bool.false_eq_true, if_false] at heq
        have hsing : Trans [(u, u)] = Dprin (u : ℕ∞) BZero := by
          have h0 := Trans_cnst_zero u
          rw [if_neg hu] at h0
          exact h0
        rw [heq, hsing, ih, if_neg hu, if_neg hu]
        rfl

/-- §8.7 補題（公差 `(0,0)` のペア数列の `Trans` の基本性質、article 5857）:
任意の `u, j₁ ∈ ℕ` に対し `M := ((u,u))_{j=0}^{j₁}` と置くと
`Trans M = (D₀ 0) ×_B j₁`（`u = 0`）／ `(D_u 0) ×_B (j₁+1)`（`u > 0`）。 -/
theorem const00_Trans (u j₁ : ℕ) :
    Trans (List.replicate (j₁ + 1) (u, u)) =
      if u = 0 then multBT (Dprin (u : ℕ∞) BZero) j₁
      else multBT (Dprin (u : ℕ∞) BZero) (j₁ + 1) :=
  Trans_cnst_key u j₁

#print axioms const00_Trans

end PSS
