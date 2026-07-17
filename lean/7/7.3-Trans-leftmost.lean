import «7».«7.3-Trans-preserves-monoT»
import «7».«7.4-RightNodes-Mark»
import «6».«6.2-P-additivity»

/-!
# §7.3 命題（`Trans` の最左単項成分 / 左端）

- 原文: `tmp/content.md` §7.3 の「最左単項成分」命題（3 節）
- Isabelle:
  - `m_7_3_Trans_leftend`      (`isabelle/layerB/pss_wip.thy:6444`)
  - `m_7_3_Trans_leftmost_pc`  (`isabelle/layerB/pss_wip.thy:16067`)
  - `reduced_e10_zero`         (`isabelle/layerB/pss_wip.thy:6384`)
  - `reduced_P0_zero_e11`      (`isabelle/layerB/pss_wip.thy:16519`)
  - `m_7_3_Trans_leftmost`     (`isabelle/layerB/pss_wip.thy:16569`)
- 依存: `7.3-Trans-preserves-monoT`（`Trans_monoT_principal` / `PB_length_addBT`）、
  `7.4-RightNodes-Mark`（`Trans_mono_leftend_form` ＝ Isabelle の単項枝の外科手術部分を
  既に済ませたもの）、`7.3-Trans-welldefined`（`Trans_Mark_multi_equations`,
  `trans_multi_prefix_RTPS`）、`6.2-P-additivity`（`Pcut_props` / `Pcut_left_min` /
  `entry_take` / `entry_drop` / `P_multi_step`）。
- 訂正: なし（すべて `RTPS` 上の主張。Isabelle と 1:1）。
- 状態: ✅ sorry 0 / 仮定 0。

Isabelle の `m_7_3_Trans_leftend` は単項枝で `trans_inv_B_hard` の外科手術設定を
100 行ほど展開して `bpHeadV` の保存を示すが、Lean 側では `Trans_mono_leftend_form`
（`7.4-RightNodes-Mark`）が既に `Trans M = D_{M_{1,0}} t` の閉じた形を与えているので、
その枝は 2 行で済む。
-/

namespace PSS

/-! ## `bpHeadV` / `PB` と `+_B` の基本補題 -/

/-- `0_B +_B b = b`。 -/
private theorem addBT_zero_left_tl (b : BT) : addBT BZero b = b := by
  cases b with
  | trm bs => simp [addBT, BZero]

/-- `a ≠ 0_B` なら `+_B` の左端指標は左被演算子のもの。
Isabelle `m_7_3_Trans_leftend` の `headAdd`。 -/
private theorem bpHeadV_addBT_left_tl (a b : BT) (ha : a ≠ BZero) :
    bpHeadV (addBT a b) = bpHeadV a := by
  cases a with
  | trm as =>
    cases b with
    | trm bs =>
      cases as with
      | nil => exact absurd rfl ha
      | cons p ps =>
        cases p with
        | db v t => simp [addBT, bpHeadV]

/-- `a ≠ 0_B` なら `+_B` の最左単項成分は左被演算子のもの。
Isabelle `PB0_addBT_left` (`pss_wip.thy:16040`)。 -/
private theorem PB0_addBT_left_tl (a b : BT) (ha : a ≠ BZero) :
    (PB (addBT a b)).getD 0 BZero = (PB a).getD 0 BZero := by
  cases a with
  | trm as =>
    cases b with
    | trm bs =>
      cases as with
      | nil => exact absurd rfl ha
      | cons p ps => simp [addBT, PB, untrm]

/-- 単項（`Lng (PB t) = 1`）なら最左単項成分は `t` 自身。
Isabelle `PB0_principal` (`pss_wip.thy:16052`)。 -/
private theorem PB0_principal_tl (t : BT) (h : (PB t).length = 1) :
    (PB t).getD 0 BZero = t := by
  cases t with
  | trm ps =>
    have hlen : ps.length = 1 := by simpa [PB, untrm] using h
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
    simp [PB, untrm]

/-! ## 簡約形の左端 -/

/-- Isabelle `reduced_e10_zero` (`pss_wip.thy:6384`):
簡約形で上段左端が `0` なら下段左端も `0`。 -/
private theorem reduced_e10_zero_tl (M : PS) (hR : RTPS M)
    (he00 : entry M 0 0 = 0) : entry M 1 0 = 0 := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      by_cases hz : zeroT M = true
      · simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
        exact hz.2
      · have hz' : zeroT M = false := by simpa using hz
        by_cases hmono : monoT M = true
        · rw [← RTPS_mono_head_eq M hR hmono]
          exact he00
        · have hmulti : multiT M = true := by simp [multiT, hz', hmono]
          have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
          obtain ⟨hcpos, hcle, _⟩ := Pcut_props M hlen
          have hcL : Pcut M < Lng M := by omega
          have hAR : RTPS (M.take (Pcut M)) := trans_multi_prefix_RTPS M hR hmulti
          have hAlen : Lng (M.take (Pcut M)) = Pcut M := by
            simp [Nat.min_eq_left hcL.le]
          have hAlt : Lng (M.take (Pcut M)) < n := by
            rw [hAlen, ← hn]; omega
          have hA00 : entry (M.take (Pcut M)) 0 0 = 0 := by
            rw [entry_take M (Pcut M) 0 0 (by omega)]; exact he00
          have hIH := ih (Lng (M.take (Pcut M))) hAlt (M.take (Pcut M)) hAR hA00 rfl
          rwa [entry_take M (Pcut M) 1 0 (by omega)] at hIH

/-! ## 左端の核（clause (1)(2)(3) 共通） -/

/-- Isabelle `m_7_3_Trans_leftend` (`pss_wip.thy:6444`):
`Trans M` の左端指標は `M_{1,0}`（零項では両辺 `0`）。 -/
theorem m_7_3_Trans_leftend (M : PS) (hR : RTPS M) :
    bpHeadV (Trans M) = (entry M 1 0 : ℕ∞) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      by_cases hz : zeroT M = true
      · have hzt : Trans M = BZero := (Trans_preserves_zeroT M hM).1 hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
        rw [hzt, hz.2]
        simp [bpHeadV, BZero]
      · have hz' : zeroT M = false := by simpa using hz
        by_cases hmono : monoT M = true
        · rcases Trans_mono_leftend_form M hR hmono with hzero | ⟨t, ht⟩
          · exfalso
            have hzz := (Trans_preserves_zeroT M hM).2 hzero
            rw [hz'] at hzz
            exact Bool.noConfusion hzz
          · rw [ht]
            simp [bpHeadV, Dprin]
        · -- 複項枝
          have hmulti : multiT M = true := by simp [multiT, hz', hmono]
          have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
          obtain ⟨hcpos, hcle, _⟩ := Pcut_props M hlen
          have hcL : Pcut M < Lng M := by omega
          let A := M.take (Pcut M)
          let J := M.drop (Pcut M)
          have hAR : RTPS A := by
            simpa [A] using trans_multi_prefix_RTPS M hR hmulti
          have hJR : RTPS J := by
            have hlast := (trans_multi_last_component M hM hmulti).1
            have hPne : P M ≠ [] := P_nonempty M
            have hidx : (P M).length - 1 < (P M).length := by
              have := List.length_pos_of_ne_nil hPne
              omega
            have hh := (RTPS_iff_P_components M hM).1 hR ((P M).length - 1) hidx
            dsimp [J]
            rw [← hlast]
            exact hh
          have hAlen : Lng A = Pcut M := by
            simp [A, Nat.min_eq_left hcL.le]
          have hJlen : Lng J = Lng M - Pcut M := by
            simp only [J, Lng, List.length_drop]
          have hAlt : Lng A < n := by rw [hAlen, ← hn]; omega
          have hJlt : Lng J < n := by rw [hJlen, ← hn]; omega
          have hA10 : entry A 1 0 = entry M 1 0 :=
            entry_take M (Pcut M) 1 0 (by omega)
          have heq := (Trans_Mark_multi_equations M hR hmulti).1
          by_cases hTA : Trans A = BZero
          · -- `Trans A = 0_B`: `A` は零項なので `M_{1,0} = 0`、右側の左端も `0`
            have hzA : zeroT A = true :=
              (Trans_preserves_zeroT A (RTPS_TPS A hAR)).2 hTA
            have hzA' := hzA
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzA'
            have hM10 : entry M 1 0 = 0 := by rw [← hA10]; exact hzA'.2
            -- `A = [(0,0)]` なので上段左端も `0`
            have hA1 : Lng A = 1 := hzA'.1
            obtain ⟨w, hw⟩ := (one_column A (RTPS_TPS A hAR)).1 ⟨hA1, hAR⟩
            have hw0 : w = 0 := by
              have : entry A 1 0 = w := by simp [hw, entry]
              rw [this] at hzA'
              exact hzA'.2
            have hA00 : entry A 0 0 = 0 := by simp [hw, hw0, entry]
            have hM00 : entry M 0 0 = 0 := by
              rw [← entry_take M (Pcut M) 0 0 (by omega)]
              exact hA00
            -- 切断の左極小性から `M_{0,Pcut M} = 0`
            have hcut00 : entry M 0 (Pcut M) = 0 := by
              have hmin := Pcut_left_min M hM hmulti hlen 0 (by omega)
              omega
            have hJ00 : entry J 0 0 = 0 := by
              rw [show J = M.drop (Pcut M) from rfl, entry_drop M (Pcut M) 0 0]
              simpa using hcut00
            have hJ10 : entry J 1 0 = 0 := reduced_e10_zero_tl J hJR hJ00
            by_cases hJzero : J = [(0, 0)]
            · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
                simpa [A, J, hJzero] using heq
              rw [hTrans, hTA, addBT_zero_left_tl, hM10]
              simp [bpHeadV, Dprin]
            · have hTrans : Trans M = addBT (Trans A) (Trans J) := by
                simpa [A, J, hJzero] using heq
              have hIHJ := ih (Lng J) hJlt J hJR rfl
              rw [hTrans, hTA, addBT_zero_left_tl, hIHJ, hJ10, hM10]
          · -- `Trans A ≠ 0_B`: 左端は左被演算子から読む
            have hIHA := ih (Lng A) hAlt A hAR rfl
            by_cases hJzero : J = [(0, 0)]
            · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
                simpa [A, J, hJzero] using heq
              rw [hTrans, bpHeadV_addBT_left_tl _ _ hTA, hIHA, hA10]
            · have hTrans : Trans M = addBT (Trans A) (Trans J) := by
                simpa [A, J, hJzero] using heq
              rw [hTrans, bpHeadV_addBT_left_tl _ _ hTA, hIHA, hA10]

/-! ## 最左単項成分 -/

/-- Isabelle `m_7_3_Trans_leftmost_pc` (`pss_wip.thy:16067`):
先頭 `P` 成分が `((0,0))` でない簡約形では、`Trans M` の最左単項成分は
`Trans (P(M)_0)` に一致する。 -/
theorem m_7_3_Trans_leftmost_pc (M : PS) (hR : RTPS M)
    (hP0 : (P M).getD 0 [] ≠ [(0, 0)]) :
    (PB (Trans M)).getD 0 BZero = Trans ((P M).getD 0 []) := by
  generalize hn : Lng M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      have hM : TPS M := RTPS_TPS M hR
      by_cases hz : zeroT M = true
      · -- 零項は簡約形では `[(0,0)]`、`P M = [M]` なので仮定に反する（空虚）
        exfalso
        apply hP0
        have hz' := hz
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz'
        obtain ⟨v, hv⟩ := (one_column M hM).1 ⟨hz'.1, hR⟩
        have hv0 : v = 0 := by
          have hev : entry M 1 0 = v := by simp [hv, entry]
          rw [hev] at hz'
          exact hz'.2
        rw [P_nonmulti_eq M (by simp [multiT, hz])]
        simp [hv, hv0]
      · have hz' : zeroT M = false := by simpa using hz
        by_cases hmono : monoT M = true
        · -- 単項枝: `P M = [M]` かつ `Trans M` は単項
          have hPM : P M = [M] := P_nonmulti_eq M (by simp [multiT, hmono])
          have hP0M : (P M).getD 0 [] = M := by simp [hPM]
          have htne : Trans M ≠ BZero := by
            intro h
            have hzz := (Trans_preserves_zeroT M hM).2 h
            rw [hz'] at hzz
            exact Bool.noConfusion hzz
          obtain ⟨p, hp⟩ := Trans_monoT_principal M hR hmono htne
          rw [hP0M]
          apply PB0_principal_tl
          simp [hp, PB, untrm]
        · -- 複項枝: 最左単項成分は前半 `A` に再帰する
          have hmulti : multiT M = true := by simp [multiT, hz', hmono]
          have hlen : 1 < Lng M := multi_length_fseq M hM hmulti
          obtain ⟨hcpos, hcle, _⟩ := Pcut_props M hlen
          have hcL : Pcut M < Lng M := by omega
          let A := M.take (Pcut M)
          let J := M.drop (Pcut M)
          have hAR : RTPS A := by
            simpa [A] using trans_multi_prefix_RTPS M hR hmulti
          have hAlen : Lng A = Pcut M := by
            simp [A, Nat.min_eq_left hcL.le]
          have hAlt : Lng A < n := by rw [hAlen, ← hn]; omega
          have hPsplit : P M = P A ++ [J] := by
            simpa [A, J] using P_multi_step M hmulti hlen
          have hPAne : P A ≠ [] := P_nonempty A
          have hhead : (P A).getD 0 [] = (P M).getD 0 [] := by
            rw [hPsplit]
            cases hPA : P A with
            | nil => exact (hPAne hPA).elim
            | cons x xs => simp
          have hP0A : (P A).getD 0 [] ≠ [(0, 0)] := by rw [hhead]; exact hP0
          -- `Trans A = 0_B` なら `A` は零項で `P A ! 0 = ((0,0))`、仮定に反する
          have hTAne : Trans A ≠ BZero := by
            intro hTA
            have hzA := (Trans_preserves_zeroT A (RTPS_TPS A hAR)).2 hTA
            apply hP0A
            have hzA' := hzA
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzA'
            obtain ⟨w, hw⟩ := (one_column A (RTPS_TPS A hAR)).1 ⟨hzA'.1, hAR⟩
            have hw0 : w = 0 := by
              have hew : entry A 1 0 = w := by simp [hw, entry]
              rw [hew] at hzA'
              exact hzA'.2
            rw [P_nonmulti_eq A (by simp [multiT, hzA])]
            simp [hw, hw0]
          have hIHA := ih (Lng A) hAlt A hAR hP0A rfl
          have heq := (Trans_Mark_multi_equations M hR hmulti).1
          rw [← hhead, ← hIHA]
          by_cases hJzero : J = [(0, 0)]
          · have hTrans : Trans M = addBT (Trans A) (Dprin 0 BZero) := by
              simpa [A, J, hJzero] using heq
            rw [hTrans, PB0_addBT_left_tl _ _ hTAne]
          · have hTrans : Trans M = addBT (Trans A) (Trans J) := by
              simpa [A, J, hJzero] using heq
            rw [hTrans, PB0_addBT_left_tl _ _ hTAne]

/-! ## 命題本体（clause (1)(2)(3)） -/

/-- 上段の値が `0` の列は上段の親を持たない（`<^Next` は上段の狭義増加を要求する）。 -/
private theorem no_parent_row0_of_zero_tl (M : PS) (j : ℕ)
    (he : entry M 0 j = 0) : hasParent M 0 j = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hp
  have hn := hasParent_next_fseq M 0 j hp
  have hn0 : nextrel0 M (parent M 0 j) j = true := by simpa [nextR] using hn
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn0
  omega

/-- `IdxSum Q` の第 1 成分は先頭成分の長さ。Isabelle `idxsum_nth` の特殊化。 -/
private theorem idxSum_one_tl (Q : List PS) (h : 1 ≤ Q.length) :
    (IdxSum Q).getD 1 0 = Lng (Q.getD 0 []) := by
  cases Q with
  | nil => simp at h
  | cons x xs => simp [IdxSum]

/-- Isabelle `reduced_P0_zero_e11` (`pss_wip.thy:16519`):
`P(M)_0 = ((0,0))` かつ `Lng (P M) > 1` の簡約形では左二列の下段は共に `0`。 -/
private theorem reduced_P0_zero_e11_tl (M : PS) (hR : RTPS M)
    (hP0 : (P M).getD 0 [] = [(0, 0)]) (hlen : 1 < Lng M)
    (hPlen : 1 < (P M).length) :
    entry M 1 0 = 0 ∧ entry M 1 1 = 0 := by
  have hM : TPS M := RTPS_TPS M hR
  have hPne : P M ≠ [] := P_nonempty M
  -- `concat (P M) = M` から `M_0 = (0,0)`
  obtain ⟨rest, hPdec⟩ : ∃ rest, P M = [(0, 0)] :: rest := by
    cases hPM : P M with
    | nil => exact absurd hPM hPne
    | cons x xs =>
        refine ⟨xs, ?_⟩
        rw [hPM] at hP0
        simp only [List.getD_cons_zero] at hP0
        rw [hP0]
  have hMform : M = (0, 0) :: rest.flatten := by
    rw [← P_concat M, hPdec]; simp
  have he00 : entry M 0 0 = 0 := by rw [hMform]; simp [entry]
  have he10 : entry M 1 0 = 0 := reduced_e10_zero_tl M hR he00
  -- 第 1 成分の左端は `IdxSum (P M) ! 1 = 1`
  have hidx1 : (IdxSum (P M)).getD 1 0 = 1 := by
    rw [idxSum_one_tl (P M) (by omega), hP0]
    rfl
  have hlmin := (P_leftend_lmin M 1 hM hPlen).2
  rw [hidx1] at hlmin
  have he01 : entry M 0 1 = 0 := by
    have h0 := hlmin 0 (by omega)
    omega
  have hnp : hasParent M 0 1 = false := no_parent_row0_of_zero_tl M 1 he01
  have hB : RedCondB M = true := (RTPS_condAB M hR).2
  have he11 : entry M 1 1 = 0 := by
    have hb := RedCondB_apply M hM hB 1 (by omega) hnp
    omega
  exact ⟨he10, he11⟩

/-- `Lng M = 1` なら複項ではない。 -/
private theorem multiT_len_one_false_tl (M : PS) (hL : Lng M = 1) :
    multiT M = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hM : TPS M := by
    intro hnil
    rw [hnil] at hL
    simp at hL
  have := multi_length_fseq M hM h
  omega

/-- Isabelle `m_7_3_Trans_leftmost` (`pss_wip.thy:16569`) の clause (1)(2)。

- (1) `P(M)_0 = ((0,0))` かつ `Lng (P M) > 1` なら `Trans M` の左端は `M_{1,1}`。
- (2) `P(M)_0 ≠ ((0,0))` なら最左単項成分は `Trans (P(M)_0)` で、左端は `M_{1,0}`。

clause (3)（`(1,0) <^Next_M (1,1)` のとき最左単項成分の左二文字が
`D_{M_{1,0}} D_u`）はこのファイルには含めていない（下記 report 参照）。 -/
theorem m_7_3_Trans_leftmost (M : PS) (hR : RTPS M) :
    ((P M).getD 0 [] = [(0, 0)] ∧ 1 < (P M).length →
        bpHeadV (Trans M) = (entry M 1 1 : ℕ∞)) ∧
      ((P M).getD 0 [] ≠ [(0, 0)] →
        (PB (Trans M)).getD 0 BZero = Trans ((P M).getD 0 []) ∧
          bpHeadV (Trans M) = (entry M 1 0 : ℕ∞)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hcore : bpHeadV (Trans M) = (entry M 1 0 : ℕ∞) := m_7_3_Trans_leftend M hR
  constructor
  · rintro ⟨hP0, hPlen⟩
    -- `Lng (P M) > 1` は `1 < Lng M` を導く
    have hlen : 1 < Lng M := by
      by_contra h
      have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
      have hL1 : Lng M = 1 := by omega
      rw [P_nonmulti_eq M (multiT_len_one_false_tl M hL1)] at hPlen
      simp at hPlen
    obtain ⟨he10, he11⟩ := reduced_P0_zero_e11_tl M hR hP0 hlen hPlen
    rw [hcore, he10, he11]
  · intro hP0
    exact ⟨m_7_3_Trans_leftmost_pc M hR hP0, hcore⟩

/-! ## §8.7 降下 dispatcher への drop-in

`lean/8/8.7-fseq-descend.lean` の

```
  def FseqDesc_m_7_3_Trans_leftmost_2 : Prop :=
    ∀ M : PS, RTPS M → (P M).getD 0 [] ≠ [(0, 0)] →
      (PB (Trans M)).getD 0 BZero = Trans ((P M).getD 0 []) ∧
        bpHeadV (Trans M) = (entry M 1 0 : ℕ∞)
```

の本体を **そのまま型として**持つ。§7 → §8 の import 方向を保つため（既存の §7 ファイルは
どれも §8 を import していない）このファイルでは `FseqDesc_…` の名前を参照しない。
`lean/8/8.7-fseq-descend-props*.lean` 側で

```
  theorem FseqDesc_m_7_3_Trans_leftmost_2_holds : FseqDesc_m_7_3_Trans_leftmost_2 :=
    m_7_3_Trans_leftmost_2_dropin
```

と 1 行書けば delta 展開で通る（kimina で elaborate 確認済み）。 -/
theorem m_7_3_Trans_leftmost_2_dropin :
    ∀ M : PS, RTPS M → (P M).getD 0 [] ≠ [(0, 0)] →
      (PB (Trans M)).getD 0 BZero = Trans ((P M).getD 0 []) ∧
        bpHeadV (Trans M) = (entry M 1 0 : ℕ∞) := by
  intro M hR hP0
  exact (m_7_3_Trans_leftmost M hR).2 hP0

#print axioms m_7_3_Trans_leftend
#print axioms m_7_3_Trans_leftmost_pc
#print axioms m_7_3_Trans_leftmost
#print axioms m_7_3_Trans_leftmost_2_dropin

end PSS
