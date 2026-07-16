import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-trmax»
import «6».«6.8-d1pos-le0»
import «6».«6.2-multi-criterion»

/-!
# §6.8 d1pos regime-B/A2 anchor 層 ＋ ctx brick 群

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域における枝 anchor の一致と文脈事実）
- 訂正: なし（タイル係数は A8 適用後の `*_68` 資産に依拠）
- Isabelle (isabelle/pss_mechanized.thy):
  `oper_d1pos_clt_regB` (16200) /
  `oper_d1pos_anchor_coincide_regA2` (16390) /
  `oper_d1pos_anchor_coincide_regB` (16463) /
  `oper_d1pos_anchor_coincide_regB2` (16617) /
  `oper_d1pos_branch_lowshift_regB_plug` (16760) /
  `oper_d1pos_ctx_multiM` (16927) /
  `oper_d1pos_row0_agree` (17021) /
  `oper_d1pos_ctx_le0Np` (17159) /
  `oper_d1pos_nth_below` (17207) /
  `oper_d1pos_ctx_stop_of_tnc` (17277) /
  `oper_d1pos_anchor_coincide_period_unified` (17364) /
  `oper_d1pos_lenPSeq_unified` (17601)
- 並行 agent 域 (14393–16199) からの私的再証明（suffix `_rb`）:
  `anchor_lt_of_uniform_witness` (15865) /
  `oper_d1pos_period_row0_floor` (15971) /
  `oper_d1pos_strict_period_floor` (16017) /
  `oper_d1pos_clt_regA` (16068、regA2 の内部 brick として)
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Prop・`oper_d1pos_ctx_dpos`/`_r1le`）,
  «6».«6.8-d1pos-trmax»（`nextR1_boundary_stop_of_prefix`）,
  «6».«6.8-standard-slice-Br-descending»（`P_last_anchor_68` 系 anchor 資産・
  `*_68` タイル読み出し・`P_length_eq_of_shift_prefix_boundary_68`・
  `last_anchor_coincide_shift_prefix_68`）, «6».«6.2-multi-criterion»
- 状態: ✅ 証明済（sorry 0）。`oper_d1pos_anchor_coincide_regA2` は Isabelle の
  truncate ルート（`oper_d1pos_anchor_coincide_regA` 経由）ではなく、同値な
  unified ルート（`shamt = 0` の `last_anchor_coincide_shift_prefix_68`）で証明
  （主張は Isabelle と 1:1）。

Prop discharge: `D1pos_oper_d1pos_ctx_multiM_holds` /
`D1pos_oper_d1pos_ctx_le0Np_holds` / `D1pos_oper_d1pos_lenPSeq_unified_holds`。
-/

namespace PSS

/-! ## 小補助（このファイル私用、suffix `_rb`） -/

/-- `1 < (P S).length` なら `S` は空列でない（`P [] = [[]]` は長さ 1）。 -/
private theorem TPS_of_P_multi_rb (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

private theorem le0Aux_refl_rb (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_rb (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_rb]

private theorem getD_entry_rb (X : PS) (s : ℕ) (hs : s < Lng X) :
    X.getD s (0, 0) = (entry X 0 s, entry X 1 s) := by
  rw [getD_eq_getElem_idx X (0, 0) hs]
  cases hx : X[s] with
  | mk a b => simp [entry, List.getElem?_eq_getElem hs, hx]

/-! ## 統一 anchor 一致（unified、純ラッパ）

Isabelle: `oper_d1pos_anchor_coincide_period_unified` (17364) /
`oper_d1pos_lenPSeq_unified` (17601)。実体は
`last_anchor_coincide_shift_prefix_68` / `P_length_eq_of_shift_prefix_boundary_68`
（`6.8-standard-slice-Br-descending`）。 -/

/-- Isabelle `oper_d1pos_lenPSeq_unified` (pss_mechanized.thy:17601)。 -/
theorem oper_d1pos_lenPSeq_unified
    (S Snside : PS) (shamt : ℕ)
    (ST : TPS S) (multi : 1 < (P S).length)
    (SnT : TPS Snside) (multiN : 1 < (P Snside).length)
    (mleS : Lng Snside - 1 ≤ Lng S - 1)
    (cleM : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Snside - 1)
    (shiftEq : seg S 0 (Lng Snside - 1 - 1) =
      IncrFirstN shamt (seg Snside 0 (Lng Snside - 1 - 1)))
    (boundEq0 : entry S 0 (Lng Snside - 1) =
      entry Snside 0 (Lng Snside - 1) + shamt) :
    (P S).length = (P Snside).length :=
  P_length_eq_of_shift_prefix_boundary_68 S Snside shamt ST SnT multi multiN
    mleS cleM shiftEq boundEq0

theorem D1pos_oper_d1pos_lenPSeq_unified_holds :
    D1pos_oper_d1pos_lenPSeq_unified := by
  intro S Snside shamt ST multi SnT multiN mleS cleM shiftEq boundEq0
  exact oper_d1pos_lenPSeq_unified S Snside shamt ST multi SnT multiN
    mleS cleM shiftEq boundEq0

/-- Isabelle `oper_d1pos_anchor_coincide_period_unified`
(pss_mechanized.thy:17364)。3 結論は `∧` 束ね。 -/
theorem oper_d1pos_anchor_coincide_period_unified
    (S Snside : PS) (shamt : ℕ)
    (ST : TPS S) (multi : 1 < (P S).length)
    (SnT : TPS Snside) (multiN : 1 < (P Snside).length)
    (mleS : Lng Snside - 1 ≤ Lng S - 1)
    (cleM : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Snside - 1)
    (lenPSeq : (P S).length = (P Snside).length)
    (shiftEq : seg S 0 (Lng Snside - 1 - 1) =
      IncrFirstN shamt (seg Snside 0 (Lng Snside - 1 - 1)))
    (boundEq0 : entry S 0 (Lng Snside - 1) =
      entry Snside 0 (Lng Snside - 1) + shamt)
    (boundEq1 : entry S 1 (Lng Snside - 1) ≤
      entry Snside 1 (Lng Snside - 1)) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
        (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 ∧
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry Snside 0 ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) +
          shamt ∧
      entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry Snside 1 ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) := by
  obtain ⟨h1, h2, h3, _⟩ := last_anchor_coincide_shift_prefix_68 S Snside shamt
    ST SnT multi multiN mleS cleM lenPSeq shiftEq boundEq0 boundEq1
  exact ⟨h1, h2, h3⟩

/-! ## ctx brick: `multiM`（Isabelle 16927） -/

/-- Isabelle `oper_d1pos_ctx_multiM` (pss_mechanized.thy:16927)。
枝領域 `S = seg M (j0' + TrMax M' + 1) j1'` は複項（`¬brle` から）。 -/
theorem oper_d1pos_ctx_multiM
    (M : PS) (j0' j1' : ℕ)
    (M'T : TPS (seg M j0' j1'))
    (lt : j0' < j1')
    (notbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true)) :
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length := by
  rw [not_or] at notbrle
  obtain ⟨trne, notle0⟩ := notbrle
  set M' := seg M j0' j1' with hM'
  set t := TrMax M' with ht
  have hM'pos : 0 < Lng M' := List.length_pos_of_ne_nil M'T
  have lenM' : Lng M' = j1' + 1 - j0' := by rw [hM']; exact length_seg M j0' j1'
  have tb : t ≤ Lng M' - 1 := TrMax_bound M' M'T
  have tlt : t < Lng M' - 1 := by omega
  -- `S` は `M'` の内側切片と一致
  have hseq : seg M' (t + 1) (Lng M' - 1) =
      seg M (j0' + (t + 1)) (j0' + (Lng M' - 1)) :=
    seg_of_seg_68 M j0' j1' (t + 1) (Lng M' - 1) (by omega) (by omega)
  have he1 : j0' + (t + 1) = j0' + t + 1 := by omega
  have he2 : j0' + (Lng M' - 1) = j1' := by omega
  rw [he1, he2] at hseq
  -- 窓 `[t+1, Lng M'-1]` の le0 失敗を切片へ転送
  have lenInner : Lng (seg M' (t + 1) (Lng M' - 1)) =
      (Lng M' - 1) + 1 - (t + 1) := length_seg M' (t + 1) (Lng M' - 1)
  have hle0eq : leR (seg M' (t + 1) (Lng M' - 1)) 0 0 (Lng M' - 1 - t - 1) =
      leR M' 0 ((t + 1) + 0) ((t + 1) + (Lng M' - 1 - t - 1)) :=
    leR0_seg_adm M' (t + 1) (Lng M' - 1) 0 (Lng M' - 1 - t - 1)
      (by omega) (by omega) (by omega) (by omega)
  have hend : (t + 1) + (Lng M' - 1 - t - 1) = Lng M' - 1 := by omega
  rw [Nat.add_zero, hend] at hle0eq
  have notle0S : ¬leR (seg M' (t + 1) (Lng M' - 1)) 0 0
      (Lng M' - 1 - t - 1) = true := by
    rw [hle0eq]; exact notle0
  rw [hseq] at notle0S
  set S := seg M (j0' + t + 1) j1' with hS
  have lenS : Lng S = Lng M' - 1 - t := by rw [hS, length_seg]; omega
  have hSpos : 0 < Lng S := by omega
  have hST : TPS S := List.ne_nil_of_length_pos hSpos
  have notle0S' : ¬leR S 0 0 (Lng S - 1) = true := by
    rw [show Lng S - 1 = Lng M' - 1 - t - 1 from by omega]
    exact notle0S
  -- `Lng S > 1`（さもなくば反射 le0 と矛盾）
  have hLngS1 : 1 < Lng S := by
    by_contra h
    apply notle0S'
    rw [show Lng S - 1 = 0 from by omega]
    exact leR0_refl_rb S 0 (by omega)
  -- 零項でも単項でもない → 複項
  have hzeroS : zeroT S = false := by
    cases h : zeroT S with
    | false => rfl
    | true =>
        have hh := h
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hh
        omega
  have hmonoS : monoT S = false := by
    cases h : monoT S with
    | false => rfl
    | true =>
        have hh := h
        simp only [monoT, Bool.and_eq_true] at hh
        exact absurd hh.2 notle0S'
  have hmultiS : multiT S = true := by
    simp [multiT, hzeroS, hmonoS]
  exact (P_components_multi_iff S hST).mp hmultiS

theorem D1pos_oper_d1pos_ctx_multiM_holds : D1pos_oper_d1pos_ctx_multiM := by
  intro M j0' j1' hT hlt hnot
  exact oper_d1pos_ctx_multiM M j0' j1' hT hlt hnot

/-! ## ctx brick: 行 0 逐語一致（Isabelle 17021） -/

/-- Isabelle `oper_d1pos_row0_agree` (pss_mechanized.thy:17021)。
`x ≤ Lng N - 1` で `N[n]` の行 0 は `N` と一致（境界では δ が丁度埋まる）。 -/
theorem oper_d1pos_row0_agree
    (N : PS) (n x : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (bnd : Lng N - 1 < Lng (oper N n))
    (hx : x ≤ Lng N - 1) :
    entry (oper N n) 0 x = entry N 0 x := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    omega
  rcases Nat.lt_or_ge x (Lng N - 1) with hxlt | hxge
  · exact entry_oper_lt_last_68 N n 0 x L hn1 (Or.inl rfl) hxlt
  · have hxeq : x = Lng N - 1 := by omega
    subst hxeq
    have hn2 : 1 < n := by
      by_contra h
      have hn1' : n = 1 := by omega
      subst hn1'
      omega
    have hread := entry_oper_d1pos_zero_68 N n 1 0 L notzero hp i1z hn2 hw
    rw [show parent N 1 (Lng N - 1) +
        1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = Lng N - 1
      from by omega] at hread
    rw [hread]
    have hdpos := oper_d1pos_ctx_dpos N hp i1z j0lt
    simp only [Nat.add_zero, Nat.one_mul]
    omega

/-! ## ctx brick: `le0Np`（Isabelle 17159） -/

/-- Isabelle `oper_d1pos_ctx_le0Np` (pss_mechanized.thy:17159)。
`le0 M j0' j1'` の端点制限＋行 0 転送で `le0 N j0' (Lng N - 1)`。
Lean では値特徴付け（`ancestor_basic_1` ＋ `parent_exists_3`）で直接構成。 -/
theorem oper_d1pos_ctx_le0Np
    (N M : PS) (n j0' j1' : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (Neq : M = oper N n)
    (le0M : leR M 0 j0' j1' = true)
    (j0plt : j0' < Lng N - 1)
    (jM : j1' < Lng M)
    (bge : Lng N - 1 ≤ j1') :
    leR N 0 j0' (Lng N - 1) = true := by
  subst Neq
  have hNT : TPS N := by
    have h0 : 0 < Lng N := by omega
    exact List.ne_nil_of_length_pos h0
  have bnd : Lng N - 1 < Lng (oper N n) := by omega
  apply parent_exists_3 N j0' (Lng N - 1) hNT j0plt (by omega)
  intro j hj hjle
  have hMT : TPS (oper N n) := by
    have h0 : 0 < Lng (oper N n) := by omega
    exact List.ne_nil_of_length_pos h0
  have hgrow : entry (oper N n) 0 j0' < entry (oper N n) 0 j :=
    ancestor_basic_1 (oper N n) j0' j j1' hMT hj (by omega) le0M
  rw [oper_d1pos_row0_agree N n j0' L notzero hp i1z j0lt bnd (by omega),
    oper_d1pos_row0_agree N n j L notzero hp i1z j0lt bnd hjle] at hgrow
  exact hgrow

theorem D1pos_oper_d1pos_ctx_le0Np_holds : D1pos_oper_d1pos_ctx_le0Np := by
  intro N M n j0' j1' L notzero hp i1z j0lt Neq le0M j0plt jM bge
  exact oper_d1pos_ctx_le0Np N M n j0' j1' L notzero hp i1z j0lt Neq
    le0M j0plt jM bge

/-! ## ctx brick: 境界未満の全対一致（Isabelle 17207） -/

/-- Isabelle `oper_d1pos_nth_below` (pss_mechanized.thy:17207)。
`x < Lng N - 1` で `N[n]` の対全体（両行）が `N` と一致。 -/
theorem oper_d1pos_nth_below
    (N : PS) (n x : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (bnd : Lng N - 1 < Lng (oper N n))
    (hx : x < Lng N - 1) :
    (oper N n).getD x (0, 0) = N.getD x (0, 0) := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    omega
  have hxM : x < Lng (oper N n) := by omega
  have hxN : x < Lng N := by omega
  rw [getD_entry_rb (oper N n) x hxM, getD_entry_rb N x hxN,
    entry_oper_lt_last_68 N n 0 x L hn1 (Or.inl rfl) hx,
    entry_oper_lt_last_68 N n 1 x L hn1 (Or.inr rfl) hx]

/-! ## ctx brick: `tnc` からの境界停止（Isabelle 17277） -/

/-- Isabelle `oper_d1pos_ctx_stop_of_tnc` (pss_mechanized.thy:17277)。
厳格 `tnc` の下で、`N` 側参照切片の幹右端の行 1 ステップは `M'` 側でも失敗
（共有接頭辞 `[0, c]` の純転送）。 -/
theorem oper_d1pos_ctx_stop_of_tnc
    (N M : PS) (n j0' j1' : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (Neq : M = oper N n)
    (j0plt : j0' < Lng N - 1)
    (lt : j0' < j1')
    (jM : j1' < Lng M)
    (bge : Lng N - 1 ≤ j1')
    (tnc : TrMax (seg N j0' (Lng N - 1)) < Lng N - 1 - 1 - j0') :
    nextR (seg (oper N n) j0' j1') 1
      (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false := by
  subst Neq
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    omega
  set c := Lng N - 1 - 1 - j0' with hc
  set Mp := seg (oper N n) j0' j1' with hMp
  set Np := seg N j0' (Lng N - 1) with hNp
  have lenMp : Lng Mp = j1' + 1 - j0' := by rw [hMp]; exact length_seg _ _ _
  have lenNp : Lng Np = Lng N - j0' := by
    rw [hNp, length_seg]; omega
  have hcM : c < Lng Mp := by omega
  have hcN : c < Lng Np := by omega
  have hMpT : TPS Mp := by
    have h0 : 0 < Lng Mp := by omega
    exact List.ne_nil_of_length_pos h0
  have hNpT : TPS Np := by
    have h0 : 0 < Lng Np := by omega
    exact List.ne_nil_of_length_pos h0
  have hagree := seg_oper_prefix_agree_68 N n j0' j1' c L hn1 hcM hcN
    (fun s hs => by omega)
  exact nextR1_boundary_stop_of_prefix Mp Np c hMpT hNpT hagree hcM hcN
    (by omega) (by omega)

/-! ## 周期内 行 0 floor（並行 agent 域の私的再証明、suffix `_rb`）

Isabelle: `oper_d1pos_strict_period_floor` (16017) /
`oper_d1pos_period_row0_floor` (15971) / `anchor_lt_of_uniform_witness` (15865)。 -/

/-- Isabelle `oper_d1pos_strict_period_floor` (16017) の私的再証明。
周期窓 `[j₋₂, Lng N-1]` の行 0 は基点で厳格最小。 -/
private theorem oper_d1pos_strict_period_floor_rb
    (N : PS) (s : ℕ)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hs0 : 0 < s)
    (hsle : s ≤ Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry N 0 (parent N 1 (Lng N - 1)) <
      entry N 0 (parent N 1 (Lng N - 1) + s) := by
  have hNT : TPS N := by
    have h0 : 0 < Lng N := by omega
    exact List.ne_nil_of_length_pos h0
  have hp1 : hasParent N 1 (Lng N - 1) = true := by simpa [i1z] using hp
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
  have hrow0 : leR N 0 (parent N 1 (Lng N - 1)) (Lng N - 1) = true :=
    (nextR_implies_row0 N 1 (parent N 1 (Lng N - 1)) (Lng N - 1) hnext).2
  have hmono : monoT (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) = true :=
    mono_ancestor_slice N (parent N 1 (Lng N - 1)) (Lng N - 1) hNT j0lt hrow0
  have lenSeg : Lng (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) =
      (Lng N - 1) + 1 - parent N 1 (Lng N - 1) :=
    length_seg N (parent N 1 (Lng N - 1)) (Lng N - 1)
  have hsegT : TPS (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) := by
    have h0 : 0 < Lng (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) := by omega
    exact List.ne_nil_of_length_pos h0
  have hleR0 : leR (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) 0 0
      (Lng (seg N (parent N 1 (Lng N - 1)) (Lng N - 1)) - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hstrict := (multi_criterion_23 _ hsegT).mpr hleR0 s hs0 (by omega)
  rw [entry_seg N (parent N 1 (Lng N - 1)) (Lng N - 1) 0 0 (by omega),
    entry_seg N (parent N 1 (Lng N - 1)) (Lng N - 1) 0 s (by omega)] at hstrict
  simpa using hstrict

/-- Isabelle `oper_d1pos_period_row0_floor` (15971) の私的再証明（弱形）。 -/
private theorem oper_d1pos_period_row0_floor_rb
    (N : PS) (s : ℕ)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hsle : s ≤ Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry N 0 (parent N 1 (Lng N - 1)) ≤
      entry N 0 (parent N 1 (Lng N - 1) + s) := by
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0
    simp
  · exact (oper_d1pos_strict_period_floor_rb N s hp i1z j0lt hpos hsle).le

/-- Isabelle `anchor_lt_of_uniform_witness` (15865) の私的再証明。
一様行 0 証人 `jj < k` があれば最終 anchor は `k` 未満。 -/
private theorem anchor_lt_of_uniform_witness_rb
    (S : PS) (k jj : ℕ) (hS : TPS S) (hmulti : 1 < (P S).length)
    (hjj : jj < k)
    (hwit : ∀ x, k ≤ x → x ≤ Lng S - 1 → entry S 0 jj < entry S 0 x) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 < k := by
  obtain ⟨_, hcle, hlmin, _, _⟩ := P_last_anchor_68 S hS hmulti
  by_contra hnot
  have hkc : k ≤ (IdxSum (P S)).getD ((P S).length - 1) 0 := by omega
  have ha := hlmin jj (by omega)
  have hb := hwit ((IdxSum (P S)).getD ((P S).length - 1) 0) hkc hcle
  omega

/-! ## regime-B の anchor 上界 `c ≤ m`（Isabelle 16200） -/

/-- Isabelle `oper_d1pos_clt_regB` (pss_mechanized.thy:16200)。
regime B（`j₋₂ ≤ A < Lng N - 1`）で消費側枝 anchor は境界 `m` 以下。 -/
theorem oper_d1pos_clt_regB
    (N : PS) (A E n : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_n1 : 1 ≤ n)
    (Ajm2 : parent N 1 (Lng N - 1) ≤ A)
    (AltN : A < Lng N - 1)
    (Ele : Lng N - 1 ≤ E)
    (Eub : E < Lng (oper N n))
    (dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (multi : 1 < (P (seg (oper N n) A E)).length) :
    (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 ≤
      Lng (seg N A (Lng N - 1)) - 1 := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  set S := seg (oper N n) A E with hS
  have lenSraw : Lng (seg (oper N n) A E) = E + 1 - A :=
    length_seg (oper N n) A E
  have lenS : Lng S = E + 1 - A := lenSraw
  have lenNs : Lng (seg N A (Lng N - 1)) = (Lng N - 1) + 1 - A :=
    length_seg N A (Lng N - 1)
  have hST : TPS S := TPS_of_P_multi_rb S multi
  -- 証人 jj とそのブロック指数 qjj（A はブロック 0 内）
  obtain ⟨jj, qjj, hqjj1, hfloor⟩ :
      ∃ jj qjj, qjj ≤ 1 ∧
        A + jj = parent N 1 (Lng N - 1) +
          qjj * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
    by_cases hs0 : A = parent N 1 (Lng N - 1)
    · exact ⟨0, 0, by omega, by omega⟩
    · exact ⟨parent N 1 (Lng N - 1) +
        (Lng N - 1 - parent N 1 (Lng N - 1)) - A, 1, by omega, by omega⟩
  have hjm : A + jj ≤ Lng N - 1 := by
    rcases Nat.lt_or_ge qjj 1 with h | h
    · have h0 : qjj = 0 := by omega
      subst h0
      omega
    · have h1 : qjj = 1 := by omega
      subst h1
      omega
  have hqjjn : qjj < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        qjj * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  -- 証人の読み出し
  have eSjj : entry S 0 jj =
      entry N 0 (parent N 1 (Lng N - 1)) +
        qjj * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) := by
    have hdecode := entry_oper_d1pos_zero_68 N n qjj 0 L notzero hp i1z hqjjn hw
    have hidx : parent N 1 (Lng N - 1) +
        qjj * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = A + jj := by omega
    rw [hidx] at hdecode
    have hread : entry S 0 jj = entry (oper N n) 0 (A + jj) :=
      entry_seg (oper N n) A E 0 jj (by omega)
    rw [hread, hdecode]
    simp only [Nat.add_zero]
  -- 一様証人: 厳格尾部 `[m+1, Lng S-1]` を撃ち落とす
  have hwit : ∀ x, (Lng N - 1 - A) + 1 ≤ x → x ≤ Lng S - 1 →
      entry S 0 jj < entry S 0 x := by
    intro x hxlo hxhi
    have hAxge : parent N 1 (Lng N - 1) ≤ A + x := by omega
    have hAxE : A + x ≤ E := by omega
    have hdm := Nat.div_add_mod (A + x - parent N 1 (Lng N - 1))
      (Lng N - 1 - parent N 1 (Lng N - 1))
    set qx := (A + x - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) with hqxdef
    set sx := (A + x - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) with hsxdef
    have hsxw : sx < Lng N - 1 - parent N 1 (Lng N - 1) :=
      Nat.mod_lt _ hw
    have hcomm : (Lng N - 1 - parent N 1 (Lng N - 1)) * qx =
        qx * (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.mul_comm _ _
    have hxsplit : A + x = parent N 1 (Lng N - 1) +
        qx * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx := by omega
    have hqxn : qx < n := by
      by_contra hcon
      have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have eSx : entry S 0 x =
        entry N 0 (parent N 1 (Lng N - 1) + sx) +
          qx * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by
      have hdecode := entry_oper_d1pos_zero_68 N n qx sx L notzero hp i1z
        hqxn hsxw
      have hidx : parent N 1 (Lng N - 1) +
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx = A + x := by omega
      rw [hidx] at hdecode
      have hread : entry S 0 x = entry (oper N n) 0 (A + x) :=
        entry_seg (oper N n) A E 0 x (by omega)
      rw [hread, hdecode]
    -- ブロック順: qjj ≤ qx
    have hqle : qjj ≤ qx := by
      by_contra hcon
      have hsucc : qx + 1 ≤ qjj := by omega
      have hmul : (qx + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          qjj * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ hsucc
      have hexp : (qx + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) +
            (Lng N - 1 - parent N 1 (Lng N - 1)) := by ring
      omega
    have hfloorle : entry N 0 (parent N 1 (Lng N - 1)) ≤
        entry N 0 (parent N 1 (Lng N - 1) + sx) :=
      oper_d1pos_period_row0_floor_rb N sx hp i1z j0lt (by omega)
    by_cases hqeq : qjj = qx
    · -- SAME block: `sx > 0`、厳格 floor
      subst hqeq
      have hsxpos : 0 < sx := by omega
      have hstrict : entry N 0 (parent N 1 (Lng N - 1)) <
          entry N 0 (parent N 1 (Lng N - 1) + sx) :=
        oper_d1pos_strict_period_floor_rb N sx hp i1z j0lt hsxpos (by omega)
      omega
    · -- HIGHER block: `qjj + 1 ≤ qx`、δ 一段で undercut
      have hsucc : qjj + 1 ≤ qx := by omega
      have hexp : (qjj + 1) * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) =
        qjj * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) +
          (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by ring
      have hmulq : (qjj + 1) * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) ≤
        qx * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) :=
        Nat.mul_le_mul_right _ hsucc
      omega
  have hclt := anchor_lt_of_uniform_witness_rb S ((Lng N - 1 - A) + 1) jj
    hST multi (by omega) hwit
  omega

/-! ## regime-B anchor 一致（両 anchor が境界の真下、Isabelle 16463） -/

/-- Isabelle `oper_d1pos_anchor_coincide_regB` (pss_mechanized.thy:16463)。
シフト一致 `shiftEq` から純構造的に anchor 一致・接合 entry 等式を導く。 -/
theorem oper_d1pos_anchor_coincide_regB
    (S Snside : PS) (shamt : ℕ)
    (ST : TPS S) (multi : 1 < (P S).length)
    (SnT : TPS Snside) (multiN : 1 < (P Snside).length)
    (clt : (IdxSum (P S)).getD ((P S).length - 1) 0 < Lng Snside - 1)
    (cNlt : (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 <
      Lng Snside - 1)
    (LngEq : Lng S = Lng Snside)
    (shiftEq : seg S 0 (Lng Snside - 1 - 1) =
      IncrFirstN shamt (seg Snside 0 (Lng Snside - 1 - 1))) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
        (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 ∧
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry Snside 0 ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) +
          shamt ∧
      entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry Snside 1 ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) := by
  have lenPreSraw : Lng (seg S 0 (Lng Snside - 1 - 1)) =
      (Lng Snside - 1 - 1) + 1 - 0 := length_seg S 0 (Lng Snside - 1 - 1)
  have lenPreNraw : Lng (seg Snside 0 (Lng Snside - 1 - 1)) =
      (Lng Snside - 1 - 1) + 1 - 0 := length_seg Snside 0 (Lng Snside - 1 - 1)
  -- dropLast 等式（anchor は境界 `m` の真下）
  have hdropS : (P (seg S 0 (Lng Snside - 1 - 1))).dropLast =
      (P S).dropLast :=
    P_dropLast_seg_zero_after_anchor_68 S (Lng Snside - 1) ST multi clt
      (by omega)
  have hdropN : (P (seg Snside 0 (Lng Snside - 1 - 1))).dropLast =
      (P Snside).dropLast :=
    P_dropLast_seg_zero_after_anchor_68 Snside (Lng Snside - 1) SnT multiN
      cNlt (by omega)
  -- `P` はシフトと可換
  have hPpre : P (seg S 0 (Lng Snside - 1 - 1)) =
      (P (seg Snside 0 (Lng Snside - 1 - 1))).map (IncrFirstN shamt) := by
    rw [shiftEq, P_IncrFirstN_equivariance]
  have hbutShift : (P S).dropLast =
      ((P Snside).dropLast).map (IncrFirstN shamt) := by
    rw [← hdropS, ← hdropN, hPpre]
    exact List.map_dropLast.symm
  -- anchor は dropLast 長の総和 → シフトで不変
  have hceq : (IdxSum (P S)).getD ((P S).length - 1) 0 =
      (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 := by
    rw [last_anchor_eq_sum_dropLast_68 S,
      last_anchor_eq_sum_dropLast_68 Snside, hbutShift]
    simp [List.map_map, Function.comp_def, IncrFirstN_eq_map]
  refine ⟨hceq, ?_, ?_⟩
  · -- 行 0: 接頭辞内で `+shamt`
    have hcltN : (IdxSum (P S)).getD ((P S).length - 1) 0 <
        Lng (seg Snside 0 (Lng Snside - 1 - 1)) := by omega
    have hcltS : (IdxSum (P S)).getD ((P S).length - 1) 0 <
        Lng (seg S 0 (Lng Snside - 1 - 1)) := by omega
    have hh : entry (seg S 0 (Lng Snside - 1 - 1)) 0
          ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry (seg Snside 0 (Lng Snside - 1 - 1)) 0
          ((IdxSum (P S)).getD ((P S).length - 1) 0) + shamt := by
      rw [shiftEq]
      exact entry_IncrFirstN_zero shamt (seg Snside 0 (Lng Snside - 1 - 1))
        ((IdxSum (P S)).getD ((P S).length - 1) 0) hcltN
    rw [entry_seg S 0 (Lng Snside - 1 - 1) 0 _ hcltS,
      entry_seg Snside 0 (Lng Snside - 1 - 1) 0 _ hcltN] at hh
    simp only [Nat.zero_add] at hh
    rw [← hceq]
    exact hh
  · -- 行 1: 接頭辞内で不変
    have hcltN : (IdxSum (P S)).getD ((P S).length - 1) 0 <
        Lng (seg Snside 0 (Lng Snside - 1 - 1)) := by omega
    have hcltS : (IdxSum (P S)).getD ((P S).length - 1) 0 <
        Lng (seg S 0 (Lng Snside - 1 - 1)) := by omega
    have hh : entry (seg S 0 (Lng Snside - 1 - 1)) 1
          ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry (seg Snside 0 (Lng Snside - 1 - 1)) 1
          ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
      rw [shiftEq]
      exact entry_IncrFirstN_one shamt (seg Snside 0 (Lng Snside - 1 - 1))
        ((IdxSum (P S)).getD ((P S).length - 1) 0)
    rw [entry_seg S 0 (Lng Snside - 1 - 1) 1 _ hcltS,
      entry_seg Snside 0 (Lng Snside - 1 - 1) 1 _ hcltN] at hh
    simp only [Nat.zero_add] at hh
    rw [← hceq]
    exact hh.le

/-! ## regime-B 境界 anchor 一致（`c = cN = m`、Isabelle 16617） -/

/-- Isabelle `oper_d1pos_anchor_coincide_regB2` (pss_mechanized.thy:16617)。
残差 block-fold 左最小事実 `mLmin_S`/`mLmin_Sn` で両 anchor を境界 `m` に固定し、
接合 entry を単一添字 `m` で読む。 -/
theorem oper_d1pos_anchor_coincide_regB2
    (N : PS) (A E n : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (n1 : 1 ≤ n)
    (Ajm2 : parent N 1 (Lng N - 1) ≤ A)
    (AltN : A < Lng N - 1)
    (Ele : Lng N - 1 ≤ E)
    (Eub : E < Lng (oper N n))
    (dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (multi : 1 < (P (seg (oper N n) A E)).length)
    (multiN : 1 < (P (seg N A (Lng N - 1))).length)
    (mLmin_S : ∀ j, j < Lng (seg N A (Lng N - 1)) - 1 →
      entry (seg (oper N n) A E) 0 (Lng (seg N A (Lng N - 1)) - 1) ≤
        entry (seg (oper N n) A E) 0 j)
    (mLmin_Sn : ∀ j, j < Lng (seg N A (Lng N - 1)) - 1 →
      entry (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1) ≤
        entry (seg N A (Lng N - 1)) 0 j)
    (r1le : entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 (Lng N - 1)) :
    (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 =
        (IdxSum (P (seg N A (Lng N - 1)))).getD
          ((P (seg N A (Lng N - 1))).length - 1) 0 ∧
      entry (seg (oper N n) A E) 0
          ((IdxSum (P (seg (oper N n) A E))).getD
            ((P (seg (oper N n) A E)).length - 1) 0) =
        entry (seg N A (Lng N - 1)) 0
          ((IdxSum (P (seg N A (Lng N - 1)))).getD
            ((P (seg N A (Lng N - 1))).length - 1) 0) ∧
      entry (seg (oper N n) A E) 1
          ((IdxSum (P (seg (oper N n) A E))).getD
            ((P (seg (oper N n) A E)).length - 1) 0) ≤
        entry (seg N A (Lng N - 1)) 1
          ((IdxSum (P (seg N A (Lng N - 1)))).getD
            ((P (seg N A (Lng N - 1))).length - 1) 0) := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have lenSraw : Lng (seg (oper N n) A E) = E + 1 - A :=
    length_seg (oper N n) A E
  have lenNs : Lng (seg N A (Lng N - 1)) = (Lng N - 1) + 1 - A :=
    length_seg N A (Lng N - 1)
  have hST : TPS (seg (oper N n) A E) := TPS_of_P_multi_rb _ multi
  have hSnT : TPS (seg N A (Lng N - 1)) := TPS_of_P_multi_rb _ multiN
  have n2 : 1 < n := by
    by_contra hcon
    have hn1' : n = 1 := by omega
    subst hn1'
    omega
  -- c = m
  have cle := oper_d1pos_clt_regB N A E n L notzero hp i1z j0lt n1 Ajm2
    AltN Ele Eub dpos multi
  have cge := last_anchor_ge_of_leftmin_68 (seg (oper N n) A E)
    (Lng (seg N A (Lng N - 1)) - 1) hST (by omega) mLmin_S
  have ceqm : (IdxSum (P (seg (oper N n) A E))).getD
      ((P (seg (oper N n) A E)).length - 1) 0 =
      Lng (seg N A (Lng N - 1)) - 1 := by omega
  -- cN = m
  obtain ⟨_, hcNle, _, _, _⟩ :=
    P_last_anchor_68 (seg N A (Lng N - 1)) hSnT multiN
  have cNge := last_anchor_ge_of_leftmin_68 (seg N A (Lng N - 1))
    (Lng (seg N A (Lng N - 1)) - 1) hSnT (le_refl _) mLmin_Sn
  have cNeqm : (IdxSum (P (seg N A (Lng N - 1)))).getD
      ((P (seg N A (Lng N - 1))).length - 1) 0 =
      Lng (seg N A (Lng N - 1)) - 1 := by omega
  -- 接合 entry を添字 `m`（= 大域 `Lng N - 1`、block 1 offset 0）で読む
  have hAm : A + (Lng (seg N A (Lng N - 1)) - 1) = Lng N - 1 := by omega
  have eSm0 : entry (seg (oper N n) A E) 0 (Lng (seg N A (Lng N - 1)) - 1) =
      entry N 0 (Lng N - 1) := by
    have hread : entry (seg (oper N n) A E) 0
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry (oper N n) 0 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg (oper N n) A E 0 _ (by omega)
    have hdecode := entry_oper_d1pos_zero_68 N n 1 0 L notzero hp i1z n2 hw
    rw [show parent N 1 (Lng N - 1) +
        1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = Lng N - 1
      from by omega] at hdecode
    rw [hread, hAm, hdecode]
    simp only [Nat.add_zero, Nat.one_mul]
    omega
  have eSnm0 : entry (seg N A (Lng N - 1)) 0
      (Lng (seg N A (Lng N - 1)) - 1) = entry N 0 (Lng N - 1) := by
    have hread : entry (seg N A (Lng N - 1)) 0
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry N 0 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg N A (Lng N - 1) 0 _ (by omega)
    rw [hread, hAm]
  have eSm1 : entry (seg (oper N n) A E) 1 (Lng (seg N A (Lng N - 1)) - 1) =
      entry N 1 (parent N 1 (Lng N - 1)) := by
    have hread : entry (seg (oper N n) A E) 1
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry (oper N n) 1 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg (oper N n) A E 1 _ (by omega)
    have hdecode := entry_oper_d1pos_one_68 N n 1 0 L notzero hp i1z n2 hw
    rw [show parent N 1 (Lng N - 1) +
        1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = Lng N - 1
      from by omega] at hdecode
    rw [hread, hAm, hdecode]
    simp only [Nat.add_zero]
  have eSnm1 : entry (seg N A (Lng N - 1)) 1
      (Lng (seg N A (Lng N - 1)) - 1) = entry N 1 (Lng N - 1) := by
    have hread : entry (seg N A (Lng N - 1)) 1
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry N 1 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg N A (Lng N - 1) 1 _ (by omega)
    rw [hread, hAm]
  refine ⟨by omega, ?_, ?_⟩
  · rw [ceqm, cNeqm, eSm0, eSnm0]
  · rw [ceqm, cNeqm, eSm1, eSnm1]
    exact r1le

/-! ## regime-B lowshift の plug-in 形（Isabelle 16760） -/

/-- Isabelle `oper_d1pos_branch_lowshift_regB_plug` (pss_mechanized.thy:16760)。
単一ブロック読み出し `seg_oper_d1pos_block_eq_68` を `baseEq` で
`oper_d1pos_branch_collapse_concrete` 形へ書き換える純 rewrite。 -/
theorem oper_d1pos_branch_lowshift_regB_plug
    (N Snside : PS) (n q A E s0 cc cN : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (_j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (qn : q < n)
    (Aform : A = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (s0e0 : s0 ≤ s0 + (cc - 1))
    (e0lt : s0 + (cc - 1) < Lng N - 1 - parent N 1 (Lng N - 1))
    (Ele : A ≤ E) (ccle : cc - 1 ≤ E - A)
    (baseEq : seg N (parent N 1 (Lng N - 1) + s0)
        (parent N 1 (Lng N - 1) + (s0 + (cc - 1))) = seg Snside 0 (cN - 1)) :
    seg (seg (oper N n) A E) 0 (cc - 1) =
      IncrFirstN (q * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))))
        (seg Snside 0 (cN - 1)) := by
  have hss := seg_of_seg_68 (oper N n) A E 0 (cc - 1) Ele ccle
  have hblock := seg_oper_d1pos_block_eq_68 N n q s0 (s0 + (cc - 1))
    L notzero hp i1z qn s0e0 e0lt
  rw [hss, Nat.add_zero, ← baseEq,
    show A + (cc - 1) = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + (cc - 1))
      from by omega,
    show A = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 from Aform]
  exact hblock

/-! ## regime-A anchor 一致（clt/cNlt 不要形、Isabelle 16390）

Isabelle は truncate ルート（`oper_d1pos_anchor_coincide_regA` 経由）だが、
ここでは同値な unified ルート（`shamt = 0` の
`last_anchor_coincide_shift_prefix_68`）で証明する。内部 brick として
`oper_d1pos_clt_regA` (16068) を私的再証明。 -/

private theorem IncrFirstN_zero_rb (M : PS) : IncrFirstN 0 M = M := by
  simp [IncrFirstN_eq_map]

/-- Isabelle `oper_d1pos_clt_regA` (16068) の私的再証明:
regime A（`A < j₋₂`）で消費側枝 anchor は境界 `m` の真下。 -/
private theorem oper_d1pos_clt_regA_rb
    (N : PS) (A E n : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (n1 : 1 ≤ n)
    (Abnd : A < parent N 1 (Lng N - 1))
    (Ele : Lng N - 1 ≤ E)
    (Eub : E < Lng (oper N n))
    (dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (multi : 1 < (P (seg (oper N n) A E)).length) :
    (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 <
      Lng (seg N A (Lng N - 1)) - 1 := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have lenSraw : Lng (seg (oper N n) A E) = E + 1 - A :=
    length_seg (oper N n) A E
  have lenNs : Lng (seg N A (Lng N - 1)) = (Lng N - 1) + 1 - A :=
    length_seg N A (Lng N - 1)
  have hST : TPS (seg (oper N n) A E) := TPS_of_P_multi_rb _ multi
  have hn0 : 0 < n := by omega
  -- 証人 `jj = j₋₂ - A` は `entry N 0 j₋₂` を逐語で読む（block 0 offset 0）
  have eSjj : entry (seg (oper N n) A E) 0 (parent N 1 (Lng N - 1) - A) =
      entry N 0 (parent N 1 (Lng N - 1)) := by
    have hdecode := entry_oper_d1pos_zero_68 N n 0 0 L notzero hp i1z hn0 hw
    rw [show parent N 1 (Lng N - 1) +
        0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 =
        parent N 1 (Lng N - 1) from by omega] at hdecode
    have hread : entry (seg (oper N n) A E) 0
        (parent N 1 (Lng N - 1) - A) =
        entry (oper N n) 0 (A + (parent N 1 (Lng N - 1) - A)) :=
      entry_seg (oper N n) A E 0 _ (by omega)
    rw [hread,
      show A + (parent N 1 (Lng N - 1) - A) = parent N 1 (Lng N - 1)
        from by omega,
      hdecode]
    simp only [Nat.add_zero, Nat.zero_mul]
  -- 一様証人: 尾部 `[m, Lng S - 1]` はすべて上位ブロック（`qx ≥ 1`）
  have hwit : ∀ x, Lng N - 1 - A ≤ x →
      x ≤ Lng (seg (oper N n) A E) - 1 →
      entry (seg (oper N n) A E) 0 (parent N 1 (Lng N - 1) - A) <
        entry (seg (oper N n) A E) 0 x := by
    intro x hxlo hxhi
    have hAxge : parent N 1 (Lng N - 1) ≤ A + x := by omega
    have hAxE : A + x ≤ E := by omega
    have hdm := Nat.div_add_mod (A + x - parent N 1 (Lng N - 1))
      (Lng N - 1 - parent N 1 (Lng N - 1))
    set qx := (A + x - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) with hqxdef
    set sx := (A + x - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) with hsxdef
    have hsxw : sx < Lng N - 1 - parent N 1 (Lng N - 1) :=
      Nat.mod_lt _ hw
    have hcomm : (Lng N - 1 - parent N 1 (Lng N - 1)) * qx =
        qx * (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.mul_comm _ _
    have hxsplit : A + x = parent N 1 (Lng N - 1) +
        qx * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx := by omega
    have hqxn : qx < n := by
      by_contra hcon
      have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    -- `qx ≥ 1`（`A + x ≥ Lng N - 1 = j₋₂ + w`）
    have hqx1 : 1 ≤ qx := by
      rw [hqxdef, Nat.le_div_iff_mul_le hw]
      omega
    have eSx : entry (seg (oper N n) A E) 0 x =
        entry N 0 (parent N 1 (Lng N - 1) + sx) +
          qx * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by
      have hdecode := entry_oper_d1pos_zero_68 N n qx sx L notzero hp i1z
        hqxn hsxw
      have hidx : parent N 1 (Lng N - 1) +
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx = A + x := by omega
      rw [hidx] at hdecode
      have hread : entry (seg (oper N n) A E) 0 x =
          entry (oper N n) 0 (A + x) :=
        entry_seg (oper N n) A E 0 x (by omega)
      rw [hread, hdecode]
    have hfloorle : entry N 0 (parent N 1 (Lng N - 1)) ≤
        entry N 0 (parent N 1 (Lng N - 1) + sx) :=
      oper_d1pos_period_row0_floor_rb N sx hp i1z j0lt (by omega)
    have hmulq : 1 * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) ≤
      qx * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) :=
      Nat.mul_le_mul_right _ hqx1
    have h1m : 1 * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) =
      entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)) :=
      Nat.one_mul _
    omega
  have hjjlt : parent N 1 (Lng N - 1) - A < Lng N - 1 - A := by omega
  have hclt := anchor_lt_of_uniform_witness_rb (seg (oper N n) A E)
    (Lng N - 1 - A) (parent N 1 (Lng N - 1) - A) hST multi hjjlt hwit
  omega

/-- Isabelle `oper_d1pos_anchor_coincide_regA2` (pss_mechanized.thy:16390)。
regime A の anchor 一致、clt/cNlt 不要形（内部で導出）。 -/
theorem oper_d1pos_anchor_coincide_regA2
    (N : PS) (A E n : ℕ)
    (L : 1 < Lng N)
    (notzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (n1 : 1 ≤ n)
    (Abnd : A < parent N 1 (Lng N - 1))
    (Ele : Lng N - 1 ≤ E)
    (Eub : E < Lng (oper N n))
    (dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (multi : 1 < (P (seg (oper N n) A E)).length)
    (multiN : 1 < (P (seg N A (Lng N - 1))).length) :
    (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 =
        (IdxSum (P (seg N A (Lng N - 1)))).getD
          ((P (seg N A (Lng N - 1))).length - 1) 0 ∧
      entry (seg (oper N n) A E) 0
          ((IdxSum (P (seg (oper N n) A E))).getD
            ((P (seg (oper N n) A E)).length - 1) 0) =
        entry (seg N A (Lng N - 1)) 0
          ((IdxSum (P (seg N A (Lng N - 1)))).getD
            ((P (seg N A (Lng N - 1))).length - 1) 0) ∧
      entry (seg (oper N n) A E) 1
          ((IdxSum (P (seg (oper N n) A E))).getD
            ((P (seg (oper N n) A E)).length - 1) 0) ≤
        entry (seg N A (Lng N - 1)) 1
          ((IdxSum (P (seg N A (Lng N - 1)))).getD
            ((P (seg N A (Lng N - 1))).length - 1) 0) := by
  have hLng := length_oper_d1pos_68 N n L notzero hp i1z
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have AltN : A < Lng N - 1 := by omega
  have lenSraw : Lng (seg (oper N n) A E) = E + 1 - A :=
    length_seg (oper N n) A E
  have lenNs : Lng (seg N A (Lng N - 1)) = (Lng N - 1) + 1 - A :=
    length_seg N A (Lng N - 1)
  have hST : TPS (seg (oper N n) A E) := TPS_of_P_multi_rb _ multi
  have hSnT : TPS (seg N A (Lng N - 1)) := TPS_of_P_multi_rb _ multiN
  have bnd : Lng N - 1 < Lng (oper N n) := by omega
  have n2 : 1 < n := by
    by_contra hcon
    have hn1' : n = 1 := by omega
    subst hn1'
    omega
  -- `m ≥ 1`（`0 < cN ≤ m`）
  obtain ⟨hcN0, hcNle, _, _, _⟩ :=
    P_last_anchor_68 (seg N A (Lng N - 1)) hSnT multiN
  have hmpos : 0 < Lng (seg N A (Lng N - 1)) - 1 := by omega
  -- 逐語接頭辞一致（shamt = 0）: `A + i < Lng N - 1` で全対一致
  have hpre : seg (oper N n) A (A + (Lng (seg N A (Lng N - 1)) - 1 - 1)) =
      seg N A (A + (Lng (seg N A (Lng N - 1)) - 1 - 1)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : A + i < Lng N - 1 := by
        simp only [length_seg] at h1
        omega
      rw [seg_getElem_68 (oper N n) A _ i h1, seg_getElem_68 N A _ i h2,
        entry_oper_lt_last_68 N n 0 (A + i) L n1 (Or.inl rfl) hi,
        entry_oper_lt_last_68 N n 1 (A + i) L n1 (Or.inr rfl) hi]
  have hshift0 : seg (seg (oper N n) A E) 0
      (Lng (seg N A (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0 (seg (seg N A (Lng N - 1)) 0
        (Lng (seg N A (Lng N - 1)) - 1 - 1)) := by
    have h1 := seg_of_seg_68 (oper N n) A E 0
      (Lng (seg N A (Lng N - 1)) - 1 - 1) (by omega) (by omega)
    have h2 := seg_of_seg_68 N A (Lng N - 1) 0
      (Lng (seg N A (Lng N - 1)) - 1 - 1) (by omega) (by omega)
    rw [h1, h2, Nat.add_zero, hpre, IncrFirstN_zero_rb]
  -- 境界 entry: 行 0 は一致（+0）、行 1 は `≤`
  have hAm : A + (Lng (seg N A (Lng N - 1)) - 1) = Lng N - 1 := by omega
  have hbound0 : entry (seg (oper N n) A E) 0
      (Lng (seg N A (Lng N - 1)) - 1) =
      entry (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1) + 0 := by
    have hread : entry (seg (oper N n) A E) 0
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry (oper N n) 0 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg (oper N n) A E 0 _ (by omega)
    have hreadN : entry (seg N A (Lng N - 1)) 0
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry N 0 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg N A (Lng N - 1) 0 _ (by omega)
    rw [hread, hreadN, hAm, Nat.add_zero]
    exact oper_d1pos_row0_agree N n (Lng N - 1) L notzero hp i1z j0lt bnd
      (le_refl _)
  have hbound1 : entry (seg (oper N n) A E) 1
      (Lng (seg N A (Lng N - 1)) - 1) ≤
      entry (seg N A (Lng N - 1)) 1 (Lng (seg N A (Lng N - 1)) - 1) := by
    have hread : entry (seg (oper N n) A E) 1
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry (oper N n) 1 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg (oper N n) A E 1 _ (by omega)
    have hreadN : entry (seg N A (Lng N - 1)) 1
        (Lng (seg N A (Lng N - 1)) - 1) =
        entry N 1 (A + (Lng (seg N A (Lng N - 1)) - 1)) :=
      entry_seg N A (Lng N - 1) 1 _ (by omega)
    have hdecode := entry_oper_d1pos_one_68 N n 1 0 L notzero hp i1z n2 hw
    rw [show parent N 1 (Lng N - 1) +
        1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = Lng N - 1
      from by omega] at hdecode
    rw [hread, hreadN, hAm, hdecode]
    simp only [Nat.add_zero]
    exact oper_d1pos_ctx_r1le N hp i1z
  -- スパン・anchor 上界
  have mleS : Lng (seg N A (Lng N - 1)) - 1 ≤
      Lng (seg (oper N n) A E) - 1 := by omega
  have hclt := oper_d1pos_clt_regA_rb N A E n L notzero hp i1z j0lt n1
    Abnd Ele Eub dpos multi
  have cleM : (IdxSum (P (seg (oper N n) A E))).getD
      ((P (seg (oper N n) A E)).length - 1) 0 ≤
      Lng (seg N A (Lng N - 1)) - 1 := by omega
  -- 成分数一致 → unified anchor 一致（shamt = 0）
  have hlenP := P_length_eq_of_shift_prefix_boundary_68
    (seg (oper N n) A E) (seg N A (Lng N - 1)) 0 hST hSnT multi multiN
    mleS cleM hshift0 hbound0
  obtain ⟨h1, h2, h3, _⟩ := last_anchor_coincide_shift_prefix_68
    (seg (oper N n) A E) (seg N A (Lng N - 1)) 0 hST hSnT multi multiN
    mleS cleM hlenP hshift0 hbound0 hbound1
  refine ⟨h1, by omega, h3⟩

end PSS

#print axioms PSS.oper_d1pos_lenPSeq_unified
#print axioms PSS.D1pos_oper_d1pos_lenPSeq_unified_holds
#print axioms PSS.oper_d1pos_anchor_coincide_period_unified
#print axioms PSS.oper_d1pos_ctx_multiM
#print axioms PSS.D1pos_oper_d1pos_ctx_multiM_holds
#print axioms PSS.oper_d1pos_row0_agree
#print axioms PSS.oper_d1pos_ctx_le0Np
#print axioms PSS.D1pos_oper_d1pos_ctx_le0Np_holds
#print axioms PSS.oper_d1pos_nth_below
#print axioms PSS.oper_d1pos_ctx_stop_of_tnc
#print axioms PSS.oper_d1pos_clt_regB
#print axioms PSS.oper_d1pos_anchor_coincide_regB
#print axioms PSS.oper_d1pos_anchor_coincide_regB2
#print axioms PSS.oper_d1pos_branch_lowshift_regB_plug
#print axioms PSS.oper_d1pos_anchor_coincide_regA2
