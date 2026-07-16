import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Trans-preserves-zeroT»
import «6».«6.3-marked-slice»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»
import «6».«6.6-one-column»
import «5».«5.1-ancestor-tree»
import «5».«5.1-ancestor-basic»

/-!
# §8.1 補題（条件(I)か(III)の下での `c₁` 前後の具体表示）

- 原文: `tmp/content.md` L2923 付近（「補題（条件(I)か(III)の下での\(c_1\)前後の具体表示）」）。
  5 部構成（(1)/(2)/(3-1)(3-2)/(4-1)(4-2)/(5)）。
- 訂正: **A20**（part (1) の切片等式 `Trans((M_j)_{j=j₀}^{j₁-1}) = c₁` は
  `j₀ = j₁ - 1` の非簡約 1 列切片で偽。訂正案どおりガード
  「`j₀ < j₁ - 1` または `M_{0,j₀} = M_{1,j₀}`（切片が簡約）」付きで移植し、
  原文形の反例 `M = ((0,0),(1,0),(2,0))` を `c1_around_1_original_false` に機械証明で併記）
  ＋ **A21**（part (5) の `j₀^N = j′₀` は条件(III)で偽。条件(I)を仮定した訂正形で移植し、
  原文形の反例 `M = ((0,0),(1,1),(2,1))`, `n = 2` を `c1_around_5_original_false` に
  機械証明で併記）
- Isabelle: `p_8_1_condI_III_c1_around` (isabelle/pss_paper.thy:1710) の証明は
  `m_8_1_c1_around_part1_noeq` / `m_8_1_c1_around_part1` / `m_8_1_c1_around_part2` /
  `m_8_1_c1_around_part3_1` / `m_8_1_c1_around_part3_2` / `m_8_1_c1_around_part4_*` /
  `m_8_1_c1_around_part5`（いずれも isabelle/layerB/pss_wip.thy）
- 依存: «7».«7.4-Mark-Trans-repr»（`Mark_Trans_repr`, `seg_Pred_eq`）,
  «7».«7.3-Trans-preserves-zeroT», «6».«6.3-marked-slice», «6».«6.4-FirstNodes-Joints-mono»,
  «6».«6.6-P-condAB», «6».«6.6-condAB-coeff», «5».«5.1-ancestor-tree»
- 状態: 🚨 部分証明。part (1)（A20 訂正形・full）/ part (2) / part (3-2)（空虚）と
  反例 2 件（A20/A21）は sorry 0。part (3-1) / part (4-1)(4-2) / part (5) は sorry
  （Isabelle 側の `Mark_gap_peel`（gap 剥がし）・part4 前剥がし・§8.3 kind0 基盤が
  Lean に未移植のため）。
-/

namespace PSS

/-! ## 行 1 の許容化祖先関係（Isabelle `adm_row1_ancestry` の私的再証明）

`7.3-Trans-welldefined.lean` に同内容の補題があるが private のため、ここに再掲する。
共有層 `PSS/Adm.lean` への昇格候補（needs 参照）。 -/

private theorem le1Aux_chain_c1a (M : PS) (a : ℕ) (b fuel : ℕ)
    (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → nextrel1 M (j - 1) j = true)
    (hfuel : b - a ≤ fuel) : le1Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by omega
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      by_cases heq : a = b
      · subst b
        simp [le1Aux]
      · have hablt : a < b := lt_of_le_of_ne hab heq
        rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        refine ⟨b - 1, by omega, hstep b hablt (le_refl _), ?_⟩
        apply ih (b := b - 1)
        · omega
        · intro j haj hjb
          exact hstep j haj (by omega)
        · omega

private theorem adm_row1_ancestry_c1a (M : PS) (j : ℕ)
    (hM : TPS M) (hj : j ≤ Lng M - 1) :
    leR M 1 (Adm M j) j = true := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : j < Lng M := by omega
  have haLe : Adm M j ≤ j := Adm_le M j
  have haL : Adm M j < Lng M := haLe.trans_lt hjL
  have hstep : ∀ k, Adm M j < k → k ≤ j →
      nextrel1 M (k - 1) k = true := by
    intro k hak hkj
    have hkadm : adm M k = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M k j hk hkj
      omega
    have hnadm : nadm M k = true := by
      simpa [adm] using hkadm
    have hpair : nextR M 1 (k - 1) k = true ∧
        nextR M 1 k (k + 1) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · exact hn
    simpa [nextR] using hpair.1
  have haux : le1Aux M (Lng M) (Adm M j) j = true :=
    le1Aux_chain_c1a M (Adm M j) j (Lng M) haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_refl_c1a (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_row0_c1a (M : PS) (fuel : ℕ) (a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_c1a]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_c1a]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

private theorem row1_row0_c1a (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_row0_c1a M (Lng M) a b hM hh.1.2 hh.2

/-! ## part (1) — A20 訂正形（切片等式は「`j₀ < j₁ - 1` または切片が簡約」ガード付き） -/

/-- 非零対角 1 列の翻訳。`TransAux_singleton`（`7.3-two-column.lean`、private）の再掲。 -/
private theorem Trans_singleton_c1a (v : ℕ) (hv : v ≠ 0) :
    Trans [(v, v)] = Dprin (v : ℕ∞) BZero := by
  have hred : reduced [(v, v)] = true := by
    have hfix := Red_singleton v v
    simp [reduced, hfix]
  have hfuel : transFuel [(v, v)] = (transFuel [(v, v)] - 1) + 1 := by
    simp [transFuel]
  rw [Trans, hfuel, TransAux]
  simp [hred, lastIdx, entry, Dprin, BZero, hv]

/-- 原文 part (1)（訂正 A20 適用後）: `t₁ ≠ 0`、`M` は条件(I)か(III)を満たし、
`c₁ ∈ PT_B`。切片等式 `Trans((M_j)_{j=j₀}^{j₁-1}) = c₁` は
「`j₀ < j₁ - 1` または `M_{0,j₀} = M_{1,j₀}`（すなわち切片が簡約）」に制限する。 -/
theorem c1_around_1 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M)) :
    transT1 M ≠ BZero ∧
    (transCondI M = true ∨ transCondIII M = true) ∧
    ((transJ0 M < transJ1 M - 1 ∨
        entry M 0 (transJ0 M) = entry M 1 (transJ0 M)) →
        Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M) ∧
    transC1 M ∈ T_B ∧ (∃ p, transC1 M = .trm [p]) := by
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hj1' : 1 < Lng M - 1 := by omega
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS (Pred M) hpredR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  -- (1a) `t₁ ≠ 0`: `Pred M` は零項でない
  have ht1 : Trans (Pred M) ≠ BZero := by
    intro h0
    have hz : zeroT (Pred M) = true :=
      (Trans_preserves_zeroT (Pred M) hpredT).mpr h0
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    omega
  -- (1b) 条件(I)か(III)
  have hcond : transCondI M = true ∨ transCondIII M = true := by
    by_cases hz : entry M 1 (lastIdx M) = 0
    · left
      simp only [transCondI, Bool.and_eq_true, beq_iff_eq]
      exact ⟨hz, hadm⟩
    · right
      have hpos : 0 < entry M 1 (lastIdx M) := Nat.pos_of_ne_zero hz
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hpos, hge⟩, hadm⟩
  -- 基点 `(Pred M, j₀) ∈ Marked`（`adm M j₀` より `Adm M j₀ = j₀`）
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hAdmEq : Adm M (transJ0 M) = transJ0 M := by
    simp [Adm, hadm]
  have hmarked : Marked (Pred M) (transJ0 M) := by
    have h := Marked_Pred_Adm M hM hlen hp
    rw [← htJ0] at h
    rwa [hAdmEq] at h
  -- `c₁ = Mark (Pred M) j₀`
  have hc1def : transC1 M = Mark (Pred M) (transJ0 M) := by
    simp only [transC1, transJm1, hAdmEq]
  -- (1c) `c₁ ∈ T_B` かつ principal
  have hc1TB : transC1 M ∈ T_B := by
    rw [hc1def]
    exact Mark_mem_T_B (Pred M) (transJ0 M) hpredR hmarked
  have hprinc : ∃ p, transC1 M = .trm [p] := by
    rw [hc1def]
    exact marked_component_principal ht1
      (Trans_Mark_mem_MarkedB (Pred M) (transJ0 M) hpredR hmarked)
  -- `j₀ < j₁`（親は真に手前）と `j₀` の行 0 祖先性
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    rw [htJ0]
    exact hasParent_next_fseq M 0 (Lng M - 1) hp
  have hj0lt : transJ0 M < Lng M - 1 := by
    rw [htJ0]
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M _ _ hnpar
  -- A20 ガード付き切片等式・第 1 分岐（§7.4 の `Mark` の `Trans` 表示の応用）
  have hrepr : transJ0 M < transJ1 M - 1 →
      Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M := by
    intro g
    have hlt : transJ0 M < Lng (Pred M) - 1 := by omega
    have repr := Mark_Trans_repr (Pred M) (transJ0 M) hmarked hpredR hlt
    have hLP1 : Lng (Pred M) - 1 = transJ1 M - 1 := by omega
    have repr' : Mark (Pred M) (transJ0 M) =
        Trans (seg (Pred M) (transJ0 M) (transJ1 M - 1)) := by
      rw [repr, hLP1]
    have hsegP : seg (Pred M) (transJ0 M) (transJ1 M - 1) =
        seg M (transJ0 M) (transJ1 M - 1) :=
      seg_Pred_eq M _ _ hlen (by omega) (by omega)
    rw [hc1def, repr', hsegP]
  -- 第 2 分岐: `j₀ = j₁ - 1` かつ切片 `((M_{0,j₀},M_{1,j₀}))` が簡約（対角）
  have hsing : transJ0 M = transJ1 M - 1 →
      entry M 0 (transJ0 M) = entry M 1 (transJ0 M) →
      Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M := by
    intro hj0eq hv
    -- `c₁` は `Pred M` の右端基点: `D_{M_{1,j₀}} 0`
    have hm : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
    have hbound : Mark (Pred M) (transJ0 M) =
        Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero :=
      Mark_Pred_terminal_boundary M (transJ0 M) hm hR (by omega) (by omega)
    -- `M_{1,j₀} = M_{0,j₀} > 0`（単項性: 行 0 の祖先で係数は真に増える）
    have hfull : leR M 0 0 (Lng M - 1) = true := by
      have hh := hmono
      simp only [monoT, Bool.and_eq_true] at hh
      exact hh.2
    have hpos : entry M 0 0 < entry M 0 (transJ0 M) :=
      ancestor_basic_1 M 0 (transJ0 M) (Lng M - 1) hM (by omega)
        (by omega) hfull
    have hvpos : entry M 1 (transJ0 M) ≠ 0 := by omega
    -- 切片は対角 1 列 `((v,v))`
    have hidx : transJ1 M - 1 = transJ0 M := by omega
    have hseg1 : seg M (transJ0 M) (transJ0 M) =
        [(entry M 0 (transJ0 M), entry M 1 (transJ0 M))] := by
      simp [seg]
    rw [hidx, hseg1, hv, hc1def, hbound]
    exact Trans_singleton_c1a (entry M 1 (transJ0 M)) hvpos
  have hslice : (transJ0 M < transJ1 M - 1 ∨
      entry M 0 (transJ0 M) = entry M 1 (transJ0 M)) →
      Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M := by
    rintro (g | hv)
    · exact hrepr g
    · rcases Nat.lt_or_ge (transJ0 M) (transJ1 M - 1) with g | g'
      · exact hrepr g
      · exact hsing (by omega) hv
  exact ⟨ht1, hcond, hslice, hc1TB, hprinc⟩

/-! ## part (2) — 基点の切片遺伝 -/

/-- 原文 part (2): `j′₀ ≤ j₁ - 2` かつ `(Pred M, j′₋₁) ∈ Marked` かつ
`((M_j)_{j=j′₋₁}^{j₁-1}, j₀ - j′₋₁) ∈ Marked`。ここで `j′₋₁ = Adm M j′₀`。 -/
theorem c1_around_2 (M : PS) (j₀' : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (_hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true) :
    j₀' ≤ transJ1 M - 2 ∧
    Marked (Pred M) (Adm M j₀') ∧
    Marked (seg M (Adm M j₀') (transJ1 M - 1)) (transJ0 M - Adm M j₀') := by
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hj1' : 1 < Lng M - 1 := by omega
  have hlen : 1 < Lng M := by omega
  -- `j₀` は `j₁ = Lng M - 1` の行 0 の親
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    rw [htJ0]
    exact hasParent_next_fseq M 0 (Lng M - 1) hp
  have hj0lt : transJ0 M < Lng M - 1 := by
    rw [htJ0]
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M _ _ hnpar
  -- `j′₀` は `j₀` の行 0 の親: `j′₀ < j₀` と行 0 祖先
  have hn0 : nextrel0 M j₀' (transJ0 M) = true := by
    simpa [nextR] using np
  have hj0'lt : j₀' < transJ0 M := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hle0' : leR M 0 j₀' (transJ0 M) = true := nextR0_leR M _ _ np
  -- 許容化 `j′₋₁ = Adm M j′₀ ≤ j′₀`、許容
  have haLe : Adm M j₀' ≤ j₀' := Adm_le M j₀'
  have haAdm : adm M (Adm M j₀') = true := Adm_adm M j₀'
  -- 行 1 祖先 → 行 0 祖先 → `j₁` までの連鎖
  have hle1a : leR M 1 (Adm M j₀') j₀' = true :=
    adm_row1_ancestry_c1a M j₀' hM (by omega)
  have hle0a : leR M 0 (Adm M j₀') j₀' = true :=
    row1_row0_c1a M _ _ hM hle1a
  have hchain : leR M 0 (Adm M j₀') (Lng M - 1) = true :=
    row0_transitive M _ _ _ hM
      (row0_transitive M _ _ _ hM hle0a hle0') hleJ0
  -- `(M, j′₋₁) ∈ Marked` → `(Pred M, j′₋₁) ∈ Marked`
  have hmarkedA : Marked M (Adm M j₀') := ⟨hM, haAdm, hchain⟩
  have hpredA : Marked (Pred M) (Adm M j₀') :=
    Marked_Pred M _ hM hlen hmarkedA (by omega)
  -- `(M, j₀) ∈ Marked` → 切片遺伝
  have hmarkedJ0 : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
  have hsegMk : Marked (seg M (Adm M j₀') (Lng M - 1 - 1))
      (transJ0 M - Adm M j₀') :=
    marked_slice M (transJ0 M) (Adm M j₀') (Lng M - 1 - 1) hmarkedJ0
      (by omega) (by omega) (by omega)
  refine ⟨by omega, hpredA, ?_⟩
  have hidx : transJ1 M - 1 = Lng M - 1 - 1 := by omega
  rw [hidx]
  exact hsegMk

/-! ## part (3) — `j′₀ + 1 = j₀`（隣接する次親） -/

/-- 原文 part (3-2) 単独（sorry 0 で監査可能な形）: `j′₀ + 1 = j₀` のとき、前件
`j′₋₁ < j′₀ ∧ M_{1,j′₀} ≥ M_{1,j₀}` は空虚に偽である。`Adm M j′₀ < j′₀` は
`j′₀` の非 `M` 許容を強制し、非許容の定義から `(1,j′₀) <^Next (1,j′₀+1)`、
隣接性 `j′₀ + 1 = j₀` から `M_{1,j′₀} < M_{1,j₀}` となって前件と矛盾する。
Isabelle: `m_8_1_c1_around_part3_2`。 -/
theorem c1_around_3_2 (M : PS) (j₀' : ℕ) (_hR : RTPS M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 = transJ0 M) :
    Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀' →
      Mark (Pred M) (Adm M j₀')
        = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
            (Dprin (entry M 1 j₀' : ℕ∞) (transC1 M)) := by
  rintro ⟨hAdmLt, hgeE⟩
  exfalso
  -- `Adm M j′₀ < j′₀` は `¬ adm M j′₀` を強制する
  have hnotadm : adm M j₀' = false := by
    cases hja : adm M j₀' with
    | true =>
        have : Adm M j₀' = j₀' := by simp [Adm, hja]
        omega
    | false => rfl
  have hnadm : nadm M j₀' = true := by
    have h := hnotadm
    simp only [adm, Bool.not_eq_false'] at h
    exact h
  -- `j′₀ < Lng M`（next 関係から）
  have hn0 : nextrel0 M j₀' (transJ0 M) = true := by
    simpa [nextR] using np
  have hj0'L : j₀' < Lng M := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.1.1
  -- 非許容の第 2 分岐: `(1, j′₀) <^Next (1, j′₀ + 1)`
  have hpair : nextR M 1 (j₀' - 1) j₀' = true ∧
      nextR M 1 j₀' (j₀' + 1) = true := by
    have hn := hnadm
    simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at hn
    rcases hn with hn | hn
    · omega
    · exact hn
  have hnr1 : nextrel1 M j₀' (j₀' + 1) = true := by
    simpa [nextR] using hpair.2
  have hlt1 : entry M 1 j₀' < entry M 1 (j₀' + 1) := by
    have hh := hnr1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  rw [hadj] at hlt1
  omega

/-- 原文 part (3): `j′₀ + 1 = j₀` のとき
(3-1) `j′₋₁ = j′₀` または `M_{1,j′₀}+1 = M_{1,j₀}` ならば
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}} c₁`、
(3-2) `j′₋₁ < j′₀` かつ `M_{1,j′₀} ≥ M_{1,j₀}` ならば
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}} D_{M_{1,j′₀}} c₁`。
(3-2) の前件は空虚に偽（`Adm M j′₀ < j′₀` は `j′₀` の非許容を強制し、
隣接性から `M_{1,j′₀} < M_{1,j₀}` になる）。

(3-1) は Isabelle `m_8_1_c1_around_part3_1`（`Mark_gap_peel` 経由）に対応するが、
gap 剥がしエンジンが Lean 未移植のため sorry。 -/
theorem c1_around_3 (M : PS) (j₀' : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 = transJ0 M) :
    ((Adm M j₀' = j₀' ∨ entry M 1 j₀' + 1 = entry M 1 (transJ0 M)) →
        Mark (Pred M) (Adm M j₀')
          = Dprin (entry M 1 (Adm M j₀') : ℕ∞) (transC1 M)) ∧
    (Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀' →
        Mark (Pred M) (Adm M j₀')
          = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
              (Dprin (entry M 1 j₀' : ℕ∞) (transC1 M))) := by
  constructor
  · -- (3-1): Isabelle 版は `Mark_gap_peel`（間隙が全て非許容のとき
    -- `Mark Q a = D_{Q_{1,a}} (Mark Q b)`）で閉じる。Lean 未移植。
    sorry
  · -- (3-2): 前件が空虚に偽（`c1_around_3_2` に単独 green 版）
    exact c1_around_3_2 M j₀' hR np hadj

/-! ## part (4) — `j′₀ + 1 < j₀`（離れた次親） -/

/-- 原文 part (4): `j′₀ + 1 < j₀` のとき
(4-1) `j′₋₁ = j′₀` または `M_{1,j′₀}+1 = M_{1,j₀}` ならば一意な `t′₂ ∈ T_B` が存在して
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}}(t′₂ + c₁)`、
(4-2) `j′₋₁ < j′₀` かつ `M_{1,j′₀} ≥ M_{1,j₀}` ならば一意な `(t′₃,t′₄) ∈ T_B²` が存在して
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}}(t′₃ + D_{M_{1,j′₀}}(t′₄ + c₁))`。

Isabelle 側は `m_8_1_c1_around_part4_setup` / `_Nred` / `_Adm0` / `_cond41` / `_cond42` /
`_TransN_41` / `_TransN_42` / `_segpos` を経て `m_8_1_c1_around_part4_1` /
`m_8_1_c1_around_part4_2`（約 3000 行の前剥がし基盤）。Lean 未移植のため sorry。 -/
theorem c1_around_4 (M : PS) (j₀' : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    ((Adm M j₀' = j₀' ∨ entry M 1 j₀' + 1 = entry M 1 (transJ0 M)) →
        ∃! t₂' : BT, Mark (Pred M) (Adm M j₀')
          = Dprin (entry M 1 (Adm M j₀') : ℕ∞) (addBT t₂' (transC1 M))) ∧
    (Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀' →
        ∃! t34 : BT × BT, Mark (Pred M) (Adm M j₀')
          = Dprin (entry M 1 (Adm M j₀') : ℕ∞)
              (addBT t34.1 (Dprin (entry M 1 j₀' : ℕ∞)
                (addBT t34.2 (transC1 M))))) := by
  sorry

/-! ## part (5) — 基本列 `M[n]` の最終ブロック切片（A21 訂正形 = 条件(I)を仮定） -/

/-- 原文 part (5)（訂正 A21 適用後）: 条件(I)の下で、`n > 1`、
`idx = j₀ + (n-1)(j₁-j₀)`、`N = (M[n]_j)_{j=0}^{idx}` と置くと、
`(M[n], idx) ∈ Marked`、`(0,j′₀) <_{M[n]}^Next (0,idx)`、`j₁^N = idx`、
`j₀^N = j′₀`、`j₋₁^N = j′₋₁`、`t₁^N ≠ 0`、`N` は条件(VI)を満たさない。
（原文は条件(III)でも `j₀^N = j′₀` を主張するがこれは偽 — A21。
`c1_around_5_original_false` を参照。）

Isabelle `m_8_1_c1_around_part5`（§8.3 kind0 基盤 `Lng_operI` /
`oper_d0zero_prefix_to_lastblock` / `repr_parent_M_to_seg` / `adm_prefix_agree_eq`
に依存）。Lean 未移植のため sorry。 -/
theorem c1_around_5 (M : PS) (j₀' n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (hcondI : transCondI M = true)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hn : 1 < n) :
    Marked (oper M n) (transJ0 M + (n - 1) * (transJ1 M - transJ0 M)) ∧
    nextR (oper M n) 0 j₀'
      (transJ0 M + (n - 1) * (transJ1 M - transJ0 M)) = true ∧
    Lng (seg (oper M n) 0 (transJ0 M + (n - 1) * (transJ1 M - transJ0 M))) - 1
      = transJ0 M + (n - 1) * (transJ1 M - transJ0 M) ∧
    transJ0 (seg (oper M n) 0
      (transJ0 M + (n - 1) * (transJ1 M - transJ0 M))) = j₀' ∧
    transJm1 (seg (oper M n) 0
      (transJ0 M + (n - 1) * (transJ1 M - transJ0 M))) = Adm M j₀' ∧
    Trans (Pred (seg (oper M n) 0
      (transJ0 M + (n - 1) * (transJ1 M - transJ0 M)))) ≠ BZero ∧
    transCondVI (seg (oper M n) 0
      (transJ0 M + (n - 1) * (transJ1 M - transJ0 M))) = false := by
  sorry

/-! ## 原文形の反例（A20 / A21） -/

private theorem c1_around_1_cex_vals :
    (Trans (seg ([(0, 0), (1, 0), (2, 0)] : PS)
        (transJ0 [(0, 0), (1, 0), (2, 0)])
        (transJ1 [(0, 0), (1, 0), (2, 0)] - 1))
      == transC1 [(0, 0), (1, 0), (2, 0)]) = false := by
  decide

/-- 訂正 A20 の反例: `M = ((0,0),(1,0),(2,0))` は補題の全仮定を満たすが
（`j₀ = 1 = j₁ - 1` かつ `M_{0,j₀} = 1 ≠ 0 = M_{1,j₀}`、すなわち訂正後ガードの
両選言肢の外）、原文 part (1) の切片等式 `Trans((M_j)_{j=j₀}^{j₁-1}) = c₁` は
成り立たない（左辺 `0`、右辺 `D₀0`）。 -/
theorem c1_around_1_original_false :
    let M : PS := [(0, 0), (1, 0), (2, 0)]
    RTPS M ∧ monoT M = true ∧ adm M (transJ0 M) = true ∧ 1 < transJ1 M ∧
    entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) ∧
    transJ0 M = transJ1 M - 1 ∧
    entry M 0 (transJ0 M) ≠ entry M 1 (transJ0 M) ∧
    Trans (seg M (transJ0 M) (transJ1 M - 1)) ≠ transC1 M := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  intro h
  have hv := c1_around_1_cex_vals
  rw [h] at hv
  simp at hv

/-- 訂正 A21 の反例: `M = ((0,0),(1,1),(2,1))` は条件(III)の下で補題の全仮定を
満たすが（`j₀ = 1`、`j′₀ = 0`、`n = 2`）、原文 part (5) の `j₀^N = j′₀` は
成り立たない（`N = ((0,0),(1,1),(2,0))` の右端の親は `1 ≠ 0 = j′₀`）。 -/
theorem c1_around_5_original_false :
    let M : PS := [(0, 0), (1, 1), (2, 1)]
    RTPS M ∧ monoT M = true ∧ adm M (transJ0 M) = true ∧ 1 < transJ1 M ∧
    entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) ∧
    transCondIII M = true ∧
    nextR M 0 0 (transJ0 M) = true ∧
    parent (seg (oper M 2) 0
        (transJ0 M + (2 - 1) * (transJ1 M - transJ0 M))) 0
      (Lng (seg (oper M 2) 0
        (transJ0 M + (2 - 1) * (transJ1 M - transJ0 M))) - 1) ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  decide

#print axioms c1_around_1
#print axioms c1_around_2
#print axioms c1_around_3_2
#print axioms c1_around_3
#print axioms c1_around_4
#print axioms c1_around_5
#print axioms c1_around_1_original_false
#print axioms c1_around_5_original_false

end PSS
