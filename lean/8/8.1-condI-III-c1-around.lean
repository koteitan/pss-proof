import «8».«8.3-kind0-base-basepoint»
import «6».«6.6-reduced-fseq»
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

/-! ## part (3-1) エンジン層 1/3: 全非許容ギャップの 2 塔
（Isabelle `Trans_gap_2tower`, layerB/pss_wip.thy:19569）

簡約 mono `N`・両端 Marked・内部全非許容なら
`Trans N = D_{N₁,₀}(D_{N₁,last} 0)`。Isabelle は Trans 再帰の手展開だったが、
Lean では `Mark_zero_eq_Trans`＋`Mark_transJm1_eq_transC2`（7.4-Mark-Trans-repr）
経由で `Trans N = transC2 N` が既存補題 2 本から出るため大幅に短い。 -/

private theorem adm_zero_gp (M : PS) : adm M 0 = true := by
  simp [adm, nadm, nextR, nextrel1]

private theorem adm_last_gp (M : PS) : adm M (Lng M - 1) = true := by
  have h1 : nextrel1 M (Lng M - 1) (Lng M - 1 + 1) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
    have := h.1.1.1.1.2
    omega
  simp [adm, nadm, nextR, h1]

private theorem le0Aux_refl_gp (M : PS) (fuel j : ℕ) : le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_gp (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_gp]

private theorem find_adm_zero_gp (M : PS) :
    ∀ j, adm M 0 = true → (∀ k, 1 ≤ k → k < j → adm M k = false) → 0 < j →
      (((List.range j).reverse.find? (fun j' => adm M j')).getD 0) = 0
  | 0, _, _, h0 => absurd h0 (by omega)
  | 1, hadm0, _, _ => by
      simp [List.range_succ, hadm0]
  | (j + 2), hadm0, hfail, _ => by
      rw [show List.range (j + 2) = List.range (j + 1) ++ [j + 1] from
        List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      rw [List.find?_cons_of_neg (by
        rw [hfail (j + 1) (by omega) (by omega)]
        simp)]
      exact find_adm_zero_gp M (j + 1) hadm0
        (fun k h1 hk => hfail k h1 (by omega)) (by omega)

/-- 全非許容ギャップの下では許容化は `0` に落ちる（Isabelle `Adm_eq_0_of_nadm_below`）。 -/
private theorem Adm_eq_zero_of_nadm_below_gp (M : PS) (j : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ j → adm M k = false) : Adm M j = 0 := by
  unfold Adm
  by_cases hj : j = 0
  · subst hj
    simp [adm_zero_gp]
  · have hja : adm M j = false := h j (by omega) (le_refl j)
    rw [hja]
    simp only [Bool.false_eq_true, if_false]
    exact find_adm_zero_gp M j (adm_zero_gp M)
      (fun k h1 hk => h k h1 (by omega)) (by omega)

private theorem Trans_gap_2tower_aux_gp : ∀ (n : ℕ) (N : PS), Lng N ≤ n → RTPS N →
    Marked N 0 → Marked N (Lng N - 1) → 1 < Lng N →
    (∀ k, 0 < k → k < Lng N - 1 → adm N k = false) →
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)
  | 0, N, hn, _, _, _, hL, _ => by omega
  | n + 1, N, hn, hR, hm0, hmL, hL, hgap => by
      have hNT : TPS N := RTPS_TPS N hR
      have hmono : monoT N = true := by
        have hz : zeroT N = false := by
          rw [Bool.eq_false_iff]
          intro h
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
          omega
        have hle : leR N 0 0 (Lng N - 1) = true := hm0.2.2
        simp [monoT, hz, hle]
      by_cases hL2 : Lng N = 2
      · -- 基底: 2 列
        have h2 := two_column_Trans N hR hmono hL2
        have hidx : Lng N - 1 = 1 := by omega
        rw [hidx, h2]
      · have hL3 : 2 < Lng N := by omega
        -- 行 0 の親は存在し（mono）、`transJm1 N = 0`
        have hpar0 : hasParent N 0 (Lng N - 1) = true :=
          mono_hasParent_row0 N hNT hmono (Lng N - 1) (by omega) (by omega)
        have hparlt : parent N 0 (Lng N - 1) < Lng N - 1 := by
          have hnx := hasParent_next_fseq N 0 (Lng N - 1) hpar0
          exact (nextR_implies_row0 N 0 _ _ hnx).1
        have hAdm0 : Adm N (lastParent N) = 0 := by
          apply Adm_eq_zero_of_nadm_below_gp
          intro k h1 hk
          have hklt : k < Lng N - 1 := by
            have : lastParent N < Lng N - 1 := by
              simpa [lastParent, lastIdx] using hparlt
            omega
          exact hgap k (by omega) hklt
        have hJm1 : transJm1 N = 0 := by
          simpa [transJm1, transJ0] using hAdm0
        -- `Pred N` の基本量
        have hPredEq : Pred N = N.take (Lng N - 1) := Pred_eq_take N hL
        have hPredL : Lng (Pred N) = Lng N - 1 := by
          rw [hPredEq]
          simp
        have hPredT : TPS (Pred N) := by
          apply List.ne_nil_of_length_pos
          change 0 < Lng (Pred N)
          omega
        have hRP : RTPS (Pred N) := RTPS_Pred N hR
        have ht₁ : Trans (Pred N) ≠ BZero := by
          intro h0
          have hzP := (Trans_preserves_zeroT (Pred N) hPredT).mpr h0
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP
          omega
        -- `Trans N = transC2 N`
        have hTC2 : Trans N = transC2 N := by
          have h1 := Mark_transJm1_eq_transC2 N hR hmono hL ht₁
          have h2 : Mark N 0 = Trans N := Mark_zero_eq_Trans N hR hm0
          rw [hJm1, h2] at h1
          exact h1
        -- IH を `Pred N` に
        have hm0P : Marked (Pred N) 0 := Marked_Pred N 0 hNT hL hm0 (by omega)
        have hmLP : Marked (Pred N) (Lng (Pred N) - 1) := by
          refine ⟨hPredT, adm_last_gp (Pred N), leR0_refl_gp (Pred N) _ (by omega)⟩
        have hgapP : ∀ k, 0 < k → k < Lng (Pred N) - 1 → adm (Pred N) k = false := by
          intro k hk0 hkL
          have hkN : k < Lng N - 2 := by omega
          have hadmN : adm N k = false := hgap k hk0 (by omega)
          have hnadmN : nadm N k = true := by
            simpa [adm] using hadmN
          have e1 : nextR (Pred N) 1 (k - 1) k = nextR N 1 (k - 1) k := by
            rw [hPredEq]
            exact nextR_take_adm N (Lng N - 1) 1 (k - 1) k (by omega) (by omega)
              (by omega)
          have e2 : nextR (Pred N) 1 k (k + 1) = nextR N 1 k (k + 1) := by
            rw [hPredEq]
            exact nextR_take_adm N (Lng N - 1) 1 k (k + 1) (by omega) (by omega)
              (by omega)
          have hpairN : nextR N 1 (k - 1) k = true ∧ nextR N 1 k (k + 1) = true := by
            simp only [nadm, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq] at hnadmN
            rcases hnadmN with h | h
            · exfalso
              omega
            · exact h
          have hnadmP : nadm (Pred N) k = true := by
            simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            right
            rw [e1, e2]
            exact hpairN
          simp [adm, hnadmP]
        have hIH := Trans_gap_2tower_aux_gp n (Pred N) (by omega) hRP hm0P hmLP
          (by omega) hgapP
        -- `Pred N` の行 1 entry は `N` のもの
        have he0 : entry (Pred N) 1 0 = entry N 1 0 := by
          rw [hPredEq]
          exact entry_take N (Lng N - 1) 1 0 (by omega)
        have hePidx : Lng (Pred N) - 1 = Lng N - 2 := by omega
        have heP : entry (Pred N) 1 (Lng (Pred N) - 1) = entry N 1 (Lng N - 2) := by
          rw [hePidx, hPredEq]
          exact entry_take N (Lng N - 1) 1 (Lng N - 2) (by omega)
        -- `transC1/transV/transT2` の値
        have hC1 : transC1 N = Trans (Pred N) := by
          have h0 : Mark (Pred N) 0 = Trans (Pred N) :=
            Mark_zero_eq_Trans (Pred N) hRP hm0P
          simp [transC1, hJm1, h0]
        have hC1v : transC1 N = Dprin (entry N 1 0 : ℕ∞)
            (Dprin (entry N 1 (Lng N - 2) : ℕ∞) BZero) := by
          rw [hC1, hIH, he0, heP]
        have hV : transV N = (entry N 1 0 : ℕ∞) := by
          simp [transV, hC1v, bpHeadV, Dprin]
        -- `j₁ - 1` は非許容 → 行 1 の辺 → 行 0 の隣接辺 → 両行の親 = `j₁ - 1`
        have hnadm1 : nadm N (Lng N - 2) = true := by
          have := hgap (Lng N - 2) (by omega) (by omega)
          simpa [adm] using this
        have hpair1 : nextR N 1 (Lng N - 2) (Lng N - 2 + 1) = true := by
          simp only [nadm, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at hnadm1
          rcases hnadm1 with h | h
          · exfalso
            omega
          · exact h.2
        have hj₁idx : Lng N - 2 + 1 = Lng N - 1 := by omega
        rw [hj₁idx] at hpair1
        have hnr1 : nextrel1 N (Lng N - 2) (Lng N - 1) = true := by
          simpa [nextR] using hpair1
        have hle0adj : le0 N (Lng N - 2) (Lng N - 1) = true := by
          have hh := hnr1
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
          exact hh.1.2
        have hnr0 : nextrel0 N (Lng N - 2) (Lng N - 1) = true := by
          have hb : le0 N (Lng N - 2) (Lng N - 2 + 1) = true := by
            rw [hj₁idx]
            exact hle0adj
          have hstep := le0_adjacent N (Lng N - 2) hb
          rwa [hj₁idx] at hstep
        have hpar0v : parent N 0 (Lng N - 1) = Lng N - 2 := by
          obtain ⟨p, hpnext, hpuniq⟩ :=
            (hasParent_iff_unique_fseq N 0 (Lng N - 1)).mp hpar0
          have h1 : Lng N - 2 = p := hpuniq _ (by simpa [nextR] using hnr0)
          have h2 : parent N 0 (Lng N - 1) = p :=
            parent_eq_of_unique_fseq N 0 (Lng N - 1) p hpnext hpuniq
          omega
        have hstrict1 : entry N 1 (Lng N - 2) < entry N 1 (Lng N - 1) := by
          have hh := hnr1
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
          exact hh.1.1.2
        have hpar1 : hasParent N 1 (Lng N - 1) = true := by
          rw [hasParent_iff_unique_fseq]
          refine ⟨Lng N - 2, by simpa [nextR] using hnr1, ?_⟩
          intro q hq
          have hq1 : nextrel1 N q (Lng N - 1) = true := by
            simpa [nextR] using hq
          by_contra hne
          have hqlt : q < Lng N - 1 := by
            have hh := hq1
            simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.1.1.2
          have hqlt1 : q < Lng N - 2 := by omega
          have hh := hq1
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true, List.mem_range] at hh
          have hval := hh.2 (Lng N - 2) (by omega)
          simp only [hqlt1, hle0adj, decide_true, Bool.and_true, Bool.not_true,
            Bool.false_or, decide_eq_true_eq] at hval
          omega
        have hpar1v : parent N 1 (Lng N - 1) = Lng N - 2 := by
          obtain ⟨p, hpnext, hpuniq⟩ :=
            (hasParent_iff_unique_fseq N 1 (Lng N - 1)).mp hpar1
          have h1 : Lng N - 2 = p := hpuniq _ (by simpa [nextR] using hnr1)
          have h2 : parent N 1 (Lng N - 1) = p :=
            parent_eq_of_unique_fseq N 1 (Lng N - 1) p hpnext hpuniq
          omega
        have hA : RedCondA N = true := (RTPS_condAB N hR).1
        have hstep1 : entry N 1 (parent N 1 (Lng N - 1)) + 1
            = entry N 1 (Lng N - 1) :=
          RedCondA_apply N hA 1 (Lng N - 1) (by omega) (by omega) hpar1
        rw [hpar1v] at hstep1
        -- 条件 (VI) 成立、(I)/(III)/(V) 不成立
        have hcondVI : transCondVI N = true := by
          simp only [transCondVI, lastIdx, lastParent, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq]
          rw [hpar0v]
          refine ⟨⟨by omega, by omega⟩, by omega⟩
        have hcondI : transCondI N = false := by
          rw [Bool.eq_false_iff]
          intro h
          simp only [transCondI, lastIdx, Bool.and_eq_true, beq_iff_eq] at h
          omega
        have hcondIII : transCondIII N = false := by
          rw [Bool.eq_false_iff]
          intro h
          simp only [transCondIII, lastIdx, lastParent, Bool.and_eq_true,
            decide_eq_true_eq] at h
          rw [hpar0v] at h
          omega
        have hcondV : transCondV N = false := by
          rw [Bool.eq_false_iff]
          intro h
          simp only [transCondV, lastIdx, lastParent, Bool.and_eq_true,
            decide_eq_true_eq, beq_iff_eq] at h
          rw [hpar0v] at h
          omega
        -- `transC2` の潰れ
        have hC2 : transC2 N = Dprin (transV N)
            (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) := by
          simp only [transC2, transC2Core, lastIdx, hcondI, hcondIII, hcondV,
            hcondVI]
          simp
        rw [hTC2, hC2, hV]

/-- 全非許容ギャップの 2 塔（Isabelle `Trans_gap_2tower`）。 -/
private theorem Trans_gap_2tower_gp (N : PS) (hR : RTPS N) (hm0 : Marked N 0)
    (hmL : Marked N (Lng N - 1)) (hL : 1 < Lng N)
    (hgap : ∀ k, 0 < k → k < Lng N - 1 → adm N k = false) :
    Trans N = Dprin (entry N 1 0 : ℕ∞)
      (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero) :=
  Trans_gap_2tower_aux_gp (Lng N) N (le_refl _) hR hm0 hmL hL hgap

/-! ## part (3-1) エンジン層 2/3: 右端へのギャップ剥がし
（Isabelle `Mark_gap_rightmost_peel`, layerB:19789）

`Mark Q a` を `Mark_Trans_repr` で値化し、切片を `Red` して 2 塔を適用。
`IncrFirstN` は行 1 の entry と許容性を変えない。 -/

private theorem adm_IncrFirstN_gp (k : ℕ) (M : PS) (j : ℕ) :
    adm (IncrFirstN k M) j = adm M j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem entry_IncrFirstN_one_gp (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) :
    entry (IncrFirstN n M) 1 j = entry M 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj, List.getElem_map]

private theorem Mark_gap_rightmost_peel_gp (Q : PS) (a : ℕ)
    (hQR : RTPS Q) (hma : Marked Q a) (hmb : Marked Q (Lng Q - 1))
    (hab : a < Lng Q - 1)
    (hgap : ∀ k, a < k → k < Lng Q - 1 → adm Q k = false) :
    Mark Q a = Dprin (entry Q 1 a : ℕ∞) (Mark Q (Lng Q - 1)) := by
  have hQT : TPS Q := RTPS_TPS Q hQR
  have hL : 1 < Lng Q := by omega
  have hzQ : zeroT Q = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
    omega
  have hmarkb : Mark Q (Lng Q - 1)
      = Dprin (entry Q 1 (Lng Q - 1) : ℕ∞) BZero :=
    Mark_rightmost1_forward Q hQR hzQ
  have hrepr : Mark Q a = Trans (seg Q a (Lng Q - 1)) :=
    Mark_Trans_repr Q a hma hQR hab
  have hleMa : leR Q 0 a (Lng Q - 1) = true := hma.2.2
  have hfacts := ancestor_slice_Red_IncrFirst Q a (Lng Q - 1) hQR hab
    (le_refl _) hleMa
  have hRedN : Red (Red (seg Q a (Lng Q - 1))) = Red (seg Q a (Lng Q - 1)) :=
    hfacts.1
  have hmonoN : monoT (Red (seg Q a (Lng Q - 1))) = true := hfacts.2.1
  have hIF : seg Q a (Lng Q - 1)
      = IncrFirstN (entry Q 0 a - entry Q 1 a) (Red (seg Q a (Lng Q - 1))) :=
    hfacts.2.2
  have hLS : Lng (seg Q a (Lng Q - 1)) = Lng Q - 1 + 1 - a := by
    simp [seg]
  have hLN : Lng (Red (seg Q a (Lng Q - 1))) = Lng Q - 1 + 1 - a := by
    have h1 : Lng (IncrFirstN (entry Q 0 a - entry Q 1 a)
        (Red (seg Q a (Lng Q - 1))))
        = Lng (Red (seg Q a (Lng Q - 1))) := by
      simp [IncrFirstN_eq_map]
    have h2 := congrArg Lng hIF
    rw [h1] at h2
    rw [← h2]
    simp [seg]
  have hLN1 : 1 < Lng (Red (seg Q a (Lng Q - 1))) := by omega
  have hNT : TPS (Red (seg Q a (Lng Q - 1))) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red (seg Q a (Lng Q - 1)))
    omega
  have hNR : RTPS (Red (seg Q a (Lng Q - 1))) := by
    show reduced (Red (seg Q a (Lng Q - 1))) = true
    have hne : Red (seg Q a (Lng Q - 1)) ≠ [] := hNT
    simp [reduced, hne, hRedN]
  have hSTrans : Trans (seg Q a (Lng Q - 1))
      = Trans (Red (seg Q a (Lng Q - 1))) := by
    apply Trans_Red
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg Q a (Lng Q - 1))
    omega
  -- 両端 Marked
  have hmonoLe : leR (Red (seg Q a (Lng Q - 1))) 0 0
      (Lng (Red (seg Q a (Lng Q - 1))) - 1) = true := by
    have hh := hmonoN
    simp only [monoT, Bool.and_eq_true] at hh
    exact hh.2
  have hN0M : Marked (Red (seg Q a (Lng Q - 1))) 0 :=
    ⟨hNT, adm_zero_gp _, hmonoLe⟩
  have hNlastM : Marked (Red (seg Q a (Lng Q - 1)))
      (Lng (Red (seg Q a (Lng Q - 1))) - 1) :=
    ⟨hNT, adm_last_gp _, leR0_refl_gp _ _ (by omega)⟩
  -- 内部の非許容性は `Q` から輸送される
  have hgapN : ∀ k, 0 < k → k < Lng (Red (seg Q a (Lng Q - 1))) - 1 →
      adm (Red (seg Q a (Lng Q - 1))) k = false := by
    intro k hk0 hkL
    have hadm1 : adm (seg Q a (Lng Q - 1)) k
        = adm (Red (seg Q a (Lng Q - 1))) k := by
      conv_lhs => rw [hIF]
      exact adm_IncrFirstN_gp _ _ _
    have hkS : k < Lng (seg Q a (Lng Q - 1)) := by omega
    have hadm2 : adm (seg Q a (Lng Q - 1)) k = adm Q (a + k) := by
      have e1 : nextR (seg Q a (Lng Q - 1)) 1 (k - 1) k
          = nextR Q 1 (a + (k - 1)) (a + k) :=
        nextR_seg_adm Q a (Lng Q - 1) 1 (k - 1) k (by omega) (by omega)
          (by omega) (by omega)
      have e2 : nextR (seg Q a (Lng Q - 1)) 1 k (k + 1)
          = nextR Q 1 (a + k) (a + (k + 1)) :=
        nextR_seg_adm Q a (Lng Q - 1) 1 k (k + 1) (by omega) (by omega)
          (by omega) (by omega)
      have i1 : a + (k - 1) = a + k - 1 := by omega
      have i2 : a + (k + 1) = a + k + 1 := by omega
      rw [i1] at e1
      rw [i2] at e2
      have d1 : decide (Lng (seg Q a (Lng Q - 1)) < k) = false := by
        simp
        omega
      have d2 : decide (Lng Q < a + k) = false := by
        simp
        omega
      simp only [adm, nadm, e1, e2, d1, d2]
    have hQside : adm Q (a + k) = false := hgap (a + k) (by omega) (by omega)
    rw [← hadm1, hadm2, hQside]
  -- 2 塔
  have htower := Trans_gap_2tower_gp (Red (seg Q a (Lng Q - 1))) hNR hN0M
    hNlastM hLN1 hgapN
  -- 行 1 entry の対応（`IncrFirstN` は行 1 を変えない）
  have hIF1 : ∀ j, j < Lng (Red (seg Q a (Lng Q - 1))) →
      entry (seg Q a (Lng Q - 1)) 1 j
      = entry (Red (seg Q a (Lng Q - 1))) 1 j := by
    intro j hj
    conv_lhs => rw [hIF]
    exact entry_IncrFirstN_one_gp _ _ j hj
  have he0 : entry (Red (seg Q a (Lng Q - 1))) 1 0 = entry Q 1 a := by
    have h1 := hIF1 0 (by omega)
    have h2 : entry (seg Q a (Lng Q - 1)) 1 0 = entry Q 1 (a + 0) :=
      entry_seg Q a (Lng Q - 1) 1 0 (by omega)
    rw [← h1, h2]
    simp
  have heLast : entry (Red (seg Q a (Lng Q - 1))) 1
      (Lng (Red (seg Q a (Lng Q - 1))) - 1) = entry Q 1 (Lng Q - 1) := by
    have h1 := hIF1 (Lng (Red (seg Q a (Lng Q - 1))) - 1) (by omega)
    have h2 : entry (seg Q a (Lng Q - 1)) 1
        (Lng (Red (seg Q a (Lng Q - 1))) - 1)
        = entry Q 1 (a + (Lng (Red (seg Q a (Lng Q - 1))) - 1)) :=
      entry_seg Q a (Lng Q - 1) 1 _ (by omega)
    have h3 : a + (Lng (Red (seg Q a (Lng Q - 1))) - 1) = Lng Q - 1 := by
      omega
    rw [← h1, h2, h3]
  rw [hrepr, hSTrans, htower, he0, heLast, hmarkb]

/-! ## part (3-1) エンジン層 3/3: 一般ギャップ剥がし
（Isabelle `Mark_gap_peel`, layerB:19922）

`b` が右端なら 2/3、内部なら `Pred Q` へ転送して強 `Lng` 帰納。`Pred Q` 上の
剥がし等式を `Mark_nest_common_marked` の共通 scb 位置で `Q` に持ち上げる。 -/

private theorem Mark_marked_principal_gp (N : PS) (k : ℕ)
    (hR : RTPS N) (hk : Marked N k) (hL : 1 < Lng N) :
    ∃ p, Mark N k = .trm [p] := by
  have hTransNe : Trans N ≠ BZero := by
    intro hzero
    have hz : zeroT N = true :=
      (Trans_preserves_zeroT N (RTPS_TPS N hR)).2 hzero
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    omega
  exact marked_component_principal hTransNe
    (Trans_Mark_mem_MarkedB N k hR hk)

private theorem Mark_gap_peel_aux_gp : ∀ (n : ℕ) (Q : PS) (a b : ℕ), Lng Q ≤ n →
    RTPS Q → Marked Q a → Marked Q b → a < b → b ≤ Lng Q - 1 →
    (∀ k, a < k → k < b → adm Q k = false) →
    Mark Q a = Dprin (entry Q 1 a : ℕ∞) (Mark Q b)
  | 0, Q, a, b, hn, hR, _, _, _, _, _ => by
      have hQT : TPS Q := RTPS_TPS Q hR
      have := List.length_pos_of_ne_nil hQT
      omega
  | n + 1, Q, a, b, hn, hR, hma, hmb, hab, hbub, hgap => by
      have hQT : TPS Q := RTPS_TPS Q hR
      have hL : 1 < Lng Q := by omega
      by_cases hbrm : b = Lng Q - 1
      · rw [hbrm] at hmb hab hgap ⊢
        exact Mark_gap_rightmost_peel_gp Q a hR hma hmb hab hgap
      · have hbint : b < Lng Q - 1 := by omega
        have hPredEq : Pred Q = Q.take (Lng Q - 1) := Pred_eq_take Q hL
        have hPredL : Lng (Pred Q) = Lng Q - 1 := by
          rw [hPredEq]
          simp
        have hPredT : TPS (Pred Q) := by
          apply List.ne_nil_of_length_pos
          change 0 < Lng (Pred Q)
          omega
        have hRP : RTPS (Pred Q) := RTPS_Pred Q hR
        have hmaP : Marked (Pred Q) a := Marked_Pred Q a hQT hL hma (by omega)
        have hmbP : Marked (Pred Q) b := Marked_Pred Q b hQT hL hmb (by omega)
        have he1a : entry (Pred Q) 1 a = entry Q 1 a := by
          rw [hPredEq]
          exact entry_take Q (Lng Q - 1) 1 a (by omega)
        -- ギャップ非許容性は `Pred Q` に降りる
        have hgapP : ∀ k, a < k → k < b → adm (Pred Q) k = false := by
          intro k hka hkb
          have hadmN : adm Q k = false := hgap k hka hkb
          have hnadmN : nadm Q k = true := by
            simpa [adm] using hadmN
          have e1 : nextR (Pred Q) 1 (k - 1) k = nextR Q 1 (k - 1) k := by
            rw [hPredEq]
            exact nextR_take_adm Q (Lng Q - 1) 1 (k - 1) k (by omega) (by omega)
              (by omega)
          have e2 : nextR (Pred Q) 1 k (k + 1) = nextR Q 1 k (k + 1) := by
            rw [hPredEq]
            exact nextR_take_adm Q (Lng Q - 1) 1 k (k + 1) (by omega) (by omega)
              (by omega)
          have hpairN : nextR Q 1 (k - 1) k = true ∧ nextR Q 1 k (k + 1) = true := by
            simp only [nadm, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq] at hnadmN
            rcases hnadmN with h | h
            · exfalso
              omega
            · exact h
          have hnadmP : nadm (Pred Q) k = true := by
            simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            right
            rw [e1, e2]
            exact hpairN
          simp [adm, hnadmP]
        -- `Pred Q` 上の剥がし: 内部なら帰納、境界なら右端剥がし
        have hrelP : Mark (Pred Q) a
            = Dprin (entry Q 1 a : ℕ∞) (Mark (Pred Q) b) := by
          by_cases hbP : b < Lng (Pred Q) - 1
          · have hres := Mark_gap_peel_aux_gp n (Pred Q) a b (by omega) hRP
              hmaP hmbP hab (by omega) hgapP
            rwa [he1a] at hres
          · have hbLP : b < Lng (Pred Q) := by omega
            have hbPrm : b = Lng (Pred Q) - 1 := by omega
            have hmbP' : Marked (Pred Q) (Lng (Pred Q) - 1) := by
              rwa [hbPrm] at hmbP
            have hres := Mark_gap_rightmost_peel_gp (Pred Q) a hRP hmaP hmbP'
              (by omega) (fun k hk1 hk2 => hgapP k hk1 (by omega))
            rw [he1a] at hres
            rwa [← hbPrm] at hres
        -- `Mark (Pred Q) b` は principal
        have hprinP := Mark_marked_principal_gp (Pred Q) b hRP hmbP (by omega)
        obtain ⟨p, hp⟩ := hprinP
        have hPTB : isPTB_str (flatBT (Mark (Pred Q) b)) := by
          rw [hp]
          have hTB : Mark (Pred Q) b ∈ T_B := Mark_mem_T_B (Pred Q) b hRP hmbP
          rw [hp] at hTB
          exact (principal_flat_properties hTB ⟨p, rfl⟩).1
        have hself : scb_decomp (Mark (Pred Q) b) [] (flatBT (Mark (Pred Q) b)) [] :=
          ⟨by simp, fun _ => hPTB, by simp⟩
        -- dP: `Pred Q` 側の scb 位置は `[D_{Q1,a}]`
        have hdP : scb_decomp (Mark (Pred Q) a) [.dsym (entry Q 1 a : ℕ∞)]
            (flatBT (Mark (Pred Q) b)) [] := by
          have hlift := scb_compose_dprin (entry Q 1 a : ℕ∞) (Mark (Pred Q) b) []
            (flatBT (Mark (Pred Q) b)) [] hself hPTB
          rwa [← hrelP] at hlift
        -- 共通 scb 位置で `Q` に転送
        obtain ⟨sb, ⟨hsbP, hsbQ⟩, _⟩ :=
          Mark_nest_common_marked Q a b hR hma hmb hab.le hbint
        have hsbeq := scb_unique_decomp_unconditional (Mark (Pred Q) a) sb.1
          [.dsym (entry Q 1 a : ℕ∞)] (flatBT (Mark (Pred Q) b)) sb.2 [] hsbP hdP
        have hdQ : scb_decomp (Mark Q a) [.dsym (entry Q 1 a : ℕ∞)]
            (flatBT (Mark Q b)) [] := by
          rw [← hsbeq.1, ← hsbeq.2]
          exact hsbQ
        have hflat : flatBT (Mark Q a)
            = flatBT (Dprin (entry Q 1 a : ℕ∞) (Mark Q b)) := by
          have h1 := hdQ.1
          have h2 : flatBT (Dprin (entry Q 1 a : ℕ∞) (Mark Q b))
              = .dsym (entry Q 1 a : ℕ∞) :: flatBT (Mark Q b) := rfl
          rw [h2, h1]
          simp
        exact flatBT_injective hflat

/-- 一般ギャップ剥がし（Isabelle `Mark_gap_peel`）: `a < b` が両方基点で
間が全部非許容なら `Mark Q a = D_{Q₁,a}(Mark Q b)`。 -/
private theorem Mark_gap_peel_gp (Q : PS) (a b : ℕ)
    (hR : RTPS Q) (hma : Marked Q a) (hmb : Marked Q b)
    (hab : a < b) (hbub : b ≤ Lng Q - 1)
    (hgap : ∀ k, a < k → k < b → adm Q k = false) :
    Mark Q a = Dprin (entry Q 1 a : ℕ∞) (Mark Q b) :=
  Mark_gap_peel_aux_gp (Lng Q) Q a b (le_refl _) hR hma hmb hab hbub hgap

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
  · -- (3-1): `Pred M` 上で `Mark_gap_peel_gp`（間隙 `j′₋₁ < k < j₀ = j′₀+1` は
    -- `j′₋₁ = Adm M j′₀` の最大性から全て非許容）
    intro _hguard
    have hM : TPS M := RTPS_TPS M hR
    have htJ1 : transJ1 M = Lng M - 1 := rfl
    have hlen : 1 < Lng M := by omega
    have hjm1 : transJm1 M = transJ0 M := by
      simp [transJm1, Adm, hadm]
    have hc1 : transC1 M = Mark (Pred M) (transJ0 M) := by
      simp [transC1, hjm1]
    have hp : hasParent M 0 (Lng M - 1) = true :=
      mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
    have hj0lt : transJ0 M < Lng M - 1 := by
      show parent M 0 (Lng M - 1) < Lng M - 1
      exact parent_lt_of_hasParent M 0 (Lng M - 1) hp
    have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
      show nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true
      exact hasParent_next_fseq M 0 (Lng M - 1) hp
    have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
      nextR0_leR M _ _ hnpar
    have haLe : Adm M j₀' ≤ j₀' := Adm_le M j₀'
    have hpredA : Marked (Pred M) (Adm M j₀') :=
      (c1_around_2 M j₀' hR hmono hadm hj1 hge np).2.1
    have hmarkedJ0 : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
    have hpredJ0 : Marked (Pred M) (transJ0 M) :=
      Marked_Pred M _ hM hlen hmarkedJ0 (by omega)
    have hPredEq : Pred M = M.take (Lng M - 1) := Pred_eq_take M hlen
    have hPredL : Lng (Pred M) = Lng M - 1 := by
      rw [hPredEq]
      simp
    have hRP : RTPS (Pred M) := RTPS_Pred M hR
    have hgap : ∀ k, Adm M j₀' < k → k < transJ0 M →
        adm (Pred M) k = false := by
      intro k hka hkb
      have hklej : k ≤ j₀' := by omega
      have hadmMk : adm M k = false := by
        cases hbool : adm M k with
        | false => rfl
        | true =>
            exfalso
            have := Adm_max M k j₀' hbool hklej
            omega
      have hnadmN : nadm M k = true := by
        simpa [adm] using hadmMk
      have e1 : nextR (Pred M) 1 (k - 1) k = nextR M 1 (k - 1) k := by
        rw [hPredEq]
        exact nextR_take_adm M (Lng M - 1) 1 (k - 1) k (by omega) (by omega)
          (by omega)
      have e2 : nextR (Pred M) 1 k (k + 1) = nextR M 1 k (k + 1) := by
        rw [hPredEq]
        exact nextR_take_adm M (Lng M - 1) 1 k (k + 1) (by omega) (by omega)
          (by omega)
      have hpairN : nextR M 1 (k - 1) k = true ∧ nextR M 1 k (k + 1) = true := by
        simp only [nadm, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at hnadmN
        rcases hnadmN with h | h
        · exfalso
          omega
        · exact h
      have hnadmP : nadm (Pred M) k = true := by
        simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        right
        rw [e1, e2]
        exact hpairN
      simp [adm, hnadmP]
    have hpeel := Mark_gap_peel_gp (Pred M) (Adm M j₀') (transJ0 M) hRP hpredA
      hpredJ0 (by omega) (by omega) hgap
    have he1 : entry (Pred M) 1 (Adm M j₀') = entry M 1 (Adm M j₀') := by
      rw [hPredEq]
      exact entry_take M (Lng M - 1) 1 (Adm M j₀') (by omega)
    rw [hc1, ← he1]
    exact hpeel
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

/-! ## part (5) エンジン層（§8.3 kind0 基盤の 8.1 側接着）

`entry` の接頭辞一致（`z ≤ j₀`）、`nextrel1`/`adm`/`Adm` の接頭辞転送
（値特徴付け経由、8.3-base-basepoint と同型）、prefix→最終ブロック開始の
行 0 辺（Isabelle `oper_d0zero_prefix_to_lastblock`）。 -/

private theorem entry_ne_zero_p5 (X : PS) (i z : ℕ) (hi : i ≠ 0) :
    entry X i z = entry X 1 z := by
  unfold entry
  cases X[z]? <;> simp [hi]

/-- `oper` の接頭辞一致（`z ≤ j₀` を含む）: 全行。 -/
private theorem entry_oper_prefix_le_p5 (M : PS) (n i z : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hz : z ≤ parent M 0 (Lng M - 1)) :
    entry (oper M n) i z = entry M i z := by
  rcases Nat.lt_or_eq_of_le hz with h | h
  · exact entry_oper_tiling_prefix M n i z hlast hzero hp (by rw [hi₁]; exact h)
  · subst h
    by_cases hi : i = 0
    · subst hi
      have hh := entry_oper_tiling_block_zero M n 0 0 hlast hzero hp hn
        (by rw [hi₁]; omega)
      rw [hi₁] at hh
      simpa using hh
    · rw [entry_ne_zero_p5 (oper M n) i _ hi, entry_ne_zero_p5 M i _ hi]
      have hh := entry_oper_tiling_block_one M n 0 0 hlast hzero hp hn
        (by rw [hi₁]; omega)
      rw [hi₁] at hh
      simpa using hh

/-- 接頭辞領域の `le0` 転送（値特徴付け経由、両方向を担う一般形）。 -/
private theorem le0_agree_lift_p5 (A B : PS) (c x y : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcB : c < Lng B) (hy : y ≤ c)
    (h : leR A 0 x y = true) : leR B 0 x y = true := by
  have hxy : x ≤ y := by
    have hh : le0 A x y = true := by simpa [leR] using h
    simp only [le0, Bool.and_eq_true] at hh
    exact le0Aux_index_fseq hh.2
  rcases Nat.eq_or_lt_of_le hxy with heq | hlt
  · subst heq
    simp [leR, le0, show x < Lng B by omega, le0Aux_refl_gp]
  · apply parent_exists_3 B x y hBT hlt (by omega)
    intro k hxk hky
    have hbase : entry A 0 x < entry A 0 k :=
      ancestor_basic_1 A x k y hAT hxk hky h
    rw [agree 0 x (by omega), agree 0 k (by omega)] at hbase
    exact hbase

/-- 接頭辞領域の `nextrel1` 転送（`y ≤ c`、`A → B`）。 -/
private theorem nextrel1_prefix_imp_p5 (A B : PS) (c x y : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcA : c < Lng A) (hcB : c < Lng B) (hy : y ≤ c)
    (h : nextrel1 A x y = true) : nextrel1 B x y = true := by
  have agree' : ∀ i z, z ≤ c → entry B i z = entry A i z := by
    intro i z hz
    exact (agree i z hz).symm
  have hh := h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hxy : x < y := hh.1.1.1.2
  have he1A : entry A 1 x < entry A 1 y := hh.1.1.2
  have hle0A : le0 A x y = true := hh.1.2
  have hvalleyA := hh.2
  have hle0B : leR B 0 x y = true :=
    le0_agree_lift_p5 A B c x y hAT hBT agree hcB hy
      (by simpa [leR] using hle0A)
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by omega, by omega⟩, hxy⟩, ?_⟩, by simpa [leR] using hle0B⟩, ?_⟩
  · rw [← agree 1 x (by omega), ← agree 1 y hy]
    exact he1A
  · rw [List.all_eq_true]
    intro j hjmem
    by_cases hcase : x < j ∧ le0 B j y = true
    · have hjy : j ≤ y := by
        have hh' := hcase.2
        simp only [le0, Bool.and_eq_true] at hh'
        exact le0Aux_index_fseq hh'.2
      have hle0Aj : le0 A j y = true := by
        have := le0_agree_lift_p5 B A c j y hBT hAT agree' hcA hy
          (by simpa [leR] using hcase.2)
        simpa [leR] using this
      have hjA : j < Lng A := by omega
      have hv := List.all_eq_true.mp hvalleyA j (List.mem_range.mpr hjA)
      simp only [hle0Aj, hcase.1, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at hv
      have hgoal : entry B 1 y ≤ entry B 1 j := by
        rw [← agree 1 y hy, ← agree 1 j (by omega)]
        exact hv
      simp [hgoal]
    · rcases not_and_or.mp hcase with h' | h'
      · simp [h']
      · have h'' : le0 B j y = false := by
          revert h'
          simp
        simp [h'']

/-- 接頭辞領域の `adm` 一致（`j + 1 ≤ c`）。 -/
private theorem adm_prefix_agree_eq_p5 (A B : PS) (c j : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcA : c < Lng A) (hcB : c < Lng B) (hjc : j + 1 ≤ c) :
    adm A j = adm B j := by
  have agree' : ∀ i z, z ≤ c → entry B i z = entry A i z := by
    intro i z hz
    exact (agree i z hz).symm
  have hpair : (nextR A 1 (j - 1) j = true ∧ nextR A 1 j (j + 1) = true)
      ↔ (nextR B 1 (j - 1) j = true ∧ nextR B 1 j (j + 1) = true) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by
        simp only [nextR] at h1 ⊢
        exact nextrel1_prefix_imp_p5 A B c (j - 1) j hAT hBT agree hcA hcB
          (by omega) (by simpa using h1), by
        simp only [nextR] at h2 ⊢
        exact nextrel1_prefix_imp_p5 A B c j (j + 1) hAT hBT agree hcA hcB
          (by omega) (by simpa using h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by
        simp only [nextR] at h1 ⊢
        exact nextrel1_prefix_imp_p5 B A c (j - 1) j hBT hAT agree' hcB hcA
          (by omega) (by simpa using h1), by
        simp only [nextR] at h2 ⊢
        exact nextrel1_prefix_imp_p5 B A c j (j + 1) hBT hAT agree' hcB hcA
          (by omega) (by simpa using h2)⟩
  have hnadm : nadm A j = nadm B j := by
    have hgA : decide (Lng A < j) = false := by
      simp
      omega
    have hgB : decide (Lng B < j) = false := by
      simp
      omega
    simp only [nadm, hgA, hgB, Bool.false_or]
    cases hA : (nextR A 1 (j - 1) j && nextR A 1 j (j + 1)) with
    | false =>
        cases hB : (nextR B 1 (j - 1) j && nextR B 1 j (j + 1)) with
        | false => rfl
        | true =>
            exfalso
            have hBpair : nextR B 1 (j - 1) j = true
                ∧ nextR B 1 j (j + 1) = true := by
              simpa [Bool.and_eq_true] using hB
            have hApair := hpair.mpr hBpair
            have hAt : (nextR A 1 (j - 1) j && nextR A 1 j (j + 1)) = true := by
              simp [hApair.1, hApair.2]
            rw [hAt] at hA
            cases hA
    | true =>
        have hApair : nextR A 1 (j - 1) j = true
            ∧ nextR A 1 j (j + 1) = true := by
          simpa [Bool.and_eq_true] using hA
        have hBpair := hpair.mp hApair
        have hBt : (nextR B 1 (j - 1) j && nextR B 1 j (j + 1)) = true := by
          simp [hBpair.1, hBpair.2]
        rw [hBt]
  simp [adm, hnadm]

/-- `adm` が `≤ j` で一致すれば許容化も一致。 -/
private theorem find_adm_congr_p5 (A B : PS) :
    ∀ (l : List ℕ), (∀ k ∈ l, adm A k = adm B k) →
      l.find? (fun j' => adm A j') = l.find? (fun j' => adm B j')
  | [], _ => rfl
  | x :: xs, h => by
      have hx : adm A x = adm B x := h x (by simp)
      have ih := find_adm_congr_p5 A B xs
        (fun k hk => h k (List.mem_cons_of_mem _ hk))
      cases hpx : adm B x with
      | true =>
          rw [List.find?_cons_of_pos (by rw [hx]; exact hpx),
            List.find?_cons_of_pos hpx]
      | false =>
          rw [List.find?_cons_of_neg (by rw [hx, hpx]; simp),
            List.find?_cons_of_neg (by rw [hpx]; simp), ih]

private theorem Adm_eq_of_adm_below_p5 (A B : PS) (j : ℕ)
    (h : ∀ k, k ≤ j → adm A k = adm B k) : Adm A j = Adm B j := by
  unfold Adm
  rw [h j (le_refl j)]
  cases hj : adm B j with
  | true => simp
  | false =>
      simp only [Bool.false_eq_true, if_false]
      congr 1
      apply find_adm_congr_p5
      intro k hk
      have : k < j := by
        have := List.mem_range.mp (List.mem_reverse.mp hk)
        exact this
      exact h k (by omega)

/-- prefix → 最終ブロック開始の行 0 辺
（Isabelle `oper_d0zero_prefix_to_lastblock`）。 -/
private theorem oper_prefix_to_lastblock_p5 (M : PS) (n j₀' : ℕ)
    (hMT : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi₁ : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hstep : nextrel0 M j₀' (parent M 0 (Lng M - 1)) = true) :
    nextrel0 (oper M n) j₀'
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true := by
  have hdec := hstep
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdec
  have hj₀'lt : j₀' < parent M 0 (Lng M - 1) := hdec.1.1.2
  have he0lt : entry M 0 j₀' < entry M 0 (parent M 0 (Lng M - 1)) := hdec.1.2
  have hvalM := hdec.2
  have hw : 0 < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hlen : Lng (oper M n) = parent M 0 (Lng M - 1)
      + n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    simpa [hi₁] using length_oper_tiling M n hlast hzero hp
  have hrel : n * ((Lng M - 1) - parent M 0 (Lng M - 1))
      = (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
        + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.succ_mul]
  have hidxlt : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    omega
  -- 読み出し
  have hej₀' : entry (oper M n) 0 j₀' = entry M 0 j₀' :=
    entry_oper_tiling_prefix M n 0 j₀' hlast hzero hp (by rw [hi₁]; omega)
  have heidxl : entry (oper M n) 0
      (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      = entry M 0 (parent M 0 (Lng M - 1)) := by
    have hh := entry_oper_tiling_block_zero M n (n - 1) 0 hlast hzero hp
      (by omega) (by rw [hi₁]; omega)
    rw [hi₁] at hh
    simpa using hh
  have hfloor : ∀ x, parent M 0 (Lng M - 1) ≤ x → x < Lng (oper M n) →
      entry M 0 (parent M 0 (Lng M - 1)) ≤ entry (oper M n) 0 x := by
    intro x hx hxL
    have hh := oper_tiling_block_floor M n x hMT hlast hzero hp
      (by rw [hi₁]; exact hx) hxL
    rw [hi₁] at hh
    exact hh
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by omega, hidxlt⟩, by
    have h1w : (Lng M - 1) - parent M 0 (Lng M - 1)
        ≤ (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) ∨ n = 1 := by
      cases n with
      | zero => omega
      | succ m =>
          cases m with
          | zero => omega
          | succ m' =>
              left
              calc (Lng M - 1) - parent M 0 (Lng M - 1)
                  = 1 * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
                _ ≤ (m' + 1 + 1 - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) :=
                    Nat.mul_le_mul_right _ (by omega)
    rcases h1w with h1w | h1w
    · omega
    · subst h1w
      omega⟩, ?_⟩, ?_⟩
  · rw [hej₀', heidxl]
    exact he0lt
  · rw [List.all_eq_true]
    intro j hjmem
    have hjlt : j < parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) :=
      List.mem_range.mp hjmem
    by_cases hgt : j₀' < j
    · have hval : entry (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
          ≤ entry (oper M n) 0 j := by
        rw [heidxl]
        by_cases hjj₀ : j < parent M 0 (Lng M - 1)
        · -- 接頭辞: `M` の谷を輸送
          have hej : entry (oper M n) 0 j = entry M 0 j :=
            entry_oper_tiling_prefix M n 0 j hlast hzero hp (by rw [hi₁]; omega)
          rw [hej]
          rcases hvalM j hjj₀ with h | h
          · exact absurd hgt h
          · exact h
        · -- ブロック域: 床
          have hge : parent M 0 (Lng M - 1) ≤ j := by omega
          have hjL : j < Lng (oper M n) := by omega
          exact hfloor j hge hjL
      simp [hval]
    · simp [hgt]

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
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  simp only [htJ0, htJ1]
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    have hh := hcondI
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hi₁ : idx1 M (Lng M - 1) = 0 := by
    simp [idx1, he1z]
  have hpar : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    rw [hi₁]
    exact hp0
  have hnext0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hasParent_next_fseq M 0 (Lng M - 1) hp0
  have hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh := hnext0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have he0j₀ : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := by
    have hh := hnext0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    omega
  have hw : 0 < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hstep : nextrel0 M j₀' (parent M 0 (Lng M - 1)) = true := by
    have := np
    rw [htJ0] at this
    simpa [nextR] using this
  have hj₀'lt : j₀' < parent M 0 (Lng M - 1) := by
    have hh := hstep
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hlenMn : Lng (oper M n) = parent M 0 (Lng M - 1)
      + n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    simpa [hi₁] using length_oper_tiling M n hlen hzero hpar
  have hwq : (Lng M - 1) - parent M 0 (Lng M - 1)
      ≤ (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    calc (Lng M - 1) - parent M 0 (Lng M - 1)
        = 1 * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
      _ ≤ (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) :=
          Nat.mul_le_mul_right _ (by omega)
  have hrel : n * ((Lng M - 1) - parent M 0 (Lng M - 1))
      = (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
        + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.succ_mul]
  have hidxlt : parent M 0 (Lng M - 1)
      + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    omega
  have hidxgt1 : 1 < parent M 0 (Lng M - 1)
      + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
  have hMnT : TPS (oper M n) := oper_TPS M n hM (by omega)
  -- (1) 基点
  have conj1 : Marked (oper M n)
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) :=
    ((kind0_base_basepoint M n hR (by omega) hp0 he1z).1 hn).1
  -- (2) 行 0 の辺
  have conj2 : nextrel0 (oper M n) j₀'
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true :=
    oper_prefix_to_lastblock_p5 M n j₀' hM hlen hzero hpar hi₁ (by omega)
      hj₀lt hstep
  -- (3) 切片の長さ
  have hLS : Lng (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
      = parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) + 1 := by
    simp [seg]
  -- (4) 切片内の親
  have hnextRMn : nextR (oper M n) 0 j₀'
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
    simpa [nextR] using conj2
  have hparS : parent (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = j₀' := by
    apply parent_eq_of_unique_fseq
    · have hseg := nextR_seg_adm (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) 0 j₀'
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        (Nat.zero_le _) hidxlt (by rw [hLS]; omega) (by rw [hLS]; omega)
      rw [hseg]
      simpa using hnextRMn
    · intro q hq
      have hqS : q < Lng (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) := by
        have hh : nextrel0 (seg (oper M n) 0
            (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) q
            (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
          simpa [nextR] using hq
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
        exact hh.1.1.1.1
      have hseg := nextR_seg_adm (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) 0 q
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        (Nat.zero_le _) hidxlt hqS (by rw [hLS]; omega)
      rw [hseg] at hq
      have hq' : nextR (oper M n) 0 q
          (parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
        simpa using hq
      exact row0_parent_unique (oper M n) q j₀' _ hq' hnextRMn
  have hlastS : lastIdx (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
      = parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    show Lng (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) - 1 = _
    omega
  have conj4 : transJ0 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) = j₀' := by
    show parent (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) 0
      (lastIdx (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) = j₀'
    rw [hlastS]
    exact hparS
  -- (5) 許容化の移送
  have hAdmS : Adm (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) j₀'
      = Adm (oper M n) j₀' := by
    have hh := admof_slice (oper M n) 0 j₀'
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
      hMnT (Nat.zero_le _) (by omega) (by omega)
    simpa using hh
  have hadmagree : ∀ k, k ≤ j₀' → adm (oper M n) k = adm M k := by
    intro k hk
    exact adm_prefix_agree_eq_p5 (oper M n) M (parent M 0 (Lng M - 1)) k hMnT hM
      (fun i z hz => entry_oper_prefix_le_p5 M n i z hlen hzero hpar hi₁
        (by omega) hj₀lt hz)
      (by omega) (by omega) (by omega)
  have hAdmMn : Adm (oper M n) j₀' = Adm M j₀' :=
    Adm_eq_of_adm_below_p5 (oper M n) M j₀' hadmagree
  have conj5 : transJm1 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) = Adm M j₀' := by
    show Adm (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
      (transJ0 (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) = Adm M j₀'
    rw [conj4, hAdmS, hAdmMn]
  -- (6) `Trans (Pred N) ≠ 0`
  have hnotle : ¬ (Lng (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) ≤ 1) := by omega
  have hPredS_eq : Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
      = (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))).dropLast := by
    unfold Pred
    rw [if_neg hnotle]
  have hLPredS : Lng (Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))))
      = parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    rw [hPredS_eq]
    show ((seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))).dropLast).length = _
    rw [List.length_dropLast]
    have h2 : (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))).length
        = parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) + 1 := hLS
    omega
  have hPredST : TPS (Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) := by
    apply List.ne_nil_of_length_pos
    have h3 : (Pred (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))).length
        = parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLPredS
    omega
  have conj6 : Trans (Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) ≠ BZero := by
    intro h0
    have hz := (Trans_preserves_zeroT _ hPredST).mpr h0
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    omega
  -- (7) 条件 (VI) 不成立（間隔が 2 以上）
  have conj7 : transCondVI (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    have h3 := h.2
    have h4 : lastParent (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) = j₀' := by
      show parent (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) 0
        (lastIdx (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) = j₀'
      rw [hlastS]
      exact hparS
    rw [h4, hlastS] at h3
    omega
  exact ⟨conj1, hnextRMn, by omega, conj4, conj5, conj6, conj7⟩

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
