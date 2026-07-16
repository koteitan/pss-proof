import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-Adm-nextAdm»
import «7».«7.3-Trans-IncrFirst-Red»
import «6».«6.6-reduced-slice»
import «6».«6.3-marked-slice»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.6-P-condAB»
import «5».«5.1-ancestor-tree»

/-!
# §8.1 part (4) 中間層（back-slice の簡約・Adm-zero・条件判定）

- 原文: `tmp/content.md` L3021–3036（part (4) の前剥がし基盤の中間節）
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `m_8_1_c1_around_part4_Nred`   (30389) → `c1_around_part4_Nred`
  - `m_8_1_c1_around_part4_Adm0`   (30590) → `c1_around_part4_Adm0`
  - `m_8_1_c1_around_part4_cond42` (30932) → `c1_around_part4_cond42`
  - `m_8_1_c1_around_part4_cond41` (31225) → `c1_around_part4_cond41`
- 依存: «7».«7.4-Mark-Trans-repr»（`transJ0_Red_terminal_slice` /
  `entry1_Red_terminal_slice` / `transJm1_Red_terminal_slice` /
  `adm_lastParent_Red_terminal_slice` = Isabelle の `repr_*` シフト束）,
  «7».«7.4-Adm-nextAdm»（`adm_row1_ancestry`, `row1_implies_row0`）,
  «6».«6.6-reduced-slice»（`RTPS_initial_slice` = Isabelle `seg_0_RT_PS`）,
  «6».«6.3-marked-slice» / «6».«6.3-admof-slice»（`marked_slice`, `admof_slice`）,
  «6».«6.6-ancestor-slice-Red-IncrFirst» ほか（推移 import）。
- 私的補助（接尾辞 `_pm`）: `seg_of_seg0_pm`（Isabelle `seg_of_seg` の接頭辞特化）,
  `parent0_seg_pm`（Isabelle `repr_parent_M_to_seg` の行 0 特化 =
  7.4-Mark-Trans-repr の private `parent0_terminal_seg` の再証明）,
  `part4_facts_pm` / `part4_prefix_pm` / `part4_atoms_pm`（共通文脈束）。
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## 私的補助: 接頭辞切片の切片（Isabelle `seg_of_seg` の `a = 0` 特化） -/

private theorem seg_of_seg0_pm (M : PS) (b c d : ℕ) (hdb : d ≤ b) :
    seg (seg M 0 b) c d = seg M c d := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < d + 1 - c := by simpa using h2
    have hci : c + i < Lng (seg M 0 b) := by
      rw [length_seg]
      omega
    simp only [show seg (seg M 0 b) c d =
        (List.range' c (d + 1 - c)).map
          (fun j => (entry (seg M 0 b) 0 j, entry (seg M 0 b) 1 j)) from rfl,
      show seg M c d =
        (List.range' c (d + 1 - c)).map
          (fun j => (entry M 0 j, entry M 1 j)) from rfl,
      List.getElem_map, List.getElem_range', one_mul]
    rw [entry_seg M 0 b 0 (c + i) hci, entry_seg M 0 b 1 (c + i) hci]
    simp

/-! ## 私的補助: 行 0 の親の切片転送（Isabelle `repr_parent_M_to_seg` の行 0 形。
`7.4-Mark-Trans-repr` の private `parent0_terminal_seg` の再証明） -/

private theorem parent0_seg_pm (M : PS) (m j₁ : ℕ)
    (hj₁ : j₁ < Lng M) (hmp : m ≤ parent M 0 j₁)
    (hp : hasParent M 0 j₁ = true) :
    hasParent (seg M m j₁) 0 (j₁ - m) = true ∧
      parent (seg M m j₁) 0 (j₁ - m) = parent M 0 j₁ - m := by
  let p := parent M 0 j₁
  let pl := p - m
  let jl := j₁ - m
  have hnextM : nextR M 0 p j₁ = true := by
    simpa [p] using hasParent_next_fseq M 0 j₁ hp
  have hpLt : p < j₁ := by
    simpa [p] using parent_lt_of_hasParent M 0 j₁ hp
  have hmpl : m + pl = p := by simp [pl, p, hmp]
  have hmjl : m + jl = j₁ := by simp [jl]; omega
  have hpljl : pl < jl := by omega
  have hjlS : jl < Lng (seg M m j₁) := by simp [jl]; omega
  have hplS : pl < Lng (seg M m j₁) := hpljl.trans hjlS
  have hnextS : nextR (seg M m j₁) 0 pl jl = true := by
    rw [nextR_seg_adm M m j₁ 0 pl jl (by omega) hj₁ hplS hjlS]
    simpa [hmpl, hmjl] using hnextM
  have huniq : ∀ q, nextR (seg M m j₁) 0 q jl = true → q = pl := by
    intro q hq
    exact row0_parent_unique (seg M m j₁) q pl jl hq hnextS
  have hpS : hasParent (seg M m j₁) 0 jl = true :=
    (hasParent_iff_unique_fseq (seg M m j₁) 0 jl).mpr
      ⟨pl, hnextS, huniq⟩
  have hparS : parent (seg M m j₁) 0 jl = pl :=
    parent_eq_of_unique_fseq (seg M m j₁) 0 jl pl hnextS huniq
  simpa [jl, pl, p] using And.intro hpS hparS

/-! ## 私的補助: part (4) 共通文脈（`j₀ = transJ0 M` の親子・許容化の基本事実） -/

private theorem part4_facts_pm (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true) :
    Adm M j₀' ≤ j₀' ∧ j₀' < transJ0 M ∧ transJ0 M < Lng M - 1 ∧
      leR M 0 (Adm M j₀') (transJ0 M) = true ∧ Marked M (Adm M j₀') := by
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hj1' : 1 < Lng M - 1 := by omega
  have hlen : 1 < Lng M := by omega
  -- `j₀ = transJ0 M` は最終列の行 0 の親
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
  -- `j₀'` は `j₀` の行 0 の親
  have hn0 : nextrel0 M j₀' (transJ0 M) = true := by
    simpa [nextR] using np
  have hj0'lt : j₀' < transJ0 M := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hle0' : leR M 0 j₀' (transJ0 M) = true := nextR0_leR M _ _ np
  -- 許容化 `j′₋₁ = Adm M j₀'` と行 1→行 0 祖先性
  have haLe : Adm M j₀' ≤ j₀' := Adm_le M j₀'
  have haAdm : adm M (Adm M j₀') = true := Adm_adm M j₀'
  have hle1a : leR M 1 (Adm M j₀') j₀' = true :=
    adm_row1_ancestry M j₀' hM (by omega)
  have hle0a : leR M 0 (Adm M j₀') j₀' = true :=
    row1_implies_row0 M _ _ hM hle1a
  have hleAJ0 : leR M 0 (Adm M j₀') (transJ0 M) = true :=
    row0_transitive M _ _ _ hM hle0a hle0'
  have hchain : leR M 0 (Adm M j₀') (Lng M - 1) = true :=
    row0_transitive M _ _ _ hM hleAJ0 hleJ0
  exact ⟨haLe, hj0'lt, hj0lt, hleAJ0, hM, haAdm, hchain⟩

/-! ## part (4) N-reduction（Isabelle `m_8_1_c1_around_part4_Nred`, 30389）

back-slice `N = (M_j)_{j=j′₋₁}^{j₀}` の簡約 `Red N` の基本性質:
`Trans` 不変・簡約形・単項性・長さ。 -/

theorem c1_around_part4_Nred (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (_hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true) :
    leR M 0 (Adm M j₀') (transJ0 M) = true ∧
    Adm M j₀' < transJ0 M ∧
    Trans (seg M (Adm M j₀') (transJ0 M)) =
      Trans (Red (seg M (Adm M j₀') (transJ0 M))) ∧
    RTPS (Red (seg M (Adm M j₀') (transJ0 M))) ∧
    monoT (Red (seg M (Adm M j₀') (transJ0 M))) = true ∧
    Lng (Red (seg M (Adm M j₀') (transJ0 M))) = transJ0 M + 1 - Adm M j₀' := by
  obtain ⟨haLe, hj0'lt, hj0lt, hleAJ0, hmarkedA⟩ :=
    part4_facts_pm M j₀' hR hmono hj1 np
  have hM : TPS M := RTPS_TPS M hR
  have hlt : Adm M j₀' < transJ0 M := by omega
  have hSlen : Lng (seg M (Adm M j₀') (transJ0 M)) =
      transJ0 M + 1 - Adm M j₀' := by simp
  have hSpos : 0 < Lng (seg M (Adm M j₀') (transJ0 M)) := by omega
  have hST : TPS (seg M (Adm M j₀') (transJ0 M)) :=
    List.ne_nil_of_length_pos hSpos
  have hTrans : Trans (seg M (Adm M j₀') (transJ0 M)) =
      Trans (Red (seg M (Adm M j₀') (transJ0 M))) :=
    Trans_Red (seg M (Adm M j₀') (transJ0 M)) hST
  have hmonoS : monoT (seg M (Adm M j₀') (transJ0 M)) = true :=
    mono_ancestor_slice M (Adm M j₀') (transJ0 M) hM hlt hleAJ0
  have hSnm : multiT (seg M (Adm M j₀') (transJ0 M)) = false := by
    simp [multiT, hmonoS]
  have hNR : RTPS (Red (seg M (Adm M j₀') (transJ0 M))) :=
    Red_nonmulti_RTPS _ hST hSnm
  have hmonoN : monoT (Red (seg M (Adm M j₀') (transJ0 M))) = true :=
    Red_preserves_monoT_forward _ hST hmonoS
  have hLng : Lng (Red (seg M (Adm M j₀') (transJ0 M))) =
      Lng (seg M (Adm M j₀') (transJ0 M)) := Lng_Red_invariance _ hST
  exact ⟨hleAJ0, hlt, hTrans, hNR, hmonoN, by omega⟩

/-! ## 私的補助: 接頭辞切片 `M′ = (M_j)_{j=0}^{j₀}` の文脈束
（Isabelle の `seg_0_RT_PS` / `m_6_3_marked_slice` / `repr_parent_M_to_seg` /
`m_6_3_Adm_prefix_slice` / `seg_of_seg` の組み合わせ） -/

private theorem part4_prefix_pm (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    RTPS (seg M 0 (transJ0 M)) ∧
    Marked (seg M 0 (transJ0 M)) (Adm M j₀') ∧
    Adm M j₀' < Lng (seg M 0 (transJ0 M)) - 2 ∧
    hasParent (seg M 0 (transJ0 M)) 0 (Lng (seg M 0 (transJ0 M)) - 1) = true ∧
    parent (seg M 0 (transJ0 M)) 0 (Lng (seg M 0 (transJ0 M)) - 1) = j₀' ∧
    Adm (seg M 0 (transJ0 M)) j₀' = Adm M j₀' ∧
    seg (seg M 0 (transJ0 M)) (Adm M j₀') (Lng (seg M 0 (transJ0 M)) - 1) =
      seg M (Adm M j₀') (transJ0 M) := by
  obtain ⟨haLe, hj0'lt, hj0lt, hleAJ0, hmarkedA⟩ :=
    part4_facts_pm M j₀' hR hmono hj1 np
  have hM : TPS M := RTPS_TPS M hR
  have hj0le : transJ0 M ≤ Lng M - 1 := le_of_lt hj0lt
  have hMpR : RTPS (seg M 0 (transJ0 M)) :=
    RTPS_initial_slice M (transJ0 M) hR hj0le
  have hLMp : Lng (seg M 0 (transJ0 M)) = transJ0 M + 1 := by simp
  have hidx : Lng (seg M 0 (transJ0 M)) - 1 = transJ0 M := by omega
  have hmarkedMp : Marked (seg M 0 (transJ0 M)) (Adm M j₀') := by
    have h := marked_slice M (Adm M j₀') 0 (transJ0 M) hmarkedA (Nat.zero_le _)
      (by omega) hj0le
    simpa using h
  have huniq : ∀ q, nextR M 0 q (transJ0 M) = true → q = j₀' := fun q hq =>
    row0_parent_unique M q j₀' (transJ0 M) hq np
  have hpj0 : hasParent M 0 (transJ0 M) = true :=
    (hasParent_iff_unique_fseq M 0 (transJ0 M)).mpr ⟨j₀', np, huniq⟩
  have hparj0 : parent M 0 (transJ0 M) = j₀' :=
    parent_eq_of_unique_fseq M 0 (transJ0 M) j₀' np huniq
  have hj0L : transJ0 M < Lng M := by omega
  have hs := parent0_seg_pm M 0 (transJ0 M) hj0L (Nat.zero_le _) hpj0
  have hpMp : hasParent (seg M 0 (transJ0 M)) 0 (transJ0 M) = true := by
    simpa using hs.1
  have hparMp : parent (seg M 0 (transJ0 M)) 0 (transJ0 M) = j₀' := by
    have h2 := hs.2
    simp only [Nat.sub_zero] at h2
    rw [hparj0] at h2
    exact h2
  have hAdmMp : Adm (seg M 0 (transJ0 M)) j₀' = Adm M j₀' := by
    have h := admof_slice M 0 j₀' (transJ0 M) hM (Nat.zero_le _) hj0'lt hj0le
    simpa using h
  have hsegseg : seg (seg M 0 (transJ0 M)) (Adm M j₀')
      (Lng (seg M 0 (transJ0 M)) - 1) = seg M (Adm M j₀') (transJ0 M) := by
    rw [hidx]
    exact seg_of_seg0_pm M (transJ0 M) (Adm M j₀') (transJ0 M) (le_refl _)
  refine ⟨hMpR, hmarkedMp, by omega, ?_, ?_, hAdmMp, hsegseg⟩
  · rw [hidx]
    exact hpMp
  · rw [hidx]
    exact hparMp

/-! ## part (4) Adm-zero（Isabelle `m_8_1_c1_around_part4_Adm0`, 30590）

gap ガード `j₀' + 1 < j₀` の下で、簡約 back-slice は Adm-zero 領域:
`transJm1 (Red N) = 0`。経路 = 接頭辞 `M′ = (M_j)_{j=0}^{j₀}` を介した
`transJm1` シフト（`transJm1_Red_terminal_slice`）＋ `Adm` 接頭辞不変性。 -/

theorem c1_around_part4_Adm0 (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (_hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    transJm1 (Red (seg M (Adm M j₀') (transJ0 M))) = 0 := by
  obtain ⟨haLe, _hj0'lt, _hj0lt, _hleAJ0, _hmarkedA⟩ :=
    part4_facts_pm M j₀' hR hmono hj1 np
  obtain ⟨hMpR, hmarkedMp, hlt2, hpLast, hparLast, hAdmMp, hsegseg⟩ :=
    part4_prefix_pm M j₀' hR hmono hj1 np hadj
  have hanc : leR (seg M 0 (transJ0 M)) 0 (Adm M j₀')
      (Lng (seg M 0 (transJ0 M)) - 1) = true := hmarkedMp.2.2
  have hmpLast : Adm M j₀' ≤ parent (seg M 0 (transJ0 M)) 0
      (Lng (seg M 0 (transJ0 M)) - 1) := by
    rw [hparLast]
    exact haLe
  have hshift := transJm1_Red_terminal_slice (seg M 0 (transJ0 M)) (Adm M j₀')
    hmarkedMp hMpR hlt2 hanc hpLast hmpLast
  have htJ0Mp : transJ0 (seg M 0 (transJ0 M)) = j₀' := by
    show parent (seg M 0 (transJ0 M)) 0 (lastIdx (seg M 0 (transJ0 M))) = j₀'
    exact hparLast
  have htJm1Mp : transJm1 (seg M 0 (transJ0 M)) = Adm M j₀' := by
    show Adm (seg M 0 (transJ0 M)) (transJ0 (seg M 0 (transJ0 M))) = Adm M j₀'
    rw [htJ0Mp, hAdmMp]
  rw [← hsegseg, hshift, htJm1Mp, Nat.sub_self]

/-! ## 私的補助: 条件判定の原子束（Isabelle `repr_transCond_atoms` の
`M′ = (M_j)_{j=0}^{j₀}` への適用 = Lean の `*_Red_terminal_slice` 群） -/

private theorem part4_atoms_pm (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    Lng (Red (seg M (Adm M j₀') (transJ0 M))) = transJ0 M + 1 - Adm M j₀' ∧
    lastIdx (Red (seg M (Adm M j₀') (transJ0 M))) = transJ0 M - Adm M j₀' ∧
    lastParent (Red (seg M (Adm M j₀') (transJ0 M))) = j₀' - Adm M j₀' ∧
    entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
      (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) =
      entry M 1 (transJ0 M) ∧
    entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) = entry M 1 j₀' ∧
    (adm (Red (seg M (Adm M j₀') (transJ0 M)))
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) = true ↔
      Adm M j₀' = j₀') := by
  obtain ⟨haLe, hj0'lt, hj0lt, hleAJ0, hmarkedA⟩ :=
    part4_facts_pm M j₀' hR hmono hj1 np
  obtain ⟨hMpR, hmarkedMp, hlt2, hpLast, hparLast, hAdmMp, hsegseg⟩ :=
    part4_prefix_pm M j₀' hR hmono hj1 np hadj
  have hanc : leR (seg M 0 (transJ0 M)) 0 (Adm M j₀')
      (Lng (seg M 0 (transJ0 M)) - 1) = true := hmarkedMp.2.2
  have hmpLast : Adm M j₀' ≤ parent (seg M 0 (transJ0 M)) 0
      (Lng (seg M 0 (transJ0 M)) - 1) := by
    rw [hparLast]
    exact haLe
  -- `Lng N` / `lastIdx N`
  have hSlen : Lng (seg M (Adm M j₀') (transJ0 M)) =
      transJ0 M + 1 - Adm M j₀' := by simp
  have hSpos : 0 < Lng (seg M (Adm M j₀') (transJ0 M)) := by omega
  have hST : TPS (seg M (Adm M j₀') (transJ0 M)) :=
    List.ne_nil_of_length_pos hSpos
  have hLngN : Lng (Red (seg M (Adm M j₀') (transJ0 M))) =
      transJ0 M + 1 - Adm M j₀' := by
    rw [Lng_Red_invariance _ hST]
    exact hSlen
  have hlastIdx : lastIdx (Red (seg M (Adm M j₀') (transJ0 M))) =
      transJ0 M - Adm M j₀' := by
    simp only [lastIdx]
    omega
  -- `transJ0` シフト → `lastParent N` の値
  have htJ0Mp : transJ0 (seg M 0 (transJ0 M)) = j₀' := by
    show parent (seg M 0 (transJ0 M)) 0 (lastIdx (seg M 0 (transJ0 M))) = j₀'
    exact hparLast
  have hshift0 := transJ0_Red_terminal_slice (seg M 0 (transJ0 M)) (Adm M j₀')
    hMpR hlt2 hanc hpLast hmpLast
  rw [hsegseg, htJ0Mp] at hshift0
  have hlastPar : lastParent (Red (seg M (Adm M j₀') (transJ0 M))) =
      j₀' - Adm M j₀' := hshift0
  -- 行 1 entry（最終列）
  have hent : entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
      (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) =
      entry M 1 (transJ0 M) := by
    rw [hlastIdx]
    have hi : transJ0 M - Adm M j₀' <
        Lng (Red (seg (seg M 0 (transJ0 M)) (Adm M j₀')
          (Lng (seg M 0 (transJ0 M)) - 1))) := by
      rw [hsegseg]
      omega
    have h := entry1_Red_terminal_slice (seg M 0 (transJ0 M)) (Adm M j₀')
      (transJ0 M - Adm M j₀') hMpR hlt2 hanc hi
    rw [hsegseg] at h
    rw [h]
    have hidx2 : Adm M j₀' + (transJ0 M - Adm M j₀') = transJ0 M := by omega
    rw [hidx2]
    have hjS : transJ0 M < Lng (seg M 0 (transJ0 M)) := by
      rw [length_seg]
      omega
    simpa using entry_seg M 0 (transJ0 M) 1 (transJ0 M) hjS
  -- 行 1 entry（行 0 の親）
  have hepar : entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) =
      entry M 1 j₀' := by
    rw [hlastPar]
    have hi : j₀' - Adm M j₀' <
        Lng (Red (seg (seg M 0 (transJ0 M)) (Adm M j₀')
          (Lng (seg M 0 (transJ0 M)) - 1))) := by
      rw [hsegseg]
      omega
    have h := entry1_Red_terminal_slice (seg M 0 (transJ0 M)) (Adm M j₀')
      (j₀' - Adm M j₀') hMpR hlt2 hanc hi
    rw [hsegseg] at h
    rw [h]
    have hidx2 : Adm M j₀' + (j₀' - Adm M j₀') = j₀' := by omega
    rw [hidx2]
    have hjS : j₀' < Lng (seg M 0 (transJ0 M)) := by
      rw [length_seg]
      omega
    simpa using entry_seg M 0 (transJ0 M) 1 j₀' hjS
  -- `adm`（行 0 の親）
  have hadmN : adm (Red (seg M (Adm M j₀') (transJ0 M)))
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) =
      adm (seg M 0 (transJ0 M)) j₀' := by
    have h := adm_lastParent_Red_terminal_slice (seg M 0 (transJ0 M))
      (Adm M j₀') hmarkedMp hMpR hlt2 hanc hpLast hmpLast
    rw [hsegseg] at h
    have hlpMp : lastParent (seg M 0 (transJ0 M)) = j₀' := htJ0Mp
    rw [hlpMp] at h
    exact h
  have hadmIff : adm (Red (seg M (Adm M j₀') (transJ0 M)))
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) = true ↔
      Adm M j₀' = j₀' := by
    rw [hadmN]
    constructor
    · intro h
      have hAv : Adm (seg M 0 (transJ0 M)) j₀' = j₀' := by
        simp [Adm, h]
      rw [← hAdmMp, hAv]
    · intro h
      have hAa := Adm_adm (seg M 0 (transJ0 M)) j₀'
      rwa [hAdmMp, h] at hAa
  exact ⟨hLngN, hlastIdx, hlastPar, hent, hepar, hadmIff⟩

/-! ## part (4-2) 条件判定（Isabelle `m_8_1_c1_around_part4_cond42`, 30932）

(4-2) ガード `j′₋₁ < j′₀ ∧ M_{1,j′₀} ≥ M_{1,j₀}` の下で、簡約 back-slice は
条件 (II) か (IV) を満たす（`j₀^N` が非 `N`-許容になるため）。 -/

theorem c1_around_part4_cond42 (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (_hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    Adm M j₀' < j₀' ∧ entry M 1 (transJ0 M) ≤ entry M 1 j₀' →
      transCondII (Red (seg M (Adm M j₀') (transJ0 M))) = true ∨
      transCondIV (Red (seg M (Adm M j₀') (transJ0 M))) = true := by
  obtain ⟨_hLngN, _hlastIdx, _hlastPar, hent, hepar, hadmIff⟩ :=
    part4_atoms_pm M j₀' hR hmono hj1 np hadj
  rintro ⟨hlt', hge'⟩
  have hadmN : adm (Red (seg M (Adm M j₀') (transJ0 M)))
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have := hadmIff.mp h
    omega
  by_cases hz : entry M 1 (transJ0 M) = 0
  · left
    simp [transCondII, hent, hz, hadmN]
  · right
    have hpos : 0 < entry M 1 (transJ0 M) := Nat.pos_of_ne_zero hz
    simp [transCondIV, hent, hepar, hadmN, hpos, hge']

/-! ## part (4-1) 条件判定（Isabelle `m_8_1_c1_around_part4_cond41`, 31225）

(4-1) ガード `j′₋₁ = j′₀ ∨ M_{1,j′₀}+1 = M_{1,j₀}` の下で、簡約 back-slice は
条件 (I)/(III)/(V) を満たす。(V) は `M_{1,j′₀}+1 = M_{1,j₀}` の枝で直接
（gap ガードが非隣接性を供給）、`j′₋₁ = j′₀` の枝では `R` の最終列の行 0 の
親が `0` になるので、簡約性（RedCondA 行 0 ＋ 左端 行 0=行 1 ＋ 係数条件）が
`M_{1,j₀} ≤ M_{1,j′₀}+1` を固定して (I)/(III) が出る。 -/

theorem c1_around_part4_cond41 (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (_hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M) :
    Adm M j₀' = j₀' ∨ entry M 1 j₀' + 1 = entry M 1 (transJ0 M) →
      transCondI (Red (seg M (Adm M j₀') (transJ0 M))) = true ∨
      transCondIII (Red (seg M (Adm M j₀') (transJ0 M))) = true ∨
      transCondV (Red (seg M (Adm M j₀') (transJ0 M))) = true := by
  obtain ⟨haLe, hj0'lt, hj0lt, hleAJ0, _hmarkedA⟩ :=
    part4_facts_pm M j₀' hR hmono hj1 np
  obtain ⟨hLngN, hlastIdx, hlastPar, hent, hepar, hadmIff⟩ :=
    part4_atoms_pm M j₀' hR hmono hj1 np hadj
  have hM : TPS M := RTPS_TPS M hR
  -- `N = Red (seg M j′₋₁ j₀)` の簡約性・単項性（Nred と同じ導出）
  have hlt : Adm M j₀' < transJ0 M := by omega
  have hSpos : 0 < Lng (seg M (Adm M j₀') (transJ0 M)) := by
    rw [length_seg]
    omega
  have hST : TPS (seg M (Adm M j₀') (transJ0 M)) :=
    List.ne_nil_of_length_pos hSpos
  have hmonoS : monoT (seg M (Adm M j₀') (transJ0 M)) = true :=
    mono_ancestor_slice M (Adm M j₀') (transJ0 M) hM hlt hleAJ0
  have hSnm : multiT (seg M (Adm M j₀') (transJ0 M)) = false := by
    simp [multiT, hmonoS]
  have hNR : RTPS (Red (seg M (Adm M j₀') (transJ0 M))) :=
    Red_nonmulti_RTPS _ hST hSnm
  have hNT : TPS (Red (seg M (Adm M j₀') (transJ0 M))) := RTPS_TPS _ hNR
  have hmonoN : monoT (Red (seg M (Adm M j₀') (transJ0 M))) = true :=
    Red_preserves_monoT_forward _ hST hmonoS
  -- 最終列の行 0 の親・簡約条件 (A)・左端 行 0=行 1・係数条件
  have hpN : hasParent (Red (seg M (Adm M j₀') (transJ0 M))) 0
      (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) = true :=
    mono_hasParent_row0 _ hNT hmonoN _
      (by rw [hlastIdx]; omega) (by rw [hlastIdx]; omega)
  have hA : RedCondA (Red (seg M (Adm M j₀') (transJ0 M))) = true :=
    (RTPS_condAB _ hNR).1
  have he0last : entry (Red (seg M (Adm M j₀') (transJ0 M))) 0
      (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) + 1 =
      entry (Red (seg M (Adm M j₀') (transJ0 M))) 0
        (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) :=
    RedCondA_apply (Red (seg M (Adm M j₀') (transJ0 M))) hA 0
      (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) (by omega)
      (by rw [hlastIdx]; omega) hpN
  have he00 : entry (Red (seg M (Adm M j₀') (transJ0 M))) 0 0 =
      entry (Red (seg M (Adm M j₀') (transJ0 M))) 1 0 :=
    RTPS_mono_head_eq _ hNR hmonoN
  have hcoeff : entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
      (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) ≤
      entry (Red (seg M (Adm M j₀') (transJ0 M))) 0
        (lastIdx (Red (seg M (Adm M j₀') (transJ0 M)))) :=
    reduced_coeff _ hNR _ (by rw [hlastIdx]; omega)
  intro g
  by_cases hVc : entry M 1 j₀' + 1 = entry M 1 (transJ0 M)
  · -- (V): `M_{1,j′₀}+1 = M_{1,j₀}` の枝（gap ガードで非隣接）
    right
    right
    have hpos : 0 < entry M 1 (transJ0 M) := by omega
    have h3 : lastParent (Red (seg M (Adm M j₀') (transJ0 M))) + 1 <
        lastIdx (Red (seg M (Adm M j₀') (transJ0 M))) := by
      rw [hlastPar, hlastIdx]
      omega
    simp [transCondV, hent, hepar, hpos, hVc, h3]
  · have hAeq : Adm M j₀' = j₀' := by
      rcases g with h | h
      · exact h
      · exact absurd h hVc
    have hadmNtrue : adm (Red (seg M (Adm M j₀') (transJ0 M)))
        (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) = true :=
      hadmIff.mpr hAeq
    by_cases hz : entry M 1 (transJ0 M) = 0
    · -- (I)
      left
      simp [transCondI, hent, hz, hadmNtrue]
    · -- (III): 親が列 0 に落ち、簡約性の連鎖で `M_{1,j₀} ≤ M_{1,j′₀}`
      right
      left
      have hpos : 0 < entry M 1 (transJ0 M) := Nat.pos_of_ne_zero hz
      have hlp0 : lastParent (Red (seg M (Adm M j₀') (transJ0 M))) = 0 := by
        rw [hlastPar, hAeq]
        omega
      have h4 : entry (Red (seg M (Adm M j₀') (transJ0 M))) 0
          (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) =
          entry (Red (seg M (Adm M j₀') (transJ0 M))) 0 0 := by
        rw [hlp0]
      have h6 : entry (Red (seg M (Adm M j₀') (transJ0 M))) 1
          (lastParent (Red (seg M (Adm M j₀') (transJ0 M)))) =
          entry (Red (seg M (Adm M j₀') (transJ0 M))) 1 0 := by
        rw [hlp0]
      have hge : entry M 1 (transJ0 M) ≤ entry M 1 j₀' := by omega
      simp [transCondIII, hent, hepar, hadmNtrue, hpos, hge]

#print axioms c1_around_part4_Nred
#print axioms c1_around_part4_Adm0
#print axioms c1_around_part4_cond42
#print axioms c1_around_part4_cond41

end PSS
