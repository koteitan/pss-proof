import «7».«7.4-RightNodes-Mark»
import «7».«7.4-Mark-Trans-repr»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»
import «6».«6.6-reduced-leftend»
import «6».«6.5-Red-Pred-commute»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.3-marked-slice»
import «6».«6.3-admof-slice»
import «6».«6.2-P-fseq»
import «6».«6.2-P-additivity»
import «5».«5.1-ancestor-tree»

/-!
# §8.1 補題 part (4) — setup ＋ depth-1 head（前剥がしキャンペーンの下層）

- 原文: `tmp/content.md` L2923 付近（「補題（条件(I)か(III)の下での\(c_1\)前後の
  具体表示）」part (4-1)(4-2)）。本ファイルはその共有 setup と depth-1 head。
- Isabelle: `m_8_1_c1_around_part4_setup`（isabelle/layerB/pss_wip.thy:29756）/
  `m_8_1_c1_around_part4_head`（同 29815）。Isabelle の `defines`
  （`j₁ = Lng M - 1`, `j₀ = parent M 0 j₁`, `j₋₁ = Adm M j₀`,
  `c₁ = Mark (Pred M) j₋₁`, `j′₋₁ = Adm M j₀'`）は Lean 側の
  `transJ1`/`transJ0`/`transJm1`/`transC1`/`Adm M j₀'` にインライン展開。
- head の中身: 後方切片 `Trans((M_j)_{j=j′₋₁}^{j₁-1})` は非零 principal で
  頭 `D_{M_{1,j′₋₁}}`。Isabelle は `Mark_leftend_form`＋非零除去の手組みだが、
  Lean は `Mark_leftend_form_proper`（7.4-RightNodes-Mark、零ケース込み）で短絡。
- 依存: «7».«7.4-Mark-Trans-repr»（`Mark_Trans_repr`, `seg_Pred_eq`）,
  «7».«7.4-RightNodes-Mark»（`Mark_leftend_form_proper`）,
  «7».«7.3-Trans-welldefined»（`Marked_Pred`、transitively）,
  «6».«6.3-marked-slice» ほか §5/§6 基盤。
- 状態: ✅ sorry 0（本ファイル単独）。part4_1/part4_2 と
  `8.1-condI-III-c1-around.lean` の sorry 差し替えは次 wave。
-/

namespace PSS

/-! ## 行 1 の許容化祖先関係（Isabelle `adm_row1_ancestry` の私的再証明）

`7.3-Trans-welldefined.lean` / `8.1-condI-III-c1-around.lean` に同内容の private
補題があるが import できないため、ここに `_ps` 接尾辞で再掲する。
共有層 `PSS/Adm.lean` への昇格候補（needs 参照）。 -/

private theorem le1Aux_chain_ps (M : PS) (a : ℕ) (b fuel : ℕ)
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

theorem adm_row1_ancestry_ps (M : PS) (j : ℕ)
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
    le1Aux_chain_ps M (Adm M j) j (Lng M) haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_refl_ps (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_row0_ps (M : PS) (fuel : ℕ) (a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_ps]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_ps]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

private theorem row1_row0_ps (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_row0_ps M (Lng M) a b hM hh.1.2 hh.2

/-! ## part (4) setup — 幾何と Marked 事実の束
（Isabelle `m_8_1_c1_around_part4_setup`, layerB/pss_wip.thy:29756） -/

/-- part (4) の共有 setup: `adm M j₀` の下で許容化恒等 `j₋₁ = j₀`
（したがって `c₁ = Mark (Pred M) j₀`）、添字の幾何
`j′₋₁ ≤ j′₀ < j₀ < j₁ < Lng M`、`j₀ ≤ Lng (Pred M) - 1`、および
`(Pred M, j′₋₁) ∈ Marked`・`(Pred M, j₀) ∈ Marked`。 -/
theorem c1_around_part4_setup (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (_hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true) :
    transJm1 M = transJ0 M ∧
    transC1 M = Mark (Pred M) (transJ0 M) ∧
    Adm M j₀' ≤ j₀' ∧
    j₀' < transJ0 M ∧
    transJ0 M < transJ1 M ∧
    transJ1 M < Lng M ∧
    Adm M j₀' < transJ0 M ∧
    transJ0 M ≤ Lng (Pred M) - 1 ∧
    Marked (Pred M) (Adm M j₀') ∧
    Marked (Pred M) (transJ0 M) := by
  have hM : TPS M := RTPS_TPS M hR
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
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
  -- `j′₀ < j₀` と行 0 祖先
  have hn0 : nextrel0 M j₀' (transJ0 M) = true := by
    simpa [nextR] using np
  have hj0'lt : j₀' < transJ0 M := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hle0' : leR M 0 j₀' (transJ0 M) = true := nextR0_leR M _ _ np
  -- 許容化 `j′₋₁ = Adm M j′₀ ≤ j′₀`
  have haLe : Adm M j₀' ≤ j₀' := Adm_le M j₀'
  have haAdm : adm M (Adm M j₀') = true := Adm_adm M j₀'
  -- 行 1 祖先 → 行 0 祖先 → `j₁` までの連鎖
  have hle1a : leR M 1 (Adm M j₀') j₀' = true :=
    adm_row1_ancestry_ps M j₀' hM (by omega)
  have hle0a : leR M 0 (Adm M j₀') j₀' = true :=
    row1_row0_ps M _ _ hM hle1a
  have hchain : leR M 0 (Adm M j₀') (Lng M - 1) = true :=
    row0_transitive M _ _ _ hM
      (row0_transitive M _ _ _ hM hle0a hle0') hleJ0
  -- `(Pred M, j′₋₁) ∈ Marked`
  have hmarkedA : Marked M (Adm M j₀') := ⟨hM, haAdm, hchain⟩
  have hpredA : Marked (Pred M) (Adm M j₀') :=
    Marked_Pred M _ hM hlen hmarkedA (by omega)
  -- `(Pred M, j₀) ∈ Marked`
  have hmarkedJ0 : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
  have hpredJ0 : Marked (Pred M) (transJ0 M) :=
    Marked_Pred M _ hM hlen hmarkedJ0 (by omega)
  -- `adm M j₀` の下での許容化恒等 `j₋₁ = j₀`
  have hjm1 : transJm1 M = transJ0 M := by
    simp [transJm1, Adm, hadm]
  have hc1 : transC1 M = Mark (Pred M) (transJ0 M) := by
    simp [transC1, hjm1]
  have hPredL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  exact ⟨hjm1, hc1, haLe, hj0'lt, by omega, by omega, by omega, by omega,
    hpredA, hpredJ0⟩

/-! ## part (4) depth-1 head
（Isabelle `m_8_1_c1_around_part4_head`, layerB/pss_wip.thy:29815）

後方切片 `Trans((M_j)_{j=j′₋₁}^{j₁-1})` は頭 `D_{M_{1,j′₋₁}}` の非零 principal。
`Mark_Trans_repr`（`Mark (Pred M) j′₋₁` の切片表示）＋ `seg_Pred_eq`
（`Pred` 切片の `M` 切片への同定）＋ `Mark_leftend_form_proper`
（左端 principal 形、零ケース除去込み）＋ `butlast` の行 1 entry 保存。 -/

/-- part (4) depth-1 head: `∃ t, Trans((M_j)_{j=j′₋₁}^{j₁-1}) = D_{M_{1,j′₋₁}}(t)`。 -/
theorem c1_around_part4_head (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true) :
    ∃ t : BT, Trans (seg M (Adm M j₀') (transJ1 M - 1))
      = Dprin (entry M 1 (Adm M j₀') : ℕ∞) t := by
  obtain ⟨_hjm1, _hc1, _haLe, _hj0'lt, hj0j1, _hj1L, haj0, hj0ub, hpredA, _hpredJ0⟩ :=
    c1_around_part4_setup M j₀' hR hmono hadm hj1 hge np
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hlt : Adm M j₀' < Lng (Pred M) - 1 := by omega
  -- 後方切片表示: `Mark (Pred M) j′₋₁ = Trans (seg (Pred M) j′₋₁ (Lng (Pred M) - 1))`
  have hrepr : Mark (Pred M) (Adm M j₀') =
      Trans (seg (Pred M) (Adm M j₀') (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (Adm M j₀') hpredA hpredR hlt
  have hLP : Lng (Pred M) - 1 = transJ1 M - 1 := by omega
  -- `Pred` 切片 = `M` 切片
  have hsegeq : seg (Pred M) (Adm M j₀') (transJ1 M - 1) =
      seg M (Adm M j₀') (transJ1 M - 1) :=
    seg_Pred_eq M (Adm M j₀') (transJ1 M - 1) hlen (by omega) (by omega)
  have hreprM : Mark (Pred M) (Adm M j₀') =
      Trans (seg M (Adm M j₀') (transJ1 M - 1)) := by
    rw [hrepr, hLP, hsegeq]
  -- `butlast` は行 1 entry を保つ
  have he1 : entry (Pred M) 1 (Adm M j₀') = entry M 1 (Adm M j₀') := by
    rw [Pred_eq_take M hlen]
    exact entry_take M (Lng M - 1) 1 (Adm M j₀') (by omega)
  -- 左端 principal 形（零ケース除去は `Mark_leftend_form_proper` に内蔵）
  obtain ⟨t, ht⟩ :=
    Mark_leftend_form_proper (Pred M) (Adm M j₀') hpredA hpredR hlt
  refine ⟨t, ?_⟩
  rw [← hreprM, ht, he1]

#print axioms c1_around_part4_setup
#print axioms c1_around_part4_head

end PSS
