import «8».«8.4-slice-ext-engines»

/-!
# §8.4 `Kind1Shape_se` の討伐（`c1` の kind1 shape）

- 原文: `tmp/content.md` §8.4。ブループリント: Isabelle `s84c3_RightAnces_chain`
  （`isabelle/layerB/pss_wip.thy`:55372）＋ `m_8_4_Trans_scb`（同 :55575）の中核。
- 対象: «8».«8.4-slice-ext-engines» が露出した tight named 残差 `Kind1Shape_se`
  （dec1 エンジンが供給する `c1` の scb 分解 `(u0,v0)` を [Buc1] 第 1 種分解へ昇格）。

## 証明の骨格

`scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0` は与えられた scb 分解
（`hd0`）に、中心 principal `Trans (s84x_N M)` の右スパイン
`RightNodes (Trans (s84x_N M))` が **谷** であること（先頭 `M₁,ⱼ₋₃` < 末尾 `M₁,ⱼ₁`
≤ 各内点）を付ければよい。谷性は Isabelle の `RightAnces` 連鎖不変量を移植して得る:

1. `chain_k1`（= `s84c3_RightAnces_chain`）: 被約単項列 `Q` について
   `RightAnces Q = map (entry Q 1) ks` かつ index 連鎖 `ks` が `chainOK_k1`
   （0 始点・`Lng Q - 1` 終点・狭義増加・各点が終点の行0祖先・窓条件 `winOK_k1`）を満たす。
   `Lng` 上の強帰納法＋`RightAncesAux_RTPS_equation` の 1 段展開で構成する。
2. `sN_valley_k1`（= `m_8_4_Trans_scb` の中核）: `Q = Red (s84x_N M)` に連鎖不変量を適用し、
   `Q → N → M` の entry/le0/adm 移送（`IncrFirst` 冪＋切片）で `winOK` を M 側の谷へ変換。
3. `kind1Shape_holds`: `flatBT` 単射性で principal を同定し、谷を kind1 shape に組む。

- 依存（すべてビルド済み）: «8».«8.4-slice-ext-engines»（`Kind1Shape_se` def・`s84x_N`/
  `RightNodes`/`Trans`/`scb_decomp`/`scb_kind1`・`RightAnces`/`RightAncesAux`・
  `ancestor_slice_Red_IncrFirst`/`Mark_Trans_repr`/`Trans_Red` ほか §5–§7 基盤）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_k1`。
-/

namespace PSS

private def winOK_k1 (Q : PS) (ks : List ℕ) : Prop :=
  ∀ i, i + 1 < ks.length →
    adm Q (ks.getD i 0) = true ∨
      (entry Q 1 (ks.getD (i + 1) 0) ≤ entry Q 1 (ks.getD i 0) ∧
        (i + 1 = ks.length - 1 ∨ adm Q (ks.getD (i + 1) 0) = true))

private theorem getD_append_lt_k1 (xs ys : List ℕ) (i : ℕ) (h : i < xs.length) :
    (xs ++ ys).getD i 0 = xs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge_k1 (xs ys : List ℕ) (i : ℕ) (h : xs.length ≤ i) :
    (xs ++ ys).getD i 0 = ys.getD (i - xs.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private def chainOK_k1 (Q : PS) (ks : List ℕ) : Prop :=
  ks ≠ [] ∧ ks.getD 0 0 = 0 ∧ ks.getD (ks.length - 1) 0 = Lng Q - 1 ∧
    List.Pairwise (· < ·) ks ∧
    (∀ k ∈ ks, leR Q 0 k (Lng Q - 1) = true) ∧
    winOK_k1 Q ks

private theorem winOK_singleton_k1 (Q : PS) (a : ℕ) : winOK_k1 Q [a] := by
  intro i h; simp at h

private theorem winOK_pair_k1 (Q : PS) (a b : ℕ) (ha : adm Q a = true) :
    winOK_k1 Q [a, b] := by
  intro i h
  have hi : i = 0 := by simp at h; omega
  subst i
  exact Or.inl (by simpa using ha)

private theorem winOK_triple_k1 (Q : PS) (a b c : ℕ)
    (ha : adm Q a = true) (hbc : entry Q 1 c ≤ entry Q 1 b) :
    winOK_k1 Q [a, b, c] := by
  intro i h
  have hi : i = 0 ∨ i = 1 := by simp at h; omega
  rcases hi with hi | hi <;> subst i
  · exact Or.inl (by simpa using ha)
  · refine Or.inr ⟨by simpa using hbc, Or.inl (by simp)⟩

private theorem getD_prefix_agree_k1 (xs ys : List ℕ) (m k : ℕ)
    (hk : k ≤ xs.length) :
    (xs ++ [m]).getD k 0 = (xs ++ m :: ys).getD k 0 := by
  rcases Nat.lt_or_ge k xs.length with h | h
  · rw [getD_append_lt_k1 xs [m] k h, getD_append_lt_k1 xs (m :: ys) k h]
  · have hk' : k = xs.length := le_antisymm hk h
    subst k
    rw [getD_append_ge_k1 xs [m] _ (le_refl _),
      getD_append_ge_k1 xs (m :: ys) _ (le_refl _)]
    simp

private theorem winOK_glue_k1 (Q : PS) (xs ys : List ℕ) (m : ℕ)
    (hA : winOK_k1 Q (xs ++ [m])) (hB : winOK_k1 Q (m :: ys))
    (ham : adm Q m = true) : winOK_k1 Q (xs ++ m :: ys) := by
  intro i hi
  have hlenL : (xs ++ m :: ys).length = xs.length + 1 + ys.length := by
    simp [List.length_append]; omega
  rcases Nat.lt_or_ge i xs.length with hix | hix
  · have hLi : (xs ++ m :: ys).getD i 0 = (xs ++ [m]).getD i 0 :=
      (getD_prefix_agree_k1 xs ys m i (le_of_lt hix)).symm
    have hLi1 : (xs ++ m :: ys).getD (i + 1) 0 = (xs ++ [m]).getD (i + 1) 0 :=
      (getD_prefix_agree_k1 xs ys m (i + 1) hix).symm
    have hAi1 : i + 1 < (xs ++ [m]).length := by simp [List.length_append]; omega
    have hwA := hA i hAi1
    rw [hLi, hLi1]
    rcases hwA with hl | ⟨he, hend⟩
    · exact Or.inl hl
    · refine Or.inr ⟨he, ?_⟩
      have hAlen : (xs ++ [m]).length - 1 = xs.length := by simp [List.length_append]
      rcases hend with heq | hadm
      · rw [hAlen] at heq
        have : (xs ++ [m]).getD (i + 1) 0 = m := by
          rw [heq, getD_append_ge_k1 xs [m] _ (le_refl _)]; simp
        rw [this]; exact Or.inr ham
      · exact Or.inr hadm
  · set d := i - xs.length with hd
    have hid : i = xs.length + d := by omega
    have hLi : (xs ++ m :: ys).getD i 0 = (m :: ys).getD d 0 := by
      rw [getD_append_ge_k1 xs (m :: ys) i hix, ← hd]
    have hLi1 : (xs ++ m :: ys).getD (i + 1) 0 = (m :: ys).getD (d + 1) 0 := by
      rw [getD_append_ge_k1 xs (m :: ys) (i + 1) (by omega)]
      congr 1; omega
    have hBd : d + 1 < (m :: ys).length := by simp only [List.length_cons]; omega
    have hwB := hB d hBd
    rw [hLi, hLi1]
    rcases hwB with hl | ⟨he, hend⟩
    · exact Or.inl hl
    · refine Or.inr ⟨he, ?_⟩
      rcases hend with heq | hadm
      · left
        have : (m :: ys).length - 1 = ys.length := by simp
        rw [this] at heq
        rw [hlenL]; omega
      · exact Or.inr hadm

private theorem jplt_k1 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true) (hlen : 1 < Lng Q) :
    parent Q 0 (Lng Q - 1) < Lng Q - 1 := by
  have hQT : TPS Q := RTPS_TPS Q hR
  have hp0 : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hQT hmono (Lng Q - 1) (by omega) (by omega)
  exact (nextR_implies_row0 Q 0 _ _ (nextR_parent0_of_hasParent Q (Lng Q - 1) hp0)).1

private theorem row0_valley_last_k1 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (L : 1 < Lng Q) {j : ℕ}
    (hjp : parent Q 0 (Lng Q - 1) < j)
    (hle : leR Q 0 j (Lng Q - 1) = true) :
    j = Lng Q - 1 := by
  have hQT : TPS Q := RTPS_TPS Q hR
  have hp0 : hasParent Q 0 (Lng Q - 1) = true :=
    mono_hasParent_row0 Q hQT hmono (Lng Q - 1) (by omega) (by omega)
  have parR : nextR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
    nextR_parent0_of_hasParent Q (Lng Q - 1) hp0
  have nr0 : nextrel0 Q (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
    simpa [nextR] using parR
  have hle0 : le0 Q j (Lng Q - 1) = true := by simpa [leR] using hle
  have hjle : j ≤ Lng Q - 1 := le0_index_fseq hle0
  rcases Nat.lt_or_ge j (Lng Q - 1) with hlt | hge
  · exfalso
    have hgrow : entry Q 0 j < entry Q 0 (Lng Q - 1) :=
      ancestor_basic_1 Q j (Lng Q - 1) (Lng Q - 1) hQT hlt (le_refl _) hle
    have hh := nr0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range] at hh
    have hval := hh.2 j hlt
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_lt, decide_eq_true_eq] at hval
    rcases hval with hcontr | hdom
    · omega
    · omega
  · omega

private theorem row1_last_bound_k1 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (L : 1 < Lng Q) :
    entry Q 1 (Lng Q - 1) ≤ entry Q 1 (parent Q 0 (Lng Q - 1)) ∨
      entry Q 1 (parent Q 0 (Lng Q - 1)) + 1 = entry Q 1 (Lng Q - 1) := by
  have hQT : TPS Q := RTPS_TPS Q hR
  by_cases hge : entry Q 1 (Lng Q - 1) ≤ entry Q 1 (parent Q 0 (Lng Q - 1))
  · exact Or.inl hge
  · right
    have he1 : entry Q 1 (parent Q 0 (Lng Q - 1)) < entry Q 1 (Lng Q - 1) := by omega
    have hp0 : hasParent Q 0 (Lng Q - 1) = true :=
      mono_hasParent_row0 Q hQT hmono (Lng Q - 1) (by omega) (by omega)
    have parR : nextR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
      nextR_parent0_of_hasParent Q (Lng Q - 1) hp0
    have hjplt : parent Q 0 (Lng Q - 1) < Lng Q - 1 :=
      (nextR_implies_row0 Q 0 _ _ parR).1
    have hle0jp : leR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
      (nextR_implies_row0 Q 0 _ _ parR).2
    have hjpL : parent Q 0 (Lng Q - 1) < Lng Q := by omega
    have hj1L : Lng Q - 1 < Lng Q := by omega
    have nr1 : nextrel1 Q (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range]
      refine ⟨⟨⟨⟨⟨hjpL, hj1L⟩, hjplt⟩, he1⟩, by simpa [leR] using hle0jp⟩, ?_⟩
      intro j _hjL
      rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases hlt : parent Q 0 (Lng Q - 1) < j
      · by_cases hl0 : le0 Q j (Lng Q - 1) = true
        · right
          have hjeq : j = Lng Q - 1 :=
            row0_valley_last_k1 Q hR hmono L hlt (by simpa [leR] using hl0)
          rw [hjeq]; simp
        · exact Or.inl (Or.inr (by simpa using hl0))
      · exact Or.inl (Or.inl (by simpa using hlt))
    have wit1 : nextR Q 1 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true := by
      simpa [nextR] using nr1
    have huniq : ∀ y, nextR Q 1 y (Lng Q - 1) = true → y = parent Q 0 (Lng Q - 1) :=
      fun y hy => nextR1_unique_mr Q y (parent Q 0 (Lng Q - 1)) (Lng Q - 1) hy wit1
    have hpar1 : parent Q 1 (Lng Q - 1) = parent Q 0 (Lng Q - 1) :=
      parent_eq_of_unique_fseq Q 1 (Lng Q - 1) (parent Q 0 (Lng Q - 1)) wit1 huniq
    have hp1 : hasParent Q 1 (Lng Q - 1) = true :=
      (hasParent_iff_unique_fseq Q 1 (Lng Q - 1)).mpr ⟨_, wit1, huniq⟩
    have hA : RedCondA Q = true := (RTPS_condAB Q hR).1
    have hAsucc : entry Q 1 (parent Q 1 (Lng Q - 1)) + 1 = entry Q 1 (Lng Q - 1) := by
      have hh := hA
      simp only [RedCondA, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_true_eq] at hh
      have hthis := hh 1 (by omega) (Lng Q - 1) hj1L
      rcases hthis with hcontr | hgood
      · rw [hp1] at hcontr; simp at hcontr
      · exact hgood
    rw [hpar1] at hAsucc
    exact hAsucc

private theorem jpwin_k1 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true) (hlen : 1 < Lng Q)
    (hnc : (transCondI Q || transCondIII Q || transCondV Q || transCondVI Q) = false) :
    entry Q 1 (Lng Q - 1) ≤ entry Q 1 (parent Q 0 (Lng Q - 1)) ∧
      adm Q (parent Q 0 (Lng Q - 1)) = false := by
  simp only [Bool.or_eq_false_iff] at hnc
  obtain ⟨⟨⟨hI, hIII⟩, hV⟩, hVI⟩ := hnc
  have hjplt : parent Q 0 (Lng Q - 1) < Lng Q - 1 := jplt_k1 Q hR hmono hlen
  have dich := row1_last_bound_k1 Q hR hmono hlen
  by_cases he0 : entry Q 1 (Lng Q - 1) = 0
  · refine ⟨by omega, ?_⟩
    by_contra hadm
    have hadmt : adm Q (parent Q 0 (Lng Q - 1)) = true := by simpa using hadm
    have hcI : transCondI Q = true := by
      simp only [transCondI, lastIdx, lastParent, Bool.and_eq_true]
      exact ⟨by simpa using he0, hadmt⟩
    rw [hcI] at hI; simp at hI
  · have hpos : 0 < entry Q 1 (Lng Q - 1) := by omega
    rcases dich with hge | hsucc
    · refine ⟨hge, ?_⟩
      by_contra hadm
      have hadmt : adm Q (parent Q 0 (Lng Q - 1)) = true := by simpa using hadm
      have hcIII : transCondIII Q = true := by
        simp only [transCondIII, lastIdx, lastParent, Bool.and_eq_true]
        exact ⟨⟨by simpa using hpos, by simpa using hge⟩, hadmt⟩
      rw [hcIII] at hIII; simp at hIII
    · exfalso
      rcases Nat.lt_or_ge (parent Q 0 (Lng Q - 1) + 1) (Lng Q - 1) with hlt | hge2
      · have hcV : transCondV Q = true := by
          simp only [transCondV, lastIdx, lastParent, Bool.and_eq_true]
          exact ⟨⟨by simpa using hpos, by simpa using hsucc⟩, by simpa using hlt⟩
        rw [hcV] at hV; simp at hV
      · have heq : parent Q 0 (Lng Q - 1) + 1 = Lng Q - 1 := by omega
        have hcVI : transCondVI Q = true := by
          simp only [transCondVI, lastIdx, lastParent, Bool.and_eq_true]
          exact ⟨⟨by simpa using hpos, by simpa using hsucc⟩, by simpa using heq⟩
        rw [hcVI] at hVI; simp at hVI

private theorem RA_step_k1 (f : ℕ) (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (hlen : 1 < Lng Q) (hzPf : zeroT (Pred Q) = false) :
    RightAncesAux (f + 1) Q =
      (if zeroT (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) then [0]
       else RightAncesAux f (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))))
      ++ (if transCondI Q || transCondIII Q || transCondV Q || transCondVI Q
          then [entry Q 1 (Lng Q - 1)]
          else [entry Q 1 (parent Q 0 (Lng Q - 1)), entry Q 1 (Lng Q - 1)]) := by
  rw [RightAncesAux_RTPS_equation f Q hR]
  have hj1ne : (Lng Q - 1 == 0) = false := by simp; omega
  by_cases hc : (transCondI Q || transCondIII Q || transCondV Q || transCondVI Q) = true
  · simp [hj1ne, hmono, hzPf, hc]
  · simp [hj1ne, hmono, hzPf, hc]

private theorem winOK_transport_k1 (Q : PS) (jm : ℕ) (ks0 : List ℕ)
    (hbound : ∀ k ∈ ks0, k ≤ jm)
    (henttr : ∀ k, k ≤ jm → entry (seg Q 0 jm) 1 k = entry Q 1 k)
    (hadmtr : ∀ k, k ≤ jm → adm (seg Q 0 jm) k = true → adm Q k = true)
    (hw : winOK_k1 (seg Q 0 jm) ks0) : winOK_k1 Q ks0 := by
  intro i hi
  have hilt : i < ks0.length := by omega
  have hmi : ks0.getD i 0 ∈ ks0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]; exact List.getElem_mem hilt
  have hmi1 : ks0.getD (i + 1) 0 ∈ ks0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  have hbi := hbound _ hmi
  have hbi1 := hbound _ hmi1
  rcases hw i hi with hl | ⟨he, hend⟩
  · exact Or.inl (hadmtr _ hbi hl)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [← henttr _ hbi1, ← henttr _ hbi]; exact he
    · rcases hend with heq | had
      · exact Or.inl heq
      · exact Or.inr (hadmtr _ hbi1 had)

/-- The RightAnces chain invariant on reduced mono sequences (Isabelle
`s84c3_RightAnces_chain`). -/
private theorem chain_k1 : ∀ (n fuel : ℕ) (Q : PS), RTPS Q → monoT Q = true →
    Lng Q = n → Lng Q ≤ fuel →
    ∃ ks : List ℕ, RightAncesAux fuel Q = ks.map (fun k => entry Q 1 k) ∧ chainOK_k1 Q ks := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel Q hR hmono hn hfuel
    have hQT : TPS Q := RTPS_TPS Q hR
    have hpos : 0 < Lng Q := List.length_pos_of_ne_nil hQT
    have hmono' := hmono
    simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at hmono'
    obtain ⟨hnzQ, hmono00⟩ := hmono'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    by_cases hOne : Lng Q = 1
    · -- Length 1: Q = [(v,v)], RightAnces = [v], ks = [0]
      obtain ⟨v, rfl⟩ := (one_column Q hQT).1 ⟨hOne, hR⟩
      have hv0 : v ≠ 0 := by
        intro h; subst h; simp [zeroT, entry] at hnzQ
      have hRA : RightAncesAux (f + 1) [(v, v)] = [v] := by
        rw [RightAncesAux_RTPS_equation f [(v, v)] hR]
        simp [entry, hv0]
      refine ⟨[0], ?_, ?_⟩
      · rw [hRA]; simp [entry]
      · refine ⟨by simp, by simp, ?_, by simp, ?_, winOK_singleton_k1 [(v, v)] 0⟩
        · simp
        · intro k hk
          simp only [List.mem_singleton] at hk; subst hk
          exact leR0_refl_68 [(v, v)] 0 (by simp)
    · have hlen : 1 < Lng Q := by omega
      have hj1ne : Lng Q - 1 ≠ 0 := by omega
      by_cases hzP : zeroT (Pred Q) = true
      · -- Pred is zeroT: RightAnces = [0, entry Q 1 (Lng Q-1)], ks = [0, Lng Q-1]
        have he10z : entry Q 1 0 = 0 := by
          have hzz := hzP
          simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzz
          have := entry_Pred Q 1 0 (by omega)
          rw [← this]; exact hzz.2
        have hRA : RightAncesAux (f + 1) Q = [0, entry Q 1 (Lng Q - 1)] := by
          rw [RightAncesAux_RTPS_equation f Q hR]
          have : (Lng Q - 1 == 0) = false := by simp; omega
          simp [this, hmono, hzP]
        refine ⟨[0, Lng Q - 1], ?_, ?_⟩
        · rw [hRA]; simp [he10z]
        · refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
          · simp
          · simp; omega
          · intro k hk
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl
            · exact hmono00
            · exact leR0_refl_68 Q (Lng Q - 1) (by omega)
          · exact winOK_pair_k1 Q 0 (Lng Q - 1) (adm_zero Q)
      · -- Recursive branch
        have hzPf : zeroT (Pred Q) = false := by
          simpa using hzP
        have hp0 : hasParent Q 0 (Lng Q - 1) = true :=
          mono_hasParent_row0 Q hQT hmono (Lng Q - 1) (by omega) (by omega)
        have hnext : nextR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
          nextR_parent0_of_hasParent Q (Lng Q - 1) hp0
        have hjplt : parent Q 0 (Lng Q - 1) < Lng Q - 1 :=
          (nextR_implies_row0 Q 0 _ _ hnext).1
        have hjpj1le : leR Q 0 (parent Q 0 (Lng Q - 1)) (Lng Q - 1) = true :=
          (nextR_implies_row0 Q 0 _ _ hnext).2
        have hjmle : Adm Q (parent Q 0 (Lng Q - 1)) ≤ parent Q 0 (Lng Q - 1) :=
          Adm_le Q _
        have hjmlt : Adm Q (parent Q 0 (Lng Q - 1)) < Lng Q - 1 := by omega
        have hjmLast : Adm Q (parent Q 0 (Lng Q - 1)) ≤ Lng Q - 1 := by omega
        have hadmjm : adm Q (Adm Q (parent Q 0 (Lng Q - 1))) = true := Adm_adm Q _
        have hjpLe : parent Q 0 (Lng Q - 1) ≤ Lng Q - 1 := by omega
        have hrow1jm : leR Q 1 (Adm Q (parent Q 0 (Lng Q - 1))) (parent Q 0 (Lng Q - 1)) = true :=
          adm_row1_ancestry Q _ hQT hjpLe
        have hrow0jm : leR Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) (parent Q 0 (Lng Q - 1)) = true :=
          row1_implies_row0 Q _ _ hQT hrow1jm
        have hle0jmj1 : leR Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) (Lng Q - 1) = true :=
          row0_transitive Q _ _ _ hQT hrow0jm hjpj1le
        have hRA := RA_step_k1 f Q hR hmono hlen hzPf
        -- ============ a-part ============
        have apart : ∃ aks : List ℕ,
            (if zeroT (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) then [0]
             else RightAncesAux f (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))))
              = aks.map (fun k => entry Q 1 k) ∧
            aks ≠ [] ∧ aks.getD 0 0 = 0 ∧
            aks.getD (aks.length - 1) 0 = Adm Q (parent Q 0 (Lng Q - 1)) ∧
            List.Pairwise (· < ·) aks ∧
            (∀ k ∈ aks, k ≤ Adm Q (parent Q 0 (Lng Q - 1)) ∧
              leR Q 0 k (Adm Q (parent Q 0 (Lng Q - 1))) = true) ∧
            winOK_k1 Q aks := by
          by_cases hsegz : zeroT (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) = true
          · have hSlen : Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1))))
                = Adm Q (parent Q 0 (Lng Q - 1)) + 1 := by simp [length_seg]
            have hjmz : Adm Q (parent Q 0 (Lng Q - 1)) = 0 := by
              have hz := hsegz
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
              omega
            have he10z : entry Q 1 0 = 0 := by
              have hz := hsegz
              simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
              have heq := entry_seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) 1 0 (by omega)
              rw [hjmz] at heq
              simpa using heq ▸ hz.2
            refine ⟨[0], ?_, by simp, by simp, ?_, by simp, ?_, winOK_singleton_k1 Q 0⟩
            · simp [hsegz, he10z]
            · simp [hjmz]
            · intro k hk
              simp only [List.mem_singleton] at hk; subst k
              exact ⟨by omega, by rw [hjmz]; exact leR0_refl_68 Q 0 hpos⟩
          · have hsegnz : zeroT (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) = false := by
              simpa using hsegz
            have hSlen : Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1))))
                = Adm Q (parent Q 0 (Lng Q - 1)) + 1 := by simp [length_seg]
            have hSlt : Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) < n := by
              rw [hSlen, ← hn]; omega
            have hSR : RTPS (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) :=
              RTPS_initial_slice Q _ hR hjmLast
            have hfS : Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) ≤ f := by
              rw [hSlen]; omega
            -- transfer lemmas S ↔ Q (S = seg Q 0 jm)
            have henttr : ∀ k, k ≤ Adm Q (parent Q 0 (Lng Q - 1)) →
                entry (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) 1 k = entry Q 1 k := by
              intro k hk
              have hkS : k < Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) := by
                rw [hSlen]; omega
              have := entry_seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) 1 k hkS
              simpa using this
            have hle0tr : ∀ a b, a ≤ Adm Q (parent Q 0 (Lng Q - 1)) →
                b ≤ Adm Q (parent Q 0 (Lng Q - 1)) →
                leR (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) 0 a b = leR Q 0 a b := by
              intro a b ha hb
              have haS : a < Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) := by rw [hSlen]; omega
              have hbS : b < Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) := by rw [hSlen]; omega
              have := leR0_seg_adm Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) a b
                (by omega) (by omega) haS hbS
              simpa using this
            have hadmtr : ∀ k, k ≤ Adm Q (parent Q 0 (Lng Q - 1)) →
                adm (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) k = true → adm Q k = true := by
              intro k hk hadmS
              have hiff := adm_slice Q 0 k (Adm Q (parent Q 0 (Lng Q - 1))) hQT
                (by omega) hk hjmLast
              simp only [Nat.sub_zero] at hiff
              have := hiff.mpr hadmS
              rcases this with h | h | h
              · exact h
              · rw [← h]; exact adm_zero Q
              · rw [h]; exact hadmjm
            have hmonoS : monoT (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) = true := by
              have hle0Q0jm : leR Q 0 0 (Adm Q (parent Q 0 (Lng Q - 1))) = true :=
                ancestor_tree_1 Q 0 (Adm Q (parent Q 0 (Lng Q - 1))) (Lng Q - 1) hQT
                  hmono00 (Nat.zero_le _) hjmLast
              simp only [monoT, Bool.and_eq_true]
              refine ⟨by simpa using hsegnz, ?_⟩
              rw [show Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) - 1
                    = Adm Q (parent Q 0 (Lng Q - 1)) from by simp [hSlen]]
              rw [hle0tr 0 (Adm Q (parent Q 0 (Lng Q - 1))) (by omega) (le_refl _)]
              exact hle0Q0jm
            obtain ⟨ks0, hmap0, hchain0⟩ :=
              ih _ hSlt f _ hSR hmonoS rfl hfS
            obtain ⟨hne0, hhd0, hlast0, hsort0, hle0set0, hwin0⟩ := hchain0
            -- bounds
            have hbound0 : ∀ k ∈ ks0, k ≤ Adm Q (parent Q 0 (Lng Q - 1)) := by
              intro k hk
              have hle := hle0set0 k hk
              have hle0 : le0 (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) k
                  (Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) - 1) = true := by
                simpa [leR] using hle
              have := le0_index_fseq hle0
              rw [hSlen] at this; omega
            have hle0Q0 : ∀ k ∈ ks0, leR Q 0 k (Adm Q (parent Q 0 (Lng Q - 1))) = true := by
              intro k hk
              have hkb := hbound0 k hk
              have hle := hle0set0 k hk
              rw [show Lng (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1)))) - 1
                    = Adm Q (parent Q 0 (Lng Q - 1)) from by simp [hSlen]] at hle
              rw [← hle0tr k (Adm Q (parent Q 0 (Lng Q - 1))) hkb (le_refl _)]; exact hle
            have hmapeq : RightAncesAux f (seg Q 0 (Adm Q (parent Q 0 (Lng Q - 1))))
                = ks0.map (fun k => entry Q 1 k) := by
              rw [hmap0]
              apply List.map_congr_left
              intro x hx
              exact henttr x (hbound0 x hx)
            have hwinQ0 : winOK_k1 Q ks0 :=
              winOK_transport_k1 Q (Adm Q (parent Q 0 (Lng Q - 1))) ks0 hbound0 henttr hadmtr hwin0
            refine ⟨ks0, ?_, hne0, hhd0, ?_, hsort0, ?_, hwinQ0⟩
            · rw [if_neg hsegz, hmapeq]
            · rw [hlast0, hSlen]; omega
            · intro k hk; exact ⟨hbound0 k hk, hle0Q0 k hk⟩
        -- ============ assembly ============
        obtain ⟨aks, hamap, hane, hahd, halast, hasort, haset, hawin⟩ := apart
        -- The tail chain (packaged so the cond-split is done once).
        obtain ⟨tailks, htailmap, htailne, htaillast, htailsort, htaille0, htailgt, hwintail⟩ :
            ∃ tailks : List ℕ,
              (if transCondI Q || transCondIII Q || transCondV Q || transCondVI Q
                then [entry Q 1 (Lng Q - 1)]
                else [entry Q 1 (parent Q 0 (Lng Q - 1)), entry Q 1 (Lng Q - 1)])
                = tailks.map (fun k => entry Q 1 k) ∧
              tailks ≠ [] ∧
              tailks.getD (tailks.length - 1) 0 = Lng Q - 1 ∧
              List.Pairwise (· < ·) tailks ∧
              (∀ y ∈ tailks, leR Q 0 y (Lng Q - 1) = true) ∧
              (∀ y ∈ tailks, Adm Q (parent Q 0 (Lng Q - 1)) < y) ∧
              winOK_k1 Q (Adm Q (parent Q 0 (Lng Q - 1)) :: tailks) := by
          by_cases hc : (transCondI Q || transCondIII Q || transCondV Q || transCondVI Q) = true
          · refine ⟨[Lng Q - 1], by rw [if_pos hc]; simp, by simp, by simp, by simp, ?_, ?_, ?_⟩
            · intro y hy; simp only [List.mem_singleton] at hy; subst hy
              exact leR0_refl_68 Q (Lng Q - 1) (by omega)
            · intro y hy; simp only [List.mem_singleton] at hy; subst hy; omega
            · exact winOK_pair_k1 Q _ _ hadmjm
          · have hcf : (transCondI Q || transCondIII Q || transCondV Q || transCondVI Q) = false := by
              simpa using hc
            have hjw := jpwin_k1 Q hR hmono hlen hcf
            have hjmnjp : Adm Q (parent Q 0 (Lng Q - 1)) < parent Q 0 (Lng Q - 1) := by
              rcases Nat.lt_or_ge (Adm Q (parent Q 0 (Lng Q - 1))) (parent Q 0 (Lng Q - 1)) with h | h
              · exact h
              · exfalso
                have heqjp : Adm Q (parent Q 0 (Lng Q - 1)) = parent Q 0 (Lng Q - 1) := by omega
                rw [heqjp, hjw.2] at hadmjm; simp at hadmjm
            refine ⟨[parent Q 0 (Lng Q - 1), Lng Q - 1], by rw [if_neg hc]; simp,
              by simp, by simp, by simp [hjplt], ?_, ?_, ?_⟩
            · intro y hy; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hy
              rcases hy with rfl | rfl
              · exact hjpj1le
              · exact leR0_refl_68 Q (Lng Q - 1) (by omega)
            · intro y hy; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hy
              rcases hy with rfl | rfl
              · exact hjmnjp
              · omega
            · exact winOK_triple_k1 Q _ _ _ hadmjm hjw.1
        -- ks = aks ++ tailks
        have haposlen : 0 < aks.length := List.length_pos_of_ne_nil hane
        have htlposlen : 0 < tailks.length := List.length_pos_of_ne_nil htailne
        refine ⟨aks ++ tailks, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hRA, hamap, htailmap, List.map_append]
        · exact List.append_ne_nil_of_left_ne_nil hane _
        · rw [getD_append_lt_k1 aks tailks 0 haposlen]; exact hahd
        · rw [List.length_append,
            getD_append_ge_k1 aks tailks (aks.length + tailks.length - 1) (by omega)]
          have hidx : aks.length + tailks.length - 1 - aks.length = tailks.length - 1 := by omega
          rw [hidx]; exact htaillast
        · rw [List.pairwise_append]
          refine ⟨hasort, htailsort, ?_⟩
          intro x hx y hy
          exact lt_of_le_of_lt (haset x hx).1 (htailgt y hy)
        · intro k hk
          rw [List.mem_append] at hk
          rcases hk with hk | hk
          · exact row0_transitive Q k (Adm Q (parent Q 0 (Lng Q - 1))) (Lng Q - 1) hQT
              (haset k hk).2 hle0jmj1
          · exact htaille0 k hk
        · -- winOK via glue
          have hidxpos : aks.length - 1 < aks.length := by omega
          have hgetlast : aks.getLast hane = Adm Q (parent Q 0 (Lng Q - 1)) := by
            rw [List.getLast_eq_getElem hane, ← halast, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hidxpos, Option.getD_some]
          have hdecomp : aks.dropLast ++ [Adm Q (parent Q 0 (Lng Q - 1))] = aks := by
            conv_rhs => rw [← List.dropLast_append_getLast hane]
            rw [hgetlast]
          have hAglue : winOK_k1 Q (aks.dropLast ++ [Adm Q (parent Q 0 (Lng Q - 1))]) := by
            rw [hdecomp]; exact hawin
          have hglued := winOK_glue_k1 Q aks.dropLast tailks
            (Adm Q (parent Q 0 (Lng Q - 1))) hAglue hwintail hadmjm
          have hrw : aks.dropLast ++ Adm Q (parent Q 0 (Lng Q - 1)) :: tailks = aks ++ tailks := by
            rw [← List.singleton_append, ← List.append_assoc, hdecomp]
          rw [hrw] at hglued; exact hglued

private theorem adm_IncrFirstN_k1 (k : ℕ) (M : PS) (j : ℕ) :
    adm (IncrFirstN k M) j = adm M j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

/-- the built-in row-1 valley of the row-1 parent of the last column. -/
private theorem sN_valleyM_k1 (M : PS) (hMT : TPS M)
    (hp1 : hasParent M 1 (Lng M - 1) = true) :
    s84x_jm2 M < Lng M - 1 ∧
    entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) ∧
    (∀ j, s84x_jm2 M < j → le0 M j (Lng M - 1) = true →
      entry M 1 (Lng M - 1) ≤ entry M 1 j) := by
  have hnr1 : nextR M 1 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [s84x_jm2] using hasParent_next_fseq M 1 (Lng M - 1) hp1
  have hh1 := hnr1
  simp only [nextR, if_neg (by decide : ¬(1 : ℕ) = 0), nextrel1, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hh1
  obtain ⟨⟨⟨⟨⟨_hjm2L, _hj1L⟩, hjm2lt⟩, he1jm2lt⟩, _hle0jm2⟩, hvalleyraw⟩ := hh1
  refine ⟨hjm2lt, he1jm2lt, ?_⟩
  intro j hjgt hjle
  have hjL : j < Lng M := by have := le0_index_fseq hjle; omega
  have hv := hvalleyraw j hjL
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hv
  rcases hv with (hd | hd) | hd
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hd; omega
  · rw [hd] at hjle; simp at hjle
  · simpa using hd

/-- The valley of `RightNodes (Trans (s84x_N M))` (Isabelle `m_8_4_Trans_scb` middle). -/
private theorem sN_valley_k1 (M : PS) (hST : STPS M) (_hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    1 ≤ (RightNodes (Trans (s84x_N M))).length - 1 ∧
    (RightNodes (Trans (s84x_N M))).getD 0 0
      < (RightNodes (Trans (s84x_N M))).getD ((RightNodes (Trans (s84x_N M))).length - 1) 0 ∧
    ∀ j, 0 < j → j < (RightNodes (Trans (s84x_N M))).length - 1 →
      (RightNodes (Trans (s84x_N M))).getD ((RightNodes (Trans (s84x_N M))).length - 1) 0
        ≤ (RightNodes (Trans (s84x_N M))).getD j 0 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hjm2lt, he1jm2lt, valleyM⟩ := sN_valleyM_k1 M hMT hp1
  -- jm3 facts
  have hjm3le : s84x_jm3 M ≤ s84x_jm2 M := by simpa [s84x_jm3] using Adm_le M (s84x_jm2 M)
  have hjm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt hjm3le hjm2lt
  have hjm3Last : s84x_jm3 M ≤ Lng M - 1 := by omega
  have hadmjm3 : adm M (s84x_jm3 M) = true := by simpa [s84x_jm3] using Adm_adm M (s84x_jm2 M)
  have hjm2Le : s84x_jm2 M ≤ Lng M - 1 := by omega
  have hrow1 : leR M 1 (s84x_jm3 M) (s84x_jm2 M) = true := by
    simpa [s84x_jm3] using adm_row1_ancestry M (s84x_jm2 M) hMT hjm2Le
  have hrow0jm3 : leR M 0 (s84x_jm3 M) (s84x_jm2 M) = true := row1_implies_row0 M _ _ hMT hrow1
  have hle0jm2j1 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    have hnr1 : nextR M 1 (s84x_jm2 M) (Lng M - 1) = true := by
      simpa [s84x_jm2] using hasParent_next_fseq M 1 (Lng M - 1) hp1
    exact (nextR_implies_row0 M 1 _ _ hnr1).2
  have hle0jm3j1 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    row0_transitive M _ _ _ hMT hrow0jm3 hle0jm2j1
  have hMarked : Marked M (s84x_jm3 M) := ⟨hMT, hadmjm3, hle0jm3j1⟩
  have he1jm3le : entry M 1 (s84x_jm3 M) ≤ entry M 1 (s84x_jm2 M) := by
    rcases eq_or_lt_of_le hjm3le with heq | hlt
    · rw [heq]
    · exact le_of_lt (ancestor_basic_2 M (s84x_jm3 M) (s84x_jm2 M) (s84x_jm2 M) hMT hlt
        (le_refl _) hrow1 (leR0_refl_68 M _ (by omega)))
  have he1jm3lt : entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1) :=
    lt_of_le_of_lt he1jm3le he1jm2lt
  -- slice / Red / IncrFirst (use `set` to keep terms small)
  have hs84N : s84x_N M = seg M (s84x_jm3 M) (Lng M - 1) := rfl
  set N := seg M (s84x_jm3 M) (Lng M - 1) with hNdef
  have hsliceT : TPS N := by
    have : 0 < Lng N := by rw [hNdef, length_seg]; omega
    exact List.ne_nil_of_length_pos this
  have hslice_mono : monoT N = true := by
    rw [hNdef]; exact mono_ancestor_slice M (s84x_jm3 M) (Lng M - 1) hMT hjm3lt hle0jm3j1
  have hslice_multi : multiT N = false := by simp [multiT, hslice_mono]
  have hQR : RTPS (Red N) := Red_nonmulti_RTPS N hsliceT hslice_multi
  set Q := Red N with hQdef
  obtain ⟨_hRedQ, hmonoQ0, hseqIF0⟩ :=
    ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 1) hMR hjm3lt (le_refl _) hle0jm3j1
  rw [← hNdef, ← hQdef] at hmonoQ0 hseqIF0
  have hmonoQ : monoT Q = true := hmonoQ0
  have hseqIF : N = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M)) Q := hseqIF0
  -- lengths
  have hLenN : Lng N = Lng M - s84x_jm3 M := by rw [hNdef, length_seg]; omega
  have hLenQ : Lng N = Lng Q := by rw [hseqIF, length_IncrFirstN]
  have hLQval : Lng Q = Lng M - s84x_jm3 M := by rw [← hLenQ, hLenN]
  have hLQ2 : 2 ≤ Lng Q := by rw [hLQval]; omega
  have hidxLast : s84x_jm3 M + (Lng Q - 1) = Lng M - 1 := by rw [hLQval]; omega
  -- value
  have hTNQ : Trans N = Trans Q := by rw [hQdef]; exact Trans_Red N hsliceT
  obtain ⟨ks, hchmap, hchainOK⟩ :=
    chain_k1 (Lng Q) (transFuel Q) Q hQR hmonoQ rfl (transFuel_ge_length _)
  obtain ⟨hkne, hkhd, hklast, hksort, hkle0, hkwin⟩ := hchainOK
  have hRN_eq : RightNodes (Trans (s84x_N M)) = ks.map (fun k => entry Q 1 k) := by
    rw [hs84N, hTNQ, ← m_7_4_RightAnces_RightNodes Q hQR, RightAnces, hchmap]
  -- transfers
  have entryQM : ∀ k, k < Lng Q → entry Q 1 k = entry M 1 (s84x_jm3 M + k) := by
    intro k hk
    have h1 : entry N 1 k = entry Q 1 k := by rw [hseqIF]; exact entry_IncrFirstN_one _ _ _
    have hkN : k < Lng N := by rw [hLenQ]; exact hk
    have h2 : entry N 1 k = entry M 1 (s84x_jm3 M + k) := by
      rw [hNdef]; exact entry_seg M (s84x_jm3 M) (Lng M - 1) 1 k (by rw [hNdef] at hkN; exact hkN)
    rw [← h1, h2]
  have hleReq : leR N = leR Q := by rw [hseqIF]; exact leR_IncrFirstN _ _
  have le0QM : ∀ k, k < Lng Q → leR Q 0 k (Lng Q - 1) = true →
      leR M 0 (s84x_jm3 M + k) (Lng M - 1) = true := by
    intro k hk hle
    have hleN : leR N 0 k (Lng Q - 1) = true := by rw [hleReq]; exact hle
    rw [hNdef] at hleN
    have hkN : k < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by rw [← hNdef, hLenQ]; exact hk
    have hbN : Lng Q - 1 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by
      rw [← hNdef, hLenQ]; omega
    have htr := leR0_seg_adm M (s84x_jm3 M) (Lng M - 1) k (Lng Q - 1) (by omega) (by omega) hkN hbN
    rw [htr, hidxLast] at hleN
    simpa using hleN
  have admQM : ∀ k, 0 < k → k < Lng Q - 1 →
      adm Q k = true → adm M (s84x_jm3 M + k) = true := by
    intro k hkpos hkint hadmk
    have hadmN : adm (seg M (s84x_jm3 M) (Lng M - 1)) k = true := by
      rw [← hNdef, hseqIF, adm_IncrFirstN_k1]; exact hadmk
    have hiff := adm_slice M (s84x_jm3 M) (s84x_jm3 M + k) (Lng M - 1) hMT (by omega)
      (by rw [hLQval] at hkint; omega) (le_refl _)
    have hdisj := hiff.mpr (by
      rw [show s84x_jm3 M + k - s84x_jm3 M = k from by omega]; exact hadmN)
    rcases hdisj with h | h | h
    · exact h
    · omega
    · exfalso; rw [hLQval] at hkint; omega
  -- index bookkeeping
  have hgetD_getElem : ∀ i (hi : i < ks.length), ks.getD i 0 = ks[i] := by
    intro i hi; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hks_lt : ∀ i j, i < ks.length → j < ks.length → i < j →
      ks.getD i 0 < ks.getD j 0 := by
    intro i j hi hj hij
    rw [hgetD_getElem i hi, hgetD_getElem j hj]
    exact List.pairwise_iff_getElem.mp hksort i j hi hj hij
  have hlen2 : 2 ≤ ks.length := by
    by_contra hc
    have h1 : ks.length = 1 := by
      have : 0 < ks.length := List.length_pos_of_ne_nil hkne
      omega
    have hcontra : (0 : ℕ) = Lng Q - 1 := by rw [← hkhd, ← hklast, h1]
    omega
  have kidx : ∀ i, i < ks.length → ks.getD i 0 < Lng Q := by
    intro i hi
    have hmem : ks.getD i 0 ∈ ks := by rw [hgetD_getElem i hi]; exact List.getElem_mem hi
    have hle := hkle0 _ hmem
    have hle0 : le0 Q (ks.getD i 0) (Lng Q - 1) = true := by simpa [leR] using hle
    have := le0_index_fseq hle0; omega
  -- admissible bridge
  have admbridge : ∀ k, 0 < k → k < Lng Q - 1 → adm Q k = true →
      leR Q 0 k (Lng Q - 1) = true → entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm3 M + k) := by
    intro k hkpos hkint hadmk hlek
    have hadmM : adm M (s84x_jm3 M + k) = true := admQM k hkpos hkint hadmk
    have hgt : s84x_jm2 M < s84x_jm3 M + k := by
      by_contra hle
      rw [not_lt] at hle
      have hbound := Adm_max M (s84x_jm3 M + k) (s84x_jm2 M) hadmM hle
      have heq : Adm M (s84x_jm2 M) = s84x_jm3 M := rfl
      rw [heq] at hbound; omega
    have hle0M : le0 M (s84x_jm3 M + k) (Lng M - 1) = true := by
      simpa [leR] using le0QM k (by omega) hlek
    exact valleyM (s84x_jm3 M + k) hgt hle0M
  -- endpoints
  have hrlen : (RightNodes (Trans (s84x_N M))).length = ks.length := by
    rw [hRN_eq, List.length_map]
  have hr0 : (RightNodes (Trans (s84x_N M))).getD 0 0 = entry M 1 (s84x_jm3 M) := by
    rw [hRN_eq]
    have h0len : 0 < ks.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h0len]
    have hk0 : ks[0] = 0 := by rw [← hgetD_getElem 0 h0len]; exact hkhd
    simp only [Option.map_some, Option.getD_some, hk0]
    have := entryQM 0 (by omega); simpa using this
  have hrlast : (RightNodes (Trans (s84x_N M))).getD
      ((RightNodes (Trans (s84x_N M))).length - 1) 0 = entry M 1 (Lng M - 1) := by
    rw [hrlen, hRN_eq]
    have hll : ks.length - 1 < ks.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hll]
    have hval : ks[ks.length - 1] = Lng Q - 1 := by
      rw [← hgetD_getElem (ks.length - 1) hll]; exact hklast
    simp only [Option.map_some, Option.getD_some, hval]
    have := entryQM (Lng Q - 1) (by omega)
    rw [this, hidxLast]
  -- valley on the chain
  have valleyR : ∀ j, 0 < j → j < ks.length - 1 →
      entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm3 M + ks.getD j 0) := by
    intro j hjpos hjlt
    have hjlen : j < ks.length := by omega
    have hSjlen : j + 1 < ks.length := by omega
    have hlastlen : ks.length - 1 < ks.length := by omega
    have hkpos : 0 < ks.getD j 0 := by
      have hlt' : ks.getD 0 0 < ks.getD j 0 := hks_lt 0 j (by omega) hjlen hjpos
      omega
    have hkint : ks.getD j 0 < Lng Q - 1 := by
      have hlt' : ks.getD j 0 < ks.getD (ks.length - 1) 0 :=
        hks_lt j (ks.length - 1) hjlen hlastlen hjlt
      omega
    have hkL : ks.getD j 0 < Lng Q := by omega
    have hkmem : ks.getD j 0 ∈ ks := by rw [hgetD_getElem j hjlen]; exact List.getElem_mem hjlen
    have hle0k : leR Q 0 (ks.getD j 0) (Lng Q - 1) = true := hkle0 _ hkmem
    rcases hkwin j hSjlen with hadmk | ⟨hent, hend⟩
    · exact admbridge (ks.getD j 0) hkpos hkint hadmk hle0k
    · have hk'L : ks.getD (j + 1) 0 < Lng Q := kidx (j + 1) hSjlen
      have hk'mem : ks.getD (j + 1) 0 ∈ ks := by
        rw [hgetD_getElem (j + 1) hSjlen]; exact List.getElem_mem hSjlen
      have hle0k' : leR Q 0 (ks.getD (j + 1) 0) (Lng Q - 1) = true := hkle0 _ hk'mem
      have hentM : entry M 1 (s84x_jm3 M + ks.getD (j + 1) 0)
          ≤ entry M 1 (s84x_jm3 M + ks.getD j 0) := by
        rw [← entryQM (ks.getD (j + 1) 0) hk'L, ← entryQM (ks.getD j 0) hkL]; exact hent
      by_cases hj1last : j + 1 = ks.length - 1
      · have hk'eq : ks.getD (j + 1) 0 = Lng Q - 1 := by rw [hj1last]; exact hklast
        rw [hk'eq, hidxLast] at hentM; exact hentM
      · have hadmk' : adm Q (ks.getD (j + 1) 0) = true := by
          rcases hend with h | h
          · exact absurd h hj1last
          · exact h
        have hk'pos : 0 < ks.getD (j + 1) 0 := by
          have hlt' : ks.getD 0 0 < ks.getD (j + 1) 0 := hks_lt 0 (j + 1) (by omega) hSjlen (by omega)
          omega
        have hk'int : ks.getD (j + 1) 0 < Lng Q - 1 := by
          have hlt2 : j + 1 < ks.length - 1 := by omega
          have hlt' : ks.getD (j + 1) 0 < ks.getD (ks.length - 1) 0 :=
            hks_lt (j + 1) (ks.length - 1) hSjlen hlastlen hlt2
          omega
        exact le_trans (admbridge (ks.getD (j + 1) 0) hk'pos hk'int hadmk' hle0k') hentM
  -- assemble
  refine ⟨?_, ?_, ?_⟩
  · rw [hrlen]; omega
  · rw [hr0, hrlast]; exact he1jm3lt
  · intro j hjpos hjlt
    rw [hrlen] at hjlt
    have hjlen : j < ks.length := by omega
    rw [hrlast]
    have hrj : (RightNodes (Trans (s84x_N M))).getD j 0
        = entry M 1 (s84x_jm3 M + ks.getD j 0) := by
      rw [hRN_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjlen]
      have hgd : ks.getD j 0 = ks[j] := hgetD_getElem j hjlen
      simp only [Option.map_some, Option.getD_some]
      rw [← hgd]; exact entryQM (ks.getD j 0) (kidx j hjlen)
    rw [hrj]
    exact valleyR j hjpos hjlt


/-- **`Kind1Shape_se` の drop-in**（house pattern）。与えられた `c1` の scb 分解を
[Buc1] 第 1 種へ昇格する。`RightNodes (Trans (s84x_N M))` の谷性を `sN_valley_k1` から取り、
`flatBT` 単射性で principal を同定する。 -/
theorem kind1Shape_holds : Kind1Shape_se := by
  intro M u0 v0 hST hmono hp1 hj1 _hcond hd0
  refine ⟨hd0, ?_⟩
  intro p hpeq
  have hTeq : Trans (s84x_N M) = BT.trm [p] := flatBT_injective (by rw [hpeq]; rfl)
  have hRNeq : RightNodes (BT.trm [p]) = RightNodes (Trans (s84x_N M)) := by rw [hTeq]
  obtain ⟨h1, h2, h3⟩ := sN_valley_k1 M hST hmono hp1 hj1
  simp only [hRNeq]
  exact ⟨h1, h2, h3⟩

#print axioms kind1Shape_holds

end PSS
