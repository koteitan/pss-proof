import «8».«8.4-slice-ext-engines»
import «8».«8.4-oper5-residual»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.4 `L1SliceData_se` の討伐（`L₁` slice 幾何、条件(III)/(IV)）

- 対象: «8».«8.4-slice-ext-engines» が露出した tight named 残差
  `L1SliceData_se`（`L₁ := s84x_L M 1` の `Trans (Pred)`/`transC1`/`transC2` を
  `M` 側の語彙へ結ぶ純幾何）。
- ブループリント: Isabelle `s84d_L1_data`（`isabelle/layerB/pss_wip.thy`:59295,
  ~15 sub-lemmas）＋ `s84d_c2hole_L1`（59433）。
- 対象 Prop（`8.4-slice-ext-engines`:115）:
  ```
  ∀ M, STPS M → monoT M → hasParent M 1 (Lng M - 1) → 1 < Lng M - 1 →
    (transCondIII M ∨ transCondIV M) →
      RTPS (s84x_L M 1) ∧ monoT (s84x_L M 1) ∧ 1 < Lng (s84x_L M 1) ∧
      Trans (Pred (s84x_L M 1)) = Trans (Pred M) ∧
      transC1 (s84x_L M 1) = transC1 M ∧
      transC2 (s84x_L M 1) = c2hole_ch M (entry M 1 (s84x_jm2 M))
  ```

## 攻め筋

`8.5-exchV-nadm-c2l1` の `l1_geom_cl` / `l1_congr_cl` は **条件(V)** 版だが、
幾何部分は条件に依存せず `hasParent M 1 (Lng M - 1)` ＋ `1 < Lng M` のみで閉じる。
本ファイルはそれを条件(III)/(IV) 向けに再導出する。

1. `l1Geom_l1` — `l1_geom_cl` ＋ `exchV_L1_structure_adm` の mono/RTPS を統合。
   `Lng`/`Pred`/`RTPS`/`monoT`/`transJ0`/pairPrefix/`entry` 合同を無条件に。
2. `l1E1_l1` — `entry M 1 (s84x_jm2 M) < entry M 1 (transJ0 M)`（`s84c1_jm2_basic` の
   `entry M 1 (s84x_jm2 M) < entry M 1 (Lng M-1)` ＋ transCondIII/IV の
   `entry M 1 (Lng M-1) ≤ entry M 1 (transJ0 M)`）と `transJ0 M < Lng M - 1`。
3. `l1AdmJ0_l1` — `adm (s84x_L M 1) (transJ0 M) = adm M (transJ0 M)`。内部枝は
   `nextR_prefix_agree_68`、隅枝（`transJ0 M + 1 = Lng M - 1`）は両辺 true。
4. `l1TransC1_l1` — `transC1 (s84x_L M 1) = transC1 M`（`Adm` 合同 → `transJm1` 合同 →
   `Pred` 合同）。
5. `l1C2hole_l1` — `transC2 (s84x_L M 1) = c2hole_ch M (entry M 1 (s84x_jm2 M))`。
   `c2hole_at_j1_ch` で穴を露出し、branch/component 合同（regime, `transV`, `transT2`,
   `entry 1 (lastParent)`）で `c2hole_ch (s84x_L M 1) · = c2hole_ch M ·` に潰す。

- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_l1`。
-/

namespace PSS

/-! ## 1. `L₁` 幾何合同（`l1_geom_cl` ＋ mono/RTPS、条件非依存） -/

/-- `L₁ := s84x_L M 1` の幾何合同。Isabelle `s84d_L1_data` の合同群
（`Lng`/`Pred`/`transJ0`/entry）＋ `RTPS`/`monoT`。条件(V) 依存の `condV_setup`/
`condV_bridge` を落とし、`hasParent M 1 (Lng M - 1)` ＋ `1 < Lng M - 1` から直接。 -/
private theorem l1Geom_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    Lng (s84x_L M 1) = Lng M
    ∧ Pred (s84x_L M 1) = Pred M
    ∧ RTPS (s84x_L M 1)
    ∧ monoT (s84x_L M 1) = true
    ∧ transJ0 (s84x_L M 1) = transJ0 M
    ∧ (∀ j, j < Lng M - 1 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0))
    ∧ entry (s84x_L M 1) 1 (Lng M - 1) = entry M 1 (s84x_jm2 M)
    ∧ (∀ j, j < Lng M → entry (s84x_L M 1) 0 j = entry M 0 j) := by
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  have hlen : 1 < Lng M := by omega
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp1).1
  have hlejm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [leR] using (s84c1_jm2_basic M hp1).2.2
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hM hjm2lt (le_refl _) hlejm2
  have hsum : entry M 0 (s84x_jm2 M)
        + (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) = entry M 0 (Lng M - 1) := by omega
  have hL1form : s84x_L M 1
      = Pred M ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))] := by
    rw [s84x_L_eq_append, ← pred_is_oper1 M hM hlen]
    simp [hsum]
  have hPredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLngL1 : Lng (s84x_L M 1) = Lng M := by
    rw [hL1form]
    simp only [List.length_append, List.length_cons, List.length_nil, hPredLen]
    omega
  have hPredL1 : Pred (s84x_L M 1) = Pred M := by
    rw [Pred_eq_take (s84x_L M 1) (by rw [hLngL1]; omega), hL1form]
    have htake : (Pred M ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]).take (Lng M - 1)
        = Pred M := by
      rw [← hPredLen]; exact List.take_left' rfl
    simpa [hLngL1] using htake
  have hpairPrefix : ∀ j, j < Lng M - 1 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0) := by
    intro j hj
    have hjTake : j < (M.take (Lng M - 1)).length := by simp; omega
    rw [hL1form, Pred_eq_take M hlen]
    change ((M.take (Lng M - 1) ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))])[j]?).getD (0, 0) = (M[j]?).getD (0, 0)
    rw [List.getElem?_append_left hjTake, List.getElem?_take]
    simp [hj]
  have hentry1j1 : entry (s84x_L M 1) 1 (Lng M - 1) = entry M 1 (s84x_jm2 M) := by
    rw [hL1form, entry_append_right_mr (Pred M) _ 1 (Lng M - 1) (by rw [hPredLen]), hPredLen]
    simp [entry]
  have hentry0 : ∀ j, j < Lng M → entry (s84x_L M 1) 0 j = entry M 0 j := by
    intro j hj
    by_cases hjp : j < Lng M - 1
    · rw [hL1form, entry_append_left_mr (Pred M) _ 0 j (by rw [hPredLen]; exact hjp),
        Pred_eq_take M hlen, entry_take M (Lng M - 1) 0 j hjp]
    · have hjlast : j = Lng M - 1 := by omega
      subst j
      rw [hL1form, entry_append_right_mr (Pred M) _ 0 (Lng M - 1) (by rw [hPredLen]), hPredLen]
      simp [entry]
  -- monoT
  have hmonoL1 : monoT (s84x_L M 1) = true := by
    have hleM : le0 M 0 (Lng M - 1) = true := by
      have h := hmono
      simp only [monoT, Bool.and_eq_true] at h
      simpa [leR] using h.2
    have hleL : le0 (s84x_L M 1) 0 (Lng (s84x_L M 1) - 1) = true := by
      rw [hLngL1]
      rw [le0_row0_congr M (s84x_L M 1) id hLngL1.symm strictMono_id
        (by intro j hj; simpa using hentry0 j hj)]
      exact hleM
    have hzL : zeroT (s84x_L M 1) = false := by
      simp [zeroT, hLngL1]; omega
    simp [monoT, hzL, leR, hleL]
  -- RTPS
  have hRT : RTPS (s84x_L M 1) := RTPS_s84x_L M 1 hST hp1 hj1 (by omega)
  -- transJ0
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hnext0eq : ∀ a b, nextR (s84x_L M 1) 0 a b = nextR M 0 a b := by
    intro a b
    simp only [nextR]
    exact nextrel0_row0_congr M (s84x_L M 1) id hLngL1.symm strictMono_id
      (by intro j hj; simpa using hentry0 j hj) a b
  have hnextL : nextR (s84x_L M 1) 0 (transJ0 M) (Lng (s84x_L M 1) - 1) = true := by
    rw [hLngL1, hnext0eq]; exact hnextM
  obtain ⟨p, hp, huniq⟩ := (hasParent_iff_unique_fseq M 0 (Lng M - 1)).mp hp0
  have hpj0 : p = transJ0 M := (huniq (transJ0 M) hnextM).symm
  subst p
  have huniqL : ∀ y, nextR (s84x_L M 1) 0 y (Lng (s84x_L M 1) - 1) = true → y = transJ0 M := by
    intro y hy
    apply huniq
    have hy' : nextR (s84x_L M 1) 0 y (Lng M - 1) = true := by simpa [hLngL1] using hy
    rw [hnext0eq] at hy'; exact hy'
  have hparentL : parent (s84x_L M 1) 0 (Lng (s84x_L M 1) - 1) = transJ0 M :=
    parent_eq_of_unique_fseq (s84x_L M 1) 0 (Lng (s84x_L M 1) - 1) (transJ0 M) hnextL huniqL
  have hj0L : transJ0 (s84x_L M 1) = transJ0 M := by
    simpa [transJ0, lastParent, lastIdx] using hparentL
  exact ⟨hLngL1, hPredL1, hRT, hmonoL1, hj0L, hpairPrefix, hentry1j1, hentry0⟩

/-! ## 2. 行1エントリ facts（strict `<`） -/

/-- `entry M 1 (s84x_jm2 M) < entry M 1 (transJ0 M)` ＋ `transJ0 M < Lng M - 1`。
`s84c1_jm2_basic`（`< entry M 1 (Lng M-1)`）＋ transCondIII/IV（`entry M 1 (Lng M-1)
≤ entry M 1 (transJ0 M)`）。 -/
private theorem l1E1_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    entry M 1 (s84x_jm2 M) < entry M 1 (transJ0 M) ∧ transJ0 M < Lng M - 1 := by
  have hM : TPS M := STPS_TPS M hST
  have hlt1 : entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) := (s84c1_jm2_basic M hp1).2.1
  have hge : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    rcases hcond with h | h
    · have h' := h
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
    · have h' := h
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  exact ⟨by omega, hj0lt⟩

/-- 行1エントリの `getD` 表示（`l1_congr_cl` の `entry1_eq_getD_cl` の複製）。 -/
private theorem entry1_getD_l1 (X : PS) (j : ℕ) :
    entry X 1 j = (X.getD j (0, 0)).2 := by
  simp only [entry, List.getD_eq_getElem?_getD]
  cases X[j]? <;> simp

/-- 述語がリスト要素上で一致すれば `List.find?` は一致する（`find?_congr_cl` の複製）。 -/
private theorem find?_congr_l1 {α : Type _} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : p a = q a := h a (by simp)
    have iht : t.find? p = t.find? q := ih (fun x hx => h x (by simp [hx]))
    simp only [List.find?_cons, ha, iht]

/-! ## 3. `adm` 合同（内部枝 ＋ 隅枝） -/

/-- 内部枝の `adm` 合同: `j' + 1 < Lng M - 1` なら `adm (s84x_L M 1) j' = adm M j'`
（`nextR_prefix_agree_68`、`l1_congr_cl` と同型）。 -/
private theorem l1AdmCong_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    ∀ j', j' + 1 < Lng M - 1 → adm (s84x_L M 1) j' = adm M j' := by
  obtain ⟨hLng, _, _, _, _, hpair, _, _⟩ := l1Geom_l1 M hST hmono hp1 hj1
  intro j' hj'
  have hbound : Lng M - 2 < Lng M := by omega
  have hboundL : Lng M - 2 < Lng (s84x_L M 1) := by rw [hLng]; omega
  have hagree : ∀ j, j ≤ Lng M - 2 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0) := by
    intro j hj; exact hpair j (by omega)
  have h1 : nextR (s84x_L M 1) 1 (j' - 1) j' = nextR M 1 (j' - 1) j' :=
    nextR_prefix_agree_68 (s84x_L M 1) M (Lng M - 2) 1 (j' - 1) j'
      hagree hboundL hbound (by omega) (by omega)
  have h2 : nextR (s84x_L M 1) 1 j' (j' + 1) = nextR M 1 j' (j' + 1) :=
    nextR_prefix_agree_68 (s84x_L M 1) M (Lng M - 2) 1 j' (j' + 1)
      hagree hboundL hbound (by omega) (by omega)
  simp only [adm, nadm, hLng, h1, h2]

/-- `j₀` での `adm` 合同（内部枝は `l1AdmCong_l1`、隅枝 `transJ0 M + 1 = Lng M - 1`
は両辺 true）。隅では M/L₁ とも `nextR 1 j₀ (Lng M - 1)` が偽（entry 比較から）。 -/
private theorem l1AdmJ0_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    adm (s84x_L M 1) (transJ0 M) = adm M (transJ0 M) := by
  obtain ⟨hLng, _, _, _, hj0L, hpair, hEj1, _⟩ := l1Geom_l1 M hST hmono hp1 hj1
  obtain ⟨he1, hj0lt⟩ := l1E1_l1 M hST hmono hp1 hj1 hcond
  -- `entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M)`（transCondIII/IV）
  have hge : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    rcases hcond with h | h
    · have h' := h
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M); exact h'.1.2
    · have h' := h
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M); exact h'.1.2
  by_cases hint : transJ0 M + 1 < Lng M - 1
  · exact l1AdmCong_l1 M hST hmono hp1 hj1 (transJ0 M) hint
  · -- 隅: transJ0 M + 1 = Lng M - 1
    have hcorner : transJ0 M + 1 = Lng M - 1 := by omega
    -- 行1 prefix 合同
    have hentry1 : ∀ j, j < Lng M - 1 → entry (s84x_L M 1) 1 j = entry M 1 j := by
      intro j hj; rw [entry1_getD_l1, entry1_getD_l1, hpair j hj]
    -- M 側: adm M (transJ0 M) = true
    have hadmM : adm M (transJ0 M) = true := by
      simp only [adm, nadm, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff]
      refine ⟨by simp only [decide_eq_false_iff_not, Nat.not_lt]; omega, ?_⟩
      right
      have hnf : nextR M 1 (transJ0 M) (transJ0 M + 1) = false := by
        by_contra h
        rw [Bool.not_eq_false] at h
        simp only [nextR, if_neg (by decide : ¬ (1 = 0)), nextrel1, Bool.and_eq_true,
          decide_eq_true_eq] at h
        have : entry M 1 (transJ0 M) < entry M 1 (transJ0 M + 1) := h.1.1.2
        rw [hcorner] at this; omega
      exact hnf
    -- L₁ 側: adm (s84x_L M 1) (transJ0 M) = true
    have hadmL : adm (s84x_L M 1) (transJ0 M) = true := by
      simp only [adm, nadm, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff]
      refine ⟨by simp only [decide_eq_false_iff_not, Nat.not_lt]; rw [hLng]; omega, ?_⟩
      right
      have hnf : nextR (s84x_L M 1) 1 (transJ0 M) (transJ0 M + 1) = false := by
        by_contra h
        rw [Bool.not_eq_false] at h
        simp only [nextR, if_neg (by decide : ¬ (1 = 0)), nextrel1, Bool.and_eq_true,
          decide_eq_true_eq] at h
        have hlt : entry (s84x_L M 1) 1 (transJ0 M) < entry (s84x_L M 1) 1 (transJ0 M + 1) :=
          h.1.1.2
        rw [hentry1 (transJ0 M) hj0lt, hcorner, hEj1] at hlt
        omega
      exact hnf
    rw [hadmM, hadmL]

/-! ## 4. `transC1` 合同 -/

/-- `transC1 (s84x_L M 1) = transC1 M`（`Adm` 合同 → `transJm1` 合同 → `Pred` 合同、
`l1_congr_cl` の該当部と同型）。 -/
private theorem l1TransC1_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    transC1 (s84x_L M 1) = transC1 M := by
  obtain ⟨_, hPred, _, _, hj0L, _, _, _⟩ := l1Geom_l1 M hST hmono hp1 hj1
  obtain ⟨_, hj0lt⟩ := l1E1_l1 M hST hmono hp1 hj1 hcond
  have hadmJ0 : adm (s84x_L M 1) (transJ0 M) = adm M (transJ0 M) :=
    l1AdmJ0_l1 M hST hmono hp1 hj1 hcond
  have hfindcong : (List.range (transJ0 M)).reverse.find? (fun j' => adm (s84x_L M 1) j')
      = (List.range (transJ0 M)).reverse.find? (fun j' => adm M j') := by
    apply find?_congr_l1
    intro x hx
    have hxlt : x < transJ0 M := List.mem_range.mp (List.mem_reverse.mp hx)
    exact l1AdmCong_l1 M hST hmono hp1 hj1 x (by omega)
  have hAdmcong : Adm (s84x_L M 1) (transJ0 M) = Adm M (transJ0 M) := by
    simp only [Adm, hadmJ0, hfindcong]
  have htransJm1 : transJm1 (s84x_L M 1) = transJm1 M := by
    show Adm (s84x_L M 1) (transJ0 (s84x_L M 1)) = Adm M (transJ0 M)
    rw [hj0L, hAdmcong]
  show Mark (Pred (s84x_L M 1)) (transJm1 (s84x_L M 1)) = Mark (Pred M) (transJm1 M)
  rw [hPred, htransJm1]

/-! ## 5. `transC2` = c2hole（component 合同で `c2hole_ch (s84x_L M 1) = c2hole_ch M`） -/

/-- `transC2 (s84x_L M 1) = c2hole_ch M (entry M 1 (s84x_jm2 M))`。`c2hole_at_j1_ch` で
穴を露出し、regime / `transV` / `transT2` / `entry 1 (lastParent)` の component 合同で
`c2hole_ch (s84x_L M 1) · = c2hole_ch M ·` に潰す。 -/
private theorem l1C2hole_l1 (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp1 : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    transC2 (s84x_L M 1) = c2hole_ch M (entry M 1 (s84x_jm2 M)) := by
  obtain ⟨hLng, _, _, _, hj0L, hpair, hEj1, _⟩ := l1Geom_l1 M hST hmono hp1 hj1
  obtain ⟨he1, hj0lt⟩ := l1E1_l1 M hST hmono hp1 hj1 hcond
  -- `lastParent M` 形（`transJ0 M` と defeq）で omega が使えるようにする
  have he1' : entry M 1 (s84x_jm2 M) < entry M 1 (lastParent M) := he1
  have hadmJ0 : adm (s84x_L M 1) (transJ0 M) = adm M (transJ0 M) :=
    l1AdmJ0_l1 M hST hmono hp1 hj1 hcond
  have htransC1 : transC1 (s84x_L M 1) = transC1 M :=
    l1TransC1_l1 M hST hmono hp1 hj1 hcond
  -- `entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)`（transCondIII/IV）
  have hge : entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M) := by
    rcases hcond with h | h
    · have h' := h; simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact h'.1.2
    · have h' := h; simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact h'.1.2
  -- component 合同
  have hV : transV (s84x_L M 1) = transV M := by
    show bpHeadV (transC1 (s84x_L M 1)) = bpHeadV (transC1 M); rw [htransC1]
  have hT2 : transT2 (s84x_L M 1) = transT2 M := by
    show bpHeadT (transC1 (s84x_L M 1)) = bpHeadT (transC1 M); rw [htransC1]
  -- 行1 prefix 合同
  have hentry1 : ∀ j, j < Lng M - 1 → entry (s84x_L M 1) 1 j = entry M 1 j := by
    intro j hj; rw [entry1_getD_l1, entry1_getD_l1, hpair j hj]
  -- index 事実
  have hLi : lastIdx (s84x_L M 1) = Lng M - 1 := by simp only [lastIdx, hLng]
  have hLp : lastParent (s84x_L M 1) = transJ0 M := hj0L
  have hEi1 : entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1)) = entry M 1 (s84x_jm2 M) := by
    rw [hLi]; exact hEj1
  have hEp : entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) = entry M 1 (lastParent M) := by
    rw [hLp]; exact hentry1 (transJ0 M) hj0lt
  have hadmLp : adm (s84x_L M 1) (lastParent (s84x_L M 1)) = adm M (lastParent M) := by
    rw [hLp]; exact hadmJ0
  -- regime: transCondV/VI 両辺で偽
  have hmidL : (entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) + 1
      == entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1))) = false := by
    rw [hEp, hEi1]; simp only [beq_eq_false_iff_ne]; omega
  have hmidM : (entry M 1 (lastParent M) + 1 == entry M 1 (lastIdx M)) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have hVL : transCondV (s84x_L M 1) = false := by
    simp only [transCondV, hmidL, Bool.and_false, Bool.false_and]
  have hVM : transCondV M = false := by
    simp only [transCondV, hmidM, Bool.and_false, Bool.false_and]
  have hVIL : transCondVI (s84x_L M 1) = false := by
    simp only [transCondVI, hmidL, Bool.and_false, Bool.false_and]
  have hVIM : transCondVI M = false := by
    simp only [transCondVI, hmidM, Bool.and_false, Bool.false_and]
  have hVI : transCondVI (s84x_L M 1) = transCondVI M := by rw [hVIL, hVIM]
  -- regime disjunction 合同
  have hR1 : (transCondI (s84x_L M 1) || transCondIII (s84x_L M 1) || transCondV (s84x_L M 1))
      = (transCondI M || transCondIII M || transCondV M) := by
    rw [hVL, hVM, Bool.or_false, Bool.or_false]
    by_cases hadm : adm M (lastParent M) = true
    · -- adm true → transCondIII M true（transCondIV は !adm で偽）; 両辺 true
      have hIVfalse : transCondIV M = false := by
        simp only [transCondIV, hadm, Bool.not_true, Bool.and_false]
      have hIIIM : transCondIII M = true := by
        rcases hcond with h | h
        · exact h
        · rw [hIVfalse] at h; simp at h
      have hL : (transCondI (s84x_L M 1) || transCondIII (s84x_L M 1)) = true := by
        by_cases hz : entry M 1 (s84x_jm2 M) = 0
        · have hI : transCondI (s84x_L M 1) = true := by
            simp only [transCondI, hEi1, hadmLp, hadm, hz, Bool.and_true, beq_self_eq_true]
          simp [hI]
        · have hIII : transCondIII (s84x_L M 1) = true := by
            simp only [transCondIII, hEi1, hEp, hadmLp, hadm, Bool.and_true, Bool.and_eq_true,
              decide_eq_true_eq]
            exact ⟨by omega, by omega⟩
          simp [hIII]
      rw [hL]; simp [hIIIM]
    · -- adm false → transCondI/III すべて偽
      rw [Bool.not_eq_true] at hadm
      have hIL : transCondI (s84x_L M 1) = false := by
        simp only [transCondI, hadmLp, hadm, Bool.and_false]
      have hIIIL : transCondIII (s84x_L M 1) = false := by
        simp only [transCondIII, hadmLp, hadm, Bool.and_false]
      have hIM : transCondI M = false := by
        simp only [transCondI, hadm, Bool.and_false]
      have hIIIM : transCondIII M = false := by
        simp only [transCondIII, hadm, Bool.and_false]
      rw [hIL, hIIIL, hIM, hIIIM]
  -- 穴を露出し c2hole 合同で潰す
  have hstep1 : transC2 (s84x_L M 1)
      = c2hole_ch (s84x_L M 1) (entry M 1 (s84x_jm2 M)) := by
    rw [c2hole_at_j1_ch (s84x_L M 1), hEi1]
  rw [hstep1]
  simp only [c2hole_ch, c2hole_t3_ch, c2hole_t4_ch, hR1, hVI, hV, hT2, hEp]

/-! ## 6. 縮約本体 -/

section Main

/-- **`L1SliceData_se` の完全証明**。6 連言（`RTPS`/`monoT`/`1 < Lng`/`Trans (Pred)`/
`transC1`/`transC2`）を各 helper から組む。 -/
theorem l1SliceData_holds : L1SliceData_se := by
  intro M hST hmono hp1 hj1 hcond
  obtain ⟨hLng, hPred, hRT, hmonoL1, _, _, _, _⟩ := l1Geom_l1 M hST hmono hp1 hj1
  refine ⟨hRT, hmonoL1, ?_, ?_, ?_, ?_⟩
  · rw [hLng]; omega
  · rw [hPred]
  · exact l1TransC1_l1 M hST hmono hp1 hj1 hcond
  · exact l1C2hole_l1 M hST hmono hp1 hj1 hcond

#print axioms l1SliceData_holds

end Main

end PSS
