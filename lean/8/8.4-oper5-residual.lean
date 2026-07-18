import «8».«8.4-oper5-support»
import «7».«7.4-Mark-Trans-repr»
import «8».«8.6-Trans-Red-funpow-IncrFirst»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «7».«7.3-Trans-welldefined»

/-!
# §8.4 `oper` 基本性質 (5) の残差 `Oper5Residual` の discharge

- 原文: `tmp/content.md` 4389（命題「条件(III)〜(VI)の下での展開規則の基本性質」part(5)）。
- Isabelle（設計図）: `s84c1_*` クラスタ（`isabelle/layerB/pss_wip.thy`:53440–54005）。
  * 葉(4) `Marked (s84x_L M n) (s84x_ms M n)` ← `s84c1_marked_L`(:53860)
    = `s84c1_adm_L_mstar`(:53659) ＋ `s84c1_le0_L_mstar`(:53779)。
  * 葉(8) `Mark (s84x_L M n) (s84x_ms M n) = Trans (s84x_Lp M)` ← `s84c1_Mark_L_mstar`(:53883)。
  * 葉(9) 内部レジーム ← `s84c1_Mark_Mn_mstar`(:53932)。
- 依存（すべてビルド済み）: «8».«8.4-oper5-support»(`Oper5Residual`/`s84x_L`/`s84x_Lp`/
  `s84x_ms`/`s84x_w`)、«7».«7.4-Mark-Trans-repr»(`Mark_Trans_repr`)、
  «8».«8.6-Trans-Red-funpow-IncrFirst»(`Trans_funpow_IncrFirst`/`a1_Red_funpow_IncrFirst`)、
  «6».«6.6-ancestor-slice-Red-IncrFirst»(`ancestor_slice_Red_IncrFirst`)、
  «7».«7.3-Trans-welldefined»(`Marked_Pred`)。
- 状態: 🤖 building。Private helper suffix: `_o5r`。
-/

namespace PSS

/-! ## 0. 算術補助 -/

/-- `n·w = (n−1)·w + w`（`n ≥ 1`）。 -/
private theorem mult_pred_o5r (n w : ℕ) (hn : 1 ≤ n) : n * w = (n - 1) * w + w := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Nat.succ_mul]

/-! ## 1. 共有下ごしらえ -/

/-- 条件(III)〜(VI)下の共有事実（`idx1 = 1`, 親 `= j₋₂`, 行0の厳増 `e0lt`）。 -/
private theorem setup_o5r (M : PS) (hM : TPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    idx1 M (Lng M - 1) = 1 ∧ 1 < Lng M ∧
      ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
      parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M ∧
      s84x_jm2 M < Lng M - 1 ∧
      entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) := by
  obtain ⟨hjm2lt, he1, hle0⟩ := s84c1_jm2_basic M hp
  have he1pos : 0 < entry M 1 (Lng M - 1) := by omega
  have hidx : idx1 M (Lng M - 1) = 1 := by unfold idx1; rw [if_pos he1pos]
  have hlast : 1 < Lng M := by omega
  have hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hidx]; exact hp
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) := by
    have hleR : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using hle0
    exact ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hM hjm2lt (le_refl _) hleR
  exact ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩

/-- `Lng (M[k]) = j₋₂ + k·w`（Isabelle `s84c1_Lng_oper`）。 -/
private theorem Lng_oper_o5r (M : PS) (k : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    Lng (oper M k) = s84x_jm2 M + k * (Lng M - 1 - s84x_jm2 M) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have h : Lng (oper M k)
      = parent M (idx1 M (Lng M - 1)) (Lng M - 1)
          + k * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :=
    length_oper_tiling M k hlast hnz hp'
  rw [hj0] at h; exact h

/-! ## 2. タイル一段展開と末尾ブロック -/

/-- 基本列の一段展開（Isabelle `s84c1_oper_Suc_eq_L_app` の oper-append 形）。 -/
private theorem oper_succ_append_o5r (M : PS) (m : ℕ)
    (hlast : 1 < Lng M)
    (hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    oper M (m + 1) = oper M m ++
      (List.range' (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                   (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))).map
        (fun j => (entry M 0 j
                     + m * (if 0 < idx1 M (Lng M - 1)
                            then entry M 0 (Lng M - 1)
                                   - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                            else 0),
                   entry M 1 j
                     + m * (if 1 < idx1 M (Lng M - 1)
                            then entry M 1 (Lng M - 1)
                                   - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                            else 0))) := by
  have e1 := oper_tiling_expand M (m + 1) hlast hnz hp'
  have e0 := oper_tiling_expand M m hlast hnz hp'
  dsimp only at e1 e0
  rw [e1, e0, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc]

/-- 末尾ブロック（Isabelle `s84c1_oper_lastblock`）: `drop m* (M[m+1])` はブロック `m`。 -/
private theorem oper_lastblock_o5r (M : PS) (m : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    (oper M (m + 1)).drop (s84x_jm2 M + m * (Lng M - 1 - s84x_jm2 M))
      = (List.range' (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M)).map
          (fun j => (entry M 0 j
                       + m * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                     entry M 1 j)) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hd1 : (if 1 < idx1 M (Lng M - 1)
             then entry M 1 (Lng M - 1) - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = 0 := by rw [hidx]; simp
  have hd0 : (if 0 < idx1 M (Lng M - 1)
             then entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) := by
    rw [hidx]; simp [s84x_jm2]
  have happ := oper_succ_append_o5r M m hlast hnz hp'
  simp only [hd0, hd1, Nat.mul_zero, Nat.add_zero] at happ
  simp only [hj0] at happ
  have hLng_m : (oper M m).length = s84x_jm2 M + m * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M m hM hp hj1
  rw [happ, List.drop_left' hLng_m]

/-! ## 3. `M[n]` の基点位置での成分読み出し -/

/-- `entry (M[n]) i m*`（`m* = j₋₂ + (n−1)w`）: Isabelle `s84c1_Mn_entry_mstar`。 -/
private theorem entry_oper_ms_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    entry (oper M n) 0 (s84x_ms M n)
        = entry M 0 (s84x_jm2 M)
            + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
      ∧ entry (oper M n) 1 (s84x_ms M n) = entry M 1 (s84x_jm2 M) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hq : n - 1 < n := by omega
  have hs0 : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
    rw [hj0]; omega
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hif0 : (if 0 < idx1 M (Lng M - 1)
             then entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) else (0 : ℕ))
             = entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) := by rw [hidx]; simp
  refine ⟨?_, ?_⟩
  · have hr := entry_oper_tiling_block_zero M n (n - 1) 0 hlast hnz hp' hq hs0
    rw [hj0] at hr
    simp only [Nat.add_zero] at hr
    rw [hif0] at hr
    rw [hms_eq]; exact hr
  · have hr := entry_oper_tiling_block_one M n (n - 1) 0 hlast hnz hp' hq hs0
    rw [hj0] at hr
    simp only [Nat.add_zero] at hr
    rw [hms_eq]; exact hr

/-- `entry (M[n]) i (m*−1)`（前列）: Isabelle `s84c1_Mn_entry_mstar_pred`。 -/
private theorem entry_oper_msm1_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 2 ≤ n) :
    entry (oper M n) 0 (s84x_ms M n - 1)
        = entry M 0 (Lng M - 2)
            + (n - 2) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
      ∧ entry (oper M n) 1 (s84x_ms M n - 1) = entry M 1 (Lng M - 2) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hq : n - 2 < n := by omega
  have hs : Lng M - 1 - s84x_jm2 M - 1 < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
    rw [hj0]; omega
  have hsplit : (n - 1) * (Lng M - 1 - s84x_jm2 M)
      = (n - 2) * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) := by
    have h := mult_pred_o5r (n - 1) (Lng M - 1 - s84x_jm2 M) (by omega)
    simpa [show n - 1 - 1 = n - 2 by omega] using h
  have hidx_eq : s84x_jm2 M + (n - 2) * (Lng M - 1 - s84x_jm2 M)
        + (Lng M - 1 - s84x_jm2 M - 1) = s84x_ms M n - 1 := by
    simp only [s84x_ms, s84x_w]; omega
  have harg_eq : s84x_jm2 M + (Lng M - 1 - s84x_jm2 M - 1) = Lng M - 2 := by omega
  have hif0 : (if 0 < idx1 M (Lng M - 1)
             then entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) else (0 : ℕ))
             = entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) := by rw [hidx]; simp
  refine ⟨?_, ?_⟩
  · have hr := entry_oper_tiling_block_zero M n (n - 2) (Lng M - 1 - s84x_jm2 M - 1)
      hlast hnz hp' hq hs
    rw [hj0] at hr
    rw [hif0] at hr
    rw [hidx_eq, harg_eq] at hr
    exact hr
  · have hr := entry_oper_tiling_block_one M n (n - 2) (Lng M - 1 - s84x_jm2 M - 1)
      hlast hnz hp' hq hs
    rw [hj0] at hr
    rw [hidx_eq, harg_eq] at hr
    exact hr

/-! ## 4. `s84x_L` の展開・切片・末尾 -/

/-- `s84x_L M m = M[m] ++ [末尾列]`（定義）。 -/
private theorem s84x_L_append_o5r (M : PS) (m : ℕ) :
    s84x_L M m = oper M m ++
      [(entry M 0 (s84x_jm2 M)
          + m * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
        entry M 1 (s84x_jm2 M))] := rfl

/-- `entry (L_m) i j = entry (M[m]) i j`（末尾列より左）。 -/
private theorem entry_L_eq_oper_o5r (M : PS) (m i j : ℕ) (hj : j < Lng (oper M m)) :
    entry (s84x_L M m) i j = entry (oper M m) i j := by
  rw [s84x_L_append_o5r]
  unfold entry
  rw [List.getElem?_append_left hj]

/-- `seg X a (Lng X − 1) = drop a X`（`a < Lng X`）。Isabelle `seg_to_last_eq_drop`。 -/
private theorem seg_to_drop_o5r (X : PS) (a : ℕ) (ha : a < Lng X) :
    seg X a (Lng X - 1) = X.drop a := by
  rw [seg_eq_take_drop_adm X a (Lng X - 1) (by omega) (by omega)]
  have hd : (X.drop a).length = Lng X - a := by rw [List.length_drop]
  have hlen : (X.drop a).length = Lng X - 1 + 1 - a := by omega
  rw [← hlen, List.take_length]

/-- `range'` の末尾切り出し。 -/
private theorem range'_snoc_o5r (s n : ℕ) :
    List.range' s n ++ [s + n] = List.range' s (n + 1) := by
  have := List.range'_append_1 (s := s) (m := n) (n := 1); simpa using this

/-- `N' = seg M j₋₂ (Lng M − 2) ++ [(M_{0,j₁}, M_{1,j₁})]`。Isabelle 経由で `Pred N'` を得る。 -/
private theorem Np_snoc_o5r (M : PS) (hjm2lt : s84x_jm2 M < Lng M - 1) :
    s84x_Np M = seg M (s84x_jm2 M) (Lng M - 2)
      ++ [(entry M 0 (Lng M - 1), entry M 1 (Lng M - 1))] := by
  have hw : Lng M - 1 + 1 - s84x_jm2 M = (Lng M - 2 + 1 - s84x_jm2 M) + 1 := by omega
  have hend : s84x_jm2 M + (Lng M - 2 + 1 - s84x_jm2 M) = Lng M - 1 := by omega
  unfold s84x_Np seg
  rw [hw, ← range'_snoc_o5r, List.map_append, hend]
  simp

/-- `Pred N' = seg M j₋₂ (Lng M − 2)`。Isabelle `s84c1_Pred_Np`。 -/
theorem Pred_s84x_Np (M : PS) (hjm2lt : s84x_jm2 M < Lng M - 1) :
    Pred (s84x_Np M) = seg M (s84x_jm2 M) (Lng M - 2) := by
  have hlen : 1 < Lng (s84x_Np M) := by
    simp only [s84x_Np, length_seg]; omega
  rw [Pred, if_neg (by omega)]
  rw [Np_snoc_o5r M hjm2lt]
  simp

/-- 末尾列だけ行1が異なる append の行0成分は一致。 -/
private theorem entry0_append_congr_o5r (P : PS) (a b : ℕ × ℕ) (hab : a.1 = b.1) (j : ℕ) :
    entry (P ++ [a]) 0 j = entry (P ++ [b]) 0 j := by
  unfold entry
  rcases lt_trichotomy j P.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · subst heq
    rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _)]
    simp [hab]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- `entry (IncrFirstN k X) 0 j = entry X 0 j + k`（`j < Lng X`）。 -/
private theorem entry_IncrFirstN0_o5r (X : PS) (k j : ℕ) (hj : j < Lng X) :
    entry (IncrFirstN k X) 0 j = entry X 0 j + k := by
  rw [IncrFirstN_eq_map]
  unfold entry
  rw [List.getElem?_map, List.getElem?_eq_getElem hj]
  simp

/-! ## 5. 行0のみに依存する `le0` の合同（Isabelle `s84c1_le0_cong` ＋ IncrFirst 不変性） -/

/-- 行0が狭義単調 `φ` で対応する 2 列で `nextrel0` は一致。 -/
private theorem nextrel0_row0_o5r (X Y : PS) (φ : ℕ → ℕ)
    (hlen : Lng X = Lng Y) (hmono : StrictMono φ)
    (hφ : ∀ j, j < Lng X → entry Y 0 j = φ (entry X 0 j))
    (a b : ℕ) : nextrel0 Y a b = nextrel0 X a b := by
  by_cases ha : a < Lng X
  · by_cases hb : b < Lng X
    · apply Bool.eq_iff_iff.mpr
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, ← hlen, ha, hb, true_and]
      constructor
      · rintro ⟨⟨hab, hent⟩, hall⟩
        rw [hφ a ha, hφ b hb] at hent
        refine ⟨⟨hab, hmono.lt_iff_lt.mp hent⟩, ?_⟩
        intro j hj
        have hjX : j < Lng X := hj.trans hb
        have hh := hall j hj
        by_cases haj : a < j
        · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
          rw [hφ b hb, hφ j hjX] at hh
          exact decide_eq_true (hmono.le_iff_le.mp (of_decide_eq_true hh))
        · simp [haj]
      · rintro ⟨⟨hab, hent⟩, hall⟩
        refine ⟨⟨hab, ?_⟩, ?_⟩
        · rw [hφ a ha, hφ b hb]; exact hmono.lt_iff_lt.mpr hent
        · intro j hj
          have hjX : j < Lng X := hj.trans hb
          have hh := hall j hj
          by_cases haj : a < j
          · simp only [haj, decide_true, Bool.not_true, Bool.false_or] at hh ⊢
            rw [hφ b hb, hφ j hjX]
            exact decide_eq_true (hmono.le_iff_le.mpr (of_decide_eq_true hh))
          · simp [haj]
    · simp [nextrel0, hb, ← hlen]
  · simp [nextrel0, ha, ← hlen]

private theorem le0Aux_row0_o5r (X Y : PS) (φ : ℕ → ℕ)
    (hlen : Lng X = Lng Y) (hmono : StrictMono φ)
    (hφ : ∀ j, j < Lng X → entry Y 0 j = φ (entry X 0 j))
    (fuel a b : ℕ) : le0Aux Y fuel a b = le0Aux X fuel a b := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
      simp only [le0Aux, nextrel0_row0_o5r X Y φ hlen hmono hφ, ih]

/-- 行0が狭義単調で対応する 2 列で `le0` は一致。 -/
private theorem le0_row0_o5r (X Y : PS) (φ : ℕ → ℕ)
    (hlen : Lng X = Lng Y) (hmono : StrictMono φ)
    (hφ : ∀ j, j < Lng X → entry Y 0 j = φ (entry X 0 j))
    (a b : ℕ) : le0 Y a b = le0 X a b := by
  unfold le0
  rw [hlen, le0Aux_row0_o5r X Y φ hlen hmono hφ]

/-! ## 6. 末尾切片 = `IncrFirstN kk L'`（Isabelle `s84c1_L_tail`） -/

/-- `seg (L_n) m* (Lng (L_n) − 1) = (IncrFirst^kk) L'`（`kk = (n−1)d₀`）。 -/
private theorem L_tail_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    seg (s84x_L M n) (s84x_ms M n) (Lng (s84x_L M n) - 1)
      = IncrFirstN ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))) (s84x_Lp M) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hM hp hj1
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hwpos : 0 < Lng M - 1 - s84x_jm2 M := by omega
  have hmul : (n - 1) * (Lng M - 1 - s84x_jm2 M) ≤ n * (Lng M - 1 - s84x_jm2 M) :=
    Nat.mul_le_mul_right _ (by omega)
  have hLngL : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hms_le : s84x_ms M n ≤ Lng (oper M n) := by rw [hLng_n, hms_eq]; omega
  have hms_ltL : s84x_ms M n < Lng (s84x_L M n) := by rw [hLngL]; omega
  -- 末尾ブロック
  have hblock : (oper M n).drop (s84x_ms M n)
      = (List.range' (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M)).map
          (fun j => (entry M 0 j
                       + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                     entry M 1 j)) := by
    have h := oper_lastblock_o5r M (n - 1) hM hp hj1
    rw [Nat.sub_add_cancel hn] at h
    rw [hms_eq]; exact h
  -- seg → drop → block ++ [末尾列]
  rw [seg_to_drop_o5r (s84x_L M n) (s84x_ms M n) hms_ltL, s84x_L_append_o5r,
    List.drop_append_of_le_length hms_le, hblock]
  -- 底 L' の seg 部分の range' 化
  have hseg_range : seg M (s84x_jm2 M) (Lng M - 2)
      = (List.range' (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M)).map
          (fun j => (entry M 0 j, entry M 1 j)) := by
    unfold seg
    rw [show Lng M - 2 + 1 - s84x_jm2 M = Lng M - 1 - s84x_jm2 M from by omega]
  -- 末尾列の行0の一致
  have hlast_eq : entry M 0 (s84x_jm2 M)
        + n * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
      = entry M 0 (Lng M - 1)
        + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) := by
    have h := mult_pred_o5r n (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) hn
    omega
  -- 右辺 IncrFirstN kk L' を展開
  rw [IncrFirstN_eq_map]
  unfold s84x_Lp
  rw [List.map_append, hlast_eq]
  congr 1
  simp only [hseg_range, List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

/-! ## 7. 基本列の L-append 形と `L_n`/`M[n]` の RT_PS 所属・末尾切片 -/

/-- `(n−1)·w < n·w`（`n ≥ 1`, `w > 0`）。 -/
private theorem sub_mul_lt_o5r (k w : ℕ) (hk : 1 ≤ k) (hw : 0 < w) :
    (k - 1) * w < k * w := by
  have h := mult_pred_o5r k w hk; omega

/-- `range'` の先頭剥がし（`n > 0`）。 -/
private theorem range'_eq_cons_o5r (s n : ℕ) (hn : 0 < n) :
    List.range' s n = s :: List.range' (s + 1) (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-- `M[m+1] = L_m ++ 残り`（`idx1 = 1` に特殊化した L-append 形）。
Isabelle `s84c1_oper_Suc_eq_L_app`（`s84x_L` 形、wip:52886）。 -/
private theorem oper_succ_L_o5r (M : PS) (m : ℕ)
    (hlast : 1 < Lng M)
    (hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hidx : idx1 M (Lng M - 1) = 1)
    (hjm2lt : s84x_jm2 M < Lng M - 1) :
    oper M (m + 1) = s84x_L M m ++
      (List.range' (s84x_jm2 M + 1) (Lng M - 1 - s84x_jm2 M - 1)).map
        (fun j => (entry M 0 j
                     + m * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                   entry M 1 j)) := by
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  have hd1 : (if 1 < idx1 M (Lng M - 1)
             then entry M 1 (Lng M - 1) - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = 0 := by rw [hidx]; simp
  have hd0 : (if 0 < idx1 M (Lng M - 1)
             then entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) := by
    rw [hidx]; simp [s84x_jm2]
  have happ := oper_succ_append_o5r M m hlast hnz hp'
  simp only [hd0, hd1, Nat.mul_zero, Nat.add_zero] at happ
  simp only [hj0] at happ
  rw [happ, range'_eq_cons_o5r (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M) (by omega),
    List.map_cons, s84x_L_append_o5r]
  rw [List.append_assoc]
  rfl

/-- 葉(5) `L_n ∈ RT_PS`（Isabelle `m_8_4_oper_props_2(1)`）。
`L_n = seg (M[n+1]) 0 (Lng (M[n]))` を `RTPS_initial_slice` に通す。 -/
private theorem RTPS_L_o5r (M : PS) (n : ℕ)
    (hST : STPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    RTPS (s84x_L M n) := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hMT hp hj1
  have hSuccST : STPS (oper M (n + 1)) := STPS.oper hST (n + 1) (by omega)
  have hSuccR : RTPS (oper M (n + 1)) := STPS_RTPS _ hSuccST
  have hLng_n := Lng_oper_o5r M n hMT hp hj1
  have hLng_n1 := Lng_oper_o5r M (n + 1) hMT hp hj1
  have hLngL_n : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hlt_succ : Lng (oper M n) < Lng (oper M (n + 1)) := by
    rw [hLng_n, hLng_n1]
    have hexp : (n + 1) * (Lng M - 1 - s84x_jm2 M)
        = n * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) := by ring
    omega
  have hslice := RTPS_initial_slice (oper M (n + 1)) (Lng (oper M n)) hSuccR (by omega)
  have hprefix : seg (oper M (n + 1)) 0 (Lng (oper M n)) = s84x_L M n := by
    rw [seg_eq_take_drop_adm (oper M (n + 1)) 0 (Lng (oper M n)) (Nat.zero_le _) hlt_succ]
    simp only [List.drop_zero, Nat.sub_zero]
    have hsucc := oper_succ_L_o5r M n hlast hnz hp' hidx hjm2lt
    rw [hsucc]
    exact List.take_left' hLngL_n
  rw [hprefix] at hslice
  exact hslice

/-- `M[n]` の末尾切片 = `IncrFirstN kk (Pred N')`（Isabelle `s84c1_Mn_tail`）。 -/
private theorem Mn_tail_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    seg (oper M n) (s84x_ms M n) (Lng (oper M n) - 1)
      = IncrFirstN ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)))
          (Pred (s84x_Np M)) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hM hp hj1
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hms_lt : s84x_ms M n < Lng (oper M n) := by
    rw [hLng_n, hms_eq]
    have := sub_mul_lt_o5r n (Lng M - 1 - s84x_jm2 M) hn (by omega); omega
  rw [seg_to_drop_o5r (oper M n) (s84x_ms M n) hms_lt]
  have hblock : (oper M n).drop (s84x_ms M n)
      = (List.range' (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M)).map
          (fun j => (entry M 0 j
                       + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                     entry M 1 j)) := by
    have h := oper_lastblock_o5r M (n - 1) hM hp hj1
    rw [Nat.sub_add_cancel hn] at h
    rw [hms_eq]; exact h
  rw [hblock, Pred_s84x_Np M hjm2lt]
  have hseg_range : seg M (s84x_jm2 M) (Lng M - 2)
      = (List.range' (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M)).map
          (fun j => (entry M 0 j, entry M 1 j)) := by
    unfold seg
    rw [show Lng M - 2 + 1 - s84x_jm2 M = Lng M - 1 - s84x_jm2 M from by omega]
  rw [hseg_range, IncrFirstN_eq_map, List.map_map]
  apply List.map_congr_left
  intro j _
  rfl

/-! ## 8. 葉(4) `le0`: `le0 (L_n) m* (Lng (L_n) − 1)`（Isabelle `s84c1_le0_L_mstar`） -/

/-- `leR X 0 a b = le0 X a b`（定義展開、`i = 0` 分岐）。 -/
private theorem leRz_o5r (X : PS) (a b : ℕ) : leR X 0 a b = le0 X a b := rfl

private theorem le0_L_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    le0 (s84x_L M n) (s84x_ms M n) (Lng (s84x_L M n) - 1) = true := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hM hp hj1
  have hLngL : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hsplit : n * (Lng M - 1 - s84x_jm2 M)
      = (n - 1) * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) :=
    mult_pred_o5r n (Lng M - 1 - s84x_jm2 M) hn
  have hle0M : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  -- step 1: `le0 N' 0 w`
  have harg : s84x_jm2 M + (Lng M - 1 - s84x_jm2 M) = Lng M - 1 := by omega
  have le0Np : le0 (s84x_Np M) 0 (Lng M - 1 - s84x_jm2 M) = true := by
    have hconv := leR0_seg_adm M (s84x_jm2 M) (Lng M - 1) 0 (Lng M - 1 - s84x_jm2 M)
      (le_of_lt hjm2lt) (by omega) (by simp only [length_seg]; omega)
      (by simp only [length_seg]; omega)
    simp only [leRz_o5r, Nat.add_zero, harg] at hconv
    show le0 (seg M (s84x_jm2 M) (Lng M - 1)) 0 (Lng M - 1 - s84x_jm2 M) = true
    rw [hconv]; exact hle0M
  -- step 2: transport to `L'`（行0 が `N'` と一致）
  have hlenNpLp : Lng (s84x_Np M) = Lng (s84x_Lp M) := by
    simp only [s84x_Np, s84x_Lp, length_seg]; simp; omega
  have hφ : ∀ j, j < Lng (s84x_Np M) →
      entry (s84x_Lp M) 0 j = id (entry (s84x_Np M) 0 j) := by
    intro j _
    rw [Np_snoc_o5r M hjm2lt]
    exact entry0_append_congr_o5r (seg M (s84x_jm2 M) (Lng M - 2))
      (entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))
      (entry M 0 (Lng M - 1), entry M 1 (Lng M - 1)) rfl j
  have le0Lp : le0 (s84x_Lp M) 0 (Lng M - 1 - s84x_jm2 M) = true := by
    rw [le0_row0_o5r (s84x_Np M) (s84x_Lp M) id hlenNpLp strictMono_id hφ
        0 (Lng M - 1 - s84x_jm2 M)]
    exact le0Np
  -- step 3: `IncrFirst` 冪不変性
  have le0IF : le0 (IncrFirstN ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)))
      (s84x_Lp M)) 0 (Lng M - 1 - s84x_jm2 M) = true := by
    have h := congrFun (congrFun (congrFun
        (leR_IncrFirstN ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)))
          (s84x_Lp M)) 0) 0) (Lng M - 1 - s84x_jm2 M)
    have h' : le0 (IncrFirstN ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)))
        (s84x_Lp M)) 0 (Lng M - 1 - s84x_jm2 M) = le0 (s84x_Lp M) 0 (Lng M - 1 - s84x_jm2 M) := by
      simpa [leR] using h
    rw [h']; exact le0Lp
  -- step 4: 末尾切片 = `IncrFirstN kk L'`、`adm_le0_seg` で持ち上げ
  have hmsw : s84x_ms M n + (Lng M - 1 - s84x_jm2 M) = Lng (s84x_L M n) - 1 := by
    rw [hLngL, hLng_n, hms_eq]; omega
  have hconv2 := leR0_seg_adm (s84x_L M n) (s84x_ms M n) (Lng (s84x_L M n) - 1) 0
    (Lng M - 1 - s84x_jm2 M)
    (by rw [hLngL, hLng_n, hms_eq]; omega)
    (by rw [hLngL]; omega)
    (by simp only [length_seg]; rw [hLngL, hLng_n, hms_eq]; omega)
    (by simp only [length_seg]; rw [hLngL, hLng_n, hms_eq]; omega)
  rw [L_tail_o5r M n hM hp hj1 hn] at hconv2
  simp only [leRz_o5r, Nat.add_zero, hmsw] at hconv2
  rw [← hconv2]; exact le0IF

/-! ## 9. 葉(4) `adm`: `adm (L_n) m*`（Isabelle `s84c1_adm_L_mstar`、背理法） -/

private theorem adm_L_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 2 ≤ n) :
    adm (s84x_L M n) (s84x_ms M n) = true := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hM hp hj1
  have hn1 : 1 ≤ n := by omega
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hM hp hj1
  have hLngL : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hsplit : n * (Lng M - 1 - s84x_jm2 M)
      = (n - 1) * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) :=
    mult_pred_o5r n (Lng M - 1 - s84x_jm2 M) hn1
  have hw1 : 1 ≤ (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    have := Nat.mul_le_mul (show 1 ≤ n - 1 by omega) (show 1 ≤ Lng M - 1 - s84x_jm2 M by omega)
    omega
  have hms_lt : s84x_ms M n < Lng (oper M n) := by rw [hLng_n, hms_eq]; omega
  have hms_pos : 1 ≤ s84x_ms M n := by rw [hms_eq]; omega
  have hmsm1_lt : s84x_ms M n - 1 < Lng (oper M n) := by omega
  have hms_le_Ln : s84x_ms M n ≤ Lng (s84x_L M n) := by omega
  -- entries of `M[n]` at `m*` and `m*-1`, transported to `L_n`
  have hom := entry_oper_ms_o5r M n hM hp hj1 hn1
  have hom1 := entry_oper_msm1_o5r M n hM hp hj1 hn
  have hEmsL0 : entry (s84x_L M n) 0 (s84x_ms M n)
      = entry M 0 (s84x_jm2 M)
          + (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) := by
    rw [entry_L_eq_oper_o5r M n 0 (s84x_ms M n) hms_lt]; exact hom.1
  have hEmsL1 : entry (s84x_L M n) 1 (s84x_ms M n) = entry M 1 (s84x_jm2 M) := by
    rw [entry_L_eq_oper_o5r M n 1 (s84x_ms M n) hms_lt]; exact hom.2
  have hEm1L0 : entry (s84x_L M n) 0 (s84x_ms M n - 1)
      = entry M 0 (Lng M - 2)
          + (n - 2) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) := by
    rw [entry_L_eq_oper_o5r M n 0 (s84x_ms M n - 1) hmsm1_lt]; exact hom1.1
  have hEm1L1 : entry (s84x_L M n) 1 (s84x_ms M n - 1) = entry M 1 (Lng M - 2) := by
    rw [entry_L_eq_oper_o5r M n 1 (s84x_ms M n - 1) hmsm1_lt]; exact hom1.2
  -- 背理法の本体: `nextR (L_n) 1 (m*-1) m* = true` から False
  have himp : nextR (s84x_L M n) 1 (s84x_ms M n - 1) (s84x_ms M n) = true → False := by
    intro hedge
    have hn1e : nextrel1 (s84x_L M n) (s84x_ms M n - 1) (s84x_ms M n) = true := by
      simpa [nextR] using hedge
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hn1e
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, he1lt⟩, hle0e⟩, _⟩ := hn1e
    -- 隣接 `le0` を `nextrel0` に潰す
    have hmssucc : s84x_ms M n - 1 + 1 = s84x_ms M n := by omega
    have hle0e' : le0 (s84x_L M n) (s84x_ms M n - 1) (s84x_ms M n - 1 + 1) = true := by
      rw [hmssucc]; exact hle0e
    have hn0e := le0_adjacent (s84x_L M n) (s84x_ms M n - 1) hle0e'
    rw [hmssucc] at hn0e
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn0e
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, he0e⟩, _⟩ := hn0e
    -- ブロック構造から成分を読む
    rw [hEm1L1, hEmsL1] at he1lt
    rw [hEm1L0, hEmsL0] at he0e
    -- `r0lt'`
    have hsplitd : (n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
        = (n - 2) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))
          + (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) := by
      have h := mult_pred_o5r (n - 1) (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) (by omega)
      rw [show n - 1 - 1 = n - 2 from by omega] at h
      exact h
    have r0lt' : entry M 0 (Lng M - 2) < entry M 0 (Lng M - 1) := by omega
    -- `M` 側の親辺 `(1, Lng-2) <^Next (1, Lng-1)`
    have hLngM : 0 < Lng M := by omega
    have n0M : nextrel0 M (Lng M - 2) (Lng M - 1) = true := by
      simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, r0lt'⟩, ?_⟩
      intro j hj
      have hnlt : ¬(Lng M - 2 < j) := by omega
      simp [hnlt]
    have le0M : le0 M (Lng M - 2) (Lng M - 1) = true :=
      nextR0_leR M (Lng M - 2) (Lng M - 1) (by simpa [nextR] using n0M)
    have e1M : entry M 1 (Lng M - 2) < entry M 1 (Lng M - 1) := by
      have hjm2b := (s84c1_jm2_basic M hp).2.1
      omega
    have n1M : nextrel1 M (Lng M - 2) (Lng M - 1) = true := by
      simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, e1M⟩, le0M⟩, ?_⟩
      intro j hj
      by_cases hjeq : j = Lng M - 1
      · subst hjeq; simp
      · have hnlt : ¬(Lng M - 2 < j) := by omega
        simp [hnlt]
    have e2 : nextR M 1 (Lng M - 2) (Lng M - 1) = true := by simpa [nextR] using n1M
    have jm2eq : Lng M - 2 = s84x_jm2 M :=
      nextR1_unique_mr M (Lng M - 2) (s84x_jm2 M) (Lng M - 1) e2 (s84c1_nextR1_jm2 M hp)
    rw [jm2eq] at he1lt
    exact (lt_irrefl _ he1lt)
  -- `adm = !nadm`、両選言が偽
  have hnadm : nadm (s84x_L M n) (s84x_ms M n) = false := by
    unfold nadm
    have h1 : decide (Lng (s84x_L M n) < s84x_ms M n) = false := by
      simp only [decide_eq_false_iff_not]; omega
    have h2 : nextR (s84x_L M n) 1 (s84x_ms M n - 1) (s84x_ms M n) = false := by
      cases h : nextR (s84x_L M n) 1 (s84x_ms M n - 1) (s84x_ms M n) with
      | false => rfl
      | true => exact (himp h).elim
    rw [h1, h2]; simp
  simp only [adm, hnadm, Bool.not_false]

/-! ## 10. 葉(4) 完成: `Marked (L_n) m*`（Isabelle `s84c1_marked_L`） -/

private theorem marked_L_o5r (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 2 ≤ n) :
    Marked (s84x_L M n) (s84x_ms M n) := by
  refine ⟨?_, adm_L_o5r M n hM hp hj1 hn, ?_⟩
  · rw [s84x_L_append_o5r]; simp [TPS]
  · rw [leRz_o5r]; exact le0_L_o5r M n hM hp hj1 (by omega)

/-! ## 11. 末尾切片 `Red` の RT_PS 所属（Isabelle `slice_Red_in_RT_PS`） -/

/-- `Red (seg N m (Lng N − 1)) ∈ RT_PS`（許容祖先切片の簡約は簡約形）。 -/
private theorem RTPS_Red_tail_o5r (N : PS) (m : ℕ)
    (hN : RTPS N) (hmlt : m < Lng N - 1)
    (hle : leR N 0 m (Lng N - 1) = true) :
    RTPS (Red (seg N m (Lng N - 1))) := by
  have hNT : TPS N := RTPS_TPS N hN
  have hmono : monoT (seg N m (Lng N - 1)) = true :=
    mono_ancestor_slice N m (Lng N - 1) hNT hmlt hle
  have hnm : multiT (seg N m (Lng N - 1)) = false := by simp [multiT, hmono]
  have hST : TPS (seg N m (Lng N - 1)) := by
    apply List.ne_nil_of_length_pos; simp only [length_seg]; omega
  exact Red_nonmulti_RTPS (seg N m (Lng N - 1)) hST hnm

/-! ## 12. 葉(8): `Mark (L_n) m* = Trans L'`（Isabelle `s84c1_Mark_L_mstar`） -/

private theorem mark_L_o5r (M : PS) (n : ℕ)
    (hST : STPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 2 ≤ n) :
    Mark (s84x_L M n) (s84x_ms M n) = Trans (s84x_Lp M) := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hMT hp hj1
  have hn1 : 1 ≤ n := by omega
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hMT hp hj1
  have hLngL : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hsplit : n * (Lng M - 1 - s84x_jm2 M)
      = (n - 1) * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) :=
    mult_pred_o5r n (Lng M - 1 - s84x_jm2 M) hn1
  have hmslt : s84x_ms M n < Lng (s84x_L M n) - 1 := by rw [hLngL, hLng_n, hms_eq]; omega
  have hmk : Marked (s84x_L M n) (s84x_ms M n) := marked_L_o5r M n hMT hp hj1 hn
  have hLnRT : RTPS (s84x_L M n) := RTPS_L_o5r M n hST hp hj1 hn1
  have hle_marked : leR (s84x_L M n) 0 (s84x_ms M n) (Lng (s84x_L M n) - 1) = true := hmk.2.2
  have hrepr : Mark (s84x_L M n) (s84x_ms M n)
      = Trans (seg (s84x_L M n) (s84x_ms M n) (Lng (s84x_L M n) - 1)) :=
    Mark_Trans_repr (s84x_L M n) (s84x_ms M n) hmk hLnRT hmslt
  have htail := L_tail_o5r M n hMT hp hj1 hn1
  have LpT : TPS (s84x_Lp M) := by unfold s84x_Lp; simp [TPS]
  have RedLp0 := RTPS_Red_tail_o5r (s84x_L M n) (s84x_ms M n) hLnRT hmslt hle_marked
  rw [htail, a1_Red_funpow_IncrFirst (s84x_Lp M)
      ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))) LpT] at RedLp0
  rw [hrepr, htail, Trans_funpow_IncrFirst (s84x_Lp M)
      ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))) LpT RedLp0]

/-! ## 13. 葉(9): 内部レジーム `Marked (M[n]) m*` かつ `Mark (M[n]) m* = Trans (Pred N')`
    （Isabelle `s84c1_Mark_Mn_mstar`） -/

private theorem interior_o5r (M : PS) (n : ℕ)
    (hST : STPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 2 ≤ n)
    (hint : s84x_jm2 M + 1 < Lng M - 1) :
    Marked (oper M n) (s84x_ms M n)
    ∧ Mark (oper M n) (s84x_ms M n) = Trans (Pred (s84x_Np M)) := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_o5r M hMT hp hj1
  have hn1 : 1 ≤ n := by omega
  have hLng_n : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_o5r M n hMT hp hj1
  have hLngL : Lng (s84x_L M n) = Lng (oper M n) + 1 := by rw [s84x_L_append_o5r]; simp
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hsplit : n * (Lng M - 1 - s84x_jm2 M)
      = (n - 1) * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) :=
    mult_pred_o5r n (Lng M - 1 - s84x_jm2 M) hn1
  have hnwpos : 1 ≤ n * (Lng M - 1 - s84x_jm2 M) := by
    have := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ Lng M - 1 - s84x_jm2 M by omega)
    omega
  have hLnoperpos : 1 ≤ Lng (oper M n) := by rw [hLng_n]; omega
  have hmsltL : s84x_ms M n < Lng (s84x_L M n) - 1 := by rw [hLngL, hLng_n, hms_eq]; omega
  have hmkL : Marked (s84x_L M n) (s84x_ms M n) := marked_L_o5r M n hMT hp hj1 hn
  have hLnT : TPS (s84x_L M n) := hmkL.1
  have hLngLn1 : 1 < Lng (s84x_L M n) := by rw [hLngL]; omega
  have hmkPred : Marked (Pred (s84x_L M n)) (s84x_ms M n) :=
    Marked_Pred (s84x_L M n) (s84x_ms M n) hLnT hLngLn1 hmkL hmsltL
  have hPredL : Pred (s84x_L M n) = oper M n := by
    rw [Pred, if_neg (by omega), s84x_L_append_o5r]; simp
  have hmkMn : Marked (oper M n) (s84x_ms M n) := by rw [← hPredL]; exact hmkPred
  refine ⟨hmkMn, ?_⟩
  -- Mark 部
  have hMnRT : RTPS (oper M n) := STPS_RTPS _ (STPS.oper hST n hn1)
  have hmsltMn : s84x_ms M n < Lng (oper M n) - 1 := by rw [hLng_n, hms_eq]; omega
  have hle_marked : leR (oper M n) 0 (s84x_ms M n) (Lng (oper M n) - 1) = true := hmkMn.2.2
  have hrepr : Mark (oper M n) (s84x_ms M n)
      = Trans (seg (oper M n) (s84x_ms M n) (Lng (oper M n) - 1)) :=
    Mark_Trans_repr (oper M n) (s84x_ms M n) hmkMn hMnRT hmsltMn
  have htail := Mn_tail_o5r M n hMT hp hj1 hn1
  have PnT : TPS (Pred (s84x_Np M)) := by
    rw [Pred_s84x_Np M hjm2lt]; apply List.ne_nil_of_length_pos
    simp only [length_seg]; omega
  have RedPn0 := RTPS_Red_tail_o5r (oper M n) (s84x_ms M n) hMnRT hmsltMn hle_marked
  rw [htail, a1_Red_funpow_IncrFirst (Pred (s84x_Np M))
      ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))) PnT] at RedPn0
  rw [hrepr, htail, Trans_funpow_IncrFirst (Pred (s84x_Np M))
      ((n - 1) * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M))) PnT RedPn0]

/-! ## 14. 残差 `Oper5Residual` の discharge、および無条件 `Oper5Support` -/

/-- Isabelle `s84c1_marked_L`/`s84c1_Mark_L_mstar`/`s84c1_Mark_Mn_mstar` の合流。
`8.4-oper5-support` が緑モジュロ入力としていた束 `Oper5Residual` を無仮定で閉じる。 -/
theorem oper5Residual_holds (M : PS) (n : ℕ)
    (hST : STPS M) (_hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 < n) :
    Oper5Residual M n := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  have hn2 : 2 ≤ n := hn
  refine ⟨marked_L_o5r M n hMT hp hj1 hn2, mark_L_o5r M n hST hp hj1 hn2, ?_⟩
  intro hint
  exact interior_o5r M n hST hp hj1 hn2 hint

/-- 残差を discharge した結果、`Oper5Support` は `oper5Support_holds` と合成して
`STPS`/`monoT`/`hasParent`/`1 < Lng M − 1`/`1 < n` の下で無条件に成立する。 -/
theorem oper5Support_unconditional (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 < n) :
    Oper5Support M n :=
  oper5Support_holds M n hST hmono hp hj1 hn (oper5Residual_holds M n hST hmono hp hj1 hn)

/-- 残差が閉じたので、§8.4 命題 part (5)（Isabelle `m_8_4_oper_props_5`）は
green-modulo 入力なしに、`STPS`/`monoT`/`hasParent`/`1 < Lng M − 1`/`1 < n` のみで成立する。 -/
theorem oper_props_5_unconditional (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 < n) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_L M (n - 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2
        ∧ scb_decomp (Trans (s84x_L M n)) sb.1 (flatBT (Trans (s84x_Lp M))) sb.2
        ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
             scb_decomp (Trans (oper M n)) sb.1
               (flatBT (Trans (Pred (s84x_Np M)))) sb.2) :=
  m_8_4_oper_props_5 M n hST hmono hp hj1 hn
    (oper5Support_unconditional M n hST hmono hp hj1 hn)

/-! ## 15. ExchV 底段で再利用する公開幾何補題 -/

/-- `s84x_L` の定義展開。底段 `n = 1` の列形を読む公開入口。 -/
theorem s84x_L_eq_append (M : PS) (n : ℕ) :
    s84x_L M n = oper M n ++
      [(entry M 0 (s84x_jm2 M)
          + n * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
        entry M 1 (s84x_jm2 M))] :=
  s84x_L_append_o5r M n

/-- `s84x_L M n` は `n ≥ 1` なら簡約ペア数列。 -/
theorem RTPS_s84x_L (M : PS) (n : ℕ)
    (hST : STPS M) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    RTPS (s84x_L M n) :=
  RTPS_L_o5r M n hST hp hj1 hn

/-- 長さと行0が狭義単調な写像で対応する列では `nextrel0` が一致する。 -/
theorem nextrel0_row0_congr (X Y : PS) (φ : ℕ → ℕ)
    (hlen : Lng X = Lng Y) (hmono : StrictMono φ)
    (hφ : ∀ j, j < Lng X → entry Y 0 j = φ (entry X 0 j))
    (a b : ℕ) : nextrel0 Y a b = nextrel0 X a b :=
  nextrel0_row0_o5r X Y φ hlen hmono hφ a b

/-- 長さと行0が狭義単調な写像で対応する列では `le0` が一致する。 -/
theorem le0_row0_congr (X Y : PS) (φ : ℕ → ℕ)
    (hlen : Lng X = Lng Y) (hmono : StrictMono φ)
    (hφ : ∀ j, j < Lng X → entry Y 0 j = φ (entry X 0 j))
    (a b : ℕ) : le0 Y a b = le0 X a b :=
  le0_row0_o5r X Y φ hlen hmono hφ a b

/-- 終端までの `seg` は `drop`。 -/
theorem seg_to_last_eq_drop (X : PS) (a : ℕ) (ha : a < Lng X) :
    seg X a (Lng X - 1) = X.drop a :=
  seg_to_drop_o5r X a ha

#print axioms oper5Residual_holds
#print axioms oper5Support_unconditional
#print axioms oper_props_5_unconditional
#print axioms Pred_s84x_Np
#print axioms RTPS_s84x_L
#print axioms nextrel0_row0_congr
#print axioms le0_row0_congr
#print axioms seg_to_last_eq_drop

end PSS
