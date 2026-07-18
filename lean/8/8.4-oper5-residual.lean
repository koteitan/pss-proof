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
private theorem Pred_Np_o5r (M : PS) (hjm2lt : s84x_jm2 M < Lng M - 1) :
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

end PSS
