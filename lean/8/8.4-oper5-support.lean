import «8».«8.4-oper-props5»
import «8».«8.7-const00-Trans»
import «6».«6.6-reduced-fseq»
import «6».«6.6-reduced-slice»

/-!
# §8.4 `oper` 基本性質 (5) の支持束 `Oper5Support` の discharge

- 原文: `tmp/content.md` 4389（命題「条件(III)〜(VI)の下での展開規則の基本性質」
  parts (5-1)/(5-2)/(5-3)）。§8.4 の scb 分解クラスタは `pss_paper.thy` 上
  DEFERRED（`8.4-scb-decompositions`）。
- Isabelle（設計図）: `s84c1_*` クラスタ（`isabelle/layerB/pss_wip.thy`:52660–54005、
  ~1350 行）。`Oper5Support` の 10 葉の対応:
  * 葉(1) `s84x_jm2 M < Lng M − 1` ← `s84c1_jm2_basic(1)` (:52675)。
  * 葉(2) `Lng (M[n]) = ?ms + ?w` ← `s84c1_Lng_oper` (:52865) ＋ `s84c1_mult_pred` (:53393)。
  * 葉(3) `Lng (L_n) = Lng (M[n]) + 1` ← `s84c1_Lng_L` (:52921)。
  * 葉(4) `(L_n, ?ms) ∈ Marked` ← `s84c1_marked_L` (:53860)。
  * 葉(5) `L_n ∈ RT_PS` ← `m_8_4_oper_props_2(1)` (:52946)。
  * 葉(6) `seg (L_n) 0 ?ms = L_{n−1}` ← `s84c1_L_prefix(2)` (:53549)。
  * 葉(7) `entry (L_n) 1 ?ms = M_{1,j₋₂}` ← `s84c1_Mn_entry_mstar` (:53597) ＋ 末尾列外し。
  * 葉(8) `Mark (L_n) ?ms = Trans (L')` ← `s84c1_Mark_L_mstar` (:53883)。
  * 葉(9) 内部レジーム ← `s84c1_Mark_Mn_mstar` (:53932)/`s84c1_L_prefix(1)`/block-read。
  * 葉(10) 境界レジーム ← `s84c1_oper_Suc_eq_L_app` (:52886)/`s84c1_Pred_Np` (:53440)/
    `Red_singleton`/`Trans_singleton`。

## 移植状態（house green-modulo）

無条件に閉じた葉: (1)(2)(3)(5)(6)(7)(10)。核となるタイル恒等式
`oper M (m+1) = L_m ++ tail`（Isabelle `s84c1_oper_Suc_eq_L_app`）を `oper_tiling_expand`
（§6.6）から証明し、そこから `L_take`/`L_prefix`/境界レジームを導いた。RT_PS 閉性は
`RTPS_initial_slice`（§6.6）＋ take 恒等式。ブロック読み出しは `entry_oper_tiling_block_*`
（§6.6）。境界の `Trans (Pred N') = D_{M_1,j₋₂} 0` は `Red_singleton`/`Trans_singleton`/`Trans_Red`。

残差 `Oper5Residual`（Mark/Marked/adm クラスタ、§7.4 依存）: 葉(4) `Marked L`、葉(8) `Mark L`、
葉(9) の内部レジーム Mark/Marked。Isabelle `s84c1_adm_L_mstar`/`s84c1_le0_L_mstar`/
`s84c1_Mark_L_mstar`/`s84c1_Mark_Mn_mstar`（`m_7_4_Mark_Trans_repr` ＋ `Trans_funpow_IncrFirst`
＋ `slice_Red_in_RT_PS` に依存、~400 行）に対応。

- 依存（すべてビルド済み）: «8».«8.4-oper-props5»（`Oper5Support`/`s84x_L`/`s84x_Lp`/
  `s84x_w`/`s84x_ms`/`m_8_4_oper_props_5`）、«6».«6.6-reduced-fseq»（`oper_tiling_expand`/
  `length_oper_tiling`/`entry_oper_tiling_block_one`/`entry_oper_tiling_prefix`）、
  «6».«6.6-reduced-slice»（`RTPS_initial_slice`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private helper suffix: `_o5s`。
-/

namespace PSS

/-! ## 0. 算術補助（Isabelle `s84c1_mult_pred` 相当） -/

/-- Isabelle `s84c1_mult_pred` (wip:53393): `n·w = (n−1)·w + w`（`n ≥ 1`）。 -/
private theorem mult_pred_o5s (n w : ℕ) (hn : 1 ≤ n) : n * w = (n - 1) * w + w := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Nat.succ_mul]

/-- `(n−1)·w < n·w`（`n ≥ 1`, `w > 0`）。 -/
private theorem sub_mul_lt_o5s (n w : ℕ) (hn : 1 ≤ n) (hw : 0 < w) :
    (n - 1) * w < n * w := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.succ_mul]
  omega

/-! ## 1. 残差 Prop（§7.4 依存の Mark/Marked 葉） -/

/-- `Oper5Support` のうち §7.4 Mark/Trans 表示に依存する葉の束。
Isabelle `s84c1_marked_L`/`s84c1_Mark_L_mstar`/`s84c1_Mark_Mn_mstar`。 -/
def Oper5Residual (M : PS) (n : ℕ) : Prop :=
  -- 葉(4) `s84c1_marked_L`。
  Marked (s84x_L M n) (s84x_ms M n)
  -- 葉(8) `s84c1_Mark_L_mstar`。
  ∧ Mark (s84x_L M n) (s84x_ms M n) = Trans (s84x_Lp M)
  -- 葉(9) 内部レジームの Mark/Marked（`s84c1_Mark_Mn_mstar`）。
  ∧ (s84x_jm2 M + 1 < Lng M - 1 →
        Marked (oper M n) (s84x_ms M n)
      ∧ Mark (oper M n) (s84x_ms M n) = Trans (Pred (s84x_Np M)))

/-! ## 2. 共有下ごしらえ・タイル恒等式 -/

/-- `s84x_L M m = oper M m ++ [末尾列]`（定義展開）。 -/
private theorem s84x_L_append_o5s (M : PS) (m : ℕ) :
    s84x_L M m = oper M m ++
      [(entry M 0 (s84x_jm2 M)
          + m * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
        entry M 1 (s84x_jm2 M))] := rfl

/-- `entry (L_m) i j = entry (M[m]) i j`（末尾列より左の添字）。 -/
private theorem entry_L_eq_oper_o5s (M : PS) (m i j : ℕ) (hj : j < Lng (oper M m)) :
    entry (s84x_L M m) i j = entry (oper M m) i j := by
  rw [s84x_L_append_o5s]
  unfold entry
  rw [List.getElem?_append_left hj]

/-- `range'` の先頭剥がし（`n > 0`）。 -/
private theorem range'_eq_cons_o5s (s n : ℕ) (hn : 0 < n) :
    List.range' s n = s :: List.range' (s + 1) (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-- Isabelle `s84c1_oper_Suc_eq_L_app` (wip:52886): 基本列の一段展開
`M[m+1] = M[m] ++ ブロック m`（タイル恒等式、`oper_tiling_expand` から）。 -/
private theorem oper_succ_append_o5s (M : PS) (m : ℕ)
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

/-- `M[m+1] = L_m ++ 残り`（`idx1 = 1` に特殊化した L-append 形）。
Isabelle `s84c1_oper_Suc_eq_L_app` (wip:52886) の `s84x_L` 形。 -/
private theorem oper_succ_L_o5s (M : PS) (m : ℕ)
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
  have happ := oper_succ_append_o5s M m hlast hnz hp'
  simp only [hd0, hd1, Nat.mul_zero, Nat.add_zero] at happ
  simp only [hj0] at happ
  rw [happ, range'_eq_cons_o5s (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M) (by omega),
    List.map_cons, s84x_L_append_o5s]
  rw [List.append_assoc]
  rfl

/-- `Lng (M[k]) = j₋₂ + k·w`（Isabelle `s84c1_Lng_oper` (wip:52865)、`w = Lng M − 1 − j₋₂`）。 -/
private theorem Lng_oper_o5s (M : PS) (k : ℕ)
    (hlast : 1 < Lng M)
    (hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hidx : idx1 M (Lng M - 1) = 1) :
    Lng (oper M k) = s84x_jm2 M + k * (Lng M - 1 - s84x_jm2 M) := by
  have h : Lng (oper M k)
      = parent M (idx1 M (Lng M - 1)) (Lng M - 1)
          + k * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :=
    length_oper_tiling M k hlast hnz hp'
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  rw [hj0] at h; exact h

/-- `Lng (L_k) = Lng (M[k]) + 1`（Isabelle `s84c1_Lng_L` (wip:52921)）。 -/
private theorem Lng_L_o5s (M : PS) (k : ℕ) :
    Lng (s84x_L M k) = Lng (oper M k) + 1 := by
  rw [s84x_L_append_o5s]; simp

/-! ## 3. 主定理 -/

/-- Isabelle `s84c1_*` クラスタ（`m_8_4_oper_props_5` の入力 `Oper5Support`）の discharge。
無条件に閉じた葉: (1)(2)(3)(5)(6)(7)(10)。残差 `Oper5Residual`（葉 (4)(8)(9) の
Mark/Marked、§7.4 依存）は green-modulo 入力。 -/
theorem oper5Support_holds (M : PS) (n : ℕ)
    (hST : STPS M) (_hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 < n)
    (hres : Oper5Residual M n) :
    Oper5Support M n := by
  obtain ⟨hres4, hres8, hres9⟩ := hres
  -- 共有下ごしらえ
  have hjm2b := s84c1_jm2_basic M hp
  have hjm2lt : s84x_jm2 M < Lng M - 1 := hjm2b.1
  have he1 : 0 < entry M 1 (Lng M - 1) := by have := hjm2b.2.1; omega
  have hidx : idx1 M (Lng M - 1) = 1 := by unfold idx1; rw [if_pos he1]
  have hlast : 1 < Lng M := by omega
  have hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hidx]; exact hp
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  have hwpos : 0 < Lng M - 1 - s84x_jm2 M := by omega
  have hms_eq : s84x_ms M n = s84x_jm2 M + (n - 1) * (Lng M - 1 - s84x_jm2 M) := by
    simp only [s84x_ms, s84x_w]
  have hnm1 : (n - 1) + 1 = n := by omega
  have hLng_n := Lng_oper_o5s M n hlast hnz hp' hidx
  have hLngL_n := Lng_L_o5s M n
  have hms_lt : s84x_ms M n < Lng (oper M n) := by
    rw [hLng_n, hms_eq]
    have := sub_mul_lt_o5s n (Lng M - 1 - s84x_jm2 M) (by omega) hwpos
    omega
  have hms_lt_L : s84x_ms M n < Lng (s84x_L M n) := by rw [hLngL_n]; omega
  -- ブロック読み出し: `entry (M[n]) 1 m* = M_{1,j₋₂}`（Isabelle `s84c1_Mn_entry_mstar`）
  have hentry_oper : entry (oper M n) 1 (s84x_ms M n) = entry M 1 (s84x_jm2 M) := by
    have hq : n - 1 < n := by omega
    have hs0 : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
      rw [hj0]; omega
    have hread := entry_oper_tiling_block_one M n (n - 1) 0 hlast hnz hp' hq hs0
    rw [hj0] at hread
    simp only [Nat.add_zero] at hread
    rw [hms_eq]; exact hread
  -- 始切片: `seg (M[n]) 0 m* = L_{n−1}`（Isabelle `s84c1_L_prefix(1)`）
  have hseg_oper : seg (oper M n) 0 (s84x_ms M n) = s84x_L M (n - 1) := by
    have hsucc' := oper_succ_L_o5s M (n - 1) hlast hnz hp' hidx hjm2lt
    rw [hnm1] at hsucc'
    have hLng_nm1 := Lng_oper_o5s M (n - 1) hlast hnz hp' hidx
    have hLngL_nm1 := Lng_L_o5s M (n - 1)
    have hmseq : (s84x_L M (n - 1)).length = s84x_ms M n + 1 := by
      show Lng (s84x_L M (n - 1)) = s84x_ms M n + 1
      rw [hLngL_nm1, hLng_nm1, hms_eq]
    rw [seg_eq_take_drop_adm (oper M n) 0 (s84x_ms M n) (Nat.zero_le _) hms_lt]
    simp only [List.drop_zero, Nat.sub_zero]
    rw [hsucc']
    exact List.take_left' hmseq
  -- 主連言
  refine ⟨hjm2lt, ?_, hLngL_n, hres4, ?_, ?_, ?_, hres8, ?_, ?_⟩
  · -- 葉(2): `Lng (M[n]) = m* + w`
    have hw : s84x_w M = Lng M - 1 - s84x_jm2 M := rfl
    rw [hLng_n, hms_eq, hw]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  · -- 葉(5): `L_n ∈ RT_PS`
    have hSuccST : STPS (oper M (n + 1)) := STPS.oper hST (n + 1) (by omega)
    have hSuccR : RTPS (oper M (n + 1)) := STPS_RTPS _ hSuccST
    have hLng_n1 := Lng_oper_o5s M (n + 1) hlast hnz hp' hidx
    have hlt_succ : Lng (oper M n) < Lng (oper M (n + 1)) := by
      rw [hLng_n, hLng_n1]
      have hexp : (n + 1) * (Lng M - 1 - s84x_jm2 M)
          = n * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) := by ring
      omega
    have hslice := RTPS_initial_slice (oper M (n + 1)) (Lng (oper M n)) hSuccR (by omega)
    have hprefix : seg (oper M (n + 1)) 0 (Lng (oper M n)) = s84x_L M n := by
      rw [seg_eq_take_drop_adm (oper M (n + 1)) 0 (Lng (oper M n)) (Nat.zero_le _) hlt_succ]
      simp only [List.drop_zero, Nat.sub_zero]
      have hsucc := oper_succ_L_o5s M n hlast hnz hp' hidx hjm2lt
      rw [hsucc]
      have hlen : (s84x_L M n).length = Lng (oper M n) + 1 := hLngL_n
      exact List.take_left' hlen
    rw [hprefix] at hslice
    exact hslice
  · -- 葉(6): `seg (L_n) 0 m* = L_{n−1}`
    have hL_seg : seg (s84x_L M n) 0 (s84x_ms M n) = seg (oper M n) 0 (s84x_ms M n) := by
      rw [seg_eq_take_drop_adm (s84x_L M n) 0 (s84x_ms M n) (Nat.zero_le _) hms_lt_L,
          seg_eq_take_drop_adm (oper M n) 0 (s84x_ms M n) (Nat.zero_le _) hms_lt]
      simp only [List.drop_zero, Nat.sub_zero]
      rw [s84x_L_append_o5s M n, List.take_append_of_le_length hms_lt]
    rw [hL_seg]; exact hseg_oper
  · -- 葉(7): `entry (L_n) 1 m* = M_{1,j₋₂}`
    rw [entry_L_eq_oper_o5s M n 1 (s84x_ms M n) hms_lt]; exact hentry_oper
  · -- 葉(9): 内部レジーム
    intro hint
    exact ⟨(hres9 hint).1, (hres9 hint).2, hseg_oper, hentry_oper⟩
  · -- 葉(10): 境界レジーム
    intro hbound
    have hbdeq : s84x_jm2 M + 1 = Lng M - 1 := by omega
    refine ⟨?_, ?_⟩
    · -- `M[n] = L_{n−1}`
      have hw1 : Lng M - 1 - s84x_jm2 M - 1 = 0 := by omega
      have hsucc' := oper_succ_L_o5s M (n - 1) hlast hnz hp' hidx hjm2lt
      rw [hnm1, hw1] at hsucc'
      simp only [List.range'_zero, List.map_nil, List.append_nil] at hsucc'
      exact hsucc'
    · -- `Trans (Pred N') = D_{M_{1,j₋₂}} 0`
      intro hgz
      have hlen2 : Lng M - 1 + 1 - s84x_jm2 M = 2 := by omega
      have hPredNp : Pred (s84x_Np M)
          = [(entry M 0 (s84x_jm2 M), entry M 1 (s84x_jm2 M))] := by
        have hrange : List.range' (s84x_jm2 M) (Lng M - 1 + 1 - s84x_jm2 M)
            = [s84x_jm2 M, s84x_jm2 M + 1] := by rw [hlen2]; rfl
        unfold s84x_Np seg
        rw [hrange]
        simp only [List.map_cons, List.map_nil]
        unfold Pred
        simp
      have he1pos : 0 < entry M 1 (s84x_jm2 M) := by
        rw [hPredNp] at hgz
        by_contra hle
        have hb0 : entry M 1 (s84x_jm2 M) = 0 := by omega
        rw [hb0] at hgz
        exact hgz (by simp [zeroT, entry])
      have hPredT : TPS (Pred (s84x_Np M)) := by rw [hPredNp]; simp [TPS]
      have hRed : Red (Pred (s84x_Np M))
          = [(entry M 1 (s84x_jm2 M), entry M 1 (s84x_jm2 M))] := by
        rw [hPredNp]; exact Red_singleton _ _
      have hsing : Trans [(entry M 1 (s84x_jm2 M), entry M 1 (s84x_jm2 M))]
          = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero := by
        have h := const00_Trans (entry M 1 (s84x_jm2 M)) 0
        rw [if_neg (by omega : entry M 1 (s84x_jm2 M) ≠ 0)] at h
        rw [show (List.replicate 1 (entry M 1 (s84x_jm2 M), entry M 1 (s84x_jm2 M)))
              = [(entry M 1 (s84x_jm2 M), entry M 1 (s84x_jm2 M))] from rfl] at h
        rw [h]; simp [multBT, addBT, BZero, Dprin]
      rw [Trans_Red (Pred (s84x_Np M)) hPredT, hRed, hsing]

#print axioms oper5Support_holds

end PSS
