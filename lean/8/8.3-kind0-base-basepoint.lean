import «6».«6.6-reduced-fseq»
import «6».«6.2-P-fseq»
import «6».«6.5-Red-le-core»
import «6».«6.6-reduced-leftend»
import «6».«6.3-admof-slice»
import «5».«5.1-parent-exists»
import «5».«5.1-ancestor-basic»
import «7».«7.4-Adm-nextAdm»
import PSS.Adm

/-!
# §8.3 補題（第 `0` 種型基本列の基本基点関係）

- 原文: `tmp/content.md` 3998 付近
- 訂正: なし
- Isabelle: `p_8_3_kind0_base_basepoint` (isabelle/pss_paper.thy:1832) の証明は
             `m_8_3_kind0_base_basepoint` (isabelle/layerB/pss_wip.thy:17284)
- 依存: `6.6-reduced-fseq`（タイル読み出し・`RTPS_oper`・`oper_tiling_strict_floor`）、
  `5.1-parent-exists`（`parent_exists_3` = 値特徴付けからの `le0` 構築）、
  `5.1-ancestor-basic`（`ancestor_basic_1` = 逆向き）、`7.4-Adm-nextAdm`
  （`adm_row1_ancestry`/`row1_implies_row0`）、`6.3-admof-slice`（`Adm_le`/`Adm_adm`）
- 状態: ✅ 証明済（sorry 0）

(1) `n>1` なら最終ブロック開始 `j₀+(n-1)w` が `M[n]` の基点。許容性=ブロック開始は
行 0 最小なので直前からの隣接辺が立たない。到達性=最終ブロック内で右端まで。
(2) `j₀` 非許容なら `Adm_M(j₀)` が基点。許容性=接頭辞転送、到達性=`M` の祖先鎖の
値特徴付けを `M[n]` に写す。**`le0` の持ち上げ/転送はすべて
`ancestor_basic_1`（le0→値）＋ entry 一致 ＋ `parent_exists_3`（値→le0）で構成**し、
燃料付き `le0Aux` の帰納を一切使わない（Isabelle 版の rtrancl 操作の置き換え）。
-/

namespace PSS

/-! ## 補助（`le0` の反射律・添字単調性） -/

private theorem le0Aux_refl_bb (M : PS) (fuel j : ℕ) : le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_bb (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_bb]

private theorem le0_index_mono_bb (M : PS) (a b : ℕ)
    (h : le0 M a b = true) : a ≤ b := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_index_fseq h.2

/-! ## 補助（接頭辞 `[0, j₀]` の entry 一致） -/

private theorem entry_pref0_bb (M : PS) (n x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hx : x ≤ parent M 0 (Lng M - 1)) :
    entry (oper M n) 0 x = entry M 0 x := by
  rcases Nat.lt_or_eq_of_le hx with h | h
  · exact entry_oper_tiling_prefix M n 0 x hlast hzero hp (by rw [hi]; exact h)
  · subst h
    have hh := entry_oper_tiling_block_zero M n 0 0 hlast hzero hp hn
      (by rw [hi]; omega)
    rw [hi] at hh
    simpa using hh

private theorem entry_pref1_bb (M : PS) (n x : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hx : x ≤ parent M 0 (Lng M - 1)) :
    entry (oper M n) 1 x = entry M 1 x := by
  rcases Nat.lt_or_eq_of_le hx with h | h
  · exact entry_oper_tiling_prefix M n 1 x hlast hzero hp (by rw [hi]; exact h)
  · subst h
    have hh := entry_oper_tiling_block_one M n 0 0 hlast hzero hp hn
      (by rw [hi]; omega)
    rw [hi] at hh
    simpa using hh

/-! ## 補助（接頭辞領域の `le0` 転送: 値特徴付け経由） -/

private theorem le0_pref_lift_bb (M : PS) (n x y : ℕ)
    (hMT : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hy : y ≤ parent M 0 (Lng M - 1))
    (h : leR M 0 x y = true) :
    leR (oper M n) 0 x y = true := by
  have hoperT : TPS (oper M n) := oper_TPS M n hMT hn
  have hlen : Lng (oper M n) = parent M 0 (Lng M - 1)
      + n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    simpa [hi] using length_oper_tiling M n hlast hzero hp
  have hw : 0 < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hnw : 0 < n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := Nat.mul_pos hn hw
  have hxy : x ≤ y := le0_index_mono_bb M x y (by simpa [leR] using h)
  rcases Nat.eq_or_lt_of_le hxy with heq | hlt
  · subst heq
    exact leR0_refl_bb (oper M n) x (by omega)
  · apply parent_exists_3 (oper M n) x y hoperT hlt (by omega)
    intro k hxk hky
    have hk₀ : k ≤ parent M 0 (Lng M - 1) := hky.trans hy
    have hbase : entry M 0 x < entry M 0 k :=
      ancestor_basic_1 M x k y hMT hxk hky h
    rw [entry_pref0_bb M n x hlast hzero hp hi hn hj₀lt (hxy.trans hy),
      entry_pref0_bb M n k hlast hzero hp hi hn hj₀lt hk₀]
    exact hbase

private theorem le0_pref_back_bb (M : PS) (n x y : ℕ)
    (hMT : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hy : y ≤ parent M 0 (Lng M - 1))
    (h : leR (oper M n) 0 x y = true) :
    leR M 0 x y = true := by
  have hoperT : TPS (oper M n) := oper_TPS M n hMT hn
  have hyM : y < Lng M := by omega
  have hxy : x ≤ y := le0_index_mono_bb (oper M n) x y (by simpa [leR] using h)
  rcases Nat.eq_or_lt_of_le hxy with heq | hlt
  · subst heq
    exact leR0_refl_bb M x hyM
  · apply parent_exists_3 M x y hMT hlt hyM
    intro k hxk hky
    have hk₀ : k ≤ parent M 0 (Lng M - 1) := hky.trans hy
    have hbase : entry (oper M n) 0 x < entry (oper M n) 0 k :=
      ancestor_basic_1 (oper M n) x k y hoperT hxk hky h
    rw [entry_pref0_bb M n x hlast hzero hp hi hn hj₀lt (hxy.trans hy),
      entry_pref0_bb M n k hlast hzero hp hi hn hj₀lt hk₀] at hbase
    exact hbase

/-! ## 補助（接頭辞領域の行 1 親子辺の逆転送 `M[n] → M`） -/

private theorem nextrel1_prefix_back_bb (M : PS) (n x y : ℕ)
    (hMT : TPS M)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hn : 0 < n)
    (hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1)
    (hy : y ≤ parent M 0 (Lng M - 1))
    (h : nextrel1 (oper M n) x y = true) :
    nextrel1 M x y = true := by
  have hoperT : TPS (oper M n) := oper_TPS M n hMT hn
  have hyM : y < Lng M := by omega
  have hh := h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hxy : x < y := hh.1.1.1.2
  have he1op : entry (oper M n) 1 x < entry (oper M n) 1 y := hh.1.1.2
  have hle0op : le0 (oper M n) x y = true := hh.1.2
  have hvalley := hh.2
  have hxle : x ≤ parent M 0 (Lng M - 1) := (Nat.le_of_lt hxy).trans hy
  have hle0M : leR M 0 x y = true :=
    le0_pref_back_bb M n x y hMT hlast hzero hp hi hn hj₀lt hy
      (by simpa [leR] using hle0op)
  have hex1 := entry_pref1_bb M n x hlast hzero hp hi hn hj₀lt hxle
  have hey1 := entry_pref1_bb M n y hlast hzero hp hi hn hj₀lt hy
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by omega, hyM⟩, hxy⟩, ?_⟩, by simpa [leR] using hle0M⟩, ?_⟩
  · rw [← hex1, ← hey1]; exact he1op
  · rw [List.all_eq_true]
    intro j hjmem
    by_cases hcase : x < j ∧ le0 M j y = true
    · have hjy : j ≤ y := le0_index_mono_bb M j y hcase.2
      have hj₀ : j ≤ parent M 0 (Lng M - 1) := hjy.trans hy
      have hliftR : leR (oper M n) 0 j y = true :=
        le0_pref_lift_bb M n j y hMT hlast hzero hp hi hn hj₀lt hy
          (by simpa [leR] using hcase.2)
      have hlift : le0 (oper M n) j y = true := by simpa [leR] using hliftR
      have hjopL : j < Lng (oper M n) := by
        have hh' := hlift
        simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh'
        exact hh'.1.1
      have hv := List.all_eq_true.mp hvalley j (List.mem_range.mpr hjopL)
      simp only [hlift, hcase.1, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at hv
      have hj1 := entry_pref1_bb M n j hlast hzero hp hi hn hj₀lt hj₀
      rw [hey1, hj1] at hv
      simp [hv]
    · rcases not_and_or.mp hcase with h' | h'
      · simp [h']
      · have h'' : le0 M j y = false := by
          revert h'; simp
        simp [h'']

/-- 補題（第 `0` 種型基本列の基本基点関係）。
(1) `n>1` なら最終ブロック開始が `M[n]` の基点、(2) `j₀` 非許容なら `Adm_M(j₀)` が基点。 -/
theorem kind0_base_basepoint (M : PS) (n : ℕ)
    (hMR : RTPS M) (hn : 0 < n)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (he1 : entry M 1 (Lng M - 1) = 0) :
    (1 < n →
      Marked (oper M n)
        (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        ∧ RTPS (oper M n))
    ∧ (adm M (parent M 0 (Lng M - 1)) = false →
      Marked (oper M n) (Adm M (parent M 0 (Lng M - 1))) ∧ RTPS (oper M n)) := by
  have hMT : TPS M := RTPS_TPS M hMR
  have hi : idx1 M (Lng M - 1) = 0 := by simp [idx1, he1]
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    rw [hi]; exact hp0
  have hnext0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hasParent_next_fseq M 0 (Lng M - 1) hp0
  have hdec := hnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hdec
  have hj₀lt : parent M 0 (Lng M - 1) < Lng M - 1 := hdec.1.1.2
  have he0j₀ : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := hdec.1.2
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by omega
  have hw : 0 < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  have hoperT : TPS (oper M n) := oper_TPS M n hMT hn
  have hMnRT : RTPS (oper M n) := RTPS_oper M n hMR hn
  have hlen : Lng (oper M n) = parent M 0 (Lng M - 1)
      + n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    simpa [hi] using length_oper_tiling M n hlast hzero hp
  have hnw : 0 < n * ((Lng M - 1) - parent M 0 (Lng M - 1)) := Nat.mul_pos hn hw
  have hrel : n * ((Lng M - 1) - parent M 0 (Lng M - 1))
      = (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
        + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.succ_mul]
  -- ブロック床（行 0）
  have hgemin : ∀ x, parent M 0 (Lng M - 1) ≤ x → x < Lng (oper M n) →
      entry M 0 (parent M 0 (Lng M - 1)) ≤ entry (oper M n) 0 x := by
    intro x hx hxL
    have hh := oper_tiling_block_floor M n x hMT hlast hzero hp
      (by rw [hi]; exact hx) hxL
    rw [hi] at hh
    exact hh
  constructor
  -- ====================== (1) 最終ブロック開始 ======================
  · intro hn2
    have hnm1w : 0 < (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) :=
      Nat.mul_pos (by omega) hw
    have hidxllt : parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
      omega
    -- ブロック開始の読み出し
    have heidxl : entry (oper M n) 0
        (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        = entry M 0 (parent M 0 (Lng M - 1)) := by
      have hh := entry_oper_tiling_block_zero M n (n - 1) 0 hlast hzero hp
        (by omega) (by rw [hi]; omega)
      rw [hi] at hh
      simpa using hh
    -- 許容性: ブロック開始へは隣接辺が立たない（行 0 最小）
    have hadm1 : adm (oper M n)
        (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        = true := by
      cases hbool : nadm (oper M n)
        (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) with
      | false => simp [adm, hbool]
      | true =>
        exfalso
        simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbool
        rcases hbool with hcase | hcase
        · omega
        · have h1 : nextrel1 (oper M n)
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1)
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
            simpa [nextR] using hcase.1
          have hle0adj : le0 (oper M n)
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1)
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) = true := by
            have hh := h1
            simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.2
          have hsuc : parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1 + 1
              = parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := by omega
          have hstep := le0_adjacent (oper M n)
            (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1)
            (by rw [hsuc]; exact hle0adj)
          rw [hsuc] at hstep
          have hstrict : entry (oper M n) 0
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1)
              < entry (oper M n) 0
              (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) := by
            have hh := hstep
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
            exact hh.1.2
          have hfloor := hgemin
            (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) - 1)
            (by omega) (by omega)
          rw [heidxl] at hstrict
          omega
    -- 到達性: 最終ブロック内で右端まで
    have hreach : leR (oper M n) 0
        (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
        (Lng (oper M n) - 1) = true := by
      by_cases hdeg : parent M 0 (Lng M - 1)
          + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) = Lng (oper M n) - 1
      · rw [hdeg]
        exact leR0_refl_bb (oper M n) (Lng (oper M n) - 1) (by omega)
      · apply parent_exists_3 (oper M n)
          (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
          (Lng (oper M n) - 1) hoperT (by omega) (by omega)
        intro j hjgt hjle
        have hjeq : j = parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
            + (j - (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))) := by omega
        have htlt : j - (parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))
            < (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
        have hread : entry (oper M n) 0
            (parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
              + (j - (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)))))
            = entry M 0 (parent M 0 (Lng M - 1)
              + (j - (parent M 0 (Lng M - 1)
                + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))) := by
          have hh := entry_oper_tiling_block_zero M n (n - 1)
            (j - (parent M 0 (Lng M - 1)
              + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
            hlast hzero hp (by omega) (by rw [hi]; exact htlt)
          rw [hi] at hh
          simpa using hh
        rw [heidxl, hjeq, hread]
        have hsf := oper_tiling_strict_floor M
          (j - (parent M 0 (Lng M - 1)
            + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))))
          hMT hp (by omega) (by rw [hi]; omega)
        rw [hi] at hsf
        exact hsf
    exact ⟨⟨hoperT, hadm1, hreach⟩, hMnRT⟩
  -- ====================== (2) 許容化基点 ======================
  · intro hnadmj
    have haLe : Adm M (parent M 0 (Lng M - 1)) ≤ parent M 0 (Lng M - 1) :=
      Adm_le M (parent M 0 (Lng M - 1))
    have haAdm : adm M (Adm M (parent M 0 (Lng M - 1))) = true :=
      Adm_adm M (parent M 0 (Lng M - 1))
    have halt : Adm M (parent M 0 (Lng M - 1)) < parent M 0 (Lng M - 1) := by
      rcases Nat.lt_or_eq_of_le haLe with h | h
      · exact h
      · rw [h] at haAdm
        rw [haAdm] at hnadmj
        cases hnadmj
    -- `M` 内の祖先関係 `a ≤₀ j₀`
    have hleaj₀ : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (parent M 0 (Lng M - 1))
        = true := by
      have h1 := adm_row1_ancestry M (parent M 0 (Lng M - 1)) hMT (by omega)
      exact row1_implies_row0 M _ _ hMT h1
    -- 許容性: 行 1 の両辺を `M` に逆転送して `adm M a` と矛盾
    have hadm2 : adm (oper M n) (Adm M (parent M 0 (Lng M - 1))) = true := by
      cases hbool : nadm (oper M n) (Adm M (parent M 0 (Lng M - 1))) with
      | false => simp [adm, hbool]
      | true =>
        exfalso
        simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbool
        rcases hbool with hcase | hcase
        · omega
        · have h1 : nextrel1 (oper M n) (Adm M (parent M 0 (Lng M - 1)) - 1)
              (Adm M (parent M 0 (Lng M - 1))) = true := by
            simpa [nextR] using hcase.1
          have h2 : nextrel1 (oper M n) (Adm M (parent M 0 (Lng M - 1)))
              (Adm M (parent M 0 (Lng M - 1)) + 1) = true := by
            simpa [nextR] using hcase.2
          have b1 := nextrel1_prefix_back_bb M n _ _ hMT hlast hzero hp hi hn hj₀lt
            (Nat.le_of_lt halt) h1
          have b2 := nextrel1_prefix_back_bb M n _ _ hMT hlast hzero hp hi hn hj₀lt
            (by omega) h2
          have hnadmMa : nadm M (Adm M (parent M 0 (Lng M - 1))) = true := by
            simp only [nadm, Bool.or_eq_true, Bool.and_eq_true]
            right
            constructor
            · simpa [nextR] using b1
            · simpa [nextR] using b2
          rw [adm, hnadmMa] at haAdm
          simp at haAdm
    -- 到達性: `a <₀ j₀` の値特徴付けを `M[n]` の右端まで延長
    have hreach2 : leR (oper M n) 0 (Adm M (parent M 0 (Lng M - 1)))
        (Lng (oper M n) - 1) = true := by
      apply parent_exists_3 (oper M n) (Adm M (parent M 0 (Lng M - 1)))
        (Lng (oper M n) - 1) hoperT (by omega) (by omega)
      intro k hak hkend
      have hexa : entry (oper M n) 0 (Adm M (parent M 0 (Lng M - 1)))
          = entry M 0 (Adm M (parent M 0 (Lng M - 1))) :=
        entry_pref0_bb M n _ hlast hzero hp hi hn hj₀lt (Nat.le_of_lt halt)
      rw [hexa]
      have haj₀ : entry M 0 (Adm M (parent M 0 (Lng M - 1)))
          < entry M 0 (parent M 0 (Lng M - 1)) :=
        ancestor_basic_1 M _ _ _ hMT halt (le_refl _) hleaj₀
      by_cases hkj₀ : k ≤ parent M 0 (Lng M - 1)
      · rw [entry_pref0_bb M n k hlast hzero hp hi hn hj₀lt hkj₀]
        exact ancestor_basic_1 M _ k _ hMT hak hkj₀ hleaj₀
      · have hkL : k < Lng (oper M n) := by omega
        have hfloor := hgemin k (by omega) hkL
        omega
    exact ⟨⟨hoperT, hadm2, hreach2⟩, hMnRT⟩

/-! ## 回帰ベクトル -/

private def cexBB_83 : PS := [(0,0),(1,1),(2,2),(3,1),(2,0)]

#guard decide (RTPS cexBB_83)
#guard hasParent cexBB_83 0 (Lng cexBB_83 - 1)
#guard entry cexBB_83 1 (Lng cexBB_83 - 1) == 0
#guard !adm cexBB_83 1
#guard Adm cexBB_83 1 == 0
-- (1) n=2: 最終ブロック開始 idxl = 1 + 1*3 = 4 が基点
#guard decide (Marked (oper cexBB_83 2) 4)
#guard decide (RTPS (oper cexBB_83 2))
-- (2) n=1,2: Adm_M(j₀) = 0 が基点
#guard decide (Marked (oper cexBB_83 1) 0)
#guard decide (Marked (oper cexBB_83 2) 0)

#print axioms kind0_base_basepoint

end PSS
