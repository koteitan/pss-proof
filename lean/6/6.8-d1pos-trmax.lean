import «6».«6.8-standard-slice-Br-descending»
import «6».«6.3-adm-slice»

/-!
# §6.8 補題（d1pos 跨りスライスの `TrMax` 対応 brick 層）

- 原文: `tmp/content.md` L1422 付近（§6.8 命題の証明本体・`i₁ = 1`（d1pos）分岐）。
  原文の命題本体は `6.8-standard-slice-Br-descending`（訂正 A7/A8 適用済み）で、
  本ファイルはその d1pos leg（`RankSuccD1posLeg`）が消費する
  TrMax-of-slice brick 層（幹右端の対応・境界停止）。
- 訂正: なし（A7/A8 は親命題ファイル側で処理済み）
- Isabelle: `TrMax_eqI` (isabelle/pss_mechanized.thy:11295),
  `TrMax_stop` (同:11421), `le1_imp_entry1_le` (同:11486),
  `nextR1_boundary_stop_of_prefix` (同:11525),
  `nextR1_boundary_stop_d1pos` (同:11771),
  `TrMax_seg_oper_d1pos_eq` (同:12118),
  `TrMax_seg_oper_d1pos_eq_notbrle_uncapped` (同:12385),
  `TrMax_seg_oper_d1pos_brle_uncapped` (同:12522)
- 依存: `6.8-standard-slice-Br-descending`（`TrMax_eq_of_prefix_agree_68`/
  `_sym_68`, `nextR_prefix_agree_68`, `seg_oper_prefix_agree_68`,
  `entry_oper_d1pos_one_68`/`_zero_68`, `length_oper_d1pos_68`,
  `TrMax_IncrFirstN_68`, `TrMax_seg_oper_d1pos_eq_span_68`,
  `trunk_entry1_mono_68`, `leR0_refl_68`）、
  `6.5-Red-le-core`（`TrMax_stop_uncond`、経由 import）、
  `6.3-adm-slice`（`nextR_seg_adm`）
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## `TrMax` の一般特徴付け（Isabelle `TrMax_eqI`/`TrMax_stop` の移植） -/

/-- `TrMax` の特徴付け: `j` の下では行 1 の連鎖が全部立ち、`j` で止まるなら
`TrMax M = j`。 -/
theorem TrMax_eqI (M : PS) (j : ℕ) (hM : TPS M)
    (hbelow : ∀ j', j' < j → nextR M 1 j' (j' + 1) = true)
    (hstop : nextR M 1 j (j + 1) = false) :
    TrMax M = j := by
  have hge : j ≤ TrMax M := le_TrMax_intro_wd M j hM hbelow
  have hle : TrMax M ≤ j := by
    by_contra hlt
    have hstep := TrMax_trunk_step M j hM (by omega)
    rw [hstop] at hstep
    simp at hstep
  omega

/-- 幹が右端まで届かないとき、幹右端の行 1 ステップは失敗する（Lean 版の
`TrMax` 定義では `TrMax_stop_uncond` により無条件に成立するが、Isabelle 原文の
主張を保つ）。 -/
theorem TrMax_stop (M : PS) (hM : TPS M)
    (_hlt : TrMax M < Lng M - 1) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false :=
  TrMax_stop_uncond M hM

/-! ## 行 1 直系先祖に沿った行 1 の単調性 -/

private theorem le1Aux_entry1_le_dt (M : PS) (fuel : ℕ) :
    ∀ a b, le1Aux M fuel a b = true → entry M 1 a ≤ entry M 1 b := by
  induction fuel with
  | zero =>
      intro a b h
      have hab : a = b := by simpa [le1Aux] using h
      subst hab
      exact le_rfl
  | succ fuel ih =>
      intro a b h
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _hpb, hpnext, hap⟩
      · subst h
        exact le_rfl
      · have hstep : entry M 1 p < entry M 1 b := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          exact hn.1.1.2
        exact (ih a p hap).trans hstep.le

/-- 行 1 直系先祖 `(1,a) ≤_M (1,b)` に沿って行 1 の値は弱増加する
（`nextrel1` の各段が狭義増加のため）。 -/
theorem le1_imp_entry1_le (M : PS) (a b : ℕ)
    (h : leR M 1 a b = true) :
    entry M 1 a ≤ entry M 1 b := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_entry1_le_dt M (Lng M) a b hh.2

/-! ## 境界停止の接頭辞転送（易しい方向） -/

/-- 停止添字 `TrMax N + 1` が共有接頭辞 `[0,c]` の内側にあるとき、`N` 側の
幹停止が `M` に転送される。 -/
theorem nextR1_boundary_stop_of_prefix
    (M N : PS) (c : ℕ) (_hM : TPS M) (hN : TPS N)
    (hagree : ∀ j, j ≤ c → M.getD j (0, 0) = N.getD j (0, 0))
    (hcM : c < Lng M) (hcN : c < Lng N)
    (_htnlt : TrMax N < Lng N - 1)
    (hinrange : TrMax N + 1 ≤ c) :
    nextR M 1 (TrMax N) (TrMax N + 1) = false := by
  have hsame := nextR_prefix_agree_68 M N c 1 (TrMax N) (TrMax N + 1)
    hagree hcM hcN (by omega) hinrange
  rw [hsame]
  exact TrMax_stop_uncond N hN

/-! ## d1pos 境界停止（本体 brick）

d0zero と違い最終列の行 1 は非零なので、幹の内在的閉じ込めは無い。代わりに
ブロック境界での行 1 リセット（d1pos の行 1 は per-block シフト無し）と、
簡約幹に沿った行 1 弱増加（`trunk_entry1_mono_68`）で境界の狭義増加を潰す。 -/

/-- §6.8 d1pos regime-A capped 境界停止: `j₀' ≤ j₋₂`, `Lng N - 1 ≤ j₁'` のとき、
`M' = seg (N[n]) j₀' j₁'` の中で参照切片 `N_p = seg N j₀' (Lng N - 1)` の
幹右端の行 1 ステップは失敗する。 -/
theorem nextR1_boundary_stop_d1pos
    (N : PS) (n j₀' j₁' : ℕ)
    (_hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hpar : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn : 1 ≤ n)
    (hstart : j₀' ≤ parent N 1 (Lng N - 1))
    (hbge : Lng N - 1 ≤ j₁')
    (hend : j₁' < Lng (oper N n)) :
    nextR (seg (oper N n) j₀' j₁') 1
      (TrMax (seg N j₀' (Lng N - 1)))
      (TrMax (seg N j₀' (Lng N - 1)) + 1) = false := by
  let j₁ := Lng N - 1
  let jm2 := parent N 1 (Lng N - 1)
  let w := j₁ - jm2
  let Mp := seg (oper N n) j₀' j₁'
  let Np := seg N j₀' j₁
  let t := TrMax Np
  have hj₁d : j₁ = Lng N - 1 := rfl
  have hjm2d : jm2 = parent N 1 (Lng N - 1) := rfl
  have hwd : w = j₁ - jm2 := rfl
  have hparlt : jm2 < j₁ := hpar
  have hstart' : j₀' ≤ jm2 := hstart
  have hj₀'lt : j₀' < j₁ := by omega
  have hj₀'le : j₀' ≤ j₁' := by omega
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hLNp : Lng Np = j₁ + 1 - j₀' := by simp [Np]
  have hLMp : Lng Mp = j₁' + 1 - j₀' := by simp [Mp]
  have hNpLen : 1 < Lng Np := by omega
  have htb : t ≤ Lng Np - 1 := TrMax_bound Np hNpT
  apply Bool.eq_false_iff.mpr
  intro hstep0
  have hstep : nextR Mp 1 t (t + 1) = true := hstep0
  by_cases heasy : t + 1 ≤ Lng Np - 2
  · -- EASY: 停止添字が接頭辞一致領域の内側
    have hcM : Lng Np - 2 < Lng Mp := by omega
    have hcN : Lng Np - 2 < Lng Np := by omega
    have hagree : ∀ s, s ≤ Lng Np - 2 →
        Mp.getD s (0, 0) = Np.getD s (0, 0) := by
      intro s hs
      exact seg_oper_prefix_agree_68 N n j₀' j₁' (Lng Np - 2) hlen hn
        hcM hcN (by intro s' hs'; omega) s hs
    have htnlt : t < Lng Np - 1 := by omega
    have hstopP : nextR Mp 1 t (t + 1) = false :=
      nextR1_boundary_stop_of_prefix Mp Np (Lng Np - 2)
        hMpT hNpT hagree hcM hcN htnlt heasy
    rw [hstopP] at hstep
    simp at hstep
  · -- HARD: 停止添字がブロック境界に届く
    have htge : Lng Np - 2 ≤ t := by omega
    have hdata := hstep
    simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
      Bool.and_eq_true, decide_eq_true_eq] at hdata
    have ht1Mp : t + 1 < Lng Mp := hdata.1.1.1.1.2
    have htMp : t < Lng Mp := by omega
    have hstrict : entry Mp 1 t < entry Mp 1 (t + 1) := hdata.1.1.2
    have hj₁Oper : j₁ < Lng (oper N n) := by omega
    have hOL : Lng (oper N n) = jm2 + n * w :=
      length_oper_d1pos_68 N n hlen hzero hp hi
    have hn2 : 2 ≤ n := by
      by_contra hcon
      have hn1 : n = 1 := by omega
      rw [hOL, hn1] at hj₁Oper
      omega
    have hn2' : 1 < n := by omega
    have hMp_t1 : entry Mp 1 (t + 1) = entry (oper N n) 1 (j₀' + (t + 1)) :=
      entry_seg (oper N n) j₀' j₁' 1 (t + 1) ht1Mp
    have hMp_t : entry Mp 1 t = entry (oper N n) 1 (j₀' + t) :=
      entry_seg (oper N n) j₀' j₁' 1 t htMp
    have hidx_t_le : j₀' + t ≤ j₁ := by omega
    -- 行 1 の境界リセット: `entry M' 1 (t+1) = N_{1,j₋₂}`
    have hsegt1 : entry Mp 1 (t + 1) = entry N 1 jm2 := by
      by_cases hcase : j₀' + (t + 1) = j₁
      · -- 境界そのもの: ブロック 1 の先頭（offset 0）
        have hh := entry_oper_d1pos_one_68 N n 1 0 hlen hzero hp hi hn2'
          (by omega)
        have hidx : parent N 1 (Lng N - 1) +
            1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 =
              j₀' + (t + 1) := by omega
        rw [hMp_t1, ← hidx, hh]
        simp [hjm2d]
      · -- 境界の一つ先: `w = 1` が強制される
        have heqLN : j₀' + (t + 1) = j₁ + 1 := by omega
        have htLNp : t = Lng Np - 1 := by omega
        have hpre_lt : Lng Np - 2 < t := by omega
        have hstepNp := TrMax_trunk_step Np (Lng Np - 2) hNpT hpre_lt
        have hsegNp : Lng (seg N j₀' j₁) = Lng Np := rfl
        have haN : Lng Np - 2 < Lng (seg N j₀' j₁) := by
          rw [hsegNp]; omega
        have hbN : Lng Np - 2 + 1 < Lng (seg N j₀' j₁) := by
          rw [hsegNp]; omega
        have htr := nextR_seg_adm N j₀' j₁ 1 (Lng Np - 2) (Lng Np - 2 + 1)
          (by omega) (by omega) haN hbN
        have hstepN0 : nextR N 1 (j₀' + (Lng Np - 2))
            (j₀' + (Lng Np - 2 + 1)) = true := by
          rw [← htr]
          exact hstepNp
        have hidxlo : j₀' + (Lng Np - 2) = j₁ - 1 := by omega
        have hidxhi : j₀' + (Lng Np - 2 + 1) = j₁ := by omega
        rw [hidxlo, hidxhi] at hstepN0
        have hdataN := hstepN0
        simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
          Bool.and_eq_true, decide_eq_true_eq] at hdataN
        have hle0pred : le0 N (j₁ - 1) (Lng N - 1) = true := hdataN.1.2
        have hstrictN : entry N 1 (j₁ - 1) < entry N 1 (Lng N - 1) :=
          hdataN.1.1.2
        have hp1 : hasParent N 1 (Lng N - 1) = true := by
          simpa [hi] using hp
        have hnr1 := hasParent_next_fseq N 1 (Lng N - 1) hp1
        have hdata1 := hnr1
        simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
          Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range] at hdata1
        -- 行 1 親の最小性から `w = 1`
        have hw1 : w = 1 := by
          by_contra hwne
          have hlt' : parent N 1 (Lng N - 1) < j₁ - 1 := by omega
          have hmin := hdata1.2 (j₁ - 1) (by omega)
          have hminP : entry N 1 (Lng N - 1) ≤ entry N 1 (j₁ - 1) := by
            simpa [hlt', hle0pred] using hmin
          omega
        -- するとその添字はブロック 2 の先頭（offset 0）
        have hn3 : 2 < n := by
          have hj₁'ge : j₁ + 1 ≤ j₁' := by omega
          have hlt2 : j₁ + 1 < Lng (oper N n) := by omega
          rw [hOL, hw1, Nat.mul_one] at hlt2
          omega
        have hh := entry_oper_d1pos_one_68 N n 2 0 hlen hzero hp hi hn3
          (by omega)
        have hidx2 : parent N 1 (Lng N - 1) +
            2 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 =
              j₀' + (t + 1) := by omega
        rw [hMp_t1, ← hidx2, hh]
        simp [hjm2d]
    -- 簡約幹に沿った行 1 弱増加: `N_{1,j₋₂} ≤ entry M' 1 t`
    have hjjle : jm2 - j₀' ≤ t := by omega
    have hmono := trunk_entry1_mono_68 Np (jm2 - j₀') t hNpT hjjle le_rfl
    have hjmNp : jm2 - j₀' < Lng Np := by omega
    have htNp : t < Lng Np := by omega
    rw [entry_seg N j₀' j₁ 1 (jm2 - j₀') hjmNp,
      entry_seg N j₀' j₁ 1 t htNp] at hmono
    have hjidx : j₀' + (jm2 - j₀') = jm2 := by omega
    rw [hjidx] at hmono
    have he_Mt : entry N 1 jm2 ≤ entry Mp 1 t := by
      by_cases hblock : j₀' + t < j₁
      · -- ブロック 0 の逐語領域
        have hoper : entry (oper N n) 1 (j₀' + t) = entry N 1 (j₀' + t) :=
          entry_oper_lt_last_68 N n 1 (j₀' + t) hlen hn (Or.inr rfl)
            (by omega)
        rw [hMp_t, hoper]
        exact hmono
      · -- 境界: 行 1 リセット
        have heqj : j₀' + t = j₁ := by omega
        have hh := entry_oper_d1pos_one_68 N n 1 0 hlen hzero hp hi hn2'
          (by omega)
        have hidx1 : parent N 1 (Lng N - 1) +
            1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 = j₀' + t := by
          omega
        rw [hMp_t, ← hidx1, hh]
        simp [hjm2d]
    -- 合成して矛盾
    have hkey : entry Mp 1 (t + 1) ≤ entry Mp 1 t := by
      rw [hsegt1]
      exact he_Mt
    omega

/-! ## d1pos TrEq キーストーン群 -/

/-- ブロック `q` 内の接頭辞 `[0, b-1-a]` での点ごとの一致:
`seg (N[n]) j₀' j₁'` と `IncrFirstN sh (seg N a b)`（`sh = q·δ`）。
`TrMax_seg_oper_d1pos_eq_span_68` の一致部分の切り出し。 -/
private theorem d1pos_agree_dt
    (N : PS) (n q s₀ a b j₀' j₁' sh : ℕ)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n)
    (ha : a = parent N 1 (Lng N - 1) + s₀)
    (hj₀ : j₀' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
    (hsh : sh = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hb : b ≤ Lng N - 1) (hab : a < b)
    (hcM : b - 1 - a < Lng (seg (oper N n) j₀' j₁')) :
    ∀ s, s ≤ b - 1 - a →
      (seg (oper N n) j₀' j₁').getD s (0, 0) =
        (IncrFirstN sh (seg N a b)).getD s (0, 0) := by
  intro s hsc
  have hsM : s < Lng (seg (oper N n) j₀' j₁') := hsc.trans_lt hcM
  have hsN : s < Lng (seg N a b) := by
    simp
    omega
  have hsNs : s < Lng (IncrFirstN sh (seg N a b)) := by
    simpa [IncrFirstN_eq_map] using hsN
  have hsoff : s₀ + s < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  rw [getD_eq_getElem_idx _ (0, 0) hsM,
    getD_eq_getElem_idx _ (0, 0) hsNs,
    seg_getElem_68 (oper N n) j₀' j₁' s hsM]
  simp only [IncrFirstN_eq_map, List.getElem_map]
  rw [seg_getElem_68 N a b s hsN]
  have hidxM : j₀' + s = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s₀ + s) := by
    simp [hj₀, Nat.add_assoc]
  have hidxN : a + s = parent N 1 (Lng N - 1) + (s₀ + s) := by
    simp [ha, Nat.add_assoc]
  rw [hidxM, hidxN,
    entry_oper_d1pos_zero_68 N n q (s₀ + s) hlen hzero hp hi hq hsoff,
    entry_oper_d1pos_one_68 N n q (s₀ + s) hlen hzero hp hi hq hsoff]
  simp [hsh]

/-- §6.8 d1pos TrEq キーストーン（UNCAPPED 逐語 span 形、`tnc`/`stop` を仮定に
持つ条件付き形）: `M' = seg (N[n]) j₀' j₁'` の幹右端は参照切片
`seg N j0red j1red` の幹右端に一致する。 -/
theorem TrMax_seg_oper_d1pos_eq
    (N : PS) (n q s₀ j0red j1red j₀' j₁' shamt : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (_hpar : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hn : 1 ≤ n)
    (hq : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s₀)
    (hs0lt : s₀ < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj₀'eq : j₀' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hspan : j1red = j0red + (j₁' - j₀'))
    (hj0j1' : j₀' < j₁')
    (hj1lt : j₁' < Lng (oper N n))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j₀' j₁') 1
      (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false) :
    TrMax (seg (oper N n) j₀' j₁') = TrMax (seg N j0red j1red) :=
  TrMax_seg_oper_d1pos_eq_span_68 N n q s₀ j0red j1red j₀' j₁' shamt
    hNT hlen hzero hp hi hq hs0w hs0eq hs0lt hj₀'eq hshamt
    hj1redle hj0j1red (by omega) hj0j1' hj1lt htnc hstop

/-- §6.8 d1pos TrEq キーストーン（`¬brle` 無条件 UNCAPPED 形）: `tnc`/`stop` を
`¬brle` の 2 連言（`Mlt`/`notle`）から `M'` 側で調達し、対称接頭辞転送
（`TrMax_eq_of_prefix_agree_sym_68`）で幹の一致を得る。 -/
theorem TrMax_seg_oper_d1pos_eq_notbrle_uncapped
    (N : PS) (n q s₀ j0red j1red j₀' j₁' shamt : ℕ)
    (_hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (_hpar : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hn : 1 ≤ n)
    (hq : q < n)
    (_hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s₀)
    (_hs0lt : s₀ < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj₀'eq : j₀' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hspan : j1red = j0red + (j₁' - j₀'))
    (hj0j1' : j₀' < j₁')
    (_hj1lt : j₁' < Lng (oper N n))
    (hMlt : TrMax (seg (oper N n) j₀' j₁') <
      Lng (seg (oper N n) j₀' j₁') - 1)
    (hnotle : leR (seg (oper N n) j₀' j₁') 0
      (TrMax (seg (oper N n) j₀' j₁') + 1)
      (Lng (seg (oper N n) j₀' j₁') - 1) = false) :
    TrMax (seg (oper N n) j₀' j₁') = TrMax (seg N j0red j1red) := by
  let Mp := seg (oper N n) j₀' j₁'
  let Np := seg N j0red j1red
  let Nps := IncrFirstN shamt Np
  let c := j1red - 1 - j0red
  have hcd : c = j1red - 1 - j0red := rfl
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hNpsT : TPS Nps := by
    simpa [Nps, TPS, IncrFirstN_eq_map] using hNpT
  have hLMp : Lng Mp = j₁' + 1 - j₀' := by simp [Mp]
  have hLNps : Lng Nps = j1red + 1 - j0red := by
    simp [Nps, Np, IncrFirstN_eq_map]
  have htrShift : TrMax Nps = TrMax Np := TrMax_IncrFirstN_68 shamt Np
  have hMlt' : TrMax Mp < Lng Mp - 1 := hMlt
  have hcLMp : c = Lng Mp - 2 := by omega
  have hcM : c < Lng Mp := by omega
  have hcN : c < Lng Nps := by omega
  have hLMp2 : 2 ≤ Lng Mp := by omega
  -- `¬brle` の 2 連言から `M'` 側の strict-2 閉じ込め
  have htncM1 : TrMax Mp + 1 ≤ c := by
    have hle_c : TrMax Mp ≤ c := by omega
    have hne : TrMax Mp ≠ c := by
      intro heq
      have hidx : TrMax Mp + 1 = Lng Mp - 1 := by omega
      have hendlt : Lng Mp - 1 < Lng Mp := by omega
      have hrefl : leR Mp 0 (Lng Mp - 1) (Lng Mp - 1) = true :=
        leR0_refl_68 Mp (Lng Mp - 1) hendlt
      have hnotle' : leR Mp 0 (TrMax Mp + 1) (Lng Mp - 1) = false := hnotle
      rw [hidx] at hnotle'
      rw [hnotle'] at hrefl
      simp at hrefl
    omega
  have hstopM : nextR Mp 1 (TrMax Mp) (TrMax Mp + 1) = false :=
    TrMax_stop_uncond Mp hMpT
  have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Nps.getD s (0, 0) :=
    d1pos_agree_dt N n q s₀ j0red j1red j₀' j₁' shamt hlen hzero hp hi hq
      hs0eq hj₀'eq hshamt hj1redle hj0j1red hcM
  have hsym := TrMax_eq_of_prefix_agree_sym_68 Mp Nps c hMpT hNpsT hagree
    hcM hcN htncM1 hstopM
  rw [htrShift] at hsym
  exact hsym

/-- §6.8 d1pos `brle` 帰結クローザ（UNCAPPED 形）: 参照幹が切片を満たすなら
`M'` 側は `brle`（幹が右端まで届く、または幹右端の次から右端へ `le0`）。
`¬brle` を仮定すると無条件 UNCAPPED キーストーンが幹の一致を与え、
長さ一致と fill 仮定が `Mlt` と矛盾する。 -/
theorem TrMax_seg_oper_d1pos_brle_uncapped
    (N : PS) (n q s₀ j0red j1red j₀' j₁' shamt : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hpar : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn : 1 ≤ n)
    (hq : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s₀)
    (hs0lt : s₀ < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj₀'eq : j₀' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hspan : j1red = j0red + (j₁' - j₀'))
    (hj0j1' : j₀' < j₁')
    (hj1lt : j₁' < Lng (oper N n))
    (hfill : TrMax (seg N j0red j1red) =
      Lng (seg N j0red j1red) - 1) :
    TrMax (seg (oper N n) j₀' j₁') =
        Lng (seg (oper N n) j₀' j₁') - 1 ∨
      leR (seg (oper N n) j₀' j₁') 0
        (TrMax (seg (oper N n) j₀' j₁') + 1)
        (Lng (seg (oper N n) j₀' j₁') - 1) = true := by
  by_contra hcon
  obtain ⟨hne, hnotle⟩ := not_or.mp hcon
  have hnotle' : leR (seg (oper N n) j₀' j₁') 0
      (TrMax (seg (oper N n) j₀' j₁') + 1)
      (Lng (seg (oper N n) j₀' j₁') - 1) = false :=
    Bool.eq_false_iff.mpr hnotle
  have hMpT : TPS (seg (oper N n) j₀' j₁') := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have htb := TrMax_bound (seg (oper N n) j₀' j₁') hMpT
  have hMlt : TrMax (seg (oper N n) j₀' j₁') <
      Lng (seg (oper N n) j₀' j₁') - 1 := by omega
  have hTrEq := TrMax_seg_oper_d1pos_eq_notbrle_uncapped N n q s₀
    j0red j1red j₀' j₁' shamt hNT hlen hzero hp hi hpar hn hq hs0w
    hs0eq hs0lt hj₀'eq hshamt hj1redle hj0j1red hspan hj0j1' hj1lt
    hMlt hnotle'
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red := by simp
  have hLMp : Lng (seg (oper N n) j₀' j₁') = j₁' + 1 - j₀' := by simp
  omega

end PSS

#print axioms PSS.TrMax_eqI
#print axioms PSS.TrMax_stop
#print axioms PSS.le1_imp_entry1_le
#print axioms PSS.nextR1_boundary_stop_of_prefix
#print axioms PSS.nextR1_boundary_stop_d1pos
#print axioms PSS.TrMax_seg_oper_d1pos_eq
#print axioms PSS.TrMax_seg_oper_d1pos_eq_notbrle_uncapped
#print axioms PSS.TrMax_seg_oper_d1pos_brle_uncapped
