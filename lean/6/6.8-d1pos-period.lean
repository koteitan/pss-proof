import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-trmax»
import «6».«6.8-d1pos-le0»
import «6».«6.8-d1pos-base»

/-!
# §6.8 d1pos 周期レジーム層（CELL-4 PERIODIC-TAIL brick 群）＋即討ち Props

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域、周期尾部 `j₀' ≥ Lng N - 1` の場合分け）
- 訂正: A7/A8 は上位ファイル群と同じ座標系（`*_68` 読み出し）で適用済み
- Isabelle (pss_mechanized.thy):
  - `oper_d1pos_anchor_coincide_period_interior` 18671
  - `oper_d1pos_anchor_coincide_period_boundary` 18732
  - `oper_d1pos_notbrle_period_fullShift` 18791
  - `oper_d1pos_notbrle_period_boundary_geom` 18956
  - `oper_d1pos_period_row0_unif` 19267
  - `oper_d1pos_ctx_period_le0Np` 19442
  - `oper_d1pos_ctx_stop_direct` 19581
  - `oper_d1pos_ctx_stop_direct_strict` 19891
  - `oper_d1pos_ctx_period_tncstrict_uncapped` 20019
  - 即討ち: `oper_d1pos_ctx_tnc_capped` 13593（le0 層の既存定理の引数順替え）／
    `nextR1_boundary_stop_d1pos` 11771（trmax 層の既存定理の引数順替え）
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Props・`oper_d1pos_ctx_dpos`/
  `oper_d1pos_ctx_r1le`）、«6».«6.8-d1pos-trmax»（`nextR1_boundary_stop_of_prefix`・
  `TrMax_seg_oper_d1pos_eq_notbrle_uncapped`・`le1_imp_entry1_le`）、
  «6».«6.8-d1pos-le0»（`oper_d1pos_ctx_tnc_capped`）、
  «6».«6.8-d1pos-base»（`oper_d1pos_LOW_source_eq`）、
  推移 import の `*_68` 読み出し群（`entry_oper_d1pos_zero_68`/`one_68`,
  `length_oper_d1pos_68`, `seg_of_seg_68`, `TrMax_IncrFirstN_68`,
  `TrMax_seg_oper_d1pos_eq_span_68`, `P_last_anchor_68`,
  `last_anchor_eq_sum_dropLast_68`, `last_anchor_ge_of_leftmin_68`,
  `leR0_refl_68`）
- 状態: ✅ 証明済（sorry 0、公開定理 17 本、D1pos Props 8 本 discharge:
  `ctx_tnc_capped` / `nextR1_boundary_stop_d1pos` /
  `ctx_period_tncstrict_uncapped` / `ctx_period_le0Np` /
  `ctx_stop_direct` / `ctx_stop_direct_strict` /
  `notbrle_period_fullShift` / `notbrle_period_boundary_geom`）
- Isabelle との差分メモ: `le0` の周期転送（Isa `le0_prefix_row0_shift` の
  rtrancl 帰納）は値特徴付け（`ancestor_basic_1`＋`oper_d1pos_period_row0_unif`
  ＋`parent_exists_3`）で置換。TrEq は Isa `oper_d1pos_notbrle_Br_align` の
  代わりに built keystone `TrMax_seg_oper_d1pos_eq_span_68` から直接取る
  （align の消費は TrEq 連言のみ）。
-/

namespace PSS

/-! ## 私用補助（suffix `_pd`） -/

/-- `1 < (P S).length` なら `S ≠ []`（`P [] = [[]]` は長さ 1）。 -/
private theorem TPS_of_P_multi_pd (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

/-! ## 即討ち Prop (a): `oper_d1pos_ctx_tnc_capped`（既存定理の引数順替え） -/

theorem D1pos_oper_d1pos_ctx_tnc_capped_holds :
    D1pos_oper_d1pos_ctx_tnc_capped := by
  intro N n q s0 j0red j1red j0' j1' shamt
  intro hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hnotbrle
  exact oper_d1pos_ctx_tnc_capped N n q j0red j1red s0 j0' j1' shamt
    hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hnotbrle

/-! ## 即討ち Prop (b): `nextR1_boundary_stop_d1pos`（既存定理そのもの） -/

theorem D1pos_nextR1_boundary_stop_d1pos_holds :
    D1pos_nextR1_boundary_stop_d1pos := by
  intro N n j0' j1' hNT hlen hzero hp hi hpar hn hstart hbge hend
  exact nextR1_boundary_stop_d1pos N n j0' j1'
    hNT hlen hzero hp hi hpar hn hstart hbge hend

/-! ## 即討ち Prop (c): UNCAPPED STRICT-tnc discharger
Isabelle `oper_d1pos_ctx_period_tncstrict_uncapped` (pss_mechanized.thy:20019)。
`¬brle` の 2 連言から `M'` 側の strict-2 閉じ込め `TrMax M' + 1 ≤ Lng M' - 2` を
取り、built keystone `TrMax_seg_oper_d1pos_eq_notbrle_uncapped` の TrEq と
uncapped span の長さ一致で `TrMax N_red < c` に落とす。 -/

theorem oper_d1pos_ctx_period_tncstrict_uncapped
    (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n) (hqn : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hspan : j1red = j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    TrMax (seg N j0red j1red) < j1red - 1 - j0red := by
  obtain ⟨hndisj1, hnotle⟩ := not_or.mp hnotbrle
  have hMpT : TPS (seg (oper N n) j0' j1') := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have htb := TrMax_bound (seg (oper N n) j0' j1') hMpT
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' :=
    length_seg (oper N n) j0' j1'
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red :=
    length_seg N j0red j1red
  have hMlt : TrMax (seg (oper N n) j0' j1') <
      Lng (seg (oper N n) j0' j1') - 1 := by omega
  -- strict-2 閉じ込め: TrMax M' + 1 ≤ Lng M' - 2
  have htncM1 : TrMax (seg (oper N n) j0' j1') + 1 ≤
      Lng (seg (oper N n) j0' j1') - 2 := by
    have hne : TrMax (seg (oper N n) j0' j1') ≠
        Lng (seg (oper N n) j0' j1') - 2 := by
      intro heq
      apply hnotle
      have hidx : TrMax (seg (oper N n) j0' j1') + 1 =
          Lng (seg (oper N n) j0' j1') - 1 := by omega
      rw [hidx]
      exact leR0_refl_68 (seg (oper N n) j0' j1')
        (Lng (seg (oper N n) j0' j1') - 1) (by omega)
    omega
  have hnotle' : leR (seg (oper N n) j0' j1') 0
      (TrMax (seg (oper N n) j0' j1') + 1)
      (Lng (seg (oper N n) j0' j1') - 1) = false :=
    Bool.eq_false_iff.mpr hnotle
  have hTrEq := TrMax_seg_oper_d1pos_eq_notbrle_uncapped N n q s0
    j0red j1red j0' j1' shamt hNT hlen hzero hp hi hj0lt hn1 hqn hs0w
    hs0eq hs0lt hj0'eq hshamt hj1redle hj0j1red hspan hj0j1' hj1lt
    hMlt hnotle'
  omega

theorem D1pos_oper_d1pos_ctx_period_tncstrict_uncapped_holds :
    D1pos_oper_d1pos_ctx_period_tncstrict_uncapped := by
  intro N n q s0 j0red j1red j0' j1' shamt
  intro hNT hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt hj0'eq hshamt
    hj1redle hj0j1red hspan hj0j1' hj1lt hnotbrle
  exact oper_d1pos_ctx_period_tncstrict_uncapped N n q s0 j0red j1red
    j0' j1' shamt hNT hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hspan hj0j1' hj1lt hnotbrle

/-! ## アンカー一致（CELL-4 PERIODIC-TAIL）— INTERIOR 亜種
Isabelle `oper_d1pos_anchor_coincide_period_interior` (pss_mechanized.thy:18671)。
`S` が `Snside` の完全シフト `IncrFirstN shamt` のとき、最終 P アンカーは一致し、
接合部の行 0 は `+shamt`、行 1 は不変（従って `≤`）。 -/

theorem oper_d1pos_anchor_coincide_period_interior
    (S Snside : PS) (shamt : ℕ)
    (hSnT : TPS Snside) (hmultiN : 1 < (P Snside).length)
    (hfullShift : S = IncrFirstN shamt Snside) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
        (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 ∧
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry Snside 0
          ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) + shamt ∧
      entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry Snside 1
          ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) := by
  subst hfullShift
  have hPS : P (IncrFirstN shamt Snside) = (P Snside).map (IncrFirstN shamt) :=
    P_IncrFirstN_equivariance shamt Snside
  -- アンカー一致: butlast の長さ和はシフト不変
  have hceq : (IdxSum (P (IncrFirstN shamt Snside))).getD
      ((P (IncrFirstN shamt Snside)).length - 1) 0 =
      (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 := by
    rw [last_anchor_eq_sum_dropLast_68 (IncrFirstN shamt Snside),
      last_anchor_eq_sum_dropLast_68 Snside, hPS]
    rw [← List.map_dropLast]
    simp [List.map_map, Function.comp_def, IncrFirstN_eq_map]
  -- アンカーの範囲: cN < Lng Snside
  obtain ⟨_, hcNle, _, _, _⟩ := P_last_anchor_68 Snside hSnT hmultiN
  have hSnPos : 0 < Lng Snside := List.length_pos_of_ne_nil hSnT
  have hcNlt : (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 <
      Lng Snside := by omega
  refine ⟨hceq, ?_, ?_⟩
  · rw [hceq]
    exact entry_IncrFirstN_zero shamt Snside _ hcNlt
  · rw [hceq, entry_IncrFirstN_one shamt Snside _]

/-! ## アンカー一致（CELL-4 PERIODIC-TAIL）— BOUNDARY 亜種
Isabelle `oper_d1pos_anchor_coincide_period_boundary` (pss_mechanized.thy:18732)。
`S` 側アンカーが境界 `m = Lng Snside - 1` に固定されているとき、`Snside` 側も
`m` が行 0 左最小（`mLmin`）ゆえアンカーは `m` に一致し、接合値は境界読み出し
（`boundEq0`/`boundEq1`）から。 -/

theorem oper_d1pos_anchor_coincide_period_boundary
    (S Snside : PS) (shamt : ℕ)
    (_hST : TPS S) (_hmulti : 1 < (P S).length)
    (hSnT : TPS Snside) (hmultiN : 1 < (P Snside).length)
    (_hmleS : Lng Snside - 1 ≤ Lng S - 1)
    (hcle : (IdxSum (P S)).getD ((P S).length - 1) 0 = Lng Snside - 1)
    (hmLmin : ∀ j, j < Lng Snside - 1 →
      entry Snside 0 (Lng Snside - 1) ≤ entry Snside 0 j)
    (hboundEq0 : entry S 0 (Lng Snside - 1) =
      entry Snside 0 (Lng Snside - 1) + shamt)
    (hboundEq1 : entry S 1 (Lng Snside - 1) ≤
      entry Snside 1 (Lng Snside - 1)) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
        (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 ∧
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry Snside 0
          ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) + shamt ∧
      entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry Snside 1
          ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) := by
  obtain ⟨_, hcNle, _, _, _⟩ := P_last_anchor_68 Snside hSnT hmultiN
  have hcNge : Lng Snside - 1 ≤
      (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 :=
    last_anchor_ge_of_leftmin_68 Snside (Lng Snside - 1) hSnT le_rfl hmLmin
  have hcNeq : (IdxSum (P Snside)).getD ((P Snside).length - 1) 0 =
      Lng Snside - 1 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hcle, hcNeq]
    exact hboundEq0
  · rw [hcle, hcNeq]
    exact hboundEq1

/-! ## 周期尾部の行 0 一様一致
Isabelle `oper_d1pos_period_row0_unif` (pss_mechanized.thy:19267)。
消費側 `M' = seg (N[n]) j0' j1'` の行 0 値は、`[0, Lng Np - 1]` の全オフセットで
`Np = seg N j0red j1red` の行 0 値 `+shamt`。ブロック内（`s0+j < w`）は
ブロック `q0` 読み出し、境界（`s0+j = w`）はブロック `q0+1` オフセット 0 の
読み出しと `dpos` の詰め直しで一致。 -/

theorem oper_d1pos_period_row0_unif
    (N : PS) (n q0 s0 j0red j0' shamt j1red j : ℕ)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hq0n : q0 < n)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0reds : j0red = parent N 1 (Lng N - 1) + s0)
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red ≤ j1red)
    (hjvalid : j0' + j < Lng (oper N n))
    (hjle : j ≤ j1red - j0red) :
    entry (oper N n) 0 (j0' + j) = entry N 0 (j0red + j) + shamt := by
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hsle : s0 + j ≤ Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  by_cases hcase : s0 + j < Lng N - 1 - parent N 1 (Lng N - 1)
  · -- ブロック `q0` 内
    have he := entry_oper_d1pos_zero_68 N n q0 (s0 + j) hlen hzero hp hi
      hq0n hcase
    have hidx : j0' + j = parent N 1 (Lng N - 1) +
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + j) := by omega
    have hidxN : parent N 1 (Lng N - 1) + (s0 + j) = j0red + j := by omega
    rw [hidx, he, hidxN, hshamt]
  · -- 境界: `s0 + j = w`、`j0red + j = Lng N - 1`
    have hseqw : s0 + j = Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hjredeq : j0red + j = Lng N - 1 := by omega
    have hsucc : (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
          (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.succ_mul q0 _
    have hidxB : j0' + j = parent N 1 (Lng N - 1) +
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 := by omega
    have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
    have hq1n : q0 + 1 < n := by
      by_contra hcon
      have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have he := entry_oper_d1pos_zero_68 N n (q0 + 1) 0 hlen hzero hp hi
      hq1n hw
    have hdpos : entry N 0 (parent N 1 (Lng N - 1)) <
        entry N 0 (Lng N - 1) := oper_d1pos_ctx_dpos N hp hi hj0lt
    have hsuccd : (q0 + 1) * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) =
        q0 * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) +
        (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) := Nat.succ_mul q0 _
    rw [hidxB, he, hjredeq, hshamt]
    simp only [Nat.add_zero]
    omega

/-! ## CELL-4 le0Np discharger
Isabelle `oper_d1pos_ctx_period_le0Np` (pss_mechanized.thy:19442)。
Isabelle は `le0_prefix_row0_shift`（rtrancl 帰納）経由だが、Lean 版は値特徴付け:
`le0M` の鎖に沿った行 0 真増加（`ancestor_basic_1`）を行 0 一様一致
（`oper_d1pos_period_row0_unif`）で `N` 側に移送し、`parent_exists_3` で
`le0 N j0red j1red` を再構成する。 -/

theorem oper_d1pos_ctx_period_le0Np
    (N M : PS) (n q0 s0 j0red j1red j0' j1' shamt : ℕ)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hMeq : M = oper N n)
    (hle0M : leR M 0 j0' j1' = true)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (hq0n : q0 < n)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0reds : j0red = parent N 1 (Lng N - 1) + s0)
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hj1redspan : j1red ≤ j0red + (j1' - j0')) :
    leR N 0 j0red j1red = true := by
  subst hMeq
  have hNT : TPS N := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng N
    omega
  have hMT : TPS (oper N n) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (oper N n)
    omega
  -- 行 0 一様一致（両端点込み）
  have hunif : ∀ t, t ≤ j1red - j0red →
      entry (oper N n) 0 (j0' + t) = entry N 0 (j0red + t) + shamt := by
    intro t ht
    exact oper_d1pos_period_row0_unif N n q0 s0 j0red j0' shamt j1red t
      hlen hzero hp hi hj0lt hq0n hs0lt hj0reds hj0'eq hshamt hj1redle
      (by omega) (by omega) ht
  -- 値特徴付けで N 側の鎖を再構成
  apply parent_exists_3 N j0red j1red hNT hj0j1red (by omega)
  intro x hx1 hx2
  have ht0 := hunif 0 (by omega)
  have htx := hunif (x - j0red) (by omega)
  rw [show j0red + (x - j0red) = x by omega] at htx
  have hgrow : entry (oper N n) 0 j0' <
      entry (oper N n) 0 (j0' + (x - j0red)) :=
    ancestor_basic_1 (oper N n) j0' (j0' + (x - j0red)) j1' hMT
      (by omega) (by omega) hle0M
  simp only [Nat.add_zero] at ht0
  omega

theorem D1pos_oper_d1pos_ctx_period_le0Np_holds :
    D1pos_oper_d1pos_ctx_period_le0Np := by
  intro N M n q0 s0 j0red j1red j0' j1' shamt
  intro hlen hzero hp hi hj0lt hMeq hle0M hlt hjM hq0n hs0lt hj0reds
    hj0'eq hshamt hj1redle hj0j1red hj1redspan
  exact oper_d1pos_ctx_period_le0Np N M n q0 s0 j0red j1red j0' j1' shamt
    hlen hzero hp hi hj0lt hMeq hle0M hlt hjM hq0n hs0lt hj0reds
    hj0'eq hshamt hj1redle hj0j1red hj1redspan

/-! ## 私用: `[0, c]` の点別一致（`M'` と `IncrFirstN shamt N_red`）
`6.8-d1pos-trmax` の private `d1pos_agree_dt` の複製（cross-scope につき
本ファイルで `_pd` 複製、statement 同一）。 -/

private theorem d1pos_agree_pd
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

/-! ## 私用: 幹に沿った行 1 到達（`trunk_le0` の行 1 版） -/

private theorem le1Aux_trunk_pd (M : PS) (hM : TPS M) :
    ∀ fuel c, c ≤ fuel → c ≤ TrMax M → c < Lng M →
      le1Aux M fuel 0 c = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro c hc _ _
      have hc0 : c = 0 := by omega
      subst hc0
      simp [le1Aux]
  | succ fuel ih =>
      intro c hc hcT hcL
      cases c with
      | zero => simp [le1Aux]
      | succ c' =>
          have hstep : nextrel1 M c' (c' + 1) = true := by
            have hh := TrMax_trunk_step M c' hM (by omega)
            simpa [nextR] using hh
          have hih : le1Aux M fuel 0 c' = true :=
            ih c' (by omega) (by omega) (by omega)
          simp only [le1Aux, Bool.or_eq_true, List.any_eq_true,
            Bool.and_eq_true, List.mem_range]
          right
          exact ⟨c', by omega, hstep, hih⟩

/-- 幹の内側 `c ≤ TrMax M` へは行 1 到達 `(1,0) ≤_M (1,c)`。 -/
private theorem trunk_le1_pd (M : PS) (c : ℕ) (hM : TPS M)
    (hc : c ≤ TrMax M) (hcL : c < Lng M) : leR M 1 0 c = true := by
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have haux := le1Aux_trunk_pd M hM (Lng M) c (by omega) hc hcL
  simp [leR, le1, hpos, hcL, haux]

/-! ## CELL-4 UNCAPPED stop（STRICT 変種）
Isabelle `oper_d1pos_ctx_stop_direct_strict` (pss_mechanized.thy:19891)。
strict 閉じ込め `tncstrict` により停止添字が共有接頭辞の内側に入るので、
EASY 枝（`nextR1_boundary_stop_of_prefix` の転送）のみで閉じる。 -/

theorem oper_d1pos_ctx_stop_direct_strict
    (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ)
    (_hNT : TPS N) (_hmono : monoT N = true) (_hstd : STPS N)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (_hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hn1 : 1 ≤ n) (hqn : q < n)
    (_hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (_hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hspan : j1red = j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (_hj1lt : j1' < Lng (oper N n))
    (htncstrict : TrMax (seg N j0red j1red) < j1red - 1 - j0red) :
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false := by
  have hMpT : TPS (seg (oper N n) j0' j1') := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hNpT : TPS (seg N j0red j1red) := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hNppT : TPS (IncrFirstN shamt (seg N j0red j1red)) := by
    simpa [TPS, IncrFirstN_eq_map] using hNpT
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' :=
    length_seg (oper N n) j0' j1'
  have hLNpp : Lng (IncrFirstN shamt (seg N j0red j1red)) =
      j1red + 1 - j0red := by
    simp [IncrFirstN_eq_map]
  have htrShift : TrMax (IncrFirstN shamt (seg N j0red j1red)) =
      TrMax (seg N j0red j1red) :=
    TrMax_IncrFirstN_68 shamt (seg N j0red j1red)
  have hcM : j1red - 1 - j0red < Lng (seg (oper N n) j0' j1') := by omega
  have hcN : j1red - 1 - j0red <
      Lng (IncrFirstN shamt (seg N j0red j1red)) := by omega
  have htNlt : TrMax (IncrFirstN shamt (seg N j0red j1red)) <
      Lng (IncrFirstN shamt (seg N j0red j1red)) - 1 := by omega
  have hagree := d1pos_agree_pd N n q s0 j0red j1red j0' j1' shamt
    hlen hzero hp hi hqn hs0eq hj0'eq hshamt hj1redle hj0j1red hcM
  have hinrange : TrMax (IncrFirstN shamt (seg N j0red j1red)) + 1 ≤
      j1red - 1 - j0red := by omega
  have hstop := nextR1_boundary_stop_of_prefix
    (seg (oper N n) j0' j1') (IncrFirstN shamt (seg N j0red j1red))
    (j1red - 1 - j0red) hMpT hNppT hagree hcM hcN htNlt hinrange
  rw [htrShift] at hstop
  exact hstop

theorem D1pos_oper_d1pos_ctx_stop_direct_strict_holds :
    D1pos_oper_d1pos_ctx_stop_direct_strict := by
  intro N n q s0 j0red j1red j0' j1' shamt
  intro hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hspan hj0j1' hj1lt htncstrict
  exact oper_d1pos_ctx_stop_direct_strict N n q s0 j0red j1red j0' j1' shamt
    hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hspan hj0j1' hj1lt htncstrict

/-! ## CELL-4 CAPPED stop（DIRECT producer）
Isabelle `oper_d1pos_ctx_stop_direct` (pss_mechanized.thy:19581)。
`tnc` は built `oper_d1pos_ctx_tnc_capped`（¬brle の対偶）から。EASY 枝
（`TrMax N_red < c`）は共有接頭辞転送、HARD 枝（`= c`、周期境界）は
境界の行 1 非増加 B3N（`gap`＝行 1 親最小性 ＋ `sub1`＝near-fill 幹の行 1
弱増加）で行 1 ステップを潰す。 -/

theorem oper_d1pos_ctx_stop_direct
    (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ)
    (hNT : TPS N) (hmono : monoT N = true) (hstd : STPS N)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n) (hqn : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hcap : j1red = Lng N - 1)
    (hspan : j1red < j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (hle0M : leR (oper N n) 0 j0' j1' = true)
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false := by
  -- (tnc) 簡約幹の閉じ込め（`_brle_capped` の対偶、built）
  have htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red :=
    oper_d1pos_ctx_tnc_capped N n q j0red j1red s0 j0' j1' shamt
      hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
      hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hnotbrle
  -- 基本事実
  have hMpT : TPS (seg (oper N n) j0' j1') := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hNpT : TPS (seg N j0red j1red) := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hNppT : TPS (IncrFirstN shamt (seg N j0red j1red)) := by
    simpa [TPS, IncrFirstN_eq_map] using hNpT
  have hLMp : Lng (seg (oper N n) j0' j1') = j1' + 1 - j0' :=
    length_seg (oper N n) j0' j1'
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red :=
    length_seg N j0red j1red
  have hLNpp : Lng (IncrFirstN shamt (seg N j0red j1red)) =
      j1red + 1 - j0red := by
    simp [IncrFirstN_eq_map]
  have htrShift : TrMax (IncrFirstN shamt (seg N j0red j1red)) =
      TrMax (seg N j0red j1red) :=
    TrMax_IncrFirstN_68 shamt (seg N j0red j1red)
  have hcM : j1red - 1 - j0red < Lng (seg (oper N n) j0' j1') := by omega
  have hcM1 : j1red - 1 - j0red + 1 < Lng (seg (oper N n) j0' j1') := by
    omega
  have hcN : j1red - 1 - j0red <
      Lng (IncrFirstN shamt (seg N j0red j1red)) := by omega
  have hagree := d1pos_agree_pd N n q s0 j0red j1red j0' j1' shamt
    hlen hzero hp hi hqn hs0eq hj0'eq hshamt hj1redle hj0j1red hcM
  rcases Nat.lt_or_ge (TrMax (seg N j0red j1red)) (j1red - 1 - j0red)
    with heasy | hhard
  · -- EASY: 停止添字が共有接頭辞の内側
    have htNlt : TrMax (IncrFirstN shamt (seg N j0red j1red)) <
        Lng (IncrFirstN shamt (seg N j0red j1red)) - 1 := by omega
    have hinrange : TrMax (IncrFirstN shamt (seg N j0red j1red)) + 1 ≤
        j1red - 1 - j0red := by omega
    have hstop := nextR1_boundary_stop_of_prefix
      (seg (oper N n) j0' j1') (IncrFirstN shamt (seg N j0red j1red))
      (j1red - 1 - j0red) hMpT hNppT hagree hcM hcN htNlt hinrange
    rw [htrShift] at hstop
    exact hstop
  · -- HARD: `TrMax N_red = c`（周期境界）— 行 1 の境界非増加 B3N で停止
    have hteq : TrMax (seg N j0red j1red) = j1red - 1 - j0red := by omega
    have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hsucc : (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
        q * (Lng N - 1 - parent N 1 (Lng N - 1)) +
          (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.succ_mul q _
    have hs0c1 : s0 + (j1red - 1 - j0red + 1) =
        Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hidx_c1 : parent N 1 (Lng N - 1) +
        (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 =
        j0' + (j1red - 1 - j0red + 1) := by omega
    have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
    have hq1n : q + 1 < n := by
      by_contra hcon
      have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    -- 行 1 境界読み出し
    have he1_c1 : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red + 1) =
        entry N 1 (parent N 1 (Lng N - 1)) := by
      have hh := entry_oper_d1pos_one_68 N n (q + 1) 0 hlen hzero hp hi
        hq1n hw
      rw [entry_seg (oper N n) j0' j1' 1 (j1red - 1 - j0red + 1) hcM1,
        ← hidx_c1, hh]
      simp
    have hidx_c : parent N 1 (Lng N - 1) +
        q * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (Lng N - 1 - parent N 1 (Lng N - 1) - 1) =
        j0' + (j1red - 1 - j0red) := by omega
    have he1_c : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red) =
        entry N 1 (Lng N - 2) := by
      have hh := entry_oper_d1pos_one_68 N n q
        (Lng N - 1 - parent N 1 (Lng N - 1) - 1) hlen hzero hp hi hqn
        (by omega)
      rw [entry_seg (oper N n) j0' j1' 1 (j1red - 1 - j0red) hcM,
        ← hidx_c, hh,
        show parent N 1 (Lng N - 1) +
          (Lng N - 1 - parent N 1 (Lng N - 1) - 1) = Lng N - 2 by omega]
    -- 行 1 親関係の H1・最小性
    have hp1 : hasParent N 1 (Lng N - 1) = true := by
      have hh := hp; rw [hi] at hh; exact hh
    have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
    have hdata1 : nextrel1 N (parent N 1 (Lng N - 1)) (Lng N - 1) = true := by
      simpa [nextR] using hnext
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata1
    have hH1 : entry N 1 (parent N 1 (Lng N - 1)) < entry N 1 (Lng N - 1) :=
      hdata1.1.1.2
    -- (gap) `N₁,j₋₂ ≤ N₁,j₀ʳᵉᵈ`
    have hle0red : leR N 0 j0red (Lng N - 1) = true := by
      have hh := oper_d1pos_ctx_period_le0Np N (oper N n) n q s0 j0red
        j1red j0' j1' shamt hlen hzero hp hi hj0lt rfl hle0M hj0j1'
        hj1lt hqn hs0lt hs0eq hj0'eq hshamt hj1redle hj0j1red
        (le_of_lt hspan)
      rwa [hcap] at hh
    have hgap : entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 j0red := by
      by_cases hcase : parent N 1 (Lng N - 1) = j0red
      · rw [hcase]
      · have hlt' : parent N 1 (Lng N - 1) < j0red := by omega
        have hle0' : le0 N j0red (Lng N - 1) = true := by
          simpa [leR] using hle0red
        have hvalley := hdata1.2
        rw [List.all_eq_true] at hvalley
        have hv := hvalley j0red (List.mem_range.mpr (by omega))
        simp [hlt', hle0'] at hv
        omega
    -- (sub1) `N₁,j₀ʳᵉᵈ ≤ N₁,Lng N-2`（near-fill 幹の行 1 弱増加）
    have hle1Np : leR (seg N j0red j1red) 1 0 (j1red - 1 - j0red) = true :=
      trunk_le1_pd (seg N j0red j1red) (j1red - 1 - j0red) hNpT
        (by omega) (by omega)
    have hmono1 := le1_imp_entry1_le (seg N j0red j1red) 0
      (j1red - 1 - j0red) hle1Np
    have he_Np0 : entry (seg N j0red j1red) 1 0 = entry N 1 j0red := by
      have hh := entry_seg N j0red j1red 1 0 (by omega)
      simpa using hh
    have he_Npc : entry (seg N j0red j1red) 1 (j1red - 1 - j0red) =
        entry N 1 (Lng N - 2) := by
      rw [entry_seg N j0red j1red 1 (j1red - 1 - j0red) (by omega),
        show j0red + (j1red - 1 - j0red) = Lng N - 2 by omega]
    have hsub1 : entry N 1 j0red ≤ entry N 1 (Lng N - 2) := by
      rw [← he_Np0, ← he_Npc]
      exact hmono1
    -- B3N → B3 → 停止
    have hB3 : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red + 1) ≤
        entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red) := by
      rw [he1_c1, he1_c]
      omega
    cases hb : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
        (TrMax (seg N j0red j1red) + 1) with
    | false => rfl
    | true =>
        exfalso
        rw [hteq] at hb
        have hdata : nextrel1 (seg (oper N n) j0' j1')
            (j1red - 1 - j0red) (j1red - 1 - j0red + 1) = true := by
          simpa [nextR] using hb
        simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata
        have hstrict := hdata.1.1.2
        omega

theorem D1pos_oper_d1pos_ctx_stop_direct_holds :
    D1pos_oper_d1pos_ctx_stop_direct := by
  intro N n q s0 j0red j1red j0' j1' shamt
  intro hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hle0M hnotbrle
  exact oper_d1pos_ctx_stop_direct N n q s0 j0red j1red j0' j1' shamt
    hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq hs0lt
    hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hle0M hnotbrle

/-! ## CELL-4 fullShift discharger（INTERIOR）
Isabelle `oper_d1pos_notbrle_period_fullShift` (pss_mechanized.thy:18791)。
周期尾部（`j0' ≥ Lng N - 1`）で枝領域がブロック `q0` に収まる（interior）とき、
`M` 側枝ソースはブロック 0 像の `IncrFirstN (q0·δ)` シフトそのもの。
TrEq は built `TrMax_seg_oper_d1pos_eq_span_68`、シフト同一性は
`oper_d1pos_LOW_source_eq`。 -/

theorem oper_d1pos_notbrle_period_fullShift
    (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hMeq : M = oper N n)
    (_hn1 : 1 ≤ n)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hj0pge : Lng N - 1 ≤ j0')
    (hq0def : q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hs0def : s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hj0reddef : j0red = parent N 1 (Lng N - 1) + s0)
    (hj1reddef : j1red = min (j0red + (j1' - j0')) (Lng N - 1))
    (hshamtdef : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1
      (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (_hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (hinterior : j1red < Lng N - 1) :
    seg M (j0' + TrMax (seg M j0' j1') + 1) j1' =
      IncrFirstN shamt
        (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) := by
  subst hMeq
  -- 基本幾何
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1) := by
    rw [hs0def]
    exact Nat.mod_lt _ hw
  have hj0redlt : j0red < Lng N - 1 := by omega
  have hsplit : q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 =
      j0' - parent N 1 (Lng N - 1) := by
    rw [hq0def, hs0def]
    have hdm := Nat.div_add_mod (j0' - parent N 1 (Lng N - 1))
      (Lng N - 1 - parent N 1 (Lng N - 1))
    rw [Nat.mul_comm] at hdm
    omega
  have hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 := by omega
  have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
  have hq0n : q0 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hj0j1red : j0red < j1red := by omega
  have hj1redle : j1red ≤ Lng N - 1 := by omega
  have hspan : j1red = j0red + (j1' - j0') := by omega
  -- TrEq（built keystone）
  have hTrEq : TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) :=
    TrMax_seg_oper_d1pos_eq_span_68 N n q0 s0 j0red j1red j0' j1' shamt
      hNT hlen hzero hp hi hq0n hj0redlt hj0reddef hs0lt hj0'eq hshamtdef
      hj1redle hj0j1red (by omega) hlt hjM htnc hstop
  rw [hTrEq]
  set tN := TrMax (seg N j0red j1red) with htN
  -- ブロック内オフセット: sp = s0 + (tN + 1), e0 = s0 + (j1red - j0red)
  have hsple : s0 + (tN + 1) ≤ s0 + (j1red - j0red) := by omega
  have he0lt : s0 + (j1red - j0red) <
      Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hsrc := oper_d1pos_LOW_source_eq N n q0 (s0 + (tN + 1))
    (s0 + (j1red - j0red)) hlen hzero hp hi hj0lt hq0n hsple he0lt
  calc
    seg (oper N n) (j0' + tN + 1) j1'
        = seg (oper N n)
            (parent N 1 (Lng N - 1) +
              q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + (tN + 1)))
            (parent N 1 (Lng N - 1) +
              q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
              (s0 + (j1red - j0red))) := by
          rw [show j0' + tN + 1 = parent N 1 (Lng N - 1) +
              q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
              (s0 + (tN + 1)) by omega,
            show j1' = parent N 1 (Lng N - 1) +
              q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
              (s0 + (j1red - j0red)) by omega]
    _ = IncrFirstN
          (q0 * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))))
          (seg N (parent N 1 (Lng N - 1) + (s0 + (tN + 1)))
            (parent N 1 (Lng N - 1) + (s0 + (j1red - j0red)))) := hsrc
    _ = IncrFirstN shamt (seg N (j0red + tN + 1) j1red) := by
          rw [show parent N 1 (Lng N - 1) + (s0 + (tN + 1)) =
              j0red + tN + 1 by omega,
            show parent N 1 (Lng N - 1) + (s0 + (j1red - j0red)) =
              j1red by omega,
            ← hshamtdef]

theorem D1pos_oper_d1pos_notbrle_period_fullShift_holds :
    D1pos_oper_d1pos_notbrle_period_fullShift := by
  intro N M n j0' j1' q0 s0 j0red j1red shamt
  intro hNT hlen hzero hp hi hMeq hn1 hlt hjM hj0lt hj0pge hq0def hs0def
    hj0reddef hj1reddef hshamtdef htnc hstop hnotbrle hinterior
  exact oper_d1pos_notbrle_period_fullShift N M n j0' j1' q0 s0 j0red
    j1red shamt hNT hlen hzero hp hi hMeq hn1 hlt hjM hj0lt hj0pge
    hq0def hs0def hj0reddef hj1reddef hshamtdef htnc hstop hnotbrle
    hinterior

/-! ## CELL-4 BOUNDARY-junction discharger
Isabelle `oper_d1pos_notbrle_period_boundary_geom` (pss_mechanized.thy:18956)。
枝領域が周期境界を跨ぐ（`j1red = Lng N - 1`）とき、境界添字
`m = Lng Snside - 1` は `M` 側絶対添字 `A + m = j₋₂ + (q0+1)·w`
（ブロック `q0+1` の先頭）。接頭辞はブロック `q0` 内シフト
（`oper_d1pos_LOW_source_eq`）、境界の行 0 は `dpos` の詰め直しで `+shamt`、
行 1 は `r1le` で非増加、span 上界も同時に返す。 -/

theorem oper_d1pos_notbrle_period_boundary_geom
    (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hMeq : M = oper N n)
    (_hn1 : 1 ≤ n)
    (hlt : j0' < j1')
    (hjM : j1' < Lng M)
    (_hbge : Lng N - 1 ≤ j1')
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hj0pge : Lng N - 1 ≤ j0')
    (hq0def : q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hs0def : s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hj0reddef : j0red = parent N 1 (Lng N - 1) + s0)
    (hj1reddef : j1red = min (j0red + (j1' - j0')) (Lng N - 1))
    (hshamtdef : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1
      (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (hmultiNp : 1 <
      (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length)
    (_hnotbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (hboundary : ¬j1red < Lng N - 1) :
    (seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1) =
      IncrFirstN shamt
        (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
          (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1))) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) =
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) + shamt) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) ≤
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)) ∧
    (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1) := by
  subst hMeq
  -- 基本幾何（fullShift と共通）
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1) := by
    rw [hs0def]
    exact Nat.mod_lt _ hw
  have hj0redlt : j0red < Lng N - 1 := by omega
  have hsplit : q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 =
      j0' - parent N 1 (Lng N - 1) := by
    rw [hq0def, hs0def]
    have hdm := Nat.div_add_mod (j0' - parent N 1 (Lng N - 1))
      (Lng N - 1 - parent N 1 (Lng N - 1))
    rw [Nat.mul_comm] at hdm
    omega
  have hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 := by omega
  have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
  have hq0n : q0 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hj0j1red : j0red < j1red := by omega
  have hj1redle : j1red ≤ Lng N - 1 := by omega
  have hj1redB : j1red = Lng N - 1 := by omega
  have hspan' : j1red ≤ j0red + (j1' - j0') := by omega
  -- TrEq（built keystone）
  have hTrEq : TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) :=
    TrMax_seg_oper_d1pos_eq_span_68 N n q0 s0 j0red j1red j0' j1' shamt
      hNT hlen hzero hp hi hq0n hj0redlt hj0reddef hs0lt hj0'eq hshamtdef
      hj1redle hj0j1red hspan' hlt hjM htnc hstop
  rw [hTrEq]
  set tN := TrMax (seg N j0red j1red) with htN
  -- 枝領域の座標
  have hANle : j0red + tN + 1 ≤ j1red := by omega
  have hLSn : Lng (seg N (j0red + tN + 1) j1red) =
      j1red + 1 - (j0red + tN + 1) := length_seg N (j0red + tN + 1) j1red
  have hSnT : TPS (seg N (j0red + tN + 1) j1red) :=
    TPS_of_P_multi_pd _ hmultiNp
  have hmultiT : multiT (seg N (j0red + tN + 1) j1red) = true :=
    (P_components_multi_iff _ hSnT).mpr hmultiNp
  have hLngSn1 : 1 < Lng (seg N (j0red + tN + 1) j1red) :=
    multi_length_fseq _ hSnT hmultiT
  set m := Lng (seg N (j0red + tN + 1) j1red) - 1 with hmdef
  have hm_val : j0red + tN + 1 + m = j1red := by omega
  have hmpos : 0 < m := by omega
  have hspw : s0 + (tN + 1) + m = Lng N - 1 - parent N 1 (Lng N - 1) := by
    omega
  have hsucc : (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.succ_mul q0 _
  have hAmle : j0' + tN + 1 + m ≤ j1' := by omega
  have hAle : j0' + tN + 1 ≤ j1' := by omega
  have hLS : Lng (seg (oper N n) (j0' + tN + 1) j1') =
      j1' + 1 - (j0' + tN + 1) := length_seg (oper N n) (j0' + tN + 1) j1'
  have hAm : j0' + tN + 1 + m = parent N 1 (Lng N - 1) +
      (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) := by omega
  have hq1n : q0 + 1 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hmLS : m < Lng (seg (oper N n) (j0' + tN + 1) j1') := by omega
  have hmLSn : m < Lng (seg N (j0red + tN + 1) j1red) := by omega
  -- 境界の値読み出し（行 0 / 行 1）
  have hSm0 : entry (seg (oper N n) (j0' + tN + 1) j1') 0 m =
      entry (oper N n) 0 (j0' + tN + 1 + m) :=
    entry_seg (oper N n) (j0' + tN + 1) j1' 0 m hmLS
  have hSm1 : entry (seg (oper N n) (j0' + tN + 1) j1') 1 m =
      entry (oper N n) 1 (j0' + tN + 1 + m) :=
    entry_seg (oper N n) (j0' + tN + 1) j1' 1 m hmLS
  have hSnm0 : entry (seg N (j0red + tN + 1) j1red) 0 m =
      entry N 0 (j0red + tN + 1 + m) :=
    entry_seg N (j0red + tN + 1) j1red 0 m hmLSn
  have hSnm1 : entry (seg N (j0red + tN + 1) j1red) 1 m =
      entry N 1 (j0red + tN + 1 + m) :=
    entry_seg N (j0red + tN + 1) j1red 1 m hmLSn
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (shiftEqB) 接頭辞のブロック内シフト
    have hdb : m - 1 ≤ j1' - (j0' + tN + 1) := by omega
    have hdbN : m - 1 ≤ j1red - (j0red + tN + 1) := by omega
    have hsple : s0 + (tN + 1) ≤ s0 + (tN + 1) + (m - 1) := by omega
    have heplt : s0 + (tN + 1) + (m - 1) <
        Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hsrc := oper_d1pos_LOW_source_eq N n q0 (s0 + (tN + 1))
      (s0 + (tN + 1) + (m - 1)) hlen hzero hp hi hj0lt hq0n hsple heplt
    have e1 : parent N 1 (Lng N - 1) +
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + (tN + 1)) =
        j0' + tN + 1 := by omega
    have e2 : parent N 1 (Lng N - 1) +
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (s0 + (tN + 1) + (m - 1)) = j0' + tN + 1 + (m - 1) := by omega
    have e3 : parent N 1 (Lng N - 1) + (s0 + (tN + 1)) =
        j0red + tN + 1 := by omega
    have e4 : parent N 1 (Lng N - 1) + (s0 + (tN + 1) + (m - 1)) =
        j0red + tN + 1 + (m - 1) := by omega
    rw [e1, e2, e3, e4] at hsrc
    have hL1 := seg_of_seg_68 (oper N n) (j0' + tN + 1) j1' 0 (m - 1)
      hAle hdb
    have hR1 := seg_of_seg_68 N (j0red + tN + 1) j1red 0 (m - 1)
      hANle hdbN
    simp only [Nat.add_zero] at hL1 hR1
    rw [hL1, hR1, hshamtdef]
    exact hsrc
  · -- (boundEq0B) 行 0 接合値
    have hh := entry_oper_d1pos_zero_68 N n (q0 + 1) 0 hlen hzero hp hi
      hq1n hw
    have hdpos : entry N 0 (parent N 1 (Lng N - 1)) <
        entry N 0 (Lng N - 1) := oper_d1pos_ctx_dpos N hp hi hj0lt
    have hsuccd : (q0 + 1) * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) =
        q0 * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) +
        (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) := Nat.succ_mul q0 _
    rw [hSm0, hSnm0,
      show j0red + tN + 1 + m = Lng N - 1 by omega,
      show j0' + tN + 1 + m = parent N 1 (Lng N - 1) +
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 by omega,
      hh, hshamtdef]
    simp only [Nat.add_zero]
    omega
  · -- (boundEq1B) 行 1 接合値
    have hh := entry_oper_d1pos_one_68 N n (q0 + 1) 0 hlen hzero hp hi
      hq1n hw
    have hr1le : entry N 1 (parent N 1 (Lng N - 1)) ≤
        entry N 1 (Lng N - 1) := oper_d1pos_ctx_r1le N hp hi
    rw [hSm1, hSnm1,
      show j0red + tN + 1 + m = Lng N - 1 by omega,
      show j0' + tN + 1 + m = parent N 1 (Lng N - 1) +
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 by omega,
      hh]
    simp only [Nat.add_zero]
    exact hr1le
  · -- (mleSB) span 上界
    omega

theorem D1pos_oper_d1pos_notbrle_period_boundary_geom_holds :
    D1pos_oper_d1pos_notbrle_period_boundary_geom := by
  intro N M n j0' j1' q0 s0 j0red j1red shamt
  intro hNT hlen hzero hp hi hMeq hn1 hlt hjM hbge hj0lt hj0pge hq0def
    hs0def hj0reddef hj1reddef hshamtdef htnc hstop hmultiNp hnotbrle
    hboundary
  exact oper_d1pos_notbrle_period_boundary_geom N M n j0' j1' q0 s0
    j0red j1red shamt hNT hlen hzero hp hi hMeq hn1 hlt hjM hbge hj0lt
    hj0pge hq0def hs0def hj0reddef hj1reddef hshamtdef htnc hstop
    hmultiNp hnotbrle hboundary

end PSS

#print axioms PSS.D1pos_oper_d1pos_ctx_tnc_capped_holds
#print axioms PSS.D1pos_nextR1_boundary_stop_d1pos_holds
#print axioms PSS.oper_d1pos_ctx_period_tncstrict_uncapped
#print axioms PSS.D1pos_oper_d1pos_ctx_period_tncstrict_uncapped_holds
#print axioms PSS.oper_d1pos_anchor_coincide_period_interior
#print axioms PSS.oper_d1pos_anchor_coincide_period_boundary
#print axioms PSS.oper_d1pos_period_row0_unif
#print axioms PSS.oper_d1pos_ctx_period_le0Np
#print axioms PSS.D1pos_oper_d1pos_ctx_period_le0Np_holds
#print axioms PSS.oper_d1pos_ctx_stop_direct_strict
#print axioms PSS.D1pos_oper_d1pos_ctx_stop_direct_strict_holds
#print axioms PSS.oper_d1pos_ctx_stop_direct
#print axioms PSS.D1pos_oper_d1pos_ctx_stop_direct_holds
#print axioms PSS.oper_d1pos_notbrle_period_fullShift
#print axioms PSS.D1pos_oper_d1pos_notbrle_period_fullShift_holds
#print axioms PSS.oper_d1pos_notbrle_period_boundary_geom
#print axioms PSS.D1pos_oper_d1pos_notbrle_period_boundary_geom_holds
