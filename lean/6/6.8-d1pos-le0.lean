import PSS.Defs
import «6».«6.8-standard-slice-Br-descending»

/-!
# §6.8 d1pos ブロック内 le0 ＋ tnc 文脈 brick 層

- 原文: `tmp/content.md` L1422 付近（「命題（標準形の切片と`Br`の降順性の関係）」）の
  証明本体、d1pos（行 1 正）タイル展開の ¬brle 枝を支える le0 到達性 brick 群
- 訂正: A8（タイル係数 off-by-one）適用後の座標系で構成（読み出しは
  `6.8-standard-slice-Br-descending` の `*_68` 群に委譲）
- Isabelle: `oper_d1pos_nextrel0_within` (isabelle/pss_mechanized.thy:12605),
  `oper_d1pos_le0_within` (12702), `oper_d1pos_le0_start_to_start` (12809),
  `oper_d1pos_le0_start_to_any` (12869), `oper_d1pos_seg_le0_boundary` (12927),
  `oper_d1pos_b3n_boundary` (13051), `oper_d1pos_ctx_b3n` (13155),
  `oper_d1pos_ctx_tnc` (13206), `TrMax_seg_oper_d1pos_brle_capped` (13278),
  `oper_d1pos_ctx_tnc_capped` (13593)
- 依存: `6.8-standard-slice-Br-descending`（d1pos 読み出し `*_68`・
  `TrMax_eq_of_prefix_agree_sym_68`・`TrMax_IncrFirstN_68`）、
  `5.1-ancestor-basic`（`ancestor_basic_1`）、`5.1-parent-exists`
  （`parent_exists_3`）、`6.4-mono-slice`（`trunk_le0`・`TrMax_trunk_step`）、
  `6.3-adm-slice`（`leR0_seg_adm`）、`6.5-Red-le-core`（`TrMax_stop_uncond`・
  `entry_IncrFirstN_*`）、`6.2-P-fseq`（`hasParent_next_fseq`・
  `nextR_implies_row0`）— すべて上記 import の推移閉包
- 状態: ✅ 証明済（sorry 0）

Isabelle 版の rtrancl 持ち上げ（`oper_d1pos_nextrel0_within` 経由の帰納）は、
Lean 版では `le0` の値特徴付け（`ancestor_basic_1` ＋ `parent_exists_3`）で
置き換える（8.3-kind0-base-basepoint で確立した勝ち筋）。数値検証:
`python/d1pos_le0_audit.py`（成分<4 長さ≤4 全数＋成分≤8 長さ≤6 乱択、
engine/start_to_any/nextrel0_within いずれも反例 0）。
-/

namespace PSS

/-! ## 補助（le0 の反射律・添字単調性・行 1 親の行 0 到達） -/

private theorem le0Aux_refl_dl (M : PS) (fuel j : ℕ) : le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

private theorem leR0_refl_dl (M : PS) (x : ℕ) (hx : x < Lng M) :
    leR M 0 x x = true := by
  simp [leR, le0, hx, le0Aux_refl_dl]

/-- d1pos 文脈: 行 1 親関係から行 0 到達 `j₀ ≤₀ Lng M - 1` を読む。 -/
private theorem row0_parent_dl (M : PS)
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1) :
    leR M 0 (parent M 1 (Lng M - 1)) (Lng M - 1) = true := by
  have hp1 : hasParent M 1 (Lng M - 1) = true := by
    have := hp; rw [hi] at this; exact this
  have hnext := hasParent_next_fseq M 1 (Lng M - 1) hp1
  exact (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1) hnext).2

/-! ## エンジン（ブロック開始点は右側全域の行 0 真最小） -/

/-- d1pos タイル層で、ブロック `k` の開始点 `j₀+k·w` の行 0 値は、それより右の
（範囲内）全添字で真に増加する。`le0` 系 3 補題すべての値内容。 -/
private theorem entry0_blockmin_dl (M : PS) (n k x : ℕ)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n)
    (hxgt : parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) < x)
    (hxlt : x < Lng (oper M n)) :
    entry (oper M n) 0
        (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
      < entry (oper M n) 0 x := by
  have hMT : TPS M := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng M
    omega
  have hLng := length_oper_d1pos_68 M n hlen hzero hp hi
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hrow0 := row0_parent_dl M hp hi
  have hδ : 0 < entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)) := by
    have := ancestor_basic_1 M (parent M 1 (Lng M - 1)) (Lng M - 1) (Lng M - 1)
      hMT hj0lt (le_refl _) hrow0
    omega
  -- x をブロック座標に分解
  obtain ⟨qx, sx, hsx, hxsplit⟩ :
      ∃ qx sx, sx < Lng M - 1 - parent M 1 (Lng M - 1) ∧
        x = parent M 1 (Lng M - 1) +
          qx * (Lng M - 1 - parent M 1 (Lng M - 1)) + sx := by
    refine ⟨(x - parent M 1 (Lng M - 1)) / (Lng M - 1 - parent M 1 (Lng M - 1)),
      (x - parent M 1 (Lng M - 1)) % (Lng M - 1 - parent M 1 (Lng M - 1)),
      Nat.mod_lt _ hw, ?_⟩
    have hdm := Nat.div_add_mod (x - parent M 1 (Lng M - 1))
      (Lng M - 1 - parent M 1 (Lng M - 1))
    rw [Nat.mul_comm] at hdm
    omega
  have hqxn : qx < n := by
    by_contra hcon
    have hmul : n * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
        qx * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hkqx : k ≤ qx := by
    by_contra hcon
    have hmul : (qx + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (qx + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
        qx * (Lng M - 1 - parent M 1 (Lng M - 1)) +
          (Lng M - 1 - parent M 1 (Lng M - 1)) := by ring
    omega
  -- 両端の値読み出し
  have hbase : entry (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1))) =
      entry M 0 (parent M 1 (Lng M - 1)) +
        k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by
    have hh := entry_oper_d1pos_zero_68 M n k 0 hlen hzero hp hi hkn (by omega)
    simpa using hh
  have hxval : entry (oper M n) 0 x =
      entry M 0 (parent M 1 (Lng M - 1) + sx) +
        qx * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by
    rw [hxsplit]
    exact entry_oper_d1pos_zero_68 M n qx sx hlen hzero hp hi hqxn hsx
  rw [hbase, hxval]
  rcases Nat.eq_or_lt_of_le hkqx with heq | hlt
  · -- 同一ブロック: sx > 0 で行 0 祖先鎖が真増加
    subst heq
    have hsxpos : 0 < sx := by omega
    have hstrict : entry M 0 (parent M 1 (Lng M - 1)) <
        entry M 0 (parent M 1 (Lng M - 1) + sx) :=
      ancestor_basic_1 M (parent M 1 (Lng M - 1))
        (parent M 1 (Lng M - 1) + sx) (Lng M - 1) hMT (by omega) (by omega) hrow0
    omega
  · -- 後続ブロック: δ ≥ 1 の分だけシフトが真増加
    have hmul : (k + 1) * (entry M 0 (Lng M - 1) -
        entry M 0 (parent M 1 (Lng M - 1))) ≤
        qx * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (k + 1) * (entry M 0 (Lng M - 1) -
        entry M 0 (parent M 1 (Lng M - 1))) =
        k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) +
          (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by ring
    have hge : entry M 0 (parent M 1 (Lng M - 1)) ≤
        entry M 0 (parent M 1 (Lng M - 1) + sx) := by
      rcases Nat.eq_zero_or_pos sx with hz | hpos
      · subst hz; simp
      · exact (ancestor_basic_1 M (parent M 1 (Lng M - 1))
          (parent M 1 (Lng M - 1) + sx) (Lng M - 1) hMT (by omega) (by omega)
          hrow0).le
    omega

/-- エンジンの `le0` 形: ブロック `k` の開始点は範囲内の任意の右側添字に行 0 到達。 -/
private theorem le0_reach_dl (M : PS) (n k x : ℕ)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n)
    (hxge : parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤ x)
    (hxlt : x < Lng (oper M n)) :
    leR (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
      x = true := by
  have hopT : TPS (oper M n) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (oper M n)
    omega
  rcases Nat.eq_or_lt_of_le hxge with heq | hlt
  · subst heq
    exact leR0_refl_dl (oper M n) _ hxlt
  · apply parent_exists_3 (oper M n) _ x hopT hlt hxlt
    intro j hbj hjx
    exact entry0_blockmin_dl M n k j hlen hzero hp hi hj0lt hkn hbj (by omega)

/-! ## §6.8 d1pos ブロック内 nextrel0 転送（k < n） -/

/-- 右端点が切片内部に留まる（`y < Lng M - 1`）行 0 の 1 段親子辺は、
ブロック `k` へそのまま持ち上がる。 -/
theorem oper_d1pos_nextrel0_within (M : PS) (n k x y : ℕ)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n)
    (hxge : parent M 1 (Lng M - 1) ≤ x)
    (hylt : y < Lng M - 1)
    (hstep : nextrel0 M x y = true) :
    nextrel0 (oper M n)
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (x - parent M 1 (Lng M - 1)))
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (y - parent M 1 (Lng M - 1))) = true := by
  have hLng := length_oper_d1pos_68 M n hlen hzero hp hi
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hexp : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (Lng M - 1 - parent M 1 (Lng M - 1)) := by ring
  have hmul : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hh := hstep
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hh
  obtain ⟨⟨⟨⟨hxL, hyL⟩, hxy⟩, hval⟩, hvalley⟩ := hh
  -- 値読み出し（両端）
  have hex : entry (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (x - parent M 1 (Lng M - 1))) =
      entry M 0 x +
        k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by
    have hh2 := entry_oper_d1pos_zero_68 M n k (x - parent M 1 (Lng M - 1))
      hlen hzero hp hi hkn (by omega)
    rw [show parent M 1 (Lng M - 1) + (x - parent M 1 (Lng M - 1)) = x by omega]
      at hh2
    exact hh2
  have hey : entry (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (y - parent M 1 (Lng M - 1))) =
      entry M 0 y +
        k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))) := by
    have hh2 := entry_oper_d1pos_zero_68 M n k (y - parent M 1 (Lng M - 1))
      hlen hzero hp hi hkn (by omega)
    rw [show parent M 1 (Lng M - 1) + (y - parent M 1 (Lng M - 1)) = y by omega]
      at hh2
    exact hh2
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩, ?_⟩
  · rw [hex, hey]; omega
  · -- 谷条件: 中間点はすべてブロック k 内
    intro j hj
    by_cases htx : parent M 1 (Lng M - 1) +
        k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (x - parent M 1 (Lng M - 1)) < j
    · obtain ⟨u, hu⟩ : ∃ u, j = parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1)) + u :=
        ⟨j - (parent M 1 (Lng M - 1) +
          k * (Lng M - 1 - parent M 1 (Lng M - 1))), by omega⟩
      subst hu
      have hej : entry (oper M n) 0
          (parent M 1 (Lng M - 1) +
            k * (Lng M - 1 - parent M 1 (Lng M - 1)) + u) =
          entry M 0 (parent M 1 (Lng M - 1) + u) +
            k * (entry M 0 (Lng M - 1) -
              entry M 0 (parent M 1 (Lng M - 1))) :=
        entry_oper_d1pos_zero_68 M n k u hlen hzero hp hi hkn (by omega)
      have hxu : x < parent M 1 (Lng M - 1) + u := by omega
      have hb := hvalley (parent M 1 (Lng M - 1) + u) (by omega)
      simp only [hxu, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at hb
      have hgoal : entry (oper M n) 0
          (parent M 1 (Lng M - 1) +
            k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
            (y - parent M 1 (Lng M - 1))) ≤
          entry (oper M n) 0
            (parent M 1 (Lng M - 1) +
              k * (Lng M - 1 - parent M 1 (Lng M - 1)) + u) := by
        rw [hey, hej]; omega
      simp [hgoal]
    · simp [htx]

/-! ## §6.8 d1pos ブロック内到達（k < n） -/

/-- ブロック `k` の開始点は同ブロック内（オフセット `t < w`）の任意点に行 0 到達。 -/
theorem oper_d1pos_le0_within (M : PS) (n k t : ℕ)
    (_hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n)
    (htw : t < Lng M - 1 - parent M 1 (Lng M - 1)) :
    leR (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) + t)
      = true := by
  have hLng := length_oper_d1pos_68 M n hlen hzero hp hi
  have hexp : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (Lng M - 1 - parent M 1 (Lng M - 1)) := by ring
  have hmul : (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  exact le0_reach_dl M n k _ hlen hzero hp hi hj0lt hkn (by omega) (by omega)

/-! ## §6.8 d1pos ブロック開始点間の推移到達（k ≤ r < n） -/

/-- ブロック `k` の開始点はブロック `r`（`k ≤ r < n`）の開始点に行 0 到達。 -/
theorem oper_d1pos_le0_start_to_start (M : PS) (n k r : ℕ)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkr : k ≤ r)
    (hrn : r < n) :
    leR (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
      (parent M 1 (Lng M - 1) + r * (Lng M - 1 - parent M 1 (Lng M - 1)))
      = true := by
  have hLng := length_oper_d1pos_68 M n hlen hzero hp hi
  have hw : 0 < Lng M - 1 - parent M 1 (Lng M - 1) := by omega
  have hmulkr : k * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
      r * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.mul_le_mul_right _ hkr
  have hexp : (r + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) =
      r * (Lng M - 1 - parent M 1 (Lng M - 1)) +
        (Lng M - 1 - parent M 1 (Lng M - 1)) := by ring
  have hmulrn : (r + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤
      n * (Lng M - 1 - parent M 1 (Lng M - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  exact le0_reach_dl M n k _ hlen hzero hp hi hj0lt (by omega) (by omega)
    (by omega)

/-! ## §6.8 d1pos ブロック開始点から任意の右側添字への到達（k < n） -/

/-- ブロック `k` の開始点は範囲内の任意の `x ≥ j₀+k·w` に行 0 到達。 -/
theorem oper_d1pos_le0_start_to_any (M : PS) (n k x : ℕ)
    (_hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 1)
    (hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hkn : k < n)
    (hxge : parent M 1 (Lng M - 1) +
      k * (Lng M - 1 - parent M 1 (Lng M - 1)) ≤ x)
    (hxlt : x < Lng (oper M n)) :
    leR (oper M n) 0
      (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
      x = true :=
  le0_reach_dl M n k x hlen hzero hp hi hj0lt hkn hxge hxlt

/-! ## §6.8 d1pos capped 切片のブロック境界 le0（境界 brick） -/

/-- capped（`j₁ʳᵉᵈ = Lng N - 1`）・跨り（span 超過）切片で、切片内位置
`c+1 = j₁ʳᵉᵈ - j₀ʳᵉᵈ`（ブロック `q+1` の開始）から切片右端への行 0 到達。 -/
theorem oper_d1pos_seg_le0_boundary
    (N : PS) (n q j0red j1red s0 j0' j1' : ℕ)
    (hNT : TPS N)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hn1 : 1 ≤ n)
    (hqn : q < n)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hcap : j1red = Lng N - 1)
    (hspan : j1red < j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n)) :
    leR (seg (oper N n) j0' j1') 0 (j1red - 1 - j0red + 1)
      (Lng (seg (oper N n) j0' j1') - 1) = true := by
  have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hj0j1red : j0red < j1red := by omega
  -- 切片から (oper N n) レベルへ転送
  have htrans := leR0_seg_adm (oper N n) j0' j1' (j1red - 1 - j0red + 1)
    (Lng (seg (oper N n) j0' j1') - 1) (by omega) hj1lt
    (by rw [length_seg]; omega) (by rw [length_seg]; omega)
  rw [htrans]
  -- 添字の同定
  have hidx_c1 : j0' + (j1red - 1 - j0red + 1) =
      parent N 1 (Lng N - 1) +
        (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
    have hexp : (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
        q * (Lng N - 1 - parent N 1 (Lng N - 1)) +
          (Lng N - 1 - parent N 1 (Lng N - 1)) := by ring
    omega
  have hidx_end : j0' + (Lng (seg (oper N n) j0' j1') - 1) = j1' := by
    rw [length_seg]; omega
  rw [hidx_c1, hidx_end]
  -- ブロック q+1 の開始 ≤ j1'、q+1 < n
  have hstart_le : parent N 1 (Lng N - 1) +
      (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤ j1' := by
    have h1 : j1red - 1 - j0red + 1 ≤ Lng (seg (oper N n) j0' j1') - 1 := by
      rw [length_seg]; omega
    omega
  have hq1n : q + 1 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  exact oper_d1pos_le0_start_to_any N n (q + 1) j1' hNT hlen hzero hp hi
    hj0lt hq1n hstart_le hj1lt

/-! ## §6.8 d1pos N 側境界不等式 B3N（fill 条件付き） -/

/-- `N` 参照簡約切片 `seg N a (Lng N - 1)` が満杯幹（fill）なら、行 1 親は
直前列の行 1 値を超えない: `entry N 1 j₋₂ ≤ entry N 1 (Lng N - 2)`。 -/
theorem oper_d1pos_b3n_boundary (N : PS) (a : ℕ)
    (_hNT : TPS N)
    (hlen : 1 < Lng N)
    (hp1 : hasParent N 1 (Lng N - 1) = true)
    (ha : a < Lng N - 1)
    (hfill : TrMax (seg N a (Lng N - 1)) = Lng (seg N a (Lng N - 1)) - 1) :
    entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 (Lng N - 2) := by
  -- 行 1 親関係の展開
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
  have hdata : nextrel1 N (parent N 1 (Lng N - 1)) (Lng N - 1) = true := by
    simpa [nextR] using hnext
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata
  have hjm2lt : parent N 1 (Lng N - 1) < Lng N - 1 := hdata.1.1.1.2
  have hH1 : entry N 1 (parent N 1 (Lng N - 1)) < entry N 1 (Lng N - 1) :=
    hdata.1.1.2
  -- 満杯幹の最終段 → 切片 le0 → N 転送
  have hSNT : TPS (seg N a (Lng N - 1)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg N a (Lng N - 1))
    rw [length_seg]; omega
  have htr := trunk_le0 (seg N a (Lng N - 1))
    (Lng (seg N a (Lng N - 1)) - 2) (Lng (seg N a (Lng N - 1)) - 1)
    hSNT (by omega) (by omega)
  have htrans := leR0_seg_adm N a (Lng N - 1)
    (Lng (seg N a (Lng N - 1)) - 2) (Lng (seg N a (Lng N - 1)) - 1)
    (by omega) (by omega)
    (by rw [length_seg]; omega) (by rw [length_seg]; omega)
  rw [htrans] at htr
  rw [show a + (Lng (seg N a (Lng N - 1)) - 2) = Lng N - 2 by
        rw [length_seg]; omega,
      show a + (Lng (seg N a (Lng N - 1)) - 1) = Lng N - 1 by
        rw [length_seg]; omega] at htr
  -- 合成: 反射ケースと最小性ケース
  by_cases hcase : parent N 1 (Lng N - 1) = Lng N - 2
  · rw [hcase]
  · have hjm2s : parent N 1 (Lng N - 1) < Lng N - 2 := by omega
    have hle0' : le0 N (Lng N - 2) (Lng N - 1) = true := by
      simpa [leR] using htr
    have hvalley := hdata.2
    rw [List.all_eq_true] at hvalley
    have hv := hvalley (Lng N - 2) (List.mem_range.mpr (by omega))
    simp [hjm2s, hle0'] at hv
    omega

/-! ## §6.8 d1pos B3N の keystone 形 -/

/-- keystone `le0 N (Lng N - 2) (Lng N - 1)`（最終列に到達する最終幹段）から
B3N を導く核。 -/
theorem oper_d1pos_ctx_b3n (N : PS)
    (hp1 : hasParent N 1 (Lng N - 1) = true)
    (hlen : 1 < Lng N)
    (hkey : leR N 0 (Lng N - 2) (Lng N - 1) = true) :
    entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 (Lng N - 2) := by
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
  have hdata : nextrel1 N (parent N 1 (Lng N - 1)) (Lng N - 1) = true := by
    simpa [nextR] using hnext
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata
  have hjm2lt : parent N 1 (Lng N - 1) < Lng N - 1 := hdata.1.1.1.2
  have hH1 : entry N 1 (parent N 1 (Lng N - 1)) < entry N 1 (Lng N - 1) :=
    hdata.1.1.2
  by_cases hcase : parent N 1 (Lng N - 1) = Lng N - 2
  · rw [hcase]
  · have hjm2s : parent N 1 (Lng N - 1) < Lng N - 2 := by omega
    have hle0' : le0 N (Lng N - 2) (Lng N - 1) = true := by
      simpa [leR] using hkey
    have hvalley := hdata.2
    rw [List.all_eq_true] at hvalley
    have hv := hvalley (Lng N - 2) (List.mem_range.mpr (by omega))
    simp [hjm2s, hle0'] at hv
    omega

/-! ## §6.8 d1pos B3 からの厳格幹閉じ込め（fill-free） -/

/-- 境界の行 1 非増加 B3 ＋ 境界 le0 ＋ ¬brle 証人から、厳格閉じ込め
`TrMax M' + 1 ≤ c`。 -/
theorem oper_d1pos_ctx_tnc (Mp : PS) (c : ℕ)
    (hMpT : TPS Mp)
    (hB3 : entry Mp 1 (c + 1) ≤ entry Mp 1 c)
    (hbdry : leR Mp 0 (c + 1) (Lng Mp - 1) = true)
    (hnotle : ¬leR Mp 0 (TrMax Mp + 1) (Lng Mp - 1) = true) :
    TrMax Mp + 1 ≤ c := by
  -- 境界停止: 幹段 c → c+1 は立たない
  have htnc : TrMax Mp ≤ c := by
    by_contra hcon
    have hstep := TrMax_trunk_step Mp c hMpT (by omega)
    have hdata : nextrel1 Mp c (c + 1) = true := by
      simpa [nextR] using hstep
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata
    have := hdata.1.1.2
    omega
  -- 厳格 2: TrMax Mp = c は境界 le0 が notle と矛盾
  have hne : TrMax Mp ≠ c := by
    intro heq
    apply hnotle
    rw [heq]
    exact hbdry
  omega

/-! ## §6.8 d1pos brle 結論 closer（capped 形） -/

private theorem getD_entry_dl (X : PS) (s : ℕ) (hs : s < Lng X) :
    X.getD s (0, 0) = (entry X 0 s, entry X 1 s) := by
  rw [getD_eq_getElem_idx X (0, 0) hs]
  cases hx : X[s] with
  | mk a b => simp [entry, List.getElem?_eq_getElem hs, hx]

/-- capped（min-cap 有効）跨り切片: `N` 参照簡約切片が満杯幹（fill）なら
`M' = seg (N[n]) j₀' j₁'` は brle（単一成分）。 -/
theorem TrMax_seg_oper_d1pos_brle_capped
    (N : PS) (n q j0red j1red s0 j0' j1' shamt : ℕ)
    (hNT : TPS N) (_hmono : monoT N = true) (_hstd : STPS N)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hqn : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (_hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hcap : j1red = Lng N - 1)
    (hspan : j1red < j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (hfill : TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1) :
    TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true := by
  by_contra hcon
  obtain ⟨hndisj, hnotle⟩ := not_or.mp hcon
  have hLng := length_oper_d1pos_68 N n hlen hzero hp hi
  have hw : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hMpT : TPS (seg (oper N n) j0' j1') := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg (oper N n) j0' j1')
    rw [length_seg]; omega
  have htb := TrMax_bound _ hMpT
  -- c = j1red - 1 - j0red の範囲
  have hcM1 : j1red - 1 - j0red + 1 < Lng (seg (oper N n) j0' j1') := by
    rw [length_seg]; omega
  have hcM : j1red - 1 - j0red < Lng (seg (oper N n) j0' j1') := by omega
  -- ブロック境界の添字同定と q+1 < n
  have hidx_c1 : j0' + (j1red - 1 - j0red + 1) =
      parent N 1 (Lng N - 1) +
        (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
    have hexp : (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
        q * (Lng N - 1 - parent N 1 (Lng N - 1)) +
          (Lng N - 1 - parent N 1 (Lng N - 1)) := by ring
    omega
  have hq1n : q + 1 < n := by
    by_contra hcon2
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have hcle : j0' + (j1red - 1 - j0red + 1) ≤ j1' := by
      have := hcM1
      rw [length_seg] at this
      omega
    omega
  -- 行 1 の境界値同定
  have he1_c1 : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red + 1) =
      entry N 1 (parent N 1 (Lng N - 1)) := by
    rw [entry_seg (oper N n) j0' j1' 1 (j1red - 1 - j0red + 1) hcM1, hidx_c1]
    have hh := entry_oper_d1pos_one_68 N n (q + 1) 0 hlen hzero hp hi hq1n
      (by omega)
    simpa using hh
  have hidx_c : j0' + (j1red - 1 - j0red) =
      parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (Lng N - 1 - parent N 1 (Lng N - 1) - 1) := by
    omega
  have he1_c : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red) =
      entry N 1 (Lng N - 2) := by
    rw [entry_seg (oper N n) j0' j1' 1 (j1red - 1 - j0red) hcM, hidx_c]
    rw [entry_oper_d1pos_one_68 N n q
      (Lng N - 1 - parent N 1 (Lng N - 1) - 1) hlen hzero hp hi hqn (by omega)]
    rw [show parent N 1 (Lng N - 1) +
      (Lng N - 1 - parent N 1 (Lng N - 1) - 1) = Lng N - 2 by omega]
  -- B3N（fill から）→ B3
  have hp1 : hasParent N 1 (Lng N - 1) = true := by
    have := hp; rw [hi] at this; exact this
  have hfill' : TrMax (seg N j0red (Lng N - 1)) =
      Lng (seg N j0red (Lng N - 1)) - 1 := by
    rw [← hcap]; exact hfill
  have hB3N := oper_d1pos_b3n_boundary N j0red hNT hlen hp1 (by omega) hfill'
  have hB3 : entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red + 1) ≤
      entry (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red) := by
    rw [he1_c1, he1_c]; exact hB3N
  -- 境界停止 → 閉じ込め TrMax M' ≤ c
  have hstop_c : nextR (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red)
      (j1red - 1 - j0red + 1) = false := by
    cases hb : nextR (seg (oper N n) j0' j1') 1 (j1red - 1 - j0red)
        (j1red - 1 - j0red + 1) with
    | false => rfl
    | true =>
        have hdata : nextrel1 (seg (oper N n) j0' j1') (j1red - 1 - j0red)
            (j1red - 1 - j0red + 1) = true := by
          simpa [nextR] using hb
        simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hdata
        have := hdata.1.1.2
        omega
  have htncM : TrMax (seg (oper N n) j0' j1') ≤ j1red - 1 - j0red := by
    by_contra hcon2
    have hstep := TrMax_trunk_step _ (j1red - 1 - j0red) hMpT (by omega)
    rw [hstop_c] at hstep
    exact Bool.false_ne_true hstep
  -- 厳格 2: TrMax M' + 1 ≤ c（境界 le0 と notle）
  have htncM1 : TrMax (seg (oper N n) j0' j1') + 1 ≤ j1red - 1 - j0red := by
    have hne : TrMax (seg (oper N n) j0' j1') ≠ j1red - 1 - j0red := by
      intro heq
      apply hnotle
      have hbdry := oper_d1pos_seg_le0_boundary N n q j0red j1red s0 j0' j1'
        hNT hlen hzero hp hi hj0lt hn1 hqn hs0eq hs0lt hj0'eq hcap hspan
        hj0j1' hj1lt
      rw [← heq] at hbdry
      exact hbdry
    omega
  -- [0, c] の点別一致（M' と IncrFirstN shamt N_red）
  have hLNpp : Lng (IncrFirstN shamt (seg N j0red j1red)) =
      j1red + 1 - j0red := by
    simp [IncrFirstN_eq_map]
  have hcN : j1red - 1 - j0red < Lng (IncrFirstN shamt (seg N j0red j1red)) := by
    rw [hLNpp]; omega
  have hagree : ∀ s, s ≤ j1red - 1 - j0red →
      (seg (oper N n) j0' j1').getD s (0, 0) =
        (IncrFirstN shamt (seg N j0red j1red)).getD s (0, 0) := by
    intro s hs
    have hsM : s < Lng (seg (oper N n) j0' j1') := by omega
    have hsN : s < Lng (seg N j0red j1red) := by rw [length_seg]; omega
    have hsNpp : s < Lng (IncrFirstN shamt (seg N j0red j1red)) := by
      rw [hLNpp]; omega
    rw [getD_entry_dl _ s hsM, getD_entry_dl _ s hsNpp]
    have h0M : entry (seg (oper N n) j0' j1') 0 s =
        entry N 0 (j0red + s) + shamt := by
      rw [entry_seg (oper N n) j0' j1' 0 s hsM,
        show j0' + s = parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + s) by omega,
        entry_oper_d1pos_zero_68 N n q (s0 + s) hlen hzero hp hi hqn (by omega),
        hshamt,
        show parent N 1 (Lng N - 1) + (s0 + s) = j0red + s by omega]
    have h1M : entry (seg (oper N n) j0' j1') 1 s =
        entry N 1 (j0red + s) := by
      rw [entry_seg (oper N n) j0' j1' 1 s hsM,
        show j0' + s = parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + s) by omega,
        entry_oper_d1pos_one_68 N n q (s0 + s) hlen hzero hp hi hqn (by omega),
        show parent N 1 (Lng N - 1) + (s0 + s) = j0red + s by omega]
    have h0N : entry (IncrFirstN shamt (seg N j0red j1red)) 0 s =
        entry N 0 (j0red + s) + shamt := by
      rw [entry_IncrFirstN_zero shamt (seg N j0red j1red) s hsN,
        entry_seg N j0red j1red 0 s hsN]
    have h1N : entry (IncrFirstN shamt (seg N j0red j1red)) 1 s =
        entry N 1 (j0red + s) := by
      rw [entry_IncrFirstN_one shamt (seg N j0red j1red) s,
        entry_seg N j0red j1red 1 s hsN]
    rw [h0M, h1M, h0N, h1N]
  -- SYM 転送: TrMax M' = TrMax N_red、fill と矛盾
  have hNppT : TPS (IncrFirstN shamt (seg N j0red j1red)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (IncrFirstN shamt (seg N j0red j1red))
    rw [hLNpp]; omega
  have hstopM := TrMax_stop_uncond _ hMpT
  have hTrEq := TrMax_eq_of_prefix_agree_sym_68 (seg (oper N n) j0' j1')
    (IncrFirstN shamt (seg N j0red j1red)) (j1red - 1 - j0red)
    hMpT hNppT hagree hcM hcN htncM1 hstopM
  rw [TrMax_IncrFirstN_68 shamt (seg N j0red j1red)] at hTrEq
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red :=
    length_seg N j0red j1red
  omega

/-! ## §6.8 d1pos capped 幹閉じ込め tnc（brle_capped の対偶） -/

/-- ¬brle（跨り切片の証人）から `N` 参照簡約切片の幹閉じ込め
`TrMax N_red ≤ j₁ʳᵉᵈ - 1 - j₀ʳᵉᵈ`。 -/
theorem oper_d1pos_ctx_tnc_capped
    (N : PS) (n q j0red j1red s0 j0' j1' shamt : ℕ)
    (hNT : TPS N) (hmono : monoT N = true) (hstd : STPS N)
    (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hqn : q < n)
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
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0
        (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red := by
  -- brle_capped の対偶: ¬brle は fill（満杯幹）を排除
  have hnotfill : TrMax (seg N j0red j1red) ≠ Lng (seg N j0red j1red) - 1 := by
    intro hfill
    exact hnotbrle (TrMax_seg_oper_d1pos_brle_capped N n q j0red j1red s0
      j0' j1' shamt hNT hmono hstd hlen hzero hp hi hj0lt hn1 hqn hs0w hs0eq
      hs0lt hj0'eq hshamt hj1redle hj0j1red hcap hspan hj0j1' hj1lt hfill)
  have hNpT : TPS (seg N j0red j1red) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg N j0red j1red)
    rw [length_seg]; omega
  have htb := TrMax_bound _ hNpT
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red :=
    length_seg N j0red j1red
  omega

#print axioms oper_d1pos_nextrel0_within
#print axioms oper_d1pos_le0_within
#print axioms oper_d1pos_le0_start_to_start
#print axioms oper_d1pos_le0_start_to_any
#print axioms oper_d1pos_seg_le0_boundary
#print axioms oper_d1pos_b3n_boundary
#print axioms oper_d1pos_ctx_b3n
#print axioms oper_d1pos_ctx_tnc
#print axioms TrMax_seg_oper_d1pos_brle_capped
#print axioms oper_d1pos_ctx_tnc_capped

end PSS
