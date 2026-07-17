import «6».«6.5-Red-Pred-commute»
import «6».«6.6-reduced-slice»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Mark-rightmost1»
import «7».«7.4-RightAnces-zeroT»
import «7».«7.4-RightNodes-Mark»
import «7».«7.4-RightAnces-RightNodes»
import «7».«7.4-Mark-Trans-repr»

/-!
# §7.4 `Mark M m ≠ Trans M`（`m > 0`）・`RightNodes (Trans M)` の長さ下界・`Mark` の順序保存

前 2 命題は `8.2-subexpr-admpos-engine.lean` に private 複製（接尾辞 `_ape`）として
先行実装されていたものを、本来の §7 の住所へ昇格させた（statement・proof とも同一。
親エージェントが後段で private 複製を削除する）。第 3 命題 `Mark_order` は、その
昇格で `m₀ = 0` 分岐が開通したことにより本ファイルで新規に閉じた。

- Isabelle (`isabelle/layerB/pss_wip.thy`) との対応:
  - `Trans_mono_RN_ge2` ← 同名 (9011)
  - `Mark0_ne_Mark`     ← 同名 (9636)
  - `Mark_order`        ← `m_7_4_Mark_order` (9707)  ※**訂正 A19**（下記）
  - private ブリック（いずれも Isabelle からの移植、接尾辞 `_m0`）:
    - `MarkedB_antisym_m0`               ← `MarkedB_antisym` (9465)
    - `RightNodes_seg_len_strict_mono_m0` ← `RightNodes_seg_len_strict_mono` (9490)
    - `Mark_interior_RN_ge2_m0`          ← `Mark_interior_RN_ge2` (9553)
    - `Mark_distinct_m0`                 ← `Mark_distinct` (9586)
    - `seg_getElem_m0` / `seg_of_seg_zero_m0`（Isabelle の `seg_0_eq_take`＋`take_take` 相当）
  - Isabelle の `M ∈ RT_PS ∩ PT_PS` は `(hR : RTPS M) (hmono : monoT M = true)` に展開。

## 訂正 A19（`Mark_order`）

原文 §7.4 の結論 (2) は `(Mark(M,m₁), Mark(M,m₀)) ∈ T_B^Marked` だが、`T_B^Marked` は
(whole, block) 規約であり `m` が小さいほど像が大きい（`Mark(M,0) = Trans M` が最大）ため
**対が逆で偽**（経験的確認 0/249）。本ファイルは訂正後の向き
`(Mark M m₀, Mark M m₁) ∈ MarkedB`（249/249）を証明している。

## 証明の構造（Isabelle からの短縮）

`Trans_mono_RN_ge2` は Isabelle では `Trans.psimps` を手展開して `c₂` の全分岐を
再構成する（~250 行）が、Lean には `RightAncesAux_RTPS_equation`（`RightAnces` の
再帰式）と `RightAncesAux_eq_RightNodes_Trans`（`RightAnces = RightNodes ∘ Trans`）が
あるので、再帰式を**一段ほどくだけ**で済む。単項簡約列（長さ > 1）の
`RightNodes (Trans M)` は「祖先ブロック `a`（非空）＋ 末尾 1〜2 成分」なので長さ ≥ 2。
祖先ブロックの非空性は `zeroT` 分岐の両側で個別に出す（`zeroT` 側は `[0]`、
非 `zeroT` 側は `RightNodes_eq_nil_iff` ＋ `Trans_preserves_zeroT` の対偶）。

`Mark0_ne_Mark` は 2 ケース。**両方が load-bearing**（内部ケースだけでは足りない）:
- 内部 (`m < Lng M - 1`): `RightNodes_Mark`（§7.4, A47 形）の 3 分割で
  `RightNodes (Trans M) = a₀ ++ …`, `RightNodes (Mark M m) = …` を得て、
  始切片 `seg M 0 m`（長さ `m+1 ≥ 2` の単項簡約列）に `Trans_mono_RN_ge2` を
  適用して `a₀ ≠ []` を出し、長さ比較で矛盾。
- 右端 (`m = Lng M - 1`): `Mark_rightmost1_forward` で `Mark M m = D_{M₁,ₘ} 0` と
  なり `RightNodes` 長 1 < 2 で矛盾。

## 依存（主要）
- `RightAncesAux_RTPS_equation` / `RightAncesAux_eq_RightNodes_Trans`（7.4-RightAnces-RightNodes）
- `RightNodes_Mark` / `Mark_leftend_form_proper`（7.4-RightNodes-Mark、訂正 A47 形）
- `RightNodes_eq_nil_iff`（7.4-RightAnces-zeroT）
- `Mark_rightmost1_forward` / `Mark_tail_nonzero` / `Mark_MarkedB_nest`（7.3-Mark-rightmost1、訂正 A17）
- `Mark_zero_eq_Trans`（7.4-Mark-Trans-repr）
- `Trans_preserves_zeroT`（7.3-Trans-preserves-zeroT）
- `RTPS_initial_slice`（6.6-reduced-slice）, `marked_slice`（6.3-marked-slice）
- `mono_hasParent_row0`（6.6-P-condAB）, `parent_lt_of_hasParent`（6.6-condAB-coeff）
- `Adm_le`（6.3-admof-slice）, `RTPS_TPS`（6.5-Red-preserves-monoT）
- `entry_seg` / `length_seg`（6.2-mono-ancestor-slice）, `flatBT_injective`（PSS/Flat）

## 罠（本ファイルで実際に踏んだもの）
- `rw [h] at hq` は `X = X` 形の**両辺**を書き換える → 2 表示の突き合わせは
  `congrArg List.length (hT0.symm.trans hT1)` で行う。
- `simp only [entry_seg M a b i (0 + i) hic, Nat.zero_add]` は `Nat.zero_add` が先に
  `0 + i` を潰して `entry_seg` のパターンが不一致になる → `entry_seg` は添字 `i` の形で渡す。

## 状態: green（sorry 0、仮定 0、axioms は 3 種のみ）
-/

namespace PSS

/-- Isabelle `Trans_mono_RN_ge2` (layerB/pss_wip.thy 9011)。

単項簡約列 `M`（`Lng M > 1`）の `RightNodes (Trans M)` は長さ 2 以上。 -/
theorem Trans_mono_RN_ge2 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M) :
    2 ≤ (RightNodes (Trans M)).length := by
  have hM : TPS M := RTPS_TPS M hR
  have hEq : RightAncesAux (Lng M) M = RightNodes (Trans M) :=
    RightAncesAux_eq_RightNodes_Trans M (Lng M) hR (le_refl _)
  have hf : Lng M = (Lng M - 1) + 1 := by omega
  -- 祖先ブロック `a` の非空性（`if` の分解より先に用意する）
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have := parent_lt_of_hasParent M 0 (Lng M - 1) hp
    omega
  have hjmlt : Adm M (parent M 0 (Lng M - 1)) < Lng M - 1 := by
    have := Adm_le M (parent M 0 (Lng M - 1))
    omega
  have ha : 1 ≤ (if zeroT (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) = true then [0]
      else RightAncesAux (Lng M - 1)
        (seg M 0 (Adm M (parent M 0 (Lng M - 1))))).length := by
    by_cases hza : zeroT (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) = true
    · rw [if_pos hza]; simp
    · rw [if_neg hza]
      have hsR : RTPS (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) :=
        RTPS_initial_slice M _ hR (by omega)
      have hsT : TPS (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) := RTPS_TPS _ hsR
      rw [RightAncesAux_eq_RightNodes_Trans _ (Lng M - 1) hsR (by simp; omega)]
      have hne : RightNodes (Trans (seg M 0 (Adm M (parent M 0 (Lng M - 1))))) ≠ [] := by
        rw [Ne, RightNodes_eq_nil_iff]
        intro hzz
        exact hza ((Trans_preserves_zeroT _ hsT).2 hzz)
      exact List.length_pos_of_ne_nil hne
  rw [← hEq, hf, RightAncesAux_RTPS_equation (Lng M - 1) M hR]
  simp only [hmono, if_true]
  rw [if_neg (show ¬((Lng M - 1 == 0) = true) from by
    simp only [beq_iff_eq]; omega)]
  by_cases hz : zeroT (Pred M) = true
  · rw [if_pos hz]; simp
  · rw [if_neg hz]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

/-- Isabelle `Mark0_ne_Mark` (layerB/pss_wip.thy 9636)。

簡約列 `M` の基点 `m > 0` について `Mark M m ≠ Trans M`。 -/
theorem Mark0_ne_Mark (M : PS) (m : ℕ) (hR : RTPS M)
    (hmk0 : Marked M 0) (hmk : Marked M m) (hpos : 0 < m) :
    Mark M m ≠ Trans M := by
  have hM : TPS M := RTPS_TPS M hR
  have hmlt : m < Lng M := by
    have h : le0 M m (Lng M - 1) = true := hmk.2.2
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hlen : 1 < Lng M := by omega
  have hnz : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    left; omega
  have hmono : monoT M = true := by
    simp only [monoT, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hnz, hmk0.2.2⟩
  have hRN2 : 2 ≤ (RightNodes (Trans M)).length :=
    Trans_mono_RN_ge2 M hR hmono hlen
  intro heq
  by_cases hint : m < Lng M - 1
  · obtain ⟨a₀, a₁, hRT, hSseg, hRMark⟩ := RightNodes_Mark M m hmk hR hpos hint
    -- 始切片 `seg M 0 m` は長さ `m+1 ≥ 2` の単項簡約列
    have hsR : RTPS (seg M 0 m) := RTPS_initial_slice M m hR (by omega)
    have hsLen : Lng (seg M 0 m) = m + 1 := by simp
    have hsmk0 : Marked (seg M 0 m) 0 := by
      have := marked_slice M 0 0 m hmk0 (le_refl _) (by omega) (by omega)
      simpa using this
    have hsnz : zeroT (seg M 0 m) = false := by
      simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      left; omega
    have hsmono : monoT (seg M 0 m) = true := by
      simp only [monoT, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hsnz, hsmk0.2.2⟩
    have hsRN2 : 2 ≤ (RightNodes (Trans (seg M 0 m))).length :=
      Trans_mono_RN_ge2 _ hsR hsmono (by omega)
    rw [hSseg] at hsRN2
    simp only [List.length_append, List.length_cons, List.length_nil] at hsRN2
    -- `Mark M m = Trans M` は `a₀ = []` を強いる
    have hlenEq : (RightNodes (Mark M m)).length = (RightNodes (Trans M)).length := by
      rw [heq]
    rw [hRT, hRMark] at hlenEq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlenEq
    omega
  · -- 右端: `m = Lng M - 1`（**この分岐は load-bearing**）
    have hmeq : m = Lng M - 1 := by omega
    have hmk1 : Mark M m = Dprin (entry M 1 m : ℕ∞) BZero := by
      rw [hmeq]; exact Mark_rightmost1_forward M hR hnz
    rw [heq] at hmk1
    rw [hmk1] at hRN2
    simp at hRN2

/-! ## `Mark_order`（§7.4 命題、訂正 A19）に要る private ブリック

`Mark0_ne_Mark` が落ちたことで A19 の `m0 = 0` 分岐が開通したので、ここで仕上げる。
Isabelle 連鎖（`isabelle/layerB/pss_wip.thy`）:
`MarkedB_antisym` (9465) → `RightNodes_seg_len_strict_mono` (9490) →
`Mark_interior_RN_ge2` (9553) → `Mark_distinct` (9586) → `m_7_4_Mark_order` (9707)。 -/

private theorem seg_getElem_m0 (M : PS) (a b i : ℕ) (hi : i < Lng (seg M a b)) :
    (seg M a b)[i] = (entry M 0 (a + i), entry M 1 (a + i)) := by
  simp [seg, List.getElem_range']

/-- 始切片の始切片は始切片。Isabelle は `seg_0_eq_take` ＋ `take_take` で処理する。 -/
private theorem seg_of_seg_zero_m0 (M : PS) (m0 m1 : ℕ) (h : m0 ≤ m1) :
    seg (seg M 0 m1) 0 m0 = seg M 0 m0 := by
  apply List.ext_getElem
  · simp only [length_seg]
  · intro i hiL hiR
    have hic : i < Lng (seg M 0 m1) := by
      simp only [length_seg] at hiL ⊢; omega
    -- `rw` は RHS の `entry M _ i` にも当たるので `simp only` で一括正規化する。
    -- `entry_seg` は添字 `i` の形で渡す（`Nat.zero_add` が先に `0 + i` を潰すため）。
    simp only [seg_getElem_m0 (seg M 0 m1) 0 m0 i hiL, seg_getElem_m0 M 0 m0 i hiR,
      entry_seg M 0 m1 0 i hic, entry_seg M 0 m1 1 i hic, Nat.zero_add]

/-- Isabelle `MarkedB_antisym` (layerB 9465)。両向きの入れ子は長さ勘定で
`s = b = []` を強制し、`flatBT_injective` で項の一致に落ちる。 -/
private theorem MarkedB_antisym_m0 {t c : BT} (h1 : (t, c) ∈ MarkedB)
    (h2 : (c, t) ∈ MarkedB) : t = c := by
  simp only [MarkedB, Set.mem_setOf_eq, scb_decomp] at h1 h2
  obtain ⟨s, b, e1, -, -⟩ := h1
  obtain ⟨s', b', e2, -, -⟩ := h2
  have l1 := congrArg List.length e1
  have l2 := congrArg List.length e2
  simp only [List.length_append] at l1 l2
  have hs : s = [] := by
    apply List.eq_nil_of_length_eq_zero; omega
  have hb : b = [] := by
    apply List.eq_nil_of_length_eq_zero; omega
  refine flatBT_injective ?_
  rw [e1, hs, hb]; simp

/-- Isabelle `Mark_interior_RN_ge2` (layerB 9553)。内部基点の像は
`D_{M₁,ₘ} t`（`Mark_leftend_form_proper`）で `t ≠ 0_B`（`Mark_tail_nonzero`）。 -/
private theorem Mark_interior_RN_ge2_m0 (M : PS) (m : ℕ) (hR : RTPS M)
    (hm : Marked M m) (hmlt : m < Lng M - 1) :
    2 ≤ (RightNodes (Mark M m)).length := by
  obtain ⟨t, hmk⟩ := Mark_leftend_form_proper M m hm hR hmlt
  have htne : t ≠ BZero := by
    intro h
    exact Mark_tail_nonzero M m hm hR hmlt (by rw [hmk, h])
  have hrn : RightNodes t ≠ [] := by
    rw [Ne, RightNodes_eq_nil_iff]; exact htne
  have hpos := List.length_pos_of_ne_nil hrn
  rw [hmk, RightNodes_Dprin]
  simp only [List.length_cons]
  omega

/-- Isabelle `RightNodes_seg_len_strict_mono` (layerB 9490)。
`N = seg M 0 m1` の列 `m0` に `RightNodes_Mark` を当てると
`RightNodes (Trans (seg M 0 m0))` は `RightNodes (Trans N)` の真の始切片。 -/
private theorem RightNodes_seg_len_strict_mono_m0 (M : PS) (m0 m1 : ℕ)
    (hR : RTPS M) (hm0 : Marked M m0) (hpos : 0 < m0) (hlt : m0 < m1)
    (hm1le : m1 ≤ Lng M - 1) :
    (RightNodes (Trans (seg M 0 m0))).length
      < (RightNodes (Trans (seg M 0 m1))).length := by
  have hNR : RTPS (seg M 0 m1) := RTPS_initial_slice M m1 hR hm1le
  have hLN : Lng (seg M 0 m1) = m1 + 1 := by simp
  have hNm0 : Marked (seg M 0 m1) m0 := by
    have := marked_slice M m0 0 m1 hm0 (Nat.zero_le _) (by omega) hm1le
    simpa using this
  have hm0ltN : m0 < Lng (seg M 0 m1) - 1 := by omega
  obtain ⟨a₀, a₁, hRT, hSseg, hRMark⟩ :=
    RightNodes_Mark (seg M 0 m1) m0 hNm0 hNR hpos hm0ltN
  -- `a₁ ≠ []`: 内部基点の像は右 spine 長 ≥ 2
  have hge2 : 2 ≤ (RightNodes (Mark (seg M 0 m1) m0)).length :=
    Mark_interior_RN_ge2_m0 (seg M 0 m1) m0 hNR hNm0 hm0ltN
  rw [hRMark] at hge2
  simp only [List.length_append, List.length_cons, List.length_nil] at hge2
  rw [seg_of_seg_zero_m0 M m0 m1 (le_of_lt hlt)] at hSseg
  rw [hSseg, hRT]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Isabelle `Mark_distinct` (layerB 9586)。`0 < m0 < m1` では
`Mark M m0` の右 spine が `Mark M m1` のそれより真に長い。 -/
private theorem Mark_distinct_m0 (M : PS) (m0 m1 : ℕ) (hR : RTPS M)
    (hm0 : Marked M m0) (hm1 : Marked M m1) (hpos : 0 < m0) (hlt : m0 < m1)
    (hm1le : m1 ≤ Lng M - 1) :
    Mark M m0 ≠ Mark M m1 := by
  have hm0lt : m0 < Lng M - 1 := by omega
  have hm1pos : 0 < m1 := by omega
  by_cases hint : m1 < Lng M - 1
  · obtain ⟨b₀, c₀, hT0, hS0, hR0⟩ := RightNodes_Mark M m0 hm0 hR hpos hm0lt
    obtain ⟨b₁, c₁, hT1, hS1, hR1⟩ := RightNodes_Mark M m1 hm1 hR hm1pos hint
    have hg := RightNodes_seg_len_strict_mono_m0 M m0 m1 hR hm0 hpos hlt hm1le
    rw [hS0, hS1] at hg
    simp only [List.length_append, List.length_cons, List.length_nil] at hg
    -- `rw [hT0] at hq` は `X = X` の両辺を書き換えてしまうので、2 表示を直接突き合わせる
    have hq := congrArg List.length (hT0.symm.trans hT1)
    simp only [List.length_append, List.length_cons, List.length_nil] at hq
    intro heq
    have hlenEq : (RightNodes (Mark M m0)).length = (RightNodes (Mark M m1)).length := by
      rw [heq]
    rw [hR0, hR1] at hlenEq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlenEq
    omega
  · -- 右端: `m1 = Lng M - 1`
    have hm1eq : m1 = Lng M - 1 := by omega
    have hlen : 1 < Lng M := by omega
    have hnz : zeroT M = false := by
      simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      left; omega
    have h1 : Mark M m1 = Dprin (entry M 1 m1 : ℕ∞) BZero := by
      rw [hm1eq]; exact Mark_rightmost1_forward M hR hnz
    have h2 : 2 ≤ (RightNodes (Mark M m0)).length :=
      Mark_interior_RN_ge2_m0 M m0 hR hm0 hm0lt
    intro heq
    rw [heq, h1] at h2
    simp at h2

/-- §7.4 命題（`Mark` が順序関係を保つこと）＝ Isabelle `m_7_4_Mark_order`
(layerB/pss_wip.thy 9707)。**訂正 A19**: 原文の結論 (2) は
`(Mark M m₁, Mark M m₀) ∈ T_B^Marked` だが、`T_B^Marked` は (whole, block) 規約で
`m` が小さいほど像が大きいため対が逆であり偽（経験的確認 0/249）。正しい向きは
`(Mark M m₀, Mark M m₁) ∈ MarkedB`（249/249）。以下はその訂正後の主張。 -/
theorem Mark_order (M : PS) (m0 m1 : ℕ) (hR : RTPS M)
    (hm0 : Marked M m0) (hm1 : Marked M m1) :
    m0 < m1 ↔ (Mark M m1 ≠ Mark M m0 ∧ (Mark M m0, Mark M m1) ∈ MarkedB) := by
  constructor
  · intro hlt
    have hnest : (Mark M m0, Mark M m1) ∈ MarkedB :=
      Mark_MarkedB_nest M m0 m1 hm0 hm1 (le_of_lt hlt) hR
    have hm1le : m1 ≤ Lng M - 1 := by
      have h : le0 M m1 (Lng M - 1) = true := hm1.2.2
      simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
      omega
    refine ⟨?_, hnest⟩
    by_cases hpos : 0 < m0
    · exact (Mark_distinct_m0 M m0 m1 hR hm0 hm1 hpos hlt hm1le).symm
    · -- `m0 = 0`: ここが `Mark0_ne_Mark` の出番
      have hm00 : m0 = 0 := by omega
      have hm1pos : 0 < m1 := by omega
      have hne : Mark M m1 ≠ Trans M := by
        refine Mark0_ne_Mark M m1 hR ?_ hm1 hm1pos
        rw [← hm00]; exact hm0
      have heq0 : Mark M m0 = Trans M := by
        rw [hm00]
        refine Mark_zero_eq_Trans M hR ?_
        rw [← hm00]; exact hm0
      rw [heq0]; exact hne
  · rintro ⟨hne, hnest01⟩
    by_contra hnlt
    have hle : m1 ≤ m0 := by omega
    have hnest10 : (Mark M m1, Mark M m0) ∈ MarkedB :=
      Mark_MarkedB_nest M m1 m0 hm1 hm0 hle hR
    exact hne (MarkedB_antisym_m0 hnest10 hnest01)

#print axioms Trans_mono_RN_ge2
#print axioms Mark0_ne_Mark
#print axioms Mark_order

end PSS
