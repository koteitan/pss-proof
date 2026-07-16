import PSS.Red
import «6».«6.8-standard-slice-Br-descending»

/-!
# §6.8 d1pos leg — green-modulo dispatch（`RankSuccD1posLeg` の brick 分解）

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域、regime A/B/boundary/periodic の場合分け）
- 訂正: A7（帰納対象は `Br(M′)` の降順性）／ A8（タイル係数は `n`）—
  いずれも上位ファイル `6.8-standard-slice-Br-descending` と同じ形で適用済み
- Isabelle:
  - assembly: `oper_d1pos_notbrle_LOW_take_eq` (isabelle/pss_mechanized.thy:21497–21960)
  - leg: `m_6_8_slice_Br_descending_monoT` の d1pos 枝 (同:23785–23967)
  - brick 対応（本ファイルで `D1pos_*` Prop として仮定化、行番号は pss_mechanized.thy）:
    `oper_d1pos_notbrle_LOW_take_eq_regA` 17737 / `_regB` 18008 /
    `_boundary` 18323 / `_periodic` 20584 /
    `oper_d1pos_ctx_period_tncstrict_uncapped` 20019 /
    `oper_d1pos_notbrle_period_fullShift` 18791 /
    `oper_d1pos_ctx_tnc_capped` 13593 /
    `oper_d1pos_ctx_stop_direct` 19581 / `oper_d1pos_ctx_stop_direct_strict` 19891 /
    `oper_d1pos_period_boundary_cleMB` 21135 /
    `oper_d1pos_notbrle_period_boundary_geom` 18956 /
    `oper_d1pos_notbrle_Br_align_regA` 15399 /
    `oper_d1pos_low_anchor_shamt0` 20904 / `oper_d1pos_lenPSeq_unified` 17601 /
    `oper_d1pos_ctx_tnc_prefix` 15041 / `oper_d1pos_ctx_period_le0Np` 19442 /
    `oper_d1pos_ctx_notbrleNp` 20172 / `oper_d1pos_ctx_notbrleNp_verbatim` 20322 /
    `oper_d1pos_ctx_multiM` 16927 / `oper_d1pos_ctx_le0Np` 17159 /
    `oper_d1pos_branch_anchor` 14553 / `nextR1_boundary_stop_d1pos` 11771
  - 本ファイルで直接証明: `oper_d1pos_ctx_j0lt` 16904 / `oper_d1pos_ctx_dpos` 16864 /
    `oper_d1pos_ctx_r1le` 16879。
    `oper_d1pos_ctx_period_multiNp`（Isabelle 20469）は Isabelle 同様
    `oper_d1pos_ctx_multiM` の一行適用なので Prop 化せずインライン展開。
- 依存: «6».«6.8-standard-slice-Br-descending»（とその推移的 import）, PSS.Red
- 状態: ✅ 配線完了（sorry 0、ビルド緑）。ただし green-modulo:
  残債務はすべて `D1pos_*` Prop 群（各 brick を定理化すれば
  `rankSuccD1posLeg_of_bricks` 経由で `RankSuccD1posLeg` が無条件化する）
-/

namespace PSS

/-! ## 小補題（このファイル私用） -/

/-- `1 < (P S).length` なら `S` は空列でない（`P [] = [[]]` は長さ 1）。 -/
private theorem TPS_of_P_multi_d1d (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

/-- `seg` と `IncrFirstN` の交換（左端 0、右端が範囲内のとき）。 -/
private theorem seg_IncrFirstN_d1d (sh : ℕ) (X : PS) (b : ℕ) (hb : b < Lng X) :
    seg (IncrFirstN sh X) 0 b = IncrFirstN sh (seg X 0 b) := by
  apply List.ext_getElem
  · simp [IncrFirstN_eq_map]
  · intro i h1 h2
    have hib : i < b + 1 := by simpa using h1
    have hiX : 0 + i < Lng X := by omega
    have h2' : i < Lng (seg X 0 b) := by
      simp
      omega
    rw [seg_getElem_68 (IncrFirstN sh X) 0 b i h1,
      entry_IncrFirstN_zero sh X (0 + i) hiX, entry_IncrFirstN_one sh X (0 + i)]
    simp only [IncrFirstN_eq_map, List.getElem_map]
    rw [seg_getElem_68 X 0 b i h2']

/-! ## 自明 ctx brick（直接証明、Isabelle 名を維持）

Isabelle: `oper_d1pos_ctx_j0lt` (16904) / `oper_d1pos_ctx_dpos` (16864) /
`oper_d1pos_ctx_r1le` (16879)。 -/

/-- Isabelle `oper_d1pos_ctx_j0lt` (pss_mechanized.thy:16904)。 -/
theorem oper_d1pos_ctx_j0lt (N : PS)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1) :
    parent N 1 (Lng N - 1) < Lng N - 1 :=
  oper_d1pos_parent_lt_68 N hp i1z

/-- Isabelle `oper_d1pos_ctx_dpos` (pss_mechanized.thy:16864)。 -/
theorem oper_d1pos_ctx_dpos (N : PS)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1) :
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) := by
  have hp1 : hasParent N 1 (Lng N - 1) = true := by simpa [i1z] using hp
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
  have hrow0 := (nextR_implies_row0 N 1 (parent N 1 (Lng N - 1))
    (Lng N - 1) hnext).2
  have hNT : TPS N := by
    have h0 : 0 < Lng N := by omega
    exact List.ne_nil_of_length_pos h0
  exact ancestor_basic_1 N (parent N 1 (Lng N - 1)) (Lng N - 1) (Lng N - 1)
    hNT j0lt (le_refl _) hrow0

/-- Isabelle `oper_d1pos_ctx_r1le` (pss_mechanized.thy:16879)。 -/
theorem oper_d1pos_ctx_r1le (N : PS)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1z : idx1 N (Lng N - 1) = 1) :
    entry N 1 (parent N 1 (Lng N - 1)) ≤ entry N 1 (Lng N - 1) := by
  have hp1 : hasParent N 1 (Lng N - 1) = true := by simpa [i1z] using hp
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) hp1
  have hnext1 : nextrel1 N (parent N 1 (Lng N - 1)) (Lng N - 1) = true := by
    simpa [nextR] using hnext
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hnext1
  exact Nat.le_of_lt hnext1.1.1.2

/-! ## D1pos brick Props（Isabelle brick と 1:1、未証明の名前付き債務）

各 Prop は対応する Isabelle 補題の主張の逐語訳（規約: `le0 M a b` →
`leR M 0 a b = true`、`¬ nextR …` → `nextR … = false`、`M[n]` → `oper M n`）。
将来の brick agent は `theorem <name> : D1pos_<name> := ...` を証明して
配線を無条件化する。 -/

/-- Isabelle `nextR1_boundary_stop_d1pos` (pss_mechanized.thy:11771)。 -/
def D1pos_nextR1_boundary_stop_d1pos : Prop :=
  ∀ (N : PS) (n j0' j1' : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n →
    j0' ≤ parent N 1 (Lng N - 1) →
    Lng N - 1 ≤ j1' →
    j1' < Lng (oper N n) →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false

/-- Isabelle `oper_d1pos_ctx_multiM` (pss_mechanized.thy:16927)。
Isabelle `oper_d1pos_ctx_period_multiNp` (同:20469) はこれの一行適用
（`M := N, j0' := j0red, j1' := j1red`）なので別 Prop にしない。 -/
def D1pos_oper_d1pos_ctx_multiM : Prop :=
  ∀ (M : PS) (j0' j1' : ℕ),
    TPS (seg M j0' j1') →
    j0' < j1' →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length

/-- Isabelle `oper_d1pos_ctx_le0Np` (pss_mechanized.thy:17159)。 -/
def D1pos_oper_d1pos_ctx_le0Np : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    M = oper N n →
    leR M 0 j0' j1' = true →
    j0' < Lng N - 1 →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    leR N 0 j0' (Lng N - 1) = true

/-- Isabelle `oper_d1pos_ctx_tnc_prefix` (pss_mechanized.thy:15041)。 -/
def D1pos_oper_d1pos_ctx_tnc_prefix : Prop :=
  ∀ (N : PS) (n j0' j1' : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n →
    j0' < parent N 1 (Lng N - 1) →
    Lng N - 1 ≤ j1' →
    j0' < j1' →
    j1' < Lng (oper N n) →
    ¬(TrMax (seg (oper N n) j0' j1') = Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true) →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0'

/-- Isabelle `oper_d1pos_ctx_tnc_capped` (pss_mechanized.thy:13593)。 -/
def D1pos_oper_d1pos_ctx_tnc_capped : Prop :=
  ∀ (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ),
    TPS N → monoT N = true → STPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n → q < n →
    j0red < Lng N - 1 →
    j0red = parent N 1 (Lng N - 1) + s0 →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red = Lng N - 1 →
    j1red < j0red + (j1' - j0') →
    j0' < j1' →
    j1' < Lng (oper N n) →
    ¬(TrMax (seg (oper N n) j0' j1') = Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true) →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red

/-- Isabelle `oper_d1pos_ctx_period_tncstrict_uncapped` (pss_mechanized.thy:20019)。 -/
def D1pos_oper_d1pos_ctx_period_tncstrict_uncapped : Prop :=
  ∀ (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n → q < n →
    j0red < Lng N - 1 →
    j0red = parent N 1 (Lng N - 1) + s0 →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red = j0red + (j1' - j0') →
    j0' < j1' →
    j1' < Lng (oper N n) →
    ¬(TrMax (seg (oper N n) j0' j1') = Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true) →
    TrMax (seg N j0red j1red) < j1red - 1 - j0red

/-- Isabelle `oper_d1pos_ctx_stop_direct` (pss_mechanized.thy:19581)。 -/
def D1pos_oper_d1pos_ctx_stop_direct : Prop :=
  ∀ (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ),
    TPS N → monoT N = true → STPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n → q < n →
    j0red < Lng N - 1 →
    j0red = parent N 1 (Lng N - 1) + s0 →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red = Lng N - 1 →
    j1red < j0red + (j1' - j0') →
    j0' < j1' →
    j1' < Lng (oper N n) →
    leR (oper N n) 0 j0' j1' = true →
    ¬(TrMax (seg (oper N n) j0' j1') = Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true) →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false

/-- Isabelle `oper_d1pos_ctx_stop_direct_strict` (pss_mechanized.thy:19891)。 -/
def D1pos_oper_d1pos_ctx_stop_direct_strict : Prop :=
  ∀ (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ),
    TPS N → monoT N = true → STPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n → q < n →
    j0red < Lng N - 1 →
    j0red = parent N 1 (Lng N - 1) + s0 →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red = j0red + (j1' - j0') →
    j0' < j1' →
    j1' < Lng (oper N n) →
    TrMax (seg N j0red j1red) < j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false

/-- Isabelle `oper_d1pos_ctx_period_le0Np` (pss_mechanized.thy:19442)。 -/
def D1pos_oper_d1pos_ctx_period_le0Np : Prop :=
  ∀ (N M : PS) (n q0 s0 j0red j1red j0' j1' shamt : ℕ),
    1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    M = oper N n →
    leR M 0 j0' j1' = true →
    j0' < j1' →
    j1' < Lng M →
    q0 < n →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red ≤ j0red + (j1' - j0') →
    leR N 0 j0red j1red = true

/-- Isabelle `oper_d1pos_ctx_notbrleNp` (pss_mechanized.thy:20172)。 -/
def D1pos_oper_d1pos_ctx_notbrleNp : Prop :=
  ∀ (N M : PS) (n q0 s0 j0red j1red j0' j1' shamt : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    M = oper N n →
    1 ≤ n → q0 < n →
    j0red < Lng N - 1 →
    s0 < Lng N - 1 - parent N 1 (Lng N - 1) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    j1red = min (j0red + (j1' - j0')) (Lng N - 1) →
    j0red < j1red →
    j0' < j1' →
    j1' < Lng M →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    ¬(TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1 ∨
      leR (seg N j0red j1red) 0 (TrMax (seg N j0red j1red) + 1)
        (Lng (seg N j0red j1red) - 1) = true)

/-- Isabelle `oper_d1pos_ctx_notbrleNp_verbatim` (pss_mechanized.thy:20322)。 -/
def D1pos_oper_d1pos_ctx_notbrleNp_verbatim : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    M = oper N n →
    1 ≤ n →
    j0' < Lng N - 1 →
    j0' < j1' →
    Lng N - 1 ≤ j1' →
    j1' < Lng M →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    ¬(TrMax (seg N j0' (Lng N - 1)) = Lng (seg N j0' (Lng N - 1)) - 1 ∨
      leR (seg N j0' (Lng N - 1)) 0 (TrMax (seg N j0' (Lng N - 1)) + 1)
        (Lng (seg N j0' (Lng N - 1)) - 1) = true)

/-- Isabelle `oper_d1pos_notbrle_Br_align_regA` (pss_mechanized.thy:15399)。 -/
def D1pos_oper_d1pos_notbrle_Br_align_regA : Prop :=
  ∀ (N : PS) (n j0red j1red j0' j1' : ℕ),
    1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    1 ≤ n →
    j1red ≤ Lng N - 1 →
    j0red < j1red →
    j1red ≤ j0red + (j1' - j0') →
    j0red = j0' →
    j0' < j1' →
    j1' < Lng (oper N n) →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    ¬(TrMax (seg (oper N n) j0' j1') = Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true) →
    TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) ∧
      Br (seg (oper N n) j0' j1') =
        P (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') ∧
      Br (seg N j0red j1red) =
        P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) ∧
      Br (seg (oper N n) j0' j1') ≠ [] ∧
      Br (seg N j0red j1red) ≠ []

/-- Isabelle `oper_d1pos_notbrle_period_fullShift` (pss_mechanized.thy:18791)。 -/
def D1pos_oper_d1pos_notbrle_period_fullShift : Prop :=
  ∀ (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    j0' < j1' →
    j1' < Lng M →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    Lng N - 1 ≤ j0' →
    q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j1red = min (j0red + (j1' - j0')) (Lng N - 1) →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    j1red < Lng N - 1 →
    seg M (j0' + TrMax (seg M j0' j1') + 1) j1' =
      IncrFirstN shamt
        (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)

/-- Isabelle `oper_d1pos_notbrle_period_boundary_geom` (pss_mechanized.thy:18956)。 -/
def D1pos_oper_d1pos_notbrle_period_boundary_geom : Prop :=
  ∀ (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ),
    TPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    Lng N - 1 ≤ j0' →
    q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j1red = min (j0red + (j1' - j0')) (Lng N - 1) →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    1 < (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    ¬j1red < Lng N - 1 →
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
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1)

/-- Isabelle `oper_d1pos_branch_anchor` (pss_mechanized.thy:14553)。
`c := (IdxSum (P S)).getD ((P S).length - 1) 0`（Isabelle の `defines` を
インライン展開）。`last (P S)` は `(P S).getD ((P S).length - 1) []`。 -/
def D1pos_oper_d1pos_branch_anchor : Prop :=
  ∀ (S : PS),
    TPS S → 1 < (P S).length →
    0 < (IdxSum (P S)).getD ((P S).length - 1) 0 ∧
    (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng S - 1 ∧
    (∀ j, j < (IdxSum (P S)).getD ((P S).length - 1) 0 →
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤ entry S 0 j) ∧
    multiT (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)) = false ∧
    seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) =
      (P S).getD ((P S).length - 1) [] ∧
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
      Lng S - Lng ((P S).getD ((P S).length - 1) [])

/-- Isabelle `oper_d1pos_lenPSeq_unified` (pss_mechanized.thy:17601)。
`c`/`cN` の `defines` はインライン展開。 -/
def D1pos_oper_d1pos_lenPSeq_unified : Prop :=
  ∀ (S Snside : PS) (shamt : ℕ),
    TPS S → 1 < (P S).length →
    TPS Snside → 1 < (P Snside).length →
    Lng Snside - 1 ≤ Lng S - 1 →
    (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Snside - 1 →
    seg S 0 (Lng Snside - 1 - 1) =
      IncrFirstN shamt (seg Snside 0 (Lng Snside - 1 - 1)) →
    entry S 0 (Lng Snside - 1) = entry Snside 0 (Lng Snside - 1) + shamt →
    (P S).length = (P Snside).length

/-- Isabelle `oper_d1pos_period_boundary_cleMB` (pss_mechanized.thy:21135)。 -/
def D1pos_oper_d1pos_period_boundary_cleMB : Prop :=
  ∀ (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ),
    TPS N → monoT N = true → STPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    Lng N - 1 ≤ j0' →
    q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j1red = min (j0red + (j1' - j0')) (Lng N - 1) →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    1 < (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    ¬j1red < Lng N - 1 →
    (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1

/-- Isabelle `oper_d1pos_low_anchor_shamt0` (pss_mechanized.thy:20904)。 -/
def D1pos_oper_d1pos_low_anchor_shamt0 : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    TPS N → monoT N = true → STPS N → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    j0' < Lng N - 1 →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1 →
    j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1 →
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    leR M 0 j0' j1' = true →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false →
    (seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
          (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1))) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) =
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + 0) ∧
    (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ≤
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)) ∧
    ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length) ∧
    ((IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ∧
    (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1)

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_regA` (pss_mechanized.thy:17737)。
結論の存在文は `d1posAlignment_68 N (seg M j0' j1')` の定義体と逐語一致。 -/
def D1pos_oper_d1pos_notbrle_LOW_take_eq_regA : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    TPS N → monoT N = true → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    TPS (seg M j0' j1') →
    leR M 0 j0' j1' = true →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) →
    j0' + TrMax (seg M j0' j1') + 1 < parent N 1 (Lng N - 1) →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    1 < (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length →
    leR N 0 j0' (Lng N - 1) = true →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false →
    d1posAlignment_68 N (seg M j0' j1')

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_regB` (pss_mechanized.thy:18008)。 -/
def D1pos_oper_d1pos_notbrle_LOW_take_eq_regB : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    TPS N → monoT N = true → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    TPS (seg M j0' j1') →
    leR M 0 j0' j1' = true →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) →
    (parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1 ∧
      j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1) →
    parent N 1 (Lng N - 1) ≤ j0' →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    1 < (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length →
    leR N 0 j0' (Lng N - 1) = true →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false →
    seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
          (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)) →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) =
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + 0 →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ≤
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) →
    (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length →
    (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 →
    Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1 →
    d1posAlignment_68 N (seg M j0' j1')

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_boundary` (pss_mechanized.thy:18323)。 -/
def D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary : Prop :=
  ∀ (N M : PS) (n j0' j1' : ℕ),
    TPS N → monoT N = true → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    TPS (seg M j0' j1') →
    leR M 0 j0' j1' = true →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) →
    (parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1 ∧
      j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1) →
    j0' < parent N 1 (Lng N - 1) →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    1 < (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length →
    leR N 0 j0' (Lng N - 1) = true →
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false →
    seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
          (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)) →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) =
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + 0 →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ≤
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) →
    (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length →
    (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 →
    Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1 →
    d1posAlignment_68 N (seg M j0' j1')

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_periodic` (pss_mechanized.thy:20584)。 -/
def D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic : Prop :=
  ∀ (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ),
    TPS N → monoT N = true → 1 < Lng N →
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) →
    hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true →
    idx1 N (Lng N - 1) = 1 →
    M = oper N n →
    1 ≤ n →
    TPS (seg M j0' j1') →
    leR M 0 j0' j1' = true →
    j0' < j1' →
    j1' < Lng M →
    Lng N - 1 ≤ j1' →
    ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true) →
    parent N 1 (Lng N - 1) < Lng N - 1 →
    entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) →
    Lng N - 1 ≤ j0' →
    q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)) →
    j0red = parent N 1 (Lng N - 1) + s0 →
    j1red = min (j0red + (j1' - j0')) (Lng N - 1) →
    shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))) →
    1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length →
    1 < (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length →
    leR N 0 j0red j1red = true →
    TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red →
    nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false →
    seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1) =
      IncrFirstN shamt
        (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
          (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)) →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) =
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) + shamt →
    entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) ≤
      entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) →
    (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length →
    (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 →
    Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1 →
    d1posAlignment_68 N (seg M j0' j1')

/-! ## assembly（Isabelle `oper_d1pos_notbrle_LOW_take_eq` 21497–21960 の移植）

4-cell case-split dispatch: PERIODIC（`Lng N - 1 ≤ j0'`、cap の
INTERIOR/BOUNDARY 分割つき）vs LOW（regA `A < j₋₂` / regB `j₋₂ ≤ j0'` /
boundary `j0' < j₋₂ ≤ A`）。各 cell に regime 固有の追加仮定
（tnc/stop/multi/le0/anchor 束）を調達して渡す。結論
`d1posAlignment_68 N (seg M j0' j1')` は Isabelle の存在文と逐語一致。 -/

theorem oper_d1pos_notbrle_LOW_take_eq
    (hcellA : D1pos_oper_d1pos_notbrle_LOW_take_eq_regA)
    (hcellB : D1pos_oper_d1pos_notbrle_LOW_take_eq_regB)
    (hcellBd : D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary)
    (hcellP : D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic)
    (htncCap : D1pos_oper_d1pos_ctx_tnc_capped)
    (htncUncap : D1pos_oper_d1pos_ctx_period_tncstrict_uncapped)
    (hstopDir : D1pos_oper_d1pos_ctx_stop_direct)
    (hstopStrict : D1pos_oper_d1pos_ctx_stop_direct_strict)
    (hle0P : D1pos_oper_d1pos_ctx_period_le0Np)
    (hnbNp : D1pos_oper_d1pos_ctx_notbrleNp)
    (hnbNpV : D1pos_oper_d1pos_ctx_notbrleNp_verbatim)
    (hmultiMB : D1pos_oper_d1pos_ctx_multiM)
    (hfull : D1pos_oper_d1pos_notbrle_period_fullShift)
    (hbdGeom : D1pos_oper_d1pos_notbrle_period_boundary_geom)
    (hbrAlignA : D1pos_oper_d1pos_notbrle_Br_align_regA)
    (hanchor0 : D1pos_oper_d1pos_low_anchor_shamt0)
    (hlenPu : D1pos_oper_d1pos_lenPSeq_unified)
    (hbdCle : D1pos_oper_d1pos_period_boundary_cleMB)
    (hbrAnchor : D1pos_oper_d1pos_branch_anchor)
    (htncPre : D1pos_oper_d1pos_ctx_tnc_prefix)
    (hbdStop : D1pos_nextR1_boundary_stop_d1pos)
    (hle0L : D1pos_oper_d1pos_ctx_le0Np)
    (N M : PS) (n j0' j1' : ℕ)
    (NT : TPS N) (monoN : monoT N = true) (std : STPS N)
    (LNgt : 1 < Lng N)
    (notzeroN : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hasparN : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1zN : idx1 N (Lng N - 1) = 1)
    (Neq : M = oper N n) (n1 : 1 ≤ n)
    (M'T : TPS (seg M j0' j1'))
    (le0M : leR M 0 j0' j1' = true)
    (lt : j0' < j1') (jM : j1' < Lng M)
    (bge : Lng N - 1 ≤ j1')
    (notbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true)) :
    d1posAlignment_68 N (seg M j0' j1') := by
  subst Neq
  -- regime 非依存の context discharger
  have j0lt : parent N 1 (Lng N - 1) < Lng N - 1 :=
    oper_d1pos_ctx_j0lt N hasparN i1zN
  have dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) :=
    oper_d1pos_ctx_dpos N hasparN i1zN j0lt
  have multiM : 1 < (P (seg (oper N n)
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length :=
    hmultiMB (oper N n) j0' j1' M'T lt notbrle
  by_cases hper : Lng N - 1 ≤ j0'
  · -- CELL 4: PERIODIC（切片開始が周期尾部）
    obtain ⟨q0, hq0⟩ : ∃ x, x = (j0' - parent N 1 (Lng N - 1)) /
        (Lng N - 1 - parent N 1 (Lng N - 1)) := ⟨_, rfl⟩
    obtain ⟨s0, hs0⟩ : ∃ x, x = (j0' - parent N 1 (Lng N - 1)) %
        (Lng N - 1 - parent N 1 (Lng N - 1)) := ⟨_, rfl⟩
    obtain ⟨j0red, hj0red⟩ : ∃ x, x = parent N 1 (Lng N - 1) + s0 := ⟨_, rfl⟩
    obtain ⟨j1red, hj1red⟩ : ∃ x,
        x = min (j0red + (j1' - j0')) (Lng N - 1) := ⟨_, rfl⟩
    obtain ⟨shamt, hshamt⟩ : ∃ x, x = q0 * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) := ⟨_, rfl⟩
    have w0 : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have s0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1) := by
      rw [hs0]
      exact Nat.mod_lt _ w0
    have j0redlt : j0red < Lng N - 1 := by omega
    have hsplit : q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 =
        j0' - parent N 1 (Lng N - 1) := by
      rw [hq0, hs0]
      exact Nat.div_add_mod' _ _
    have j0'eq : j0' = parent N 1 (Lng N - 1) +
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 := by omega
    have LngM : Lng (oper N n) = parent N 1 (Lng N - 1) +
        n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      length_oper_d1pos_68 N n LNgt notzeroN hasparN i1zN
    have q0n : q0 < n := by
      have h1 : q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) <
          n * (Lng N - 1 - parent N 1 (Lng N - 1)) := by omega
      exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
    have j1redle : j1red ≤ Lng N - 1 := by omega
    have j0j1red : j0red < j1red := by omega
    have j1redspan : j1red ≤ j0red + (j1' - j0') := by omega
    -- tnc: min-cap の ACTIVE / INACTIVE で分岐
    have tnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red := by
      by_cases hcap : Lng N - 1 < j0red + (j1' - j0')
      · have capeq : j1red = Lng N - 1 := by omega
        have spanstrict : j1red < j0red + (j1' - j0') := by omega
        exact htncCap N n q0 s0 j0red j1red j0' j1' shamt NT monoN std LNgt
          notzeroN hasparN i1zN j0lt n1 q0n j0redlt hj0red s0lt j0'eq hshamt
          j1redle j0j1red capeq spanstrict lt jM notbrle
      · have span : j1red = j0red + (j1' - j0') := by omega
        have h := htncUncap N n q0 s0 j0red j1red j0' j1' shamt NT LNgt
          notzeroN hasparN i1zN j0lt n1 q0n j0redlt hj0red s0lt j0'eq hshamt
          j1redle j0j1red span lt jM notbrle
        omega
    -- stop: 同じ分岐
    have stop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
        (TrMax (seg N j0red j1red) + 1) = false := by
      by_cases hcap : Lng N - 1 < j0red + (j1' - j0')
      · have capeq : j1red = Lng N - 1 := by omega
        have spanstrict : j1red < j0red + (j1' - j0') := by omega
        exact hstopDir N n q0 s0 j0red j1red j0' j1' shamt NT monoN std LNgt
          notzeroN hasparN i1zN j0lt n1 q0n j0redlt hj0red s0lt j0'eq hshamt
          j1redle j0j1red capeq spanstrict lt jM le0M notbrle
      · have span : j1red = j0red + (j1' - j0') := by omega
        have tncstrict := htncUncap N n q0 s0 j0red j1red j0' j1' shamt NT
          LNgt notzeroN hasparN i1zN j0lt n1 q0n j0redlt hj0red s0lt j0'eq
          hshamt j1redle j0j1red span lt jM notbrle
        exact hstopStrict N n q0 s0 j0red j1red j0' j1' shamt NT monoN std
          LNgt notzeroN hasparN i1zN j0lt n1 q0n j0redlt hj0red s0lt j0'eq
          hshamt j1redle j0j1red span lt jM tncstrict
    have NpT : TPS (seg N j0red j1red) := by
      have h0 : 0 < Lng (seg N j0red j1red) := by
        rw [length_seg]
        omega
      exact List.ne_nil_of_length_pos h0
    have le0Np : leR N 0 j0red j1red = true :=
      hle0P N (oper N n) n q0 s0 j0red j1red j0' j1' shamt LNgt notzeroN
        hasparN i1zN j0lt rfl le0M lt jM q0n s0lt hj0red j0'eq hshamt
        j1redle j0j1red j1redspan
    have notbrleNp : ¬(TrMax (seg N j0red j1red) =
        Lng (seg N j0red j1red) - 1 ∨
        leR (seg N j0red j1red) 0 (TrMax (seg N j0red j1red) + 1)
          (Lng (seg N j0red j1red) - 1) = true) :=
      hnbNp N (oper N n) n q0 s0 j0red j1red j0' j1' shamt NT LNgt notzeroN
        hasparN i1zN j0lt rfl n1 q0n j0redlt s0lt hj0red j0'eq hshamt hj1red
        j0j1red lt jM tnc stop notbrle
    have multiNp : 1 < (P (seg N (j0red + TrMax (seg N j0red j1red) + 1)
        j1red)).length :=
      hmultiMB N j0red j1red NpT j0j1red notbrleNp
    -- anchor 束: INTERIOR（fullShift から剥がす）vs BOUNDARY（geom brick）
    have anchorBundle :
        (seg (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') 0
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1) =
          IncrFirstN shamt
            (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
              (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1))) ∧
        (entry (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') 0
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) =
          entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) + shamt) ∧
        (entry (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') 1
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) ≤
          entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)) ∧
        (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 ≤
          Lng (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') - 1) := by
      by_cases hint : j1red < Lng N - 1
      · have full := hfull N (oper N n) n j0' j1' q0 s0 j0red j1red shamt NT
          LNgt notzeroN hasparN i1zN rfl n1 lt jM j0lt hper hq0 hs0 hj0red
          hj1red hshamt tnc stop notbrle hint
        have SnT : TPS (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) :=
          TPS_of_P_multi_d1d _ multiNp
        have Snpos : 0 < Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1)
            j1red) := List.length_pos_of_ne_nil SnT
        have Lgeq : Lng (seg (oper N n)
            (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') =
            Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) := by
          rw [full, IncrFirstN_eq_map]
          simp
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [full, seg_IncrFirstN_d1d shamt
            (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)
            (by omega)]
        · rw [full, entry_IncrFirstN_zero shamt
            (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)
            (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
            (by omega)]
        · rw [full, entry_IncrFirstN_one]
        · omega
      · exact hbdGeom N (oper N n) n j0' j1' q0 s0 j0red j1red shamt NT LNgt
          notzeroN hasparN i1zN rfl n1 lt jM bge j0lt hper hq0 hs0 hj0red
          hj1red hshamt tnc stop multiNp notbrle hint
    obtain ⟨shiftEqB, boundEq0B, boundEq1B, mleSB⟩ := anchorBundle
    have ST : TPS (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
      TPS_of_P_multi_d1d _ multiM
    have SnT : TPS (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) :=
      TPS_of_P_multi_d1d _ multiNp
    -- cleMB: INTERIOR は branch_anchor(2) + 長さ一致、BOUNDARY は cleMB brick
    have cleMB : (IdxSum (P (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'))).getD
        ((P (seg (oper N n)
          (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length - 1) 0 ≤
        Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 := by
      by_cases hint : j1red < Lng N - 1
      · have full := hfull N (oper N n) n j0' j1' q0 s0 j0red j1red shamt NT
          LNgt notzeroN hasparN i1zN rfl n1 lt jM j0lt hper hq0 hs0 hj0red
          hj1red hshamt tnc stop notbrle hint
        have Lgeq : Lng (seg (oper N n)
            (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') =
            Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) := by
          rw [full, IncrFirstN_eq_map]
          simp
        have cle := (hbrAnchor (seg (oper N n)
          (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') ST multiM).2.1
        omega
      · exact hbdCle N (oper N n) n j0' j1' q0 s0 j0red j1red shamt NT monoN
          std LNgt notzeroN hasparN i1zN rfl n1 lt jM bge j0lt hper hq0 hs0
          hj0red hj1red hshamt tnc stop multiNp multiM notbrle hint
    have lenPSeqB : (P (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length =
        (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)).length :=
      hlenPu (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')
        (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) shamt ST multiM
        SnT multiNp mleSB cleMB shiftEqB boundEq0B
    exact hcellP N (oper N n) n j0' j1' q0 s0 j0red j1red shamt NT monoN LNgt
      notzeroN hasparN i1zN rfl n1 M'T le0M lt jM bge notbrle j0lt dpos hper
      hq0 hs0 hj0red hj1red hshamt multiM multiNp le0Np tnc stop shiftEqB
      boundEq0B boundEq1B lenPSeqB cleMB mleSB
  · -- LOW: witnesses は `j0red = j0'`, `j1red = Lng N - 1`, `shamt = 0`
    have j0plt : j0' < Lng N - 1 := by omega
    have le0Np : leR N 0 j0' (Lng N - 1) = true :=
      hle0L N (oper N n) n j0' j1' LNgt notzeroN hasparN i1zN j0lt rfl le0M
        j0plt jM bge
    -- tnc: verbatim-prefix（j0' < j₋₂）vs 同一ブロック（j₋₂ ≤ j0'、q=0 で ctx brick）
    have tnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' := by
      by_cases hpre : j0' < parent N 1 (Lng N - 1)
      · exact htncPre N n j0' j1' NT LNgt notzeroN hasparN i1zN j0lt n1 hpre
          bge lt jM notbrle
      · have s0eq : j0' = parent N 1 (Lng N - 1) +
            (j0' - parent N 1 (Lng N - 1)) := by omega
        have s0lt : j0' - parent N 1 (Lng N - 1) <
            Lng N - 1 - parent N 1 (Lng N - 1) := by omega
        have j0'eqc : j0' = parent N 1 (Lng N - 1) +
            0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
            (j0' - parent N 1 (Lng N - 1)) := by omega
        have shz : (0 : ℕ) = 0 * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by omega
        by_cases hcap : Lng N - 1 < j0' + (j1' - j0')
        · exact htncCap N n 0 (j0' - parent N 1 (Lng N - 1)) j0' (Lng N - 1)
            j0' j1' 0 NT monoN std LNgt notzeroN hasparN i1zN j0lt n1 n1
            j0plt s0eq s0lt j0'eqc shz (le_refl _) j0plt rfl hcap lt jM
            notbrle
        · have span : Lng N - 1 = j0' + (j1' - j0') := by omega
          have h := htncUncap N n 0 (j0' - parent N 1 (Lng N - 1)) j0'
            (Lng N - 1) j0' j1' 0 NT LNgt notzeroN hasparN i1zN j0lt n1 n1
            j0plt s0eq s0lt j0'eqc shz (le_refl _) j0plt span lt jM notbrle
          omega
    -- stop: verbatim-prefix は境界停止 brick、同一ブロックは stop_direct 系
    have stop : nextR (seg (oper N n) j0' j1') 1
        (TrMax (seg N j0' (Lng N - 1)))
        (TrMax (seg N j0' (Lng N - 1)) + 1) = false := by
      by_cases hpre : j0' < parent N 1 (Lng N - 1)
      · exact hbdStop N n j0' j1' NT LNgt notzeroN hasparN i1zN j0lt n1
          (by omega) bge jM
      · have s0eq : j0' = parent N 1 (Lng N - 1) +
            (j0' - parent N 1 (Lng N - 1)) := by omega
        have s0lt : j0' - parent N 1 (Lng N - 1) <
            Lng N - 1 - parent N 1 (Lng N - 1) := by omega
        have j0'eqc : j0' = parent N 1 (Lng N - 1) +
            0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
            (j0' - parent N 1 (Lng N - 1)) := by omega
        have shz : (0 : ℕ) = 0 * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by omega
        by_cases hcap : Lng N - 1 < j0' + (j1' - j0')
        · exact hstopDir N n 0 (j0' - parent N 1 (Lng N - 1)) j0' (Lng N - 1)
            j0' j1' 0 NT monoN std LNgt notzeroN hasparN i1zN j0lt n1 n1
            j0plt s0eq s0lt j0'eqc shz (le_refl _) j0plt rfl hcap lt jM le0M
            notbrle
        · have span : Lng N - 1 = j0' + (j1' - j0') := by omega
          have tncstrict := htncUncap N n 0 (j0' - parent N 1 (Lng N - 1))
            j0' (Lng N - 1) j0' j1' 0 NT LNgt notzeroN hasparN i1zN j0lt n1
            n1 j0plt s0eq s0lt j0'eqc shz (le_refl _) j0plt span lt jM
            notbrle
          exact hstopStrict N n 0 (j0' - parent N 1 (Lng N - 1)) j0'
            (Lng N - 1) j0' j1' 0 NT monoN std LNgt notzeroN hasparN i1zN
            j0lt n1 n1 j0plt s0eq s0lt j0'eqc shz (le_refl _) j0plt span lt
            jM tncstrict
    have notbrleNp : ¬(TrMax (seg N j0' (Lng N - 1)) =
        Lng (seg N j0' (Lng N - 1)) - 1 ∨
        leR (seg N j0' (Lng N - 1)) 0 (TrMax (seg N j0' (Lng N - 1)) + 1)
          (Lng (seg N j0' (Lng N - 1)) - 1) = true) :=
      hnbNpV N (oper N n) n j0' j1' NT LNgt notzeroN hasparN i1zN j0lt rfl n1
        j0plt lt bge jM tnc stop notbrle
    have NpT : TPS (seg N j0' (Lng N - 1)) := by
      have h0 : 0 < Lng (seg N j0' (Lng N - 1)) := by
        rw [length_seg]
        omega
      exact List.ne_nil_of_length_pos h0
    have multiNp : 1 < (P (seg N
        (j0' + TrMax (seg N j0' (Lng N - 1)) + 1) (Lng N - 1))).length :=
      hmultiMB N j0' (Lng N - 1) NpT j0plt notbrleNp
    -- regA 整列で TrEq を取り、`A < Lng N - 1` を導出（A = LN-1 は multiNp と矛盾）
    have alignL := hbrAlignA N n j0' (Lng N - 1) j0' j1' LNgt notzeroN
      hasparN i1zN j0lt n1 (le_refl _) j0plt (by omega) rfl lt jM tnc stop
      notbrle
    have TrEqL : TrMax (seg (oper N n) j0' j1') =
        TrMax (seg N j0' (Lng N - 1)) := alignL.1
    have multiNpB : 1 < (P (seg N
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1))).length := by
      rw [TrEqL]
      exact multiNp
    have AltN : j0' + TrMax (seg (oper N n) j0' j1') + 1 < Lng N - 1 := by
      by_contra hcon
      have hL1 : Lng (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1)
          (Lng N - 1)) = 1 := by
        rw [length_seg]
        omega
      have hT1 : TPS (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1)
          (Lng N - 1)) := by
        have h0 : 0 < Lng (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1)
            (Lng N - 1)) := by omega
        exact List.ne_nil_of_length_pos h0
      have hmul := (P_components_multi_iff _ hT1).mpr multiNpB
      simp [multiT, monoT, zeroT, hL1, leR, le0, le0Aux] at hmul
    -- dispatch: regA（A < j₋₂）/ regB（j₋₂ ≤ j0'）/ boundary（j0' < j₋₂ ≤ A）
    by_cases hAreg : j0' + TrMax (seg (oper N n) j0' j1') + 1 <
        parent N 1 (Lng N - 1)
    · exact hcellA N (oper N n) n j0' j1' NT monoN LNgt notzeroN hasparN i1zN
        rfl n1 M'T le0M lt jM bge notbrle j0lt dpos hAreg multiM multiNpB
        le0Np tnc stop
    · have Ajm2 : parent N 1 (Lng N - 1) ≤
          j0' + TrMax (seg (oper N n) j0' j1') + 1 := by omega
      obtain ⟨shiftEqB, boundEq0B, boundEq1B, lenPSeqB, cleMB, mleSB⟩ :=
        hanchor0 N (oper N n) n j0' j1' NT monoN std LNgt notzeroN hasparN
          i1zN rfl n1 j0plt lt jM bge Ajm2 AltN dpos multiM le0M notbrle tnc
          stop
      by_cases hj0pge : parent N 1 (Lng N - 1) ≤ j0'
      · exact hcellB N (oper N n) n j0' j1' NT monoN LNgt notzeroN hasparN
          i1zN rfl n1 M'T le0M lt jM bge notbrle j0lt dpos ⟨Ajm2, AltN⟩
          hj0pge multiM multiNpB le0Np tnc stop shiftEqB boundEq0B boundEq1B
          lenPSeqB cleMB mleSB
      · exact hcellBd N (oper N n) n j0' j1' NT monoN LNgt notzeroN hasparN
          i1zN rfl n1 M'T le0M lt jM bge notbrle j0lt dpos ⟨Ajm2, AltN⟩
          (by omega) multiM multiNpB le0Np tnc stop shiftEqB boundEq0B
          boundEq1B lenPSeqB cleMB mleSB

/-! ## leg（Isabelle `m_6_8_slice_Br_descending_monoT` d1pos 枝 23785–23967 の移植）

`RankSuccD1posLeg` を brick Props に還元する。groundwork（notzero/hasParent は
`reaching_old_end_forces_tiling`、`monoT N` は非 multi ＋ d1pos、`i₁ = 1` は
`idx1` の定義）→ A0 副ケースは空虚（`j₋₂ < Lng N - 1 ≤ j₁'`）→ brle は
`descending_Br_of_branch_le0`、¬brle は assembly ＋ rank-k IH ＋
`descending_shift_append`（`descending_of_d1posAlignment_68` 経由）。 -/

theorem rankSuccD1posLeg_of_bricks
    (hcellA : D1pos_oper_d1pos_notbrle_LOW_take_eq_regA)
    (hcellB : D1pos_oper_d1pos_notbrle_LOW_take_eq_regB)
    (hcellBd : D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary)
    (hcellP : D1pos_oper_d1pos_notbrle_LOW_take_eq_periodic)
    (htncCap : D1pos_oper_d1pos_ctx_tnc_capped)
    (htncUncap : D1pos_oper_d1pos_ctx_period_tncstrict_uncapped)
    (hstopDir : D1pos_oper_d1pos_ctx_stop_direct)
    (hstopStrict : D1pos_oper_d1pos_ctx_stop_direct_strict)
    (hle0P : D1pos_oper_d1pos_ctx_period_le0Np)
    (hnbNp : D1pos_oper_d1pos_ctx_notbrleNp)
    (hnbNpV : D1pos_oper_d1pos_ctx_notbrleNp_verbatim)
    (hmultiMB : D1pos_oper_d1pos_ctx_multiM)
    (hfull : D1pos_oper_d1pos_notbrle_period_fullShift)
    (hbdGeom : D1pos_oper_d1pos_notbrle_period_boundary_geom)
    (hbrAlignA : D1pos_oper_d1pos_notbrle_Br_align_regA)
    (hanchor0 : D1pos_oper_d1pos_low_anchor_shamt0)
    (hlenPu : D1pos_oper_d1pos_lenPSeq_unified)
    (hbdCle : D1pos_oper_d1pos_period_boundary_cleMB)
    (hbrAnchor : D1pos_oper_d1pos_branch_anchor)
    (htncPre : D1pos_oper_d1pos_ctx_tnc_prefix)
    (hbdStop : D1pos_nextR1_boundary_stop_d1pos)
    (hle0L : D1pos_oper_d1pos_ctx_le0Np) :
    RankSuccD1posLeg := by
  intro k IH N M n j₀' j₁' hN hMdef hn hNlen hnm hd1 hlt hj₁ hbge hleR
  subst hMdef
  have hNT : TPS N := SkTPS_TPS k N hN
  have hstd : STPS N := SkTPS_STPS k N hN
  obtain ⟨hnotzero, hpar⟩ :=
    reaching_old_end_forces_tiling N (oper N n) n j₁' rfl hNlen hbge hj₁
  have hi1 : idx1 N (Lng N - 1) = 1 := by simp [idx1, hd1]
  have hzeroN : zeroT N = false := by
    simp [zeroT]
    omega
  have hmonoN : monoT N = true := by
    cases hm : monoT N with
    | false =>
        exfalso
        have hmul : multiT N = true := by simp [multiT, hzeroN, hm]
        rw [hnm] at hmul
        simp at hmul
    | true => rfl
  have hjM : j₁' < Lng (oper N n) := by omega
  have hM'T : TPS (seg (oper N n) j₀' j₁') := by
    have h0 : 0 < Lng (seg (oper N n) j₀' j₁') := by
      rw [length_seg]
      omega
    exact List.ne_nil_of_length_pos h0
  by_cases hbrle : TrMax (seg (oper N n) j₀' j₁') =
      Lng (seg (oper N n) j₀' j₁') - 1 ∨
      le0 (seg (oper N n) j₀' j₁') (TrMax (seg (oper N n) j₀' j₁') + 1)
        (Lng (seg (oper N n) j₀' j₁') - 1) = true
  · -- brle: 単一成分の枝、`descending` は自明
    exact descending_Br_of_branch_le0 (seg (oper N n) j₀' j₁') hM'T hbrle
  · -- ¬brle: assembly → alignment → IH + shift-append
    have hnotbrle : ¬(TrMax (seg (oper N n) j₀' j₁') =
        Lng (seg (oper N n) j₀' j₁') - 1 ∨
        leR (seg (oper N n) j₀' j₁') 0 (TrMax (seg (oper N n) j₀' j₁') + 1)
          (Lng (seg (oper N n) j₀' j₁') - 1) = true) := by
      intro hcon
      apply hbrle
      rcases hcon with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [leR] using h)
    have halign : d1posAlignment_68 N (seg (oper N n) j₀' j₁') :=
      oper_d1pos_notbrle_LOW_take_eq hcellA hcellB hcellBd hcellP htncCap
        htncUncap hstopDir hstopStrict hle0P hnbNp hnbNpV hmultiMB hfull
        hbdGeom hbrAlignA hanchor0 hlenPu hbdCle hbrAnchor htncPre hbdStop
        hle0L N (oper N n) n j₀' j₁' hNT hmonoN hstd hNlen hnotzero hpar hi1
        rfl hn hM'T hleR hlt hjM hbge hnotbrle
    exact descending_of_d1posAlignment_68 k IH N (seg (oper N n) j₀' j₁')
      hN hmonoN halign

end PSS

#print axioms PSS.oper_d1pos_ctx_j0lt
#print axioms PSS.oper_d1pos_ctx_dpos
#print axioms PSS.oper_d1pos_ctx_r1le
#print axioms PSS.oper_d1pos_notbrle_LOW_take_eq
#print axioms PSS.rankSuccD1posLeg_of_bricks
