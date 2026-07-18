import «8».«8.4-corner-engine»

/-!
# §8.4 交換パッケージ condIV admeq 隅の CORNER CORE 残差の縮約
（`MnformCornerCoreResidual_ce` の attack、`8.4-corner-engine` が露出した 5 葉）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-corner-engine»:285 が宣言した named 残差
  `MnformCornerCoreResidual_ce`（隅 mnform の genuinely-missing 部、共有対 `(s₁,b₁)` を
  入力に取り、5 葉を要求する）。`8.4-corner-engine` の `mnformCornerResidual_holds_ce`
  がこれを `MnformCornerResidual_md` へ戻す。

## 5 葉の内訳（`MnformCornerCoreResidual_ce`）

`e₃ = M_{1,j₋₃}`、`e₂ = M_{1,j₋₂}`、`v₁ = M_{1,Lng M-1}`。入力 `hd1`/`hd2` は
`(s₁,b₁)` が `Trans (M[1])`（穴 `transC1`）と `Trans M`（穴 `transC2`）を切ること。

* **LEAF1**（inner）: `scb_decomp (bpHeadT (transC2 M)) s0 (flatBT (D_{v₁}0)) b0`
  ＝ condIV `c₂`-body の穴 `D_{v₁}0`。
* **LEAF2**（k1）: `scb_kind1 (Trans M) s1 (flatBT (transC2 M)) b1`（`c4dx_condIV_k1`）。
* **LEAF3**（`L₁`）/ **LEAF4**（`Trans (Lp)`）/ **LEAF5**（`Trans (Pred Np)`）:
  底スライスの平坦式（§7.4 Mark = `Oper5Residual` 葉）。

## 本ファイルの縮約（3 段の無条件討伐）

1. **LEAF1 は新規残差でなく、既存の `TransC2HoleDecomp_md`（«8».«8.4-mnform-corner-dispatch»、
   ltJ 枝が既に要求する残差）から無条件に導ける**。`TransC2HoleDecomp_md` は
   `transC2 M` 全体の穴 `D_{v₁}0` 分解 `(u2,v2)` を出す。隅の `transC2 M` は単一 principal
   `D_{transV M}(bpHeadT)` なので、外側の `Dsym (transV M)` を 1 段剥がすと LEAF1
   `(bpHeadT の分解)` になる。剥がせる（`u2 ≠ []`）ことは **uv 境界**
   `transV M = M_{1,j₋₁} ≤ M_{1,j₋₂} < M_{1,Lng M-1} = v₁`（`c4dx_uv` wip:84338 の Lean 再導出、
   `entry1_Adm_le_cc` ＋ `s84c1_jm2_basic`）から `Dsym (transV M) ≠ Dsym v₁` で従う。
   ＝ **隅 core は c₂-body 分解を独立に要求せず、ltJ 枝と共有する**（残差の de-dup）。
2. **LEAF2 の `scb_decomp` 部は入力 `hd2` そのもの**。残るのは kind1 順序
   （`transC2 M` のスパインのみに依存）＝ `CornerC2Kind1_cc`。
3. **LEAF3/4/5** は共有 witness `(s0,b0)` に対する底スライス平坦式 ＝ `CornerCoreReadouts_cc`。

よって隅 core が termination まで隔てる新規未移植内容は
`CornerC2Kind1_cc` ＋ `CornerCoreReadouts_cc` の 2 本（LEAF1 は既存 `TransC2HoleDecomp_md`
の再利用）。

- 依存（すべてビルド済み・main e383af6）: «8».«8.4-corner-engine»
  （`MnformCornerCoreResidual_ce` def・`TransC2HoleDecomp_md`・`transC1`/`transC2`/`transV`/
  `transJm1`/`s84x_jm2`/`s84x_jm3`/`s84x_L`/`s84x_Lp`/`s84x_Np`・`bpHeadT`/`Dprin`/`BZero`/
  `flatBT`/`RightNodes`・`scb_decomp`/`scb_kind1`・`Trans`・`c1_shape_holds`/`s84c1_jm2_basic`/
  `Adm_le`/`Adm_max`/`Trans_Mark_invariant`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 `TransC2HoleDecomp_md`（再利用）＋ `CornerC2Kind1_cc` ＋ `CornerCoreReadouts_cc`。
- Private helper suffix: `_cc`。
-/

namespace PSS

/-! ## 0. uv 境界の補助（`c4dx_uv` wip:84338 の Lean 再導出、`8.6-condVI-props` private の複製） -/

/-- `adm M j₀ = false` かつ `Adm M j₀ ≤ j < j₀` なら行 1 は次段で真増加
（Isabelle `viB_suffix` の 1 段、`8.6-condVI-props` private `entry1_step_v6p` の複製）。 -/
private theorem entry1_step_cc (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
    (hj₀ : j₀ < Lng M) (hge : Adm M j₀ ≤ j) (hlt : j < j₀) :
    entry M 1 j < entry M 1 (j + 1) := by
  have hnaS : adm M (j + 1) = false := by
    by_contra hcon
    have hadm : adm M (j + 1) = true := by simpa using hcon
    rcases Nat.lt_or_ge (j + 1) j₀ with h | h
    · have := Adm_max M (j + 1) j₀ hadm (by omega)
      omega
    · have hEq : j + 1 = j₀ := by omega
      rw [hEq] at hadm
      rw [hadm] at hna
      exact absurd hna (by simp)
  have hnadm : nadm M (j + 1) = true := by
    simpa [adm] using hnaS
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadm
  have hlen : ¬ (Lng M < j + 1) := by omega
  rcases hnadm with h | h
  · exact absurd h hlen
  · have hn1 : nextrel1 M j (j + 1) = true := by
      simpa [nextR] using h.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact hn1.1.1.2

/-- `M_{1,Adm(j₀)} ≤ M_{1,j₀}`（Isabelle `viB_suffix_max`、`8.6-condVI-props` private
`entry1_Adm_le_v6p` の複製）。 -/
private theorem entry1_Adm_le_cc (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
    entry M 1 (Adm M j₀) ≤ entry M 1 j₀ := by
  by_cases hadm : adm M j₀ = true
  · simp [Adm, hadm]
  · have hna : adm M j₀ = false := by simpa using hadm
    have hmono : ∀ d a, d = j₀ - a → Adm M j₀ ≤ a → a ≤ j₀ →
        entry M 1 a ≤ entry M 1 j₀ := by
      intro d
      induction d with
      | zero => intro a hd _ hle; have : a = j₀ := by omega
                rw [this]
      | succ d ih =>
          intro a hd hge hle
          have hlt : a < j₀ := by omega
          have hstep := entry1_step_cc M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-! ## 0b. 隅 setup / `transC2` principal 頭（`8.4-corner-engine` private の複製） -/

/-- 隅 setup: `0 < transJ1 M`（`J1pos`）と `transT1 M ≠ 0_B`（`T1`）。
`8.4-corner-engine` private `corner_setup_ce` と同一。 -/
private theorem corner_setup_cc (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
    0 < transJ1 M ∧ transT1 M ≠ BZero := by
  have hlen : 1 < Lng M := by omega
  refine ⟨by simp only [transJ1, lastIdx]; omega, ?_⟩
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1' : Trans (Pred M) ≠ BZero :=
    (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
  simpa [transT1] using T1'

/-- `transC2 M` は先頭指標 `transV M` の principal（`8.4-corner-engine` private
`transC2_eq_Dprin_ce`/`transC2_head_ce`）。 -/
private theorem transC2_eq_Dprin_cc (M : PS) :
    ∃ body, transC2 M = Dprin (transV M) body := by
  unfold transC2 transC2Core
  split_ifs <;> exact ⟨_, rfl⟩

/-- `flatBT (transC2 M) = Dsym (transV M) :: flatBT (bpHeadT (transC2 M))`。 -/
private theorem transC2_flat_head_cc (M : PS) :
    flatBT (transC2 M) = Sym.dsym (transV M) :: flatBT (bpHeadT (transC2 M)) := by
  obtain ⟨body, hb⟩ := transC2_eq_Dprin_cc M
  rw [hb]; rfl

/-- 底穴 `flatBT (D_{n} 0_B)` の `isPTB_str`（`8.4-mnform-corner-dispatch` private
`isPTB_Dprin_nat_md` の複製）。 -/
private theorem isPTB_Dprin_nat_cc (n : ℕ) :
    isPTB_str (flatBT (Dprin (n : ℕ∞) BZero)) :=
  ⟨.db (n : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩

/-! ## 0c. LEAF1: `TransC2HoleDecomp_md` から外側 `Dsym` を剥がして bpHeadT 分解へ -/

/-- **LEAF1 の無条件討伐**。`TransC2HoleDecomp_md` の `transC2 M` 全体の穴分解 `(u2,v2)` から、
外側 principal `Dsym (transV M)` を 1 段剥がして bpHeadT 側の穴分解 `(s0,b0)` を得る。
剥がせること（`u2 ≠ []`）は uv 境界 `transV M ≠ v₁` から従う。 -/
private theorem leaf1_of_hole_cc (M : PS)
    (hTV : transV M = (entry M 1 (transJm1 M) : ℕ∞))
    (huv : entry M 1 (transJm1 M) < entry M 1 (Lng M - 1))
    (hhole : ∃ u2 v2 : List Sym, scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2) :
    ∃ s0 b0 : List Sym, scb_decomp (bpHeadT (transC2 M)) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 := by
  obtain ⟨u2, v2, hflat, _hptb, hv2rp⟩ := hhole
  -- `transV M ≠ v₁` (uv 境界)
  have hne : transV M ≠ ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) := by
    rw [hTV]; exact_mod_cast Nat.ne_of_lt huv
  rw [transC2_flat_head_cc M] at hflat
  cases u2 with
  | nil =>
      exfalso
      rw [List.nil_append,
        show flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero) ++ v2
            = Sym.dsym ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) :: Sym.zero :: v2 from rfl] at hflat
      injection hflat with hxeq _
      injection hxeq with hveq
      exact hne hveq
  | cons x u2' =>
      simp only [List.cons_append] at hflat
      injection hflat with _hx htail
      exact ⟨u2', v2, htail, fun _ => isPTB_Dprin_nat_cc (entry M 1 (Lng M - 1)), hv2rp⟩

/-! ## 1. 露出する named 残差 -/

/-- **LEAF2 の内容部**（`c4dx_condIV_k1` wip:84541 の kind1 順序）。
`scb_kind1` の第 2 連言そのもの: `flatBT (transC2 M)` を平坦化する principal `p` の
`RightNodes` が [Buc1] 第 1 種（先頭 < 末尾 ≤ 各内点）の順序を満たす。`transC2 M` の
スパイン（`= RightAnces` 相当）だけに依存し、`Trans M`/`s1`/`b1` に非依存。 -/
def CornerC2Kind1_cc : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    ∀ p : BP, flatBT (transC2 M) = flatBP p →
      let r := RightNodes (.trm [p])
      let j1 := r.length - 1
      1 ≤ j1 ∧ r.getD 0 0 < r.getD j1 0 ∧
        ∀ j, 0 < j → j < j1 → r.getD j1 0 ≤ r.getD j 0

/-- **LEAF3 ＋ LEAF4 ＋ LEAF5 の束**（共有 witness `(s0,b0)`）。
底スライスの平坦式 `L₁`/`Trans (Lp)`/`Trans (Pred Np)`（§7.4 Mark = `Oper5Residual` 葉）。
witness `(s0,b0)` は LEAF1（本ファイルが `TransC2HoleDecomp_md` から供給）の bpHeadT 穴分解、
共有対 `(s1,b1)` は `hd1`/`hd2` で threaded。 -/
def CornerCoreReadouts_cc : Prop :=
  ∀ (M : PS) (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    scb_decomp (Trans (oper M 1)) s1 (flatBT (transC1 M)) b1 →
    scb_decomp (Trans M) s1 (flatBT (transC2 M)) b1 →
    scb_decomp (bpHeadT (transC2 M)) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
      flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ b0 ++ b1 ∧
      flatBT (Trans (s84x_Lp M))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ b0) ∧
      flatBT (Trans (Pred (s84x_Np M)))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: flatBT (bpHeadT (transC1 M))

/-! ## 2. `MnformCornerCoreResidual_ce` の縮約（house pattern） -/

/-- **`MnformCornerCoreResidual_ce` の drop-in**（house pattern）。
LEAF1 を `TransC2HoleDecomp_md` から uv 剥がしで供給し（`leaf1_of_hole_cc`）、その witness
`(s0,b0)` に対する LEAF3/4/5 を `CornerCoreReadouts_cc` から、LEAF2 を入力 `hd2`（`scb_decomp`
部）＋ `CornerC2Kind1_cc`（kind1 順序）から組む。 -/
theorem mnformCornerCoreResidual_holds_cc
    (hC4 : TransC2HoleDecomp_md) (hread : CornerCoreReadouts_cc)
    (hk1 : CornerC2Kind1_cc) :
    MnformCornerCoreResidual_ce := by
  intro M s1 b1 hST hmono hp hj1 hIV hadmeq hd1 hd2
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨hJ1pos, hT1⟩ := corner_setup_cc M hMR hj1
  obtain ⟨hTV, _hc1eq, _ht2TB, _hjm1lt⟩ := c1_shape_holds M hMR hMT hmono hJ1pos hT1
  -- uv 境界: `M_{1,j₋₁} = M_{1,Adm(j₋₂)} ≤ M_{1,j₋₂} < v₁`
  obtain ⟨hjm2lt, hjm2v1, _⟩ := s84c1_jm2_basic M hp
  have hjm2L : s84x_jm2 M < Lng M := by omega
  have hAdmle : entry M 1 (Adm M (s84x_jm2 M)) ≤ entry M 1 (s84x_jm2 M) :=
    entry1_Adm_le_cc M (s84x_jm2 M) hjm2L
  have huv : entry M 1 (transJm1 M) < entry M 1 (Lng M - 1) := by
    rw [← hadmeq]; omega
  -- LEAF1（`TransC2HoleDecomp_md` から uv 剥がし）
  obtain ⟨s0, b0, hinner⟩ :=
    leaf1_of_hole_cc M hTV huv (hC4 M hST hmono hp hj1 (Or.inr hIV))
  -- LEAF3/4/5
  obtain ⟨hL1, hLp, hPN⟩ :=
    hread M s0 b0 s1 b1 hST hmono hp hj1 hIV hadmeq hd1 hd2 hinner
  -- 組み立て（LEAF2 の `scb_decomp` 部 = `hd2`、kind1 順序 = `hk1`）
  refine ⟨s0, b0, hinner, ⟨hd2, ?_⟩, hL1, hLp, hPN⟩
  intro p hpe
  exact hk1 M hST hmono hp hj1 hIV hadmeq p hpe

#print axioms mnformCornerCoreResidual_holds_cc

end PSS
