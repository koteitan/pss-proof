import «8».«8.4-corner-core»
import «8».«8.4-base-legs»

/-!
# §8.4 交換パッケージ condIV admeq 隅の DEEP 葉の討伐
（`Base1pCorner_bl3`／corner core の残差 `CornerC2Kind1_cc`・`CornerCoreReadouts_cc`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: 隅（condIV ∧ admeq）で露出する named 残差
  * `Base1pCorner_bl3`（«8».«8.4-base-legs»:388）= 隅専用 base1′ 順序 fact
    （Isabelle 隅 base1′ `oy1_base1Y_condIV`/`c4dx_condIV_base1` の admeq 退化版）。
  * `CornerC2Kind1_cc`（«8».«8.4-corner-core»:177）= `transC2 M` スパインの kind1 順序
    （Isabelle `c4dx_condIV_k1` の第 1 種述語部、`s84c3_RightAnces_chain` 依存）。
  * `CornerCoreReadouts_cc`（«8».«8.4-corner-core»:190）= 底スライス平坦式 `L₁`/`Lp`/`Pred Np`
    （§7.4 Mark = `Oper5Residual` 葉）。

## 本ファイルの成果（隅 deep 葉 3 本のうち 2 本を無条件討伐）

1. **`Base1pCorner_bl3` を完全に無条件討伐**（`base1pCorner_holds_cd`）。
2. **`CornerC2Kind1_cc` を完全に無条件討伐**（`cornerC2Kind1_holds_cd`）。

これで `MnformCornerCoreResidual_ce`（«8».«8.4-corner-core»）の残り 2 葉のうち
`CornerC2Kind1_cc` が閉じ、隅 core の残差は `CornerCoreReadouts_cc` 1 本のみ。
また `Base1pCorner_bl3`（«8».«8.4-base-legs» の 2 named 残差の 1 本）が閉じ、
`base1pCondIIIIV_holds_bl3`（Base 脚 2）の負債が消える。

### 成果 1: `Base1pCorner_bl3`（`base1pCorner_holds_cd`）

隅では collapse で `Trans (Pred (s84x_N M)) = transC1 M`／`Trans (s84x_N M) = transC2 M`
となり、base1′ の oy1 論法（外側 `u1`/`v1` 包み）は退化する。しかし残差 `Base1pCorner_bl3`
自体は `hinner`（`bpHeadT (transC2 M)` の穴 `D_{v₁}0` の scb 分解）だけを入力に取り、
`lessBT (bpHeadT (transC1 M)) (ins 0_B)` を出す純 `T_B`/scb の事実である。

攻め筋（Isabelle `c4dx_condIV_base1` layerB/pss_wip.thy:84624 の admeq 版）:
1. `bpHeadT (transC1 M) = transT2 M`（`c1_shape_holds`）。
2. `Cnv_c2_shape_condIV_holds`（既存・無条件）で `bpHeadT (transC2 M)
   = t₃ +_B D_{jpe}(t₄ +_B D_{v₁}0)` と形状二分 `dich` を得る。
3. `Cnv_nested_hole_pair_holds`（既存・無条件）で穴内容 `c'` に依らない一様 surgery 対
   `(sB,bB)` を得る。穴 `= D_{v₁}0` 版で `bpHeadT (transC2 M)` を切ると、`hinner` の
   `(s0,b0)` と scb 一意性で一致（`s0=sB`, `b0=bB`）。
4. `ins 0_B` は surgery で穴 `D_{v₁}0` を `D_{ub}0`（`ub=v₁-1`）に置換した項
   ＝ `t₃ +_B D_{jpe}(t₄ +_B D_{ub}0)`（flat 一致 ＋ `unflatBT_flat`）。
5. `dich` ＋ `D_{ub}0 ≠ 0_B` から成長 `lessBT (transT2 M) (t₃ +_B D_{jpe}(t₄ +_B D_{ub}0))`
   （`cnv_body_grow_cd`）。

`c4dx_condIV_base1` は挿入引数を `D_{ub}0` にした版（内側二重 `D_{ub}`）を証明するが、
実 base1′（producer 表）は `d4vx_ins s0 ub b0 0_B` ＝ `ins 0_B`（内側単項 `D_{ub}0`）を要求する。
成長論法は内側項の形に依らず成立するので、admeq 版はそのまま通る。

### 成果 2: `CornerC2Kind1_cc`（`cornerC2Kind1_holds_cd`）

隅（condIV）では `Cnv_c2_shape_condIV` が `transC2 M` を
`D_{transV}(t₃ +_B D_{jpe}(t₄ +_B D_{v₁}0))` に pin する。よって `transC2 M` の
`RightNodes` は**厳密に長さ 3 の鎖** `[transV, jpe, v₁]`（`RightNodes_addBT_Dprin`）。
[Buc1] 第 1 種順序 `先頭 < 末尾 ≤ 内点` は 2 個の算術に還元される:
* 先頭 `transV < 末尾 v₁`（uv 境界。`transV = M_{1,Adm(j₋₂)} ≤ M_{1,j₋₂} < v₁`、
  `entry1_Adm_le_cd` ＋ `s84c1_jm2_basic` ＋ admeq）
* 末尾 `v₁ ≤ 内点 jpe`（condIV 第 2 連言 `M_{1,Lng-1} ≤ M_{1,lastParent}`＝`transJ0`）。

`s84c3_RightAnces_chain` の一般鎖不変量（`chainOK`/`winOK`）は**不要**——隅では shape が
pin されるので鎖は 3 点に確定する（`Kind1Shape_se`（«8».«8.4-slice-ext-engines»）の
非隅版とは異なり、condIV shape 経由で無条件）。

- 依存（すべてビルド済み・main aeece04）: «8».«8.4-base-legs»（`Base1pCorner_bl3` def・
  `cornerCollapse_holds_cr`・`Cnv_c2_shape_condIV_holds`・`Cnv_nested_hole_pair_holds`・
  `c1_shape_holds`・`scb_unique_decomp_unconditional`・`unflatBT_flat`・`lessBT_addBT_self`・
  `lessBT_linear_irrefl`・`transC1`/`transC2`/`transV`/`transT2`/`transT1`/`transJ0`/`transJ1`・
  `Dprin`/`BZero`/`flatBT`/`flatBP`/`bpHeadT`/`addBT`/`scb_decomp`・`STPS_RTPS`/`RTPS_TPS`/
  `RTPS_Pred`/`Trans_Mark_invariant`）、«8».«8.4-corner-core»（`CornerC2Kind1_cc`/
  `CornerCoreReadouts_cc` def・`s84c1_jm2_basic`・`RightNodes_addBT_Dprin`/`RightNodes_Dprin`・
  `Adm_le`/`Adm_max`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  討伐: `Base1pCorner_bl3` ＋ `CornerC2Kind1_cc`。残差 `CornerCoreReadouts_cc`
  （§7.4 Mark = `d4vx_core` 塔 readback、Isabelle `c4cx2_condIV_mnform_of_slice` 依存、未移植）。
- Private helper suffix: `_cd`。
-/

namespace PSS

/-! ## 0. `lessBT` 成長補助（base1p private helper の `_cd` 複製） -/

/-- `bpHeadT (D_v a) = a`。 -/
private theorem bpHeadT_Dprin_cd (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（後向き）。 -/
private theorem lessBP_same_head_cd (v : ℕ∞) {a b : BT} (h : lessBT a b = true) :
    lessBP (.db v a) (.db v b) = true := by
  simp [lessBP, h]

/-- `lessBP` は非反射的。 -/
private theorem lessBP_irrefl_cd (p : BP) : lessBP p p = false := by
  cases p with
  | db u a => simp [lessBP, lessBT_linear_irrefl a]

/-- 共通前置 `ps` を落として `lessBPList` を比較。 -/
private theorem lessBPList_prefix_cd (ps qs rs : List BP) :
    lessBPList (ps ++ qs) (ps ++ rs) = lessBPList qs rs := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.cons_append, lessBPList, lessBP_irrefl_cd p, beq_self_eq_true,
        Bool.true_and, Bool.false_or]
      exact ih

/-- `addBT` は右引数に対して狭義単調（前置 `t` を共有）。 -/
private theorem lessBT_addBT_mono_right_cd {a b : BT} (t : BT)
    (h : lessBT a b = true) : lessBT (addBT t a) (addBT t b) = true := by
  obtain ⟨tp⟩ := t; obtain ⟨ap⟩ := a; obtain ⟨bp⟩ := b
  show lessBPList (tp ++ ap) (tp ++ bp) = true
  rw [lessBPList_prefix_cd]; exact h

/-- 頭指標が同じ principal 項の順序は本体の順序に一致（前向き）。 -/
private theorem lessBT_Dprin_same_cd (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- Isabelle `cnv_body_grow`/`c4dx_lessBT_grow` の系: 形状二分の下で
`t₂ < t₃ +_B D_w(t₄ +_B c)`（`c ≠ 0_B`）。 -/
private theorem cnv_body_grow_cd {t2 t3 t4 c : BT} {w : ℕ∞}
    (dich : (t3 = t2 ∧ t4 = t2) ∨ t2 = addBT t3 (Dprin w t4)) (cne : c ≠ BZero) :
    lessBT t2 (addBT t3 (Dprin w (addBT t4 c))) = true := by
  rcases dich with ⟨ht3, ht4⟩ | hb
  · subst ht3; subst ht4
    apply lessBT_addBT_self; simp [Dprin, BZero]
  · rw [hb]
    apply lessBT_addBT_mono_right_cd
    apply lessBT_Dprin_same_cd
    exact lessBT_addBT_self t4 c cne

/-- `D_n 0_B ∈ T_B`（`n` は有限指標）。 -/
private theorem Dprin_nat_mem_T_B_cd (n : ℕ) : Dprin (n : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, BZero]

/-- `adm M j₀ = false` かつ `Adm M j₀ ≤ j < j₀` なら行 1 は次段で真増加
（`corner-core` private `entry1_step_cc` の複製）。 -/
private theorem entry1_step_cd (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
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

/-- `M_{1,Adm(j₀)} ≤ M_{1,j₀}`（`corner-core` private `entry1_Adm_le_cc` の複製）。 -/
private theorem entry1_Adm_le_cd (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
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
          have hstep := entry1_step_cd M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-- 隅 setup: `0 < transJ1 M` ＋ `transT1 M ≠ 0_B`（`corner_setup_ce` の複製）。 -/
private theorem corner_setup_cd (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
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

/-! ## 1. `Base1pCorner_bl3` の完全討伐（`c4dx_condIV_base1` admeq 版） -/

/-- **`Base1pCorner_bl3`（«8».«8.4-base-legs»:388）の drop-in**。
隅（condIV ∧ admeq）専用の base1′ 順序 fact を無条件に証明する。 -/
theorem base1pCorner_holds_cd : Base1pCorner_bl3 := by
  intro M ins s0 b0 hST hmono hp hj1 hIV hadmeq hflat hb0RP hinner
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨J1pos, hT1⟩ := corner_setup_cd M hMR hj1
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono J1pos hT1
  have hbpT1 : bpHeadT (transC1 M) = transT2 M := by rw [hc1eq, bpHeadT_Dprin_cd]
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ :=
    Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hIV
  -- `bpHeadT (transC2 M) = t₃ +_B D_{jpe}(t₄ +_B D_{v₁}0)`
  have hbpT2 : bpHeadT (transC2 M)
      = addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero))) := by
    rw [c2full, bpHeadT_Dprin_cd]
  -- 一様 surgery 対 `(sB,bB)`（穴内容 `c'` に非依存）
  obtain ⟨sB, bB, holeU⟩ :=
    Cnv_nested_hole_pair_holds t3 t4 ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) ht4TB
  have cTB : Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero ∈ T_B :=
    Dprin_nat_mem_T_B_cd (entry M 1 (Lng M - 1))
  have ccTB : Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero ∈ T_B :=
    Dprin_nat_mem_T_B_cd (entry M 1 (Lng M - 1) - 1)
  have cp : ∃ p, Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero = BT.trm [p] :=
    ⟨.db _ BZero, rfl⟩
  have ccp : ∃ p, Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero = BT.trm [p] :=
    ⟨.db _ BZero, rfl⟩
  have ccne : Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero ≠ BZero := by
    simp [Dprin, BZero]
  -- 穴 `= D_{v₁}0` 版で `bpHeadT (transC2 M)` を切る（`hinner` と scb 一意性で一致）
  have dB : scb_decomp (bpHeadT (transC2 M)) sB
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) bB := by
    rw [hbpT2]; exact holeU _ cTB cp
  have dBcc : scb_decomp
      (addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero))))
      sB (flatBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero)) bB :=
    holeU _ ccTB ccp
  obtain ⟨hs0, hb0⟩ := scb_unique_decomp_unconditional (bpHeadT (transC2 M))
    s0 sB (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 bB hinner dB
  -- `ins 0_B` の再構成: 穴を `D_{ub}0` に置換した項
  have hccflat : Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT BZero
      = flatBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero) := by
    simp [Dprin, flatBT, flatBP]
  have hfins : flatBT (ins BZero)
      = flatBT (addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero)))) := by
    rw [hflat BZero, hs0, hb0, hccflat, dBcc.1]
  have hins : ins BZero
      = addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero))) := by
    calc ins BZero = unflatBT (flatBT (ins BZero)) := (unflatBT_flat _).symm
      _ = unflatBT (flatBT (addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
            (addBT t4 (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero))))) := by
          rw [hfins]
      _ = _ := unflatBT_flat _
  rw [hbpT1, hins]
  exact cnv_body_grow_cd dich ccne

#print axioms base1pCorner_holds_cd

/-! ## 2. `CornerC2Kind1_cc` の完全討伐（`transC2 M` スパインの kind1 順序）

隅（condIV）では `Cnv_c2_shape_condIV` が `transC2 M` を
`D_{transV}(t₃ +_B D_{jpe}(t₄ +_B D_{v₁}0))` に pin する。よって `transC2 M` の
`RightNodes` は**厳密に長さ 3 の鎖** `[transV, jpe, v₁]`（`RightNodes_addBT_Dprin`）。
kind1 順序 `先頭 < 末尾 ≤ 内点` は
* 末尾 `v₁` < 先頭 `transV`… ではなく `先頭 transV < 末尾 v₁`（uv 境界、
  `entry1_Adm_le_cd` ＋ `s84c1_jm2_basic` ＋ admeq）
* 末尾 `v₁ ≤` 内点 `jpe`（condIV の第 2 連言 `v₁ ≤ jpe`）
に還元される。`s84c3_RightAnces_chain` の一般鎖不変量は不要（隅では shape が pin される）。 -/

/-- **`CornerC2Kind1_cc`（«8».«8.4-corner-core»:177）の drop-in**。 -/
theorem cornerC2Kind1_holds_cd : CornerC2Kind1_cc := by
  intro M hST hmono hp hj1 hIV hadmeq p hpe
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨J1pos, hT1⟩ := corner_setup_cd M hMR hj1
  obtain ⟨hVeq, hc1eq, ht2TB, _⟩ := c1_shape_holds M hMR hMT hmono J1pos hT1
  obtain ⟨t3, t4, ht3TB, ht4TB, c2full, dich⟩ :=
    Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hIV
  -- `.trm [p] = transC2 M`（flat 一致 ＋ `unflatBT_flat`）
  have h : flatBT (BT.trm [p]) = flatBT (transC2 M) := hpe.symm
  have hpeq : BT.trm [p] = transC2 M := by
    calc BT.trm [p] = unflatBT (flatBT (BT.trm [p])) := (unflatBT_flat _).symm
      _ = unflatBT (flatBT (transC2 M)) := by rw [h]
      _ = transC2 M := unflatBT_flat _
  -- `RightNodes (.trm [p]) = [transV, jpe, v₁]`（有限指標へ落とす）
  have hRN : RightNodes (BT.trm [p])
      = [entry M 1 (transJm1 M), entry M 1 (transJ0 M), entry M 1 (Lng M - 1)] := by
    rw [hpeq, c2full, hVeq]; simp
  -- uv 境界: `M_{1,j₋₁} < v₁`
  obtain ⟨hjm2lt, hjm2v1, _⟩ := s84c1_jm2_basic M hp
  have hjm2L : s84x_jm2 M < Lng M := by omega
  have hAdmle : entry M 1 (Adm M (s84x_jm2 M)) ≤ entry M 1 (s84x_jm2 M) :=
    entry1_Adm_le_cd M (s84x_jm2 M) hjm2L
  have huv : entry M 1 (transJm1 M) < entry M 1 (Lng M - 1) := by
    rw [← hadmeq]; omega
  -- condIV: `v₁ ≤ jpe`
  have hle : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    have hIV' := hIV
    simp only [transCondIV, lastIdx, Bool.and_eq_true, decide_eq_true_eq] at hIV'
    exact hIV'.1.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hRN]; simp
  · rw [hRN]; simpa using huv
  · intro j hj0 hj2
    rw [hRN] at hj2 ⊢
    -- 内点は `j = 1` のみ
    have hj1' : j = 1 := by simp only [List.length_cons, List.length_nil] at hj2; omega
    subst hj1'; simpa using hle

#print axioms cornerC2Kind1_holds_cd

end PSS
