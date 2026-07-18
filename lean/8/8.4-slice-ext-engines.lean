import «8».«8.4-slice-ext-tuple»
import «8».«8.4-c2hole-engine»

/-!
# §8.4 `SliceExtTupleEngines_st` の縮約（`L₁` 平坦式を c2hole エンジンで無条件討伐）

- 原文: `tmp/content.md` §8.4。ブループリント: Isabelle
  `m_8_4_various_scb_IIIIV_from_slice`（`isabelle/layerB/pss_wip.thy`:60034）の
  engine 入力（slice 分解 ＋ `d4vx_ins` flat 則 ＋ kind1）。
- 対象: ビルド済み «8».«8.4-slice-ext-tuple» が露出した tight named 残差
  `SliceExtTupleEngines_st`（dec1 エンジンで `c1` の scb 分解 witness `(u0,v0)` を
  無条件生成した後の、canonical `(u0,v0)` に対する 3 連言: `c1` の kind1 shape ＋
  `c7`（右端置換）＋ `L₁` 平坦式）。

## 本ファイルの寄与

3 連言のうち **`L₁` 平坦式（塔基底、Isabelle `base5`）を本ファイルで完全に組み立てる**。
Isabelle 証明の `base5`（wip:60231）は
`flatBT (Trans (s84x_L M 1)) = s0 @ D_{j₋₃} # (s1' @ s2 @ [D_{j₋₂}]) @ [Z] @ (w' @ b1') @ b0`
を、
- `s84c2_Trans_c2_decomp`（Lean `Trans_c1_c2_decomp`, «8».«8.3-condII-masterCF»）で
  `Trans (s84x_L M 1)` と `Trans (Pred (s84x_L M 1))` の共有 scb 分解 `(s1L,b1L)` を取り、
- 右端穴エンジン `c2hole_scb_ch`（«8».«8.4-c2hole-engine»）を穴 `a = M₁,j₁` / `a = M₁,j₋₂`
  で埋めて `(u2,v2)` を pin（`scb_unique_decomp_unconditional`）し、
- 合成 `scb_compose`（`Trans M` の内側 marked `Trans (s84x_N M)`）＋一意性で
  `s1 = u0 @ D_{j₋₃} # u1`, `b1 = v1 @ v0` を pin し、
- `flatBT (Trans (s84x_L M 1)) = s1 @ flatBT (c2hole_ch M M₁,j₋₂) @ b1` を組む。

**未移植の入力**は raw な §8.4 L₁ slice 幾何のみ（`s84d_L1_data` ＋ `s84d_c2hole_L1`）で、
tight named Prop `L1SliceData_se` として露出する（これらは L₁ 塔基底列 `s84x_L M 1` の
`Trans (Pred)`/`transC1`/`transC2` を `M` 側の語彙へ結ぶ純幾何。c2hole 差し替えは
`transC2 (s84x_L M 1) = c2hole_ch M M₁,j₋₂`）。

残る 2 連言（未移植 engine）は tight named Prop として露出:
- `Kind1Shape_se`: `c1` の kind1 shape（scb 分解 `hd0` を第 1 種へ昇格。
  Isabelle `s84c3_RightAnces_chain` ＋条件(III)/(IV) 分類）。
- `C7Rightend_se`: `c7`（`Trans (s84x_Lp M)` の分解、Isabelle `m_8_4_rightend_Trans` ＋
  入力に無い `d4b`）。

- 依存（すべてビルド済み・main 6739865）: «8».«8.4-slice-ext-tuple»
  （`SliceExtTupleEngines_st`・`s84x_*`・`transC1`/`transC2`・`Trans`/`scb_decomp`/
  `scb_kind1`・`Dprin`/`flatBT`/`BZero`・`STPS`/`STPS_RTPS`/`RTPS_TPS`・
  transitively `Trans_c1_c2_decomp`/`scb_compose`/`scb_unique_decomp_unconditional`）、
  «8».«8.4-c2hole-engine»（`c2hole_ch`/`c2hole_at_j1_ch`/`c2hole_scb_ch`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `L₁` 平坦式を無条件討伐。残差 = `Kind1Shape_se`（kind1 昇格）＋ `C7Rightend_se`（右端）＋
  `L1SliceData_se`（L₁ slice 幾何）。
- Private helper suffix: `_se`。
-/

namespace PSS

/-! ## 0. 局所補助 -/

/-- `flatBT t = D_u :: rest` なら `t` は単一 principal `D_u a`（«8».«8.4-exch84-from-slice»
の private `flatBT_head_dsym_fs` の複製）。 -/
private theorem flatBT_head_dsym_se {t : BT} {u : ℕ∞} {rest : List Sym}
    (h : flatBT t = .dsym u :: rest) : ∃ a, t = .trm [.db u a] := by
  rcases t with ⟨ps⟩
  match ps with
  | [] => simp [flatBT] at h
  | [BP.db u' a] =>
      refine ⟨a, ?_⟩
      have : Sym.dsym u' = Sym.dsym u := by
        simpa [flatBT, flatBP] using congrArg List.head? h
      simp_all
  | p :: q :: ps => simp [flatBT] at h

/-- `Trans (Pred M) ≠ 0_B`（`1 < Lng M - 1` 下）。«8».«8.4-slicepkg-residuals» の
private `transT1_ne_sr` と同型。 -/
private theorem transPred_ne_bzero_se (M : PS) (hMR : RTPS M) (hj1 : 1 < Lng M - 1) :
    Trans (Pred M) ≠ BZero := by
  have hlen : 1 < Lng M := by omega
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  exact (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP

/-! ## 1. 露出する named 残差（未移植 engine の tight な葉） -/

/-- 残差 (kind1 shape): `c1` の scb 分解 `hd0`（本ファイル caller が dec1 エンジンで供給）を
[Buc1] 第 1 種分解へ昇格。Isabelle `s84c3_RightAnces_chain` ＋条件(III)/(IV) 分類。純増
スパインは第 1 種でないので、条件(III)/(IV) の深い機構を要する。**未移植**。 -/
def Kind1Shape_se : Prop :=
  ∀ (M : PS) (u0 v0 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 →
    scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0

/-- 残差 (c7): `Trans (s84x_Lp M)` の分解（穴 `D_{e₂} 0`）。Isabelle `m_8_4_rightend_Trans`
（右端置換）＋ `d4b`（`Trans (s84x_Np M)` の分解、本残差の入力に無い）。**未移植**。 -/
def C7Rightend_se : Prop :=
  ∀ (M : PS) (u1 u2 v1 v2 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans (Pred (s84x_N M)))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 →
    scb_decomp (transC2 M) u2
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 →
    scb_decomp (Trans (Pred (s84x_Np M)))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    scb_decomp (Trans (s84x_Lp M))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
      (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1)

/-- 残差 (L₁ slice 幾何): 塔基底列 `s84x_L M 1` の `Trans (Pred)`/`transC1`/`transC2` を
`M` 側の語彙へ結ぶ純幾何。Isabelle `s84d_L1_data`（`(1)`/`(2)`/`(3)`/`(7)`/`(11)`）＋
`s84d_c2hole_L1`（`transC2 (s84x_L M 1) = s84d_c2hole M M₁,j₋₂`）。**未移植**。
本ファイルはこの package から `L₁` 平坦式を無条件に組む。 -/
def L1SliceData_se : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
      RTPS (s84x_L M 1) ∧ monoT (s84x_L M 1) = true ∧ 1 < Lng (s84x_L M 1) ∧
      Trans (Pred (s84x_L M 1)) = Trans (Pred M) ∧
      transC1 (s84x_L M 1) = transC1 M ∧
      transC2 (s84x_L M 1) = c2hole_ch M (entry M 1 (s84x_jm2 M))

/-! ## 2. `L₁` 平坦式の組み立て（Isabelle `base5`, wip:60231） -/

/-- **`base5` の Lean 版**。c2hole エンジン ＋ 合成 ＋一意性で `L₁` 平坦式を組む。 -/
private theorem l1Base_se (hLdat : L1SliceData_se)
    (M : PS) (u1 u2 v1 v2 u0 v0 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondIII M = true ∨ transCondIV M = true)
    (d2 : scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1)
    (d4c2 : scb_decomp (transC2 M) u2
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2)
    (hd0 : scb_decomp (Trans M) u0 (flatBT (Trans (s84x_N M))) v0) :
    flatBT (Trans (s84x_L M 1))
      = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
          ++ [Sym.zero] ++ (v2 ++ v1) ++ v0 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlenM : 1 < Lng M := by omega
  have hT1M : Trans (Pred M) ≠ BZero := transPred_ne_bzero_se M hMR hj1
  -- c2hole エンジン
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hT1' : transT1 M ≠ BZero := by simpa [transT1] using hT1M
  obtain ⟨w, w', W⟩ := c2hole_scb_ch M hMR hMT hmono hJ1pos hT1'
  -- 穴 `a = M₁,j₁`（= `transC2 M`）で pin `(u2, v2)`
  have Wj1 : scb_decomp (transC2 M) (Sym.dsym (transV M) :: w)
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) w' :=
    W (entry M 1 (Lng M - 1))
  obtain ⟨hu2, hv2⟩ := scb_unique_decomp_unconditional (transC2 M) u2
    (Sym.dsym (transV M) :: w)
    (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 w' d4c2 Wj1
  -- 穴 `a = M₁,j₋₂`（= `transC2 (s84x_L M 1)`）
  have Wjm2 : scb_decomp (c2hole_ch M (entry M 1 (s84x_jm2 M))) u2
      (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) v2 := by
    rw [hu2, hv2]; exact W (entry M 1 (s84x_jm2 M))
  -- `Trans (s84x_N M)` は単一 principal
  have hTNhead : flatBT (Trans (s84x_N M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (u1 ++ flatBT (transC2 M) ++ v1) := by
    have h := d2.1
    simpa [List.cons_append] using h
  obtain ⟨bodyN, hTNeq⟩ := flatBT_head_dsym_se hTNhead
  have hc0N : ∃ p, Trans (s84x_N M) = BT.trm [p] := ⟨_, hTNeq⟩
  -- `M` の共有 wrapper `(s1, b1)`
  obtain ⟨s1, b1, dc1, dc2M⟩ := Trans_c1_c2_decomp M hMR hmono hlenM hT1M
  -- pin `s1 = u0 @ D_{j₋₃} # u1`, `b1 = v1 @ v0`
  have comp1 := scb_compose (Trans M) (Trans (s84x_N M)) u0
    (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1)
    (flatBT (transC2 M)) v1 v0 hc0N hd0 d2
  obtain ⟨hs1, hb1⟩ := scb_unique_decomp_unconditional (Trans M) s1
    (u0 ++ (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1))
    (flatBT (transC2 M)) b1 (v1 ++ v0) dc2M comp1
  -- L₁ slice 幾何
  obtain ⟨hLR, hLmono, hLlen, hLpred, hLc1, hLc2⟩ := hLdat M hST hmono hp hj1 hcond
  have hT1L : Trans (Pred (s84x_L M 1)) ≠ BZero := by rw [hLpred]; exact hT1M
  obtain ⟨s1L, b1L, dc1L, dc2L⟩ := Trans_c1_c2_decomp (s84x_L M 1) hLR hLmono hLlen hT1L
  -- `dc1L` を `M` 側の語彙へ移送し `(s1L,b1L) = (s1,b1)` を pin
  rw [hLpred, hLc1] at dc1L
  obtain ⟨hs1L, hb1L⟩ := scb_unique_decomp_unconditional (Trans (Pred M)) s1L s1
    (flatBT (transC1 M)) b1L b1 dc1L dc1
  -- 平坦式の組み立て
  have f2 : flatBT (c2hole_ch M (entry M 1 (s84x_jm2 M)))
      = u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ v2 := by
    have h := Wjm2.1
    simpa [Dprin, flatBT, flatBP, BZero] using h
  have f1 := dc2L.1
  rw [hs1L, hb1L, hLc2, f2, hs1, hb1] at f1
  rw [f1]
  simp [List.append_assoc]

/-! ## 3. 縮約本体（house pattern） -/

/-- **`SliceExtTupleEngines_st` の drop-in**（house pattern）。3 連言のうち `L₁` 平坦式を
c2hole エンジンで無条件に組み、kind1 shape と `c7` は named 残差から取る。 -/
theorem sliceExtTupleEngines_of_residuals
    (hK : Kind1Shape_se) (hC7 : C7Rightend_se) (hLdat : L1SliceData_se) :
    SliceExtTupleEngines_st := by
  intro M u1 u2 v1 v2 u0 v0 hST hmono hp hj1 hcond dP d2 d4c2 d4a hd0
  refine ⟨?_, ?_, ?_⟩
  · exact hK M u0 v0 hST hmono hp hj1 hcond hd0
  · exact hC7 M u1 u2 v1 v2 hST hmono hp hj1 hcond dP d2 d4c2 d4a
  · exact l1Base_se hLdat M u1 u2 v1 v2 u0 v0 hST hmono hp hj1 hcond d2 d4c2 hd0

#print axioms sliceExtTupleEngines_of_residuals

/-- 3 残差から from_slice の底タプル残差 `SliceExtTupleResidual` までの全鎖
（`sliceExtTupleResidual_holds`（«8».«8.4-slice-ext-tuple»）と合成）。 -/
theorem sliceExtTupleResidual_of_engines_se
    (hK : Kind1Shape_se) (hC7 : C7Rightend_se) (hLdat : L1SliceData_se) :
    SliceExtTupleResidual :=
  sliceExtTupleResidual_holds (sliceExtTupleEngines_of_residuals hK hC7 hLdat)

#print axioms sliceExtTupleResidual_of_engines_se

end PSS
