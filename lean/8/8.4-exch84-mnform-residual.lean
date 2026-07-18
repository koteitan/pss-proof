import «8».«8.4-exch84-mnform»

/-!
# §8.4 `MnformResidual` の底葉束への縮約（`mnform_of_residual` の入力供給）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: ビルド済み «8».«8.4-exch84-mnform» が緑モジュロ入力とした残差
  `MnformResidual`（10 連言の底葉束）を、Isabelle `cpx_condIII_mnform`
  (isabelle/layerB/pss_wip.thy:98605) の底読み出しに沿って、**未移植の生 scb タプル**
  `MnformBottomResidual`（＝ `cpx_various_scb_IIIIV` @ `m=1` の出力：c1(kind1)/c2/c3/c4/
  c5/c7 の 6 分解 ＋ `M[1]`/`L₁` の 2 平坦式 ＋ 挿入段 `ins` の flat 則 ＋ `ubeq`）へ縮約する。
  塔帰納より下の底読み出し（`inner`/`k1`/`hM1`/`hL1`/`hLp`/`hPN`）は本ファイルが無条件に閉じる。

## 縮約の内訳（Isabelle `cpx_condIII_mnform` 対応、`ExchVMTowerResidual` の姉妹）

`MnformBottomResidual` は explicit witness `u0 u1 u2 v2 v1 v0` で生タプルを束ね、
`MnformResidual` の出力 witness は `ins`／`s0 = u1++u2`／`b0 = v2++v1`／`s1 = u0`／`b1 = v0`。

| `MnformResidual` の脚 | 本ファイルの導出 |
|---|---|
| `hflat` | 生 `ins` の flat 則（`d4vx_ins_flat` の忠実 twin は未移植）そのまま |
| `hb0rp`/`hb1rp` | `c4`/`c3`（`v2`/`v1`）と `c1`（`v0`）の scb 分解 RP 成分 |
| `hinner` | `c3`→`fbody`（`flat_head_bpHeadT`）＋ `c4`→`fc2` で `wrap`、`isPTB` は `D_{v₁}0` |
| `hk1` | `c1`（kind1）の穴を `princN`（`c3`→`Trans N = D_{e₃} body`）で書き換え |
| `hub` | 生 `ubeq`（Isabelle は `RedCondA`、値葉として保持） |
| `hM1` | 生 `M[1]` 平坦式 ＋ `fA0`（`c2`→`flat_head_bpHeadT`） |
| `hL1` | 生 `L₁` 平坦式（純文字列代数） |
| `hLp` | `c7` scb 分解の展開（穴 `D_{e₂}0`） |
| `hPN` | `c5` scb 分解の展開 ＋ `fA0` |

読み出し補題 = `flat_head_bpHeadT_mr2`（Isabelle `vf2x_flat_head_bpHeadT` wip:69403）、
`princ_of_flat_mr2`（`w84x_flat_head_Dpt`）、`isPTB_Dprin_nat_mr2`（`isPTB_str_Dpt`）。

- 依存（すべてビルド済み・committed main 19dc5fd 以前）: «8».«8.4-exch84-mnform»
  (`MnformResidual`・`Dprin`・`bpHeadT`・`scb_decomp`/`scb_kind1`・`s84x_N`/`s84x_Np`/
  `s84x_L`/`s84x_Lp`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transC2`・`Trans`/`oper`/`entry`/
  `Lng`・`flatBT`/`flatBP`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  底読み出しは無条件に閉じ、残差 `MnformBottomResidual`（`needs` 参照、Isabelle
  `cpx_various_scb_IIIIV` @ `m=1`：REGS/REGSP 正則性を消費するため未移植）のみ。
- Private helper suffix: `_mr2`。
-/

namespace PSS

/-! ## 0. 底読み出し補題（Isabelle `vf2x_flat_head_bpHeadT` / `w84x_flat_head_Dpt` / `isPTB_str_Dpt`） -/

/-- `flatBT t = Dsym v :: rest` なら `flatBT (bpHeadT t) = rest`
（Isabelle `vf2x_flat_head_bpHeadT`, layerB/pss_wip.thy:69403）。 -/
private theorem flat_head_bpHeadT_mr2 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : flatBT (bpHeadT t) = rest := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      simp only [bpHeadT]; exact h.2
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `flatBT t = Dsym v :: rest` なら `t = D_v (bpHeadT t)`（主頭の読み戻し、
Isabelle `w84x_flat_head_Dpt`）。 -/
private theorem princ_of_flat_mr2 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : t = Dprin v (bpHeadT t) := by
  obtain ⟨xs⟩ := t
  match xs with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      simp only [flatBT, flatBP, List.cons.injEq] at h
      obtain ⟨h1, _⟩ := h
      simp only [Sym.dsym.injEq] at h1
      simp only [bpHeadT, Dprin, h1]
  | .db u a :: .db u2 a2 :: qs =>
      simp only [flatBT, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h

/-- `isPTB_str (flatBT (D_{n} 0_B))`（Isabelle `isPTB_str_Dpt`）。 -/
private theorem isPTB_Dprin_nat_mr2 (n : ℕ) :
    isPTB_str (flatBT (Dprin (n : ℕ∞) BZero)) :=
  ⟨.db (n : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩

/-! ## 1. 生 scb タプル残差（Isabelle `cpx_various_scb_IIIIV` @ `m=1`、REGS/REGSP を消費） -/

/-- **`mnform` 脚の未移植底束**。§8.4 の condIII/(IV) ホスト `M` について、`m=1` の
L6 タプルの生データを explicit witness `u0 u1 u2 v2 v1 v0` で束ねる:
挿入段 `ins`（flat 則）、`c1`（`Trans M` の kind1 分解、穴 `Trans N`）、`c2`/`c3`
（`Pred N`/`N` の分解、頭 `D_{e₃}`）、`c4`（`transC2` の分解、穴 `D_{v₁}0`）、`c5`
（`Pred Np` の分解、頭 `D_{e₂}`）、`c7`（`Lp` の分解、穴 `D_{e₂}0`）、`M[1]`/`L₁` の
2 平坦式、`ubeq`。Isabelle `cpx_various_scb_IIIIV`（L6 タプル）は REGS/REGSP の
Red 正則性を消費するため未移植（`Exch84_scbDecompPkg` と同じ残差境界を `mnform` 脚へ拡張）。 -/
def MnformBottomResidual : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    ∃ (ins : BT → BT) (u0 u1 u2 v2 v1 v0 : List Sym),
      -- 挿入段の flat 則（穴 `dsym ub`、`b0 = v2++v1`）
      (∀ X, flatBT (ins X)
          = (u1 ++ u2) ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞)
              :: flatBT X ++ (v2 ++ v1)) ∧
      -- `c1`: `Trans M` の kind1 分解（穴 `Trans N`）
      scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 ∧
      -- `c2`: `Trans (Pred N)` の分解（頭 `D_{e₃}`）
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      -- `c3`: `Trans N` の分解（頭 `D_{e₃}`）
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      -- `c4`: `transC2` の分解（穴 `D_{v₁}0`）
      scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 ∧
      -- `c5`: `Trans (Pred Np)` の分解（頭 `D_{e₂}`）
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      -- `c7`: `Trans (Lp)` の分解（穴 `D_{e₂}0`）
      scb_decomp (Trans (s84x_Lp M))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1 ++ u2)
        (flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)) (v2 ++ v1) ∧
      -- `L₁` 平坦式（塔深さ 1）
      flatBT (Trans (s84x_L M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: (u1 ++ u2 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
            ++ [Sym.zero] ++ (v2 ++ v1) ++ v0 ∧
      -- `M[1]` 平坦式（塔深さ 0）
      flatBT (Trans (oper M 1))
        = u0 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            :: u1 ++ flatBT (transC1 M) ++ v1 ++ v0 ∧
      -- `ubeq`
      entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1

/-! ## 2. 縮約本体（house pattern） -/

/-- **`MnformResidual` の drop-in**（house pattern）。生 scb タプル `MnformBottomResidual`
から底読み出し（`inner`/`k1`/`hM1`/`hL1`/`hLp`/`hPN`）を無条件に組み、
`MnformResidual M`（«8».«8.4-exch84-mnform»）を出す。Isabelle `cpx_condIII_mnform`
(layerB/pss_wip.thy:98605) の底読み出しに 1:1 対応。 -/
theorem mnformResidual_holds (hbot : MnformBottomResidual) :
    ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) → MnformResidual M := by
  intro M hST hmono hp hj1 hcond
  obtain ⟨ins, u0, u1, u2, v2, v1, v0, hflat, hc1, hc2, hc3, hc4, hc5, hc7, hL1flat,
    hM1flat, hub⟩ := hbot M hST hmono hp hj1 hcond
  -- `c3` の頭形（`Trans N = D_{e₃} :: ...`）→ `princN`、`fbody`
  have c3flat : flatBT (Trans (s84x_N M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: (u1 ++ flatBT (transC2 M) ++ v1) := by
    have h := hc3.1; simpa [List.cons_append] using h
  have princN : Trans (s84x_N M)
      = Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) (bpHeadT (Trans (s84x_N M))) :=
    princ_of_flat_mr2 c3flat
  have fbody : flatBT (bpHeadT (Trans (s84x_N M))) = u1 ++ flatBT (transC2 M) ++ v1 :=
    flat_head_bpHeadT_mr2 c3flat
  -- `c2` の頭形 → `fA0`
  have c2flat : flatBT (Trans (Pred (s84x_N M)))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: (u1 ++ flatBT (transC1 M) ++ v1) := by
    have h := hc2.1; simpa [List.cons_append] using h
  have fA0 : flatBT (bpHeadT (Trans (Pred (s84x_N M)))) = u1 ++ flatBT (transC1 M) ++ v1 :=
    flat_head_bpHeadT_mr2 c2flat
  -- `b0 = v2++v1`（全 RP）、`b1 = v0`（全 RP）
  have hb0rp : ∀ x ∈ (v2 ++ v1), x = Sym.rp := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hc4.2.2 x h
    · exact hc3.2.2 x h
  have hb1rp : ∀ x ∈ v0, x = Sym.rp := hc1.1.2.2
  -- 出力束
  refine ⟨ins, u1 ++ u2, v2 ++ v1, u0, v0, hflat, hb0rp, hb1rp, ?_, ?_, hub, ?_, ?_, ?_, ?_⟩
  · -- `hinner`
    refine ⟨?_, fun _ => isPTB_Dprin_nat_mr2 (entry M 1 (Lng M - 1)), hb0rp⟩
    rw [fbody, hc4.1]
    simp only [List.append_assoc]
  · -- `hk1`
    have hbeq : flatBT (Trans (s84x_N M))
        = flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            (bpHeadT (Trans (s84x_N M)))) := congrArg flatBT princN
    exact hbeq ▸ hc1
  · -- `hM1`
    rw [hM1flat, fA0]
    simp only [List.cons_append, List.append_assoc]
  · -- `hL1`
    have h := hL1flat
    simpa [List.cons_append, List.append_assoc] using h
  · -- `hLp`
    have hDe2 : flatBT (Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) BZero)
        = [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] := rfl
    have h := hc7.1
    rw [hDe2] at h
    simpa [List.cons_append, List.append_assoc] using h
  · -- `hPN`
    have c5flat : flatBT (Trans (Pred (s84x_Np M)))
        = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
            :: (u1 ++ flatBT (transC1 M) ++ v1) := by
      have h := hc5.1; simpa [List.cons_append] using h
    rw [c5flat, ← fA0]

#print axioms mnformResidual_holds

end PSS
