import «8».«8.2-condV-VE-close»

/-!
# §8.2 条件(V) terminal-slice `Trans` の無条件閉包

- 原文: `tmp/content.md` L3664 付近。
- Isabelle: `m_8_2_condV_terminal_slice_Trans` (`layerB/pss_wip.thy`:77102)
  = `m_8_2_condV_terminal_slice_Trans_modVE` + `vcx_VE_all`。
- 依存: `8.2-condV-terminal-slice-Trans` の `_modVE` 定理と
  `8.2-condV-VE-close` の無条件 `vcx_VE_all`。import cycle を避けるため
  後置の close モジュールで配線する。
- 状態: ✅ 完了（sorry 0）。
-/

namespace PSS

/-- **§8.2 補題（条件(V)の下での終切片と `Trans` の関係）**。
Isabelle `m_8_2_condV_terminal_slice_Trans` の残差なしの逐語形。 -/
theorem condV_terminal_slice_Trans (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hreg : m < (Joints M).getD ((Br M).length - 1) 0 ∨
      (m = (Joints M).getD ((Br M).length - 1) 0 ∧
        entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
        descendingB (Br M) = true)) :
    ∃! t₁ : BT, Trans M = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans (seg M m (Lng M - 1)) = Dprin (entry M 1 m : ℕ∞) t₁ := by
  apply condV_terminal_slice_Trans_modVE M m hR hmono hBrne hreg
  exact vcx_VE_all m M ⟨hR, hmono, hBrne, hreg⟩

#print axioms condV_terminal_slice_Trans

end PSS
