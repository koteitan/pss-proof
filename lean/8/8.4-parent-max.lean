import «8».«8.4-exch84-regs»
import «6».«6.4-FirstNodes-Joints-mono»

/-!
# §8.4 行0親最大性チェーン — `Regs_jm2_lt_transJ0` の discharge

- 原文: `tmp/content.md` §8.4（補題（条件(III)～(VI)の下での展開規則の基本性質），
  content.md 4389, 4413-4417）part (1): 条件(III)/(IV) の下では行1の親 `j₋₂`
  （= `s84x_jm2 M`）は行0の親 `j₀`（= `transJ0 M`）より真に手前。
- 移植元（Isabelle）:
  * `m_8_4_oper_props_1(1)` (`isabelle/layerB/pss_wip.thy:52810`): 主張本体。
    `entry M 1 j₋₂ < entry M 1 j₀`（`s84c1_jm2_basic(2)` ＋ (III)/(IV) の `ge`）から
    `j₋₂ ≠ j₀`、これと `j₋₂ ≤ j₀` を合わせて `<`。
  * `s84c1_jm2_le_j0` (同 :52746): `s84x_jm2 M ≤ transJ0 M`。
  * `s84c1_anc_le_j0` (同 :52735): `le0 M j (Lng M-1)` ∧ `j < Lng M-1` ⟹ `j ≤ transJ0 M`。
    Isabelle は `parent_max` (`pss_mechanized.thy:4969`) を rtrancl peel で使うが、
    Lean は **`nextR0_largest_below`**（`6.4-FirstNodes-Joints-mono`、行0の親最大性を
    値レベルで既に持つ）＋ `ancestor_basic_1`（祖先の狭義増加）で置き換えた
    （parent_max の新規移植は不要 — CONTENT-GREP で既存資産を確認）。
  * `s84c1_hp0` (同 :52702) / `s84c1_nextR0_j0(1)` (同 :52711): 行0の親存在と親辺。
    Lean は `mono_hasParent_row0`（§6.6）＋ `nextR_parent0_of_hasParent`（§6.4）。

- Lean 語彙: `parent_max` (i=0) ＝ `nextR0_largest_below`、`s84c1_jm2_basic`
  ＝ 8.4-s84x-vocab-run の同名定理、`transJ0 M = lastParent M = parent M 0 (Lng M-1)`
  （defeq）、`transCondIII/IV` の中間連言が `ge : M_{1,j₁} ≤ M_{1,j₀}`。

- 依存（すべてビルド済み）: «8».«8.4-exch84-regs»（`Regs_jm2_lt_transJ0`／推移的に
  `s84x_jm2`・`s84c1_jm2_basic`・`transJ0`・`transCondIII`/`transCondIV`・`STPS_RTPS`・
  `RTPS_TPS`・`mono_hasParent_row0`・`ancestor_basic_1`）、
  «6».«6.4-FirstNodes-Joints-mono»（`nextR0_largest_below`・`nextR_parent0_of_hasParent`）。

- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `regs_jm2_lt_transJ0_holds : Regs_jm2_lt_transJ0` を house pattern で無条件 discharge。
  これで `regS_holds` の第3残差が閉じる（残り `Regs_jm3Marked`・`Regs_MCOND`）。
- Private helper suffix: `_pm`。
-/

namespace PSS

/-- Isabelle `s84c1_anc_le_j0` (wip:52735) の行0版。
`le0 M j (Lng M-1)` かつ `j < Lng M-1` なら `j ≤ transJ0 M`。
Isabelle の `parent_max` 経由を Lean の `nextR0_largest_below`（行0親最大性の
値レベル版）＋ `ancestor_basic_1`（祖先の狭義増加）で構成する。 -/
private theorem s84c1_anc_le_j0_pm (M : PS) (hMT : TPS M) (hmono : monoT M = true)
    (j1gt : 0 < Lng M - 1) {j : ℕ}
    (jle : le0 M j (Lng M - 1) = true) (jlt : j < Lng M - 1) :
    j ≤ transJ0 M := by
  -- 行0の親存在（最終列 `j₁ = Lng M - 1`）
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  -- 親辺 `nextR M 0 j₀ j₁`（`transJ0 M = parent M 0 (Lng M - 1)` defeq）
  have hnextR0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  -- `entry M 0 j < entry M 0 j₁`（狭義増加）
  have hleR : leR M 0 j (Lng M - 1) = true := by simpa [leR] using jle
  have hgrow : entry M 0 j < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M j (Lng M - 1) (Lng M - 1) hMT jlt (le_refl _) hleR
  -- 行0親最大性
  exact nextR0_largest_below M (transJ0 M) j (Lng M - 1) hnextR0 jlt hgrow

/-- Isabelle `m_8_4_oper_props_1(1)` (wip:52810) の drop-in（house pattern）。
条件(III)/(IV) の下で `s84x_jm2 M < transJ0 M`。 -/
theorem regs_jm2_lt_transJ0_holds : Regs_jm2_lt_transJ0 := by
  intro M hST hmono hp j1gt branch
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  -- (III)/(IV) の中間連言: `M_{1,j₁} ≤ M_{1,j₀}`
  have ge : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    rcases branch with h | h
    · unfold transCondIII at h
      simp only [lastIdx, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    · unfold transCondIV at h
      simp only [lastIdx, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
  -- `M_{1,j₋₂} < M_{1,j₁} ≤ M_{1,j₀}` ⟹ `M_{1,j₋₂} < M_{1,j₀}`
  have e1lt : entry M 1 (s84x_jm2 M) < entry M 1 (transJ0 M) := by
    have h := (s84c1_jm2_basic M hp).2.1
    omega
  -- `j₋₂ ≤ j₀`
  obtain ⟨jm2lt, _, le0j⟩ := s84c1_jm2_basic M hp
  have jm2_le : s84x_jm2 M ≤ transJ0 M :=
    s84c1_anc_le_j0_pm M hMT hmono (by omega) le0j jm2lt
  -- `M_{1,·}` の狭義性から `j₋₂ ≠ j₀`、`≤` と合わせて `<`
  have hne : s84x_jm2 M ≠ transJ0 M := by
    intro heq; rw [heq] at e1lt; exact absurd e1lt (lt_irrefl _)
  omega

#print axioms regs_jm2_lt_transJ0_holds

end PSS
