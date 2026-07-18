import «8».«8.5-exchV-M-tower»
import «5».«5.1-ancestor-basic»
import «6».«6.2-P-fseq»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-monoT-Red»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»

/-!
# §8.5 `ExchVMTowerResidual` の橋渡し部（条件(V) 橋 `s85b_condV_bridge(3)(4)`）の討伐

- 原文: `tmp/content.md` §8.5「命題（条件(V)の下での Trans と基本列の交換関係）」の
  幾何前提。
- 対象: ビルド済み «8».«8.5-exchV-M-tower»:83 が定義した残差 named Prop
  `ExchVMTowerResidual`（6 連言）のうち、**幾何橋の 2 連言**
  * (a) `hasParent M 1 (Lng M − 1) = true`（Isabelle `s85b_condV_bridge(3)`, wip:57072）、
  * (b) `s84x_jm2 M = transJ0 M`（同 `(4)`）
  を条件(V) ホスト（`STPS`＋`monoT`＋`transCondV`）から **無条件に** 証明し、残る
  4 連言（`(∀ n>1, Oper5Residual)`／`PredNp`／`Lpv`／`L1v`）を狭い named Prop
  `ExchVMCoreResidual` へ切り出す（house pattern：`exchVMres_of_core` の型が
  `ExchVMTowerResidual` そのもの）。これで `ExchVMTowerResidual` 残差は
  6 連言 → 4 連言（`ExchVMCoreResidual`）へ縮む。

## 移植方針

条件(V) 橋 (3)(4)（Isabelle `s85b_condV_bridge`, pss_wip.thy:57072）:
`M ∈ PT_PS ∧ transCondV M` の下で、行1の親辺 `nextR M 1 j₀ (Lng M-1)` を作る。核は
`nextrel1 M j₀ (Lng M-1)` の最小性連言で、これは **行0親最大性チェーン**
（§8.4 `s84c1_anc_le_j0`, wip:52735）に帰着する。Isabelle は `parent_max`
を rtrancl peel で使うが、Lean 側は既存資産
`nextR0_largest_below`（§6.4 行0親最大性の値レベル版）＋ `ancestor_basic_1`（祖先の
狭義増加）で代替する（`8.4-parent-max` の private `s84c1_anc_le_j0_pm` と同一構成を
`_mc` 接尾で複製）。行1一意性は `nextR1_unique_mr`（§6.5）、`hasParent`/`parent`
表示は `hasParent_iff_unique_fseq` / `parent_eq_of_unique_fseq`（§6.2）。

`s84x_jm2 M = parent M 1 (Lng M − 1)` は def 展開。

## 残差 `ExchVMCoreResidual`（4 連言）について

`(∀ n>1, Oper5Residual M n)`（§7.4 Mark 依存、並行 agent が閉包中）／`PredNp`／`Lpv`／
`L1v` は本ファイルでは触らない。`PredNp`/`Lpv`/`L1v` は Isabelle でも adm 枝
（§7.4/§8.4 Mark；Lean 側は `ExchV_scbdec_adm_forms` 残差, `8.5-Trans-fseq-condV`:106）／
非 adm 枝（§8.2 VE 残差）に分かれ、**どちらも Lean 未移植**なので named Prop へ委譲する。

- 依存（すべてビルド済み・main 2843f0c）: «8».«8.5-exchV-M-tower»
  (`ExchVMTowerResidual` / `s84x_jm2` / `s84x_Np` / `s84x_Lp` / `s84x_L` /
  `exchV_tail` / `Oper5Residual` / 推移的に `transJ0` / `transJ1` / `transJm1` /
  `transT2` / `STPS_RTPS` / `STPS_TPS` / `RTPS_TPS`)、
  «5».«5.1-ancestor-basic» (`ancestor_basic_1`)、
  «6».«6.2-P-fseq» (`le0_index_fseq` / `hasParent_iff_unique_fseq` /
  `parent_eq_of_unique_fseq`)、«6».«6.4-FirstNodes-Joints-mono»
  (`nextR0_leR` / `nextR_parent0_of_hasParent` / `nextR0_largest_below`)、
  «6».«6.5-monoT-Red» (`nextR1_unique_mr`)、«6».«6.6-P-condAB»
  (`mono_hasParent_row0`)、«6».«6.6-condAB-coeff» (`parent_lt_of_hasParent`)。
- 訂正: なし。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 `ExchVMCoreResidual`（4 連言）1 本。幾何橋 2 連言は無条件に閉じる。
- Private helper suffix: `_mc`。
-/

namespace PSS

/-! ## 行0親最大性補題（`8.4-parent-max` の private `s84c1_anc_le_j0_pm` を `_mc` 複製） -/

/-- Isabelle `s84c1_anc_le_j0` (wip:52735) の行0版。
`le0 M j (Lng M-1)` かつ `j < Lng M-1` なら `j ≤ transJ0 M`。
`nextR0_largest_below`（行0親最大性の値レベル版）＋ `ancestor_basic_1`（祖先の
狭義増加）で構成する。 -/
private theorem s84c1_anc_le_j0_mc (M : PS) (hMT : TPS M) (hmono : monoT M = true)
    (j1gt : 0 < Lng M - 1) {j : ℕ}
    (jle : le0 M j (Lng M - 1) = true) (jlt : j < Lng M - 1) :
    j ≤ transJ0 M := by
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnextR0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hleR : leR M 0 j (Lng M - 1) = true := by simpa [leR] using jle
  have hgrow : entry M 0 j < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M j (Lng M - 1) (Lng M - 1) hMT jlt (le_refl _) hleR
  exact nextR0_largest_below M (transJ0 M) j (Lng M - 1) hnextR0 jlt hgrow

/-! ## 条件(V) 橋（Isabelle `s85b_condV_bridge(3)(4)`, pss_wip.thy:57072） -/

/-- 条件(V) 下の橋 (3)(4): 行1の親存在 `hasParent M 1 (Lng M-1)` と親値
`s84x_jm2 M = transJ0 M`。核は `nextrel1 M (transJ0 M) (Lng M-1)` の最小性で、
最小性連言は `s84c1_anc_le_j0_mc`（行0親最大性）に帰着する。 -/
private theorem condV_bridge_hp_jm2_mc (M : PS) (hM : TPS M)
    (hmono : monoT M = true) (hcond : transCondV M = true) :
    hasParent M 1 (Lng M - 1) = true ∧ s84x_jm2 M = transJ0 M := by
  -- 条件(V) の算術（`j₀ + 1 < Lng M - 1`, `M_{1,j₀} + 1 = M_{1,j₁}`）
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hmid : entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.1.2
  -- `le0 M j₀ (Lng M-1)`: `j₀` は最終列の行0親
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextR0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hle0 : le0 M (transJ0 M) (Lng M - 1) = true := by
    have hleR0 : leR M 0 (transJ0 M) (Lng M - 1) = true := nextR0_leR M _ _ hnextR0
    simpa [leR] using hleR0
  -- 行1親辺 `nextrel1 M (transJ0 M) (Lng M-1)`
  have hnr1 : nextrel1 M (transJ0 M) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, hle0⟩, ?_⟩
    intro u _
    by_cases hpu : transJ0 M < u
    · by_cases hux : le0 M u (Lng M - 1) = true
      · have hule : u ≤ Lng M - 1 := le0_index_fseq hux
        have hue : u = Lng M - 1 := by
          by_contra hne
          have hult : u < Lng M - 1 := lt_of_le_of_ne hule hne
          have hle : u ≤ transJ0 M :=
            s84c1_anc_le_j0_mc M hM hmono (by omega) hux hult
          omega
        subst hue
        simp
      · simp [hpu, hux]
    · simp [hpu]
  have hnextR1 : nextR M 1 (transJ0 M) (Lng M - 1) = true := by
    simpa [nextR] using hnr1
  have huniq : ∀ y, nextR M 1 y (Lng M - 1) = true → y = transJ0 M := by
    intro y hy; exact nextR1_unique_mr M y (transJ0 M) (Lng M - 1) hy hnextR1
  refine ⟨(hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨transJ0 M, hnextR1, huniq⟩, ?_⟩
  show parent M 1 (Lng M - 1) = transJ0 M
  exact parent_eq_of_unique_fseq M 1 (Lng M - 1) (transJ0 M) hnextR1 huniq

/-! ## 残差 named Prop（`ExchVMTowerResidual` の後半 4 連言） -/

/-- **`ExchVMTowerResidual` の橋 2 連言を落とした狭い残差**。条件(V) ホストの下で
`ExchVMTowerResidual` の後半 4 連言のみを要求する:
`(∀ n>1, Oper5Residual M n)`（§7.4 Mark 依存）／`PredNp`／`Lpv`／`L1v`（adm 枝＝
§7.4/§8.4 Mark、非 adm 枝＝§8.2 VE、どちらも Lean 未移植）。 -/
def ExchVMCoreResidual : Prop :=
  ∀ (M : PS) (s₀ s₁ b₀ b₁ : List Sym), STPS M → monoT M = true → transCondV M = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ →
    (∀ n, 1 < n → Oper5Residual M n) ∧
    Trans (Pred (s84x_Np M)) = Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) ∧
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) ∧
    flatBT (Trans (s84x_L M 1))
      = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: (List.replicate (exchV_tail M 1)
                (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (exchV_tail M 1) b₀).flatten ++ b₁

/-! ## 本体 -/

/-- **`ExchVMTowerResidual` の drop-in**（house pattern）。橋 2 連言
（`hasParent` / `s84x_jm2 = transJ0`）を条件(V) から無条件に供給し、残る 4 連言を
狭い残差 `ExchVMCoreResidual` から受け取る。 -/
theorem exchVMres_of_core (h : ExchVMCoreResidual) : ExchVMTowerResidual := by
  intro M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd₁
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hp, hjm2⟩ := condV_bridge_hp_jm2_mc M hM hmono hcond
  exact ⟨hp, hjm2, h M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd₁⟩

#print axioms exchVMres_of_core

end PSS
