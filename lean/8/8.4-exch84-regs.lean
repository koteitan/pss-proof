import «8».«8.2-condV-VE-base»
import «8».«8.4-s84x-vocab-run»
import «6».«6.3-admof-slice»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.2-P-fseq»
import «6».«6.6-P-condAB»
import «6».«6.6-condAB-coeff»

/-!
# §8.4 交換パッケージの `REGS` 脚（`mcx_regS`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  `REGS` は `oi5_IIIIV_pkg`（`Exch84_condIIIIV_pkg` の Isabelle 原形、
  `isabelle/layerC/pss_scratch.thy:1213`）が discharge する 3 束
  （`REGS`/`REGSP`/`RUN`）のうちの `REGS`。
- 移植元（Isabelle）:
  * `mcx_regS` (`isabelle/layerB/pss_wip.thy:94021`):
    `crx_regS_red_of_mcond ∘ mcx_MCOND_RN`。
  * `crx_regS_red_of_mcond` (同 :89979): `MCOND` の下で
    `cfbx_reg (j₋₂-j₋₃) (Red N)` を組み立てる（memberships / `Br ≠ []` /
    `descending` は完全に落ちる）。
  * `mcx_MCOND_RN` (同 :93796): `MCOND` 論理和そのもの（`≤` core ＝
    `mcx_d_le_last_joint` :93647 をインライン ＋ 等号枝の対角性）。
  * 支持: `s84d_jm3_Marked` (同 :58783)、`m_8_4_oper_props_1` (同 :52810)、
    `crx_trmax_run` (同 :89879)。

- Lean 語彙: `cfbx_reg` = `VEReg`（«8».«8.2-condV-VE-base»:79、逐語移植済）、
  `cfbx_j1p` = `VEj1p`（同 :72）。したがって本ファイルは新規定義を作らず、
  `REGS` を `VEReg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))` として述べる。

- 本ファイルの分担:
  * `regS_of_mcond_rg`（= `crx_regS_red_of_mcond`）: `MCOND` ＋ 支持事実
    （`Marked`・`j₋₂ < Lng M - 2`）から `VEReg …` を**完全証明**。核は `Br (Red N) ≠ []`
    （最終列の行1親が非隣接 ⟹ 幹はスライスの右端まで届かない）を `IncrFirst` 転送で示す部分。
  * `regS_holds`（= `mcx_regS`, house pattern）: 露出した支持 Prop
    （`Regs_jm3Marked`, `Regs_jm2_lt_transJ0`, `Regs_MCOND`）から `Regs_mcx_regS` を出す。
    `j₋₂ < Lng M - 2` は `Regs_jm2_lt_transJ0`（= `m_8_4_oper_props_1(1)`）と
    `transJ0 M < Lng M - 1`（`mono_hasParent_row0` ＋ `parent_lt_of_hasParent` で
    **本ファイル内で証明**）を合成する。

- 残差（露出した named Prop、いずれも Isabelle で証明済＝bundle は充足可能）:
  * `Regs_jm3Marked`  = `s84d_jm3_Marked`（`§6.3` 許容性 chain 未移植）。
  * `Regs_jm2_lt_transJ0` = `m_8_4_oper_props_1(1)`（`§8.4` 親最大性 chain 未移植）。
  * `Regs_MCOND` = `mcx_MCOND_RN`（sharp な対角残差。python `_r33_eq3.py` 検証済）。

- 依存（すべてビルド済み）: «8».«8.2-condV-VE-base»（`VEReg`/`VEj1p`/`descendingB`/
  `DTPS`/`DTPS_iff`/`standard_slice_Red_strongmono`／推移的に `TrMax_trunk_step`/
  `nextR1_seg_adm`/`nextR1_unique_mr`）、«8».«8.4-s84x-vocab-run»（`s84x_*`/
  `s84c1_jm2_basic`/`s84c1_nextR1_jm2`）、«6».«6.3-admof-slice»（`Adm_le`）、
  «6».«6.5-Lng-Red-invariance»（`Lng_Red_invariance`）、
  «6».«6.5-Red-IncrFirst-invariance»（`nextR_IncrFirstN_ri`）、
  «6».«6.6-ancestor-slice-Red-IncrFirst»（`ancestor_slice_Red_IncrFirst`）、
  «6».«6.2-P-fseq»（`P_nonempty`）、«6».«6.6-P-condAB»（`mono_hasParent_row0`）、
  «6».«6.6-condAB-coeff»（`parent_lt_of_hasParent`）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `regS_of_mcond_rg` は完全証明。残差 = 上記 3 named Prop。
- Private helper suffix: `_rg`。
-/

namespace PSS

/-! ## 1. 露出する named Prop（`REGS` 支持事実） -/

/-- Isabelle `s84d_jm3_Marked` (layerB/pss_wip.thy:58783)。
`j₋₃ = Adm M j₋₂` は基点であり、`j₋₃ ≤ j₋₂ < Lng M - 1`。 -/
def Regs_jm3Marked : Prop :=
  ∀ M : PS, RTPS M → TPS M → hasParent M 1 (Lng M - 1) = true →
    Marked M (s84x_jm3 M) ∧ s84x_jm3 M ≤ s84x_jm2 M ∧ s84x_jm2 M < Lng M - 1

/-- Isabelle `m_8_4_oper_props_1(1)` (layerB/pss_wip.thy:52810)。
条件(III)/(IV) の下では行1の親 `j₋₂` は行0の親 `j₀` より真に手前。 -/
def Regs_jm2_lt_transJ0 : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm2 M < transJ0 M

/-- Isabelle `mcx_MCOND_RN` (layerB/pss_wip.thy:93796)。
簡約スライス `Red N` の最終枝に対する `m`-条件の論理和（`m < 最終 joint`、
または `m = 最終 joint` かつ最終枝左端が対角）。sharp な対角残差。 -/
def Regs_MCOND : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < s84x_jm2 M →
    s84x_jm2 M - s84x_jm3 M
        < (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
      ∨ (s84x_jm2 M - s84x_jm3 M
           = (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
         ∧ entry (Red (s84x_N M)) 0 (VEj1p (Red (s84x_N M)))
           = entry (Red (s84x_N M)) 1 (VEj1p (Red (s84x_N M))))

/-- Isabelle `mcx_regS` (layerB/pss_wip.thy:94021) を Lean 語彙で述べたもの
（`cfbx_reg` = `VEReg`）。`REGS` 脚そのもの。 -/
def Regs_mcx_regS : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < s84x_jm2 M →
    VEReg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))

/-! ## 2. `crx_regS_red_of_mcond`: `MCOND` から `VEReg` を組み立てる -/

/-- Isabelle `crx_regS_red_of_mcond` (layerB/pss_wip.thy:89979)。
`MCOND` の論理和と支持事実（`Marked M j₋₃`、`j₋₂ < Lng M - 2`）から、
簡約スライス `Red (s84x_N M)` に対する `VEReg (j₋₂-j₋₃) …` を完全に組み立てる。

memberships（`RTPS`/`monoT`/`descendingB`）は `standard_slice_Red_strongmono`
＋ `DTPS_iff` から、`Br ≠ []` は最終列の行1親が非隣接であること（`notnx1`）を
`IncrFirst` 転送でスライスへ移して示す。 -/
theorem regS_of_mcond_rg (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (j1gt : 1 < Lng M - 1)
    (hMarked : Marked M (s84x_jm3 M))
    (hjm2pred : s84x_jm2 M < Lng M - 2)
    (hMCOND : s84x_jm2 M - s84x_jm3 M
          < (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
        ∨ (s84x_jm2 M - s84x_jm3 M
             = (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
           ∧ entry (Red (s84x_N M)) 0 (VEj1p (Red (s84x_N M)))
             = entry (Red (s84x_N M)) 1 (VEj1p (Red (s84x_N M))))) :
    VEReg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true := hMarked.2.2
  -- 簡約スライスの `DTPS` 事実
  have hRcDT : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  have RNRT : RTPS (Red (s84x_N M)) := ((DTPS_iff _).mp hRcDT).1
  have monoRN : monoT (Red (s84x_N M)) = true := ((DTPS_iff _).mp hRcDT).2.1
  have descRN : descendingB (Br (Red (s84x_N M))) = true := ((DTPS_iff _).mp hRcDT).2.2
  have RNT : TPS (Red (s84x_N M)) := RTPS_TPS _ RNRT
  -- スライスの長さ
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have LngRN : Lng (Red (s84x_N M)) = Lng (s84x_N M) := Lng_Red_invariance (s84x_N M) NT
  -- `N = IncrFirst^dd (Red N)`
  have segIF : s84x_N M
      = IncrFirstN (entry M 0 (s84x_jm3 M) - entry M 1 (s84x_jm3 M)) (Red (s84x_N M)) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm3 M) (Lng M - 1) hMR jm3lt (le_refl _) leR3).2.2
  -- 最終列の行1親は非隣接: `¬ nextR M 1 (j₁-1) j₁`
  have notnx1 : nextR M 1 (Lng M - 1 - 1) (Lng M - 1) = true → False := by
    intro H
    have huniq := nextR1_unique_mr M (Lng M - 1 - 1) (s84x_jm2 M) (Lng M - 1) H
      (s84c1_nextR1_jm2 M hp)
    omega
  set RN := Red (s84x_N M) with hRN
  have hLngRNval : Lng RN = Lng M - s84x_jm3 M := LngRN.trans hlenN
  have LRN2 : 2 ≤ Lng RN := by rw [hLngRNval]; omega
  -- スライス添字の境界
  have jm3leLm1 : s84x_jm3 M ≤ Lng M - 1 := le_of_lt jm3lt
  have j1L : Lng M - 1 < Lng M := by omega
  have a1 : Lng RN - 2 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by
    rw [length_seg]; omega
  have a2 : Lng RN - 1 < Lng (seg M (s84x_jm3 M) (Lng M - 1)) := by
    rw [length_seg]; omega
  have hseg := nextR1_seg_adm M (s84x_jm3 M) (Lng M - 1) (Lng RN - 2) (Lng RN - 1)
    jm3leLm1 j1L a1 a2
  have idxA : s84x_jm3 M + (Lng RN - 2) = Lng M - 1 - 1 := by omega
  have idxB : s84x_jm3 M + (Lng RN - 1) = Lng M - 1 := by omega
  -- `Br RN ≠ []`
  have Brne : Br RN ≠ [] := by
    intro Bemp
    have trmaxeq : TrMax RN = Lng RN - 1 := by
      by_contra ne
      have hBr : Br RN = P (seg RN (TrMax RN + 1) (Lng RN - 1)) := by
        unfold Br; rw [if_neg ne]
      rw [hBr] at Bemp
      exact P_nonempty _ Bemp
    have lt2 : Lng RN - 2 < TrMax RN := by rw [trmaxeq]; omega
    have stepN_seg : nextR (seg M (s84x_jm3 M) (Lng M - 1)) 1 (Lng RN - 2) (Lng RN - 1)
        = true := by
      have e : seg M (s84x_jm3 M) (Lng M - 1) = s84x_N M := rfl
      rw [e, segIF, nextR_IncrFirstN_ri]
      have step2 := TrMax_trunk_step RN (Lng RN - 2) RNT lt2
      rwa [show Lng RN - 2 + 1 = Lng RN - 1 from by omega] at step2
    rw [hseg, idxA, idxB] at stepN_seg
    exact notnx1 stepN_seg
  -- 組み立て（Isabelle 90072-90074、`cfbx_reg_def` の逐語）
  refine ⟨RNRT, monoRN, Brne, ?_⟩
  rcases hMCOND with hlt | ⟨heq, hdiag⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hdiag, descRN⟩

/-! ## 3. `mcx_regS` の drop-in（house pattern） -/

/-- Isabelle `mcx_regS` (layerB/pss_wip.thy:94021) の drop-in。
支持 Prop（`Regs_jm3Marked` = `s84d_jm3_Marked`、`Regs_jm2_lt_transJ0` =
`m_8_4_oper_props_1(1)`、`Regs_MCOND` = `mcx_MCOND_RN`）を与えれば `REGS` 脚が閉じる。
`transJ0 M < Lng M - 1` は本ファイル内で証明する。 -/
theorem regS_holds (hM : Regs_jm3Marked) (hJ : Regs_jm2_lt_transJ0)
    (hC : Regs_MCOND) : Regs_mcx_regS := by
  intro M hST hmono hp j1gt branch guard
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨hMarked, _jm3le, _jm2lt⟩ := hM M hMR hMT hp
  -- `j₋₂ < transJ0 < Lng M - 1` ⟹ `j₋₂ < Lng M - 2`
  have hjm2j0 : s84x_jm2 M < transJ0 M := hJ M hST hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have hjm2pred : s84x_jm2 M < Lng M - 2 := by omega
  exact regS_of_mcond_rg M hST hmono hp j1gt hMarked hjm2pred
    (hC M hST hmono hp j1gt branch guard)

#print axioms regS_of_mcond_rg
#print axioms regS_holds

end PSS
