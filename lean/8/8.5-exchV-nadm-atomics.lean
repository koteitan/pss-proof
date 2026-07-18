import «8».«8.5-exchV-values-close»
import «8».«8.2-condIIIV-terminal-slice-Trans»
import «7».«7.4-Adm-nextAdm»
import «6».«6.8-standard-slice-Br-descending»
import «6».«6.6-P-condAB»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.3-admof-slice»
import «5».«5.1-ancestor-basic»
import «5».«5.1-parent-exists»

/-!
# §8.5 ExchV 非許容枝 原子3値の残差縮約（`ExchVMNadmAtomicPackage`）

## 目的

停止性主定理へ渡す `TerminationResidual.exchVMvalues : ExchVMNadmAtomicPackage`
（`8.5-exchV-values-close` 参照。`Rightmost84ReplaceCorrected ∧ ExchVMNadmAtomicResidual`）
のうち **non-admissible 原子3値**（`ExchVMNadmAtomicResidual` = `PredNp` / `Np` /
`c₂(L₁)`）を、より深い 2 本の残差
`{NadmW2nostr（no-straddle body transfer）, NadmC2L1（c₂(L₁) の値）}` へ縮約する。

`PredNp` と `Np` は Isabelle の **de-admissibilization kernel** 経由で
`NadmW2nostr` へ落ちる。`c₂(L₁)` は Isabelle `atx_c2L1`（`dax_c2L1_of_notLD` 依存）で
閉じるが本ファイルでは `NadmC2L1` として据え置く。よって
`ExchVMNadmAtomicPackage` は本ファイルにより
`{Rightmost84ReplaceCorrected, NadmW2nostr, NadmC2L1}` の 3 残差へ縮約される。

## 原文 / Isabelle 対応

- 原文: §8.5「補題（条件(V)の下での各種scb分解）」/「補題（条件(V)の下での Joints と
  FirstNodes と t₂ の基本性質）」(content.md 5209/5283)。DEFERRED 系。
- Isabelle blueprint（`isabelle/layerB/pss_wip.thy`）:
  * `ncx_deadm_of_w2nostr`(77489) — de-adm 恒等式を slice principal 頭形状
    (`dkax_slice_principal_gen`=Lean `slice_Trans_principal_head`) と no-straddle
    body transfer `W2c` から復元。→ 本ファイル `exchV_deadm_of_W2_na`。
  * `nf3x_slice_jm1_c2`(69535) / `nf3x_slice_jm1_c1`(69568) — 祖先切片 Bridge A/B
    (`= transC2 M` / `= transC1 M`)。→ 本ファイル `bridgeA_na` / `bridgeB_na`。
  * `nf3x_NpVal`(69619) / `nf3x_PredNp`(69652) — de-adm kernel から `Np`/`PredNp`。
    → 本ファイル `exchVMNadmAtomicResidual_of_parts` に内蔵。
  * `wnx_setup`(81008) — 到達性束。→ 本ファイル `nadm_setup_na`。
  * `oi4_DEADM1`(118106) / `oi4_DEADM2`(118127) — DEADM を W2nostr へ。
  * `wnx_W2nostr_c1`(81279) / `wnx_W2nostr_c2`(81304) — no-straddle body transfer
    （深い cfbx_reg regime 追跡。**未移植** → `NadmW2nostr`）。
  * `atx_c2L1`(86248) — c₂(L₁) の値（**未移植** → `NadmC2L1`）。

## 訂正

- A30 / A31: `Rightmost84ReplaceCorrected`（`8.4-rightmost-replace-Trans`）参照。

## 依存（すべて committed 緑, main db1f93c）

«8».«8.5-exchV-values-close»（`ExchVMNadmAtomicResidual`/`ExchVMNadmAtomicPackage`/
`Rightmost84ReplaceCorrected`/`condV_setup_holds`/`condV_bridge_hp_jm2`/`c1_shape_holds`/
`transC2_condV_eq`/`s84x_Np`/`Pred_s84x_Np`/`Mark_Trans_repr`/`m_7_3_Mark_rightmost2`/
`Marked_Pred_Adm`/`seg_Pred_eq`/`STPS_*`/`RTPS_Pred`/`length_Pred`）,
«8».«8.2-condIIIV-terminal-slice-Trans»（`slice_Trans_principal_head`）,
«7».«7.4-Adm-nextAdm»（`adm_row1_ancestry`/`row1_implies_row0`）,
«6».«6.8…»（`monoT_seg_of_le0_68`/`parent_block_le0_68`）,
«6».«6.6-P-condAB»（`mono_hasParent_row0`）,
«6».«6.4…»（`nextR_parent0_of_hasParent`/`nextR0_leR`）,
«6».«6.3-admof-slice»（`Adm_adm`/`Adm_le`）,
«5».«5.1-…»（`ancestor_basic_1`/`parent_exists_3`）.

## 状態

GREEN（sorry 0, axioms = [propext, Classical.choice, Quot.sound]）。
`ExchVMNadmAtomicPackage` を 3 named-Prop 残差へ縮約（house green-modulo）。
残差: `Rightmost84ReplaceCorrected`, `NadmW2nostr`, `NadmC2L1`。

## private 接尾辞: `_na`
-/

namespace PSS

/-! ## 補助（private） -/

/-- `bpHeadT (D_v b) = b`（`Dprin`/`bpHeadT` の定義計算）。 -/
private theorem bpHeadT_Dprin_na (v : ℕ∞) (b : BT) : bpHeadT (Dprin v b) = b := rfl

/-- `le0`（`leR _ 0 _`）の推移律。`le0_trans_jfb`（8.5-Joints-FirstNodes-basic）
と同一骨格（`parent_exists_3` + `ancestor_basic_1`）。 -/
private theorem le0_trans_na (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hbc : leR M 0 b c = true)
    (halt : a < b) (hblt : b < c) (hcL : c < Lng M) :
    leR M 0 a c = true := by
  apply parent_exists_3 M a c hM (by omega) hcL
  intro j haj hjc
  by_cases hjb : j ≤ b
  · exact ancestor_basic_1 M a j b hM haj hjb hab
  · have h1 : entry M 0 a < entry M 0 b :=
      ancestor_basic_1 M a b b hM halt le_rfl hab
    have h2 : entry M 0 b < entry M 0 j :=
      ancestor_basic_1 M b j c hM (by omega) hjc hbc
    omega

/-- Isabelle `wnx_setup`（pss_wip.thy:81008）の到達性束。 -/
private theorem nadm_setup_na (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hnadm : adm M (transJ0 M) = false) :
    transJm1 M < transJ0 M ∧
      transJ0 M + 1 < Lng M - 1 ∧
      leR M 0 (transJm1 M) (Lng M - 1) = true ∧
      leR M 0 (transJ0 M) (Lng M - 1) = true ∧
      leR M 0 (transJ0 M) (Lng M - 2) = true ∧
      leR M 0 (transJm1 M) (Lng M - 2) = true ∧
      nextR M 0 (transJ0 M) (Lng M - 1) = true := by
  have hM : TPS M := STPS_TPS M hST
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  -- j₋₁ < j₀
  have hjm1lt : transJm1 M < transJ0 M := by
    have hle : transJm1 M ≤ transJ0 M := Adm_le M (transJ0 M)
    have hadm : adm M (transJm1 M) = true := Adm_adm M (transJ0 M)
    rcases Nat.lt_or_ge (transJm1 M) (transJ0 M) with h | h
    · exact h
    · exfalso
      have heq : transJm1 M = transJ0 M := by omega
      rw [heq, hnadm] at hadm
      exact Bool.noConfusion hadm
  -- 行1祖先 → 行0到達性
  have hle1a : leR M 1 (transJm1 M) (transJ0 M) = true :=
    adm_row1_ancestry M (transJ0 M) hM (by omega)
  have hle0a : leR M 0 (transJm1 M) (transJ0 M) = true :=
    row1_implies_row0 M (transJm1 M) (transJ0 M) hM hle1a
  -- j₀ → j₁ 到達性
  have hle0c1 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M (transJ0 M) (Lng M - 1) hnextM
  -- j₀ → j₁-1 到達性
  have hle0c2 : leR M 0 (transJ0 M) (Lng M - 2) = true := by
    have hraw := parent_block_le0_68 M (transJ0 M) (Lng M - 1)
      ((Lng M - 2) - transJ0 M) hM hnextM (by omega)
    have hidx : transJ0 M + ((Lng M - 2) - transJ0 M) = Lng M - 2 := by omega
    rw [hidx] at hraw
    simpa [leR] using hraw
  refine ⟨hjm1lt, hrng, ?_, hle0c1, hle0c2, ?_, hnextM⟩
  · exact le0_trans_na M (transJm1 M) (transJ0 M) (Lng M - 1) hM hle0a hle0c1
      hjm1lt (by omega) (by omega)
  · exact le0_trans_na M (transJm1 M) (transJ0 M) (Lng M - 2) hM hle0a hle0c2
      hjm1lt (by omega) (by omega)

/-- Isabelle `ncx_deadm_of_w2nostr`（pss_wip.thy:77489）。到達性 `leR M 0 j₀ c` の下で、
切片 `seg M j₀ c` は頭指標 `M₁,ⱼ₀` の principal（`slice_Trans_principal_head`）であり、
no-straddle body transfer `hW2`（`bpHeadT` が非許容前線を跨いで一定）で本体を先祖切片
`seg M j₋₁ c` へ移す。 -/
private theorem exchV_deadm_of_W2_na (M : PS) (c : ℕ) (hR : RTPS M)
    (hreach : leR M 0 (transJ0 M) c = true) (hqc : transJ0 M < c) (hcL : c < Lng M)
    (hW2 : bpHeadT (Trans (seg M (transJ0 M) c))
        = bpHeadT (Trans (seg M (transJm1 M) c))) :
    Trans (seg M (transJ0 M) c)
      = Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (bpHeadT (Trans (seg M (transJm1 M) c))) := by
  have hle0 : le0 M (transJ0 M) c = true := by simpa [leR] using hreach
  have hmono : monoT (seg M (transJ0 M) c) = true :=
    monoT_seg_of_le0_68 M (transJ0 M) c hcL hqc hle0
  have hhead := slice_Trans_principal_head M (transJ0 M) c hR hqc (by omega) hmono
  conv_lhs => rw [hhead]
  rw [hW2]

/-- Isabelle `nf3x_slice_jm1_c2`（pss_wip.thy:69535）。祖先切片 `seg M j₋₁ j₁` は `c₂`。
`j₋₁ = Adm M j₀` は許容（`Adm_adm`）かつ `j₁` へ到達（`nadm_setup_na`）なので `Marked`、
`Mark_Trans_repr` + `m_7_3_Mark_rightmost2`。 -/
private theorem bridgeA_na (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hnadm : adm M (transJ0 M) = false) :
    Trans (seg M (transJm1 M) (Lng M - 1)) = transC2 M := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc1, _ht2TB, hjm1lt⟩ := c1_shape_holds M hR hM hmono hj1pos ht1ne
  obtain ⟨_, _, hreachJm1, _, _, _, _⟩ := nadm_setup_na M hST hmono hcond hnadm
  have hadmJm1 : adm M (transJm1 M) = true := Adm_adm M (transJ0 M)
  have hmk : Marked M (transJm1 M) := ⟨hM, hadmJm1, hreachJm1⟩
  have hrepr : Mark M (transJm1 M) = Trans (seg M (transJm1 M) (Lng M - 1)) :=
    Mark_Trans_repr M (transJm1 M) hmk hR hjm1lt
  have hrm2 : Mark M (transJm1 M) = transC2 M :=
    m_7_3_Mark_rightmost2 M hR hmono hj1pos ht1ne
  rw [← hrepr]; exact hrm2

/-- Isabelle `nf3x_slice_jm1_c1`（pss_wip.thy:69568）。祖先切片 `seg M j₋₁ (j₁-1)` は
`c₁ = Mark (Pred M) j₋₁`。`Marked_Pred_Adm` + `Mark_Trans_repr` + `seg_Pred_eq`。 -/
private theorem bridgeB_na (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) :
    Trans (seg M (transJm1 M) (Lng M - 2)) = transC1 M := by
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmk : Marked (Pred M) (transJm1 M) := Marked_Pred_Adm M hM hlen hp0
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hjm1le : transJm1 M ≤ transJ0 M := Adm_le M (transJ0 M)
  have hjm1lt : transJm1 M < Lng (Pred M) - 1 := by rw [hpredLen]; omega
  have hrepr : Mark (Pred M) (transJm1 M)
      = Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (transJm1 M) hmk hpredR hjm1lt
  have hsegPred : seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)
      = seg M (transJm1 M) (Lng M - 2) := by
    rw [hpredLen]
    exact seg_Pred_eq M (transJm1 M) (Lng M - 2) hlen (by omega) (by omega)
  calc
    Trans (seg M (transJm1 M) (Lng M - 2))
        = Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)) := by rw [hsegPred]
    _ = Mark (Pred M) (transJm1 M) := hrepr.symm
    _ = transC1 M := rfl

/-! ## 深い残差（named Prop） -/

/-- Isabelle `wnx_W2nostr_c1`(81279) / `wnx_W2nostr_c2`(81304)。non-admissible 前線
`[j₋₁, j₀]` を跨いでも `Trans` 本体（`bpHeadT`）は一定。深い cfbx_reg regime 追跡。 -/
def NadmW2nostr : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = false →
    (bpHeadT (Trans (seg M (transJ0 M) (Lng M - 1)))
        = bpHeadT (Trans (seg M (transJm1 M) (Lng M - 1)))) ∧
    (bpHeadT (Trans (seg M (transJ0 M) (Lng M - 2)))
        = bpHeadT (Trans (seg M (transJm1 M) (Lng M - 2))))

/-- Isabelle `atx_c2L1`（pss_wip.thy:86248）。non-admissible 枝の `c₂(L₁)` の値。
`dax_c2L1_of_notLD`（surgery）依存。 -/
def NadmC2L1 : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = false →
    transC2 (s84x_L M 1) = Dprin (entry M 1 (transJm1 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞)
        (addBT (transT2 M)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero))))

/-! ## 縮約 -/

/-- 深い残差 `{NadmW2nostr, NadmC2L1}` から non-admissible 原子3値
`ExchVMNadmAtomicResidual`（`PredNp` / `Np` / `c₂(L₁)`）を復元する。 -/
theorem exchVMNadmAtomicResidual_of_parts
    (hW2 : NadmW2nostr) (hc2 : NadmC2L1) : ExchVMNadmAtomicResidual := by
  intro M hST hmono hcond hnadm
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨_, hrng, _, hreach0_1, hreach0_2, _, _⟩ :=
    nadm_setup_na M hST hmono hcond hnadm
  obtain ⟨hW2c1, hW2c2⟩ := hW2 M hST hmono hcond hnadm
  -- de-adm 恒等式（DEADM1 / DEADM2）
  have hDEADM1 : Trans (seg M (transJ0 M) (Lng M - 1))
      = Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (bpHeadT (Trans (seg M (transJm1 M) (Lng M - 1)))) :=
    exchV_deadm_of_W2_na M (Lng M - 1) hR hreach0_1 (by omega) (by omega) hW2c1
  have hDEADM2 : Trans (seg M (transJ0 M) (Lng M - 2))
      = Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (bpHeadT (Trans (seg M (transJm1 M) (Lng M - 2)))) :=
    exchV_deadm_of_W2_na M (Lng M - 2) hR hreach0_2 (by omega) (by omega) hW2c2
  -- 祖先切片 Bridge A / B
  have hBrA : Trans (seg M (transJm1 M) (Lng M - 1)) = transC2 M :=
    bridgeA_na M hST hmono hcond hnadm
  have hBrB : Trans (seg M (transJm1 M) (Lng M - 2)) = transC1 M :=
    bridgeB_na M hST hmono hcond
  -- slice 同一視
  have hjm2 : s84x_jm2 M = transJ0 M := (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hNpSeg : s84x_Np M = seg M (transJ0 M) (Lng M - 1) := by
    rw [s84x_Np, hjm2]
  have hPredNpSeg : Pred (s84x_Np M) = seg M (transJ0 M) (Lng M - 2) := by
    rw [Pred_s84x_Np M (by rw [hjm2]; omega), hjm2]
  -- Np
  have hNp : Trans (s84x_Np M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
    rw [hNpSeg, hDEADM1, hBrA, transC2_condV_eq M hcond]
    rfl
  -- PredNp
  have hPredNp : Trans (Pred (s84x_Np M))
      = Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) := by
    rw [hPredNpSeg, hDEADM2, hBrB]
    rfl
  -- c₂(L₁)
  have hc2L1 := hc2 M hST hmono hcond hnadm
  exact ⟨hPredNp, hNp, hc2L1⟩

/-- 訂正済み §8.4 右端置換 `Rightmost84ReplaceCorrected` と深い残差
`{NadmW2nostr, NadmC2L1}` から `ExchVMNadmAtomicPackage` を復元する。 -/
theorem exchVMNadmAtomicPackage_of_parts
    (hrr : Rightmost84ReplaceCorrected) (hW2 : NadmW2nostr) (hc2 : NadmC2L1) :
    ExchVMNadmAtomicPackage :=
  ⟨hrr, exchVMNadmAtomicResidual_of_parts hW2 hc2⟩

#print axioms exchV_deadm_of_W2_na
#print axioms bridgeA_na
#print axioms bridgeB_na
#print axioms exchVMNadmAtomicResidual_of_parts
#print axioms exchVMNadmAtomicPackage_of_parts

end PSS
