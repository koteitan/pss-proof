import «8».«8.3-condII-NotLdjLeg2»
import «8».«8.2-condV-VE-close»
import «8».«8.2-condV-VE-wnx»
import «8».«8.2-condIIIV-terminal-slice-Trans»
import «8».«8.3-condII-Dichotomy»
import «8».«8.3-condII-R3LE»
import «8».«8.3-condII-LDJB-lttrmax»
import «8».«8.3-condII-BoundaryLeg2»

/-!
# §8.3 条件(II) — `TV_NotLdjReg` の無条件化

Isabelle `c2sx_tailval_of_reg` (`layerB/pss_wip.thy`:87838) を、既存の
`wnx_seg_transport_W1/W2` と §8.2 の無条件 `vcx_VE_all` から閉じる。
簡約祖先切片 `R_c` 上の VE を元の二つの切片へ戻し、末尾側切片の principal 表示と
`c2sx_slice_jm1_c1` を組み合わせる。

状態: ✅ `tv_notldjreg_holds` / `tv_notldjleg_holds`（sorry 0）。これを既存の
5 脚と合わせ、`CondII_masterCF` の残差を `TvxBoundaryData` 1 本へ縮約する。
-/

namespace PSS

/-- Isabelle `wnx_transfer_of_reg` (layerB 80867): 簡約祖先切片上の VE を、元の
非許容 run の両端から始まる切片の `bpHeadT` 等式へ戻す。 -/
private theorem wnx_transfer_of_reg_nlr (M : PS) (a b m : ℕ)
    (hR : RTPS M) (hab : a < b) (hbL : b ≤ Lng M - 1)
    (hleab : leR M 0 a b = true) (hamb : a + m < b)
    (hleam : le0 M (a + m) b = true) (hreg : VEReg m (Red (seg M a b))) :
    bpHeadT (Trans (seg M (a + m) b)) = bpHeadT (Trans (seg M a b)) := by
  have hW2 := wnx_seg_transport_W2 M a b m hR hab hbL hleab hamb hleam
  have hW1 := wnx_seg_transport_W1 M a b hab
  have hVE := vcx_VE_all m (Red (seg M a b)) hreg
  unfold VEeq at hVE
  rw [hW2, hW1]
  exact hVE

/-- Isabelle `c2sx_tailval_of_reg` (layerB 87838): `cfbx_reg` (`VEReg`) 分岐の
条件(II) tail value。 -/
theorem tv_notldjreg_holds : TV_NotLdjReg := by
  intro M hR hmono hj1 hII hnotldj hreg
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hII
  let j0 := parent M 0 (Lng M - 1)
  let jm1 := Adm M j0
  let b := Lng M - 2
  let d := j0 - jm1
  have hjm1le : jm1 ≤ j0 := by
    dsimp [jm1]
    exact Adm_le M j0
  have hjm1d : jm1 + d = j0 := by
    dsimp [d]
    omega
  have hab : jm1 < b := by dsimp [jm1, j0, b]; omega
  have hbL : b ≤ Lng M - 1 := by dsimp [b]; omega
  have hleab : leR M 0 jm1 b = true := by
    dsimp [jm1, j0, b]
    exact c2sx_reach_leab M hR hmono hj1 hII
  have hamb : jm1 + d < b := by rw [hjm1d]; dsimp [j0, b]; omega
  have hleam : le0 M (jm1 + d) b = true := by
    rw [hjm1d]
    dsimp [j0, b]
    exact c2sx_reach_leam M hR hmono hj1 hII
  have hreg' : VEReg d (Red (seg M jm1 b)) := by
    simpa [d, jm1, j0, b, tvx_d, tvx_Rc] using hreg
  have hbody :
      bpHeadT (Trans (seg M j0 b)) = bpHeadT (Trans (seg M jm1 b)) := by
    have h := wnx_transfer_of_reg_nlr M jm1 b d hR hab hbL hleab hamb hleam hreg'
    rwa [hjm1d] at h
  have hmonoSeg : monoT (seg M j0 b) = true := by
    apply monoT_seg_of_le0_68 M j0 b
    · dsimp [b]; omega
    · dsimp [j0, b]; omega
    · rw [← hjm1d]
      exact hleam
  have hhead :
      Trans (seg M j0 b) =
        Dprin (entry M 1 j0 : ℕ∞) (bpHeadT (Trans (seg M j0 b))) :=
    slice_Trans_principal_head M j0 b hR (by dsimp [j0, b]; omega) hbL hmonoSeg
  have hbridge :
      Trans (seg M jm1 b) = Dprin (entry M 1 jm1 : ℕ∞) (transT2 M) := by
    simpa [jm1, j0, b] using c2sx_slice_jm1_c1 M hR hmono hj1 hII
  have hbp : bpHeadT (Trans (seg M jm1 b)) = transT2 M := by
    rw [hbridge]
    rfl
  have ht4 : condII_t4 M = transT2 M := by
    simp [condII_t4, hnotldj]
  unfold CondII_tailval
  change Trans (seg M j0 b) = Dprin (entry M 1 j0 : ℕ∞) (condII_t4 M)
  rw [hhead, hbody, hbp, ht4]

/-- `TV_NotLdjLeg` の最後の残差を閉じた無条件版。 -/
theorem tv_notldjleg_holds : TV_NotLdjLeg :=
  tv_notldjleg_of_reg tv_notldjreg_holds

/-- CondII の 6 tail-value 脚のうち、今回 `NotLdj` を閉じ、既閉の 4 脚を配線する。
残るのは境界脚の transport/value データ `TvxBoundaryData` だけ。 -/
theorem condII_masterCF_of_boundaryData (hData : TvxBoundaryData) : CondII_masterCF :=
  condII_masterCF_of_residuals_cm2 TV_Dichotomy_holds TV_TrunkLeg_holds
    (tv_boundaryleg_of_data hData) tv_notldjleg_holds tv_ldjb_holds TV_R3LE_holds

#print axioms tv_notldjreg_holds
#print axioms tv_notldjleg_holds
#print axioms condII_masterCF_of_boundaryData

end PSS
