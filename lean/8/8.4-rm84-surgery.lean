import «8».«8.4-rightmost-exists»
import «8».«8.4-c2hole-engine»
import «8».«8.4-s84x-vocab-run»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-Red2»
import «7».«7.3-c1-c2-order»
import «7».«7.3-Trans-IncrFirst-Red»

/-!
# §8.4 補題（右端置き換えと `Trans`）存在部 `Rightmost84ReplaceExists` の **忠実な外科手術** 還元

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は **DEFERRED**。
- ブループリント: Isabelle `m_8_4_rightend_Trans`（`isabelle/layerB/pss_wip.thy`:54650、
  ~500 行）＋その scb 分解手術族 `s84d_*`（wip:58412–58690、`8.4-c2hole-engine` で port 済）。
- 攻略対象: `«8».«8.4-rightmost-replace-close»` の存在部 `Rightmost84ReplaceExists`（同 :43）。
  一意部は同ファイルで無条件に閉じている。

## 値ルートは死路、外科手術が忠実ルート

Wave AB で **値リードバック残差 `Rm84NpValue`/`Rm84LpValue`/`Rm84HeadValue` は 3 件とも
機械反証**された（`8.4-rm84-lp-value`/`8.4-rm84-np-value`、cex `(0,0)(1,1)(2,1)` 条件(III):
c₂-hole 内側 readback が `j₋₂≠j₀` で 1 principal ずれる）。忠実ルートは Isabelle
`m_8_4_rightend_Trans` の **外科手術**（値でなく scb 分解の transport）である。

## 手術の構造（`m_8_4_rightend_Trans` の忠実 port）

`M` を域元とし `Np := s84x_Np M = seg M j₋₂ j₁`（`j₁ = Lng M − 1`, `j₋₂ = s84x_jm2 M`）
とする。

* `Q := Red Np`（`s84rs_Q M`）は §6.6 `ancestor_slice_Red_IncrFirst` により
  **簡約・単項・`RT_PS`** で、`Np = IncrFirst^k Q`。よって `Trans Np = Trans Q`
  （`Trans_Red`、行0 の底上げは `Trans` 不変）。
* `R := butlast Q ⊕ (Q_{0,LngQ−1}, Q_{1,0})`（`s84rs_R M`）は右端の行1成分だけを
  `Q_{1,LngQ−1}` から `Q_{1,0}` に置き換えた列。`Q` と `R` は `Pred`・`transV`・`transT2`・
  `transT1`・`transC1`・`transJ0`・`transJ1` を **すべて共有**し、`transC2` の **最内 core
  `D_β 0` / `D_γ 0` だけ**が異なる（`β = M_{1,j₁} = Q_{1,LngQ−1}`, `γ = M_{1,j₋₂} = Q_{1,0}`）。

**核（本ファイルで無条件に組む部分）**: `c2hole` エンジン `c2hole_scb_ch Q` は `Q` の
`transC2` の穴 `a` を **すべての `a` について共有 `(w,w')`** で印付ける。これを穴
`a = β`（`transC2 Q = c2hole_ch Q β`、`c2hole_at_j1_ch`）と穴 `a = γ`（`transC2 R
= c2hole_ch Q γ`、手術）に埋めれば **core-swap**（`transC2 Q` と `transC2 R` の共有 scb
分解）が立つ。あとは外側 `Trans → transC2` 分解（`s84c2_Trans_c2_decomp`）を `scb_compose`
で合成し、readback で `Trans Np`/`Trans (rrLp M)` に移せば `Rightmost84ReplaceExists`。

## 残差 `Rm84SurgeryFrame`（忠実・非死路）

エンジンより上（`Q`/`R` の shape・値橋・外側分解・`rrLp` readback）を named Prop に束ねた。
これは Isabelle `m_8_4_rightend_Trans` の {value bridges `aQeq`/`aReq`, `transC2 R` の
`c2hole` 同定（branch 解析 `condAQ_iff`/`condAR_iff` の帰結）, 外側対 `dTQ`/`dTR'`,
`TransLp`} に対応する。**旧 `C2HoleSliceTransport_ch`（`8.4-c2hole-engine`、Wave Y で偽）と
違い、`c2hole` を `M` でなく簡約列 `Q = Red Np` に適用する**ため反証を回避する。

- 数値検証（`python/trans_model.py` ＋ `/tmp/check_frame_rs.py`）: STPS×monoT×hasParent₁(last)×
  `j₋₂+1<j₁` の域で、`Trans Np = Trans Q`・`Trans (rrLp M) = Trans R`・core-swap 共有分解が
  **45/45**、frame 5 部（`β`/`γ` 橋・`transC2 Q = c2hole Q β`・`transC2 R = c2hole Q γ`・
  外側分解共有）も **45/45** 成立。反証 cex `(0,0)(1,1)(2,1)`（値ルートが崩れた点）でも
  手術は成立（共有分解 witness 存在）。A30 host `(0,0)(1,1)(2,2)(2,1)`（multi-principal）でも成立。

- 依存（すべてビルド済み・committed at e383af6）: «8».«8.4-rightmost-exists»
  （`Rightmost84ReplaceExists`/`s84x_Np`/`s84x_jm2`/`rrLp`/`Rightmost84ReplaceCorrected`/
  `rightmost84ReplaceCorrected_of_exists`）、«8».«8.4-c2hole-engine»
  （`c2hole_ch`/`c2hole_scb_ch`/`c2hole_at_j1_ch`）、«8».«8.4-s84x-vocab-run»
  （`s84c1_jm2_basic`）、«6».«6.6-ancestor-slice-Red-IncrFirst»
  （`ancestor_slice_Red_IncrFirst`）、«6».«6.6-Red2»（`Red2`）、«7».«7.3-c1-c2-order»
  （`transC2_single_principal`/`principal_reconstruct`）、«7».«7.3-Trans-IncrFirst-Red»
  （`Trans_Red`）、推移的に «7».«7.2-scb-compose»（`scb_compose`）、«7».«7.3-Trans-welldefined»
  （`Trans_Mark_invariant`）、«6».«6.5-Red-Pred-commute»（`RTPS_Pred`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  core-swap＋外側合成＋readback 組立は無条件。残差 = `Rm84SurgeryFrame`（Isabelle の
  R-facts＋branch 解析＋外側分解＝L4 part(2)(3)）。
- Private suffix: `_rs`。
-/

namespace PSS

/-! ## 0. 手術の対象列 -/

/-- `Q := Red (s84x_Np M)`（Isabelle `Q = Red Np`, wip:54682）。 -/
def s84rs_Q (M : PS) : PS := Red (s84x_Np M)

/-- `R := butlast Q ⊕ (Q_{0,LngQ−1}, Q_{1,0})`（Isabelle `R`, wip:54748）。右端置き換え列。 -/
def s84rs_R (M : PS) : PS :=
  (s84rs_Q M).dropLast
    ++ [(entry (s84rs_Q M) 0 (Lng (s84rs_Q M) - 1), entry (s84rs_Q M) 1 0)]

/-! ## 1. `Q` の基本性質（`ancestor_slice_Red_IncrFirst` の帰結） -/

/-- `s84x_Np M` は非空（`j₋₂ ≤ j₁ < Lng M`）。 -/
private theorem tps_Np_rs (M : PS) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    TPS (s84x_Np M) := by
  have hlen : 0 < Lng (s84x_Np M) := by
    unfold s84x_Np; rw [length_seg]; omega
  exact List.ne_nil_of_length_pos hlen

/-- `Q = Red Np` の簡約性・単項性・`Np = IncrFirst^k Q`（`ancestor_slice_Red_IncrFirst`）。 -/
private theorem q_facts_rs (M : PS) (hMR : RTPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    RTPS (s84rs_Q M) ∧ monoT (s84rs_Q M) = true ∧
      s84x_Np M = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_Q M) := by
  obtain ⟨hjm2lt, _, hle0⟩ := s84c1_jm2_basic M hp
  have hleR : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using hle0
  have hanc := ancestor_slice_Red_IncrFirst M (s84x_jm2 M) (Lng M - 1) hMR hjm2lt (le_refl _) hleR
  obtain ⟨hRedN, hmonoN, hIF⟩ := hanc
  -- defeq 変換（`seg M j₋₂ j₁` = `s84x_Np M`、`Red (seg ..)` = `s84rs_Q M`）
  have hRedN' : Red (Red (s84x_Np M)) = Red (s84x_Np M) := hRedN
  have hmonoN' : monoT (s84rs_Q M) = true := hmonoN
  have hIF' : s84x_Np M
      = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_Q M) := hIF
  refine ⟨?_, hmonoN', hIF'⟩
  have hTPSNp : TPS (s84x_Np M) := tps_Np_rs M hrng
  have h2 := Red2 (s84x_Np M) hTPSNp
  rw [hRedN'] at h2
  exact h2

/-- `Q` の長さは `≥ 3`（`j₋₂ + 1 < j₁` の下）。 -/
private theorem lenQ3_rs (M : PS)
    (hrng : s84x_jm2 M + 1 < Lng M - 1)
    (hIF : s84x_Np M
      = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M)) (s84rs_Q M)) :
    3 ≤ Lng (s84rs_Q M) := by
  have hlenNp : Lng (s84x_Np M) = Lng (s84rs_Q M) := by
    have h := congrArg Lng hIF
    rwa [length_IncrFirstN] at h
  have h1 : Lng (s84x_Np M) = Lng M - 1 + 1 - s84x_jm2 M := by
    unfold s84x_Np; rw [length_seg]
  omega

/-- `transC2 X` は単一 principal `D_{transV X} (·)`（`transC2_single_principal` の系）。 -/
private theorem transC2_principal_rs (X : PS) : ∃ p, transC2 X = .trm [p] := by
  have h := principal_reconstruct (transC2_single_principal X)
  refine ⟨.db (bpHeadV (transC2 X)) (bpHeadT (transC2 X)), ?_⟩
  conv_lhs => rw [h]
  rfl

/-- `transT1 Q ≠ 0_B`（`c2hole` エンジンの前提。Isabelle `T1neQ`、`setup_sd_ch` と同一構成）。 -/
private theorem transT1ne_rs (Q : PS) (hQR : RTPS Q) (hLen3 : 3 ≤ Lng Q) :
    transT1 Q ≠ BZero := by
  have hlen : 1 < Lng Q := by omega
  have hLP : Lng (Pred Q) = Lng Q - 1 := by
    simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred Q) = false := by
    simp [zeroT, hLP]; omega
  have T1' : Trans (Pred Q) ≠ BZero :=
    (Trans_Mark_invariant (Pred Q) (RTPS_Pred Q hQR)).2.1 nzP
  simpa [transT1] using T1'

/-! ## 2. 残差 `Rm84SurgeryFrame`（エンジンより上、忠実・非死路） -/

/-- **手術フレーム残差**。域元 `M` について:
* 値橋 `β`/`γ`: `Q_{1,LngQ−1} = M_{1,j₁}`, `Q_{1,0} = M_{1,j₋₂}`（Isabelle `aQeq`/`aReq`）。
* `transC2 R = c2hole_ch Q γ`（`R` の `c₂` は `Q` の穴エンジンの穴 `γ`。branch 解析
  `condAQ_iff`/`condAR_iff`＋`tVQR`/`tT2QR` の帰結）。
* `Trans (rrLp M) = Trans R`（Isabelle `TransLp`、`Lp = IncrFirst^k R`＋`Trans_Red`）。
* 外側分解対 `dTQ`/`dTR'`: `Trans Q`/`Trans R` が共有 `(s₁,b₁)` で `transC2 Q`/`transC2 R`
  を印付ける（Isabelle `s84c2_Trans_c2_decomp` を `Q`,`R` に適用＋`Pred` 一意性）。 -/
def Rm84SurgeryFrame : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
      entry (s84rs_Q M) 1 (Lng (s84rs_Q M) - 1) = entry M 1 (Lng M - 1) ∧
      entry (s84rs_Q M) 1 0 = entry M 1 (s84x_jm2 M) ∧
      transC2 (s84rs_R M) = c2hole_ch (s84rs_Q M) (entry (s84rs_Q M) 1 0) ∧
      Trans (rrLp M) = Trans (s84rs_R M) ∧
      ∃ s1 b1 : List Sym,
        scb_decomp (Trans (s84rs_Q M)) s1 (flatBT (transC2 (s84rs_Q M))) b1 ∧
        scb_decomp (Trans (s84rs_R M)) s1 (flatBT (transC2 (s84rs_R M))) b1

/-! ## 3. 還元：手術フレーム ⟹ 存在部 `Rightmost84ReplaceExists`

core-swap を `c2hole_scb_ch Q` から生成し、外側分解対と `scb_compose` で合成、readback で
`Trans Np`/`Trans (rrLp M)` へ移す。エンジンより下（core-swap 組立）は無条件。 -/
theorem rightmost84ReplaceExists_of_surgeryFrame_rs (h : Rm84SurgeryFrame) :
    Rightmost84ReplaceExists := by
  intro M hST hmono hp hrng
  obtain ⟨hβ, hγ, hRc2, hLp, s1, b1, dQ, dR⟩ := h M hST hmono hp hrng
  -- `Q` の基本性質
  have hMR : RTPS M := STPS_RTPS M hST
  obtain ⟨hQR, hQmono, hIF⟩ := q_facts_rs M hMR hp hrng
  have hQT : TPS (s84rs_Q M) := RTPS_TPS _ hQR
  have hLen3 : 3 ≤ Lng (s84rs_Q M) := lenQ3_rs M hrng hIF
  have hJ1pos : 0 < transJ1 (s84rs_Q M) := by
    simp only [transJ1, lastIdx]; omega
  have hQt1 : transT1 (s84rs_Q M) ≠ BZero := transT1ne_rs (s84rs_Q M) hQR hLen3
  -- `c2hole` エンジンを `Q` に適用
  obtain ⟨w, w', W⟩ := c2hole_scb_ch (s84rs_Q M) hQR hQT hQmono hJ1pos hQt1
  -- core-swap: 穴 `β`（= `transC2 Q`）と穴 `γ`（= `transC2 R`）
  have cswQ : scb_decomp (transC2 (s84rs_Q M)) (Sym.dsym (transV (s84rs_Q M)) :: w)
      (flatBT (Dprin (entry (s84rs_Q M) 1 (lastIdx (s84rs_Q M)) : ℕ∞) BZero)) w' := by
    have hw := W (entry (s84rs_Q M) 1 (lastIdx (s84rs_Q M)))
    rwa [← c2hole_at_j1_ch (s84rs_Q M)] at hw
  have cswR : scb_decomp (transC2 (s84rs_R M)) (Sym.dsym (transV (s84rs_Q M)) :: w)
      (flatBT (Dprin (entry (s84rs_Q M) 1 0 : ℕ∞) BZero)) w' := by
    have hw := W (entry (s84rs_Q M) 1 0)
    rwa [← hRc2] at hw
  -- `transC2 Q`/`transC2 R` は単一 principal
  have hc2Qp : ∃ p, transC2 (s84rs_Q M) = .trm [p] := transC2_principal_rs (s84rs_Q M)
  have hc2Rp : ∃ p, transC2 (s84rs_R M) = .trm [p] := transC2_principal_rs (s84rs_R M)
  -- 外側分解と合成
  have dFinQ : scb_decomp (Trans (s84rs_Q M))
      (s1 ++ (Sym.dsym (transV (s84rs_Q M)) :: w))
      (flatBT (Dprin (entry (s84rs_Q M) 1 (lastIdx (s84rs_Q M)) : ℕ∞) BZero)) (w' ++ b1) :=
    scb_compose (Trans (s84rs_Q M)) (transC2 (s84rs_Q M)) s1
      (Sym.dsym (transV (s84rs_Q M)) :: w)
      (flatBT (Dprin (entry (s84rs_Q M) 1 (lastIdx (s84rs_Q M)) : ℕ∞) BZero)) w' b1
      hc2Qp dQ cswQ
  have dFinR : scb_decomp (Trans (s84rs_R M))
      (s1 ++ (Sym.dsym (transV (s84rs_Q M)) :: w))
      (flatBT (Dprin (entry (s84rs_Q M) 1 0 : ℕ∞) BZero)) (w' ++ b1) :=
    scb_compose (Trans (s84rs_R M)) (transC2 (s84rs_R M)) s1
      (Sym.dsym (transV (s84rs_Q M)) :: w)
      (flatBT (Dprin (entry (s84rs_Q M) 1 0 : ℕ∞) BZero)) w' b1
      hc2Rp dR cswR
  -- readback: `Trans Np = Trans Q`
  have hNpread : Trans (s84x_Np M) = Trans (s84rs_Q M) :=
    Trans_Red (s84x_Np M) (tps_Np_rs M hrng)
  -- 中心の値橋（`β`/`γ`）
  have hcenterβ : (entry (s84rs_Q M) 1 (lastIdx (s84rs_Q M)) : ℕ∞)
      = (entry M 1 (Lng M - 1) : ℕ∞) := by
    simp only [lastIdx]; exact_mod_cast hβ
  have hcenterγ : (entry (s84rs_Q M) 1 0 : ℕ∞) = (entry M 1 (s84x_jm2 M) : ℕ∞) := by
    exact_mod_cast hγ
  rw [hcenterβ] at dFinQ
  rw [hcenterγ] at dFinR
  refine ⟨(s1 ++ (Sym.dsym (transV (s84rs_Q M)) :: w), w' ++ b1), ?_, ?_⟩
  · rw [hNpread]; exact dFinQ
  · rw [hLp]; exact dFinR

/-- 訂正 A30 形 `Rightmost84ReplaceCorrected` への合成。 -/
theorem rightmost84ReplaceCorrected_of_surgeryFrame_rs (h : Rm84SurgeryFrame) :
    Rightmost84ReplaceCorrected :=
  rightmost84ReplaceCorrected_of_exists (rightmost84ReplaceExists_of_surgeryFrame_rs h)

#print axioms rightmost84ReplaceExists_of_surgeryFrame_rs
#print axioms rightmost84ReplaceCorrected_of_surgeryFrame_rs

end PSS
