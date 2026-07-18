import «8».«8.4-slice-ext-close»
import «8».«8.4-exch84-regs»
import «8».«8.4-exch84-mcond»
import «8».«8.2-condV-VE-wnx»
import «8».«8.2-condV-VE-close»
import «8».«8.2-condIIIV-terminal-slice-Trans»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.4-kind1-shape»
import «8».«8.4-l1-slice-data»
import «8».«8.4-rm84-rfacts-close»
import «8».«8.4-mnform-corner-dispatch»
import «8».«8.4-corner-engine»
import «8».«8.4-corner-deep»
import «8».«8.4-exch84-from-slice»
import «8».«8.4-slicepkg-residuals»
import «8».«8.4-d4a-trunk»

/-!
# §8.4 `Np_c2decomp_sc3`（`d4b` dispatch 残差）の無条件 discharge

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係、
  補題（条件(III)か(IV)の下での各種 scb 分解）content.md 4802 の L6）。
- 対象: ビルド済み «8».«8.4-slice-ext-close» が露出した named 残差
  `Np_c2decomp_sc3`（= Isabelle `w84x_d4b_dispatch`, layerB/pss_wip.thy:79198）。
  N 側 transC2 分解 `d2`（頭 `Dsym(M₁,ⱼ₋₃)`）から `Np` 側 transC2 分解 `d4b`
  （頭 `Dsym(M₁,ⱼ₋₂)`・同一中辺 `flatBT (transC2 M)`・同一末尾 `b1`）を作る。

## 移植構造

Isabelle `w84x_d4b_dispatch` は `s84x_jm3 M < s84x_jm2 M` で分岐する（自明枝
`j₋₃ = j₋₂` は `Np = N`、非自明枝は §8.4 正則性 `cfbx_reg`）。本 Lean 移植は
両枝を **1 本の値事実**

  `valNp : Trans (s84x_Np M) = D_{M₁,ⱼ₋₂} (bpHeadT (Trans (s84x_N M)))`

に集約する（Isabelle `w84x_d4b_of_regS` の値段 `valNp'`）。値が得られれば残りは純 scb
操作: `d2` の flatten から源 principal `princN`（`flatBT_head_dsym_principal_nc2`）を取り、
principal 頭を剥がし（`scb_dprin_unlift_nc2` = Isabelle `w84x_scb_unlift`）、新しい頭
`Dsym(M₁,ⱼ₋₂)` を被せ直す（`scb_dprin_lift_nc2` = Isabelle `scb_Dpt_lift`）だけ
（«8».«8.4-exch84-d4a» の `d4a` 骨格と同型）。

### 値 `valNp` の証明（reduced host 経由、trunk 枝不要）

M→R transport（`wnx_seg_transport_W1/W2` ＋ `repr_entry1_shift_gen`）で
`Trans (s84x_Np M)` を **簡約host `RN = Red (s84x_N M)` の相対 offset
`m = j₋₂ - j₋₃` の終切片値** へ落とす。その簡約host 値
`Trans (seg RN m (Lng RN - 1)) = D_{RN₁,ₘ} (bpHeadT (Trans RN))` は:

* `m = 0`（`j₋₃ = j₋₂`）: `VE_index0`（body 保存自明）＋ `slice_Trans_principal_head`。
* `m > 0`（guard `j₋₃ < j₋₂`）: `regS_holds`（«8».«8.4-exch84-regs»、`Regs_jm3Marked_holds`＋
  `regs_jm2_lt_transJ0_holds`＋`Regs_MCOND_holds` から無条件、`VEReg m RN` は
  `Br RN ≠ []` を内蔵）＋ `vcx_VE_all`（«8».«8.2-condV-VE-close»）で body 保存
  `VEeq m RN` を得、`slice_Trans_principal_head` で頭を付ける。

`w84x_d4b_of_regS` が要求する raw slice `cfbx_reg (…) (s84x_N M)` は raw slice が
非簡約（`s84x_N M = IncrFirstN k RN`）なので Lean では取れないが、`Trans` は簡約不変
（`wnx_seg_transport_W1 = Trans_Red`）なので簡約host 版で等価に閉じられる。d4a 側で
`Br (Red (Pred (s84x_N M))) ≠ []` が明示前提だったのと違い、N 側は `regS_holds` が
`Br RN ≠ []` を保証するので **trunk 枝の場合分けは不要**。

- 依存（すべてビルド済み・main 6e1621a）: «8».«8.4-slice-ext-close»
  （`Np_c2decomp_sc3`・`c7Rightend_of_rm84_np_sc3`・`sliceExtTupleEngines_of_reduced_sc3`・
  `sliceExtTupleResidual_of_reduced_sc3`・`s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・
  `Trans`/`transC2`/`scb_decomp`/`isPTB_str`・`Dprin`/`bpHeadT`/`flatBT`/`BZero`・
  `Rightmost84ReplaceExists`・`Kind1Shape_se`/`L1SliceData_se`・推移的に
  `s84c1_jm2_basic`/`Adm_le`/`regs_jm2_lt_transJ0_holds`/`Lng_Red_invariance`）、
  «8».«8.4-exch84-regs»（`regS_holds`/`Regs_mcx_regS`）、«8».«8.4-exch84-mcond»
  （`Regs_jm3Marked_holds`/`Regs_MCOND_holds`）、«8».«8.2-condV-VE-wnx»
  （`wnx_seg_transport_W1/W2/W3`・`repr_entry1_shift_gen`）、«8».«8.2-condV-VE-close»
  （`vcx_VE_all`・推移的に `VE_index0`/`VEReg`/`VEeq`）、
  «8».«8.2-condIIIV-terminal-slice-Trans»（`slice_Trans_principal_head`）、
  «8».«8.2-standard-slice-Red-strongmono»（`standard_slice_Red_strongmono`/`DTPS_iff`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound、無条件）。
- Private helper suffix: `_nc2`。
-/

namespace PSS

/-! ## 1. scb 操作の骨格（«8».«8.4-exch84-d4a» の private `_d4` の複製、private は module 跨ぎ不可） -/

/-- Isabelle `w84x_scb_unlift` (layerB/pss_wip.thy:78906): principal 頭 `Dprin v` と
先頭記号 `Dsym v` を同時に剥がす。 -/
private theorem scb_dprin_unlift_nc2 {W : BT} {v : ℕ∞} {s c b : List Sym}
    (d : scb_decomp (Dprin v W) (Sym.dsym v :: s) c b) : scb_decomp W s c b := by
  obtain ⟨hflat, hipt, hb⟩ := d
  refine ⟨?_, ?_, hb⟩
  · have h1 : flatBT (Dprin v W) = Sym.dsym v :: flatBT W := by
      simp [Dprin, flatBT, flatBP]
    rw [h1] at hflat
    simpa [List.cons_append] using hflat
  · intro _
    exact hipt (by simp [Dprin, BZero])

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): principal 頭 `Dprin v` と
先頭記号 `Dsym v` を被せると scb 分解の中辺・末尾は保存される。 -/
private theorem scb_dprin_lift_nc2 {W : BT} {v : ℕ∞} {s c b : List Sym}
    (d : scb_decomp W s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v W) (Sym.dsym v :: s) c b := by
  obtain ⟨hflat, _, hb⟩ := d
  refine ⟨?_, ?_, hb⟩
  · have h1 : flatBT (Dprin v W) = Sym.dsym v :: flatBT W := by
      simp [Dprin, flatBT, flatBP]
    rw [h1, hflat]
    simp [List.cons_append]
  · intro _; exact ipt

/-- 頭が `Sym.dsym v` の flatten を持つ BT は単一 principal `Dprin v (bpHeadT t)`。 -/
private theorem flatBT_head_dsym_principal_nc2 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : t = Dprin v (bpHeadT t) := by
  cases t with
  | trm ps =>
    rcases ps with _ | ⟨p, ps'⟩
    · simp [flatBT] at h
    · rcases p with ⟨u, a⟩
      rcases ps' with _ | ⟨q, qs⟩
      · simp only [flatBT, flatBP] at h
        injection h with hhead _
        injection hhead with hu
        subst hu
        rfl
      · simp [flatBT, flatBP] at h

/-! ## 2. `Np_c2decomp_sc3` の無条件 discharge -/

/-- **`Np_c2decomp_sc3` の完全証明**（無条件、= Isabelle `w84x_d4b_dispatch`）。 -/
theorem np_c2decomp_holds : Np_c2decomp_sc3 := by
  intro M s1 b1 hST hmono hp hj1 hcond d2
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  -- 基本の添字
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm3le : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have hle0jm2m1 : le0 M (s84x_jm2 M) (Lng M - 1) = true := (s84c1_jm2_basic M hp).2.2
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true :=
    (Regs_jm3Marked_holds M hMR hMT hp).1.2.2
  -- 簡約host `RN = Red (s84x_N M)` の基本性質
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have hLenRN : Lng (Red (s84x_N M)) = Lng M - s84x_jm3 M :=
    (Lng_Red_invariance (s84x_N M) NT).trans hlenN
  have hDT : DTPS (Red (s84x_N M)) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 1) hST jm3lt (le_refl _) leR3
  obtain ⟨hRNR, hmonoRN, _hdescRN⟩ := (DTPS_iff _).mp hDT
  have hRNT : TPS (Red (s84x_N M)) := RTPS_TPS _ hRNR
  have hmlt : s84x_jm2 M - s84x_jm3 M < Lng (Red (s84x_N M)) - 1 := by rw [hLenRN]; omega
  -- REGS の producer（無条件）
  have regSAll : Regs_mcx_regS :=
    regS_holds Regs_jm3Marked_holds regs_jm2_lt_transJ0_holds Regs_MCOND_holds
  -- 簡約host 値: `Trans (seg RN m (Lng RN-1)) = D_{RN₁,ₘ} (bpHeadT (Trans RN))`
  have hval : Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                (Lng (Red (s84x_N M)) - 1))
      = Dprin ((entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (s84x_N M)))) := by
    have key : s84x_jm2 M - s84x_jm3 M
          ≤ (Joints (Red (s84x_N M))).getD ((Br (Red (s84x_N M))).length - 1) 0
        ∧ VEeq (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) := by
      rcases Nat.eq_zero_or_pos (s84x_jm2 M - s84x_jm3 M) with hm0 | hmpos
      · exact ⟨by rw [hm0]; exact Nat.zero_le _,
              by rw [hm0]; exact VE_index0 (Red (s84x_N M)) hRNT⟩
      · have hguard : s84x_jm3 M < s84x_jm2 M := by omega
        have hVEReg : VEReg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) :=
          regSAll M hST hmono hp hj1 hcond hguard
        refine ⟨?_, vcx_VE_all (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M)) hVEReg⟩
        obtain ⟨-, -, -, hdisj⟩ := hVEReg
        rcases hdisj with hlt' | ⟨heq', -⟩ <;> omega
    obtain ⟨hmleq, hbody⟩ := key
    have hmonoSlice : monoT (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
        (Lng (Red (s84x_N M)) - 1)) = true :=
      mono_slice (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M) (Lng (Red (s84x_N M)) - 1)
        hRNT hmonoRN hmlt (le_refl _) hmleq
    have hprinc := slice_Trans_principal_head (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
      (Lng (Red (s84x_N M)) - 1) hRNR hmlt (le_refl _) hmonoSlice
    unfold VEeq at hbody
    rw [hprinc, hbody]
  -- M→R transport bricks
  have ham : s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M) = s84x_jm2 M := by omega
  have hW1 : Trans (s84x_N M) = Trans (Red (s84x_N M)) :=
    wnx_seg_transport_W1 M (s84x_jm3 M) (Lng M - 1) jm3lt
  have hW2 : Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 1))
      = Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                 (Lng (Red (s84x_N M)) - 1)) :=
    wnx_seg_transport_W2 M (s84x_jm3 M) (Lng M - 1) (s84x_jm2 M - s84x_jm3 M) hMR
      jm3lt (le_refl _) leR3 (by rw [ham]; exact jm2lt) (by rw [ham]; exact hle0jm2m1)
  have hentry : entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M)
      = entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) :=
    repr_entry1_shift_gen M (s84x_jm3 M) (Lng M - 1) (s84x_jm2 M - s84x_jm3 M) hMR
      jm3lt (le_refl _) leR3
      (by show s84x_jm2 M - s84x_jm3 M < Lng (Red (s84x_N M)); rw [hLenRN]; omega)
  -- 値事実 `valNp`
  have valNp : Trans (s84x_Np M)
      = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) (bpHeadT (Trans (s84x_N M))) := by
    calc Trans (s84x_Np M)
        = Trans (seg M (s84x_jm2 M) (Lng M - 1)) := rfl
      _ = Trans (seg M (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) (Lng M - 1)) := by rw [ham]
      _ = Trans (seg (Red (s84x_N M)) (s84x_jm2 M - s84x_jm3 M)
                   (Lng (Red (s84x_N M)) - 1)) := hW2
      _ = Dprin ((entry (Red (s84x_N M)) 1 (s84x_jm2 M - s84x_jm3 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (s84x_N M)))) := hval
      _ = Dprin ((entry M 1 (s84x_jm3 M + (s84x_jm2 M - s84x_jm3 M)) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (s84x_N M)))) := by rw [hentry]
      _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (Red (s84x_N M)))) := by rw [ham]
      _ = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
              (bpHeadT (Trans (s84x_N M))) := by rw [← hW1]
  -- 源 principal（`d2` の flatten から無条件に）
  have hf : flatBT (Trans (s84x_N M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (s1 ++ flatBT (transC2 M) ++ b1) := by
    have h := d2.1
    simpa [List.cons_append] using h
  have princN : Trans (s84x_N M)
      = Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) (bpHeadT (Trans (s84x_N M))) :=
    flatBT_head_dsym_principal_nc2 hf
  have iptN : isPTB_str (flatBT (transC2 M)) := by
    apply d2.2.1
    rw [princN]; simp [Dprin, BZero]
  rw [princN] at d2
  have inner : scb_decomp (bpHeadT (Trans (s84x_N M))) s1 (flatBT (transC2 M)) b1 :=
    scb_dprin_unlift_nc2 d2
  have lifted := scb_dprin_lift_nc2
    (v := ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)) inner iptN
  rw [valNp]
  exact lifted

#print axioms np_c2decomp_holds

/-! ## 3. 下流組立（`SliceExtTupleEngines_st` / `SliceExtTupleResidual` の解錠）

`Np_c2decomp_sc3` が閉じたので、«8».«8.4-slice-ext-close» の還元と Wave AE/AF で
無条件化した `Rightmost84ReplaceExists`・`Kind1Shape_se`・`L1SliceData_se` を合わせて、
`SliceExtTupleEngines_st` と底タプル残差 `SliceExtTupleResidual` を無条件に得る。 -/

/-- `C7Rightend_se`（`c7`）が無条件で閉じる。 -/
theorem c7Rightend_holds_nc2 : C7Rightend_se :=
  c7Rightend_of_rm84_np_sc3 rightmost84ReplaceExists_rc2 np_c2decomp_holds

/-- `SliceExtTupleEngines_st` が無条件で閉じる。 -/
theorem sliceExtTupleEngines_holds_nc2 : SliceExtTupleEngines_st :=
  sliceExtTupleEngines_of_reduced_sc3 kind1Shape_holds rightmost84ReplaceExists_rc2
    np_c2decomp_holds l1SliceData_holds

/-- 底タプル残差 `SliceExtTupleResidual` が無条件で閉じる。 -/
theorem sliceExtTupleResidual_holds_nc2 : SliceExtTupleResidual :=
  sliceExtTupleResidual_of_reduced_sc3 kind1Shape_holds rightmost84ReplaceExists_rc2
    np_c2decomp_holds l1SliceData_holds

#print axioms c7Rightend_holds_nc2
#print axioms sliceExtTupleEngines_holds_nc2
#print axioms sliceExtTupleResidual_holds_nc2

/-! ## 4. `Exch84_condIIIIV_slicepkg` の単一残差への collapse

`SliceExtTupleResidual` が無条件化したので、slicepkg dispatch
(`exch84slicepkg_of_dispatch_md`, «8».«8.4-mnform-corner-dispatch») の 6 脚のうち **5 脚が
無条件に閉じる**:

| 脚 | producer | 状態 |
|---|---|---|
| `hD4a : NestScbD4aTransport_ns` | `nestScbD4aTransport_dk`（Wave AC） | 無条件 |
| `hC4 : TransC2HoleDecomp_md` | `transC2HoleDecomp_holds_sr`（Wave Z） | 無条件 |
| `hext : MnformBottomExtResidual` | `mnformBottomExtResidual_holds sliceExtTupleResidual_holds_nc2` | **本 wave で無条件化** |
| `hb1 : Base1p_condIIIIV` | `base1pCondIIIIV_holds_bl3 base1pCorner_holds_cd`（Wave AE/AF） | 無条件 |
| `hcorner : MnformCornerResidual_md` | `mnformCornerResidual_holds_ce (mnformCornerCoreResidual_holds_cc …)` | **残差 1 本経由** |
| `hb0 : Base0_condIIIIV` | `base0CondIIIIV_holds_bl3 hcorner` | `hcorner` に従属 |

`hcorner`（と従属する `hb0`）は隅コア `MnformCornerCoreResidual_ce` へ、それは
`mnformCornerCoreResidual_holds_cc` により `TransC2HoleDecomp_md`（無条件）／
`CornerC2Kind1_cc`（`cornerC2Kind1_holds_cd`, 無条件）／`CornerCoreReadouts_cc` の 3 入力へ
分解される。前 2 者は無条件なので、**slicepkg 全体が単一の未移植残差
`CornerCoreReadouts_cc`（隅 `d4vx_core` 塔 = Isabelle `c4cx2_condIV_mnform_of_slice`）へ
collapse する**。 -/
theorem exch84slicepkg_of_cornerReadouts_nc2 (hread : CornerCoreReadouts_cc) :
    Exch84_condIIIIV_slicepkg :=
  let hcorner : MnformCornerResidual_md :=
    mnformCornerResidual_holds_ce
      (mnformCornerCoreResidual_holds_cc transC2HoleDecomp_holds_sr hread
        cornerC2Kind1_holds_cd)
  exch84slicepkg_of_dispatch_md
    nestScbD4aTransport_dk
    transC2HoleDecomp_holds_sr
    (mnformBottomExtResidual_holds sliceExtTupleResidual_holds_nc2)
    hcorner
    (base0CondIIIIV_holds_bl3 hcorner)
    (base1pCondIIIIV_holds_bl3 base1pCorner_holds_cd)

#print axioms exch84slicepkg_of_cornerReadouts_nc2

end PSS
