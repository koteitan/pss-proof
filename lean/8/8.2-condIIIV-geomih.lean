import «8».«8.2-condIIIV-assembly»
import «8».«8.2-condIIIV-geometry»

/-!
# §8.2 条件(II)/(IV) STEP assembly の幾何残差 `TspinGeomIH_as` の組立

- 目標: `8.2-condIIIV-assembly` が露出した単一の幾何残差 `TspinGeomIH_as`
  （scb 本体 `tsx_assembly_scb_core_as` が要する slice naturality の入力束）を、
  **transC1/transC2 の slice 自然性 2 本 modulo** で組み立てる。
- Isabelle 対応: `tsx_t1_identified` (isabelle/layerB/pss_wip.thy 104001) の 2 結論
  （終切片 leadform ＝ `Trans (Pred Mp)` の principal 頭同定と、IH-identified な
  `Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))`）＋`bpx_step_setup`/`tsx_Mp_facts`
  の体制事実。深い scb・parent/Adm 幾何（`tsx_jp_geom`/`tsx_parent_slice`/`tsx_Adm_slice`）は
  本残差には現れない（それらは `tsx_c1_eq`/`tsx_c2_eq` の内部でのみ使われ、ここでは
  自然性 2 本を仮定として受け取る）。

## 本ファイルの成果

- `TspinGeomIH_as` の 5 連言のうち、slice 自然性
  `transC1 Mp = transC1 N`（`tsx_c1_eq`）と `transC2 Mp = transC2 N`（`tsx_c2_eq`）を
  **仮定として受け取り**（sibling agent が別ファイルで port 中）、残りを discharge:
  1. **体制事実 (N)**: `RTPS N`・`monoT N`・`1 < Lng N`（`VE34Reg4D N` の分解＋STEP 条件）＋
     `Trans (Pred N) ≠ 0_B`（下の (5) が `Dprin` 形ゆえ）。
  2. **終切片体制 (Mp)**: `RTPS Mp`・`monoT Mp`・`1 < Lng Mp`（`stepTerminalReady_holds`,
     `= vg8x_terminal_slice_DT`）＋`Trans (Pred Mp) ≠ 0_B`・`Trans Mp ≠ 0_B`・
     `Trans (Pred Mp)` 単項（すべて `Trans_principal_head` の `Dprin` 形から）。
  3. **IH-identified `Pred` 形 (5)**: `tsx_t1_identified` (104001) の逐語移植
     `tsx_t1_identified_gi`。IH の VE4 連言（`ihVE4` 段 104043 が消費）を STEP の
     `Pred`-転送（`stepFrontPred`/`stepTermPred`/`stepPredIndex`）でホストの slice に
     書き換え、ホスト leadform（`Trans_principal_head (Pred N)`）と終切片 leadform
     （`Trans_principal_head (Pred Mp)`）で組み上げる。

## 公開ターゲット

`tspinGeomIH_of_slicenat_gi : (c1-nat) → (c2-nat) → TspinGeomIH_as`。ここで
`(c1-nat)`/`(c2-nat)` は `TspinGeomIH_as` の連言 (3)/(4) をそのまま量化子付きで
取り出した命題（`tsx_c1_eq`/`tsx_c2_eq` の Lean 版そのもの）。合成すると
`tspinAssemblyIH_of_geom_as` 経由で `TspinAssemblyIH_tc` が閉じる。

## 数値検証

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（assembly の `w1_as` と同一）で、
transC1/transC2 自然性・IH-identified `Pred` 形・終切片 leadform の単項性が実 `Trans` で
成立することを `#guard` で確認（残差が空虚でも偽陽性でもない）。

- 訂正: なし（Isabelle `tsx_t1_identified`/`bpx_step_setup`/`tsx_Mp_facts` の逐語移植と、
  討伐済 STEP closure `step*_holds`・体制補題の LIVE 合成）。
- 依存 module: `8.2-condIIIV-assembly`（`TspinGeomIH_as`/`TspinAssemblyIH_tc`/
  `tspinAssemblyIH_of_geom_as`/`transC1`/`transC2`/`Dprin`/`addBT` 推移）,
  `8.2-condIIIV-geometry`（`stepTerminalReady_holds`/`stepFrontPred_holds`/
  `stepTermPred_holds`/`stepPredIndex_holds`/`VE34Reg4D`/`VE34Reg4D_DTPS`/`VE34goal`/
  `VEj1p`/`Trans_principal_head`/`monoT_Pred_long`/`RTPS_Pred`/`entry_seg`/`length_Pred`/
  `DTPS_iff` 推移）。
- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  `TspinGeomIH_as` を transC1/transC2 slice 自然性 2 本 modulo で組立。
- Private suffix: `_gi`。
-/

namespace PSS

/-! ## `Dprin` は零項でない（`Dprin v a = .trm [.db v a] ≠ .trm [] = 0_B`） -/

private theorem Dprin_ne_BZero_gi (v : ℕ∞) (a : BT) : Dprin v a ≠ BZero := by
  simp [Dprin, BZero]

/-! ## `tsx_t1_identified` (Isabelle 104001) の逐語移植

STEP ホスト `N`（`VE34Reg4D N`, `VEj1p N < Lng N - 1`）と IH（`VE34goal (Pred N)`）から、
終切片 `Mp = seg N j₀' (Lng N-1)` の leadform（`Trans (Pred Mp)` の principal 頭同定）と、
IH-identified な `Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))` を放出する。 -/

private theorem tsx_t1_identified_gi (N : PS)
    (regD : VE34Reg4D N) (hlt : VEj1p N < Lng N - 1)
    (regDP : VE34Reg4D (Pred N)) (ihP : VE34goal (Pred N)) :
    Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
        = Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
            (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))
      ∧ Trans (Pred N)
        = Dprin (entry N 1 0 : ℕ∞)
            (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
              (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))) := by
  -- 体制事実（Pred N）
  obtain ⟨hRP, hmonoP, _⟩ := (DTPS_iff (Pred N)).mp (VE34Reg4D_DTPS (Pred N) regDP)
  -- 終切片体制（Mp）
  obtain ⟨hMpR, hMpMono, _hMpBrne, hMpLen⟩ := stepTerminalReady_holds N regD hlt
  have hMpT : TPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) := RTPS_TPS _ hMpR
  have hLMp1 : 1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) := by omega
  have hLMp2 : 2 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) := by omega
  have hPredMpR : RTPS (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) :=
    RTPS_Pred _ hMpR
  have hPredMpMono : monoT (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) = true :=
    monoT_Pred_long _ hMpT hMpMono hLMp2
  -- STEP の Pred-転送 closure
  have hFP := stepFrontPred_holds N regD hlt
  have hTP := stepTermPred_holds N regD hlt
  obtain ⟨he10, hej0⟩ := stepPredIndex_holds N regD hlt
  -- (a) 終切片 leadform `Trans (Pred Mp) = D_{N₁,j₀'}(bpHeadT ..)`
  have hpos : 0 < Lng (seg (Pred N) ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0)
      (Lng (Pred N) - 1)) := by
    rw [hTP, length_Pred _ hLMp1]; omega
  have hentryPMp :
      entry (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) 1 0
        = entry N 1 ((Joints N).getD ((Br N).length - 1) 0) := by
    rw [← hTP, entry_seg (Pred N) ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0)
      (Lng (Pred N) - 1) 1 0 hpos, Nat.add_zero]
    exact hej0
  have leadPMp :
      Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))
        = Dprin (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞)
            (bpHeadT (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))) := by
    have h := Trans_principal_head _ hPredMpR hPredMpMono
    rw [hentryPMp] at h
    exact h
  refine ⟨leadPMp, ?_⟩
  -- (b) ホスト leadform `Trans (Pred N) = D_{N₁,0}(bpHeadT ..)`
  have hhost := Trans_principal_head (Pred N) hRP hmonoP
  rw [he10] at hhost
  -- IH の VE4 連言をホストの slice に書き換え
  obtain ⟨_t2, _hP1, _hP2, hP3⟩ := ihP
  rw [hFP, hej0, hTP, ← leadPMp] at hP3
  -- 組立
  calc Trans (Pred N)
      = Dprin (entry N 1 0 : ℕ∞) (bpHeadT (Trans (Pred N))) := hhost
    _ = Dprin (entry N 1 0 : ℕ∞)
          (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
            (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))))) := by
        rw [hP3]

/-! ## 公開ターゲット: transC1/transC2 slice 自然性 2 本から `TspinGeomIH_as` -/

/-- **`TspinGeomIH_as` を transC1/transC2 slice 自然性 modulo で組立**（Isabelle
`tsx_t1_identified` ＋ 体制事実の逐語移植）。仮定 `hc1`/`hc2` は `TspinGeomIH_as` の
連言 (3)/(4) そのまま（`tsx_c1_eq`/`tsx_c2_eq`、sibling agent が別ファイルで port 中）。 -/
theorem tspinGeomIH_of_slicenat_gi
    (hc1 : ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 → VE34Reg4D (Pred N) → VE34goal (Pred N) →
      transC1 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC1 N)
    (hc2 : ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 → VE34Reg4D (Pred N) → VE34goal (Pred N) →
      transC2 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC2 N) :
    TspinGeomIH_as := by
  intro N regD hlt regDP ihP
  -- 体制事実（N）
  obtain ⟨hR, hmono, _⟩ := (DTPS_iff N).mp (VE34Reg4D_DTPS N regD)
  have hL1 : 1 < Lng N := by omega
  -- 終切片体制（Mp）
  obtain ⟨hMpR, hMpMono, _hMpBrne, hMpLen⟩ := stepTerminalReady_holds N regD hlt
  have hLMp1 : 1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) := by omega
  -- slice 自然性（仮定）
  have hc1val := hc1 N regD hlt regDP ihP
  have hc2val := hc2 N regD hlt regDP ihP
  -- IH-identified 形と終切片 leadform（helper）
  obtain ⟨leadPMp, h5⟩ := tsx_t1_identified_gi N regD hlt regDP ihP
  -- `Trans Mp ≠ 0_B`（principal 形）
  have hTMpNe :
      Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ BZero := by
    rw [Trans_principal_head _ hMpR hMpMono]; exact Dprin_ne_BZero_gi _ _
  refine ⟨⟨hR, hmono, hL1, ?_⟩,
    ⟨hMpR, hMpMono, hLMp1, ?_, hTMpNe, ?_⟩, hc1val, hc2val, h5⟩
  · -- Trans (Pred N) ≠ 0_B
    rw [h5]; exact Dprin_ne_BZero_gi _ _
  · -- Trans (Pred Mp) ≠ 0_B
    rw [leadPMp]; exact Dprin_ne_BZero_gi _ _
  · -- ∃ p, Trans (Pred Mp) = .trm [p]
    exact ⟨_, leadPMp⟩

/-! ## `TspinAssemblyIH_tc` の閉包（slice 自然性 2 本 modulo）

`tspinAssemblyIH_of_geom_as`（scb 本体、`8.2-condIIIV-assembly` で無条件緑）へ流し込む。 -/

/-- **`TspinAssemblyIH_tc` を slice 自然性 2 本 modulo で供給**。scb 深部は assembly で
陥落済ゆえ、残るギャップは transC1/transC2 の slice 自然性のみ。 -/
theorem tspinAssemblyIH_of_slicenat_gi
    (hc1 : ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 → VE34Reg4D (Pred N) → VE34goal (Pred N) →
      transC1 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC1 N)
    (hc2 : ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 → VE34Reg4D (Pred N) → VE34goal (Pred N) →
      transC2 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC2 N) :
    TspinAssemblyIH_tc :=
  tspinAssemblyIH_of_geom_as (tspinGeomIH_of_slicenat_gi hc1 hc2)

/-! ## 転記の数値検証（STEP witness 上で実 `Trans` で成立） -/

private def w1_gi : PS := [(0,0),(1,1),(2,2),(2,1),(3,1)]

-- transC1 自然性 `transC1 Mp = transC1 N`（仮定の非空虚性）。
#guard (transC1 (seg w1_gi ((Joints w1_gi).getD ((Br w1_gi).length - 1) 0) (Lng w1_gi - 1))
  == transC1 w1_gi) = true

-- transC2 自然性 `transC2 Mp = transC2 N`（仮定の非空虚性）。
#guard (transC2 (seg w1_gi ((Joints w1_gi).getD ((Br w1_gi).length - 1) 0) (Lng w1_gi - 1))
  == transC2 w1_gi) = true

-- IH-identified `Pred` 形 (5)。
#guard (Trans (Pred w1_gi) == Dprin (entry w1_gi 1 0 : ℕ∞)
  (addBT (bpHeadT (Trans (seg w1_gi 0 ((FirstNodes w1_gi).getD (LastStep w1_gi) 0 - 1))))
    (Trans (Pred (seg w1_gi ((Joints w1_gi).getD ((Br w1_gi).length - 1) 0) (Lng w1_gi - 1)))))) = true

-- 終切片 leadform の単項性 `Trans (Pred Mp)` は `untrm` 長さ 1。
#guard ((untrm (Trans (Pred (seg w1_gi ((Joints w1_gi).getD ((Br w1_gi).length - 1) 0)
  (Lng w1_gi - 1))))).length == 1) = true

#print axioms Dprin_ne_BZero_gi
#print axioms tsx_t1_identified_gi
#print axioms tspinGeomIH_of_slicenat_gi
#print axioms tspinAssemblyIH_of_slicenat_gi

end PSS
