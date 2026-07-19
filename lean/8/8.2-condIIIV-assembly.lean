import «8».«8.2-condIIIV-tspin-close»
import «8».«8.3-condII-masterCF»
import «7».«7.4-Trans-Mark-Pred»

/-!
# §8.2 条件(II)/(IV) STEP スロット assembly（`tsx_assembly` の scb 本体）

- Isabelle: `tsx_assembly` (isabelle/layerB/pss_wip.thy 104073)、その IH-identified 段
  `tsx_t1_identified` (104001)、scb 工具 `tsx_scb_Dpt_lift` (103577)。
- 目標: `8.2-condIIIV-tspin-close` の露出残差 `TspinAssemblyIH_tc`
  （= `Trans N = D_{N₁,0}(F +_B Trans Mp)`、IH 付き）を、`tsx_assembly` の **scb 本体**
  （103558 の replaced-string 再認識）を忠実移植して閉じる方向へ前進させる。

## Wave AT 残差マップの更新（asset-blindness 訂正）

Wave AT は port に「4 scb 工具（無/private）」が要ると記録したが、うち 3 本は既に
public な Lean twin が存在する（notes は STALE）:
- (i) `Trans_unflat_transC2` → **`Trans_c1_c2_decomp`**（public, `8.3-condII-masterCF`）:
  ホスト `M` の mono 枝で `∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b
  ∧ scb_decomp (Trans M) s (flatBT (transC2 M)) b`。Isabelle の `Trans_unflat_transC2`
  ＋存在（`m_7_3_Trans_Mark_MarkedB`）＋`SOME` を **一括**で供給し、しかも Trans M 側の
  完成した scb 分解まで返す（`replaceScb` が実行可能な「最初の文脈」選択なので原文の
  抽象 `SOME` 手続きが不要）。
- (ii) `scbimg_image_BT` → `principal_replacement_image`（public, `7.2-scb-replaceable`）。
  実は本 Lean 経路では (i) が Trans Mp 側の分解を直接返すので **不要**。
- (iii) `m_7_3_Trans_Mark_MarkedB` → `Trans_Mark_mem_MarkedB`（public,
  `7.3-Trans-welldefined`）。(i) に吸収。

残る真の未移植は **(iv) `tsx_scb_Dpt_lift`** のみ（本ファイルで port）。private helper
`scb_addBT_left_74`（`7.4-Trans-Mark-Pred`）は本ファイルへ複製（`_as`）。

## 本ファイルの成果

1. **`tsx_scb_Dpt_lift_as`**（Isabelle `tsx_scb_Dpt_lift` 103577 の逐語移植）: scb 分解が
   principal 頭 `D_v` を通して持ち上がる（`Dsym v` を `s` に前置）。無条件・緑・再利用可能。
2. **`scb_addBT_left_74_as`**（`7.4-Trans-Mark-Pred` の private `scb_addBT_left_74` の複製）。
3. **`tsx_assembly_scb_core_as`**（`tsx_assembly` 104073 の **scb 本体** 523-702 の忠実移植）:
   ホスト `N` とその終切片 `Mp` の surgery データが自然（`transC1 Mp = transC1 N`,
   `transC2 Mp = transC2 N`）で、かつ IH-identified な `Pred` 形
   `Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))` が与えられれば、assembly 等式
   `Trans N = D_{N₁,0}(F +_B Trans Mp)` が出る。前置 `F` の零/非零で場合分け（原文の
   `case True/False`）。両ホストの `Trans_c1_c2_decomp` → 一意性（`scb_unique_decomp_unconditional`）
   → 平坦化一致 → `unflatBT_flat` で項一致。**無条件・緑**（scb 代数の深部を全て閉じた）。
4. **`TspinGeomIH_as`**（新しい単一残差、幾何/自然性の入力束）: 上の core が要する
   `N`/`Mp` の体制・`transC1/2` 自然性・IH-identified `Pred` 形・`Trans (Pred Mp)` 単項性。
   これは Isabelle の `tsx_c1_eq` (103771) / `tsx_c2_eq` (103971) / `tsx_t1_identified`
   (104001) 連鎖（＋`tsx_jp_geom`/`tsx_parent_slice`/`tsx_Adm_slice`/`bpx_step_setup`）の
   Lean 未移植部分そのもの。深い scb は含まず、slice-naturality の transport のみ。
5. **`tspinAssemblyIH_of_geom_as : TspinGeomIH_as → TspinAssemblyIH_tc`**: core の適用。
   これで `TspinAssemblyIH_tc` は **(scb core 緑) modulo (幾何残差 `TspinGeomIH_as`)** に
   分割された。深い頭輸送 scb は本ファイルで陥落し、残差は routine な slice naturality に。

## 数値検証

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（`8.2-condIIIV-tspin-close` の `w1_tc`）で
`TspinGeomIH_as` の各成分（`transC1/2` 自然性、IH-identified `Pred` 形、単項性）が実
`Trans` で成立することを `#guard` で確認（＝残差が空虚でも偽でもない）。

- 訂正: なし。
- 状態: ⚠️ 部分（sorry 0、rc=0、公理 `[propext, Classical.choice, Quot.sound]` のみ）。
  `tsx_assembly` の scb 本体を無条件で緑移植し、`TspinAssemblyIH_tc` を単一の幾何残差
  `TspinGeomIH_as`（slice naturality）modulo に還元。scb 工具 `tsx_scb_Dpt_lift_as` を landing。
- Private suffix: `_as`。
-/

namespace PSS

/-! ## (iv) `tsx_scb_Dpt_lift` の移植（Isabelle 103577）

scb 分解 `scb_decomp X s c b` が principal 頭 `D_v` を通して持ち上がる:
`scb_decomp (D_v X) (Dsym v # s) c b`。`X ≠ 0_B` が要る（中央 `c` の principal 性は
`X` の非零から来る）。 -/

/-- **`scb_decomp` は `Dprin` 頭を通して持ち上がる**（Isabelle `tsx_scb_Dpt_lift` 103577）:
`flatBT (Dprin v X) = Dsym v :: flatBT X` なので前置文字列に `Dsym v` を足すだけ。 -/
theorem tsx_scb_Dpt_lift_as {X : BT} {s c b : List Sym} {v : ℕ∞}
    (d : scb_decomp X s c b) (hXne : X ≠ BZero) :
    scb_decomp (Dprin v X) (.dsym v :: s) c b := by
  obtain ⟨he, hpc, hrb⟩ := d
  refine ⟨?_, ?_, hrb⟩
  · have hf : flatBT (Dprin v X) = .dsym v :: flatBT X := by
      simp [Dprin, flatBT, flatBP]
    rw [hf, he, List.cons_append, List.cons_append]
  · intro _
    exact hpc hXne

/-! ## `scb_addBT_left_74` の複製（`7.4-Trans-Mark-Pred` の private helper） -/

private theorem flatBPTail_append_singleton_as (ps : List BP) (p : BP) :
    flatBPTail (ps ++ [p]) = flatBPTail ps ++ (.cm :: flatBP p) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

/-- **`scb_decomp` は `addBT` 前置を通して持ち上がる**（`7.4` の private
`scb_addBT_left_74` の複製）: `scb_decomp X s c b`, `X` 単項, `Y` 非零 ⟹
`scb_decomp (addBT Y X) (liftScbPrefix Y s) c (b ++ [RP])`。 -/
private theorem scb_addBT_left_as {X Y : BT} {s c b : List Sym}
    (hd : scb_decomp X s c b)
    (hXone : (untrm X).length = 1)
    (hYne : untrm Y ≠ []) :
    scb_decomp (addBT Y X) (liftScbPrefix Y s) c (b ++ [.rp]) := by
  rcases X with ⟨xs⟩
  rcases Y with ⟨ys⟩
  simp only [untrm] at hXone hYne
  cases xs with
  | nil => simp at hXone
  | cons x xs =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact (hYne rfl).elim
          | cons y ys =>
              rcases hd with ⟨hflat, hprincipal, htail⟩
              have hXne : BT.trm [x] ≠ BZero := by simp [BZero]
              have hc : isPTB_str c := hprincipal hXne
              have hflat' : flatBP x = s ++ c ++ b := by
                simpa [flatBT] using hflat
              refine ⟨?_, ?_, ?_⟩
              · cases ys <;>
                  simp [addBT, flatBT, flatBPTail, liftScbPrefix, untrm,
                    flatBPTail_append_singleton_as, hflat', List.append_assoc]
              · intro _
                exact hc
              · intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact htail z hz
                · simpa using hz
      | cons x' xs => simp at hXone

/-! ## `tsx_assembly` の scb 本体（Isabelle 104073 の 523-702）

ホスト `N` と終切片 `Mp` の surgery データが自然（`transC1 Mp = transC1 N`,
`transC2 Mp = transC2 N`）で、IH-identified な `Pred` 形
`Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))` が与えられれば assembly 等式が出る。
両ホストの `Trans_c1_c2_decomp` が `(sM,bM)` / `(s,b)` を供給し、`F +_B ·` 前置と
`Dprin` 頭で持ち上げ（`scb_addBT_left_as` / `tsx_scb_Dpt_lift_as`）、一意性
（`scb_unique_decomp_unconditional`）でホスト側の `(s,b)` を pin、平坦化一致から
`unflatBT_flat` で項一致。前置 `F` の零/非零で場合分け（原文 `case True/False`）。 -/

/-- **`tsx_assembly` の scb 本体**（Isabelle 104073、523-702 の忠実移植）。 -/
private theorem tsx_assembly_scb_core_as
    (N Mp : PS) (F : BT) (e10 : ℕ)
    (RN : RTPS N) (monoN : monoT N = true) (LN : 1 < Lng N)
    (t1Nne : Trans (Pred N) ≠ BZero)
    (RMp : RTPS Mp) (monoMp : monoT Mp = true) (LMp : 1 < Lng Mp)
    (t1MpNe : Trans (Pred Mp) ≠ BZero) (TMpNe : Trans Mp ≠ BZero)
    (t1MpP : ∃ p, Trans (Pred Mp) = .trm [p])
    (c1eq : transC1 Mp = transC1 N) (c2eq : transC2 Mp = transC2 N)
    (t1Nform : Trans (Pred N) = Dprin (e10 : ℕ∞) (addBT F (Trans (Pred Mp)))) :
    Trans N = Dprin (e10 : ℕ∞) (addBT F (Trans Mp)) := by
  -- 終切片の scb 分解（c₁ 側 / c₂ 側が同じ `(sM,bM)`）
  obtain ⟨sM, bM, dPredMp0, dMp0⟩ := Trans_c1_c2_decomp Mp RMp monoMp LMp t1MpNe
  rw [c1eq] at dPredMp0
  rw [c2eq] at dMp0
  -- ホストの scb 分解（c₁ 側 / c₂ 側が同じ `(s,b)`）
  obtain ⟨s, b, dPredN, dN⟩ := Trans_c1_c2_decomp N RN monoN LN t1Nne
  -- 単項性（`untrm` の長さ 1）
  obtain ⟨pMp, hpMp⟩ := t1MpP
  have hXone1 : (untrm (Trans (Pred Mp))).length = 1 := by rw [hpMp]; simp [untrm]
  obtain ⟨qMp, hqMp⟩ := Trans_monoT_principal Mp RMp monoMp TMpNe
  have hXone2 : (untrm (Trans Mp)).length = 1 := by rw [hqMp]; simp [untrm]
  -- 「同じ scb データ → 平坦化一致 → 項一致」の最終段（総称版）
  have finish : ∀ (R : BT) (s' b' : List Sym),
      scb_decomp (Trans N) s' (flatBT (transC2 N)) b' →
      scb_decomp R s' (flatBT (transC2 N)) b' →
      Trans N = R := by
    intro R s' b' hN hR
    have hfl : flatBT (Trans N) = flatBT R := by rw [hN.1, hR.1]
    calc Trans N = unflatBT (flatBT (Trans N)) := (unflatBT_flat _).symm
      _ = unflatBT (flatBT R) := by rw [hfl]
      _ = R := unflatBT_flat _
  by_cases hF : F = BZero
  · -- 退化前置: `addBT 0_B X = X`
    subst hF
    have haddP : addBT BZero (Trans (Pred Mp)) = Trans (Pred Mp) := by rw [hpMp]; rfl
    have haddM : addBT BZero (Trans Mp) = Trans Mp := by rw [hqMp]; rfl
    have d1c : scb_decomp (Dprin (e10 : ℕ∞) (Trans (Pred Mp)))
        (.dsym (e10 : ℕ∞) :: sM) (flatBT (transC1 N)) bM :=
      tsx_scb_Dpt_lift_as dPredMp0 t1MpNe
    have d1c' : scb_decomp (Trans (Pred N))
        (.dsym (e10 : ℕ∞) :: sM) (flatBT (transC1 N)) bM := by
      rw [t1Nform, haddP]; exact d1c
    obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional _ _ _ _ _ _ dPredN d1c'
    rw [hs, hb] at dN
    have d2c : scb_decomp (Dprin (e10 : ℕ∞) (Trans Mp))
        (.dsym (e10 : ℕ∞) :: sM) (flatBT (transC2 N)) bM :=
      tsx_scb_Dpt_lift_as dMp0 TMpNe
    rw [haddM]
    exact finish _ _ _ dN d2c
  · -- 非零前置
    have hFne : untrm F ≠ [] := by
      rcases F with ⟨fs⟩
      simp only [untrm]
      intro h
      subst h
      exact hF rfl
    have d1b : scb_decomp (addBT F (Trans (Pred Mp)))
        (liftScbPrefix F sM) (flatBT (transC1 N)) (bM ++ [.rp]) :=
      scb_addBT_left_as dPredMp0 hXone1 hFne
    have hneF1 : addBT F (Trans (Pred Mp)) ≠ BZero := by
      rw [hpMp]; rcases F with ⟨fs⟩; simp [addBT, BZero]
    have d1c : scb_decomp (Dprin (e10 : ℕ∞) (addBT F (Trans (Pred Mp))))
        (.dsym (e10 : ℕ∞) :: liftScbPrefix F sM) (flatBT (transC1 N)) (bM ++ [.rp]) :=
      tsx_scb_Dpt_lift_as d1b hneF1
    have d1c' : scb_decomp (Trans (Pred N))
        (.dsym (e10 : ℕ∞) :: liftScbPrefix F sM) (flatBT (transC1 N)) (bM ++ [.rp]) := by
      rw [t1Nform]; exact d1c
    obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional _ _ _ _ _ _ dPredN d1c'
    rw [hs, hb] at dN
    have d2b : scb_decomp (addBT F (Trans Mp))
        (liftScbPrefix F sM) (flatBT (transC2 N)) (bM ++ [.rp]) :=
      scb_addBT_left_as dMp0 hXone2 hFne
    have hneF2 : addBT F (Trans Mp) ≠ BZero := by
      rw [hqMp]; rcases F with ⟨fs⟩; simp [addBT, BZero]
    have d2c : scb_decomp (Dprin (e10 : ℕ∞) (addBT F (Trans Mp)))
        (.dsym (e10 : ℕ∞) :: liftScbPrefix F sM) (flatBT (transC2 N)) (bM ++ [.rp]) :=
      tsx_scb_Dpt_lift_as d2b hneF2
    exact finish _ _ _ dN d2c

/-! ## 幾何/自然性の単一残差 `TspinGeomIH_as` と assembly への配線

`tsx_assembly_scb_core_as` が要する幾何入力を束ねた単一 Prop。これは Isabelle の
`tsx_c1_eq` (103771) / `tsx_c2_eq` (103971) / `tsx_t1_identified` (104001) 連鎖
（＋`tsx_jp_geom`/`tsx_parent_slice`/`tsx_Adm_slice`/`bpx_step_setup`）の Lean 未移植部分。
深い scb は無く、slice-naturality の transport のみ（`m_7_4_Mark_Trans_repr` /
`m_7_4_Mark_Pred_boundary` 経由の Mark 自然性が本体）。 -/

/-- **STEP assembly の幾何残差**（`tsx_c1_eq` / `tsx_c2_eq` / `tsx_t1_identified` の束）:
ホスト `N` とその終切片 `Mp = seg N j₀' (Lng N-1)` の体制・surgery データ自然性・
IH-identified な `Pred` 形。 -/
def TspinGeomIH_as : Prop :=
  ∀ N : PS, VE34Reg4D N → VEj1p N < Lng N - 1 →
    VE34Reg4D (Pred N) → VE34goal (Pred N) →
    (RTPS N ∧ monoT N = true ∧ 1 < Lng N ∧ Trans (Pred N) ≠ BZero) ∧
    (RTPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
      monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true ∧
      1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
      Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) ≠ BZero ∧
      Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ BZero ∧
      (∃ p, Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))) = .trm [p])) ∧
    transC1 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC1 N ∧
    transC2 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC2 N ∧
    Trans (Pred N) = Dprin (entry N 1 0 : ℕ∞)
      (addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))))
        (Trans (Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)))))

/-- **`TspinAssemblyIH_tc` を幾何残差 `TspinGeomIH_as` modulo で供給**: scb 本体
`tsx_assembly_scb_core_as`（無条件・緑）へ幾何入力を流し込むだけ。深い頭輸送 scb は本
ファイルで陥落済み。 -/
theorem tspinAssemblyIH_of_geom_as (hg : TspinGeomIH_as) : TspinAssemblyIH_tc := by
  intro N regD hlt regDP ihP
  obtain ⟨⟨RN, monoN, LN, t1Nne⟩,
      ⟨RMp, monoMp, LMp, t1MpNe, TMpNe, t1MpP⟩, c1eq, c2eq, t1Nform⟩ :=
    hg N regD hlt regDP ihP
  exact tsx_assembly_scb_core_as N _ _ _ RN monoN LN t1Nne RMp monoMp LMp
    t1MpNe TMpNe t1MpP c1eq c2eq t1Nform

/-! ## 転記の数値検証（幾何残差の各成分が STEP witness 上で実 `Trans` で成立）

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（`8.2-condIIIV-tspin-close` の `w1_tc`、
`VE34Reg4D`, `VEj1p = 3 < 4`）で `j₀' = 1`、`transC1/2` 自然性・IH-identified `Pred` 形・
`Trans (Pred Mp)` 単項性がすべて成立（＝残差が空虚でなく偽陽性でもない）。 -/

private def w1_as : PS := [(0,0),(1,1),(2,2),(2,1),(3,1)]

-- 終切片 surgery データ `c₁` の自然性 `transC1 Mp = transC1 N`。
#guard (transC1 (seg w1_as ((Joints w1_as).getD ((Br w1_as).length - 1) 0) (Lng w1_as - 1))
  == transC1 w1_as) = true

-- 終切片 surgery データ `c₂` の自然性 `transC2 Mp = transC2 N`。
#guard (transC2 (seg w1_as ((Joints w1_as).getD ((Br w1_as).length - 1) 0) (Lng w1_as - 1))
  == transC2 w1_as) = true

-- IH-identified `Pred` 形 `Trans (Pred N) = D_{N₁,0}(F +_B Trans (Pred Mp))`。
#guard (Trans (Pred w1_as) == Dprin (entry w1_as 1 0 : ℕ∞)
  (addBT (bpHeadT (Trans (seg w1_as 0 ((FirstNodes w1_as).getD (LastStep w1_as) 0 - 1))))
    (Trans (Pred (seg w1_as ((Joints w1_as).getD ((Br w1_as).length - 1) 0) (Lng w1_as - 1)))))) = true

-- `Trans (Pred Mp)` は単項（`untrm` 長さ 1）。
#guard ((untrm (Trans (Pred (seg w1_as ((Joints w1_as).getD ((Br w1_as).length - 1) 0)
  (Lng w1_as - 1))))).length == 1) = true

#print axioms tsx_scb_Dpt_lift_as
#print axioms tsx_assembly_scb_core_as
#print axioms tspinAssemblyIH_of_geom_as

end PSS
