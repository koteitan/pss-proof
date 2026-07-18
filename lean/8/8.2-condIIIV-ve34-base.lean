import «8».«8.2-condIIIV-deep3»
import «8».«8.2-condV-VE-base2»

/-!
# §8.2 条件(II)/(IV) VE34 BASE 脚の極小基底（`Lng = TrMax + 2`）を無条件討伐

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、原文が `j₁ - TrMax M` に関する数学的帰納法で示すと述べている部分
  （「subexpr-component-`Pred`」補題、L3360）。`8.2-condIIIV-deep3` の
  `condIIIVterminalSlice_of_deep2` は `condIIIVts` フィールド（`CondIIIVterminalSlice`）を
  **四つの残差** `{VE3Base, VE3Step, VE4Base, VE4Step}` に還元した。本ファイルはその
  BASE 二残差 `{VE3Base, VE4Base}`（§7.4 頭シフト readback surgery、`VEj1p Q = Lng Q - 1`）の
  **真の極小基底 `Lng N = TrMax N + 2`（＝`j₁ - TrMax = 1`）を無条件で討伐** する。
- 訂正: なし（Isabelle 側で証明済みの補題の逐語移植、または名前付き Prop 骨格）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）: BASE の実体は `bfx_*` (104483–105477)／
  `hqx_*` (108411–108722) の run-peel 後ろ剥がし機構で、その最下段（`j₁ - TrMax = 1`、
  151/151 のホスト）は対角幹に末尾単一列を付けた列 `N = diagSeq u v ++ [(wp, w)]` の
  `Trans` 直接計算に落ちる。本ファイルはその極小基底を、条件(V) 双子
  `8.2-condV-VE-base2` の BASE 直接計算パターン（`a0x_base_VE_vb2` の `Adm0` 枝＝
  case-3 diagApp）と `8.1-Pred-diagSeq-Trans` の `Pred_diagSeq_Trans`／`diagSeq_Trans` で
  逐語に閉じる。⚠️ naive prefix-append 帰納は反証済（Isabelle run-peel は非極小基底＝
  run 領域でのみ必要）。非極小基底 `TrMax N + 2 < Lng N`（run 領域）は名前付き残差
  `{VE3BaseDeep, VE4BaseDeep}` に露出する（＝Isabelle の `bfx_` run-peel 対象）。
- 幾何: 極小基底 `Lng N = TrMax N + 2` かつ `VEj1p N = Lng N - 1` かつ体制 `VE34Reg4` では
  `N = diagSeq u v ++ [(wp, w)]`（`v = u + TrMax N`）で、`0 < j₀' < TrMax` ＋ 非対角ガード
  （`w < wp`）より末尾列は `Pred_diagSeq_Trans` の case 3（`u + 1 < wp ∧ wp ≤ v ∧ w < wp`）。
  前置辞 `seg N 0 (fnLS - 1) = seg N 0 (Lng - 2) = diagSeq u v`（`m1_bounds` で `fnLS-1 = Lng-2`）、
  終切片 `seg N j₀' (Lng - 1) = diagSeq (wp-1) v ++ [(wp, w)]`（case 4）。三つの `Trans` を
  直接計算して VE3goal/VE4goal を `bpHeadT (Dprin _ _) = _` の rfl に落とす。
- 依存 module: `8.2-condIIIV-deep3`（`VE3Base`/`VE3Step`/`VE4Base`/`VE4Step`/`VE3goal`/
  `VE4goal`/`VE34Reg4`/`VEj1p`/`m1_bounds`/`condIIIVterminalSlice_of_deep2`/
  `CondIIIVterminalSlice`／§6-§7 補題群を推移的に）、`8.2-condV-VE-base2`
  （`baseU_alltrunk_diag_entry`／`Pred_diagSeq_Trans`／`diagSeq_Trans`／`entry_diagSeq_68`／
  `seg_getElem_68`／`take_eq_seg`／`Pred_eq_take` を推移的に）。
- 状態: ⚠️ 部分（sorry 0、rc=0）。`VE3Base`/`VE4Base` の極小基底 `Lng = TrMax + 2` を
  **無条件討伐**、残差は非極小基底（run 領域）`{VE3BaseDeep, VE4BaseDeep}`
  ＋ STEP `{VE3Step, VE4Step}`。
- Private suffix: `_vb`。
-/

namespace PSS

/-! ## 私的補助（suffix `_vb`） -/

/-- `leR M 0 a b` は両添字を `Lng M` 未満に閉じ込める（入口 `leR0_bounds_v34` の再掲）。 -/
private theorem leR0_bounds_vb (M : PS) (a b : ℕ)
    (h : leR M 0 a b = true) : a < Lng M ∧ b < Lng M := by
  have h0 : le0 M a b = true := by simpa [leR] using h
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact ⟨h0.1.1, h0.1.2⟩

/-- 枝の左端は `Lng` 未満（Isabelle `a1_FN_lt`, pss_mechanized 33186）。 -/
private theorem FN_lt_vb (M : PS) (J : ℕ) (hM : TPS M) (hmono : monoT M = true)
    (hJ : J < (Br M).length) : (FirstNodes M).getD J 0 < Lng M :=
  (leR0_bounds_vb M _ _
    (nextR_implies_row0 M 0 _ _ (Joints_nextR_FirstNodes M J hM hmono hJ)).2).2

/-- `bpHeadT (Dprin a b) = b`（principal 項の内部項読み出し、`rfl`）。 -/
private theorem bpHeadT_Dprin_vb (a : ℕ∞) (b : BT) : bpHeadT (Dprin a b) = b := rfl

/-- 体制 `VE34Reg4` の下で `TrMax N + 2 ≤ Lng N`（`VEReg_TrMax_le` の VE34Reg4 版）。
BASE 二分岐 `Lng N = TrMax N + 2` / `TrMax N + 2 < Lng N` に必要。 -/
private theorem reg4_TrMax_le_vb (N : PS) (reg : VE34Reg4 N) : TrMax N + 2 ≤ Lng N := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _⟩, _, _⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hgeom := (FirstNodes_TrMax_Joints N _ hM hmono hJ).2
  have hfnlt := FN_lt_vb N _ hM hmono hJ
  omega

/-- 対角幹＋末尾単一列の終切片は左端だけ `m` 進める（`8.2-condV-VE-base2` の
`seg_diagApp_vb2` の再掲）。 -/
private theorem seg_diagApp_vb (u v wp w m : ℕ) (huv : u < v) (hm : m < v - u) :
    seg (diagSeq u v ++ [(wp, w)]) m
      (Lng (diagSeq u v ++ [(wp, w)]) - 1) =
      diagSeq (u + m) v ++ [(wp, w)] := by
  apply List.ext_getElem
  · simp [diagSeq]
    omega
  · intro i hiL hiR
    have hlenD : Lng (diagSeq (u + m) v) = v + 1 - (u + m) := by
      simp [diagSeq]
    by_cases hi : i < Lng (diagSeq (u + m) v)
    · rw [seg_getElem_68 _ m _ i hiL]
      have hmi : m + i < Lng (diagSeq u v) := by
        simp [diagSeq] at hi ⊢
        omega
      rw [entry_append_left_mr _ _ 0 _ hmi,
        entry_append_left_mr _ _ 1 _ hmi]
      rw [entry_diagSeq_68 u v 0 (m + i) hmi,
        entry_diagSeq_68 u v 1 (m + i) hmi]
      simp only [List.getElem_append_left hi]
      simp [diagSeq, List.getElem_map, List.getElem_range']
      omega
    · have hieq : i = Lng (diagSeq (u + m) v) := by
        simp [diagSeq] at hi hiR
        omega
      subst i
      rw [seg_getElem_68 _ m _ _ hiL]
      have hidx : m + Lng (diagSeq (u + m) v) = Lng (diagSeq u v) := by
        simp [diagSeq]
        omega
      rw [hidx]
      rw [entry_append_right_mr _ _ 0 _ (le_refl _),
        entry_append_right_mr _ _ 1 _ (le_refl _)]
      simp [entry]

/-! ## 極小基底の対角分解と三つの `Trans` 直接計算（Isabelle `hqx_*` 最下段） -/

/-- **極小基底の全データ**: 体制 `VE34Reg4 N`・BASE `VEj1p N = Lng N - 1`・極小基底
`Lng N = TrMax N + 2` の下で、対角幹分解 `N = diagSeq u v ++ [(wp, w)]`（case 3）から
`Trans N`・前置辞 `Trans`・終切片 `Trans`・最終 joint の行1値をすべて閉形式で返す。 -/
private theorem minbase_data_vb (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) (hmin : Lng N = TrMax N + 2) :
    ∃ u v wp w : ℕ,
      Trans N = Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero)
            (Dprin (wp - 1 : ℕ∞)
              (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) ∧
      Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1))
          = Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero) ∧
      Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))
          = Dprin (wp - 1 : ℕ∞)
              (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) ∧
      (entry N 1 ((Joints N).getD ((Br N).length - 1) 0) : ℕ∞) = (wp - 1 : ℕ∞) := by
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := reg
  have hM : TPS N := RTPS_TPS N hR
  have hNne : N ≠ [] := hM
  have heq : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
    simpa only [VEj1p] using hbase
  -- 基本境界
  have hL3 : 2 < Lng N := by omega
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have htrP : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL1 htrne
  have htrPeq : TrMax (Pred N) = Lng (Pred N) - 1 := by omega
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
  -- 対角幹
  let u := entry (Pred N) 1 0
  let v := u + (Lng (Pred N) - 1)
  have huv : u < v := by dsimp [v]; omega
  have hdiag : Pred N = diagSeq u v := by
    apply List.ext_getElem
    · change Lng (Pred N) = Lng (diagSeq u v)
      simp [diagSeq, v]
      omega
    · intro i hiP _hiD
      have hiL : i < Lng (Pred N) := hiP
      obtain ⟨he0, he1⟩ :=
        baseU_alltrunk_diag_entry (Pred N) i hpredR hmonoP htrPeq hiL
      have hPi : (Pred N)[i] = (entry (Pred N) 0 i, entry (Pred N) 1 i) := by
        simp [entry, List.getElem?_eq_getElem hiL]
      rw [hPi, he0, he1]
      simp [u, diagSeq, List.getElem_map, List.getElem_range']
  -- 末尾列
  let wp := (N.getLast hNne).1
  let w := (N.getLast hNne).2
  have hPredDrop : Pred N = N.dropLast := by
    simp [Pred, show ¬Lng N ≤ 1 by omega]
  have hshape : N = diagSeq u v ++ [(wp, w)] := by
    calc
      N = N.dropLast ++ [N.getLast hNne] :=
        (List.dropLast_append_getLast hNne).symm
      _ = Pred N ++ [(wp, w)] := by simp [← hPredDrop, wp, w]
      _ = diagSeq u v ++ [(wp, w)] := by rw [hdiag]
  -- 末尾列の行0親 = j₀'
  have hp : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hplt : parent N 0 (Lng N - 1) < Lng N - 1 :=
    parent_lt_of_hasParent N 0 (Lng N - 1) hp
  have hlastIdx : Lng N - 1 = Lng (diagSeq u v) := by rw [hshape]; simp
  have hpD : parent N 0 (Lng N - 1) < Lng (diagSeq u v) := by
    rw [← hlastIdx]; exact hplt
  have hepar : entry N 0 (parent N 0 (Lng N - 1)) =
      u + parent N 0 (Lng N - 1) := by
    calc
      entry N 0 (parent N 0 (Lng N - 1)) =
          entry (diagSeq u v ++ [(wp, w)]) 0 (parent N 0 (Lng N - 1)) :=
        congrArg (fun Q : PS => entry Q 0 (parent N 0 (Lng N - 1))) hshape
      _ = entry (diagSeq u v) 0 (parent N 0 (Lng N - 1)) :=
        entry_append_left_mr _ _ 0 _ hpD
      _ = u + parent N 0 (Lng N - 1) :=
        entry_diagSeq_68 u v 0 _ hpD
  have helast0 : entry N 0 (Lng N - 1) = wp := by
    rw [hshape]
    have hidx : Lng (diagSeq u v ++ [(wp, w)]) - 1 = Lng (diagSeq u v) := by simp
    rw [hidx, entry_append_right_mr _ _ 0 _ (le_refl _)]
    simp [entry]
  have helast1 : entry N 1 (Lng N - 1) = w := by
    rw [hshape]
    have hidx : Lng (diagSeq u v ++ [(wp, w)]) - 1 = Lng (diagSeq u v) := by simp
    rw [hidx, entry_append_right_mr _ _ 1 _ (le_refl _)]
    simp [entry]
  have hA : RedCondA N = true := (RTPS_condAB N hR).1
  have htop := RedCondA_apply N hA 0 (Lng N - 1) (by omega) (by omega) hp
  have htop2 : u + parent N 0 (Lng N - 1) + 1 = wp := by
    have h := htop; rw [hepar, helast0] at h; exact h
  have hparentFormula : parent N 0 (Lng N - 1) = wp - u - 1 := by omega
  have huwp : u < wp := by omega
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hjoint : (Joints N).getD ((Br N).length - 1) 0 =
      parent N 0 (Lng N - 1) := by
    have h := Joints_getD N ((Br N).length - 1) hJ
    rw [heq] at h; exact h
  have hjointP : (Joints N).getD ((Br N).length - 1) 0 = wp - u - 1 :=
    hjoint.trans hparentFormula
  -- case-3 の三境界
  have hvTr : v = u + TrMax N := by dsimp [v]; omega
  have hwlt : w < wp := by
    have hg := hguard
    simp only [VEj1p] at hg
    rw [heq, helast1, helast0] at hg
    exact hg
  have hwpgt : u + 1 < wp := by
    have h := hj0pos; rw [hjointP] at h; omega
  have hwpv : wp ≤ v := by
    have h := hj0lt; rw [hjointP] at h; omega
  -- 前置辞: seg N 0 (fnLS - 1) = diagSeq u v
  have hfn1 : (FirstNodes N).getD (LastStep N) 0 - 1 = Lng N - 2 := by
    obtain ⟨hb1, hb2⟩ := m1_bounds N hM hmono hBrne
    omega
  have hprefix_eq : seg N 0 (Lng N - 2) = diagSeq u v := by
    have h1 : N.take (Lng N - 1) = seg N 0 (Lng N - 2) := by
      have h := take_eq_seg N (Lng N - 1) (by omega) (by omega)
      rwa [show Lng N - 1 - 1 = Lng N - 2 from by omega] at h
    rw [← h1, ← Pred_eq_take N hL1, hdiag]
  -- 終切片: seg N j₀' (Lng N - 1) = diagSeq (wp-1) v ++ [(wp, w)]
  have hterm_eq : seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)
      = diagSeq (wp - 1) v ++ [(wp, w)] := by
    rw [hjointP, hshape, seg_diagApp_vb u v wp w (wp - u - 1) huv (by omega),
      show u + (wp - u - 1) = wp - 1 from by omega]
  -- 三つの Trans と最終 joint 行1値
  refine ⟨u, v, wp, w, ?_, ?_, ?_, ?_⟩
  · rw [hshape]
    exact (Pred_diagSeq_Trans u v wp w huv).2.2.1 ⟨hwpgt, hwpv, hwlt⟩
  · rw [hfn1, hprefix_eq]
    exact diagSeq_Trans u v huv
  · rw [hterm_eq]
    exact (Pred_diagSeq_Trans (wp - 1) v wp w (by omega)).2.2.2 ⟨by omega, hwlt⟩
  · have hent_nat : entry N 1 ((Joints N).getD ((Br N).length - 1) 0) = wp - 1 := by
      have hlenD : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
      rw [hjointP, hshape,
        entry_append_left_mr (diagSeq u v) [(wp, w)] 1 (wp - u - 1) (by rw [hlenD]; omega),
        entry_diagSeq_68 u v 1 (wp - u - 1) (by rw [hlenD]; omega)]
      omega
    rw [hent_nat]
    exact ENat.coe_sub wp 1

/-! ## 極小基底の VE3goal / VE4goal（直接計算） -/

/-- **VE3 極小基底脚**: 極小基底 `Lng N = TrMax N + 2` では成長成分 `VE3goal N` が成立。
`t₂ = D_w(0_B)`（＝終切片頭 − 前置辞頭）で存在を与える。 -/
theorem VE3_minbase_vb (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) (hmin : Lng N = TrMax N + 2) : VE3goal N := by
  obtain ⟨u, v, wp, w, _hN, hpre, hterm, _hent⟩ := minbase_data_vb N reg hbase hmin
  refine ⟨Dprin (w : ℕ∞) BZero, ?_, ?_⟩
  · rw [hterm, hpre, bpHeadT_Dprin_vb, bpHeadT_Dprin_vb]
  · simp [Dprin, BZero]

/-- **VE4 極小基底脚**: 極小基底 `Lng N = TrMax N + 2` では頭シフト成分 `VE4goal N` が成立。 -/
theorem VE4_minbase_vb (N : PS) (reg : VE34Reg4 N)
    (hbase : VEj1p N = Lng N - 1) (hmin : Lng N = TrMax N + 2) : VE4goal N := by
  obtain ⟨u, v, wp, w, hN, hpre, hterm, hent⟩ := minbase_data_vb N reg hbase hmin
  unfold VE4goal
  rw [hN, hpre, hterm, hent, bpHeadT_Dprin_vb, bpHeadT_Dprin_vb, bpHeadT_Dprin_vb]
  -- LHS/RHS now syntactically identical (coefficient `↑wp - 1` on both sides)

/-! ## 非極小基底（run 領域）残差と BASE 二残差の還元

極小基底 `Lng N = TrMax N + 2`（＝`j₁ - TrMax = 1`）を無条件討伐したので、`VE3Base`/`VE4Base`
は非極小基底 `TrMax N + 2 < Lng N`（Isabelle `bfx_` run-peel 対象）のみに絞られる。 -/

/-- **VE3 非極小基底残差**（Isabelle `bfx_*`/`hqx_*` run-peel、`TrMax N + 2 < Lng N`）。 -/
def VE3BaseDeep : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N → VE3goal N

/-- **VE4 非極小基底残差**（Isabelle `bfx_*`/`hqx_*` run-peel、`TrMax N + 2 < Lng N`）。 -/
def VE4BaseDeep : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N → VE4goal N

/-- `VE3Base`（`8.2-condIIIV-VE234`）を極小基底脚＋非極小基底残差 `VE3BaseDeep` から放出。 -/
theorem VE3Base_of_deep (h : VE3BaseDeep) : VE3Base := by
  intro N reg hbase
  rcases lt_or_eq_of_le (reg4_TrMax_le_vb N reg) with hlt | heq
  · exact h N reg hbase hlt
  · exact VE3_minbase_vb N reg hbase heq.symm

/-- `VE4Base`（`8.2-condIIIV-VE234`）を極小基底脚＋非極小基底残差 `VE4BaseDeep` から放出。 -/
theorem VE4Base_of_deep (h : VE4BaseDeep) : VE4Base := by
  intro N reg hbase
  rcases lt_or_eq_of_le (reg4_TrMax_le_vb N reg) with hlt | heq
  · exact h N reg hbase hlt
  · exact VE4_minbase_vb N reg hbase heq.symm

/-! ## キャップストーン: `condIIIVts` フィールドを run 領域二残差 modulo で供給

BASE 二残差 `{VE3Base, VE4Base}` を非極小基底（run 領域）二残差
`{VE3BaseDeep, VE4BaseDeep}` に置換し、`8.2-condIIIV-deep3` の四残差版
`condIIIVterminalSlice_of_deep2` に差し込む。 -/

/-- **run 領域四残差版キャップストーン**: `condIIIVts` フィールドを
`{VE3BaseDeep, VE3Step, VE4BaseDeep, VE4Step}` から供給する。 -/
theorem condIIIVterminalSlice_of_deepBase
    (hV3bd : VE3BaseDeep) (hV3s : VE3Step)
    (hV4bd : VE4BaseDeep) (hV4s : VE4Step) :
    CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_deep2
    (VE3Base_of_deep hV3bd) hV3s (VE4Base_of_deep hV4bd) hV4s

/-! ## 転記の数値検証（極小基底討伐の量化域が非空）

witness `M = (0,0)(1,1)(2,2)(2,0)`（`8.2-condIIIV-VE34-reg` の `witness_c24`）は `VE34Reg4` に
属し、最終枝の左端 `VEj1p = 3 = Lng - 1`（BASE）かつ `Lng = 4 = TrMax + 2 = 2 + 2`（極小基底）。 -/

#guard decide (VE34Reg4 [(0,0),(1,1),(2,2),(2,0)] ∧
  VEj1p [(0,0),(1,1),(2,2),(2,0)] = Lng [(0,0),(1,1),(2,2),(2,0)] - 1 ∧
  Lng [(0,0),(1,1),(2,2),(2,0)] = TrMax [(0,0),(1,1),(2,2),(2,0)] + 2) = true

#print axioms VE3_minbase_vb
#print axioms VE4_minbase_vb
#print axioms VE3Base_of_deep
#print axioms VE4Base_of_deep
#print axioms condIIIVterminalSlice_of_deepBase

end PSS
