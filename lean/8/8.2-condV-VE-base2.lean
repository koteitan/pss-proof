import «8».«8.2-condV-VE-base»
import «8».«8.2-condV-rightmost-parent»
import «8».«8.2-subexpr-component-Pred»
import «8».«8.1-Pred-diagSeq-Trans»

/-!
# §8.2 値方程式 `VE` の BASE 脚（`Lng = TrMax + 2` 極小基底）

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)下の終切片と `Trans` の関係）の
  省略された帰納法（BASE = 「`j₁ - TrMax(M) = 1`」）。原文 LaTeX 4922
  「…を `j₁ - TrMax(M)` に関する数学的帰納法で示す」の底。
- 訂正: なし（Isabelle 側で無条件に証明済みの補題の逐語移植）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）:
  - `a0x_base_VE` (75701) → `a0x_base_VE_vb2`（本ファイルの公開主定理）。
    Isabelle は `a0x_base_VE = vbx_base_VE_modAdm0[OF reg base a0x_base_VE_Adm0]` で
    閉じる。本ファイルはその `transJm1` 二分岐を Lean 側で証明し、
    両分岐も `Pred N` の対角列形と `Pred_diagSeq_Trans` の直接計算で閉じる。
  - `vbx_base_transJm1_zero_or_TrMax` (74440) → `transJm1_zero_or_TrMax_vb2`
    （Lean 側で **完全証明**。`Adm_adm`/`Adm_le`/`Joints_getD`/`FirstNodes_TrMax_Joints`/
    `VEReg_base_j1p_eq`/`adm_le_TrMax_cases` で閉じる）。
  - `adm_le_TrMax_cases` (isabelle/pss_mechanized.thy 32296) → `adm_le_TrMax_cases_vb2`
    （private 再証明。`8.2-subexpr-component-Pred` の `_ck` は private のため再掲）。
  - `vbx_base_VE_modAdm0` (74476) の骨格 = `a0x_base_VE_vb2` の証明本体。
- 中間 named Prop（各々が Isabelle の 1 補題に対応し、本ファイル内で無条件に閉じる）:
  - `BaseMLtTrMax`  = `bihx_base_m_lt_TrMax` (71267) を BASE 体制に特化（`m < TrMax N`）。
    第二枝に必要な `joint_row1_eq`/`branch_col0_val`/`det_imp_joint_lt_TrMax` は
    Wave C-1 で公開済みなので、本ファイルで無条件に閉じる。
  - `BaseVEAdm0`    = `a0x_base_VE_Adm0` (75453、240 行)。`transJm1 N = 0` の頭部崩壊枝。
  - `BaseVEStrict`  = `vbx_base_VE_strict` (74300、~110 行)。`m < transJm1 N` の狭域枝。
- 依存: `8.2-condV-VE-base`（`VEReg`/`VEj1p`/`VEeq`/`transJm1` 系/`VEReg_base_j1p_eq`/
  `VE_backpeel_TrMax`）、`8.2-condV-rightmost-parent`（上記3補題）。
- 方針: Isabelle `vbx_base_VE_modAdm0` と同じ二分岐。体制の下で
  `transJm1 N = Adm N (parent N 0 (Lng N - 1))` は許容かつ `≤ TrMax N` なので
  `adm_le_TrMax_cases` により `0` か `TrMax N`。前者は `BaseVEAdm0`、後者は
  `m < TrMax N`（`BaseMLtTrMax`）より `m < transJm1 N` を得て `BaseVEStrict`。
  得られる `a0x_base_VE_vb2 m …` は型がちょうど `VE_backpeel_TrMax` の BASE 仮定
  `∀ N, VEReg m N → Lng N = TrMax N + 2 → VEeq m N` に一致する（末尾 `example` で確認）。
- 状態: ✅ 完了（sorry 0、rc=0）。`BaseMLtTrMax` / `BaseVEAdm0` /
  `BaseVEStrict` と共通基底ブリック `baseMint_holds` / `baseLeR_holds` /
  `basePredVE_holds` をすべて無条件化。`a0x_base_VE_vb2` は残差引数 0 で
  `VE_backpeel_TrMax` の BASE 仮定を与える。
-/

namespace PSS

/-! ## private 再証明: `adm_le_TrMax_cases`（Isabelle pss_mechanized 32296） -/

/-- Isabelle `adm_trunk_interior_nadm` (wip 32280): 幹の内部添字 `0 < j < TrMax M` は
`M` 非許容。 -/
private theorem adm_trunk_interior_nadm_vb2 (M : PS) (j : ℕ) (hM : TPS M)
    (hjpos : 0 < j) (hjlt : j < TrMax M) : adm M j = false := by
  have hs1 : nextR M 1 (j - 1) (j - 1 + 1) = true :=
    TrMax_trunk_step M (j - 1) hM (by omega)
  have hkeq : j - 1 + 1 = j := by omega
  rw [hkeq] at hs1
  have hs2 : nextR M 1 j (j + 1) = true := TrMax_trunk_step M j hM hjlt
  simp [adm, nadm, hs1, hs2]

/-- Isabelle `adm_le_TrMax_cases` (wip 32296): `TrMax M` 以下の `M` 許容な添字は
`0` か `TrMax M` のみ。 -/
private theorem adm_le_TrMax_cases_vb2 (M : PS) (j : ℕ) (hM : TPS M)
    (ha : adm M j = true) (hjle : j ≤ TrMax M) : j = 0 ∨ j = TrMax M := by
  by_contra hnot
  have hj0 : j ≠ 0 := fun h => hnot (Or.inl h)
  have hjT : j ≠ TrMax M := fun h => hnot (Or.inr h)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjlt : j < TrMax M := lt_of_le_of_ne hjle hjT
  have hbad := adm_trunk_interior_nadm_vb2 M j hM hjpos hjlt
  rw [hbad] at ha
  exact Bool.false_ne_true ha

/-! ## `transJm1` の BASE 二分岐（Isabelle `vbx_base_transJm1_zero_or_TrMax`, 74440） -/

/-- Isabelle `vbx_base_transJm1_zero_or_TrMax` (wip 74440): 極小基底 `Lng N = TrMax N + 2`
の体制下では `transJm1 N` は `0` か `TrMax N`。

`transJm1 N = Adm N (parent N 0 (Lng N - 1))` は `Adm` の定義より許容
（`Adm_adm`）で、`Adm_le` により `≤ parent N 0 (Lng N - 1)`。基底では最終枝の左端は
最終列（`VEReg_base_j1p_eq`）なので `parent N 0 (Lng N - 1) = Joints N ! (Br 末) ≤ TrMax N`
（`Joints_getD` + `FirstNodes_TrMax_Joints`）。あとは `adm_le_TrMax_cases`。 -/
private theorem transJm1_zero_or_TrMax_vb2 (m : ℕ) (N : PS)
    (hreg : VEReg m N) (hbase : Lng N = TrMax N + 2) :
    transJm1 N = 0 ∨ transJm1 N = TrMax N := by
  have heq : VEj1p N = Lng N - 1 := VEReg_base_j1p_eq m N hreg hbase
  unfold VEj1p at heq
  obtain ⟨hR, hmono, hBrne, _⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  -- `parent N 0 (Lng N - 1) ≤ TrMax N`
  have hjoint : (Joints N).getD ((Br N).length - 1) 0
      = parent N 0 ((FirstNodes N).getD ((Br N).length - 1) 0) := Joints_getD N _ hJ
  have hgeom : (Joints N).getD ((Br N).length - 1) 0 ≤ TrMax N :=
    (FirstNodes_TrMax_Joints N _ hM hmono hJ).1
  rw [heq] at hjoint
  have hjpTr : parent N 0 (Lng N - 1) ≤ TrMax N := by
    rw [← hjoint]; exact hgeom
  -- `transJ0 N = parent N 0 (Lng N - 1)`
  have hj0 : transJ0 N = parent N 0 (Lng N - 1) := by
    simp [transJ0, lastParent, lastIdx]
  -- 許容性と `≤ TrMax N`
  have hadmJ : adm N (transJm1 N) = true := by
    unfold transJm1; exact Adm_adm N (transJ0 N)
  have hleJ : transJm1 N ≤ TrMax N := by
    have h1 : transJm1 N ≤ transJ0 N := by
      unfold transJm1; exact Adm_le N (transJ0 N)
    rw [hj0] at h1; omega
  exact adm_le_TrMax_cases_vb2 N (transJm1 N) hM hadmJ hleJ

/-! ## BASE 脚の中間 named Prop（以下ですべて無条件に閉じる） -/

/-- Isabelle `bihx_base_m_lt_TrMax` (wip 71267) を BASE 体制に特化。
第二枝 `m = Joints ∧ descending` は未移植の `m_8_2_*` 連鎖を要する。 -/
def BaseMLtTrMax (m : ℕ) : Prop :=
  ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → m < TrMax N

/-- Isabelle `a0x_base_VE_Adm0` (wip 75453、240 行): `transJm1 N = 0` の頭部崩壊枝。 -/
def BaseVEAdm0 (m : ℕ) : Prop :=
  ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → transJm1 N = 0 → VEeq m N

/-- Isabelle `vbx_base_VE_strict` (wip 74300、~110 行): `m < transJm1 N` の狭域枝。 -/
def BaseVEStrict (m : ℕ) : Prop :=
  ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → m < transJm1 N → VEeq m N

/-! ## BASE regime の幾何残差を無条件に閉じる -/

/-- Isabelle `bihx_base_m_lt_TrMax` (wip 71267)。`VEReg` の左分岐は
`m < Joints(last) ≤ TrMax`。右分岐は公開済みの joint/branch 読み出しから
行1値の狭義増加を作り、`det_imp_joint_lt_TrMax` で strictness を得る。 -/
theorem baseMLtTrMax_holds (m : ℕ) : BaseMLtTrMax m := by
  intro N hreg _hbase
  obtain ⟨hR, hmono, hBrne, hcases⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br N).length - 1 < (Br N).length := by omega
  have hgeom : (Joints N).getD ((Br N).length - 1) 0 ≤ TrMax N :=
    (FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ).1
  rcases hcases with hlt | ⟨hmeq, hdiag, hdesc⟩
  · omega
  · have hD : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
    simp only [VEj1p] at hdiag
    have he1j := joint_row1_eq N ((Br N).length - 1) hD hJ
    have he0f := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ
    have hc0 := branch_col0_val N ((Br N).length - 1) hD hJ
    have hdet : entry N 1 ((Joints N).getD ((Br N).length - 1) 0) <
        entry N 1 ((FirstNodes N).getD ((Br N).length - 1) 0) := by
      omega
    have hjlt := det_imp_joint_lt_TrMax N hD hBrne hdet
    omega

/-! ## BASE 専用ブリック（Isabelle `bihx_base_*` / `vbax_base_baseIH`） -/

/-- Isabelle `bihx_base_mint` (wip 71334)。極小基底では `m < TrMax N = Lng N - 2`。 -/
theorem baseMint_holds (m : ℕ) (N : PS) (hreg : VEReg m N)
    (hbase : Lng N = TrMax N + 2) : m < Lng N - 2 := by
  have hm := baseMLtTrMax_holds m N hreg hbase
  omega

/-- Isabelle `bihx_base_lerB` (wip 71358)。体制の最終 joint 境界から終切片を
単項化し、その左端が最終列の行0祖先であることを読み戻す。 -/
theorem baseLeR_holds (m : ℕ) (N : PS) (hreg : VEReg m N)
    (hbase : Lng N = TrMax N + 2) : leR N 0 m (Lng N - 1) = true := by
  obtain ⟨hR, hmono, hBrne, hcases⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hmint : m < Lng N - 2 :=
    baseMint_holds m N ⟨hR, hmono, hBrne, hcases⟩ hbase
  have hmj : m ≤ (Joints N).getD ((Br N).length - 1) 0 := by
    rcases hcases with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact heq.le
  have hmonoS : monoT (seg N m (Lng N - 1)) = true :=
    mono_slice N m (Lng N - 1) hM hmono (by omega) (le_refl _) hmj
  have hle0 : le0 N m (Lng N - 1) = true :=
    le0_monoT_seg_into_list N m (Lng N - 1) (Lng N - 1) hM hmonoS
      (by omega) (le_refl _) (by omega)
  simpa [leR] using hle0

/-- Isabelle `vbax_base_baseIH` (wip 71891)。真の極小基底では `Pred N` の幹が
右端まで伸び、簡約単項性から対角列になる。対角列とその終切片の `Trans` は
それぞれ `D_u(D_b 0)` / `D_(u+m)(D_b 0)` なので深部 head が一致する。 -/
theorem basePredVE_holds (m : ℕ) (N : PS) (hreg : VEReg m N)
    (hbase : Lng N = TrMax N + 2) : VEeq m (Pred N) := by
  obtain ⟨hR, hmono, hBrne, hcases⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hmint : m < Lng N - 2 :=
    baseMint_holds m N ⟨hR, hmono, hBrne, hcases⟩ hbase
  have hL3 : 2 < Lng N := by omega
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have hLP2 : 1 < Lng (Pred N) := by omega
  have htrP : TrMax (Pred N) = TrMax N :=
    TrMax_Pred_nontrunk N hM hL1 htrne
  have htrPeq : TrMax (Pred N) = Lng (Pred N) - 1 := by omega
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
  let u := entry (Pred N) 1 0
  let b := u + (Lng (Pred N) - 1)
  have hub : u < b := by dsimp [b]; omega
  have hdiag : Pred N = diagSeq u b := by
    apply List.ext_getElem
    · change Lng (Pred N) = Lng (diagSeq u b)
      simp [diagSeq, b]
      omega
    · intro i hiP _hiD
      have hiL : i < Lng (Pred N) := hiP
      obtain ⟨he0, he1⟩ :=
        baseU_alltrunk_diag_entry (Pred N) i hpredR hmonoP htrPeq hiL
      have hPi : (Pred N)[i] = (entry (Pred N) 0 i, entry (Pred N) 1 i) := by
        simp [entry, List.getElem?_eq_getElem hiL]
      rw [hPi, he0, he1]
      simp [u, diagSeq, List.getElem_map, List.getElem_range']
  have htPred : Trans (Pred N) = Dprin (u : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
    rw [hdiag]
    exact diagSeq_Trans u b hub
  have hmle : m ≤ b - u := by dsimp [b]; omega
  have hseg : seg (Pred N) m (Lng (Pred N) - 1) = diagSeq (u + m) b := by
    have hend : Lng (Pred N) - 1 = b - u := by dsimp [b]; omega
    rw [hend, hdiag]
    calc
      seg (diagSeq u b) m (b - u) = diagSeq (u + m) (u + (b - u)) :=
        seg_diagSeq_68 u b m (b - u) hmle (le_refl _) hub.le
      _ = diagSeq (u + m) b := by rw [Nat.add_sub_of_le hub.le]
  have humb : u + m < b := by dsimp [b] at hub ⊢; omega
  have htSeg : Trans (seg (Pred N) m (Lng (Pred N) - 1)) =
      Dprin ((u + m : ℕ) : ℕ∞) (Dprin (b : ℕ∞) BZero) := by
    rw [hseg]
    exact diagSeq_Trans (u + m) b humb
  unfold VEeq
  rw [htSeg, htPred]
  rfl

/-! ## strict BASE: 対角幹＋末尾列の直接計算 -/

/-- 対角幹に末尾列を付けた列の終切片は、対角幹の左端だけを `m` だけ進める。 -/
private theorem seg_diagApp_vb2 (u v wp w m : ℕ) (huv : u < v)
    (hm : m < v - u) :
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

/-- Isabelle `vbx_base_VE_strict`。極小基底の `Pred N` は対角列であり、
`m < transJm1 N` は末尾列の行0親が対角幹の右端であることを強制する。
したがって `N` とその終切片は同じ末尾二段塔を持ち、外側の指標だけが
`u` から `u+m` へ変わるので `bpHeadT` は一致する。 -/
theorem baseVEStrict_holds (m : ℕ) : BaseVEStrict m := by
  intro N hreg hbase hstr
  obtain ⟨hR, hmono, hBrne, hcases⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hNne : N ≠ [] := hM
  by_cases hm0 : m = 0
  · subst m
    exact VE_index0 N hNne
  have hmint : m < Lng N - 2 :=
    baseMint_holds m N ⟨hR, hmono, hBrne, hcases⟩ hbase
  have hL3 : 2 < Lng N := by omega
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have htrP : TrMax (Pred N) = TrMax N :=
    TrMax_Pred_nontrunk N hM hL1 htrne
  have htrPeq : TrMax (Pred N) = Lng (Pred N) - 1 := by omega
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
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
  have hp : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hJ0lt : transJ0 N < Lng N - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent N 0 (Lng N - 1) hp
  have hJ0ltD := hJ0lt
  rw [hshape] at hJ0ltD
  have hbound : transJ0 (diagSeq u v ++ [(wp, w)]) ≤ v - u := by
    have hlenApp : Lng (diagSeq u v ++ [(wp, w)]) = v - u + 2 := by
      simp [diagSeq]
      omega
    rw [hlenApp] at hJ0ltD
    omega
  have hposN : 0 < transJm1 N := by omega
  have hposD : 0 < transJm1 (diagSeq u v ++ [(wp, w)]) := by
    simpa only [hshape] using hposN
  have hj0D : transJ0 (diagSeq u v ++ [(wp, w)]) = v - u :=
    diagApp_transJm1_pos_forces_parent_rightmost u v wp w huv hbound hposD
  have hj0N : transJ0 N = v - u := by
    rw [hshape]
    exact hj0D
  have hparent : parent N 0 (Lng N - 1) = v - u := by
    simpa [transJ0, lastParent, lastIdx] using hj0N
  have hparD : v - u < Lng (diagSeq u v) := by
    simp [diagSeq]
    omega
  have hepar : entry N 0 (parent N 0 (Lng N - 1)) = v := by
    rw [hparent, hshape, entry_append_left_mr _ _ 0 _ hparD,
      entry_diagSeq_68 u v 0 (v - u) hparD]
    omega
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
  have hwp : wp = v + 1 := by rw [hepar, helast0] at htop; omega
  have hwle : w ≤ wp := by
    have hc := reduced_coeff N hR (Lng N - 1) (by omega)
    rwa [helast1, helast0] at hc
  have hwv : w ≤ v := by
    have hwle' : w ≤ v + 1 := by omega
    by_contra hnot
    have hw : w = v + 1 := by omega
    have hdiagN : N = diagSeq u (v + 1) := by
      rw [hshape, hwp, hw, diagSeq_succ_eq_append u v huv.le]
    have hbrzero : Br N = [] := by
      rw [hdiagN]
      exact Br_diagSeq_68 u (v + 1) (by omega)
    exact hBrne hbrzero
  have hmvu : m < v - u := by
    have hadmle : transJm1 N ≤ transJ0 N := by
      unfold transJm1
      exact Adm_le N (transJ0 N)
    rw [hj0N] at hadmle
    omega
  have hslice :
      seg N m (Lng N - 1) = diagSeq (u + m) v ++ [(v + 1, w)] := by
    rw [hshape, hwp]
    exact seg_diagApp_vb2 u v (v + 1) w m huv hmvu
  have htN : Trans N =
      Dprin (u : ℕ∞) (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero)) := by
    rw [hshape, hwp]
    exact diagApp_last_Trans u v w huv hwv
  have htS : Trans (seg N m (Lng N - 1)) =
      Dprin (u + m : ℕ∞) (Dprin (v : ℕ∞) (Dprin (w : ℕ∞) BZero)) := by
    rw [hslice]
    exact diagApp_last_Trans (u + m) v w (by omega) hwv
  unfold VEeq
  rw [htS, htN]
  rfl

/-- Isabelle `a0x_base_VE_Adm0`。`transJm1 N = 0` の極小基底も、対角幹に
付く末尾列の位置で場合分けして直接計算できる。行1値が行0値と等しい枝では
case 2、狭義に小さい枝では付着位置により case 3/4 となる。`VEReg` の
`m ≤ Joints(last)` は切片後も同じ case に留まるために必要な境界を与える。 -/
theorem baseVEAdm0_holds (m : ℕ) : BaseVEAdm0 m := by
  intro N hreg hbase hAdm0
  have heq : VEj1p N = Lng N - 1 := VEReg_base_j1p_eq m N hreg hbase
  unfold VEj1p at heq
  obtain ⟨hR, hmono, hBrne, hcases⟩ := hreg
  have hM : TPS N := RTPS_TPS N hR
  have hNne : N ≠ [] := hM
  by_cases hm0 : m = 0
  · subst m
    exact VE_index0 N hNne
  have hmint : m < Lng N - 2 :=
    baseMint_holds m N ⟨hR, hmono, hBrne, hcases⟩ hbase
  have hL3 : 2 < Lng N := by omega
  have hL1 : 1 < Lng N := by omega
  have htrne : TrMax N ≠ Lng N - 1 := by omega
  have hpredR : RTPS (Pred N) := RTPS_Pred N hR
  have hLP : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  have htrP : TrMax (Pred N) = TrMax N :=
    TrMax_Pred_nontrunk N hM hL1 htrne
  have htrPeq : TrMax (Pred N) = Lng (Pred N) - 1 := by omega
  have hmonoP : monoT (Pred N) = true := monoT_Pred_long N hM hmono hL3
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
  have hp : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hplt : parent N 0 (Lng N - 1) < Lng N - 1 :=
    parent_lt_of_hasParent N 0 (Lng N - 1) hp
  have hlastIdx : Lng N - 1 = Lng (diagSeq u v) := by
    rw [hshape]
    simp
  have hpD : parent N 0 (Lng N - 1) < Lng (diagSeq u v) := by
    rw [← hlastIdx]
    exact hplt
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
  have hparentFormula : parent N 0 (Lng N - 1) = wp - u - 1 := by
    rw [hepar, helast0] at htop
    omega
  have huwp : u < wp := by
    rw [hepar, helast0] at htop
    omega
  have hpBound : parent N 0 (Lng N - 1) ≤ v - u := by
    have hlenD : Lng (diagSeq u v) = v + 1 - u := by simp [diagSeq]
    rw [hlenD] at hpD
    omega
  have hwpBound : wp ≤ v + 1 := by
    rw [hepar, helast0] at htop
    omega
  have hj0N : transJ0 N = wp - u - 1 := by
    simpa [transJ0, lastParent, lastIdx] using hparentFormula
  have hJ : (Br N).length - 1 < (Br N).length := by
    cases hb : Br N with
    | nil => exact absurd hb hBrne
    | cons a t => simp
  have hjoint : (Joints N).getD ((Br N).length - 1) 0 =
      parent N 0 (Lng N - 1) := by
    have h := Joints_getD N ((Br N).length - 1) hJ
    rw [heq] at h
    exact h
  have hjointP : (Joints N).getD ((Br N).length - 1) 0 = wp - u - 1 :=
    hjoint.trans hparentFormula
  have hmleP : m ≤ wp - u - 1 := by
    have hmle : m ≤ (Joints N).getD ((Br N).length - 1) 0 := by
      rcases hcases with hlt | ⟨hme, _⟩
      · exact hlt.le
      · exact hme.le
    rwa [hjointP] at hmle
  have hwle : w ≤ wp := by
    have hc := reduced_coeff N hR (Lng N - 1) (by omega)
    rwa [helast1, helast0] at hc
  have right_w_le (hwpLast : wp = v + 1) : w ≤ v := by
    by_contra hnot
    have hw : w = v + 1 := by omega
    have hdiagN : N = diagSeq u (v + 1) := by
      rw [hshape, hwpLast, hw, diagSeq_succ_eq_append u v huv.le]
    have hbrzero : Br N = [] := by
      rw [hdiagN]
      exact Br_diagSeq_68 u (v + 1) (by omega)
    exact hBrne hbrzero
  have hwpv : wp ≤ v := by
    by_contra hnot
    have hwpLast : wp = v + 1 := by omega
    have hwv : w ≤ v := right_w_le hwpLast
    have hjm : transJm1 N = v - u := by
      rw [hshape, hwpLast]
      exact diagApp_last_transJm1 u v w huv hwv
    rw [hAdm0] at hjm
    omega
  have hmvu : m < v - u := by omega
  have hslice :
      seg N m (Lng N - 1) = diagSeq (u + m) v ++ [(wp, w)] := by
    rw [hshape]
    exact seg_diagApp_vb2 u v wp w m huv hmvu
  by_cases hweq : w = wp
  · have humwp : u + m < wp := by omega
    have htN : Trans N = Dprin (u : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) := by
      rw [hshape]
      exact (Pred_diagSeq_Trans u v wp w huv).2.1 ⟨huwp, hwpv, hweq⟩
    have htS : Trans (seg N m (Lng N - 1)) = Dprin (u + m : ℕ∞)
        (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)) := by
      rw [hslice]
      exact (Pred_diagSeq_Trans (u + m) v wp w (by omega)).2.1
        ⟨humwp, hwpv, hweq⟩
    unfold VEeq
    rw [htS, htN]
    rfl
  · have hwwp : w < wp := by omega
    by_cases hfirst : wp = u + 1
    · have hmzero : m = 0 := by omega
      subst m
      exact VE_index0 N hNne
    · have hgap : u + 1 < wp := by omega
      have hmltP : m < wp - u - 1 := by
        rcases hcases with hlt | ⟨_hme, hdiagLast, _hdesc⟩
        · rwa [hjointP] at hlt
        · change entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0) =
            entry N 1 ((FirstNodes N).getD ((Br N).length - 1) 0) at hdiagLast
          rw [heq, helast0, helast1] at hdiagLast
          exact absurd hdiagLast.symm hweq
      have hgapS : u + m + 1 < wp := by omega
      have htN : Trans N = Dprin (u : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero)
            (Dprin (wp - 1 : ℕ∞)
              (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) := by
        rw [hshape]
        exact (Pred_diagSeq_Trans u v wp w huv).2.2.1
          ⟨hgap, hwpv, hwwp⟩
      have htS : Trans (seg N m (Lng N - 1)) = Dprin (u + m : ℕ∞)
          (addBT (Dprin (v : ℕ∞) BZero)
            (Dprin (wp - 1 : ℕ∞)
              (addBT (Dprin (v : ℕ∞) BZero) (Dprin (w : ℕ∞) BZero)))) := by
        rw [hslice]
        exact (Pred_diagSeq_Trans (u + m) v wp w (by omega)).2.2.1
          ⟨hgapS, hwpv, hwwp⟩
      unfold VEeq
      rw [htS, htN]
      rfl

/-! ## BASE 脚（Isabelle `a0x_base_VE`, 75701） -/

/-- Isabelle `a0x_base_VE` (wip 75701)。三つの無条件補題を組み立て、
型は `VE_backpeel_TrMax` の BASE 仮定に一致する。

Isabelle `vbx_base_VE_modAdm0` (74476) と同じ二分岐：`transJm1 N = 0` なら
`BaseVEAdm0`、さもなくば二分岐（`transJm1_zero_or_TrMax_vb2`）より `transJm1 N = TrMax N`
となり、`BaseMLtTrMax`（`m < TrMax N`）から `m < transJm1 N` を得て `BaseVEStrict`。 -/
theorem a0x_base_VE_vb2 (m : ℕ) :
    ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → VEeq m N := by
  intro N hreg hbase
  rcases transJm1_zero_or_TrMax_vb2 m N hreg hbase with h0 | hT
  · exact baseVEAdm0_holds m N hreg hbase h0
  · have hmlt : m < TrMax N := baseMLtTrMax_holds m N hreg hbase
    have hstr : m < transJm1 N := by rw [hT]; exact hmlt
    exact baseVEStrict_holds m N hreg hbase hstr

/-! ## 差し込み確認: `a0x_base_VE_vb2` が `VE_backpeel_TrMax` の BASE 枠に一致する。 -/

example (m : ℕ)
    (STEP : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N →
      VEReg m (Pred N) → VEeq m (Pred N) → VEeq m N)
    (RPERS : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N → VEReg m (Pred N))
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  VE_backpeel_TrMax m (a0x_base_VE_vb2 m) STEP RPERS M hM

#print axioms baseMLtTrMax_holds
#print axioms baseMint_holds
#print axioms baseLeR_holds
#print axioms basePredVE_holds
#print axioms baseVEStrict_holds
#print axioms baseVEAdm0_holds
#print axioms transJm1_zero_or_TrMax_vb2
#print axioms a0x_base_VE_vb2

end PSS
