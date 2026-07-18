import «8».«8.2-condV-VE-base»
import «8».«8.2-condV-rightmost-parent»
import «8».«8.2-subexpr-component-Pred»

/-!
# §8.2 値方程式 `VE` の BASE 脚（`Lng = TrMax + 2` 極小基底）

- 原文: `tmp/content.md` L3664 付近の補題（条件(V)下の終切片と `Trans` の関係）の
  省略された帰納法（BASE = 「`j₁ - TrMax(M) = 1`」）。原文 LaTeX 4922
  「…を `j₁ - TrMax(M)` に関する数学的帰納法で示す」の底。
- 訂正: なし（Isabelle 側で無条件に証明済みの補題の逐語移植）。
- Isabelle（`isabelle/layerB/pss_wip.thy`）:
  - `a0x_base_VE` (75701) → `a0x_base_VE_vb2`（本ファイルの公開主定理）。
    Isabelle は `a0x_base_VE = vbx_base_VE_modAdm0[OF reg base a0x_base_VE_Adm0]` で
    閉じる。本ファイルはその **modAdm0 の上位骨格**（`transJm1` 二分岐）を Lean 側で
    証明し、二つの genuinely-hard 枝を named Prop に隔離する。
  - `vbx_base_transJm1_zero_or_TrMax` (74440) → `transJm1_zero_or_TrMax_vb2`
    （Lean 側で **完全証明**。`Adm_adm`/`Adm_le`/`Joints_getD`/`FirstNodes_TrMax_Joints`/
    `VEReg_base_j1p_eq`/`adm_le_TrMax_cases` で閉じる）。
  - `adm_le_TrMax_cases` (isabelle/pss_mechanized.thy 32296) → `adm_le_TrMax_cases_vb2`
    （private 再証明。`8.2-subexpr-component-Pred` の `_ck` は private のため再掲）。
  - `vbx_base_VE_modAdm0` (74476) の骨格 = `a0x_base_VE_vb2` の証明本体。
- 露出する named Prop（green-modulo。各々が Isabelle の 1 補題に対応）:
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
- 状態: ⚠️ 部分（sorry 0、rc=0）。BASE 脚の**上位骨格は無条件**。
  `BaseMLtTrMax` は閉じ、残差は {`BaseVEAdm0`, `BaseVEStrict`} の2本。
  加えて strict/collapse の双方が使う基底ブリック `baseMint_holds` / `baseLeR_holds` /
  `basePredVE_holds` を無条件化済み。
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

/-! ## 露出する named Prop（BASE 脚の残差＝二つの hard 枝＋一つの幾何残差） -/

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
  have htrbase : TrMax N = Lng N - 2 := by omega
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

/-! ## BASE 脚（Isabelle `a0x_base_VE`, 75701 の modAdm0 骨格） -/

/-- Isabelle `a0x_base_VE` (wip 75701) の上位骨格。三つの named Prop 残差を消費し、
型は `VE_backpeel_TrMax` の BASE 仮定に一致する。

Isabelle `vbx_base_VE_modAdm0` (74476) と同じ二分岐：`transJm1 N = 0` なら
`BaseVEAdm0`、さもなくば二分岐（`transJm1_zero_or_TrMax_vb2`）より `transJm1 N = TrMax N`
となり、`BaseMLtTrMax`（`m < TrMax N`）から `m < transJm1 N` を得て `BaseVEStrict`。 -/
theorem a0x_base_VE_vb2 (m : ℕ)
    (hAdm0 : BaseVEAdm0 m) (hStrict : BaseVEStrict m) :
    ∀ N : PS, VEReg m N → Lng N = TrMax N + 2 → VEeq m N := by
  intro N hreg hbase
  rcases transJm1_zero_or_TrMax_vb2 m N hreg hbase with h0 | hT
  · exact hAdm0 N hreg hbase h0
  · have hmlt : m < TrMax N := baseMLtTrMax_holds m N hreg hbase
    have hstr : m < transJm1 N := by rw [hT]; exact hmlt
    exact hStrict N hreg hbase hstr

/-! ## 差し込み確認: `a0x_base_VE_vb2` が `VE_backpeel_TrMax` の BASE 枠に一致する。 -/

example (m : ℕ)
    (hAdm0 : BaseVEAdm0 m) (hStrict : BaseVEStrict m)
    (STEP : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N →
      VEReg m (Pred N) → VEeq m (Pred N) → VEeq m N)
    (RPERS : ∀ N : PS, VEReg m N → TrMax N + 2 < Lng N → VEReg m (Pred N))
    (M : PS) (hM : VEReg m M) : VEeq m M :=
  VE_backpeel_TrMax m (a0x_base_VE_vb2 m hAdm0 hStrict) STEP RPERS M hM

#print axioms baseMLtTrMax_holds
#print axioms baseMint_holds
#print axioms baseLeR_holds
#print axioms basePredVE_holds
#print axioms transJm1_zero_or_TrMax_vb2
#print axioms a0x_base_VE_vb2

end PSS
