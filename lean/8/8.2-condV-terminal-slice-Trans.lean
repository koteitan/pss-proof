import «8».«8.2-condV-rightmost-parent»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «7».«7.3-Trans-IncrFirst-Red»
import «7».«7.4-RightNodes-Mark»

/-!
# §8.2 補題（条件(V)の下での終切片と `Trans` の関係）

- 原文: `tmp/content.md` L3664 付近（補題本体 L3664–L3672、証明 L3674–）
- 訂正: なし（本補題の主張自体には訂正なし）。ただし原文の証明は
  「`Trans` が単項性を保つ」を無条件に使うが、これは訂正 A16 により偽
  （先頭 `P` 成分が零項のとき反例。`Trans_monoT_original_counterexample`,
  lean/7/7.3-Trans-preserves-monoT.lean:201）。本ファイルは A16 を回避し、
  `RTPS ∧ monoT` の下でのみ成立する正しい形
  （`Trans_monoT_principal` / `Trans_mono_leftend_form`）を使う。
- Isabelle:
  - 逐語: `p_8_2_condV_terminal_slice_Trans` (isabelle/pss_paper.thy:1607)
  - 本体: `m_8_2_condV_terminal_slice_Trans` (isabelle/layerB/pss_wip.thy:77102)
    ＝ `m_8_2_condV_terminal_slice_Trans_modVE` (同 61039) ＋ `vcx_VE_all` (同 77076)
  - 本ファイルが移植したのは前者 `_modVE` の連鎖:
    - `e2x_Trans_principal_head` (同 60990) → `Trans_principal_head`
    - `e2x_terminal_slice_scaffold` (同 61011) → `terminal_slice_Trans_scaffold`
    - `m_6_4_mono_slice` / `le0_monoT_seg_into_list` / `slice_Red_in_RT_PS` /
      `m_7_3_Trans_Red` / `repr_entry1_shift_gen` / `m_6_5_Red_preserves_monoT`
      → 下記 `condV_terminal_slice_principal` に集約
  - 未移植: `vcx_VE_all`（値方程式 `VE`
    `bpHeadT (Trans (seg M m (Lng M - 1))) = bpHeadT (Trans M)`）。
    Isabelle 側では `cfbx_VE_backpeel` (63230) に始まり `a0x_*`/`vjx_*`/`vsx_*`/
    `vbax_*`/`vcx_*` の約 14000 行・271 補題の back-peel 帰納法。単一ファイルの
    射程外のため、本ファイルは `VE` を仮定に持つ `_modVE` 形までを緑で提供する。
- 依存: `8.2-condV-rightmost-parent`（`le0_monoT_seg_into_list`）、
  `6.4-mono-slice`（`mono_slice`）、`6.4-FirstNodes-TrMax-Joints`
  （`FirstNodes_TrMax_Joints`/`TrMax_bound`）、`6.2-mono-ancestor-slice`
  （`entry_seg`/`length_seg`）、`6.6-ancestor-slice-Red-IncrFirst`
  （`ancestor_slice_Red_IncrFirst` ＝ `slice_Red_in_RT_PS` ＋ `Red_preserves_monoT`
  ＋ `repr` を一括提供）、`7.3-Trans-IncrFirst-Red`（`Trans_Red`）、
  `7.3-Trans-preserves-zeroT`（`Trans_preserves_zeroT`）、
  `7.4-RightNodes-Mark`（`Trans_mono_leftend_form`）
- 方針: Isabelle と同じ骨格。`Trans` の principal 表示（左端 `M₁,₀`）は
  `Trans_mono_leftend_form` ＋ 非零性、切片側は `Red` して `RTPS` に落とし
  （`ancestor_slice_Red_IncrFirst`）、`Trans (seg …) = Trans (Red (seg …))` と
  `entry (Red (seg M m j₁)) 1 0 = M₁,ₘ`（`IncrFirstN` は行 1 を動かさない）で
  頭指標を `M₁,ₘ` に読み替える。`VE` が両者の深部末尾を同定する。
- 状態: ⚠️ 部分（sorry 0、rc=0）。公開定理はすべて無条件または `VE` 仮定付き。
  原文の主張そのもの（`VE` 込み）は `vcx_VE_all` の移植待ち。
-/

namespace PSS

/-! ## 私的補助（suffix `_cts`） -/

/-- `Dprin` の内部項は `bpHeadT` で読み出せる。 -/
private theorem bpHeadT_Dprin_cts (v : ℕ∞) (a : BT) :
    bpHeadT (Dprin v a) = a := rfl

/-- `Dprin` は第 2 引数について単射（第 1 引数固定）。 -/
private theorem Dprin_inj_cts {v : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin v b) : a = b := by
  have := congrArg bpHeadT h
  simpa [bpHeadT_Dprin_cts] using this

/-- 単項なら非零。 -/
private theorem zeroT_false_of_monoT_cts (M : PS) (hmono : monoT M = true) :
    zeroT M = false := by
  simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at hmono
  exact hmono.1

/-- 簡約かつ単項な `M` の `Trans` は非零（Isabelle `m_7_3_Trans_zeroT` 経由の
`tne`）。 -/
private theorem Trans_ne_BZero_cts (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) : Trans M ≠ BZero := by
  intro ht
  have hM : TPS M := RTPS_TPS M hR
  have hz : zeroT M = true := (Trans_preserves_zeroT M hM).2 ht
  rw [zeroT_false_of_monoT_cts M hmono] at hz
  exact Bool.noConfusion hz

/-- `IncrFirstN` は行 1 の entry を動かさない（Isabelle `repr_entry1_shift_gen`
の核）。 -/
private theorem entry_IncrFirstN_one_cts (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) : entry (IncrFirstN n M) 1 j = entry M 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

/-! ## 公開補助 1: `Trans` の principal 表示（無条件） -/

/-- Isabelle `e2x_Trans_principal_head` (layerB 60990):
簡約かつ単項な `M` について `Trans M` は principal であり、その頭指標は
左端の行 1 の値 `M₁,₀` である：`Trans M = D_{M₁,₀} (bpHeadT (Trans M))`。

（原文の「`Trans` が単項性を保つ」＝訂正 A16 で偽 の、正しい `RTPS` 版。） -/
theorem Trans_principal_head (M : PS) (hR : RTPS M) (hmono : monoT M = true) :
    Trans M = Dprin (entry M 1 0 : ℕ∞) (bpHeadT (Trans M)) := by
  rcases Trans_mono_leftend_form M hR hmono with hz | ⟨t, ht⟩
  · exact absurd hz (Trans_ne_BZero_cts M hR hmono)
  · rw [ht, bpHeadT_Dprin_cts]

/-! ## 公開補助 2: 一意存在の足場（無条件） -/

/-- Isabelle `e2x_terminal_slice_scaffold` (layerB 61011):
`Trans M` と `Trans M'` がそれぞれ頭指標 `M₁,₀` / `M₁,ₘ` の principal 項であり、
かつ深部末尾（`bpHeadT`）が一致するなら、共通の `t₁` が一意に存在する。 -/
theorem terminal_slice_Trans_scaffold (M M' : PS) (m : ℕ)
    (princM : Trans M = Dprin (entry M 1 0 : ℕ∞) (bpHeadT (Trans M)))
    (princM' : Trans M' = Dprin (entry M 1 m : ℕ∞) (bpHeadT (Trans M')))
    (hVE : bpHeadT (Trans M') = bpHeadT (Trans M)) :
    ∃! t₁ : BT, Trans M = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans M' = Dprin (entry M 1 m : ℕ∞) t₁ := by
  refine ⟨bpHeadT (Trans M), ⟨princM, ?_⟩, ?_⟩
  · rw [← hVE]; exact princM'
  · rintro t ⟨ht, -⟩
    exact (Dprin_inj_cts (princM.symm.trans ht)).symm

/-! ## 条件(V)の体制（原文の仮定） -/

/-- 原文の仮定「`m < j'₀`」または「`m = j'₀` かつ `M₀,ⱼ'₁ = M₁,ⱼ'₁` かつ
`Br M` が降順」。`J₁ = Lng (Br M) - 1`, `j'₀ = Joints(M)_{J₁}`,
`j'₁ = FirstNodes(M)_{J₁}`（Isabelle `cfbx_reg`, layerB 63208）。

公開定理では逐語性のため展開形を直接書く（本 `def` は補助専用）。 -/
private def condVReg (M : PS) (m : ℕ) : Prop :=
  m < (Joints M).getD ((Br M).length - 1) 0 ∨
    (m = (Joints M).getD ((Br M).length - 1) 0 ∧
      entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
        = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
      descendingB (Br M) = true)

/-! ## 幾何: `m ≤ j'₀ ≤ TrMax M < Lng M - 1` -/

/-- 体制の下で `m ≤ j'₀`。 -/
private theorem m_le_j0'_cts (M : PS) (m : ℕ) (hreg : condVReg M m) :
    m ≤ (Joints M).getD ((Br M).length - 1) 0 := by
  rcases hreg with h | ⟨h, -, -⟩
  · exact h.le
  · exact h.le

/-- `Br M ≠ []` なら幹の右端は右端列より真に左（`Br` の定義から）。 -/
private theorem TrMax_lt_last_cts (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    TrMax M < Lng M - 1 := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have := TrMax_bound M hM
  omega

/-- 体制の下で `m < Lng M - 1`（Isabelle `mj1`）。 -/
private theorem m_lt_j1_cts (M : PS) (m : ℕ) (hR : RTPS M)
    (hmono : monoT M = true) (hBrne : Br M ≠ []) (hreg : condVReg M m) :
    m < Lng M - 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have hJ1 : (Br M).length - 1 < (Br M).length := by
    have : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
    omega
  have hgeom := FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ1
  have hm := m_le_j0'_cts M m hreg
  have := TrMax_lt_last_cts M hM hBrne
  omega

/-! ## 切片の principal 表示 -/

/-- Isabelle `m_8_2_condV_terminal_slice_Trans_modVE` (layerB 61039) の前半
（`VE` を使わない部分）を単独の公開定理として：条件(V)の体制の下で、終切片
`M' = (M_j)_{j=m}^{j₁}` の `Trans` は頭指標 `M₁,ₘ` の principal 項である。

証明は Isabelle と同じ：切片は単項（`mono_slice`、`m ≤ j'₀` を使う）で、その
簡約形 `N = Red M'` は `RTPS`（`ancestor_slice_Red_IncrFirst`）かつ単項。
`Trans M' = Trans N`（`Trans_Red`）で `Trans_principal_head` を `N` に適用し、
`entry N 1 0 = M₁,ₘ`（`M' = IncrFirstN k N` は行 1 を動かさない）で頭指標を
読み替える。 -/
theorem condV_terminal_slice_principal (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hreg : m < (Joints M).getD ((Br M).length - 1) 0 ∨
      (m = (Joints M).getD ((Br M).length - 1) 0 ∧
        entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
        descendingB (Br M) = true)) :
    Trans (seg M m (Lng M - 1))
      = Dprin (entry M 1 m : ℕ∞) (bpHeadT (Trans (seg M m (Lng M - 1)))) := by
  have hreg : condVReg M m := hreg
  have hM : TPS M := RTPS_TPS M hR
  have hmj1 : m < Lng M - 1 := m_lt_j1_cts M m hR hmono hBrne hreg
  have hLpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hj1ltL : Lng M - 1 < Lng M := by omega
  -- 切片は単項
  have hmj0 : m ≤ (Joints M).getD ((Br M).length - 1) 0 := m_le_j0'_cts M m hreg
  have hmonoS : monoT (seg M m (Lng M - 1)) = true :=
    mono_slice M m (Lng M - 1) hM hmono hmj1 (le_refl _) hmj0
  -- 左端は右端の行 0 直系先祖
  have hle0 : le0 M m (Lng M - 1) = true :=
    le0_monoT_seg_into_list M m (Lng M - 1) (Lng M - 1) hM hmonoS
      (by omega) (le_refl _) hj1ltL
  have hleM : leR M 0 m (Lng M - 1) = true := by simpa [leR] using hle0
  -- 簡約形 `N` の基本性質
  have hfacts := ancestor_slice_Red_IncrFirst M m (Lng M - 1) hR hmj1
    (le_refl _) hleM
  have hRedN : Red (Red (seg M m (Lng M - 1))) = Red (seg M m (Lng M - 1)) :=
    hfacts.1
  have hmonoN : monoT (Red (seg M m (Lng M - 1))) = true := hfacts.2.1
  have hIF : seg M m (Lng M - 1)
      = IncrFirstN (entry M 0 m - entry M 1 m) (Red (seg M m (Lng M - 1))) :=
    hfacts.2.2
  -- 長さ
  have hLS : Lng (seg M m (Lng M - 1)) = Lng M - 1 + 1 - m := length_seg M m _
  have hLN : Lng (Red (seg M m (Lng M - 1))) = Lng M - 1 + 1 - m := by
    have h1 : Lng (IncrFirstN (entry M 0 m - entry M 1 m)
        (Red (seg M m (Lng M - 1)))) = Lng (Red (seg M m (Lng M - 1))) := by
      simp [IncrFirstN_eq_map]
    have h2 := congrArg Lng hIF
    rw [h1] at h2
    rw [← h2, hLS]
  have hNT : TPS (Red (seg M m (Lng M - 1))) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red (seg M m (Lng M - 1)))
    omega
  have hST : TPS (seg M m (Lng M - 1)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M m (Lng M - 1))
    omega
  have hNR : RTPS (Red (seg M m (Lng M - 1))) := by
    show reduced (Red (seg M m (Lng M - 1))) = true
    have hne : Red (seg M m (Lng M - 1)) ≠ [] := hNT
    simp [reduced, hne, hRedN]
  -- `Trans` は簡約で不変
  have hTS : Trans (seg M m (Lng M - 1)) = Trans (Red (seg M m (Lng M - 1))) :=
    Trans_Red _ hST
  -- 頭指標の読み替え: `entry N 1 0 = M₁,ₘ`
  have hNpos : (0 : ℕ) < Lng (Red (seg M m (Lng M - 1))) := by omega
  have hhead : entry (Red (seg M m (Lng M - 1))) 1 0 = entry M 1 m := by
    have h1 : entry (seg M m (Lng M - 1)) 1 0
        = entry (Red (seg M m (Lng M - 1))) 1 0 := by
      conv_lhs => rw [hIF]
      exact entry_IncrFirstN_one_cts _ _ 0 hNpos
    have h2 : entry (seg M m (Lng M - 1)) 1 0 = entry M 1 m := by
      have hSpos : (0 : ℕ) < Lng (seg M m (Lng M - 1)) := by omega
      rw [entry_seg M m (Lng M - 1) 1 0 hSpos, Nat.add_zero]
    rw [← h1, h2]
  -- principal 表示を `N` から輸送
  have princN := Trans_principal_head _ hNR hmonoN
  rw [hhead] at princN
  rw [hTS]
  exact princN

/-! ## 主張（`VE` 仮定付き）: Isabelle `m_8_2_condV_terminal_slice_Trans_modVE` -/

/-- **§8.2 補題（条件(V)の下での終切片と `Trans` の関係）**（原文 L3664）、
Isabelle `p_8_2_condV_terminal_slice_Trans` (pss_paper.thy:1607) の逐語形。

ただし値方程式
`VE : bpHeadT (Trans (seg M m (Lng M - 1))) = bpHeadT (Trans M)`
を仮定として持つ（Isabelle `m_8_2_condV_terminal_slice_Trans_modVE`,
layerB 61039 に対応）。`VE` は Isabelle では `vcx_VE_all` (layerB 77076) が
無条件に与えるが、その back-peel 帰納法は約 14000 行あり本ファイルの射程外。 -/
theorem condV_terminal_slice_Trans_modVE (M : PS) (m : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hBrne : Br M ≠ [])
    (hreg : m < (Joints M).getD ((Br M).length - 1) 0 ∨
      (m = (Joints M).getD ((Br M).length - 1) 0 ∧
        entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
          = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
        descendingB (Br M) = true))
    (hVE : bpHeadT (Trans (seg M m (Lng M - 1))) = bpHeadT (Trans M)) :
    ∃! t₁ : BT, Trans M = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
      Trans (seg M m (Lng M - 1)) = Dprin (entry M 1 m : ℕ∞) t₁ :=
  terminal_slice_Trans_scaffold M (seg M m (Lng M - 1)) m
    (Trans_principal_head M hR hmono)
    (condV_terminal_slice_principal M m hR hmono hBrne hreg)
    hVE

#print axioms Trans_principal_head
#print axioms terminal_slice_Trans_scaffold
#print axioms condV_terminal_slice_principal
#print axioms condV_terminal_slice_Trans_modVE

end PSS
