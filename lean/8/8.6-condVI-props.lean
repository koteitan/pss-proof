import «8».«8.6-condVI-close»
import «8».«8.5-exchV-props»

/-!
# §8.6 condition-(VI) の named Prop の解消（`CondVI*` の drop-in）

- 原文: `tmp/content.md` 5484（証明 5670–5760）＝
  命題（条件(VI)の下での Trans と基本列の交換関係）
- 訂正: **なし**（A34/A37 は取り下げ済＝`corrections-old.md`:123/154。A23 は `operB` の
  *定義* にかかるだけで本命題の主張にはかからない）。
- 対象: ビルド済み «8».«8.6-Trans-fseq-condVI» の 3 本
  （`CondVIAdmTowerScb` / `CondVIExchNadm` / `TransPreservesOT`）と、
  «8».«8.6-condVI-close» が残した 2 本
  （`CondVI_scbdec_adm_forms_v6` / `CondVI_scbdec_nadm_forms_v6`）。

  | Prop | 本ファイル | 状態 |
  |---|---|---|
  | `TransPreservesOT` | `transPreservesOT_holds_v6p` | ✅ §8.7 の `OTdisp_*` へ合流 |
  | `CondVI_scbdec_adm_forms_v6` | `condVI_scbdec_adm_forms_holds_v6p` | ⚠️ `CondVIres_adm_Ltower_v6p` 上 |
  | `CondVI_scbdec_nadm_forms_v6` | `condVI_scbdec_nadm_forms_holds_v6p` | ⚠️ `CondVIres_nadm_Ltower_v6p` 上 |
  | `CondVIAdmTowerScb` | `condVIAdmTowerScb_holds_v6p` | ⚠️ 同上（close 経由） |
  | `CondVIExchNadm` | `condVIExchNadm_holds_v6p` | ⚠️ 同上（close 経由） |
  | `FseqDesc_exchVI` | `exchVI_holds_v6p` | ⚠️ 同上（close 経由） |

- Isabelle（設計図）:
  * 逐語転記 = `p_8_6_Trans_fseq_condVI`（`isabelle/pss_paper.thy`:2218、`sorry`）
  * 許容枝 = `c613x_condVI_exch_adm`（`layerB/pss_wip.thy`:73312）の
    `d1`/`d2`/`c2eq`/`dc2`/`k1`/`b1RP` 段（＝本ファイルが証明した部分）と
    `Ltower`/`LtowerBP`/`flatMn` 段（＝残差 (A′)）
  * 非許容枝 = `c613x_condVI_exch_nadm`（同 :73514）＋
    `c6nx_condVI_exch_nadm_uncond`（同 :76705）
  * 指標事実 = `c6gx_condVI_j0`（同 :69818）、guard = `c6gx_condVI_setup`（同 :69867）、
    `c₂` の形 = `c6gx_condVI_transC2`（同 :69884）、
    許容枝の `c₁` = `c6gx_condVI_transC1_adm`（同 :69904）
  * 手術 = `trans_surgery_localized`（同 :23635）、
    行 1 の単調性 = `viB_suffix_max`（同 :4177）
  * 残差の中身 = `c6zx_L_tower`（同 :72166）＋ `c6zx_condVI_oper_L`（同 :72257）＋
    `c6zx_condVI_baseL_free`（同 :72286）＋ `c6nx_t2eq`（同 :76619）、いずれも
    `m_8_4_oper_props_5` / `s84x_L`（＝**§8.4 scb 分解クラスタ**）に乗る
- 依存（すべてビルド済み）: «8».«8.6-condVI-close»（5 本の Prop 本体・
  `condVIAdmTowerScb_of_scbforms_v6` / `condVIExchNadm_of_scbforms_v6` /
  `exchVI_holds_v6` / `p_8_6_Trans_fseq_condVI`、推移的に «8».«8.7-Trans-preserves-OT»
  ＝ `Trans_preserves_OT` ＋ 12 本の `OTdisp_*`、«8».«8.7-fseq-descend»
  ＝ `FseqDesc_exchVI`）、«8».«8.5-exchV-props»（`c1_shape_holds`
  ＝ Isabelle `m_8_5_scbdec_c1_shape`、推移的に «7».«7.3-Trans-welldefined»
  ＝ `replaceScb_spec` / `Trans_Mark_mono_equations` / `Trans_Mark_invariant` /
  `transC2Core_properties`、«7».«7.3-c1-c2-order» ＝ `transC1_single_principal` /
  `principal_reconstruct`、«7».«7.4-RightAnces-RightNodes»
  ＝ `RightNodes_transC2_tail`、«7».«7.3-Mark-rightmost1»
  ＝ `Mark_rightmost1_forward`、«5».«5.3-pred-is-oper1» ＝ `pred_is_oper1`）。

## 設計（`8.6-condVI-close`:39 の「未達」注記の更新）

`8.6-condVI-close`:39 は残差 `CondVI_scbdec_*_forms_v6` を
「`trans_surgery_localized` が Lean 未移植ゆえ閉じられない」と報告しているが、これは
**«8».«8.5-exchV-props»:61 が既に訂正済みの誤り**である（`trans_surgery_localized` は
`replaceScb_spec` で置き換わり、しかも 1 対で両側が出るので uniqueness 段が不要）。
本ファイルはその訂正を §8.6 に適用し、両残差から

* **`k1`（`Trans M` の第 1 種 scb 分解）** — `condVI_surgery_k1_v6p`。
  `replaceScb_spec` ＋ `RightNodes_transC2_tail`（`RightNodes (c₂) = [U, u+1]`）＋
  `U ≤ u < u+1`（`entry1_Adm_le_v6p`）で**両枝とも無条件**;
* **`U` の同定と `U < u+1`（非許容枝）** — `c1_shape_holds` ＋ `entry1_Adm_le_v6p`;
* **`n = 1` の脚（許容枝）** — `condVI_transC1_adm_v6p`（`c₁ = D_u 0`、
  `Mark_rightmost1_forward`）＋ `pred_is_oper1`

を除去した。残ったのは **L 塔の閉形式だけ**＝ Isabelle の `c6zx_L_tower` ＋
`c6zx_condVI_oper_L` ＋ `c6zx_condVI_baseL_free`（許容枝）/ `c6nx_t2eq`（非許容枝）で、
これらは一律に **§8.4 の `s84x_L` / `m_8_4_oper_props_5` クラスタ**（Lean 未移植、
原文でも `8.4-scb-decompositions` は pss_paper 上 DEFERRED）に乗る。
これは «8».«8.5-exchV-props» の `ExchVres_adm_towers` / `ExchV_nf3x` が露出している
欠落と**同一の単一ブリック**であり、単一ファイルの射程を超える（`needs` 参照）。

## 経験的確認（真正 ST_PS プール = `STPS.diag` 種 6 本の `oper` 閉包、深さ 3・`n ≤ 4`、750 本）

**非空虚性**: 条件 (VI) ホストは許容 `j₀` が **153 本**、非許容 `j₀` が **32 本**
（`1 < Lng M - 1` ∧ `monoT`）＝両枝とも空虚でない。

**本ファイルの無条件補題**:
* `condVI_transC1_adm_v6p`（`c₁ = D_u 0`）: 許容枝 **153/153**
* `condVI_transC2_shape_v6p`（`c₂ = D_U(D_{u+1} 0)`）＋
  `condVI_U_le_u_v6p`（`U < u+1`）: 全条件 (VI) ホスト **185/185**

**残差の真偽**（`Lng M ≤ 8` に制限、上記から機械抽出した正準手術対 `(s₁,b₁)` で検査）:
* (A′) `CondVIres_adm_Ltower_v6p`: **82/82**（`n = 2,3,4`）、仮定部も同時に成立
* (B′) `CondVIres_nadm_Ltower_v6p`: **32/32**（`n = 1,2,3,4`）。`c6nx_t2eq`
  （`c₁ = D_U(D_u 0)`）も同じ 32 本で成立
＝**削減後の残差は空虚でなく、かつ真**（偽命題を下流に渡していない）。

- 状態: GREEN（sorry 0）。5 本中 1 本（`TransPreservesOT`）を §8.7 へ合流させ、
  4 本を **`CondVIres_adm_Ltower_v6p` / `CondVIres_nadm_Ltower_v6p` の 2 本へ削減**。
  §8.6 ツリー項目と `FseqDesc_exchVI` は、この 2 本＝§8.4 L 塔クラスタが落ちれば閉じる。
-/

namespace PSS

/-! ## 条件 (VI) の指標事実（Isabelle `c6gx_condVI_j0`, pss_wip.thy:69818） -/

private theorem condVI_j0_v6p {M : PS} (hcond : transCondVI M = true) :
    transJ0 M + 1 = Lng M - 1 ∧
      entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) ∧
      0 < entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  exact ⟨hcond.2, hcond.1.2, hcond.1.1⟩

/-! ## 非退化枝の guard（Isabelle `c6gx_condVI_setup`, pss_wip.thy:69867） -/

private theorem condVI_setup_v6p {M : PS} (hR : RTPS M) (_hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) : 0 < transJ1 M ∧ transT1 M ≠ BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 2 < Lng M := by omega
  refine ⟨by simp only [transJ1, lastIdx]; omega, ?_⟩
  intro ht₁
  have hzP : zeroT (Pred M) = true :=
    (Trans_preserves_zeroT (Pred M) (Pred_TPS M hM)).2 ht₁
  have hLP : Lng (Pred M) = Lng M - 1 := by
    simp only [Pred]
    rw [if_neg (by omega)]
    simp
  have h1 : Lng (Pred M) = 1 := by
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzP
    exact hzP.1
  omega

/-! ## `c₂` の形（Isabelle `c6gx_condVI_transC2`, pss_wip.thy:69884） -/

private theorem condVI_not135_v6p {M : PS} (hcond : transCondVI M = true) :
    (transCondI M || transCondIII M || transCondV M) = false := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
  obtain ⟨⟨hpos, heq⟩, hadj⟩ := hcond
  have hI : transCondI M = false := by
    have h : ¬ (entry M 1 (lastIdx M) = 0) := by omega
    simp [transCondI, h]
  have hIII : transCondIII M = false := by
    have h : ¬ (entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)) := by omega
    simp [transCondIII, h]
  have hV : transCondV M = false := by
    have h : ¬ (lastParent M + 1 < lastIdx M) := by omega
    simp [transCondV, h]
  simp [hI, hIII, hV]

private theorem condVI_transC2_v6p {M : PS} (hcond : transCondVI M = true) :
    transC2 M = Dprin (transV M) (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero) := by
  have h135 := condVI_not135_v6p hcond
  simp [transC2, transC2Core, h135, hcond, lastIdx]

/-! ## 許容化に沿った行 1 の単調性（Isabelle `viB_suffix_max`, pss_wip.thy:4177）

`8.5-exchV-props` の `entry1_step_xv` / `entry1_Adm_le_xv` は `private` なので、
同じ証明を本ファイルに複製する（suffix `_v6p`）。 -/

private theorem entry1_step_v6p (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
    (hj₀ : j₀ < Lng M) (hge : Adm M j₀ ≤ j) (hlt : j < j₀) :
    entry M 1 j < entry M 1 (j + 1) := by
  have hnaS : adm M (j + 1) = false := by
    by_contra hcon
    have hadm : adm M (j + 1) = true := by simpa using hcon
    rcases Nat.lt_or_ge (j + 1) j₀ with h | h
    · have := Adm_max M (j + 1) j₀ hadm (by omega)
      omega
    · have hEq : j + 1 = j₀ := by omega
      rw [hEq] at hadm
      rw [hadm] at hna
      exact absurd hna (by simp)
  have hnadm : nadm M (j + 1) = true := by
    simpa [adm] using hnaS
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadm
  have hlen : ¬ (Lng M < j + 1) := by omega
  rcases hnadm with h | h
  · exact absurd h hlen
  · have hn1 : nextrel1 M j (j + 1) = true := by
      simpa [nextR] using h.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact hn1.1.1.2

private theorem entry1_Adm_le_v6p (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
    entry M 1 (Adm M j₀) ≤ entry M 1 j₀ := by
  by_cases hadm : adm M j₀ = true
  · simp [Adm, hadm]
  · have hna : adm M j₀ = false := by simpa using hadm
    have hmono : ∀ d a, d = j₀ - a → Adm M j₀ ≤ a → a ≤ j₀ →
        entry M 1 a ≤ entry M 1 j₀ := by
      intro d
      induction d with
      | zero => intro a hd _ hle; have : a = j₀ := by omega
                rw [this]
      | succ d ih =>
          intro a hd hge hle
          have hlt : a < j₀ := by omega
          have hstep := entry1_step_v6p M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-! ## 手術（Isabelle `trans_surgery_localized`, pss_wip.thy:23635）

`8.5-exchV-props`:324 の `trans_surgery_localized_xv` と同一（`private` なので複製）。
`replaceScb_spec`（`7.3-Trans-welldefined`:318）が **1 つの対 `(s,b)`** で
`Trans (Pred M)` 側と `Trans M` 側の scb 分解を同時に出すので、Isabelle の
uniqueness 段（`m_7_2_scb_unique_sb`）は不要。 -/

private theorem transC1_principal_v6p (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    ∃ p, transC1 M = .trm [p] := by
  have h := principal_reconstruct (transC1_single_principal M hR hmono hj₁ ht₁)
  exact ⟨.db (transV M) (transT2 M), by simpa [Dprin] using h⟩

private theorem transC2_principal_v6p (M : PS) (hcond : transCondVI M = true) :
    ∃ p, transC2 M = .trm [p] :=
  ⟨.db (transV M) _, by simpa [Dprin] using condVI_transC2_v6p hcond⟩

theorem trans_surgery_localized_v6p (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero)
    (hc₂P : ∃ p, transC2 M = .trm [p]) :
    ∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
  have hinv := (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hmarked
  have ht₁TB : Trans (Pred M) ∈ T_B := (Trans_Mark_invariant (Pred M) hpredR).1
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using hinv.1
  have hmb : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transT1, transC1, transJm1, transJ0, lastParent] using hinv.2
  have hc₁P := transC1_principal_v6p M hR hmono hj₁ ht₁
  have hc₂TB : transC2 M ∈ T_B := by
    have := transC2Core_properties M (transC1 M) hc₁TB hc₁P
    simpa [transC2, transV, transT2] using this.1
  obtain ⟨s, b, hd₁, _hflat, hd₂⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P hmb
  refine ⟨s, b, hd₁, ?_⟩
  have hTM : Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
    have ht₁b : (Trans (Pred M) == BZero) = false := by
      simpa [beq_iff_eq, transT1] using ht₁
    simpa [transT1, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent, ht₁b] using heq
  rw [hTM]
  exact hd₂

/-! ## 条件 (VI) の共有 scb 対と kind-1 producer（両枝共通、**無条件**）

Isabelle `c613x_condVI_exch_adm`（pss_wip.thy:73312）の `d1`/`d2`/`c2eq`/`dc2`/`k1`
段と、`c613x_condVI_exch_nadm`（同 :73514）の同じ段を、**許容・非許容を分けずに**
一度に出す。crux は `RightNodes (transC2 M) = [U, u+1]`
（`RightNodes_transC2_tail` ＝ Isabelle `ra_RightNodes_transC2_tail`；Isabelle は
`rnp`/`rncond` を `simp` で潰してから `scb_kind1_of_suffix` に渡している）＋
`U ≤ u < u + 1`（`entry1_Adm_le_v6p` ＝ `viB_suffix_max`）。 -/

private theorem condVI_j0_lt_v6p {M : PS} (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) : transJ0 M < Lng M := by
  have h := (condVI_j0_v6p hcond).1
  omega

/-- `U := M_{1,j₋₁} ≤ u := M_{1,j₀}`（許容枝では等号）。 -/
private theorem condVI_U_le_u_v6p {M : PS} (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) :
    entry M 1 (transJm1 M) ≤ entry M 1 (transJ0 M) := by
  simpa [transJm1] using entry1_Adm_le_v6p M (transJ0 M) (condVI_j0_lt_v6p hcond hj₁)

/-- **条件 (VI) の共有 scb 対**（無条件）: `Trans (M[1]) = Trans (Pred M)` を `c₁` で、
`Trans M` を `c₂ = D_U(D_{u+1} 0)` で切る 1 つの対 `(s₁,b₁)` が存在し、しかも後者は
**第 1 種**である。Isabelle の `d1` ＋ `k1` に対応。 -/
private theorem condVI_surgery_k1_v6p (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    ∃ s₁ b₁ : List Sym,
      scb_decomp (Trans (oper M 1)) s₁ (flatBT (transC1 M)) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      transV M = (entry M 1 (transJm1 M) : ℕ∞) ∧
      transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨hj₁pos, ht₁⟩ := condVI_setup_v6p hR hcond hj₁
  obtain ⟨hV, hc₁eq, _ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁pos ht₁
  obtain ⟨s₁, b₁, hd₁, hd₂⟩ :=
    trans_surgery_localized_v6p M hR hmono hj₁pos ht₁ (transC2_principal_v6p M hcond)
  refine ⟨s₁, b₁, ?_, ⟨hd₂, ?_⟩, hV, hc₁eq⟩
  · rw [← pred_is_oper1 M hM hlen]; exact hd₁
  · -- kind-1: `RightNodes (transC2 M) = [U, u+1]` と `U ≤ u < u+1`
    intro p hp
    have hc₂ : transC2 M = .trm [p] := by
      apply flatBT_injective
      simpa [flatBT] using hp
    have hrn : RightNodes (.trm [p]) =
        [(transV M).toNat, entry M 1 (transJ1 M)] := by
      rw [← hc₂]
      have hA : (transCondI M || transCondIII M || transCondV M
        || transCondVI M) = true := by simp [hcond]
      simpa [hA] using RightNodes_transC2_tail M
    have huv : (transV M).toNat < entry M 1 (transJ1 M) := by
      rw [hV]
      have hle := condVI_U_le_u_v6p hcond hj₁
      have hsucc := (condVI_j0_v6p hcond).2.1
      have hj1eq : transJ1 M = Lng M - 1 := rfl
      rw [hj1eq]
      simpa using by omega
    simp only [hrn]
    exact ⟨by simp, by simpa using huv, by intro j hj0 hj1; simp at hj1; omega⟩

/-! ## 許容 `j₀` の `c₁`（Isabelle `c6gx_condVI_transC1_adm`, pss_wip.thy:69904）

許容枝では第 2 基点が潰れて `j₋₁ = j₀`、しかも条件 (VI) の隣接性
（`j₀ + 1 = j₁`）から `j₀ = Lng (Pred M) - 1` ＝ `Pred M` の**右端**になるので、
`c₁ = Mark (Pred M) j₀ = D_u 0`（`Mark_rightmost1_forward`
＝ Isabelle `m_7_3_Mark_rightmost1`）で `t₂ = 0`。 -/

private theorem entry_Pred_v6p (M : PS) (j : ℕ) (hlen : 1 < Lng M)
    (hj : j < Lng M - 1) : entry (Pred M) 1 j = entry M 1 j := by
  rw [Pred_eq_take M hlen]
  exact entry_take M (Lng M - 1) 1 j (by omega)

private theorem Lng_Pred_v6p (M : PS) (hlen : 1 < Lng M) : Lng (Pred M) = Lng M - 1 := by
  simp only [Pred]
  rw [if_neg (by omega)]
  simp

private theorem condVI_jm1_adm_v6p {M : PS} (hadm : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by
  simp [transJm1, Adm, hadm]

private theorem condVI_transC1_adm_v6p (M : PS) (hR : RTPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hadm : adm M (transJ0 M) = true) :
    transC1 M = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := by
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hLP : Lng (Pred M) = Lng M - 1 := Lng_Pred_v6p M hlen
  have hj0 := (condVI_j0_v6p hcond).1
  have hj0last : transJ0 M = Lng (Pred M) - 1 := by omega
  have hnz : zeroT (Pred M) = false := by
    have h1 : ¬ (Lng (Pred M) = 1) := by omega
    simp [zeroT, h1]
  have hright := Mark_rightmost1_forward (Pred M) hpredR hnz
  have hentry : entry (Pred M) 1 (transJ0 M) = entry M 1 (transJ0 M) :=
    entry_Pred_v6p M (transJ0 M) hlen (by omega)
  have : Mark (Pred M) (transJ0 M) = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := by
    rw [hj0last, hright, ← hj0last, hentry]
  rw [transC1, condVI_jm1_adm_v6p hadm]
  exact this

/-- 条件 (VI) の `c₂` を、`U = M_{1,j₋₁}` と `u + 1 = M_{1,j₁}` で書いた形
（Isabelle `c2eq`、`c613x_condVI_exch_adm` 内）。 -/
private theorem condVI_transC2_shape_v6p (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    transC2 M = Dprin (entry M 1 (transJm1 M) : ℕ∞)
      (Dprin ((entry M 1 (transJ0 M) + 1 : ℕ) : ℕ∞) BZero) := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hj₁pos, ht₁⟩ := condVI_setup_v6p hR hcond hj₁
  obtain ⟨hV, _, _, _⟩ := c1_shape_holds M hR hM hmono hj₁pos ht₁
  have hsucc := (condVI_j0_v6p hcond).2.1
  rw [condVI_transC2_v6p hcond, hV, hsucc]

/-! ## 塔の `T_B` 事実（`8.6-condVI-close` の `Dtower_*_v6` は `private` なので複製） -/

private theorem BZero_mem_T_B_v6p : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem tower_mem_T_B_v6p (u k : ℕ) : (Dprin (u : ℕ∞))^[k] BZero ∈ T_B := by
  induction k with
  | zero => simpa using BZero_mem_T_B_v6p
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h : dfree_BT ((Dprin (u : ℕ∞))^[k] BZero) = true := ih
      simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, h]

private theorem isPTB_str_Dprin_tower_v6p (U u k : ℕ) :
    isPTB_str (flatBT (Dprin (U : ℕ∞) ((Dprin (u : ℕ∞))^[k] BZero))) := by
  refine ⟨.db (U : ℕ∞) _, ?_, rfl⟩
  have h : dfree_BT ((Dprin (u : ℕ∞))^[k] BZero) = true := tower_mem_T_B_v6p u k
  simp [dfree_BP, h]

/-! ## 削減後の残差 2 本（§8.4 L 塔クラスタのみ） -/

/-- **削減後の残差 (A′)** — 許容 `j₀` の条件 (VI) ホストの **L 塔だけ**。

`8.6-condVI-close`:244 の `CondVI_scbdec_adm_forms_v6` との差:
* **`k1`（`Trans M` の kind-1 scb 分解）が消えている** — 本ファイルの
  `condVI_surgery_k1_v6p` が `replaceScb_spec` ＋ `RightNodes_transC2_tail` から
  **無条件に**出す;
* **`n = 1` の脚が消えている** — `M[1] = Pred M` と
  `condVI_transC1_adm_v6p`（＝ `c6gx_condVI_transC1_adm`）で `c₁ = D_u 0` が出るため;
* 共有 scb 対 `(s₁,b₁)` は `∃` ではなく**入力**になった（`ExchVres_adm_towers`
  ＝ `8.5-exchV-props`:412 と同じ形）。

残っているのは Isabelle の `c6zx_L_tower`（pss_wip.thy:72166、`m_8_4_oper_props_5` の
(5-1)/(5-2) 上の帰納）＋ 境界同定 `c6zx_condVI_oper_L`（同 :72257、
`s84c1_oper_Suc_eq_L_app` で `M[Suc n] = L_n`）＋ 底値 `c6zx_condVI_baseL_free`
（同 :72286）だけ、すなわち **§8.4 scb 分解クラスタ（`s84x_L` / `m_8_4_oper_props_5`）の
Lean 未移植分**である。仮定の `scb_decomp (Trans (M[1])) s₁ (flatBT (D_u 0)) b₁` は
Isabelle が `c6zx_condVI_baseL_free` に渡す `d1u` そのもの。 -/
def CondVIres_adm_Ltower_v6p : Prop :=
  ∀ (M : PS) (s₁ b₁ : List Sym), STPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → adm M (transJ0 M) = true →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) b₁ →
    ∀ n, 2 ≤ n →
      flatBT (Trans (oper M n))
        = s₁ ++ flatBP (.db (entry M 1 (transJ0 M) : ℕ∞)
            ((Dprin (entry M 1 (transJ0 M) : ℕ∞))^[n - 1] BZero)) ++ b₁

/-- **削減後の残差 (B′)** — 非許容 `j₀` の条件 (VI) ホストの **L 塔だけ**。

`8.6-condVI-close`:317 の `CondVI_scbdec_nadm_forms_v6` との差:
* **`U < u + 1` と `k1` が消えている** — 前者は `entry1_Adm_le_v6p`
  （＝ `viB_suffix_max`）で `U = M_{1,j₋₁} ≤ M_{1,j₀} = u < u+1`、後者は
  `condVI_surgery_k1_v6p`（どちらも無条件）;
* `U` の同定（Isabelle `c6nx_condVI_uv`, pss_wip.thy:76352）も消えている
  ——`U = M_{1,j₋₁}` は `c1_shape_holds`（`8.5-exchV-props`:145）が出す。

残差は塔の閉形式のみ。`n = 1` の脚がここに残っているのは、非許容枝では
`c₁ = D_U(D_u 0)` を出すのに `t₂ = D_u 0`（Isabelle `c6nx_t2eq`, 同 :76619 ＝
内部基点の値事実）が要り、これも §8.4 クラスタ側だからである。 -/
def CondVIres_nadm_Ltower_v6p : Prop :=
  ∀ (M : PS) (s₁ b₁ : List Sym), STPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → ¬ (adm M (transJ0 M) = true) →
    scb_decomp (Trans (oper M 1)) s₁ (flatBT (transC1 M)) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    ∀ n, 1 ≤ n →
      flatBT (Trans (oper M n))
        = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
            ((Dprin (entry M 1 (transJ0 M) : ℕ∞))^[n] BZero)) ++ b₁

/-! ## `CondVI_scbdec_adm_forms_v6` / `CondVI_scbdec_nadm_forms_v6` の discharge -/

/-- **`CondVI_scbdec_adm_forms_v6`（`8.6-condVI-close`:244）の削減**。
`k1` と `n = 1` の脚を無条件に供給し、残差を L 塔だけにする。 -/
theorem condVI_scbdec_adm_forms_holds_v6p (h : CondVIres_adm_Ltower_v6p) :
    CondVI_scbdec_adm_forms_v6 := by
  intro M hST hR hmono hcond hj₁ hadm
  obtain ⟨s₁, b₁, hd₁, hk1, _hV, _hc₁eq⟩ := condVI_surgery_k1_v6p M hR hmono hcond hj₁
  have hjm1 : transJm1 M = transJ0 M := condVI_jm1_adm_v6p hadm
  have hc₁ : transC1 M = Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero :=
    condVI_transC1_adm_v6p M hR hcond hj₁ hadm
  have hbase : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) b₁ := by
    rw [← hc₁]; exact hd₁
  have hLt := h M s₁ b₁ hST hmono hcond hj₁ hadm hbase
  refine ⟨s₁, b₁, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact hbase
    · exact ⟨hLt n h2, fun _ => isPTB_str_Dprin_tower_v6p _ _ _, hd₁.2.2⟩
  · have hc₂ := condVI_transC2_shape_v6p M hR hmono hcond hj₁
    rw [hc₂, hjm1] at hk1
    exact hk1

/-- **`CondVI_scbdec_nadm_forms_v6`（`8.6-condVI-close`:317）の削減**。
`U` の同定・`U < u+1`・`k1` を無条件に供給し、残差を L 塔だけにする。 -/
theorem condVI_scbdec_nadm_forms_holds_v6p (h : CondVIres_nadm_Ltower_v6p) :
    CondVI_scbdec_nadm_forms_v6 := by
  intro M hST hR hmono hcond hj₁ hadm
  obtain ⟨s₁, b₁, hd₁, hk1, _hV, _hc₁eq⟩ := condVI_surgery_k1_v6p M hR hmono hcond hj₁
  have hLt := h M s₁ b₁ hST hmono hcond hj₁ hadm hd₁ hk1
  refine ⟨entry M 1 (transJm1 M), s₁, b₁, ?_, hLt, ?_⟩
  · have hle := condVI_U_le_u_v6p hcond hj₁
    omega
  · have hc₂ := condVI_transC2_shape_v6p M hR hmono hcond hj₁
    rw [hc₂] at hk1
    exact hk1

/-! ## `8.6-Trans-fseq-condVI` の 3 本の named Prop への drop-in（house pattern） -/

/-- **`CondVIAdmTowerScb`（`8.6-Trans-fseq-condVI`:220）の drop-in**（残差 (A′) modulo）。
Buchholz 側（`operB` の塔閉形式 `ov`）は `8.6-condVI-close` の
`condVIAdmTowerScb_of_scbforms_v6`（＝ Isabelle `c613x_operB_fseq_value`）が供給する。 -/
theorem condVIAdmTowerScb_holds_v6p (h : CondVIres_adm_Ltower_v6p) :
    CondVIAdmTowerScb :=
  condVIAdmTowerScb_of_scbforms_v6 (condVI_scbdec_adm_forms_holds_v6p h)

/-- **`CondVIExchNadm`（`8.6-Trans-fseq-condVI`:236）の drop-in**（残差 (B′) modulo）。 -/
theorem condVIExchNadm_holds_v6p (h : CondVIres_nadm_Ltower_v6p) :
    CondVIExchNadm :=
  condVIExchNadm_of_scbforms_v6 (condVI_scbdec_nadm_forms_holds_v6p h)

/-- **`TransPreservesOT`（`8.6-Trans-fseq-condVI`:247）の drop-in**。

§8.7 の `Trans_preserves_OT`（`8.7-Trans-preserves-OT`:487）がそのまま外れる。
これは 8.6 固有の残差を §8.7 が**既に露出している** 12 本の `OTdisp_*` へ合流させる
もので、プロジェクト全体の残差集合は増えない。`8.6-condVI-close`:370 の
`transPreservesOT_of_OTdisp_v6` と同一内容（house pattern のため本ファイルでも
Prop を型として明示する）。 -/
theorem transPreservesOT_holds_v6p
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq) :
    TransPreservesOT :=
  Trans_preserves_OT hI hII hOTint hOTpred hOTmulti hZC hCIn1 hCIj0 hCIj1
    hCVIj1 hCVIa hCVIn

/-! ## 降下柱（`8.7-fseq-descend`）と原文命題への配線 -/

/-- **`FseqDesc_exchVI`（`8.7-fseq-descend`:101）の drop-in**（残差 (A′)/(B′) modulo）。
`TransPreservesOT` は不要（`8.6-condVI-close`:394 の `exchVI_holds_v6` を参照:
降下柱は `1 < m` しか要求しないので原文 (1) の例外脚が立たない）。 -/
theorem exchVI_holds_v6p (hA : CondVIres_adm_Ltower_v6p)
    (hB : CondVIres_nadm_Ltower_v6p) : FseqDesc_exchVI :=
  exchVI_holds_v6 (condVIAdmTowerScb_holds_v6p hA) (condVIExchNadm_holds_v6p hB)

/-- **§8.6 命題の逐語形**（原文 `tmp/content.md` 5484 ＝ `p_8_6_Trans_fseq_condVI`、
`isabelle/pss_paper.thy`:2218）を、**本ファイルの削減後の残差の上で**述べ直したもの。
`8.6-condVI-close`:426 の `p_8_6_Trans_fseq_condVI_v6` から
`CondVI_scbdec_adm_forms_v6` / `CondVI_scbdec_nadm_forms_v6` が
`CondVIres_adm_Ltower_v6p` / `CondVIres_nadm_Ltower_v6p` に置き換わっている。 -/
theorem p_8_6_Trans_fseq_condVI_v6p
    (hA : CondVIres_adm_Ltower_v6p) (hB : CondVIres_nadm_Ltower_v6p)
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hR : RTPS M) (hmono : monoT M = true) (hn : 0 < n)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondVI M = true) :
    (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true →
        ∃ k, 1 < k ∧ k ≤ entry M 1 (Lng M - 1) + 1 ∧
          Trans (oper M n) = ((fun a => operB a (numBT 0))^[k]) (Trans M))
      ∧ (¬ (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true) →
        Trans (oper M n) =
          operB (Trans M)
            (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 2 else n - 1)))
      ∧ lessBT (Trans (oper M n)) (Trans M) = true :=
  p_8_6_Trans_fseq_condVI M n
    (condVIAdmTowerScb_holds_v6p hA)
    (condVIExchNadm_holds_v6p hB)
    (transPreservesOT_holds_v6p hI hII hOTint hOTpred hOTmulti hZC hCIn1
      hCIj0 hCIj1 hCVIj1 hCVIa hCVIn)
    hST hR hmono hn hj₁ hcond

#print axioms condVI_scbdec_adm_forms_holds_v6p
#print axioms condVI_scbdec_nadm_forms_holds_v6p
#print axioms condVIAdmTowerScb_holds_v6p
#print axioms condVIExchNadm_holds_v6p
#print axioms transPreservesOT_holds_v6p
#print axioms exchVI_holds_v6p
#print axioms p_8_6_Trans_fseq_condVI_v6p

end PSS
