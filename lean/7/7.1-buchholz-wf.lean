import «7».«7.1-buchholz-wf-Buc2body»
import «7».«7.1-buchholz-wf-bachmann»
import «7».«7.1-buchholz-fseq-closed»
import PSS.Buchholz

/-!
# §7.1 [Buc1] 補題 2.2 — `(OT_B, <)` の整礎性（キャンペーン頂点）

- 原文: `tmp/content.md` 5978 / 6331（`(OT_B, <)` の整礎性を [Buc1] 補題 2.2 として引用）。
  逐語形は `buc1_2_2_OT_B_wf`（isabelle/pss_paper.thy、`sorry` 引用）。
- [Buc1]: Lemma 2.2（p.137）。**Buchholz 自身の 2.2 は意味論的**（順序数への評価写像
  `o : OT → Ord`、`ψ_v`、`Ω_u` を使い、`a < c ⟹ o(a) < o(c)` を示す）であり、
  定義的 HOL / Lean では**表現できない**。ここで移植するのは Buchholz–Schütte の
  distinguished sets 法による **cardinal-free** 経路である。
  **順序数・`ψ`・`Ω` は本ファイルに一切現れない。**
- 訂正: なし（A23＝[Buc1] 脚注 [30] の `xseq` 転置誤植の訂正は上流
  `7.1-buchholz-wf-Buc2body` / `7.1-buchholz-wf-bachmann` で消化済）。
- Isabelle: `isabelle/layerC/pss_scratch.thy`
  - `RTrel` (64629, layerB/pss_wip.thy) ＝ 本ファイルの `RTrelW`
  - `wfox_goal_eq_RTrel` (layerB/pss_wip.thy:64633) ＝ 目標関係が `RTrel` に一致
  - `bwl_not_lessBT_zero` (9770) ＝ `not_lessBT_zero_wfe`
  - `y3_cof0` (11455) / `y3_cof0_imp_bwl_cof` (11464) ＝ `bwl_cof_wfe`
  - `bwl_acc_of_W` (9808) ＝ `acc_of_W_wfe`
  - `y4_cof0` (13678) / `y4_wf_RPrel` (13689)
  - `y4_buc1_2_2_OT_B_wf` (13700) ＝ 本ファイルの `buchholz_wf`
- 依存（ビルド済みのみ import）: `7.1-buchholz-wf-W`（`bwl_W`/`bwl_Aop`/`bwl_A2'`/
  `y3_TBv_dfree_W`/`y3_dfree_W_ex`、経由: Buc2body）、`7.1-buchholz-wf-Buc2body`
  （`Bwl28Principal_holds`/`Bwl24bAdd_holds`/`bwo_domB_Nil`）、
  `7.1-buchholz-wf-bachmann`（`y4_bachmann_domB` ＝ Bachmann 共終性）、
  `7.1-buchholz-fseq-closed`（`buchholz_fseq_closed`/`buchholz_fseq_closed_general`
  ＝ [Buc1] 3.3）、`PSS.Buchholz`。
- 状態: ✅ green（sorry 0、**名前付き仮定 0**）。

## Isabelle 経路との差分（`RPrel` 層の全消去）

Isabelle は
`bwl_cof → bwl_Wstar_total_of_cof (9927) → bwo_2_2_wf (7834) → y4_wf_RPrel (13689)
→ wfox_tuple_lift (layerB:64949) → y4_buc1_2_2_OT_B_wf (13700)`
と、principal 順序 `RPrel` を経由して `wf RTrel` へ戻る。これは r66 の bwo ブロックが
`bwo_Wstar_total` を残差として切り出した歴史的経緯によるもので、`bwl_acc_of_W`
（`bwl_cof ⟹ W_u ⊆ acc RTrel`、9808）が r68 で証明された時点で**迂回可能になっている**:

  `y3_dfree_W_ex`（`dfree_BT t ⟹ ∃ m. t ∈ W_m`、11382）＋ `bwl_acc_of_W`
  ＋「`OT_B` 外の項は `RTrel`-前者を持たないので自明に `acc`」

で全項の `acc RTrel` が直ちに出る。従って本ファイルは `RPrel` / `bwo_Wstar` /
`wfj_tuple_acc` / `wfc_wf_of_pbody_hyp` / `wfox_tuple_lift` を**一切必要としない**。
（`bwo_2_2_wf_iff` (7871) が示すとおり `bwo_Wstar_total ⟺ wf RPrel` は
overshoot のない同値なので、この短絡は強さを失わない。）

## `8.7-OT-tail-annihilable` の `OT_B_wf` との接続

`lean/8/8.7-OT-tail-annihilable.lean:52` の名前付き仮定
`def OT_B_wf : Prop := WellFounded (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true)`
と本ファイルの `buchholz_wf` は**同一の型**である。従って `buchholz_wf` はその仮定の
drop-in であり、8.7 の唯一の残差が閉じる。

**本ファイルは 8.7 を import しない**（＝`theorem OT_B_wf_holds : OT_B_wf := buchholz_wf`
を同居させない）。理由は依存の向き: 8.7 の残差を落とす配線は 8.7 側が本ファイルを
import する形になるので、こちらから 8.7 を import すると**循環する**。§7 が §8 を
import する層の逆転でもある。

同値性は使い捨てファイルで**外部確認済み**（本ファイルは未ビルドなので import できず、
上流の同一 import 集合で検査した）。8.7 と本ファイルの上流
（`7.1-buchholz-wf-Buc2body` / `7.1-buchholz-wf-bachmann` / `7.1-buchholz-fseq-closed`）は
名前衝突なく co-import でき、その状態で

    example : OT_B_wf ↔
        WellFounded (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) := Iff.rfl

が通る（`check_lean.py` rc=0）。すなわち両者は**定義的に等しい**。配線側は
`theorem OT_B_wf_holds : OT_B_wf := buchholz_wf` と書けばよい。

`private` 補助の接尾辞は `_wfe`。
-/

namespace PSS

/-! ## 0. 目標関係

Isabelle の `RTrel = {(a,b). isOT_BT a ∧ dfree_BT a ∧ isOT_BT b ∧ dfree_BT b ∧ lessBT a b}`
と `wfox_goal_eq_RTrel : {(a,b). a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b} = RTrel`
（`OT_B = OT ∩ T_B` を展開するだけ）を、Lean では**目標形のまま**採る。
Isabelle の `(x,y) ∈ r` は「`x` が小さい」なので、Lean の `WellFounded r` の引数順
（第 1 引数が小さい）と一致する。 -/

/-- Isabelle `RTrel`（＝ `wfox_goal_eq_RTrel` により目標関係そのもの）。 -/
private def RTrelW : BT → BT → Prop :=
  fun a b => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true

private theorem RTrelW_iff {a b : BT} :
    RTrelW a b ↔ (a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) := Iff.rfl

/-- `OT_B = OT ∩ T_B` の展開。 -/
private theorem memOTB_wfe {t : BT} :
    t ∈ OT_B ↔ (isOT_BT t = true ∧ dfree_BT t = true) := Iff.rfl

/-- Isabelle: `bwl_not_lessBT_zero` (pss_scratch.thy:9770)。 -/
private theorem not_lessBT_zero_wfe (y : BT) : lessBT y BZero = false := by
  rcases y with ⟨ys⟩
  cases ys <;> simp [lessBT, BZero, lessBPList]

/-! ## 1. `dom` の非退化（`c ≠ 0` の判定） -/

private theorem zeroOnly_ne_empty_wfe : ({BZero} : Set BT) ≠ (∅ : Set BT) := by
  intro h
  have hb : BZero ∈ ({BZero} : Set BT) := rfl
  rw [h] at hb
  exact hb

private theorem NatSet_ne_empty_wfe : (NatSet : Set BT) ≠ (∅ : Set BT) := by
  intro h
  have hb : numBT 0 ∈ NatSet := ⟨0, rfl⟩
  rw [h] at hb
  exact hb

private theorem TBv_ne_empty_wfe (m : ℕ) : (TBv (m : ℕ∞) : Set BT) ≠ (∅ : Set BT) := by
  intro h
  have hb : BZero ∈ TBv (m : ℕ∞) := by simp [TBv, BZero]
  rw [h] at hb
  exact hb

/-! ## 2. Bachmann 共終性の `W`-形（Isabelle `y3_cof0` → `bwl_cof`）

`y3_cof0` (11455) は `bwl_cof` から節 `z ∈ W_m` を落としたもので、
`y3_cof0_imp_bwl_cof` (11464) がその節を `y3_TBv_dfree_W`（`z ∈ dom(a) = T_m` かつ
`z` が `D_ω`-free なら既に `z ∈ W_m`）で無料で回復する。`y4_cof0` (13678) は
「`y3_cof0` は文字どおり `y4_bachmann`」であった。Lean 側では `y4_bachmann_domB`
（`7.1-buchholz-wf-bachmann`）が `y3_cof0` そのものなので、ここで両段を合成する。 -/

private theorem bwl_cof_wfe {a b : BT}
    (ota : isOT_BT a = true) (dfa : dfree_BT a = true)
    (otb : isOT_BT b = true) (dfb : dfree_BT b = true) (hba : lessBT b a = true) :
    ((domB a = {BZero} ∨ domB a = NatSet) → ∃ n : ℕ, leBT b (operB a (numBT n)) = true) ∧
    (∀ m : ℕ, domB a = TBv (m : ℕ∞) →
        ∃ z, z ∈ bwl_W m ∧ z ∈ domB a ∧ isOT_BT z = true ∧ dfree_BT z = true ∧
          leBT b (operB a z) = true) := by
  obtain ⟨c1, c2⟩ := y4_bachmann_domB a b ota dfa otb dfb hba
  refine ⟨c1, fun m hm => ?_⟩
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := c2 m hm
  have hzT : z ∈ TBv (m : ℕ∞) := by rw [← hm]; exact hz1
  exact ⟨z, y3_TBv_dfree_W Bwl28Principal_holds Bwl24bAdd_holds hz3 hzT,
         hz1, hz2, hz3, hz4⟩

/-! ## 3. 橋（Isabelle `bwl_acc_of_W`, 9808）

`bwl_cof` の下で `acc RTrel` は `A_u`-閉である。よって（無料の）最小性 (A2) から
`W_u ⊆ acc RTrel`。`OT_B` に属さない項は `RTrel`-前者を一切持たないので無料で `acc`。 -/

private theorem acc_of_W_wfe (u : ℕ) : bwl_W u ⊆ {t : BT | Acc RTrelW t} := by
  refine bwl_A2' ?_
  intro c A
  by_cases hOT : isOT_BT c = true ∧ dfree_BT c = true
  · obtain ⟨otc, dfc⟩ := hOT
    have cOT : c ∈ OT_B := memOTB_wfe.mpr ⟨otc, dfc⟩
    rcases A with hz | ⟨hd, hop⟩ | ⟨m, _, hd, hop⟩
    · -- (zero) `c = 0`: 何も `< 0` でない
      refine Acc.intro c ?_
      intro y hy
      obtain ⟨_, _, hlt⟩ := RTrelW_iff.mp hy
      rw [hz, not_lessBT_zero_wfe y] at hlt
      exact absurd hlt (by simp)
    · -- (num) `dom c ∈ {{0}, ℕ}`: 数項の基本列が共終
      have cne : c ≠ BZero := by
        intro h
        rw [h, bwo_domB_Nil] at hd
        rcases hd with h1 | h1
        · exact zeroOnly_ne_empty_wfe h1.symm
        · exact NatSet_ne_empty_wfe h1.symm
      refine Acc.intro c ?_
      intro b hb
      obtain ⟨bOT, _, hlb⟩ := RTrelW_iff.mp hb
      obtain ⟨otb, dfb⟩ := memOTB_wfe.mp bOT
      obtain ⟨cof1, _⟩ := bwl_cof_wfe otc dfc otb dfb hlb
      obtain ⟨n, hn⟩ := cof1 hd
      have accn : Acc RTrelW (operB c (numBT n)) := hop n
      have otn : operB c (numBT n) ∈ OT_B := buchholz_fseq_closed c n cOT cne
      simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hn
      rcases hn with hlt | heq
      · exact accn.inv (RTrelW_iff.mpr ⟨bOT, otn, hlt⟩)
      · rw [heq]; exact accn
    · -- (tu) `dom c = T_m`: `W_m` 内の引数で共終
      have cne : c ≠ BZero := by
        intro h
        rw [h, bwo_domB_Nil] at hd
        exact TBv_ne_empty_wfe m hd.symm
      refine Acc.intro c ?_
      intro b hb
      obtain ⟨bOT, _, hlb⟩ := RTrelW_iff.mp hb
      obtain ⟨otb, dfb⟩ := memOTB_wfe.mp bOT
      obtain ⟨_, cof2⟩ := bwl_cof_wfe otc dfc otb dfb hlb
      obtain ⟨z, zW, zd, otz, dfz, hn⟩ := cof2 m hd
      have accz : Acc RTrelW (operB c z) := hop z zW
      have hcl := buchholz_fseq_closed_general c z otc dfc cne (Or.inl zd) otz dfz
      have otz' : operB c z ∈ OT_B := memOTB_wfe.mpr ⟨hcl.1, hcl.2⟩
      simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hn
      rcases hn with hlt | heq
      · exact accz.inv (RTrelW_iff.mpr ⟨bOT, otz', hlt⟩)
      · rw [heq]; exact accz
  · -- `c ∉ OT_B`: `RTrel`-前者が存在しない
    refine Acc.intro c ?_
    intro y hy
    obtain ⟨_, cOT, _⟩ := RTrelW_iff.mp hy
    exact absurd (memOTB_wfe.mp cOT) hOT

/-! ## 4. 全項の `acc`（Isabelle `bwl_Wstar_total_of_cof` → `bwo_2_2_wf` の短絡）

`D_ω`-free な項は `y3_dfree_W_ex`（11382）でどれかの `W_m` に属し、§3 の橋で `acc`。
`D_ω`-free でない項は `T_B` に属さない＝`OT_B` に属さないので `RTrel`-前者が無く、
やはり `acc`。 -/

private theorem acc_all_wfe (t : BT) : Acc RTrelW t := by
  by_cases hdf : dfree_BT t = true
  · obtain ⟨m, hm⟩ := y3_dfree_W_ex Bwl28Principal_holds Bwl24bAdd_holds hdf
    exact acc_of_W_wfe m hm
  · refine Acc.intro t ?_
    intro y hy
    obtain ⟨_, tOT, _⟩ := RTrelW_iff.mp hy
    exact absurd (memOTB_wfe.mp tOT).2 hdf

/-! ## 5. [Buc1] 補題 2.2 -/

/-- **[Buc1] 補題 2.2**: `(OT_B, <)` は整礎である。

Isabelle: `y4_buc1_2_2_OT_B_wf : wf {(a, b). a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b}`
(isabelle/layerC/pss_scratch.thy:13700)。Isabelle の `(x,y) ∈ r` は「`x` が小さい」
なので Lean の `WellFounded` の引数順と一致する。

`lean/8/8.7-OT-tail-annihilable.lean:52` の名前付き仮定 `OT_B_wf` と型が一致する。 -/
theorem buchholz_wf :
    WellFounded (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true) :=
  WellFounded.intro acc_all_wfe

#print axioms buchholz_wf

end PSS
