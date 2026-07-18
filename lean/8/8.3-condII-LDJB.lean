import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-R3LE»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»
import «6».«6.5-Red-le-core»
import «6».«6.6-reduced-iff-condAB»

/-!
# §8.3 条件(II) — `TV_LDJB`（`ljx_LDJB`）: `ldj` 境界の exactness

## 目的

ビルド済み «8».«8.3-condII-masterCF-port»:148 の名前付き残差 `TV_LDJB`
（`CondII_masterCF` の tailval 連鎖 6 本のうちの 1 本）を Isabelle
`ljx_LDJB`（layerB/pss_wip.thy:115131）の証明構造で閉じる。

`ldj` 分岐で `Br R_c ≠ []` かつ `d ≤ j_L` のとき、境界が **exact**（`d = j_L`）で
かつ最終 first node の対角が **strict**（`entry R_c 1 fn < entry R_c 0 fn`）になる。

## Isabelle 対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `ljx_LDJB` | layerB/pss_wip.thy:115131 | `TV_LDJB_of_readouts`（`TV_LDJB` を drop-in、5 残差 modulo） |
| `ljx_RightNodes_pj_ldj` | layerB/pss_wip.thy:114535 | 🤖 `RN_ldj_pj_ldjb` |
| `ljx_RightNodes_a0_trmax` | layerB/pss_wip.thy:114607 | 🤖 `RN_a0_trmax_ldjb` |
| `ljx_RightNodes_a0_lt_trmax` | layerB/pss_wip.thy:114847 | 🤖 `RN_a0_lt_trmax_ldjb` |
| `pos1ldj`(内, `wnx_run_entries`+`repr_entry1_shift_gen`) | layerB:115180 | 🤖 `TVX_pos1ldj_ldjb` |
| `tvx_d_lt_TrMax` | layerB/pss_wip.thy:110442 | 🤖 `TVX_dstrict_ldjb` |
| `tvx_fn_row_bound` | layerB/pss_wip.thy:110857 | ✅ `TV_R3LE_holds`（«8».«8.3-condII-R3LE» で無条件済、再利用） |
| `c2sx_reach`(leab) | layerB/pss_wip.thy:87668 | private `condII_reach_ldjb`（R3LE の `condII_reach_r3` の複製） |

## 証明構造（`ljx_LDJB` の逐語移植）

1. `R_c = tvx_Rc K` は `DT_PS`（`standard_slice_Red_strongmono`）→ `RT_PS`/`monoT`/`TPS`/
   `RedCondA`。到達性 `leab` は `condII_reach_ldjb`（値特徴付けで `Marked_Pred_Adm` 経由）。
2. `d > 0`（`condII_host_basic` clause 5: `Adm K j₀ < j₀`）、`j_L > 0`（`d ≤ j_L`）。
3. `j_L ≤ TrMax R_c`（`FirstNodes_TrMax_Joints`）、
   `offsJ : entry R_c 1 j_L = entry R_c 1 0 + j_L`（`trunk_entries_offset`）。
4. 位置1の `ldj` 側読み出し `L1`（`RN_ldj_pj_ldjb`）と、その値 `pos1ldj`
   （`TVX_pos1ldj_ldjb`: `entry K 1 j₀ = entry R_c 1 0 + d`）。
5. `dstrict : d < TrMax R_c`（`TVX_dstrict_ldjb`）。
6. `j_L = TrMax R_c` で場合分け:
   * `=` ⇒ `RN_a0_trmax_ldjb` の読み出しと `L1` の突き合わせで `d = j_L`、`dstrict` と矛盾（空虚）。
   * `<` ⇒ `RN_a0_lt_trmax_ldjb` の二分岐: (g) 位置1 = `entry R_c 1 j_L` かつ非対角
     ⇒ `d = j_L` ＋ `TV_R3LE_holds`（`entry R_c 1 fn ≤ entry R_c 0 fn`）で strict。
     (v) 位置1 = `entry R_c 1 j_L + 1` ⇒ `d = j_L + 1`、`d ≤ j_L` と矛盾（空虚）。

## 依存（すべて COMMITTED 緑）

* «8».«8.3-condII-masterCF-port» — `TV_LDJB` / `tvx_Rc` / `tvx_d` / `tvx_jL` / `tvx_fn` /
  `STPS_RTPS` ＋推移的に `condII_host_basic_holds` / `condII_ldj` / `transCondII`。
* «8».«8.3-condII-R3LE» — `TV_R3LE_holds`（= `tvx_fn_row_bound`、無条件）を再利用。
* «6».«6.4-FirstNodes-TrMax-Joints» — `FirstNodes_TrMax_Joints`。
* «8».«8.2-standard-slice-Red-strongmono» — `standard_slice_Red_strongmono` / `DTPS_iff` /
  `DTPS_TPS`。
* «6».«6.5-Red-le-core» — `trunk_entries_offset`。
* «6».«6.6-reduced-iff-condAB» — `RTPS_condAB`。
* 私的（`_ldjb`）: `condII_reach_ldjb`（R3LE の `condII_reach_r3` の逐語複製、private は
  module 跨ぎ不可のため再掲）。土台 = `parent_exists_3` / `ancestor_basic_1` /
  `entry_Pred` / `length_Pred`（すべて公開）。

## 状態

* ⚠️ `TV_LDJB` は本ファイルでは**無条件には未閉**。Isabelle の証明が依存する 5 本の
  campaign-size 補題を名前付き残差として露出し、その上の**組み立て（`ljx_LDJB` の骨格）**
  を無条件に閉じた還元定理 `TV_LDJB_of_readouts` を green で bank する。
* 🤖 露出残差（すべて Isabelle では**定理**、`needs` に報告）:
  `RN_ldj_pj_ldjb` / `RN_a0_trmax_ldjb` / `RN_a0_lt_trmax_ldjb`（RightNodes の位置1構造
  読み出し。Buchholz 項 `Dpt`/`transT2`/`PB`/`bpHeadV` レベルの未移植機構＝
  `wnx_seg_transport`/`c2sx_slice_jm1_c1` に依存）、`TVX_pos1ldj_ldjb`（`wnx_run_entries`
  ＋`repr_entry1_shift_gen`、未移植）、`TVX_dstrict_ldjb`（`tvx_d_lt_TrMax`、`tvx_run_nadm_Rc`
  に依存、未移植）。
-/

namespace PSS

/-! ## 露出した campaign-size 残差 `Prop`（Isabelle 名 1:1）

いずれも Isabelle では**定理**であって空虚な仮定ではない。仮定束は Isabelle 側の
`ljx_RightNodes_*` / `tvx_d_lt_TrMax` と文字単位で一致（`M ∈ RT_PS` → `RTPS M`、
`M ∈ PT_PS` → `monoT M = true`（`RTPS M ⟹ TPS M`）、`c2sx_ldj M` → `condII_ldj M = true`）。 -/

/-- Isabelle `ljx_RightNodes_pj_ldj` (pss_wip.thy:114535): `ldj` 側の `RightNodes`
位置1読み出し（`Trans R_c` の第2成分が `entry K 1 j₀`）。 -/
def RN_ldj_pj_ldjb : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    condII_ldj M = true →
    ∃ rest, RightNodes (Trans (tvx_Rc M))
      = entry (tvx_Rc M) 1 0 :: entry M 1 (parent M 0 (Lng M - 1)) :: rest

/-- Isabelle `ljx_RightNodes_a0_trmax` (pss_wip.thy:114607): `j_L = TrMax R_c` の場合、
`RightNodes (Trans R_c)` の第2成分は `entry R_c 1 j_L`（対角プレフィックス分解）。 -/
def RN_a0_trmax_ldjb : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    Br (tvx_Rc M) ≠ [] → 0 < tvx_jL M → tvx_jL M = TrMax (tvx_Rc M) →
    ∃ a1, RightNodes (Trans (tvx_Rc M))
      = entry (tvx_Rc M) 1 0 :: entry (tvx_Rc M) 1 (tvx_jL M) :: a1

/-- Isabelle `ljx_RightNodes_a0_lt_trmax` (pss_wip.thy:114847): `j_L < TrMax R_c` の場合、
位置1は `entry R_c 1 j_L`（非対角付き）か `entry R_c 1 j_L + 1`（cond V 側で対角排除）。 -/
def RN_a0_lt_trmax_ldjb : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    Br (tvx_Rc M) ≠ [] → 0 < tvx_jL M → tvx_jL M < TrMax (tvx_Rc M) →
    (∃ a1, RightNodes (Trans (tvx_Rc M))
        = entry (tvx_Rc M) 1 0 :: entry (tvx_Rc M) 1 (tvx_jL M) :: a1
        ∧ entry (tvx_Rc M) 1 (tvx_fn M) ≠ entry (tvx_Rc M) 0 (tvx_fn M))
    ∨ (∃ a1, RightNodes (Trans (tvx_Rc M))
        = entry (tvx_Rc M) 1 0 :: (entry (tvx_Rc M) 1 (tvx_jL M) + 1) :: a1)

/-- Isabelle `ljx_LDJB` 内の `pos1ldj` (pss_wip.thy:115180、`wnx_run_entries`
＋`repr_entry1_shift_gen`): `ldj` 側の位置1値 `entry K 1 j₀ = entry R_c 1 0 + d`。 -/
def TVX_pos1ldj_ldjb : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    condII_ldj M = true →
    entry M 1 (parent M 0 (Lng M - 1)) = entry (tvx_Rc M) 1 0 + tvx_d M

/-- Isabelle `tvx_d_lt_TrMax` (pss_wip.thy:110442): 非許容 run の長さ `d` は幹長 `TrMax R_c`
より真に短い（境界 strictness）。 -/
def TVX_dstrict_ldjb : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    tvx_d M < TrMax (tvx_Rc M)

/-! ## 到達性脚 `leab`（R3LE `condII_reach_r3` の複製、private は module 跨ぎ不可） -/

/-- Isabelle `c2sx_reach`(1) の `leab` 脚。R3LE の `condII_reach_r3` を逐語複製。
`Pred K` の基点性から `parent_exists_3` の値特徴付け（`ancestor_basic_1`＋`entry_Pred`）で
`le0`（したがって `leR`）を構成する。 -/
private theorem condII_reach_ldjb (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
    (hmk : Marked (Pred K) a) (hab : a < Lng K - 2) :
    leR K 0 a (Lng K - 2) = true := by
  have hKT : TPS K := RTPS_TPS K hKR
  have hpredT : TPS (Pred K) := hmk.1
  have hpl : Lng (Pred K) = Lng K - 1 := length_Pred K hL
  have hle0P : leR (Pred K) 0 a (Lng (Pred K) - 1) = true := hmk.2.2
  have hidx : Lng (Pred K) - 1 = Lng K - 2 := by omega
  rw [hidx] at hle0P
  have hLK2 : Lng K - 2 < Lng K := by omega
  apply parent_exists_3 K a (Lng K - 2) hKT hab hLK2
  intro j hlo hhi
  have hgrowPred : entry (Pred K) 0 a < entry (Pred K) 0 j :=
    ancestor_basic_1 (Pred K) a j (Lng K - 2) hpredT hlo hhi hle0P
  have haLt : a < Lng K - 1 := by omega
  have hjLt : j < Lng K - 1 := by omega
  rw [entry_Pred K 0 a haLt, entry_Pred K 0 j hjLt] at hgrowPred
  exact hgrowPred

/-! ## `ljx_LDJB` の組み立て（house pattern で `TV_LDJB` を drop-in） -/

/-- Isabelle `ljx_LDJB` (pss_wip.thy:115131) の 1:1 移植。露出した 5 本の campaign-size
残差から `TV_LDJB`（«8».«8.3-condII-masterCF-port»:148）を drop-in で充足する。
`tvx_fn_row_bound` は `TV_R3LE_holds`（無条件済）で threading 済み。 -/
theorem TV_LDJB_of_readouts
    (hpj : RN_ldj_pj_ldjb) (htrm : RN_a0_trmax_ldjb) (hlt : RN_a0_lt_trmax_ldjb)
    (hpos1 : TVX_pos1ldj_ldjb) (hdstrict : TVX_dstrict_ldjb) :
    TV_LDJB := by
  intro K hST hmono hj1 hII hldj hBR hdle
  have hKR : RTPS K := STPS_RTPS K hST
  have hKT : TPS K := RTPS_TPS K hKR
  have hL : 1 < Lng K := by omega
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds K hKR hmono hj1 hII
  -- 到達性 `leab`（R3LE 同型）
  have hab : Adm K (parent K 0 (Lng K - 1)) < Lng K - 2 := by omega
  have hmk : Marked (Pred K) (Adm K (parent K 0 (Lng K - 1))) :=
    Marked_Pred_Adm K hKT hL hp0
  have leab : leR K 0 (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2) = true :=
    condII_reach_ldjb K (Adm K (parent K 0 (Lng K - 1))) hKR hL hmk hab
  have hbL2 : Lng K - 2 ≤ Lng K - 1 := by omega
  -- `R_c = tvx_Rc K` の `DT_PS`／`RT_PS`／`monoT`／`TPS`／`RedCondA`
  have hRcDT : DTPS (tvx_Rc K) :=
    standard_slice_Red_strongmono K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2)
      hST hab hbL2 leab
  have hRcRT : RTPS (tvx_Rc K) := ((DTPS_iff (tvx_Rc K)).mp hRcDT).1
  have hmonoRc : monoT (tvx_Rc K) = true := ((DTPS_iff (tvx_Rc K)).mp hRcDT).2.1
  have hRcT : TPS (tvx_Rc K) := DTPS_TPS (tvx_Rc K) hRcDT
  have hcondARc : RedCondA (tvx_Rc K) = true := (RTPS_condAB (tvx_Rc K) hRcRT).1
  -- 最終枝インデックス `BL` と `j_L ≤ TrMax R_c`
  have hBLlt : (Br (tvx_Rc K)).length - 1 < (Br (tvx_Rc K)).length := by
    have hposBr := List.length_pos_of_ne_nil hBR
    omega
  have hjle : tvx_jL K ≤ TrMax (tvx_Rc K) :=
    (FirstNodes_TrMax_Joints (tvx_Rc K) ((Br (tvx_Rc K)).length - 1) hRcT hmonoRc hBLlt).1
  -- `offsJ : entry R_c 1 j_L = entry R_c 1 0 + j_L`
  have hoffJ : entry (tvx_Rc K) 1 (tvx_jL K) = entry (tvx_Rc K) 1 0 + tvx_jL K :=
    (trunk_entries_offset (tvx_Rc K) hRcT hcondARc (tvx_jL K) hjle).2
  -- `d > 0`, `j_L > 0`
  have hdpos : 0 < tvx_d K := by unfold tvx_d; omega
  have hjpos : 0 < tvx_jL K := by omega
  -- ブリック `pos1ldj` と `dstrict`
  have hpos1ldj : entry K 1 (parent K 0 (Lng K - 1)) = entry (tvx_Rc K) 1 0 + tvx_d K :=
    hpos1 K hKR hmono hj1 hII hldj
  have hdstr : tvx_d K < TrMax (tvx_Rc K) :=
    hdstrict K hKR hmono hj1 hII
  -- `ldj` 側読み出し `L1`
  obtain ⟨rest, hL1⟩ := hpj K hKR hmono hj1 hII hldj
  -- `j_L = TrMax R_c` で場合分け
  by_cases hjeq : tvx_jL K = TrMax (tvx_Rc K)
  · -- `=`: 読み出しの突き合わせで `d = j_L`、`dstrict` と矛盾（空虚）
    obtain ⟨a1, hS⟩ := htrm K hKR hmono hj1 hII hBR hjpos hjeq
    have hcat := hL1.symm.trans hS
    simp only [List.cons.injEq] at hcat
    have heqd : entry K 1 (parent K 0 (Lng K - 1)) = entry (tvx_Rc K) 1 (tvx_jL K) :=
      hcat.2.1
    have hdeq : tvx_d K = tvx_jL K := by omega
    exfalso; omega
  · -- `<`: 二分岐
    have hjlt : tvx_jL K < TrMax (tvx_Rc K) := lt_of_le_of_ne hjle hjeq
    rcases hlt K hKR hmono hj1 hII hBR hjpos hjlt with
      ⟨a1, hS, hne⟩ | ⟨a1, hV⟩
    · -- (g): 位置1 = `entry R_c 1 j_L` かつ非対角 ⇒ `d = j_L` ＋ strict
      have hcat := hL1.symm.trans hS
      simp only [List.cons.injEq] at hcat
      have heqd : entry K 1 (parent K 0 (Lng K - 1)) = entry (tvx_Rc K) 1 (tvx_jL K) :=
        hcat.2.1
      have hdeq : tvx_d K = tvx_jL K := by omega
      have hlefn : entry (tvx_Rc K) 1 (tvx_fn K) ≤ entry (tvx_Rc K) 0 (tvx_fn K) :=
        TV_R3LE_holds K hST hmono hj1 hII hBR
      exact ⟨hdeq, lt_of_le_of_ne hlefn hne⟩
    · -- (v): 位置1 = `entry R_c 1 j_L + 1` ⇒ `d = j_L + 1`、`d ≤ j_L` と矛盾（空虚）
      have hcat := hL1.symm.trans hV
      simp only [List.cons.injEq] at hcat
      have heqd : entry K 1 (parent K 0 (Lng K - 1))
          = entry (tvx_Rc K) 1 (tvx_jL K) + 1 := hcat.2.1
      exfalso; omega

#print axioms TV_LDJB_of_readouts

end PSS
