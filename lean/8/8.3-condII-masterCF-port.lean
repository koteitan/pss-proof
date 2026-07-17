import «8».«8.3-condII-step»

/-!
# §8.3 条件(II) — `CondII_masterCF` の drop-in ポート（`tvx_` 還元）

## 目的

ビルド済み «8».«8.3-TransCondII-engine»:219 の `CondII_masterCF`（**`STPS` 形**）を
house pattern で充足することを目指し、残差を Isabelle の実在チェーンに 1:1 で
対応する**名前付き 6 本**へ還元する。

## Isabelle 側の対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `y3j_condII_tailval` | layerC/pss_scratch.thy:17076 | `CondII_TailvalAll_ST`（«8».«8.3-condII-masterCF»:702） |
| `ljx_TVall_of_fin` | layerB/pss_wip.thy:115242 | `TailvalAll_ST_of_residuals_cm2` |
| `tvx_TVall_of_LDJB_fin` | layerB/pss_wip.thy:110943 | 同上 |
| `tvx_TVall_of_residuals` | layerB/pss_wip.thy:110706 | 同上（**本ファイルの主内容**） |
| `ot9_FINRC` | layerC/pss_scratch.thy:10032 | ✅ `tvx_finRc_holds`（**無条件で証明**） |
| `cdx_d_le_joints` | layerB/pss_wip.thy:90230 | 🤖 `TV_Dichotomy` |
| `c2sx_tailval_trunk` | layerB/pss_wip.thy:87720 | 🤖 `TV_TrunkLeg` |
| `tvx_tailval_of_boundary` | layerB/pss_wip.thy:110527 | 🤖 `TV_BoundaryLeg` |
| `cdx_tailval_notldj` | layerB/pss_wip.thy:90415 | 🤖 `TV_NotLdjLeg` |
| `ljx_LDJB` | layerB/pss_wip.thy:115131 | 🤖 `TV_LDJB` |
| `tvx_fn_row_bound` | layerB/pss_wip.thy:110857 | 🤖 `TV_R3LE` |

`Lng` は Isabelle では `'a list ⇒ nat`（多相 length, pss_defs.thy:36）だが Lean では
`PS → ℕ` なので、`Lng (Br X)` は `(Br X).length` と綴る。`Isabelle の ! は .getD`。

## 依存

* «8».«8.3-condII-step» — `condII_step_holds`（`CondII_step` ✅ 無条件）
  ＋ 推移的に «8».«8.3-condII-masterCF»（`CondII_TailvalAll_ST` / `condII_masterCF_holds`）
  ＋ «8».«8.3-TransCondII-engine»（`CondII_masterCF` / `exchII_of_masterCF`）

## 状態

* ✅ `tvx_finRc_holds` … **無条件**（Isabelle `ot9_FINRC` の 1:1。`nth` 由来の
  `fin` 人工物は `J < (Br _).length` から `Set.finite_Iio` の部分集合で落ちる）。
* 🤖 `TailvalAll_ST_of_residuals_cm2` … 残差 **6 本**
  （`TV_Dichotomy`/`TV_TrunkLeg`/`TV_BoundaryLeg`/`TV_NotLdjLeg`/`TV_LDJB`/`TV_R3LE`）。
  `FINRC` は**スレッド済み**＝Isabelle の 3 残差 `{LDJB, R3LE, FINRC}` のうち
  `FINRC` は本ファイルで消えている。
* 🤖 `condII_masterCF_of_residuals_cm2` … 同 6 本から `CondII_masterCF` を drop-in。

🚨 **`CondII_masterCF` は本ファイルでは無条件には閉じていない**（残差 6 本）。
Isabelle 側の未移植量は `tvx_`/`cdx_`/`ljx_`/`wnx_`/`hqx_`/`dkax_` 連鎖で ~3200 行あり、
1 ラウンドでは入らない。`c2sx_` 部（~800 行）は «8».«8.3-condII-step» で移植済み。

🚨 **RT_PS 形は偽**（«8».«8.3-condII-tailval» の `not_CondII_masterCF_RTPS_form`）。
本ファイルは一貫して `STPS` 形のみを扱う。Isabelle の `y3j_condII_tailval` も
`M ∈ ST_PS` 束縛であって `RT_PS` ではない。
-/

namespace PSS

/-! ## `tvx_` の境界データ（Isabelle pss_wip.thy:110652-110690） -/

/-- Isabelle `tvx_Rc` (pss_wip.thy:110652): 条件(II) ホストの**簡約された祖先切片**。 -/
def tvx_Rc (K : PS) : PS :=
  Red (seg K (Adm K (parent K 0 (Lng K - 1))) (Lng K - 2))

/-- Isabelle `tvx_d` (pss_wip.thy:110656): 非許容 run の長さ。 -/
def tvx_d (K : PS) : ℕ :=
  parent K 0 (Lng K - 1) - Adm K (parent K 0 (Lng K - 1))

/-- Isabelle `tvx_jL` (pss_wip.thy:110659): `R_c` の最後の枝成分の joint。 -/
def tvx_jL (K : PS) : ℕ :=
  (Joints (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0

/-- Isabelle `tvx_fn` (pss_wip.thy:110662): `R_c` の最後の枝成分の first node。 -/
def tvx_fn (K : PS) : ℕ :=
  (FirstNodes (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) 0

/-- Isabelle `tvx_finRc` (pss_wip.thy:110675): `LastStep` の `Min`-集合の有限性を
`R_c` で instantiate したもの（`hqx_condIIIV_of_DT` の `fin` 側条件）。

Isabelle の注記どおり、これは**全称 `J` の total-`nth` 人工物**であって、ホスト側の
`fin` からは出ない。しかし `J < (Br R_c).length` という**合併子が集合の中にある**ので、
`{..< (Br R_c).length}` の部分集合として無条件に有限（＝`ot9_FINRC`）。 -/
def tvx_finRc (K : PS) : Prop :=
  {J : ℕ | J < (Br (tvx_Rc K)).length ∧
      entry ((Br (tvx_Rc K)).getD ((Br (tvx_Rc K)).length - 1) []) 0 0
        = entry ((Br (tvx_Rc K)).getD J []) 0 0 ∧
      entry ((Br (tvx_Rc K)).getD J []) 1 0
        < entry ((Br (tvx_Rc K)).getD J []) 0 0}.Finite

/-! ## `ot9_FINRC` (layerC/pss_scratch.thy:10032) — ✅ 無条件

Isabelle:
```
lemma ot9_FINRC: "tvx_finRc K"
  unfolding tvx_finRc_def
  by (rule finite_subset[of _ "{..< Lng (Br (tvx_Rc K))}"]) auto
```
Lean でもそのまま: `Set.finite_Iio` の部分集合。 -/

/-- Isabelle `ot9_FINRC` (layerC/pss_scratch.thy:10032) の **1:1** 移植。
Isabelle 側で `FINRC` census slot を DISCHARGE した capstone (r69) と同じ内容。 -/
theorem tvx_finRc_holds (K : PS) : tvx_finRc K :=
  Set.Finite.subset (Set.finite_Iio (Br (tvx_Rc K)).length)
    (fun _ hJ => hJ.1)

/-! ## 露出した残差 `Prop`（Isabelle 名 1:1）

いずれも Isabelle では**定理**であって空虚な仮定ではない（＝`CondII_masterCF` は
`STPS` 形では真である）。仮定束は Isabelle 側と文字単位で一致させてある:
`M ∈ ST_PS` → `STPS M`、`M ∈ PT_PS` → `monoT M = true`（`PT_PS = T_PS ∧ monoT`,
pss_defs.thy:240。`STPS M ⟹ TPS M` なので `T_PS` 側は自動）。 -/

/-- Isabelle `cdx_d_le_joints` (pss_wip.thy:90230)。`R_c` は**幹**であるか、
さもなくば枝を持ち `d ≤ Joints!last` が成り立つ、という二分岐。 -/
def TV_Dichotomy : Prop :=
  ∀ K : PS, STPS K → monoT K = true → 1 < Lng K - 1 → transCondII K = true →
    TrMax (tvx_Rc K) = Lng (tvx_Rc K) - 1 ∨
      (Br (tvx_Rc K) ≠ [] ∧ tvx_d K ≤ tvx_jL K)

/-- Isabelle `c2sx_tailval_trunk` (pss_wip.thy:87720)。幹の場合の `tailval`。
🚨 あちらの仮定は `MR : M ∈ RT_PS`（`ST_PS` ではない）なので `RTPS` で述べる。 -/
def TV_TrunkLeg : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    TrMax (tvx_Rc M) = Lng (tvx_Rc M) - 1 →
    CondII_tailval M

/-- Isabelle `tvx_tailval_of_boundary` (pss_wip.thy:110527)。境界が exact
（`d = jL`）かつ guard が成り立つときの `tailval`（結論 (1)）と `ldj`（結論 (2)）。
`FIN` 仮定は Isabelle と 1:1 に残してあるが、使用側では `tvx_finRc_holds` で
**無条件に落ちる**。 -/
def TV_BoundaryLeg : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    Br (tvx_Rc M) ≠ [] →
    tvx_d M = tvx_jL M →
    entry (tvx_Rc M) 1 (tvx_fn M) < entry (tvx_Rc M) 0 (tvx_fn M) →
    tvx_finRc M →
    CondII_tailval M ∧ condII_ldj M = true

/-- Isabelle `cdx_tailval_notldj` (pss_wip.thy:90415)。`¬ ldj` の場合の `tailval`
（`DIAG` 入力つき）。 -/
def TV_NotLdjLeg : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    condII_ldj M = false →
    (Br (tvx_Rc M) ≠ [] → tvx_d M = tvx_jL M →
      entry (tvx_Rc M) 0 (tvx_fn M) = entry (tvx_Rc M) 1 (tvx_fn M)) →
    CondII_tailval M

/-- Isabelle `ljx_LDJB` (pss_wip.thy:115131)。`ldj` 境界の exactness。 -/
def TV_LDJB : Prop :=
  ∀ K : PS, STPS K → monoT K = true → 1 < Lng K - 1 → transCondII K = true →
    condII_ldj K = true → Br (tvx_Rc K) ≠ [] → tvx_d K ≤ tvx_jL K →
    tvx_d K = tvx_jL K ∧
      entry (tvx_Rc K) 1 (tvx_fn K) < entry (tvx_Rc K) 0 (tvx_fn K)

/-- Isabelle `tvx_fn_row_bound` (pss_wip.thy:110857)。最後の first node での行境界。 -/
def TV_R3LE : Prop :=
  ∀ K : PS, STPS K → monoT K = true → 1 < Lng K - 1 → transCondII K = true →
    Br (tvx_Rc K) ≠ [] →
    entry (tvx_Rc K) 1 (tvx_fn K) ≤ entry (tvx_Rc K) 0 (tvx_fn K)

/-! ## `tvx_TVall_of_residuals` (pss_wip.thy:110706) — 場合分けの解剖

Isabelle の構造をそのまま:
1. `cdx_d_le_joints` で trunk / branched に二分。
2. trunk ⇒ `c2sx_tailval_trunk`。
3. branched + `ldj` ⇒ `LDJB` で境界を exact 化 → `tvx_tailval_of_boundary`(1)。
4. branched + `¬ ldj` ⇒ `cdx_tailval_notldj`。その `DIAG` 入力はここで**放電**する:
   guard が成り立てば `tvx_tailval_of_boundary`(2) が `ldj` を出して `¬ ldj` と矛盾
   （空虚）、guard が破れれば `R3LE` が対角を強制する。 -/

/-- Isabelle `tvx_TVall_of_residuals` (pss_wip.thy:110706) ＋ `tvx_TVall_of_LDJB_fin`
(110943) ＋ `ljx_TVall_of_fin` (115242) の合成 = `y3j_condII_tailval`
(layerC/pss_scratch.thy:17076) の Lean 形。

`FINRC` は `tvx_finRc_holds` で**スレッド済み**＝Isabelle の 3 残差
`{LDJB, R3LE, FINRC}` のうち `FINRC` はここで消えている。 -/
theorem TailvalAll_ST_of_residuals_cm2
    (hDich : TV_Dichotomy) (hTrunk : TV_TrunkLeg) (hBd : TV_BoundaryLeg)
    (hNot : TV_NotLdjLeg) (hLDJB : TV_LDJB) (hR3LE : TV_R3LE) :
    CondII_TailvalAll_ST := by
  intro K hST hmono hj1 hcond
  have hR : RTPS K := STPS_RTPS K hST
  -- `FINRC` は無条件（`ot9_FINRC`）
  have hFin : tvx_finRc K := tvx_finRc_holds K
  rcases hDich K hST hmono hj1 hcond with htrunk | ⟨hBrne, hdle⟩
  · -- trunk
    exact hTrunk K hR hmono hj1 hcond htrunk
  · -- branched
    cases hldj : condII_ldj K with
    | true =>
      obtain ⟨hDEQ, hGUARD⟩ := hLDJB K hST hmono hj1 hcond hldj hBrne hdle
      exact (hBd K hST hmono hj1 hcond hBrne hDEQ hGUARD hFin).1
    | false =>
      refine hNot K hST hmono hj1 hcond hldj ?_
      -- `DIAG` の放電
      intro _hBr hdeq
      by_cases hg : entry (tvx_Rc K) 1 (tvx_fn K) < entry (tvx_Rc K) 0 (tvx_fn K)
      · -- guard が成り立つ ⇒ `ldj`（境界 (2)）で `¬ ldj` と矛盾（空虚）
        have : condII_ldj K = true :=
          (hBd K hST hmono hj1 hcond hBrne hdeq hg hFin).2
        rw [hldj] at this; exact absurd this (by simp)
      · -- guard が破れる ⇒ `R3LE` が対角を強制
        have hle : entry (tvx_Rc K) 1 (tvx_fn K) ≤ entry (tvx_Rc K) 0 (tvx_fn K) :=
          hR3LE K hST hmono hj1 hcond hBrne
        omega

/-! ## `CondII_masterCF` の drop-in（house pattern）

ビルド済み «8».«8.3-condII-masterCF»:710 の `condII_masterCF_holds` に、
✅ 無条件の `condII_step_holds`（«8».«8.3-condII-step»:1010）と上の
`TailvalAll_ST_of_residuals_cm2` を食わせる。 -/

/-- ビルド済み «8».«8.3-TransCondII-engine»:219 の `CondII_masterCF` を、
`tvx_` 残差 **6 本**から drop-in で充足する（`CondII_step` と `FINRC` は
既に無条件に閉じているので現れない）。 -/
theorem condII_masterCF_of_residuals_cm2
    (hDich : TV_Dichotomy) (hTrunk : TV_TrunkLeg) (hBd : TV_BoundaryLeg)
    (hNot : TV_NotLdjLeg) (hLDJB : TV_LDJB) (hR3LE : TV_R3LE) :
    CondII_masterCF :=
  condII_masterCF_holds condII_step_holds
    (TailvalAll_ST_of_residuals_cm2 hDich hTrunk hBd hNot hLDJB hR3LE)

/-- 親による独立検証用: 上の 6 残差から `FseqDesc_exchII` が実際に落ちること
（`exchII_of_masterCF` はビルド済み engine :231）。 -/
theorem condII_exchII_of_residuals_cm2
    (hDich : TV_Dichotomy) (hTrunk : TV_TrunkLeg) (hBd : TV_BoundaryLeg)
    (hNot : TV_NotLdjLeg) (hLDJB : TV_LDJB) (hR3LE : TV_R3LE) :
    FseqDesc_exchII :=
  exchII_of_masterCF
    (condII_masterCF_of_residuals_cm2 hDich hTrunk hBd hNot hLDJB hR3LE)

#print axioms tvx_finRc_holds
#print axioms TailvalAll_ST_of_residuals_cm2
#print axioms condII_masterCF_of_residuals_cm2
#print axioms condII_exchII_of_residuals_cm2

end PSS
