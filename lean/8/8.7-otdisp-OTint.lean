import «8».«8.7-Trans-preserves-OT»

/-!
# §8.7 `OTdisp_OTint` — no-parent 隅の discharge と III/IV/V 分解

- Isabelle: `oix_OTint_slot2` (`layerB/pss_wip.thy`:112196) が
  `OTdisp_OTint` と**逐語一致**する slot（`otx_Trans_preserves_OT_dispatch`
  (:85710) の仮定 `OTint`）。その 4 分岐:
  III → `oi8_OTint_condIII` (`layerC/pss_scratch.thy`:3716)、
  IV → `oi8_OTint_condIV` (:3774)、
  V-adm → `oix_OTint_condV_adm` (`layerB/pss_wip.thy`:111599)、
  V-nadm → `oix_OTint_condV_nadm` (:112041)。
- 本ファイルが移植したのは `oi8_OTint_condIII` / `oi8_OTint_condIV` の
  `proof (cases "hasParent N 1 (Lng N - 1)")` の **`False` 側**＝ no-parent 隅:
  `npx_oper_noParent_Pred` (`layerB/pss_wip.thy`:101281) で `N[m] = Pred N` に
  潰し、`Pred` の OT 所属を取る。
  Isabelle は condIII 側で `npx_operB_numBT0_Pred_condIII` (:101500)、condIV 側で
  `ot2_IVNP` (`layerC/pss_scratch.thy`:2627) と別ルートを踏むが、`ot2_IVNP` の実体は
  `od4_OTpred_final` (:874)＝**仮定なしの強 OTpred**（`N ∈ ST_PS`,
  `Trans N ∈ OT_B`, `1 < Lng N` のみ）である。本ファイルはこの観察を使い、
  **III/IV/V の 3 条件すべての no-parent 隅を 1 本の OTpred 呼び出しに統一する**
  （condIII/IV/V はいずれも `0 < N_{1,j₁}` を含むので `npx_oper_noParent_Pred` の
  前提が揃い、かつ条件 (I)/(VI) を排除するので既存の葉 `OTdisp_OTpred` の
  3 つの corner exclusion がそのまま成立する）。
  ⇒ **新しい残差を増やさずに** `OTdisp_OTint` を `hasParent` 付きに弱められる。
- 依存（ビルド済みのみ import）: `8.7-Trans-preserves-OT`
  （`OTdisp_OTint` / `OTdisp_OTpred` の定義元）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `OTdisp_OTint` は**無条件には閉じていない**。本ファイルの成果は
  `OTdisp_OTint_of_hasParent`: 残差 1 本 `OTint_hasParent`（＝`OTdisp_OTint` に
  `hasParent N 1 (Lng N - 1)` を足しただけの**真に弱い**言明）＋既存の葉
  `OTdisp_OTpred` から `OTdisp_OTint` を出す。残差本数は増えない。
  さらに `OTint_hasParent_of_legs` で Isabelle の 4 分岐に割る選択肢も提供する
  （こちらは残差 1 → 4 になるので、並列に攻めたい時だけ使う）。
-/

namespace PSS

/-! ## 1. 残差 `Prop`

`OTdisp_OTint` に `hasParent N 1 (Lng N - 1)` を加えただけのもの。Isabelle 側では
`oi8_OTint_condIII` / `oi8_OTint_condIV` の `True` 枝（`oi8_OTint_IIIIV_hp`
(`layerC/pss_scratch.thy`:3432) 経由）と `oix_OTint_condV_adm` /
`oix_OTint_condV_nadm` がそのまま供給する（いずれも `hasParent` を課しても真）。 -/

/-- Isabelle `oix_OTint_slot2` の結論に `hasParent N 1 (Lng N - 1)` を足した形。 -/
def OTint_hasParent : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    (transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true) →
    hasParent N 1 (Lng N - 1) = true →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-! ## 2. no-parent 隅の材料 -/

/-- Isabelle `npx_oper_noParent_Pred` (`layerB/pss_wip.thy`:101281)。
`j₁ > 0`、`0 < N_{1,j₁}`（したがって `idx1 N j₁ = 1`）、行 1 の親なし ⟹
`oper` は全ての `m` で `Pred N` に潰れる。 -/
private theorem oper_noParent_Pred_oi {N : PS} {m : ℕ}
    (j1gt : 0 < Lng N - 1)
    (epos : 0 < entry N 1 (Lng N - 1))
    (nhp : hasParent N 1 (Lng N - 1) = false) :
    oper N m = Pred N := by
  have hj1 : ¬ (Lng N - 1 = 0) := by omega
  have he : ¬ (entry N 1 (Lng N - 1) = 0) := by omega
  have hi1 : idx1 N (Lng N - 1) = 1 := by simp [idx1, epos]
  simp [oper, hj1, he, hi1, nhp]

/-- 条件 (III)/(IV)/(V) はいずれも `0 < N_{1,j₁}` を含む。 -/
private theorem cond345_entry1_pos_oi {N : PS}
    (hc : transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true) :
    0 < entry N 1 (Lng N - 1) := by
  rcases hc with h | h | h
  · simp [transCondIII, lastIdx] at h; omega
  · simp [transCondIV, lastIdx] at h; omega
  · simp [transCondV, lastIdx] at h; omega

/-- 条件 (III)/(IV)/(V) は条件 (I) を排除する（(I) は `N_{1,j₁} = 0` を要求）。 -/
private theorem cond345_not_condI_oi {N : PS}
    (hc : transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true) :
    transCondI N = false := by
  have hpos : 0 < entry N 1 (Lng N - 1) := cond345_entry1_pos_oi hc
  simp [transCondI, lastIdx]
  omega

/-- 条件 (III)/(IV)/(V) は条件 (VI) を排除する。
(III)/(IV) は `N_{1,j₁} ≤ N_{1,j₀}`、(VI) は `N_{1,j₀} + 1 = N_{1,j₁}` で矛盾。
(V) は `j₀ + 1 < j₁`、(VI) は `j₀ + 1 = j₁` で矛盾。 -/
private theorem cond345_not_condVI_oi {N : PS}
    (hc : transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true) :
    transCondVI N = false := by
  rcases hc with h | h | h
  · simp [transCondIII, lastIdx] at h
    simp [transCondVI, lastIdx]
    omega
  · simp [transCondIV, lastIdx] at h
    simp [transCondVI, lastIdx]
    omega
  · simp [transCondV, lastIdx] at h
    simp [transCondVI, lastIdx]
    omega

/-! ## 3. no-parent 隅の discharge

Isabelle `oi8_OTint_condIII` / `oi8_OTint_condIV` の `case False`。 -/

/-- no-parent 隅: `N[m] = Pred N` かつ `Trans (Pred N) ∈ OT_B`。
Isabelle の condIV 側 (`ot2_IVNP` → `od4_OTpred_final`) と同じルートを、
condIII/condV にも共有させたもの。 -/
private theorem OTint_noParent_oi (hpred : OTdisp_OTpred)
    {N : PS} {m : ℕ} (hST : STPS N) (_hmono : monoT N = true)
    (j1gt : 1 < Lng N - 1)
    (hc : transCondIII N = true ∨ transCondIV N = true ∨ transCondV N = true)
    (nhp : hasParent N 1 (Lng N - 1) = false)
    (hOT : Trans N ∈ OT_B) :
    Trans (oper N m) ∈ OT_B := by
  have hpos : 0 < entry N 1 (Lng N - 1) := cond345_entry1_pos_oi hc
  have hop : oper N m = Pred N :=
    oper_noParent_Pred_oi (by omega) hpos nhp
  have hL : 2 < Lng N := by omega
  have hnz : ¬ (entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) := by
    rintro ⟨-, h2⟩; omega
  have hnI : ¬ (monoT N = true ∧ transCondI N = true) := by
    rintro ⟨-, h2⟩
    rw [cond345_not_condI_oi hc] at h2
    exact Bool.noConfusion h2
  have hnVI : ¬ (monoT N = true ∧ transCondVI N = true ∧
      ¬ (adm N (transJ0 N) = true)) := by
    rintro ⟨-, h2, -⟩
    rw [cond345_not_condVI_oi hc] at h2
    exact Bool.noConfusion h2
  have := hpred N hST hOT hL hnz hnI hnVI
  rw [hop]
  exact this

/-! ## 4. 主結果 -/

/-- **`OTdisp_OTint` を `hasParent` 付きに弱める**。残差は
`OTint_hasParent` 1 本のみ（＋既にある葉 `OTdisp_OTpred`）＝残差本数は増えない。
Isabelle: `oi8_OTint_condIII` / `oi8_OTint_condIV` の `hasParent` 場合分けを
condV にも広げたもの。 -/
theorem OTdisp_OTint_of_hasParent
    (hpred : OTdisp_OTpred) (hhp : OTint_hasParent) : OTdisp_OTint := by
  intro N m hST hmono j1gt hc hOT hm
  cases hp : hasParent N 1 (Lng N - 1) with
  | false => exact OTint_noParent_oi hpred hST hmono j1gt hc hp hOT
  | true => exact hhp N m hST hmono j1gt hc hp hOT hm

/-! ## 5. Isabelle の 4 分岐（並列攻略用のオプション） -/

/-- Isabelle `oi8_OTint_condIII` の `True` 枝（`oi8_OTint_IIIIV_hp` 経由）。 -/
def OTint_hp_condIII : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondIII N = true → hasParent N 1 (Lng N - 1) = true →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-- Isabelle `oi8_OTint_condIV` の `True` 枝。 -/
def OTint_hp_condIV : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondIV N = true → hasParent N 1 (Lng N - 1) = true →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-- Isabelle `oix_OTint_condV_adm` (`layerB/pss_wip.thy`:111599) を
`hasParent` 付きに弱めたもの。 -/
def OTint_hp_condV_adm : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondV N = true → adm N (transJ0 N) = true →
    hasParent N 1 (Lng N - 1) = true →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-- Isabelle `oix_OTint_condV_nadm` (`layerB/pss_wip.thy`:112041) を
`hasParent` 付きに弱めたもの（Isabelle 側は `PredNpH`/`LpvH`/`L1vH` を
残差に持つが、最終 census (`od4_termination_census_v4` 系) で全て discharge
される）。 -/
def OTint_hp_condV_nadm : Prop :=
  ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
    transCondV N = true → adm N (transJ0 N) = false →
    hasParent N 1 (Lng N - 1) = true →
    Trans N ∈ OT_B → 1 < m → Trans (oper N m) ∈ OT_B

/-- Isabelle `oix_OTint_slot2` の 4 way case split そのもの。 -/
theorem OTint_hasParent_of_legs
    (h3 : OTint_hp_condIII) (h4 : OTint_hp_condIV)
    (hVa : OTint_hp_condV_adm) (hVn : OTint_hp_condV_nadm) :
    OTint_hasParent := by
  intro N m hST hmono j1gt hc hp hOT hm
  rcases hc with h | h | h
  · exact h3 N m hST hmono j1gt h hp hOT hm
  · exact h4 N m hST hmono j1gt h hp hOT hm
  · cases ha : adm N (transJ0 N) with
    | true => exact hVa N m hST hmono j1gt h ha hp hOT hm
    | false => exact hVn N m hST hmono j1gt h ha hp hOT hm

/-- 上の 2 本の合成。 -/
theorem OTdisp_OTint_of_legs
    (hpred : OTdisp_OTpred) (h3 : OTint_hp_condIII) (h4 : OTint_hp_condIV)
    (hVa : OTint_hp_condV_adm) (hVn : OTint_hp_condV_nadm) :
    OTdisp_OTint :=
  OTdisp_OTint_of_hasParent hpred (OTint_hasParent_of_legs h3 h4 hVa hVn)

#print axioms OTdisp_OTint_of_hasParent
#print axioms OTint_hasParent_of_legs
#print axioms OTdisp_OTint_of_legs

end PSS
