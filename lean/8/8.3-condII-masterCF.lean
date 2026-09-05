import «6».«6.6-P-condAB»
import «7».«7.3-Trans-welldefined»
import «7».«7.4-RightNodes-Mark»
import «8».«8.2-subexpr-adm0-ctx»
import «8».«8.3-TransCondII-engine»
import «8».«8.7-Trans-preserves-OT»

/-!
# §8.3 条件(II) — `CondII_masterCF` の討伐（`c2sx_` 連鎖の移植）

- 原文: `tmp/content.md` 3956–4247（§8.3 命題（条件(II)の下での `Trans` と基本列の
  交換関係））。逐語形は `p_8_3_TransCondII_oper_descend`
  (isabelle/pss_paper.thy:1863)。

- 担当: ビルド済み «8».«8.3-TransCondII-engine» が露出した名前付き `Prop`
  `CondII_masterCF`（同 :211）ただ 1 本。これは exchII の唯一の残差であり、
  `FseqDesc_exchII`（降下柱）と `OTdisp_exchII`（OT 所属柱）は byte-identical
  なので、**両柱が同時にこの 1 本に依存する**。

- Isabelle 側の連鎖（`c2sx_` corpus, isabelle/layerB/pss_wip.thy 86363–87630）:
  | Isabelle | 行 | 本ファイル | 状態 |
  |---|---|---|---|
  | `c2sx_condII_masterCF` | 87430 | `condII_masterCF_of_tailval` | ✅ 組み立て移植（`TV` 込み 1:1） |
  | `c2sx_host_basic` | 86474 | `condII_host_basic_holds` | ✅ 無仮定 |
  | `c2sx_c1_shape` | 86546 | `condII_c1_shape_holds` | ✅ 無仮定 |
  | `c2sx_c2_val` | 86603 | `condII_c2_val_holds` | ✅ 無仮定 |
  | `c2sx_t2_split` | 86626 | `condII_t2_split_holds` | ✅ 無仮定（A36 二分岐の在処） |
  | `s84c2_Trans_c2_decomp` | — | `Trans_c1_c2_decomp` | ✅ 無仮定（`replaceScb_spec` 経由） |
  | `BT_split_last_principal` | 26360 | private `BT_split_last_principal_cf2` | ✅ 無仮定 |
  | `c2sx_addBT_0right` 他 | 86455– | private `addBT_zero_right_cf2` 他 | ✅ 無仮定 |
  | `c2sx_tailval` | 86448 | `CondII_tailval`（def） | — 1:1 転記 |
  | **`c2sx_step`** | **87202** | **`CondII_step`** | 🤖 **残差 1/2**（下部 ~800 行未移植） |
  | **`y3j_condII_tailval`** | **scratch:17079** | **`CondII_TailvalAll`** | 🤖 **残差 2/2**（🚨 RT_PS 版＝Isabelle に無い） |

  すなわち **`CondII_masterCF` の残差は `CondII_step` と `CondII_TailvalAll` の
  2 本ちょうど**に絞り込んだ（Isabelle ~1500 行の `c2sx_` 連鎖のうち、組み立て・
  host_basic・c1_shape・c2_val・t2_split・scb 対・BT 算術は全て無仮定で片付いた）。

- 🚨🚨 **`CondII_masterCF` は Isabelle の `c2sx_condII_masterCF` より真に強い**
  （本ファイル最大の所見。engine ヘッダの記述は不正確）:
  * Isabelle の `c2sx_condII_masterCF` は仮定 `TV : c2sx_tailval M` を持つ。
  * engine ヘッダは「`TV` は `y3j_condII_tailval` が**無条件に**落とす」と書くが、
    `y3j_condII_tailval` (layerC/pss_scratch.thy:17079) の仮定は
    **`MST : M ∈ ST_PS`** であって `M ∈ RT_PS` ではない。
  * 一方 `CondII_masterCF` は **`RTPS M`** 上で `TV` 抜きで述べられている。
  * すなわち `CondII_masterCF` ⟸ Isabelle corpus は**成り立たない**。移植可能な
    のは `RTPS + CondII_tailval` 版（＝本ファイルの `condII_masterCF_of_tailval`）
    までで、`RTPS ⟹ CondII_tailval`（`CondII_TailvalAll`）は Isabelle には
    **存在しない**（ST_PS 版しかない）。
  * ⚠️ **`c2sx_tailval` の供給元は全 9 本を確認した**（`shows "c2sx_tailval"` を
    全数 grep）。RT_PS 版は 2 本存在するが**どちらも追加仮定つき**:
    `c2sx_tailval_trunk` (87720, 仮定 `TR`＝`TrMax (Red (seg …)) = Lng (…) - 1`)、
    `c2sx_tailval_of_reg` (87838, 仮定 `¬ldj` ＋ `REG`＝`cfbx_reg …`)。
    **無仮定**の供給元（`cdx_tailval_notldj` 90424 / `tvx_TVall_of_LDJB_fin`
    110714 / `tvx_TVall_of_residuals` 110948 / `ljx_TVall_of_fin` 115242）は
    **すべて `ST_PS` 束縛**。すなわち「RT_PS 上で無条件の tailval」は
    corpus に**存在しない**（名前ではなく `shows` の内容で全数確認済み）。
  * 数値監査（`python/audit_83_condII_tailval_deep.py`、`PSS_CAP=10 PSS_LMAX=5`）:
    reduced 数列 **330106 本**を走査し、RT_PS 条件(II) ホスト **144 本**
    （**成分最大 9**＝`memo.md` par.3 の危険帯 6〜9 の**内側**、`ldj` 両枝
    True=44 / False=100）で `CondII_tailval` は **144/144 成立・反例 0**。
    ただし**予備監査の母数は過少申告だった**:
    `audit_83_condII_masterCF.py` は「成分 < 6・`Lng ≤ 5` で 10 本」と報告するが、
    それは **`M[0]` を `(0,0)` に釘付け**していたため。`reduced` は 0 列目に
    `M[0] = (a,a)` しか課さない（`a > 0` も RT_PS）ので、同じ境界で実際には
    **46 本**ある（`ldj` 両枝: True=14 / False=32）。deep 版は `(a,a)` を全数
    展開し、かつ `reduced` の**前緊閉性**（`RTPS_Pred` が証明済＝butlast で閉じる
    ⟹ 全 prefix が reduced）で DFS 枝刈りするので、`memo.md` par.3 の警告する
    **成分 6〜9 の帯**まで到達できる（予備監査の `CAP=6` はこの帯の**手前**で
    止まっており、記録された 13 件の偽陽性と同じ形をしていた）。
    よって `CondII_masterCF` は**真らしい**が、**未証明**であり、engine ヘッダの
    「Isabelle では定理」は RT_PS 版については**誤り**。

- 訂正: **A36 は取り下げ済み**（`corrections-old.md:138`）＝存在形 (`∃ c`) が原文に
  忠実。`c2sx_ldj` は原文の「`P(t₂)_{J₁}` の左端が `D_{M₁,ⱼ₀}` であるか否かに従って
  `mₙ := n-1` または `n-2`」の場合分けそのもの（scratch:17028 の注記）。

- 依存（ビルド済みのみ import）: `6.6-P-condAB`（`mono_hasParent_row0`）、
  `7.3-Trans-welldefined`（`Marked_Pred_Adm`, `replaceScb_spec`,
  `Trans_Mark_mono_equations`, `Trans_mem_T_B`, `Mark_mem_T_B`,
  `transC2Core_properties`, `unflatBT_flat`）、`7.4-RightNodes-Mark`
  （`Mark_leftend_form_proper`）、`8.2-subexpr-adm0-ctx`（`t2ne_notAVI`
  ＝ `m_8_2_t2ne_notAVI`）、`8.3-TransCondII-engine`（`CondII_masterCF` 本体）。

- 状態:
  - `condII_host_basic_holds` / `condII_c1_shape_holds` / `condII_c2_val_holds`
    / `condII_t2_split_holds` / `Trans_c1_c2_decomp` … ✅ **GREEN・無仮定**。
  - `condII_masterCF_of_tailval` … 🤖 GREEN-MODULO（残差 `CondII_step` のみ）。
    Isabelle の `c2sx_condII_masterCF` と 1:1（`TV` 込み）。
  - `condII_masterCF_holds` … 🤖 GREEN-MODULO（`CondII_step` ＋
    `CondII_TailvalAll`）。`CondII_masterCF` を drop-in で充足する（house pattern）。
  - `condII_exchII_of_residuals` … 同 2 本から `FseqDesc_exchII` まで通す
    （親の独立検証用。`OTdisp_exchII` は byte-identical なので同時に落ちる）。
  - 🎯 `condII_exchII_of_ST_residuals` / `condII_OTdispII_of_ST_residuals` …
    🤖 GREEN-MODULO（`CondII_step` ＋ `CondII_TailvalAll_ST`）。
    **engine の `CondII_masterCF` を経由せずに両柱の `exchII` を供給する**。
    残差が**両方とも Isabelle の定理**（`c2sx_step` / `y3j_condII_tailval`）に
    なるので、`condII_exchII_of_residuals` より**厳密に望ましい**（後者の
    `CondII_TailvalAll` は RT_PS 無条件版＝corpus に存在しない）。
    `OTdisp_exchII` が `FseqDesc_exchII` と定義的に同一であることは
    `condII_OTdispII_of_ST_residuals` が**型検査で機械確認**している。
  - sorry 0、axioms = propext/Classical.choice/Quot.sound。

- 📌 **親への推奨**（本ファイルの外＝engine の 1 行修正）: ビルド済み
  «8».«8.3-TransCondII-engine»:212 の `CondII_masterCF` の `RTPS M` を
  **`STPS M` に変える**（`exchII_of_masterCF`:225 の `STPS_RTPS` の行が不要に
  なるだけ）。消費者（`FseqDesc_exchII`:78 / `OTdisp_exchII`:88）は**両方とも
  `STPS N`** を渡してくるので RT_PS 版は誰も要求しておらず、この 1 行で残差は
  Isabelle の定理 2 本（`c2sx_step` / `y3j_condII_tailval`）だけになる。
  本ファイルはその修正を待たずに `condII_exchII_of_ST_residuals` で
  同じ結論（両柱の `exchII`）を既に供給している。
-/

namespace PSS

/-! ## `BT` の算術補助（Isabelle `c2sx_addBT_0right` 86455 / `c2sx_multBT_one`
86458 / `c2sx_multBT_add` 86461、および `scx_addBT_assoc`） -/

private theorem addBT_zero_right_cf2 (t : BT) : addBT t BZero = t := by
  cases t with
  | trm ps => simp [addBT, BZero]

private theorem addBT_zero_left_cf2 (t : BT) : addBT BZero t = t := by
  cases t with
  | trm ps => simp [addBT, BZero]

private theorem addBT_assoc_cf2 (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  cases a with
  | trm as => cases b with
    | trm bs => cases c with
      | trm cs => simp [addBT]

private theorem multBT_one_cf2 (a : BT) : multBT a 1 = a := by
  simp [multBT, addBT_zero_left_cf2]

private theorem multBT_add_cf2 (a : BT) (i j : ℕ) :
    multBT a (i + j) = addBT (multBT a i) (multBT a j) := by
  induction j with
  | zero => simp [multBT, addBT_zero_right_cf2]
  | succ j ih =>
      have : i + (j + 1) = (i + j) + 1 := by omega
      rw [this]
      simp only [multBT, ih]
      rw [addBT_assoc_cf2]

/-! ## 条件(II) の `c₂` の枝データ（Isabelle `c2sx_pj`/`c2sx_ldj`/`c2sx_t3`/
`c2sx_t4`, pss_wip.thy:86431–86443）

Lean の `transC2Core`（`PSS/Trans.lean:139`）の `else` 枝が既にこの分岐
（`leftDj₀`/`t₃`/`t₄`）を内蔵しているので、下の 4 定義はその `let` を
トップレベルに露出したものであり、`c2sx_*` と 1:1 で一致する。
`Isabelle の ! は .getD`（SPELLING 規約）。 -/

/-- Isabelle `c2sx_pj` (86431): `t₂` の最後の principal。 -/
def condII_pj (M : PS) : BT :=
  (PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero

/-- Isabelle `c2sx_ldj` (86434): 原文の「`P(t₂)_{J₁}` の左端が `D_{M₁,ⱼ₀}` か」。 -/
def condII_ldj (M : PS) : Bool :=
  bpHeadV (condII_pj M) == (entry M 1 (transJ0 M) : ℕ∞)

/-- Isabelle `c2sx_t3` (86437)。 -/
def condII_t3 (M : PS) : BT :=
  if condII_ldj M then SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1))
  else transT2 M

/-- Isabelle `c2sx_t4` (86442)。 -/
def condII_t4 (M : PS) : BT :=
  if condII_ldj M then bpHeadT (condII_pj M) else transT2 M

/-- Isabelle `c2sx_tailval` (86448)。**THE 残差**: 追加ブロックの終切片の値
`W = Trans (seg M j₀ (Lng M - 2))` が `D_{M₁,ⱼ₀} t₄` であること。
頭部は Isabelle 側で証明済（`dkax_slice_principal_gen`）で、本体
`bpHeadT W = t₄` の同定が原文 §8.2「条件(II)か(IV)の下での終切片と `Trans` の
関係」（`p_8_2_condIIIV_terminal_slice_Trans`）の深い内容。 -/
def CondII_tailval (M : PS) : Prop :=
  Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))
    = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M)

/-! ## `c2sx_host_basic` (pss_wip.thy:86474) — 条件(II) ホストの基本事実

Isabelle の 12 結論のうち、下流（`c1_shape`/`c2_val`/`masterCF`）が実際に使う
ものを連言で束ねた。`w ≥ 2`（`j₀ + 1 < j₁`）が条件(II) では**常に**成り立つ
ことが要点（原文の `w = 1` の隅は存在しない）。 -/

/-- Isabelle `c2sx_host_basic` (86474) の結論 (1)-(6)(9)(10)(11)。 -/
def CondII_host_basic : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    hasParent M 0 (Lng M - 1) = true ∧
    entry M 1 (Lng M - 1) = 0 ∧
    adm M (parent M 0 (Lng M - 1)) = false ∧
    0 < parent M 0 (Lng M - 1) ∧
    Adm M (parent M 0 (Lng M - 1)) < parent M 0 (Lng M - 1) ∧
    parent M 0 (Lng M - 1) + 1 < Lng M - 1 ∧
    ¬(transCondI M = true ∨ transCondIII M = true ∨ transCondV M = true) ∧
    transCondVI M = false ∧
    transT2 M ≠ BZero

/-- 非許容点の許容化は真に下がる（Isabelle `nadm_Adm_lt`）。 -/
private theorem nadm_Adm_lt_cf2 (M : PS) (j : ℕ) (hna : adm M j = false) :
    Adm M j < j := by
  have hle := Adm_le M j
  have hadm := Adm_adm M j
  rcases Nat.lt_or_ge (Adm M j) j with h | h
  · exact h
  · exfalso
    have heq : Adm M j = j := by omega
    rw [heq] at hadm
    rw [hadm] at hna
    exact absurd hna (by simp)

/-- `0` は常に許容（Isabelle `adm_index0`）。`nadm` の両枝が `j = 0` で潰れる。 -/
private theorem adm_index0_cf2 (M : PS) : adm M 0 = true := by
  simp only [adm, nadm, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff]
  refine ⟨by simp, ?_⟩
  left
  simp only [nextR, if_neg (by decide : ¬(1 = 0))]
  simp [nextrel1]

/-- Isabelle `c2sx_host_basic` (pss_wip.thy:86474)。 -/
theorem condII_host_basic_holds : CondII_host_basic := by
  intro M hR hmono hj1 hcond
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  -- 条件(II) の展開
  have hcond' := hcond
  simp only [transCondII, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    lastIdx, lastParent] at hcond'
  have e1z : entry M 1 (Lng M - 1) = 0 := hcond'.1
  have nadmj : adm M (parent M 0 (Lng M - 1)) = false := hcond'.2
  -- (1) 行 0 の親の存在
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  -- j₀ < j₁（親辺 `nextrel0` から）
  have hedge : nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true :=
    nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hedge0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hedge
  have hj0lt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have h := hedge0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2
  -- (4) `j₀ > 0`: さもなくば `adm M 0 = true` に反する
  have hj0pos : 0 < parent M 0 (Lng M - 1) := by
    rcases Nat.eq_zero_or_pos (parent M 0 (Lng M - 1)) with h0 | h
    · exfalso
      rw [h0] at nadmj
      rw [adm_index0_cf2 M] at nadmj
      exact Bool.noConfusion nadmj
    · exact h
  -- (5) 許容化の狭義降下
  have hjm1lt : Adm M (parent M 0 (Lng M - 1)) < parent M 0 (Lng M - 1) :=
    nadm_Adm_lt_cf2 M _ nadmj
  -- (6) `w ≥ 2`: 非許容な `j₀` は行 1 の子辺 `(1,j₀) <^Next (1,j₀+1)` を持つ
  have hw2 : parent M 0 (Lng M - 1) + 1 < Lng M - 1 := by
    have hna : nadm M (parent M 0 (Lng M - 1)) = true := by
      simpa [adm] using nadmj
    have hna' := hna
    simp only [nadm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hna'
    have hnx1 : nextR M 1 (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + 1)
        = true := by
      rcases hna' with hlt | hpair
      · exfalso; omega
      · exact hpair.2
    have hlt1 : entry M 1 (parent M 0 (Lng M - 1))
        < entry M 1 (parent M 0 (Lng M - 1) + 1) := by
      have h := hnx1
      simp only [nextR, if_neg (by decide : ¬(1 = 0)), nextrel1,
        Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.2
    have hne : parent M 0 (Lng M - 1) + 1 ≠ Lng M - 1 := by
      intro heq
      rw [heq] at hlt1
      omega
    omega
  -- (9)(10) 条件(I)(III)(V)(VI) の排除
  have hnotA : ¬(transCondI M = true ∨ transCondIII M = true
      ∨ transCondV M = true) := by
    rintro (h | h | h)
    · simp [transCondI, lastIdx, lastParent, nadmj] at h
    · simp [transCondIII, lastIdx, e1z] at h
    · simp [transCondV, lastIdx, e1z] at h
  have hnotVI : transCondVI M = false := by
    simp only [transCondVI, lastIdx, Bool.and_eq_false_iff, e1z]
    left; left; simp
  -- (11) `t₂ ≠ 0_B`（Isabelle `m_8_2_t2ne_notAVI`）
  have ht2 : transT2 M ≠ BZero := t2ne_notAVI M hR hmono hL hj1 hnotA hnotVI
  exact ⟨hp0, e1z, nadmj, hj0pos, hjm1lt, hw2, hnotA, hnotVI, ht2⟩

/-! ## `c2sx_c1_shape` (pss_wip.thy:86546) — 基点列の値 `c₁ = D_va t₂` -/

/-- Isabelle `c2sx_c1_shape` (86546) の結論 (1)(2)(3)(4)。 -/
def CondII_c1_shape : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))
        = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) (transT2 M) ∧
    transV M = (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) ∧
    transT2 M ∈ T_B ∧
    Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) ∈ T_B

/-- `Dprin v t ∈ T_B → t ∈ T_B`（Isabelle `scx_TB_Dpt_body`）。 -/
private theorem TB_Dprin_body_cf2 {v : ℕ∞} {t : BT} (h : Dprin v t ∈ T_B) :
    t ∈ T_B := by
  have h' : ¬v = ⊤ ∧ dfree_BT t = true := by
    simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList] using h
  simpa [T_B] using h'.2

/-- Isabelle `c2sx_c1_shape` (pss_wip.thy:86546)。 -/
theorem condII_c1_shape_holds : CondII_c1_shape := by
  intro M hR hmono hj1 hcond
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  obtain ⟨hp0, e1z, nadmj, _hj0pos, hjm1lt, hw2, _, _, ht2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  -- 基点性
  have mkA : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hL hp0
  have hc1TB : Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) ∈ T_B :=
    Mark_mem_T_B (Pred M) _ hpredR mkA
  -- `transC1 M = Mark (Pred M) (Adm M j₀)`（定義展開）
  have hC1M : transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) := by
    simp [transC1, transJm1, transJ0, lastParent, lastIdx]
  have ht2E : transT2 M
      = bpHeadT (Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))) := by
    simp [transT2, hC1M]
  -- `c₁` は左端基点形 `D_{(Pred M)₁,ⱼ₋₁} t`
  have hjm1small : Adm M (parent M 0 (Lng M - 1)) < Lng (Pred M) - 1 := by
    rw [hpredLen]; omega
  obtain ⟨t, htE⟩ :=
    Mark_leftend_form_proper (Pred M) (Adm M (parent M 0 (Lng M - 1)))
      mkA hpredR hjm1small
  -- `Pred` は末尾のみを落とすので `j₋₁ < Lng M - 1` の entry は不変
  have hentryP : entry (Pred M) 1 (Adm M (parent M 0 (Lng M - 1)))
      = entry M 1 (Adm M (parent M 0 (Lng M - 1))) :=
    entry_Pred M 1 _ (by omega)
  have hteq : t = transT2 M := by rw [ht2E, htE]; simp [bpHeadT, Dprin]
  have hc1E : Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))
      = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) (transT2 M) := by
    rw [htE, hentryP, hteq]
  refine ⟨hc1E, ?_, ?_, hc1TB⟩
  · rw [transV, hC1M, hc1E]; simp [bpHeadV, Dprin]
  · exact TB_Dprin_body_cf2 (by rw [← hc1E]; exact hc1TB)

/-! ## `c2sx_c2_val` (pss_wip.thy:86603) — `c₂` の値

条件(II) は `transC2Core`（`PSS/Trans.lean:139`）の **4 番目の枝**（`else`）に
落ちる: (I)(III)(V) は `M₁,ⱼ₁ = 0` と `¬adm j₀` で、(VI) は `M₁,ⱼ₁ = 0` で、
`t₂ = 0_B` 枝は `host_basic(11)` で排除される。その枝の `let` が
`condII_ldj`/`condII_t3`/`condII_t4` そのもの。 -/

/-- Isabelle `c2sx_c2_val` (86603)。 -/
def CondII_c2_val : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    transC2 M = Dprin (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞)
      (addBT (condII_t3 M)
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)
          (addBT (condII_t4 M) (Dprin 0 BZero))))

/-- Isabelle `c2sx_c2_val` (pss_wip.thy:86603)。 -/
theorem condII_c2_val_holds : CondII_c2_val := by
  intro M hR hmono hj1 hcond
  obtain ⟨_, e1z, _, _, _, _, hnotA, hnotVI, ht2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hI : transCondI M = false :=
    Bool.eq_false_iff.mpr (fun h => hnotA (Or.inl h))
  have hIII : transCondIII M = false :=
    Bool.eq_false_iff.mpr (fun h => hnotA (Or.inr (Or.inl h)))
  have hV : transCondV M = false :=
    Bool.eq_false_iff.mpr (fun h => hnotA (Or.inr (Or.inr h)))
  have ht2b : (transT2 M == BZero) = false := by
    simpa [beq_eq_false_iff_ne] using ht2
  have hV2 : transV M = (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) :=
    (condII_c1_shape_holds M hR hmono hj1 hcond).2.1
  -- `transC2Core` の 4 番目の枝へ落とす
  rw [transC2, transC2Core]
  simp only [hI, hIII, hV, hnotVI, ht2b, Bool.or_self, Bool.false_eq_true,
    if_false, hV2, lastIdx, lastParent, e1z, Nat.cast_zero]
  rfl

/-! ## `s84c2_Trans_c2_decomp` — ホストの mono 枝の scb 対 `(s₁,b₁)`

`Trans (Pred M)` の中の `c₁` の scb 文脈 `(s₁,b₁)` が、`Trans M` の中では
そのまま `c₂` の scb 文脈になる。Isabelle は専用補題を持つが、Lean では
`Trans_Mark_mono_equations`(1)（`Trans M = replaceScb t₁ c₁ c₂`）と
`replaceScb_spec` から直接出る（原文の `t₂` 手展開が不要＝Lean 側の短縮）。 -/

/-- Isabelle `s84c2_Trans_c2_decomp` の Lean 版。 -/
theorem Trans_c1_c2_decomp (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) :
    ∃ s b : List Sym,
      scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have ht₁TB : Trans (Pred M) ∈ T_B := Trans_mem_T_B (Pred M) hpredR
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have ht₁c₁ : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Trans_Mark_mem_MarkedB (Pred M) _ hpredR hmarked
  have hc₁P : ∃ p, transC1 M = .trm [p] :=
    marked_component_principal ht₁ ht₁c₁
  have hc₂facts := transC2Core_properties M (transC1 M) hc₁TB hc₁P
  have hc₂TB : transC2 M ∈ T_B := by
    simpa [transC2, transV, transT2] using hc₂facts.1
  have hc₂P : ∃ p, transC2 M = .trm [p] := by
    simpa [transC2, transV, transT2] using hc₂facts.2
  have hTrans : Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    simpa [ht₁, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent] using (Trans_Mark_mono_equations M hR hlen hmono).1
  obtain ⟨s, b, hd, _hout, hd2⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
  exact ⟨s, b, hd, by rw [hTrans]; exact hd2⟩

/-! ## `c2sx_t2_split` (pss_wip.thy:86626) — 基底の分解 `t₂ = t₃ +_B X^cnt₁`

`cnt₁ = 1 ⟺ ldj` が **A36 の数え上げ二分岐そのもの**（帰納自身の分岐ではなく、
最終の再梱包の分岐）。Isabelle は `BT_split_last_principal` を使うが、Lean には
その twin が無いので `List.dropLast_append_getLast` で直接証明する
（`7.2-scb-outer-surgery-split`:17 の注記どおり）。 -/

/-- `PB` は `SigmaB` の逆（`flatMap untrm ∘ map (trm [·]) = id`）。 -/
private theorem flatMap_untrm_map_cf2 (ps : List BP) :
    (ps.map (fun p => BT.trm [p])).flatMap untrm = ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [untrm, ih]

private theorem dfree_BPList_append_cf2 (as bs : List BP) :
    dfree_BPList (as ++ bs) = (dfree_BPList as && dfree_BPList bs) := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons a as ih => simp [dfree_BPList, ih, Bool.and_assoc]

/-- `x +_B y ∈ T_B` は両成分の `T_B` 所属と同値（Isabelle `scx_TB_addBT_left` 系）。 -/
private theorem TB_addBT_split_cf2 {x y : BT} (h : addBT x y ∈ T_B) :
    x ∈ T_B ∧ y ∈ T_B := by
  cases x with
  | trm as => cases y with
    | trm bs =>
        have h' : dfree_BPList (as ++ bs) = true := by
          simpa [T_B, addBT, dfree_BT] using h
        rw [dfree_BPList_append_cf2] at h'
        simp only [Bool.and_eq_true] at h'
        exact ⟨by simpa [T_B, dfree_BT] using h'.1,
               by simpa [T_B, dfree_BT] using h'.2⟩

/-- Isabelle `BT_split_last_principal` (pss_wip.thy:26360) の Lean 版。 -/
private theorem BT_split_last_principal_cf2 (t : BT) (ht : t ≠ BZero) :
    t = addBT (SigmaB ((PB t).dropLast))
      (Dprin (bpHeadV ((PB t).getD ((PB t).length - 1) BZero))
        (bpHeadT ((PB t).getD ((PB t).length - 1) BZero))) := by
  cases t with
  | trm ps =>
      have hps : ps ≠ [] := by
        intro h; exact ht (by simp [h, BZero])
      -- 最後の principal を取り出す
      obtain ⟨qs, q, rfl⟩ : ∃ qs q, ps = qs ++ [q] := by
        obtain ⟨q, qs, hrev⟩ := List.exists_cons_of_ne_nil (l := ps.reverse)
          (by simpa using hps)
        exact ⟨qs.reverse, q, by
          have := congrArg List.reverse hrev
          simpa using this⟩
      cases q with
      | db v a =>
          simp [PB, untrm, SigmaB, Dprin, addBT, bpHeadV, bpHeadT,
            List.getD_eq_getElem?_getD, flatMap_untrm_map_cf2]

/-- Isabelle `c2sx_t2_split` (86626) の結論 (1)(2)(3)。 -/
def CondII_t2_split : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    transT2 M = addBT (condII_t3 M)
        (multBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M))
          (if condII_ldj M then 1 else 0)) ∧
    condII_t3 M ∈ T_B ∧ condII_t4 M ∈ T_B

/-- Isabelle `c2sx_t2_split` (pss_wip.thy:86626)。 -/
theorem condII_t2_split_holds : CondII_t2_split := by
  intro M hR hmono hj1 hcond
  obtain ⟨_, _, _, _, _, _, _, _, ht2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have ht2TB : transT2 M ∈ T_B :=
    (condII_c1_shape_holds M hR hmono hj1 hcond).2.2.1
  have hsplit := BT_split_last_principal_cf2 (transT2 M) ht2
  -- `transJ0 M = parent M 0 (Lng M - 1)`（定義展開）
  have hJ0 : transJ0 M = parent M 0 (Lng M - 1) := by
    simp [transJ0, lastParent, lastIdx]
  by_cases hldj : condII_ldj M = true
  · -- `ldj` 枝: 最後の principal の頭が `M₁,ⱼ₀`、`cnt₁ = 1`
    have hv : bpHeadV (condII_pj M) = (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) := by
      have := hldj
      simp only [condII_ldj, beq_iff_eq] at this
      rw [this, hJ0]
    have ht3 : condII_t3 M
        = SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)) := by
      simp [condII_t3, hldj]
    have ht4 : condII_t4 M = bpHeadT (condII_pj M) := by simp [condII_t4, hldj]
    have hdl : (PB (transT2 M)).dropLast
        = (PB (transT2 M)).take ((PB (transT2 M)).length - 1) :=
      List.dropLast_eq_take
    have hmain : transT2 M
        = addBT (condII_t3 M)
            (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M)) := by
      rw [ht3, ht4, ← hv, ← hdl]
      exact hsplit
    refine ⟨?_, ?_, ?_⟩
    · rw [hmain]
      simp only [hldj, if_true, multBT_one_cf2]
    · -- `t₃ ∈ T_B`: `t₂ = t₃ +_B (…)` の左成分
      have hin : addBT (condII_t3 M)
          (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M)) ∈ T_B := by
        rw [← hmain]; exact ht2TB
      exact (TB_addBT_split_cf2 hin).1
    · -- `t₄ ∈ T_B`: `D_{v} t₄` の本体
      have hin : addBT (condII_t3 M)
          (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) (condII_t4 M)) ∈ T_B := by
        rw [← hmain]; exact ht2TB
      exact TB_Dprin_body_cf2 (TB_addBT_split_cf2 hin).2
  · -- `¬ldj` 枝: `t₃ = t₄ = t₂`、`cnt₁ = 0`
    have hf : condII_ldj M = false := by simpa using hldj
    have ht3 : condII_t3 M = transT2 M := by simp [condII_t3, hf]
    have ht4 : condII_t4 M = transT2 M := by simp [condII_t4, hf]
    refine ⟨?_, ?_, ?_⟩
    · simp only [hf, if_false, multBT, ht3]
      exact (addBT_zero_right_cf2 _).symm
    · rw [ht3]; exact ht2TB
    · rw [ht4]; exact ht2TB

/-! ## `c2sx_step` (pss_wip.thy:87202) — 一歩あたりの surgery（🤖 残差）

Isabelle の per-step surgery は**一様**（場合分けなし）: `N = seg (M[n]) 0 idx`
（`idx = j₀ + (n-1)w`、最終ブロックの先頭。`Pred N = M[n-1]`）が常に条件(V) を
満たし、その `c₂^N` は葉 `D_{M₁,ⱼ₀} 0` を追加し、その葉が
`Mark (M[n]) idx = W` に置換される（`m_7_4_Trans_Mark_seg` /
`m_7_4_Mark_Trans_repr`）。条件(II) の下では `w ≥ 2` が**常に**成立するので
`w = 1` の隅は存在しない。

依存する Isabelle の下部構造（未移植、~800 行）: `c2sx_N_facts` (86706, ~280 行、
run 算術)、`c2sx_mark_idx` (86987)、`c2sx_marked_jm1` (87021)、
`c2sx_mark_pin` (87033, ~170 行)。 -/

/-- Isabelle `c2sx_step` (pss_wip.thy:87202)。二重トラック不変量の帰納段。 -/
def CondII_step : Prop :=
  ∀ (M : PS) (n va : ℕ) (t₂ : BT) (s' b' : List Sym),
    RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    2 ≤ n →
    va = entry M 1 (Adm M (parent M 0 (Lng M - 1))) →
    t₂ ∈ T_B →
    scb_decomp (Trans (Pred M)) s'
      (flatBT (Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))))) b' →
    Mark (oper M (n - 1)) (Adm M (parent M 0 (Lng M - 1)))
      = Dprin (va : ℕ∞) (addBT t₂
          (multBT (Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))) (n - 2))) →
    scb_decomp (Trans (oper M (n - 1))) s'
      (flatBT (Dprin (va : ℕ∞) (addBT t₂
        (multBT (Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))) (n - 2))))) b' →
    (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1)))
        = Dprin (va : ℕ∞) (addBT t₂
            (multBT (Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))) (n - 1))) ∧
      scb_decomp (Trans (oper M n)) s'
        (flatBT (Dprin (va : ℕ∞) (addBT t₂
          (multBT (Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))) (n - 1))))) b')

/-! ## `c2sx_condII_masterCF` (pss_wip.thy:87430) — 組み立て

Isabelle の構造をそのまま:
1. ホストの mono 枝の scb 対 `(s₁,b₁)`（`Trans_c1_c2_decomp`）。
2. 二重トラック不変量 `INV` を `n` について帰納（base = `M[1] = Pred M`、
   step = `CondII_step`）。
3. `t₂ = t₃ +_B X^cnt₁`（`t2_split`）と `W = X`（`tailval`）で
   `t₂ +_B W^(m-1) = t₃ +_B X^(cnt₁ + (m-1))` に再結合し、`c = cnt₁ + (m-1) ≥ 1`
   を存在量化に落とす（＝A36 の数え上げ二分岐が消える場所）。 -/

/-- Isabelle `c2sx_condII_masterCF` (pss_wip.thy:87430) の**数え上げを露出した形**。
Isabelle の `y3j_mnp1 M m = if leftDj0 M then m else m - 1`（`8/Support_8_C.thy`:15042）
がここでは `cnt₁ + (m - 1)`（`cnt₁ = if condII_ldj M then 1 else 0`）として現れる。
`condII_masterCF_of_tailval` はこれを存在量化に落としたものである。

正確な数え上げは Naruyoko (2022) の 補題（基本列の関係）で要る（あちらは
`Trans(M)[k]` を与えて `Trans(M[m])` の側の添字を**指定**する必要がある）。 -/
theorem condII_masterCF_exact_of_tailval (hstep : CondII_step) :
    ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
      CondII_tailval M →
      ∃ (s b : List Sym) (u v : ℕ) (t₀ t₁ : BT) (cnt : ℕ),
        t₀ ∈ T_B ∧ t₁ ∈ T_B ∧ cnt ≤ 1 ∧
        scb_decomp (Trans M) s
          (flatBT (Dprin (u : ℕ∞)
            (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b ∧
        (∀ m, 1 ≤ m → Trans (oper M m)
          = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
              (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (cnt + (m - 1))))) ++ b)) := by
  intro M hR hmono hj1 hcond hTV
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  obtain ⟨hp0, e1z, _nadmj, _hj0pos, _hjm1lt, _hw2, _, _, ht2⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨hc1E, _hvE, ht2TB, _hc1TB⟩ := condII_c1_shape_holds M hR hmono hj1 hcond
  obtain ⟨hSP1, hSP2, hSP3⟩ := condII_t2_split_holds M hR hmono hj1 hcond
  have hc2V := condII_c2_val_holds M hR hmono hj1 hcond
  -- 記号
  set j₀ := parent M 0 (Lng M - 1) with hj₀
  set va := entry M 1 (Adm M j₀) with hva
  set v0 := entry M 1 j₀ with hv0
  set W := Trans (seg M j₀ (Lng M - 2)) with hW
  set X := Dprin (v0 : ℕ∞) (condII_t4 M) with hX
  set cnt1 : ℕ := (if condII_ldj M then 1 else 0) with hcnt1
  -- `Trans (Pred M) ≠ 0_B`
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have hT1ne : Trans (Pred M) ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT (Pred M) (RTPS_TPS _ hpredR)).mpr h
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hz
    omega
  -- (1) ホストの mono 枝の scb 対
  obtain ⟨s1, b1, dPM, dWM⟩ := Trans_c1_c2_decomp M hR hmono hL hT1ne
  have hC1M : transC1 M = Mark (Pred M) (Adm M j₀) := by
    simp [transC1, transJm1, transJ0, lastParent, lastIdx, hj₀]
  have dInit : scb_decomp (Trans (Pred M)) s1
      (flatBT (Mark (Pred M) (Adm M j₀))) b1 := by rw [← hC1M]; exact dPM
  -- `TV` の値化: `W = X`
  have hTVE : W = X := by rw [hW, hX, hv0, hj₀]; exact hTV
  -- (2) 二重トラック不変量
  have INV : ∀ n, 1 ≤ n →
      Mark (oper M n) (Adm M j₀)
          = Dprin (va : ℕ∞) (addBT (transT2 M) (multBT W (n - 1))) ∧
        scb_decomp (Trans (oper M n)) s1
          (flatBT (Dprin (va : ℕ∞) (addBT (transT2 M) (multBT W (n - 1))))) b1 := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (by omega)
    | succ n ih =>
        intro _
        by_cases hn0 : n = 0
        · -- base: `M[1] = Pred M`、`W^0 = 0_B`
          subst hn0
          have hoper1 : oper M 1 = Pred M := (pred_is_oper1 M hM hL).symm
          have hz : addBT (transT2 M) (multBT W (1 - 1)) = transT2 M := by
            simp only [multBT]
            exact addBT_zero_right_cf2 _
          constructor
          · rw [hoper1, hz, hc1E]
          · rw [hoper1, hz]
            rw [← hc1E]
            exact dInit
        · -- step
          have hn1 : 1 ≤ n := by omega
          have hn2 : 2 ≤ n + 1 := by omega
          obtain ⟨mkIH, dIH⟩ := ih hn1
          have e1 : n + 1 - 1 = n := by omega
          have e2 : n + 1 - 2 = n - 1 := by omega
          exact hstep M (n + 1) va (transT2 M) s1 b1 hR hmono hj1 hcond hn2
            hva.symm ht2TB dInit (by rw [e1]; rw [e2] at *; exact mkIH)
            (by rw [e1]; rw [e2] at *; exact dIH)
  -- (3) 閉形式（存在量化）
  refine ⟨s1, b1, va, v0, condII_t3 M, condII_t4 M, cnt1, hSP2, hSP3,
    (by rw [hcnt1]; split <;> omega), ?_, ?_⟩
  · -- `dM`: `c2_val` を `flatBT` 経由で読む
    have : transC2 M = Dprin (va : ℕ∞)
        (addBT (condII_t3 M) (Dprin (v0 : ℕ∞)
          (addBT (condII_t4 M) (Dprin 0 BZero)))) := hc2V
    rw [← this]
    exact dWM
  · intro m hm1
    obtain ⟨_, d⟩ := INV m hm1
    have hTmE : Trans (oper M m)
        = unflatBT (s1 ++ flatBT (Dprin (va : ℕ∞)
            (addBT (transT2 M) (multBT W (m - 1)))) ++ b1) := by
      calc Trans (oper M m)
          = unflatBT (flatBT (Trans (oper M m))) := (unflatBT_flat _).symm
        _ = _ := by rw [d.1]
    -- `t₂ +_B W^(m-1) = t₃ +_B X^(cnt₁ + (m-1))`
    have hceq : addBT (transT2 M) (multBT W (m - 1))
        = addBT (condII_t3 M) (multBT X (cnt1 + (m - 1))) := by
      rw [hTVE, hSP1, addBT_assoc_cf2, ← multBT_add_cf2]
    rw [hTmE, hceq]

/-- Isabelle `c2sx_condII_masterCF` (pss_wip.thy:87430) — `TV` 込みの 1:1 形。
`condII_masterCF_exact_of_tailval` の数え上げを存在量化に落としたもの。 -/
theorem condII_masterCF_of_tailval (hstep : CondII_step) :
    ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
      CondII_tailval M →
      ∃ (s b : List Sym) (u v : ℕ) (t₀ t₁ : BT), t₀ ∈ T_B ∧ t₁ ∈ T_B ∧
        scb_decomp (Trans M) s
          (flatBT (Dprin (u : ℕ∞)
            (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b ∧
        (∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
          = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
              (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b)) := by
  intro M hR hmono hj1 hcond hTV
  obtain ⟨s, b, u, v, t₀, t₁, cnt, ht₀, ht₁, _hcnt, hd, hall⟩ :=
    condII_masterCF_exact_of_tailval hstep M hR hmono hj1 hcond hTV
  exact ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd,
    fun m hm => ⟨cnt + (m - 1), by omega, hall m (by omega)⟩⟩

/-! ## 終切片の値、そして `CondII_masterCF` の drop-in

🚨 `CondII_TailvalAll` は Isabelle の `y3j_condII_tailval`
(layerC/pss_scratch.thy:17079) の **`RT_PS` 版**であり、Isabelle 側には
**存在しない**（あちらは `MST : M ∈ ST_PS`）。ビルド済み engine が
`CondII_masterCF` を `RTPS` 上で述べてしまっているため、drop-in にはこの
強い形が要る。ヘッダの 🚨🚨 を参照。 -/

/-- Isabelle `y3j_condII_tailval` (layerC/pss_scratch.thy:17079) の **`RT_PS` 版**。
Isabelle は `ljx_TVall_of_fin` ＋ `ot9_FINRC` で `ST_PS` 上に落とす。

🚨 **この `RT_PS` 版は偽**（`lean/8/8.3-condII-tailval.lean` の
`not_CondII_TailvalAll` が反例 `(0,0)(1,1)(2,2)(2,0)(2,2)(2,0)` で機械証明）。
史料として残すだけで、**使うな**。実在するのは下の `CondII_TailvalAll_ST`。 -/
def CondII_TailvalAll : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    CondII_tailval M

/-- Isabelle `y3j_condII_tailval` (layerC/pss_scratch.thy:17076) の **1:1** 移植。
あちらは `ljx_TVall_of_fin[OF ot9_FINRC]` で**無条件に落ちる定理**である
（`CondII_TailvalAll` の `RT_PS` 版とは違い、これは実在する）。 -/
def CondII_TailvalAll_ST : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    CondII_tailval M

/-- **本ファイルの成果物**: ビルド済み «8».«8.3-TransCondII-engine» の
`CondII_masterCF` を、2 本の名前付き残差から drop-in で充足する（house pattern）。
`exchII_of_masterCF` に食わせれば `FseqDesc_exchII` が、同型の `OTdisp_exchII`
も同時に落ちる。 -/
theorem condII_masterCF_holds (hstep : CondII_step) (hTV : CondII_TailvalAll_ST) :
    CondII_masterCF := by
  intro M hST hmono hj1 hcond
  have hR : RTPS M := STPS_RTPS M hST
  exact condII_masterCF_of_tailval hstep M hR hmono hj1 hcond
    (hTV M hST hmono hj1 hcond)

/-- 親による独立検証用: `CondII_masterCF` が実際に `FseqDesc_exchII` を出すこと
（`exchII_of_masterCF` はビルド済み engine :223）。 -/
theorem condII_exchII_of_residuals (hstep : CondII_step) (hTV : CondII_TailvalAll_ST) :
    FseqDesc_exchII :=
  exchII_of_masterCF (condII_masterCF_holds hstep hTV)

/-! ## 🎯 Isabelle に裏打ちされた `exchII` 供給ルート（本ラウンドの主成果）

上の `condII_masterCF_holds` は engine の `CondII_masterCF` を drop-in するために
`CondII_TailvalAll`（**RT_PS 版**）を要求する。しかしヘッダ 🚨🚨 のとおり、これは
Isabelle corpus に**存在しない**（`y3j_condII_tailval` は `MST : M ∈ ST_PS`。
その供給連鎖 `ljx_TVall_of_fin` (pss_wip.thy:115242) ＋ `ot9_FINRC`
(pss_scratch.thy:10032) も**両方とも ST_PS 束縛**）。

**ところが `RT_PS` 版は誰も必要としていない**: `CondII_masterCF` の唯一の消費者で
ある `FseqDesc_exchII` (`8.7-fseq-descend`:78) と `OTdisp_exchII`
(`8.7-Trans-preserves-OT`:88) は**どちらも仮定が `STPS N`** であり（両者は
byte-identical）、engine の `exchII_of_masterCF` は `STPS_RTPS` で `RTPS` に
落としてから `CondII_masterCF` を呼んでいる。すなわち engine が
`CondII_masterCF` を `RTPS` 上で述べたのは**不要な強化**であって、
その強化のぶんだけ Isabelle corpus の外に出てしまっている。

そこで本節は engine の `CondII_masterCF` を**経由せず**、
`CondII_step`（Isabelle `c2sx_step` の 1:1、`RT_PS`）と
`CondII_TailvalAll_ST`（Isabelle `y3j_condII_tailval` の 1:1、**あちらでは定理**）
から `FseqDesc_exchII` を直接供給する。`condII_exchII_of_residuals` との違いは
**残差 2 本が両方とも Isabelle 側の定理である**こと＝移植可能であること。

engine 側を直すなら `CondII_masterCF` の `RTPS M` を `STPS M` に変えるだけでよい
（`exchII_of_masterCF` の `STPS_RTPS` の行が不要になる）。 -/


/-- Isabelle `operB_marked_scb_value` (pss_wip.thy:37100)。engine :165 の
private 版と同一内容（private は module を跨げないので複製）。 -/
private theorem operB_marked_scb_value_cf2 {t₀ t₁ t : BT} {u v n : ℕ}
    {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b) :
    operB t (numBT n)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b) := by
  have hd2 := scb_fseq_decomp (n := n) ht₀ ht₁ ht hd
  calc operB t (numBT n)
      = unflatBT (flatBT (operB t (numBT n))) := (unflatBT_flat _).symm
    _ = _ := by rw [hd2.1]

/-- Isabelle `c2ex_exch_of_lhs_closed_ex` (pss_wip.thy:70717)。engine :185 の
private 版と同一内容（同上の理由で複製）。 -/
private theorem exch_of_lhs_closed_ex_cf2
    {M : PS} {n u v : ℕ} {t₀ t₁ : BT} {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (htT : Trans M ∈ T_B)
    (hd : scb_decomp (Trans M) s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b)
    (hlhs : ∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b))
    (hn : 1 < n) :
    ∃ k, Trans (oper M n) = operB (Trans M) (numBT k) := by
  obtain ⟨c, hc1, hlc⟩ := hlhs n hn
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  exact ⟨k, by rw [hlc, operB_marked_scb_value_cf2 (n := k) ht₀ ht₁ htT hd]⟩

/-- **本ラウンドの主成果**: `FseqDesc_exchII` を、**両方とも Isabelle の定理である**
2 本の残差（`CondII_step` ＝ `c2sx_step`、`CondII_TailvalAll_ST` ＝
`y3j_condII_tailval`）から供給する。engine の `CondII_masterCF`（RT_PS 版、
Isabelle に裏打ちなし）を経由しない。`OTdisp_exchII` は byte-identical なので
同時に落ちる（下の `condII_OTdispII_of_ST_residuals`）。 -/
theorem condII_exchII_of_ST_residuals
    (hstep : CondII_step) (hTV : CondII_TailvalAll_ST) : FseqDesc_exchII := by
  intro N m hST hmono hj1 hcond hm
  have hR : RTPS N := STPS_RTPS N hST
  have htT : Trans N ∈ T_B := Trans_mem_T_B N hR
  obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, hlhs⟩ :=
    condII_masterCF_of_tailval hstep N hR hmono hj1 hcond
      (hTV N hST hmono hj1 hcond)
  exact exch_of_lhs_closed_ex_cf2 ht₀ ht₁ htT hd hlhs hm

/-- `OTdisp_exchII`（OT 所属柱）も同じ 2 本から落ちる（`FseqDesc_exchII` と
byte-identical であることの機械的確認を兼ねる）。 -/
theorem condII_OTdispII_of_ST_residuals
    (hstep : CondII_step) (hTV : CondII_TailvalAll_ST) : OTdisp_exchII :=
  condII_exchII_of_ST_residuals hstep hTV

#print axioms condII_host_basic_holds
#print axioms condII_c1_shape_holds
#print axioms condII_c2_val_holds
#print axioms condII_t2_split_holds
#print axioms Trans_c1_c2_decomp
#print axioms condII_masterCF_of_tailval
#print axioms condII_masterCF_holds
#print axioms condII_exchII_of_residuals
#print axioms condII_exchII_of_ST_residuals
#print axioms condII_OTdispII_of_ST_residuals

end PSS
