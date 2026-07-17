import «8».«8.3-condII-masterCF»
import «8».«8.3-kind0-base-basepoint»
import «8».«8.3-kind0-branch-rule»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.2-scb-unique»
import «7».«7.2-scb-compose»
import «7».«7.2-add-scb»
import «7».«7.4-RightNodes-Mark»
import «6».«6.8-standard-slice-Br-descending»
import «6».«6.6-reduced-slice»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.5-Red-le-core»

/-!
# §8.3 条件(II) — `CondII_step`（Isabelle `c2sx_step`）の討伐

- 原文: `tmp/content.md` 3956–4247（§8.3 命題（条件(II)の下での `Trans` と基本列の
  交換関係））。逐語形は `p_8_3_TransCondII_oper_descend`
  (isabelle/pss_paper.thy:1863)。

- 担当: ビルド済み «8».«8.3-condII-masterCF» が露出した名前付き `Prop`
  `CondII_step`（同 :552）ただ 1 本。これは `CondII_masterCF` の残差 2 本のうちの
  1 本であり、`FseqDesc_exchII`（降下柱）と `OTdisp_exchII`（OT 所属柱）は
  byte-identical なので**両柱が同時にこれに依存する**。

- **結果: `CondII_step` は無条件で完全証明された**（sorry 0、axioms =
  propext/Classical.choice/Quot.sound）。`c2sx_` 連鎖の下部構造（Isabelle ~800 行）
  はすべて移植済みで、**新たな名前付き残差は 1 本も導入していない**。

- Isabelle 側の連鎖（`c2sx_` corpus, isabelle/layerB/pss_wip.thy）:
  | Isabelle | 行 | 本ファイル | 状態 |
  |---|---|---|---|
  | `c2sx_step` | 87202 | **`condII_step_holds`** | ✅ **無仮定**（＝`CondII_step` 討伐） |
  | `c2sx_N_facts` | 86706 | `c2s_nums`/`c2s_struct`/`c2s_append`/`c2s_predN`/`c2s_eNidx`/`c2s_segtail`/`c2s_marked_idx`/`c2s_le0_mono`/`c2s_parN`/`c2s_AdmN`/`c2s_T1N`/`c2s_condVN` | ✅ 無仮定（必要な 14/17 結論） |
  | `c2sx_mark_idx` | 86987 | `c2s_mark_idx` | ✅ 無仮定 |
  | `c2sx_marked_jm1` | 87021 | `c2s_marked_jm1` | ✅ 無仮定 |
  | `c2sx_mark_pin` | 87033 | `c2s_mark_pin` | ✅ 無仮定 |
  | `scb_context_eq_of_prefix` | 39775 | `scb_context_eq_of_prefix_c2s` | ✅ 無仮定 |
  | `c2sx_host_basic` (7)(8)(12) | 86474 | `condII_host_extra_c2s` | ✅ 無仮定（下記 🚨） |
  | `wnx_run_nadm` / `wnx_run_step_entries`(2) | 80695/80710 | `run_nadm_c2s` / `run_step_entry1_c2s` | ✅ 無仮定 |
  | `wnx_adjacent_parent1` | 80633 | `adjacent_parent1_c2s` | ✅ 無仮定 |
  | `scx_le0_to_parent` | 82278 | `le0_to_parent_c2s` | ✅ 無仮定 |
  | `scb_Dpt_lift` | 1663 | `scb_Dprin_lift_c2s` | ✅ 無仮定 |
  | `Lng_operI` / `operI_Suc_append` / `scx_map_block_seg` | —/17621/82210 | `Lng_oper_c2s` / `oper_Suc_append_c2s` / `map_block_seg_c2s` | ✅ 無仮定 |

- **Isabelle から短縮できた 2 点**（移植不要と判明した重い補題）:
  1. `oper_d0zero_le0_lift` (pss_mechanized.thy:52265, ~80 行) — `N_facts`(16) の
     `le0 (M[n]) 0 idx`。Lean は**行 0 の祖先関係が値で特徴付けられる**
     （`ancestor_basic_1` / `parent_exists_3`）ので、ビルド済み `kind0_branch_rule`
     の辺 `j₀-1 <^Next₀ idx` と `0 ≤₀ j₀-1` を繋ぐだけで済む（§3–§4）。
  2. `dkax_slice_principal_gen` (pss_wip.thy:71793) — `W` が単項 principal（頭 `v₀`）
     であること。ビルド済み `Mark_leftend_form_proper`（§7.4）＋ `c2s_mark_idx`
     （`W = Mark (M[n]) idx`）で直接得られる（§8）。
  さらに `N_facts`(5)（`Adm N (j₀-1) = Adm M j₀`）は、Isabelle が `Adm_def` の `Max`
  を直接いじり `adm` の接頭辞一致補題を要するのに対し、ビルド済み `admof_slice`
  で `M[n]`/`M` 双方の切片に落とすと **`Adm M (j₀-1) = Adm M j₀`**（`Adm_max` の
  両向きのみ）に還元される。

- 🚨 **`«8».«8.1-condI-masterCF` は import できない**（本ファイル最大の運用上の
  所見）。同ファイルは `scx_Lng_oper` / `scx_take_RTPS` / `scx_seg0_eq_take` /
  `scx_map_block_seg` という**まさに本移植が要する kind-0 汎用補助**を公開して
  いるが、**ビルドが通っていない**ため import すると header が静かに毒され
  （`trivial` すら unknown になる）、エラーではなく全 identifier の消失として
  現れる。よって本ファイルは同等物を private に再証明した（`_c2s` 接尾辞）。
  ⚠️ 同ファイルの header は「§5 で `CondIcf_stepA`/`CondIcf_stepB`/
  `CondIcf_markPinCtx` を露出する」と書くが、**実体は存在しない**（`scx_Lng_oper`
  で終わっている＝header の overclaim）。`CondI_masterCF` は未討伐。

- 🚨 **ビルド済み `CondII_host_basic` 束は Isabelle `c2sx_host_basic` の 12 結論の
  うち 9 本（(1)-(6)(9)(10)(11)）しか持たない**。`transCondV N`（`N_facts`(7)）と
  `le0 (M[n]) 0 idx`（同 (16)）が要する (7)(8)(12) は落ちているので、§2 の
  `condII_host_extra_c2s` で再証明した（`wnx_run_step_entries` 経由）。

- 依存（**ビルド済みのみ** import）: `8.3-condII-masterCF`（`CondII_step` の定義、
  `condII_host_basic_holds`, `condII_masterCF_holds`, `condII_exchII_of_residuals`）、
  `8.3-kind0-base-basepoint`（`kind0_base_basepoint`）、
  `8.3-kind0-branch-rule`（`kind0_branch_rule`）、`7.4-Mark-Trans-repr`
  （`Mark_Trans_repr`, `Mark_Trans_repr_zero`）、`7.4-RightNodes-Mark`
  （`Mark_leftend_form_proper`）、`7.3-Trans-preserves-zeroT`
  （`Trans_preserves_zeroT`）、`7.2-scb-unique`
  （`scb_unique_decomp_unconditional`）、`7.2-scb-compose`（`scb_compose`）、
  `7.2-add-scb`（`add_scb_marked` = conj1, `add_scb_replace_last` = conj2,
  `addBT_mem_T_B`）、`6.8-standard-slice-Br-descending`（`oper_d0zero_expand_68`,
  `entry_oper_lt_last_68`）、`6.6-reduced-slice`（`RTPS_initial_slice`）、
  `6.6-reduced-iff-condAB`（`RTPS_condAB`）、`6.5-Red-le-core`（`RedCondA_apply`）。
  推移的に `6.3-admof-slice`（`admof_slice`, `Adm_max`, `Adm_adm`, `Adm_le`）、
  `7.3-Trans-welldefined`（`Marked_Pred_Adm`, `unflatBT_flat`）。

- 🚨🚨 **下流注意**: `CondII_step` は落ちたが、その RT_PS 水準の消費者
  （`CondII_TailvalAll` / `CondII_masterCF`）は**偽**である（姉妹ファイル
  `«8».«8.3-condII-tailval»` が緑で反証。§9 参照）。よって本ファイルは
  `condII_masterCF_holds` への 1 行配線を**意図的に置かない**（空虚になるため）。
  `CondII_step` の健全な用途は **ST_PS 版** `condII_exchII_of_ST_residuals` の
  第 1 引数のみ。

- 状態: ✅ **GREEN・無仮定**（sorry 0）。公開定理は `condII_step_holds` **1 本**
  のみで、axioms は propext/Classical.choice/Quot.sound。**残差ゼロ**
  （新たな名前付き `Prop` を導入していない）。空虚な系は置いていない。
-/

namespace PSS

/-! ## §1 kind-0 反復の構造（Isabelle `kind0_parent_facts` / `Lng_operI` /
`operI_Suc_append` / `scx_map_block_seg`）

条件(II) は `entry M 1 (Lng M - 1) = 0`（`e1z`）と `hasParent M 0 (Lng M - 1)`
（`hp0`）を満たすので、kind-0 のタイル貼り（§6.8 `oper_d0zero_expand_68`）が
そのまま使える。以下は `«8».«8.1-condI-masterCF»` が公開しているはずの補助の
再証明（同ファイルは未ビルドで import 不可）。 -/

/-- Isabelle `kind0_parent_facts` (pss_wip.thy:13671) の必要部分。 -/
private theorem kind0_facts_c2s (M : PS)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true ∧
    parent M 0 (Lng M - 1) < Lng M - 1 ∧
    ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
    hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
    1 < Lng M := by
  have hpar := hasParent_next_fseq M 0 (Lng M - 1) hp0
  have h0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hpar
  have hfacts := h0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hfacts
  have hlt : parent M 0 (Lng M - 1) < Lng M - 1 := hfacts.1.1.2
  have he0 : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) :=
    hfacts.1.2
  have hidx : idx1 M (Lng M - 1) = 0 := by simp [idx1, e1z]
  exact ⟨h0, hlt, by omega, by rw [hidx]; exact hp0, by omega⟩

private theorem length_flatMap_const_c2s {α β : Type} (l : List α) (B : List β) :
    (l.flatMap (fun _ => B)).length = l.length * B.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Isabelle `Lng_operI`。kind-0 の反復の長さ。 -/
private theorem Lng_oper_c2s (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    Lng (oper M n) =
      parent M 0 (Lng M - 1) + n * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
  obtain ⟨_, hj0lt, hnz, hp, hL⟩ := kind0_facts_c2s M hp0 e1z
  have hexp := oper_d0zero_expand_68 M n hL hnz hp e1z
  simp only at hexp
  have hj0L : parent M 0 (Lng M - 1) ≤ Lng M := by omega
  rw [hexp]
  simp only [Lng, List.length_append, length_flatMap_const_c2s,
    List.length_take, List.length_map, List.length_range, List.length_range',
    Nat.min_eq_left hj0L]

/-- Isabelle `operI_Suc_append` (pss_wip.thy:17621)。 -/
private theorem oper_Suc_append_c2s (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    oper M (n + 1) = oper M n ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
  obtain ⟨_, _, hnz, hp, hL⟩ := kind0_facts_c2s M hp0 e1z
  have hn := oper_d0zero_expand_68 M n hL hnz hp e1z
  have hsn := oper_d0zero_expand_68 M (n + 1) hL hnz hp e1z
  simp only at hn hsn
  rw [hn, hsn, List.range_succ, List.flatMap_append]
  simp [List.append_assoc]

/-- Isabelle `scx_map_block_seg` (pss_wip.thy:82210)。追加ブロックは切片。 -/
private theorem map_block_seg_c2s (M : PS) (j0 j1 : ℕ) (h1 : 1 ≤ j1) :
    (List.range' j0 (j1 - j0)).map (fun j => (entry M 0 j, entry M 1 j))
      = seg M j0 (j1 - 1) := by
  unfold seg
  congr 2
  omega

/-- `seg K 0 j = K.take (j+1)`（Isabelle `seg_0_eq_take`）。 -/
private theorem seg0_eq_take_c2s (K : PS) (j : ℕ) (hj : j < Lng K) :
    seg K 0 j = K.take (j + 1) := by
  simpa using seg_eq_take_drop_adm K 0 j (Nat.zero_le _) hj

/-! ## §2 非許容 run の算術（Isabelle `wnx_run_nadm` 80695 /
`wnx_adjacent_parent1` 80633 / `wnx_run_step_entries` 80710）

`c2sx_host_basic` の結論 (7)(8)(12) は **Lean の `CondII_host_basic` 束には
入っていない**（同束は 12 結論のうち (1)-(6)(9)(10)(11) の 9 本のみ）。
`transCondV N`（`N_facts` (7)）と `le0 (M[n]) 0 idx`（同 (16)）はそれらを要する
ので、ここで private に再証明する。 -/

/-- Isabelle `wnx_run_nadm` (pss_wip.thy:80695)。`Adm_M(j₀)` より上・`j₀` 以下は
すべて非許容（`Adm` の最大性そのもの）。 -/
private theorem run_nadm_c2s (M : PS) (j0 s : ℕ) (_hnadm : adm M j0 = false)
    (lo : Adm M j0 < s) (hi : s ≤ j0) : adm M s = false := by
  by_contra h
  have h' : adm M s = true := by simpa using h
  have := Adm_max M s j0 h' hi
  omega

/-- Isabelle `wnx_adjacent_parent1` (pss_wip.thy:80633)。隣接する行 1 の辺は
一意な親を与える。 -/
private theorem adjacent_parent1_c2s (M : PS) (t : ℕ)
    (hnx : nextR M 1 t (t + 1) = true) :
    hasParent M 1 (t + 1) = true ∧ parent M 1 (t + 1) = t := by
  refine ⟨(hasParent_iff_unique_fseq M 1 (t + 1)).mpr
      ⟨t, hnx, fun q hq => nextR1_unique_mr M q t (t + 1) hq hnx⟩,
    parent_eq_of_unique_fseq M 1 (t + 1) t hnx
      (fun q hq => nextR1_unique_mr M q t (t + 1) hq hnx)⟩

/-- Isabelle `wnx_run_step_entries` (pss_wip.thy:80710) の結論 (2)。
非許容 run の内部では行 1 の係数がちょうど 1 ずつ上がる（条件(A)）。 -/
private theorem run_step_entry1_c2s (M : PS) (j0 s : ℕ) (hR : RTPS M)
    (jL : j0 < Lng M) (nadm0 : adm M j0 = false)
    (lo : Adm M j0 < s) (hi : s ≤ j0) :
    entry M 1 s = entry M 1 (s - 1) + 1 := by
  have nadms : adm M s = false := run_nadm_c2s M j0 s nadm0 lo hi
  have hna : nadm M s = true := by simpa [adm] using nadms
  have hsL : ¬ (Lng M < s) := by omega
  have hedges : nextR M 1 (s - 1) s = true ∧ nextR M 1 s (s + 1) = true := by
    have h := hna
    simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | h
    · exact absurd h hsL
    · exact h
  have hspos : 0 < s := by omega
  -- `s = t + 1` に書き換えて隣接親を読む
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hnx : nextR M 1 t (t + 1) = true := by simpa using hedges.1
  obtain ⟨hp1, hpar1⟩ := adjacent_parent1_c2s M t hnx
  have hA : RedCondA M = true := (RTPS_condAB M hR).1
  have htL : t + 1 < Lng M := by omega
  have := RedCondA_apply M hA 1 (t + 1) (by omega) htL hp1
  rw [hpar1] at this
  simpa using this.symm

/-- Isabelle `scx_le0_to_parent` (pss_wip.thy:82278)。`a ≤₀ j₁`・`j₀ <^Next₀ j₁`・
`a ≠ j₁` なら `a ≤₀ j₀`。（`«8».«8.1-condI-masterCF»` が公開しているが未ビルドの
ため再証明。） -/
private theorem le0_to_parent_c2s (M : PS) (a j0 j1 : ℕ) (hM : TPS M)
    (hle : le0 M a j1 = true) (hedge : nextrel0 M j0 j1 = true) (hne : a ≠ j1) :
    le0 M a j0 = true := by
  have hleR : leR M 0 a j1 = true := by simpa [leR] using hle
  have hedge' := hedge
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hedge'
  obtain ⟨⟨⟨⟨hj0L, hj1L⟩, hj0j1⟩, he0⟩, hmin⟩ := hedge'
  have haL : a < Lng M := by
    have := hle
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  have hale : a ≤ j1 := by
    have := hle
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at this
    exact le0Aux_index_fseq this.2
  have halt : a < j1 := lt_of_le_of_ne hale hne
  have haj0 : a ≤ j0 := by
    by_contra hc
    have hj0a : j0 < a := by omega
    have hge : entry M 0 j1 ≤ entry M 0 a := by
      have := hmin a halt
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact h
    have hlt : entry M 0 a < entry M 0 j1 :=
      ancestor_basic_1 M a j1 j1 hM halt le_rfl hleR
    omega
  rcases Nat.eq_or_lt_of_le haj0 with heq | hlt2
  · subst heq
    have : leR M 0 a a = true := leR0_refl_68 M a haL
    simpa [leR] using this
  · have : leR M 0 a j0 = true := by
      refine parent_exists_3 M a j0 hM hlt2 hj0L ?_
      intro j haj hjj0
      exact ancestor_basic_1 M a j j1 hM haj (by omega) hleR
    simpa [leR] using this

/-- Isabelle `c2sx_host_basic` (pss_wip.thy:86474) の結論 (7)(8)(12)
（Lean のビルド済み `CondII_host_basic` 束が**落としている** 3 本）。 -/
private theorem condII_host_extra_c2s (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) :
    entry M 1 (parent M 0 (Lng M - 1))
        = entry M 1 (parent M 0 (Lng M - 1) - 1) + 1 ∧
    0 < entry M 1 (parent M 0 (Lng M - 1)) ∧
    le0 M 0 (parent M 0 (Lng M - 1)) = true := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hp0, e1z, nadmj, hj0pos, hjm1lt, _hw2, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨hedge, hj0lt, _, _, hL⟩ := kind0_facts_c2s M hp0 e1z
  have hj0L : parent M 0 (Lng M - 1) < Lng M := by omega
  -- (7) run の一歩（`s = j₀`）
  have run1 : entry M 1 (parent M 0 (Lng M - 1))
      = entry M 1 (parent M 0 (Lng M - 1) - 1) + 1 :=
    run_step_entry1_c2s M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1))
      hR hj0L nadmj hjm1lt le_rfl
  -- (12) 単調性を親へ降ろす
  have hle01 : le0 M 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    simpa [leR] using hh.2
  have hle0j0 : le0 M 0 (parent M 0 (Lng M - 1)) = true :=
    le0_to_parent_c2s M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) hM hle01 hedge
      (by omega)
  exact ⟨run1, by omega, hle0j0⟩

/-! ## §3 行 0 の祖先関係の道具立て（値特徴付け）

Isabelle は `le0` を rtrancl で扱い、`oper_d0zero_le0_lift`
(pss_mechanized.thy:52265, ~80 行) でタイル越しに持ち上げるが、Lean では
**行 0 の祖先関係が値で特徴付けられる**（`ancestor_basic_1`: `le0` → 値の狭義増加、
`parent_exists_3`: 値 → `le0`）ので、持ち上げ補題を移植せずに済む。
`N_facts` (16) は「branch rule の辺 `j₀-1 <^Next₀ idx` ＋ `0 ≤₀ j₀-1`」で構成する
（`kind0_branch_rule` が既にビルド済みで辺を与える）。 -/

/-- 行 0 の親辺は祖先関係を与える（Isabelle `poper_nextR_imp_le0`）。 -/
private theorem le0_of_nextR0_c2s (M : PS) (a b : ℕ) (hM : TPS M)
    (h : nextR M 0 a b = true) : leR M 0 a b = true := by
  have h0 : nextrel0 M a b = true := by simpa [nextR] using h
  have hh := h0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hh
  obtain ⟨⟨⟨⟨_haL, hbL⟩, hab⟩, he⟩, hmin⟩ := hh
  refine parent_exists_3 M a b hM hab hbL ?_
  intro j haj hjb
  rcases Nat.lt_or_ge j b with hjlt | hjge
  · have hj := hmin j hjlt
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at hj
    rcases hj with h' | h'
    · omega
    · omega
  · have hjeq : j = b := by omega
    rw [hjeq]
    exact he

/-- Isabelle `le0_trans` の値特徴付けによる構成。 -/
private theorem le0_trans_c2s (M : PS) (a b c : ℕ) (hM : TPS M)
    (hab : leR M 0 a b = true) (hbc : leR M 0 b c = true)
    (halt : a < b) (hblt : b < c) (hcL : c < Lng M) :
    leR M 0 a c = true := by
  apply parent_exists_3 M a c hM (by omega) hcL
  intro j haj hjc
  by_cases hjb : j ≤ b
  · exact ancestor_basic_1 M a j b hM haj hjb hab
  · have h1 : entry M 0 a < entry M 0 b :=
      ancestor_basic_1 M a b b hM halt le_rfl hab
    have h2 : entry M 0 b < entry M 0 j :=
      ancestor_basic_1 M b j c hM (by omega) hjc hbc
    omega

/-- `0` からの行 0 祖先関係は下向きに閉じる（`entry M 0 0` が `[0,b]` の最小値
だから）。**行 0 に限る**: 一般の `a` からの祖先関係は下向きに閉じない。 -/
private theorem le0_from0_down_c2s (M : PS) (a b : ℕ) (hM : TPS M)
    (hb : leR M 0 0 b = true) (hab : a ≤ b) (haL : a < Lng M) :
    leR M 0 0 a = true := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · exact leR0_refl_68 M 0 haL
  · exact parent_exists_3 M 0 a hM hapos haL
      (fun j hj hja => ancestor_basic_1 M 0 j b hM hj (by omega) hb)

/-- 値一致による行 0 祖先関係の移送（両向き。`c` 以下で entry が一致すれば
`[a,b] ⊆ [0,c]` 上の `le0` は移る）。 -/
private theorem le0_transfer_c2s (A B : PS) (a b c : ℕ) (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ z, z ≤ c → entry A 0 z = entry B 0 z)
    (hab : a < b) (hbc : b ≤ c) (hbB : b < Lng B)
    (hle : leR A 0 a b = true) : leR B 0 a b = true := by
  refine parent_exists_3 B a b hBT hab hbB ?_
  intro j haj hjb
  rw [← agree a (by omega), ← agree j (by omega)]
  exact ancestor_basic_1 A a j b hAT haj hjb hle

/-! ## §4 `c2sx_N_facts` (pss_wip.thy:86706) — 最終ブロック開始点の接頭辞 `N`

`idx = j₀ + (n-1)w`（最終ブロックの先頭）、`N = seg (M[n]) 0 idx`。 -/

/-- 最終ブロックの開始位置 `idx = j₀ + (n-1)w`。 -/
private def c2sIdx (M : PS) (n : ℕ) : ℕ :=
  parent M 0 (Lng M - 1) + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))

/-- `N = seg (M[n]) 0 idx`（最終ブロック開始までの接頭辞）。 -/
private def c2sN (M : PS) (n : ℕ) : PS := seg (oper M n) 0 (c2sIdx M n)

/-- `c2sx_N_facts` の数値部分（`idx` の位置と `M[n]` の長さ）。 -/
private theorem c2s_nums (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    0 < parent M 0 (Lng M - 1) ∧
    parent M 0 (Lng M - 1) < Lng M - 1 ∧
    2 ≤ (Lng M - 1) - parent M 0 (Lng M - 1) ∧
    parent M 0 (Lng M - 1) + ((Lng M - 1) - parent M 0 (Lng M - 1)) ≤ c2sIdx M n ∧
    parent M 0 (Lng M - 1) < c2sIdx M n ∧
    1 < c2sIdx M n ∧
    Lng (oper M n) = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
  obtain ⟨hp0, e1z, _nadmj, hj0pos, _hjm1lt, hw2, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_c2s M hp0 e1z
  have hw2' : 2 ≤ (Lng M - 1) - parent M 0 (Lng M - 1) := by omega
  -- `idxlb`: `1 * w ≤ (n-1) * w`
  have hmul : 1 * ((Lng M - 1) - parent M 0 (Lng M - 1))
      ≤ (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hidxE : c2sIdx M n
      = parent M 0 (Lng M - 1)
        + (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1)) := rfl
  -- `n * w = (n-1) * w + w`
  have hmulexp : n * ((Lng M - 1) - parent M 0 (Lng M - 1))
      = (n - 1) * ((Lng M - 1) - parent M 0 (Lng M - 1))
        + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.succ_mul]
  have hLngMn : Lng (oper M n)
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := by
    rw [Lng_oper_c2s M n hp0 e1z, hmulexp, hidxE]
    omega
  refine ⟨hj0pos, hj0lt, hw2', by omega, by omega, by omega, hLngMn⟩

/-- `c2sx_N_facts` (15)(3)(9): `N = take (idx+1) (M[n])`、`Lng N = idx+1`、
`N ∈ RT_PS`。 -/
private theorem c2s_struct (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    c2sN M n = (oper M n).take (c2sIdx M n + 1) ∧
    Lng (c2sN M n) = c2sIdx M n + 1 ∧
    RTPS (c2sN M n) := by
  obtain ⟨_, _, hw2, _, _, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hidxlt : c2sIdx M n < Lng (oper M n) := by
    show c2sIdx M n < (oper M n).length
    omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have htake : c2sN M n = (oper M n).take (c2sIdx M n + 1) :=
    seg0_eq_take_c2s (oper M n) (c2sIdx M n) hidxlt
  have hle : c2sIdx M n ≤ Lng (oper M n) - 1 := by
    show c2sIdx M n ≤ (oper M n).length - 1
    omega
  refine ⟨htake, ?_, ?_⟩
  · rw [htake]
    show ((oper M n).take (c2sIdx M n + 1)).length = c2sIdx M n + 1
    rw [List.length_take]
    omega
  · exact RTPS_initial_slice (oper M n) (c2sIdx M n) hMnR hle

/-- ブロック分解 `M[n] = M[n-1] @ B`（`B` は最終ブロック）と
`Lng (M[n-1]) = idx`。Isabelle の `app` / `LngMn1`。 -/
private theorem c2s_append (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    oper M n = oper M (n - 1) ++
        (List.range' (parent M 0 (Lng M - 1))
          ((Lng M - 1) - parent M 0 (Lng M - 1))).map
          (fun j => (entry M 0 j, entry M 1 j)) ∧
      Lng (oper M (n - 1)) = c2sIdx M n := by
  obtain ⟨hp0, e1z, _, _, _, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  have hn : n - 1 + 1 = n := by omega
  constructor
  · have h := oper_Suc_append_c2s M (n - 1) hp0 e1z
    rw [hn] at h
    exact h
  · have h := Lng_oper_c2s M (n - 1) hp0 e1z
    exact h

/-- `c2sx_N_facts` (8): `Pred N = M[n-1]`。 -/
private theorem c2s_predN (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    Pred (c2sN M n) = oper M (n - 1) := by
  obtain ⟨_, _, hw2, _, _, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, hLngN, _⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  obtain ⟨happ, hLn1⟩ := c2s_append M n hR hmono hj1 hcond hn2
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  -- `Pred N = N.dropLast`（`Lng N = idx+1 > 1`）
  have hPred : Pred (c2sN M n) = (c2sN M n).dropLast := by
    simp only [Pred]
    rw [if_neg (by omega : ¬ Lng (c2sN M n) ≤ 1)]
  -- `N.dropLast = (M[n]).take idx`
  have hlenTake : ((oper M n).take (c2sIdx M n + 1)).length = c2sIdx M n + 1 := by
    rw [List.length_take]; omega
  have hdl : (c2sN M n).dropLast = (oper M n).take (c2sIdx M n) := by
    rw [htake, List.dropLast_eq_take, hlenTake, List.take_take]
    congr 1
    omega
  -- `take idx (M[n-1] @ B) = M[n-1]`
  have hlenP : (oper M (n - 1)).length = c2sIdx M n := hLn1
  rw [hPred, hdl, happ, List.take_left' hlenP]

/-- `c2sx_N_facts` (13): `entry N 1 idx = entry M 1 j₀`（最終ブロックの先頭）。 -/
private theorem c2s_eNidx (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    entry (c2sN M n) 1 (c2sIdx M n) = entry M 1 (parent M 0 (Lng M - 1)) ∧
    entry (oper M n) 1 (c2sIdx M n) = entry M 1 (parent M 0 (Lng M - 1)) := by
  obtain ⟨_, _, hw2, _, _, _, _⟩ := c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, _, _⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  obtain ⟨happ, hLn1⟩ := c2s_append M n hR hmono hj1 hcond hn2
  have hlenP : (oper M (n - 1)).length = c2sIdx M n := hLn1
  -- `(M[n])[idx] = B[0] = (M₀,ⱼ₀, M₁,ⱼ₀)`
  have hget : (oper M n)[c2sIdx M n]?
      = some (entry M 0 (parent M 0 (Lng M - 1)),
              entry M 1 (parent M 0 (Lng M - 1))) := by
    rw [happ, List.getElem?_append_right (by omega), hlenP]
    obtain ⟨k, hk⟩ : ∃ k, (Lng M - 1) - parent M 0 (Lng M - 1) = k + 1 :=
      ⟨(Lng M - 1) - parent M 0 (Lng M - 1) - 1, by omega⟩
    simp [hk, List.range']
  have hMn : entry (oper M n) 1 (c2sIdx M n)
      = entry M 1 (parent M 0 (Lng M - 1)) := by
    simp only [entry, hget]
    simp
  refine ⟨?_, hMn⟩
  rw [htake, entry_take (oper M n) (c2sIdx M n + 1) 1 (c2sIdx M n) (by omega)]
  exact hMn

/-- `c2sx_N_facts` (14): 最終ブロックは `M` の切片そのもの。 -/
private theorem c2s_segtail (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    seg (oper M n) (c2sIdx M n) (Lng (oper M n) - 1)
      = seg M (parent M 0 (Lng M - 1)) (Lng M - 2) := by
  obtain ⟨_, _, hw2, _, _, _, hLngMn⟩ := c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨happ, hLn1⟩ := c2s_append M n hR hmono hj1 hcond hn2
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hlenP : (oper M (n - 1)).length = c2sIdx M n := hLn1
  -- 末尾までの切片は `drop`
  have hseg : seg (oper M n) (c2sIdx M n) (Lng (oper M n) - 1)
      = (oper M n).drop (c2sIdx M n) := by
    rw [seg_eq_take_drop_adm (oper M n) (c2sIdx M n) (Lng (oper M n) - 1)
      (by show c2sIdx M n ≤ (oper M n).length - 1; omega)
      (by show (oper M n).length - 1 < (oper M n).length; omega)]
    have hlend : ((oper M n).drop (c2sIdx M n)).length
        = (oper M n).length - c2sIdx M n := by
      rw [List.length_drop]
    have : (oper M n).length - 1 + 1 - c2sIdx M n
        = ((oper M n).drop (c2sIdx M n)).length := by rw [hlend]; omega
    rw [this, List.take_length]
  rw [hseg, happ, List.drop_left' hlenP]
  have h1 : 1 ≤ Lng M - 1 := by omega
  have := map_block_seg_c2s M (parent M 0 (Lng M - 1)) (Lng M - 1) h1
  have hEq : Lng M - 1 - 1 = Lng M - 2 := by omega
  rw [this, hEq]

/-- `c2sx_N_facts` (1): `idx` は `M[n]` の基点。 -/
private theorem c2s_marked_idx (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    Marked (oper M n) (c2sIdx M n) := by
  obtain ⟨hp0, e1z, _, _, _, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  exact ((kind0_base_basepoint M n hR (by omega) hp0 e1z).1 (by omega)).1

/-- `c2sx_N_facts` (16)(10): `0 ≤₀ idx`（`M[n]` の中）と `monoT N`。

Isabelle は `oper_d0zero_le0_lift`（pss_mechanized.thy:52265, ~80 行）で
`le0 M 0 j₀` をタイル越しに持ち上げるが、ここでは**ビルド済みの
`kind0_branch_rule`**（最終ブロック開始の行 0 の親は `j₀-1`）と
`0 ≤₀ j₀-1`（`le0_from0_down_c2s`）を繋ぐだけでよい。 -/
private theorem c2s_le0_mono (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    leR (oper M n) 0 0 (c2sIdx M n) = true ∧ monoT (c2sN M n) = true := by
  obtain ⟨hp0, e1z, nadmj, hj0pos, _, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, _, hle0j0⟩ := condII_host_extra_c2s M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, hw2, _, hj0idx, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, hLngN, hNR⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have hMnT : TPS (oper M n) := RTPS_TPS _ hMnR
  have hNT : TPS (c2sN M n) := RTPS_TPS _ hNR
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hidxltA : c2sIdx M n < Lng (oper M n) := by
    show c2sIdx M n < (oper M n).length; omega
  -- `M` の中で `0 ≤₀ j₀-1`
  have hle0j0R : leR M 0 0 (parent M 0 (Lng M - 1)) = true := by
    simpa [leR] using hle0j0
  have hdown : leR M 0 0 (parent M 0 (Lng M - 1) - 1) = true :=
    le0_from0_down_c2s M (parent M 0 (Lng M - 1) - 1) (parent M 0 (Lng M - 1))
      hM hle0j0R (by omega) (by omega)
  -- `M[n]` は `[0, j₁)` 上で `M` と逐語一致
  have hagree : ∀ z, z ≤ parent M 0 (Lng M - 1) - 1 →
      entry M 0 z = entry (oper M n) 0 z := by
    intro z hz
    exact (entry_oper_lt_last_68 M n 0 z hL (by omega) (Or.inl rfl) (by omega)).symm
  -- branch rule: 最終ブロック開始の行 0 の親は `j₀-1`
  have hedge : nextR (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (c2sIdx M n) = true :=
    (kind0_branch_rule M n (n - 1) hR (by omega) hp0 e1z le_rfl nadmj).1
  have hedgeLe : leR (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (c2sIdx M n) = true :=
    le0_of_nextR0_c2s (oper M n) _ _ hMnT hedge
  -- `0 ≤₀ idx`（`j₀ = 1` なら `j₀-1 = 0` で辺そのもの）
  have hmain : leR (oper M n) 0 0 (c2sIdx M n) = true := by
    by_cases hj02 : 2 ≤ parent M 0 (Lng M - 1)
    · have hpre : leR (oper M n) 0 0 (parent M 0 (Lng M - 1) - 1) = true :=
        le0_transfer_c2s M (oper M n) 0 (parent M 0 (Lng M - 1) - 1)
          (parent M 0 (Lng M - 1) - 1) hM hMnT hagree (by omega) le_rfl
          (by show parent M 0 (Lng M - 1) - 1 < (oper M n).length; omega) hdown
      exact le0_trans_c2s (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (c2sIdx M n)
        hMnT hpre hedgeLe (by omega) (by omega) hidxltA
    · have hj01 : parent M 0 (Lng M - 1) - 1 = 0 := by omega
      rw [hj01] at hedgeLe
      exact hedgeLe
  refine ⟨hmain, ?_⟩
  -- `monoT N`
  have hagreeN : ∀ z, z ≤ c2sIdx M n → entry (oper M n) 0 z = entry (c2sN M n) 0 z := by
    intro z hz
    rw [htake, entry_take (oper M n) (c2sIdx M n + 1) 0 z (by omega)]
  have hleN : leR (c2sN M n) 0 0 (c2sIdx M n) = true :=
    le0_transfer_c2s (oper M n) (c2sN M n) 0 (c2sIdx M n) (c2sIdx M n)
      hMnT hNT hagreeN (by omega) le_rfl (by omega) hmain
  have hzN : zeroT (c2sN M n) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left
    omega
  simp only [monoT, hzN, Bool.not_false, Bool.true_and, hLngN]
  simpa using hleN

/-- `nextrel0` の接頭辞移送（`nextrel0` の極小性は `range j₁` 上なので、
`j₁ < k` なら関係する添字はすべて `take k` の中にあり、entry の一致だけで移る）。 -/
private theorem nextrel0_take_c2s (A : PS) (a b k : ℕ) (hbk : b < k) (hkA : k ≤ Lng A)
    (h : nextrel0 A a b = true) : nextrel0 (A.take k) a b = true := by
  have hkA' : k ≤ A.length := hkA
  have hlen : (A.take k).length = k := by rw [List.length_take]; omega
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨⟨haL, hbL⟩, hab⟩, he⟩, hmin⟩ := h
  refine ⟨⟨⟨⟨?_, ?_⟩, hab⟩, ?_⟩, ?_⟩
  · show a < (A.take k).length; omega
  · show b < (A.take k).length; omega
  · rw [entry_take A k 0 a (by omega), entry_take A k 0 b (by omega)]; exact he
  · intro j hjb
    have hj := hmin j hjb
    rw [entry_take A k 0 b (by omega), entry_take A k 0 j (by omega)]
    exact hj

/-- `c2sx_N_facts` (4): `N` の中でも最終ブロック開始の行 0 の親は `j₀-1`。 -/
private theorem c2s_parN (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    parent (c2sN M n) 0 (c2sIdx M n) = parent M 0 (Lng M - 1) - 1 := by
  obtain ⟨hp0, e1z, nadmj, _, _, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, _, hw2, _, _, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, hLngN, _⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hedge : nextR (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (c2sIdx M n) = true :=
    (kind0_branch_rule M n (n - 1) hR (by omega) hp0 e1z le_rfl nadmj).1
  have hedge0 : nextrel0 (oper M n) (parent M 0 (Lng M - 1) - 1) (c2sIdx M n) = true := by
    simpa [nextR] using hedge
  have hN : nextrel0 (c2sN M n) (parent M 0 (Lng M - 1) - 1) (c2sIdx M n) = true := by
    rw [htake]
    exact nextrel0_take_c2s (oper M n) _ _ (c2sIdx M n + 1) (by omega)
      (by show c2sIdx M n + 1 ≤ (oper M n).length; omega) hedge0
  exact parent_eq_of_nextR0 (c2sN M n) _ _ (by simpa [nextR] using hN)

/-- `Adm M (j₀-1) = Adm M j₀`（`j₀` が非許容なら許容化は `j₀-1` を経由しない）。
Isabelle は `Adm_def` の `Max` を直接いじるが、Lean は `Adm_max` の両向きで済む。 -/
private theorem Adm_pred_eq_c2s (M : PS) (j0 : ℕ) (hna : adm M j0 = false)
    (hj0 : 0 < j0) : Adm M (j0 - 1) = Adm M j0 := by
  have hlt : Adm M j0 < j0 := by
    have hle := Adm_le M j0
    have hadm := Adm_adm M j0
    rcases Nat.lt_or_ge (Adm M j0) j0 with h | h
    · exact h
    · exfalso
      have heq : Adm M j0 = j0 := by omega
      rw [heq, hna] at hadm
      exact Bool.noConfusion hadm
  have hle1 : Adm M (j0 - 1) ≤ Adm M j0 :=
    Adm_max M (Adm M (j0 - 1)) j0 (Adm_adm M (j0 - 1))
      (le_trans (Adm_le M (j0 - 1)) (by omega))
  have hle2 : Adm M j0 ≤ Adm M (j0 - 1) :=
    Adm_max M (Adm M j0) (j0 - 1) (Adm_adm M j0) (by omega)
  omega

/-- `c2sx_N_facts` (5): `N` の中での `j₀-1` の許容化は `Adm M j₀` に潰れる。 -/
private theorem c2s_AdmN (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    Adm (c2sN M n) (parent M 0 (Lng M - 1) - 1) = Adm M (parent M 0 (Lng M - 1)) := by
  obtain ⟨hp0, e1z, nadmj, hj0pos, _, hw2', _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, hw2, _, hj0idx, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have hMnT : TPS (oper M n) := RTPS_TPS _ hMnR
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  -- (a) `N` から `M[n]` へ（`admof_slice`, `s = 0`）
  have hA : Adm (c2sN M n) (parent M 0 (Lng M - 1) - 1)
      = Adm (oper M n) (parent M 0 (Lng M - 1) - 1) := by
    have := admof_slice (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (c2sIdx M n)
      hMnT (by omega) (by omega)
      (by show c2sIdx M n ≤ (oper M n).length - 1; omega)
    simpa [c2sN] using this
  -- (b) `M[n]` と `M` は `[0, j₁)` 上で逐語一致 ⟹ 切片が等しい
  have hsegEq : seg (oper M n) 0 (Lng M - 2) = seg M 0 (Lng M - 2) := by
    simp only [seg]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range'] at hj
    have hjlt : j < Lng M - 1 := by omega
    rw [entry_oper_lt_last_68 M n 0 j hL (by omega) (Or.inl rfl) hjlt,
        entry_oper_lt_last_68 M n 1 j hL (by omega) (Or.inr rfl) hjlt]
  have hB : Adm (oper M n) (parent M 0 (Lng M - 1) - 1)
      = Adm (seg (oper M n) 0 (Lng M - 2)) (parent M 0 (Lng M - 1) - 1) := by
    have := admof_slice (oper M n) 0 (parent M 0 (Lng M - 1) - 1) (Lng M - 2)
      hMnT (by omega) (by omega)
      (by show Lng M - 2 ≤ (oper M n).length - 1; omega)
    simpa using this.symm
  have hC : Adm (seg M 0 (Lng M - 2)) (parent M 0 (Lng M - 1) - 1)
      = Adm M (parent M 0 (Lng M - 1) - 1) := by
    have := admof_slice M 0 (parent M 0 (Lng M - 1) - 1) (Lng M - 2)
      hM (by omega) (by omega) (by omega)
    simpa using this
  rw [hA, hB, hsegEq, hC]
  exact Adm_pred_eq_c2s M (parent M 0 (Lng M - 1)) nadmj hj0pos

/-- `c2sx_N_facts` (6): `Trans (Pred N) ≠ 0_B`（`Pred N = M[n-1]` は長さ `idx > 1`）。 -/
private theorem c2s_T1N (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    Trans (Pred (c2sN M n)) ≠ BZero := by
  obtain ⟨_, _, _, _, _, hidxpos, _⟩ := c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨_, hLn1⟩ := c2s_append M n hR hmono hj1 hcond hn2
  have hpredN : Pred (c2sN M n) = oper M (n - 1) :=
    c2s_predN M n hR hmono hj1 hcond hn2
  have hn1R : RTPS (oper M (n - 1)) := RTPS_oper M (n - 1) hR (by omega)
  have hn1T : TPS (oper M (n - 1)) := RTPS_TPS _ hn1R
  have hnz : zeroT (oper M (n - 1)) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left
    omega
  rw [hpredN]
  intro hzero
  have := (Trans_preserves_zeroT (oper M (n - 1)) hn1T).mpr hzero
  rw [hnz] at this
  exact Bool.noConfusion this

/-- `c2sx_N_facts` (7): `N` は条件(V) を満たす（追加ブロックの葉 `D_{M₁,ⱼ₀} 0`）。 -/
private theorem c2s_condVN (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    transCondV (c2sN M n) = true := by
  obtain ⟨hp0, e1z, _, hj0pos, _, hw2', _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨hrun1, hv0pos, _⟩ := condII_host_extra_c2s M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, hw2, _, hj0idx, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, hLngN, _⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  obtain ⟨heN, _⟩ := c2s_eNidx M n hR hmono hj1 hcond hn2
  have hL : 1 < Lng M := by omega
  have hparN : parent (c2sN M n) 0 (c2sIdx M n) = parent M 0 (Lng M - 1) - 1 :=
    c2s_parN M n hR hmono hj1 hcond hn2
  -- `lastIdx N = idx`、`lastParent N = j₀-1`
  have hlastIdx : lastIdx (c2sN M n) = c2sIdx M n := by
    simp only [lastIdx, hLngN]
    omega
  have hlastPar : lastParent (c2sN M n) = parent M 0 (Lng M - 1) - 1 := by
    simp only [lastParent, hlastIdx, hparN]
  -- `entry N 1 (j₀-1) = entry M 1 (j₀-1)`
  have heNm1 : entry (c2sN M n) 1 (parent M 0 (Lng M - 1) - 1)
      = entry M 1 (parent M 0 (Lng M - 1) - 1) := by
    rw [htake, entry_take (oper M n) (c2sIdx M n + 1) 1
      (parent M 0 (Lng M - 1) - 1) (by omega)]
    exact entry_oper_lt_last_68 M n 1 (parent M 0 (Lng M - 1) - 1) hL
      (by omega) (Or.inr rfl) (by omega)
  simp only [transCondV, hlastIdx, hlastPar, heN, heNm1, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨hv0pos, hrun1.symm⟩, by omega⟩

/-! ## §5 `c2sx_mark_idx` (86987) / `c2sx_marked_jm1` (87021) -/

/-- Isabelle `c2sx_mark_idx` (pss_wip.thy:86987)。最終ブロック開始の基点値は
終切片の `Trans` 値 `W` に等しい。 -/
private theorem c2s_mark_idx (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn2 : 2 ≤ n) :
    Mark (oper M n) (c2sIdx M n)
      = Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2)) := by
  obtain ⟨_, _, hw2, _, _, _, hLngMn⟩ := c2s_nums M n hR hmono hj1 hcond hn2
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have hmk : Marked (oper M n) (c2sIdx M n) :=
    c2s_marked_idx M n hR hmono hj1 hcond hn2
  have hidxlt : c2sIdx M n < Lng (oper M n) - 1 := by
    show c2sIdx M n < (oper M n).length - 1; omega
  rw [Mark_Trans_repr (oper M n) (c2sIdx M n) hmk hMnR hidxlt]
  rw [c2s_segtail M n hR hmono hj1 hcond hn2]

/-- Isabelle `c2sx_marked_jm1` (pss_wip.thy:87021)。`j₋₁ = Adm_M(j₀)` は
すべての反復 `M[n]`（`n > 0`）の基点。 -/
private theorem c2s_marked_jm1 (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondII M = true) (hn : 0 < n) :
    Marked (oper M n) (Adm M (parent M 0 (Lng M - 1))) := by
  obtain ⟨hp0, e1z, nadmj, _, _, _, _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  exact ((kind0_base_basepoint M n hR hn hp0 e1z).2 nadmj).1

/-! ## §6 `c2sx_mark_pin` (pss_wip.thy:87033) — OW 文脈安定性による `Mark` の固定

Isabelle は `scb_context_eq_of_prefix` (39775) を経由する。同補題は Isabelle で
**証明済み**（仮定なしの定理）で、その入力 `m_7_4_Trans_Mark_seg` は Lean にも
ビルド済みで存在するので、そのまま移植できる。
⚠️ Lean の `scb_unique_decomp_unconditional` は Isabelle の `m_7_2_scb_unique_sb`
より**強い**（`t ≠ 0_B` 不要）ので、Isabelle 側の `segnz` 仮定は落とせる。 -/

/-- Isabelle `scb_context_eq_of_prefix` (pss_wip.thy:39775)。同じ基点 `m` で
接頭辞の `Trans` 値と行 1 の係数が一致する 2 本は、**同じ OW 文脈** `(s,b)` を持つ。
（Isabelle の `segnz` 仮定は Lean の無条件一意性により不要。） -/
private theorem scb_context_eq_of_prefix_c2s (Q1 Q2 : PS) (m : ℕ)
    (mk1 : Marked Q1 m) (R1 : RTPS Q1) (mk2 : Marked Q2 m) (R2 : RTPS Q2)
    (mpos : 0 < m) (mlt1 : m < Lng Q1 - 1) (mlt2 : m < Lng Q2 - 1)
    (segeq : Trans (seg Q1 0 m) = Trans (seg Q2 0 m))
    (entryeq : entry Q1 1 m = entry Q2 1 m) :
    ∃ s b, scb_decomp (Trans Q1) s (flatBT (Mark Q1 m)) b
         ∧ scb_decomp (Trans Q2) s (flatBT (Mark Q2 m)) b := by
  obtain ⟨sb1, C1, _⟩ := m_7_4_Trans_Mark_seg Q1 m mk1 R1 mpos mlt1
  obtain ⟨sb2, C2, _⟩ := m_7_4_Trans_Mark_seg Q2 m mk2 R2 mpos mlt2
  -- 両者は同じ接頭辞 `Trans` を同じ中心で分解する
  have A1 : scb_decomp (Trans (seg Q2 0 m)) sb1.1
      (flatBT (Dprin ((entry Q2 1 m : ℕ∞)) BZero)) sb1.2 := by
    rw [← segeq, ← entryeq]; exact C1.1
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (seg Q2 0 m))
    sb1.1 sb2.1 (flatBT (Dprin ((entry Q2 1 m : ℕ∞)) BZero)) sb1.2 sb2.2 A1 C2.1
  refine ⟨sb1.1, sb1.2, C1.2, ?_⟩
  rw [hs, hb]
  exact C2.2

/-- Isabelle `c2sx_mark_pin` (pss_wip.thy:87033)。`Pred M` 側で `(s',b')` に
固定された OW 文脈は `M[n]` 側でも同じ基点 `j₋₁` を切り出す。 -/
private theorem c2s_mark_pin (M : PS) (n : ℕ) (X : BT) (s' b' : List Sym)
    (hR : RTPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondII M = true) (hn2 : 2 ≤ n)
    (dInit : scb_decomp (Trans (Pred M)) s'
      (flatBT (Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))))) b')
    (dTn : scb_decomp (Trans (oper M n)) s' (flatBT X) b') :
    Mark (oper M n) (Adm M (parent M 0 (Lng M - 1))) = X := by
  obtain ⟨hp0, e1z, nadmj, hj0pos, hjm1lt, hw2', _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, hw2, _, hj0idx, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have hMnT : TPS (oper M n) := RTPS_TPS _ hMnR
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredT : TPS (Pred M) := RTPS_TPS _ hpredR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hL
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  -- `Trans (Pred M) ≠ 0_B`
  have hnzP : zeroT (Pred M) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; omega
  have hT1ne : Trans (Pred M) ≠ BZero := by
    intro hz
    have := (Trans_preserves_zeroT (Pred M) hpredT).mpr hz
    rw [hnzP] at this; exact Bool.noConfusion this
  -- 両側の基点性
  have mkn : Marked (oper M n) (Adm M (parent M 0 (Lng M - 1))) :=
    c2s_marked_jm1 M n hR hmono hj1 hcond (by omega)
  have mkP : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hL hp0
  have flatTn : flatBT (Trans (oper M n)) = s' ++ flatBT X ++ b' := dTn.1
  -- `M[n]` と `Pred M` は `[0, j₋₁]` 上で逐語一致
  have hagr : ∀ i z, (i = 0 ∨ i = 1) → z ≤ Adm M (parent M 0 (Lng M - 1)) →
      entry (oper M n) i z = entry (Pred M) i z := by
    intro i z hi hz
    have hzlt : z < Lng M - 1 := by omega
    rcases hi with rfl | rfl
    · rw [entry_oper_lt_last_68 M n 0 z hL (by omega) (Or.inl rfl) hzlt,
        Pred_eq_take M hL, entry_take M (Lng M - 1) 0 z hzlt]
    · rw [entry_oper_lt_last_68 M n 1 z hL (by omega) (Or.inr rfl) hzlt,
        Pred_eq_take M hL, entry_take M (Lng M - 1) 1 z hzlt]
  -- 接頭辞切片の一致
  have hsegEq : seg (oper M n) 0 (Adm M (parent M 0 (Lng M - 1)))
      = seg (Pred M) 0 (Adm M (parent M 0 (Lng M - 1))) := by
    simp only [seg]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range'] at hj
    rw [hagr 0 j (Or.inl rfl) (by omega), hagr 1 j (Or.inr rfl) (by omega)]
  have hentryEq : entry (oper M n) 1 (Adm M (parent M 0 (Lng M - 1)))
      = entry (Pred M) 1 (Adm M (parent M 0 (Lng M - 1))) :=
    hagr 1 _ (Or.inr rfl) le_rfl
  by_cases hjm0 : Adm M (parent M 0 (Lng M - 1)) = 0
  · -- `j₋₁ = 0`: 両者とも `Mark _ 0 = Trans _` で、文脈は空
    rw [hjm0] at dInit mkn mkP ⊢
    have hsegP : seg (Pred M) 0 (Lng (Pred M) - 1) = Pred M := by
      rw [seg0_eq_take_c2s (Pred M) (Lng (Pred M) - 1) (by omega)]
      have : Lng (Pred M) - 1 + 1 = Lng (Pred M) := by omega
      rw [this]; exact List.take_length
    have hm0P : Mark (Pred M) 0 = Trans (Pred M) := by
      rw [Mark_Trans_repr_zero (Pred M) hpredR mkP (by omega), hsegP]
    have hsegN : seg (oper M n) 0 (Lng (oper M n) - 1) = oper M n := by
      rw [seg0_eq_take_c2s (oper M n) (Lng (oper M n) - 1)
        (by show Lng (oper M n) - 1 < (oper M n).length; omega)]
      have : Lng (oper M n) - 1 + 1 = Lng (oper M n) := by
        show (oper M n).length - 1 + 1 = (oper M n).length; omega
      rw [this]; exact List.take_length
    have hm0n : Mark (oper M n) 0 = Trans (oper M n) := by
      rw [Mark_Trans_repr_zero (oper M n) hMnR mkn
        (by show 0 < (oper M n).length - 1; omega), hsegN]
    -- `s' = [] ∧ b' = []`（長さ勘定）
    have he : flatBT (Trans (Pred M))
        = s' ++ flatBT (Trans (Pred M)) ++ b' := by
      have := dInit.1; rwa [hm0P] at this
    have hlens := congrArg List.length he
    simp only [List.length_append] at hlens
    have hs'0 : s' = [] := by
      rcases s' with _ | ⟨x, xs⟩
      · rfl
      · simp at hlens; omega
    have hb'0 : b' = [] := by
      rcases b' with _ | ⟨x, xs⟩
      · rfl
      · simp at hlens; omega
    rw [hm0n]
    rw [hs'0, hb'0] at flatTn
    simp only [List.nil_append, List.append_nil] at flatTn
    calc Trans (oper M n) = unflatBT (flatBT (Trans (oper M n))) :=
          (unflatBT_flat _).symm
      _ = unflatBT (flatBT X) := by rw [flatTn]
      _ = X := unflatBT_flat _
  · -- `j₋₁ > 0`: OW 文脈安定性
    have hjmpos : 0 < Adm M (parent M 0 (Lng M - 1)) := by omega
    have mlt1 : Adm M (parent M 0 (Lng M - 1)) < Lng (oper M n) - 1 := by
      show Adm M (parent M 0 (Lng M - 1)) < (oper M n).length - 1; omega
    have mlt2 : Adm M (parent M 0 (Lng M - 1)) < Lng (Pred M) - 1 := by
      omega
    obtain ⟨s, b, cs1, cs2⟩ := scb_context_eq_of_prefix_c2s (oper M n) (Pred M)
      (Adm M (parent M 0 (Lng M - 1))) mkn hMnR mkP hpredR hjmpos mlt1 mlt2
      (congrArg Trans hsegEq) hentryEq
    obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (Pred M))
      s s' (flatBT (Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))))) b b' cs2 dInit
    have flatMk : flatBT (Trans (oper M n))
        = s' ++ flatBT (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1)))) ++ b' := by
      have := cs1.1; rwa [hs, hb] at this
    have hcomb : s' ++ flatBT X ++ b'
        = s' ++ flatBT (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1)))) ++ b' :=
      flatTn.symm.trans flatMk
    have feq : flatBT (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1))))
        = flatBT X := by
      have h1 : s' ++ (flatBT X ++ b')
          = s' ++ (flatBT (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1)))) ++ b') := by
        simpa [List.append_assoc] using hcomb
      exact (List.append_cancel_right (List.append_cancel_left h1)).symm
    calc Mark (oper M n) (Adm M (parent M 0 (Lng M - 1)))
        = unflatBT (flatBT (Mark (oper M n) (Adm M (parent M 0 (Lng M - 1))))) :=
          (unflatBT_flat _).symm
      _ = unflatBT (flatBT X) := by rw [feq]
      _ = X := unflatBT_flat _

/-! ## §7 `BT` / scb の基盤（Isabelle `scx_addBT_assoc` / `scx_TB_*` /
`scb_Dpt_lift` 1663） -/

private theorem addBT_zero_right_c2s (t : BT) : addBT t BZero = t := by
  cases t with | trm ps => simp [addBT, BZero]

private theorem addBT_assoc_c2s (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  cases a; cases b; cases c; simp [addBT]

private theorem BZero_mem_T_B_c2s : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

/-- Isabelle `scx_TB_Dpt`。`v : ℕ` の像は `⊤` でないので本体の `T_B` 所属だけでよい。 -/
private theorem Dprin_mem_T_B_c2s {t : BT} (v : ℕ) (ht : t ∈ T_B) :
    Dprin (v : ℕ∞) t ∈ T_B := by
  have ht' : dfree_BT t = true := by simpa [T_B] using ht
  simp [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList, ht']

/-- Isabelle `scx_TB_multBT`。 -/
private theorem multBT_mem_T_B_c2s {a : BT} (ha : a ∈ T_B) : ∀ n, multBT a n ∈ T_B
  | 0 => BZero_mem_T_B_c2s
  | n + 1 => addBT_mem_T_B (multBT_mem_T_B_c2s ha n) ha

/-- Isabelle `addscb_princ_isPTB` / `isPTB_str_Dpt`。単項 principal の平坦化は
`isPTB_str`。 -/
private theorem principal_isPTB_c2s {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = BT.trm [p]) : isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `scb_Dpt_lift` (pss_wip.thy:1663)。 -/
private theorem scb_Dprin_lift_c2s {X : BT} {s c b : List Sym} (v : ℕ∞)
    (d : scb_decomp X s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v X) ((.dsym v) :: s) c b := by
  obtain ⟨he, _, hrp⟩ := d
  refine ⟨?_, fun _ => ipt, hrp⟩
  have hflat : flatBT (Dprin v X) = (.dsym v) :: flatBT X := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, he]
  simp

/-! ## §8 `c2sx_step` (pss_wip.thy:87202) — 一歩あたりの surgery

Isabelle の per-step surgery は**一様**（場合分けなし）: `N = seg (M[n]) 0 idx`
（`Pred N = M[n-1]`）が常に条件(V) を満たし、その `c₂^N` は葉 `D_{M₁,ⱼ₀} 0` を
追加し、その葉が `Mark (M[n]) idx = W` に置換される。

⚠️ **Isabelle からの短縮**: Isabelle は `W` が単項 principal（頭 `v₀`）である
ことを `dkax_slice_principal_gen` (71793) で出すが、Lean では
`Mark_leftend_form_proper`（ビルド済み §7.4）＋ `c2s_mark_idx`（`W = Mark (M[n]) idx`）
で直接得られるので、同補題の移植は不要。 -/

/-- Isabelle `c2sx_step` (pss_wip.thy:87202)。**本ファイルの成果物**: ビルド済み
«8».«8.3-condII-masterCF» の名前付き `Prop` `CondII_step` を drop-in で充足する
（house pattern: `Prop` をそのまま型にしているので elaborator が一致を機械確認）。 -/
theorem condII_step_holds : CondII_step := by
  intro M n va t₂ s' b' hR hmono hj1 hcond hn2 hvaE ht2TB dInit mkIH dIH
  obtain ⟨hp0, e1z, nadmj, hj0pos, hjm1lt, hw2', _, _, _⟩ :=
    condII_host_basic_holds M hR hmono hj1 hcond
  obtain ⟨_, hj0lt, hw2, _, hj0idx, hidxpos, hLngMn⟩ :=
    c2s_nums M n hR hmono hj1 hcond hn2
  obtain ⟨htake, hLngN, hNR⟩ := c2s_struct M n hR hmono hj1 hcond hn2
  obtain ⟨heNidx, heMnidx⟩ := c2s_eNidx M n hR hmono hj1 hcond hn2
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR (by omega)
  have hlen : (oper M n).length
      = c2sIdx M n + ((Lng M - 1) - parent M 0 (Lng M - 1)) := hLngMn
  have hidxlt1 : c2sIdx M n < Lng (oper M n) - 1 := by
    show c2sIdx M n < (oper M n).length - 1; omega
  -- 記号
  set W := Trans (seg M (parent M 0 (Lng M - 1)) (Lng M - 2)) with hWdef
  set body := addBT t₂ (multBT W (n - 2)) with hbodydef
  set leaf := Dprin ((entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)) BZero with hleafdef
  -- `N` の Trans-記号
  have hparN : parent (c2sN M n) 0 (c2sIdx M n) = parent M 0 (Lng M - 1) - 1 :=
    c2s_parN M n hR hmono hj1 hcond hn2
  have hAdmN : Adm (c2sN M n) (parent M 0 (Lng M - 1) - 1)
      = Adm M (parent M 0 (Lng M - 1)) := c2s_AdmN M n hR hmono hj1 hcond hn2
  have hpredN : Pred (c2sN M n) = oper M (n - 1) :=
    c2s_predN M n hR hmono hj1 hcond hn2
  have hlastIdxN : lastIdx (c2sN M n) = c2sIdx M n := by
    simp only [lastIdx, hLngN]; omega
  have hlastParN : lastParent (c2sN M n) = parent M 0 (Lng M - 1) - 1 := by
    simp only [lastParent, hlastIdxN, hparN]
  have hC1N : transC1 (c2sN M n) = Dprin (va : ℕ∞) body := by
    simp only [transC1, transJm1, transJ0, hlastParN, hAdmN, hpredN]
    exact mkIH
  have hVN : transV (c2sN M n) = (va : ℕ∞) := by
    simp only [transV, hC1N]; simp [bpHeadV, Dprin]
  have hT2N : transT2 (c2sN M n) = body := by
    simp only [transT2, hC1N]; simp [bpHeadT, Dprin]
  -- `N` は条件(V): `c₂^N` は葉 `D_{v₀} 0` を追加する
  have hcondVN : transCondV (c2sN M n) = true :=
    c2s_condVN M n hR hmono hj1 hcond hn2
  have hC2N : transC2 (c2sN M n) = Dprin (va : ℕ∞) (addBT body leaf) := by
    simp only [transC2, transC2Core, hcondVN, Bool.or_true, if_true, hVN, hT2N,
      hlastIdxN, heNidx, hleafdef]
  -- mono 枝の scb 対を `(s',b')` に固定
  have hmonoN : monoT (c2sN M n) = true :=
    (c2s_le0_mono M n hR hmono hj1 hcond hn2).2
  have hT1Nne : Trans (Pred (c2sN M n)) ≠ BZero :=
    c2s_T1N M n hR hmono hj1 hcond hn2
  obtain ⟨sN, bN, dPn, dWn⟩ :=
    Trans_c1_c2_decomp (c2sN M n) hNR hmonoN (by omega) hT1Nne
  have dPn' : scb_decomp (Trans (oper M (n - 1))) sN
      (flatBT (Dprin (va : ℕ∞) body)) bN := by
    rw [← hpredN, ← hC1N]; exact dPn
  obtain ⟨hsN, hbN⟩ := scb_unique_decomp_unconditional (Trans (oper M (n - 1)))
    sN s' (flatBT (Dprin (va : ℕ∞) body)) bN b' dPn' dIH
  have dWnE : scb_decomp (Trans (c2sN M n)) s'
      (flatBT (Dprin (va : ℕ∞) (addBT body leaf))) b' := by
    rw [← hC2N, ← hsN, ← hbN]; exact dWn
  -- 終切片の値 `W`: `idx` の基点値であり、単項 principal（頭 `v₀`）
  have mkIdx : Marked (oper M n) (c2sIdx M n) :=
    c2s_marked_idx M n hR hmono hj1 hcond hn2
  have markidx : Mark (oper M n) (c2sIdx M n) = W :=
    c2s_mark_idx M n hR hmono hj1 hcond hn2
  have WTB : W ∈ T_B := by
    rw [← markidx]; exact Mark_mem_T_B (oper M n) (c2sIdx M n) hMnR mkIdx
  have WE : ∃ t, W = Dprin ((entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞)) t := by
    obtain ⟨t, ht⟩ := Mark_leftend_form_proper (oper M n) (c2sIdx M n)
      mkIdx hMnR hidxlt1
    exact ⟨t, by rw [← markidx, ht, heMnidx]⟩
  have Wp : ∃ p, W = BT.trm [p] := by
    obtain ⟨t, ht⟩ := WE; exact ⟨_, by rw [ht, Dprin]⟩
  -- `T_B` と形の事実
  have leafTB : leaf ∈ T_B :=
    Dprin_mem_T_B_c2s _ BZero_mem_T_B_c2s
  have leafp : ∃ p, leaf = BT.trm [p] := ⟨_, by rw [hleafdef, Dprin]⟩
  have bodyTB : body ∈ T_B :=
    addBT_mem_T_B ht2TB (multBT_mem_T_B_c2s WTB (n - 2))
  have iptleaf : isPTB_str (flatBT leaf) := principal_isPTB_c2s leafTB leafp
  have iptW : isPTB_str (flatBT W) := principal_isPTB_c2s WTB Wp
  -- 追加された葉の標準的な内部位置
  obtain ⟨si, bi, iA0⟩ := add_scb_marked body leaf bodyTB leafTB leafp
  have iA : scb_decomp (Dprin (va : ℕ∞) (addBT body leaf))
      ((.dsym (va : ℕ∞)) :: si) (flatBT leaf) bi :=
    scb_Dprin_lift_c2s _ iA0 iptleaf
  -- 最終ブロック開始の Mark/Trans-seg 対
  obtain ⟨sb0, TMS, _⟩ := m_7_4_Trans_Mark_seg (oper M n) (c2sIdx M n)
    mkIdx hMnR (by omega) hidxlt1
  have dseg : scb_decomp (Trans (c2sN M n)) sb0.1 (flatBT leaf) sb0.2 := by
    have h := TMS.1
    rw [heMnidx] at h
    exact h
  have dmark : scb_decomp (Trans (oper M n)) sb0.1 (flatBT W) sb0.2 := by
    have h := TMS.2
    rw [markidx] at h
    exact h
  -- 葉を `W` に置換（同じ内部位置）
  have dCI : scb_decomp (Trans (c2sN M n)) (s' ++ ((.dsym (va : ℕ∞)) :: si))
      (flatBT leaf) (bi ++ b') :=
    scb_compose (Trans (c2sN M n)) (Dprin (va : ℕ∞) (addBT body leaf)) s'
      ((.dsym (va : ℕ∞)) :: si) (flatBT leaf) bi b' ⟨_, rfl⟩ dWnE iA
  obtain ⟨hp1, hp2⟩ := scb_unique_decomp_unconditional (Trans (c2sN M n))
    sb0.1 (s' ++ ((.dsym (va : ℕ∞)) :: si)) (flatBT leaf) sb0.2 (bi ++ b')
    dseg dCI
  have dmark' : scb_decomp (Trans (oper M n)) (s' ++ ((.dsym (va : ℕ∞)) :: si))
      (flatBT W) (bi ++ b') := by rw [← hp1, ← hp2]; exact dmark
  have iA2_0 : scb_decomp (addBT body W) si (flatBT W) bi :=
    add_scb_replace_last body leaf W si bi bodyTB leafTB leafp WTB Wp iA0
  -- 閉形式の再結合 `t₂ +_B W^(n-2) +_B W = t₂ +_B W^(n-1)`
  have snoc : multBT W (n - 1) = addBT (multBT W (n - 2)) W := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rfl
  have assocX : addBT body W = addBT t₂ (multBT W (n - 1)) := by
    rw [hbodydef, addBT_assoc_c2s, ← snoc]
  have iA2 : scb_decomp (Dprin (va : ℕ∞) (addBT t₂ (multBT W (n - 1))))
      ((.dsym (va : ℕ∞)) :: si) (flatBT W) bi := by
    rw [← assocX]
    exact scb_Dprin_lift_c2s _ iA2_0 iptW
  -- 外側の分解を組み直す
  have XnTB : Dprin (va : ℕ∞) (addBT t₂ (multBT W (n - 1))) ∈ T_B :=
    Dprin_mem_T_B_c2s _ (addBT_mem_T_B ht2TB (multBT_mem_T_B_c2s WTB (n - 1)))
  have iptXn : isPTB_str (flatBT (Dprin (va : ℕ∞) (addBT t₂ (multBT W (n - 1))))) :=
    principal_isPTB_c2s XnTB ⟨_, by rw [Dprin]⟩
  have dTn : scb_decomp (Trans (oper M n)) s'
      (flatBT (Dprin (va : ℕ∞) (addBT t₂ (multBT W (n - 1))))) b' := by
    refine ⟨?_, fun _ => iptXn, dIH.2.2⟩
    have fMn := dmark'.1
    have fX2 := iA2.1
    rw [fMn, fX2]
    simp [List.append_assoc]
  exact ⟨c2s_mark_pin M n _ s' b' hR hmono hj1 hcond hn2 dInit dTn, dTn⟩

/-! ## §9 下流への配線について — **意図的に何も供給しない**

`CondII_step` は落ちたが、**RT_PS 水準の消費者は偽なので、そこへ繋ぐと空虚になる**。
以下は本ファイルが `condII_masterCF_holds` / `condII_exchII_of_residuals` への
1 行配線（`condII_masterCF_of_tailvalAll` 等）を**あえて置かない**理由。

🚨🚨 **`CondII_TailvalAll` と `CondII_masterCF` は偽**（同ラウンドの姉妹ファイル
`«8».«8.3-condII-tailval»` が**緑・sorry 0・axioms clean** で
`not_CondII_TailvalAll` / `not_CondII_masterCF` を証明済み。反例
`M = (0,0)(1,1)(2,2)(2,0)(2,2)(2,0)` は `RTPS ∧ monoT ∧ 1 < Lng-1 ∧ transCondII`
を**すべて**満たす＝空虚な反例ではない。本ファイルの担当者も checker で独立に
再確認した）。したがって:
  * `condII_masterCF_holds condII_step_holds hTV` は仮定 `hTV : CondII_TailvalAll`
    が反証可能なので**空虚**。
  * `condII_exchII_of_residuals condII_step_holds hTV` も同様に**空虚**。
  * ビルド済み engine «8».«8.3-TransCondII-engine» の名前付き `Prop`
    `CondII_masterCF`（RT_PS 版）は **充足不能**＝これを field に持つ束は
    そこで詰んでいる。masterCF ヘッダの「数値監査 144/144 ⟹ 真らしい」は
    **誤り**（有界監査の偽陰性。`memo.md` par.3 の警告どおり）。

  ⟹ **`CondII_step` が使われるべき唯一の健全な経路は ST_PS 版**:
     `condII_exchII_of_ST_residuals condII_step_holds hTV_ST`
     （`CondII_TailvalAll_ST` ＝ Isabelle `y3j_condII_tailval`,
     layerC/pss_scratch.thy:17079 ＝**本物の定理**）。これは engine の
     `CondII_masterCF` を経由しない。masterCF ソース版の 📌 推奨（engine :212 の
     `RTPS M` を `STPS M` に変える）は、単なる最適化ではなく**必須の修正**である。

🚨 **ビルド済み «8».«8.3-condII-masterCF» は作業ディレクトリの同名ファイルより
古い版**（`#check` で確認）。ビルド版にあるのは `CondII_step` /
`CondII_TailvalAll` / `CondII_masterCF` / `condII_masterCF_holds` /
`condII_masterCF_of_tailval` / `condII_exchII_of_residuals` / `FseqDesc_exchII` /
`exchII_of_masterCF` まで。ソース版の `CondII_TailvalAll_ST` /
`condII_exchII_of_ST_residuals` / `OTdisp_exchII` は**ビルド版に無い**ので、
ST 経路の 1 行配線は masterCF 再ビルド後に初めて書ける。
**本ファイルの `condII_step_holds` はビルド版の `CondII_step` に対して型検査
されており、その文はソース版・Isabelle `c2sx_step` と 1:1 で一致する**
（`#print CondII_step` で照合済）ので、再ビルドしても壊れない。 -/

#print axioms condII_step_holds

end PSS
