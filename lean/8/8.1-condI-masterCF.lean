import «8».«8.1-Trans-fseq-condI»
import «8».«8.1-condI-III-c1-around»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Mark-rightmost1»
import «7».«7.2-scb-unique»
import «7».«7.2-scb-compose»
import «7».«7.4-Adm-nextAdm»
import «7».«7.4-Trans-Mark-seg»
import «6».«6.3-admof-slice»
import «6».«6.2-P-fseq»
import «5».«5.1-parent-exists»

/-!
# §8.1 条件(I)・`j₀ > 0` の marking-nesting 閉形式（`CondI_masterCF` の討伐）

- 原文: `tmp/content.md` 3160–3260（§8.1 の条件(I) 交換関係の証明本体）。
  本ファイルは**新しい記事命題を主張しない**。ビルド済み
  `«8».«8.1-Trans-fseq-condI»` が露出した唯一の `Prop` `CondI_masterCF`
  （同 :417）を討伐するための移植ファイル。
- Isabelle: r28-STEPCORE ブロック（`isabelle/layerB/pss_wip.thy` :82085–83900）
  * `scx_addBT_assoc` / `scx_TB_*` / `scx_scb_compose` (:82123–82170) — 基盤
  * `scx_take_RT_PS` (:82171) / `scx_seg0_RT_PS` (:82199) / `scx_map_block_seg` (:82210)
  * `scx_row1_bound` (:82228) — 簡約性と係数の関係（場合分けの網羅性境界）
  * `scx_le0_to_parent` (:82278) / `scx_hasParent_of_le0` (:82297)
  * `scx_host_basic` (:82322) — 条件(I)・`j₀>0` の host 基本事実
  * `scx_operI_nth_le_j0` (:82361) — 反復の逐語接頭辞
  * `scx_N_facts` (:82405) — 最終ブロック開始点の接頭辞 `N` の構造束
  * `scx_mark_idx` (:82604) / `scx_c1_w1` (:82645) — `Mark (M[n]) idx = c₁`
  * `scx_marked_jm1p` (:82685) — `j₋₁'` が反復の基点であること
  * `scx_mark_pin` (:82771) — OW 文脈安定性による `Mark` の固定
  * `scx_stepA` (:82938) / `scx_stepB` (:83254) — 一歩の surgery（case A / case B）
  * `scx_condI_j0pos_masterCF` (:83639) — 組み立て
- 訂正: 本ブロックに掛かる訂正は無い。**A20 は使う**（`c1_around_1` の切片等式は
  `j₀ < j₁ - 1`（＝`w ≥ 2`）でガードされる。`w = 1` は `scx_c1_w1` で別処理）。
  `corrections-old.md` の取り下げ訂正（A24–A28/A35 等 operB 誤読由来）には依存しない。
- 依存（ビルド済みのみ import）: `8.1-Trans-fseq-condI`（`CondI_masterCF` の定義）、
  `8.1-condI-III-c1-around`（`c1_around_1` / `c1_around_2` / `c1_around_5` —
  いずれも sorry 0・axioms は propext/Classical.choice/Quot.sound。同ファイルに残る
  part(4) の sorry には**触れない**）、`7.4-Mark-Trans-repr`（`Mark_Trans_repr`,
  `Mark_Trans_repr_zero`）、`7.3-Mark-rightmost1`（`m_7_3_Mark_rightmost1`）、
  `7.2-scb-unique`（`scb_unique_decomp_unconditional`）、`7.2-scb-compose`
  （`scb_compose`）、`7.4-Adm-nextAdm`（`adm_row1_ancestry`）、`6.3-admof-slice`
  （`Adm_adm` / `Adm_le`）、`6.2-P-fseq`（`le0Aux_*`）、`5.1-parent-exists`
  （`parent_exists_1/2/3`）。推移的に `6.8-standard-slice-Br-descending`
  （`oper_d0zero_expand_68` / `entry_oper_lt_last_68` / `seg_oper_eq_68`）、
  `6.6-reduced-fseq`（`RTPS_oper`）、`6.5-Red-Pred-commute`（`RTPS_Pred` /
  `Pred_eq_take`）、`6.4-P-IdxSum-characterization`（`row0_parent_unique`）。
- 状態: 🤖 **GREEN・部分スコープ**（sorry 0、公開 23 定理の axioms はすべて
  propext/Classical.choice/Quot.sound）。**`CondI_masterCF` は未討伐**。

  **落ちた範囲 = r28-STEPCORE の chunk 1/2/3（pss_wip.thy 82085–82934）を無仮定で全部**:
  `scx_addBT_*`/`scx_TB_*`/`scx_scb_compose`（private）、`scx_take_RTPS`、
  `scx_seg0_RTPS`、`scx_map_block_seg`、`scx_le0_to_parent`、`scx_row1_bound`、
  `scx_host_basic`、`Lng_operI` 相当（`scx_Lng_oper`/`scx_Lng_oper_idx`）、
  `scx_N_facts`（18 結論を個別定理に分解＝`scx_N_take`/`scx_N_Pred`/
  `scx_N_marked_edge`/`scx_le0_oper_idx`/`scx_N_RTPS_monoT`/`scx_N_entry_le_j0`/
  `scx_N_entry1_idx`/`scx_N_tail_seg`/`scx_N_nextR`）、`scx_mark_idx`、`scx_c1_w1`、
  `scx_marked_jm1p`、`scb_context_eq_of_prefix`、`scx_mark_pin`。

  **残り = chunk 4a/4b/5**: `scx_stepA` (82938–83249)・`scx_stepB` (83254–83629)・
  `scx_condI_j0pos_masterCF` の組み立て (83639–84103)。**この 3 つは本ファイルに
  一切現れない**（dead な `Prop` 宣言を置かない方針）。上の 23 本はすべてその
  入力なので、続きは本ファイルを import して chunk 4a→4b→5 の順に足せばよい。

  **Isabelle からの短縮**: `scx_operI_nth_le_j0`（反復の逐語接頭辞）は Lean では
  既存の `entry_oper_lt_last_68`（§6.8）が `x < Lng M - 1` の全域で与えるので不要。
  同様に `scx_hasParent_of_le0` は `mono_hasParent_row0`（§6.6）で直接賄えるため
  `le0 M 0 j₀` 経由の迂回が要らない。`scx_le0_to_parent` は行 0 の値特徴付け
  （`ancestor_basic_1` ＋ `parent_exists_3`）で書き、rtrancl 機構を使わない。
  `scx_N_facts` の S1/S2/S4/S5/S6/S7 は `c1_around_5`（Lean 移植済）がそのまま
  与えるので再証明していない（`scx_N_marked_edge` で読み替えるだけ）。
  `scb_context_eq_of_prefix` は Isabelle の `segnz` 仮定を**落とせる**
  （Lean の `scb_unique_decomp_unconditional` が無条件なので）。

  **本ファイルは新しい `Prop` を露出しない。**

  ⚠️ 罠（実際に踏んだ）: `Lng X` は `X.length` の abbrev だが **rw/omega には
  別アトム**。長さ等式は用途に応じて `Lng` 形と `.length` 形を defeq-cast
  （`have h : X.length = _ := hLng形`）で使い分けること。また omega は
  `(n-1) * w` を不透明アトム扱いするので `w ≤ (n-1)*w` は
  `Nat.mul_le_mul_right` で明示的に供給する。
-/

namespace PSS

/-! ## §1 基盤 — Isabelle `scx_addBT_assoc` … `scx_scb_compose` (pss_wip.thy:82123–82170) -/

/-- Isabelle `scx_addBT_assoc`。 -/
private theorem addBT_assoc_cf1 (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  cases a; cases b; cases c; simp [addBT]

/-- Isabelle `scx_addBT_0left`。 -/
private theorem addBT_zero_left_cf1 (t : BT) : addBT BZero t = t := by
  cases t; simp [addBT, BZero]

/-- Isabelle `scx_addBT_0right`（Isabelle では `add_0_right` 相当）。 -/
private theorem addBT_zero_right_cf1 (t : BT) : addBT t BZero = t := by
  cases t; simp [addBT, BZero]

/-- Isabelle `scx_TB_zero`。 -/
private theorem BZero_mem_T_B_cf1 : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

/-- Isabelle `scx_TB_multBT`。 -/
private theorem multBT_mem_T_B_cf1 {a : BT} (ha : a ∈ T_B) (n : ℕ) :
    multBT a n ∈ T_B := by
  induction n with
  | zero => simpa [multBT] using BZero_mem_T_B_cf1
  | succ k ih => exact addBT_mem_T_B ih ha

/-- Isabelle `scx_TB_Dpt_body`。 -/
private theorem T_B_Dprin_body_cf1 {v : ℕ∞} {t : BT} (h : Dprin v t ∈ T_B) :
    t ∈ T_B := by
  simp only [T_B, Set.mem_setOf_eq, Dprin, dfree_BT, dfree_BPList, dfree_BP,
    Bool.and_eq_true, bne_iff_ne, ne_eq, and_true] at h ⊢
  exact h.2

/-- Isabelle `scx_TB_addBT_left` / `scx_TB_addBT_right`。 -/
private theorem T_B_addBT_split_cf1 {a b : BT} (h : addBT a b ∈ T_B) :
    a ∈ T_B ∧ b ∈ T_B := by
  cases a with
  | trm as =>
    cases b with
    | trm bs =>
      simp only [T_B, Set.mem_setOf_eq, addBT, dfree_BT] at h ⊢
      induction as with
      | nil => simpa [dfree_BPList] using h
      | cons p ps ih =>
          simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h ⊢
          exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩

/-- Isabelle `scx_scb_compose`（scb 分解の合成則; 中心 `c` は文字列のまま）。 -/
private theorem scb_compose_str_cf1 {T X : BT} {s₁ s₂ c b₁ b₂ : List Sym}
    (d1 : scb_decomp T s₁ (flatBT X) b₁)
    (d2 : scb_decomp X s₂ c b₂)
    (hXne : X ≠ BZero) :
    scb_decomp T (s₁ ++ s₂) c (b₂ ++ b₁) := by
  obtain ⟨fT, _, rb1⟩ := d1
  obtain ⟨fX, pc, rb2⟩ := d2
  refine ⟨?_, ?_, ?_⟩
  · rw [fT, fX]; simp [List.append_assoc]
  · intro _; exact pc hXne
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact rb2 x h
    · exact rb1 x h

/-! ## §1.2 接頭辞の簡約性 — Isabelle `scx_take_RT_PS` / `scx_seg0_RT_PS` -/

private theorem take_RTPS_aux_cf1 : ∀ (d : ℕ) (K : PS) (j : ℕ), RTPS K →
    j < Lng K → Lng K - (j + 1) = d → RTPS (K.take (j + 1)) := by
  intro d
  induction d with
  | zero =>
      intro K j hK hj hd
      have hjL : j + 1 = Lng K := by omega
      rw [hjL, List.take_length]
      exact hK
  | succ d ih =>
      intro K j hK hj hd
      have hj2 : j + 1 < Lng K := by omega
      have hd2 : Lng K - (j + 1 + 1) = d := by omega
      have ih' : RTPS (K.take (j + 1 + 1)) := ih K (j + 1) hK hj2 hd2
      have hle2 : j + 2 ≤ Lng K := by omega
      have hLT : Lng (K.take (j + 2)) = j + 2 := by
        rw [show Lng (K.take (j + 2)) = min (j + 2) (Lng K) from List.length_take ..]
        omega
      have hlen2 : 1 < Lng (K.take (j + 2)) := by rw [hLT]; omega
      have hPred : Pred (K.take (j + 2)) = K.take (j + 1) := by
        rw [Pred_eq_take (K.take (j + 2)) hlen2, hLT, List.take_take]
        congr 1
        omega
      have := RTPS_Pred (K.take (j + 2)) (by simpa using ih')
      rwa [hPred] at this

/-- Isabelle `scx_take_RT_PS` (pss_wip.thy:82171)。 -/
theorem scx_take_RTPS (K : PS) (j : ℕ) (hK : RTPS K) (hj : j < Lng K) :
    RTPS (K.take (j + 1)) :=
  take_RTPS_aux_cf1 (Lng K - (j + 1)) K j hK hj rfl

/-- `seg K 0 j = K.take (j+1)`（Isabelle `seg_0_eq_take`）。 -/
theorem scx_seg0_eq_take (K : PS) (j : ℕ) (hj : j < Lng K) :
    seg K 0 j = K.take (j + 1) := by
  have := seg_eq_take_drop_adm K 0 j (Nat.zero_le _) hj
  simpa using this

/-- Isabelle `scx_seg0_RT_PS` (pss_wip.thy:82199)。 -/
theorem scx_seg0_RTPS (K : PS) (j : ℕ) (hK : RTPS K) (hj : j < Lng K) :
    RTPS (seg K 0 j) := by
  rw [scx_seg0_eq_take K j hj]
  exact scx_take_RTPS K j hK hj

/-- Isabelle `scx_map_block_seg` (pss_wip.thy:82210)。追加ブロックは切片。 -/
theorem scx_map_block_seg (M : PS) (j0 j1 : ℕ) (h1 : 1 ≤ j1) :
    (List.range' j0 (j1 - j0)).map (fun j => (entry M 0 j, entry M 1 j))
      = seg M j0 (j1 - 1) := by
  unfold seg
  congr 2
  omega

/-! ## §1.3 行 0 の親への降下 — Isabelle `scx_le0_to_parent` (pss_wip.thy:82278)

Isabelle は `rtranclp.cases` で最後の一歩を剥がすが、Lean は行 0 の値特徴付け
（`ancestor_basic_1` ＋ `parent_exists_3`）で書ける。 -/

/-- Isabelle `scx_le0_to_parent`。`a ≤₀ j₁`・`j₀ <^Next₀ j₁`・`a ≠ j₁` なら
`a ≤₀ j₀`。 -/
theorem scx_le0_to_parent (M : PS) (a j0 j1 : ℕ) (hM : TPS M)
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
  -- `a ≤ j₀`: さもなくば `j₀ < a < j₁` で `M₀,j₁ ≤ M₀,a` と `M₀,a < M₀,j₁` が衝突
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

/-! ## §1.4 簡約性と係数の関係 — Isabelle `scx_row1_bound` (pss_wip.thy:82228)

簡約列では行 0 の親辺に沿って行 1 の係数は高々 1 しか増えない。もっと増えたなら
`j₀` の行 1 の親 `j'`（`parent_exists_2` で存在、条件(A) の等式を満たす）が
`j₀'` と `j₀` の間に真に入り `le0 M j' j₀` を持つ — しかしその区間の列は
行 0 の値が `M₀,j₀` 以上である一方、行 0 の祖先関係は値を狭義に増やすので矛盾。 -/

/-- 行 0 の親辺から祖先関係。Isabelle `poper_nextR_imp_le0`。 -/
private theorem le0_of_nextR0_cf1 (M : PS) (a b : ℕ) (hM : TPS M)
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

/-- Isabelle `scx_row1_bound` (pss_wip.thy:82228)。 -/
theorem scx_row1_bound (M : PS) (j0' j0 : ℕ) (hR : RTPS M)
    (np : nextR M 0 j0' j0 = true) :
    entry M 1 j0 ≤ entry M 1 j0' + 1 := by
  by_contra hc
  push_neg at hc
  have hM : TPS M := RTPS_TPS M hR
  have hn0 : nextrel0 M j0' j0 = true := by simpa [nextR] using np
  have hh := hn0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hh
  obtain ⟨⟨⟨⟨_hj0'L, hj0L⟩, hj0'j0⟩, _he0⟩, hmin⟩ := hh
  have hleR0 : leR M 0 j0' j0 = true := le0_of_nextR0_cf1 M j0' j0 hM np
  have helt : entry M 1 j0' < entry M 1 j0 := by omega
  obtain ⟨j', hj'ge, hj'lt, hj'par⟩ :=
    parent_exists_2 M j0' j0 hM hj0'j0 hj0L helt hleR0
  have huniq1 : ∀ q, nextR M 1 q j0 = true → q = j' :=
    fun q hq => nextR1_unique_mr M q j' j0 hq hj'par
  have hp1 : hasParent M 1 j0 = true :=
    (hasParent_iff_unique_fseq M 1 j0).mpr ⟨j', hj'par, huniq1⟩
  have hpj' : parent M 1 j0 = j' :=
    parent_eq_of_unique_fseq M 1 j0 j' hj'par huniq1
  have hA : RedCondA M = true := (RTPS_condAB M hR).1
  have heq1 : entry M 1 (parent M 1 j0) + 1 = entry M 1 j0 :=
    RedCondA_apply M hA 1 j0 (by omega) hj0L hp1
  rw [hpj'] at heq1
  have hj'gt : j0' < j' := by
    rcases Nat.eq_or_lt_of_le hj'ge with h | h
    · exfalso; rw [← h] at heq1; omega
    · exact h
  have hle0j' : le0 M j' j0 = true := by
    have hh1 := hj'par
    simp only [nextR, if_neg (by omega : ¬(1 : ℕ) = 0), nextrel1,
      Bool.and_eq_true] at hh1
    exact hh1.1.2
  have hle0j'R : leR M 0 j' j0 = true := by simpa [leR] using hle0j'
  have he0lt : entry M 0 j' < entry M 0 j0 :=
    ancestor_basic_1 M j' j0 j0 hM hj'lt le_rfl hle0j'R
  have he0ge : entry M 0 j0 ≤ entry M 0 j' := by
    have hj := hmin j' hj'lt
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at hj
    rcases hj with h' | h'
    · omega
    · exact h'
  omega

/-! ## §2 host 基本事実 — Isabelle `scx_host_basic` (pss_wip.thy:82322) -/

/-- Isabelle `scx_host_basic`。条件(I)・`j₀ > 0` の下での 8 つの基本事実。

Isabelle の `le0 M 0 j₀`（HB(4)）経由で `hasParent M 0 j₀`（HB(5)）を出す迂回は
Lean では不要（`mono_hasParent_row0` が直接与える）。ただし `le0 M 0 j₀` 自体は
`N` の単調性で使うので `scx_le0_to_parent` から出しておく。 -/
theorem scx_host_basic (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) :
    hasParent M 0 (Lng M - 1) = true ∧
    entry M 1 (Lng M - 1) = 0 ∧
    adm M (parent M 0 (Lng M - 1)) = true ∧
    le0 M 0 (parent M 0 (Lng M - 1)) = true ∧
    hasParent M 0 (parent M 0 (Lng M - 1)) = true ∧
    nextR M 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)) = true ∧
    entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1)) ∧
    parent M 0 (parent M 0 (Lng M - 1)) < parent M 0 (Lng M - 1) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  have hadmj0 : adm M (parent M 0 (Lng M - 1)) = true := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastParent, lastIdx] using hI.2
  -- `0 ≤₀ j₁` は単調性そのもの
  have hle01 : le0 M 0 (Lng M - 1) = true := by
    have hh := hmono
    simp only [monoT, Bool.and_eq_true] at hh
    simpa [leR] using hh.2
  have hedge : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hasParent_next_fseq M 0 (Lng M - 1) hp0
  have hj0lt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh := hedge
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hle0j0 : le0 M 0 (parent M 0 (Lng M - 1)) = true :=
    scx_le0_to_parent M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) hM hle01 hedge
      (by omega)
  have hpj0 : hasParent M 0 (parent M 0 (Lng M - 1)) = true :=
    mono_hasParent_row0 M hM hmono (parent M 0 (Lng M - 1)) hj0pos (by omega)
  have hnp : nextR M 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)) = true :=
    hasParent_next_fseq M 0 (parent M 0 (Lng M - 1)) hpj0
  have hj0'lt : parent M 0 (parent M 0 (Lng M - 1)) < parent M 0 (Lng M - 1) := by
    have hh : nextrel0 M (parent M 0 (parent M 0 (Lng M - 1)))
        (parent M 0 (Lng M - 1)) = true := by simpa [nextR] using hnp
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  exact ⟨hp0, he1z, hadmj0, hle0j0, hpj0, hnp, by omega, hj0'lt⟩

/-! ## §3 反復の構造 — Isabelle `Lng_operI` / `operI_Suc_append` / `scx_N_facts` -/

/-- Isabelle `kind0_parent_facts` (pss_wip.thy:13671) の必要部分。 -/
private theorem kind0_facts_cf1 (M : PS)
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

/-- Isabelle `operI_Suc_append` (pss_wip.thy:17621)。 -/
private theorem operI_Suc_append_cf1 (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    oper M (n + 1) = oper M n ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
  obtain ⟨_, _, hnz, hp, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn := oper_d0zero_expand_68 M n hL hnz hp e1z
  have hsn := oper_d0zero_expand_68 M (n + 1) hL hnz hp e1z
  simp only at hn hsn
  rw [hn, hsn, List.range_succ, List.flatMap_append]
  simp [List.append_assoc]

private theorem length_flatMap_const_cf1 {α β : Type} (l : List α) (B : List β) :
    (l.flatMap (fun _ => B)).length = l.length * B.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Isabelle `Lng_operI`。条件(I)（kind-0）の反復の長さ。 -/
theorem scx_Lng_oper (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    Lng (oper M n) =
      parent M 0 (Lng M - 1) + n * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
  obtain ⟨_, hj0lt, hnz, hp, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hexp := oper_d0zero_expand_68 M n hL hnz hp e1z
  simp only at hexp
  have hj0L : parent M 0 (Lng M - 1) ≤ Lng M := by omega
  rw [hexp]
  simp only [Lng, List.length_append, length_flatMap_const_cf1,
    List.length_take, List.length_map, List.length_range, List.length_range',
    Nat.min_eq_left hj0L]

/-! ### §3.2 追加ブロック内の値読み出し -/

private theorem getElem?_entry_cf1 (X : PS) (j : ℕ) (hj : j < Lng X) :
    X[j]? = some (entry X 0 j, entry X 1 j) := by
  simp [entry, List.getElem?_eq_getElem hj]

/-- `M[n]` の最終ブロック（開始点 `idx = j₀ + (n-1)w`）は `M` の枝ブロックの逐語コピー。 -/
private theorem entry_oper_block_cf1 (M : PS) (n i k : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 1 ≤ n) (hi : i = 0 ∨ i = 1)
    (hk : k < Lng M - 1 - parent M 0 (Lng M - 1)) :
    entry (oper M n) i
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + k)
      = entry M i (parent M 0 (Lng M - 1) + k) := by
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hA : oper M n = oper M (n - 1) ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
    have h := operI_Suc_append_cf1 M (n - 1) hp0 e1z
    rwa [show n - 1 + 1 = n by omega] at h
  -- ⚠️ `Lng X` と `X.length` は rw/omega にとって別アトム: defeq-cast で橋渡しする
  have hLA : (oper M (n - 1)).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper M (n - 1) hp0 e1z
  have hget : (oper M n)[parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + k]?
      = some (entry M 0 (parent M 0 (Lng M - 1) + k),
              entry M 1 (parent M 0 (Lng M - 1) + k)) := by
    rw [hA, List.getElem?_append_right (by rw [hLA]; omega), hLA,
      show parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + k
        - (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = k from by omega,
      List.getElem?_map]
    have hr : (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1)))[k]?
        = some (parent M 0 (Lng M - 1) + k) := by
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp [List.getElem_range']
    rw [hr]
    simp
  rcases hi with rfl | rfl
  · simp [entry, hget]
  · simp [entry, hget]

/-! ### §3.3 `N = seg (M[n]) 0 idx` の構造束 — Isabelle `scx_N_facts` (pss_wip.thy:82405)

Isabelle の 18 個の結論のうち、S1/S2/S4/S5/S6/S7（`Marked`・親辺・`transJ0 N`・
`transJm1 N`・`Trans (Pred N) ≠ 0`・`¬condVI N`）は Lean では **`c1_around_5` が
そのまま与える**ので再証明しない。ここでは残り（長さ・`take` 表示・`Pred N`・
簡約性・単調性・値読み出し・末尾切片・`le0`）を証明する。 -/

/-- `Pred (X.take (m+1)) = X.take m`（`1 ≤ m`、`m+1 ≤ Lng X`）。 -/
private theorem Pred_take_cf1 (X : PS) (m : ℕ) (hm : 1 ≤ m) (hmX : m + 1 ≤ Lng X) :
    Pred (X.take (m + 1)) = X.take m := by
  have hmX' : m + 1 ≤ X.length := hmX
  have hLT : Lng (X.take (m + 1)) = m + 1 := by
    show (X.take (m + 1)).length = m + 1
    simp only [List.length_take]
    omega
  have hlen2 : 1 < Lng (X.take (m + 1)) := by rw [hLT]; omega
  rw [Pred_eq_take _ hlen2, hLT, List.take_take]
  congr 1
  omega

/-- Isabelle `scx_N_facts` S12: `Lng (M[n]) = idx + w`。 -/
theorem scx_Lng_oper_idx (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 1 ≤ n) :
    Lng (oper M n) =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) := by
  rw [scx_Lng_oper M n hp0 e1z]
  have hnw : n * (Lng M - 1 - parent M 0 (Lng M - 1))
      = (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.succ_sub_one, Nat.succ_mul]
  omega

/-- Isabelle `scx_N_facts` S15: `N = take (idx+1) (M[n])`（＋ S3: `Lng N = idx+1`）。 -/
theorem scx_N_take (M : PS) (n idx : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0)
    (hidx : idx < Lng (oper M n)) :
    seg (oper M n) 0 idx = (oper M n).take (idx + 1) ∧
    Lng (seg (oper M n) 0 idx) = idx + 1 := by
  have hidx' : idx < (oper M n).length := hidx
  have h := scx_seg0_eq_take (oper M n) idx hidx
  refine ⟨h, ?_⟩
  have : Lng ((oper M n).take (idx + 1)) = idx + 1 := by
    simp only [Lng, List.length_take]
    omega
  rw [h]; exact this

/-- Isabelle `scx_N_facts` S8: `Pred N = M[n-1]`。 -/
theorem scx_N_Pred (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 2 ≤ n) :
    Pred (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = oper M (n - 1) := by
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hA : oper M n = oper M (n - 1) ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
    have h := operI_Suc_append_cf1 M (n - 1) hp0 e1z
    rwa [show n - 1 + 1 = n by omega] at h
  have hLA : (oper M (n - 1)).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper M (n - 1) hp0 e1z
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z (by omega)
  -- `(n-1)·w ≥ w ≥ 1`（omega は非線形項をアトム扱いするので明示的に供給する）
  have hmul : Lng M - 1 - parent M 0 (Lng M - 1)
      ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have h := Nat.mul_le_mul_right (Lng M - 1 - parent M 0 (Lng M - 1))
      (show 1 ≤ n - 1 by omega)
    simpa using h
  have hidx : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length
    omega
  have hseg := scx_seg0_eq_take (oper M n) _ hidx
  rw [hseg, Pred_take_cf1 (oper M n) _ (by omega) (by show _ ≤ (oper M n).length; omega)]
  conv_lhs => rw [hA]
  rw [← hLA, List.take_left]

/-! ### §3.4 `c1_around_5` の読み替え

`transJ0 M = parent M 0 (Lng M - 1)` / `transJ1 M = Lng M - 1` は定義的等式
（`rfl`）なので、`c1_around_5` の結論をそのまま本ファイルの記法に移せる。 -/

/-- Isabelle `scx_N_facts` S1/S2（`m_8_1_c1_around_part5` の instance）。 -/
theorem scx_N_marked_edge (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n) :
    Marked (oper M n)
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) ∧
    nextR (oper M n) 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true ∧
    Trans (Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))) ≠ BZero ∧
    transCondVI (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = false ∧
    transJ0 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = parent M 0 (parent M 0 (Lng M - 1)) ∧
    transJm1 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = Adm M (parent M 0 (parent M 0 (Lng M - 1))) := by
  obtain ⟨hp0, e1z, hadm, _, _, hnp, hge, _⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have h5 := c1_around_5 M (parent M 0 (parent M 0 (Lng M - 1))) n hR hmono
    hadm hj1 hge hI hnp (by omega)
  obtain ⟨hm, he, _, hj0N, hjm1N, hne, hVI⟩ := h5
  exact ⟨hm, he, hne, hVI, hj0N, hjm1N⟩

/-! ### §3.5 `le0`・簡約性・単調性 -/

/-- Isabelle `scx_N_facts` S16: `le0 (M[n]) 0 idx`。 -/
theorem scx_le0_oper_idx (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n) :
    le0 (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true := by
  obtain ⟨hp0, e1z, _hadm, hle0j0, _hpj0, hnp, _, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  -- (a) `0 ≤₀ j₀'` in `M`
  have hedge' : nextrel0 M (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)) = true := by simpa [nextR] using hnp
  have hle0j0' : le0 M 0 (parent M 0 (parent M 0 (Lng M - 1))) = true :=
    scx_le0_to_parent M 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)) hM hle0j0 hedge' (by omega)
  -- (b) 逐語接頭辞なので `M[n]` に移せる
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hmul : Lng M - 1 - parent M 0 (Lng M - 1)
      ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have h := Nat.mul_le_mul_right (Lng M - 1 - parent M 0 (Lng M - 1))
      (show 1 ≤ n - 1 by omega)
    simpa using h
  have hoperT : TPS (oper M n) := by
    have : (oper M n).length ≠ 0 := by omega
    simpa [TPS, ← List.length_eq_zero_iff] using this
  have hlt0' : parent M 0 (parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length
    omega
  have hoper0' : leR (oper M n) 0 0
      (parent M 0 (parent M 0 (Lng M - 1))) = true := by
    rcases Nat.eq_zero_or_pos (parent M 0 (parent M 0 (Lng M - 1))) with hz | hpos
    · rw [hz]; exact leR0_refl_68 (oper M n) 0 (by show _ < (oper M n).length; omega)
    · refine parent_exists_3 (oper M n) 0 _ hoperT hpos hlt0' ?_
      intro j hj0 hjle
      rw [entry_oper_lt_last_68 M n 0 0 hL hn1 (Or.inl rfl) (by omega),
        entry_oper_lt_last_68 M n 0 j hL hn1 (Or.inl rfl) (by omega)]
      exact ancestor_basic_1 M 0 j (parent M 0 (parent M 0 (Lng M - 1))) hM hj0
        hjle (by simpa [leR] using hle0j0')
  -- (c) `j₀' <^Next₀ idx` in `M[n]`（part (5)）を継いで推移律
  obtain ⟨_, hedgeN, _, _, _, _⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  have hstep : leR (oper M n) 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true :=
    le0_of_nextR0_cf1 (oper M n) _ _ hoperT hedgeN
  have := row0_transitive (oper M n) 0 (parent M 0 (parent M 0 (Lng M - 1)))
    (parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) hoperT hoper0' hstep
  simpa [leR] using this

/-- Isabelle `scx_N_facts` S9/S10/S11: `N` の簡約性・単調性。 -/
theorem scx_N_RTPS_monoT (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n) :
    RTPS (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) ∧
    monoT (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = true := by
  obtain ⟨hp0, e1z, _, _, _, _, _, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hmul : Lng M - 1 - parent M 0 (Lng M - 1)
      ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have h := Nat.mul_le_mul_right (Lng M - 1 - parent M 0 (Lng M - 1))
      (show 1 ≤ n - 1 by omega)
    simpa using h
  have hidx : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length; omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR hn1
  have hNR : RTPS (seg (oper M n) 0 _) := scx_seg0_RTPS (oper M n) _ hMnR hidx
  refine ⟨hNR, ?_⟩
  have hseg := scx_seg0_eq_take (oper M n) _ hidx
  have hLN : Lng (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + 1 :=
    (scx_N_take M n _ hp0 e1z hidx).2
  have hLN' : (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))).length
      = parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + 1 := hLN
  have hle0N : le0 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true := by
    rw [hseg, le0_take_adm (oper M n) _ 0 _ (by show _ ≤ (oper M n).length; omega)
      (by omega) (by omega)]
    exact scx_le0_oper_idx M n hR hmono hj1 hI hj0pos hn
  have hnz : zeroT (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    left
    rw [hLN]
    omega
  simp only [monoT, Bool.and_eq_true, Bool.not_eq_true', hnz, hLN, leR]
  refine ⟨trivial, ?_⟩
  simpa using hle0N

/-! ### §3.6 `N` の値読み出し・末尾切片・親辺 -/

/-- Isabelle `scx_N_facts` S17: `N` は `j₀` まで `M` の逐語コピー。 -/
theorem scx_N_entry_le_j0 (M : PS) (n i x : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 1 ≤ n) (hi : i = 0 ∨ i = 1)
    (hx : x ≤ parent M 0 (Lng M - 1)) :
    entry (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) i x
      = entry M i x := by
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn
  have hidx : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length; omega
  rw [scx_seg0_eq_take (oper M n) _ hidx, entry_take _ _ i x (by omega)]
  exact entry_oper_lt_last_68 M n i x hL hn hi (by omega)

/-- Isabelle `scx_N_facts` S13: `entry N 1 idx = entry M 1 j₀`（追加列の値）。 -/
theorem scx_N_entry1_idx (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 1 ≤ n) :
    entry (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) 1
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
      = entry M 1 (parent M 0 (Lng M - 1)) := by
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn
  have hidx : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length; omega
  rw [scx_seg0_eq_take (oper M n) _ hidx, entry_take _ _ 1 _ (by omega)]
  have h := entry_oper_block_cf1 M n 1 0 hp0 e1z hn (Or.inr rfl) (by omega)
  simpa using h

/-- Isabelle `scx_N_facts` S14: `M[n]` の末尾切片は `M` の枝ブロックそのもの。 -/
theorem scx_N_tail_seg (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) (hn : 1 ≤ n) :
    seg (oper M n)
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
        (Lng (oper M n) - 1)
      = seg M (parent M 0 (Lng M - 1)) (Lng M - 1 - 1) := by
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn
  have hLn2 : Lng (oper M n) =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) := hLn
  apply List.ext_getElem
  · simp only [length_seg, hLn2]
    omega
  · intro k hk₁ _
    have hkw : k < Lng M - 1 - parent M 0 (Lng M - 1) := by
      simp only [length_seg, hLn2] at hk₁
      omega
    rw [seg_getElem_68, seg_getElem_68]
    rw [entry_oper_block_cf1 M n 0 k hp0 e1z hn (Or.inl rfl) hkw,
      entry_oper_block_cf1 M n 1 k hp0 e1z hn (Or.inr rfl) hkw]

/-- Isabelle `scx_N_facts` S18: `j₀' <^Next₀ idx` は `N` の中でも成り立つ。 -/
theorem scx_N_nextR (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n) :
    nextR (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) 0
        (parent M 0 (parent M 0 (Lng M - 1)))
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true := by
  obtain ⟨hp0, e1z, _, _, _, _, _, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hidx : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    show _ < (oper M n).length; omega
  obtain ⟨_, hedgeN, _, _, _, _⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  rw [scx_seg0_eq_take (oper M n) _ hidx,
    nextR_take_adm (oper M n) _ 0 _ _ (by show _ ≤ (oper M n).length; omega)
      (by omega) (by omega)]
  exact hedgeN

/-! ## §4 最終ブロック開始点の marked 値 — Isabelle `scx_mark_idx` (pss_wip.thy:82604)
／`scx_c1_w1` (同 :82645) -/

/-- `Pred M` は `M` の `Lng M - 1` 接頭辞なので、`j < Lng M - 1` で値が一致。 -/
private theorem entry_Pred_cf1 (M : PS) (i j : ℕ) (hlen : 1 < Lng M)
    (hj : j < Lng M - 1) : entry (Pred M) i j = entry M i j := by
  rw [Pred_eq_take M hlen]
  exact entry_take M (Lng M - 1) i j hj

/-- Isabelle `scx_mark_idx` (pss_wip.thy:82604)。`w ≥ 2`・`n ≥ 2` のとき
`Mark (M[n]) idx = c₁ = Mark (Pred M) (Adm_M(j₀))`。

`Mark`/`Trans` 表示（§7.4）で末尾切片を読み、それが逐語の枝ブロック
（`scx_N_tail_seg`）であること、その `Trans` が `c₁` であること（`c1_around_1`
の切片等式、訂正 A20 のガード `j₀ < j₁ - 1` ＝ `w ≥ 2`）を合わせる。 -/
theorem scx_mark_idx (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n)
    (hw2 : 1 < Lng M - 1 - parent M 0 (Lng M - 1)) :
    Mark (oper M n)
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
      = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) := by
  obtain ⟨hp0, e1z, hadm, _, _, _, hge, _⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR hn1
  obtain ⟨hmk, _, _, _, _, _⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hidxlt : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) - 1 := by
    show _ < (oper M n).length - 1; omega
  have hrepr := Mark_Trans_repr (oper M n) _ hmk hMnR hidxlt
  rw [hrepr, scx_N_tail_seg M n hp0 e1z hn1]
  -- `Trans (seg M j₀ (j₁-1)) = transC1 M`（A20 のガードは `w ≥ 2`）
  have h1 := c1_around_1 M hR hmono hadm hj1 hge
  have hslice := h1.2.2.1 (Or.inl (by
    show transJ0 M < transJ1 M - 1
    show parent M 0 (Lng M - 1) < Lng M - 1 - 1
    omega))
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  rw [htJ0, htJ1] at hslice
  rw [hslice]
  rfl

/-- Isabelle `scx_c1_w1` (pss_wip.thy:82645)。`w = 1` のとき追加ブロックは単一列
`(M₀,j₀, M₁,j₀)` なので `c₁ = D_{M₁,j₀} 0`（右端第 1 基点の値、`m_7_3_Mark_rightmost1`）。 -/
theorem scx_c1_w1 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hw1 : Lng M - 1 - parent M 0 (Lng M - 1) = 1) :
    Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))
      = Dprin ((entry M 1 (parent M 0 (Lng M - 1)) : ℕ)) BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have he1z : entry M 1 (Lng M - 1) = 0 := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastIdx] using hI.1
  have hadm : adm M (parent M 0 (Lng M - 1)) = true := by
    simp only [transCondI, Bool.and_eq_true, beq_iff_eq] at hI
    simpa [lastParent, lastIdx] using hI.2
  obtain ⟨_, hj0lt, _, _, _⟩ := kind0_facts_cf1 M hp0 he1z
  have hmkA : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp0
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hnzP : zeroT (Pred M) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    left
    rw [hLP]
    omega
  have hjm1eq : Adm M (parent M 0 (Lng M - 1)) = parent M 0 (Lng M - 1) := by
    simp [Adm, hadm]
  have hLPeq : Adm M (parent M 0 (Lng M - 1)) = Lng (Pred M) - 1 := by
    rw [hjm1eq, hLP]; omega
  have hright := (m_7_3_Mark_rightmost1 (Pred M) (Adm M (parent M 0 (Lng M - 1)))
    hmkA hpredR hnzP).mp hLPeq
  rw [hright, hjm1eq, entry_Pred_cf1 M 1 (parent M 0 (Lng M - 1)) hlen (by omega)]

/-! ## §5 `j₋₁'` は反復の基点 — Isabelle `scx_marked_jm1p` (pss_wip.thy:82685)

Isabelle は `le0_prefix_agree` / `adm_prefix_agree_eq` を使う。Lean 側の同等物は
`8.1-condI-III-c1-around` に `_p5` 接尾辞で **private** に存在するので、ここでは
`_cf1` 接尾辞で同じものを private に再構成する（scope 外には出さない）。 -/

private theorem entry_row_ne_zero_cf1 (X : PS) (i z : ℕ) (hi : i ≠ 0) :
    entry X i z = entry X 1 z := by
  simp only [entry]
  cases X[z]? <;> simp [hi]

private theorem le0Aux_refl_cf1 (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

/-- 接頭辞領域の `le0` 転送（Isabelle `le0_prefix_agree`）。 -/
private theorem le0_agree_lift_cf1 (A B : PS) (c x y : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcB : c < Lng B) (hy : y ≤ c)
    (h : leR A 0 x y = true) : leR B 0 x y = true := by
  have hxy : x ≤ y := by
    have hh : le0 A x y = true := by simpa [leR] using h
    simp only [le0, Bool.and_eq_true] at hh
    exact le0Aux_index_fseq hh.2
  rcases Nat.eq_or_lt_of_le hxy with heq | hlt
  · subst heq
    simp [leR, le0, show x < Lng B by omega, le0Aux_refl_cf1]
  · apply parent_exists_3 B x y hBT hlt (by omega)
    intro k hxk hky
    have hbase : entry A 0 x < entry A 0 k :=
      ancestor_basic_1 A x k y hAT hxk hky h
    rw [agree 0 x (by omega), agree 0 k (by omega)] at hbase
    exact hbase

/-- 接頭辞領域の `nextrel1` 転送。 -/
private theorem nextrel1_prefix_imp_cf1 (A B : PS) (c x y : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcA : c < Lng A) (hcB : c < Lng B) (hy : y ≤ c)
    (h : nextrel1 A x y = true) : nextrel1 B x y = true := by
  have agree' : ∀ i z, z ≤ c → entry B i z = entry A i z := by
    intro i z hz
    exact (agree i z hz).symm
  have hh := h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hxy : x < y := hh.1.1.1.2
  have he1A : entry A 1 x < entry A 1 y := hh.1.1.2
  have hle0A : le0 A x y = true := hh.1.2
  have hvalleyA := hh.2
  have hle0B : leR B 0 x y = true :=
    le0_agree_lift_cf1 A B c x y hAT hBT agree hcB hy (by simpa [leR] using hle0A)
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by omega, by omega⟩, hxy⟩, ?_⟩, by simpa [leR] using hle0B⟩, ?_⟩
  · rw [← agree 1 x (by omega), ← agree 1 y hy]
    exact he1A
  · rw [List.all_eq_true]
    intro j _
    by_cases hcase : x < j ∧ le0 B j y = true
    · have hjy : j ≤ y := by
        have hh' := hcase.2
        simp only [le0, Bool.and_eq_true] at hh'
        exact le0Aux_index_fseq hh'.2
      have hle0Aj : le0 A j y = true := by
        have := le0_agree_lift_cf1 B A c j y hBT hAT agree' hcA hy
          (by simpa [leR] using hcase.2)
        simpa [leR] using this
      have hjA : j < Lng A := by omega
      have hv := List.all_eq_true.mp hvalleyA j (List.mem_range.mpr hjA)
      simp only [hle0Aj, hcase.1, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at hv
      have hgoal : entry B 1 y ≤ entry B 1 j := by
        rw [← agree 1 y hy, ← agree 1 j (by omega)]
        exact hv
      simp [hgoal]
    · rcases not_and_or.mp hcase with h' | h'
      · simp [h']
      · have h'' : le0 B j y = false := by revert h'; simp
        simp [h'']

/-- 接頭辞領域の `adm` 一致（Isabelle `adm_prefix_agree_eq`）。 -/
private theorem adm_prefix_agree_eq_cf1 (A B : PS) (c j : ℕ)
    (hAT : TPS A) (hBT : TPS B)
    (agree : ∀ i z, z ≤ c → entry A i z = entry B i z)
    (hcA : c < Lng A) (hcB : c < Lng B) (hjc : j + 1 ≤ c) :
    adm A j = adm B j := by
  have agree' : ∀ i z, z ≤ c → entry B i z = entry A i z := by
    intro i z hz
    exact (agree i z hz).symm
  have hpair : (nextR A 1 (j - 1) j = true ∧ nextR A 1 j (j + 1) = true)
      ↔ (nextR B 1 (j - 1) j = true ∧ nextR B 1 j (j + 1) = true) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by
        simp only [nextR] at h1 ⊢
        exact nextrel1_prefix_imp_cf1 A B c (j - 1) j hAT hBT agree hcA hcB
          (by omega) (by simpa using h1), by
        simp only [nextR] at h2 ⊢
        exact nextrel1_prefix_imp_cf1 A B c j (j + 1) hAT hBT agree hcA hcB
          (by omega) (by simpa using h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by
        simp only [nextR] at h1 ⊢
        exact nextrel1_prefix_imp_cf1 B A c (j - 1) j hBT hAT agree' hcB hcA
          (by omega) (by simpa using h1), by
        simp only [nextR] at h2 ⊢
        exact nextrel1_prefix_imp_cf1 B A c j (j + 1) hBT hAT agree' hcB hcA
          (by omega) (by simpa using h2)⟩
  have hnadm : nadm A j = nadm B j := by
    have hgA : decide (Lng A < j) = false := by simp; omega
    have hgB : decide (Lng B < j) = false := by simp; omega
    simp only [nadm, hgA, hgB, Bool.false_or]
    cases hA : (nextR A 1 (j - 1) j && nextR A 1 j (j + 1)) with
    | false =>
        cases hB : (nextR B 1 (j - 1) j && nextR B 1 j (j + 1)) with
        | false => rfl
        | true =>
            exfalso
            have hBpair : nextR B 1 (j - 1) j = true
                ∧ nextR B 1 j (j + 1) = true := by
              simpa [Bool.and_eq_true] using hB
            have hApair := hpair.mpr hBpair
            have hAt : (nextR A 1 (j - 1) j && nextR A 1 j (j + 1)) = true := by
              simp [hApair.1, hApair.2]
            rw [hAt] at hA
            cases hA
    | true =>
        have hApair : nextR A 1 (j - 1) j = true
            ∧ nextR A 1 j (j + 1) = true := by
          simpa [Bool.and_eq_true] using hA
        have hBpair := hpair.mp hApair
        have hBt : (nextR B 1 (j - 1) j && nextR B 1 j (j + 1)) = true := by
          simp [hBpair.1, hBpair.2]
        rw [hBt]
  simp [adm, hnadm]

/-- Isabelle `scx_marked_jm1p` (pss_wip.thy:82685)。`j₋₁' = Adm_M(j₀')` は
`M[n]` の基点でもある。 -/
theorem scx_marked_jm1p (M : PS) (n : ℕ) (hR : RTPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1) (hI : transCondI M = true)
    (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n) :
    Marked (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) := by
  obtain ⟨hp0, e1z, _hadm, _hle0j0, _hpj0, _hnp, _hge, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hjmle : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
      ≤ parent M 0 (parent M 0 (Lng M - 1)) :=
    Adm_le M (parent M 0 (parent M 0 (Lng M - 1)))
  have hadmM : adm M (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) = true :=
    Adm_adm M (parent M 0 (parent M 0 (Lng M - 1)))
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hmul : Lng M - 1 - parent M 0 (Lng M - 1)
      ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have h := Nat.mul_le_mul_right (Lng M - 1 - parent M 0 (Lng M - 1))
      (show 1 ≤ n - 1 by omega)
    simpa using h
  have hoperT : TPS (oper M n) := by
    have : (oper M n).length ≠ 0 := by omega
    simpa [TPS, ← List.length_eq_zero_iff] using this
  have hcB : parent M 0 (Lng M - 1) < Lng (oper M n) := by
    show _ < (oper M n).length; omega
  -- 逐語接頭辞の値一致（`i ≠ 0` は行 1 と同値なので全 `i` で成立）
  have agree : ∀ i z, z ≤ parent M 0 (Lng M - 1) →
      entry M i z = entry (oper M n) i z := by
    intro i z hz
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact (entry_oper_lt_last_68 M n 0 z hL hn1 (Or.inl rfl) (by omega)).symm
    · rw [entry_row_ne_zero_cf1 M i z (by omega),
        entry_row_ne_zero_cf1 (oper M n) i z (by omega)]
      exact (entry_oper_lt_last_68 M n 1 z hL hn1 (Or.inr rfl) (by omega)).symm
  -- (1) 許容性の転送
  have hadmOp : adm (oper M n)
      (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) = true := by
    rw [← adm_prefix_agree_eq_cf1 M (oper M n) (parent M 0 (Lng M - 1))
      (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) hM hoperT agree
      (by omega) hcB (by omega)]
    exact hadmM
  -- (2) `j₋₁' ≤₀ j₀'` を `M` で作って `M[n]` に移す
  have hle1M : leR M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
      (parent M 0 (parent M 0 (Lng M - 1))) = true :=
    adm_row1_ancestry M (parent M 0 (parent M 0 (Lng M - 1))) hM (by omega)
  have hle0M : leR M 0 (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
      (parent M 0 (parent M 0 (Lng M - 1))) = true :=
    row1_implies_row0 M _ _ hM hle1M
  have hle0Op : leR (oper M n) 0
      (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
      (parent M 0 (parent M 0 (Lng M - 1))) = true :=
    le0_agree_lift_cf1 M (oper M n) (parent M 0 (Lng M - 1)) _ _ hM hoperT
      agree hcB (by omega) hle0M
  -- (3) `j₀' <^Next₀ idx` と `idx ≤₀ 末尾` を継ぐ
  obtain ⟨hmk, hedgeN, _, _, _, _⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  have hstep : leR (oper M n) 0 (parent M 0 (parent M 0 (Lng M - 1)))
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = true :=
    le0_of_nextR0_cf1 (oper M n) _ _ hoperT hedgeN
  have hlast : leR (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
      (Lng (oper M n) - 1) := hmk.2.2
  refine ⟨hoperT, hadmOp, ?_⟩
  exact row0_transitive (oper M n) _ _ _ hoperT
    (row0_transitive (oper M n) _ _ _ hoperT hle0Op hstep) hlast

/-! ## §6 `Mark` の固定 — Isabelle `scb_context_eq_of_prefix` (pss_wip.thy:39775)
／`scx_mark_pin` (同 :82771)

Isabelle `scb_context_eq_of_prefix` の唯一の入力 `m_7_4_Trans_Mark_seg` は
**Lean に既にある**（`7.4-Trans-Mark-seg`、`Trans_Mark_seg_exists`）ので、
green-modulo の `Prop` にせず本ファイルで証明する。Isabelle の `segnz` 仮定は
Lean の `scb_unique_decomp_unconditional` が無条件なので**落とせる**（強化）。 -/

private theorem seg_full_cf1 (X : PS) (h : 0 < Lng X) : seg X 0 (Lng X - 1) = X := by
  rw [scx_seg0_eq_take X (Lng X - 1) (by omega),
    show Lng X - 1 + 1 = Lng X from by omega]
  exact List.take_length

/-- Isabelle `scb_context_eq_of_prefix` (pss_wip.thy:39775)。同じ接頭辞 `Trans` と
同じ `M₁,m` を持つ 2 つの基点付き簡約列は、`m` における scb 文脈 `(s,b)` を共有する。 -/
theorem scx_scb_context_eq_of_prefix (Q1 Q2 : PS) (m : ℕ)
    (mk1 : Marked Q1 m) (R1 : RTPS Q1) (mk2 : Marked Q2 m) (R2 : RTPS Q2)
    (mpos : 0 < m) (mlt1 : m < Lng Q1 - 1) (mlt2 : m < Lng Q2 - 1)
    (segeq : Trans (seg Q1 0 m) = Trans (seg Q2 0 m))
    (entryeq : entry Q1 1 m = entry Q2 1 m) :
    ∃ s b, scb_decomp (Trans Q1) s (flatBT (Mark Q1 m)) b ∧
           scb_decomp (Trans Q2) s (flatBT (Mark Q2 m)) b := by
  obtain ⟨s1, b1, C1seg, C1mark⟩ := Trans_Mark_seg_exists Q1 m mk1 R1 mpos mlt1
  obtain ⟨s2, b2, C2seg, C2mark⟩ := Trans_Mark_seg_exists Q2 m mk2 R2 mpos mlt2
  have A1 : scb_decomp (Trans (seg Q2 0 m)) s1
      (flatBT (Dprin (entry Q2 1 m : ℕ∞) BZero)) b1 := by
    rw [← segeq, ← entryeq]; exact C1seg
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (seg Q2 0 m))
    s1 s2 _ b1 b2 A1 C2seg
  subst hs; subst hb
  exact ⟨s1, b1, C1mark, C2mark⟩

/-- Isabelle `scx_mark_pin` (pss_wip.thy:82771)。基底の scb 対 `(s', b')` は
全ての反復に移るので、中心 `X` での `(s',b')`-分解は `Mark (M[n]) j₋₁' = X` を強制する。 -/
theorem scx_mark_pin (M : PS) (n : ℕ) (X : BT) (s' b' : List Sym)
    (hR : RTPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hI : transCondI M = true) (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n)
    (dInit : scb_decomp (Trans (Pred M)) s'
      (flatBT (Mark (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))) b')
    (dTn : scb_decomp (Trans (oper M n)) s' (flatBT X) b') :
    Mark (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) = X := by
  obtain ⟨hp0, e1z, hadm, _, _, hnp, hge, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hjmle : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
      ≤ parent M 0 (parent M 0 (Lng M - 1)) :=
    Adm_le M (parent M 0 (parent M 0 (Lng M - 1)))
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hLP : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hMnR : RTPS (oper M n) := RTPS_oper M n hR hn1
  have hmkn : Marked (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) :=
    scx_marked_jm1p M n hR hmono hj1 hI hj0pos hn
  have hmkP : Marked (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) :=
    (c1_around_2 M (parent M 0 (parent M 0 (Lng M - 1))) hR hmono hadm hj1
      hge hnp).2.1
  have hLn : (oper M n).length =
      parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        + (Lng M - 1 - parent M 0 (Lng M - 1)) :=
    scx_Lng_oper_idx M n hp0 e1z hn1
  have hmul : Lng M - 1 - parent M 0 (Lng M - 1)
      ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have h := Nat.mul_le_mul_right (Lng M - 1 - parent M 0 (Lng M - 1))
      (show 1 ≤ n - 1 by omega)
    simpa using h
  have hLnb : parent M 0 (Lng M - 1) + 2 ≤ (oper M n).length := by omega
  have hflatTn : flatBT (Trans (oper M n)) = s' ++ flatBT X ++ b' := dTn.1
  by_cases hjmz : Adm M (parent M 0 (parent M 0 (Lng M - 1))) = 0
  · -- `j₋₁' = 0`: 文脈は空、`Mark _ 0 = Trans _`
    have hposP : 0 < Lng (Pred M) := by omega
    have hm0P : Mark (Pred M) 0 = Trans (Pred M) := by
      have hmk0 : Marked (Pred M) 0 := by rwa [hjmz] at hmkP
      rw [Mark_Trans_repr_zero (Pred M) hpredR hmk0 (by omega),
        seg_full_cf1 (Pred M) hposP]
    have hposn : 0 < Lng (oper M n) := by show 0 < (oper M n).length; omega
    have hm0n : Mark (oper M n) 0 = Trans (oper M n) := by
      have hmk0n : Marked (oper M n) 0 := by rwa [hjmz] at hmkn
      rw [Mark_Trans_repr_zero (oper M n) hMnR hmk0n
          (by show 0 < (oper M n).length - 1; omega),
        seg_full_cf1 (oper M n) hposn]
    have e : flatBT (Trans (Pred M)) = s' ++ flatBT (Trans (Pred M)) ++ b' := by
      have h := dInit.1
      rwa [hjmz, hm0P] at h
    have hlene := congrArg List.length e
    simp only [List.length_append] at hlene
    have hs' : s' = [] := List.length_eq_zero_iff.mp (by omega)
    have hb' : b' = [] := List.length_eq_zero_iff.mp (by omega)
    have : flatBT (Trans (oper M n)) = flatBT X := by
      rw [hflatTn, hs', hb']; simp
    rw [hjmz, hm0n, ← unflatBT_flat (Trans (oper M n)), this, unflatBT_flat]
  · -- `j₋₁' > 0`: OW 文脈安定性で `(s',b')` に固定
    have hjmpos : 0 < Adm M (parent M 0 (parent M 0 (Lng M - 1))) := by omega
    have hmlt1 : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
        < Lng (oper M n) - 1 := by
      show _ < (oper M n).length - 1; omega
    have hmlt2 : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
        < Lng (Pred M) - 1 := by rw [hLP]; omega
    have hagr : ∀ i x, (i = 0 ∨ i = 1) →
        x ≤ Adm M (parent M 0 (parent M 0 (Lng M - 1))) →
        entry (oper M n) i x = entry (Pred M) i x := by
      intro i x hi hx
      rw [entry_oper_lt_last_68 M n i x hL hn1 hi (by omega),
        entry_Pred_cf1 M i x hlen (by omega)]
    have hsegeq_list : seg (oper M n) 0
        (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
        = seg (Pred M) 0 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) := by
      apply List.ext_getElem
      · simp
      · intro k hk₁ _
        have hkm : k ≤ Adm M (parent M 0 (parent M 0 (Lng M - 1))) := by
          simp only [length_seg] at hk₁; omega
        rw [seg_getElem_68, seg_getElem_68]
        rw [hagr 0 (0 + k) (Or.inl rfl) (by omega),
          hagr 1 (0 + k) (Or.inr rfl) (by omega)]
    have hsegeq : Trans (seg (oper M n) 0
        (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))
        = Trans (seg (Pred M) 0
          (Adm M (parent M 0 (parent M 0 (Lng M - 1))))) := by rw [hsegeq_list]
    have hentryeq : entry (oper M n) 1
        (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
        = entry (Pred M) 1
          (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) :=
      hagr 1 _ (Or.inr rfl) le_rfl
    obtain ⟨s, b, cs1, cs2⟩ := scx_scb_context_eq_of_prefix (oper M n) (Pred M)
      _ hmkn hMnR hmkP hpredR hjmpos hmlt1 hmlt2 hsegeq hentryeq
    obtain ⟨hps, hpb⟩ := scb_unique_decomp_unconditional (Trans (Pred M))
      s s' _ b b' cs2 dInit
    subst hps; subst hpb
    have hfeq : flatBT (Mark (oper M n)
        (Adm M (parent M 0 (parent M 0 (Lng M - 1))))) = flatBT X := by
      have h1 := cs1.1
      rw [hflatTn] at h1
      exact (List.append_cancel_left (List.append_cancel_right h1)).symm
    rw [← unflatBT_flat (Mark (oper M n)
      (Adm M (parent M 0 (parent M 0 (Lng M - 1))))), hfeq, unflatBT_flat]

/-! ## §4 一歩の surgery — Isabelle `scx_stepA` / `scx_stepB`

Isabelle の `scx_stepA` (:82938) / `scx_stepB` (:83254) は共通の前置き（`N` 束の
折り畳み）を持つ。Lean では `N` 束は §3 の `scx_N_*` が既に個別定理として与えて
いるので、両者の差は「`transC1 N` の形」と「最終の再梱包」だけになる。 -/

/-- Isabelle `addscb_princ_isPTB` / `isPTB_str_Dpt`。 -/
private theorem principal_flat_isPTB_cm1 {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) : isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `s84c2_Trans_c2_decomp`。`Trans (Pred M)` 内の `c₁` の scb 文脈は
`Trans M` では `c₂` の scb 文脈になる（`Trans_Mark_mono_equations`(1) ＋
`replaceScb_spec`）。 -/
private theorem Trans_c1_c2_decomp_cm1 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) :
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

/-- Isabelle `scx_stepA` (pss_wip.thy:82938)。case A（`j₋₁' = j₀'` または
`M_{1,j₀'} + 1 = M_{1,j₀}`）の一歩の surgery: 反復 `n - 1` から `n` へ、
`Mark (M[n]) j₋₁' = D_va(τ +_B c₁·n)` と、その基底 scb 対 `(s',b')` での分解を
同時に進める。

Isabelle との差: `scx_mark_pin` が `Mark` 側を `Trans` 側の分解から完全に決める
ので、Lean では **`dTn` 一本を作れば結論の 2 つ組が出る**（`suffices`）。 -/
theorem scx_stepA (M : PS) (n va : ℕ) (tau c1 : BT) (s' b' : List Sym)
    (hR : RTPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hI : transCondI M = true) (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n)
    (hc1 : c1 = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))))
    (caseA : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
               = parent M 0 (parent M 0 (Lng M - 1))
             ∨ entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) + 1
               = entry M 1 (parent M 0 (Lng M - 1)))
    (vaE : va = entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))
    (tauT : tau ∈ T_B)
    (dInit : scb_decomp (Trans (Pred M)) s'
      (flatBT (Mark (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))) b')
    (mkIH : Mark (oper M (n - 1)) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
      = Dprin (va : ℕ∞) (addBT tau (multBT c1 (n - 1))))
    (dIH : scb_decomp (Trans (oper M (n - 1))) s'
      (flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 (n - 1))))) b') :
    Mark (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
        = Dprin (va : ℕ∞) (addBT tau (multBT c1 n))
      ∧ scb_decomp (Trans (oper M n)) s'
          (flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 n)))) b' := by
  -- `scx_mark_pin` により `Mark` 側は `Trans` 側の分解から決まる
  suffices dTn : scb_decomp (Trans (oper M n)) s'
      (flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 n)))) b' from
    ⟨scx_mark_pin M n _ s' b' hR hmono hj1 hI hj0pos hn dInit dTn, dTn⟩
  obtain ⟨hp0, e1z, hadm, _hle0j0, _hpj0, hnp, hge, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  have hw1 : 1 ≤ Lng M - 1 - parent M 0 (Lng M - 1) := by omega
  -- `N` 束
  have hLngMn := scx_Lng_oper_idx M n hp0 e1z hn1
  have hidxlt : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    rw [hLngMn]; omega
  obtain ⟨hNtake, hLngN⟩ := scx_N_take M n _ hp0 e1z hidxlt
  obtain ⟨hmkIdx, _hnx0, hT1N, _hnVI, hJ0N, hJm1N⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  have hPredN := scx_N_Pred M n hp0 e1z hn
  obtain ⟨hNR, hNmono⟩ := scx_N_RTPS_monoT M n hR hmono hj1 hI hj0pos hn
  have heNidx := scx_N_entry1_idx M n hp0 e1z hn1
  have heNj0' := scx_N_entry_le_j0 M n 1 (parent M 0 (parent M 0 (Lng M - 1)))
    hp0 e1z hn1 (Or.inr rfl) (le_of_lt hj0'lt)
  have hnxN := scx_N_nextR M n hR hmono hj1 hI hj0pos hn
  have hj0ltidx : parent M 0 (Lng M - 1)
      < parent M 0 (Lng M - 1) + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have : 1 * (Lng M - 1 - parent M 0 (Lng M - 1))
        ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  -- `Trans`-記号の折り畳み
  have hJ1N : transJ1 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    simp [transJ1, lastIdx, hLngN]
  have hLNgt : 1 < Lng (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) := by
    rw [hLngN]; omega
  have hC1N : transC1 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = Dprin (va : ℕ∞) (addBT tau (multBT c1 (n - 1))) := by
    rw [transC1, hJm1N, hPredN]; exact mkIH
  have hVN : transV (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = (va : ℕ∞) := by
    rw [transV, hC1N]; rfl
  have hT2N : transT2 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = addBT tau (multBT c1 (n - 1)) := by
    rw [transT2, hC1N]; rfl
  -- 分類: `N` は条件 (I) / (III) / (V) のいずれか
  have hspacn : parent M 0 (parent M 0 (Lng M - 1)) + 1
      < parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by omega
  have hclsA : transCondI (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = true
      ∨ transCondIII (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = true
      ∨ transCondV (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) = true := by
    have hlp : lastParent (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
        = parent M 0 (parent M 0 (Lng M - 1)) := by
      simpa [transJ0] using hJ0N
    have hli : lastIdx (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
        = parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
      simpa [transJ1] using hJ1N
    by_cases hcase : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
        = parent M 0 (parent M 0 (Lng M - 1))
    · -- `j₋₁' = j₀'`: `j₀'` は `M` 許容 ⇒ 接頭辞一致で `N` 許容
      have hadmM : adm M (parent M 0 (parent M 0 (Lng M - 1))) = true := by
        have := Adm_adm M (parent M 0 (parent M 0 (Lng M - 1)))
        rwa [hcase] at this
      have hNT : TPS (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) :=
        RTPS_TPS _ hNR
      have hadmN : adm (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
          (parent M 0 (parent M 0 (Lng M - 1))) = true := by
        have hagree : ∀ i z, z ≤ parent M 0 (Lng M - 1) →
            entry (seg (oper M n) 0
              (parent M 0 (Lng M - 1)
                + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))) i z
              = entry M i z := by
          intro i z hz
          by_cases hi : i = 0 ∨ i = 1
          · exact scx_N_entry_le_j0 M n i z hp0 e1z hn1 hi hz
          · have hi0 : i ≠ 0 := fun h => hi (Or.inl h)
            rw [entry_row_ne_zero_cf1 _ i z hi0, entry_row_ne_zero_cf1 M i z hi0]
            exact scx_N_entry_le_j0 M n 1 z hp0 e1z hn1 (Or.inr rfl) hz
        rw [← adm_prefix_agree_eq_cf1 M (seg (oper M n) 0
            (parent M 0 (Lng M - 1)
              + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
            (parent M 0 (Lng M - 1)) (parent M 0 (parent M 0 (Lng M - 1)))
            hM hNT (fun i z hz => (hagree i z hz).symm) (by omega)
            (by rw [hLngN]; omega) (by omega)]
        exact hadmM
      by_cases hz0 : entry M 1 (parent M 0 (Lng M - 1)) = 0
      · left
        simp only [transCondI, Bool.and_eq_true, beq_iff_eq]
        exact ⟨by rw [hli, heNidx]; exact hz0, by rw [hlp]; exact hadmN⟩
      · have hbnd : entry M 1 (parent M 0 (Lng M - 1))
            ≤ entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) + 1 :=
          scx_row1_bound M _ _ hR hnp
        by_cases hle : entry M 1 (parent M 0 (Lng M - 1))
            ≤ entry M 1 (parent M 0 (parent M 0 (Lng M - 1)))
        · right; left
          simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨by rw [hli, heNidx]; omega, ?_⟩, by rw [hlp]; exact hadmN⟩
          rw [hli, heNidx, hlp, heNj0']; exact hle
        · right; right
          simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq]
          refine ⟨⟨by rw [hli, heNidx]; omega, ?_⟩, ?_⟩
          · rw [hli, heNidx, hlp, heNj0']; omega
          · rw [hli, hlp]; omega
    · -- `j₋₁' < j₀'`: case A の第 2 枝 `M_{1,j₀'} + 1 = M_{1,j₀}`
      have heq : entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) + 1
          = entry M 1 (parent M 0 (Lng M - 1)) := by
        rcases caseA with h | h
        · exact absurd h hcase
        · exact h
      right; right
      simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨by rw [hli, heNidx]; omega, ?_⟩, ?_⟩
      · rw [hli, heNidx, hlp, heNj0']; exact heq
      · rw [hli, hlp]; omega
  -- `c₂` の値
  have hc2NE : transC2 (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
      = Dprin (va : ℕ∞) (addBT (addBT tau (multBT c1 (n - 1)))
          (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) := by
    have hcls : (transCondI (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
        || transCondIII (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))
        || transCondV (seg (oper M n) 0
          (parent M 0 (Lng M - 1)
            + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))) = true := by
      rcases hclsA with h | h | h <;> simp [h]
    rw [transC2, transC2Core]
    simp only [hcls, if_true, hVN, hT2N]
    congr 1
    · rw [transJ1] at hJ1N
      rw [hJ1N, heNidx]
  -- 単項分解の骨格
  have hNRne : Trans (Pred (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))) ≠ BZero := hT1N
  obtain ⟨sN, bN, dPn, dWn⟩ :=
    Trans_c1_c2_decomp_cm1 _ hNR hNmono hLNgt hNRne
  have dPn' : scb_decomp (Trans (oper M (n - 1))) sN
      (flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 (n - 1))))) bN := by
    rw [← hC1N, ← hPredN]; exact dPn
  have hTn1ne : Trans (oper M (n - 1)) ≠ BZero := by rw [← hPredN]; exact hT1N
  obtain ⟨hps, hpb⟩ := scb_unique_decomp_unconditional (Trans (oper M (n - 1)))
    sN s' _ bN b' dPn' dIH
  rw [hps, hpb] at dWn
  have dWnE : scb_decomp (Trans (seg (oper M n) 0
      (parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))) s'
      (flatBT (Dprin (va : ℕ∞) (addBT (addBT tau (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))) b' := by
    rw [← hc2NE]; exact dWn
  -- `T_B` と形の事実
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hmkA : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM (by omega) hp0
  have hc1TB : c1 ∈ T_B := by
    rw [hc1]; exact Mark_mem_T_B (Pred M) _ hpredR hmkA
  have hc1P : ∃ p, c1 = .trm [p] := by
    have := (c1_around_1 M hR hmono hadm hj1 hge).2.2.2.2
    rw [hc1]
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using this
  have hleafTB : Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) BZero_mem_T_B_cf1
  have hleafP : ∃ p, Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero
      = BT.trm [p] := ⟨_, rfl⟩
  have hbodyTB : addBT tau (multBT c1 (n - 1)) ∈ T_B :=
    addBT_mem_T_B tauT (multBT_mem_T_B_cf1 hc1TB _)
  have hiptleaf : isPTB_str (flatBT
      (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) :=
    principal_flat_isPTB_cm1 hleafTB hleafP
  have hiptc1 : isPTB_str (flatBT c1) := principal_flat_isPTB_cm1 hc1TB hc1P
  -- 追加された葉の標準内部位置
  obtain ⟨si, bi, iA0⟩ : ∃ si bi, scb_decomp
      (addBT (addBT tau (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero))
      si (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) bi :=
    add_scb_marked _ _ hbodyTB hleafTB hleafP
  have iA : scb_decomp (Dprin (va : ℕ∞)
      (addBT (addBT tau (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))
      (.dsym (va : ℕ∞) :: si)
      (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) bi :=
    scb_compose_dprin _ _ _ _ _ iA0 hiptleaf
  -- 閉形式の再結合
  have hsnoc : multBT c1 n = addBT (multBT c1 (n - 1)) c1 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rfl
  have hassocX : addBT (addBT tau (multBT c1 (n - 1))) c1
      = addBT tau (multBT c1 n) := by
    rw [hsnoc, addBT_assoc_cf1]
  by_cases hw : Lng M - 1 - parent M 0 (Lng M - 1) = 1
  · -- `w = 1`: `N = M[n]` かつ `c₁` 自身が右端の葉
    have hc1w1v : c1 = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero := by
      rw [hc1]; exact scx_c1_w1 M hR hmono hj1 hI hw
    have hNMn : seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = oper M n := by
      rw [hNtake]
      have hlen2 : (oper M n).length =
          parent M 0 (Lng M - 1) + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
            + (Lng M - 1 - parent M 0 (Lng M - 1)) := hLngMn
      have h2 : parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + 1
          = (oper M n).length := by omega
      rw [h2, List.take_length]
    have hceq : addBT (addBT tau (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)
        = addBT tau (multBT c1 n) := by
      rw [← hc1w1v]; exact hassocX
    rw [hNMn, hceq] at dWnE
    exact dWnE
  · -- `w ≥ 2`: 葉を `c₁` に貼り替えて外側の分解を組み直す
    have hw2 : 1 < Lng M - 1 - parent M 0 (Lng M - 1) := by omega
    have hidxlt1 : parent M 0 (Lng M - 1)
        + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))
        < Lng (oper M n) - 1 := by rw [hLngMn]; omega
    have hMnR : RTPS (oper M n) := RTPS_oper M n hR hn1
    obtain ⟨sb0f, sb0s, TMS1, TMS2⟩ :=
      Trans_Mark_seg_exists (oper M n) _ hmkIdx hMnR (by omega) hidxlt1
    have heMnidx : entry (oper M n) 1
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))
        = entry M 1 (parent M 0 (Lng M - 1)) := by
      rw [← heNidx, hNtake, entry, entry, List.getElem?_take_of_lt (by omega)]
    have dseg : scb_decomp (Trans (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))))) sb0f
        (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) sb0s := by
      rw [← heMnidx]; exact TMS1
    have dCI : scb_decomp (Trans (seg (oper M n) 0
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)))))
        (s' ++ (.dsym (va : ℕ∞) :: si))
        (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero))
        (bi ++ b') :=
      scb_compose_str_cf1 dWnE iA (by simp [Dprin, BZero])
    obtain ⟨hp1, hp2⟩ := scb_unique_decomp_unconditional _ sb0f
      (s' ++ (.dsym (va : ℕ∞) :: si)) _ sb0s (bi ++ b') dseg dCI
    subst hp1; subst hp2
    have hmarkidx : Mark (oper M n)
        (parent M 0 (Lng M - 1)
          + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1))) = c1 := by
      rw [hc1]; exact scx_mark_idx M n hR hmono hj1 hI hj0pos hn hw2
    have dmark' : scb_decomp (Trans (oper M n))
        (s' ++ (.dsym (va : ℕ∞) :: si)) (flatBT c1) (bi ++ b') := by
      rw [← hmarkidx]; exact TMS2
    -- 同じ内部位置で葉を `c₁` に置換
    have iA2_0 : scb_decomp (addBT (addBT tau (multBT c1 (n - 1))) c1) si
        (flatBT c1) bi :=
      add_scb_replace_last _ _ _ _ _ hbodyTB hleafTB hleafP hc1TB hc1P iA0
    have iA2 : scb_decomp (Dprin (va : ℕ∞)
        (addBT (addBT tau (multBT c1 (n - 1))) c1))
        (.dsym (va : ℕ∞) :: si) (flatBT c1) bi :=
      scb_compose_dprin _ _ _ _ _ iA2_0 hiptc1
    -- 外側の分解を組み直す
    have hXnTB : Dprin (va : ℕ∞) (addBT tau (multBT c1 n)) ∈ T_B :=
      Dprin_mem_T_B (by simp) (addBT_mem_T_B tauT (multBT_mem_T_B_cf1 hc1TB _))
    have hiptXn : isPTB_str (flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 n)))) :=
      principal_flat_isPTB_cm1 hXnTB ⟨_, rfl⟩
    have fMn : flatBT (Trans (oper M n))
        = (s' ++ (.dsym (va : ℕ∞) :: si)) ++ flatBT c1 ++ (bi ++ b') := dmark'.1
    have fX2 : flatBT (Dprin (va : ℕ∞) (addBT tau (multBT c1 n)))
        = (.dsym (va : ℕ∞) :: si) ++ flatBT c1 ++ bi := by
      rw [← hassocX]; exact iA2.1
    refine ⟨?_, fun _ => hiptXn, dIH.2.2⟩
    rw [fMn, fX2]
    simp [List.append_assoc]

/-! ### case B の PB 補助 -/

private theorem PB_addBT_app_cm1 (a b : BT) : PB (addBT a b) = PB a ++ PB b := by
  rcases a with ⟨as⟩; rcases b with ⟨bs⟩; simp [PB, addBT, untrm]

private theorem PB_Dprin_single_cm1 (v : ℕ∞) (t : BT) :
    PB (Dprin v t) = [Dprin v t] := by simp [PB, Dprin, untrm]

private theorem SigmaB_PB_cm1 (t : BT) : SigmaB (PB t) = t := by
  rcases t with ⟨ps⟩
  simp only [PB, untrm, SigmaB]
  congr 1
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [untrm, ih]

/-- Isabelle `scx_stepB` (pss_wip.thy:83254)。case B（`j₋₁' < j₀'` かつ
`M_{1,j₀} ≤ M_{1,j₀'}`）の一歩の surgery。`c₁` の 2 段ネスト
`D_va(t₃ +_B D_vb(t₄ +_B c₁·n))` を反復とともに進める。`N` は else 分岐
（`¬(I∨III∨V) ∧ ¬VI ∧ t₂≠0 ∧ leftDj₀`）に落ちるので `transC2Core` の最終分岐で
葉が 2 段下に追加される。 -/
theorem scx_stepB (M : PS) (n va vb : ℕ) (t3 t4 c1 : BT) (s' b' : List Sym)
    (hR : RTPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hI : transCondI M = true) (hj0pos : 0 < parent M 0 (Lng M - 1)) (hn : 2 ≤ n)
    (hc1 : c1 = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))))
    (caseB1 : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
               < parent M 0 (parent M 0 (Lng M - 1)))
    (caseB2 : entry M 1 (parent M 0 (Lng M - 1))
               ≤ entry M 1 (parent M 0 (parent M 0 (Lng M - 1))))
    (vaE : va = entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))
    (vbE : vb = entry M 1 (parent M 0 (parent M 0 (Lng M - 1))))
    (t3T : t3 ∈ T_B) (t4T : t4 ∈ T_B)
    (dInit : scb_decomp (Trans (Pred M)) s'
      (flatBT (Mark (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))) b')
    (mkIH : Mark (oper M (n - 1)) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
      = Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
          (addBT t4 (multBT c1 (n - 1))))))
    (dIH : scb_decomp (Trans (oper M (n - 1))) s'
      (flatBT (Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
        (addBT t4 (multBT c1 (n - 1))))))) b') :
    Mark (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
        = Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 n))))
      ∧ scb_decomp (Trans (oper M n)) s'
          (flatBT (Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
            (addBT t4 (multBT c1 n)))))) b' := by
  suffices dTn : scb_decomp (Trans (oper M n)) s'
      (flatBT (Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
        (addBT t4 (multBT c1 n)))))) b' from
    ⟨scx_mark_pin M n _ s' b' hR hmono hj1 hI hj0pos hn dInit dTn, dTn⟩
  obtain ⟨hp0, e1z, hadm, _hle0j0, _hpj0, hnp, hge, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_, hj0lt, _, _, hL⟩ := kind0_facts_cf1 M hp0 e1z
  have hn1 : 1 ≤ n := by omega
  -- `N` 束
  have hLngMn := scx_Lng_oper_idx M n hp0 e1z hn1
  have hidxlt : parent M 0 (Lng M - 1)
      + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) < Lng (oper M n) := by
    rw [hLngMn]; omega
  obtain ⟨hNtake, hLngN⟩ := scx_N_take M n _ hp0 e1z hidxlt
  obtain ⟨hmkIdx, _hnx0, hT1N, hnVIN, hJ0N, hJm1N⟩ :=
    scx_N_marked_edge M n hR hmono hj1 hI hj0pos hn
  have hPredN := scx_N_Pred M n hp0 e1z hn
  obtain ⟨hNR, hNmono⟩ := scx_N_RTPS_monoT M n hR hmono hj1 hI hj0pos hn
  have heNidx := scx_N_entry1_idx M n hp0 e1z hn1
  have heNj0' := scx_N_entry_le_j0 M n 1 (parent M 0 (parent M 0 (Lng M - 1)))
    hp0 e1z hn1 (Or.inr rfl) (le_of_lt hj0'lt)
  have hj0ltidx : parent M 0 (Lng M - 1)
      < parent M 0 (Lng M - 1) + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) := by
    have : 1 * (Lng M - 1 - parent M 0 (Lng M - 1))
        ≤ (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  -- 略記
  set idx := parent M 0 (Lng M - 1)
    + (n - 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) with hidxdef
  set N := seg (oper M n) 0 idx with hNdef
  set j0' := parent M 0 (parent M 0 (Lng M - 1)) with hj0'def
  -- `Trans`-記号の折り畳み
  have hLNgt : 1 < Lng N := by rw [hLngN]; omega
  have hC1N : transC1 N
      = Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1))))) := by
    rw [transC1, hJm1N, hPredN]; exact mkIH
  have hVN : transV N = (va : ℕ∞) := by rw [transV, hC1N]; rfl
  have hT2N : transT2 N
      = addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1)))) := by
    rw [transT2, hC1N]; rfl
  have hLPN : lastParent N = j0' := hJ0N
  have hLIN : lastIdx N = idx := by simp [lastIdx, hLngN]
  -- else 分岐の分類: `N` は非許容 (parent M 0 j0)
  have hAdmNeq : Adm N j0' = Adm M j0' := by
    have h : Adm N (transJ0 N) = Adm M j0' := hJm1N
    rwa [hJ0N] at h
  have hnadmN : adm N j0' = false := by
    cases hh : adm N j0' with
    | false => rfl
    | true =>
      exfalso
      have hAeq : Adm N j0' = j0' := by simp [Adm, hh]
      rw [hAdmNeq] at hAeq
      omega
  have hentryLI : entry N 1 (lastIdx N) = entry M 1 (parent M 0 (Lng M - 1)) := by
    rw [hLIN]; exact heNidx
  have hentryLP : entry N 1 (lastParent N) = vb := by
    rw [hLPN, heNj0', ← vbE]
  -- 分類 booleans
  have hnI : transCondI N = false := by
    simp only [transCondI, Bool.and_eq_false_iff]; right; rw [hLPN]; exact hnadmN
  have hnIII : transCondIII N = false := by
    simp only [transCondIII, Bool.and_eq_false_iff]; right; rw [hLPN]; exact hnadmN
  have hnV : transCondV N = false := by
    -- 条件 V の中段等式 `M_{1,j₀'}+1 = M_{1,j₀}` は caseB2 と矛盾
    simp only [transCondV, Bool.and_eq_false_iff]
    left; right
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [hentryLP, hentryLI]
    omega
  -- `t₂ ≠ 0`
  have ht2Nne : transT2 N ≠ BZero := by
    rw [hT2N]
    rcases t3 with ⟨as⟩
    simp [addBT, Dprin, BZero]
  -- `c₂` の値（leftDj₀ 分岐）
  have hpt2 : PB (transT2 N)
      = PB t3 ++ [Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1)))] := by
    rw [hT2N, PB_addBT_app_cm1, PB_Dprin_single_cm1]
  have hgetD : (PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero
      = Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1))) := by
    rw [hpt2]
    have hlm : (PB t3 ++ [Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1)))]).length - 1
        = (PB t3).length := by simp
    rw [hlm, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _)]
    simp
  have htake : SigmaB ((PB (transT2 N)).take ((PB (transT2 N)).length - 1)) = t3 := by
    rw [hpt2]
    have hlm : (PB t3 ++ [Dprin (vb : ℕ∞) (addBT t4 (multBT c1 (n - 1)))]).length - 1
        = (PB t3).length := by simp
    rw [hlm, List.take_left]
    exact SigmaB_PB_cm1 t3
  have hbT : bpHeadT ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
      = addBT t4 (multBT c1 (n - 1)) := by
    rw [hgetD]; simp [bpHeadT, Dprin]
  have hleftB : (bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
      == (entry N 1 (lastParent N) : ℕ∞)) = true := by
    rw [hgetD]
    simp only [bpHeadV, Dprin]
    rw [hentryLP]; simp
  have hnA' : ¬((transCondI N || transCondIII N || transCondV N) = true) := by
    rw [hnI, hnIII, hnV]; simp
  have hnVI' : ¬(transCondVI N = true) := by rw [hnVIN]; simp
  have ht₂' : ¬((transT2 N == BZero) = true) := by simpa using ht2Nne
  have hc2NE : transC2 N
      = Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
          (addBT (addBT t4 (multBT c1 (n - 1)))
            (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))) := by
    show transC2Core N (transV N) (transT2 N) = _
    simp only [transC2Core]
    rw [if_neg hnA', if_neg hnVI', if_neg ht₂', if_pos hleftB, if_pos hleftB,
      hbT, hVN, htake, hentryLI, hentryLP]
  -- 単項分解
  have hNRne : Trans (Pred N) ≠ BZero := hT1N
  obtain ⟨sN, bN, dPn, dWn⟩ :=
    Trans_c1_c2_decomp_cm1 _ hNR hNmono hLNgt hNRne
  have dPn' : scb_decomp (Trans (oper M (n - 1))) sN
      (flatBT (Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
        (addBT t4 (multBT c1 (n - 1))))))) bN := by
    rw [← hC1N, ← hPredN]; exact dPn
  have hTn1ne : Trans (oper M (n - 1)) ≠ BZero := by rw [← hPredN]; exact hT1N
  obtain ⟨hps, hpb⟩ := scb_unique_decomp_unconditional (Trans (oper M (n - 1)))
    sN s' _ bN b' dPn' dIH
  rw [hps, hpb] at dWn
  have dWnE : scb_decomp (Trans N) s'
      (flatBT (Dprin (va : ℕ∞) (addBT t3 (Dprin (vb : ℕ∞)
          (addBT (addBT t4 (multBT c1 (n - 1)))
            (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))))) b' := by
    rw [← hc2NE]; exact dWn
  -- `T_B`・形の事実
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hmkA : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM (by omega) hp0
  have hc1TB : c1 ∈ T_B := by rw [hc1]; exact Mark_mem_T_B (Pred M) _ hpredR hmkA
  have hc1P : ∃ p, c1 = .trm [p] := by
    have := (c1_around_1 M hR hmono hadm hj1 hge).2.2.2.2
    rw [hc1]
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using this
  have hleafTB : Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) BZero_mem_T_B_cf1
  have hleafP : ∃ p, Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero
      = BT.trm [p] := ⟨_, rfl⟩
  have hbody4TB : addBT t4 (multBT c1 (n - 1)) ∈ T_B :=
    addBT_mem_T_B t4T (multBT_mem_T_B_cf1 hc1TB _)
  have hiptleaf : isPTB_str (flatBT
      (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) :=
    principal_flat_isPTB_cm1 hleafTB hleafP
  have hiptc1 : isPTB_str (flatBT c1) := principal_flat_isPTB_cm1 hc1TB hc1P
  -- 内側 2 段の scb 位置（葉版）
  obtain ⟨si, bi, iI0⟩ : ∃ si bi, scb_decomp
      (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero))
      si (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) bi :=
    add_scb_marked _ _ hbody4TB hleafTB hleafP
  have iI : scb_decomp (Dprin (vb : ℕ∞)
      (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))
      (.dsym (vb : ℕ∞) :: si)
      (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) bi :=
    scb_compose_dprin _ _ _ _ _ iI0 hiptleaf
  have hmidTB : Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
      (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) ∈ T_B :=
    Dprin_mem_T_B (by simp) (addBT_mem_T_B hbody4TB hleafTB)
  have hmidP : ∃ p, Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
      (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) = .trm [p] := ⟨_, rfl⟩
  obtain ⟨so, bo, iO0⟩ : ∃ so bo, scb_decomp
      (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero))))
      so (flatBT (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))) bo :=
    add_scb_marked _ _ t3T hmidTB hmidP
  have hiptmid : isPTB_str (flatBT (Dprin (vb : ℕ∞)
      (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))) :=
    principal_flat_isPTB_cm1 hmidTB hmidP
  have iO : scb_decomp (Dprin (va : ℕ∞)
      (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))))
      (.dsym (va : ℕ∞) :: so)
      (flatBT (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))) bo :=
    scb_compose_dprin _ _ _ _ _ iO0 hiptmid
  have iComp : scb_decomp (Dprin (va : ℕ∞)
      (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)))))
      ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si))
      (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) (bi ++ bo) :=
    scb_compose_str_cf1 iO iI (by simp [Dprin, BZero])
  -- 閉形式の再結合
  have hsnoc : multBT c1 n = addBT (multBT c1 (n - 1)) c1 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rfl
  have hassocX : addBT (addBT t4 (multBT c1 (n - 1))) c1 = addBT t4 (multBT c1 n) := by
    rw [hsnoc, addBT_assoc_cf1]
  by_cases hw : Lng M - 1 - parent M 0 (Lng M - 1) = 1
  · -- `w = 1`: `N = M[n]`、`c₁` 自身が右端葉
    have hc1w1v : c1 = Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero := by
      rw [hc1]; exact scx_c1_w1 M hR hmono hj1 hI hw
    have hNMn : N = oper M n := by
      rw [hNtake]
      have hlen2 : (oper M n).length
          = idx + (Lng M - 1 - parent M 0 (Lng M - 1)) := hLngMn
      have h2 : idx + 1 = (oper M n).length := by omega
      rw [h2, List.take_length]
    have hceq : addBT (addBT t4 (multBT c1 (n - 1)))
        (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)
        = addBT t4 (multBT c1 n) := by
      rw [← hc1w1v]; exact hassocX
    rw [hNMn, hceq] at dWnE
    exact dWnE
  · -- `w ≥ 2`: 2 段の葉を `c₁` に貼り替える
    have hw2 : 1 < Lng M - 1 - parent M 0 (Lng M - 1) := by omega
    have hidxlt1 : idx < Lng (oper M n) - 1 := by rw [hidxdef, hLngMn]; omega
    have hMnR : RTPS (oper M n) := RTPS_oper M n hR hn1
    obtain ⟨sb0f, sb0s, TMS1, TMS2⟩ :=
      Trans_Mark_seg_exists (oper M n) idx hmkIdx hMnR (by rw [hidxdef]; omega) hidxlt1
    have heMnidx : entry (oper M n) 1 idx
        = entry M 1 (parent M 0 (Lng M - 1)) := by
      rw [← heNidx, hNtake]
      simp only [entry]
      rw [List.getElem?_take_of_lt (show idx < idx + 1 by omega)]
    have dseg : scb_decomp (Trans N) sb0f
        (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero)) sb0s := by
      rw [hNdef, ← heMnidx]; exact TMS1
    have dCI : scb_decomp (Trans N)
        (s' ++ ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si)))
        (flatBT (Dprin (entry M 1 (parent M 0 (Lng M - 1)) : ℕ∞) BZero))
        ((bi ++ bo) ++ b') :=
      scb_compose_str_cf1 dWnE iComp (by simp [Dprin, BZero])
    obtain ⟨hp1, hp2⟩ := scb_unique_decomp_unconditional (Trans N) sb0f
      (s' ++ ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si))) _
      sb0s ((bi ++ bo) ++ b') dseg dCI
    subst hp1; subst hp2
    have hmarkidx : Mark (oper M n) idx = c1 := by
      rw [hc1, hidxdef]; exact scx_mark_idx M n hR hmono hj1 hI hj0pos hn hw2
    have dmark' : scb_decomp (Trans (oper M n))
        (s' ++ ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si)))
        (flatBT c1) ((bi ++ bo) ++ b') := by
      rw [← hmarkidx]; exact TMS2
    -- 葉を `c₁` に置換（2 段）
    have iI2_0 : scb_decomp (addBT (addBT t4 (multBT c1 (n - 1))) c1) si
        (flatBT c1) bi :=
      add_scb_replace_last _ _ _ _ _ hbody4TB hleafTB hleafP hc1TB hc1P iI0
    have iI2 : scb_decomp (Dprin (vb : ℕ∞)
        (addBT (addBT t4 (multBT c1 (n - 1))) c1))
        (.dsym (vb : ℕ∞) :: si) (flatBT c1) bi :=
      scb_compose_dprin _ _ _ _ _ iI2_0 hiptc1
    have hmid2TB : Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1) ∈ T_B :=
      Dprin_mem_T_B (by simp) (addBT_mem_T_B hbody4TB hc1TB)
    have hmid2P : ∃ p, Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1)
        = .trm [p] := ⟨_, rfl⟩
    have iO2_0 : scb_decomp
        (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1)))
        so (flatBT (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1))) bo :=
      add_scb_replace_last _ _ _ _ _ t3T hmidTB hmidP hmid2TB hmid2P iO0
    have hiptmid2 : isPTB_str (flatBT (Dprin (vb : ℕ∞)
        (addBT (addBT t4 (multBT c1 (n - 1))) c1))) :=
      principal_flat_isPTB_cm1 hmid2TB hmid2P
    have iO2 : scb_decomp (Dprin (va : ℕ∞)
        (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1))))
        (.dsym (va : ℕ∞) :: so)
        (flatBT (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1))) bo :=
      scb_compose_dprin _ _ _ _ _ iO2_0 hiptmid2
    have iComp2 : scb_decomp (Dprin (va : ℕ∞)
        (addBT t3 (Dprin (vb : ℕ∞) (addBT (addBT t4 (multBT c1 (n - 1))) c1))))
        ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si))
        (flatBT c1) (bi ++ bo) :=
      scb_compose_str_cf1 iO2 iI2 (by simp [Dprin, BZero])
    -- 外側を組み直す
    have hXnTB : Dprin (va : ℕ∞)
        (addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 n)))) ∈ T_B :=
      Dprin_mem_T_B (by simp) (addBT_mem_T_B t3T (Dprin_mem_T_B (by simp)
        (addBT_mem_T_B t4T (multBT_mem_T_B_cf1 hc1TB _))))
    have hiptXn : isPTB_str (flatBT (Dprin (va : ℕ∞)
        (addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 n)))))) :=
      principal_flat_isPTB_cm1 hXnTB ⟨_, rfl⟩
    have fMn : flatBT (Trans (oper M n))
        = (s' ++ ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si)))
          ++ flatBT c1 ++ ((bi ++ bo) ++ b') := dmark'.1
    have fX2 : flatBT (Dprin (va : ℕ∞)
        (addBT t3 (Dprin (vb : ℕ∞) (addBT t4 (multBT c1 n)))))
        = ((.dsym (va : ℕ∞) :: so) ++ (.dsym (vb : ℕ∞) :: si)) ++ flatBT c1
          ++ (bi ++ bo) := by
      rw [show addBT t4 (multBT c1 n)
          = addBT (addBT t4 (multBT c1 (n - 1))) c1 from hassocX.symm]
      exact iComp2.1
    refine ⟨?_, fun _ => hiptXn, dIH.2.2⟩
    rw [fMn, fX2]
    simp [List.append_assoc]

/-! ## 公開定理の axioms 監査 -/

#print axioms scx_take_RTPS
#print axioms scx_seg0_eq_take
#print axioms scx_seg0_RTPS
#print axioms scx_map_block_seg
#print axioms scx_le0_to_parent
#print axioms scx_row1_bound
#print axioms scx_host_basic
#print axioms scx_Lng_oper
#print axioms scx_Lng_oper_idx
#print axioms scx_N_take
#print axioms scx_N_Pred
#print axioms scx_N_marked_edge
#print axioms scx_le0_oper_idx
#print axioms scx_N_RTPS_monoT
#print axioms scx_N_entry_le_j0
#print axioms scx_N_entry1_idx
#print axioms scx_N_tail_seg
#print axioms scx_N_nextR
#print axioms scx_mark_idx
#print axioms scx_c1_w1
#print axioms scx_marked_jm1p
#print axioms scx_scb_context_eq_of_prefix
#print axioms scx_mark_pin
#print axioms scx_stepA
#print axioms scx_stepB

end PSS
