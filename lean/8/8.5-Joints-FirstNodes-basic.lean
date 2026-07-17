import «5».«5.1-ancestor-basic»
import «5».«5.1-parent-exists»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.2-P-fseq»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-mono-slice»
import «6».«6.4-mono-slice-next»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-monoT-Red»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-leftend»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.7-standard-reduced»
import «7».«7.4-Adm-nextAdm»
import «7».«7.4-Mark-Trans-repr»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-subexpr-adm0-ctx»

/-!
# §8.5 補題（条件(V)の下での `Joints` と `FirstNodes` と `t₂` の基本性質）

- 原文: `tmp/content.md` 5165（補題本体 5165–5171、証明 5173–5209）
- 訂正: **なし**。MISSION は訂正 A29 の適用を指示するが、A29 (`corrections.md` 889)
  の対象は**隣の補題**「条件(V)の下での各種scb分解」(`tmp/content.md` 5213) の
  clause (5)（`Trans(M[n])` の指数が `n = 1` で偽）であって、本補題ではない。
  本補題に clause (5) は存在せず（(1)(2)(3) のみ）、A29 の記述する
  `Trans(M[n]) = s₁ D … t₂ (b'₁)ⁿ b₁` の主張は本補題に現れない。よって
  原文の反例定理（`_original_false`）も本ファイルには存在しない。
- 転記範囲: 原文 (1) と (2)。原文 (3)（`t₂` の各単項成分は `D_{M₁,j₁} 0` 以上）は
  `Trans` の再帰的定義内部の未公開記号 `t₂` を参照するため `pss_paper.thy` でも
  DEFERRED 扱い（BLOCKING SYMBOL: `t₂`）。本ファイルは faithful transcription
  `p_8_5_Joints_FirstNodes_basic` (isabelle/pss_paper.thy:2098) の shows 4 本
  （= 原文 (1) の 3 つの主張と (2)）をそのまま述べる。
- Isabelle: `p_8_5_Joints_FirstNodes_basic` (isabelle/pss_paper.thy:2098) の証明は
  `m_8_5_Joints_FirstNodes_basic` (isabelle/layerB/pss_wip.thy:40416, 約 212 行)。
  もう一方の blueprint `m_8_5_Joints_FirstNodes_basic_condV`
  (isabelle/layerB/pss_wip.thy:60636) は**同じ結論**を、`nextR M 1 j₀ j₁` と
  `j₀ < j₁-1` を `transCondV M` から導いて仮定を減らした**言い換え**であり
  （`e1x_condV_nextR1` / `s85b_condV_bridge` 経由で 40416 版へ帰着するだけ）、
  原文の仮定は `(1,j₀) <^Next (1,j₁)` かつ `j₀ < j₁-1` の形なので、
  **paper 文と一致する 40416 版を移植**した。
  内部で使う Isabelle 補助補題と Lean 対応:
  - `m_6_7_ST_PS_subseteq_RT_PS` → `STPS_RTPS`
  - `monoT_hasParent0_last` → `mono_hasParent_row0`
  - `poper_nextR_imp_le0` → `nextR0_leR` / `nextR_parent0_of_hasParent`
  - `nadm_Adm_lt` → private `nadm_Adm_lt_jfb`（Isabelle 名を保持）
  - `adm_row1_ancestry` → `adm_row1_ancestry`、`m_le1_imp_le0` → `row1_implies_row0`
  - `le0_trans` → private `le0_trans_jfb`（**値特徴付け**で構成、下記）
  - `slice_Red_in_RT_PS` → `standard_slice_Red_strongmono` + `DTPS_iff`
  - `m_6_5_Lng_Red` → `Lng_Red_invariance`
  - `m_6_6_ancestor_slice_Red_IncrFirst` → `ancestor_slice_Red_IncrFirst`
  - `nextR_funpow_IncrFirst_eq` → `nextR_IncrFirstN_ri`、`rcpb_nextR_seg` → `nextR_seg_adm`
  - `repr_transJ0_shift` / `repr_transJm1_shift`
    → `transJ0_Red_terminal_slice` / `transJm1_Red_terminal_slice`
  - `m_8_2_parent_le_TrMax_Adm0` / `m_8_2_j1eq_Adm0` / `m_8_2_j0eq_Adm0`
    → `parent_le_TrMax_Adm0` / `j1eq_Adm0` / `j0eq_Adm0`
  - `m_6_6_reduced_iff_cond` → `RTPS_condAB`（無条件）
  - Isabelle の `RedCondB` + `¬hasParent RN 0 0` による `e00` は、Lean では
    `RTPS_mono_head_eq`（`RTPS` + `monoT` から `entry M 0 0 = entry M 1 0`）で直接得る
  - `trunk_entries_offset` → `trunk_entries_offset`、`nextR1_unique` → `nextR1_unique_mr`
  - `idxsum_parent0_unique` → `parent_eq_of_nextR0`（行 0 の親の一意性）
- 依存: `8.2-subexpr-adm0-ctx`（Adm0 族 = 最終枝の同定）、
  `8.2-standard-slice-Red-strongmono`（切片の `Red` の強単項性）、
  `7.4-Mark-Trans-repr`（`transJ0`/`transJm1` の切片シフト）、
  `6.6-ancestor-slice-Red-IncrFirst`（`seg = IncrFirstN k (Red seg)` 読み出し）、
  `6.6-reduced-iff-condAB` / `6.6-reduced-leftend`（`RedCondA`/`head_eq`）、
  `6.5-Red-le-core`（`trunk_entries_offset`/`RedCondA_apply`）、
  `5.1-parent-exists` + `5.1-ancestor-basic`（`le0` の値特徴付け）
- 状態: ✅ 証明済（sorry 0）

証明の骨格（Isabelle 40416 版そのまま）: `mm1 := Adm_M(j₀)`, `N := (M_j)_{j=mm1}^{j₁}`,
`RN := Red N` と置く。`RN` は強単項（`standard_slice_Red_strongmono`）なので
`RTPS`＋`monoT`。切片シフトで `transJ0 RN = j₀-mm1`, `transJm1 RN = 0` なので
**§8.2 の Adm0 族が発火**し、最終枝が `FirstNodes RN ! J₁ = Lng RN - 1 = j₁-mm1`,
`Joints RN ! J₁ = transJ0 RN = j₀-mm1` と同定される（= (1)）。`Br RN ≠ []` は、
空なら `TrMax RN = Lng RN - 1` となり幹ステップが `nextR M 1 (j₁-1) j₁` を与えて
行 1 の親の一意性（親は `j₀ ≠ j₁-1`）に矛盾、で示す。(2) は幹上の係数オフセット
`trunk_entries_offset` と `entry RN 0 0 = entry RN 1 0` から `j₀-mm1` での上下一致を得、
`RedCondA` の `+1` ステップを行 0・行 1 の両方で最終列へ持ち上げる。

**`le0` の推移律は `ancestor_basic_1`（`le0` → 行 0 の値の狭義増加）＋
`parent_exists_3`（値 → `le0`）の値特徴付けで構成**し、Isabelle の `rtrancl`
分解を使わない（本 repo の定石）。
-/

namespace PSS

/-! ## 補助（Isabelle 名を保持した private 補題） -/

/-- Isabelle `le0_trans` の値特徴付けによる構成。`a <^0 b` かつ `b <^0 c` なら
`a <^0 c`。`ancestor_basic_1`（`le0` → 値の狭義増加）で `(a,b]` と `(b,c]` の
両区間の増加を取り出し、`parent_exists_3`（値 → `le0`）で貼り合わせる。 -/
private theorem le0_trans_jfb (M : PS) (a b c : ℕ) (hM : TPS M)
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

/-- Isabelle `nadm_Adm_lt`。`j` が非 `M` 許容なら `Adm_M(j) < j`。 -/
private theorem nadm_Adm_lt_jfb (M : PS) (j : ℕ) (hna : adm M j = false) :
    Adm M j < j := by
  have hle : Adm M j ≤ j := Adm_le M j
  have hadm : adm M (Adm M j) = true := Adm_adm M j
  rcases Nat.lt_or_ge (Adm M j) j with h | h
  · exact h
  · exfalso
    have heq : Adm M j = j := by omega
    rw [heq, hna] at hadm
    exact Bool.noConfusion hadm

/-- Isabelle `nextR1_unique` による行 1 の `hasParent` 構成。 -/
private theorem hasParent1_of_nextR_jfb (M : PS) (p k : ℕ)
    (hp : nextR M 1 p k = true) : hasParent M 1 k = true := by
  refine (hasParent_iff_unique_fseq M 1 k).mpr ⟨p, hp, ?_⟩
  intro q hq
  exact nextR1_unique_mr M q p k hq hp

/-- 行 1 の親の値。 -/
private theorem parent1_eq_of_nextR_jfb (M : PS) (p k : ℕ)
    (hp : nextR M 1 p k = true) : parent M 1 k = p := by
  have hh := hasParent1_of_nextR_jfb M p k hp
  have hlen : (parents M 1 k).length = 1 := by simpa [hasParent] using hh
  obtain ⟨s, hs⟩ := List.length_eq_one_iff.mp hlen
  have hsmem : s ∈ parents M 1 k := by rw [hs]; simp
  have hsnext : nextR M 1 s k = true := by
    have hm := hsmem
    simp only [parents, List.mem_filter, List.mem_range] at hm
    exact hm.2
  have hsp : s = p := nextR1_unique_mr M s p k hsnext hp
  rw [parent, hs]
  simpa using hsp

/-- 行 0 の `hasParent` 構成（`parent_eq_of_nextR0` による一意性）。 -/
private theorem hasParent0_of_nextR_jfb (M : PS) (p k : ℕ)
    (hp : nextR M 0 p k = true) : hasParent M 0 k = true := by
  refine (hasParent_iff_unique_fseq M 0 k).mpr ⟨p, hp, ?_⟩
  intro q hq
  have h1 : parent M 0 k = q := parent_eq_of_nextR0 M q k hq
  have h2 : parent M 0 k = p := parent_eq_of_nextR0 M p k hp
  omega

/-! ## 本体（`j₀`/`j₁`/`mm1` を変数化した core） -/

/-- `p_8_5_Joints_FirstNodes_basic` の core。`j₁`/`j₀` は Isabelle の `defines`、
`mm1 = Adm_M(j₀)` は結論に現れる略記であり、公開版ではすべて展開される。 -/
private theorem Joints_FirstNodes_basic_core_jfb (M : PS) (j₀ j₁ mm1 : ℕ)
    (hST : STPS M) (hmono : monoT M = true)
    (hj₁ : j₁ = Lng M - 1)
    (hj₀ : j₀ = parent M 0 (Lng M - 1))
    (hmm1 : mm1 = Adm M j₀)
    (hnx1 : nextR M 1 j₀ j₁ = true)
    (hnadm : adm M j₀ = false)
    (hgap : j₀ < j₁ - 1) :
    1 ≤ (Br (Red (seg M mm1 j₁))).length
      ∧ j₀ - mm1
          = (Joints (Red (seg M mm1 j₁))).getD
              ((Br (Red (seg M mm1 j₁))).length - 1) 0
      ∧ (FirstNodes (Red (seg M mm1 j₁))).getD
              ((Br (Red (seg M mm1 j₁))).length - 1) 0
          = j₁ - mm1
      ∧ entry (Red (seg M mm1 j₁)) 0 (j₁ - mm1)
          = entry (Red (seg M mm1 j₁)) 1 (j₁ - mm1) := by
  -- 基本的な所属
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  -- 長さの評価
  have hL1 : 1 < Lng M := by omega
  have hj₁L : j₁ < Lng M := by omega
  have hj₁le : j₁ ≤ Lng M - 1 := by omega
  -- `j₀` は最終列の行 0 の親
  have hp0M : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hparj0 : nextR M 0 j₀ j₁ = true := by
    rw [hj₀, hj₁]; exact nextR_parent0_of_hasParent M (Lng M - 1) hp0M
  have hlej0j1 : leR M 0 j₀ j₁ = true := nextR0_leR M j₀ j₁ hparj0
  have hj0ltj1 : j₀ < j₁ := by omega
  -- `mm1 = Adm_M(j₀) < j₀`
  have hmm1ltj0 : mm1 < j₀ := by rw [hmm1]; exact nadm_Adm_lt_jfb M j₀ hnadm
  have hadmmm1 : adm M mm1 = true := by rw [hmm1]; exact Adm_adm M j₀
  have hmm1ltj1 : mm1 < j₁ := by omega
  have hmm1lej1 : mm1 ≤ j₁ := by omega
  -- `mm1 <^1 j₀` から `mm1 <^0 j₀`、そして推移律で `mm1 <^0 j₁`
  have hle1a : leR M 1 mm1 j₀ = true := by
    rw [hmm1]; exact adm_row1_ancestry M j₀ hMT (by omega)
  have hle0a : leR M 0 mm1 j₀ = true := row1_implies_row0 M mm1 j₀ hMT hle1a
  have hleM : leR M 0 mm1 j₁ = true :=
    le0_trans_jfb M mm1 j₀ j₁ hMT hle0a hlej0j1 hmm1ltj0 hj0ltj1 hj₁L
  have hleM2 : leR M 0 mm1 (Lng M - 1) = true := by rw [← hj₁]; exact hleM
  have hmarked : Marked M mm1 := ⟨hMT, hadmmm1, hleM2⟩
  -- 切片シフト補題の前提
  have hmint : mm1 < Lng M - 2 := by omega
  have hanc0 : mm1 ≤ parent M 0 (Lng M - 1) := by omega
  -- `RN := Red N` の所属
  have hND : DTPS (Red (seg M mm1 j₁)) :=
    standard_slice_Red_strongmono M mm1 j₁ hST hmm1ltj1 hj₁le hleM
  have hNR : RTPS (Red (seg M mm1 j₁)) := ((DTPS_iff _).mp hND).1
  have hmonoRN : monoT (Red (seg M mm1 j₁)) = true := ((DTPS_iff _).mp hND).2.1
  have hNT : TPS (Red (seg M mm1 j₁)) := RTPS_TPS _ hNR
  -- 長さ
  have hsegT : TPS (seg M mm1 j₁) := by
    have : Lng (seg M mm1 j₁) = j₁ + 1 - mm1 := length_seg M mm1 j₁
    intro hc
    rw [hc] at this
    simp [Lng] at this
    omega
  have hLRN : Lng (Red (seg M mm1 j₁)) = Lng (seg M mm1 j₁) :=
    Lng_Red_invariance (seg M mm1 j₁) hsegT
  have hLNval : Lng (seg M mm1 j₁) = j₁ + 1 - mm1 := length_seg M mm1 j₁
  have hLRNm1 : Lng (Red (seg M mm1 j₁)) - 1 = j₁ - mm1 := by
    rw [hLRN, hLNval]; omega
  -- `seg = IncrFirstN k (Red seg)` 読み出し
  have hfacts := ancestor_slice_Red_IncrFirst M mm1 j₁ hMR hmm1ltj1 hj₁le hleM
  have hsegeq : seg M mm1 j₁
      = IncrFirstN (entry M 0 mm1 - entry M 1 mm1) (Red (seg M mm1 j₁)) := hfacts.2.2
  -- `nextR` のブリッジ
  have hbridge : ∀ i p q : ℕ, p < Lng (seg M mm1 j₁) → q < Lng (seg M mm1 j₁) →
      nextR (Red (seg M mm1 j₁)) i p q = nextR M i (mm1 + p) (mm1 + q) := by
    intro i p q hp hq
    have h1 : nextR (seg M mm1 j₁) i p q = nextR (Red (seg M mm1 j₁)) i p q := by
      conv_lhs => rw [hsegeq]
      rw [nextR_IncrFirstN_ri]
    rw [← h1]
    exact nextR_seg_adm M mm1 j₁ i p q hmm1lej1 hj₁L hp hq
  -- 切片シフト: `transJ0 RN = j₀ - mm1`, `transJm1 RN = 0`
  have hRNexp : Red (seg M mm1 j₁) = Red (seg M mm1 (Lng M - 1)) := by rw [hj₁]
  have htj0RN : transJ0 (Red (seg M mm1 j₁)) = j₀ - mm1 := by
    rw [hRNexp, transJ0_Red_terminal_slice M mm1 hMR hmint hleM2 hp0M hanc0]
    simp [transJ0, lastParent, lastIdx, ← hj₀]
  have hAdm0RN : transJm1 (Red (seg M mm1 j₁)) = 0 := by
    rw [hRNexp, transJm1_Red_terminal_slice M mm1 hmarked hMR hmint hleM2 hp0M hanc0]
    have : transJm1 M = mm1 := by
      simp [transJm1, transJ0, lastParent, lastIdx, ← hj₀, ← hmm1]
    omega
  have hparRNlast : parent (Red (seg M mm1 j₁)) 0 (Lng (Red (seg M mm1 j₁)) - 1)
      = j₀ - mm1 := by
    have := htj0RN
    simpa [transJ0, lastParent, lastIdx] using this
  -- (Y) `j₀ - mm1 ≤ TrMax RN`
  have hjpTr : j₀ - mm1 ≤ TrMax (Red (seg M mm1 j₁)) := by
    have := parent_le_TrMax_Adm0 (Red (seg M mm1 j₁)) hNR hmonoRN hAdm0RN
    rwa [hparRNlast] at this
  have hjppos : 0 < j₀ - mm1 := by omega
  -- `RN` 上の行 0 / 行 1 の親辺（ブリッジ経由）
  have hplt0 : j₀ - mm1 < Lng (seg M mm1 j₁) := by rw [hLNval]; omega
  have hqlt : j₁ - mm1 < Lng (seg M mm1 j₁) := by rw [hLNval]; omega
  have hB0 : nextR (Red (seg M mm1 j₁)) 0 (j₀ - mm1) (j₁ - mm1) = true := by
    rw [hbridge 0 (j₀ - mm1) (j₁ - mm1) hplt0 hqlt]
    have e0 : mm1 + (j₀ - mm1) = j₀ := by omega
    have e1 : mm1 + (j₁ - mm1) = j₁ := by omega
    rw [e0, e1]; exact hparj0
  have hB1 : nextR (Red (seg M mm1 j₁)) 1 (j₀ - mm1) (j₁ - mm1) = true := by
    rw [hbridge 1 (j₀ - mm1) (j₁ - mm1) hplt0 hqlt]
    have e0 : mm1 + (j₀ - mm1) = j₀ := by omega
    have e1 : mm1 + (j₁ - mm1) = j₁ := by omega
    rw [e0, e1]; exact hnx1
  -- `¬ nextR M 1 (j₁-1) j₁`（行 1 の親は一意で `j₀ ≠ j₁-1`）
  have hnotnext : nextR M 1 (j₁ - 1) j₁ ≠ true := by
    intro hc
    have : j₁ - 1 = j₀ := nextR1_unique_mr M (j₁ - 1) j₀ j₁ hc hnx1
    omega
  -- (1a) `Br RN ≠ []`
  have hj1gtRN : 1 < Lng (Red (seg M mm1 j₁)) - 1 := by rw [hLRNm1]; omega
  have hBrne : Br (Red (seg M mm1 j₁)) ≠ [] := by
    intro hBemp
    have htrmaxeq : TrMax (Red (seg M mm1 j₁)) = Lng (Red (seg M mm1 j₁)) - 1 := by
      by_contra hne
      have : Br (Red (seg M mm1 j₁))
          = P (seg (Red (seg M mm1 j₁)) (TrMax (Red (seg M mm1 j₁)) + 1)
                (Lng (Red (seg M mm1 j₁)) - 1)) := by
        simp [Br, hne]
      rw [hBemp] at this
      exact P_nonempty _ this.symm
    have hstep : nextR (Red (seg M mm1 j₁)) 1
        (Lng (Red (seg M mm1 j₁)) - 2) (Lng (Red (seg M mm1 j₁)) - 1) = true := by
      have h := TrMax_trunk_step (Red (seg M mm1 j₁))
        (Lng (Red (seg M mm1 j₁)) - 2) hNT (by omega)
      have e : Lng (Red (seg M mm1 j₁)) - 2 + 1 = Lng (Red (seg M mm1 j₁)) - 1 := by
        omega
      rwa [e] at h
    have hp2 : Lng (Red (seg M mm1 j₁)) - 2 < Lng (seg M mm1 j₁) := by
      rw [← hLRN]; omega
    have hq2 : Lng (Red (seg M mm1 j₁)) - 1 < Lng (seg M mm1 j₁) := by
      rw [← hLRN]; omega
    rw [hbridge 1 _ _ hp2 hq2] at hstep
    have ep : mm1 + (Lng (Red (seg M mm1 j₁)) - 2) = j₁ - 1 := by
      have := hLRNm1; omega
    have eq' : mm1 + (Lng (Red (seg M mm1 j₁)) - 1) = j₁ := by
      have := hLRNm1; omega
    rw [ep, eq'] at hstep
    exact hnotnext hstep
  -- (1) の 3 本
  have hG1 : 1 ≤ (Br (Red (seg M mm1 j₁))).length := by
    cases hb : Br (Red (seg M mm1 j₁)) with
    | nil => exact absurd hb hBrne
    | cons a l => simp
  have hG3 : (FirstNodes (Red (seg M mm1 j₁))).getD
      ((Br (Red (seg M mm1 j₁))).length - 1) 0 = j₁ - mm1 := by
    have := j1eq_Adm0 (Red (seg M mm1 j₁)) hNR hmonoRN hBrne hj1gtRN hAdm0RN
    rw [this, hLRNm1]
  have hG2 : j₀ - mm1 = (Joints (Red (seg M mm1 j₁))).getD
      ((Br (Red (seg M mm1 j₁))).length - 1) 0 := by
    have := j0eq_Adm0 (Red (seg M mm1 j₁)) hNR hmonoRN hBrne hj1gtRN hAdm0RN
    rw [this, htj0RN]
  -- (2) 幹上の一致を `RedCondA` で最終列へ持ち上げる
  have hcondA : RedCondA (Red (seg M mm1 j₁)) = true := (RTPS_condAB _ hNR).1
  have he00 : entry (Red (seg M mm1 j₁)) 0 0 = entry (Red (seg M mm1 j₁)) 1 0 :=
    RTPS_mono_head_eq _ hNR hmonoRN
  have hoff := trunk_entries_offset (Red (seg M mm1 j₁)) hNT hcondA (j₀ - mm1) hjpTr
  have hcoincide : entry (Red (seg M mm1 j₁)) 0 (j₀ - mm1)
      = entry (Red (seg M mm1 j₁)) 1 (j₀ - mm1) := by
    rw [hoff.1, hoff.2, he00]
  have hB0' : nextR (Red (seg M mm1 j₁)) 0 (j₀ - mm1)
      (Lng (Red (seg M mm1 j₁)) - 1) = true := by rw [hLRNm1]; exact hB0
  have hB1' : nextR (Red (seg M mm1 j₁)) 1 (j₀ - mm1)
      (Lng (Red (seg M mm1 j₁)) - 1) = true := by rw [hLRNm1]; exact hB1
  have hp0RN : hasParent (Red (seg M mm1 j₁)) 0 (Lng (Red (seg M mm1 j₁)) - 1) = true :=
    hasParent0_of_nextR_jfb _ (j₀ - mm1) _ hB0'
  have hp1RN : hasParent (Red (seg M mm1 j₁)) 1 (Lng (Red (seg M mm1 j₁)) - 1) = true :=
    hasParent1_of_nextR_jfb _ (j₀ - mm1) _ hB1'
  have hpar1RN : parent (Red (seg M mm1 j₁)) 1 (Lng (Red (seg M mm1 j₁)) - 1)
      = j₀ - mm1 := parent1_eq_of_nextR_jfb _ (j₀ - mm1) _ hB1'
  have hRNpos : 0 < Lng (Red (seg M mm1 j₁)) := by omega
  have hrcA0 : entry (Red (seg M mm1 j₁)) 0 (j₀ - mm1) + 1
      = entry (Red (seg M mm1 j₁)) 0 (Lng (Red (seg M mm1 j₁)) - 1) := by
    have h := RedCondA_apply (Red (seg M mm1 j₁)) hcondA 0
      (Lng (Red (seg M mm1 j₁)) - 1) (by omega) (by omega) hp0RN
    rwa [hparRNlast] at h
  have hrcA1 : entry (Red (seg M mm1 j₁)) 1 (j₀ - mm1) + 1
      = entry (Red (seg M mm1 j₁)) 1 (Lng (Red (seg M mm1 j₁)) - 1) := by
    have h := RedCondA_apply (Red (seg M mm1 j₁)) hcondA 1
      (Lng (Red (seg M mm1 j₁)) - 1) (by omega) (by omega) hp1RN
    rwa [hpar1RN] at h
  have hG4 : entry (Red (seg M mm1 j₁)) 0 (j₁ - mm1)
      = entry (Red (seg M mm1 j₁)) 1 (j₁ - mm1) := by
    rw [← hLRNm1, ← hrcA0, ← hrcA1, hcoincide]
  exact ⟨hG1, hG2, hG3, hG4⟩

/-! ## 公開定理 -/

/-- **§8.5 補題（条件(V)の下での `Joints` と `FirstNodes` と `t₂` の基本性質）**
（原文 `tmp/content.md` 5165、faithful transcription
`p_8_5_Joints_FirstNodes_basic` = isabelle/pss_paper.thy:2098）。

`M ∈ ST_PS ∩ PT_PS` に対し、`Trans` の再帰的定義中の記号で
`j₁ = Lng M - 1`、`j₀ = parent M 0 (Lng M - 1)`、
`N = (M_j)_{j=j₋₁}^{j₁} = seg M (Adm_M(j₀)) j₁`、`J₁ = Lng(Br(Red N)) - 1` と置く。
`(1,j₀) <_M^Next (1,j₁)` かつ `j₀` が非 `M` 許容かつ `j₀ < j₁-1` ならば:

(1) `J₁ ≥ 0`（= `Lng(Br(Red N)) ≥ 1`）かつ
    `j₀-j₋₁ = Joints(Red N)_{J₁}` かつ `FirstNodes(Red N)_{J₁} = j₁-j₋₁`;

(2) `Red(N)_{0,j₁-j₋₁} = Red(N)_{1,j₁-j₋₁}`。

原文 (3)（`t₂` の各単項成分は `D_{M₁,j₁} 0` 以上）は未公開記号 `t₂` を参照するため
`pss_paper.thy` 同様 DEFERRED（本ファイルの scope 外）。 -/
theorem Joints_FirstNodes_basic (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hnx1 : nextR M 1 (parent M 0 (Lng M - 1)) (Lng M - 1) = true)
    (hnadm : adm M (parent M 0 (Lng M - 1)) = false)
    (hgap : parent M 0 (Lng M - 1) < Lng M - 1 - 1) :
    -- (1) `J₁ ≥ 0`
    1 ≤ (Br (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 1)))).length
      -- (1) `j₀ - j₋₁ = Joints(Red N)_{J₁}`
      ∧ parent M 0 (Lng M - 1) - Adm M (parent M 0 (Lng M - 1))
          = (Joints (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 1)))).getD
              ((Br (Red (seg M (Adm M (parent M 0 (Lng M - 1)))
                  (Lng M - 1)))).length - 1) 0
      -- (1) `FirstNodes(Red N)_{J₁} = j₁ - j₋₁`
      ∧ (FirstNodes (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 1)))).getD
              ((Br (Red (seg M (Adm M (parent M 0 (Lng M - 1)))
                  (Lng M - 1)))).length - 1) 0
          = Lng M - 1 - Adm M (parent M 0 (Lng M - 1))
      -- (2) `Red(N)_{0,j₁-j₋₁} = Red(N)_{1,j₁-j₋₁}`
      ∧ entry (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 1))) 0
              (Lng M - 1 - Adm M (parent M 0 (Lng M - 1)))
          = entry (Red (seg M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 1))) 1
              (Lng M - 1 - Adm M (parent M 0 (Lng M - 1))) :=
  Joints_FirstNodes_basic_core_jfb M (parent M 0 (Lng M - 1)) (Lng M - 1)
    (Adm M (parent M 0 (Lng M - 1))) hST hmono rfl rfl rfl hnx1 hnadm hgap

#print axioms Joints_FirstNodes_basic

end PSS
