import «6».«6.8-standard-P-descending»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.5-monoT-Red»
import «6».«6.7-standard-P-components»
import «6».«6.6-reduced-fseq»

/-!
# §6.8 命題（標準形の切片と `Br` の降順性の関係）

- 原文: `tmp/content.md` L1422 付近（「命題（標準形の切片と`Br`の降順性の関係）」）;
  `isabelle/pss_paper.thy` の `p_6_8_standard_slice_Br_descending`
- 訂正 A7: 証明本体の帰納対象「`M′` が標準形」は偽（反例
  `M = (0,0)(1,1)(2,0) ∈ ST_PS`, `M′ = (1,1)(2,0) ∉ ST_PS`）。訂正後の
  帰納対象「`Br(M′)` が降順」で移植する。命題の主張自体は訂正不要。
  （`¬STPS` は帰納述語の否定で `decide` 不可のため反例定理は原文注記のみ。）
- 訂正 A8: 証明本体の `j₁ = j₀^N + (n+1)(j₁^N - j₀^N) - 1` は off-by-one
  （正しくは係数 `n`）。本ファイルのタイル展開系はすべて訂正後の式で構成。
- Isabelle: `m_6_8_standard_slice_Br_descending` (pss_mechanized.thy:24002)、
  monoT core は `m_6_8_slice_Br_descending_monoT` (同:21961)、
  d1pos 系 brick は `oper_d1pos_*` 群 (同:9302–21950)
- 依存: `6.8-standard-P-descending`, `6.2-mono-ancestor-slice`,
  `6.5-monoT-Red`, `6.7-standard-P-components`, `6.6-reduced-fseq`
- 状態: 🚨 部分達成（ビルド緑・sorry 0）。rank 帰納の d1pos leg
  （`RankSuccD1posLeg`、Isabelle の `oper_d1pos_notbrle_*` 群に相当）のみ
  未証明の名前付き仮定として残る。それを除く全ケース（rank 0 / multi 前駆 /
  非 multi prefix / d0zero 全 3 サブケース）と WLOG 還元・最終定理は
  `standard_slice_Br_descending_of_d1pos` として無 sorry で完結。
-/

namespace PSS

/-- Branch components are ordered lexicographically downwards by their left
column: row zero is primary and row one breaks ties. -/
def cdom (C D : PS) : Prop :=
  entry D 0 0 ≤ entry C 0 0 ∧
    (entry C 0 0 = entry D 0 0 → entry D 1 0 ≤ entry C 1 0)

/-- The article's `descending`: every later component is dominated by every
earlier component.  `getD` only totalizes the statement; the index hypothesis
keeps every access in range. -/
def descending (Q : List PS) : Prop :=
  ∀ J₀ J₁, J₀ ≤ J₁ → J₁ < Q.length →
    cdom (Q.getD J₀ []) (Q.getD J₁ [])

@[simp] theorem cdom_refl (C : PS) : cdom C C := by
  simp [cdom]

theorem cdom_trans {C D E : PS} (hCD : cdom C D) (hDE : cdom D E) :
    cdom C E := by
  rcases hCD with ⟨hCD₀, hCD₁⟩
  rcases hDE with ⟨hDE₀, hDE₁⟩
  constructor
  · exact hDE₀.trans hCD₀
  · intro hCE
    have hCD : entry C 0 0 = entry D 0 0 := by omega
    have hDE : entry D 0 0 = entry E 0 0 := by omega
    exact (hDE₁ hDE).trans (hCD₁ hCD)

theorem descendingD {Q : List PS} (hQ : descending Q)
    {J₀ J₁ : ℕ} (h01 : J₀ ≤ J₁) (hJ₁ : J₁ < Q.length) :
    cdom (Q.getD J₀ []) (Q.getD J₁ []) :=
  hQ J₀ J₁ h01 hJ₁

theorem descending_iff_pairwise {Q : List PS} :
    descending Q ↔ Q.Pairwise cdom := by
  constructor
  · intro hQ
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hdom := hQ i j hij.le hj
    rw [getD_eq_getElem_idx Q [] hi,
      getD_eq_getElem_idx Q [] hj] at hdom
    exact hdom
  · intro hQ J₀ J₁ h01 hJ₁
    have hJ₀ : J₀ < Q.length := h01.trans_lt hJ₁
    by_cases heq : J₀ = J₁
    · subst J₁
      exact cdom_refl _
    · have hlt : J₀ < J₁ := Nat.lt_of_le_of_ne h01 heq
      have hdom := (List.pairwise_iff_getElem.mp hQ) J₀ J₁ hJ₀ hJ₁ hlt
      rw [getD_eq_getElem_idx Q [] hJ₀,
        getD_eq_getElem_idx Q [] hJ₁]
      exact hdom

@[simp] theorem descending_nil : descending ([] : List PS) := by
  intro J₀ J₁ h01 hJ₁
  simp at hJ₁

@[simp] theorem descending_singleton (C : PS) : descending [C] := by
  intro J₀ J₁ h01 hJ₁
  have hJ₁0 : J₁ = 0 := by simpa using hJ₁
  have hJ₀0 : J₀ = 0 := by omega
  subst J₀
  subst J₁
  simp

theorem descending_take {Q : List PS} (hQ : descending Q) (n : ℕ) :
    descending (Q.take n) := by
  intro J₀ J₁ h01 hJ₁
  have hJ₁Q : J₁ < Q.length := by
    rw [List.length_take] at hJ₁
    exact hJ₁.trans_le (Nat.min_le_right n Q.length)
  have hJ₀take : J₀ < (Q.take n).length := h01.trans_lt hJ₁
  have hJ₀Q : J₀ < Q.length := h01.trans_lt hJ₁Q
  have hget₀ : (Q.take n).getD J₀ [] = Q.getD J₀ [] := by
    rw [getD_eq_getElem_idx (Q.take n) [] hJ₀take,
      getD_eq_getElem_idx Q [] hJ₀Q]
    exact List.getElem_take
  have hget₁ : (Q.take n).getD J₁ [] = Q.getD J₁ [] := by
    rw [getD_eq_getElem_idx (Q.take n) [] hJ₁,
      getD_eq_getElem_idx Q [] hJ₁Q]
    exact List.getElem_take
  rw [hget₀, hget₁]
  exact hQ J₀ J₁ h01 hJ₁Q

theorem descending_append_of_cross {A B : List PS}
    (hA : descending A) (hB : descending B)
    (hcross : ∀ C ∈ A, ∀ D ∈ B, cdom C D) :
    descending (A ++ B) := by
  rw [descending_iff_pairwise, List.pairwise_append]
  exact ⟨descending_iff_pairwise.mp hA,
    descending_iff_pairwise.mp hB, hcross⟩

theorem descending_append {A B : List PS}
    (hA : descending A) (hB : descending B)
    (hjunc : A ≠ [] → B ≠ [] →
      cdom (A.getD (A.length - 1) []) (B.getD 0 [])) :
    descending (A ++ B) := by
  apply descending_append_of_cross hA hB
  intro C hCA D hDB
  have hAne : A ≠ [] := by simpa using List.ne_nil_of_mem hCA
  have hBne : B ≠ [] := by simpa using List.ne_nil_of_mem hDB
  rcases List.mem_iff_getElem.mp hCA with ⟨i, hi, hiC⟩
  rcases List.mem_iff_getElem.mp hDB with ⟨j, hj, hjD⟩
  have hlast : A.length - 1 < A.length := by
    have := List.length_pos_of_ne_nil hAne
    omega
  have hhead : 0 < B.length := List.length_pos_of_ne_nil hBne
  have hC : cdom C (A.getD (A.length - 1) []) := by
    have hh := hA i (A.length - 1) (by omega) hlast
    rw [getD_eq_getElem_idx A [] hi,
      getD_eq_getElem_idx A [] hlast] at hh
    rw [getD_eq_getElem_idx A [] hlast]
    simpa [hiC] using hh
  have hD : cdom (B.getD 0 []) D := by
    have hh := hB 0 j (Nat.zero_le j) hj
    rw [getD_eq_getElem_idx B [] hhead,
      getD_eq_getElem_idx B [] hj] at hh
    rw [getD_eq_getElem_idx B [] hhead]
    simpa [hjD] using hh
  exact cdom_trans (cdom_trans hC (hjunc hAne hBne)) hD

private theorem descending_append_junction_68 {A B : List PS}
    (h : descending (A ++ B)) (hA : A ≠ []) (hB : B ≠ []) :
    cdom (A.getD (A.length - 1) []) (B.getD 0 []) := by
  have hAlast : A.length - 1 < A.length := by
    have := List.length_pos_of_ne_nil hA
    omega
  have hBzero : 0 < B.length := List.length_pos_of_ne_nil hB
  have hright : A.length < (A ++ B).length := by simp; omega
  have hh := h (A.length - 1) A.length (by omega) hright
  have hgetL : (A ++ B).getD (A.length - 1) [] =
      A.getD (A.length - 1) [] := by
    rw [getD_eq_getElem_idx (A ++ B) [] (by simp; omega),
      getD_eq_getElem_idx A [] hAlast]
    simp [List.getElem_append, hAlast]
  have hgetR : (A ++ B).getD A.length [] = B.getD 0 [] := by
    rw [getD_eq_getElem_idx (A ++ B) [] hright,
      getD_eq_getElem_idx B [] hBzero]
    simp [List.getElem_append]
  rw [hgetL, hgetR] at hh
  exact hh

theorem descending_const_head {Q : List PS} {v₀ v₁ : ℕ}
    (hhead : ∀ J, J < Q.length →
      entry (Q.getD J []) 0 0 = v₀ ∧
        entry (Q.getD J []) 1 0 = v₁) :
    descending Q := by
  intro J₀ J₁ h01 hJ₁
  have hJ₀ : J₀ < Q.length := h01.trans_lt hJ₁
  rcases hhead J₀ hJ₀ with ⟨h00, h10⟩
  rcases hhead J₁ hJ₁ with ⟨h01, h11⟩
  rw [cdom]
  constructor
  · rw [h01, h00]
  · intro _
    rw [h11, h10]

@[simp] theorem descending_replicate (n : ℕ) (C : PS) :
    descending (List.replicate n C) := by
  apply descending_const_head (v₀ := entry C 0 0) (v₁ := entry C 1 0)
  intro J hJ
  rw [getD_eq_getElem_idx (List.replicate n C) [] hJ]
  simp

theorem cdom_IncrFirstN_iff (n : ℕ) (C D : PS)
    (hC : TPS C) (hD : TPS D) :
    cdom (IncrFirstN n C) (IncrFirstN n D) ↔ cdom C D := by
  have hCL : 0 < Lng C := List.length_pos_of_ne_nil hC
  have hDL : 0 < Lng D := List.length_pos_of_ne_nil hD
  rw [cdom, cdom,
    entry_IncrFirstN_zero n C 0 hCL,
    entry_IncrFirstN_zero n D 0 hDL,
    entry_IncrFirstN_one n C 0,
    entry_IncrFirstN_one n D 0]
  omega

/-- A uniform shift of row zero preserves descending component lists. -/
theorem descending_map_IncrFirstN (n : ℕ) (Q : List PS)
    (hQ : descending Q) (hT : ∀ C ∈ Q, TPS C) :
    descending (Q.map (IncrFirstN n)) := by
  rw [descending_iff_pairwise] at hQ ⊢
  rw [List.pairwise_map]
  induction Q with
  | nil => simp
  | cons C Q ih =>
      rw [List.pairwise_cons] at hQ ⊢
      constructor
      · intro D hD
        exact (cdom_IncrFirstN_iff n C D
          (hT C (by simp)) (hT D (by simp [hD]))).2 (hQ.1 D hD)
      · exact ih hQ.2 (fun D hD => hT D (by simp [hD]))

/-- Replace every component except the last by a uniform row-zero shift, and
replace the last component by one with the same shifted row-zero head and a
no-larger row-one head.  Descendingness is preserved. -/
theorem descending_shift_append {Q PRE : List PS} {TL : PS} {c : ℕ}
    (hQ : descending Q) (hQne : Q ≠ [])
    (hlen : PRE.length = Q.length - 1)
    (hpre0 : ∀ J, J < PRE.length →
      entry (PRE.getD J []) 0 0 = entry (Q.getD J []) 0 0 + c)
    (hpre1 : ∀ J, J < PRE.length →
      entry (PRE.getD J []) 1 0 = entry (Q.getD J []) 1 0)
    (htail0 : entry TL 0 0 =
      entry (Q.getD (Q.length - 1) []) 0 0 + c)
    (htail1 : entry TL 1 0 ≤
      entry (Q.getD (Q.length - 1) []) 1 0) :
    descending (PRE ++ [TL]) := by
  have hPRE : descending PRE := by
    intro J₀ J₁ h01 hJ₁
    have hJ₀ : J₀ < PRE.length := h01.trans_lt hJ₁
    have hJ₁Q : J₁ < Q.length := by omega
    have hbase := hQ J₀ J₁ h01 hJ₁Q
    rw [cdom] at hbase ⊢
    rw [hpre0 J₀ hJ₀, hpre0 J₁ hJ₁,
      hpre1 J₀ hJ₀, hpre1 J₁ hJ₁]
    constructor
    · omega
    · intro htie
      apply hbase.2
      omega
  apply descending_append hPRE (descending_singleton TL)
  intro hPREne _
  have hprepos : 0 < PRE.length := List.length_pos_of_ne_nil hPREne
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQne
  have hqLast : Q.length - 1 < Q.length := by omega
  have hpreLast : PRE.length - 1 < PRE.length := by omega
  have hidx : PRE.length - 1 = Q.length - 2 := by omega
  have hbase := hQ (Q.length - 2) (Q.length - 1) (by omega) hqLast
  have hpre0last := hpre0 (PRE.length - 1) hpreLast
  have hpre1last := hpre1 (PRE.length - 1) hpreLast
  have hget : PRE.getD (PRE.length - 1) [] =
      PRE.getD (Q.length - 2) [] := by rw [hidx]
  rw [hget] at hpre0last hpre1last
  rw [hidx] at hpre0last hpre1last
  rw [cdom] at hbase ⊢
  simp only [List.getD_cons_zero]
  rw [hget, hpre0last, hpre1last, htail0]
  constructor
  · exact Nat.add_le_add_right hbase.1 c
  · intro htie
    exact htail1.trans (hbase.2 (by omega))

private theorem seg_getElem_68 (M : PS) (a b i : ℕ)
    (hi : i < Lng (seg M a b)) :
    (seg M a b)[i] = (entry M 0 (a + i), entry M 1 (a + i)) := by
  simp [seg, List.getElem_range']

private theorem getLastD_eq_getD_last_68 {α : Type} (Q : List α) (d : α)
    (hQ : Q ≠ []) : Q.getLastD d = Q.getD (Q.length - 1) d := by
  cases h : Q with
  | nil => exact (hQ h).elim
  | cons x xs =>
      simp [List.getLastD, List.getD, List.getLast_eq_getElem]

private theorem getD_dropLast_68 {α : Type} (Q : List α) (d : α)
    (j : ℕ) (hj : j < Q.dropLast.length) :
    Q.dropLast.getD j d = Q.getD j d := by
  have hjQ : j < Q.length := hj.trans_le (by simp)
  rw [getD_eq_getElem_idx Q.dropLast d hj,
    getD_eq_getElem_idx Q d hjQ]
  exact List.getElem_dropLast hj

/-- A positive fundamental-sequence step agrees with its source strictly
before the source's last column. -/
private theorem entry_oper_lt_last_68 (M : PS) (n i x : ℕ)
    (hlen : 1 < Lng M) (hn : 1 ≤ n)
    (hi : i = 0 ∨ i = 1) (hx : x < Lng M - 1) :
    entry (oper M n) i x = entry M i x := by
  have hlastNe : Lng M - 1 ≠ 0 := by omega
  by_cases hz : entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0
  · have hop : oper M n = Pred M := by
      simp [oper, hlastNe, hz]
    rw [hop, Pred_eq_take M hlen, entry_take M (Lng M - 1) i x hx]
  · let i₁ := idx1 M (Lng M - 1)
    by_cases hp : hasParent M i₁ (Lng M - 1) = true
    · let j₀ := parent M i₁ (Lng M - 1)
      have hnext := hasParent_next_fseq M i₁ (Lng M - 1) hp
      have hj₀lt : j₀ < Lng M - 1 :=
        (nextR_implies_row0 M i₁ j₀ (Lng M - 1) hnext).1
      by_cases hxpre : x < j₀
      · exact entry_oper_tiling_prefix M n i x hlen hz
          (by simpa [i₁] using hp) (by simpa [j₀, i₁] using hxpre)
      · have hj₀x : j₀ ≤ x := by omega
        let s := x - j₀
        have hs : s < Lng M - 1 - j₀ := by simp [s]; omega
        have hsEq : j₀ + s = x := by simp [s, Nat.add_sub_of_le hj₀x]
        rcases hi with rfl | rfl
        · have hh := entry_oper_tiling_block_zero M n 0 s hlen hz
            (by simpa [i₁] using hp) (by omega) (by simpa [j₀, i₁] using hs)
          simpa [j₀, i₁, hsEq] using hh
        · have hh := entry_oper_tiling_block_one M n 0 s hlen hz
            (by simpa [i₁] using hp) (by omega) (by simpa [j₀, i₁] using hs)
          simpa [j₀, i₁, hsEq] using hh
    · have hpfalse : hasParent M i₁ (Lng M - 1) = false := by
        exact Bool.eq_false_of_not_eq_true hp
      have hop : oper M n = Pred M := by
        simp [oper, hlastNe, hz, i₁, hpfalse]
      rw [hop, Pred_eq_take M hlen, entry_take M (Lng M - 1) i x hx]

private theorem seg_oper_eq_68 (M : PS) (n a b : ℕ)
    (hlen : 1 < Lng M) (hn : 1 ≤ n)
    (hab : a ≤ b) (hb : b < Lng M - 1) :
    seg (oper M n) a b = seg M a b := by
  apply List.ext_getElem
  · simp
  · intro i hiL hiR
    rw [seg_getElem_68 (oper M n) a b i hiL,
      seg_getElem_68 M a b i hiR]
    have hai : a + i < Lng M - 1 := by
      simp only [length_seg] at hiL
      omega
    rw [entry_oper_lt_last_68 M n 0 (a + i) hlen hn (Or.inl rfl) hai,
      entry_oper_lt_last_68 M n 1 (a + i) hlen hn (Or.inr rfl) hai]

/-- The already completed §6.8 second proposition plus row-zero monotonicity
gives the full descending property of the principal components of a standard
sequence. -/
theorem descending_P_of_ST (M : PS) (hM : STPS M) : descending (P M) := by
  intro J₀ J₁ h01 hJ₁
  have hMT : TPS M := STPS_TPS M hM
  have hJ₁le : J₁ ≤ (P M).length - 1 := by omega
  constructor
  · exact P_leftend_mono M J₀ J₁ hMT h01 hJ₁le
  · intro htie
    exact standard_P_descending M hM J₀ J₁ h01 hJ₁le htie

/-- A slice of a slice, with the inner right endpoint in range, is the
corresponding ambient slice. -/
theorem seg_of_seg_68 (M : PS) (a b c d : ℕ)
    (hab : a ≤ b) (hdb : d ≤ b - a) :
    seg (seg M a b) c d = seg M (a + c) (a + d) := by
  apply List.ext_getElem
  · simp only [length_seg]
    omega
  · intro i hiL hiR
    have hic : c + i < Lng (seg M a b) := by
      simp only [length_seg] at hiL ⊢
      omega
    rw [seg_getElem_68 (seg M a b) c d i hiL,
      seg_getElem_68 M (a + c) (a + d) i hiR]
    rw [entry_seg M a b 0 (c + i) hic,
      entry_seg M a b 1 (c + i) hic]
    simp [Nat.add_assoc]

/-- A nonempty branch of a slice, rewritten in ambient coordinates. -/
theorem Br_seg_reshape_68 (M : PS) (j₀ j₁ : ℕ)
    (hlt : j₀ < j₁) (_hj₁ : j₁ < Lng M)
    (htr : TrMax (seg M j₀ j₁) ≠ Lng (seg M j₀ j₁) - 1) :
    Br (seg M j₀ j₁) =
      P (seg M (j₀ + TrMax (seg M j₀ j₁) + 1) j₁) := by
  let S := seg M j₀ j₁
  let t := TrMax S
  have htr' : t ≠ Lng S - 1 := by simpa [S, t] using htr
  have hBr : Br S = P (seg S (t + 1) (Lng S - 1)) := by
    simp [Br, t, htr']
  have hend : Lng S - 1 = j₁ - j₀ := by
    simp [S]
    omega
  have hinner : seg S (t + 1) (Lng S - 1) =
      seg M (j₀ + (t + 1)) (j₀ + (Lng S - 1)) := by
    exact seg_of_seg_68 M j₀ j₁ (t + 1) (Lng S - 1)
      hlt.le (by omega)
  have hright : j₀ + (Lng S - 1) = j₁ := by omega
  rw [hBr, hinner, hright]
  congr 2

/-- Once principal components of every standard slice are known to descend,
the stated `Br` theorem follows by viewing the branch part as a second slice. -/
theorem standard_slice_Br_descending_of_slice_P
    (core : ∀ (N : PS) (a b : ℕ), STPS N → a ≤ b →
      b ≤ Lng N - 1 → descending (P (seg N a b)))
    (M : PS) (j₀ j₁ : ℕ) (hM : STPS M)
    (hlt : j₀ < j₁) (hj₁ : j₁ ≤ Lng M - 1)
    (hanc : leR M 0 j₀ j₁ = true) :
    monoT (seg M j₀ j₁) = true ∧
      descending (Br (seg M j₀ j₁)) := by
  have hMT : TPS M := STPS_TPS M hM
  constructor
  · exact mono_ancestor_slice M j₀ j₁ hMT hlt hanc
  · let S := seg M j₀ j₁
    have hST : TPS S := by
      apply List.ne_nil_of_length_pos
      simp [S]
      omega
    by_cases hBrempty : Br S = []
    · change descending (Br S)
      rw [hBrempty]
      exact descending_nil
    · have htrBound := TrMax_bound S hST
      have htrNe : TrMax S ≠ Lng S - 1 := by
        intro hEq
        have : Br S = [] := by simp [Br, hEq]
        exact hBrempty this
      have htrLt : TrMax S < Lng S - 1 := by omega
      let c := TrMax S + 1
      let e := Lng S - 1
      have hBr : Br S = P (seg S c e) := by
        simp [Br, htrNe, c, e]
      have heBound : e ≤ j₁ - j₀ := by
        simp [e, S]
        omega
      have hseg : seg S c e = seg M (j₀ + c) (j₀ + e) := by
        simpa [S] using seg_of_seg_68 M j₀ j₁ c e hlt.le heBound
      have hce : j₀ + c ≤ j₀ + e := by
        simp only [Nat.add_le_add_iff_left]
        omega
      have heM : j₀ + e ≤ Lng M - 1 := by
        simp [e, S]
        omega
      rw [hBr, hseg]
      exact core M (j₀ + c) (j₀ + e) hM hce heM

/-- If the branch suffix is itself row-zero ancestral, it is a single
principal component, so its branch list is automatically descending. -/
theorem descending_Br_of_branch_le0 (S : PS) (hS : TPS S)
    (hbrle : TrMax S = Lng S - 1 ∨
      le0 S (TrMax S + 1) (Lng S - 1) = true) :
    descending (Br S) := by
  by_cases htr : TrMax S = Lng S - 1
  · have hBr : Br S = [] := by simp [Br, htr]
    rw [hBr]
    exact descending_nil
  · have hbound := TrMax_bound S hS
    have htrlt : TrMax S < Lng S - 1 := by omega
    let Y := seg S (TrMax S + 1) (Lng S - 1)
    have hBr : Br S = P Y := by simp [Br, htr, Y]
    have hYT : TPS Y := by
      apply List.ne_nil_of_length_pos
      simp [Y]
      omega
    have hmultiY : multiT Y = false := by
      by_cases hlen : 1 < Lng Y
      · have hle : leR S 0 (TrMax S + 1) (Lng S - 1) = true := by
          simpa [leR] using hbrle.resolve_left htr
        have hmono : monoT Y = true :=
          mono_ancestor_slice S (TrMax S + 1) (Lng S - 1)
            hS (by simp [Y] at hlen; omega) hle
        simp [multiT, hmono]
      · have hpos := List.length_pos_of_ne_nil hYT
        change 0 < Lng Y at hpos
        have hlen1 : Lng Y = 1 := by omega
        by_cases hz : entry Y 1 0 = 0
        · simp [multiT, monoT, zeroT, hlen1, hz]
        · have hle : leR Y 0 0 0 = true := by
            simp [leR, le0, le0Aux, hlen1]
          have hzero : zeroT Y = false := by simp [zeroT, hlen1, hz]
          have hmono : monoT Y = true := by simp [monoT, hzero, hlen1, hle]
          simp [multiT, hzero, hmono]
    rw [hBr, P_nonmulti_eq Y hmultiY]
    exact descending_singleton Y

theorem monoT_seg_of_le0_68 (M : PS) (a b : ℕ)
    (hb : b < Lng M) (hab : a < b) (hle : le0 M a b = true) :
    monoT (seg M a b) = true := by
  have hM : TPS M := by
    apply List.ne_nil_of_length_pos
    exact (Nat.zero_le b).trans_lt hb
  exact mono_ancestor_slice M a b hM hab (by simpa [leR] using hle)

private theorem parent_block_le0_68 (M : PS) (j₀ j₁ s : ℕ)
    (hM : TPS M) (hnext : nextR M 0 j₀ j₁ = true)
    (hs : s < j₁ - j₀) : le0 M j₀ (j₀ + s) = true := by
  have hj₀lt := (nextR_implies_row0 M 0 j₀ j₁ hnext).1
  have hreach := nextR0_leR M j₀ j₁ hnext
  have hpart := ancestor_tree_1 M j₀ (j₀ + s) j₁ hM hreach
    (by omega) (by omega)
  simpa [leR] using hpart

private theorem parent_block_entry0_min_68 (M : PS) (j₀ j₁ s : ℕ)
    (hM : TPS M) (hnext : nextR M 0 j₀ j₁ = true)
    (hs : s < j₁ - j₀) :
    entry M 0 j₀ ≤ entry M 0 (j₀ + s) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  · have hle := parent_block_le0_68 M j₀ j₁ s hM hnext hs
    have hgrowth := ancestor_basic_1 M j₀ (j₀ + s) (j₀ + s) hM
      (by omega) le_rfl (by simpa [leR] using hle)
    exact hgrowth.le

private theorem P_seg_single_of_le0_68 (M : PS) (a b : ℕ)
    (hb : b < Lng M) (hab : a ≤ b) (hle : le0 M a b = true) :
    P (seg M a b) = [seg M a b] := by
  have hnm : multiT (seg M a b) = false := by
    by_cases hlt : a < b
    · have hm := monoT_seg_of_le0_68 M a b hb hlt hle
      simp [multiT, hm]
    · have heq : a = b := by omega
      subst b
      have hlen : Lng (seg M a a) = 1 := by simp
      cases hmu : multiT (seg M a a) with
      | false => rfl
      | true =>
          have hT : TPS (seg M a a) := by
            apply List.ne_nil_of_length_pos
            change 0 < Lng (seg M a a)
            rw [hlen]
            omega
          have hlong := multi_length_fseq (seg M a a) hT hmu
          rw [hlen] at hlong
          omega
  exact P_nonmulti_eq (seg M a b) hnm

private theorem TrMax_eq_of_prefix_agree_68
    (M N : PS) (c : ℕ) (hM : TPS M) (hN : TPS N)
    (hagree : ∀ j, j ≤ c → M.getD j (0, 0) = N.getD j (0, 0))
    (hcM : c < Lng M) (hcN : c < Lng N)
    (hconf : TrMax N ≤ c)
    (hstop : nextR M 1 (TrMax N) (TrMax N + 1) = false) :
    TrMax M = TrMax N := by
  have htake : M.take (c + 1) = N.take (c + 1) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left (by omega : c + 1 ≤ Lng M),
        Nat.min_eq_left (by omega : c + 1 ≤ Lng N)]
    · intro j hjM hjN
      have hj : j ≤ c := by
        simp only [List.length_take, Nat.min_eq_left (by omega : c + 1 ≤ Lng M)] at hjM
        omega
      have hjML : j < Lng M := by
        exact hj.trans_lt hcM
      have hjNL : j < Lng N := by
        exact hj.trans_lt hcN
      rw [List.getElem_take, List.getElem_take,
        ← getD_eq_getElem_idx M (0, 0) hjML,
        ← getD_eq_getElem_idx N (0, 0) hjNL]
      exact hagree j hj
  have hle : TrMax N ≤ TrMax M := by
    apply le_TrMax_intro_wd M (TrMax N) hM
    intro j hj
    have hjc : j + 1 < c + 1 := by omega
    calc
      nextR M 1 j (j + 1) = nextR (M.take (c + 1)) 1 j (j + 1) :=
        (nextR_take_adm M (c + 1) 1 j (j + 1) (by omega) (by omega) hjc).symm
      _ = nextR (N.take (c + 1)) 1 j (j + 1) := by rw [htake]
      _ = nextR N 1 j (j + 1) :=
        nextR_take_adm N (c + 1) 1 j (j + 1) (by omega) (by omega) hjc
      _ = true := TrMax_trunk_step N j hN hj
  apply Nat.le_antisymm ?_ hle
  by_contra hnot
  have hlt : TrMax N < TrMax M := by omega
  have hstep := TrMax_trunk_step M (TrMax N) hM hlt
  rw [hstop] at hstep
  simp at hstep

private theorem TrMax_lt_last_of_row1_zero_68
    (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hz : entry M 1 (Lng M - 1) = 0) :
    TrMax M < Lng M - 1 := by
  have hbound := TrMax_bound M hM
  by_contra hnot
  have heq : TrMax M = Lng M - 1 := by omega
  have hprev : Lng M - 2 < TrMax M := by omega
  have hstep := TrMax_trunk_step M (Lng M - 2) hM hprev
  have hsucc : Lng M - 2 + 1 = Lng M - 1 := by omega
  rw [hsucc] at hstep
  have hdata := hstep
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq] at hdata
  omega

private theorem nextR_prefix_agree_68
    (M N : PS) (c i x y : ℕ)
    (hagree : ∀ j, j ≤ c → M.getD j (0, 0) = N.getD j (0, 0))
    (hcM : c < Lng M) (hcN : c < Lng N)
    (hx : x ≤ c) (hy : y ≤ c) :
    nextR M i x y = nextR N i x y := by
  have htake : M.take (c + 1) = N.take (c + 1) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left (by omega : c + 1 ≤ Lng M),
        Nat.min_eq_left (by omega : c + 1 ≤ Lng N)]
    · intro j hjM hjN
      have hj : j ≤ c := by
        simp only [List.length_take,
          Nat.min_eq_left (by omega : c + 1 ≤ Lng M)] at hjM
        omega
      rw [List.getElem_take, List.getElem_take,
        ← getD_eq_getElem_idx M (0, 0) (hj.trans_lt hcM),
        ← getD_eq_getElem_idx N (0, 0) (hj.trans_lt hcN)]
      exact hagree j hj
  calc
    nextR M i x y = nextR (M.take (c + 1)) i x y :=
      (nextR_take_adm M (c + 1) i x y (by omega) (by omega) (by omega)).symm
    _ = nextR (N.take (c + 1)) i x y := by rw [htake]
    _ = nextR N i x y :=
      nextR_take_adm N (c + 1) i x y (by omega) (by omega) (by omega)

private theorem TrMax_eq_of_prefix_agree_sym_68
    (M N : PS) (c : ℕ) (hM : TPS M) (hN : TPS N)
    (hagree : ∀ j, j ≤ c → M.getD j (0, 0) = N.getD j (0, 0))
    (hcM : c < Lng M) (hcN : c < Lng N)
    (hconf : TrMax M + 1 ≤ c)
    (hstop : nextR M 1 (TrMax M) (TrMax M + 1) = false) :
    TrMax M = TrMax N := by
  have hstopN : nextR N 1 (TrMax M) (TrMax M + 1) = false := by
    have hsame := nextR_prefix_agree_68 N M c 1 (TrMax M)
      (TrMax M + 1) (fun j hj => (hagree j hj).symm)
      hcN hcM (by omega) hconf
    rw [hsame, hstop]
  have hh := TrMax_eq_of_prefix_agree_68 N M c hN hM
    (fun j hj => (hagree j hj).symm) hcN hcM (by omega) hstopN
  exact hh.symm

private theorem trunk_entry1_mono_68 (M : PS) (a b : ℕ)
    (hM : TPS M) (hab : a ≤ b) (hb : b ≤ TrMax M) :
    entry M 1 a ≤ entry M 1 b := by
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        have hbtr : b < TrMax M := by omega
        have hleft := ih a hab' (by omega)
        have hstep := TrMax_trunk_step M b hM hbtr
        have hdata := hstep
        simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
          Bool.and_eq_true, decide_eq_true_eq] at hdata
        exact hleft.trans hdata.1.1.2.le

private theorem seg_oper_prefix_agree_68
    (N : PS) (n a b c : ℕ)
    (hlen : 1 < Lng N) (hn : 1 ≤ n)
    (hcM : c < Lng (seg (oper N n) a b))
    (hcN : c < Lng (seg N a (Lng N - 1)))
    (hbefore : ∀ s, s ≤ c → a + s < Lng N - 1) :
    ∀ s, s ≤ c →
      (seg (oper N n) a b).getD s (0, 0) =
        (seg N a (Lng N - 1)).getD s (0, 0) := by
  intro s hs
  have hsM : s < Lng (seg (oper N n) a b) := hs.trans_lt hcM
  have hsN : s < Lng (seg N a (Lng N - 1)) := hs.trans_lt hcN
  rw [getD_eq_getElem_idx _ _ hsM, getD_eq_getElem_idx _ _ hsN,
    seg_getElem_68 (oper N n) a b s hsM,
    seg_getElem_68 N a (Lng N - 1) s hsN,
    entry_oper_lt_last_68 N n 0 (a + s) hlen hn (Or.inl rfl)
      (hbefore s hs),
    entry_oper_lt_last_68 N n 1 (a + s) hlen hn (Or.inr rfl)
      (hbefore s hs)]

/-! At the first d0-zero tiling boundary, the reduced trunk of the old
slice cannot acquire one more row-1 step in the expanded slice. -/
private theorem nextR1_boundary_stop_d0zero_caseA_68
    (N : PS) (n j₀' j₁' : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (hn : 1 ≤ n)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hbge : Lng N - 2 ≤ j₁')
    (hend : j₁' < Lng (oper N n)) :
    nextR (seg (oper N n) j₀' j₁') 1
      (TrMax (seg N j₀' (Lng N - 1)))
      (TrMax (seg N j₀' (Lng N - 1)) + 1) = false := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let Mp := seg (oper N n) j₀' j₁'
  let Np := seg N j₀' j₁
  let t := TrMax Np
  have hp0 : hasParent N 0 j₁ = true := by
    simpa [j₁, hi] using hp
  have hnext : nextR N 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ := (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hj₀'lt : j₀' < j₁ := hstart.trans hj₀lt
  have hstartLe : j₀' ≤ j₁' := by
    dsimp [j₁] at hj₀'lt
    omega
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hNpLen : 1 < Lng Np := by
    simp [Np]
    omega
  have hd0 : entry N 1 j₁ = 0 := by
    by_cases hpos : 0 < entry N 1 j₁
    · have hone : idx1 N j₁ = 1 := by simp [idx1, hpos]
      rw [hone] at hi
      omega
    · omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hlastBound : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hlastBound]
    have hidx : j₀' + (Lng Np - 1) = j₁ := by
      simp [Np]
      omega
    rw [hidx, hd0]
  have htLast : t < Lng Np - 1 := by
    exact TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
  have htc : t ≤ Lng Np - 2 := by omega
  apply Bool.eq_false_iff.mpr
  intro hstep
  by_cases heasy : t < Lng Np - 2
  · let c := Lng Np - 2
    have hcN : c < Lng Np := by simp [c]; omega
    have hcM : c < Lng Mp := by
      simp [c, Mp, Np]
      dsimp [j₁] at hj₀'lt
      omega
    have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Np.getD s (0, 0) := by
      simpa [Mp, Np] using
        seg_oper_prefix_agree_68 N n j₀' j₁' c hlen hn hcM hcN
          (by
            intro s hs
            simp [c, Np] at hs
            omega)
    have hsame := nextR_prefix_agree_68 Mp Np c 1 t (t + 1)
      hagree hcM hcN (by simp [c]; omega) (by simp [c]; omega)
    rw [hsame, TrMax_stop_uncond Np hNpT] at hstep
    simp at hstep
  · have hteq : t = Lng Np - 2 := by omega
    have ht1idx : j₀' + (t + 1) = j₁ := by
      simp [Np] at hteq
      omega
    have htidx : j₀' + t = j₁ - 1 := by omega
    have hdata := hstep
    simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
      Bool.and_eq_true, decide_eq_true_eq] at hdata
    have ht1Mp : t + 1 < Lng Mp := hdata.1.1.1.1.2
    have htMp : t < Lng Mp := by omega
    have hj₁Oper : j₁ < Lng (oper N n) := by
      have hsegLen : Lng Mp = j₁' + 1 - j₀' := by simp [Mp]
      rw [hsegLen] at ht1Mp
      omega
    let w := j₁ - j₀
    have hw : 0 < w := by simp [w]; omega
    have hOL : Lng (oper N n) = j₀ + n * w := by
      have hh := length_oper_tiling N n hlen hzero hp
      simpa [j₁, j₀, w, hi] using hh
    have hn2 : 2 ≤ n := by
      by_contra hnot
      have hn1 : n = 1 := by omega
      rw [hOL, hn1] at hj₁Oper
      simp [w] at hj₁Oper
      omega
    have het : entry Mp 1 t = entry N 1 (j₁ - 1) := by
      rw [entry_seg (oper N n) j₀' j₁' 1 t htMp, htidx,
        entry_oper_lt_last_68 N n 1 (j₁ - 1) hlen hn (Or.inr rfl)]
      dsimp [j₁]
      omega
    have het1 : entry Mp 1 (t + 1) = entry N 1 j₀ := by
      rw [entry_seg (oper N n) j₀' j₁' 1 (t + 1) ht1Mp, ht1idx]
      have hh := entry_oper_tiling_block_one N n 1 0 hlen hzero hp
        (by omega) (by simpa [j₁, j₀, w, hi] using hw)
      have hh' : entry (oper N n) 1 (j₀ + w) = entry N 1 j₀ := by
        simpa [j₁, j₀, w, hi] using hh
      have heq : j₀ + w = j₁ := by simp [w]; omega
      rw [← heq]
      exact hh'
    have hjlocal : j₀ - j₀' ≤ t := by
      simp [Np] at hteq
      omega
    have hmono := trunk_entry1_mono_68 Np (j₀ - j₀') t hNpT
      hjlocal (by simp [t])
    have hjNp : j₀ - j₀' < Lng Np := by
      simp [Np]
      omega
    have htNp : t < Lng Np := htLast.trans_le (Nat.sub_le _ _)
    rw [entry_seg N j₀' j₁ 1 (j₀ - j₀') hjNp,
      entry_seg N j₀' j₁ 1 t htNp] at hmono
    have hjidx : j₀' + (j₀ - j₀') = j₀ := by
      apply Nat.add_sub_of_le
      simpa [j₀, j₁] using hstart.le
    rw [hjidx, htidx] at hmono
    have hstrict : entry Mp 1 t < entry Mp 1 (t + 1) := hdata.1.1.2
    rw [het, het1] at hstrict
    omega

private theorem TrMax_seg_oper_d0zero_eq_caseA_68
    (N : PS) (n j₀' j₁' : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (hn : 1 ≤ n)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hbge : Lng N - 2 ≤ j₁')
    (hend : j₁' < Lng (oper N n)) :
    TrMax (seg (oper N n) j₀' j₁') =
      TrMax (seg N j₀' (Lng N - 1)) := by
  let j₁ := Lng N - 1
  let Mp := seg (oper N n) j₀' j₁'
  let Np := seg N j₀' j₁
  let c := j₁ - 1 - j₀'
  have hnext := hasParent_next_fseq N 0 j₁ (by simpa [j₁, hi] using hp)
  have hj₀lt : parent N 0 j₁ < j₁ :=
    (nextR_implies_row0 N 0 (parent N 0 j₁) j₁ hnext).1
  have hj₀'lt : j₀' < j₁ := hstart.trans hj₀lt
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    dsimp [j₁] at hj₀'lt
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hNpLen : 1 < Lng Np := by simp [Np]; omega
  have hd0 : entry N 1 j₁ = 0 := by
    by_cases hpos : 0 < entry N 1 j₁
    · have hone : idx1 N j₁ = 1 := by simp [idx1, hpos]
      rw [hone] at hi
      omega
    · omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hb : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hb]
    have : j₀' + (Lng Np - 1) = j₁ := by simp [Np]; omega
    rw [this, hd0]
  have htconf : TrMax Np ≤ c := by
    have hh := TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
    simp [c, Np]
    simp [Np] at hh
    omega
  have hcN : c < Lng Np := by simp [c, Np]; omega
  have hcM : c < Lng Mp := by
    simp [c, Mp]
    dsimp [j₁] at hj₀'lt
    omega
  have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Np.getD s (0, 0) := by
    simpa [Mp, Np, j₁] using
      seg_oper_prefix_agree_68 N n j₀' j₁' c hlen hn hcM hcN
        (by intro s hs; simp [c, j₁] at hs ⊢; omega)
  have hstop := nextR1_boundary_stop_d0zero_caseA_68 N n j₀' j₁'
    hNT hlen hzero hp hi hn hstart hbge hend
  exact TrMax_eq_of_prefix_agree_68 Mp Np c hMpT hNpT hagree hcM hcN
    htconf (by simpa [Mp, Np] using hstop)

private theorem leR0_refl_68 (M : PS) (a : ℕ) (ha : a < Lng M) :
    leR M 0 a a = true := by
  have haux : le0Aux M (Lng M) a a = true := by
    cases Lng M <;> simp [le0Aux]
  simp [leR, le0, ha, haux]

private theorem leR0_transfer_seg_eq_68
    (M N : PS) (a b : ℕ) (hab : a < b)
    (hbM : b < Lng M) (hbN : b < Lng N)
    (hseg : seg M a b = seg N a b)
    (hle : leR M 0 a b = true) :
    leR N 0 a b = true := by
  have hlocalM : leR (seg M a b) 0 0 (b - a) = true := by
    rw [leR0_seg_adm M a b 0 (b - a) hab.le hbM
      (by simp; omega) (by simp; omega)]
    simpa [Nat.add_sub_of_le hab.le] using hle
  have hlocalN : leR (seg N a b) 0 0 (b - a) = true := by
    rw [← hseg]
    exact hlocalM
  rw [leR0_seg_adm N a b 0 (b - a) hab.le hbN
    (by simp; omega) (by simp; omega)] at hlocalN
  simpa [Nat.add_sub_of_le hab.le] using hlocalN

private theorem P_component_head_ge_68
    (S : PS) (v J : ℕ) (hS : TPS S)
    (hJ : J < (P S).length)
    (hall : ∀ i, i < Lng S → v ≤ entry S 0 i) :
    v ≤ entry ((P S).getD J []) 0 0 := by
  let a := (IdxSum (P S)).getD J 0
  have hpos : 0 < Lng ((P S).getD J []) :=
    P_component_nonempty S J hS hJ
  have hdiff := idxSum_diff (P S) J hJ
  have hmono := idxSum_mono (P S) (J + 1) (P S).length
    (by omega) (le_refl _)
  have htotal : (IdxSum (P S)).getD (P S).length 0 = Lng S := by
    calc
      (IdxSum (P S)).getD (P S).length 0 = Lng (P S).flatten :=
        idxSum_total (P S)
      _ = Lng S := congrArg Lng (P_concat S)
  have ha : a < Lng S := by
    dsimp [a]
    rw [htotal] at hmono
    omega
  rw [P_component_leftend S J hS hJ]
  exact hall a ha

private theorem P_first_component_head_68
    (S : PS) (i : ℕ) (hS : TPS S) :
    entry ((P S).getD 0 []) i 0 = entry S i 0 := by
  have hPpos : 0 < (P S).length := List.length_pos_of_ne_nil (P_nonempty S)
  have hcomp := P_IdxSum S 0 hS (by omega : 0 ≤ (P S).length - 1)
  have hCpos : 0 < Lng ((P S).getD 0 []) :=
    P_component_nonempty S 0 hS hPpos
  rw [hcomp]
  have hsegpos : 0 < Lng (seg S ((IdxSum (P S)).getD 0 0)
      ((IdxSum (P S)).getD 1 0 - 1)) := by
    rw [← hcomp]
    exact hCpos
  rw [entry_seg S ((IdxSum (P S)).getD 0 0)
    ((IdxSum (P S)).getD 1 0 - 1) i 0 hsegpos]
  have hidx0 : (IdxSum (P S)).getD 0 0 = 0 := by
    rw [idxSum_getD (P S) 0 (Nat.zero_le _)]
    simp
  rw [hidx0]

private theorem P_seg_split_at_68
    (M : PS) (a c b : ℕ) (hM : TPS M)
    (hac : a < c) (hcb : c ≤ b) (hb : b < Lng M)
    (hmin : ∀ x, a ≤ x → x < c → entry M 0 c ≤ entry M 0 x) :
    P (seg M a b) = P (seg M a (c - 1)) ++ P (seg M c b) := by
  let S := seg M a b
  let d := c - a
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    simp [S]
    omega
  have hdpos : 0 < d := by simp [d]; omega
  have hd : d ≤ Lng S - 1 := by simp [d, S]; omega
  have hdS : d < Lng S := hd.trans_lt (by
    have := List.length_pos_of_ne_nil hST
    omega)
  have hlocalMin : ∀ r, r < d → entry S 0 d ≤ entry S 0 r := by
    intro r hrd
    have hrS : r < Lng S := hrd.trans hdS
    rw [entry_seg M a b 0 d hdS, entry_seg M a b 0 r hrS]
    have had : a + d = c := by simp [d, Nat.add_sub_of_le hac.le]
    rw [had]
    exact hmin (a + r) (by omega) (by omega)
  have hsplit := P_additivity S d hST hdpos hd hlocalMin
  have hleft : seg S 0 (d - 1) = seg M a (c - 1) := by
    have hh := seg_of_seg_68 M a b 0 (d - 1) (hac.le.trans hcb)
      (by simp [d]; omega)
    have hend : a + (d - 1) = c - 1 := by simp [d]; omega
    simpa [S, hend] using hh
  have hright : seg S d (Lng S - 1) = seg M c b := by
    have hh := seg_of_seg_68 M a b d (Lng S - 1) (hac.le.trans hcb)
      (by simp [S]; omega)
    have hstart : a + d = c := by simp [d, Nat.add_sub_of_le hac.le]
    have hend : a + (Lng S - 1) = b := by simp [S]; omega
    calc
      seg S d (Lng S - 1) =
          seg M (a + d) (a + (Lng S - 1)) := by simpa [S] using hh
      _ = seg M c b := by rw [hstart, hend]
  rw [hleft, hright] at hsplit
  exact hsplit

private theorem replicate_append_heads_68
    (q : ℕ) (C D : PS) (v₀ v₁ : ℕ)
    (hC₀ : entry C 0 0 = v₀) (hC₁ : entry C 1 0 = v₁)
    (hD₀ : entry D 0 0 = v₀) (hD₁ : entry D 1 0 = v₁) :
    ∀ J, J < (List.replicate q C ++ [D]).length →
      entry ((List.replicate q C ++ [D]).getD J []) 0 0 = v₀ ∧
        entry ((List.replicate q C ++ [D]).getD J []) 1 0 = v₁ := by
  intro J hJ
  have hmem : (List.replicate q C ++ [D]).getD J [] ∈
      List.replicate q C ++ [D] := by
    rw [getD_eq_getElem_idx _ [] hJ]
    exact List.getElem_mem hJ
  simp only [List.mem_append, List.mem_replicate,
    List.mem_singleton] at hmem
  rcases hmem with h | h
  · rw [h.2, hC₀, hC₁]
    exact ⟨rfl, rfl⟩
  · rw [h, hD₀, hD₁]
    exact ⟨rfl, rfl⟩

private theorem P_terminal_split_above_parent_68
    (N : PS) (j₀ j₁ a : ℕ) (hNT : TPS N)
    (hnext : nextR N 0 j₀ j₁ = true)
    (ha₀ : j₀ < a) (ha₁ : a < j₁) :
    P (seg N a j₁) =
      P (seg N a (j₁ - 1)) ++ [seg N j₁ j₁] := by
  let S := seg N a j₁
  let c := j₁ - a
  have hj₁N : j₁ < Lng N := by
    have hh := hnext
    simp only [nextR, if_pos, nextrel0, Bool.and_eq_true,
      decide_eq_true_eq] at hh
    exact hh.1.1.1.2
  have hST : TPS S := by
    apply List.ne_nil_of_length_pos
    simp [S]
    omega
  have hcpos : 0 < c := by simp [c]; omega
  have hc : c ≤ Lng S - 1 := by simp [c, S]; omega
  have hnext0 : nextrel0 N j₀ j₁ = true := by
    simpa [nextR] using hnext
  have hdata := hnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hdata
  have hmin : ∀ r, r < c → entry S 0 c ≤ entry S 0 r := by
    intro r hrc
    have hrS : r < Lng S := by simp [S]; omega
    have hcS : c < Lng S := by simp [c, S]; omega
    rw [entry_seg N a j₁ 0 c hcS,
      entry_seg N a j₁ 0 r hrS]
    have hac : a + c = j₁ := by simp [c, Nat.add_sub_of_le ha₁.le]
    rw [hac]
    have har : j₀ < a + r := by omega
    have harj : a + r < j₁ := by omega
    have hh := hdata.2 (a + r) (List.mem_range.mpr harj)
    simpa [har] using hh
  have hsplit := P_additivity S c hST hcpos hc hmin
  have hleft : seg S 0 (c - 1) = seg N a (j₁ - 1) := by
    have hh := seg_of_seg_68 N a j₁ 0 (c - 1) ha₁.le (by simp [c])
    have hend : a + (c - 1) = j₁ - 1 := by simp [c]; omega
    simpa [S, hend] using hh
  have hright : seg S c (Lng S - 1) = seg N j₁ j₁ := by
    have hh := seg_of_seg_68 N a j₁ c (Lng S - 1) ha₁.le
      (by simp [S]; omega)
    have hstart : a + c = j₁ := by simp [c, Nat.add_sub_of_le ha₁.le]
    have hend : a + (Lng S - 1) = j₁ := by simp [S]; omega
    calc
      seg S c (Lng S - 1) =
          seg N (a + c) (a + (Lng S - 1)) := by simpa [S] using hh
      _ = seg N j₁ j₁ := by rw [hstart, hend]
  have href : le0 N j₁ j₁ = true := by
    simpa [leR] using leR0_refl_68 N j₁ hj₁N
  have hsingle := P_seg_single_of_le0_68 N j₁ j₁ hj₁N
    (le_refl _) href
  rw [hleft, hright, hsingle] at hsplit
  exact hsplit

private theorem entry_diagSeq_68 (u v i j : ℕ)
    (hj : j < Lng (diagSeq u v)) :
    entry (diagSeq u v) i j = u + j := by
  have hget : (diagSeq u v)[j]? = some (u + j, u + j) := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    simp [diagSeq, List.getElem_map, List.getElem_range']
  simp [entry, hget]

private theorem nextR1_consecutive_68 (M : PS) (j : ℕ)
    (hL : j + 1 < Lng M)
    (he0 : entry M 0 j < entry M 0 (j + 1))
    (he1 : entry M 1 j < entry M 1 (j + 1)) :
    nextR M 1 j (j + 1) = true := by
  have hn0 : nextR M 0 j (j + 1) = true := by
    simp only [nextR, if_pos]
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he0⟩, ?_⟩
    intro k hk
    by_cases hjk : j < k
    · have : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk]
  have hleR := nextR0_leR M j (j + 1) hn0
  have hle0 : le0 M j (j + 1) = true := by simpa [leR] using hleR
  simp only [nextR, if_neg (by omega : ¬1 = 0), nextrel1,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by omega, hL⟩, by omega⟩, he1⟩, hle0⟩, ?_⟩
  intro k hk
  by_cases hjk : j < k
  · by_cases hle : le0 M k (j + 1) = true
    · have hkle := le0_index_fseq hle
      have hkeq : k = j + 1 := by omega
      subst k
      simp
    · simp [hjk, hle]
  · simp [hjk]

private theorem TrMax_diagSeq_68 (u v : ℕ) (huv : u ≤ v) :
    TrMax (diagSeq u v) = v - u := by
  have hT : TPS (diagSeq u v) := by
    apply List.ne_nil_of_length_pos
    simp [diagSeq]
    omega
  have hlen : Lng (diagSeq u v) = v - u + 1 := by
    simp [diagSeq]
    omega
  have hlower : v - u ≤ TrMax (diagSeq u v) := by
    apply le_TrMax_intro_wd (diagSeq u v) (v - u) hT
    intro j hj
    apply nextR1_consecutive_68
    · rw [hlen]
      omega
    · rw [entry_diagSeq_68 u v 0 j (by rw [hlen]; omega),
        entry_diagSeq_68 u v 0 (j + 1) (by rw [hlen]; omega)]
      omega
    · rw [entry_diagSeq_68 u v 1 j (by rw [hlen]; omega),
        entry_diagSeq_68 u v 1 (j + 1) (by rw [hlen]; omega)]
      omega
  have hupper := TrMax_bound (diagSeq u v) hT
  rw [hlen] at hupper
  omega

private theorem Br_diagSeq_68 (u v : ℕ) (huv : u ≤ v) :
    Br (diagSeq u v) = [] := by
  have htr := TrMax_diagSeq_68 u v huv
  have hlen : Lng (diagSeq u v) - 1 = v - u := by
    simp [diagSeq]
    omega
  simp [Br, htr, hlen]

private theorem seg_diagSeq_68 (u v a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ v - u) (huv : u ≤ v) :
    seg (diagSeq u v) a b = diagSeq (u + a) (u + b) := by
  apply List.ext_getElem
  · simp [diagSeq]
    omega
  · intro i hiL hiR
    rw [seg_getElem_68 (diagSeq u v) a b i hiL]
    have hai : a + i < Lng (diagSeq u v) := by
      simp [diagSeq]
      simp only [length_seg] at hiL
      omega
    rw [entry_diagSeq_68 u v 0 (a + i) hai,
      entry_diagSeq_68 u v 1 (a + i) hai]
    simp [diagSeq, List.getElem_map, List.getElem_range']
    omega

private theorem rankZero_slice_Br_descending
    (M : PS) (j₀ j₁ : ℕ) (hM : SkTPS 0 M)
    (hlt : j₀ < j₁) (hj₁ : j₁ ≤ Lng M - 1) :
    descending (Br (seg M j₀ j₁)) := by
  rcases hM with ⟨u, v, rfl, huv⟩
  have hj₁uv : j₁ ≤ v - u := by
    simp [diagSeq] at hj₁
    omega
  rw [seg_diagSeq_68 u v j₀ j₁ hlt.le hj₁uv huv,
    Br_diagSeq_68 (u + j₀) (u + j₁) (by omega)]
  exact descending_nil

/-- If the predecessor at rank `k` is multi but its fundamental-sequence
value is mono, that value is exactly the first principal component of the
predecessor and therefore already has rank `k`. -/
private theorem rankSucc_multi_value_rank
    (k : ℕ) (N M : PS) (n : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hmultiN : multiT N = true) (hmonoM : monoT M = true) :
    SkTPS k M := by
  have hNT : TPS N := SkTPS_TPS k N hN
  have hPlen : 1 < (P N).length :=
    (P_components_multi_iff N hNT).mp hmultiN
  have hmultiM : multiT M = false := by
    simp [multiT, hmonoM]
  have hPM : P M = [M] := P_nonmulti_eq M hmultiM
  have hPne : P N ≠ [] := P_nonempty N
  have hlastIdx : (P N).length - 1 < (P N).length := by omega
  have hlastPos := P_component_nonempty N ((P N).length - 1) hNT hlastIdx
  have hlastGet :
      (P N).getLastD [] = (P N).getD ((P N).length - 1) [] :=
    getLastD_eq_getD_last_68 (P N) [] hPne
  have hDpos : 0 < Lng ((P N).getLastD []) := by
    rw [hlastGet]
    exact hlastPos
  have hMP0 : M = (P N).getD 0 [] := by
    by_cases hDone : Lng ((P N).getLastD []) = 1
    · have hrel := P_fseq_1 N n hNT hn hDone
      have hPdrop : P M = (P N).dropLast := by
        have hlenNe : (P N).length ≠ 1 := by omega
        rw [if_neg hlenNe] at hrel
        simpa [hM] using hrel.2
      have hdrop : (P N).dropLast = [M] := hPdrop.symm.trans hPM
      have hdropLen : (P N).dropLast.length = 1 := by rw [hdrop]; simp
      have hzeroDrop : 0 < (P N).dropLast.length := by omega
      have hget : (P N).dropLast.getD 0 [] = M := by rw [hdrop]; simp
      rw [getD_dropLast_68 (P N) [] 0 hzeroDrop] at hget
      exact hget.symm
    · have hDgt : 1 < Lng ((P N).getLastD []) := by omega
      have hrel := P_fseq_2 N n hNT hn hDgt
      have hPappend :
          P M = (P N).dropLast ++ P (oper ((P N).getLastD []) n) := by
        simpa [hM] using hrel.2
      have htailPos : 0 < (P (oper ((P N).getLastD []) n)).length :=
        List.length_pos_of_ne_nil (P_nonempty _)
      have hdropLen : (P N).dropLast.length = (P N).length - 1 := by simp
      have hlenPM := congrArg List.length hPappend
      rw [hPM] at hlenPM
      simp only [List.length_singleton, List.length_append] at hlenPM
      omega
  have hfirst : SkTPS k ((P N).getD 0 []) :=
    SkTPS_P_components k N hN 0 (by omega)
  simpa [hMP0] using hfirst

private theorem rankSucc_nonmulti_prefix
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀ j₁ : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hNlen : 1 < Lng N) (hnmulti : multiT N = false)
    (hlt : j₀ < j₁) (hj₁N : j₁ < Lng N - 1)
    (hj₁M : j₁ ≤ Lng M - 1) (hancM : leR M 0 j₀ j₁ = true) :
    descending (Br (seg M j₀ j₁)) := by
  have hzeroN : zeroT N = false := by
    simp [zeroT]
    omega
  have hmonoN : monoT N = true := by
    simp [multiT, hzeroN] at hnmulti
    exact hnmulti
  have hseg : seg M j₀ j₁ = seg N j₀ j₁ := by
    rw [hM]
    exact seg_oper_eq_68 N n j₀ j₁ hNlen hn hlt.le hj₁N
  have hj₁ML : j₁ < Lng M := by
    have hMT : TPS M := by
      rw [hM]
      exact oper_nonempty_fseq N n (SkTPS_TPS k N hN) hNlen hn
    have := List.length_pos_of_ne_nil hMT
    omega
  have hlocalM :
      leR (seg M j₀ j₁) 0 0 (j₁ - j₀) = true := by
    rw [leR0_seg_adm M j₀ j₁ 0 (j₁ - j₀) hlt.le hj₁ML
      (by simp; omega) (by simp; omega)]
    simpa [Nat.add_sub_of_le hlt.le] using hancM
  have hlocalN :
      leR (seg N j₀ j₁) 0 0 (j₁ - j₀) = true := by
    rw [← hseg]
    exact hlocalM
  have hancN : leR N 0 j₀ j₁ = true := by
    rw [leR0_seg_adm N j₀ j₁ 0 (j₁ - j₀) hlt.le (by omega)
      (by simp; omega) (by simp; omega)] at hlocalN
    simpa [Nat.add_sub_of_le hlt.le] using hlocalN
  rw [hseg]
  exact ih N j₀ j₁ hN hmonoN hlt (by omega) hancN

private theorem rankSucc_multi_predecessor
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀ j₁ : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hmultiN : multiT N = true) (hmonoM : monoT M = true)
    (hlt : j₀ < j₁) (hj₁ : j₁ ≤ Lng M - 1)
    (hanc : leR M 0 j₀ j₁ = true) :
    descending (Br (seg M j₀ j₁)) := by
  exact ih M j₀ j₁
    (rankSucc_multi_value_rank k N M n hN hM hn hmultiN hmonoM)
    hmonoM hlt hj₁ hanc

private theorem reaching_old_end_forces_tiling
    (N M : PS) (n j₁ : ℕ)
    (hM : M = oper N n) (hNlen : 1 < Lng N)
    (hjlarge : Lng N - 1 ≤ j₁) (hjM : j₁ ≤ Lng M - 1) :
    ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) ∧
      hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true := by
  have hlastNe : Lng N - 1 ≠ 0 := by omega
  constructor
  · intro hz
    have hop : oper N n = Pred N := by simp [oper, hlastNe, hz]
    have hML : Lng M = Lng N - 1 := by
      rw [hM, hop, length_Pred N hNlen]
    omega
  · cases hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)
    · have hzero :
          ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0) := by
        intro hz
        have hop : oper N n = Pred N := by simp [oper, hlastNe, hz]
        have hML : Lng M = Lng N - 1 := by
          rw [hM, hop, length_Pred N hNlen]
        omega
      have hop : oper N n = Pred N := by
        simp [oper, hlastNe, hzero, hp]
      have hML : Lng M = Lng N - 1 := by
        rw [hM, hop, length_Pred N hNlen]
      omega
    · rfl

private theorem oper_d0zero_expand_68
    (N : PS) (n : ℕ) (hNlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hd0 : entry N 1 (Lng N - 1) = 0) :
    oper N n =
      let j₁ := Lng N - 1
      let j₀ := parent N 0 j₁
      let B := (List.range' j₀ (j₁ - j₀)).map
        (fun j => (entry N 0 j, entry N 1 j))
      N.take j₀ ++ (List.range n).flatMap (fun _ => B) := by
  have hi : idx1 N (Lng N - 1) = 0 := by simp [idx1, hd0]
  have hexpand := oper_tiling_expand N n hNlen hzero hp
  simpa [hi] using hexpand

private theorem oper_d0zero_le0_confined_68
    (N : PS) (n a b : ℕ) (hNT : TPS N)
    (hNlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (ha : parent N 0 (Lng N - 1) ≤ a)
    (hle : leR (oper N n) 0 a b = true) :
    b < parent N 0 (Lng N - 1) +
      ((a - parent N 0 (Lng N - 1)) /
          (Lng N - 1 - parent N 0 (Lng N - 1)) + 1) *
        (Lng N - 1 - parent N 0 (Lng N - 1)) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let q := (a - j₀) / w
  let B := j₀ + (q + 1) * w
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext := hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hdata := hle
  simp only [leR, if_pos, le0, Bool.and_eq_true,
    decide_eq_true_eq] at hdata
  have haL : a < Lng (oper N n) := hdata.1.1
  have hbL : b < Lng (oper N n) := hdata.1.2
  have hoperT : TPS (oper N n) :=
    List.ne_nil_of_length_pos ((Nat.zero_le a).trans_lt haL)
  have hj₀a : j₀ ≤ a := by simpa [j₀, j₁] using ha
  have hdiv : q * w + (a - j₀) % w = a - j₀ := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_add_mod (a - j₀) w
  have haform : a = j₀ + q * w + (a - j₀) % w := by
    have hsub := Nat.add_sub_of_le hj₀a
    omega
  have hrem : (a - j₀) % w < w := Nat.mod_lt _ hw
  have haB : a < B := by
    simp [B, Nat.add_mul]
    omega
  by_contra hnot
  have hBb : B ≤ b := by
    change ¬b < B at hnot
    omega
  have hBL : B < Lng (oper N n) := hBb.trans_lt hbL
  have hlen : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hNlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  have hq : q + 1 < n := by
    rw [hlen] at hBL
    simp [B, Nat.add_mul] at hBL
    nlinarith
  have hBentry : entry (oper N n) 0 B = entry N 0 j₀ := by
    have hh := entry_oper_tiling_block_zero N n (q + 1) 0
      hNlen hzero hp hq (by
        rw [hi]
        simpa [j₁, j₀, w] using hw)
    rw [hi] at hh
    simpa [B, j₁, j₀, w, Nat.add_assoc] using hh
  have hafloor : entry N 0 j₀ ≤ entry (oper N n) 0 a := by
    have hh := oper_tiling_block_floor N n a hNT hNlen hzero hp
      (by rw [hi]; simpa [j₁, j₀] using ha) haL
    rw [hi] at hh
    simpa [j₁, j₀] using hh
  have hgrowth : entry (oper N n) 0 a < entry (oper N n) 0 B :=
    ancestor_basic_1 (oper N n) a B b hoperT haB hBb hle
  rw [hBentry] at hgrowth
  omega

private theorem oper_d0zero_slice_within_block_68
    (N : PS) (n a b : ℕ) (hNT : TPS N)
    (hNlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (ha : parent N 0 (Lng N - 1) ≤ a)
    (hab : a < b) (hle : leR (oper N n) 0 a b = true) :
    ∃ q s t,
      q < n ∧ s < t ∧ t < Lng N - 1 - parent N 0 (Lng N - 1) ∧
      a = parent N 0 (Lng N - 1) +
        q * (Lng N - 1 - parent N 0 (Lng N - 1)) + s ∧
      b = parent N 0 (Lng N - 1) +
        q * (Lng N - 1 - parent N 0 (Lng N - 1)) + t ∧
      seg (oper N n) a b =
        seg N (parent N 0 (Lng N - 1) + s)
          (parent N 0 (Lng N - 1) + t) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let q := (a - j₀) / w
  let B := j₀ + q * w
  let s := a - B
  let t := b - B
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext := hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hj₀a : j₀ ≤ a := by simpa [j₀, j₁] using ha
  have hdiv : q * w + (a - j₀) % w = a - j₀ := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_add_mod (a - j₀) w
  have haform0 : a = j₀ + q * w + (a - j₀) % w := by
    have hsub := Nat.add_sub_of_le hj₀a
    omega
  have hB_le_a : B ≤ a := by simp [B]; omega
  have hsform : s = (a - j₀) % w := by simp [s, B]; omega
  have haform : a = B + s := by simp [s, Nat.add_sub_of_le hB_le_a]
  have hdata := hle
  simp only [leR, if_pos, le0, Bool.and_eq_true,
    decide_eq_true_eq] at hdata
  have haL : a < Lng (oper N n) := hdata.1.1
  have hlen : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hNlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  have hq : q < n := by
    rw [hlen] at haL
    rw [haform0] at haL
    have hrem : (a - j₀) % w < w := Nat.mod_lt _ hw
    nlinarith
  have hconf := oper_d0zero_le0_confined_68 N n a b hNT hNlen
    hzero hp hi ha hle
  change b < j₀ + (q + 1) * w at hconf
  have hB_le_b : B ≤ b := hB_le_a.trans hab.le
  have hbform : b = B + t := by simp [t, Nat.add_sub_of_le hB_le_b]
  have hst : s < t := by omega
  have ht : t < w := by
    simp [Nat.add_mul] at hconf
    omega
  refine ⟨q, s, t, hq, hst, ?_, ?_, ?_, ?_⟩
  · simpa [j₁, j₀, w] using ht
  · simpa [j₁, j₀, w, B] using haform
  · simpa [j₁, j₀, w, B] using hbform
  · change seg (oper N n) a b = seg N (j₀ + s) (j₀ + t)
    apply List.ext_getElem
    · simp only [length_seg]
      rw [haform, hbform]
      omega
    · intro r hrL hrR
      rw [seg_getElem_68 (oper N n) a b r hrL,
        seg_getElem_68 N (j₀ + s) (j₀ + t) r hrR]
      have hsr : s + r < w := by
        simp only [length_seg] at hrL
        omega
      have hread0 := entry_oper_tiling_block_zero N n q (s + r)
        hNlen hzero hp hq (by rw [hi]; simpa [j₁, j₀, w] using hsr)
      have hread1 := entry_oper_tiling_block_one N n q (s + r)
        hNlen hzero hp hq (by rw [hi]; simpa [j₁, j₀, w] using hsr)
      rw [hi] at hread0 hread1
      have hr0 : entry (oper N n) 0 (j₀ + q * w + (s + r)) =
          entry N 0 (j₀ + (s + r)) := by
        simpa [j₁, j₀, w] using hread0
      have hr1 : entry (oper N n) 1 (j₀ + q * w + (s + r)) =
          entry N 1 (j₀ + (s + r)) := by
        simpa [j₁, j₀, w] using hread1
      have har : a + r = j₀ + q * w + (s + r) := by
        rw [haform]
        simp [B]
        omega
      rw [har, hr0, hr1]
      simp [Nat.add_assoc]

private theorem oper_d0zero_block_seg_68
    (M : PS) (n q s : ℕ)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hq : q < n)
    (hs : s < Lng M - 1 - parent M 0 (Lng M - 1)) :
    seg (oper M n)
        (parent M 0 (Lng M - 1) +
          q * (Lng M - 1 - parent M 0 (Lng M - 1)))
        (parent M 0 (Lng M - 1) +
          q * (Lng M - 1 - parent M 0 (Lng M - 1)) + s) =
      seg M (parent M 0 (Lng M - 1))
        (parent M 0 (Lng M - 1) + s) := by
  let j₁ := Lng M - 1
  let j₀ := parent M 0 j₁
  let w := j₁ - j₀
  let B := j₀ + q * w
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  apply List.ext_getElem
  · simp only [length_seg]
    omega
  · intro r hrL hrR
    rw [seg_getElem_68 (oper M n) B (B + s) r hrL,
      seg_getElem_68 M j₀ (j₀ + s) r hrR]
    have hrs : r ≤ s := by
      simp only [length_seg] at hrL
      omega
    have hrw : r < w := hrs.trans_lt hs'
    have hread0 := entry_oper_tiling_block_zero M n q r hlen hzero hp hq
      (by rw [hi]; simpa [j₁, j₀, w] using hrw)
    have hread1 := entry_oper_tiling_block_one M n q r hlen hzero hp hq
      (by rw [hi]; simpa [j₁, j₀, w] using hrw)
    rw [hi] at hread0 hread1
    simpa [B, j₁, j₀, w, Nat.add_assoc] using
      congrArg₂ Prod.mk hread0 hread1

private theorem oper_d0zero_seg_P_split_68
    (M : PS) (n a k s : ℕ) (hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (ha : parent M 0 (Lng M - 1) < a)
    (haB : a < parent M 0 (Lng M - 1) +
      k * (Lng M - 1 - parent M 0 (Lng M - 1)))
    (hs : s < Lng M - 1 - parent M 0 (Lng M - 1))
    (hend : parent M 0 (Lng M - 1) +
        k * (Lng M - 1 - parent M 0 (Lng M - 1)) + s <
      Lng (oper M n))
    (hk : k < n) :
    P (seg (oper M n) a
        (parent M 0 (Lng M - 1) +
          k * (Lng M - 1 - parent M 0 (Lng M - 1)) + s)) =
      P (seg (oper M n) a
        (parent M 0 (Lng M - 1) +
          k * (Lng M - 1 - parent M 0 (Lng M - 1)) - 1)) ++
        [seg M (parent M 0 (Lng M - 1))
          (parent M 0 (Lng M - 1) + s)] := by
  let j₁ := Lng M - 1
  let j₀ := parent M 0 j₁
  let w := j₁ - j₀
  let B := j₀ + k * w
  let E := B + s
  let Q := seg (oper M n) a E
  let c := B - a
  have hp0 : hasParent M 0 j₁ = true := by
    simpa [j₁, hi] using hp
  have hnext : nextR M 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq M 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  have hend' : E < Lng (oper M n) := by
    simpa [E, B, j₁, j₀, w] using hend
  have haB' : a < B := by simpa [B, j₀, j₁, w] using haB
  have hcpos : 0 < c := by simp [c]; omega
  have haE : a ≤ E := by simp [E, B]; omega
  have hQT : TPS Q := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng Q
    simp [Q]
    omega
  have hQL : Lng Q = E + 1 - a := by simp [Q]
  have hcQ : c ≤ Lng Q - 1 := by rw [hQL]; simp [c, E]; omega
  have hcQL : c < Lng Q := by omega
  have hac : a + c = B := by simp [c, Nat.add_sub_of_le haB'.le]
  have hcutEntry : entry Q 0 c = entry M 0 j₀ := by
    rw [entry_seg (oper M n) a E 0 c hcQL, hac]
    have hread := entry_oper_tiling_block_zero M n k 0 hlen hzero hp hk
      (by rw [hi]; simpa [j₁, j₀, w] using hw)
    rw [hi] at hread
    simpa [B, j₁, j₀, w] using hread
  have hmin : ∀ r, r < c → entry Q 0 c ≤ entry Q 0 r := by
    intro r hrc
    have hrQ : r < Lng Q := hrc.trans hcQL
    rw [hcutEntry, entry_seg (oper M n) a E 0 r hrQ]
    have hj₀ar : j₀ ≤ a + r := by
      have hj₀a : j₀ < a := by simpa [j₀, j₁] using ha
      omega
    have harL : a + r < Lng (oper M n) := by
      have harB : a + r < B := by simp [c] at hrc; omega
      have hBE : B ≤ E := by simp [E]
      exact (harB.trans_le hBE).trans hend'
    have hfloor := oper_tiling_block_floor M n (a + r) hMT hlen
      hzero hp (by rw [hi]; simpa [j₁, j₀] using hj₀ar) harL
    rw [hi] at hfloor
    simpa [j₁, j₀] using hfloor
  have hsplit := P_additivity Q c hQT hcpos hcQ hmin
  have hleft : seg Q 0 (c - 1) = seg (oper M n) a (B - 1) := by
    have hinner := seg_of_seg_68 (oper M n) a E 0 (c - 1)
      haE (by simp [c, E]; omega)
    have hleftEnd : a + (c - 1) = B - 1 := by
      simp [c]
      omega
    simpa [Q, hleftEnd] using hinner
  have hright0 : seg Q c (Lng Q - 1) = seg (oper M n) B E := by
    have hdb : Lng Q - 1 ≤ E - a := by rw [hQL]; omega
    have hinner := seg_of_seg_68 (oper M n) a E c (Lng Q - 1)
      haE hdb
    have hright : a + (Lng Q - 1) = E := by rw [hQL]; omega
    calc
      seg Q c (Lng Q - 1) =
          seg (oper M n) (a + c) (a + (Lng Q - 1)) := by
            simpa [Q] using hinner
      _ = seg (oper M n) B E := by rw [hac, hright]
  have hblock : seg (oper M n) B E = seg M j₀ (j₀ + s) := by
    apply List.ext_getElem
    · simp only [length_seg]
      dsimp [E]
      omega
    · intro r hrL hrR
      rw [seg_getElem_68 (oper M n) B E r hrL,
        seg_getElem_68 M j₀ (j₀ + s) r hrR]
      have hrs : r ≤ s := by
        simp only [length_seg] at hrL
        dsimp [E] at hrL
        omega
      have hrw : r < w := hrs.trans_lt hs'
      have hread0 := entry_oper_tiling_block_zero M n k r hlen hzero hp hk
        (by rw [hi]; simpa [j₁, j₀, w] using hrw)
      have hread1 := entry_oper_tiling_block_one M n k r hlen hzero hp hk
        (by rw [hi]; simpa [j₁, j₀, w] using hrw)
      rw [hi] at hread0 hread1
      simpa [B, j₁, j₀, w, Nat.add_assoc] using congrArg₂ Prod.mk hread0 hread1
  have hleBlock := parent_block_le0_68 M j₀ j₁ s hMT hnext
    (by simpa [w] using hs')
  have hbBlock : j₀ + s < Lng M := by omega
  have hsingle := P_seg_single_of_le0_68 M j₀ (j₀ + s)
    hbBlock (by omega) hleBlock
  rw [hleft, hright0, hblock, hsingle] at hsplit
  simpa [Q, E, B, j₁, j₀, w] using hsplit

private theorem oper_d0zero_seg_P_hfold_68
    (M : PS) (n a m : ℕ) (hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (ha : parent M 0 (Lng M - 1) < a)
    (haend : a ≤ Lng M - 2)
    (hmn : m ≤ n) (hmpos : 1 ≤ m) :
    P (seg (oper M n) a
        (parent M 0 (Lng M - 1) +
          m * (Lng M - 1 - parent M 0 (Lng M - 1)) - 1)) =
      P (seg (oper M n) a (Lng M - 2)) ++
        List.replicate (m - 1)
          (seg M (parent M 0 (Lng M - 1)) (Lng M - 2)) := by
  let j₁ := Lng M - 1
  let j₀ := parent M 0 j₁
  let w := j₁ - j₀
  let O := oper M n
  let blk := seg M j₀ (Lng M - 2)
  have hp0 : hasParent M 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR M 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq M 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hjw : j₀ + w - 1 = Lng M - 2 := by simp [w, j₁]; omega
  have hOL : Lng O = j₀ + n * w := by
    have hh := length_oper_tiling M n hlen hzero hp
    simpa [O, j₁, j₀, w, hi] using hh
  induction m with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        have hend : parent M 0 (Lng M - 1) +
            (Lng M - 1 - parent M 0 (Lng M - 1)) - 1 =
            Lng M - 2 := by
          simpa [j₁, j₀, w] using hjw
        simpa using
          congrArg (fun e => P (seg (oper M n) a e)) hend
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hsrn : r + 1 ≤ n := by omega
        have hrn : r < n := by omega
        have hsw : w - 1 < w := by omega
        have habound : a < j₀ + r * w := by
          have haend' : a ≤ j₀ + w - 1 := by
            simpa [hjw] using haend
          have hmul : w ≤ r * w := by
            simpa using Nat.mul_le_mul_right w hrpos
          omega
        have hBend : j₀ + r * w + (w - 1) < Lng O := by
          rw [hOL]
          have hmul : (r + 1) * w ≤ n * w :=
            Nat.mul_le_mul_right w hsrn
          nlinarith
        have hstep := oper_d0zero_seg_P_split_68 M n a r (w - 1)
          hMT hlen hzero hp hi ha habound
          (by simpa [j₁, j₀, w] using hsw)
          (by simpa [O, j₁, j₀, w] using hBend) hrn
        have hrend : j₀ + r * w + (w - 1) =
            j₀ + (r + 1) * w - 1 := by
          simp [Nat.add_mul]
          omega
        have hblk : seg M j₀ (j₀ + (w - 1)) = blk := by
          congr 2
          omega
        have hih := ih (by omega) hrpos
        have hrepl : List.replicate (r - 1) blk ++ [blk] =
            List.replicate r blk := by
          calc
            List.replicate (r - 1) blk ++ [blk] =
                List.replicate (r - 1) blk ++ List.replicate 1 blk := by simp
            _ = List.replicate ((r - 1) + 1) blk :=
              (List.replicate_add (r - 1) 1 blk).symm
            _ = List.replicate r blk := by congr 2; omega
        rw [hrend, hblk] at hstep
        rw [hstep, hih, List.append_assoc, hrepl]
        simp [blk, j₀, j₁]

private theorem oper_d0zero_seg_P_blk1fold_68
    (M : PS) (n m s : ℕ) (hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hs : s < Lng M - 1 - parent M 0 (Lng M - 1))
    (hmn : m + 1 < n) :
    P (seg (oper M n)
        (parent M 0 (Lng M - 1) +
          (Lng M - 1 - parent M 0 (Lng M - 1)))
        (parent M 0 (Lng M - 1) +
          (m + 1) * (Lng M - 1 - parent M 0 (Lng M - 1)) + s)) =
      List.replicate m
          (seg M (parent M 0 (Lng M - 1)) (Lng M - 2)) ++
        [seg M (parent M 0 (Lng M - 1))
          (parent M 0 (Lng M - 1) + s)] := by
  let j₁ := Lng M - 1
  let j₀ := parent M 0 j₁
  let w := j₁ - j₀
  let a := j₀ + w
  let blk := seg M j₀ (Lng M - 2)
  let part := seg M j₀ (j₀ + s)
  have hp0 : hasParent M 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR M 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq M 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  have hjw : j₀ + w - 1 = Lng M - 2 := by simp [w, j₁]; omega
  induction m generalizing s with
  | zero =>
      have hq : 1 < n := by omega
      have hseg := oper_d0zero_block_seg_68 M n 1 s hlen hzero hp hi hq hs
      have hle := parent_block_le0_68 M j₀ j₁ s hMT hnext hs'
      have hsingle := P_seg_single_of_le0_68 M j₀ (j₀ + s)
        (by omega) (by omega) hle
      have hend : j₀ + (0 + 1) * w + s = a + s := by simp [a]
      simpa [j₁, j₀, w, a, part, hend, hsingle] using
        congrArg P hseg
  | succ r ih =>
      have hrn : r + 2 < n := by omega
      have hr1n : r + 1 < n := by omega
      have habound : a < j₀ + (r + 2) * w := by
        simp [a, Nat.add_mul]
        nlinarith
      have hOL : Lng (oper M n) = j₀ + n * w := by
        have hh := length_oper_tiling M n hlen hzero hp
        simpa [j₁, j₀, w, hi] using hh
      have hendL : j₀ + (r + 2) * w + s < Lng (oper M n) := by
        rw [hOL]
        have hmul : (r + 3) * w ≤ n * w :=
          Nat.mul_le_mul_right w (by omega)
        nlinarith
      have hsplit := oper_d0zero_seg_P_split_68 M n a (r + 2) s
        hMT hlen hzero hp hi (by simp [a]; omega) habound hs hendL hrn
      have hsw : w - 1 < w := by omega
      have hih := ih (s := w - 1)
        (by simpa [j₁, j₀, w] using hsw) hr1n hsw
      have hprefix : j₀ + (r + 1) * w + (w - 1) =
          j₀ + (r + 2) * w - 1 := by
        simp [Nat.add_mul]
        omega
      have hblk : seg M j₀ (j₀ + (w - 1)) = blk := by
        congr 2
        omega
      have hpre : P (seg (oper M n) a (j₀ + (r + 2) * w - 1)) =
          List.replicate (r + 1) blk := by
        rw [← hprefix, hih, hblk]
        calc
          List.replicate r blk ++ [blk] =
              List.replicate r blk ++ List.replicate 1 blk := by simp
          _ = List.replicate (r + 1) blk :=
            (List.replicate_add r 1 blk).symm
      rw [hpre] at hsplit
      simpa [j₁, j₀, w, a, blk, part] using hsplit

private theorem oper_d0zero_seg_P_blk0fold_68
    (M : PS) (n q s : ℕ) (hMT : TPS M)
    (hlen : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧
      entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi : idx1 M (Lng M - 1) = 0)
    (hs : s < Lng M - 1 - parent M 0 (Lng M - 1))
    (hq : q < n) :
    P (seg (oper M n) (parent M 0 (Lng M - 1))
        (parent M 0 (Lng M - 1) +
          q * (Lng M - 1 - parent M 0 (Lng M - 1)) + s)) =
      List.replicate q
          (seg M (parent M 0 (Lng M - 1)) (Lng M - 2)) ++
        [seg M (parent M 0 (Lng M - 1))
          (parent M 0 (Lng M - 1) + s)] := by
  let j₁ := Lng M - 1
  let j₀ := parent M 0 j₁
  let w := j₁ - j₀
  let blk := seg M j₀ (Lng M - 2)
  let part := seg M j₀ (j₀ + s)
  have hp0 : hasParent M 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR M 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq M 0 j₁ hp0
  have hj₀lt : j₀ < j₁ :=
    (nextR_implies_row0 M 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hs' : s < w := by simpa [j₁, j₀, w] using hs
  have hjw : j₀ + w - 1 = Lng M - 2 := by simp [w, j₁]; omega
  induction q with
  | zero =>
      have hn : 0 < n := by omega
      have hseg := oper_d0zero_block_seg_68 M n 0 s hlen hzero hp hi hn hs
      have hle := parent_block_le0_68 M j₀ j₁ s hMT hnext hs'
      have hsingle := P_seg_single_of_le0_68 M j₀ (j₀ + s)
        (by omega) (by omega) hle
      simpa [j₁, j₀, w, part, hsingle] using congrArg P hseg
  | succ r =>
      let E := j₀ + (r + 1) * w + s
      let Q := seg (oper M n) j₀ E
      have hrn : r + 1 < n := by omega
      have h1n : 1 < n := by omega
      have hOL : Lng (oper M n) = j₀ + n * w := by
        have hh := length_oper_tiling M n hlen hzero hp
        simpa [j₁, j₀, w, hi] using hh
      have hEL : E < Lng (oper M n) := by
        rw [hOL]
        have hmul : (r + 2) * w ≤ n * w :=
          Nat.mul_le_mul_right w (by omega)
        dsimp [E]
        nlinarith
      have hjE : j₀ ≤ E := by
        dsimp [E]
        omega
      have hQL : Lng Q = E + 1 - j₀ := by simp [Q]
      have hQT : TPS Q := by
        apply List.ne_nil_of_length_pos
        change 0 < Lng Q
        rw [hQL]
        omega
      have hcQ : w ≤ Lng Q - 1 := by
        rw [hQL]
        have hmul : w ≤ (r + 1) * w := by
          simpa using Nat.mul_le_mul_right w
            (show 1 ≤ r + 1 by omega)
        dsimp [E]
        omega
      have hwQ : w < Lng Q := by omega
      have hcut : entry Q 0 w = entry M 0 j₀ := by
        rw [entry_seg (oper M n) j₀ E 0 w hwQ]
        have hread := entry_oper_tiling_block_zero M n 1 0
          hlen hzero hp h1n
          (by rw [hi]; simpa [j₁, j₀, w] using hw)
        rw [hi] at hread
        simpa [j₁, j₀, w] using hread
      have hmin : ∀ t, t < w → entry Q 0 w ≤ entry Q 0 t := by
        intro t htw
        have htQ : t < Lng Q := htw.trans hwQ
        rw [hcut, entry_seg (oper M n) j₀ E 0 t htQ]
        have hfloor := oper_tiling_block_floor M n (j₀ + t) hMT
          hlen hzero hp (by rw [hi]; simp [j₀, j₁])
          (by exact (by omega : j₀ + t < E).trans hEL)
        rw [hi] at hfloor
        simpa [j₁, j₀] using hfloor
      have hsplit := P_additivity Q w hQT hw hcQ hmin
      have hleft0 : seg Q 0 (w - 1) =
          seg (oper M n) j₀ (j₀ + w - 1) := by
        have hdb : w - 1 ≤ E - j₀ := by
          have hmul : w ≤ (r + 1) * w := by
            simpa using Nat.mul_le_mul_right w
              (show 1 ≤ r + 1 by omega)
          dsimp [E]
          omega
        have hinner := seg_of_seg_68 (oper M n) j₀ E 0 (w - 1)
          hjE hdb
        have heq : j₀ + (w - 1) = j₀ + w - 1 := by omega
        simpa [Q, heq] using hinner
      have hblock0 := oper_d0zero_block_seg_68 M n 0 (w - 1)
        hlen hzero hp hi (by omega)
        (by simpa [j₁, j₀, w] using (show w - 1 < w by omega))
      have hleftSeg : seg Q 0 (w - 1) = blk := by
        have heq : j₀ + (w - 1) = j₀ + w - 1 := by omega
        have hb0 : seg (oper M n) j₀ (j₀ + (w - 1)) =
            seg M j₀ (j₀ + (w - 1)) := by
          simpa [j₁, j₀, w] using hblock0
        calc
          seg Q 0 (w - 1) = seg (oper M n) j₀ (j₀ + w - 1) := hleft0
          _ = seg (oper M n) j₀ (j₀ + (w - 1)) := by rw [heq]
          _ = seg M j₀ (j₀ + (w - 1)) := hb0
          _ = blk := by simp [blk, hjw, heq]
      have hleBlk := parent_block_le0_68 M j₀ j₁ (w - 1)
        hMT hnext (by omega)
      have hPblk : P blk = [blk] := by
        have hh := P_seg_single_of_le0_68 M j₀ (j₀ + (w - 1))
          (by omega) (by omega) hleBlk
        have heq : j₀ + (w - 1) = Lng M - 2 := by omega
        simpa [blk, heq] using hh
      have hright0 : seg Q w (Lng Q - 1) =
          seg (oper M n) (j₀ + w) E := by
        have hdb : Lng Q - 1 ≤ E - j₀ := by rw [hQL]; omega
        have hinner := seg_of_seg_68 (oper M n) j₀ E w (Lng Q - 1)
          hjE hdb
        have hend : j₀ + (Lng Q - 1) = E := by rw [hQL]; omega
        calc
          seg Q w (Lng Q - 1) =
              seg (oper M n) (j₀ + w) (j₀ + (Lng Q - 1)) := by
                simpa [Q] using hinner
          _ = seg (oper M n) (j₀ + w) E := by rw [hend]
      have hrightP := oper_d0zero_seg_P_blk1fold_68 M n r s hMT
        hlen hzero hp hi hs hrn
      rw [hleftSeg, hPblk, hright0, hrightP] at hsplit
      simpa [Q, E, j₁, j₀, w, blk, part, List.replicate_succ]
        using hsplit

private theorem rankSucc_d0zero_within_block
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀' j₁' : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hNlen : 1 < Lng N) (hnmulti : multiT N = false)
    (hd0 : entry N 1 (Lng N - 1) = 0)
    (hstart : parent N 0 (Lng N - 1) ≤ j₀')
    (hlt : j₀' < j₁') (hj₁M : j₁' ≤ Lng M - 1)
    (hjlarge : Lng N - 1 ≤ j₁')
    (hancM : leR M 0 j₀' j₁' = true) :
    descending (Br (seg M j₀' j₁')) := by
  have hNT : TPS N := SkTPS_TPS k N hN
  have htiling := reaching_old_end_forces_tiling N M n j₁'
    hM hNlen hjlarge hj₁M
  rcases htiling with ⟨hzero, hp⟩
  have hi : idx1 N (Lng N - 1) = 0 := by simp [idx1, hd0]
  have hancOper : leR (oper N n) 0 j₀' j₁' = true := by
    rw [← hM]
    exact hancM
  rcases oper_d0zero_slice_within_block_68 N n j₀' j₁' hNT
      hNlen hzero hp hi hstart hlt hancOper with
    ⟨q, s, t, hq, hst, ht, ha, hb, hsliceOper⟩
  let a := parent N 0 (Lng N - 1) + s
  let b := parent N 0 (Lng N - 1) + t
  have hab : a < b := by simp [a, b]; omega
  have hbN : b < Lng N := by simp [a, b] at hab ⊢; omega
  have hslice : seg M j₀' j₁' = seg N a b := by
    rw [hM]
    simpa [a, b] using hsliceOper
  have hMT : TPS M := by
    rw [hM]
    exact oper_TPS N n hNT hn
  have hj₁ML : j₁' < Lng M := by
    have hpos := List.length_pos_of_ne_nil hMT
    omega
  have hlocal :
      leR (seg M j₀' j₁') 0 0 (j₁' - j₀') = true := by
    rw [leR0_seg_adm M j₀' j₁' 0 (j₁' - j₀') hlt.le hj₁ML
      (by simp; omega) (by simp; omega)]
    simpa [Nat.add_sub_of_le hlt.le] using hancM
  rw [hslice] at hlocal
  have hlenEq : b - a = j₁' - j₀' := by
    have hh := congrArg Lng hslice
    simp only [length_seg] at hh
    omega
  have hancN : leR N 0 a b = true := by
    have hshift := leR0_seg_adm N a b 0 (b - a) hab.le hbN
      (by simp; omega) (by simp; omega)
    have hlocal' : leR (seg N a b) 0 0 (b - a) = true := by
      simpa [hlenEq] using hlocal
    rw [hshift] at hlocal'
    simpa [Nat.add_sub_of_le hab.le] using hlocal'
  have hzeroN : zeroT N = false := by simp [zeroT]; omega
  have hmonoN : monoT N = true := by
    simp [multiT, hzeroN] at hnmulti
    exact hnmulti
  rw [hslice]
  exact ih N a b hN hmonoN hab (by omega) hancN

private theorem rankSucc_d0zero_straddle_caseA_68
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀' j₁' : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hlen : 1 < Lng N) (hnmulti : multiT N = false)
    (hd0 : entry N 1 (Lng N - 1) = 0)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hlt : j₀' < j₁') (hj₁M : j₁' ≤ Lng M - 1)
    (hjlarge : Lng N - 1 ≤ j₁')
    (hancM : leR M 0 j₀' j₁' = true)
    (hcaseA : parent N 0 (Lng N - 1) - j₀' ≤
      TrMax (seg N j₀' (Lng N - 1))) :
    descending (Br (seg M j₀' j₁')) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let Np := seg N j₀' j₁
  let Mp := seg M j₀' j₁'
  let t := TrMax Np
  let a := j₀' + t + 1
  have hNT : TPS N := SkTPS_TPS k N hN
  have hMT : TPS M := by
    rw [hM]
    exact oper_TPS N n hNT hn
  have hj₁ML : j₁' < Lng M := by
    have := List.length_pos_of_ne_nil hMT
    omega
  have htiling := reaching_old_end_forces_tiling N M n j₁'
    hM hlen hjlarge hj₁M
  rcases htiling with ⟨hzero, hp⟩
  have hi : idx1 N j₁ = 0 := by simpa [j₁, idx1, hd0]
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR N 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ := (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hj₀'j₁ : j₀' < j₁ := hstart.trans hj₀lt
  have hj₁le : j₁ ≤ j₁' := by simpa [j₁] using hjlarge
  have hw : 0 < w := by simp [w]; omega
  have hj₀j₁' : j₀ ≤ j₁' := hj₀lt.le.trans hj₁le
  have hancPrefixM : leR M 0 j₀' j₀ = true :=
    ancestor_tree_1 M j₀' j₀ j₁' hMT hancM hstart.le hj₀j₁'
  have hsegPrefix : seg M j₀' j₀ = seg N j₀' j₀ := by
    rw [hM]
    exact seg_oper_eq_68 N n j₀' j₀ hlen hn hstart.le (by
      dsimp [j₀, j₁]
      omega)
  have hj₀M : j₀ < Lng M := hj₀j₁'.trans_lt hj₁ML
  have hj₀N : j₀ < Lng N := hj₀lt.trans (by simp [j₁]; omega)
  have hancPrefixN : leR N 0 j₀' j₀ = true :=
    leR0_transfer_seg_eq_68 M N j₀' j₀ hstart hj₀M hj₀N
      hsegPrefix hancPrefixM
  have hancEndN : leR N 0 j₀' j₁ = true :=
    row0_transitive N j₀' j₀ j₁ hNT hancPrefixN
      (nextR0_leR N j₀ j₁ hnext)
  have hzeroN : zeroT N = false := by simp [zeroT]; omega
  have hmonoN : monoT N = true := by
    simp [multiT, hzeroN] at hnmulti
    exact hnmulti
  have hdescNp : descending (Br Np) := by
    simpa [Np, j₁] using ih N j₀' (Lng N - 1) hN hmonoN
      (by simpa [j₁] using hj₀'j₁)
      (le_refl _) (by simpa [j₁] using hancEndN)
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    exact hj₀'j₁.le
  have hNpLen : 1 < Lng Np := by
    simp [Np]
    omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hb : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hb]
    have heq : j₀' + (Lng Np - 1) = j₁ := by
      simp [Np]
      omega
    rw [heq]
    simpa [j₁] using hd0
  have htLast : t < Lng Np - 1 :=
    TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
  have hj₀a : j₀ < a := by
    dsimp [j₀, j₁, a, t, Np] at hcaseA ⊢
    omega
  have haj₁ : a ≤ j₁ := by
    dsimp [a, t]
    simp [Np] at htLast
    omega
  have hj₁Oper : j₁' < Lng (oper N n) := by rwa [← hM]
  have hTrEq : TrMax Mp = t := by
    have hh := TrMax_seg_oper_d0zero_eq_caseA_68 N n j₀' j₁'
      hNT hlen hzero hp (by simpa [j₁] using hi) hn
      (by simpa [j₀, j₁] using hstart)
      (by simpa [j₁] using (show Lng N - 2 ≤ j₁' by omega)) hj₁Oper
    simpa [Mp, Np, t, j₁, hM] using hh
  have hTrNpNe : t ≠ Lng Np - 1 := by omega
  have hBrNp : Br Np = P (seg N a j₁) := by
    have hne : TrMax (seg N j₀' j₁) ≠
        Lng (seg N j₀' j₁) - 1 := by
      simpa [Np, t] using hTrNpNe
    have hh := Br_seg_reshape_68 N j₀' j₁
      hj₀'j₁ (by simp [j₁]; omega) hne
    simpa [Np, t, a, Nat.add_assoc] using hh
  have hTrMpLt : TrMax Mp < Lng Mp - 1 := by
    rw [hTrEq]
    have htCoord : t < j₁ - j₀' := by
      simp [Np] at htLast
      omega
    have hlenMp : Lng Mp - 1 = j₁' - j₀' := by simp [Mp]; omega
    rw [hlenMp]
    omega
  have hBrMp : Br Mp = P (seg M a j₁') := by
    have hh := Br_seg_reshape_68 M j₀' j₁' hlt hj₁ML
      (by simpa [Mp] using (ne_of_lt hTrMpLt))
    rw [hTrEq] at hh
    simpa [Mp, t, a, Nat.add_assoc] using hh
  have hOL : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  let q := (j₁' - j₀) / w
  let r := (j₁' - j₀) % w
  have hj₀le : j₀ ≤ j₁' := hj₀j₁'
  have hdiv : q * w + r = j₁' - j₀ := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod (j₁' - j₀) w
  have hj₁split : j₁' = j₀ + q * w + r := by omega
  have hr : r < w := Nat.mod_lt _ hw
  have hqpos : 1 ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le hw]
    have hj₁eq : j₁ = j₀ + w := by simp [w]; omega
    simp only [one_mul]
    omega
  have hqn : q < n := by
    have hdiff : j₁' - j₀ < n * w := by
      rw [hOL] at hj₁Oper
      omega
    dsimp [q]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hdiff)
  let blk := seg N j₀ (Lng N - 2)
  let part := seg N j₀ (j₀ + r)
  have hblkPos : 0 < Lng blk := by simp [blk]; omega
  have hpartPos : 0 < Lng part := by simp [part]
  have hblk₀ : entry blk 0 0 = entry N 0 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 0 0 hblkPos
  have hblk₁ : entry blk 1 0 = entry N 1 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 1 0 hblkPos
  have hpart₀ : entry part 0 0 = entry N 0 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 0 0 hpartPos
  have hpart₁ : entry part 1 0 = entry N 1 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 1 0 hpartPos
  by_cases haSmall : a < j₁
  · let X := P (seg N a (Lng N - 2))
    let Y := List.replicate (q - 1) blk ++ [part]
    have hprefixSeg : seg (oper N n) a (Lng N - 2) =
        seg N a (Lng N - 2) :=
      seg_oper_eq_68 N n a (Lng N - 2) hlen hn (by omega) (by omega)
    have hterminal := P_terminal_split_above_parent_68 N j₀ j₁ a
      hNT hnext hj₀a haSmall
    have hXdef : X = P (seg N a (j₁ - 1)) := by
      have heq : j₁ - 1 = Lng N - 2 := by simp [j₁]; omega
      rw [heq]
    have hdescAppend : descending (X ++ [seg N j₁ j₁]) := by
      rw [hXdef]
      rw [← hterminal, ← hBrNp]
      exact hdescNp
    have hXdesc : descending X := by
      have hh := descending_take hdescAppend X.length
      simpa [X] using hh
    have haend : a ≤ Lng N - 2 := by dsimp [j₁] at haSmall; omega
    have hfoldmid := oper_d0zero_seg_P_hfold_68 N n a q hNT hlen
      hzero hp (by simpa [j₁] using hi)
      (by simpa [j₀, j₁] using hj₀a) haend hqn.le hqpos
    have haB : a < j₀ + q * w := by
      have hj₁eq : j₁ = j₀ + w := by simp [w]; omega
      have hwle : w ≤ q * w := by
        simpa using Nat.mul_le_mul_right w hqpos
      omega
    have hsplit := oper_d0zero_seg_P_split_68 N n a q r hNT hlen
      hzero hp (by simpa [j₁] using hi)
      (by simpa [j₀, j₁] using hj₀a)
      (by simpa [j₀, j₁, w] using haB)
      (by simpa [j₀, j₁, w] using hr)
      (by simpa [j₀, j₁, w, hj₁split] using hj₁Oper) hqn
    have hsplit' :
        P (seg (oper N n) a (j₀ + q * w + r)) =
          P (seg (oper N n) a (j₀ + q * w - 1)) ++ [part] := by
      simpa [j₀, j₁, w, part] using hsplit
    have hfoldmid' :
        P (seg (oper N n) a (j₀ + q * w - 1)) =
          P (seg (oper N n) a (Lng N - 2)) ++
            List.replicate (q - 1) blk := by
      simpa [j₀, j₁, w, blk] using hfoldmid
    have hfold : P (seg M a j₁') = X ++ Y := by
      rw [hM, hj₁split]
      rw [hsplit', hfoldmid', congrArg P hprefixSeg]
      simp only [X, Y, List.append_assoc]
    have hYheads := replicate_append_heads_68 (q - 1) blk part
      (entry N 0 j₀) (entry N 1 j₀) hblk₀ hblk₁ hpart₀ hpart₁
    have hYdesc : descending Y := by
      apply descending_const_head
      simpa [Y] using hYheads
    have hnext0 : nextrel0 N j₀ j₁ = true := by simpa [nextR] using hnext
    have hndata := hnext0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hndata
    have hleafAll : ∀ i, i < Lng (seg N a (Lng N - 2)) →
        entry N 0 j₁ ≤ entry (seg N a (Lng N - 2)) 0 i := by
      intro i hiX
      rw [entry_seg N a (Lng N - 2) 0 i hiX]
      have hailt : a + i < j₁ := by
        simp only [length_seg] at hiX
        dsimp [j₁]
        omega
      have hja : j₀ < a + i := by omega
      have hh := hndata.2 (a + i) (List.mem_range.mpr hailt)
      simpa [hja] using hh
    have hXne : X ≠ [] := P_nonempty _
    have hXlast : entry N 0 j₁ ≤
        entry (X.getD (X.length - 1) []) 0 0 := by
      exact P_component_head_ge_68 (seg N a (Lng N - 2)) (entry N 0 j₁)
        (X.length - 1) (by
          apply List.ne_nil_of_length_pos
          simp
          omega) (by simp [X]; exact List.length_pos_of_ne_nil hXne)
        hleafAll
    have hYne : Y ≠ [] := by simp [Y]
    have hYzero : entry (Y.getD 0 []) 0 0 = entry N 0 j₀ := by
      exact (hYheads 0 (by simp)).1
    have hjunc0 : entry N 0 j₀ < entry N 0 j₁ := by
      exact hndata.1.2
    have hjunc : cdom (X.getD (X.length - 1) []) (Y.getD 0 []) := by
      rw [cdom, hYzero]
      constructor
      · omega
      · intro heq
        omega
    have hXY := descending_append hXdesc hYdesc
      (fun _ _ => hjunc)
    rw [hfold] at hBrMp
    rw [hBrMp]
    exact hXY
  · have haeq : a = j₁ := by omega
    let Y := List.replicate (q - 1) blk ++ [part]
    have hqm : (q - 1) + 1 = q := by omega
    have hfold0 := oper_d0zero_seg_P_blk1fold_68 N n (q - 1) r hNT
      hlen hzero hp (by simpa [j₁] using hi)
      (by simpa [j₀, j₁, w] using hr)
      (by simpa [hqm] using hqn)
    have hfold0' :
        P (seg (oper N n) (j₀ + w) (j₀ + q * w + r)) = Y := by
      simpa [j₀, j₁, w, hqm, blk, part, Y] using hfold0
    have hfold : P (seg M a j₁') = Y := by
      rw [hM, haeq, hj₁split]
      have hj₁eq : j₁ = j₀ + w := by simp [w]; omega
      rw [hj₁eq]
      exact hfold0'
    have hYheads := replicate_append_heads_68 (q - 1) blk part
      (entry N 0 j₀) (entry N 1 j₀) hblk₀ hblk₁ hpart₀ hpart₁
    have hYdesc : descending Y := by
      apply descending_const_head
      simpa [Y] using hYheads
    rw [hfold] at hBrMp
    rw [hBrMp]
    exact hYdesc

private theorem d0zero_Br_descending_branch_at_parent_68
    (N : PS) (n j₀' j₁' : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (hn : 1 ≤ n)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hlt : j₀' < j₁')
    (hbge : Lng N - 1 ≤ j₁')
    (hend : j₁' < Lng (oper N n))
    (haeq : j₀' + TrMax (seg N j₀' (Lng N - 1)) + 1 =
      parent N 0 (Lng N - 1)) :
    descending (Br (seg (oper N n) j₀' j₁')) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let Np := seg N j₀' j₁
  let Mp := seg (oper N n) j₀' j₁'
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR N 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ := (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hj₀'j₁ : j₀' < j₁ := hstart.trans hj₀lt
  have hTrEq : TrMax Mp = TrMax Np := by
    have hh := TrMax_seg_oper_d0zero_eq_caseA_68 N n j₀' j₁'
      hNT hlen hzero hp hi hn hstart (by omega) hend
    simpa [Mp, Np, j₁] using hh
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    exact hj₀'j₁.le
  have hNpLen : 1 < Lng Np := by simp [Np]; omega
  have hd0 : entry N 1 j₁ = 0 := by
    by_cases hpos : 0 < entry N 1 j₁
    · have hone : idx1 N j₁ = 1 := by simp [idx1, hpos]
      rw [hone] at hi
      omega
    · omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hb : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hb]
    have heq : j₀' + (Lng Np - 1) = j₁ := by simp [Np]; omega
    rw [heq, hd0]
  have htLast := TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
  have hTrMpLt : TrMax Mp < Lng Mp - 1 := by
    rw [hTrEq]
    have htCoord : TrMax Np < j₁ - j₀' := by
      have hlenEq : Lng Np - 1 = j₁ - j₀' := by
        simp [Np]
        omega
      rw [hlenEq] at htLast
      exact htLast
    have hlenMp : Lng Mp - 1 = j₁' - j₀' := by simp [Mp]; omega
    rw [hlenMp]
    have hj₁le : j₁ ≤ j₁' := by simpa [j₁] using hbge
    omega
  have hBr : Br Mp = P (seg (oper N n) j₀ j₁') := by
    have hh := Br_seg_reshape_68 (oper N n) j₀' j₁' hlt hend
      (by simpa [Mp] using ne_of_lt hTrMpLt)
    rw [hTrEq] at hh
    have haeq' : j₀' + TrMax Np + 1 = j₀ := by
      simpa [Np, j₀, j₁] using haeq
    simpa [Mp, haeq'] using hh
  have hOL : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  let q := (j₁' - j₀) / w
  let r := (j₁' - j₀) % w
  have hj₀le : j₀ ≤ j₁' := by
    have : j₁ ≤ j₁' := by simpa [j₁] using hbge
    omega
  have hdiv : q * w + r = j₁' - j₀ := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod (j₁' - j₀) w
  have hj₁split : j₁' = j₀ + q * w + r := by omega
  have hr : r < w := Nat.mod_lt _ hw
  have hqn : q < n := by
    have hdiff : j₁' - j₀ < n * w := by rw [hOL] at hend; omega
    dsimp [q]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hdiff)
  let blk := seg N j₀ (Lng N - 2)
  let part := seg N j₀ (j₀ + r)
  let Y := List.replicate q blk ++ [part]
  have hfold0 := oper_d0zero_seg_P_blk0fold_68 N n q r hNT hlen
    hzero hp hi (by simpa [j₀, j₁, w] using hr) hqn
  have hfold : P (seg (oper N n) j₀ j₁') = Y := by
    rw [hj₁split]
    simpa [j₀, j₁, w, blk, part, Y] using hfold0
  have hblkPos : 0 < Lng blk := by simp [blk]; omega
  have hpartPos : 0 < Lng part := by simp [part]
  have hblk₀ : entry blk 0 0 = entry N 0 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 0 0 hblkPos
  have hblk₁ : entry blk 1 0 = entry N 1 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 1 0 hblkPos
  have hpart₀ : entry part 0 0 = entry N 0 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 0 0 hpartPos
  have hpart₁ : entry part 1 0 = entry N 1 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 1 0 hpartPos
  have hheads := replicate_append_heads_68 q blk part
    (entry N 0 j₀) (entry N 1 j₀) hblk₀ hblk₁ hpart₀ hpart₁
  have hYdesc : descending Y := by
    apply descending_const_head
    simpa [Y] using hheads
  rw [hfold] at hBr
  rw [hBr]
  exact hYdesc

private theorem d0zero_Br_descending_caseB_68
    (N : PS) (n j₀' j₁' : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (hn : 1 ≤ n)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hlt : j₀' < j₁')
    (hbge : Lng N - 1 ≤ j₁')
    (hend : j₁' < Lng (oper N n))
    (hancN : leR N 0 j₀' (Lng N - 1) = true)
    (hdescNp : descending (Br (seg N j₀' (Lng N - 1))))
    (ha : j₀' + TrMax (seg N j₀' (Lng N - 1)) + 1 <
      parent N 0 (Lng N - 1))
    (hcaseB : parent (seg N j₀' (Lng N - 1)) 0
      (parent N 0 (Lng N - 1) - j₀') ≤
        TrMax (seg N j₀' (Lng N - 1))) :
    descending (Br (seg (oper N n) j₀' j₁')) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let w := j₁ - j₀
  let Np := seg N j₀' j₁
  let Mp := seg (oper N n) j₀' j₁'
  let t := TrMax Np
  let a := j₀' + t + 1
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR N 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ := (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hw : 0 < w := by simp [w]; omega
  have hj₀'j₁ : j₀' < j₁ := hstart.trans hj₀lt
  have haj₀ : a < j₀ := by simpa [a, t, Np, j₀, j₁] using ha
  have hancN' : leR N 0 j₀' j₁ = true := by simpa [j₁] using hancN
  have hancJ₀ := ancestor_tree_1 N j₀' j₀ j₁ hNT hancN'
    hstart.le hj₀lt.le
  have hentry : entry N 0 j₀' < entry N 0 j₀ :=
    ancestor_basic_1 N j₀' j₀ j₀ hNT hstart (le_refl _) hancJ₀
  have hj₀N : j₀ < Lng N := hj₀lt.trans (by simp [j₁]; omega)
  obtain ⟨p, hpge, hplt, hpnext⟩ :=
    parent_exists_1 N j₀' j₀ hNT hstart hj₀N hentry
  have hpNp : p - j₀' < Lng Np := by simp [Np]; omega
  have hj₀Np : j₀ - j₀' < Lng Np := by simp [Np]; omega
  have hpLocal : nextR Np 0 (p - j₀') (j₀ - j₀') = true := by
    rw [nextR_seg_adm N j₀' j₁ 0 (p - j₀') (j₀ - j₀')
      hj₀'j₁.le (by simp [j₁]; omega) hpNp hj₀Np]
    have heqp : j₀' + (p - j₀') = p := Nat.add_sub_of_le hpge
    have heqj : j₀' + (j₀ - j₀') = j₀ :=
      Nat.add_sub_of_le hstart.le
    simpa [heqp, heqj] using hpnext
  have hparLocal : parent Np 0 (j₀ - j₀') = p - j₀' :=
    parent_eq_of_nextR0 Np (p - j₀') (j₀ - j₀') hpLocal
  have hpltA : p < a := by
    have hh : p - j₀' ≤ t := by
      simpa [Np, t, j₀, j₁, hparLocal] using hcaseB
    omega
  have hpnext0 : nextrel0 N p j₀ = true := by simpa [nextR] using hpnext
  have hpdata := hpnext0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hpdata
  have hleftmin : ∀ x, a ≤ x → x < j₀ → entry N 0 j₀ ≤ entry N 0 x := by
    intro x hax hxj
    have hpx : p < x := hpltA.trans_le hax
    have hh := hpdata.2 x (List.mem_range.mpr hxj)
    simpa [hpx] using hh
  have hTrEq : TrMax Mp = t := by
    have hh := TrMax_seg_oper_d0zero_eq_caseA_68 N n j₀' j₁'
      hNT hlen hzero hp hi hn hstart (by omega) hend
    simpa [Mp, Np, t, j₁] using hh
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    exact hj₀'j₁.le
  have hNpLen : 1 < Lng Np := by simp [Np]; omega
  have hd0 : entry N 1 j₁ = 0 := by
    by_cases hpos : 0 < entry N 1 j₁
    · have hone : idx1 N j₁ = 1 := by simp [idx1, hpos]
      rw [hone] at hi
      omega
    · omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hb : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hb]
    have heq : j₀' + (Lng Np - 1) = j₁ := by simp [Np]; omega
    rw [heq, hd0]
  have htLast := TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
  have hTrMpLt : TrMax Mp < Lng Mp - 1 := by
    rw [hTrEq]
    have htCoord : t < j₁ - j₀' := by
      have heq : Lng Np - 1 = j₁ - j₀' := by simp [Np]; omega
      rw [heq] at htLast
      exact htLast
    have hlenMp : Lng Mp - 1 = j₁' - j₀' := by simp [Mp]; omega
    rw [hlenMp]
    have hj₁le : j₁ ≤ j₁' := by simpa [j₁] using hbge
    omega
  have hBrM : Br Mp = P (seg (oper N n) a j₁') := by
    have hh := Br_seg_reshape_68 (oper N n) j₀' j₁' hlt hend
      (by simpa [Mp] using ne_of_lt hTrMpLt)
    rw [hTrEq] at hh
    simpa [Mp, a, t, Nat.add_assoc] using hh
  have hBrN : Br Np = P (seg N a j₁) := by
    have hne : TrMax Np ≠ Lng Np - 1 := by omega
    have hh := Br_seg_reshape_68 N j₀' j₁ hj₀'j₁
      (by simp [j₁]; omega) (by simpa [Np] using hne)
    simpa [Np, a, t, Nat.add_assoc] using hh
  have hNbrSplit := P_seg_split_at_68 N a j₀ j₁ hNT haj₀
    hj₀lt.le (by simp [j₁]; omega) hleftmin
  have hOperT : TPS (oper N n) := oper_TPS N n hNT hn
  have hMleftmin : ∀ x, a ≤ x → x < j₀ →
      entry (oper N n) 0 j₀ ≤ entry (oper N n) 0 x := by
    intro x hax hxj
    rw [entry_oper_lt_last_68 N n 0 j₀ hlen hn (Or.inl rfl) (by
        simpa [j₀, j₁] using hj₀lt),
      entry_oper_lt_last_68 N n 0 x hlen hn (Or.inl rfl) (by
        have hxlast : x < j₁ := hxj.trans hj₀lt
        simpa [j₁] using hxlast)]
    exact hleftmin x hax hxj
  have hj₀leEnd : j₀ ≤ j₁' := by
    have : j₁ ≤ j₁' := by simpa [j₁] using hbge
    omega
  have hMsplit := P_seg_split_at_68 (oper N n) a j₀ j₁' hOperT haj₀
    hj₀leEnd hend hMleftmin
  have hlowSeg : seg (oper N n) a (j₀ - 1) = seg N a (j₀ - 1) :=
    seg_oper_eq_68 N n a (j₀ - 1) hlen hn (by omega) (by
      have hh : j₀ - 1 < j₁ := by omega
      simpa [j₁] using hh)
  have hOL : Lng (oper N n) = j₀ + n * w := by
    have hh := length_oper_tiling N n hlen hzero hp
    simpa [j₁, j₀, w, hi] using hh
  let q := (j₁' - j₀) / w
  let r := (j₁' - j₀) % w
  have hdiv : q * w + r = j₁' - j₀ := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod (j₁' - j₀) w
  have hj₁split : j₁' = j₀ + q * w + r := by omega
  have hr : r < w := Nat.mod_lt _ hw
  have hqn : q < n := by
    have hdiff : j₁' - j₀ < n * w := by rw [hOL] at hend; omega
    dsimp [q]
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hdiff)
  let LOW := P (seg N a (j₀ - 1))
  let HIGH := P (seg N j₀ j₁)
  let blk := seg N j₀ (Lng N - 2)
  let part := seg N j₀ (j₀ + r)
  let Y := List.replicate q blk ++ [part]
  have hhighFold0 := oper_d0zero_seg_P_blk0fold_68 N n q r hNT hlen
    hzero hp hi (by simpa [j₀, j₁, w] using hr) hqn
  have hhighFold : P (seg (oper N n) j₀ j₁') = Y := by
    rw [hj₁split]
    simpa [j₀, j₁, w, blk, part, Y] using hhighFold0
  have hNbr : Br Np = LOW ++ HIGH := by
    rw [hBrN, hNbrSplit]
  have hMbr : Br Mp = LOW ++ Y := by
    rw [hBrM, hMsplit, congrArg P hlowSeg, hhighFold]
  have hLOWdesc : descending LOW := by
    have hh : descending (LOW ++ HIGH) := by
      rw [← hNbr]
      simpa [Np, j₁] using hdescNp
    have ht := descending_take hh LOW.length
    simpa [LOW] using ht
  have hblkPos : 0 < Lng blk := by simp [blk]; omega
  have hpartPos : 0 < Lng part := by simp [part]
  have hblk₀ : entry blk 0 0 = entry N 0 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 0 0 hblkPos
  have hblk₁ : entry blk 1 0 = entry N 1 j₀ := by
    simpa [blk] using entry_seg N j₀ (Lng N - 2) 1 0 hblkPos
  have hpart₀ : entry part 0 0 = entry N 0 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 0 0 hpartPos
  have hpart₁ : entry part 1 0 = entry N 1 j₀ := by
    simpa [part] using entry_seg N j₀ (j₀ + r) 1 0 hpartPos
  have hYheads := replicate_append_heads_68 q blk part
    (entry N 0 j₀) (entry N 1 j₀) hblk₀ hblk₁ hpart₀ hpart₁
  have hYdesc : descending Y := by
    apply descending_const_head
    simpa [Y] using hYheads
  have hLOWne : LOW ≠ [] := P_nonempty _
  have hHIGHne : HIGH ≠ [] := P_nonempty _
  have hJoinN : cdom (LOW.getD (LOW.length - 1) []) (HIGH.getD 0 []) := by
    apply descending_append_junction_68
    · rw [← hNbr]
      simpa [Np, j₁] using hdescNp
    · exact hLOWne
    · exact hHIGHne
  have hSHighT : TPS (seg N j₀ j₁) := by
    apply List.ne_nil_of_length_pos
    simp
    omega
  have hHigh₀ : entry (HIGH.getD 0 []) 0 0 = entry N 0 j₀ := by
    rw [P_first_component_head_68 (seg N j₀ j₁) 0 hSHighT]
    have hpos : 0 < Lng (seg N j₀ j₁) := by simp; omega
    simpa using entry_seg N j₀ j₁ 0 0 hpos
  have hHigh₁ : entry (HIGH.getD 0 []) 1 0 = entry N 1 j₀ := by
    rw [P_first_component_head_68 (seg N j₀ j₁) 1 hSHighT]
    have hpos : 0 < Lng (seg N j₀ j₁) := by simp; omega
    simpa using entry_seg N j₀ j₁ 1 0 hpos
  have hY₀ : entry (Y.getD 0 []) 0 0 = entry N 0 j₀ :=
    (hYheads 0 (by simp)).1
  have hY₁ : entry (Y.getD 0 []) 1 0 = entry N 1 j₀ :=
    (hYheads 0 (by simp)).2
  have hJoin : cdom (LOW.getD (LOW.length - 1) []) (Y.getD 0 []) := by
    rw [cdom] at hJoinN ⊢
    rw [hHigh₀, hHigh₁] at hJoinN
    rw [hY₀, hY₁]
    exact hJoinN
  have hAll := descending_append hLOWdesc hYdesc (fun _ _ => hJoin)
  rw [hMbr]
  exact hAll

private theorem d0zero_Br_descending_caseC_68
    (N : PS) (n j₀' j₁' : ℕ)
    (hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 0)
    (hn : 1 ≤ n)
    (hstart : j₀' < parent N 0 (Lng N - 1))
    (hlt : j₀' < j₁')
    (hbge : Lng N - 1 ≤ j₁')
    (hend : j₁' < Lng (oper N n))
    (hancN : leR N 0 j₀' (Lng N - 1) = true)
    (hdescNp : descending (Br (seg N j₀' (Lng N - 1))))
    (ha : j₀' + TrMax (seg N j₀' (Lng N - 1)) + 1 <
      parent N 0 (Lng N - 1))
    (hcaseC : TrMax (seg N j₀' (Lng N - 1)) <
      parent (seg N j₀' (Lng N - 1)) 0
        (parent N 0 (Lng N - 1) - j₀')) :
    descending (Br (seg (oper N n) j₀' j₁')) := by
  let j₁ := Lng N - 1
  let j₀ := parent N 0 j₁
  let Np := seg N j₀' j₁
  let Mp := seg (oper N n) j₀' j₁'
  let t := TrMax Np
  let a := j₀' + t + 1
  let d := j₀ - j₀'
  have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
  have hnext : nextR N 0 j₀ j₁ = true := by
    simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
  have hj₀lt : j₀ < j₁ := (nextR_implies_row0 N 0 j₀ j₁ hnext).1
  have hj₀'j₁ : j₀' < j₁ := hstart.trans hj₀lt
  have haj₀ : a < j₀ := by simpa [a, t, Np, j₀, j₁] using ha
  have hj₀'j₀ : j₀' < j₀ := by simpa [j₀, j₁] using hstart
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    exact hj₀'j₁.le
  have hNpLen : 1 < Lng Np := by simp [Np]; omega
  have hancN' : leR N 0 j₀' j₁ = true := by simpa [j₁] using hancN
  have hmonoNp : monoT Np = true := by
    simpa [Np] using mono_ancestor_slice N j₀' j₁ hNT hj₀'j₁ hancN'
  have hd0 : entry N 1 j₁ = 0 := by
    by_cases hpos : 0 < entry N 1 j₁
    · have hone : idx1 N j₁ = 1 := by simp [idx1, hpos]
      rw [hone] at hi
      omega
    · omega
  have hlastNp : entry Np 1 (Lng Np - 1) = 0 := by
    have hb : Lng Np - 1 < Lng Np := by
      have := List.length_pos_of_ne_nil hNpT
      omega
    rw [entry_seg N j₀' j₁ 1 (Lng Np - 1) hb]
    have heq : j₀' + (Lng Np - 1) = j₁ := by simp [Np]; omega
    rw [heq, hd0]
  have htLast := TrMax_lt_last_of_row1_zero_68 Np hNpT hNpLen hlastNp
  have hTrEq : TrMax Mp = t := by
    have hh := TrMax_seg_oper_d0zero_eq_caseA_68 N n j₀' j₁'
      hNT hlen hzero hp hi hn hstart (by omega) hend
    simpa [Mp, Np, t, j₁] using hh
  have hTrMpLt : TrMax Mp < Lng Mp - 1 := by
    rw [hTrEq]
    have htCoord : t < j₁ - j₀' := by
      have heq : Lng Np - 1 = j₁ - j₀' := by simp [Np]; omega
      rw [heq] at htLast
      exact htLast
    have hlenMp : Lng Mp - 1 = j₁' - j₀' := by simp [Mp]; omega
    rw [hlenMp]
    have hj₁le : j₁ ≤ j₁' := by simpa [j₁] using hbge
    omega
  have hBrM : Br Mp = P (seg (oper N n) a j₁') := by
    have hh := Br_seg_reshape_68 (oper N n) j₀' j₁' hlt hend
      (by simpa [Mp] using ne_of_lt hTrMpLt)
    rw [hTrEq] at hh
    simpa [Mp, a, t, Nat.add_assoc] using hh
  have hBrN : Br Np = P (seg N a j₁) := by
    have hne : TrMax Np ≠ Lng Np - 1 := by omega
    have hh := Br_seg_reshape_68 N j₀' j₁ hj₀'j₁
      (by simp [j₁]; omega) (by simpa [Np] using hne)
    simpa [Np, a, t, Nat.add_assoc] using hh
  have hBrNne : Br Np ≠ [] := by rw [hBrN]; exact P_nonempty _
  let J := (Br Np).length - 1
  have hJ : J < (Br Np).length := by
    have := List.length_pos_of_ne_nil hBrNne
    simp [J]
    omega
  let fn := (FirstNodes Np).getD J 0
  let fnM := j₀' + fn
  have hfn : fn = t + 1 + (IdxSum (Br Np)).getD J 0 := by
    simpa [fn, t] using FirstNodes_getD Np J hJ
  have hafnM : a ≤ fnM := by simp [a, fnM, hfn]; omega
  have hdpos : 0 < d := by simp [d]; omega
  have hdNp : d < Lng Np := by simp [d, Np]; omega
  have hlastNpIdx : Lng Np - 1 < Lng Np := by
    have := List.length_pos_of_ne_nil hNpT
    omega
  have hnextLeaf : nextR Np 0 d (Lng Np - 1) = true := by
    rw [nextR_seg_adm N j₀' j₁ 0 d (Lng Np - 1)
      hj₀'j₁.le (by simp [j₁]; omega) hdNp hlastNpIdx]
    have hdEq : j₀' + d = j₀ := by
      simp [d, Nat.add_sub_of_le hj₀'j₀.le]
    have hlEq : j₀' + (Lng Np - 1) = j₁ := by simp [Np]; omega
    simpa [hdEq, hlEq] using hnext
  have hparentFn : parent Np 0 fn ≤ t := by
    have hh := (FirstNodes_TrMax_Joints Np J hNpT hmonoNp hJ).1
    rw [Joints_getD Np J hJ] at hh
    simpa [fn, t] using hh
  have hcaseC' : t < parent Np 0 d := by
    simpa [t, Np, d, j₀, j₁] using hcaseC
  let Y := seg N a j₁
  have hYT : TPS Y := by
    apply List.ne_nil_of_length_pos
    simp [Y]
    omega
  have hJY : J < (P Y).length := by simpa [Y, hBrN] using hJ
  let k := (IdxSum (P Y)).getD J 0
  have hkEq : k = (IdxSum (Br Np)).getD J 0 := by simp [k, Y, hBrN]
  have hfnMEq : fnM = a + k := by simp [fnM, a, hfn, hkEq]; omega
  have hJlast : J + 1 = (P Y).length := by
    have hlenEq : (Br Np).length = (P Y).length := by
      simpa [Y] using congrArg List.length hBrN
    rw [← hlenEq]
    have hpos := List.length_pos_of_ne_nil hBrNne
    simp [J]
    omega
  have hidxNext : (IdxSum (P Y)).getD (J + 1) 0 = Lng Y := by
    rw [hJlast]
    calc
      (IdxSum (P Y)).getD (P Y).length 0 = Lng (P Y).flatten :=
        idxSum_total (P Y)
      _ = Lng Y := congrArg Lng (P_concat Y)
  let C := (Br Np).getD J []
  have hCeq : C = seg N fnM j₁ := by
    have hcomp := P_IdxSum Y J hYT (by omega)
    have hsub := seg_of_seg_68 N a j₁ k
      ((IdxSum (P Y)).getD (J + 1) 0 - 1)
      (haj₀.trans hj₀lt).le (by
        rw [hidxNext]
        simp [Y]
        omega)
    calc
      C = (P Y).getD J [] := by simp [C, Y, hBrN]
      _ = seg Y k ((IdxSum (P Y)).getD (J + 1) 0 - 1) := hcomp
      _ = seg N (a + k)
          (a + ((IdxSum (P Y)).getD (J + 1) 0 - 1)) := hsub
      _ = seg N fnM j₁ := by
        have hendY : a + (Lng Y - 1) = j₁ := by
          simp [Y]
          have := haj₀.trans hj₀lt
          omega
        rw [hfnMEq, hidxNext]
        rw [hendY]
  have hCpos : 0 < Lng C := by
    have hh := P_component_nonempty Y J hYT hJY
    simpa [C, Y, hBrN] using hh
  have hCT : TPS C := List.ne_nil_of_length_pos hCpos
  have hCmem : C ∈ P Y := by
    have hh : (P Y).getD J [] ∈ P Y := by
      rw [getD_eq_getElem_idx (P Y) [] hJY]
      exact List.getElem_mem hJY
    simpa [C, Y, hBrN] using hh
  have hCnm : multiT C = false := by
    rcases P_components_nonmulti Y hYT C hCmem with hz | hm
    · simp [multiT, hz]
    · simp [multiT, hm]
  have hCcrit := (multi_criterion_12 C hCT).mp hCnm
  have hfnMle : fnM ≤ j₁ := by
    rw [hCeq] at hCpos
    simp at hCpos
    omega
  have hfnle : fn ≤ Lng Np - 1 := by simp [fnM, Np] at hfnMle ⊢; omega
  have hfnltLast : fn < Lng Np - 1 := by
    by_contra hh
    have heq : fn = Lng Np - 1 := by omega
    have hparLeaf : parent Np 0 (Lng Np - 1) = d :=
      parent_eq_of_nextR0 Np d (Lng Np - 1) hnextLeaf
    have hpd : parent Np 0 d < d := by
      have hnextD : nextR Np 0 (parent Np 0 d) d = true := by
        have hentry : entry Np 0 0 < entry Np 0 d := by
          have hancJ₀ := ancestor_tree_1 N j₀' j₀ j₁ hNT hancN'
            hstart.le hj₀lt.le
          have he := ancestor_basic_1 N j₀' j₀ j₀ hNT hstart
            (le_refl _) hancJ₀
          have hzeroNp : entry Np 0 0 = entry N 0 j₀' := by
            have : 0 < Lng Np := List.length_pos_of_ne_nil hNpT
            simpa [Np] using entry_seg N j₀' j₁ 0 0 this
          have hdEntry : entry Np 0 d = entry N 0 j₀ := by
            have hdEq : j₀' + d = j₀ := by
              simp [d, Nat.add_sub_of_le hj₀'j₀.le]
            simpa [Np, hdEq] using entry_seg N j₀' j₁ 0 d hdNp
          simpa [hzeroNp, hdEntry] using he
        obtain ⟨p, _, _, hpnext⟩ := parent_exists_1 Np 0 d hNpT hdpos hdNp hentry
        have hpeq := parent_eq_of_nextR0 Np p d hpnext
        simpa [hpeq] using hpnext
      exact (nextR_implies_row0 Np 0 (parent Np 0 d) d hnextD).1
    rw [heq, hparLeaf] at hparentFn
    omega
  have hNdomLocal : ∀ q, fn < q → q ≤ Lng Np - 1 →
      entry Np 0 fn < entry Np 0 q := by
    intro q hfq hqlast
    have hlenC : Lng C = Lng Np - fn := by rw [hCeq]; simp [fnM, Np]; omega
    let r := q - fn
    have hrpos : 0 < r := by simp [r]; omega
    have hrC : r < Lng C := by simp [r, hlenC]; omega
    have h0 : entry C 0 0 = entry Np 0 fn := by
      rw [hCeq]
      have : 0 < Lng (seg N fnM j₁) := by simpa [hCeq] using hCpos
      rw [entry_seg N fnM j₁ 0 0 this]
      have hfnNp : fn < Lng Np := hfnltLast.trans (by omega)
      simpa [fnM, Np] using (entry_seg N j₀' j₁ 0 fn hfnNp).symm
    have hr : entry C 0 r = entry Np 0 q := by
      rw [hCeq, entry_seg N fnM j₁ 0 r (by simpa [hCeq] using hrC)]
      have hqNp : q < Lng Np := hqlast.trans_lt (by omega)
      rw [entry_seg N j₀' j₁ 0 q hqNp]
      have hidx : fnM + r = j₀' + q := by
        simp [fnM, r]
        omega
      exact congrArg (fun z => entry N 0 z) hidx
    simpa [h0, hr] using hCcrit r hrpos hrC
  have hfnleD : fn ≤ d := by
    apply nextR0_largest_below Np d fn (Lng Np - 1) hnextLeaf hfnltLast
    exact hNdomLocal (Lng Np - 1) hfnltLast (le_refl _)
  have hfnneD : fn ≠ d := by
    intro heq
    have hc : t < parent Np 0 fn := by simpa [heq] using hcaseC'
    omega
  have hfnltD : fn < d := lt_of_le_of_ne hfnleD hfnneD
  have hfnMlt : fnM < j₀ := by
    simp [fnM, d, Nat.add_sub_of_le hj₀'j₀.le] at hfnltD ⊢
    omega
  have hNdom : ∀ q, fnM < q → q ≤ j₁ →
      entry N 0 fnM < entry N 0 q := by
    intro q hfq hq
    have hqLocal : q - j₀' ≤ Lng Np - 1 := by simp [Np]; omega
    have hfnq : fn < q - j₀' := by simp [fnM] at hfq ⊢; omega
    have hfnNp : fn < Lng Np := hfnltLast.trans (by omega)
    have hqNp : q - j₀' < Lng Np := hqLocal.trans_lt (by omega)
    have hh := hNdomLocal (q - j₀') hfnq hqLocal
    rw [entry_seg N j₀' j₁ 0 fn hfnNp,
      entry_seg N j₀' j₁ 0 (q - j₀') hqNp] at hh
    have hbase : j₀' ≤ q := by simp [fnM] at hfq; omega
    simpa [fnM, Nat.add_sub_of_le hbase] using hh
  have hOperT : TPS (oper N n) := oper_TPS N n hNT hn
  have hMdom : ∀ q, fnM < q → q ≤ j₁' →
      entry (oper N n) 0 fnM < entry (oper N n) 0 q := by
    intro q hfq hq
    have hfnAgree := entry_oper_lt_last_68 N n 0 fnM hlen hn
      (Or.inl rfl) (by simpa [j₁] using hfnMlt.trans hj₀lt)
    by_cases hqj : q ≤ j₀
    · have hqold : q < j₁ := hqj.trans_lt hj₀lt
      have hqAgree := entry_oper_lt_last_68 N n 0 q hlen hn
        (Or.inl rfl) (by simpa [j₁] using hqold)
      rw [hfnAgree, hqAgree]
      exact hNdom q hfq (hqj.trans hj₀lt.le)
    · have hfloor := oper_tiling_block_floor N n q hNT hlen hzero hp
        (by simpa [hi, j₀, j₁] using (show j₀ ≤ q by omega))
        (hq.trans_lt hend)
      have hstrict := hNdom j₀ hfnMlt hj₀lt.le
      have hfloor' : entry N 0 j₀ ≤ entry (oper N n) 0 q := by
        simpa [hi, j₀, j₁] using hfloor
      rw [hfnAgree]
      exact hstrict.trans_le hfloor'
  let TL := seg (oper N n) fnM j₁'
  have hfnMj₁' : fnM < j₁' := hfnMlt.trans hj₀lt |>.trans_le hbge
  have hTLT : TPS TL := by
    apply List.ne_nil_of_length_pos
    simp [TL]
    omega
  have hTLnm : multiT TL = false := by
    apply (multi_criterion_12 TL hTLT).2
    intro r hrpos hrTL
    have hrEntry := hMdom (fnM + r) (by omega) (by simp [TL] at hrTL; omega)
    have h0 : entry TL 0 0 = entry (oper N n) 0 fnM := by
      simpa [TL] using entry_seg (oper N n) fnM j₁' 0 0
        (List.length_pos_of_ne_nil hTLT)
    have hr : entry TL 0 r = entry (oper N n) 0 (fnM + r) := by
      simpa [TL] using entry_seg (oper N n) fnM j₁' 0 r hrTL
    simpa [h0, hr] using hrEntry
  have hPTL : P TL = [TL] := P_nonmulti_eq TL hTLnm
  by_cases hJzero : J = 0
  · have hkzero : k = 0 := by
      dsimp [k]
      rw [hJzero, idxSum_getD (P Y) 0 (Nat.zero_le _)]
      simp
    have hfnMa : fnM = a := by omega
    rw [hBrM, ← hfnMa]
    change descending (P TL)
    rw [hPTL]
    exact descending_singleton TL
  · have hkpos : 0 < k := by
      have hJm : J - 1 < (P Y).length := by omega
      have hprevPos := P_component_nonempty Y (J - 1) hYT hJm
      have hdiff := idxSum_diff (P Y) (J - 1) hJm
      have hsucc : J - 1 + 1 = J := by omega
      rw [hsucc] at hdiff
      dsimp [k]
      omega
    have hafnMlt : a < fnM := by rw [hfnMEq]; omega
    have hleftMinN : ∀ x, a ≤ x → x < fnM →
        entry N 0 fnM ≤ entry N 0 x := by
      intro x hax hx
      have hlmin := (P_leftend_lmin Y J hYT hJY).2
      let r := x - a
      have hrk : r < k := by simp [r, hfnMEq] at hx ⊢; omega
      have hrY : r < Lng Y := by
        have hkY : k ≤ Lng Y - 1 := by
          simpa [k] using (P_leftend_lmin Y J hYT hJY).1
        have hYpos := List.length_pos_of_ne_nil hYT
        omega
      have hkY : k < Lng Y := by
        have hkle : k ≤ Lng Y - 1 := by
          simpa [k] using (P_leftend_lmin Y J hYT hJY).1
        have hYpos := List.length_pos_of_ne_nil hYT
        omega
      have hh := hlmin r (by simpa [k] using hrk)
      rw [entry_seg N a j₁ 0 k hkY,
        entry_seg N a j₁ 0 r hrY] at hh
      simpa [hfnMEq, r, Nat.add_sub_of_le hax] using hh
    have hNsplit := P_seg_split_at_68 N a fnM j₁ hNT hafnMlt
      hfnMle (by simp [j₁]; omega) hleftMinN
    let LOW := P (seg N a (fnM - 1))
    have hPC : P (seg N fnM j₁) = [seg N fnM j₁] := by
      rw [← hCeq]
      exact P_nonmulti_eq C hCnm
    have hOldFold : Br Np = LOW ++ [C] := by
      rw [hBrN, hNsplit]
      simp [LOW, hPC, hCeq]
    have hLOWlen : LOW.length = J := by
      have hh := congrArg List.length hOldFold
      simp [J] at hh ⊢
      omega
    have hLOWtake : LOW = (Br Np).take J := by
      rw [hOldFold]
      simp [hLOWlen]
    have hleftMinM : ∀ x, a ≤ x → x < fnM →
        entry (oper N n) 0 fnM ≤ entry (oper N n) 0 x := by
      intro x hax hx
      rw [entry_oper_lt_last_68 N n 0 fnM hlen hn (Or.inl rfl)
          (by simpa [j₁] using hfnMlt.trans hj₀lt),
        entry_oper_lt_last_68 N n 0 x hlen hn (Or.inl rfl)
          (by simpa [j₁] using hx.trans hfnMlt |>.trans hj₀lt)]
      exact hleftMinN x hax hx
    have hMsplit := P_seg_split_at_68 (oper N n) a fnM j₁' hOperT
      hafnMlt hfnMj₁'.le hend hleftMinM
    have hlowSeg : seg (oper N n) a (fnM - 1) = seg N a (fnM - 1) :=
      seg_oper_eq_68 N n a (fnM - 1) hlen hn (by omega)
        (by simpa [j₁] using (show fnM - 1 < j₁ by omega))
    have hNewFold : Br Mp = LOW ++ [TL] := by
      rw [hBrM, hMsplit, congrArg P hlowSeg]
      simp [LOW, TL, hPTL]
    have hLOWdesc : descending LOW := by
      rw [hLOWtake]
      exact descending_take hdescNp J
    have hLOWne : LOW ≠ [] := by
      intro heq
      have := congrArg List.length heq
      simp [hLOWlen] at this
      omega
    have hOldDesc : descending (LOW ++ [C]) := by
      rw [← hOldFold]
      exact hdescNp
    have hJoinOld : cdom (LOW.getD (LOW.length - 1) []) C := by
      have hh := descending_append_junction_68 hOldDesc hLOWne
        (by simp : ([C] : List PS) ≠ [])
      simpa using hh
    have hChead₀ : entry C 0 0 = entry N 0 fnM := by
      rw [hCeq]
      simpa using entry_seg N fnM j₁ 0 0 (by simp; omega)
    have hChead₁ : entry C 1 0 = entry N 1 fnM := by
      rw [hCeq]
      simpa using entry_seg N fnM j₁ 1 0 (by simp; omega)
    have hTLhead₀ : entry TL 0 0 = entry N 0 fnM := by
      rw [show entry TL 0 0 = entry (oper N n) 0 fnM by
        simpa [TL] using entry_seg (oper N n) fnM j₁' 0 0
          (List.length_pos_of_ne_nil hTLT)]
      exact entry_oper_lt_last_68 N n 0 fnM hlen hn (Or.inl rfl)
        (by simpa [j₁] using hfnMlt.trans hj₀lt)
    have hTLhead₁ : entry TL 1 0 = entry N 1 fnM := by
      rw [show entry TL 1 0 = entry (oper N n) 1 fnM by
        simpa [TL] using entry_seg (oper N n) fnM j₁' 1 0
          (List.length_pos_of_ne_nil hTLT)]
      exact entry_oper_lt_last_68 N n 1 fnM hlen hn (Or.inr rfl)
        (by simpa [j₁] using hfnMlt.trans hj₀lt)
    have hJoin : cdom (LOW.getD (LOW.length - 1) []) TL := by
      rw [cdom] at hJoinOld ⊢
      simpa [hChead₀, hChead₁, hTLhead₀, hTLhead₁] using hJoinOld
    have hAll := descending_append hLOWdesc (descending_singleton TL)
      (fun _ _ => hJoin)
    change descending (Br Mp)
    rw [hNewFold]
    exact hAll

private theorem rankSucc_d0zero_68
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀' j₁' : ℕ)
    (hN : SkTPS k N) (hM : M = oper N n) (hn : 1 ≤ n)
    (hlen : 1 < Lng N) (hnmulti : multiT N = false)
    (hd0 : entry N 1 (Lng N - 1) = 0)
    (hlt : j₀' < j₁') (hj₁M : j₁' ≤ Lng M - 1)
    (hjlarge : Lng N - 1 ≤ j₁')
    (hancM : leR M 0 j₀' j₁' = true) :
    descending (Br (seg M j₀' j₁')) := by
  by_cases hwithin : parent N 0 (Lng N - 1) ≤ j₀'
  · exact rankSucc_d0zero_within_block k ih N M n j₀' j₁' hN hM hn
      hlen hnmulti hd0 hwithin hlt hj₁M hjlarge hancM
  · have hstart : j₀' < parent N 0 (Lng N - 1) := by omega
    by_cases hcaseA : parent N 0 (Lng N - 1) - j₀' ≤
        TrMax (seg N j₀' (Lng N - 1))
    · exact rankSucc_d0zero_straddle_caseA_68 k ih N M n j₀' j₁'
        hN hM hn hlen hnmulti hd0 hstart hlt hj₁M hjlarge hancM hcaseA
    · have hNT : TPS N := SkTPS_TPS k N hN
      have htiling := reaching_old_end_forces_tiling N M n j₁'
        hM hlen hjlarge hj₁M
      rcases htiling with ⟨hzero, hp⟩
      have hi : idx1 N (Lng N - 1) = 0 := by simp [idx1, hd0]
      have hj₁Oper : j₁' < Lng (oper N n) := by
        have hMT : TPS M := by rw [hM]; exact oper_TPS N n hNT hn
        have hj₁lt : j₁' < Lng M := by
          have := List.length_pos_of_ne_nil hMT
          omega
        rwa [hM] at hj₁lt
      let j₁ := Lng N - 1
      let j₀ := parent N 0 j₁
      let Np := seg N j₀' j₁
      have hp0 : hasParent N 0 j₁ = true := by simpa [j₁, hi] using hp
      have hnext : nextR N 0 j₀ j₁ = true := by
        simpa [j₀] using hasParent_next_fseq N 0 j₁ hp0
      have hj₀lt : j₀ < j₁ :=
        (nextR_implies_row0 N 0 j₀ j₁ hnext).1
      have hj₀'j₁ : j₀' < j₁ := hstart.trans hj₀lt
      have hMT : TPS M := by rw [hM]; exact oper_TPS N n hNT hn
      have hj₁ML : j₁' < Lng M := by
        have := List.length_pos_of_ne_nil hMT
        omega
      have hj₁le : j₁ ≤ j₁' := by simpa [j₁] using hjlarge
      have hancPrefixM : leR M 0 j₀' j₀ = true :=
        ancestor_tree_1 M j₀' j₀ j₁' hMT hancM
          (by simpa [j₀, j₁] using hstart.le)
          (hj₀lt.le.trans hj₁le)
      have hsegPrefix : seg M j₀' j₀ = seg N j₀' j₀ := by
        rw [hM]
        exact seg_oper_eq_68 N n j₀' j₀ hlen hn
          (by simpa [j₀, j₁] using hstart.le)
          (by dsimp [j₀, j₁]; omega)
      have hj₀M : j₀ < Lng M :=
        (hj₀lt.le.trans hj₁le).trans_lt hj₁ML
      have hj₀N : j₀ < Lng N := hj₀lt.trans (by simp [j₁]; omega)
      have hancPrefixN : leR N 0 j₀' j₀ = true :=
        leR0_transfer_seg_eq_68 M N j₀' j₀
          (by simpa [j₀, j₁] using hstart) hj₀M hj₀N
          hsegPrefix hancPrefixM
      have hancEndN : leR N 0 j₀' j₁ = true :=
        row0_transitive N j₀' j₀ j₁ hNT hancPrefixN
          (nextR0_leR N j₀ j₁ hnext)
      have hzeroN : zeroT N = false := by simp [zeroT]; omega
      have hmonoN : monoT N = true := by
        simp [multiT, hzeroN] at hnmulti
        exact hnmulti
      have hdescNp : descending (Br Np) := by
        simpa [Np, j₁] using ih N j₀' (Lng N - 1) hN hmonoN
          (by simpa [j₁] using hj₀'j₁) (le_refl _)
          (by simpa [j₁] using hancEndN)
      have haLe : j₀' + TrMax Np + 1 ≤ j₀ := by
        dsimp [Np, j₀, j₁] at hcaseA ⊢
        omega
      by_cases haeq : j₀' + TrMax Np + 1 = j₀
      · have hh := d0zero_Br_descending_branch_at_parent_68 N n j₀' j₁'
          hNT hlen hzero hp hi hn
          (by simpa [j₀, j₁] using hstart) hlt hjlarge hj₁Oper
          (by simpa [Np, j₀, j₁] using haeq)
        simpa [hM] using hh
      · have haLt : j₀' + TrMax Np + 1 < j₀ := by omega
        by_cases hcaseB : parent Np 0 (j₀ - j₀') ≤ TrMax Np
        · have hh := d0zero_Br_descending_caseB_68 N n j₀' j₁'
            hNT hlen hzero hp hi hn
            (by simpa [j₀, j₁] using hstart) hlt hjlarge hj₁Oper
            (by simpa [j₁] using hancEndN)
            (by simpa [Np] using hdescNp)
            (by simpa [Np, j₀, j₁] using haLt)
            (by simpa [Np, j₀, j₁] using hcaseB)
          simpa [hM] using hh
        · have hh := d0zero_Br_descending_caseC_68 N n j₀' j₁'
            hNT hlen hzero hp hi hn
            (by simpa [j₀, j₁] using hstart) hlt hjlarge hj₁Oper
            (by simpa [j₁] using hancEndN)
            (by simpa [Np] using hdescNp)
            (by simpa [Np, j₀, j₁] using haLt)
            (by simpa [Np, j₀, j₁] using (show TrMax Np <
              parent Np 0 (j₀ - j₀') by omega))
          simpa [hM] using hh

/-- Taking all but the last element is the same as `dropLast`. -/
private theorem take_pred_eq_dropLast_68 {α : Type} (l : List α) :
    l.take (l.length - 1) = l.dropLast := by
  rw [List.dropLast_eq_take]

/-- The last left endpoint of a multi-component principal decomposition is a
positive row-zero left minimum, and the suffix starting there is precisely
the final non-multi component. -/
private theorem P_last_anchor_68
    (S : PS) (hS : TPS S) (hmulti : 1 < (P S).length) :
    let J := (P S).length - 1
    let c := (IdxSum (P S)).getD J 0
    0 < c ∧ c ≤ Lng S - 1 ∧
      (∀ j, j < c → entry S 0 c ≤ entry S 0 j) ∧
      multiT (seg S c (Lng S - 1)) = false ∧
      P S = (P S).take J ++ [seg S c (Lng S - 1)] := by
  have hQpos : 0 < (P S).length := List.length_pos_of_ne_nil (P_nonempty S)
  have hJ : (P S).length - 1 < (P S).length := by omega
  have hnext : (IdxSum (P S)).getD ((P S).length - 1 + 1) 0 = Lng S := by
    rw [show (P S).length - 1 + 1 = (P S).length by omega]
    calc
      (IdxSum (P S)).getD (P S).length 0
          = Lng (P S).flatten := idxSum_total (P S)
      _ = Lng S := congrArg Lng (P_concat S)
  have htail : (P S).getD ((P S).length - 1) [] =
      seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) := by
    rw [P_IdxSum S ((P S).length - 1) hS (le_refl _), hnext]
  have hcpos : 0 < (IdxSum (P S)).getD ((P S).length - 1) 0 := by
    have hprev : (P S).length - 1 - 1 < (P S).length := by omega
    have hprevPos := P_component_nonempty S ((P S).length - 1 - 1) hS hprev
    have hdiff := idxSum_diff (P S) ((P S).length - 1 - 1) hprev
    rw [show (P S).length - 1 - 1 + 1 = (P S).length - 1 by omega] at hdiff
    omega
  have hcle : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng S - 1 :=
    (P_leftend_lmin S ((P S).length - 1) hS hJ).1
  have hlmin := (P_leftend_lmin S ((P S).length - 1) hS hJ).2
  have hmem : (P S).getD ((P S).length - 1) [] ∈ P S := by
    rw [getD_eq_getElem_idx (P S) [] hJ]
    exact List.getElem_mem hJ
  have hnmTail : multiT (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)) = false := by
    rw [← htail]
    rcases P_components_nonmulti S hS _ hmem with hz | hm
    · simp only [multiT, hz, Bool.not_true, Bool.false_and]
    · simp only [multiT, hm, Bool.not_true, Bool.and_false]
  have hlist : P S = (P S).take ((P S).length - 1) ++
      [(P S).getD ((P S).length - 1) []] := by
    have h2 : P S = (P S).take ((P S).length - 1 + 1) := by
      rw [show (P S).length - 1 + 1 = (P S).length by omega, List.take_length]
    rw [List.take_succ, List.getElem?_eq_getElem hJ] at h2
    rw [getD_eq_getElem_idx (P S) [] hJ]
    simpa using h2
  have hfold : P S = (P S).take ((P S).length - 1) ++
      [seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)] := by
    rw [← htail]
    exact hlist
  exact ⟨hcpos, hcle, hlmin, hnmTail, hfold⟩

private theorem P_last_anchor_butlast_68
    (S : PS) (hS : TPS S) (hmulti : 1 < (P S).length) :
    let c := (IdxSum (P S)).getD ((P S).length - 1) 0
    (P S).dropLast = P (seg S 0 (c - 1)) := by
  obtain ⟨hcpos, hcle, hlmin, hnm, _⟩ := P_last_anchor_68 S hS hmulti
  have hsplit := P_additivity S
    ((IdxSum (P S)).getD ((P S).length - 1) 0) hS hcpos hcle hlmin
  have htail : P (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)) = [seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)] := P_nonmulti_eq _ hnm
  rw [htail] at hsplit
  show (P S).dropLast =
    P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1))
  calc (P S).dropLast
      = (P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) ++
          [seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
            (Lng S - 1)]).dropLast := by
        rw [← hsplit]
    _ = P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) := by
        simp

private theorem P_last_anchor_tail_entry_68
    (S : PS) (i : ℕ) (hS : TPS S) (hmulti : 1 < (P S).length) :
    let c := (IdxSum (P S)).getD ((P S).length - 1) 0
    entry (seg S c (Lng S - 1)) i 0 = entry S i c := by
  obtain ⟨_, hcle, _, _, _⟩ := P_last_anchor_68 S hS hmulti
  show entry (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)) i 0 =
    entry S i ((IdxSum (P S)).getD ((P S).length - 1) 0)
  have hSpos : 0 < Lng S := List.length_pos_of_ne_nil hS
  have hpos : 0 < Lng (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)) := by
    rw [length_seg]
    omega
  simpa using entry_seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
    (Lng S - 1) i 0 hpos

private theorem P_last_anchor_getD_68
    (S : PS) (hS : TPS S) (hmulti : 1 < (P S).length) :
    let J := (P S).length - 1
    let c := (IdxSum (P S)).getD J 0
    (P S).getD J [] = seg S c (Lng S - 1) := by
  have hQpos : 0 < (P S).length := List.length_pos_of_ne_nil (P_nonempty S)
  have hnext : (IdxSum (P S)).getD ((P S).length - 1 + 1) 0 = Lng S := by
    rw [show (P S).length - 1 + 1 = (P S).length by omega]
    calc
      (IdxSum (P S)).getD (P S).length 0
          = Lng (P S).flatten := idxSum_total (P S)
      _ = Lng S := congrArg Lng (P_concat S)
  show (P S).getD ((P S).length - 1) [] =
    seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)
  rw [P_IdxSum S ((P S).length - 1) hS (le_refl _), hnext]

private theorem P_last_anchor_collapse_68
    (S base : PS) (BN : List PS) (sh : ℕ)
    (hS : TPS S) (hmulti : 1 < (P S).length)
    (hshift :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      seg S 0 (c - 1) = IncrFirstN sh base)
    (hbut : BN.dropLast = P base) :
    let c := (IdxSum (P S)).getD ((P S).length - 1) 0
    P S = (BN.dropLast).map (IncrFirstN sh) ++
      [seg S c (Lng S - 1)] := by
  obtain ⟨_, _, _, _, hfold⟩ := P_last_anchor_68 S hS hmulti
  have hdrop : (P S).dropLast =
      P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) :=
    P_last_anchor_butlast_68 S hS hmulti
  have hshift' : seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1) =
      IncrFirstN sh base := hshift
  have hlow : (P S).dropLast = (BN.dropLast).map (IncrFirstN sh) := by
    rw [hdrop, hshift', P_IncrFirstN_equivariance sh base, ← hbut]
  show P S = (BN.dropLast).map (IncrFirstN sh) ++
    [seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)]
  rw [← hlow, ← take_pred_eq_dropLast_68 (P S)]
  exact hfold

private theorem notmulti_seg_prefix_68
    (M : PS) (b : ℕ) (hM : TPS M) (hnm : multiT M = false)
    (hb : b < Lng M) : multiT (seg M 0 b) = false := by
  by_cases hb0 : b = 0
  · have hlen : Lng (seg M 0 b) = 1 := by simp [hb0]
    cases hh : multiT (seg M 0 b) with
    | false => rfl
    | true =>
        have hT : TPS (seg M 0 b) := by
          apply List.ne_nil_of_length_pos
          show 0 < Lng (seg M 0 b)
          omega
        have hlong := multi_length_fseq (seg M 0 b) hT hh
        rw [hlen] at hlong
        omega
  · have hbpos : 0 < b := by omega
    have hzero : zeroT M = false := by simp [zeroT]; omega
    have hmono : monoT M = true := by
      simp [multiT, hzero] at hnm
      exact hnm
    have hpref := mono_prefix M b hM hmono hbpos hb
    simp [multiT, hpref]

/-- Cutting a sequence anywhere strictly after its last principal anchor does
not change the principal-component prefix before the last component. -/
private theorem P_dropLast_seg_zero_after_anchor_68
    (S : PS) (m : ℕ) (hS : TPS S) (hmulti : 1 < (P S).length)
    (hcm : (IdxSum (P S)).getD ((P S).length - 1) 0 < m)
    (hm : m ≤ Lng S) :
    (P (seg S 0 (m - 1))).dropLast = (P S).dropLast := by
  obtain ⟨hcpos, hcle, hlmin, htailNm, _⟩ :=
    P_last_anchor_68 S hS hmulti
  have hSpos : 0 < Lng S := List.length_pos_of_ne_nil hS
  have hmpos : 0 < m := by omega
  have hQL : Lng (seg S 0 (m - 1)) = m := by
    rw [length_seg]
    omega
  have hQT : TPS (seg S 0 (m - 1)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg S 0 (m - 1))
    omega
  have hcQ : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤
      Lng (seg S 0 (m - 1)) - 1 := by
    rw [hQL]
    omega
  have hentryQ : ∀ j, j ≤ m - 1 →
      entry (seg S 0 (m - 1)) 0 j = entry S 0 j := by
    intro j hj
    have hjQ : j < Lng (seg S 0 (m - 1)) := by omega
    rw [entry_seg S 0 (m - 1) 0 j hjQ, Nat.zero_add]
  have hlminQ : ∀ j, j < (IdxSum (P S)).getD ((P S).length - 1) 0 →
      entry (seg S 0 (m - 1)) 0
          ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry (seg S 0 (m - 1)) 0 j := by
    intro j hj
    rw [hentryQ _ (by omega), hentryQ j (by omega)]
    exact hlmin j hj
  have hCT : TPS (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng S - 1))
    rw [length_seg]
    omega
  have heC : m - 1 - (IdxSum (P S)).getD ((P S).length - 1) 0 <
      Lng (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0)
        (Lng S - 1)) := by
    rw [length_seg]
    omega
  have hprefixNm := notmulti_seg_prefix_68 _ _ hCT htailNm heC
  have htailEq : seg (seg S 0 (m - 1))
        ((IdxSum (P S)).getD ((P S).length - 1) 0) (m - 1) =
      seg (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)) 0
        (m - 1 - (IdxSum (P S)).getD ((P S).length - 1) 0) := by
    have hleft := seg_of_seg_68 S 0 (m - 1)
      ((IdxSum (P S)).getD ((P S).length - 1) 0) (m - 1)
      (Nat.zero_le _) (by omega)
    have hright := seg_of_seg_68 S
      ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) 0
      (m - 1 - (IdxSum (P S)).getD ((P S).length - 1) 0)
      hcle (by omega)
    rw [hleft, hright, Nat.zero_add, Nat.zero_add, Nat.add_zero,
      Nat.add_sub_cancel'
        (by omega : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ m - 1)]
  have htailQNm : multiT (seg (seg S 0 (m - 1))
      ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng (seg S 0 (m - 1)) - 1)) = false := by
    rw [hQL, htailEq]
    exact hprefixNm
  have hsplitQ := P_additivity (seg S 0 (m - 1))
    ((IdxSum (P S)).getD ((P S).length - 1) 0) hQT hcpos hcQ hlminQ
  have hsingle : P (seg (seg S 0 (m - 1))
      ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng (seg S 0 (m - 1)) - 1)) = [seg (seg S 0 (m - 1))
      ((IdxSum (P S)).getD ((P S).length - 1) 0)
      (Lng (seg S 0 (m - 1)) - 1)] := P_nonmulti_eq _ htailQNm
  rw [hsingle] at hsplitQ
  have hdropQ : (P (seg S 0 (m - 1))).dropLast =
      P (seg (seg S 0 (m - 1)) 0
        ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) := by
    calc (P (seg S 0 (m - 1))).dropLast
        = (P (seg (seg S 0 (m - 1)) 0
            ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) ++
            [seg (seg S 0 (m - 1))
              ((IdxSum (P S)).getD ((P S).length - 1) 0)
              (Lng (seg S 0 (m - 1)) - 1)]).dropLast := by
          rw [← hsplitQ]
      _ = P (seg (seg S 0 (m - 1)) 0
            ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) := by
          simp
  have hleftEq : seg (seg S 0 (m - 1)) 0
      ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1) =
      seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1) := by
    have hh := seg_of_seg_68 S 0 (m - 1) 0
      ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)
      (Nat.zero_le _) (by omega)
    rw [hh, Nat.zero_add, Nat.zero_add]
  have hdropS : (P S).dropLast =
      P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) :=
    P_last_anchor_butlast_68 S hS hmulti
  rw [hdropQ, hleftEq, hdropS]

private theorem last_anchor_eq_sum_dropLast_68 (S : PS) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
      (((P S).dropLast).map Lng).sum := by
  rw [idxSum_getD (P S) ((P S).length - 1) (by omega)]
  simp [List.dropLast_eq_take]

private theorem last_anchor_ge_of_leftmin_68
    (S : PS) (k : ℕ) (hS : TPS S) (hk : k ≤ Lng S - 1)
    (hmin : ∀ j, j < k → entry S 0 k ≤ entry S 0 j) :
    k ≤ (IdxSum (P S)).getD ((P S).length - 1) 0 := by
  obtain ⟨J, hJ, hidx⟩ := P_lmin_leftend S k hS hk hmin
  have hmono := idxSum_mono (P S) J ((P S).length - 1)
    (by omega) (by omega)
  rw [hidx] at hmono
  exact hmono

/-- The number of principal components is preserved across a uniform row-zero
shift on the prefix ending immediately before the comparison boundary.  The
only possible extra component is the one starting at that boundary; its
presence is characterized by the same row-zero left-minimum condition on both
sides. -/
private theorem P_length_eq_of_shift_prefix_boundary_68
    (S Sn : PS) (sh : ℕ) (hS : TPS S) (hSn : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hmS : Lng Sn - 1 ≤ Lng S - 1)
    (hcS : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Sn - 1)
    (hshift : seg S 0 (Lng Sn - 1 - 1) =
      IncrFirstN sh (seg Sn 0 (Lng Sn - 1 - 1)))
    (hbound0 : entry S 0 (Lng Sn - 1) =
      entry Sn 0 (Lng Sn - 1) + sh) :
    (P S).length = (P Sn).length := by
  let m := Lng Sn - 1
  let c := (IdxSum (P S)).getD ((P S).length - 1) 0
  let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
  let PreS := seg S 0 (m - 1)
  let PreN := seg Sn 0 (m - 1)
  obtain ⟨hcpos, _, hcmin, _, _⟩ := P_last_anchor_68 S hS hmultiS
  obtain ⟨hcNpos, hcNle, hcNmin, _, _⟩ :=
    P_last_anchor_68 Sn hSn hmultiSn
  have hcSle : c ≤ m := by simpa [c, m] using hcS
  have hcNle' : cN ≤ m := by simpa [cN, m] using hcNle
  have hmpos : 0 < m := by omega
  have hmSn : m ≤ Lng Sn := by simp [m]
  have hmSL : m ≤ Lng S := by
    have hSpos := List.length_pos_of_ne_nil hS
    simp [m] at hmS ⊢
    omega
  have hPpre : P PreS = (P PreN).map (IncrFirstN sh) := by
    rw [show PreS = IncrFirstN sh PreN by
      simpa [PreS, PreN, m] using hshift,
      P_IncrFirstN_equivariance]
  have hpreLen : (P PreS).length = (P PreN).length := by
    rw [hPpre]
    simp
  have hrow0 : ∀ j, j < m → entry S 0 j = entry Sn 0 j + sh := by
    intro j hj
    have hjN : j < Lng PreN := by simp [PreN, m]; omega
    have hjS : j < Lng PreS := by simp [PreS, m]; omega
    have hh : entry PreS 0 j = entry PreN 0 j + sh := by
      rw [show PreS = IncrFirstN sh PreN by
        simpa [PreS, PreN, m] using hshift]
      exact entry_IncrFirstN_zero sh PreN j hjN
    rw [entry_seg S 0 (m - 1) 0 j hjS,
      entry_seg Sn 0 (m - 1) 0 j hjN] at hh
    simpa [PreS, PreN] using hh
  have hminToN :
      (∀ j, j < m → entry S 0 m ≤ entry S 0 j) →
      ∀ j, j < m → entry Sn 0 m ≤ entry Sn 0 j := by
    intro hmin j hj
    have hh := hmin j hj
    rw [show entry S 0 m = entry Sn 0 m + sh by
      simpa [m] using hbound0, hrow0 j hj] at hh
    omega
  have hminToS :
      (∀ j, j < m → entry Sn 0 m ≤ entry Sn 0 j) →
      ∀ j, j < m → entry S 0 m ≤ entry S 0 j := by
    intro hmin j hj
    have hh := hmin j hj
    rw [show entry S 0 m = entry Sn 0 m + sh by
      simpa [m] using hbound0, hrow0 j hj]
    omega
  have hstatus : c = m ↔ cN = m := by
    constructor
    · intro hcm
      have hcmEq : (IdxSum (P S)).getD ((P S).length - 1) 0 = m := hcm
      have hminS : ∀ j, j < m → entry S 0 m ≤ entry S 0 j := by
        rw [← hcmEq]
        exact hcmin
      have hminN := hminToN hminS
      have hmle : m ≤ Lng Sn - 1 := by simp [m]
      have hmAnchor := last_anchor_ge_of_leftmin_68 Sn m hSn hmle hminN
      have hcNleE : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 ≤ m := hcNle'
      show cN = m
      exact (by omega :
        (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 = m)
    · intro hcNm
      have hcNmEq : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 = m := hcNm
      have hminN : ∀ j, j < m → entry Sn 0 m ≤ entry Sn 0 j := by
        rw [← hcNmEq]
        exact hcNmin
      have hminS := hminToS hminN
      have hmle : m ≤ Lng S - 1 := by simpa [m] using hmS
      have hmAnchor := last_anchor_ge_of_leftmin_68 S m hS hmle hminS
      have hcSleE : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ m := hcSle
      show c = m
      exact (by omega :
        (IdxSum (P S)).getD ((P S).length - 1) 0 = m)
  have hlenS : (P S).length = (P PreS).length + if c = m then 1 else 0 := by
    by_cases hcm : c = m
    · have hcmEq : (IdxSum (P S)).getD ((P S).length - 1) 0 = m := hcm
      have hdrop : (P S).dropLast =
          P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) :=
        P_last_anchor_butlast_68 S hS hmultiS
      have heq : (P S).dropLast = P PreS := by
        show (P S).dropLast = P (seg S 0 (m - 1))
        rw [← hcmEq]
        exact hdrop
      have hh := congrArg List.length heq
      simp at hh
      simp [hcm]
      omega
    · have hclt : c < m := by omega
      have hcltE : (IdxSum (P S)).getD ((P S).length - 1) 0 < m := hclt
      have hdrop := P_dropLast_seg_zero_after_anchor_68 S m hS
        hmultiS hcltE hmSL
      have hh := congrArg List.length hdrop
      have hprePos : 0 < (P (seg S 0 (m - 1))).length :=
        List.length_pos_of_ne_nil (P_nonempty _)
      simp at hh
      simp [hcm]
      show (P S).length = (P (seg S 0 (m - 1))).length
      omega
  have hlenN : (P Sn).length = (P PreN).length + if cN = m then 1 else 0 := by
    by_cases hcNm : cN = m
    · have hcNmEq : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 = m := hcNm
      have hdrop : (P Sn).dropLast =
          P (seg Sn 0 ((IdxSum (P Sn)).getD ((P Sn).length - 1) 0 - 1)) :=
        P_last_anchor_butlast_68 Sn hSn hmultiSn
      have heq : (P Sn).dropLast = P PreN := by
        show (P Sn).dropLast = P (seg Sn 0 (m - 1))
        rw [← hcNmEq]
        exact hdrop
      have hh := congrArg List.length heq
      simp at hh
      simp [hcNm]
      omega
    · have hclt : cN < m := by omega
      have hcltE : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 < m := hclt
      have hdrop := P_dropLast_seg_zero_after_anchor_68 Sn m hSn
        hmultiSn hcltE hmSn
      have hh := congrArg List.length hdrop
      have hprePos : 0 < (P (seg Sn 0 (m - 1))).length :=
        List.length_pos_of_ne_nil (P_nonempty _)
      simp at hh
      simp [hcNm]
      show (P Sn).length = (P (seg Sn 0 (m - 1))).length
      omega
  by_cases hcm : c = m
  · have hcNm := hstatus.mp hcm
    simp [hcm, hcNm] at hlenS hlenN
    omega
  · have hcNm : cN ≠ m := fun h => hcm (hstatus.mpr h)
    simp [hcm, hcNm] at hlenS hlenN
    omega

/-- Unified comparison of the last anchors across an all-but-boundary uniform
shift.  It covers both an anchor strictly inside the shared prefix and an
anchor exactly at its right boundary. -/
private theorem last_anchor_coincide_shift_prefix_68
    (S Sn : PS) (sh : ℕ) (hS : TPS S) (hSn : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hmS : Lng Sn - 1 ≤ Lng S - 1)
    (hcS : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Sn - 1)
    (hlenP : (P S).length = (P Sn).length)
    (hshift : seg S 0 (Lng Sn - 1 - 1) =
      IncrFirstN sh (seg Sn 0 (Lng Sn - 1 - 1)))
    (hbound0 : entry S 0 (Lng Sn - 1) =
      entry Sn 0 (Lng Sn - 1) + sh)
    (hbound1 : entry S 1 (Lng Sn - 1) ≤
      entry Sn 1 (Lng Sn - 1)) :
    let c := (IdxSum (P S)).getD ((P S).length - 1) 0
    let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
    c = cN ∧ entry S 0 c = entry Sn 0 cN + sh ∧
      entry S 1 c ≤ entry Sn 1 cN ∧
      (P S).dropLast = ((P Sn).dropLast).map (IncrFirstN sh) := by
  let m := Lng Sn - 1
  let c := (IdxSum (P S)).getD ((P S).length - 1) 0
  let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
  let PreS := seg S 0 (m - 1)
  let PreN := seg Sn 0 (m - 1)
  obtain ⟨hcpos, _, _, _, _⟩ := P_last_anchor_68 S hS hmultiS
  obtain ⟨hcNpos, hcNle, _, _, _⟩ := P_last_anchor_68 Sn hSn hmultiSn
  have hcSle : c ≤ m := by simpa [c, m] using hcS
  have hcNle' : cN ≤ m := by simpa [cN, m] using hcNle
  have hmpos : 0 < m := by omega
  have hmSn : m ≤ Lng Sn := by simp [m]
  have hmSL : m ≤ Lng S := by
    have hSpos := List.length_pos_of_ne_nil hS
    simp [m] at hmS ⊢
    omega
  have hPpre : P PreS = (P PreN).map (IncrFirstN sh) := by
    rw [show PreS = IncrFirstN sh PreN by simpa [PreS, PreN, m] using hshift,
      P_IncrFirstN_equivariance]
  have hpreLen : (P PreS).length = (P PreN).length := by
    rw [hPpre]
    simp
  have hstatus : c = m ↔ cN = m := by
    by_cases hcm : c = m
    · have hcmEq : (IdxSum (P S)).getD ((P S).length - 1) 0 = m := hcm
      have hdropS : (P S).dropLast =
          P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) :=
        P_last_anchor_butlast_68 S hS hmultiS
      have hdropSEq : (P S).dropLast = P PreS := by
        show (P S).dropLast = P (seg S 0 (m - 1))
        rw [← hcmEq]
        exact hdropS
      have hlenS : (P S).length = (P PreS).length + 1 := by
        have hh := congrArg List.length hdropSEq
        simp at hh
        omega
      by_cases hcNm : cN = m
      · exact ⟨fun _ => hcNm, fun _ => hcm⟩
      · have hcNlt : cN < m := by omega
        have hcNltE : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 < m := hcNlt
        have hdropN := P_dropLast_seg_zero_after_anchor_68 Sn m hSn
          hmultiSn hcNltE hmSn
        have hlenN : (P PreN).length = (P Sn).length := by
          have hh := congrArg List.length hdropN
          simp at hh
          have hpreNPos : 0 < (P (seg Sn 0 (m - 1))).length :=
            List.length_pos_of_ne_nil (P_nonempty _)
          show (P (seg Sn 0 (m - 1))).length = (P Sn).length
          omega
        exfalso
        omega
    · have hclt : c < m := by omega
      have hcltE : (IdxSum (P S)).getD ((P S).length - 1) 0 < m := hclt
      have hdropS := P_dropLast_seg_zero_after_anchor_68 S m hS
        hmultiS hcltE hmSL
      have hlenS : (P PreS).length = (P S).length := by
        have hh := congrArg List.length hdropS
        simp at hh
        have hprePos : 0 < (P (seg S 0 (m - 1))).length :=
          List.length_pos_of_ne_nil (P_nonempty _)
        show (P (seg S 0 (m - 1))).length = (P S).length
        omega
      by_cases hcNm : cN = m
      · have hcNmEq : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 = m := hcNm
        have hdropN : (P Sn).dropLast =
            P (seg Sn 0 ((IdxSum (P Sn)).getD ((P Sn).length - 1) 0 - 1)) :=
          P_last_anchor_butlast_68 Sn hSn hmultiSn
        have hdropNEq : (P Sn).dropLast = P PreN := by
          show (P Sn).dropLast = P (seg Sn 0 (m - 1))
          rw [← hcNmEq]
          exact hdropN
        have hlenN : (P Sn).length = (P PreN).length + 1 := by
          have hh := congrArg List.length hdropNEq
          simp at hh
          omega
        exfalso
        omega
      · exact ⟨fun h => (hcm h).elim, fun h => (hcNm h).elim⟩
  have hbutShift : (P S).dropLast =
      ((P Sn).dropLast).map (IncrFirstN sh) := by
    by_cases hcm : c = m
    · have hcNm := hstatus.mp hcm
      have hcmEq : (IdxSum (P S)).getD ((P S).length - 1) 0 = m := hcm
      have hcNmEq : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 = m := hcNm
      have hdropS : (P S).dropLast =
          P (seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1)) :=
        P_last_anchor_butlast_68 S hS hmultiS
      have hdropN : (P Sn).dropLast =
          P (seg Sn 0 ((IdxSum (P Sn)).getD ((P Sn).length - 1) 0 - 1)) :=
        P_last_anchor_butlast_68 Sn hSn hmultiSn
      calc
        (P S).dropLast = P PreS := by
          show (P S).dropLast = P (seg S 0 (m - 1))
          rw [← hcmEq]
          exact hdropS
        _ = (P PreN).map (IncrFirstN sh) := hPpre
        _ = ((P Sn).dropLast).map (IncrFirstN sh) := by
          rw [show (P Sn).dropLast = P PreN by
            show (P Sn).dropLast = P (seg Sn 0 (m - 1))
            rw [← hcNmEq]
            exact hdropN]
    · have hclt : c < m := by omega
      have hcNlt : cN < m := by
        have := hstatus
        omega
      have hcltE : (IdxSum (P S)).getD ((P S).length - 1) 0 < m := hclt
      have hcNltE : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 < m := hcNlt
      have hdropS : (P (seg S 0 (m - 1))).dropLast = (P S).dropLast :=
        P_dropLast_seg_zero_after_anchor_68 S m hS hmultiS hcltE hmSL
      have hdropN : (P (seg Sn 0 (m - 1))).dropLast = (P Sn).dropLast :=
        P_dropLast_seg_zero_after_anchor_68 Sn m hSn hmultiSn hcNltE hmSn
      have hPpreE : P (seg S 0 (m - 1)) =
          (P (seg Sn 0 (m - 1))).map (IncrFirstN sh) := hPpre
      rw [← hdropS, ← hdropN, hPpreE]
      exact List.map_dropLast.symm
  have hceq : c = cN := by
    show (IdxSum (P S)).getD ((P S).length - 1) 0 =
      (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
    rw [last_anchor_eq_sum_dropLast_68 S,
      last_anchor_eq_sum_dropLast_68 Sn]
    rw [hbutShift]
    simp [List.map_map, Function.comp_def, IncrFirstN_eq_map]
  have hend0 : entry S 0 c = entry Sn 0 cN + sh := by
    by_cases hcm : c = m
    · have hcNm := hstatus.mp hcm
      simpa [hcm, hcNm] using hbound0
    · have hclt : c < m := by omega
      have hcPreN : c < Lng PreN := by simp [PreN, m]; omega
      have hcPreS : c < Lng PreS := by simp [PreS, m]; omega
      have hh : entry PreS 0 c = entry PreN 0 c + sh := by
        rw [show PreS = IncrFirstN sh PreN by
          simpa [PreS, PreN, m] using hshift]
        exact entry_IncrFirstN_zero sh PreN c hcPreN
      rw [entry_seg S 0 (m - 1) 0 c hcPreS,
        entry_seg Sn 0 (m - 1) 0 c hcPreN] at hh
      simpa [hceq] using hh
  have hend1 : entry S 1 c ≤ entry Sn 1 cN := by
    by_cases hcm : c = m
    · have hcNm := hstatus.mp hcm
      simpa [hcm, hcNm] using hbound1
    · have hclt : c < m := by omega
      have hcPreN : c < Lng PreN := by simp [PreN, m]; omega
      have hcPreS : c < Lng PreS := by simp [PreS, m]; omega
      have hh : entry PreS 1 c = entry PreN 1 c := by
        rw [show PreS = IncrFirstN sh PreN by
          simpa [PreS, PreN, m] using hshift]
        exact entry_IncrFirstN_one sh PreN c
      rw [entry_seg S 0 (m - 1) 1 c hcPreS,
        entry_seg Sn 0 (m - 1) 1 c hcPreN] at hh
      simpa [hceq] using hh.le
  exact ⟨hceq, hend0, hend1, hbutShift⟩

/-! The positive-row-one tiling case.  These small wrappers keep the rest of
the proof in the article's `j₋₂ / w / δ` coordinates while delegating the
literal `oper` expansion to the generic §6.6 tiling API. -/

private theorem oper_d1pos_parent_lt_68
    (N : PS) (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1) :
    parent N 1 (Lng N - 1) < Lng N - 1 := by
  have hnext := hasParent_next_fseq N 1 (Lng N - 1) (by simpa [hi] using hp)
  exact (nextR_implies_row0 N 1 (parent N 1 (Lng N - 1))
    (Lng N - 1) hnext).1

private theorem length_oper_d1pos_68
    (N : PS) (n : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1) :
    Lng (oper N n) = parent N 1 (Lng N - 1) +
      n * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
  simpa [hi] using length_oper_tiling N n hlen hzero hp

private theorem entry_oper_d1pos_zero_68
    (N : PS) (n q s : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n)
    (hs : s < Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry (oper N n) 0
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s) =
      entry N 0 (parent N 1 (Lng N - 1) + s) +
        q * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) := by
  simpa [hi] using entry_oper_tiling_block_zero N n q s hlen hzero hp hq
    (by simpa [hi] using hs)

private theorem entry_oper_d1pos_one_68
    (N : PS) (n q s : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n)
    (hs : s < Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry (oper N n) 1
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s) =
      entry N 1 (parent N 1 (Lng N - 1) + s) := by
  simpa [hi] using entry_oper_tiling_block_one N n q s hlen hzero hp hq
    (by simpa [hi] using hs)

private theorem entry_oper_d1pos_prefix_68
    (N : PS) (n i x : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hx : x < parent N 1 (Lng N - 1)) :
    entry (oper N n) i x = entry N i x := by
  exact entry_oper_tiling_prefix N n i x hlen hzero hp
    (by simpa [hi] using hx)

/-- A slice ending before block `q + 1` is independent of any later tiling
blocks.  This is the period-reduction step used to normalize the hard case. -/
private theorem seg_oper_d1pos_period_reduce_68
    (N : PS) (n q a b : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hqn : q + 1 ≤ n)
    (hb : b < parent N 1 (Lng N - 1) +
      (q + 1) * (Lng N - 1 - parent N 1 (Lng N - 1))) :
    seg (oper N n) a b = seg (oper N (q + 1)) a b := by
  let j₀ := parent N 1 (Lng N - 1)
  let w := Lng N - 1 - j₀
  have hj₀lt : j₀ < Lng N - 1 := by
    simpa [j₀] using oper_d1pos_parent_lt_68 N hp hi
  have hw : 0 < w := by simp [w]; omega
  apply List.ext_getElem
  · simp
  · intro r hrL hrR
    rw [seg_getElem_68 (oper N n) a b r hrL,
      seg_getElem_68 (oper N (q + 1)) a b r hrR]
    let x := a + r
    have hxle : x ≤ b := by
      simp only [length_seg] at hrL
      simp [x]
      omega
    by_cases hxpre : x < j₀
    · rw [entry_oper_d1pos_prefix_68 N n 0 x hlen hzero hp hi hxpre,
        entry_oper_d1pos_prefix_68 N (q + 1) 0 x hlen hzero hp hi hxpre,
        entry_oper_d1pos_prefix_68 N n 1 x hlen hzero hp hi hxpre,
        entry_oper_d1pos_prefix_68 N (q + 1) 1 x hlen hzero hp hi hxpre]
    · have hxge : j₀ ≤ x := by omega
      let qx := (x - j₀) / w
      let sx := (x - j₀) % w
      have hsx : sx < w := Nat.mod_lt _ hw
      have hxsplit : x = j₀ + qx * w + sx := by
        calc
          x = j₀ + (x - j₀) := by omega
          _ = j₀ + (w * ((x - j₀) / w) + (x - j₀) % w) := by
            rw [Nat.div_add_mod]
          _ = j₀ + qx * w + sx := by
            simp [qx, sx, Nat.mul_comm, Nat.add_assoc]
      have hqxq : qx < q + 1 := by
        rw [Nat.div_lt_iff_lt_mul hw]
        have : x < j₀ + (q + 1) * w := by
          dsimp [j₀, w] at hb ⊢
          omega
        omega
      have hqxn : qx < n := hqxq.trans_le hqn
      rw [show a + r = x by rfl, hxsplit,
        entry_oper_d1pos_zero_68 N n qx sx hlen hzero hp hi hqxn
          (by simpa [w, j₀] using hsx),
        entry_oper_d1pos_zero_68 N (q + 1) qx sx hlen hzero hp hi hqxq
          (by simpa [w, j₀] using hsx),
        entry_oper_d1pos_one_68 N n qx sx hlen hzero hp hi hqxn
          (by simpa [w, j₀] using hsx),
        entry_oper_d1pos_one_68 N (q + 1) qx sx hlen hzero hp hi hqxq
          (by simpa [w, j₀] using hsx)]

/-- A sub-slice contained in one positive-row-one block is the corresponding
source slice with a uniform row-zero shift. -/
private theorem seg_oper_d1pos_block_eq_68
    (N : PS) (n q s₀ e₀ : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n) (hse : s₀ ≤ e₀)
    (he : e₀ < Lng N - 1 - parent N 1 (Lng N - 1)) :
    seg (oper N n)
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + e₀) =
      IncrFirstN
        (q * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))))
        (seg N (parent N 1 (Lng N - 1) + s₀)
          (parent N 1 (Lng N - 1) + e₀)) := by
  let j₀ := parent N 1 (Lng N - 1)
  let w := Lng N - 1 - j₀
  let δ := entry N 0 (Lng N - 1) - entry N 0 j₀
  let sh := q * δ
  apply List.ext_getElem
  · simp [IncrFirstN_eq_map]
    omega
  · intro r hrL hrR
    have hr : s₀ + r < w := by
      simp only [length_seg] at hrL
      dsimp [j₀, w] at he ⊢
      omega
    have hrN : r < Lng (seg N (j₀ + s₀) (j₀ + e₀)) := by
      simpa [IncrFirstN_eq_map] using hrR
    rw [seg_getElem_68 (oper N n)
        (j₀ + q * w + s₀) (j₀ + q * w + e₀) r hrL]
    simp only [IncrFirstN_eq_map, List.getElem_map]
    rw [seg_getElem_68 N (j₀ + s₀) (j₀ + e₀) r hrN]
    rw [show j₀ + q * w + s₀ + r = j₀ + q * w + (s₀ + r) by omega,
      show j₀ + s₀ + r = j₀ + (s₀ + r) by omega,
      entry_oper_d1pos_zero_68 N n q (s₀ + r) hlen hzero hp hi hq
        (by simpa [j₀, w] using hr),
      entry_oper_d1pos_one_68 N n q (s₀ + r) hlen hzero hp hi hq
        (by simpa [j₀, w] using hr)]

private theorem P_seg_oper_d1pos_block_eq_68
    (N : PS) (n q s₀ e₀ : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n) (hse : s₀ ≤ e₀)
    (he : e₀ < Lng N - 1 - parent N 1 (Lng N - 1)) :
    P (seg (oper N n)
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
        (parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + e₀)) =
      (P (seg N (parent N 1 (Lng N - 1) + s₀)
        (parent N 1 (Lng N - 1) + e₀))).map
          (IncrFirstN (q * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))))) := by
  rw [seg_oper_d1pos_block_eq_68 N n q s₀ e₀ hlen hzero hp hi hq hse he,
    P_IncrFirstN_equivariance]

private theorem TrMax_IncrFirstN_68 (sh : ℕ) (S : PS) :
    TrMax (IncrFirstN sh S) = TrMax S := by
  simp [TrMax, nextR_IncrFirstN_ri]

/-- Conditional formula-G trunk correspondence.  The reference endpoint may
be capped at the source's old last column; only the prefix through `c` is
needed. -/
private theorem TrMax_seg_oper_d1pos_eq_span_68
    (N : PS) (n q s₀ a b j₀' j₁' sh : ℕ)
    (_hNT : TPS N) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧
      entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1))
      (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hq : q < n)
    (haLast : a < Lng N - 1)
    (ha : a = parent N 1 (Lng N - 1) + s₀)
    (hs₀ : s₀ < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj₀ : j₀' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s₀)
    (hsh : sh = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hb : b ≤ Lng N - 1) (hab : a < b)
    (hspan : b ≤ a + (j₁' - j₀'))
    (hlt : j₀' < j₁') (hj₁ : j₁' < Lng (oper N n))
    (hconf : TrMax (seg N a b) ≤ b - 1 - a)
    (hstop : nextR (seg (oper N n) j₀' j₁') 1
      (TrMax (seg N a b)) (TrMax (seg N a b) + 1) = false) :
    TrMax (seg (oper N n) j₀' j₁') = TrMax (seg N a b) := by
  let j₀ := parent N 1 (Lng N - 1)
  let w := Lng N - 1 - j₀
  let Mp := seg (oper N n) j₀' j₁'
  let Np := seg N a b
  let Nps := IncrFirstN sh Np
  let c := b - 1 - a
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hNpsT : TPS Nps := by
    simpa [Nps, TPS, IncrFirstN_eq_map] using hNpT
  have htrShift : TrMax Nps = TrMax Np := by
    exact TrMax_IncrFirstN_68 sh Np
  have hcN : c < Lng Nps := by
    simp [c, Nps, Np]
    omega
  have hcM : c < Lng Mp := by
    simp [c, Mp]
    omega
  have hagree : ∀ s, s ≤ c →
      Mp.getD s (0, 0) = Nps.getD s (0, 0) := by
    intro s hsc
    have hsM : s < Lng Mp := hsc.trans_lt hcM
    have hsN : s < Lng Np := by
      simp [Np, c] at hsc ⊢
      omega
    have hsNs : s < Lng Nps := by simpa [Nps] using hsN
    have hsoff : s₀ + s < w := by
      dsimp [c, w, j₀] at hsc ⊢
      omega
    rw [getD_eq_getElem_idx Mp (0, 0) hsM,
      getD_eq_getElem_idx Nps (0, 0) hsNs,
      seg_getElem_68 (oper N n) j₀' j₁' s hsM]
    simp only [Nps, IncrFirstN_eq_map, List.getElem_map]
    rw [seg_getElem_68 N a b s hsN]
    have hidxM : j₀' + s = j₀ + q * w + (s₀ + s) := by
      simp [hj₀, j₀, w, Nat.add_assoc]
    have hidxN : a + s = j₀ + (s₀ + s) := by
      simp [ha, j₀, Nat.add_assoc]
    rw [hidxM, hidxN,
      entry_oper_d1pos_zero_68 N n q (s₀ + s) hlen hzero hp hi hq
        (by simpa [j₀, w] using hsoff),
      entry_oper_d1pos_one_68 N n q (s₀ + s) hlen hzero hp hi hq
        (by simpa [j₀, w] using hsoff)]
    simp [hsh, j₀, w]
  have hstopShift : nextR Mp 1 (TrMax Nps) (TrMax Nps + 1) = false := by
    simpa [Mp, Np, htrShift] using hstop
  have hh := TrMax_eq_of_prefix_agree_68 Mp Nps c hMpT hNpsT hagree
    hcM hcN (by simpa [Np, htrShift] using hconf) hstopShift
  simpa [Mp, Np, htrShift] using hh

/-- The exact information required from the positive-row-one block geometry.
It deliberately contains no descendingness premise, so its eventual proof is
non-circular; descendingness of the source branch comes from the rank IH. -/
private def d1posAlignment_68 (N Mp : PS) : Prop :=
  ∃ a b sh LOW TL,
    a < b ∧ b ≤ Lng N - 1 ∧ le0 N a b = true ∧
    Br Mp = LOW ++ [TL] ∧ Br (seg N a b) ≠ [] ∧
    LOW.length = (Br (seg N a b)).length - 1 ∧
    (∀ J, J < LOW.length →
      entry (LOW.getD J []) 0 0 =
          entry ((Br (seg N a b)).getD J []) 0 0 + sh ∧
      entry (LOW.getD J []) 1 0 =
          entry ((Br (seg N a b)).getD J []) 1 0) ∧
    entry TL 0 0 =
        entry ((Br (seg N a b)).getD
          ((Br (seg N a b)).length - 1) []) 0 0 + sh ∧
    entry TL 1 0 ≤
        entry ((Br (seg N a b)).getD
          ((Br (seg N a b)).length - 1) []) 1 0

private theorem descending_of_d1posAlignment_68
    (k : ℕ)
    (ih : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N Mp : PS) (hN : SkTPS k N) (hmonoN : monoT N = true)
    (halign : d1posAlignment_68 N Mp) :
    descending (Br Mp) := by
  rcases halign with
    ⟨a, b, sh, LOW, TL, hab, hb, hle, hBr, hQne, hlen,
      hheads, htail0, htail1⟩
  let Q := Br (seg N a b)
  have hdesc : descending Q := by
    simpa [Q] using ih N a b hN hmonoN hab hb
      (by simpa [leR] using hle)
  have hall : descending (LOW ++ [TL]) :=
    descending_shift_append hdesc (by simpa [Q] using hQne) hlen
      (fun J hJ => (hheads J hJ).1)
      (fun J hJ => (hheads J hJ).2)
      (by simpa [Q] using htail0)
      (by simpa [Q] using htail1)
  rw [hBr]
  exact hall

/-- Convert the last-anchor comparison of two branch regions into the exact
alignment record consumed by the rank-induction assembly. -/
private theorem d1posAlignment_of_anchor_data_68
    (N Mp S Sn : PS) (a b sh : ℕ)
    (hab : a < b) (hb : b ≤ Lng N - 1) (hle : le0 N a b = true)
    (hBrM : Br Mp = P S) (hBrN : Br (seg N a b) = P Sn)
    (hST : TPS S) (hSnT : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hshift :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
      seg S 0 (c - 1) = IncrFirstN sh (seg Sn 0 (cN - 1)))
    (hend0 :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
      entry S 0 c = entry Sn 0 cN + sh)
    (hend1 :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
      entry S 1 c ≤ entry Sn 1 cN) :
    d1posAlignment_68 N Mp := by
  let JS := (P S).length - 1
  let c := (IdxSum (P S)).getD JS 0
  let JN := (P Sn).length - 1
  let cN := (IdxSum (P Sn)).getD JN 0
  let LOW := ((P Sn).dropLast).map (IncrFirstN sh)
  let TL := seg S c (Lng S - 1)
  have hbut := P_last_anchor_butlast_68 Sn hSnT hmultiSn
  have hcollapse := P_last_anchor_collapse_68 S (seg Sn 0 (cN - 1))
    (P Sn) sh hST hmultiS (by simpa [c, cN, JS, JN] using hshift)
    (by simpa [cN, JN] using hbut)
  have hfold : Br Mp = LOW ++ [TL] := by
    rw [hBrM]
    simpa [LOW, TL, c, cN, JS, JN] using hcollapse
  have hQne : Br (seg N a b) ≠ [] := by
    rw [hBrN]
    exact P_nonempty Sn
  have hlen : LOW.length = (Br (seg N a b)).length - 1 := by
    simp [LOW, hBrN]
  have hheads : ∀ J, J < LOW.length →
      entry (LOW.getD J []) 0 0 =
          entry ((Br (seg N a b)).getD J []) 0 0 + sh ∧
      entry (LOW.getD J []) 1 0 =
          entry ((Br (seg N a b)).getD J []) 1 0 := by
    intro J hJ
    have hJdrop : J < (P Sn).dropLast.length := by simpa [LOW] using hJ
    have hJP : J < (P Sn).length := hJdrop.trans_le (by simp)
    have hget : LOW.getD J [] = IncrFirstN sh ((P Sn).getD J []) := by
      rw [getD_eq_getElem_idx LOW [] hJ,
        getD_eq_getElem_idx (P Sn) [] hJP]
      simp [LOW, List.getElem_map, List.getElem_dropLast]
    have hCpos : 0 < Lng ((P Sn).getD J []) :=
      P_component_nonempty Sn J hSnT hJP
    rw [hget, entry_IncrFirstN_zero sh ((P Sn).getD J []) 0 hCpos,
      entry_IncrFirstN_one]
    simpa [hBrN]
  have hlastSn := P_last_anchor_getD_68 Sn hSnT hmultiSn
  have href : (Br (seg N a b)).getD
      ((Br (seg N a b)).length - 1) [] =
      seg Sn cN (Lng Sn - 1) := by
    simpa [hBrN, cN, JN] using hlastSn
  have htail0 : entry TL 0 0 =
      entry ((Br (seg N a b)).getD
        ((Br (seg N a b)).length - 1) []) 0 0 + sh := by
    rw [href]
    rw [show entry TL 0 0 = entry S 0 c by
      simpa [TL, c, JS] using
        P_last_anchor_tail_entry_68 S 0 hST hmultiS]
    rw [show entry (seg Sn cN (Lng Sn - 1)) 0 0 = entry Sn 0 cN by
      simpa [cN, JN] using
        P_last_anchor_tail_entry_68 Sn 0 hSnT hmultiSn]
    simpa [c, cN, JS, JN] using hend0
  have htail1 : entry TL 1 0 ≤
      entry ((Br (seg N a b)).getD
        ((Br (seg N a b)).length - 1) []) 1 0 := by
    rw [href]
    rw [show entry TL 1 0 = entry S 1 c by
      simpa [TL, c, JS] using
        P_last_anchor_tail_entry_68 S 1 hST hmultiS]
    rw [show entry (seg Sn cN (Lng Sn - 1)) 1 0 = entry Sn 1 cN by
      simpa [cN, JN] using
        P_last_anchor_tail_entry_68 Sn 1 hSnT hmultiSn]
    simpa [c, cN, JS, JN] using hend1
  exact ⟨a, b, sh, LOW, TL, hab, hb, hle, hfold, hQne, hlen,
    hheads, htail0, htail1⟩

private theorem d1posAlignment_of_P_data_68
    (N Mp S Sn : PS) (a b sh : ℕ)
    (hab : a < b) (hb : b ≤ Lng N - 1) (hle : le0 N a b = true)
    (hBrM : Br Mp = P S) (hBrN : Br (seg N a b) = P Sn)
    (hST : TPS S) (hSnT : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hPshift : (P S).dropLast =
      ((P Sn).dropLast).map (IncrFirstN sh))
    (hend0 :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
      entry S 0 c = entry Sn 0 cN + sh)
    (hend1 :
      let c := (IdxSum (P S)).getD ((P S).length - 1) 0
      let cN := (IdxSum (P Sn)).getD ((P Sn).length - 1) 0
      entry S 1 c ≤ entry Sn 1 cN) :
    d1posAlignment_68 N Mp := by
  let JS := (P S).length - 1
  let c := (IdxSum (P S)).getD JS 0
  let JN := (P Sn).length - 1
  let cN := (IdxSum (P Sn)).getD JN 0
  let LOW := ((P Sn).dropLast).map (IncrFirstN sh)
  let TL := seg S c (Lng S - 1)
  obtain ⟨_, _, _, _, hfoldP⟩ := P_last_anchor_68 S hST hmultiS
  have hfold : Br Mp = LOW ++ [TL] := by
    rw [hBrM]
    have htake : (P S).take ((P S).length - 1) = (P S).dropLast :=
      take_pred_eq_dropLast_68 (P S)
    simpa [LOW, TL, JS, c, htake, hPshift] using hfoldP
  have hQne : Br (seg N a b) ≠ [] := by
    rw [hBrN]
    exact P_nonempty Sn
  have hlen : LOW.length = (Br (seg N a b)).length - 1 := by
    simp [LOW, hBrN]
  have hheads : ∀ J, J < LOW.length →
      entry (LOW.getD J []) 0 0 =
          entry ((Br (seg N a b)).getD J []) 0 0 + sh ∧
      entry (LOW.getD J []) 1 0 =
          entry ((Br (seg N a b)).getD J []) 1 0 := by
    intro J hJ
    have hJdrop : J < (P Sn).dropLast.length := by simpa [LOW] using hJ
    have hJP : J < (P Sn).length := hJdrop.trans_le (by simp)
    have hget : LOW.getD J [] = IncrFirstN sh ((P Sn).getD J []) := by
      rw [getD_eq_getElem_idx LOW [] hJ,
        getD_eq_getElem_idx (P Sn) [] hJP]
      simp [LOW, List.getElem_map, List.getElem_dropLast]
    have hCpos : 0 < Lng ((P Sn).getD J []) :=
      P_component_nonempty Sn J hSnT hJP
    rw [hget, entry_IncrFirstN_zero sh ((P Sn).getD J []) 0 hCpos,
      entry_IncrFirstN_one]
    simpa [hBrN]
  have hlastSn := P_last_anchor_getD_68 Sn hSnT hmultiSn
  have href : (Br (seg N a b)).getD
      ((Br (seg N a b)).length - 1) [] =
      seg Sn cN (Lng Sn - 1) := by
    simpa [hBrN, cN, JN] using hlastSn
  have htail0 : entry TL 0 0 =
      entry ((Br (seg N a b)).getD
        ((Br (seg N a b)).length - 1) []) 0 0 + sh := by
    rw [href]
    rw [show entry TL 0 0 = entry S 0 c by
      simpa [TL, c, JS] using
        P_last_anchor_tail_entry_68 S 0 hST hmultiS]
    rw [show entry (seg Sn cN (Lng Sn - 1)) 0 0 = entry Sn 0 cN by
      simpa [cN, JN] using
        P_last_anchor_tail_entry_68 Sn 0 hSnT hmultiSn]
    simpa [c, cN, JS, JN] using hend0
  have htail1 : entry TL 1 0 ≤
      entry ((Br (seg N a b)).getD
        ((Br (seg N a b)).length - 1) []) 1 0 := by
    rw [href]
    rw [show entry TL 1 0 = entry S 1 c by
      simpa [TL, c, JS] using
        P_last_anchor_tail_entry_68 S 1 hST hmultiS]
    rw [show entry (seg Sn cN (Lng Sn - 1)) 1 0 = entry Sn 1 cN by
      simpa [cN, JN] using
        P_last_anchor_tail_entry_68 Sn 1 hSnT hmultiSn]
    simpa [c, cN, JS, JN] using hend1
  exact ⟨a, b, sh, LOW, TL, hab, hb, hle, hfold, hQne, hlen,
    hheads, htail0, htail1⟩

/-- Package the reusable end of every positive-row-one geometric regime: a
uniformly shifted prefix and the two boundary comparisons determine the whole
branch alignment. -/
private theorem d1posAlignment_of_shift_boundary_68
    (N Mp S Sn : PS) (a b sh : ℕ)
    (hab : a < b) (hb : b ≤ Lng N - 1) (hle : le0 N a b = true)
    (hBrM : Br Mp = P S) (hBrN : Br (seg N a b) = P Sn)
    (hST : TPS S) (hSnT : TPS Sn)
    (hmultiS : 1 < (P S).length) (hmultiSn : 1 < (P Sn).length)
    (hmS : Lng Sn - 1 ≤ Lng S - 1)
    (hcS : (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng Sn - 1)
    (hshift : seg S 0 (Lng Sn - 1 - 1) =
      IncrFirstN sh (seg Sn 0 (Lng Sn - 1 - 1)))
    (hbound0 : entry S 0 (Lng Sn - 1) =
      entry Sn 0 (Lng Sn - 1) + sh)
    (hbound1 : entry S 1 (Lng Sn - 1) ≤
      entry Sn 1 (Lng Sn - 1)) :
    d1posAlignment_68 N Mp := by
  have hlenP := P_length_eq_of_shift_prefix_boundary_68 S Sn sh hST hSnT
    hmultiS hmultiSn hmS hcS hshift hbound0
  obtain ⟨hceq, hend0, hend1, hPshift⟩ :=
    last_anchor_coincide_shift_prefix_68 S Sn sh hST hSnT
      hmultiS hmultiSn hmS hcS hlenP hshift hbound0 hbound1
  apply d1posAlignment_of_P_data_68 N Mp S Sn a b sh hab hb hle hBrM hBrN
    hST hSnT hmultiS hmultiSn hPshift
  · simpa [hceq] using hend0
  · simpa [hceq] using hend1

/-! ## rank 帰納の組み立てと WLOG 還元

以下は §6.8 命題（標準形の切片と `Br` の降順性の関係）本体の組み立て。
rank 帰納の 4 ケースのうち、d1pos（末尾第 1 成分が正で切片が旧末尾に届く
タイル領域）のケースだけが未証明で、`RankSuccD1posLeg` という名前付き仮定
として露出させてある（Isabelle 側の `oper_d1pos_notbrle_*` brick 群に相当）。
残る全ケースと WLOG 還元は無条件に完結している。 -/

/-- 標準形は必ずどこかの rank 階層に属する（`ST_PS = ⋃ₖ SkT_PS` の一方向）。 -/
private theorem STPS_exists_rank_68 (M : PS) (hM : STPS M) :
    ∃ k, SkTPS k M := by
  induction hM with
  | diag u v huv => exact ⟨0, u, v, rfl, huv⟩
  | oper hN n hn ih =>
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, _, n, rfl, hk, hn⟩

/-- The single still-unproved leg of the §6.8 rank induction: the source `N`
ends in a positive-row-one column, `M = N[n]` tiles, and the slice reaches the
old last column.  Everything else in the proposition is proved unconditionally
below.  (Isabelle: the `oper_d1pos_*` brick family feeding
`m_6_8_slice_Br_descending_monoT`.) -/
def RankSuccD1posLeg : Prop :=
  ∀ (k : ℕ)
    (_ : ∀ (X : PS) (a b : ℕ), SkTPS k X → monoT X = true →
      a < b → b ≤ Lng X - 1 → leR X 0 a b = true →
      descending (Br (seg X a b)))
    (N M : PS) (n j₀' j₁' : ℕ),
    SkTPS k N → M = oper N n → 1 ≤ n →
    1 < Lng N → multiT N = false →
    0 < entry N 1 (Lng N - 1) →
    j₀' < j₁' → j₁' ≤ Lng M - 1 →
    Lng N - 1 ≤ j₁' →
    leR M 0 j₀' j₁' = true →
    descending (Br (seg M j₀' j₁'))

/-- §6.8 monoT core（`m_6_8_slice_Br_descending_monoT` 相当）、d1pos leg を
仮定に持つ条件付き形。rank `k` の帰納で、rank 0 は対角列（`Br` 空）、
`Suc k` は前駆 `N` の multi / 非 multi × 切片位置 × 末尾行の場合分け。 -/
theorem slice_Br_descending_monoT_of_d1pos
    (d1pos : RankSuccD1posLeg) (k : ℕ) :
    ∀ (M : PS) (j₀' j₁' : ℕ), SkTPS k M → monoT M = true →
      j₀' < j₁' → j₁' ≤ Lng M - 1 → leR M 0 j₀' j₁' = true →
      descending (Br (seg M j₀' j₁')) := by
  induction k with
  | zero =>
      intro M j₀' j₁' hM _ hlt hj₁ _
      exact rankZero_slice_Br_descending M j₀' j₁' hM hlt hj₁
  | succ k ih =>
      intro M j₀' j₁' hM hmono hlt hj₁ hanc
      rcases hM with ⟨N, n, hMdef, hN, hn⟩
      by_cases hmultiN : multiT N = true
      · exact rankSucc_multi_predecessor k ih N M n j₀' j₁' hN hMdef hn
          hmultiN hmono hlt hj₁ hanc
      · have hnm : multiT N = false :=
          Bool.eq_false_of_not_eq_true hmultiN
        have hMlen : 1 < Lng M := by omega
        by_cases hNlen : 1 < Lng N
        · by_cases hjsmall : j₁' < Lng N - 1
          · exact rankSucc_nonmulti_prefix k ih N M n j₀' j₁' hN hMdef hn
              hNlen hnm hlt hjsmall hj₁ hanc
          · have hjlarge : Lng N - 1 ≤ j₁' := by omega
            by_cases hd0 : entry N 1 (Lng N - 1) = 0
            · exact rankSucc_d0zero_68 k ih N M n j₀' j₁' hN hMdef hn
                hNlen hnm hd0 hlt hj₁ hjlarge hanc
            · exact d1pos k ih N M n j₀' j₁' hN hMdef hn hNlen hnm
                (by omega) hlt hj₁ hjlarge hanc
        · exfalso
          have hNT : TPS N := SkTPS_TPS k N hN
          have hNpos : 0 < Lng N := List.length_pos_of_ne_nil hNT
          have hN1 : Lng N = 1 := by omega
          have hMeq : M = N := by
            rw [hMdef]
            simp [oper, hN1]
          rw [hMeq] at hMlen
          omega

/-- §6.8 命題（標準形の切片と `Br` の降順性の関係、訂正 A7/A8 適用後の主張）、
d1pos leg のみを仮定に持つ条件付き形。単項性は `mono_ancestor_slice`。
multi な `M` では上段先祖性が切片を `j₁'` を含む単一の `P` 成分に閉じ込め
（成分左端は上段左最小値）、その成分は同 rank・monoT で、切片は成分の切片、
`le0` も移送されて monoT core が適用できる。 -/
theorem standard_slice_Br_descending_of_d1pos
    (d1pos : RankSuccD1posLeg)
    (M : PS) (j₀' j₁' : ℕ) (hM : STPS M)
    (hlt : j₀' < j₁') (hj₁ : j₁' ≤ Lng M - 1)
    (hanc : leR M 0 j₀' j₁' = true) :
    monoT (seg M j₀' j₁') = true ∧
      descending (Br (seg M j₀' j₁')) := by
  have hMT : TPS M := STPS_TPS M hM
  obtain ⟨k, hMk⟩ := STPS_exists_rank_68 M hM
  refine ⟨mono_ancestor_slice M j₀' j₁' hMT hlt hanc, ?_⟩
  by_cases hmono : monoT M = true
  · exact slice_Br_descending_monoT_of_d1pos d1pos k M j₀' j₁'
      hMk hmono hlt hj₁ hanc
  · have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hMT
    have hjM : j₁' < Lng M := by omega
    have hlen2 : 1 < Lng M := by omega
    have hzero : zeroT M = false := by
      simp [zeroT]
      omega
    have hmonoF : monoT M = false := Bool.eq_false_of_not_eq_true hmono
    have hmulti : multiT M = true := by
      simp [multiT, hzero, hmonoF]
    have hPlen : 1 < (P M).length := (P_components_multi_iff M hMT).mp hmulti
    have htotal : (IdxSum (P M)).getD (P M).length 0 = Lng M := by
      calc (IdxSum (P M)).getD (P M).length 0
          = Lng (P M).flatten := idxSum_total (P M)
        _ = Lng M := congrArg Lng (P_concat M)
    have hjlt : j₁' < (IdxSum (P M)).getD (P M).length 0 := by omega
    obtain ⟨K, hK, hK2, hK3⟩ := idxSum_locate (P M) j₁' hjlt
    have halmin := (P_leftend_lmin M K hMT hK).2
    have haj0 : (IdxSum (P M)).getD K 0 ≤ j₀' := by
      by_contra hcon
      have hcon' : j₀' < (IdxSum (P M)).getD K 0 := Nat.lt_of_not_le hcon
      have hlt2 : entry M 0 j₀' < entry M 0 ((IdxSum (P M)).getD K 0) :=
        ancestor_basic_1 M j₀' ((IdxSum (P M)).getD K 0) j₁' hMT hcon' hK2 hanc
      have hge := halmin j₀' hcon'
      omega
    have hKle : K ≤ (P M).length - 1 := by omega
    have hcomp : (P M).getD K [] = seg M ((IdxSum (P M)).getD K 0)
        ((IdxSum (P M)).getD (K + 1) 0 - 1) := P_IdxSum M K hMT hKle
    have hlenpos : 0 < Lng ((P M).getD K []) := P_component_nonempty M K hMT hK
    have hdiff := idxSum_diff (P M) K hK
    have hbge : j₁' ≤ (IdxSum (P M)).getD (K + 1) 0 - 1 := by omega
    have hbL : (IdxSum (P M)).getD (K + 1) 0 - 1 < Lng M := by
      have hmono2 := idxSum_mono (P M) (K + 1) (P M).length
        (by omega) (le_refl _)
      omega
    have hCS : SkTPS k ((P M).getD K []) := SkTPS_P_components k M hMk K hK
    have hCLng : Lng ((P M).getD K []) =
        (IdxSum (P M)).getD (K + 1) 0 - 1 + 1 - (IdxSum (P M)).getD K 0 := by
      rw [hcomp, length_seg]
    have hCgt1 : 1 < Lng ((P M).getD K []) := by omega
    have hCzm := P_components_nonmulti M hMT ((P M).getD K []) (by
      rw [getD_eq_getElem_idx (P M) [] hK]
      exact List.getElem_mem hK)
    have hCmono : monoT ((P M).getD K []) = true := by
      rcases hCzm with hz | hm
      · exfalso
        have hz1 : Lng ((P M).getD K []) = 1 := by
          simp [zeroT] at hz
          exact hz.1
        omega
      · exact hm
    have hsegeq : seg M j₀' j₁' = seg ((P M).getD K [])
        (j₀' - (IdxSum (P M)).getD K 0)
        (j₁' - (IdxSum (P M)).getD K 0) := by
      rw [hcomp]
      rw [seg_of_seg_68 M ((IdxSum (P M)).getD K 0)
        ((IdxSum (P M)).getD (K + 1) 0 - 1)
        (j₀' - (IdxSum (P M)).getD K 0) (j₁' - (IdxSum (P M)).getD K 0)
        (by omega) (by omega)]
      rw [Nat.add_sub_cancel' haj0,
        Nat.add_sub_cancel' (by omega : (IdxSum (P M)).getD K 0 ≤ j₁')]
    have hancC : leR ((P M).getD K []) 0
        (j₀' - (IdxSum (P M)).getD K 0)
        (j₁' - (IdxSum (P M)).getD K 0) = true := by
      have hstep := leR0_seg_adm M ((IdxSum (P M)).getD K 0)
        ((IdxSum (P M)).getD (K + 1) 0 - 1)
        (j₀' - (IdxSum (P M)).getD K 0) (j₁' - (IdxSum (P M)).getD K 0)
        (by omega) hbL
        (by rw [length_seg]; omega) (by rw [length_seg]; omega)
      rw [hcomp, hstep, Nat.add_sub_cancel' haj0,
        Nat.add_sub_cancel' (by omega : (IdxSum (P M)).getD K 0 ≤ j₁')]
      exact hanc
    have hltC : j₀' - (IdxSum (P M)).getD K 0 <
        j₁' - (IdxSum (P M)).getD K 0 := by omega
    have hj₁C : j₁' - (IdxSum (P M)).getD K 0 ≤
        Lng ((P M).getD K []) - 1 := by omega
    rw [hsegeq]
    exact slice_Br_descending_monoT_of_d1pos d1pos k ((P M).getD K [])
      _ _ hCS hCmono hltC hj₁C hancC

#print axioms cdom_trans
#print axioms descending_iff_pairwise
#print axioms descending_take
#print axioms descending_append_of_cross
#print axioms descending_append
#print axioms descending_const_head
#print axioms cdom_IncrFirstN_iff
#print axioms descending_map_IncrFirstN
#print axioms descending_shift_append
#print axioms descending_P_of_ST
#print axioms seg_of_seg_68
#print axioms Br_seg_reshape_68
#print axioms standard_slice_Br_descending_of_slice_P
#print axioms descending_Br_of_branch_le0
#print axioms monoT_seg_of_le0_68
#print axioms slice_Br_descending_monoT_of_d1pos
#print axioms standard_slice_Br_descending_of_d1pos

end PSS
