import «6».«6.2-P-fseq»
import «6».«6.2-P-additivity»
import «6».«6.2-nonmulti-fseq»
import «6».«6.2-P-components-nonmulti»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-one-column»
import «6».«6.6-reduced-leftend»
import «6».«6.7-standard-P-components»
import «Buchholz-1986».«Buchholz-1986-3.2-descent»
import «OTB-well-founded-syntactic».«OTB-well-founded-syntactic-cofinality»
import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Trans-preserves-monoT»
import «7».«7.3-Pred-Trans-descend»
import «8».«8.5-exchV-props»
import «8».«8.7-fseq-descend-props»
import «8».«8.7-fseq-descend-props2»

/-!
# §8.7 OT 柱 — `OTdisp_OTmulti` の Buchholz 側再組立インフラ

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTdisp_OTmulti`
  （`«8».«8.7-Trans-preserves-OT»`:109）＝ Isabelle `opx_OTmulti`
  (`isabelle/layerB/pss_wip.thy`:115556)。訂正: なし。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  **`OTdisp_OTmulti` は本ファイルでは無条件には閉じない**（理由は下記 🚨）。
  本ファイルは Isabelle `opx_OTmulti` の証明が使う **Buchholz 側の再組立 brick**
  （`opx_OT_append_rep` / `opx_operB_snoc_local` / `opx_descP_*` / `opx_leBT_min`
  / `opx_mono_Trans_singleton` / `e4x_OT_B_operB_numBT` / `Trans_singleton`）を
  Lean 無条件で移植し、さらに casea/caseb を一本化する汎用置換補題
  `OT_append_corr_om` を追加する。将来 `OTdisp_OTint` が閉じた時点で本補題群に
  配線すれば `OTdisp_OTmulti` が落ちる。

## 🚨 仮定の不一致（wave-K 教訓の適用）

Isabelle `opx_OTmulti` は **3 本の追加仮定を明示的に取る**:
`OTint`（条件 III/IV/V の内部 OT ステップ）, `TVall`（`c2sx_tailval`、条件 II の
tail 値）, `ordIntC`（内部脚の `leBT` 順序＝降下柱の弱化）。
Lean の `OTdisp_OTmulti` は `∀ N m, STPS N → multiT N → Trans N ∈ OT_B → 1 < m →
oper N m ≠ Pred N → Trans (oper N m) ∈ OT_B` で、**この 3 本をすべて落としている**。
したがって `OTdisp_OTmulti` は `opx_OTmulti` より **真に強い**。命題自体は
（最終停止性定理の帰結として）**真**だが、無条件証明には内部枝が必要で、その内部枝
（複項 host `N` の末尾 mono 成分 `L = last (P N)` が条件 III/IV/V を満たす場合の
`Trans (L[m]) ∈ OT_B`）は **`OTdisp_OTint` を mono 成分に適用したものそのもの**であり、
`OTdisp_OTint` は未証明の残差（`8.7-termination.lean` の `TerminationResidual.otInt`）。
∴ **`OTdisp_OTmulti` は現ツリーでは無条件には閉じられない**（`props_closed` は空）。

## 証明の骨格（`opx_OTmulti` 逐語）と Lean 移植の勝ち筋

複項 host `N`（`L := last (P N)` は mono 標準・`1 < Lng L`）について
`N[m] = A @ L[m]`, `P (N[m]) = P A @ P (L[m])`（`P_fseq_2`）で、host は
`Trans N = Trm (as @ [pl])`（`as := untrm (Trans A)`, `Trans L = Trm [pl]`,
`opx_mono_Trans_singleton`）。ゆえに `Trans (N[m]) = Trm (as @ cs)` で
`cs := untrm (Trans (L[m]))`（`f7x_Trans_append_Pblocks` の非零脚）。あとは
`OT_append_corr_om` に **(i) `Trans (L[m]) ∈ OT_B`** と
**(ii) `leBT (Trans (L[m])) (Trans L)`（＝降下柱、`ordIntC` の実体）** を渡せば閉じる。
(i) の mono 成分ディスパッチ（条件 I/II/VI＝交換等式 → `operB` → `e4x`、
条件 III/IV/V＝`OTdisp_OTint`）は `8.7-Trans-preserves-OT` の
`Trans_preserves_OT_dispatch_tot` の「≠ Pred・mono」枝と同型。**未配線の穴は 2 つ**:
(a) `OTdisp_OTint`（残差本体）、(b) `f7x` の零脚（`(P (L[m])).getD 0 [] = [(0,0)]`
＝`L[m]` 先頭零列）で `Trans (L[m])` が数項になる補題（`bpHeadV` は指標のみ与え、
`D_0 0` であることは未提供）。数値検証: 標準形プール 22932 本中、複項 host の末尾
mono 成分（`Lng > 1`）は **290/290 が条件 I**（内部枝 III/IV/V は経験的に空）だが、
これは移植可能な定理ではない。零脚も 42/42 で `Trans (L[m])` は数項。

- 依存（ビルド済みのみ import）: `Buchholz-1986-3.2-descent`（`buchholz_fseq_lt`）、
  `Buchholz-1986-3.3`（`buchholz_fseq_closed`）、`Buchholz-1986-2.1-order`
  （`lessBT_linear_trans`）、`OTB-well-founded-syntactic-cofinality`（`y4_descP_*`）、
  `7.3-Trans-preserves-zeroT` / `7.3-Trans-preserves-monoT`（`m_7_3_Trans_monoT`）、
  `7.3-Pred-Trans-descend`、`6.2-*`（`P_*` 機構）、`6.6-one-column`、
  `6.6-reduced-leftend`（`RTPS_TPS`）、`6.7-standard-P-components`（`SkTPS_*`）、
  `8.5-exchV-props` / `8.7-fseq-descend-props*`（`OTdisp_*` の定義を推移的に）。
-/

namespace PSS

/-! ## 1. Buchholz 側の再組立 brick -/

/-- Isabelle `oix_leBT_trans`。 -/
private theorem leBT_trans_om {a b c : BT} (hab : leBT a b = true)
    (hbc : leBT b c = true) : leBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab hbc ⊢
  rcases hab with hab | rfl
  · rcases hbc with hbc | rfl
    · exact Or.inl (lessBT_linear_trans a b c hab hbc)
    · exact Or.inl hab
  · exact hbc

/-- Isabelle `opx_leBT_min`: `D_0 0` は全 principal 項以下。 -/
private theorem leBT_min_om (p : BP) : leBT (Dprin 0 BZero) (BT.trm [p]) = true := by
  cases p with
  | db v b =>
    rcases eq_or_ne v 0 with rfl | hv
    · cases b with
      | trm bs =>
        cases bs with
        | nil => simp [leBT, Dprin, BZero]
        | cons c cs =>
          simp [leBT, Dprin, BZero, lessBT, lessBPList, lessBP]
    · have hvp : (0 : ℕ∞) < v := pos_iff_ne_zero.mpr hv
      simp [leBT, Dprin, lessBT, lessBPList, lessBP, hvp]

/-- `isOT_BPList` の要素ごとの特徴づけ。 -/
private theorem isOT_BPList_iff_om : ∀ (ps : List BP),
    isOT_BPList ps = true ↔ ∀ p ∈ ps, isOT_BP p = true
  | [] => by simp [isOT_BPList]
  | p :: ps => by
      simp only [isOT_BPList, Bool.and_eq_true, List.mem_cons]
      rw [isOT_BPList_iff_om ps]
      constructor
      · rintro ⟨h1, h2⟩ q (rfl | hq)
        · exact h1
        · exact h2 q hq
      · intro h
        exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩

/-- Isabelle `descP_append1`。 -/
private theorem descP_append1_om : ∀ (xs ys : List BP),
    descP (xs ++ ys) = true → descP xs = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: xs', ys, h => by
      simp only [List.cons_append, descP, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, descP_append1_om (y :: xs') ys h.2⟩

/-- Isabelle `oix_descP_ge_last` の本ファイル用の形: 末尾 `y` は前の全要素以下。 -/
private theorem descP_snoc_ge_all_om (xs : List BP) (y : BP)
    (h : descP (xs ++ [y]) = true) :
    ∀ p ∈ xs, leBT (BT.trm [y]) (BT.trm [p]) = true := by
  intro p hp
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
  have h' : descP (l₁ ++ (p :: (l₂ ++ [y]))) = true := by
    simpa using h
  exact y4_descP_all_le_hd (y4_descP_suffix h') (by simp)

/-- Isabelle `opx_descP_snoc_intro`。 -/
private theorem descP_snoc_intro_om : ∀ (xs : List BP) (y : BP),
    descP xs = true → (∀ p ∈ xs, leBT (BT.trm [y]) (BT.trm [p]) = true) →
    descP (xs ++ [y]) = true
  | [], _, _, _ => rfl
  | [x], y, _, j => by
      show descP [x, y] = true
      simp only [descP]
      simpa using j x (by simp)
  | x :: y' :: xs', y, d, j => by
      simp only [List.cons_append, descP, Bool.and_eq_true] at d ⊢
      refine ⟨d.1, ?_⟩
      have := descP_snoc_intro_om (y' :: xs') y d.2
        (fun p hp => j p (List.mem_cons_of_mem x hp))
      simpa using this

/-- Isabelle `opx_descP_append_rep`。 -/
private theorem descP_append_rep_om (xs : List BP) (y : BP) (m : ℕ)
    (d : descP xs = true)
    (j : ∀ p ∈ xs, leBT (BT.trm [y]) (BT.trm [p]) = true) :
    descP (xs ++ List.replicate m y) = true := by
  induction m with
  | zero => simpa using d
  | succ m ih =>
      have he : xs ++ List.replicate (m + 1) y = (xs ++ List.replicate m y) ++ [y] := by
        rw [List.replicate_succ']
        simp
      rw [he]
      refine descP_snoc_intro_om _ y ih ?_
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact j p hp'
      · have : p = y := List.eq_of_mem_replicate hp'
        subst this
        simp [leBT]

/-- Isabelle `opx_OT_append_rep`: `OT_B` の host の末尾 principal `pl` を、
`isOT_BP` かつ `≤ pl` な `be` の `m` 個のコピーで置き換えても（`T_B` 所属さえ
あれば）`OT_B` に留まる。 -/
private theorem OT_append_rep_om (as : List BP) (pl be : BP) (m : ℕ)
    (hostOT : BT.trm (as ++ [pl]) ∈ OT_B)
    (beOT : isOT_BP be = true)
    (junc : leBT (BT.trm [be]) (BT.trm [pl]) = true)
    (tb : BT.trm (as ++ List.replicate m be) ∈ T_B) :
    BT.trm (as ++ List.replicate m be) ∈ OT_B := by
  have hOT : isOT_BT (BT.trm (as ++ [pl])) = true := hostOT.1
  rw [isOT_BT] at hOT
  simp only [Bool.and_eq_true] at hOT
  obtain ⟨hel, hdesc⟩ := hOT
  have hdA : descP as = true := descP_append1_om as [pl] hdesc
  have hjuncA : ∀ p ∈ as, leBT (BT.trm [be]) (BT.trm [p]) = true := by
    intro p hp
    exact leBT_trans_om junc (descP_snoc_ge_all_om as pl hdesc p hp)
  have hdR : descP (as ++ List.replicate m be) = true :=
    descP_append_rep_om as be m hdA hjuncA
  have helA : ∀ p ∈ as, isOT_BP p = true := by
    intro p hp
    exact (isOT_BPList_iff_om _).mp hel p (by simp [hp])
  have helR : isOT_BPList (as ++ List.replicate m be) = true := by
    refine (isOT_BPList_iff_om _).mpr ?_
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact helA p hp'
    · have : p = be := List.eq_of_mem_replicate hp'
      subst this
      exact beOT
  refine ⟨?_, tb⟩
  show isOT_BT (BT.trm (as ++ List.replicate m be)) = true
  rw [isOT_BT]
  simp [helR, hdR]

/-- Isabelle `opx_operB_snoc_local`（`b1x_operB_multi` の snoc 版）:
`operB` は最後の top-level principal に局在する。 -/
private theorem operB_snoc_local_om : ∀ (as : List BP) (pl : BP) (z : BT),
    operB (BT.trm (as ++ [pl])) z = addBT (BT.trm as) (operB (BT.trm [pl]) z)
  | [], pl, z => by
      cases hop : operB (BT.trm [pl]) z with
      | trm xs => simp [addBT, hop]
  | a :: as, pl, z => by
      have hne : as ++ [pl] ≠ [] := by simp
      obtain ⟨q, qs, hq⟩ : ∃ q qs, as ++ [pl] = q :: qs := by
        cases h : as ++ [pl] with
        | nil => exact absurd h hne
        | cons q qs => exact ⟨q, qs, rfl⟩
      have hstep : operB (BT.trm (a :: (as ++ [pl]))) z
          = addBT (BT.trm [a]) (operB (BT.trm (as ++ [pl])) z) := by
        rw [hq]; simp [operB, bOperCore]
      rw [List.cons_append, hstep, operB_snoc_local_om as pl z]
      cases hop : operB (BT.trm [pl]) z with
      | trm xs => simp [addBT]

/-! ## 2. `Trans` 側の小補題 -/

/-- Isabelle `e4x_OT_B_operB_numBT` (`layerB/pss_wip.thy`:61390)。 -/
private theorem OT_B_operB_numBT_om {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz]; simpa [operB, BZero, bOperCore] using (by
      simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList] :
      BZero ∈ OT_B)
  · exact buchholz_fseq_closed a n ha hz

/-- Isabelle `Trans_singleton`。 -/
private theorem Trans_singleton_om (v : ℕ) :
    Trans [(v, v)] = if v = 0 then BZero else Dprin (v : ℕ∞) BZero := by
  by_cases hv : v = 0
  · subst hv
    have hT : TPS ([((0:ℕ), (0:ℕ))]) := by simp [TPS]
    have hz : zeroT [((0:ℕ), (0:ℕ))] = true := by simp [zeroT, Lng, entry]
    simpa using (Trans_preserves_zeroT _ hT).mp hz
  · have hfuel : transFuel [(v, v)] = (transFuel [(v, v)] - 1) + 1 := by simp [transFuel]
    have hred : reduced [(v, v)] = true := by
      have hfix := Red_singleton v v; simp [reduced, hfix]
    rw [Trans, hfuel, TransAux]
    simp [hred, lastIdx, entry, Dprin, BZero, hv]

/-- Isabelle `opx_mono_Trans_singleton`: mono 成分の `Trans` は単一 principal。 -/
private theorem mono_Trans_singleton_om (L : PS) (hR : RTPS L) (hmono : monoT L = true) :
    ∃ pl : BP, Trans L = BT.trm [pl] := by
  have hLT : TPS L := RTPS_TPS L hR
  have hnm : multiT L = false := by
    by_contra hc
    have : multiT L = true := by simpa using hc
    rw [multiT] at this
    simp [hmono] at this
  have hPL : P L = [L] := P_nonmulti_eq L hnm
  have hz0 : zeroT ((P L).getD 0 []) = false := by
    rw [hPL]; simp only [List.getD_cons_zero]
    by_contra hc
    have hzt : zeroT L = true := by simpa using hc
    rw [monoT] at hmono; simp [hzt] at hmono
  have hlen : (PB (Trans L)).length = 1 := (m_7_3_Trans_monoT L hR hz0).mp hmono
  cases hT : Trans L with
  | trm ps =>
    have : ps.length = 1 := by
      have : (PB (BT.trm ps)).length = 1 := by rw [← hT]; exact hlen
      simpa [PB, untrm] using this
    obtain ⟨pl, rfl⟩ := List.length_eq_one_iff.mp this
    exact ⟨pl, rfl⟩

/-- `¬ zeroT M` の簡約形は `Trans` 非零。 -/
private theorem Trans_ne_BZero_om (M : PS) (hR : RTPS M) (hnz : zeroT M = false) :
    Trans M ≠ BZero := by
  intro h
  have hMT : TPS M := RTPS_TPS M hR
  have := (Trans_preserves_zeroT M hMT).mpr h
  rw [this] at hnz; simp at hnz

/-! ## 3. 一般化 `OT_B` 再組立（末尾 principal をリスト `cs` で置換） -/

/-- `leBT (Trm cs) (Trm [pl])` から先頭 principal `c` について
`leBT (Trm [c]) (Trm [pl])` を取り出す。 -/
private theorem head_le_of_leBT_om (c : BP) (cs' : List BP) (pl : BP)
    (h : leBT (BT.trm (c :: cs')) (BT.trm [pl]) = true) :
    leBT (BT.trm [c]) (BT.trm [pl]) = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with hlt | heq
  · left
    simp only [lessBT, lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hlt
    rcases hlt with hlp | ⟨_, hrest⟩
    · simpa [lessBT, lessBPList] using hlp
    · cases cs' <;> simp [lessBPList] at hrest
  · right
    have : c = pl ∧ cs' = [] := by simpa using heq
    simp [this.1]

/-- Isabelle `opx_descP` 系: 降順リスト同士を接合部条件のもとで連結。 -/
private theorem descP_append_om : ∀ (as cs : List BP),
    descP as = true → descP cs = true →
    (∀ a, as.getLast? = some a → ∀ c, cs.head? = some c →
      leBT (BT.trm [c]) (BT.trm [a]) = true) →
    descP (as ++ cs) = true
  | [], cs, _, hdc, _ => by simpa using hdc
  | [a], cs, _, hdc, hj => by
      cases cs with
      | nil => rfl
      | cons c cs' =>
        have hjac : leBT (BT.trm [c]) (BT.trm [a]) = true :=
          hj a (by simp) c (by simp)
        show descP (a :: c :: cs') = true
        simp only [descP, Bool.and_eq_true]
        exact ⟨hjac, hdc⟩
  | a :: a2 :: as', cs, hda, hdc, hj => by
      have hda' : descP (a2 :: as') = true := by
        simp only [descP, Bool.and_eq_true] at hda; exact hda.2
      have hhead : leBT (BT.trm [a2]) (BT.trm [a]) = true := by
        simp only [descP, Bool.and_eq_true] at hda; exact hda.1
      have hlast : (a :: a2 :: as').getLast? = (a2 :: as').getLast? := by
        simp [List.getLast?]
      have ih : descP ((a2 :: as') ++ cs) = true :=
        descP_append_om (a2 :: as') cs hda' hdc
          (fun a' ha' c hc => hj a' (by rw [hlast]; exact ha') c hc)
      show descP (a :: ((a2 :: as') ++ cs)) = true
      have hh2 : ((a2 :: as') ++ cs).head? = some a2 := by simp
      cases hcs : (a2 :: as') ++ cs with
      | nil => simp at hcs
      | cons d ds =>
        have : d = a2 := by rw [hcs] at hh2; simpa using hh2
        subst this
        simp only [descP, Bool.and_eq_true]
        refine ⟨hhead, ?_⟩
        rw [← hcs]; exact ih

/-- 汎用 `OT_B` 置換: `OT_B` の host `Trm (as ++ [pl])` の末尾 principal `pl` を、
`OT_B` の（whole-term で `≤ Trm [pl]` な）項 `Trm cs` に置換しても
（`T_B` 所属さえあれば）`OT_B` に留まる。casea/caseb 双方を一つに束ねる。 -/
theorem OT_append_corr_om (as cs : List BP) (pl : BP)
    (hostOT : BT.trm (as ++ [pl]) ∈ OT_B)
    (csOT : BT.trm cs ∈ OT_B)
    (junc : leBT (BT.trm cs) (BT.trm [pl]) = true)
    (tb : BT.trm (as ++ cs) ∈ T_B) :
    BT.trm (as ++ cs) ∈ OT_B := by
  have hOT : isOT_BT (BT.trm (as ++ [pl])) = true := hostOT.1
  rw [isOT_BT] at hOT
  simp only [Bool.and_eq_true] at hOT
  obtain ⟨helH, hdescH⟩ := hOT
  have hdA : descP as = true := descP_append1_om as [pl] hdescH
  have helA : ∀ p ∈ as, isOT_BP p = true := fun p hp =>
    (isOT_BPList_iff_om _).mp helH p (by simp [hp])
  have hcOT : isOT_BT (BT.trm cs) = true := csOT.1
  rw [isOT_BT] at hcOT
  simp only [Bool.and_eq_true] at hcOT
  obtain ⟨helC, hdescC⟩ := hcOT
  have helCl : ∀ p ∈ cs, isOT_BP p = true := fun p hp =>
    (isOT_BPList_iff_om _).mp helC p hp
  -- descP(as ++ cs)
  have hjunc : ∀ a, as.getLast? = some a → ∀ c, cs.head? = some c →
      leBT (BT.trm [c]) (BT.trm [a]) = true := by
    intro a ha c hc
    have hcs : ∃ cs', cs = c :: cs' := by
      cases cs with
      | nil => simp at hc
      | cons c' cs' =>
        have : c' = c := by simpa using hc
        exact ⟨cs', by rw [this]⟩
    obtain ⟨cs', rfl⟩ := hcs
    have hcpl : leBT (BT.trm [c]) (BT.trm [pl]) = true :=
      head_le_of_leBT_om c cs' pl junc
    have hplast : leBT (BT.trm [pl]) (BT.trm [a]) = true := by
      have hmem : a ∈ as := List.mem_of_getLast? ha
      exact descP_snoc_ge_all_om as pl hdescH a hmem
    exact leBT_trans_om hcpl hplast
  have hdR : descP (as ++ cs) = true := descP_append_om as cs hdA hdescC hjunc
  have helR : isOT_BPList (as ++ cs) = true := by
    refine (isOT_BPList_iff_om _).mpr ?_
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · exact helA p hp'
    · exact helCl p hp'
  refine ⟨?_, tb⟩
  show isOT_BT (BT.trm (as ++ cs)) = true
  rw [isOT_BT]; simp [helR, hdR]

#print axioms OT_append_corr_om

end PSS
