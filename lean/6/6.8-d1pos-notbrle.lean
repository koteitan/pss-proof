import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-base»
import «6».«6.8-d1pos-trmax»
import «6».«6.8-d1pos-le0»

/-!
# §6.8 d1pos ¬brle — P-split / Br-align 層（notbrle brick 族）

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1`（d1pos）
  ¬brle 跨りスライスの P 分解・アンカー崩壊・Br 整列）
- 訂正: なし（A7/A8 は上位ファイル `6.8-standard-slice-Br-descending` 側で適用済み）
- Isabelle (isabelle/pss_mechanized.thy):
  `oper_d1pos_notbrle_P_split` (14393), `oper_d1pos_notbrle_LOW_eq` (14428),
  `oper_d1pos_notbrle_take_map` (14466), `oper_d1pos_collapse` (14510),
  `oper_d1pos_branch_anchor` (14553), `oper_d1pos_branch_collapse_concrete` (14656),
  `oper_d1pos_branch_butl` (14688), `oper_d1pos_branch_lowshift_regB` (14724),
  `oper_d1pos_anchor_tail_entry` (14790), `oper_d1pos_tail_junction` (14825),
  `oper_d1pos_notbrle_Br_align` (14900), `oper_d1pos_nth_low_verbatim` (14977),
  `oper_d1pos_ctx_tnc_prefix` (15041), `oper_d1pos_notbrle_Br_align_regA` (15399)。
  private: `TrMax_seg_oper_d1pos_eq_regA_nb`（Isabelle
  `TrMax_seg_oper_d1pos_eq_regA` 15218、範囲外のため private 複製）
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Prop 定義）,
  «6».«6.8-d1pos-base»（`oper_d1pos_LOW_source_eq`）,
  «6».«6.8-d1pos-trmax»（TrEq キーストーン群・経由 import）,
  «6».«6.8-d1pos-le0»（`oper_d1pos_le0_start_to_any` / `oper_d1pos_b3n_boundary` /
  `oper_d1pos_ctx_tnc`）,
  «6».«6.8-standard-slice-Br-descending»（経由 import: `P_last_anchor_*_68` 族・
  `seg_of_seg_68` / `Br_seg_reshape_68` / `seg_getElem_68` /
  `entry_oper_lt_last_68` / `seg_oper_prefix_agree_68` /
  `TrMax_eq_of_prefix_agree_68`/`_sym_68` / `TrMax_seg_oper_d1pos_eq_span_68` /
  `P_seg_oper_d1pos_block_eq_68` / `length_oper_d1pos_68` /
  `entry_oper_d1pos_one_68`）,
  «6».«6.2-P-additivity»（`P_additivity` / `P_nonmulti_eq`、経由 import）,
  «6».«6.4-P-IdxSum»（`idxSum_diff` / `getD_eq_getElem_idx`、経由 import）,
  «6».«6.4-mono-slice»（`idxSum_total`、経由 import）
- 状態: ✅ 証明済（sorry 0）。`D1pos_oper_d1pos_branch_anchor` /
  `D1pos_oper_d1pos_ctx_tnc_prefix` / `D1pos_oper_d1pos_notbrle_Br_align_regA`
  の 3 Prop を discharge。
-/

namespace PSS

/-! ## 補助（このファイル私用） -/

/-- `getD` の entry 対表示（`6.8-d1pos-le0` の private `getD_entry_dl` の複製）。 -/
private theorem getD_entry_nb (X : PS) (s : ℕ) (hs : s < Lng X) :
    X.getD s (0, 0) = (entry X 0 s, entry X 1 s) := by
  rw [getD_eq_getElem_idx X (0, 0) hs]
  cases hx : X[s] with
  | mk a b => simp [entry, List.getElem?_eq_getElem hs, hx]

/-! ## ¬brle 構造分割（regime 非依存）

Isabelle `oper_d1pos_notbrle_P_split` (14393): 行 0 左最小カット `c` で
`P` が加法分割し、非複項尾部は単一成分。 -/

/-- Isabelle `oper_d1pos_notbrle_P_split` (pss_mechanized.thy:14393)。 -/
theorem oper_d1pos_notbrle_P_split (Yp : PS) (c : ℕ)
    (hYpT : TPS Yp)
    (hc0 : 0 < c) (hcle : c ≤ Lng Yp - 1)
    (hlmin : ∀ j, j < c → entry Yp 0 c ≤ entry Yp 0 j)
    (htailnm : multiT (seg Yp c (Lng Yp - 1)) = false) :
    P Yp = P (seg Yp 0 (c - 1)) ++ [seg Yp c (Lng Yp - 1)] := by
  rw [P_additivity Yp c hYpT hc0 hcle hlmin, P_nonmulti_eq _ htailnm]

/-! ## LOW 成分リスト同一性（d1pos, `i₁ = 1`） -/

/-- Isabelle `oper_d1pos_notbrle_LOW_eq` (pss_mechanized.thy:14428)。 -/
theorem oper_d1pos_notbrle_LOW_eq
    (M : PS) (n q s0 e0 : ℕ)
    (hL : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hi1z : idx1 M (Lng M - 1) = 1)
    (_hj0lt : parent M 1 (Lng M - 1) < Lng M - 1)
    (hq : q < n)
    (hs0e0 : s0 ≤ e0)
    (he0lt : e0 < Lng M - 1 - parent M 1 (Lng M - 1)) :
    P (seg (oper M n)
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s0)
        (parent M 1 (Lng M - 1) +
          q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e0)) =
      (P (seg M (parent M 1 (Lng M - 1) + s0)
        (parent M 1 (Lng M - 1) + e0))).map
        (IncrFirstN (q * (entry M 0 (Lng M - 1) -
          entry M 0 (parent M 1 (Lng M - 1))))) :=
  P_seg_oper_d1pos_block_eq_68 M n q s0 e0 hL hzero hp hi1z hq hs0e0 he0lt

/-! ## take-map コンビネータ -/

/-- Isabelle `oper_d1pos_notbrle_take_map` (pss_mechanized.thy:14466)。 -/
theorem oper_d1pos_notbrle_take_map
    (B1 B2 : List PS) (R1 R2 : PS) (Jm s : ℕ)
    (hleg1 : B1.take Jm = P R1)
    (hleg2 : B2.take Jm = P R2)
    (hleg3 : R1 = IncrFirstN s R2) :
    B1.take Jm = (B2.take Jm).map (IncrFirstN s) := by
  rw [hleg1, hleg3, P_IncrFirstN_equivariance, hleg2]

/-! ## ACROSS-BLOCK P-COLLAPSE（構造恒等式） -/

/-- Isabelle `oper_d1pos_collapse` (pss_mechanized.thy:14510)。 -/
theorem oper_d1pos_collapse
    (S base : PS) (BN : List PS) (c shamt : ℕ)
    (hST : TPS S)
    (hc0 : 0 < c) (hcle : c ≤ Lng S - 1)
    (hlmin : ∀ j, j < c → entry S 0 c ≤ entry S 0 j)
    (htailnm : multiT (seg S c (Lng S - 1)) = false)
    (hlowshift : seg S 0 (c - 1) = IncrFirstN shamt base)
    (hbutl : BN.dropLast = P base) :
    P S = (BN.dropLast).map (IncrFirstN shamt) ++
      [seg S c (Lng S - 1)] := by
  rw [hbutl, oper_d1pos_notbrle_P_split S c hST hc0 hcle hlmin htailnm,
    hlowshift, P_IncrFirstN_equivariance]

/-! ## ANCHOR brick（構造的、block-fold 不要）

Isabelle の `defines c ≡ IdxSum (P S) ! (length (P S) - 1)` はインライン展開
（`(IdxSum (P S)).getD ((P S).length - 1) 0`）。`last (P S)` は
`(P S).getD ((P S).length - 1) []`。 -/

/-- Isabelle `oper_d1pos_branch_anchor` (pss_mechanized.thy:14553)。 -/
theorem oper_d1pos_branch_anchor (S : PS)
    (hST : TPS S) (hmulti : 1 < (P S).length) :
    0 < (IdxSum (P S)).getD ((P S).length - 1) 0 ∧
    (IdxSum (P S)).getD ((P S).length - 1) 0 ≤ Lng S - 1 ∧
    (∀ j, j < (IdxSum (P S)).getD ((P S).length - 1) 0 →
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤ entry S 0 j) ∧
    multiT (seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1)) = false ∧
    seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) =
      (P S).getD ((P S).length - 1) [] ∧
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
      Lng S - Lng ((P S).getD ((P S).length - 1) []) := by
  obtain ⟨hcpos, hcle, hlmin, hnm, _⟩ := P_last_anchor_68 S hST hmulti
  have htail : (P S).getD ((P S).length - 1) [] =
      seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) :=
    P_last_anchor_getD_68 S hST hmulti
  have hJ : (P S).length - 1 < (P S).length := by omega
  have hdiff := idxSum_diff (P S) ((P S).length - 1) hJ
  have hnext : (IdxSum (P S)).getD ((P S).length - 1 + 1) 0 = Lng S := by
    rw [show (P S).length - 1 + 1 = (P S).length by omega]
    calc (IdxSum (P S)).getD (P S).length 0
        = Lng (P S).flatten := idxSum_total (P S)
      _ = Lng S := congrArg Lng (P_concat S)
  have hcval : (IdxSum (P S)).getD ((P S).length - 1) 0 =
      Lng S - Lng ((P S).getD ((P S).length - 1) []) := by omega
  exact ⟨hcpos, hcle, hlmin, hnm, htail.symm, hcval⟩

/-- Prop discharge: `D1pos_oper_d1pos_branch_anchor`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_branch_anchor_holds :
    D1pos_oper_d1pos_branch_anchor := by
  intro S hST hmulti
  exact oper_d1pos_branch_anchor S hST hmulti

/-! ## ASSEMBLED concrete collapse -/

/-- Isabelle `oper_d1pos_branch_collapse_concrete` (pss_mechanized.thy:14656)。 -/
theorem oper_d1pos_branch_collapse_concrete
    (S base : PS) (BN : List PS) (shamt : ℕ)
    (hST : TPS S) (hmulti : 1 < (P S).length)
    (hlowshift : seg S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0 - 1) =
      IncrFirstN shamt base)
    (hbutl : BN.dropLast = P base) :
    P S = (BN.dropLast).map (IncrFirstN shamt) ++
      [(P S).getD ((P S).length - 1) []] := by
  obtain ⟨hcpos, hcle, hlmin, hnm, _⟩ := P_last_anchor_68 S hST hmulti
  have htail : (P S).getD ((P S).length - 1) [] =
      seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) :=
    P_last_anchor_getD_68 S hST hmulti
  rw [htail]
  exact oper_d1pos_collapse S base BN
    ((IdxSum (P S)).getD ((P S).length - 1) 0) shamt hST hcpos hcle hlmin hnm
    hlowshift hbutl

/-! ## `butl` 仮定の供給（N 側 ANCHOR 適用） -/

/-- Isabelle `oper_d1pos_branch_butl` (pss_mechanized.thy:14688)。 -/
theorem oper_d1pos_branch_butl (Snside : PS)
    (hST : TPS Snside) (hmulti : 1 < (P Snside).length) :
    (P Snside).dropLast =
      P (seg Snside 0
        ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0 - 1)) :=
  P_last_anchor_butlast_68 Snside hST hmulti

/-! ## `lowshift` 仮定の供給（UNCAPPED regime B） -/

/-- Isabelle `oper_d1pos_branch_lowshift_regB` (pss_mechanized.thy:14724)。
Isabelle の `defines jm2/w` はインライン展開。 -/
theorem oper_d1pos_branch_lowshift_regB
    (N : PS) (n q s0 cc A E : ℕ)
    (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hqn : q < n)
    (hAform : A = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hs0e0 : s0 ≤ s0 + (cc - 1))
    (he0lt : s0 + (cc - 1) < Lng N - 1 - parent N 1 (Lng N - 1))
    (hEle : A ≤ E)
    (hccle : cc - 1 ≤ E - A) :
    seg (seg (oper N n) A E) 0 (cc - 1) =
      IncrFirstN (q * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))))
        (seg N (parent N 1 (Lng N - 1) + s0)
          (parent N 1 (Lng N - 1) + (s0 + (cc - 1)))) := by
  rw [seg_of_seg_68 (oper N n) A E 0 (cc - 1) hEle hccle,
    show A + 0 = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 by omega,
    show A + (cc - 1) = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + (s0 + (cc - 1)) by omega]
  exact oper_d1pos_LOW_source_eq N n q s0 (s0 + (cc - 1)) hL hzero hp hi1z
    hj0lt hqn hs0e0 he0lt

/-! ## ANCHOR TAIL entry 還元 -/

/-- Isabelle `oper_d1pos_anchor_tail_entry` (pss_mechanized.thy:14790)。 -/
theorem oper_d1pos_anchor_tail_entry (S : PS) (i : ℕ)
    (hST : TPS S) (hmulti : 1 < (P S).length) :
    entry ((P S).getD ((P S).length - 1) []) i 0 =
      entry S i ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
  have htail : (P S).getD ((P S).length - 1) [] =
      seg S ((IdxSum (P S)).getD ((P S).length - 1) 0) (Lng S - 1) :=
    P_last_anchor_getD_68 S hST hmulti
  rw [htail]
  exact P_last_anchor_tail_entry_68 S i hST hmulti

/-! ## TAIL JUNCTION（F8/F9 持ち上げ） -/

/-- Isabelle `oper_d1pos_tail_junction` (pss_mechanized.thy:14825)。 -/
theorem oper_d1pos_tail_junction (S Snside : PS) (shamt : ℕ)
    (hST : TPS S) (hmulti : 1 < (P S).length)
    (hSnT : TPS Snside) (hmultiN : 1 < (P Snside).length)
    (hF8end : entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
      entry Snside 0
        ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0) + shamt)
    (hF9end : entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
      entry Snside 1
        ((IdxSum (P Snside)).getD ((P Snside).length - 1) 0)) :
    entry ((P S).getD ((P S).length - 1) []) 0 0 =
      entry ((P Snside).getD ((P Snside).length - 1) []) 0 0 + shamt ∧
    entry ((P S).getD ((P S).length - 1) []) 1 0 ≤
      entry ((P Snside).getD ((P Snside).length - 1) []) 1 0 := by
  constructor
  · rw [oper_d1pos_anchor_tail_entry S 0 hST hmulti,
      oper_d1pos_anchor_tail_entry Snside 0 hSnT hmultiN]
    exact hF8end
  · rw [oper_d1pos_anchor_tail_entry S 1 hST hmulti,
      oper_d1pos_anchor_tail_entry Snside 1 hSnT hmultiN]
    exact hF9end

/-! ## Br alignment（regime B、span キーストーン経由） -/

/-- Isabelle `oper_d1pos_notbrle_Br_align` (pss_mechanized.thy:14900)。 -/
theorem oper_d1pos_notbrle_Br_align
    (N : PS) (n q s0 j0red j1red j0' j1' shamt : ℕ)
    (hN : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (_hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_hn1 : 1 ≤ n)
    (hqn : q < n)
    (hs0w : j0red < Lng N - 1)
    (hs0eq : j0red = parent N 1 (Lng N - 1) + s0)
    (hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1))
    (hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0)
    (hshamt : shamt = q * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hj1redspan : j1red ≤ j0red + (j1' - j0'))
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) ∧
      Br (seg (oper N n) j0' j1') =
        P (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') ∧
      Br (seg N j0red j1red) =
        P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) ∧
      Br (seg (oper N n) j0' j1') ≠ [] ∧
      Br (seg N j0red j1red) ≠ [] := by
  have hTrEq : TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) :=
    TrMax_seg_oper_d1pos_eq_span_68 N n q s0 j0red j1red j0' j1' shamt
      hN hL hzero hp hi1z hqn hs0w hs0eq hs0lt hj0'eq hshamt hj1redle
      hj0j1red hj1redspan hj0j1' hj1lt htnc hstop
  have htrneM : TrMax (seg (oper N n) j0' j1') ≠
      Lng (seg (oper N n) j0' j1') - 1 :=
    fun heq => hnotbrle (Or.inl heq)
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red := by simp
  have htrneN : TrMax (seg N j0red j1red) ≠
      Lng (seg N j0red j1red) - 1 := by omega
  have hBrM : Br (seg (oper N n) j0' j1') =
      P (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
    Br_seg_reshape_68 (oper N n) j0' j1' hj0j1' hj1lt htrneM
  have hj1redltN : j1red < Lng N := by omega
  have hBrN : Br (seg N j0red j1red) =
      P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) :=
    Br_seg_reshape_68 N j0red j1red hj0j1red hj1redltN htrneN
  refine ⟨hTrEq, hBrM, hBrN, ?_, ?_⟩
  · rw [hBrM]; exact P_nonempty _
  · rw [hBrN]; exact P_nonempty _

/-! ## REGIME A verbatim 読み出し -/

/-- Isabelle `oper_d1pos_nth_low_verbatim` (pss_mechanized.thy:14977)。
Isabelle `!` は `.getD`（規約）。 -/
theorem oper_d1pos_nth_low_verbatim
    (N : PS) (n x : ℕ)
    (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hxlt : x < Lng N - 1) :
    (oper N n).getD x (0, 0) = N.getD x (0, 0) := by
  have hOL := length_oper_d1pos_68 N n hL hzero hp hi1z
  have hmul : 1 * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
      n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
    Nat.mul_le_mul_right _ hn1
  have hxM : x < Lng (oper N n) := by omega
  have hxN : x < Lng N := by omega
  rw [getD_entry_nb (oper N n) x hxM, getD_entry_nb N x hxN,
    entry_oper_lt_last_68 N n 0 x hL hn1 (Or.inl rfl) hxlt,
    entry_oper_lt_last_68 N n 1 x hL hn1 (Or.inr rfl) hxlt]

/-! ## PREFIX 幹閉じ込め `tnc`（regA/boundary セル用） -/

/-- Isabelle `oper_d1pos_ctx_tnc_prefix` (pss_mechanized.thy:15041)。
`¬fill` を背理法で示す: fill を仮定すると、境界の行 1 非増加（B3、
`oper_d1pos_b3n_boundary`）と境界 le0（block-1 開始からの到達）から
`M'` 側の strict-2 閉じ込めが出て、対称接頭辞キーストーンの TrEq が
fill と矛盾する。 -/
theorem oper_d1pos_ctx_tnc_prefix
    (N : PS) (n j0' j1' : ℕ)
    (hNT : TPS N) (hL : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi1z : idx1 N (Lng N - 1) = 1)
    (hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hj0pre : j0' < parent N 1 (Lng N - 1))
    (hbge : Lng N - 1 ≤ j1')
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0' := by
  let Mp := seg (oper N n) j0' j1'
  let Np := seg N j0' (Lng N - 1)
  let c := Lng N - 1 - 1 - j0'
  have hcd : c = Lng N - 1 - 1 - j0' := rfl
  have hj0ltN : j0' < Lng N - 1 := by omega
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hLMp : Lng Mp = j1' + 1 - j0' := by simp [Mp]
  have hLNp : Lng Np = Lng N - 1 + 1 - j0' := by simp [Np]
  have hnotfill : TrMax Np ≠ Lng Np - 1 := by
    intro hfill
    obtain ⟨hndisj, hnotle⟩ := not_or.mp hnotbrle
    have hOL : Lng (oper N n) = parent N 1 (Lng N - 1) +
        n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      length_oper_d1pos_68 N n hL hzero hp hi1z
    -- 境界列 `Lng N - 1` が切片に入る以上 `2 ≤ n`
    have hn2 : 1 < n := by
      by_contra hcon
      have hn1eq : n = 1 := by omega
      have hOL1 : Lng (oper N n) = parent N 1 (Lng N - 1) +
          1 * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
        rw [hOL, hn1eq]
      omega
    have hcM : c < Lng Mp := by rw [hLMp]; omega
    have hcN : c < Lng Np := by rw [hLNp]; omega
    -- 接頭辞 [0,c] の逐語一致
    have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Np.getD s (0, 0) := by
      intro s hs
      exact seg_oper_prefix_agree_68 N n j0' j1' c hL hn1 hcM hcN
        (fun s' hs' => by omega) s hs
    -- 境界 B3: `entry Mp 1 (c+1) ≤ entry Mp 1 c`
    have hc1M : c + 1 < Lng Mp := by rw [hLMp]; omega
    have hidx_c1 : j0' + (c + 1) = Lng N - 1 := by omega
    have he1_c1 : entry Mp 1 (c + 1) =
        entry N 1 (parent N 1 (Lng N - 1)) := by
      have hh := entry_oper_d1pos_one_68 N n 1 0 hL hzero hp hi1z hn2
        (by omega)
      have hidx : parent N 1 (Lng N - 1) +
          1 * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 =
            j0' + (c + 1) := by omega
      have hseg : entry Mp 1 (c + 1) =
          entry (oper N n) 1 (j0' + (c + 1)) :=
        entry_seg (oper N n) j0' j1' 1 (c + 1) hc1M
      rw [hseg, ← hidx, hh]
      simp
    have he1_c : entry Mp 1 c = entry N 1 (Lng N - 2) := by
      have hseg : entry Mp 1 c = entry (oper N n) 1 (j0' + c) :=
        entry_seg (oper N n) j0' j1' 1 c hcM
      have hidxc : j0' + c = Lng N - 2 := by omega
      rw [hseg, hidxc]
      exact entry_oper_lt_last_68 N n 1 (Lng N - 2) hL hn1 (Or.inr rfl)
        (by omega)
    have hp1 : hasParent N 1 (Lng N - 1) = true := by simpa [hi1z] using hp
    have hB3N : entry N 1 (parent N 1 (Lng N - 1)) ≤
        entry N 1 (Lng N - 2) :=
      oper_d1pos_b3n_boundary N j0' hNT hL hp1 hj0ltN hfill
    have hB3 : entry Mp 1 (c + 1) ≤ entry Mp 1 c := by
      rw [he1_c1, he1_c]
      exact hB3N
    -- 境界 le0: block-1 開始 `Lng N - 1 = j0' + (c+1)` から右端へ到達
    have hbdry : leR Mp 0 (c + 1) (Lng Mp - 1) = true := by
      have htrans : leR Mp 0 (c + 1) (Lng Mp - 1) =
          leR (oper N n) 0 (j0' + (c + 1)) (j0' + (Lng Mp - 1)) :=
        leR0_seg_adm (oper N n) j0' j1' (c + 1) (Lng Mp - 1)
          (by omega) hj1lt hc1M
          (show Lng Mp - 1 < Lng Mp by omega)
      rw [htrans]
      have hidx_end : j0' + (Lng Mp - 1) = j1' := by omega
      rw [hidx_c1, hidx_end]
      have hstart : parent N 1 (Lng N - 1) +
          1 * (Lng N - 1 - parent N 1 (Lng N - 1)) = Lng N - 1 := by omega
      rw [← hstart]
      exact oper_d1pos_le0_start_to_any N n 1 j1' hNT hL hzero hp hi1z
        hj0lt hn2 (by omega) hj1lt
    -- strict-2 閉じ込め
    have hnotleF : ¬leR Mp 0 (TrMax Mp + 1) (Lng Mp - 1) = true := hnotle
    have htncM1 : TrMax Mp + 1 ≤ c :=
      oper_d1pos_ctx_tnc Mp c hMpT hB3 hbdry hnotleF
    have hstopM : nextR Mp 1 (TrMax Mp) (TrMax Mp + 1) = false :=
      TrMax_stop_uncond Mp hMpT
    -- 対称接頭辞キーストーン → fill と矛盾
    have hTrEq : TrMax Mp = TrMax Np :=
      TrMax_eq_of_prefix_agree_sym_68 Mp Np c hMpT hNpT hagree hcM hcN
        htncM1 hstopM
    omega
  have htbN := TrMax_bound Np hNpT
  show TrMax Np ≤ Lng N - 1 - 1 - j0'
  omega

/-- Prop discharge: `D1pos_oper_d1pos_ctx_tnc_prefix`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_ctx_tnc_prefix_holds :
    D1pos_oper_d1pos_ctx_tnc_prefix := by
  intro N n j0' j1' hNT hL hzero hp hi1z hj0lt hn1 hj0pre hbge hj0j1' hj1lt
    hnotbrle
  exact oper_d1pos_ctx_tnc_prefix N n j0' j1' hNT hL hzero hp hi1z hj0lt hn1
    hj0pre hbge hj0j1' hj1lt hnotbrle

/-! ## REGIME A TrEq キーストーン（private、Isabelle
`TrMax_seg_oper_d1pos_eq_regA` 15218 の複製） -/

/-- regime A（`j0red = j0'`、シフト無し）: 接頭辞 [0, j1red-1-j0red] は
両側とも `N` を逐語読みするので、非対称接頭辞キーストーンで幹が一致。 -/
private theorem TrMax_seg_oper_d1pos_eq_regA_nb
    (N : PS) (n j0red j1red j0' j1' : ℕ)
    (hL : 1 < Lng N)
    (hn1 : 1 ≤ n)
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hj1redspan : j1red ≤ j0red + (j1' - j0'))
    (hj0eqA : j0red = j0')
    (hj0j1' : j0' < j1')
    (_hj1lt : j1' < Lng (oper N n))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false) :
    TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) := by
  let Mp := seg (oper N n) j0' j1'
  let Np := seg N j0red j1red
  let c := j1red - 1 - j0red
  have hcd : c = j1red - 1 - j0red := rfl
  have hMpT : TPS Mp := by
    apply List.ne_nil_of_length_pos
    simp [Mp]
    omega
  have hNpT : TPS Np := by
    apply List.ne_nil_of_length_pos
    simp [Np]
    omega
  have hLMp : Lng Mp = j1' + 1 - j0' := by simp [Mp]
  have hLNp : Lng Np = j1red + 1 - j0red := by simp [Np]
  have hcM : c < Lng Mp := by rw [hLMp]; omega
  have hcN : c < Lng Np := by rw [hLNp]; omega
  have hagree : ∀ s, s ≤ c → Mp.getD s (0, 0) = Np.getD s (0, 0) := by
    intro s hsc
    have hsM : s < Lng Mp := by omega
    have hsN : s < Lng Np := by omega
    have hidxlt' : j0' + s < Lng N - 1 := by omega
    rw [getD_eq_getElem_idx Mp (0, 0) hsM,
      getD_eq_getElem_idx Np (0, 0) hsN,
      seg_getElem_68 (oper N n) j0' j1' s hsM,
      seg_getElem_68 N j0red j1red s hsN,
      entry_oper_lt_last_68 N n 0 (j0' + s) hL hn1 (Or.inl rfl) hidxlt',
      entry_oper_lt_last_68 N n 1 (j0' + s) hL hn1 (Or.inr rfl) hidxlt',
      hj0eqA]
  exact TrMax_eq_of_prefix_agree_68 Mp Np c hMpT hNpT hagree hcM hcN
    htnc hstop

/-! ## Br alignment（regime A、`shamt = 0`） -/

/-- Isabelle `oper_d1pos_notbrle_Br_align_regA` (pss_mechanized.thy:15399)。 -/
theorem oper_d1pos_notbrle_Br_align_regA
    (N : PS) (n j0red j1red j0' j1' : ℕ)
    (hL : 1 < Lng N)
    (_hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (_hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (_hi1z : idx1 N (Lng N - 1) = 1)
    (_hj0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hj1redle : j1red ≤ Lng N - 1)
    (hj0j1red : j0red < j1red)
    (hj1redspan : j1red ≤ j0red + (j1' - j0'))
    (hj0eqA : j0red = j0')
    (hj0j1' : j0' < j1')
    (hj1lt : j1' < Lng (oper N n))
    (htnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (hstop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (hnotbrle : ¬(TrMax (seg (oper N n) j0' j1') =
        Lng (seg (oper N n) j0' j1') - 1 ∨
      leR (seg (oper N n) j0' j1') 0 (TrMax (seg (oper N n) j0' j1') + 1)
        (Lng (seg (oper N n) j0' j1') - 1) = true)) :
    TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) ∧
      Br (seg (oper N n) j0' j1') =
        P (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') ∧
      Br (seg N j0red j1red) =
        P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) ∧
      Br (seg (oper N n) j0' j1') ≠ [] ∧
      Br (seg N j0red j1red) ≠ [] := by
  have hTrEq : TrMax (seg (oper N n) j0' j1') = TrMax (seg N j0red j1red) :=
    TrMax_seg_oper_d1pos_eq_regA_nb N n j0red j1red j0' j1' hL hn1
      hj1redle hj0j1red hj1redspan hj0eqA hj0j1' hj1lt htnc hstop
  have htrneM : TrMax (seg (oper N n) j0' j1') ≠
      Lng (seg (oper N n) j0' j1') - 1 :=
    fun heq => hnotbrle (Or.inl heq)
  have hLNp : Lng (seg N j0red j1red) = j1red + 1 - j0red := by simp
  have htrneN : TrMax (seg N j0red j1red) ≠
      Lng (seg N j0red j1red) - 1 := by omega
  have hBrM : Br (seg (oper N n) j0' j1') =
      P (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
    Br_seg_reshape_68 (oper N n) j0' j1' hj0j1' hj1lt htrneM
  have hj1redltN : j1red < Lng N := by omega
  have hBrN : Br (seg N j0red j1red) =
      P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) :=
    Br_seg_reshape_68 N j0red j1red hj0j1red hj1redltN htrneN
  refine ⟨hTrEq, hBrM, hBrN, ?_, ?_⟩
  · rw [hBrM]; exact P_nonempty _
  · rw [hBrN]; exact P_nonempty _

/-- Prop discharge: `D1pos_oper_d1pos_notbrle_Br_align_regA`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_notbrle_Br_align_regA_holds :
    D1pos_oper_d1pos_notbrle_Br_align_regA := by
  intro N n j0red j1red j0' j1' hL hzero hp hi1z hj0lt hn1 hj1redle hj0j1red
    hj1redspan hj0eqA hj0j1' hj1lt htnc hstop hnotbrle
  exact oper_d1pos_notbrle_Br_align_regA N n j0red j1red j0' j1' hL hzero hp
    hi1z hj0lt hn1 hj1redle hj0j1red hj1redspan hj0eqA hj0j1' hj1lt htnc
    hstop hnotbrle

end PSS

#print axioms PSS.oper_d1pos_notbrle_P_split
#print axioms PSS.oper_d1pos_notbrle_LOW_eq
#print axioms PSS.oper_d1pos_notbrle_take_map
#print axioms PSS.oper_d1pos_collapse
#print axioms PSS.oper_d1pos_branch_anchor
#print axioms PSS.D1pos_oper_d1pos_branch_anchor_holds
#print axioms PSS.oper_d1pos_branch_collapse_concrete
#print axioms PSS.oper_d1pos_branch_butl
#print axioms PSS.oper_d1pos_branch_lowshift_regB
#print axioms PSS.oper_d1pos_anchor_tail_entry
#print axioms PSS.oper_d1pos_tail_junction
#print axioms PSS.oper_d1pos_notbrle_Br_align
#print axioms PSS.oper_d1pos_nth_low_verbatim
#print axioms PSS.oper_d1pos_ctx_tnc_prefix
#print axioms PSS.D1pos_oper_d1pos_ctx_tnc_prefix_holds
#print axioms PSS.oper_d1pos_notbrle_Br_align_regA
#print axioms PSS.D1pos_oper_d1pos_notbrle_Br_align_regA_holds
