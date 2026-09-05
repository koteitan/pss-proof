import Bijectivity.Cited
import Bijectivity.«11-path-to-initial-segment»
import PSS.Trans
import PSS.Red
import «6».«6.2-P-additivity»
import «6».«6.7-standard-reduced»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-Trans-preserves-monoT»
import «7».«7.3-two-column»
import «7».«7.3-Pred-Trans-descend»
import «6».«6.5-Red-Pred-commute»
import «6».«6.2-P-components-nonmulti»
import «6».«6.6-P-preserves-reduced»
import «7».«7.3-Trans-welldefined»
import «6».«6.5-monoT-Red»
import «8».«8.7-descend-last2»

/-!
# 命題（後続な項の基本列）

原文: 任意の \(M\in RT_{\textrm{PS}}\) と \(n\in\mathbb{N}_+\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=1\) ならば
\((\textrm{Trans}(M),\textrm{Trans}(M[n]))=(D_00,0)\) または
\(\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)\) である。

原文の証明（要旨）: \(\textrm{dom}\) の定義より \(\textrm{Trans}(M)=D_00\) か、
ある \(s\) で \(\underline{(}s\underline{,}D_00\underline{)}\) の形。前者では [1] の
\(\textrm{Trans}\) と非可算基数の関係より \(M=((0,0),(0,0))\)。後者では \(M\) は複項で、
\(P(M)_{J_1}=((0,0))\)、[1] の \(P\) の加法性より
\(M=\textrm{Pred}(M)\oplus_{\mathbb{N}^2}((0,0))\)、よって
\(\textrm{Trans}(M)=\textrm{Trans}(\textrm{Pred}(M))+D_00=\textrm{Trans}(M[n])+D_00\)。□

## 状態

原文の証明の**後半**（\(M\) の最終列が \((0,0)\) であるところから結論まで）は
`successor_fseq_of_last_zero` として証明済み。使う道具は原文と同じで、
[1] の \(P\) の加法性 = `6/6.2-P-additivity.lean` の `P_additivity`、
\(\textrm{Trans}\) の \(P\) ブロック分解 = `8/8.7-descend-last2.lean` の
`f7x_Trans_append_Pblocks_holds`。

**残っているのは前半**、すなわち

\[
\textrm{dom}(\textrm{Trans}(M))=1
\;\Longrightarrow\;
\textrm{Lng}(M)>1\ \land\ M_{\textrm{Lng}(M)-1}=(0,0)
\]

である。原文はこれを [1] の \(\textrm{Trans}\) と非可算基数の関係・
\(\textrm{Trans}\) が零項性を保つこと・\(\textrm{Trans}\) が単項性を保つこと・
\(P\) の各成分の非複項性から導く。

## 前半の場合分け（`TransAux` の再帰に沿った整理）

`domTagBP (D_v b) = 1` となるのは `b = 0 ∧ v = 0` のときだけなので
（`domTagBP_zeroOnly_iff`）、`dom(Trans M) = 1` は
**`Trans M` の最後の主項が \(D_00\) であること**と同値である。
`TransAux` の分岐で場合分けすると:

| 分岐 | 状況 |
|---|---|
| `Lng M = 1` | `dom ≠ 1`。**証明済** (`not_domIsOne_of_lng_one`) |
| `monoT M`, `t₁ = 0` | `Trans M = D_0(D_{M_{1,j_1}}0)` で本体が非零なので `dom ≠ 1`。単項なので **`Trans M ≠ D_00`** を言えば済む |
| `monoT M`, `t₁ ≠ 0` | `Trans M = replaceScb t₁ c₁ c₂`。**ここだけが本質的に難しい**。`Trans_monoT_principal` より `Trans M` は単項なので、`Trans M ≠ D_00` を言えばよい。`replaceScb_spec` の `flatBT (replaceScb t₁ c₁ c₂) = s ++ flatBT c₂ ++ b` から長さで押さえるのが有望（`c₂ = transC2Core …` は 3 段ネストなので `flatBT` が \(D_00\) より長い） |
| 複項, `pJ = ((0,0))` | 最終列が `(0,0)` で結論そのもの |
| 複項, `pJ ≠ ((0,0))` | `Trans M = Trans(前半) + Trans(pJ)` で `domTag` は右側に落ちる（`domTag_addBT_right`）。`pJ` は長さが真に短いので帰納が回る |

すなわち残る本質的な穴は **「簡約単項 `M`（`Lng M > 1`）に対して
`Trans M ≠ D_00`」** の 1 点で、これは原文の 系（\(\textrm{Trans}\) と
非可算基数の関係）にあたる。
-/

namespace Bijectivity

open PSS

/-- \(D_00\)。 -/
def DzeroZero : BT := Dprin 0 (BT.trm [])

theorem Trans_zero_singleton' : PSS.Trans [(0, 0)] = BZero :=
  (Trans_preserves_zeroT [(0, 0)] (by simp [TPS])).mp (by simp [zeroT, entry])

theorem RTPS_zero_singleton : RTPS [(0, 0)] := by
  have h : STPS (diagSeq 0 0) := STPS.diag 0 0 (le_refl 0)
  have hd : diagSeq 0 0 = [(0, 0)] := by simp [diagSeq]
  exact STPS_RTPS _ (hd ▸ h)

/-! ## `dom(t)=1` の構文的特徴づけ -/

/-- `dom(D_v b) = 1` となるのは `D_v b = D_0 0` のときだけ。 -/
theorem domTagBP_zeroOnly_iff (v : ℕ∞) (b : BT) :
    domTagBP (.db v b) = BDom.zeroOnly ↔ (v = 0 ∧ b = BZero) := by
  by_cases hb : b = BZero
  · subst hb
    by_cases hv : v = 0
    · subst hv; simp [domTagBP]
    · by_cases hv2 : v = ⊤
      · subst hv2; simp [domTagBP]
      · simp [domTagBP, hv, hv2]
  · have hbne : (b == BZero) = false := by simpa using hb
    cases hd : domTag b with
    | empty => simp [domTagBP, hbne, hd, hb]
    | zeroOnly => simp [domTagBP, hbne, hd, hb]
    | naturals => simp [domTagBP, hbne, hd, hb]
    | below u => by_cases hle : v ≤ (u : ℕ∞) <;> simp [domTagBP, hbne, hd, hb, hle]

/-- 主項列の連結では `domTag` は右側で決まる。 -/
theorem domTagList_append : ∀ (as bs : List BP), bs ≠ [] →
    domTagList (as ++ bs) = domTagList bs
  | [], _, _ => by simp
  | a :: as, bs, hbs => by
      rw [List.cons_append]
      have hne : as ++ bs ≠ [] := by
        intro h
        exact hbs (List.append_eq_nil_iff.mp h).2
      cases hcons : as ++ bs with
      | nil => exact absurd hcons hne
      | cons c cs =>
          have hIH := domTagList_append as bs hbs
          rw [hcons] at hIH
          exact hIH

/-- `t + u` の `dom` は `u ≠ 0` なら `u` の `dom`。 -/
theorem domTag_addBT_right {t u : BT} (hu : u ≠ BZero) :
    domTag (addBT t u) = domTag u := by
  cases t with
  | trm as =>
    cases u with
    | trm bs =>
      have hbs : bs ≠ [] := by
        intro h; exact hu (by simp [BZero, h])
      show domTagList (as ++ bs) = domTagList bs
      exact domTagList_append as bs hbs

/-! ## 前半のうち `Lng M = 1` の場合 -/

/-- \(\textrm{Lng}(M)=1\) の簡約形では \(\textrm{dom}(\textrm{Trans}(M))\neq1\)。 -/
theorem not_domIsOne_of_lng_one {M : PS} (hM : RTPS M) (hlen : Lng M = 1) :
    ¬ domIsOne (PSS.Trans M) := by
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hRed : Red [p] = [p] := by
    have h : reduced [p] = true := hM
    simp only [reduced, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  by_cases hz : p.2 = 0
  · have hzT : zeroT [p] = true := by simp [zeroT, entry, hz]
    have hMz : [p] = [(0, 0)] := by rw [← hRed]; exact Red_zero_mr [p] hzT
    rw [hMz, Trans_zero_singleton']
    simp [domIsOne, BZero, domTag, domTagList]
  · have hpne : p ≠ (0, 0) := by
      intro h; exact hz (by rw [h])
    have hT : PSS.Trans [p] = Dprin (p.2 : ℕ∞) BZero := by
      rw [Trans_eq_lengthAux [p] hM]
      have hred : reduced [p] = true := hM
      simp only [TransAux, hred, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        lastIdx]
      simp [hpne, entry]
    rw [hT]
    intro hcontra
    have hcontra' : domTagBP (BP.db (p.2 : ℕ∞) BZero) = BDom.zeroOnly := hcontra
    have := (domTagBP_zeroOnly_iff _ _).mp hcontra'
    exact hz (by exact_mod_cast this.1)

/-! ## 前半のうち `monoT M` の場合 -/

/-- \(D_00\) より真に小さい項は \(0\) のみ。 -/
theorem lessBT_D00_imp_zero {t : BT} (h : lessBT t (Dprin 0 BZero) = true) :
    t = BZero := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => rfl
  | cons q rest =>
      exfalso
      rcases q with ⟨w, c⟩
      have hnil : lessBPList rest [] = false := by cases rest <;> rfl
      have hz : lessBT c BZero = false := by
        cases c with | trm qs => cases qs <;> rfl
      simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, hz, hnil] at h
      rcases h with (h | h) | h
      · exact absurd h (by simp)
      · exact Bool.noConfusion h.2
      · exact Bool.noConfusion h.2

/-- 簡約単項 \(M\)（\(\textrm{Lng}(M)>1\)）では \(\textrm{dom}(\textrm{Trans}(M))\neq1\)。

原文はここで 系（\(\textrm{Trans}\) と非可算基数の関係）を引くが、その系は
本リポジトリに無い。代わりに 命題（\(\textrm{Pred}\) による \(\textrm{Trans}\) の降下）
と \(D_00\) の最小性で置き換えてある。 -/
theorem not_domIsOne_of_monoT {M : PS} (hM : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) : ¬ domIsOne (PSS.Trans M) := by
  by_cases hz : PSS.Trans M = BZero
  · rw [domIsOne, hz]
    simp [BZero, domTag, domTagList]
  · obtain ⟨q, hp⟩ := Trans_monoT_principal M hM hmono hz
    intro hcontra
    rcases q with ⟨v, b⟩
    have hcontra' : domTagBP (BP.db v b) = BDom.zeroOnly := by
      rw [domIsOne, hp] at hcontra; exact hcontra
    obtain ⟨hv, hb⟩ := (domTagBP_zeroOnly_iff v b).mp hcontra'
    subst hv; subst hb
    have hTM : PSS.Trans M = Dprin 0 BZero := hp
    by_cases ht1 : PSS.Trans (Pred M) = BZero
    · have hPT : TPS (Pred M) := RTPS_TPS (Pred M) (RTPS_Pred M hM)
      have hzp : zeroT (Pred M) = true :=
        (Trans_preserves_zeroT (Pred M) hPT).mpr ht1
      have hlen1 : Lng (Pred M) = 1 := by
        simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzp
        exact hzp.1
      have hpl : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
      have hlen2 : Lng M = 2 := by omega
      have h2c := two_column_Trans M hM hmono hlen2
      rw [hTM] at h2c
      simp [Dprin, BZero] at h2c
    · have hdesc := Pred_Trans_descend_RTPS M hM hlen
      rw [hTM] at hdesc
      exact ht1 (lessBT_D00_imp_zero hdesc)

/-- 最終列が \((0,0)\) なら基本列は \(\textrm{Pred}\)（`oper` の定義の第 2 分岐）。 -/
theorem oper_of_last_zero {M : PS} (hlen : 1 < Lng M)
    (h0 : entry M 0 (Lng M - 1) = 0) (h1 : entry M 1 (Lng M - 1) = 0) (n : ℕ) :
    oper M n = Pred M := by
  have hj1 : Lng M - 1 ≠ 0 := by omega
  simp [oper, hj1, h0, h1]

/-- 原文の証明の後半。最終列が \((0,0)\) のとき
\(\textrm{Trans}(M[n])+D_00=\textrm{Trans}(M)\)。 -/
theorem successor_fseq_of_last_zero {M : PS} (hM : RTPS M) (hlen : 1 < Lng M)
    (h0 : entry M 0 (Lng M - 1) = 0) (h1 : entry M 1 (Lng M - 1) = 0) (n : ℕ) :
    addBT (PSS.Trans (oper M n)) DzeroZero = PSS.Trans M := by
  have hT : TPS M := RTPS_TPS M hM
  have hlt : Lng M - 1 < Lng M := by omega
  have hget : M[Lng M - 1]'hlt = (0, 0) := by
    have hp : (entry M 0 (Lng M - 1), entry M 1 (Lng M - 1)) = M[Lng M - 1]'hlt := by
      simp [entry, List.getElem?_eq_getElem hlt]
    rw [← hp, h0, h1]
  have hPred : Pred M = M.take (Lng M - 1) := by
    simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take]
  have hdrop : M.drop (Lng M - 1) = [(0, 0)] := by
    rw [List.drop_eq_getElem_cons hlt, hget]
    have : Lng M - 1 + 1 = Lng M := by omega
    rw [this]
    simp
  have hsplit : M = Pred M ++ [(0, 0)] := by
    rw [hPred, ← hdrop, List.take_append_drop]
  -- [1] の P の加法性
  have hseg0 : seg M 0 (Lng M - 1 - 1) = Pred M := by
    rw [seg_zero_eq_take M (by omega), hPred]
    congr 1
    omega
  have hseg1 : seg M (Lng M - 1) (Lng M - 1) = [(0, 0)] := by
    simp [seg, h0, h1]
  have hPadd : P M = P (Pred M) ++ P [(0, 0)] := by
    have := P_additivity M (Lng M - 1) hT (by omega) (by omega)
      (fun j _ => by rw [h0]; omega)
    rwa [hseg0, hseg1] at this
  -- Trans の P ブロック分解
  have hRz : RTPS [(0, 0)] := RTPS_zero_singleton
  have hPz : (P [(0, 0)]).getD 0 [] = [(0, 0)] := by decide
  have hkey := f7x_Trans_append_Pblocks_holds (Pred M) [(0, 0)]
    (by rw [← hsplit]; exact hM) hRz (by rw [← hsplit]; exact hPadd)
  rw [← hsplit, hPz, Trans_zero_singleton'] at hkey
  rw [oper_of_last_zero hlen h0 h1 n, hkey]
  simp only [DzeroZero, addBT, BZero]
  rfl

/-! ## 前半のうち複項の場合 -/

/-- 簡約な零項は \(((0,0))\)。 -/
theorem eq_zero_singleton_of_zeroT {N : PS} (hN : RTPS N) (hz : zeroT N = true) :
    N = [(0, 0)] := by
  have hRed : Red N = N := by
    have h : reduced N = true := hN
    simp only [reduced, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  rw [← hRed]; exact Red_zero_mr N hz

/-- 単一ブロックの `P` はそれ自身。 -/
theorem P_self_of_nonmulti {N : PS} (hN : TPS N) (hnm : multiT N = false) :
    P N = [N] := by
  have hnotlt : ¬ (1 < (P N).length) := by
    intro h
    have := (P_components_multi_iff N hN).mpr h
    rw [hnm] at this
    exact Bool.noConfusion this
  have hne : P N ≠ [] := P_nonempty N
  have hpos := List.length_pos_of_ne_nil hne
  have hone : (P N).length = 1 := by omega
  obtain ⟨X, hX⟩ := List.length_eq_one_iff.mp hone
  have hflat := P_concat N
  rw [hX] at hflat
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hflat
  rw [hX, hflat]

/-- 非空リストは「末尾を除いた部分」と「末尾」に分かれる。 -/
theorem eq_dropLast_getLastD : ∀ (l : List PS) (d : PS), l ≠ [] →
    l = l.dropLast ++ [l.getLastD d]
  | [_], _, _ => by simp
  | x :: y :: t, d, _ => by
      have hIH := eq_dropLast_getLastD (y :: t) d (by simp)
      simpa using congrArg (fun z => x :: z) hIH

/-- 前半の本体: \(\textrm{dom}(\textrm{Trans}(M))=1\) なら \(M\) の最終列は \((0,0)\)。 -/
theorem last_zero_of_domIsOne {M : PS} (hM : RTPS M) (hdom : domIsOne (PSS.Trans M)) :
    1 < Lng M ∧ entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0 := by
  have hT : TPS M := RTPS_TPS M hM
  have hpos : 0 < Lng M := List.length_pos_of_ne_nil hT
  have hlen : 1 < Lng M := by
    rcases Nat.lt_or_ge 1 (Lng M) with h | h
    · exact h
    · exact absurd hdom (not_domIsOne_of_lng_one hM (by omega))
  have hzM : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    exact Or.inl (by omega)
  have hmonoM : monoT M = false := by
    by_contra hcm
    exact not_domIsOne_of_monoT hM (by simpa using hcm) hlen hdom
  have hmulti : multiT M = true := by simp [multiT, hzM, hmonoM]
  obtain ⟨hNlast, hAlast⟩ := P_last_multi M hmulti hlen
  have hsplit : M = M.take (Pcut M) ++ M.drop (Pcut M) :=
    (List.take_append_drop _ _).symm
  have hPM : P M = P (M.take (Pcut M)) ++ [M.drop (Pcut M)] := by
    have hne : P M ≠ [] := P_nonempty M
    conv_lhs => rw [eq_dropLast_getLastD (P M) [] hne]
    rw [hAlast, hNlast]
  have hNmem : M.drop (Pcut M) ∈ P M := by rw [hPM]; simp
  have hNR : RTPS (M.drop (Pcut M)) := by
    have hall := (RTPS_iff_P_components M hT).mp hM
    have hlt : (P (M.take (Pcut M))).length < (P M).length := by rw [hPM]; simp
    have hJ : (P M).getD (P (M.take (Pcut M))).length [] = M.drop (Pcut M) := by
      rw [hPM]; simp
    exact hJ ▸ hall _ hlt
  have hNnm := P_components_nonmulti M hT _ hNmem
  have hNT : TPS (M.drop (Pcut M)) := RTPS_TPS _ hNR
  have hNmulti : multiT (M.drop (Pcut M)) = false := by
    rcases hNnm with h | h <;> simp [multiT, h]
  have hPN : P (M.drop (Pcut M)) = [M.drop (Pcut M)] := P_self_of_nonmulti hNT hNmulti
  by_cases hNz : M.drop (Pcut M) = [(0, 0)]
  · have hM2 : M = M.take (Pcut M) ++ [((0 : ℕ), (0 : ℕ))] := by
      conv_lhs => rw [hsplit]
      rw [hNz]
    have hidx : Lng (M.take (Pcut M) ++ [((0 : ℕ), (0 : ℕ))]) - 1
        = (M.take (Pcut M)).length := by simp [Lng]
    refine ⟨hlen, ?_, ?_⟩ <;> rw [hM2, hidx] <;>
      simp [entry]
  · exfalso
    have hzN : zeroT (M.drop (Pcut M)) = false := by
      by_contra hc
      exact hNz (eq_zero_singleton_of_zeroT hNR (by simpa using hc))
    have hTNne : PSS.Trans (M.drop (Pcut M)) ≠ BZero := by
      intro hc
      exact absurd ((Trans_preserves_zeroT _ hNT).mpr hc) (by simp [hzN])
    have hkey := f7x_Trans_append_Pblocks_holds (M.take (Pcut M)) (M.drop (Pcut M))
      (by rw [← hsplit]; exact hM) hNR (by rw [← hsplit, hPM, hPN])
    rw [← hsplit, hPN] at hkey
    simp only [List.getD_cons_zero, if_neg hNz] at hkey
    have hdomN : domIsOne (PSS.Trans (M.drop (Pcut M))) := by
      rw [domIsOne, ← domTag_addBT_right (t := PSS.Trans (M.take (Pcut M))) hTNne,
        ← hkey]
      exact hdom
    rcases hNnm with h | h
    · exact absurd h (by simp [hzN])
    · rcases Nat.lt_or_ge 1 (Lng (M.drop (Pcut M))) with hL | hL
      · exact not_domIsOne_of_monoT hNR h hL hdomN
      · have hL1 : Lng (M.drop (Pcut M)) = 1 := by
          have hp := List.length_pos_of_ne_nil hNT
          simp only [Lng] at hL hp ⊢
          omega
        exact not_domIsOne_of_lng_one hNR hL1 hdomN

/-- 原文の命題（後続な項の基本列）。 -/
theorem successor_fseq {M : PS} (hM : RTPS M) {n : ℕ} (hn : 1 ≤ n)
    (hdom : domIsOne (PSS.Trans M)) :
    (PSS.Trans M = DzeroZero ∧ PSS.Trans (oper M n) = BT.trm []) ∨
      addBT (PSS.Trans (oper M n)) DzeroZero = PSS.Trans M := by
  obtain ⟨hlen, h0, h1⟩ := last_zero_of_domIsOne hM hdom
  exact Or.inr (successor_fseq_of_last_zero hM hlen h0 h1 n)

end Bijectivity
