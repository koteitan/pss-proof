import Bijectivity.Cited
import Bijectivity.«11-path-to-initial-segment»
import PSS.Trans
import PSS.Red
import «6».«6.2-P-additivity»
import «6».«6.7-standard-reduced»
import «7».«7.3-Trans-preserves-zeroT»
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
\(P\) の各成分の非複項性から導く。この方向（\(\textrm{Trans}\) の値の形から
ペア数列の形を読み戻す）は本リポジトリにまだ無い。
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

/-- 原文の命題（後続な項の基本列）。

前半（`domIsOne (Trans M)` から `M` の最終列が \((0,0)\) であることを読み戻す部分）が
未証明。後半は `successor_fseq_of_last_zero` で証明済み。 -/
theorem successor_fseq {M : PS} (hM : RTPS M) {n : ℕ} (hn : 1 ≤ n)
    (hdom : domIsOne (PSS.Trans M)) :
    (PSS.Trans M = DzeroZero ∧ PSS.Trans (oper M n) = BT.trm []) ∨
      addBT (PSS.Trans (oper M n)) DzeroZero = PSS.Trans M := by
  sorry

end Bijectivity
