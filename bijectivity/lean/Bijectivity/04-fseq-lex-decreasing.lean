import Bijectivity.«02b-lex-list-lemmas»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-condAB-coeff»
import «6».«6.2-P-fseq»
import «5».«5.3-pred-is-oper1»
import Bijectivity.«07-oper-pred»

/-!
# 命題（基本列の辞書式的縮小性）

原文: 任意の \(M\in T_{\textrm{PS}}\) と \(n\in\mathbb{N}_+\) に対して、
\(\textrm{Lng}(M)>1\) ならば \(M[n]<_{\textrm{PS}}M\) である。

原文の証明（要旨）:
> \(\textrm{operator}[]\) の定義中の記号を \(M\) に対して定義する。条件より
> \(j_1>0\)。\(M[n]=\textrm{Pred}(M)\) なら明らか。よって \(M_{j_1}\neq(0,0)\) かつ
> ある \(j_0\) が存在して \((i_1,j_0)<^\textrm{Next}_M(i_1,j_1)\) とする。
> \(\textrm{Pred}\) が \([1]\) で表されることより \(n>1\) としてよい。
> \(M[n]=(M_j)_{j=0}^{j_1-1}\oplus_{\mathbb{N}^2}
> \left(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}\right)\) であるから、
> \(M[n]<_{\textrm{PS}}M\) は
> \(\bigoplus_{\mathbb{N}^2}(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})\) と同値。
> 先頭は \((M_{0,j_0}+\delta_0,M_{1,j_0}+\delta_1)\) であり、\(i_1=0\) なら
> \(<^\textrm{Next}\) の定義より \(M_{0,j_0}<M_{0,j_1}\)、\(i_1=1\) なら
> \(M_{1,j_0}<M_{1,j_1}\)。いずれでも従う。□

UNPROVEN STUB — 原文の証明は `oper` の内部記号（\(j_0\), \(i_1\), \(\delta\), \(B\)）
に対する具体計算であり、`PSS.oper` の展開に対する補題群を要する。
-/

namespace Bijectivity

open PSS

/-- \(<^\textrm{Next}\)（上段）は上段成分を狭義に増やす。 -/
theorem nextrel0_entry0_lt {M : PS} {j0 j1 : ℕ} (h : nextrel0 M j0 j1 = true) :
    entry M 0 j0 < entry M 0 j1 := by
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- \(<^\textrm{Next}\)（下段）は下段成分を狭義に増やす。 -/
theorem nextrel1_entry1_lt {M : PS} {j0 j1 : ℕ} (h : nextrel1 M j0 j1 = true) :
    entry M 1 j0 < entry M 1 j1 := by
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- \(<^\textrm{Next}\)（下段）は上段の直系先祖関係を含む。 -/
theorem nextrel1_le0 {M : PS} {j0 j1 : ℕ} (h : nextrel1 M j0 j1 = true) :
    le0 M j0 j1 = true := by
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- 上段の直系先祖関係は上段成分について広義単調。 -/
theorem le0Aux_entry0_le {M : PS} : ∀ (fuel j0 j1 : ℕ),
    le0Aux M fuel j0 j1 = true → entry M 0 j0 ≤ entry M 0 j1
  | 0, j0, j1, h => by
      simp only [le0Aux, beq_iff_eq] at h
      simp [h]
  | fuel + 1, j0, j1, h => by
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨j, _, hn, hle⟩
      · simp [h]
      · exact le_trans (le0Aux_entry0_le fuel j0 j hle) (le_of_lt (nextrel0_entry0_lt hn))

/-- 上段の直系先祖関係は上段成分について広義単調。 -/
theorem le0_entry0_le {M : PS} {j0 j1 : ℕ} (h : le0 M j0 j1 = true) :
    entry M 0 j0 ≤ entry M 0 j1 := by
  simp only [le0, Bool.and_eq_true] at h
  exact le0Aux_entry0_le _ _ _ h.2

/-- 退化枝: `oper M n = Pred M` のとき。真の接頭辞なので \(<_{\textrm{PS}}\)。 -/
theorem oper_ltPS_of_pred {M : PS} {n : ℕ} (hM : 1 < Lng M) (h : oper M n = Pred M) :
    oper M n <ₚ M := by
  rw [h, Pred_eq_take M hM]
  exact ltPS_take M (by omega)

/-- 原文の命題（基本列の辞書式的縮小性）。

退化枝（`oper M n = Pred M`）は `oper_ltPS_of_pred` で閉じている。
残るのは tiling 枝で、原文どおり \(\bigoplus(B_i)_{i=1}^{n-1}<_{\textrm{PS}}(M_{j_1})\)
を \(<^\textrm{Next}\) の定義（`nextrel0` / `nextrel1` が与える
\(M_{0,j_0}<M_{0,j_1}\) / \(M_{1,j_0}<M_{1,j_1}\)）から示す必要がある。 -/
theorem oper_ltPS {M : PS} (hM : 1 < Lng M) (n : ℕ) (hn : 1 ≤ n) : oper M n <ₚ M := by
  have hMne : TPS M := by
    intro he; rw [he] at hM; simp [Lng] at hM
  have hj1ne : Lng M - 1 ≠ 0 := by omega
  by_cases hz : entry M 0 (Lng M - 1) = 0 && entry M 1 (Lng M - 1) = 0
  · exact oper_ltPS_of_pred hM (by simp [oper, hj1ne, hz])
  · by_cases hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true
    · rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        exact oper_ltPS_of_pred hM (pred_is_oper1 M hMne hM).symm
      -- n ≥ 2: ブロック 1 の先頭が \(M_{j_1}\) より小さいことを示す
      obtain ⟨j0, hj0⟩ : ∃ j0, parent M (idx1 M (Lng M - 1)) (Lng M - 1) = j0 := ⟨_, rfl⟩
      obtain ⟨d0, hd0⟩ : ∃ d0,
          (if 0 < idx1 M (Lng M - 1) then entry M 0 (Lng M - 1) - entry M 0 j0 else 0)
            = d0 := ⟨_, rfl⟩
      obtain ⟨d1, hd1⟩ : ∃ d1,
          (if 1 < idx1 M (Lng M - 1) then entry M 1 (Lng M - 1) - entry M 1 j0 else 0)
            = d1 := ⟨_, rfl⟩
      have hj0lt : j0 < Lng M - 1 := hj0 ▸ parent_lt_of_hasParent M _ _ hp
      have hj0M : j0 ≤ M.length := by simp only [Lng] at hj0lt hM; omega
      have hop : oper M n = M.take j0 ++ (List.range n).flatMap (fun k =>
          (List.range' j0 (Lng M - 1 - j0)).map (fun j =>
            (entry M 0 j + k * d0, entry M 1 j + k * d1))) := by
        simp [oper, hj1ne, hz, hp, hj0, hd0, hd1, -mul_ite]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hrange : List.range (m + 2)
          = 0 :: 1 :: ((List.range m).map Nat.succ).map Nat.succ := by
        rw [List.range_succ_eq_map, List.range_succ_eq_map]; simp
      -- 先頭 \(j_1\) 項は M と一致する
      have hpref : M.take j0 ++
          (List.range' j0 (Lng M - 1 - j0)).map (fun j => (entry M 0 j, entry M 1 j))
            = M.take (Lng M - 1) :=
        (take_split M (le_of_lt hj0lt) (by simp only [Lng] at hM ⊢; omega)).symm
      -- 分解
      have hdec : oper M (m + 2) = M.take (Lng M - 1) ++
          ((List.range' j0 (Lng M - 1 - j0)).map (fun j =>
              (entry M 0 j + d0, entry M 1 j + d1))
            ++ (((List.range m).map Nat.succ).map Nat.succ).flatMap (fun k =>
              (List.range' j0 (Lng M - 1 - j0)).map (fun j =>
                (entry M 0 j + k * d0, entry M 1 j + k * d1)))) := by
        rw [hop, hrange]
        simp only [List.flatMap_cons, Nat.zero_mul, Nat.add_zero, Nat.one_mul]
        rw [← List.append_assoc, hpref]
      -- M 側の分解
      have hMdec : M = M.take (Lng M - 1) ++ [(entry M 0 (Lng M - 1), entry M 1 (Lng M - 1))] := by
        conv_lhs => rw [← List.take_append_drop (Lng M - 1) M]
        congr 1
        have hlast : Lng M - 1 < M.length := by simp only [Lng] at hM ⊢; omega
        apply List.ext_getElem
        · simp [Lng] at hM ⊢; omega
        · intro i h1 h2
          simp only [List.length_drop] at h1
          have hi0 : i = 0 := by simp [Lng] at hM h1 ⊢; omega
          subst hi0
          simp [List.getElem_drop, entry, List.getElem?_eq_getElem hlast]
      rw [hdec]
      conv_rhs => rw [hMdec]
      rw [ltPS_append_cancel]
      -- ブロック 1 の先頭と \(M_{j_1}\) の比較
      have hblk : (Lng M - 1 - j0) = (Lng M - 1 - j0 - 1) + 1 := by omega
      rw [hblk]
      simp only [List.range'_succ, List.map_cons, ltPS]
      have hnext := hasParent_next_fseq M (idx1 M (Lng M - 1)) (Lng M - 1) hp
      rw [hj0] at hnext
      by_cases hi1 : idx1 M (Lng M - 1) = 0
      · rw [hi1] at hnext hd0 hd1
        simp only [nextR, if_pos rfl] at hnext
        simp only [lt_irrefl, if_neg (lt_irrefl 0)] at hd0 hd1
        left
        simpa [← hd0] using nextrel0_entry0_lt hnext
      · have hi1' : idx1 M (Lng M - 1) = 1 := by
          simp only [idx1] at hi1 ⊢
          by_cases h : 0 < entry M 1 (Lng M - 1) <;> simp [h] at hi1 ⊢
        rw [hi1'] at hnext hd0 hd1
        simp only [nextR, if_neg one_ne_zero] at hnext
        simp only [if_pos Nat.zero_lt_one, lt_irrefl, if_neg (lt_irrefl 1)] at hd0 hd1
        have hle := le0_entry0_le (nextrel1_le0 hnext)
        right; left
        constructor
        · rw [← hd0]; omega
        · rw [← hd1]; simpa using nextrel1_entry1_lt hnext
    · exact oper_ltPS_of_pred hM (by simp [oper, hj1ne, hz, hp])

/-- 系: \(\textrm{Lng}\) の条件を外した弱形（\(\textrm{Lng}(M)\leq1\) では
`oper M n = M` なので等号で成立する）。 -/
theorem oper_lePS (M : PS) (n : ℕ) (hn : 1 ≤ n) : oper M n ≤ₚ M := by
  rcases Nat.lt_or_ge 1 (Lng M) with h | h
  · exact Or.inr (oper_ltPS h n hn)
  · left
    have : Lng M - 1 = 0 := by omega
    simp [oper, this]

end Bijectivity
