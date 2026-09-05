import Bijectivity.«02-lex-linear»
import Bijectivity.«02b-lex-list-lemmas»

/-!
# 補助（辞書式的順序の「最初の相違位置」による分解）

原文の 基本列的順序が辞書式的順序を含意すること の証明は、

\[
f=\min\Bigl(\{\min(j_1^M,j_1^N)+1\}\cup\{j\mid j\leq\min(j_1^M,j_1^N)\land M_j\neq N_j\}\Bigr)
\]

すなわち「\(M\) と \(N\) の最初の相違位置」で場合分けする。この \(f\) による
場合分けを Lean 側で使える形にしたのがこのファイルである。原文の命題ではなく、
原文が暗黙に使っている \(<_{\textrm{PS}}\) の定義の言い換えにあたる。
-/

namespace Bijectivity

open PSS

/-- \(M_j=(M_{0,j},M_{1,j})\)。 -/
def pairAt (M : PS) (j : ℕ) : ℕ × ℕ := (entry M 0 j, entry M 1 j)

theorem pairAt_eq_getElem (M : PS) {j : ℕ} (h : j < Lng M) : pairAt M j = M[j] := by
  simp [pairAt, entry, List.getElem?_eq_getElem h]

theorem pairAt_take (M : PS) {k j : ℕ} (h : j < k) : pairAt (M.take k) j = pairAt M j := by
  simp [pairAt, entry, List.getElem?_take_of_lt h]

/-- ペアの辞書式比較 \(p<_{\textrm{lex}}q\)。 -/
def pairLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem pairLt_irrefl (p : ℕ × ℕ) : ¬ pairLt p p := by
  rintro (h | ⟨_, h⟩) <;> omega

theorem pairLt_asymm {p q : ℕ × ℕ} (h : pairLt p q) : ¬ pairLt q p := by
  rcases h with h | ⟨h1, h2⟩ <;> rintro (h' | ⟨h1', h2'⟩) <;> omega

/-- 先頭で決まる比較。 -/
theorem ltPS_cons {p q : ℕ × ℕ} (h : pairLt p q) (B C : PS) : (p :: B) <ₚ (q :: C) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- 真の始切片は小さい。 -/
theorem ltPS_of_prefix {M N : PS} (h : M <+: N) (hne : M ≠ N) : M <ₚ N := by
  obtain ⟨R, rfl⟩ := h
  have hR : R ≠ [] := by rintro rfl; simp at hne
  have hlt : ([] : PS) <ₚ R := by
    cases R with
    | nil => exact absurd rfl hR
    | cons _ _ => trivial
  simpa using (ltPS_append_cancel M [] R).mpr hlt

/-- \(<_{\textrm{PS}}\) の分解：始切片であるか、共通接頭辞の直後で決まるか。 -/
theorem ltPS_dest : ∀ (M N : PS), M <ₚ N →
    (M <+: N ∧ M ≠ N) ∨
      ∃ (A : PS) (p q : ℕ × ℕ) (B C : PS),
        M = A ++ p :: B ∧ N = A ++ q :: C ∧ pairLt p q
  | [], [], h => absurd h (by simp [ltPS])
  | [], r :: C, _ => Or.inl ⟨⟨r :: C, rfl⟩, by simp⟩
  | _ :: _, [], h => absurd h (by simp [ltPS])
  | p :: B, q :: C, h => by
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr ⟨[], p, q, B, C, rfl, rfl, Or.inl h⟩
      · exact Or.inr ⟨[], p, q, B, C, rfl, rfl, Or.inr ⟨h1, h2⟩⟩
      · have hpq : p = q := by
          cases p; cases q; simp_all
        subst hpq
        rcases ltPS_dest B C h3 with ⟨⟨R, hR⟩, hne⟩ | ⟨A, p', q', B', C', hB, hC, hlt⟩
        · refine Or.inl ⟨⟨R, by simp [hR]⟩, ?_⟩
          simpa using hne
        · exact Or.inr ⟨p :: A, p', q', B', C', by simp [hB], by simp [hC], hlt⟩

/-- 添字 `k` 未満で一致し `k` 番目で小さければ小さい。 -/
theorem ltPS_of_agree {M N : PS} {k : ℕ} (hM : k < Lng M) (hN : k < Lng N)
    (hpre : M.take k = N.take k)
    (h : pairLt (pairAt M k) (pairAt N k)) : M <ₚ N := by
  rw [pairAt_eq_getElem M hM, pairAt_eq_getElem N hN] at h
  have hM' : M = M.take k ++ M[k] :: M.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k M, List.drop_eq_getElem_cons hM]
  have hN' : N = N.take k ++ N[k] :: N.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k N, List.drop_eq_getElem_cons hN]
  conv_lhs => rw [hM']
  conv_rhs => rw [hN']
  rw [hpre]
  exact (ltPS_append_cancel _ _ _).mpr (ltPS_cons h _ _)

private theorem pairAt_append_mid (A : PS) (p : ℕ × ℕ) (B : PS) :
    pairAt (A ++ p :: B) A.length = p := by
  rw [pairAt_eq_getElem _ (by simp)]
  simp

/-- 原文の \(f\) による場合分け。 -/
theorem ltPS_dest_idx {M N : PS} (h : M <ₚ N) :
    (Lng M < Lng N ∧ M = N.take (Lng M)) ∨
      ∃ k, k < Lng M ∧ k < Lng N ∧ M.take k = N.take k ∧
        pairLt (pairAt M k) (pairAt N k) := by
  rcases ltPS_dest M N h with ⟨⟨R, hR⟩, hne⟩ | ⟨A, p, q, B, C, hM, hN, hlt⟩
  · have hRne : R ≠ [] := by
      rintro rfl
      exact hne (by simpa using hR)
    have hpos : 0 < R.length := List.length_pos_of_ne_nil hRne
    subst hR
    refine Or.inl ⟨?_, ?_⟩
    · simp only [Lng, List.length_append]
      omega
    · simp
  · subst hM; subst hN
    refine Or.inr ⟨A.length, ?_, ?_, ?_, ?_⟩
    · simp only [Lng, List.length_append, List.length_cons]; omega
    · simp only [Lng, List.length_append, List.length_cons]; omega
    · simp
    · rw [pairAt_append_mid, pairAt_append_mid]; exact hlt

/-- 切片が小さければ本体も小さい（相手が切片より短いとき）。 -/
theorem ltPS_of_take_ltPS {M N : PS} {k : ℕ} (hk : Lng N ≤ k) (h : M.take k <ₚ N) :
    M <ₚ N := by
  simp only [Lng] at hk
  rcases ltPS_dest_idx h with ⟨hlen, _⟩ | ⟨d, hdM, hdN, hpre, hlt⟩
  · have hMk : M.length < k := by
      simp only [Lng, List.length_take] at hlen
      omega
    rwa [List.take_of_length_le (le_of_lt hMk)] at h
  · simp only [Lng, List.length_take] at hdM
    have hdk : d < k := by omega
    have hdM' : d < Lng M := by simp only [Lng]; omega
    refine ltPS_of_agree hdM' hdN ?_ ?_
    · rw [← hpre, List.take_take]
      congr 1
      omega
    · rwa [pairAt_take M hdk] at hlt

end Bijectivity
