import Bijectivity.«12b-ctps-finite»
import Bijectivity.«11-path-to-initial-segment»
import Bijectivity.«10-countable-standard-origin»
import Bijectivity.«06-fseq-segment-invariance»
import Bijectivity.«05-exp-implies-lex»

/-!
# 補助（原文 基本列的順序が辞書式的順序を含意すること の主要部）

原文の証明の中核は「\(f=j_1^N\) の場合」の議論である。すなわち

> \(M<_{\textrm{PS}}N\) かつ \((M_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\) のとき、
> \(N\) について結論が既知（内側の帰納法の仮定）ならば \(M<_{\textrm{PS}[]}N\)。

この形を `big_step` として切り出す。証明は原文の手順をそのまま辿る:

1. 可算な標準形の起源 で共通の上界 \(((j,j))_{j=0}^v\) をとる
2. \(M=((j,j))_{j=0}^v[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\) と書く
3. \(((j,j))_{j=0}^v[a_0]\cdots[a_g]<_{\textrm{PS}}N\) となる最小の \(g\) を \(g_0\)、
   \(N'=((j,j))_{j=0}^v[a_0]\cdots[a_{g_0-1}]\) とする
4. \(N<_{\textrm{PS}}N'\) と仮定すると、任意の \(n\) に対し \(N'[n]<_{\textrm{PS}}N\) となり、
   仮定 \(N<_{\textrm{PS}[]}N'\) と矛盾する
5. よって \(N=N'\) であり \(M=N[a_{g_0}]\cdots\) すなわち \(M<_{\textrm{PS}[]}N\)
-/

namespace Bijectivity

open PSS

/-! ## 対角列の始切片 -/

theorem length_diagSeq (u v : ℕ) : Lng (diagSeq u v) = v + 1 - u := by
  simp [diagSeq]

theorem diagSeq_take {u v : ℕ} (h : u ≤ v) : (diagSeq 0 v).take (u + 1) = diagSeq 0 u := by
  apply List.ext_getElem
  · simp [diagSeq]; omega
  · intro j h1 h2
    simp [diagSeq]

/-- 標準形の始切片への経路 の対角列への適用。 -/
theorem diagSeq_leExpPS {u v : ℕ} (h : u ≤ v) : diagSeq 0 u ≤ₚ[] diagSeq 0 v := by
  have hlen : Lng (diagSeq 0 v) = v + 1 := by simp [length_diagSeq]
  have hT : TPS (diagSeq 0 v) := by
    intro he
    rw [he] at hlen
    simp at hlen
  have hstep := seg_leExpPS hT (j1' := u) (by rw [hlen]; omega)
  rwa [seg_zero_eq_take _ (by rw [hlen]; omega), diagSeq_take h] at hstep

/-! ## 順序の小道具 -/

theorem lePS_ltPS_trans {A B C : PS} (h1 : A ≤ₚ B) (h2 : B <ₚ C) : A <ₚ C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact ltPS_trans h1 h2

/-- 原文「\(M\leq_{\textrm{PS}}K<_{\textrm{PS}}N\) かつ \(M\) と \(N\) が
\(j\) 未満で一致 ⟹ \(K\) と \(N\) も \(j\) 未満で一致」。 -/
theorem sandwich_agree {M K N : PS} {j : ℕ}
    (hMK : M ≤ₚ K) (hKN : K <ₚ N) (hjM : j < Lng M) (hjN : j ≤ Lng N)
    (hagree : M.take j = N.take j) : K.take j = N.take j ∧ j < Lng K := by
  rcases hMK with rfl | hMK
  · exact ⟨hagree, hjM⟩
  rcases ltPS_dest_idx hMK with ⟨hlen, hpre⟩ | ⟨d, hdM, hdK, hdpre, hdlt⟩
  · refine ⟨?_, by simp only [Lng] at hjM hlen ⊢; omega⟩
    have hstep : K.take j = (K.take (Lng M)).take j := by
      rw [List.take_take]
      congr 1
      simp only [Lng] at hjM ⊢
      omega
    rw [hstep, ← hpre, hagree]
  · rcases Nat.lt_or_ge d j with hdj | hjd
    · exfalso
      have hMNd : pairAt M d = pairAt N d := by
        rw [← pairAt_take M hdj, ← pairAt_take N hdj, hagree]
      have hNKpre : N.take d = K.take d := by
        rw [← hdpre]
        have hcut : (M.take j).take d = (N.take j).take d := by rw [hagree]
        rw [List.take_take, List.take_take] at hcut
        have hmin : min d j = d := by omega
        rw [hmin] at hcut
        exact hcut.symm
      have hdN : d < Lng N := by
        simp only [Lng] at hjN ⊢
        omega
      have : N <ₚ K := ltPS_of_agree hdN hdK hNKpre (by rw [← hMNd]; exact hdlt)
      exact ltPS_irrefl N (ltPS_trans this hKN)
    · refine ⟨?_, by simp only [Lng] at hdK ⊢; omega⟩
      have hstep : K.take j = (K.take d).take j := by
        rw [List.take_take]
        congr 1
        omega
      rw [hstep, ← hdpre, List.take_take]
      have : min j d = j := by omega
      rw [this, hagree]

/-- 原文「\((N'[a_{g_0}]_j)_{j=0}^{j_1^N}<_{\textrm{PS}}N\)」。 -/
theorem take_last_ltPS {K N : PS} {j : ℕ} (hN : Lng N = j + 1) (hjK : j < Lng K)
    (hagree : K.take j = N.take j) (hKN : K <ₚ N) : K.take (j + 1) <ₚ N := by
  rcases ltPS_dest_idx hKN with ⟨hlen, _⟩ | ⟨d, hdK, hdN, hdpre, hdlt⟩
  · exfalso; simp only [Lng] at hlen hjK hN; omega
  · have hdj : d = j := by
      by_contra hne
      have hdlt' : d < j := by simp only [Lng] at hdN hN; omega
      have : pairAt K d = pairAt N d := by
        rw [← pairAt_take K hdlt', ← pairAt_take N hdlt', hagree]
      rw [this] at hdlt
      exact pairLt_irrefl _ hdlt
    subst hdj
    refine ltPS_of_agree (k := d) (by simp only [Lng, List.length_take] at hjK ⊢; omega)
      (by simp only [Lng] at hN ⊢; omega) ?_ ?_
    · rw [List.take_take]
      have : min d (d + 1) = d := by omega
      rw [this, hagree]
    · rwa [pairAt_take K (Nat.lt_succ_self d)]

/-! ## 基本列の切片の不変性（take 形） -/

theorem oper_take_eq (N : PS) {m n k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hkm : k ≤ Lng (oper N m)) (hkn : k ≤ Lng (oper N n)) :
    (oper N m).take k = (oper N n).take k := by
  have key : ∀ p q : ℕ, 1 ≤ p → p ≤ q → k ≤ Lng (oper N p) →
      (oper N p).take k = (oper N q).take k := by
    intro p q hp hpq hk
    obtain ⟨R, hR⟩ := oper_prefix N hp hpq
    rw [hR, List.take_append_of_le_length hk]
  rcases Nat.le_total m n with h | h
  · exact key m n hm h hkm
  · exact (key n m hn h hkn).symm

theorem oper_eq_take (N : PS) {m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    oper N n = (oper N m).take (Lng (oper N n)) := by
  obtain ⟨R, hR⟩ := oper_prefix N hn hnm
  rw [hR]
  simp

/-! ## 主要部 -/

/-- 原文の \(f=j_1^N\) の場合の議論。`hPhiN` が内側の帰納法の仮定にあたる。 -/
theorem big_step {M N : PS} (hM : CTPS M) (hN : CTPS N)
    (hlt : M <ₚ N) (hlen : Lng N ≤ Lng M)
    (hagree : M.take (Lng N - 1) = N.take (Lng N - 1))
    (hPhiN : ∀ N' : PS, CTPS N' → N <ₚ N' → N <ₚ[] N') :
    M <ₚ[] N := by
  classical
  have hNne : N ≠ [] := STPS_TPS N hN.1
  have hNpos : 0 < Lng N := List.length_pos_of_ne_nil hNne
  obtain ⟨j1, hN1⟩ : ∃ k, Lng N = k + 1 := ⟨Lng N - 1, by simp only [Lng] at hNpos ⊢; omega⟩
  rw [hN1, Nat.add_sub_cancel] at hagree
  have hjM : j1 < Lng M := by simp only [Lng] at hlen hN1 ⊢; omega
  -- 手順 1, 2: 共通の上界 ((j,j))_{j=0}^v
  obtain ⟨vM, hvM⟩ := (ctps_iff_leExpPS M).mp hM
  obtain ⟨vN, hvN⟩ := (ctps_iff_leExpPS N).mp hN
  set v := max vM vN with hv
  have hMv : M ≤ₚ[] diagSeq 0 v :=
    leExpPS_trans hvM (diagSeq_leExpPS (le_max_left vM vN))
  have hNv : N ≤ₚ[] diagSeq 0 v :=
    leExpPS_trans hvN (diagSeq_leExpPS (le_max_right vM vN))
  obtain ⟨a, ha, hMa⟩ := hMv
  -- 辞書式的順序が基本列的順序を含意すること
  have hNle : N ≤ₚ diagSeq 0 v := by
    obtain ⟨b, hb, hNb⟩ := hNv
    rw [hNb]
    exact expand_lePS b _ hb
  have hane : a ≠ [] := by
    rintro rfl
    rw [show expand (diagSeq 0 v) [] = diagSeq 0 v from rfl] at hMa
    exact ltPS_irrefl N (lePS_ltPS_trans (hMa ▸ hNle) hlt)
  have hapos : 0 < a.length := List.length_pos_of_ne_nil hane
  -- 手順 3: 最小の g₀
  have hwit : expand (diagSeq 0 v) (a.take (a.length - 1 + 1)) <ₚ N := by
    have hL : a.length - 1 + 1 = a.length := by omega
    rw [hL, List.take_length, ← hMa]
    exact hlt
  have hex : ∃ g, expand (diagSeq 0 v) (a.take (g + 1)) <ₚ N := ⟨a.length - 1, hwit⟩
  set g0 := Nat.find hex with hg0def
  have hKlt : expand (diagSeq 0 v) (a.take (g0 + 1)) <ₚ N := Nat.find_spec hex
  have hg0lt : g0 < a.length := by
    have hle : Nat.find hex ≤ a.length - 1 := Nat.find_le hwit
    omega
  set N' := expand (diagSeq 0 v) (a.take g0) with hN'def
  set m := a[g0]'hg0lt with hmdef
  have hm1 : 1 ≤ m := ha m (by rw [hmdef]; exact List.getElem_mem hg0lt)
  -- K = N'[a_{g₀}]
  have htakesucc : a.take (g0 + 1) = a.take g0 ++ [m] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hg0lt]
    rfl
  have hKeq : expand (diagSeq 0 v) (a.take (g0 + 1)) = oper N' m := by
    rw [htakesucc, expand_append, ← hN'def]
    rfl
  rw [hKeq] at hKlt
  -- N' は CT_PS の元
  have hN'ct : CTPS N' := by
    refine (ctps_iff_leExpPS N').mpr ⟨v, a.take g0, ?_, rfl⟩
    intro n hn
    exact ha n (List.mem_of_mem_take hn)
  -- 手順 3 後半: N ≤ₚ N'
  have hNN' : N ≤ₚ N' := by
    rcases Nat.eq_zero_or_pos g0 with hz | hpos
    · rw [hN'def, hz, List.take_zero]
      exact hNle
    · have hmin : ¬ (expand (diagSeq 0 v) (a.take (g0 - 1 + 1)) <ₚ N) :=
        Nat.find_min hex (by omega)
      have : g0 - 1 + 1 = g0 := by omega
      rw [this] at hmin
      rcases ltPS_trichotomy N N' with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd h hmin
  -- M ≤ₚ N'[a_{g₀}]
  have hMK : M ≤ₚ oper N' m := by
    have hsplit : a = a.take (g0 + 1) ++ a.drop (g0 + 1) := (List.take_append_drop _ _).symm
    have : M = expand (oper N' m) (a.drop (g0 + 1)) := by
      rw [hMa]
      conv_lhs => rw [hsplit]
      rw [expand_append, hKeq]
    rw [this]
    exact expand_lePS _ _ (fun n hn => ha n (List.mem_of_mem_drop hn))
  -- 手順 4: N <ₚ N' からの矛盾
  have hNeq : N = N' := by
    rcases hNN' with h | h
    · exact h
    exfalso
    obtain ⟨hKagree, hjK⟩ := sandwich_agree hMK hKlt hjM (by omega) hagree
    have hKtake : (oper N' m).take (j1 + 1) <ₚ N := take_last_ltPS hN1 hjK hKagree hKlt
    -- 任意の n ≥ 1 に対して N'[n] <ₚ N
    have hall : ∀ n : ℕ, 1 ≤ n → oper N' n <ₚ N := by
      intro n hn
      by_cases hshort : Lng (oper N' n) ≤ j1
      · -- 短いときは N'[a_{g₀}] の真の始切片（基本列の切片の不変性）
        have hnm : n ≤ m := by
          by_contra hc
          obtain ⟨R, hR⟩ := oper_prefix N' hm1 (le_of_lt (Nat.lt_of_not_le hc))
          rw [hR] at hshort
          simp only [Lng, List.length_append] at hshort hjK
          omega
        have heq2 : oper N' n = ((oper N' m).take (j1 + 1)).take (Lng (oper N' n)) := by
          rw [List.take_take]
          have hmin : min (Lng (oper N' n)) (j1 + 1) = Lng (oper N' n) := by
            simp only [Lng] at hshort ⊢; omega
          rw [hmin]
          exact oper_eq_take N' hn hnm
        have hlt2 : oper N' n <ₚ (oper N' m).take (j1 + 1) := by
          conv_lhs => rw [heq2]
          exact ltPS_take _ (by simp only [Lng, List.length_take] at hshort hjK ⊢; omega)
        exact ltPS_trans hlt2 hKtake
      · -- 長いときは j1+1 までが一致（基本列の切片の不変性）
        have hlong : j1 + 1 ≤ Lng (oper N' n) := by
          simp only [Lng] at hshort ⊢; omega
        have hKlong : j1 + 1 ≤ Lng (oper N' m) := by simp only [Lng] at hjK ⊢; omega
        have hsame := oper_take_eq N' hn hm1 hlong hKlong
        refine ltPS_of_take_ltPS (k := j1 + 1) (by omega) ?_
        rw [hsame]
        exact hKtake
    -- 仮定（内側の帰納法）より N <ₚ[] N'
    obtain ⟨c, hcne, hc, hNc⟩ := hPhiN N' hN'ct h
    cases c with
    | nil => exact hcne rfl
    | cons c0 c =>
        have hc0 : 1 ≤ c0 := hc c0 (by simp)
        have hstep : N ≤ₚ oper N' c0 := by
          rw [hNc]
          exact expand_lePS c _ (fun n hn => hc n (by simp [hn]))
        exact ltPS_irrefl N (lePS_ltPS_trans hstep (hall c0 hc0))
  -- 手順 5
  have hsplit : a = a.take g0 ++ a.drop g0 := (List.take_append_drop _ _).symm
  refine ⟨a.drop g0, ?_, fun n hn => ha n (List.mem_of_mem_drop hn), ?_⟩
  · intro he
    have hlen0 := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hlen0
    omega
  · rw [hMa, hNeq, hN'def, ← expand_append, List.take_append_drop]

end Bijectivity
