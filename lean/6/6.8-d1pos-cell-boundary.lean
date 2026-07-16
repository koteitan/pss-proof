import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-notbrle»
import «6».«6.8-d1pos-anchor-regA»
import «5».«5.1-parent-basic»

/-!
# §6.8 d1pos ¬brle BOUNDARY セル ＋ 周期境界 anchor brick 群

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1`（d1pos）
  ¬brle 跨りスライスのうち、開始が base（`j'₀ < j₋₂`）で枝源 `A` が周期境界を
  跨ぐ BOUNDARY セル、および周期境界 anchor（undercut / mLmin / cle / cleMB））
- 訂正: なし（A7/A8 は上位 `6.8-standard-slice-Br-descending` 側で適用済み）
- Isabelle (isabelle/pss_mechanized.thy):
  - `oper_d1pos_notbrle_LOW_take_eq_boundary` (18323)
  - `oper_d1pos_period_boundary_undercut` (20488)
  - `oper_d1pos_period_boundary_mLmin` (20513)
  - `oper_d1pos_period_boundary_cle` (20557)
  - `oper_d1pos_period_boundary_cleMB` (21135)
- Prop discharge: `D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary_holds` /
  `D1pos_oper_d1pos_period_boundary_cleMB_holds`
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_*` Prop 定義・`oper_d1pos_ctx_dpos`）、
  «6».«6.8-d1pos-notbrle»（`oper_d1pos_notbrle_Br_align`/`_regA`）、
  «6».«6.8-d1pos-anchor-regA»（`oper_d1pos_period_row0_floor`・
  `oper_d1pos_strict_period_floor`）、
  «6».«6.8-standard-slice-Br-descending»（`d1posAlignment_of_shift_boundary_68`・
  `P_last_anchor_68`・`last_anchor_ge_of_leftmin_68`・`length_oper_d1pos_68`・
  `entry_oper_d1pos_zero_68`、推移 import）、
  «5».«5.1-parent-basic»（`parent_basic_1`）
- 状態: ✅ 証明済（sorry 0）

Isabelle との対応メモ:
- BOUNDARY セルは Isabelle では anchor 一致→lowshift→collapse→tail junction を
  手組みするが、Lean では同じ配線が `d1posAlignment_of_shift_boundary_68`
  （`6.8-standard-slice-Br-descending`）に一般形で既にあるため、
  regime-A Br 整列（`oper_d1pos_notbrle_Br_align_regA`）＋ TrEq 書換えだけで閉じる。
- private 複製（本ファイル私用、suffix `_bd`）: `TPS_of_P_multi_bd`
  （`1 < |P S| → S ≠ []`）、`anchor_lt_of_uniform_witness_bd`（Isabelle 15865）、
  `le0Aux_refl_bd`・`P_short_len_bd`（`Lng ≤ 1 → |P X| = 1`）、
  `period_boundary_cleMB_core_bd`（Isabelle 21135 の中核＝境界証人 `jj = m` の
  一様 strict 証人）。
-/

namespace PSS

/-! ## 小補助（private、suffix `_bd`） -/

/-- `1 < (P S).length` なら `S` は空列でない（`P [] = [[]]` は長さ 1）。
Isabelle 側は `P.simps` の直接評価。 -/
private theorem TPS_of_P_multi_bd (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

/-- `le0Aux` の反射律（`6.8-d1pos-base` の private 複製）。 -/
private theorem le0Aux_refl_bd (M : PS) (fuel j : ℕ) :
    le0Aux M fuel j j = true := by
  cases fuel <;> simp [le0Aux]

/-- `Lng X ≤ 1` なら `P X` は単成分（`P X = [X]`）。Isabelle 側は
`P.simps` ＋ `if_not_P`。 -/
private theorem P_short_len_bd (X : PS) (h : Lng X ≤ 1) :
    (P X).length = 1 := by
  cases X with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil =>
      have hm : multiT [a] = false := by
        cases hz : zeroT [a] with
        | true => simp [multiT, hz]
        | false =>
          have h00 : le0 [a] 0 0 = true := by
            simp [le0, Lng, le0Aux_refl_bd]
          have hmono : monoT [a] = true := by
            simp only [monoT, hz, Bool.not_false, Bool.true_and]
            have hL : Lng ([a] : PS) - 1 = 0 := rfl
            rw [hL]
            simpa [leR] using h00
          simp [multiT, hmono]
      rw [P_nonmulti_eq [a] hm]
      rfl
    | cons b t2 =>
      exfalso
      have hb : 2 ≤ Lng (a :: b :: t2) := by
        show 2 ≤ (a :: b :: t2).length
        simp only [List.length_cons]
        omega
      omega

/-- Isabelle `anchor_lt_of_uniform_witness` (15865) の私的再証明。
一様行 0 証人 `jj < k` があれば最終 anchor は `k` 未満。 -/
private theorem anchor_lt_of_uniform_witness_bd
    (S : PS) (k jj : ℕ) (hS : TPS S) (hmulti : 1 < (P S).length)
    (hjj : jj < k)
    (hwit : ∀ x, k ≤ x → x ≤ Lng S - 1 → entry S 0 jj < entry S 0 x) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 < k := by
  obtain ⟨_, hcle, hlmin, _, _⟩ := P_last_anchor_68 S hS hmulti
  by_contra hnot
  have hkc : k ≤ (IdxSum (P S)).getD ((P S).length - 1) 0 := by omega
  have ha := hlmin jj (by omega)
  have hb := hwit ((IdxSum (P S)).getD ((P S).length - 1) 0) hkc hcle
  omega

/-! ## BOUNDARY セル（Isabelle `oper_d1pos_notbrle_LOW_take_eq_boundary` 18323）

スライス開始は base（`j'₀ < j₋₂`、N-verbatim・`shamt = 0`・`j₀ʳᵉᵈ = j'₀`）だが
枝源 `A = j'₀ + TrMax M' + 1` は周期境界を跨ぐ（`j₋₂ ≤ A < Lng N - 1`）。
witness は regime-A 形（`j₁ʳᵉᵈ = Lng N - 1`, `shamt = 0`）、幾何は regime-B 形
（境界 anchor）。Lean では regime-A の Br 整列と、供給済みの UNIFIED anchor
入力（shiftEqB/boundEq0B/boundEq1B/cleMB/mleSB）を
`d1posAlignment_of_shift_boundary_68` に渡すだけで閉じる。 -/

theorem oper_d1pos_notbrle_LOW_take_eq_boundary
    (N M : PS) (n j0' j1' : ℕ)
    (_NT : TPS N) (_monoN : monoT N = true) (LNgt : 1 < Lng N)
    (notzeroN : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hasparN : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1zN : idx1 N (Lng N - 1) = 1)
    (Neq : M = oper N n)
    (n1 : 1 ≤ n)
    (_M'T : TPS (seg M j0' j1'))
    (_le0M : leR M 0 j0' j1' = true)
    (lt : j0' < j1')
    (jM : j1' < Lng M)
    (bge : Lng N - 1 ≤ j1')
    (notbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (Areg : parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1 ∧
      j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1)
    (_j0ltjm2 : j0' < parent N 1 (Lng N - 1))
    (multiM : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (multiNp : 1 < (P (seg N (j0' + TrMax (seg M j0' j1') + 1)
      (Lng N - 1))).length)
    (le0Np : leR N 0 j0' (Lng N - 1) = true)
    (tnc : TrMax (seg N j0' (Lng N - 1)) ≤ Lng N - 1 - 1 - j0')
    (stop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0' (Lng N - 1)))
      (TrMax (seg N j0' (Lng N - 1)) + 1) = false)
    (shiftEqB : seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1) =
      IncrFirstN 0
        (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
          (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)))
    (boundEq0B : entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) =
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + 0)
    (boundEq1B : entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) ≤
      entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
        (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1))
    (_lenPSeqB : (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length)
    (cleMB : (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
    (mleSB : Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1) :
    d1posAlignment_68 N (seg M j0' j1') := by
  subst Neq
  -- (1) regime-A Br 整列（`j₀ʳᵉᵈ = j'₀`、`j₁ʳᵉᵈ = Lng N - 1`）: TrEq ＋両 reshape
  obtain ⟨hTrEq, hBrM, hBrN, _, _⟩ :=
    oper_d1pos_notbrle_Br_align_regA N n j0' (Lng N - 1) j0' j1'
      LNgt notzeroN hasparN i1zN j0lt n1 le_rfl (by omega) (by omega) rfl
      lt jM tnc stop notbrle
  -- N 側 reshape の添字を M 側 TrMax に書き換え（TrEq）
  rw [← hTrEq] at hBrN
  have hST : TPS (seg (oper N n)
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
    TPS_of_P_multi_bd _ multiM
  have hSnT : TPS (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1)
      (Lng N - 1)) :=
    TPS_of_P_multi_bd _ multiNp
  have hle0 : le0 N j0' (Lng N - 1) = true := by
    simpa [leR] using le0Np
  -- (2)–(4) anchor 一致・lowshift・collapse・tail junction は一般形の
  -- `d1posAlignment_of_shift_boundary_68` が一括で配線する
  exact d1posAlignment_of_shift_boundary_68 N (seg (oper N n) j0' j1')
    (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')
    (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1))
    j0' (Lng N - 1) 0 (by omega) le_rfl hle0 hBrM hBrN hST hSnT
    multiM multiNp mleSB cleMB shiftEqB boundEq0B boundEq1B

/-- Prop discharge: `D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary`
（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary_holds :
    D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary := by
  intro N M n j0' j1' NT monoN LNgt notzeroN hasparN i1zN Neq n1 M'T le0M
    lt jM bge notbrle j0lt dpos Areg j0ltjm2 multiM multiNp le0Np tnc stop
    shiftEqB boundEq0B boundEq1B lenPSeqB cleMB mleSB
  exact oper_d1pos_notbrle_LOW_take_eq_boundary N M n j0' j1' NT monoN LNgt
    notzeroN hasparN i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos Areg
    j0ltjm2 multiM multiNp le0Np tnc stop shiftEqB boundEq0B boundEq1B
    lenPSeqB cleMB mleSB

/-! ## 周期境界 undercut（Isabelle `oper_d1pos_period_boundary_undercut` 20488）

周期 TOP 値 `entry N 0 (Lng N - 1)` は、行 0 親 `p` より右の全内部添字の行 0 値
以下（`m_5_1_parent_basic_1` = Lean `parent_basic_1` の直接帰結）。 -/

theorem oper_d1pos_period_boundary_undercut
    (N : PS) (p A x : ℕ)
    (NT : TPS N)
    (parR : nextR N 0 p (Lng N - 1) = true)
    (pA : p < A)
    (Ax : A ≤ x)
    (xlt : x < Lng N - 1) :
    entry N 0 (Lng N - 1) ≤ entry N 0 x :=
  parent_basic_1 N p x (Lng N - 1) NT (by omega) (by omega) parR

/-! ## 周期境界 mLmin（Isabelle `oper_d1pos_period_boundary_mLmin` 20513）

境界添字 `m = Lng Snside - 1` は `Snside = seg N AN (Lng N - 1)` の
行 0 左最小値（undercut の切片持ち上げ）。 -/

theorem oper_d1pos_period_boundary_mLmin
    (N : PS) (p AN : ℕ)
    (NT : TPS N)
    (parR : nextR N 0 p (Lng N - 1) = true)
    (pA : p < AN)
    (ANlt : AN < Lng N - 1) :
    ∀ j, j < Lng (seg N AN (Lng N - 1)) - 1 →
      entry (seg N AN (Lng N - 1)) 0 (Lng (seg N AN (Lng N - 1)) - 1) ≤
        entry (seg N AN (Lng N - 1)) 0 j := by
  intro j jm
  have hLSn : Lng (seg N AN (Lng N - 1)) = (Lng N - 1) + 1 - AN :=
    length_seg _ _ _
  have hmlt : Lng (seg N AN (Lng N - 1)) - 1 <
      Lng (seg N AN (Lng N - 1)) := by omega
  have hjlt : j < Lng (seg N AN (Lng N - 1)) := by omega
  rw [entry_seg N AN (Lng N - 1) 0 (Lng (seg N AN (Lng N - 1)) - 1) hmlt,
    entry_seg N AN (Lng N - 1) 0 j hjlt,
    show AN + (Lng (seg N AN (Lng N - 1)) - 1) = Lng N - 1 from by omega]
  exact oper_d1pos_period_boundary_undercut N p AN (AN + j) NT parR pA
    (by omega) (by omega)

/-! ## 周期境界 cle（Isabelle `oper_d1pos_period_boundary_cle` 20557）

`m` が左最小値かつ尾部 `(m, Lng S - 1]` を厳格に undercut するなら、
M 側 anchor `c` は丁度 `m`（`c ≤ m` は一様証人、`c ≥ m` は左最小値橋）。
Isabelle の `defines c` はインライン展開。 -/

theorem oper_d1pos_period_boundary_cle
    (S : PS) (m : ℕ)
    (ST : TPS S) (multi : 1 < (P S).length)
    (mle : m ≤ Lng S - 1)
    (lmin : ∀ j, j < m → entry S 0 m ≤ entry S 0 j)
    (tailgt : ∀ x, m < x ∧ x ≤ Lng S - 1 → entry S 0 m < entry S 0 x) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 = m := by
  have hlt : (IdxSum (P S)).getD ((P S).length - 1) 0 < m + 1 :=
    anchor_lt_of_uniform_witness_bd S (m + 1) m ST multi (by omega)
      (fun x hx1 hx2 => tailgt x ⟨by omega, hx2⟩)
  have hge : m ≤ (IdxSum (P S)).getD ((P S).length - 1) 0 :=
    last_anchor_ge_of_leftmin_68 S m ST mle lmin
  omega

/-! ## 周期境界 cleMB（Isabelle `oper_d1pos_period_boundary_cleMB` 21135）

cap ACTIVE（`j₁ʳᵉᵈ = Lng N - 1`）のとき枝領域 `S = seg (N[n]) A j₁'`
（`A = AN + q₀·w`）は境界添字 `m = Lng Snside - 1` を越えて伸びる。`m` より右の
全添字は次ブロック（`q₀+1` 以上）に落ち、`δ > 0` により境界証人 `jj = m`
（周期 TOP、ブロック `q₀`）を厳格に上回る。ゆえに anchor `c ≤ m`。 -/

/-- cleMB の中核: `A + m` がブロック境界 `j₋₂ + (q₀+1)·w` に一致し
`A + m ≤ E < Lng (N[n])` なら、`S = seg (N[n]) A E` の右端 anchor は `m` 以下。
（Isabelle 21135 の証明本体、境界証人 `jj = m` の一様 strict 証人組み立て。） -/
private theorem period_boundary_cleMB_core_bd
    (N : PS) (n q0 A E m : ℕ)
    (LNgt : 1 < Lng N)
    (notzeroN : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hasparN : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1zN : idx1 N (Lng N - 1) = 1)
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hq0n : q0 < n)
    (hAm : A + m = parent N 1 (Lng N - 1) +
      (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)))
    (hAmE : A + m ≤ E)
    (hE : E < Lng (oper N n))
    (multiS : 1 < (P (seg (oper N n) A E)).length) :
    (IdxSum (P (seg (oper N n) A E))).getD
      ((P (seg (oper N n) A E)).length - 1) 0 ≤ m := by
  have hST : TPS (seg (oper N n) A E) := TPS_of_P_multi_bd _ multiS
  have hLngM : Lng (oper N n) = parent N 1 (Lng N - 1) +
      n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
    length_oper_d1pos_68 N n LNgt notzeroN hasparN i1zN
  have hw0 : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1) :=
    oper_d1pos_ctx_dpos N hasparN i1zN j0lt
  have lenS : Lng (seg (oper N n) A E) = E + 1 - A := length_seg _ _ _
  have hmS : m < Lng (seg (oper N n) A E) := by omega
  -- 積アトムの橋（(q₀+1)·w = q₀·w + w、δ 版も同様）
  have hsmW : (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (Lng N - 1 - parent N 1 (Lng N - 1)) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hsmD : (q0 + 1) * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) =
      q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1))) +
        (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1))) := by
    rw [Nat.add_mul, Nat.one_mul]
  -- `q₀ + 1 < n`（さもなくば `A + m = Lng (N[n]) > E ≥ A + m`、矛盾＝空虚ケース）
  have hq1n : q0 + 1 < n := by
    rcases Nat.lt_or_ge (q0 + 1) n with h | h
    · exact h
    · exfalso
      have hq1 : q0 + 1 = n := by omega
      have heqw : (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
          n * (Lng N - 1 - parent N 1 (Lng N - 1)) := by rw [hq1]
      omega
  -- 境界読み出し: `entry S 0 m = 周期 TOP + q₀·δ`（ブロック q₀ の頂上）
  have heSm : entry (seg (oper N n) A E) 0 m =
      entry N 0 (Lng N - 1) +
        q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1))) := by
    have hdecode := entry_oper_d1pos_zero_68 N n (q0 + 1) 0 LNgt notzeroN
      hasparN i1zN hq1n (by omega)
    rw [entry_seg (oper N n) A E 0 m hmS,
      show A + m = parent N 1 (Lng N - 1) +
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) + 0 from by omega,
      hdecode]
    simp only [Nat.add_zero]
    omega
  -- 一様 strict 証人: 尾部 `[m+1, Lng S - 1]` は境界値を厳格に上回る
  have hwit : ∀ x, m + 1 ≤ x → x ≤ Lng (seg (oper N n) A E) - 1 →
      entry (seg (oper N n) A E) 0 m < entry (seg (oper N n) A E) 0 x := by
    intro x hx1 hx2
    have hxS : x < Lng (seg (oper N n) A E) := by omega
    have hAxE : A + x ≤ E := by omega
    -- `A + x` のブロック分解（qx, sx）
    obtain ⟨qx, sx, hsxw, hxsplit⟩ :
        ∃ qx sx, sx < Lng N - 1 - parent N 1 (Lng N - 1) ∧
          A + x = parent N 1 (Lng N - 1) +
            qx * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx := by
      refine ⟨(A + x - parent N 1 (Lng N - 1)) /
          (Lng N - 1 - parent N 1 (Lng N - 1)),
        (A + x - parent N 1 (Lng N - 1)) %
          (Lng N - 1 - parent N 1 (Lng N - 1)),
        Nat.mod_lt _ hw0, ?_⟩
      have hdm := Nat.div_add_mod (A + x - parent N 1 (Lng N - 1))
        (Lng N - 1 - parent N 1 (Lng N - 1))
      have hcm : (Lng N - 1 - parent N 1 (Lng N - 1)) *
          ((A + x - parent N 1 (Lng N - 1)) /
            (Lng N - 1 - parent N 1 (Lng N - 1))) =
          ((A + x - parent N 1 (Lng N - 1)) /
            (Lng N - 1 - parent N 1 (Lng N - 1))) *
            (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.mul_comm _ _
      omega
    have hqxn : qx < n := by
      by_contra hcon
      have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          qx * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have heSx : entry (seg (oper N n) A E) 0 x =
        entry N 0 (parent N 1 (Lng N - 1) + sx) +
          qx * (entry N 0 (Lng N - 1) -
            entry N 0 (parent N 1 (Lng N - 1))) := by
      rw [entry_seg (oper N n) A E 0 x hxS, hxsplit]
      exact entry_oper_d1pos_zero_68 N n qx sx LNgt notzeroN hasparN i1zN
        hqxn hsxw
    -- 床ブロック: `qx ≥ q₀ + 1`
    have hqxge : q0 + 1 ≤ qx := by
      by_contra hcon
      have hmul : qx * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
          q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hfloor : entry N 0 (parent N 1 (Lng N - 1)) ≤
        entry N 0 (parent N 1 (Lng N - 1) + sx) :=
      oper_d1pos_period_row0_floor N sx hasparN i1zN j0lt (by omega)
    have hqd : (q0 + 1) * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) ≤
        qx * (entry N 0 (Lng N - 1) -
          entry N 0 (parent N 1 (Lng N - 1))) :=
      Nat.mul_le_mul_right _ hqxge
    rw [heSm, heSx]
    by_cases hdd : (q0 + 1) * (entry N 0 (Lng N - 1) -
        entry N 0 (parent N 1 (Lng N - 1))) =
        qx * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))
    · -- タイト床: `qx = q₀+1` → `sx > 0` → strict 周期床
      have hqxeq : q0 + 1 = qx :=
        Nat.eq_of_mul_eq_mul_right (by omega) hdd
      have hwq : qx * (Lng N - 1 - parent N 1 (Lng N - 1)) =
          (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) := by
        rw [hqxeq]
      have hsxpos : 0 < sx := by omega
      have hstrict : entry N 0 (parent N 1 (Lng N - 1)) <
          entry N 0 (parent N 1 (Lng N - 1) + sx) :=
        oper_d1pos_strict_period_floor N sx hasparN i1zN j0lt hsxpos
          (by omega)
      omega
    · omega
  have hanchor := anchor_lt_of_uniform_witness_bd (seg (oper N n) A E)
    (m + 1) m hST multiS (by omega) hwit
  omega

/-- Isabelle `oper_d1pos_period_boundary_cleMB` (pss_mechanized.thy:21135)。 -/
theorem oper_d1pos_period_boundary_cleMB
    (N M : PS) (n j0' j1' q0 s0 j0red j1red shamt : ℕ)
    (NT : TPS N) (_monoN : monoT N = true) (_std : STPS N)
    (LNgt : 1 < Lng N)
    (notzeroN : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hasparN : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1zN : idx1 N (Lng N - 1) = 1)
    (Neq : M = oper N n)
    (n1 : 1 ≤ n)
    (lt : j0' < j1')
    (jM : j1' < Lng M)
    (_bge : Lng N - 1 ≤ j1')
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (periodic : Lng N - 1 ≤ j0')
    (q0def : q0 = (j0' - parent N 1 (Lng N - 1)) /
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (s0def : s0 = (j0' - parent N 1 (Lng N - 1)) %
      (Lng N - 1 - parent N 1 (Lng N - 1)))
    (j0reddef : j0red = parent N 1 (Lng N - 1) + s0)
    (j1reddef : j1red = min (j0red + (j1' - j0')) (Lng N - 1))
    (shamtdef : shamt = q0 * (entry N 0 (Lng N - 1) -
      entry N 0 (parent N 1 (Lng N - 1))))
    (tnc : TrMax (seg N j0red j1red) ≤ j1red - 1 - j0red)
    (stop : nextR (seg (oper N n) j0' j1') 1 (TrMax (seg N j0red j1red))
      (TrMax (seg N j0red j1red) + 1) = false)
    (multiNp : 1 < (P (seg N (j0red + TrMax (seg N j0red j1red) + 1)
      j1red)).length)
    (multiS : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (notbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (boundary : ¬j1red < Lng N - 1) :
    (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 := by
  subst Neq
  -- ブロック幾何: `j0' = j₋₂ + q₀·w + s₀`、`q₀ < n`、`j₁ʳᵉᵈ = Lng N - 1`（cap active）
  have hLngM : Lng (oper N n) = parent N 1 (Lng N - 1) +
      n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
    length_oper_d1pos_68 N n LNgt notzeroN hasparN i1zN
  have hw0 : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  have hs0lt : s0 < Lng N - 1 - parent N 1 (Lng N - 1) := by
    rw [s0def]
    exact Nat.mod_lt _ hw0
  have hj0redlt : j0red < Lng N - 1 := by omega
  have hj0'eq : j0' = parent N 1 (Lng N - 1) +
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0 := by
    have hdm := Nat.div_add_mod (j0' - parent N 1 (Lng N - 1))
      (Lng N - 1 - parent N 1 (Lng N - 1))
    rw [← q0def, ← s0def] at hdm
    have hcm : (Lng N - 1 - parent N 1 (Lng N - 1)) * q0 =
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) := Nat.mul_comm _ _
    omega
  have hq0n : q0 < n := by
    by_contra hcon
    have hmul : n * (Lng N - 1 - parent N 1 (Lng N - 1)) ≤
        q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hj1redle : j1red ≤ Lng N - 1 := by omega
  have hj1redb : j1red = Lng N - 1 := by omega
  have hj0j1red : j0red < j1red := by omega
  have hj1redspan : j1red ≤ j0red + (j1' - j0') := by omega
  -- TrEq: `TrMax M' = TrMax Np`（一般 periodic Br 整列の第 1 成分）
  obtain ⟨hTrEq, _, _, _, _⟩ :=
    oper_d1pos_notbrle_Br_align N n q0 s0 j0red j1red j0' j1' shamt
      NT LNgt notzeroN hasparN i1zN j0lt n1 hq0n hj0redlt j0reddef hs0lt
      hj0'eq shamtdef hj1redle hj0j1red hj1redspan lt jM tnc stop notbrle
  -- 境界幾何: `AN < Lng N - 1`（さもなくば `Lng Snside ≤ 1` で multiNp と矛盾）
  have hLSn : Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) =
      j1red + 1 - (j0red + TrMax (seg N j0red j1red) + 1) :=
    length_seg _ _ _
  have hANlt : j0red + TrMax (seg N j0red j1red) + 1 < Lng N - 1 := by
    by_contra hcon
    have hone := P_short_len_bd
      (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) (by omega)
    omega
  have hsmW : (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) =
      q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) +
        (Lng N - 1 - parent N 1 (Lng N - 1)) := by
    rw [Nat.add_mul, Nat.one_mul]
  -- 証人配置: `A + m = j₋₂ + (q₀+1)·w`（ブロック境界）、`A + m ≤ j₁'`
  have hAm : (j0' + TrMax (seg (oper N n) j0' j1') + 1) +
      (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) =
      parent N 1 (Lng N - 1) +
        (q0 + 1) * (Lng N - 1 - parent N 1 (Lng N - 1)) := by omega
  have hAmE : (j0' + TrMax (seg (oper N n) j0' j1') + 1) +
      (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) ≤
      j1' := by omega
  exact period_boundary_cleMB_core_bd N n q0
    (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'
    (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
    LNgt notzeroN hasparN i1zN j0lt hq0n hAm hAmE jM multiS

/-- Prop discharge: `D1pos_oper_d1pos_period_boundary_cleMB`（dispatch 由来）。 -/
theorem D1pos_oper_d1pos_period_boundary_cleMB_holds :
    D1pos_oper_d1pos_period_boundary_cleMB := by
  intro N M n j0' j1' q0 s0 j0red j1red shamt NT monoN std LNgt notzeroN
    hasparN i1zN Neq n1 lt jM bge j0lt periodic q0def s0def j0reddef
    j1reddef shamtdef tnc stop multiNp multiS notbrle boundary
  exact oper_d1pos_period_boundary_cleMB N M n j0' j1' q0 s0 j0red j1red
    shamt NT monoN std LNgt notzeroN hasparN i1zN Neq n1 lt jM bge j0lt
    periodic q0def s0def j0reddef j1reddef shamtdef tnc stop multiNp multiS
    notbrle boundary

end PSS

#print axioms PSS.oper_d1pos_notbrle_LOW_take_eq_boundary
#print axioms PSS.D1pos_oper_d1pos_notbrle_LOW_take_eq_boundary_holds
#print axioms PSS.oper_d1pos_period_boundary_undercut
#print axioms PSS.oper_d1pos_period_boundary_mLmin
#print axioms PSS.oper_d1pos_period_boundary_cle
#print axioms PSS.oper_d1pos_period_boundary_cleMB
#print axioms PSS.D1pos_oper_d1pos_period_boundary_cleMB_holds
