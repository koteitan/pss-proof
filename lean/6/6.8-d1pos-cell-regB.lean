import «6».«6.8-d1pos-dispatch»
import «6».«6.8-d1pos-notbrle»
import «6».«6.8-d1pos-anchor-regA»
import «6».«6.8-d1pos-anchor-regB»

/-!
# §6.8 d1pos ¬brle regime-B cell（LOW take-eq、`j₋₂ ≤ j0'`）

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体、`i₁ = 1` の
  δ シフトタイル領域。regime B: 切片開始 `j0'` と枝源
  `A = j0' + TrMax M' + 1` がともにブロック 0 内 `[j₋₂, Lng N - 1)`、
  共通枝 anchor は境界 `c = c_N = m` に着地、`shamt = 0`）
- 訂正: なし（タイル係数は A8 適用後の `*_68` 資産に依拠）
- Isabelle (isabelle/pss_mechanized.thy):
  `oper_d1pos_notbrle_LOW_take_eq_regB` (18008)。WIRING は Isabelle と同一:
  (1) `oper_d1pos_notbrle_Br_align`（`q = 0`, `s₀ = j0' - j₋₂`, `shamt = 0`）
      で `TrMax M' = TrMax N_p` と両 reshape・非空性;
  (2) `oper_d1pos_anchor_coincide_period_unified`（`shamt = 0`、UNIFIED anchor
      入力 shiftEqB/boundEq0B/boundEq1B/lenPSeqB/cleMB/mleSB は仮定で供給）で
      `c = c_N` / `F8end` / `F9end`;
  (3) `oper_d1pos_branch_lowshift_regA`（`shamt = 0`、両窓とも `A` 始まり、
      LOW 窓は `Lng N - 2` 以下なので N-verbatim）で lowshift;
  (4) collapse ＋ tail junction は `d1posAlignment_of_anchor_data_68`
      （`6.8-standard-slice-Br-descending`）に一括委譲。
  Isabelle の `oper_d1pos_clt_regB` 呼び出しは仮定 `cleMB` と重複するため省略
  （主張は 1:1、結論の存在文は `d1posAlignment_68` の定義体と逐語一致）。
- 依存: «6».«6.8-d1pos-dispatch»（`D1pos_oper_d1pos_notbrle_LOW_take_eq_regB`）,
  «6».«6.8-d1pos-notbrle»（`oper_d1pos_notbrle_Br_align`）,
  «6».«6.8-d1pos-anchor-regA»（`oper_d1pos_branch_lowshift_regA`）,
  «6».«6.8-d1pos-anchor-regB»（`oper_d1pos_anchor_coincide_period_unified`）,
  «6».«6.8-standard-slice-Br-descending»（`d1posAlignment_of_anchor_data_68`、推移的）
- 状態: ✅ 証明済（sorry 0）

Prop discharge: `D1pos_oper_d1pos_notbrle_LOW_take_eq_regB_holds`。
-/

namespace PSS

/-! ## 小補助（このファイル私用、suffix `_cb`） -/

/-- `1 < (P S).length` なら `S` は空列でない（`P [] = [[]]` は長さ 1）。 -/
private theorem TPS_of_P_multi_cb (S : PS) (h : 1 < (P S).length) : TPS S := by
  intro hnil
  subst hnil
  simp [P, PAux] at h

/-! ## regime-B cell 本体 -/

/-- Isabelle `oper_d1pos_notbrle_LOW_take_eq_regB` (pss_mechanized.thy:18008)。
regime B（`j₋₂ ≤ j0'`、`j₋₂ ≤ A < Lng N - 1`）の LOW take-eq cell。
証人は `j₀^red = j0'`, `j₁^red = Lng N - 1`, `shamt = 0`。
結論 `d1posAlignment_68 N (seg M j0' j1')` は Isabelle の存在文と逐語一致。 -/
theorem oper_d1pos_notbrle_LOW_take_eq_regB
    (N M : PS) (n j0' j1' : ℕ)
    (NT : TPS N) (_monoN : monoT N = true) (LNgt : 1 < Lng N)
    (notzeroN : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hasparN : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (i1zN : idx1 N (Lng N - 1) = 1)
    (Neq : M = oper N n) (n1 : 1 ≤ n)
    (_M'T : TPS (seg M j0' j1'))
    (_le0M : leR M 0 j0' j1' = true)
    (lt : j0' < j1') (jM : j1' < Lng M)
    (bge : Lng N - 1 ≤ j1')
    (notbrle : ¬(TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1 ∨
      leR (seg M j0' j1') 0 (TrMax (seg M j0' j1') + 1)
        (Lng (seg M j0' j1') - 1) = true))
    (j0lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (_dpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (Areg : parent N 1 (Lng N - 1) ≤ j0' + TrMax (seg M j0' j1') + 1 ∧
      j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1)
    (j0pge : parent N 1 (Lng N - 1) ≤ j0')
    (multiM : 1 < (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length)
    (multiNp : 1 <
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length)
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
    (lenPSeqB : (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length =
      (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1))).length)
    (cleMB : (IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))).getD
        ((P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
    (mleSB : Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 ≤
      Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1) :
    d1posAlignment_68 N (seg M j0' j1') := by
  subst Neq
  obtain ⟨Ajm2, AltN⟩ := Areg
  -- (1) regime-B Br 整列（q = 0, s₀ = j0' - j₋₂, j₀^red = j0',
  --     j₁^red = Lng N - 1, shamt = 0）
  obtain ⟨hTrEq, hBrM, hBrN, _, _⟩ :=
    oper_d1pos_notbrle_Br_align N n 0 (j0' - parent N 1 (Lng N - 1))
      j0' (Lng N - 1) j0' j1' 0
      NT LNgt notzeroN hasparN i1zN j0lt n1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (le_refl _) (by omega) (by omega)
      lt jM tnc stop notbrle
  -- N 側 reshape を M 側 TrMax（`A` の綴り）で書き直す
  rw [← hTrEq] at hBrN
  -- 両枝領域の T_PS 性（multiplicity から）
  have hST : TPS (seg (oper N n)
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1') :=
    TPS_of_P_multi_cb _ multiM
  have hSnT : TPS (seg N
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1)) :=
    TPS_of_P_multi_cb _ multiNp
  -- (2) UNIFIED anchor 一致: `c = c_N` / `F8end` / `F9end`（shamt = 0）
  obtain ⟨ceq, hF8end, hF9end⟩ :=
    oper_d1pos_anchor_coincide_period_unified
      (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')
      (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1)) 0
      hST multiM hSnT multiNp mleSB cleMB lenPSeqB
      shiftEqB boundEq0B boundEq1B
  -- (3) lowshift: anchor 上界 `c ≤ Lng N - 1 - A` から LOW 窓は
  --     `Lng N - 2` 以下、N-verbatim 読み出し（shamt = 0）
  have hLngSn : Lng (seg N
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1)) =
      (Lng N - 1) + 1 - (j0' + TrMax (seg (oper N n) j0' j1') + 1) :=
    length_seg N _ _
  have hcle : (IdxSum (P (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'))).getD
        ((P (seg (oper N n)
          (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length - 1) 0 ≤
      Lng N - 1 - (j0' + TrMax (seg (oper N n) j0' j1') + 1) := by
    omega
  have hAbnd : j0' + TrMax (seg (oper N n) j0' j1') + 1 +
      ((IdxSum (P (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'))).getD
        ((P (seg (oper N n)
          (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length - 1) 0
        - 1) <
      Lng N - 1 := by
    omega
  have hlow := oper_d1pos_branch_lowshift_regA N n
    (j0' + TrMax (seg (oper N n) j0' j1') + 1)
    (j0' + TrMax (seg (oper N n) j0' j1') + 1)
    ((IdxSum (P (seg (oper N n)
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1'))).getD
      ((P (seg (oper N n)
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')).length - 1) 0)
    ((IdxSum (P (seg N
      (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1)))).getD
      ((P (seg N
        (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1))).length - 1)
      0)
    j1' (Lng N - 1)
    LNgt notzeroN hasparN i1zN j0lt n1 rfl ceq hAbnd
    (by omega) (by omega) (by omega) (by omega)
  -- (4) collapse ＋ tail junction（一括）: alignment record を組み立てる
  exact d1posAlignment_of_anchor_data_68 N (seg (oper N n) j0' j1')
    (seg (oper N n) (j0' + TrMax (seg (oper N n) j0' j1') + 1) j1')
    (seg N (j0' + TrMax (seg (oper N n) j0' j1') + 1) (Lng N - 1))
    j0' (Lng N - 1) 0
    (by omega) (le_refl _) (by simpa [leR] using le0Np)
    hBrM hBrN hST hSnT multiM multiNp
    (by exact hlow) (by exact hF8end) (by exact hF9end)

/-! ## Prop discharge -/

theorem D1pos_oper_d1pos_notbrle_LOW_take_eq_regB_holds :
    D1pos_oper_d1pos_notbrle_LOW_take_eq_regB := by
  intro N M n j0' j1' NT monoN LNgt notzeroN hasparN i1zN Neq n1 M'T le0M
    lt jM bge notbrle j0lt dpos Areg j0pge multiM multiNp le0Np tnc stop
    shiftEqB boundEq0B boundEq1B lenPSeqB cleMB mleSB
  exact oper_d1pos_notbrle_LOW_take_eq_regB N M n j0' j1' NT monoN LNgt
    notzeroN hasparN i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos Areg
    j0pge multiM multiNp le0Np tnc stop shiftEqB boundEq0B boundEq1B
    lenPSeqB cleMB mleSB

end PSS

#print axioms PSS.oper_d1pos_notbrle_LOW_take_eq_regB
#print axioms PSS.D1pos_oper_d1pos_notbrle_LOW_take_eq_regB_holds
