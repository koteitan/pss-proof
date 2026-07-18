import «8».«8.4-rightmost-replace-close»
import «7».«7.2-add-scb»
import «7».«7.2-scb-compose»

/-!
# §8.4 補題（右端置き換えと `Trans`）存在部 `Rightmost84ReplaceExists` の攻略

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は **DEFERRED**。
- 攻略対象: `«8».«8.4-rightmost-replace-close»` の
  `Rightmost84ReplaceExists`（:43）。一意部は同ファイルの
  `rightmost84ReplaceCorrected_of_exists` で無条件に閉じており、残るのは
  「`Trans(N')` を中心 `D_{M₁,j₁} 0`、`Trans(L')` を中心 `D_{M₁,j₋₂} 0` で **同一**
  scb 文脈 `(s,b)` で分解する」純存在 1 本。
  ここで `N' = s84x_Np M = seg M j₋₂ j₁`、`L' = rrLp M = s84x_Lp M
  = seg M j₋₂ (Lng M − 2) ++ [(M_{0,j₁}, M_{1,j₋₂})]`。
  `N'` と `L'` は **最終列の行1成分だけ**（`β = M_{1,j₁}` vs `γ = M_{1,j₋₂}`）で
  異なり、前置 `P = seg M j₋₂ (Lng M − 2)`（＝ `Pred N' = Pred L'`）と最終列の行0
  成分 `a = M_{0,j₁}` を共有する。

- 本ファイルの寄与（すべて無条件・GREEN）:
  * **自己相似リードバック橋** `rr84_shared_of_readback`: `Trans(N')` と `Trans(L')`
    がともに外側 `Dprin V (addBT T2 ·)` で包まれ **最内の principal だけが `D_β 0`
    vs `D_γ 0` で異なる**とき、`add_scb_marked` / `add_scb_replace_last` /
    `scb_compose_dprin`（すべて §7.2）で共有文脈 `(dsym V :: s0, b0)` を機械的に
    構成する。scb 代数のみに依存し、条件 (III)/(V)/(VI) の閉形式
    （`exchV_Np_adm` が `transC2_condV_eq` から読む `D_e(t₂ +_B D_β 0)` 形）で
    `Rightmost84ReplaceExists` の存在部へ 1:1 で還元する再利用可能な部品。
  * 非空虚性 `rightmost84Replace_nonvacuous_re` を A30 host で機械確認。

- **ブロッカー（未解決の核）**: 橋 `rr84_shared_of_readback` の 2 前提
  `hNp : Trans(N') = D_V (T2 +_B D_β 0)` と `hLp : Trans(L') = D_V (T2 +_B D_γ 0)`。
  `Trans(N')`（`N'` は `mono_ancestor_slice` で `monoT`）は `Mark_Trans_repr` ＋
  `m_7_3_Mark_rightmost2` で読めるが、`Trans(L')` は **`L'` が非単項**（A30 host で
  `L' = (0,0)(1,1)(2,2)(2,0)`、行1 = 0,1,2,0 が非単調）ゆえ `Trans` の **multi 分岐**
  （`P M` による primary-block 分解）に落ちる。この非単項値
  `Trans (s84x_Lp M)` は Lean 側で **どこでも `needs` 入力**（§8.5 の `nf2x_Lpv`
  `exchV_Lp_of_Np` は `hrr = Rightmost84ReplaceCorrected` から逆に導く循環、
  `nf2x_L1v` `exchV_L1_decomp_of_c2` は `c₂(L₁)` 値を仮定入力に取る）であり、
  独立計算は存在しない。Isabelle 側も本補題ごと DEFERRED。したがって
  `Rightmost84ReplaceExists` は **真に atomic** で、既存機構では discharge も
  それより真かつ一般な named-Prop への還元もできない（`Dprin V (addBT T2 ·)` の閉形式
  は条件 (IV) の入れ子 `D_e(t₃ +_B D_{M₁,j'}(t₄ +_B D_β 0))` で崩れるため、
  T2 形の大域残差は偽になり不可）。

- 依存（すべてビルド済み・committed）: «8».«8.4-rightmost-replace-close»
  （`Rightmost84ReplaceExists`/`rrLp`/`s84x_Np`/`s84x_jm2`/`hostM30_rr`/
  `rr84_corrected_holds_rr`）、«7».«7.2-add-scb»（`add_scb_marked`/
  `add_scb_replace_last`）、«7».«7.2-scb-compose»（`scb_compose_dprin`）。
- 数値検証: `python/trans_model.py`（`scb_decomps`, A30 host で `share_ok=280/280`）。
- ツリー項目: 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係）(§8.4)。
- 状態: 🤖 GREEN（sorry 0）。橋＋非空虚性は無条件。存在部本体は非単項
  `Trans(s84x_Lp M)` 値ブロッカーで blocked（下流 §8.5 と共通の atomic 残差）。
- Private suffix: `_re`。
-/

namespace PSS

/-! ## 自己相似リードバック橋（無条件・scb 代数のみ）

`Trans(N')` と `Trans(L')` の閉形式が外側 `Dprin V (addBT T2 ·)` を共有し最内 principal
だけ `D_β 0` / `D_γ 0` で異なるとき、共有 scb 文脈を機械的に返す。`8.5-exchV-values-close`
の `hwit` ＋ `htarget` 構成（`exchV_Lp_of_Np`）と同型で、そこでは `hrr` から `(s,b)` を
得ていたのを、ここでは 2 つの閉形式から **直接** 構成する。 -/

private theorem dprin_mem_T_B_re (v : ℕ∞) (hv : v ≠ ⊤) :
    Dprin v BZero ∈ T_B := by
  have hbne : (v != ⊤) = true := bne_iff_ne.mpr hv
  simp [T_B, Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP, hbne]

private theorem dprin_isPTB_str_re (v : ℕ∞) (hv : v ≠ ⊤) :
    isPTB_str (flatBT (Dprin v BZero)) := by
  have hbne : (v != ⊤) = true := bne_iff_ne.mpr hv
  refine ⟨.db v BZero, ?_, ?_⟩
  · simp [dfree_BP, BZero, dfree_BT, dfree_BPList, hbne]
  · simp [Dprin, flatBT]

/-- **自己相似リードバック橋**。`Trans(N')` と `Trans(L')` の閉形式が外側
`Dprin V (addBT T2 ·)` を共有し、最内 principal だけ `D_β 0` / `D_γ 0` で異なるなら、
`Rightmost84ReplaceExists` の存在部の共有 scb 文脈 `(dsym V :: s0, b0)` が構成できる。
`β = M_{1,j₁}`, `γ = M_{1,j₋₂}`。前提の `V ≠ ⊤` / `β ≠ ⊤` / `γ ≠ ⊤` は
`entry` が自然数値ゆえ ℕ∞ への coercion で自動成立する。 -/
theorem rr84_shared_of_readback (M : PS) (V : ℕ∞) (T2 : BT)
    (hT2 : T2 ∈ T_B)
    (hNp : Trans (s84x_Np M)
        = Dprin V (addBT T2 (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)))
    (hLp : Trans (rrLp M)
        = Dprin V (addBT T2 (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))) :
    ∃ sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np M)) sb.1
          (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp M)) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2 := by
  set β : ℕ∞ := (entry M 1 (Lng M - 1) : ℕ∞) with hβ
  set γ : ℕ∞ := (entry M 1 (s84x_jm2 M) : ℕ∞) with hγ
  have hβne : β ≠ ⊤ := by simp [hβ]
  have hγne : γ ≠ ⊤ := by simp [hγ]
  -- 中心 principal の T_B 所属と単項性
  have hdβTB : Dprin β BZero ∈ T_B := dprin_mem_T_B_re β hβne
  have hdγTB : Dprin γ BZero ∈ T_B := dprin_mem_T_B_re γ hγne
  have hdβP : ∃ p, Dprin β BZero = BT.trm [p] := ⟨.db β BZero, rfl⟩
  have hdγP : ∃ p, Dprin γ BZero = BT.trm [p] := ⟨.db γ BZero, rfl⟩
  have hdβstr : isPTB_str (flatBT (Dprin β BZero)) := dprin_isPTB_str_re β hβne
  have hdγstr : isPTB_str (flatBT (Dprin γ BZero)) := dprin_isPTB_str_re γ hγne
  -- `addBT T2 (D_β 0)` の scb 分解（中心 `D_β 0`、共有位置 `(s0,b0)`）
  obtain ⟨s0, b0, hd0⟩ := add_scb_marked T2 (Dprin β BZero) hT2 hdβTB hdβP
  -- part 1: 外側 `Dprin V` を被せて `Trans(N')`
  have hpart1 : scb_decomp (Trans (s84x_Np M)) (Sym.dsym V :: s0)
      (flatBT (Dprin β BZero)) b0 := by
    rw [hNp]
    exact scb_compose_dprin V (addBT T2 (Dprin β BZero)) s0
      (flatBT (Dprin β BZero)) b0 hd0 hdβstr
  -- 最内 principal を `D_γ 0` に置換（同じ `(s0,b0)`）
  have hd0' : scb_decomp (addBT T2 (Dprin γ BZero)) s0 (flatBT (Dprin γ BZero)) b0 :=
    add_scb_replace_last T2 (Dprin β BZero) (Dprin γ BZero) s0 b0
      hT2 hdβTB hdβP hdγTB hdγP hd0
  -- part 2: 外側 `Dprin V` を被せて `Trans(L')`
  have hpart2 : scb_decomp (Trans (rrLp M)) (Sym.dsym V :: s0)
      (flatBT (Dprin γ BZero)) b0 := by
    rw [hLp]
    exact scb_compose_dprin V (addBT T2 (Dprin γ BZero)) s0
      (flatBT (Dprin γ BZero)) b0 hd0' hdγstr
  exact ⟨(Sym.dsym V :: s0, b0), hpart1, hpart2⟩

/-! ## 非空虚性（A30 host での機械確認）

`Rightmost84ReplaceExists` の存在部が空虚でないことを、`«8».«8.4-rightmost-replace-Trans»`
の共有手術対 `(s_rr, b_rr)`（A30 host `hostM30_rr = (0,0)(1,1)(2,2)(2,1)`）で確認する。
`s84x_Np hostM30_rr = hostM30_rr`、`rrLp = s84x_Lp` なので、この witness はそのまま
存在部の証拠になる。 -/
theorem rightmost84Replace_nonvacuous_re :
    ∃ sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero)) sb.2 :=
  rr84_corrected_holds_rr

#print axioms rr84_shared_of_readback
#print axioms rightmost84Replace_nonvacuous_re

end PSS
