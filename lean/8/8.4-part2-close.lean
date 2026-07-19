import «8».«8.4-lp-readout-close»
import «8».«8.4-np-c2decomp»

/-!
# §8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (2) の無条件閉包

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
- 訂正: A33 は撤回済み（`corrections-old.md`）。訂正後の part (2) は原文どおり。
- Isabelle: `p_8_4_oper_basic` (`isabelle/pss_paper.thy:2017`)；機械証明は
  `y3l_p_8_4_oper_basic_part2` / `y3m_p_8_4_oper_basic_part2_full`
  (`isabelle/layerC/pss_scratch.thy:18777,19105`)。底の `base5` は
  `isabelle/layerB/pss_wip.thy:60231`。
- 依存: «8».«8.4-lp-readout-close», «8».«8.4-np-c2decomp»。
- 状態: ✅ 証明済（sorry 0）。

## 証明の配線

既存の無条件 `sliceExtTupleResidual_holds_nc2` と corner readout から
`mnformResidual_dispatch_md` を閉じる。得られる canonical な `MnformResidual M` は、同じ
証人 `(ins,s0,b0,s1,b1)` について `ubeq`、`L₁`、`Lp` の底読み出しと kind-1 scb 分解を
同時に持つ。この証人を一度だけ取り出し、

1. `oper_rule_basic_part5` で `L₁` から `L_n` まで scb 差し替え帰納を回し、
2. `scb_fseq_kind1` で `operB (Trans M) (numBT (n-1))` を同じ文字列へ展開し、
3. `l6_op1pow_bridge_br` で記事の反復 `oper 1` 表記へ戻す。

これにより producer 証人を再び全称量化する中間残差を経由せず、canonical 証人上で
Isabelle の `base5`/`cL`/`fOp'` を直接合成する。

Private helper suffix: `_p2c`。
-/

namespace PSS

/-! ## 1. 全域の canonical `MnformResidual` -/

/-- 既存の全域 dispatch を、すでに無条件化された全入力で閉じる。 -/
private theorem mnformResidual_uncond_p2c (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    MnformResidual M := by
  let hread : CornerCoreReadouts_cc :=
    cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv
  let hcorner : MnformCornerResidual_md :=
    mnformCornerResidual_holds_ce
      (mnformCornerCoreResidual_holds_cc transC2HoleDecomp_holds_sr hread
        cornerC2Kind1_holds_cd)
  exact mnformResidual_dispatch_md
    nestScbD4aTransport_dk
    transC2HoleDecomp_holds_sr
    (mnformBottomExtResidual_holds sliceExtTupleResidual_holds_nc2)
    hcorner M hST hmono hp hj1 hcond

/-! ## 2. L 切片塔の scb 差し替え帰納 -/

private theorem flatten_replicate_comm_p2c {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

private theorem flatten_replicate_snoc_p2c {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = (List.replicate (j + 1) b).flatten := by
  rw [flatten_replicate_comm_p2c, List.replicate_succ, List.flatten_cons]

/-- `L₁` と `Lp` の canonical 底読み出しから全 `L_{k+1}` の平坦形を得る。
`«8».«8.4-l6-slice-close»` の塔帰納を、canonical witness に特化したもの。 -/
private theorem l6_tower_from_mnform_p2c
    (M : PS) (e3 ub : ℕ∞) (s0 b0 s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (hubeq : (entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
    (hbase : flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) ++ b1)
    (hlpv : flatBT (Trans (s84x_Lp M))
        = Sym.dsym ub :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0)) :
    ∀ k, flatBT (Trans (s84x_L M (k + 1)))
      = s1 ++ Sym.dsym e3 :: (List.replicate (k + 1) (s0 ++ [Sym.dsym ub])).flatten
          ++ [Sym.zero] ++ (List.replicate (k + 1) b0).flatten ++ b1 := by
  have hDe0 : flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)
      = [Sym.dsym ub, Sym.zero] := by
    show Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT BZero = _
    rw [hubeq]
    rfl
  have isPTB_De0 :
      isPTB_str (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) :=
    ⟨.db (entry M 1 (s84x_jm2 M) : ℕ∞) BZero,
      by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  have hBkrp : ∀ m : ℕ, ∀ x ∈ (List.replicate m b0).flatten ++ b1, x = Sym.rp := by
    intro m x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp h
      rw [List.eq_of_mem_replicate hl] at hxl
      exact hb0 x hxl
    · exact hb1 x h
  set X := s0 ++ [Sym.dsym ub] with hXdef
  have snocX' : ∀ (m : ℕ) (rest : List Sym),
      (List.replicate m X).flatten ++ (s0 ++ (Sym.dsym ub :: rest))
        = (List.replicate (m + 1) X).flatten ++ rest := by
    intro m rest
    have h1 : s0 ++ (Sym.dsym ub :: rest) = X ++ rest := by rw [hXdef]; simp
    rw [h1, ← List.append_assoc, flatten_replicate_snoc_p2c]
  have consB' : ∀ (m : ℕ) (rest : List Sym),
      b0 ++ ((List.replicate m b0).flatten ++ rest)
        = (List.replicate (m + 1) b0).flatten ++ rest := by
    intro m rest
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
  have Lstr : ∀ q : ℕ,
      (s1 ++ Sym.dsym e3 :: (List.replicate q X).flatten ++ s0)
        ++ (Sym.dsym ub :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0))
        ++ ((List.replicate (q + 1) b0).flatten ++ b1)
      = s1 ++ Sym.dsym e3 :: (List.replicate (q + 2) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 2) b0).flatten ++ b1 := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX', snocX', consB']
  have splitL : ∀ q : ℕ,
      (s1 ++ Sym.dsym e3 :: (List.replicate q X).flatten ++ s0)
        ++ [Sym.dsym ub, Sym.zero]
        ++ ((List.replicate (q + 1) b0).flatten ++ b1)
      = s1 ++ Sym.dsym e3 :: (List.replicate (q + 1) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 1) b0).flatten ++ b1 := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX']
  intro k
  induction k with
  | zero =>
      show flatBT (Trans (s84x_L M 1))
          = s1 ++ Sym.dsym e3 :: (List.replicate 1 X).flatten ++ [Sym.zero]
              ++ (List.replicate 1 b0).flatten ++ b1
      rw [hbase]
      simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil, hXdef]
      simp [List.append_assoc]
  | succ k ih =>
      have flatk : flatBT (Trans (s84x_L M (k + 1)))
          = (s1 ++ Sym.dsym e3 :: (List.replicate k X).flatten ++ s0)
            ++ flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)
            ++ ((List.replicate (k + 1) b0).flatten ++ b1) := by
        rw [ih, hDe0]
        exact (splitL k).symm
      have wk : scb_decomp (Trans (s84x_L M (k + 1)))
          (s1 ++ Sym.dsym e3 :: (List.replicate k X).flatten ++ s0)
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))
          ((List.replicate (k + 1) b0).flatten ++ b1) :=
        ⟨flatk, fun _ => isPTB_De0, hBkrp (k + 1)⟩
      obtain ⟨sb, ⟨hP1, hP2, _hP3⟩, _hU⟩ :=
        oper_rule_basic_part5 M (k + 2) hST hmono hp hj1 (by omega)
      have hP1' : scb_decomp (Trans (s84x_L M (k + 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2 := hP1
      obtain ⟨hpinS, hpinB⟩ := scb_unique_decomp_unconditional
        (Trans (s84x_L M (k + 1))) sb.1
        (s1 ++ Sym.dsym e3 :: (List.replicate k X).flatten ++ s0)
        (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))
        sb.2 ((List.replicate (k + 1) b0).flatten ++ b1) hP1' wk
      rw [hpinS, hpinB] at hP2
      show flatBT (Trans (s84x_L M (k + 2)))
          = s1 ++ Sym.dsym e3 :: (List.replicate (k + 2) X).flatten
              ++ [Sym.zero] ++ (List.replicate (k + 2) b0).flatten ++ b1
      rw [hP2.1, hlpv]
      exact Lstr k

/-! ## 3. 原文 part (2) の無条件定理 -/

/-- **§8.4 補題 part (2)、無条件形**。

`Trans(M)[n-1] = Trans(M[n+1][1]^{j₁-1-j₋₂})` を、訂正後の原文どおり述べる。 -/
theorem oper_basic_part2_uncond
    (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    operB (Trans M) (numBT (n - 1)) =
      Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)]
        (oper M (n + 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [l6_op1pow_bridge_br M (k + 1) hST hp hj1 (by omega)]
  simp only [Nat.add_sub_cancel]
  apply flatBT_injective
  obtain ⟨ins, s0, b0, s1, b1, hflat, hb0, hb1, hinner, hk1,
    hub, _hM1, hL1, hLp, _hPN⟩ :=
    mnformResidual_uncond_p2c M hST hmono hp hj1 hcond
  have hbase : flatBT (Trans (s84x_L M 1))
      = s1 ++ Sym.dsym (entry M 1 (s84x_jm3 M) : ℕ∞) ::
          (s0 ++ [Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞), Sym.zero] ++ b0) ++ b1 := by
    simpa [List.append_assoc] using hL1
  have hLtower := l6_tower_from_mnform_p2c M
    (entry M 1 (s84x_jm3 M) : ℕ∞) (entry M 1 (s84x_jm2 M) : ℕ∞)
    s0 b0 s1 b1 hST hmono hp hj1 hb0 hb1 rfl hbase hLp k
  have hTB : Trans M ∈ T_B := Trans_mem_T_B M (STPS_RTPS M hST)
  have hinner' : scb_decomp
      (Dprin (entry M 1 (s84x_jm3 M) : ℕ∞) (bpHeadT (Trans (s84x_N M))))
      (Sym.dsym (entry M 1 (s84x_jm3 M) : ℕ∞) :: s0)
      (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) b0 := by
    refine ⟨?_, ?_, hinner.2.2⟩
    · rw [show flatBT
          (Dprin (entry M 1 (s84x_jm3 M) : ℕ∞) (bpHeadT (Trans (s84x_N M))))
            = Sym.dsym (entry M 1 (s84x_jm3 M) : ℕ∞) ::
                flatBT (bpHeadT (Trans (s84x_N M))) by rfl,
        hinner.1]
      simp
    · intro _
      exact ⟨.db (entry M 1 (Lng M - 1) : ℕ∞) BZero,
        by simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
  have hOper := (scb_fseq_kind1 (n := k) hTB hk1 hinner').2
  rw [← hub] at hOper
  have hOper' : flatBT (operB (Trans M) (numBT k))
      = s1 ++ Sym.dsym (entry M 1 (s84x_jm3 M) : ℕ∞) ::
          (List.replicate (k + 1)
            (s0 ++ [Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞)])).flatten
          ++ [Sym.zero] ++ (List.replicate (k + 1) b0).flatten ++ b1 := by
    simpa [List.append_assoc] using hOper
  exact hOper'.trans hLtower.symm

#print axioms oper_basic_part2_uncond

end PSS
