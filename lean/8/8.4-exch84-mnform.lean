import «8».«8.4-exch84-slicepkg»
import «8».«8.4-oper5-residual»
import «7».«7.2-scb-unique»
import «7».«7.3-Trans-preserves-zeroT»

/-!
# §8.4 交換パッケージの `mnform` 脚（`Mnform_condIIIIV` / `Mnform_condIV_admeq_sp`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- 対象: `slicepkg` 組み立て（«8».«8.4-exch84-slicepkg»）が露出する 2 本の `mnform` 脚:
  1. `Mnform_condIIIIV`（«8».«8.4-exch84-regsp»:263）= Isabelle `cpx_condIII_mnform`
     (isabelle/layerB/pss_wip.thy:98605)。ltJ 枝の `M[m]` 閉形式塔。
  2. `Mnform_condIV_admeq_sp`（«8».«8.4-exch84-slicepkg»）= Isabelle condIV admeq 隅
     `c4dx_condIV_k1` / `oi5_bodyOT` (isabelle/layerC/pss_scratch.thy:1520-1554)。
  両者の出力型は同一（`SlicepkgMnformOut_sp M`＝ `Mnform_condIIIIV` の ∃ 束、ltJ 抜き）
  であり、塔エンジンは ltJ も分岐条件も使わないので、**単一の組み立て** `mnform_of_residual`
  から両方を出す。

## 移植方針（house green-modulo、condV `exchV_M_tower_of_residual` の姉妹）

Isabelle の `cpx_condIII_mnform` は L6 タプルエンジン `cpx_various_scb_IIIIV` に依るが、
Lean は無条件塔エンジン `oper_props_5_unconditional`（«8».«8.4-oper5-residual»、
= Isabelle `m_8_4_oper_props_5`）を用いて condV と同型の `s84x_L`/`M[m]` joint 塔帰納で
`M[m]` 閉形式（`coreTower_e34 ins A0 (m-1)`）を組む。塔段は両枝一様で無条件に閉じる。

底の値・分解事実（挿入段 `ins`／`inner`／`k1`／底スライスの平坦形 `hM1`/`hL1`/`hLp`/`hPN`／
`ubeq`）を named Prop `MnformResidual` に束ねて入力とする（Isabelle の
`cpx_various_scb_IIIIV` ＋ 値補題群 ＋ `d4vx_ins` 構成に対応）。これらは condV の
`ExchVMTowerResidual` と同じ役割で、塔帰納より下の葉のみ。

対応（Isabelle 記号 → 本ファイル）:
`?e3 = entry M 1 (s84x_jm3 M)`（外頭）、`?e = entry M 1 (s84x_jm2 M)`（内頭、= `?ub`）、
`?ub = entry M 1 (Lng M-1) - 1`（挿入段の穴）、`?v1 = entry M 1 (Lng M-1)`、
`?A0 = bpHeadT (Trans (Pred (s84x_N M)))`（塔の底）、`?body = bpHeadT (Trans (s84x_N M))`。
condV との差は adm/非 adm の底段オフセットが無い（塔段数 = `n`／`n-1` の恒等）点のみ。

- 依存（すべてビルド済み・committed main db1f93c）: «8».«8.4-exch84-slicepkg»
  (`Mnform_condIIIIV`・`Mnform_condIV_admeq_sp`・`SlicepkgMnformOut_sp`・`coreTower_e34`・
  `s84x_jm2`/`s84x_jm3`/`s84x_N`・`bpHeadT`・`Dprin`/`BZero`/`flatBT`/`flatBP`/`scb_decomp`/
  `scb_kind1`)、«8».«8.4-oper5-residual» (`oper_props_5_unconditional`・`s84x_L`/`s84x_Lp`/
  `s84x_Np`・`s84c1_jm2_basic`)、«7».«7.2-scb-unique» (`scb_unique_decomp_unconditional`)、
  «7».«7.3-Trans-preserves-zeroT» (`Trans_preserves_zeroT`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  塔帰納・文字列代数は無条件に閉じ、残差 `MnformResidual`（`needs` 参照）のみ。
- Private helper suffix: `_mn`。
-/

namespace PSS

/-! ## 0. 文字列代数と塔の平坦形 -/

/-- `(replicate j b).flatten ++ b = (replicate (j+1) b).flatten`。 -/
private theorem flatten_replicate_snoc_mn {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate n xs) ++ xs = List.flatten (List.replicate (n + 1) xs) := by
  rw [List.replicate_add, List.flatten_append]
  simp

/-- `(replicate j b).flatten ++ b = b ++ (replicate j b).flatten`。 -/
private theorem flatten_replicate_comm_mn {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih => rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

/-- `A0` 種の塔 `coreTower_e34 ins A0 j` の平坦形（`d4vx_core_flat` の一般底）。 -/
private theorem coreTower_base_flat_mn {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) (A0 : BT) :
    ∀ j, flatBT (coreTower_e34 ins A0 j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub]))
        ++ flatBT A0 ++ List.flatten (List.replicate j b0)
  | 0 => by simp [coreTower_e34]
  | j + 1 => by
      show flatBT (ins (coreTower_e34 ins A0 j)) = _
      rw [hflat (coreTower_e34 ins A0 j), coreTower_base_flat_mn hflat A0 j,
        List.replicate_succ (a := s0 ++ [Sym.dsym ub]), List.flatten_cons,
        List.replicate_succ (a := b0), List.flatten_cons,
        ← flatten_replicate_comm_mn b0 j]
      simp [List.append_assoc]

/-! ## 1. 残差 named Prop（底の値・分解事実、`d4vx_ins` 構成、condV `ExchVMTowerResidual` 姉妹） -/

/-- **`mnform` 脚を閉じるための残差**。§8.4 の condIII/(IV) ホスト `M` について、挿入段
`ins`（`d4vx_ins` の flat 則）・`inner`（穴 `D_{v₁} 0`）・`k1`（`Trans M` の第 1 種分解、
穴 `D_{e₃} body`）・底スライスの平坦形（`M[1]`／`L₁`／`Trans (s84x_Lp M)`／
`Trans (Pred (s84x_Np M))`）・`ubeq` を要求する。

Isabelle の `cpx_various_scb_IIIIV`（L6 タプル）＋値補題群（`w84x_flat_head_Dpt` /
`vf2x_flat_head_bpHeadT` / `crx_c2_shape_*` 等）＋ `d4vx_ins` 構成に対応する葉のみで、
塔帰納段そのものは本ファイルが無条件に閉じる。`e₃ = entry M 1 (s84x_jm3 M)`、
`e = entry M 1 (s84x_jm2 M)`、`ub = entry M 1 (Lng M-1) - 1`、`v₁ = entry M 1 (Lng M-1)`、
`A0 = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`。 -/
def MnformResidual (M : PS) : Prop :=
  ∃ (ins : BT → BT) (s0 b0 s1 b1 : List Sym),
    -- `d4vx_ins_flat`: 挿入段の flat 則（穴 `dsym ub`、`b0` は全 `RP`）
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) ∧
    (∀ x ∈ b0, x = Sym.rp) ∧
    (∀ x ∈ b1, x = Sym.rp) ∧
    -- `inner`（出力）: `body` の穴 `D_{v₁} 0` の scb 分解
    scb_decomp (bpHeadT (Trans (s84x_N M))) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 ∧
    -- `k1`（出力）: `Trans M` の第 1 種分解（穴 `D_{e₃} body`）
    scb_kind1 (Trans M) s1
      (flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
                     (bpHeadT (Trans (s84x_N M))))) b1 ∧
    -- `ubeq`: `entry M 1 (s84x_jm2 M) = entry M 1 (Lng M-1) - 1`
    entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1 ∧
    -- 底スライス `M[1]`: `s1 ++ D_{e₃}(A0) ++ b1`（塔深さ 0）
    flatBT (Trans (oper M 1))
      = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: flatBT (bpHeadT (Trans (Pred (s84x_N M)))) ++ b1 ∧
    -- 底スライス `L₁`（塔深さ 1）
    flatBT (Trans (s84x_L M 1))
      = s1 ++ Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)])
          ++ [Sym.zero] ++ b0 ++ b1 ∧
    -- `L` 段: `Trans (s84x_Lp M)` の平坦形（穴 `D_e 0` を 1 段深くする）
    flatBT (Trans (s84x_Lp M))
      = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
          :: (s0 ++ [Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞), Sym.zero] ++ b0) ∧
    -- `M` 段: `Trans (Pred (s84x_Np M))` の平坦形（底 `A0`）
    flatBT (Trans (Pred (s84x_Np M)))
      = Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)
          :: flatBT (bpHeadT (Trans (Pred (s84x_N M))))

/-! ## 2. 組み立て（`oper_props_5_unconditional` 塔帰納、house pattern） -/

/-- **`mnform` 出力の drop-in**（house pattern）。残差 `MnformResidual M` から
`SlicepkgMnformOut_sp M`（= `Mnform_condIIIIV` の ∃ 束、= `Mnform_condIV_admeq_sp` の出力）を、
`oper_props_5_unconditional` engine ＋ `s84x_L`/`M[m]` joint 塔帰納で無条件に得る。 -/
theorem mnform_of_residual (M : PS)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hres : MnformResidual M) :
    SlicepkgMnformOut_sp M := by
  obtain ⟨ins, s0, b0, s1, b1, hflat, hb0rp, hb1rp, hinner, hk1, hub, hM1, hL1, hLp, hPN⟩ := hres
  -- 略記
  set e3 : ℕ := entry M 1 (s84x_jm3 M) with he3def
  set e : ℕ := entry M 1 (s84x_jm2 M) with hedef
  set A0 : BT := bpHeadT (Trans (Pred (s84x_N M))) with hA0def
  set X : List Sym := s0 ++ [Sym.dsym (e : ℕ∞)] with hXdef
  -- 底の平坦形 `flatBT (D_e 0)`、isPTB
  have hDe0 : flatBT (Dprin (e : ℕ∞) BZero) = [Sym.dsym (e : ℕ∞), Sym.zero] := rfl
  have isPTB_De0 : isPTB_str (flatBT (Dprin (e : ℕ∞) BZero)) :=
    ⟨.db (e : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  -- `b` 側は全 `RP`
  have hBkrp : ∀ m : ℕ, ∀ x ∈ (List.replicate m b0).flatten ++ b1, x = Sym.rp := by
    intro m x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp h
      rw [List.eq_of_mem_replicate hl] at hxl
      exact hb0rp x hxl
    · exact hb1rp x h
  -- `zeroT (Pred (s84x_Np M)) = false`（底 `M` 段の guard）
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hNpLen : 1 < Lng (s84x_Np M) := by
    show 1 < Lng (seg M (s84x_jm2 M) (Lng M - 1)); rw [length_seg]; omega
  have hPredNpLen : 0 < Lng (Pred (s84x_Np M)) := by
    rw [length_Pred _ hNpLen]; omega
  have nzPredNp : ¬ (zeroT (Pred (s84x_Np M)) = true) := by
    have hTPS : TPS (Pred (s84x_Np M)) := List.ne_nil_of_length_pos hPredNpLen
    intro h
    have hz : Trans (Pred (s84x_Np M)) = BZero :=
      (Trans_preserves_zeroT (Pred (s84x_Np M)) hTPS).mp h
    have hflatz : flatBT (Trans (Pred (s84x_Np M))) = [Sym.zero] := by rw [hz]; rfl
    rw [hPN] at hflatz
    simp at hflatz
  -- 底 `L` 段 / `M` 段の平坦形（略記に沿った形）
  have hfLp : flatBT (Trans (s84x_Lp M))
      = Sym.dsym (e : ℕ∞) :: (s0 ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ b0) := hLp
  have hfPN : flatBT (Trans (Pred (s84x_Np M)))
      = Sym.dsym (e : ℕ∞) :: flatBT A0 := hPN
  have hM0 : flatBT (Trans (oper M 1)) = s1 ++ Sym.dsym (e3 : ℕ∞) :: flatBT A0 ++ b1 := hM1
  -- 文字列 combine 補題（condV `snocX'`/`consB'`）
  have snocX' : ∀ (m : ℕ) (rest : List Sym),
      (List.replicate m X).flatten ++ (s0 ++ (Sym.dsym (e : ℕ∞) :: rest))
        = (List.replicate (m + 1) X).flatten ++ rest := by
    intro m rest
    have h1 : s0 ++ (Sym.dsym (e : ℕ∞) :: rest) = X ++ rest := by rw [hXdef]; simp
    rw [h1, ← List.append_assoc, flatten_replicate_snoc_mn]
  have consB' : ∀ (m : ℕ) (rest : List Sym),
      b0 ++ ((List.replicate m b0).flatten ++ rest)
        = (List.replicate (m + 1) b0).flatten ++ rest := by
    intro m rest
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
  -- pure 文字列代数（`L` step / `M` step / flat split）
  have Lstr : ∀ q : ℕ,
      (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate q X).flatten ++ s0)
        ++ (Sym.dsym (e : ℕ∞) :: (s0 ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ b0))
        ++ ((List.replicate (q + 1) b0).flatten ++ b1)
      = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (q + 2) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 2) b0).flatten ++ b1 := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX', snocX', consB']
  have Mstr : ∀ q : ℕ,
      (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate q X).flatten ++ s0)
        ++ (Sym.dsym (e : ℕ∞) :: flatBT A0)
        ++ ((List.replicate (q + 1) b0).flatten ++ b1)
      = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (q + 1) X).flatten
          ++ flatBT A0 ++ (List.replicate (q + 1) b0).flatten ++ b1 := by
    intro q
    simp only [List.append_assoc, List.cons_append]
    rw [snocX']
  have splitL : ∀ q : ℕ,
      (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate q X).flatten ++ s0)
        ++ [Sym.dsym (e : ℕ∞), Sym.zero]
        ++ ((List.replicate (q + 1) b0).flatten ++ b1)
      = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (q + 1) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 1) b0).flatten ++ b1 := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX']
  -- engine（`oper_props_5_unconditional`）を各段で呼ぶ
  have engine : ∀ n, 1 < n → ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_L M (n - 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2
        ∧ scb_decomp (Trans (s84x_L M n)) sb.1 (flatBT (Trans (s84x_Lp M))) sb.2
        ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
             scb_decomp (Trans (oper M n)) sb.1
               (flatBT (Trans (Pred (s84x_Np M)))) sb.2) := by
    intro n hn
    exact oper_props_5_unconditional M n hST hmono hp hj1 hn
  -- joint 帰納（塔段数 = `k+1`／`k`、両枝一様）
  have main : ∀ k,
      flatBT (Trans (s84x_L M (k + 1)))
        = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (k + 1) X).flatten
            ++ [Sym.zero] ++ (List.replicate (k + 1) b0).flatten ++ b1
      ∧ flatBT (Trans (oper M (k + 1)))
        = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate k X).flatten
            ++ flatBT A0 ++ (List.replicate k b0).flatten ++ b1 := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · simpa using hL1
        · simpa using hM0
    | succ k ih =>
        obtain ⟨ihL, _ihM⟩ := ih
        -- L(k+1) を `(Sk, Bk)` の scb 分解へ（穴 `D_e 0`）
        have flatk : flatBT (Trans (s84x_L M (k + 1)))
            = (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate k X).flatten ++ s0)
              ++ flatBT (Dprin (e : ℕ∞) BZero)
              ++ ((List.replicate (k + 1) b0).flatten ++ b1) := by
          rw [ihL, hDe0]; exact (splitL k).symm
        have wk : scb_decomp (Trans (s84x_L M (k + 1)))
            (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate k X).flatten ++ s0)
            (flatBT (Dprin (e : ℕ∞) BZero))
            ((List.replicate (k + 1) b0).flatten ++ b1) :=
          ⟨flatk, fun _ => isPTB_De0, hBkrp (k + 1)⟩
        -- engine at `n = k+2`
        obtain ⟨sb, ⟨hP1, hP2, hP3⟩, _hU⟩ := engine (k + 2) (by omega)
        have hP1' : scb_decomp (Trans (s84x_L M (k + 1))) sb.1
            (flatBT (Dprin (e : ℕ∞) BZero)) sb.2 := hP1
        obtain ⟨hpinS, hpinB⟩ := scb_unique_decomp_unconditional
          (Trans (s84x_L M (k + 1))) sb.1
          (s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate k X).flatten ++ s0)
          (flatBT (Dprin (e : ℕ∞) BZero))
          sb.2 ((List.replicate (k + 1) b0).flatten ++ b1) hP1' wk
        rw [hpinS, hpinB] at hP2
        have hM2 := hP3 nzPredNp
        rw [hpinS, hpinB] at hM2
        refine ⟨?_, ?_⟩
        · show flatBT (Trans (s84x_L M (k + 2)))
              = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (k + 2) X).flatten
                  ++ [Sym.zero] ++ (List.replicate (k + 2) b0).flatten ++ b1
          rw [hP2.1, hfLp]
          exact Lstr k
        · show flatBT (Trans (oper M (k + 2)))
              = s1 ++ Sym.dsym (e3 : ℕ∞) :: (List.replicate (k + 1) X).flatten
                  ++ flatBT A0 ++ (List.replicate (k + 1) b0).flatten ++ b1
          rw [hM2.1, hfPN]
          exact Mstr k
  -- `MNall`: `M[m]` 閉形式塔（`coreTower_e34 ins A0 (m-1)`）へ折り畳む
  have hXub : X = s0 ++ [Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞)] := by
    rw [hXdef, hub]
  have MNall : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db (e3 : ℕ∞)
          (coreTower_e34 ins A0 (m - 1))) ++ b1 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hM := (main k).2
    rw [hM]
    have htower : flatBT (coreTower_e34 ins A0 k)
        = (List.replicate k X).flatten ++ flatBT A0 ++ (List.replicate k b0).flatten := by
      rw [coreTower_base_flat_mn hflat A0 k, hXub]
    simp only [flatBP, htower, Nat.add_sub_cancel]
    simp [List.append_assoc]
  -- 出力 ∃ 束（`SlicepkgMnformOut_sp M`）を組む
  exact ⟨ins, s0, b0, s1, b1, hflat, hb0rp, hb1rp, hinner, hk1, MNall⟩

/-! ## 3. 2 本の `mnform` 脚（house pattern） -/

/-- `Mnform_condIIIIV`（«8».«8.4-exch84-regsp», Isabelle `cpx_condIII_mnform`）の drop-in。
ltJ 枝。共通仮定下の残差 `MnformResidual` から `mnform_of_residual` で組む。 -/
theorem Mnform_condIIIIV_mn
    (hres : ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) → MnformResidual M) :
    Mnform_condIIIIV := by
  intro M hST hmono hp hj1 hcond _hltJ
  exact mnform_of_residual M hST hmono hp hj1 (hres M hST hmono hp hj1 hcond)

/-- `Mnform_condIV_admeq_sp`（«8».«8.4-exch84-slicepkg», Isabelle condIV admeq 隅
`c4dx_condIV_k1` / `oi5_bodyOT`）の drop-in。ltJ 枝の `Mnform_condIIIIV` と同一出力型なので
同じ組み立て `mnform_of_residual` から出る。 -/
theorem Mnform_condIV_admeq_sp_mn
    (hres : ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
      1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) → MnformResidual M) :
    Mnform_condIV_admeq_sp := by
  intro M hST hmono hp hj1 hIV _hadmeq
  exact mnform_of_residual M hST hmono hp hj1 (hres M hST hmono hp hj1 (Or.inr hIV))

#print axioms mnform_of_residual
#print axioms Mnform_condIIIIV_mn
#print axioms Mnform_condIV_admeq_sp_mn

end PSS
