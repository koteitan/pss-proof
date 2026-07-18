import «8».«8.4-c2hole-engine»
import «8».«8.4-rightmost-replace-Trans»

/-!
# §8.4 `c₂`-hole 切片リードバック transport `C2HoleSliceTransport_ch` — **反証**

- 目標（ミッション）: `«8».«8.4-c2hole-engine»` の残差 `C2HoleSliceTransport_ch`
  （手術による切片リードバック transport、`Trans (s84x_Np M)` / `Trans (rrLp M)` が
  `c2hole_ch` の scb 分解を共有 `(s,b)` のまま継承する、という主張）を discharge し、
  `rightmost84ReplaceCorrected_of_transport_ch` 経由で `rm84Readback` フィールドを
  閉じること。

- **結論: `C2HoleSliceTransport_ch` は偽（本ファイルで機械証明）。この route では
  `rm84Readback` を閉じられない。**

  ## 反証の核（条件(III)で余分な先頭 `D` が付く）

  transport は「`c2hole_ch M a` の scb 文脈 `(s,b)`（中心 `D_a 0`）がそのまま
  `Trans (s84x_Np M)`（中心 `D_β 0`）/ `Trans (rrLp M)`（中心 `D_γ 0`）を分解する」
  と主張する（`β = M_{1,Lng M−1}`, `γ = M_{1,s84x_jm2 M}`）。エンジンの `c2hole_ch M a`
  は条件(I)/(III)/(V) 枝で `transC2Core M (transV M) (transT2 M)` の穴形、すなわち
  `transC2 M = c2hole_ch M β`（`c2hole_at_j1_ch`）である。

  ところが **条件(III) の標準形 `M`**（行1の親 `s84x_jm2 M = parent M 1 (Lng M−1)`
  と 行0の親 `transJ0 M = parent M 0 (Lng M−1)` が食い違う）では、実際の
  `Trans (s84x_Np M)` は
  `Dprin (entry M 1 (s84x_jm2 M)) (transC2 M)` — すなわち `transC2 M = c2hole_ch M β`
  の **外側に余分な `D_{M_{1,s84x_jm2 M}}` が 1 段付く**（`condV_terminal_slice_Trans`
  の頭 `entry M 1 m` に対応、`m = s84x_jm2 M`）。エンジンの `(s,b)` はこの余分な先頭を
  持たないため、`Trans (s84x_Np M)` の scb 文字列 `flatBT` の長さが `c2hole_ch M β` の
  それより 1 principal 分長く、`s ++ (D_β 0) ++ b` と一致しない。ゆえに transport は
  条件(III)では成立しない。（条件(V) では `condV_bridge_hp_jm2` により
  `s84x_jm2 M = transJ0 M` となり頭が畳まれて一致するため、エンジンの設計は条件(V)
  専用であった。）

  ## 具体 host（機械証明）

  `M = (0,0)(1,1)(2,1) = oper (diagSeq 0 2) 2`（標準形・単項・条件(III)）。
  `Lng M = 3`, `s84x_jm2 M = 0`, `β = M_{1,2} = 1`, `γ = M_{1,0} = 0`。
  * `c2hole_ch M β = D_1(D_1 0)`, `flatBT = [D_1, D_1, Z]`。中心 `D_β 0 = [D_1, Z]`。
  * `c2hole_ch M γ = D_1(D_0 0)`, `flatBT = [D_1, D_0, Z]`。中心 `D_γ 0 = [D_0, Z]`。
    共有 `(s,b) = ([D_1], [])` が両者を分解する（`hA1`/`hA2`、無条件）。
  * しかし `s84x_Np M = M` かつ `Trans M = D_0(D_1(D_1 0))`,
    `flatBT = [D_0, D_1, D_1, Z]`。中心 `D_β 0 = [D_1, Z]` に対し `s ++ 中心 ++ b
    = [D_1, D_1, Z] ≠ [D_0, D_1, D_1, Z]`。すなわち共有 `(s,b)` は
    `Trans (s84x_Np M)` を分解しない。transport の結論 `concl.1` が偽。

- 帰結: `rm84Readback`（= `Rightmost84ReplaceCorrected`/`Exists`）は真だが（A30 host で
  `∃! (s,b)` を機械確認済み、`8.4-rightmost-replace-Trans`）、その reduction である
  本 `C2HoleSliceTransport_ch` も、双子の値リードバック `Rightmost84ReadbackShared`
  （`8.4-rightmost-readback`、同じく `Dprin V (addBT T2 ·)` の閉形式を仮定）も、
  **条件(III)の余分な先頭ゆえに偽**。フィールドを閉じるには、`Trans (s84x_Np M)` の
  条件(III)/(IV) での正しい先頭付き形（`condV_terminal_slice_Trans` の頭 `entry M 1 m`
  を露出した transport）に言明を作り直す必要がある。

- 依存（ビルド済み・committed e73a073）: «8».«8.4-c2hole-engine»
  （`C2HoleSliceTransport_ch`/`c2hole_ch`/`Trans`/`s84x_Np`/`rrLp`/`s84x_jm2`/`STPS`/
  `oper`/`diagSeq`/`entry`/`Lng`/`hasParent`/`monoT`/`scb_decomp`/`flatBT`/`Dprin`/
  `BZero`/`Sym`/`BP`）。
- 数値検証: `python/trans_model.py`（`Trans`/`scb_decomps`）。条件(III) STPS host で
  共有 `(s,b)` が `Trans(Np)` を分解しないことを網羅確認（93/93 fail）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private suffix: `_ct`。
-/

namespace PSS

/-! ## 1. 反例 host `M = (0,0)(1,1)(2,1)`（条件(III)標準形） -/

/-- 条件(III)の反例 host。`oper (diagSeq 0 2) 2`。 -/
def transportCex_ct : PS := [(0,0),(1,1),(2,1)]

/-- `M = (0,0)(1,1)(2,1)` は標準形（`diagSeq 0 2` から `oper` 1 段）。 -/
theorem transportCex_STPS_ct : STPS transportCex_ct := by
  have h0 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2)] := by
    have h := STPS.diag 0 2 (by decide)
    rwa [show diagSeq 0 2 = [((0:ℕ),(0:ℕ)),(1,1),(2,2)] from by decide] at h
  have h1 := STPS.oper h0 2 (by decide)
  rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2)] 2 = transportCex_ct from by decide] at h1

/-- host が transport の 4 前提をすべて満たす（反例が in-scope であることの確認）。 -/
theorem transportCex_pre_ct :
    STPS transportCex_ct ∧ monoT transportCex_ct = true ∧
      hasParent transportCex_ct 1 (Lng transportCex_ct - 1) = true ∧
      s84x_jm2 transportCex_ct + 1 < Lng transportCex_ct - 1 :=
  ⟨transportCex_STPS_ct, by decide, by decide, by decide⟩

/-! ## 2. 共有 scb 文脈（エンジンが transport に渡す `(s,b)`） -/

/-- エンジンの共有 scb 文脈の左文字列 `s = [D_{transV M}] = [D_1]`。 -/
def transportCex_s_ct : List Sym := [Sym.dsym (1:ℕ∞)]

/-- エンジンの共有 scb 文脈の右文字列 `b = []`。 -/
def transportCex_b_ct : List Sym := []

/-- transport の第 1 前提 `hA1`: 共有 `(s,b)` は `c2hole_ch M β`（中心 `D_β 0`）を
分解する。これはエンジン `c2hole_scb_ch` の出力（`β = entry M 1 (Lng M − 1) = 1`）。 -/
theorem transportCex_hA1_ct :
    scb_decomp (c2hole_ch transportCex_ct (entry transportCex_ct 1 (Lng transportCex_ct - 1)))
      transportCex_s_ct
      (flatBT (Dprin (entry transportCex_ct 1 (Lng transportCex_ct - 1) : ℕ∞) BZero))
      transportCex_b_ct := by
  refine ⟨by decide, ?_, ?_⟩
  · intro _
    exact ⟨BP.db (entry transportCex_ct 1 (Lng transportCex_ct - 1) : ℕ∞) BZero,
      by decide, by decide⟩
  · intro x hx; simp [transportCex_b_ct] at hx

/-- transport の第 2 前提 `hA2`: 同一の共有 `(s,b)` は `c2hole_ch M γ`（中心 `D_γ 0`）を
分解する（`γ = entry M 1 (s84x_jm2 M) = 0`）。 -/
theorem transportCex_hA2_ct :
    scb_decomp (c2hole_ch transportCex_ct (entry transportCex_ct 1 (s84x_jm2 transportCex_ct)))
      transportCex_s_ct
      (flatBT (Dprin (entry transportCex_ct 1 (s84x_jm2 transportCex_ct) : ℕ∞) BZero))
      transportCex_b_ct := by
  refine ⟨by decide, ?_, ?_⟩
  · intro _
    exact ⟨BP.db (entry transportCex_ct 1 (s84x_jm2 transportCex_ct) : ℕ∞) BZero,
      by decide, by decide⟩
  · intro x hx; simp [transportCex_b_ct] at hx

/-! ## 3. 反証：条件(III)で共有 `(s,b)` は `Trans (s84x_Np M)` を分解しない -/

/-- **`C2HoleSliceTransport_ch` の反証**。条件(III)標準形 host `M = (0,0)(1,1)(2,1)` で、
エンジンが渡す共有 scb 文脈 `(s,b) = ([D_1], [])` は `hA1`/`hA2` を満たす
（`c2hole_ch M β` / `c2hole_ch M γ` を分解する）が、`Trans (s84x_Np M) = D_0(D_1(D_1 0))`
の `flatBT = [D_0, D_1, D_1, Z]` は `s ++ (D_β 0) ++ b = [D_1, D_1, Z]` と長さが食い違う
（余分な先頭 `D_0 = D_{entry M 1 (s84x_jm2 M)}`）。ゆえに transport の結論の
第 1 連言が偽。したがって `C2HoleSliceTransport_ch` は成立しない。 -/
theorem c2HoleSliceTransport_ch_false_ct : ¬ C2HoleSliceTransport_ch := by
  intro h
  have hpre := transportCex_pre_ct
  have hconcl := h transportCex_ct hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
    transportCex_s_ct transportCex_b_ct transportCex_hA1_ct transportCex_hA2_ct
  exact absurd hconcl.1.1 (by decide)

#print axioms transportCex_STPS_ct
#print axioms transportCex_pre_ct
#print axioms transportCex_hA1_ct
#print axioms transportCex_hA2_ct
#print axioms c2HoleSliceTransport_ch_false_ct

/-! ## 4. 回帰ベクトル（`python/trans_model.py` と一致） -/

#guard Lng transportCex_ct == 3
#guard s84x_jm2 transportCex_ct == 0
#guard entry transportCex_ct 1 (Lng transportCex_ct - 1) == 1
#guard entry transportCex_ct 1 (s84x_jm2 transportCex_ct) == 0
#guard s84x_Np transportCex_ct == transportCex_ct
#guard flatBT (Trans (s84x_Np transportCex_ct))
  == [Sym.dsym (0:ℕ∞), Sym.dsym (1:ℕ∞), Sym.dsym (1:ℕ∞), Sym.zero]
#guard flatBT (c2hole_ch transportCex_ct (entry transportCex_ct 1 (Lng transportCex_ct - 1)))
  == [Sym.dsym (1:ℕ∞), Sym.dsym (1:ℕ∞), Sym.zero]

end PSS
