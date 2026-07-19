import «8».«8.4-fseq-basic-part2»
import «8».«8.4-oper-basic»

/-!
# §8.4 補題 part (2) の L 切片 `Trans` 閉形式 `L6TransSliceClosed_p2` の討伐（塔帰納）

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
  `j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁`、`w' = j₁ - 1 - j₋₂` として
  L 切片 `L_n := (λN. N[1])^{w'}(M[n+1])` の `Trans` 平坦形が operB 基本列側の
  producer 閉形式 `s₁ ++ D_{e₃}(coreTower ins 0_B n) ++ b₁` に一致する。
- Isabelle（設計図）: `m_8_4_various_scb_IIIIV_from_slice`
  （`isabelle/layerB/pss_wip.thy:60034`）の `flatBT (Trans (s84x_L M n)) = cL` 連言。
  塔帰納 `concat(replicate n …)` を `s84d_dec1/dec2_*` の scb-surgery で回す。

## 本ファイルの内容（producer 座標での塔帰納、house green-modulo）

対象は «8».«8.4-fseq-basic-part2» の `L6TransSliceClosed_p2`（producer 座標）。
producer の全出力（`hflat`/`hb0`/`hb1`/`fO`/`fM`/`base0`/`base1`/`Lbase`）を仮定として
持ち込み、L 切片の `Trans` 平坦形が producer 閉形式に一致することを主張する。

**塔帰納（本ファイルが無条件に閉じる）**: 単一段補題 `oper_rule_basic_part5`
（«8».«8.4-oper-basic»、Isabelle `m_8_4_oper_props_5`、**無条件**）が、各段で
`Trans(L_{n-1})` と `Trans(L_n)` を共有 scb 位置 `(sb.1,sb.2)` で結び、中心を
穴 `D_{M₁,ⱼ₋₂} 0` から `Trans(L')` へ差し替える。これを `s84x_L M n = op1^{w'}(M[n+1])`
（`op1pow` bridge）で goal の L 切片に接続し、`coreTower_zero_flat_l6` で producer
閉形式の flat へ書き換えて閉じる。塔帰納・文字列代数は無条件。文字列代数の骨格は
«8».«8.5-exchV-M-tower» の condV 版塔帰納 `exchV_M_tower_of_residual` と同一。

**残差 `L6TowerResidual`（`needs`）**: 塔帰納の底読み出し 4 本のみ:
* `op1pow` — `op1^{w'}(M[n+1]) = s84x_L M n`（Isabelle `y3l_L_eq_op1pow`、§8.4 の列構成の
  組合せ恒等式。経験的に 164/164、`python/_l6_part2_audit.py`）。
* `ub_eq` — producer の挿入深 `ub` ＝ 行1親の行1成分 `M₁,ⱼ₋₂`（`(entry M 1 (s84x_jm2 M) : ℕ∞)`）。
* `base` — 底段 `L₁` の `Trans` 平坦形が producer 座標で塔深さ 1 の形。
  Isabelle `base5`（`m_8_4_various_scb_IIIIV_from_slice` の n=1）。既移植の n=1 底読み出しは
  «8».«8.4-corner-readouts» の LEAF3（condIV∧admeq 隅）と «8».«8.4-exch84-mnform-residual»
  の `hL1flat`（condIII/IV 一般、`MnformBottomResidual` 経由）に対応する。
* `lpv` — 単一段の中心値 `Trans(L') = D_{ub}(ins 0_B)`（producer 座標）。Isabelle
  `s84d_dec*` の Lp 読み出し（LEAF4）。

塔帰納エンジン `oper_rule_basic_part5` は無条件で、これら 4 本は
`Oper84BasicPart2Residual`（両辺 flat 一致）より真に下位の底葉である
（塔帰納と operB 側 flat 化 `fO` を本ファイルが消化するため）。

- 数値監査: `python/_l6_part2_audit.py`。真正 mono ST_PS プールで
  `Trans(L-slice) == operB(TransM, numBT(n-1))` = 164/164、
  `s84x_L M n == op1^{w'}(M[n+1])` = 164/164。
- 依存（すべてビルド済み・main 1f6217a）: «8».«8.4-fseq-basic-part2»
  (`L6TransSliceClosed_p2`・`coreTower_e34`・`operB`/`numBT`・`Trans`/`oper`/`entry`/`Lng`)、
  «8».«8.4-oper-basic»
  (`oper_rule_basic_part5`・`s84x_L`/`s84x_Lp`/`s84x_jm2`・`scb_decomp`・`Dprin`・`BZero`・
  推移的に `scb_unique_decomp_unconditional`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  塔帰納は無条件に閉じ、残差は底読み出し 4 本を束ねた `L6TowerResidual` 1 本。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
- Private helper suffix: `_l6`。
-/

namespace PSS

/-! ## 0. 文字列代数の private 補助（«8».«8.4-exch84-regsp» / «8».«8.5-exchV-M-tower» の複製、`_l6`） -/

/-- «8».«8.4-exch84-regsp» private `flatten_replicate_snoc_rp` の複製。 -/
private theorem flatten_replicate_snoc_l6 {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]
  simp

/-- «8».«8.5-exchV-M-tower» private `flatten_replicate_comm_mt` の複製。 -/
private theorem flatten_replicate_comm_l6 {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

/-- «8».«8.5-exchV-M-tower» private `flatten_replicate_snoc_mt` の複製。 -/
private theorem flatten_replicate_snoc2_l6 {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = (List.replicate (j + 1) b).flatten := by
  rw [flatten_replicate_comm_l6, List.replicate_succ, List.flatten_cons]

/-- `coreTower_e34 ins 0_B j` の flat 形（«8».«8.4-exch84-regsp» private
`coreTower_zero_flat_rp` の複製）。`hflat` だけから帰納。 -/
private theorem coreTower_zero_flat_l6 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ j, flatBT (coreTower_e34 ins BZero j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub]))
        ++ [Sym.zero] ++ List.flatten (List.replicate j b0)
  | 0 => by simp [coreTower_e34, BZero, flatBT]
  | j + 1 => by
      show flatBT (ins (coreTower_e34 ins BZero j)) = _
      rw [hflat (coreTower_e34 ins BZero j), coreTower_zero_flat_l6 hflat j,
        flatten_replicate_snoc_l6 b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-! ## 1. 残差 named Prop（塔帰納の底読み出し 4 本） -/

/-- **`L6TransSliceClosed_p2` を閉じるための残差**（塔帰納の底読み出し）。producer 座標で:
* `op1pow`: `op1^{w'}(M[n+1]) = s84x_L M n`、
* `ub_eq`: `(entry M 1 (s84x_jm2 M) : ℕ∞) = ub`、
* `base`: 底段 `L₁` の `Trans` 平坦形、
* `lpv`: 単一段の中心値 `Trans(L')` の平坦形。 -/
def L6TowerResidual : Prop :=
  ∀ (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 ≤ n →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ x ∈ b1, x = Sym.rp) →
    (∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ub BZero) A0 = true →
    lessBT A0 (ins (Dprin ub BZero)) = true →
    leBT (Dprin ub BZero) (ins BZero) = true →
    ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)] (oper M (n + 1))
        = s84x_L M n)
    ∧ ((entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
    ∧ (flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) ++ b1)
    ∧ (flatBT (Trans (s84x_Lp M))
        = Sym.dsym ub :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0))

/-! ## 2. 塔帰納（無条件、単一段 `oper_rule_basic_part5` で回す） -/

/-- L 切片塔の `Trans` 閉形式（producer 座標）。底段 `base`＋単一段中心値 `lpv` から、
無条件単一段補題 `oper_rule_basic_part5` の scb 差し替えで各段を組む。文字列代数の
骨格は «8».«8.5-exchV-M-tower» の condV 版と同一。 -/
private theorem l6_tower_l6
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
  -- 中心穴 `D_{M₁,ⱼ₋₂} 0` の平坦形と `isPTB_str`
  have hDe0 : flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)
      = [Sym.dsym ub, Sym.zero] := by
    show Sym.dsym (entry M 1 (s84x_jm2 M) : ℕ∞) :: flatBT BZero = _
    rw [hubeq]; rfl
  have isPTB_De0 : isPTB_str (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) :=
    ⟨.db (entry M 1 (s84x_jm2 M) : ℕ∞) BZero,
      by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  have hBkrp : ∀ m : ℕ, ∀ x ∈ (List.replicate m b0).flatten ++ b1, x = Sym.rp := by
    intro m x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp h
      rw [List.eq_of_mem_replicate hl] at hxl; exact hb0 x hxl
    · exact hb1 x h
  set X := s0 ++ [Sym.dsym ub] with hXdef
  -- 文字列 combine 補題（condV 版 snocX'/consB' と同一）
  have snocX' : ∀ (m : ℕ) (rest : List Sym),
      (List.replicate m X).flatten ++ (s0 ++ (Sym.dsym ub :: rest))
        = (List.replicate (m + 1) X).flatten ++ rest := by
    intro m rest
    have h1 : s0 ++ (Sym.dsym ub :: rest) = X ++ rest := by rw [hXdef]; simp
    rw [h1, ← List.append_assoc, flatten_replicate_snoc2_l6]
  have consB' : ∀ (m : ℕ) (rest : List Sym),
      b0 ++ ((List.replicate m b0).flatten ++ rest)
        = (List.replicate (m + 1) b0).flatten ++ rest := by
    intro m rest
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
  -- L step / split（condV 版 Lstr/splitL と同一）
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
      -- L(k+1) を中心穴 `D_{M₁,ⱼ₋₂} 0` の位置で分割
      have flatk : flatBT (Trans (s84x_L M (k + 1)))
          = (s1 ++ Sym.dsym e3 :: (List.replicate k X).flatten ++ s0)
            ++ flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)
            ++ ((List.replicate (k + 1) b0).flatten ++ b1) := by
        rw [ih, hDe0]; exact (splitL k).symm
      have wk : scb_decomp (Trans (s84x_L M (k + 1)))
          (s1 ++ Sym.dsym e3 :: (List.replicate k X).flatten ++ s0)
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))
          ((List.replicate (k + 1) b0).flatten ++ b1) :=
        ⟨flatk, fun _ => isPTB_De0, hBkrp (k + 1)⟩
      -- 単一段 engine at n = k+2
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

/-! ## 3. 記事逐語形（house pattern） -/

/-- **§8.4 補題 part (2) の L 切片 `Trans` 閉形式**（«8».«8.4-fseq-basic-part2»
`L6TransSliceClosed_p2`）の drop-in（house pattern）。塔帰納 `l6_tower_l6` を
`op1pow` bridge で goal の L 切片に接続し、`coreTower_zero_flat_l6` で producer
閉形式の flat へ書き換えて閉じる。残差は底読み出し `L6TowerResidual` 1 本。 -/
theorem l6TransSliceClosed_holds (hres : L6TowerResidual) : L6TransSliceClosed_p2 := by
  intro M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
    hflat hb0 hb1 fO fM base0 base1 Lbase
  obtain ⟨hop1, hubeq, hbase, hlpv⟩ :=
    hres M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
      hflat hb0 hb1 fO fM base0 base1 Lbase
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hop1, l6_tower_l6 M e3 ub s0 b0 s1 b1 hST hmono hp hj1 hb0 hb1 hubeq hbase hlpv k]
  -- RHS の producer 閉形式を flat へ
  have hR : flatBP (BP.db e3 (coreTower_e34 ins BZero (k + 1)))
      = Sym.dsym e3 :: ((List.replicate (k + 1) (s0 ++ [Sym.dsym ub])).flatten
          ++ [Sym.zero] ++ (List.replicate (k + 1) b0).flatten) := by
    show Sym.dsym e3 :: flatBT (coreTower_e34 ins BZero (k + 1)) = _
    rw [coreTower_zero_flat_l6 hflat (k + 1)]
  rw [hR]
  simp [List.append_assoc]

#print axioms l6TransSliceClosed_holds

end PSS
