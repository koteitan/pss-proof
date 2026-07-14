import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# PSS.Defs — §5 定式化（ペア数列・親子関係・基本列）

移植元: `isabelle/pss_defs.thy` §4–§5, §6.1。

## 設計方針（重要）

**すべて計算可能（`Bool` 値）に定義する。** 理由は、この論文の誤り 30 件のほとんどが
**有限の反例**で落ちるから（`corrections.md`）。`decide` / `#eval` が効く形にしておけば、
Isabelle 版で偽命題の証明に何日も溶かした場面を、Lean では 1 行で反証できる。

そのため `≤_M`（親子関係の反射推移閉包）は `Relation.ReflTransGen` ではなく
**燃料付きの再帰**で定義する。`nextrel0`/`nextrel1` の辺は必ず添字を増やすので、
`j0` から `j1` への道の長さは `Lng M` 未満。よって燃料 `Lng M` で足りる（忠実性は失われない）。
命題を述べるときは `Prop` 版（`LeR`）を使う。
-/

namespace PSS

/-- ペア数列 = `(ℕ × ℕ)` の列。空列でないものが `T_PS`。 -/
abbrev PS := List (ℕ × ℕ)

/-- `T_PS`: 空でないペア数列全体。 -/
def TPS (M : PS) : Prop := M ≠ []

/-- `Lng M`: 列の長さ。 -/
abbrev Lng (M : PS) : ℕ := M.length

/-- `M_{i,j}`: `j` 番目のペアの第 `i` 成分（`i ∈ {0,1}`）。範囲外は `0`。 -/
def entry (M : PS) (i j : ℕ) : ℕ :=
  match M[j]? with
  | none => 0
  | some p => if i = 0 then p.1 else p.2

/-- `Idx M`: 添字の集合。 -/
def Idx (M : PS) : Set (ℕ × ℕ) := {p | (p.1 = 0 ∨ p.1 = 1) ∧ p.2 < Lng M}

/-! ## §5.1 親子関係 -/

/-- `(0,j0) <^Next_M (0,j1)`: 上段の親子関係（1 段）。 -/
def nextrel0 (M : PS) (j0 j1 : ℕ) : Bool :=
  (j0 < Lng M) && (j1 < Lng M) && (j0 < j1) &&
  (entry M 0 j0 < entry M 0 j1) &&
  (List.range j1).all (fun j => !(decide (j0 < j)) || decide (entry M 0 j1 ≤ entry M 0 j))

/-- `le0` の本体。燃料は道の長さの上界（`Lng M` で足りる）。 -/
def le0Aux (M : PS) : ℕ → ℕ → ℕ → Bool
  | 0,        j0, j1 => j0 == j1
  | fuel + 1, j0, j1 =>
      (j0 == j1) ||
      (List.range j1).any (fun j => nextrel0 M j j1 && le0Aux M fuel j0 j)

/-- `(0,j0) ≤_M (0,j1)`: 上段の直系先祖関係（反射推移閉包）。 -/
def le0 (M : PS) (j0 j1 : ℕ) : Bool :=
  (j0 < Lng M) && (j1 < Lng M) && le0Aux M (Lng M) j0 j1

/-- `(1,j0) <^Next_M (1,j1)`: 下段の親子関係（1 段）。上段の `≤` に依存する。 -/
def nextrel1 (M : PS) (j0 j1 : ℕ) : Bool :=
  (j0 < Lng M) && (j1 < Lng M) && (j0 < j1) &&
  (entry M 1 j0 < entry M 1 j1) &&
  le0 M j0 j1 &&
  (List.range (Lng M)).all
    (fun j => !(decide (j0 < j) && le0 M j j1) || decide (entry M 1 j1 ≤ entry M 1 j))

def le1Aux (M : PS) : ℕ → ℕ → ℕ → Bool
  | 0,        j0, j1 => j0 == j1
  | fuel + 1, j0, j1 =>
      (j0 == j1) ||
      (List.range j1).any (fun j => nextrel1 M j j1 && le1Aux M fuel j0 j)

/-- `(1,j0) ≤_M (1,j1)`: 下段の直系先祖関係。 -/
def le1 (M : PS) (j0 j1 : ℕ) : Bool :=
  (j0 < Lng M) && (j1 < Lng M) && le1Aux M (Lng M) j0 j1

/-- 段 `i` で統一した親子関係 `(i,j0) <^Next_M (i,j1)`。 -/
def nextR (M : PS) (i j0 j1 : ℕ) : Bool :=
  if i = 0 then nextrel0 M j0 j1 else nextrel1 M j0 j1

/-- 段 `i` で統一した直系先祖関係 `(i,j0) ≤_M (i,j1)`。 -/
def leR (M : PS) (i j0 j1 : ℕ) : Bool :=
  if i = 0 then le0 M j0 j1 else le1 M j0 j1

/-- 命題として使うときの `≤_M`。 -/
def LeR (M : PS) (i j0 j1 : ℕ) : Prop := leR M i j0 j1 = true

instance (M : PS) (i j0 j1 : ℕ) : Decidable (LeR M i j0 j1) := by
  unfold LeR; infer_instance

/-! ## §5.2 前者関数 -/

/-- `Pred M`: 末尾のペアを落とす（`Lng M ≤ 1` なら恒等）。 -/
def Pred (M : PS) : PS := if Lng M ≤ 1 then M else M.dropLast

/-- `Derp M`: 先頭のペアを落とす。 -/
def Derp (M : PS) : PS := M.tail

/-! ## §5.3 基本列 `M[n]` -/

/-- `i₁ = max {i ∈ {0,1} | M_{i,j₁} > 0}`（`M_{j₁} ≠ (0,0)` のとき定義される）。 -/
def idx1 (M : PS) (j1 : ℕ) : ℕ := if 0 < entry M 1 j1 then 1 else 0

/-- 段 `i` における `j1` の親の候補（原文は一意性を主張する）。 -/
def parents (M : PS) (i j1 : ℕ) : List ℕ :=
  (List.range (Lng M)).filter (fun j0 => nextR M i j0 j1)

/-- `j1` が段 `i` に（一意な）親を持つか。 -/
def hasParent (M : PS) (i j1 : ℕ) : Bool := (parents M i j1).length == 1

/-- 段 `i` における `j1` の親。存在しないときの値は使わない。 -/
def parent (M : PS) (i j1 : ℕ) : ℕ := (parents M i j1).headD 0

/-- 閉区間の切片 `(M_j)_{j=a}^{b}`（`a ≤ b` のとき長さ `b - a + 1`）。 -/
def seg (M : PS) (a b : ℕ) : PS :=
  (List.range' a (b + 1 - a)).map (fun j => (entry M 0 j, entry M 1 j))

/-- 基本列 `M[n]`（§5.3 の逐語形）。

`j₁ = Lng M - 1` として
* `j₁ = 0` なら `M[n] = M`
* `M_{j₁} = (0,0)` なら `M[n] = Pred M`
* 段 `i₁` に親が無ければ `M[n] = Pred M`
* さもなくば `M[n] = G ⊕ ⨁_{k<n} B_k`、`G = (M_j)_{j=0}^{j₀-1}`、
  `B_k = ((M_{0,j} + k·δ₀, M_{1,j} + k·δ₁))_{j=j₀}^{j₁-1}`。
-/
def oper (M : PS) (n : ℕ) : PS :=
  let j1 := Lng M - 1
  if j1 = 0 then M
  else if entry M 0 j1 = 0 && entry M 1 j1 = 0 then Pred M
  else
    let i1 := idx1 M j1
    if !hasParent M i1 j1 then Pred M
    else
      let j0 := parent M i1 j1
      let d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0
      let d1 := if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0
      M.take j0 ++
        ((List.range n).flatMap (fun k =>
          (List.range' j0 (j1 - j0)).map (fun j =>
            (entry M 0 j + k * d0, entry M 1 j + k * d1))))

/-! ## §6.1 最上行のインクリメント -/

/-- `IncrFirst M`: 上段（第 0 成分）を全部 1 増やす。 -/
def IncrFirst (M : PS) : PS := M.map (fun p => (p.1 + 1, p.2))

end PSS
