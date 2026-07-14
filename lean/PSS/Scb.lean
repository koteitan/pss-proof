import PSS.Buchholz

/-!
# PSS.Scb — §7.2 scb 分解

移植元: `isabelle/pss_paper.thy` §7.2。

Buchholz 項をアルファベット `Σ` 上の文字列へ flatten し、右端 principal spine と
scb 分解、第 0 種・第 1 種分解、基点付き Buchholz 項を定義する。
-/

namespace PSS

/-- Buchholz 項の文字列表現に用いるアルファベット `Σ`。 -/
inductive Sym where
  | lp
  | cm
  | rp
  | zero
  | dsym (u : ℕ∞)
  deriving BEq, DecidableEq

/- 項と principal 項の `Σ`-文字列、および multi 項の区切り付き tail。 -/
mutual
  def flatBT : BT → List Sym
    | .trm [] => [.zero]
    | .trm [p] => flatBP p
    | .trm (p :: q :: ps) =>
        .lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [.rp]
  def flatBP : BP → List Sym
    | .db u a => .dsym u :: flatBT a
  def flatBPTail : List BP → List Sym
    | [] => []
    | p :: ps => .cm :: flatBP p ++ flatBPTail ps
end

/- `RightNodes`: 項の末尾 principal を辿った有限指標列。 -/
mutual
  def RightNodes : BT → List ℕ
    | .trm ps => rightNodesList ps
  def rightNodesBP : BP → List ℕ
    | .db u a => u.toNat :: RightNodes a
  def rightNodesList : List BP → List ℕ
    | [] => []
    | [p] => rightNodesBP p
    | _ :: ps => rightNodesList ps
end

/-- 文字列 `c` が `D_ω`-free principal 項の文字列であること。 -/
def isPTB_str (c : List Sym) : Prop :=
  ∃ p, dfree_BP p = true ∧ c = flatBP p

/-- `(s,c,b)` が `t` の scb 分解であること。 -/
def scb_decomp (t : BT) (s c b : List Sym) : Prop :=
  flatBT t = s ++ c ++ b ∧
  (t ≠ BZero → isPTB_str c) ∧
  (∀ x ∈ b, x = .rp)

/-- 第 0 種 scb 分解。 -/
def scb_kind0 (t : BT) (s c b : List Sym) : Prop :=
  scb_decomp t s c b ∧
  ∀ p, c = flatBP p →
    (RightNodes (.trm [p])).length = 2 ∧
      (RightNodes (.trm [p])).getD 1 0 = 0

/-- 第 1 種 scb 分解。 -/
def scb_kind1 (t : BT) (s c b : List Sym) : Prop :=
  scb_decomp t s c b ∧
  ∀ p, c = flatBP p →
    let r := RightNodes (.trm [p])
    let j1 := r.length - 1
    1 ≤ j1 ∧ r.getD 0 0 < r.getD j1 0 ∧
      ∀ j, 0 < j → j < j1 → r.getD j1 0 ≤ r.getD j 0

/-- `t` が第 0 種 scb 分解可能であること。 -/
def scb_kind0_able (t : BT) : Prop := ∃ s c b, scb_kind0 t s c b

/-- `t` が第 1 種 scb 分解可能であること。 -/
def scb_kind1_able (t : BT) : Prop := ∃ s c b, scb_kind1 t s c b

/-- `T_B^Marked`: `t` の scb 分解で principal 項 `c` が印付けされていること。 -/
def MarkedB : Set (BT × BT) :=
  {tc | ∃ s b, scb_decomp tc.1 s (flatBT tc.2) b}

/-! flatten と右端 spine の回帰テスト。 -/

#guard flatBT BZero == [.zero]
#guard flatBT (Dprin 0 BZero) == [.dsym 0, .zero]
#guard flatBT (BT.trm [.db 0 BZero, .db 1 BZero]) ==
  [.lp, .dsym 0, .zero, .cm, .dsym 1, .zero, .rp]
#guard RightNodes (Dprin 1 (Dprin 2 BZero)) == [1, 2]

end PSS
