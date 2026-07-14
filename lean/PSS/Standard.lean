import PSS.Red

/-!
# PSS.Standard — §6.7 標準形

移植元: `isabelle/pss_defs.thy` §6.7。

`STPS` は、対角列を含み、正の添字による基本列操作で閉じた最小の述語である。
`SkTPS k` は生成回数を固定した階層、`anchoredSlice` は訂正 A4 後の §6.5 系で使う
直系先祖に固定された切片の定義である。
-/

namespace PSS

/-- `ST_PS`: 標準形ペア数列。 -/
inductive STPS : PS → Prop where
  /-- `u ≤ v` なら対角列 `((j,j))_(j=u)^v` は標準形。 -/
  | diag (u v : ℕ) (huv : u ≤ v) : STPS (diagSeq u v)
  /-- 標準形の正の基本列は標準形。 -/
  | oper {M : PS} (hM : STPS M) (n : ℕ) (hn : 1 ≤ n) : STPS (PSS.oper M n)

/-- `SkT_PS k`: 標準形の rank-`k` 階層。 -/
def SkTPS : ℕ → PS → Prop
  | 0, N => ∃ u v, N = diagSeq u v ∧ u ≤ v
  | k + 1, N => ∃ M n, N = oper M n ∧ SkTPS k M ∧ 1 ≤ n

/-- `anchored_slice`（訂正 A4）: 標準形、または簡約単項列の直系先祖に沿った切片。 -/
def anchoredSlice (M : PS) : Prop :=
  ∃ S a b,
    (STPS S ∨ (RTPS S ∧ TPS S ∧ monoT S = true)) ∧
    a ≤ b ∧ b < Lng S ∧ le0 S a b = true ∧ M = seg S a b

end PSS
