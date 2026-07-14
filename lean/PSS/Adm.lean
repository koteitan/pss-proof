import PSS.Defs

/-!
# PSS.Adm — §6.3 許容性 / 許容化 / 基点

移植元: `isabelle/pss_defs.thy` §6.3。
-/

namespace PSS

/-- `nadm M j`（非 `M` 許容）: `j > Lng M`、または `(1,j-1) <^Next (1,j)` と
`(1,j) <^Next (1,j+1)` の両方が成り立つ。 -/
def nadm (M : PS) (j : ℕ) : Bool :=
  (Lng M < j) || (nextR M 1 (j - 1) j && nextR M 1 j (j + 1))

/-- `adm M j`（`M` 許容）。 -/
def adm (M : PS) (j : ℕ) : Bool := !nadm M j

/-- `AdmSet M`（`ℕ_M`）: `M` 許容な自然数全体。 -/
def AdmSet (M : PS) : Set ℕ := {j | adm M j = true}

/-- `Adm M j`（`Adm_M(j)`）: `j` の許容化。`j` が許容ならそれ自身、
さもなくば `j` 未満の許容な最大の数。 -/
def Adm (M : PS) (j : ℕ) : ℕ :=
  if adm M j then j
  else ((List.range j).reverse.find? (fun j' => adm M j')).getD 0

/-- `Marked`（`T_PS^Marked`）: 基点付きペア数列。 -/
def Marked (M : PS) (m : ℕ) : Prop :=
  TPS M ∧ adm M m = true ∧ leR M 0 m (Lng M - 1) = true

instance (M : PS) (m : ℕ) : Decidable (Marked M m) := by
  unfold Marked TPS; infer_instance

end PSS
