import «7».«7.3-Pred-Trans-descend»

/-!
Executable Lean-side audit for §7.3 `Pred_Trans_descend`.

The audit enumerates all 819 nonempty sequences of length at most three with
both entries below three.  Of these, 810 have at least two columns; every one
satisfies the strict descent computed directly from `Trans`, `Pred`, and
`lessBT`.
-/

open PSS

def predTransPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def predTransSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (predTransSeqsOfLen k n).flatMap fun M =>
      (predTransPairsUpto k).map fun p => M ++ [p]

def predTransAuditInputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => predTransSeqsOfLen k (n + 1)

def predTransAuditFailures (k maxLength : ℕ) : List PS :=
  (predTransAuditInputs k maxLength).filter fun M =>
    1 < Lng M && !lessBT (Trans (Pred M)) (Trans M)

#eval (predTransAuditInputs 3 3).length
#eval ((predTransAuditInputs 3 3).filter fun M => 1 < Lng M).length
#eval (predTransAuditFailures 3 3).length
