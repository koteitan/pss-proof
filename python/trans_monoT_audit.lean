import «7».«7.3-Trans-preserves-monoT»

/-! Executable Lean-side audit for corrected A16. -/

open PSS

def transMonoPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def transMonoSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (transMonoSeqsOfLen k n).flatMap fun M =>
      (transMonoPairsUpto k).map fun p => M ++ [p]

def transMonoInputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => transMonoSeqsOfLen k (n + 1)

def transMonoReduced (k maxLength : ℕ) : List PS :=
  (transMonoInputs k maxLength).filter fun M => reduced M

def transMonoTargets (k maxLength : ℕ) : List PS :=
  (transMonoReduced k maxLength).filter fun M =>
    !zeroT ((P M).getD 0 [])

def transMonoFailures (k maxLength : ℕ) : List PS :=
  (transMonoTargets k maxLength).filter fun M =>
    monoT M != ((PB (Trans M)).length == 1)

#eval (transMonoInputs 3 3).length
#eval (transMonoReduced 3 3).length
#eval (transMonoTargets 3 3).length
#eval (transMonoFailures 3 3).length

#guard !monoT [(0, 0), (0, 0)]
#guard (PB (Trans [(0, 0), (0, 0)])).length == 1
#guard zeroT ((P [(0, 0), (0, 0)]).getD 0 [])
