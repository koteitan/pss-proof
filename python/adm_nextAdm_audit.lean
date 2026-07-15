import «7».«7.4-Adm-nextAdm»

/-! Executable Lean-side audit for §7.4 `Adm_nextAdm`. -/

open PSS

def admNextPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def admNextSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (admNextSeqsOfLen k n).flatMap fun M =>
      (admNextPairsUpto k).map fun p => M ++ [p]

def admNextInputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => admNextSeqsOfLen k (n + 1)

def admNextTargets (k maxLength : ℕ) : List (PS × ℕ) :=
  (admNextInputs k maxLength).flatMap fun M =>
    (List.range 2).filterMap fun i =>
      if hasParent M i (Lng M - 1) then some (M, i) else none

def admNextFailures (k maxLength : ℕ) : List (PS × ℕ) :=
  (admNextTargets k maxLength).filter fun Mi =>
    let M := Mi.1
    let i := Mi.2
    !nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1)

#eval (admNextInputs 3 3).length
#eval (admNextTargets 3 3).length
#eval ((admNextTargets 3 3).filter fun Mi => Mi.2 == 0).length
#eval ((admNextTargets 3 3).filter fun Mi => Mi.2 == 1).length
#eval (admNextFailures 3 3).length

#guard nextAdm [(0, 0), (1, 0)] 0 0 1
#guard nextAdm [(0, 0), (1, 1)] 1 0 1
