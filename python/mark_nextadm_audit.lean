import «7».«7.4-Mark-nextAdm»

/-!
Executable Lean-side audit for corrected §7.4 A18/A47.

The audit enumerates all 819 nonempty sequences of length at most three with
both entries below three.  It checks the marked-nesting engine and every
specialization selected by a unique final `nextAdm` parent, then evaluates the
two formal correction witnesses.
-/

open PSS

def tmpMarkNextPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def tmpMarkNextSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (tmpMarkNextSeqsOfLen k n).flatMap fun M =>
      (tmpMarkNextPairsUpto k).map fun p => M ++ [p]

def tmpMarkNextInputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => tmpMarkNextSeqsOfLen k (n + 1)

def tmpMarkNextMarked (M : PS) (m : ℕ) : Bool :=
  adm M m && leR M 0 m (Lng M - 1)

def tmpMarkNextParents (M : PS) : List ℕ :=
  (List.range (Lng M)).filter fun m => nextAdm M 0 m (Lng M - 1)

def tmpMarkNextCommon (M : PS) (m m' : ℕ) :
    List (List Sym × List Sym) :=
  let pred := scbContexts (Mark (Pred M) m) (flatBT (Mark (Pred M) m'))
  let whole := scbContexts (Mark M m) (flatBT (Mark M m'))
  pred.filter fun sb => whole.contains sb

def tmpMarkNestTargets (k maxLength : ℕ) : List (PS × ℕ × ℕ) :=
  (tmpMarkNextInputs k maxLength).flatMap fun M =>
    if !reduced M then []
    else
      (List.range (Lng M - 1)).flatMap fun m' =>
        if !tmpMarkNextMarked M m' then []
        else (List.range (m' + 1)).filterMap fun m =>
          if tmpMarkNextMarked M m then some (M, m, m') else none

def tmpMarkNextTargets (k maxLength : ℕ) : List (PS × ℕ × ℕ) :=
  (tmpMarkNextInputs k maxLength).flatMap fun M =>
    if !reduced M then []
    else match tmpMarkNextParents M with
      | [m'] => (List.range (Lng M)).filterMap fun m =>
          if tmpMarkNextMarked M m && leR M 0 m m' then some (M, m, m')
          else none
      | _ => []

def tmpMarkNextFailures (xs : List (PS × ℕ × ℕ)) :
    List (PS × ℕ × ℕ) :=
  xs.filter fun x => (tmpMarkNextCommon x.1 x.2.1 x.2.2).length != 1

def tmpMarkNextBad18 : PS := [(0, 0), (1, 1), (2, 2), (3, 1)]
def tmpMarkNextBad47 : PS :=
  [(0, 0), (4, 2), (2, 6), (4, 2), (8, 4), (6, 4)]

#eval (tmpMarkNextInputs 3 3).length
#eval (tmpMarkNestTargets 3 3).length
#eval (tmpMarkNextFailures (tmpMarkNestTargets 3 3)).length
#eval (tmpMarkNextTargets 3 3).length
#eval (tmpMarkNextFailures (tmpMarkNextTargets 3 3)).length

#guard reduced tmpMarkNextBad18
#guard tmpMarkNextParents tmpMarkNextBad18 == [2]
#guard leR tmpMarkNextBad18 0 1 2
#guard !tmpMarkNextMarked tmpMarkNextBad18 1

#guard !reduced tmpMarkNextBad47
#guard tmpMarkNextParents tmpMarkNextBad47 == [3]
#guard tmpMarkNextMarked tmpMarkNextBad47 0
#guard leR tmpMarkNextBad47 0 0 3
#guard (tmpMarkNextCommon tmpMarkNextBad47 0 3).isEmpty
