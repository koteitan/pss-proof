import «7».«7.4-Trans-nextAdm»

/-!
Executable Lean-side audit for corrected §7.4 A45/A46.

The audit enumerates all 819 nonempty sequences of length at most three with
both entries below three.  On reduced inputs it counts every proper marked
column and every unique final `nextAdm` parent whose two scb-context lists have
exactly one common member.  It also checks the formal A45/A46 counterexample.
-/

open PSS

def tmp74PairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def tmp74SeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (tmp74SeqsOfLen k n).flatMap fun M =>
      (tmp74PairsUpto k).map fun p => M ++ [p]

def tmp74Inputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => tmp74SeqsOfLen k (n + 1)

def tmp74Marked (M : PS) (m : ℕ) : Bool :=
  adm M m && leR M 0 m (Lng M - 1)

def tmp74CommonContexts (M : PS) (m : ℕ) : List (List Sym × List Sym) :=
  let pred := scbContexts (Trans (Pred M)) (flatBT (Mark (Pred M) m))
  let whole := scbContexts (Trans M) (flatBT (Mark M m))
  pred.filter fun sb => whole.contains sb

def tmp74A46Targets (k maxLength : ℕ) : List (PS × ℕ) :=
  (tmp74Inputs k maxLength).flatMap fun M =>
    if reduced M then
      (List.range (Lng M - 1)).filterMap fun m =>
        if tmp74Marked M m then some (M, m) else none
    else []

def tmp74A45Targets (k maxLength : ℕ) : List (PS × ℕ) :=
  (tmp74Inputs k maxLength).filterMap fun M =>
    if !reduced M then none
    else
      let ps := (List.range (Lng M)).filter fun m =>
        nextAdm M 0 m (Lng M - 1)
      match ps with
      | [m] => some (M, m)
      | _ => none

def tmp74Failures (xs : List (PS × ℕ)) : List (PS × ℕ) :=
  xs.filter fun x => (tmp74CommonContexts x.1 x.2).length != 1

def tmp74Bad : PS := [(0, 0), (0, 1), (1, 2), (1, 0)]

#eval (tmp74Inputs 3 3).length
#eval (tmp74A46Targets 3 3).length
#eval (tmp74Failures (tmp74A46Targets 3 3)).length
#eval (tmp74A45Targets 3 3).length
#eval (tmp74Failures (tmp74A45Targets 3 3)).length
#eval (List.range 4).filter fun m => nextAdm tmp74Bad 0 m 3
#eval (tmp74CommonContexts tmp74Bad 1).length
