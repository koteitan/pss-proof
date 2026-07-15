import «7».«7.3-Mark-rightmost1»

/-!
Executable Lean-side audit for §7.3 `Mark_rightmost1` / correction A17.

The audit enumerates all 819 nonempty sequences of length at most three with
both entries below three.  On every reduced input it checks the final-column
formula, the corrected iff and strict-tail claims on marked columns, and the
executable scb occurrence corresponding to `Mark_MarkedB_nest`.
-/

open PSS

def markRightmostPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def markRightmostSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (markRightmostSeqsOfLen k n).flatMap fun M =>
      (markRightmostPairsUpto k).map fun p => M ++ [p]

def markRightmostInputs (k maxLength : ℕ) : List PS :=
  (List.range maxLength).flatMap fun n => markRightmostSeqsOfLen k (n + 1)

def markRightmostReducedInputs (k maxLength : ℕ) : List PS :=
  (markRightmostInputs k maxLength).filter fun M => reduced M

def markRightmostMarkedTargets (k maxLength : ℕ) : List (PS × ℕ) :=
  (markRightmostReducedInputs k maxLength).flatMap fun M =>
    (List.range (Lng M)).filterMap fun m =>
      if decide (Marked M m) then some (M, m) else none

def markRightmostForwardFailures (k maxLength : ℕ) : List PS :=
  (markRightmostReducedInputs k maxLength).filter fun M =>
    !zeroT M &&
      Mark M (Lng M - 1) !=
        Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero

def markRightmostIffFailures (k maxLength : ℕ) : List (PS × ℕ) :=
  (markRightmostMarkedTargets k maxLength).filter fun Mm =>
    let M := Mm.1
    let m := Mm.2
    !zeroT M &&
      ((m == Lng M - 1) !=
        (Mark M m == Dprin (entry M 1 m : ℕ∞) BZero))

def markRightmostTailFailures (k maxLength : ℕ) : List (PS × ℕ) :=
  (markRightmostMarkedTargets k maxLength).filter fun Mm =>
    let M := Mm.1
    let m := Mm.2
    m < Lng M - 1 &&
      Mark M m == Dprin (entry M 1 m : ℕ∞) BZero

def markRightmostNestingTargets (k maxLength : ℕ) : List (PS × ℕ × ℕ) :=
  (markRightmostReducedInputs k maxLength).flatMap fun M =>
    (List.range (Lng M)).flatMap fun a =>
      (List.range (Lng M)).filterMap fun b =>
        if decide (Marked M a) && decide (Marked M b) && a ≤ b then
          some (M, a, b)
        else none

def markRightmostNestingFailures (k maxLength : ℕ) : List (PS × ℕ × ℕ) :=
  (markRightmostNestingTargets k maxLength).filter fun Mab =>
    let M := Mab.1
    let a := Mab.2.1
    let b := Mab.2.2
    (scbContexts (Mark M a) (flatBT (Mark M b))).isEmpty

#eval (markRightmostInputs 3 3).length
#eval (markRightmostReducedInputs 3 3).length
#eval (markRightmostMarkedTargets 3 3).length
#eval (markRightmostNestingTargets 3 3).length
#eval (markRightmostForwardFailures 3 3).length
#eval (markRightmostIffFailures 3 3).length
#eval (markRightmostTailFailures 3 3).length
#eval (markRightmostNestingFailures 3 3).length

#guard Mark [(0, 0)] 0 == BZero
#guard Mark [(0, 0)] 0 != Dprin (entry [(0, 0)] 1 0 : ℕ∞) BZero
