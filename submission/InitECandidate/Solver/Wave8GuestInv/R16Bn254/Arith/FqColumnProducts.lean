import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryFactors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang

def fqProducts0 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 0)]

def fqProducts1 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 1),
   (.a 1, .b 0),
   (.m 0, .constant 1008765974)]

def fqProducts2 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 2),
   (.a 1, .b 1),
   (.a 2, .b 0),
   (.m 0, .constant 1752287885),
   (.m 1, .constant 1008765974)]

def fqProducts3 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 3),
   (.a 1, .b 2),
   (.a 2, .b 1),
   (.a 3, .b 0),
   (.m 0, .constant 2541841041),
   (.m 1, .constant 1752287885),
   (.m 2, .constant 1008765974)]

def fqProducts4 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 4),
   (.a 1, .b 3),
   (.a 2, .b 2),
   (.a 3, .b 1),
   (.a 4, .b 0),
   (.m 0, .constant 2172737629),
   (.m 1, .constant 2541841041),
   (.m 2, .constant 1752287885),
   (.m 3, .constant 1008765974)]

def fqProducts5 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 5),
   (.a 1, .b 4),
   (.a 2, .b 3),
   (.a 3, .b 2),
   (.a 4, .b 1),
   (.a 5, .b 0),
   (.m 0, .constant 3092268470),
   (.m 1, .constant 2172737629),
   (.m 2, .constant 2541841041),
   (.m 3, .constant 1752287885),
   (.m 4, .constant 1008765974)]

def fqProducts6 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 6),
   (.a 1, .b 5),
   (.a 2, .b 4),
   (.a 3, .b 3),
   (.a 4, .b 2),
   (.a 5, .b 1),
   (.a 6, .b 0),
   (.m 0, .constant 3778125865),
   (.m 1, .constant 3092268470),
   (.m 2, .constant 2172737629),
   (.m 3, .constant 2541841041),
   (.m 4, .constant 1752287885),
   (.m 5, .constant 1008765974)]

def fqProducts7 : List (MontFactor × MontFactor) :=
  [(.a 0, .b 7),
   (.a 1, .b 6),
   (.a 2, .b 5),
   (.a 3, .b 4),
   (.a 4, .b 3),
   (.a 5, .b 2),
   (.a 6, .b 1),
   (.a 7, .b 0),
   (.m 0, .constant 811880050),
   (.m 1, .constant 3778125865),
   (.m 2, .constant 3092268470),
   (.m 3, .constant 2172737629),
   (.m 4, .constant 2541841041),
   (.m 5, .constant 1752287885),
   (.m 6, .constant 1008765974)]

def fqProducts8 : List (MontFactor × MontFactor) :=
  [(.a 1, .b 7),
   (.a 2, .b 6),
   (.a 3, .b 5),
   (.a 4, .b 4),
   (.a 5, .b 3),
   (.a 6, .b 2),
   (.a 7, .b 1),
   (.m 1, .constant 811880050),
   (.m 2, .constant 3778125865),
   (.m 3, .constant 3092268470),
   (.m 4, .constant 2172737629),
   (.m 5, .constant 2541841041),
   (.m 6, .constant 1752287885),
   (.m 7, .constant 1008765974)]

def fqProducts9 : List (MontFactor × MontFactor) :=
  [(.a 2, .b 7),
   (.a 3, .b 6),
   (.a 4, .b 5),
   (.a 5, .b 4),
   (.a 6, .b 3),
   (.a 7, .b 2),
   (.m 2, .constant 811880050),
   (.m 3, .constant 3778125865),
   (.m 4, .constant 3092268470),
   (.m 5, .constant 2172737629),
   (.m 6, .constant 2541841041),
   (.m 7, .constant 1752287885)]

def fqProducts10 : List (MontFactor × MontFactor) :=
  [(.a 3, .b 7),
   (.a 4, .b 6),
   (.a 5, .b 5),
   (.a 6, .b 4),
   (.a 7, .b 3),
   (.m 3, .constant 811880050),
   (.m 4, .constant 3778125865),
   (.m 5, .constant 3092268470),
   (.m 6, .constant 2172737629),
   (.m 7, .constant 2541841041)]

def fqProducts11 : List (MontFactor × MontFactor) :=
  [(.a 4, .b 7),
   (.a 5, .b 6),
   (.a 6, .b 5),
   (.a 7, .b 4),
   (.m 4, .constant 811880050),
   (.m 5, .constant 3778125865),
   (.m 6, .constant 3092268470),
   (.m 7, .constant 2172737629)]

def fqProducts12 : List (MontFactor × MontFactor) :=
  [(.a 5, .b 7),
   (.a 6, .b 6),
   (.a 7, .b 5),
   (.m 5, .constant 811880050),
   (.m 6, .constant 3778125865),
   (.m 7, .constant 3092268470)]

def fqProducts13 : List (MontFactor × MontFactor) :=
  [(.a 6, .b 7),
   (.a 7, .b 6),
   (.m 6, .constant 811880050),
   (.m 7, .constant 3778125865)]

def fqProducts14 : List (MontFactor × MontFactor) :=
  [(.a 7, .b 7),
   (.m 7, .constant 811880050)]

def fqColumnFactors (i : Fin 15) : List (MontFactor × MontFactor) :=
  match i.val with
  | 0 => fqProducts0
  | 1 => fqProducts1
  | 2 => fqProducts2
  | 3 => fqProducts3
  | 4 => fqProducts4
  | 5 => fqProducts5
  | 6 => fqProducts6
  | 7 => fqProducts7
  | 8 => fqProducts8
  | 9 => fqProducts9
  | 10 => fqProducts10
  | 11 => fqProducts11
  | 12 => fqProducts12
  | 13 => fqProducts13
  | _ => fqProducts14

theorem fqColumnFactors_length (i : Fin 15) : (fqColumnFactors i).length ≤ 16 := by
  fin_cases i <;> decide

theorem fqColumnFactors_bounded (i : Fin 15) :
    ∀ p ∈ fqColumnFactors i, montFactorBounded p.1 ∧ montFactorBounded p.2 := by
  fin_cases i <;> simp [fqColumnFactors, montFactorBounded,
    fqProducts0, fqProducts1, fqProducts2, fqProducts3, fqProducts4, fqProducts5, fqProducts6, fqProducts7, fqProducts8, fqProducts9, fqProducts10, fqProducts11, fqProducts12, fqProducts13, fqProducts14]

end InitECandidate.Solver.Wave8GuestInv.Arith
