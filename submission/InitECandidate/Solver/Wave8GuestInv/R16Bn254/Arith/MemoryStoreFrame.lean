import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryStructRead

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack

/-- Exact sequential store footprint, including machine-address wraparound. -/
def storeFootprint {width : Nat} (address : BitVec width) : Nat → List (BitVec width)
  | 0 => []
  | n + 1 => address :: storeFootprint (address + panBytesInWord width) n

/-- Successful stores preserve every address outside their actual footprint. -/
theorem memStores_frame {width : Nat} [NeZero width]
    (values : List (HolWordLab width)) (address current : BitVec width)
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory updated : BitVec width → HolWordLab width)
    (run : panMemStoresHOL address values domain memory = some updated)
    (outside : current ∉ storeFootprint address values.length) :
    updated current = memory current := by
  induction values generalizing address memory with
  | nil =>
      simp only [panMemStoresHOL_nil, Option.some.injEq] at run
      subst updated
      rfl
  | cons value rest ih =>
      simp only [List.length_cons, storeFootprint, List.mem_cons, not_or] at outside
      by_cases hd : domain address
      · simp only [panMemStoresHOL, panMemStoreHOL, if_pos hd] at run
        have h := ih (address + panBytesInWord width)
          (fun x => if x = address then value else memory x) run outside.2
        simpa only [if_neg outside.1] using h
      · simp only [panMemStoresHOL, panMemStoreHOL, if_neg hd] at run
        cases run

end InitECandidate.Solver.Wave8GuestInv.Arith
