import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

/-- Every successful lookup of this name yields a memory-preserving body. -/
def MemoryPureFunction (name : MlS) : Prop :=
  ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL),
    lookupCodeHOLFinite originalRuntimeCode.lookup name values = some (body, callee, shape) →
      MemoryPure body

theorem MemoryPure.call (name : MlS) (args : List (ExpHOL 64))
    (destination : Option (Option (VarKind × MlS))) (hp : MemoryPureFunction name) :
    MemoryPure (.call (destination.map (fun d => (d, none))) name args) := by
  intro F s hc
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values hargs
    split
    · rfl
    · rename_i body callee shape hlk
      have hp' : MemoryPure body := hp values body callee shape (by simpa only [hc] using hlk)
      split
      · rfl
      · have hm := hp' (callEntryStateHOLFinite s callee) hc
        cases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result mid =>
          rw [hr] at hm
          change mid.memory = s.memory at hm
          cases result with
          | none => exact hm
          | some result =>
            cases result <;> dsimp only <;> try exact hm
            · split
              · cases destination with
                | none => exact hm
                | some destination =>
                  cases destination with
                  | none => exact hm
                  | some destination =>
                    rcases destination with ⟨kind,key⟩
                    simp only [Option.map_some]
                    split
                    · cases kind <;> exact hm
                    · exact hm
              · exact hm
            · cases destination with
              | none => exact hm
              | some destination => exact hm

theorem MemoryPure.decCall (resultName : MlS) (shape : ShapeHOL)
    (name : MlS) (args : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hp : MemoryPureFunction name) (hq : MemoryPure continuation) :
    MemoryPure (.decCall resultName shape name args continuation) := by
  intro F s hc
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · rfl
  · rename_i values hargs
    split
    · rfl
    · rename_i body callee rs hlk
      have hp' : MemoryPure body := hp values body callee rs (by simpa only [hc] using hlk)
      split
      · rfl
      · dsimp only
        have hm := hp' (callEntryStateHOLFinite s callee) hc
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result mid =>
          rw [hr] at hm hmeta
          change mid.memory = s.memory at hm
          change mid.code = s.code at hmeta
          cases result with
          | none => exact hm
          | some result =>
            cases result <;> dsimp only <;> try exact hm
            split
            · rename_i value hshape
              let resumed := setVarHOLFinite resultName value
                { (fixClockHOLFinite (callEntryStateHOLFinite s callee)
                    (some (PanSemResultExact.returned value), mid)).2 with locals := s.locals }
              exact (hq resumed (hmeta.trans hc)).trans hm
            · exact hm

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
