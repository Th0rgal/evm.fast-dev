import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithContextPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

/-- Every successful lookup of this name yields a memory-preserving body. -/
def ArithContextPureFunction (name : MlS) : Prop :=
  ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL),
    lookupCodeHOLFinite originalRuntimeCode.lookup name values = some (body, callee, shape) →
      ArithContextPure body

theorem ArithContextPure.call (name : MlS) (args : List (ExpHOL 64))
    (destination : Option (Option (VarKind × MlS)))
    (hdest : ∀ key, destination ≠ some (some (.global,key)))
    (hp : ArithContextPureFunction name) :
    ArithContextPure (.call (destination.map (fun d => (d, none))) name args) := by
  intro F s hc
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values hargs
    split
    · rfl
    · rename_i body callee shape hlk
      have hp' : ArithContextPure body := hp values body callee shape (by simpa only [hc] using hlk)
      split
      · rfl
      · have hm := hp' (callEntryStateHOLFinite s callee) hc
        cases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result mid =>
          rw [hr] at hm
          change arithContext mid = arithContext s at hm
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
                    · cases kind with
                      | «local» => exact hm
                      | «global» => exact False.elim (hdest key rfl)
                    · exact hm
              · exact hm
            · cases destination with
              | none => exact hm
              | some destination => exact hm

theorem ArithContextPure.decCall (resultName : MlS) (shape : ShapeHOL)
    (name : MlS) (args : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hp : ArithContextPureFunction name) (hq : ArithContextPure continuation) :
    ArithContextPure (.decCall resultName shape name args continuation) := by
  intro F s hc
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · rfl
  · rename_i values hargs
    split
    · rfl
    · rename_i body callee rs hlk
      have hp' : ArithContextPure body := hp values body callee rs (by simpa only [hc] using hlk)
      split
      · rfl
      · dsimp only
        have hm := hp' (callEntryStateHOLFinite s callee) hc
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result mid =>
          rw [hr] at hm hmeta
          change arithContext mid = arithContext s at hm
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

theorem ArithContextPure.loop (e : ExpHOL 64) {p : ProgHOL 64}
    (hp : ArithContextPure p) : ArithContextPure (.while e p) := by
  intro F s hc
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F), s.clock = n →
      s.code = originalRuntimeCode →
      arithContext (evaluateHOLFiniteState s (.while e p)).2 = arithContext s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hc
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      split
      · split
        · split
          · rfl
          · rename_i hclock
            have hm := hp (decClockHOLFinite s) hc
            have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s) p).1
            have hbound := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) p
            cases hr : evaluateHOLFiniteState (decClockHOLFinite s) p with
            | mk result mid =>
              rw [hr] at hm hmeta hbound
              have hsmall : mid.clock < n := by
                change mid.clock ≤ s.clock - 1 at hbound
                omega
              have hnext := ih mid.clock hsmall mid rfl (hmeta.trans hc)
              cases result with
              | none => exact hnext.trans hm
              | some result =>
                cases result <;> first | exact hm | exact hnext.trans hm
        · rfl
      · rfl
  exact hall s.clock s rfl hc

end InitECandidate.Solver.Wave8GuestInv.Arith
