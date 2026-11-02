import InitECandidate.Solver.Wave8GuestInv.Shards.S04.PushAdvance
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Base

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8Leaves.S04.Rlp
open Light AdvanceEffects

/-- The literal loop body of the guest function, extracted without any semantic abstraction. -/
def jumpBody : ProgHOL 64 :=
  match InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_compute_jumpdests).body with
  | .decCall _ _ _ _ (.seq _ (.dec _ _ _ (.seq (.while _ body) _))) => body
  | _ => .skip

syntax "s04_jump_body" : tactic
macro_rules
  | `(tactic| s04_jump_body) => `(tactic|
      dsimp only [jumpBody, extractFn, Guest.Software.guestFn_compute_jumpdests,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map])

theorem jumpBody_advances : VariableAdvance (ofString "pc") jumpBody := by
  s04_jump_body
  apply advance_dec (by decide)
  apply advance_init (by decide)
  apply advance_seq
  · s04_range
  · rfl

theorem jumpLoop_bound : TerminatingProgBoundedOn GuestInv
    (.while (.cmp .lower (.var .local (ofString "pc")) (.var .local (ofString "n"))) jumpBody)
    ((domainBytes + 1) * (0 + 1)) := by
  apply while_variable_walk (d := ofString "code") (i := ofString "pc") jumpBody_advances
  · s04_jump_body; rfl
  · s04_jump_body; exact firstAccess_dec_loadByte _ _ _ _ _
  · s04_jump_body; rfl
  · s04_jump_body; rfl

end InitECandidate.Solver.Wave8Leaves.S04
