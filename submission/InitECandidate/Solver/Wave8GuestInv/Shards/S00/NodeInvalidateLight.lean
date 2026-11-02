import InitECandidate.Solver.PanTerminatingBounded

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00Light
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound

theorem fb_node_invalidate
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
      originalRuntimeCode.lookup (ofString "node_invalidate") =
        some (params, body, retShape) ∧ TerminatingProgBoundedOn P body 0 := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_node_invalidate) rfl, ?_⟩
  exact fun s hc _ => TerminatingProgBounded.straight _ rfl s hc

end InitECandidate.Solver.Wave8Leaves.S00Light
