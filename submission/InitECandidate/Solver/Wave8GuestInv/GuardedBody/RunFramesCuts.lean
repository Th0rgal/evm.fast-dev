import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.RunFramesDefs
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

open InitECandidate.Solver.Wave8GuestInv.RunFramesRace

/-- The dispatch call and its EvmErr handler, inside the active-frame branch. -/
def rfDispatch : ProgHOL 64 :=
  match rfFirst with
  | .ite _ _ (.ite _ _ (.dec _ _ _ (.ite _ _ (.dec _ _ _ p)))) => p
  | _ => .skip

def rfParentCond : ExpHOL 64 :=
  .cmp .equal (.load .one (.op .add [.var .global (ofString "cur_cont"), .const 16])) (.const 0)

def rfExit : ProgHOL 64 :=
  match rfSecond with
  | .ite _ (.seq _ (.seq _ (.ite _ p _))) _ => p
  | _ => .skip

def rfPop : ProgHOL 64 :=
  match rfSecond with
  | .ite _ (.seq _ (.seq _ (.ite _ _ p))) _ => p
  | _ => .skip

/-- Restoring caller locals after a normal opcode return, including child-push returns.
The dispatch specification supplies the strict potential decrease for both cases. -/
def DispatchReturnCut (p0 R0 L0 F0 : Nat) : Prop :=
  ∀ {F : Type} (t : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F),
    GPdisp p0 R0 L0 F0 t → EvmInv post →
    evmPot post < evmPot (callEntryStateHOLFinite t callee) →
    GA p0 R0 L0 F0 none { post with locals := t.locals }

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
