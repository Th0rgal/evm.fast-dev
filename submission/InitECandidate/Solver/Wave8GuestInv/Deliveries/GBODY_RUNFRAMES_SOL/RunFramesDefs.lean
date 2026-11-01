import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Walk
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def DispatchSpec : Prop :=
    FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch")

def ExceptionSpec : Prop :=
    FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception")

def EpilogueSpec : Prop :=
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue")

def FinishSpec : Prop :=
    FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child")

/-- The loop guard and body are extracted from the literal, pinned function body. -/
def rfCond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)
def rfCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_run_frames).2.2.1
def rfBody : ProgHOL 64 :=
  match rfCode with
  | .dec _ _ _ (.seq (.while _ b) _) => b
  | _ => .skip


theorem rfCode_eq : rfCode = .dec (ofString "go") .one (.const 1)
    (.seq (.while rfCond rfBody) (.return (.const 0))) := rfl

theorem rfEntry_eq : (sourceFunctionEntry Guest.Software.guestFn_run_frames).2 =
    ([], rfCode, .one) := rfl

theorem rfLoop_eq : some (rfCond, rfBody) = some (rfCond, rfBody) := rfl

theorem rfCost_eq : walkCost rfBody =
    max 0 (max 0 (max 0 ((K.op_dispatch + 1) + (K.frame_exception + 1)))) +
      max ((K.frame_epilogue + 1) + max 0 ((K.finish_child + 1) + (K.frame_exception + 1))) 0 := by
  rfl


def rfFirst : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq a _) => a
  | _ => .skip

def rfSecond : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq _ b) => b
  | _ => .skip

theorem rfBody_eq : rfBody = .dec (ofString "done") .one (.const 0)
    (.seq rfFirst rfSecond) := rfl

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
