import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitE.SourceNameFacts
import InitE.SourceMainFacts
import InitECandidate.Solver.CompactComputation
import InitECandidate.Solver.FrontendCodecComputation
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestFrameMemKeep

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

def badFrameMem : List MlS :=
  ([
    "attempt_l1", "attempt_l2", "attempt_l3", "attempt_l4", "attempt_l5", "attempt_l6", "attempt_l7",
    "charge_with_memory", "copy_from_buffer", "execute_block", "extend_memory", "finish_child",
    "frame_mem_alloc", "frame_mem_release", "frame_new", "frame_open",
    "generic_call", "generic_create", "main", "mem_init",
    "op_call", "op_callcode", "op_calldatacopy", "op_codecopy", "op_create", "op_create2",
    "op_delegatecall", "op_dispatch", "op_extcodecopy", "op_keccak", "op_log", "op_mcopy",
    "op_mload", "op_mstore", "op_mstore8", "op_return", "op_returndatacopy", "op_revert",
    "op_staticcall", "process_checked_system_transaction", "process_create_message",
    "process_general_purpose_requests", "process_message", "process_message_call",
    "process_transaction", "process_unchecked_system_transaction",
    "run_attempt", "run_frames", "start_child", "verify_stateless_new_payload"
  ] : List String).map ofString

def goodFrameMem (f : MlS) : Bool := !(badFrameMem.contains f)

def keepsG (watched : MlS) (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => keepsG watched good body
  | .seq first second => keepsG watched good first && keepsG watched good second
  | .ite _ yes no => keepsG watched good yes && keepsG watched good no
  | .while _ body => keepsG watched good body
  | .assign .global name _ => !(name == watched)
  | .assign .local _ _ => true
  | .store _ _ | .store32 _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ => true
  | .decCall _ _ function _ continuation => good function && keepsG watched good continuation
  | .call none function _ => good function
  | .call (some (none, none)) function _ => good function
  | .call (some (some (.local, _), none)) function _ => good function
  | .call (some (some (.global, name), none)) function _ => good function && !(name == watched)
  | .call (some (none, some (_, _, handler))) function _ => good function && keepsG watched good handler
  | .call (some (some (.local, _), some (_, _, handler))) function _ => good function && keepsG watched good handler
  | .call (some (some (.global, name), some (_, _, handler))) function _ =>
      good function && !(name == watched) && keepsG watched good handler
  | .primitive _ _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .shMemLoad _ .global name _ => !(name == watched)
  | .shMemStore _ _ _ => true
  | .tick => true

theorem program_check_frame_mem_ptr :
    (functionsHOL sourceDeclarations).all
      (fun entry => !(goodFrameMem entry.1) || keepsG (ofString "frame_mem_ptr") goodFrameMem entry.2.2.1) = true := by
  unfold sourceDeclarations
  rw [InitECandidate.Solver.FrontendCodecComputation.declToHOL_function_eq]
  kernel_rfl

end InitECandidate.Solver.GuestFrameMemKeep
