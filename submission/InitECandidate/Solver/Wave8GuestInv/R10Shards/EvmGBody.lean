import InitECandidate.Solver.Wave8GuestInv.FrameGlue
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07

/-! Guarded composition proofs for `op_dispatch` and `finish_child` over R11,
importing `ContractParts.C07` (before `C08`..`C16`) so zero `sorry` exists in the
dependency cone unless an unproved leaf is explicitly referenced. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.EvmGBody

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `gbody_op_dispatch` -/

structure DispatchWalk (p : ProgHOL 64) (k : Nat) : Prop where
  bound : TerminatingProgBoundedOn EvmRun p k
  keeps : Hoare EvmRun p (fun r t => r = none → EvmRun t)

private theorem seq_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  cases r with
  | none => exact return_ne_none t e
  | some _ => simp

theorem DispatchWalk.skip : DispatchWalk .skip 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_skip s), Hoare.skip (fun _ hi _ => hi)⟩

theorem DispatchWalk.returned (e : ExpHOL 64) : DispatchWalk (.return e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_return s e),
    ⟨fun s _ _ _ hn => (return_ne_none s e hn).elim⟩⟩

theorem DispatchWalk.raise (n : MlS) (e : ExpHOL 64) : DispatchWalk (.raise n e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_raise s n e),
    ⟨fun s _ _ _ hn => (raise_ne_none s n e hn).elim⟩⟩

theorem DispatchWalk.callReturn {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {b : Nat} (hf : TerminatingFunBoundedOn Pc fname b)
    (args : List (ExpHOL 64)) (e : ExpHOL 64) (hentry : CallEntryOn EvmRun Pc fname args) :
    DispatchWalk (.seq (.call (some (none, none)) fname args) (.return e)) (b + 1) := by
  refine ⟨?_, ⟨fun s _ _ _ hn => (seq_return_ne_none s _ e hn).elim⟩⟩
  have hb : TerminatingProgBoundedOn EvmRun _ _ := TerminatingProgBoundedOn.seq_guestInv_after
    (TerminatingProgBoundedOn.call_on hf none args hentry)
    (fun s hi => evmInv_guestInv s hi.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s e))
  intro F s hc hi
  simpa only [Nat.add_zero] using hb s hc hi

theorem DispatchWalk.seq {p q : ProgHOL 64} {a b : Nat}
    (h1 : DispatchWalk p a) (h2 : DispatchWalk q b) : DispatchWalk (.seq p q) (a + b) :=
  ⟨TerminatingProgBoundedOn.seq_hoare h1.bound h1.keeps h2.bound,
   Hoare.seq ⟨fun s hc hi hnt => ⟨h1.keeps.run s hc hi hnt, fun hn hz => (hn hz).elim⟩⟩ h2.keeps⟩

theorem DispatchWalk.ite (c : ExpHOL 64) {p q : ProgHOL 64} {a b : Nat}
    (h1 : DispatchWalk p a) (h2 : DispatchWalk q b) : DispatchWalk (.ite c p q) (max a b) :=
  ⟨TerminatingProgBoundedOn.ite_on h1.bound h2.bound,
    Hoare.ite (Hoare.mono h1.keeps (fun _ h => h.1))
      (Hoare.mono h2.keeps (fun _ h => h.1)) (fun _ _ h => by cases h)⟩

theorem dispatchEntry_guest (f : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn EvmRun GuestInv f args :=
  callEntryOn_of_imp localsFree_guestInv (fun s hi => evmInv_guestInv s hi.1) f args

theorem dispatchEntry_run (f : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn EvmRun EvmRun f args :=
  callEntryOn_of_localsFree localsFree_evmRun f args

theorem lookup_op_dispatch : originalRuntimeCode.lookup (ofString "op_dispatch") =
    some ((sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 577 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_dispatch) rfl

def GBodyOpDispatch : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.«op_create2») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.«op_dup») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.«op_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.«op_gaslimit») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.«op_swap») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.«op_swapn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.«op_timestamp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.«op_xor») →
  TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch»

theorem gbody_op_dispatch : GBodyOpDispatch := by
  intro h_op_add h_op_addmod h_op_address h_op_and h_op_balance h_op_basefee h_op_blobbasefee h_op_blobhash h_op_blockhash h_op_byte h_op_call h_op_callcode h_op_calldatacopy h_op_calldataload h_op_calldatasize h_op_caller h_op_callvalue h_op_chainid h_op_clz h_op_codecopy h_op_codesize h_op_coinbase h_op_create h_op_create2 h_op_delegatecall h_op_div h_op_dup h_op_dupn h_op_eq h_op_exchange h_op_exp h_op_extcodecopy h_op_extcodehash h_op_extcodesize h_op_gas h_op_gaslimit h_op_gasprice h_op_gt h_op_iszero h_op_jump h_op_jumpdest h_op_jumpi h_op_keccak h_op_log h_op_lt h_op_mcopy h_op_mload h_op_mod h_op_msize h_op_mstore h_op_mstore8 h_op_mul h_op_mulmod h_op_not h_op_number h_op_or h_op_origin h_op_pc h_op_pop h_op_prevrandao h_op_push h_op_return h_op_returndatacopy h_op_returndatasize h_op_revert h_op_sar h_op_sdiv h_op_selfbalance h_op_selfdestruct h_op_sgt h_op_shl h_op_shr h_op_signextend h_op_sload h_op_slotnum h_op_slt h_op_smod h_op_sstore h_op_staticcall h_op_stop h_op_sub h_op_swap h_op_swapn h_op_timestamp h_op_tload h_op_tstore h_op_xor
  refine ⟨_, _, _, lookup_op_dispatch, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_op_dispatch,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply TerminatingProgBoundedOn.mono_bound
  · exact DispatchWalk.bound (
      (DispatchWalk.seq
        (DispatchWalk.ite _
          (DispatchWalk.seq
            (DispatchWalk.ite _
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_stop _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_add _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mul _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sub _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_div _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sdiv _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mod _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_smod _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_addmod _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mulmod _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_exp _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_signextend _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip))))))))))))
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_lt _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_gt _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_slt _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sgt _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_eq _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_iszero _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_and _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_or _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_xor _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_not _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_byte _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_shl _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_shr _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sar _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_clz _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip))))))))))))))))
            (DispatchWalk.raise _ _))
          DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _
          (DispatchWalk.seq
            (DispatchWalk.ite _
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_keccak _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_address _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_balance _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_origin _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_caller _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_callvalue _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_calldataload _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_calldatasize _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_calldatacopy _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_codesize _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_codecopy _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_gasprice _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_extcodesize _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_extcodecopy _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_returndatasize _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_returndatacopy _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_extcodehash _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)))))))))))))))))
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_blockhash _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_coinbase _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_timestamp _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_number _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_prevrandao _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_gaslimit _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_chainid _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_selfbalance _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_basefee _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_blobhash _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_blobbasefee _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_slotnum _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_pop _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mload _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mstore _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mstore8 _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sload _ _ (dispatchEntry_run _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_sstore _ _ (dispatchEntry_run _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_jump _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_jumpi _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_pc _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_msize _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_gas _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_jumpdest _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_tload _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_tstore _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
              (DispatchWalk.seq
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_mcopy _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
                (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_push _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)))))))))))))))))))))))))))))
            (DispatchWalk.raise _ _))
          DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _
          (DispatchWalk.seq
            (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_push _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
          (DispatchWalk.seq
            (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_dup _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
            (DispatchWalk.callReturn h_op_swap _ _ (dispatchEntry_guest _ _))))
          DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_log _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_dupn _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_swapn _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_exchange _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_create _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_call _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_callcode _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_return _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_delegatecall _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_create2 _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_staticcall _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_revert _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.ite _ (DispatchWalk.callReturn h_op_selfdestruct _ _ (dispatchEntry_guest _ _)) DispatchWalk.skip)
      (DispatchWalk.seq
        (DispatchWalk.raise _ _)
        (DispatchWalk.returned _)))))))))))))))))))
  · simp only [K.«op_dispatch», show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl,
      Nat.add_assoc, Nat.add_zero]
    exact Nat.le_refl _

/-! ## 2. `gbody_run_frames` -/

section RunFramesProof

private def rfCharge (f : MlS) : Nat :=
  if f = ofString "op_dispatch" then K.op_dispatch else
  if f = ofString "finish_child" then K.finish_child else
  if f = ofString "frame_epilogue" then K.frame_epilogue else
  if f = ofString "frame_exception" then K.frame_exception else 0

private theorem rfCharge_op_dispatch : rfCharge (ofString "op_dispatch") = K.op_dispatch := by
  simp only [rfCharge, ↓reduceIte]

private theorem rfCharge_finish_child : rfCharge (ofString "finish_child") = K.finish_child := by
  simp only [rfCharge, if_neg (show ofString "finish_child" ≠ ofString "op_dispatch" from by decide), ↓reduceIte]

private theorem rfCharge_frame_epilogue : rfCharge (ofString "frame_epilogue") = K.frame_epilogue := by
  simp only [rfCharge, if_neg (show ofString "frame_epilogue" ≠ ofString "op_dispatch" from by decide),
    if_neg (show ofString "frame_epilogue" ≠ ofString "finish_child" from by decide), ↓reduceIte]

private theorem rfCharge_frame_exception : rfCharge (ofString "frame_exception") = K.frame_exception := by
  simp only [rfCharge, if_neg (show ofString "frame_exception" ≠ ofString "op_dispatch" from by decide),
    if_neg (show ofString "frame_exception" ≠ ofString "finish_child" from by decide),
    if_neg (show ofString "frame_exception" ≠ ofString "frame_epilogue" from by decide), ↓reduceIte]

private def rfWalkCost : ProgHOL 64 → Nat
  | .seq a b => rfWalkCost a + rfWalkCost b
  | .ite _ a b => max (rfWalkCost a) (rfWalkCost b)
  | .dec _ _ _ b => rfWalkCost b
  | .call (some (_, some (_, _, h))) f _ => (rfCharge f + 1) + rfWalkCost h
  | .call _ f _ => rfCharge f + 1
  | _ => 0

private structure BHoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop where
  hoare : Hoare P prog Q
  bounded : TerminatingProgBoundedOn P prog (rfWalkCost prog)

private theorem BHoare.of_bound {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (hb : TerminatingProgBoundedOn P prog (rfWalkCost prog)) (h : Hoare P prog Q) :
    BHoare P prog Q := ⟨h, hb⟩

private theorem BHoare.skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    BHoare P .skip Q :=
  ⟨Hoare.skip h, TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)⟩

private theorem BHoare.seq {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : BHoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : BHoare R second Q) : BHoare P (.seq first second) Q := by
  refine ⟨Hoare.seq h1.hoare h2.hoare, ?_⟩
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    have hp := h1.hoare.run state hcode hP hnt1
    rw [hr1] at hp
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    obtain ⟨s2, k2⟩ := h2.bounded mid (hmeta.1.trans hcode) (hp.1 rfl) hnt
    exact ⟨by change state.clock ≤ _ + (rfWalkCost first + rfWalkCost second); dsimp only at s1 k1; omega,
      by dsimp only at k1; omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1.bounded state hcode hP hnt1
    rw [hr1] at s1 k1
    exact ⟨by change state.clock ≤ _ + (rfWalkCost first + rfWalkCost second); dsimp only at s1; omega, k1⟩

private theorem BHoare.ite {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : BHoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : BHoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.ite cond yes no) Q :=
  ⟨Hoare.ite hyes.hoare hno.hoare herr,
    TerminatingProgBoundedOn.ite_cond_on hyes.bounded hno.bounded⟩

private theorem BHoare.dec {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : BHoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.dec name shape init body) Q := by
  refine ⟨Hoare.dec hname hinit hbody.hoare hQ herr, ?_⟩
  intro F state hcode hPs hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val hv _
      have hb := hbody.bounded (setVarHOLFinite name val state) hcode (hinit state val hPs hv) hnt
      simpa only [setVarHOLFinite, rfWalkCost] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

private theorem BHoare.assign {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    BHoare P (.assign kind name source) Q :=
  ⟨Hoare.assign h herr, TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)⟩

private def rfCond : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)
private def rfCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_run_frames).2.2.1
private def rfBody : ProgHOL 64 :=
  match rfCode with
  | .dec _ _ _ (.seq (.while _ b) _) => b
  | _ => .skip

private theorem rfCode_eq : rfCode = .dec (ofString "go") .one (.const 1)
    (.seq (.while rfCond rfBody) (.return (.const 0))) := rfl

private theorem rfCost_eq : rfWalkCost rfBody =
    max 0 (max 0 (max 0 ((K.op_dispatch + 1) + (K.frame_exception + 1)))) +
      max ((K.frame_epilogue + 1) + max 0 ((K.finish_child + 1) + (K.frame_exception + 1))) 0 := rfl

private def rfFirst : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq a _) => a
  | _ => .skip

private def rfSecond : ProgHOL 64 :=
  match rfBody with
  | .dec _ _ _ (.seq _ b) => b
  | _ => .skip

private theorem rfBody_eq : rfBody = .dec (ofString "done") .one (.const 0)
    (.seq rfFirst rfSecond) := rfl

private theorem rf_firstwalk
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.op_dispatch)
    (h1 : type_of% @op_dispatch_spec)
    (h2 : type_of% @frame_exception_spec)
    (p0 R0 L0 F0 : Nat)
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0) :
    BHoare (GP1 p0 R0 L0 F0) rfFirst (GA p0 R0 L0 F0) := by
  simp only [rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
  · refine BHoare.assign (fun t v hP hv => ?_)
      (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
    cases evalAt_const t 1 v hv
    refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
    · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
        (evmInv_setVar _ _ hP.1.1.1) hP.1.1
    · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
      have := condTrue_ne0 hP.2
      exact Or.inl (by simpa using this)
    · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
      rw [locN_setVar_same]; decide
  · refine BHoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
    · refine BHoare.assign (fun t v hP hv => ?_)
        (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
      cases evalAt_const t 1 v hv
      refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
      · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
          (evmInv_setVar _ _ hP.1.1.1.1) hP.1.1.1
      · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
        have := condTrue_eq0 hP.2
        exact Or.inr (Or.inl (by simpa using this))
      · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
        rw [locN_setVar_same]; decide
    · refine BHoare.dec (names := ["go", "done"]) (P' := GPpc p0 R0 L0 F0) (by decide) ?_ ?_
        (ga_postLocals p0 R0 L0 F0)
        (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
      · intro F t v hP hv
        obtain ⟨⟨hP1, hc1⟩, hc2⟩ := hP
        obtain ⟨a, rfl, ha⟩ := evalAt_loadG t "ev" 0 v hv
        refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
          (evmInv_setVar _ _ hP1.1.1) hP1.1, ?_, ?_, ?_, ?_⟩
        · rw [locN_setVar_ne t "done" (ofString "pc") _ (by decide)]; exact hP1.2
        · show memW t (globN t "cur_cont" + 32) = 0
          have := condFalse_ne0 hc1; simpa using this
        · show memW t (globN t "ev" + 104) ≠ 0
          have := condFalse_eq0 hc2; simpa using this
        · rw [locN_setVar_same]
          show a.toNat = memW t (globN t "ev")
          simpa using ha
      · refine BHoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
        · refine BHoare.assign (fun t v hP hv => ?_)
            (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          cases evalAt_const t 1 v hv
          obtain ⟨⟨hpre, _, _, _, hpc⟩, w, hw, hne⟩ := hP
          refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
          · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t)
              rfl rfl (evmInv_setVar _ _ hpre.1) hpre
          · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
            have := (cond_notLower hw).1 hne
            refine Or.inr (Or.inr ?_)
            rw [← hpc]; simpa using this
          · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
            rw [locN_setVar_same]; decide
        · refine BHoare.dec (names := ["go", "done"]) (P' := GPdisp p0 R0 L0 F0) (by decide)
            ?_ ?_ (ga_postLocals p0 R0 L0 F0)
            (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          · intro F t v hP hv
            cases evalAt_const t 0 v hv
            obtain ⟨⟨hpre, hdone, hc1, hc2, hpc⟩, hc3⟩ := hP
            have hlt := (cond_notLower hc3).2 rfl
            have hnd : ¬ EvmDone t := by
              rintro (h | h | h)
              · exact h hc1
              · exact hc2 h
              · rw [← hpc] at h; simp at hlt; omega
            refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
              (evmInv_setVar _ _ hpre.1) hpre, ?_, ?_, ?_⟩
            · rw [locN_setVar_ne t "done" (ofString "err") _ (by decide)]; exact hdone
            · exact fun h => hnd ((evmDone_congr (s := t) (t := setVarHOLFinite _ _ t)
                rfl rfl).1 h)
            · rw [← hpre.2.2.2.2, ← hpre.2.2.2.1, evmFp_notDone hnd]
          · refine BHoare.of_bound ?_ ?_
            · have hb : TerminatingProgBoundedOn (GPdisp p0 R0 L0 F0) _ _ :=
                TerminatingProgBoundedOn.callHandle_on bd
                  (fun t hP => evmInv_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err")
                  (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err"))])
                  [.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48]),
                    .var .local (ofString "pc")])]
                  (P := GPdisp p0 R0 L0 F0)
                  (by
                    intro F t values body callee ret _ hP _ _
                    exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
                      ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩)
              intro F u hc hi
              simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
                rfCharge_frame_epilogue, rfCharge_frame_exception,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
            refine Hoare.callH (Pc := fun s => EvmInv s ∧ ¬ EvmDone s) (Ph := GPh R0 L0 F0)
              h1 ?_ ?_ ?_ ?_ (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
            · intro F t values body callee ret _ hP _ _
              exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
                ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hlt⟩ := hq.1 ⟨v, rfl⟩
              refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.1⟩, fun h => absurd rfl h⟩
              rw [(evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).1]
              rw [(evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1,
                hP.1.2.1] at hlt
              exact hlt
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hlen, hR⟩ := hq.2 ⟨v, rfl⟩
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
              obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                (t := setVarHOLFinite (ofString "err") v { post with locals := t.locals }) rfl rfl
              refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, ?_, hP.2.2.2⟩
              · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
              · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
              · rw [locN_setVar_ne _ "done" (ofString "err") _ (by decide)]; exact hP.2.1
            · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_
                (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
              · intro F t values body callee ret _ hP _ _
                exact evmInv_entry callee hP.1
              · intro F u callee post v _ hP hq
                obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u) (t := callEntryStateHOLFinite u callee) rfl rfl
                obtain ⟨fp, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := u.locals }) rfl rfl
                refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.2.2.1⟩, fun h => absurd rfl h⟩
                apply hfin _ (evmInv_locals _ hi)
                · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                · rw [fF, evmFp_done hd, hlen, eL, hP.2.1, hP.2.2.2.2]; omega

private theorem rf_secondwalk
    (bf : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (h2 : type_of% @frame_exception_spec)
    (h3 : type_of% @frame_epilogue_spec)
    (h4 : type_of% @finish_child_spec)
    (p0 R0 L0 F0 : Nat)
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0) :
    BHoare (GMid p0 R0 L0 F0) rfSecond (GQ p0) := by
  simp only [rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
  · refine BHoare.seq (R := GPdone p0 R0 L0 F0)
      (BHoare.skip fun t hP => ⟨fun _ => ?_, fun h => absurd rfl h⟩) ?_
    · rcases hP.1 with ⟨hp, hd, _⟩ | ⟨_, _, hz⟩
      · exact ⟨hp, hd⟩
      · exact absurd hz (condTrue_local_ne0 hP.2)
    refine BHoare.seq (R := GPepi R0 L0 F0) ?_ ?_
    · refine BHoare.of_bound ?_ ?_
      · have hb : TerminatingProgBoundedOn (GPdone p0 R0 L0 F0) _ _ := TerminatingProgBoundedOn.call_on be none []
          (P := GPdone p0 R0 L0 F0)
          (by
            intro F t values body callee ret _ hP _ _
            exact guestInv_callEntry t callee (evmInv_guestInv t hP.1.1))
        intro F u hc hi
        simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
          rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
          rfCharge_frame_epilogue, rfCharge_frame_exception] using hb u hc hi
      refine Hoare.call0 (Pc := fun s => EvmInv s ∧ EvmDone s) h3 ?_ ?_
        (fun r t h h' => ⟨fun hr => absurd hr h, fun _ => gq_other p0 r t h h'⟩)
      · intro F t values body callee ret _ hP _ _
        exact ⟨evmInv_entry callee hP.1.1,
          (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2 hP.2⟩
      · intro F t callee post v _ hP hq
        obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
        obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl
        refine ⟨fun _ => ⟨evmInv_locals _ hi,
          (evmDone_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).2 hd,
          ?_, ?_, ?_⟩, fun h => absurd rfl h⟩
        · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
        · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
        · rw [← hP.1.2.2.2.2, evmFp_done hP.2, hP.1.2.2.2.1]
    · refine BHoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
      · refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp) (by simp)⟩)) ?_
        refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp) (by simp)⟩)) ?_
        refine BHoare.assign (fun t v _ hv => ?_) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        cases evalAt_const t 0 v hv
        intro _; right
        show locN (setVarHOLFinite (ofString "go") (.val (.word 0)) t) "go" = 0
        rw [locN_setVar_same]; rfl
      · refine BHoare.dec (names := ["go"]) (P' := GPfin R0 L0 F0) (by decide) ?_ ?_
          (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        · intro F t v hP hv
          cases evalAt_const t 0 v hv
          obtain ⟨⟨hi, hd, hlen, hR, hF⟩, hk⟩ := hP
          obtain ⟨-, fR, fL, -⟩ := evm_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl
          refine ⟨⟨evmInv_setVar _ _ hi,
            (evmDone_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl).2 hd,
            fL.trans hlen, (le_of_eq fR).trans hR, hF⟩, ?_⟩
          show memW t (globN t "cur_cont" + 16) ≠ 0
          have := condFalse_eq0 hk; simpa using this
        · refine BHoare.of_bound ?_ ?_
          · have hb : TerminatingProgBoundedOn (GPfin R0 L0 F0) _ _ := TerminatingProgBoundedOn.callHandle_on bf
              (fun t hP => evmInv_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err2")
              (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err2"))]) []
              (P := GPfin R0 L0 F0)
              (by
                intro F t values body callee ret _ hP _ _
                exact ⟨evmInv_entry callee hP.1.1,
                  (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                    hP.1.2.1, hP.2⟩)
            intro F u hc hi
            simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
              rfWalkCost, rfCharge_op_dispatch, rfCharge_finish_child,
              rfCharge_frame_epilogue, rfCharge_frame_exception,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
          refine Hoare.callH
            (Pc := fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
            (Ph := GPh4 R0 L0 F0) h4 ?_ ?_ ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
          · intro F t values body callee ret _ hP _ _
            exact ⟨evmInv_entry callee hP.1.1,
              (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                hP.1.2.1, hP.2⟩
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inl ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
            obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl
            intro _; left
            refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
            · rw [fF]
              have h1 := evmFp_le post
              have h2 := hP.1.2.2.2.2
              rw [eL, hP.1.2.2.1] at hlen; omega
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inr ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
            obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
              (t := setVarHOLFinite (ofString "err2") v { post with locals := t.locals }) rfl rfl
            refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, hP.1.2.2.2.2⟩
            · rw [fL, hlen, eL]; exact hP.1.2.2.1
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
          · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
            · intro F t values body callee ret _ hP _ _
              exact evmInv_entry callee hP.1
            · intro F u callee post v _ hP hq
              obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u) (t := callEntryStateHOLFinite u callee) rfl rfl
              obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post) (t := { post with locals := u.locals }) rfl rfl
              intro _; left
              refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
              · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
              · rw [fF, evmFp_done hd, hlen, eL]
                have := hP.2.1; have := hP.2.2.2; omega
  · refine BHoare.skip (fun t hP => fun _ => ?_)
    rcases hP.1 with ⟨_, _, hn⟩ | ⟨hi, hp, _⟩
    · exact absurd (condFalse_local_ne0 hP.2) hn
    · exact Or.inl ⟨hi, hp⟩

private theorem rf_body_walk
    (bf : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.op_dispatch)
    (h1 : type_of% @op_dispatch_spec)
    (h2 : type_of% @frame_exception_spec)
    (h3 : type_of% @frame_epilogue_spec)
    (h4 : type_of% @finish_child_spec) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      BHoare (GPre (evmPot s) (evmR s) (evmChain s).length (evmFp s)) rfBody (GQ (evmPot s)) := by
  intro F s
  set p0 := evmPot s
  set R0 := evmR s
  set L0 := (evmChain s).length
  set F0 := evmFp s
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0 := fun t ht hR hF =>
    lt_of_lt_of_le (evmPot_lt_bound t ht hR hF) (evmPot_ge s)
  rw [rfBody_eq]
  refine BHoare.dec (names := ["go"]) (P' := GP1 p0 R0 L0 F0) (by decide) ?_ ?_
    (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
  · intro F t v hP hv
    cases evalAt_const t 0 v hv
    refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
      (evmInv_setVar _ _ hP.1) hP, ?_⟩
    rw [locN_setVar_same]; rfl
  · exact BHoare.seq
      (rf_firstwalk bx bd h1 h2 p0 R0 L0 F0 hfin)
      (rf_secondwalk bf be bx h2 h3 h4 p0 R0 L0 F0 hfin)

private theorem rf_sum_pair_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum ≤
      l.length * (2 * (2 ^ 64 - 1))
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + 64)
    have h2 := memW_lt s (x.1 + 192)
    have hi := rf_sum_pair_le s xs
    omega

private theorem rf_potential_bounded {F : Type} (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s) :
    evmPot s < evmPotMax := by
  have hlen := evmInv_len s hi
  have hR : evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) :=
    (rf_sum_pair_le s (evmChain s)).trans (Nat.mul_le_mul_right _ hlen)
  have hcap : evmR s ≤ 2 * Wave8GuestInv.maxChain * 2 ^ 64 := by
    have : 2 * (2 ^ 64 - 1) ≤ 2 * 2 ^ 64 := by omega
    calc evmR s ≤ Wave8GuestInv.maxChain * (2 * (2 ^ 64 - 1)) := hR
      _ ≤ Wave8GuestInv.maxChain * (2 * 2 ^ 64) := Nat.mul_le_mul_left _ this
      _ = 2 * Wave8GuestInv.maxChain * 2 ^ 64 := by omega
  have hp := evmPot_lt_bound s hi hcap (evmFp_lt s hi)
  have hcap_alg : ∀ a b c : Nat, a * (b * c) + b * c = (a + 1) * b * c := fun a b c => by
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  exact lt_of_lt_of_eq hp (hcap_alg (2 * Wave8GuestInv.maxChain * 2 ^ 64) evmPotF evmPotS)

private def rfHeadInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ (EvmInv s ∨ locN s "go" = 0)

private def rfRank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => if locN s "go" = 0 then 0 else evmPot s + 1

private theorem rf_active_ne {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ha : LoopActive rfCond s) : locN s "go" ≠ 0 :=
  condTrue_local_ne0 ha

private theorem rf_active_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hi : rfHeadInv s) (ha : LoopActive rfCond s) : EvmInv s := by
  rcases hi.2 with hi | hz
  · exact hi
  · exact (rf_active_ne ha hz).elim

def GBodyRunFrames : Prop :=
  (TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.«finish_child») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch») →
  (type_of% @finish_child_spec) →
  (type_of% @frame_epilogue_spec) →
  (type_of% @frame_exception_spec) →
  (type_of% @op_dispatch_spec) →
  TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.«run_frames»

theorem gbody_run_frames : GBodyRunFrames := by
  intro bf be bx bd hf he hx hd
  have hb : TerminatingProgBoundedOn (fun s => rfHeadInv s ∧ LoopActive rfCond s)
      rfBody (rfWalkCost rfBody) := by
    intro F s hc hi
    exact (rf_body_walk bf be bx bd hd hx he hf s).bounded s hc
      ⟨rf_active_inv hi.1 hi.2, rfl, rfl, rfl, rfl⟩
  have hl : TerminatingProgBoundedOn rfHeadInv (.while rfCond rfBody)
      ((evmPotMax + 1) * (rfWalkCost rfBody + 1)) := by
    refine TerminatingProgBoundedOn.while_rank_stationary_active (P := rfHeadInv) (N := evmPotMax) rfRank ?_ hb ?_ ?_
    · intro F s hi
      exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hi.1,
        hi.2.elim (fun h => Or.inl (localsFree_evmInv s _ _ h)) (fun h => Or.inr h)⟩
    · intro F s _ hi ha
      have hp := rf_potential_bounded s (rf_active_inv hi ha)
      simp only [rfRank, if_neg (rf_active_ne ha)]
      omega
    · intro F s hc hi ha hflow
      have hnt : (evaluateHOLFiniteState (decClockHOLFinite s) rfBody).1 ≠ some .timeOut := by
        rcases hflow with h | h <;> rw [h] <;> simp
      have hpre : GPre (evmPot s) (evmR s) (evmChain s).length (evmFp s) (decClockHOLFinite s) := by
        obtain ⟨e1, e2, e3, e4⟩ := evm_congr (s := s) (t := decClockHOLFinite s) rfl rfl
        exact ⟨localsFree_evmInv s s.locals (s.clock - 1) (rf_active_inv hi ha), e1, e2, e3, e4⟩
      have hs := (rf_body_walk bf be bx bd hd hx he hf s).hoare.run (decClockHOLFinite s) hc hpre hnt hflow
      have hg := guestInv_evaluate (decClockHOLFinite s) rfBody
        (guestInv_congr (s := s) rfl rfl rfl rfl hi.1)
      rcases hs with ⟨hpost, hp⟩ | hz
      · refine ⟨⟨hg, Or.inl hpost⟩, Or.inl ?_⟩
        simp only [rfRank, if_neg (rf_active_ne ha)]
        split <;> omega
      · refine ⟨⟨hg, Or.inr hz⟩, Or.inl ?_⟩
        simp only [rfRank, if_pos hz, if_neg (rf_active_ne ha)]
        omega
  have hseq : TerminatingProgBoundedOn rfHeadInv _ _ := TerminatingProgBoundedOn.seq_guestInv_after hl (fun _ hi => hi.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const 0)))
  have hseq' : TerminatingProgBoundedOn EvmInv
      (.seq (.while rfCond rfBody) (.return (.const 0)))
      ((evmPotMax + 1) * (rfWalkCost rfBody + 1)) := by
    intro F s hc hi
    simpa only [Nat.add_zero] using hseq s hc ⟨evmInv_guestInv s hi, Or.inl hi⟩
  refine ⟨[], rfCode, .one, lookup_run_frames, ?_⟩
  rw [rfCode_eq]
  have hb0 : TerminatingProgBoundedOn EvmInv _ _ := TerminatingProgBoundedOn.dec_on localsFree_evmInv
    (ofString "go") .one (.const 1) hseq'
  intro F u hc hi
  simpa only [K.run_frames, rfCost_eq] using hb0 u hc hi

end RunFramesProof

end InitECandidate.Solver.Wave8GuestInv.EvmGBody
