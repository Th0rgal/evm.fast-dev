import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.DispatchWalk
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.RunFramesRace

/-- Child 0/1 selects the first/second sequential or conditional branch. -/
def binaryAt : List Nat → ProgHOL 64 → ProgHOL 64
  | [], p => p
  | i :: rest, .seq a b => binaryAt rest (if i = 0 then a else b)
  | i :: rest, .ite _ a b => binaryAt rest (if i = 0 then a else b)
  | _, _ => .skip

/-- Replace the continuation after n sequential statements, retaining lexical syntax. -/
def seqCut : Nat → ProgHOL 64 → ProgHOL 64 → ProgHOL 64
  | 0, _, tail => tail
  | n+1, .seq a b, tail => .seq a (seqCut n b tail)
  | _, p, _ => p

def dispatchCode : ProgHOL 64 :=
  (sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2.2.1
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


theorem lookup_op_dispatch : originalRuntimeCode.lookup (ofString "op_dispatch") =
    some ((sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 577 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_dispatch) rfl


def dispatchGroup01 : ProgHOL 64 :=
  binaryAt [0, 0, 0, 0] dispatchCode

def dispatchCost01 : Nat := ((max (K.op_stop + 1) 0) + ((max (K.op_add + 1) 0) + ((max (K.op_mul + 1) 0) + ((max (K.op_sub + 1) 0) + ((max (K.op_div + 1) 0) + ((max (K.op_sdiv + 1) 0) + ((max (K.op_mod + 1) 0) + ((max (K.op_smod + 1) 0) + ((max (K.op_addmod + 1) 0) + ((max (K.op_mulmod + 1) 0) + ((max (K.op_exp + 1) 0) + (max (K.op_signextend + 1) 0))))))))))))

def dispatchGroup02 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 6 (binaryAt [0, 0, 0, 1] dispatchCode) tail

def dispatchCost02 (b : Nat) : Nat := ((max (K.op_lt + 1) 0) + ((max (K.op_gt + 1) 0) + ((max (K.op_slt + 1) 0) + ((max (K.op_sgt + 1) 0) + ((max (K.op_eq + 1) 0) + ((max (K.op_iszero + 1) 0) + b))))))

def dispatchGroup03 : ProgHOL 64 :=
  binaryAt [0, 0, 0, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchCost03 : Nat := ((max (K.op_and + 1) 0) + ((max (K.op_or + 1) 0) + ((max (K.op_xor + 1) 0) + ((max (K.op_not + 1) 0) + ((max (K.op_byte + 1) 0) + ((max (K.op_shl + 1) 0) + ((max (K.op_shr + 1) 0) + ((max (K.op_sar + 1) 0) + (max (K.op_clz + 1) 0)))))))))

def dispatchGroup04 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 9 (binaryAt [1, 0, 0, 0, 0] dispatchCode) tail

def dispatchCost04 (b : Nat) : Nat := ((max (K.op_keccak + 1) 0) + ((max (K.op_address + 1) 0) + ((max (K.op_balance + 1) 0) + ((max (K.op_origin + 1) 0) + ((max (K.op_caller + 1) 0) + ((max (K.op_callvalue + 1) 0) + ((max (K.op_calldataload + 1) 0) + ((max (K.op_calldatasize + 1) 0) + ((max (K.op_calldatacopy + 1) 0) + b)))))))))

def dispatchGroup05 : ProgHOL 64 :=
  binaryAt [1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchCost05 : Nat := ((max (K.op_codesize + 1) 0) + ((max (K.op_codecopy + 1) 0) + ((max (K.op_gasprice + 1) 0) + ((max (K.op_extcodesize + 1) 0) + ((max (K.op_extcodecopy + 1) 0) + ((max (K.op_returndatasize + 1) 0) + ((max (K.op_returndatacopy + 1) 0) + (max (K.op_extcodehash + 1) 0))))))))

def dispatchGroup06 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 12 (binaryAt [1, 0, 0, 0, 1] dispatchCode) tail

def dispatchCost06 (b : Nat) : Nat := ((max (K.op_blockhash + 1) 0) + ((max (K.op_coinbase + 1) 0) + ((max (K.op_timestamp + 1) 0) + ((max (K.op_number + 1) 0) + ((max (K.op_prevrandao + 1) 0) + ((max (K.op_gaslimit + 1) 0) + ((max (K.op_chainid + 1) 0) + ((max (K.op_selfbalance + 1) 0) + ((max (K.op_basefee + 1) 0) + ((max (K.op_blobhash + 1) 0) + ((max (K.op_blobbasefee + 1) 0) + ((max (K.op_slotnum + 1) 0) + b))))))))))))

def dispatchGroup07 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 6 (binaryAt [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode) tail

def dispatchCost07 (b : Nat) : Nat := ((max (K.op_pop + 1) 0) + ((max (K.op_mload + 1) 0) + ((max (K.op_mstore + 1) 0) + ((max (K.op_mstore8 + 1) 0) + ((max (K.op_sload + 1) 0) + ((max (K.op_sstore + 1) 0) + b))))))

def dispatchGroup08 : ProgHOL 64 :=
  binaryAt [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchCost08 : Nat := ((max (K.op_jump + 1) 0) + ((max (K.op_jumpi + 1) 0) + ((max (K.op_pc + 1) 0) + ((max (K.op_msize + 1) 0) + ((max (K.op_gas + 1) 0) + ((max (K.op_jumpdest + 1) 0) + ((max (K.op_tload + 1) 0) + ((max (K.op_tstore + 1) 0) + ((max (K.op_mcopy + 1) 0) + (max (K.op_push + 1) 0))))))))))

def dispatchGroup09 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 1 (binaryAt [1, 1] dispatchCode) tail

def dispatchCost09 (b : Nat) : Nat := ((max ((max (K.op_push + 1) 0) + ((max (K.op_dup + 1) 0) + (K.op_swap + 1))) 0) + b)

def dispatchGroup10 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 4 (binaryAt [1, 1, 1] dispatchCode) tail

def dispatchCost10 (b : Nat) : Nat := ((max (K.op_log + 1) 0) + ((max (K.op_dupn + 1) 0) + ((max (K.op_swapn + 1) 0) + ((max (K.op_exchange + 1) 0) + b))))

def dispatchGroup11 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 7 (binaryAt [1, 1, 1, 1, 1, 1, 1] dispatchCode) tail

def dispatchCost11 (b : Nat) : Nat := ((max (K.op_create + 1) 0) + ((max (K.op_call + 1) 0) + ((max (K.op_callcode + 1) 0) + ((max (K.op_return + 1) 0) + ((max (K.op_delegatecall + 1) 0) + ((max (K.op_create2 + 1) 0) + ((max (K.op_staticcall + 1) 0) + b)))))))

def dispatchGroup12 : ProgHOL 64 :=
  binaryAt [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchCost12 : Nat := ((max (K.op_revert + 1) 0) + ((max (K.op_selfdestruct + 1) 0) + (0 + 0)))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
