import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxContracts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def ptxCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn_process_transaction).2.2.1

attribute [irreducible] ptxCode

def spineAt : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n+1, .seq _ b => spineAt n b
  | n+1, .dec _ _ _ b => spineAt n b
  | n+1, .decCall _ _ _ _ b => spineAt n b
  | _, p => p

def spinePlug : Nat → ProgHOL 64 → ProgHOL 64 → ProgHOL 64
  | 0, _, tail => tail
  | n+1, .seq a b, tail => .seq a (spinePlug n b tail)
  | n+1, .dec x sh e b, tail => .dec x sh e (spinePlug n b tail)
  | n+1, .decCall x sh f args b, tail => .decCall x sh f args (spinePlug n b tail)
  | _, p, _ => p

def ptxCharge (f : MlS) : Nat :=
  if f = ofString "alloc" then K.«alloc» else
  if f = ofString "calculate_blob_gas_price" then K.«calculate_blob_gas_price» else
  if f = ofString "calculate_total_blob_gas" then K.«calculate_total_blob_gas» else
  if f = ofString "check_transaction" then K.«check_transaction» else
  if f = ofString "clear_account_preserving_balance" then K.«clear_account_preserving_balance» else
  if f = ofString "compute_contract_address" then K.«compute_contract_address» else
  if f = ofString "create_ether" then K.«create_ether» else
  if f = ofString "encode_receipt" then K.«encode_receipt» else
  if f = ofString "encode_transaction" then K.«encode_transaction» else
  if f = ofString "fee_mul" then K.«fee_mul» else
  if f = ofString "frame_mem_release" then K.«frame_mem_release» else
  if f = ofString "get_account" then K.«get_account» else
  if f = ofString "htab_item" then K.«htab_item» else
  if f = ofString "htab_new" then K.«htab_new» else
  if f = ofString "htab_set" then K.«htab_set» else
  if f = ofString "incorporate_tx_into_block" then K.«incorporate_tx_into_block» else
  if f = ofString "increment_nonce" then K.«increment_nonce» else
  if f = ofString "keccak256" then K.«keccak256» else
  if f = ofString "lst_new" then K.«lst_new» else
  if f = ofString "lst_push" then K.«lst_push» else
  if f = ofString "max" then K.«max» else
  if f = ofString "memcpy" then K.«memcpy» else
  if f = ofString "min" then K.«min» else
  if f = ofString "msg_new" then K.«msg_new» else
  if f = ofString "process_message_call" then K.«process_message_call» else
  if f = ofString "recover_sender_with_chain_id" then K.«recover_sender_with_chain_id» else
  if f = ofString "scratch_release" then K.«scratch_release» else
  if f = ofString "set_account_balance" then K.«set_account_balance» else
  if f = ofString "state_fresh_tx" then K.«state_fresh_tx» else
  if f = ofString "te_new" then K.«te_new» else
  if f = ofString "tx_chain_id" then K.«tx_chain_id» else
  if f = ofString "tx_has_access_list" then K.«tx_has_access_list» else
  if f = ofString "tx_is_blob" then K.«tx_is_blob» else
  if f = ofString "tx_is_setcode" then K.«tx_is_setcode» else
  if f = ofString "u256_sub" then K.«u256_sub» else
  if f = ofString "udiv_small5" then K.«udiv_small5» else
  if f = ofString "validate_transaction" then K.«validate_transaction» else
  0

def ptxCost : ProgHOL 64 → Nat
  | .seq a b => ptxCost a + ptxCost b
  | .ite _ a b => max (ptxCost a) (ptxCost b)
  | .dec _ _ _ b => ptxCost b
  | .decCall _ _ f _ b => ptxCharge f + 1 + ptxCost b
  | .call _ f _ => ptxCharge f + 1
  | .while _ b => (2 ^ 64 + 1) * (ptxCost b + 1)
  | _ => 0

def ptxPhase1 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 34 ptxCode tail
def ptxCost1 : Nat := (K.«state_fresh_tx» + 1) + (K.«encode_transaction» + 1) + (K.«tx_chain_id» + 1) + (K.«alloc» + 1) + (K.«recover_sender_with_chain_id» + 1) + (K.«validate_transaction» + 1) + (K.«check_transaction» + 1) + (K.«calculate_total_blob_gas» + 1) + (K.«get_account» + 1) + Nat.max ((K.«calculate_blob_gas_price» + 1) + (K.«fee_mul» + 1)) (0) + (K.«fee_mul» + 1) + (K.«min» + 1) + (K.«increment_nonce» + 1) + (K.«u256_sub» + 1) + (K.«u256_sub» + 1) + (K.«set_account_balance» + 1)

def ptxPhase2 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 64 (spineAt 34 ptxCode) tail
def ptxCost2 : Nat := (K.«te_new» + 1) + (K.«tx_has_access_list» + 1) + (K.«alloc» + 1) + (2 ^ 64 + 1) * (0 + 1) + (K.«alloc» + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1) + (K.«tx_is_blob» + 1) + (K.«tx_is_setcode» + 1) + (K.«alloc» + 1) + (K.«keccak256» + 1) + (K.«msg_new» + 1) + (K.«htab_new» + 1) + (K.«htab_set» + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (K.«htab_new» + 1) + (2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1) + (K.«alloc» + 1) + Nat.max ((K.«get_account» + 1) + (K.«alloc» + 1) + (K.«compute_contract_address» + 1)) (0) + (K.«htab_set» + 1)

def ptxPhase3 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 1 (spineAt 98 ptxCode) tail
def ptxCost3 : Nat := (K.«process_message_call» + 1)

def ptxPhase4 (tail : ProgHOL 64) : ProgHOL 64 := spinePlug 40 (spineAt 99 ptxCode) tail
def ptxCost4 : Nat := (K.«udiv_small5» + 1) + (K.«min» + 1) + (K.«max» + 1) + (K.«fee_mul» + 1) + (K.«u256_sub» + 1) + (K.«fee_mul» + 1) + (K.«create_ether» + 1) + (K.«create_ether» + 1) + (K.«max» + 1) + Nat.max ((K.«lst_new» + 1)) (0) + (K.«encode_receipt» + 1) + (2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1) + (K.«lst_new» + 1) + (2 ^ 64 + 1) * (0 + 1) + (K.«lst_push» + 1)

def ptxPhase5 : ProgHOL 64 := spineAt 139 ptxCode
def ptxCost5 : Nat := Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) + Nat.max ((K.«clear_account_preserving_balance» + 1)) (0) + 1)) (0) + (K.«incorporate_tx_into_block» + 1) + Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) (0)

theorem spineAt_add (n m : Nat) (p : ProgHOL 64) :
    spineAt (n + m) p = spineAt m (spineAt n p) := by
  induction n generalizing p m with
  | zero => simp only [Nat.zero_add, spineAt]
  | succ n ih =>
    cases p <;> try { cases m <;> rfl }
    all_goals simpa only [Nat.succ_add, spineAt] using ih m _

theorem spinePlug_restore (n : Nat) (p : ProgHOL 64) :
    spinePlug n p (spineAt n p) = p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => cases p <;> simp_all [spinePlug, spineAt]

theorem spinePlug_restore_at (n m : Nat) (p : ProgHOL 64) :
    spinePlug m (spineAt n p) (spineAt (n + m) p) = spineAt n p := by
  rw [spineAt_add, spinePlug_restore]

theorem spine_restore_four (p : ProgHOL 64) : p =
    spinePlug 34 p (spinePlug 64 (spineAt 34 p)
      (spinePlug 1 (spineAt 98 p) (spinePlug 40 (spineAt 99 p) (spineAt 139 p)))) := by
  have h4 := spinePlug_restore_at 99 40 p
  have h3 := spinePlug_restore_at 98 1 p
  have h2 := spinePlug_restore_at 34 64 p
  rw [h4, h3, h2]
  exact (spinePlug_restore 34 p).symm

theorem ptx_phases_eq : ptxCode = ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))) := by
  simpa only [ptxPhase1, ptxPhase2, ptxPhase3, ptxPhase4, ptxPhase5] using spine_restore_four ptxCode

theorem ptx_cost_algebra (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 : Nat) :
    (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15) + ((x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35) + ((x36) + ((x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51) + ((x52 + x53 + x54))))) =
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25 + x26 + x27 + x28 + x29 + x30 + x31 + x32 + x33 + x34 + x35 + x36 + x37 + x38 + x39 + x40 + x41 + x42 + x43 + x44 + x45 + x46 + x47 + x48 + x49 + x50 + x51 + x52 + x53 + x54 := by omega

theorem ptx_cost_eq : ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5))) = K.process_transaction := by
  exact ptx_cost_algebra ((K.«state_fresh_tx» + 1)) ((K.«encode_transaction» + 1)) ((K.«tx_chain_id» + 1)) ((K.«alloc» + 1)) ((K.«recover_sender_with_chain_id» + 1)) ((K.«validate_transaction» + 1)) ((K.«check_transaction» + 1)) ((K.«calculate_total_blob_gas» + 1)) ((K.«get_account» + 1)) (Nat.max ((K.«calculate_blob_gas_price» + 1) + (K.«fee_mul» + 1)) (0)) ((K.«fee_mul» + 1)) ((K.«min» + 1)) ((K.«increment_nonce» + 1)) ((K.«u256_sub» + 1)) ((K.«u256_sub» + 1)) ((K.«set_account_balance» + 1)) ((K.«te_new» + 1)) ((K.«tx_has_access_list» + 1)) ((K.«alloc» + 1)) ((2 ^ 64 + 1) * (0 + 1)) ((K.«alloc» + 1)) ((2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((K.«memcpy» + 1) + (K.«memcpy» + 1) + 1) + 1)) ((K.«tx_is_blob» + 1)) ((K.«tx_is_setcode» + 1)) ((K.«alloc» + 1)) ((K.«keccak256» + 1)) ((K.«msg_new» + 1)) ((K.«htab_new» + 1)) ((K.«htab_set» + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((K.«htab_new» + 1)) ((2 ^ 64 + 1) * ((K.«htab_set» + 1) + 1)) ((K.«alloc» + 1)) (Nat.max ((K.«get_account» + 1) + (K.«alloc» + 1) + (K.«compute_contract_address» + 1)) (0)) ((K.«htab_set» + 1)) ((K.«process_message_call» + 1)) ((K.«udiv_small5» + 1)) ((K.«min» + 1)) ((K.«max» + 1)) ((K.«fee_mul» + 1)) ((K.«u256_sub» + 1)) ((K.«fee_mul» + 1)) ((K.«create_ether» + 1)) ((K.«create_ether» + 1)) ((K.«max» + 1)) (Nat.max ((K.«lst_new» + 1)) (0)) ((K.«encode_receipt» + 1)) ((2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1)) ((K.«lst_new» + 1)) ((2 ^ 64 + 1) * (0 + 1)) ((K.«lst_push» + 1)) (Nat.max ((2 ^ 64 + 1) * ((K.«htab_item» + 1) + Nat.max ((K.«clear_account_preserving_balance» + 1)) (0) + 1)) (0)) ((K.«incorporate_tx_into_block» + 1)) (Nat.max ((K.«scratch_release» + 1) + (K.«frame_mem_release» + 1)) (0))

theorem ptx_lookup : originalRuntimeCode.lookup (ofString "process_transaction") =
    some ((sourceFunctionEntry Guest.Software.guestFn_process_transaction).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 873 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_transaction) rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
