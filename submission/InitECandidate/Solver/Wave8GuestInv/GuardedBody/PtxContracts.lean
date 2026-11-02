import InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10Views
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
def TxAccessListOK {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  let tx := locN s "tx"
  let nal := memW s (tx + 216)
  let recs := memW s (tx + 208)
  tx % 8 = 0 ∧ Inside (tx, 384) sourceBase (globN s "heap_ptr") ∧
  (∀ o ∈ worldOwned s S Nd, Disj (tx, 384) o) ∧
  (memW s tx ≠ 0 →
    nal < 2 ^ 32 ∧
    (0 < nal → recs % 8 = 0 ∧ Inside (recs, 24 * nal) sourceBase (globN s "heap_ptr") ∧
      ∀ o ∈ worldOwned s S Nd, Disj (recs, 24 * nal) o) ∧
    ((List.range nal).map (fun i => memW s (recs + 24 * i + 16))).sum < 2 ^ 32)


/-- Bounds needed by transaction encoding, in addition to access-list ownership.
The decoded transaction and its referenced slices are heap inputs. -/
def TxValid {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  let tx := locN s "tx"
  WordsOK s (tx, 384) ∧ memW s tx ≤ 4 ∧
  memW s (tx + 200) < 2 ^ 32 ∧ memW s (tx + 264) < 2 ^ 32 ∧
  memW s (tx + 280) < 2 ^ 32 ∧
  Inside (memW s (tx + 192), memW s (tx + 200)) 0 heapLimit

def TxReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReady s ∧ TxValid s ∧ globN s "journal_cap" ≠ 0 ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧ memW s (globN s "bo" + 72) ≠ 0 ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListOK s S Nd


/-- One decoded log: a 40-byte record, at most four topics, bounded data. -/
def LogEntryOK {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) : Prop :=
  WordsOK s (p, 40) ∧ Allocated s (p, 40) ∧
  memW s (p + 16) ≤ 4 ∧ memW s (p + 32) < 2 ^ 32 ∧
  Allocated s (memW s p, 20) ∧
  Allocated s (memW s (p + 8), 32 * memW s (p + 16)) ∧
  Allocated s (memW s (p + 24), memW s (p + 32))

/-- The null log list is replaced by lst_new before receipt encoding. -/
def LogsListOK {F : Type} (s : PanSemStateFiniteExact 64 F) (logs : Nat) : Prop :=
  logs = 0 ∨
    WordsOK s (logs, 24) ∧ Allocated s (logs, 24) ∧
    memW s (logs + 8) < 2 ^ 28 ∧
    WordsOK s (memW s logs, 8 * memW s (logs + 8)) ∧
    Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧
    ∀ i, i < memW s (logs + 8) → LogEntryOK s (memW s (memW s logs + 8 * i))

/-- Receipt slices and the still-live input log list are non-wrapping. -/
def RetReceiptBounded : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) →
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] ∧
      Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr") ∧
      memW post (locN s "logs" + 8) < 2 ^ 28 ∧ LogsListOK post (locN s "logs")

def RetMessageLogs : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun _ r post => ∀ v, r = some (.returned v) →
    ∃ out : BitVec 64, v = .val (.word out) ∧ WordsOK post (out.toNat, 96) ∧
      LogsListOK post (memW post (out.toNat + 16))

structure TxEnv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  bo_nz : globN s "bo" ≠ 0
  bo24 : memW s (globN s "bo" + 24) ≠ 0
  bo32 : memW s (globN s "bo" + 32) ≠ 0
  bo40 : memW s (globN s "bo" + 40) ≠ 0
  bo72 : memW s (globN s "bo" + 72) ≠ 0
  idx_lt : locN s "index" < memW s (globN s "bo" + 80)
  jcap_nz : globN s "journal_cap" ≠ 0

def TxWorld : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ TxEnv s

def PtxValidated : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReadyStrong s ∧
    Inside (locN s "sender", 24) sourceBase (globN s "heap_ptr") ∧
    WordsOK s (locN s "sender", 24) ∧ locN s "mgas" ≤ 16777216

def PtxMessageReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧
    MsgReady (setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s)

def PtxMessageDone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ WordsOK s (locN s "out", 96) ∧
    LogsListOK s (memW s (locN s "out" + 16))

/-- Logs have been copied into block lists before any scratch release in phase 5. -/
def PtxReceiptsDone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ LogsListOK s (locN s "stable_logs") ∧
    memW s (locN s "stable_logs" + 8) < 2 ^ 28

/-- Direct callee assumptions; R10 contracts are hypotheses, never imported proofs. -/
structure PtxCallees : Prop where
  fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»
  fb_calculate_blob_gas_price : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price»
  fb_calculate_total_blob_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas»
  fb_check_transaction : TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction»
  fb_clear_account_preserving_balance : TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance»
  fb_compute_contract_address : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address»
  fb_create_ether : TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether»
  fb_encode_receipt : TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt»
  fb_encode_transaction : TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction»
  fb_fee_mul : TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul»
  fb_frame_mem_release : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release»
  fb_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»
  fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»
  fb_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»
  fb_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»
  gb_incorporate_tx_into_block : TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block»
  fb_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»
  fb_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»
  fb_lst_new : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new»
  fb_lst_push : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push»
  fb_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»
  fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»
  fb_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min»
  fb_msg_new : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»
  gb_process_message_call : TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»
  fb_recover_sender_with_chain_id : TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id»
  fb_scratch_release : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release»
  fb_set_account_balance : TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance»
  fb_state_fresh_tx : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»
  fb_te_new : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new»
  fb_tx_chain_id : TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id»
  fb_tx_has_access_list : TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list»
  fb_tx_is_blob : TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob»
  fb_tx_is_setcode : TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode»
  fb_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»
  fb_udiv_small5 : TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5»
  fb_validate_transaction : TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction»
  wk_alloc : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc")
  rt_alloc : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
    (ofString "alloc")
  wk_calculate_blob_gas_price : WorldKeeps WorldOK (fun s => [(globN s "u256_ws", 640)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "calculate_blob_gas_price")
  ro_calculate_total_blob_gas : ReadOnlyFn (ofString "calculate_total_blob_gas")
  wk_check_transaction : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "sk_buf", 64), (globN s "u256_ws", 640)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "check_transaction")
  wk_clear_account_preserving_balance : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "sk_buf", 64)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "clear_account_preserving_balance")
  wk_compute_contract_address : WorldKeeps WorldOK (fun s => [(locN s "out", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "compute_contract_address")
  wk_create_ether : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "sk_buf", 64)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "create_ether")
  wk_encode_receipt : WorldKeeps (fun s => WorldOK s ∧ LogsListOK s (locN s "logs") ∧ locN s "logs" ≠ 0) (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_receipt")
  wk_encode_transaction : WorldKeeps (fun s => WorldOK s ∧ TxValid s) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction")
  ro_fee_mul : ReadOnlyFn (ofString "fee_mul")
  wk_get_account : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "get_account")
  ro_htab_item : ReadOnlyFn (ofString "htab_item")
  htab_new_spec : FunSpec HtabNewReady HtabNewExit (ofString "htab_new")
  htab_set_spec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")
  wk_increment_nonce : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "sk_buf", 64)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "increment_nonce")
  wk_keccak256 : WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "keccak256")
  wk_lst_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
      (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new")
  rt_lst_new : Returns ArenaReady (fun s post l =>
      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
    (ofString "lst_new")
  wk_lst_push : WorldKeeps BoListArg (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlot (ofString "lst_push")
  ro_max : ReadOnlyFn (ofString "max")
  wk_memcpy : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memcpy")
  dm_memcpy : ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy")
  ro_min : ReadOnlyFn (ofString "min")
  rv_min : RetLe (fun s => locN s "a") (ofString "min")
  wk_msg_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new")
  rt_msg_new : Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0)
    (ofString "msg_new")
  wk_process_message_call : WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) (fun s => [(locN s "msg", 176), (globN s "b2_v", 128), (globN s "bn_expw", 352), (globN s "bn_gamma", 384), (globN s "evm_key_buf", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "pre_hdr_buf", 96), (globN s "rmd_h", 40), (globN s "rmd_pad", 128), (globN s "rmd_x", 128), (globN s "sha_pad", 128), (globN s "sha_st", 64), (globN s "sk_buf", 64), (globN s "u256_ws", 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "process_message_call")
  wk_recover_sender_with_chain_id : WorldKeeps WorldOK (fun s => [(locN s "out20", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "u256_ws", 640)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "recover_sender_with_chain_id")
  wk_set_account_balance : WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64), (globN s "sk_buf", 64)])
    ["heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "set_account_balance")
  wk_state_fresh_tx : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")
  wk_te_new : WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new")
  rt_te_new : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0)
    (ofString "te_new")
  ro_tx_chain_id : ReadOnlyFn (ofString "tx_chain_id")
  ro_tx_has_access_list : ReadOnlyFn (ofString "tx_has_access_list")
  ro_tx_is_blob : ReadOnlyFn (ofString "tx_is_blob")
  ro_tx_is_setcode : ReadOnlyFn (ofString "tx_is_setcode")
  ro_u256_sub : ReadOnlyFn (ofString "u256_sub")
  ro_udiv_small5 : ReadOnlyFn (ofString "udiv_small5")
  ro_validate_transaction : ReadOnlyFn (ofString "validate_transaction")
  rv_validate_transaction : RetIntrinsic (ofString "validate_transaction")
  message_logs : FunSpec MsgReady RetMessageLogs (ofString "process_message_call")
  receipt_bounded : FunSpec (fun s => WorldOK s ∧ LogsListOK s (locN s "logs") ∧ locN s "logs" ≠ 0)
    RetReceiptBounded (ofString "encode_receipt")

def GBodyProcessTransaction : Prop :=
  PtxCallees → TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.process_transaction

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
