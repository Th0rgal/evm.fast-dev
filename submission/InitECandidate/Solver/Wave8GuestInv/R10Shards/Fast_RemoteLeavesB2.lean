import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

/-! Fast_RemoteLeavesB2:
- 5 S10 opcode/helper leaves (`fb_is_warm_storage_key`, `fb_op_sdiv`, `fb_op_selfbalance`,
  `fb_op_selfdestruct`, `fb_op_staticcall`), ported from `origin/wave8/leaves-s10` to R11
  `GuestInv` and `K.*` bounds, plus `_of` / helper-discharging wrappers.
- 4 small field arithmetic callee leaves (`fb_fe_add`, `fb_fe_sub`, `fb_fe_mul_small`,
  `fb_fq_mul_small`) and their loop-free callees (`fb_u256_add`, `fb_u256_sub`, `fb_fq_add`,
  `fb_fq_sub`), proved unconditionally under `GuestInv`.
Imports only `R10Shards.P13Callees`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees

/-! ### 1. S10 opcode and storage-warmness leaves + loop-free EVM/u256 helpers -/

theorem fb_sk_make : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make» := by
  have _ := fb_memcpy
  fb_prove 360 Guest.Software.guestFn_sk_make K.«sk_make»

theorem fb_is_warm_storage_key
    (h_sk_make : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make»)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key» := by
  fb_prove 525 Guest.Software.guestFn_is_warm_storage_key K.«is_warm_storage_key»

example : type_of% fb_is_warm_storage_key = (
    (TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») →
      TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key») := rfl

theorem fb_is_warm_storage_key_of
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key» :=
  fb_is_warm_storage_key fb_sk_make h_htab_has

theorem fb_u256_neg : TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» := by
  fb_prove 58 Guest.Software.guestFn_u256_neg K.«u256_neg»

theorem fb_u256_abs : TerminatingFunBoundedOn GuestInv (ofString "u256_abs") K.«u256_abs» := by
  have _ := fb_u256_neg
  fb_prove 72 Guest.Software.guestFn_u256_abs K.«u256_abs»

theorem fb_u256_div_of
    (h_u256_divmod : TerminatingFunBoundedOn GuestInv (ofString "u256_divmod") K.«u256_divmod») :
    TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div» := by
  fb_prove 70 Guest.Software.guestFn_u256_div K.«u256_div»

theorem fb_u256_sdiv_of
    (h_u256_div : TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div») :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv» := by
  have _ := fb_u256_abs
  have _ := fb_u256_neg
  fb_prove 73 Guest.Software.guestFn_u256_sdiv K.«u256_sdiv»

theorem fb_op_sdiv
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_sdiv : TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv» := by
  fb_prove 479 Guest.Software.guestFn_op_sdiv K.«op_sdiv»

example : type_of% fb_op_sdiv = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv») := rfl

theorem fb_op_sdiv_of
    (h_u256_sdiv : TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv») :
    TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv» :=
  fb_op_sdiv fb_stack_pop fb_charge_gas h_u256_sdiv fb_stack_push fb_pc_add

theorem fb_op_sdiv_of_divmod
    (h_u256_divmod : TerminatingFunBoundedOn GuestInv (ofString "u256_divmod") K.«u256_divmod») :
    TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv» :=
  fb_op_sdiv_of (fb_u256_sdiv_of (fb_u256_div_of h_u256_divmod))

theorem fb_op_selfbalance
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance» := by
  fb_prove 549 Guest.Software.guestFn_op_selfbalance K.«op_selfbalance»

example : type_of% fb_op_selfbalance = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance») := rfl

theorem fb_op_selfbalance_of
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account») :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance» :=
  fb_op_selfbalance fb_charge_gas h_get_account fb_stack_push fb_pc_add

theorem fb_to_address_masked :
    TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked» := by
  have _ := fb_st_be32
  have _ := fb_st_be64
  fb_prove 444 Guest.Software.guestFn_to_address_masked K.«to_address_masked»

theorem fb_charge_state_gas :
    TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas» := by
  have _ := fb_add_sat
  fb_prove 449 Guest.Software.guestFn_charge_state_gas K.«charge_state_gas»

theorem fb_emit_transfer_log :
    TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log» := by
  have _ := fb_u256_is_zero
  have _ := fb_alloc
  have _ := fb_memcpy
  have _ := fb_memzero
  have _ := fb_u256_to_be32
  have _ := fb_log_append
  fb_prove 567 Guest.Software.guestFn_emit_transfer_log K.«emit_transfer_log»

theorem fb_is_warm_address_of
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address» := by
  fb_prove 471 Guest.Software.guestFn_is_warm_address K.«is_warm_address»

theorem fb_warm_address_of
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address» := by
  fb_prove 472 Guest.Software.guestFn_warm_address K.«warm_address»

theorem fb_op_selfdestruct
    (h_require_not_static : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static»)
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_move_ether : TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_emit_transfer_log : TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log»)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct» := by
  fb_prove 570 Guest.Software.guestFn_op_selfdestruct K.«op_selfdestruct»

example : type_of% fb_op_selfdestruct = (
    (TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked») →
    (TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address») →
    (TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive») →
    (TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    (TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
      TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct») := rfl

theorem fb_op_selfdestruct_of
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_move_ether : TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct» :=
  fb_op_selfdestruct fb_require_not_static fb_stack_pop fb_to_address_masked
    (fb_is_warm_address_of h_htab_has) fb_charge_gas (fb_warm_address_of h_htab_set)
    h_is_account_alive h_get_account fb_u256_is_zero fb_charge_state_gas
    h_move_ether h_memeq fb_emit_transfer_log h_htab_has h_htab_set

theorem fb_is_valid_delegation :
    TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.«is_valid_delegation» := by
  fb_prove 446 Guest.Software.guestFn_is_valid_delegation K.«is_valid_delegation»

theorem fb_calculate_delegation_cost_of
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost» := by
  have _ := fb_is_valid_delegation
  have _ := fb_alloc
  have _ := fb_memcpy
  fb_prove 573 Guest.Software.guestFn_calculate_delegation_cost K.«calculate_delegation_cost»

theorem fb_calculate_message_call_gas :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas» := by
  have _ := fb_u256_is_zero
  have _ := fb_add_sat
  fb_prove 602 Guest.Software.guestFn_calculate_message_call_gas K.«calculate_message_call_gas»

theorem fb_op_staticcall
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_extend_memory_cost2 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost2") K.«extend_memory_cost2»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address»)
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    (h_calculate_delegation_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_calculate_message_call_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas»)
    (h_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory»)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall» := by
  fb_prove 606 Guest.Software.guestFn_op_staticcall K.«op_staticcall»

example : type_of% fb_op_staticcall = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked») →
    (TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost2") K.«extend_memory_cost2») →
    (TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address») →
    (TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address») →
    (TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost») →
    (TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of») →
    (TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory») →
    (TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall») := rfl

theorem fb_op_staticcall_of
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call») :
    TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall» :=
  fb_op_staticcall fb_stack_pop fb_to_address_masked fb_extend_memory_cost2
    (fb_is_warm_address_of h_htab_has) fb_add_sat fb_charge_gas (fb_warm_address_of h_htab_set)
    (fb_calculate_delegation_cost_of h_ext_code_of (fb_is_warm_address_of h_htab_has))
    h_ext_code_of fb_sat_word fb_calculate_message_call_gas fb_extend_memory
    h_generic_call fb_pc_add

/-! ### 2. Loop-free field callees (`fb_u256_add`, `fb_u256_sub`, `fb_fq_add`, `fb_fq_sub`) -/

theorem fb_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» := by
  fb_prove 56 Guest.Software.guestFn_u256_add K.«u256_add»

theorem fb_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» := by
  fb_prove 57 Guest.Software.guestFn_u256_sub K.«u256_sub»

theorem fb_fq_add : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add» := by
  have _ := fb_u256_add
  have _ := fb_u256_lt
  have _ := fb_u256_sub
  fb_prove 649 Guest.Software.guestFn_fq_add K.«fq_add»

theorem fb_fq_sub : TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.«fq_sub» := by
  have _ := fb_u256_lt
  have _ := fb_u256_sub
  have _ := fb_u256_add
  fb_prove 650 Guest.Software.guestFn_fq_sub K.«fq_sub»

/-! ### 3. `bit_length64` return-value bound (`≤ 64`) and `fb_fq_mul_small` -/

private def fnBodyHOL (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

private theorem lookup_bit_length64 :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], fnBodyHOL Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

private theorem lookupCode_one_word {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fn p1 : MlS} {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {v1 : ValueHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlookup : code fn = some ([(p1, .one)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1] =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ ∃ w1 : BitVec 64, locals.lookup p1 = some (.val (.word w1)) := by
  have hb := lookupCodeHOLFinite_installed_body code fn _ body foundBody rs foundRs
    [v1] locals hlookup hfound
  refine ⟨hb, ?_⟩
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    cases v1 with
    | val wl =>
      cases wl with
      | word w1 =>
        have hraw : lookupCodeHOLExact code fn [ValueHOL.val (HolWordLab.word w1)] =
            some (body,
              (fun current => if current = p1 then some (ValueHOL.val (HolWordLab.word w1)) else none),
              rs) := by
          simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL]
        rw [hraw] at raw
        cases raw
        cases hfound
        exact ⟨w1, by simp⟩
    | rStruct _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw
    | nStruct _ _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw

private theorem bit_length64_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (n x : BitVec 64) (hx : x.toNat < 2 ^ (2 * k.toNat))
    (hk_pos : 0 < k.toNat) (hk_le : k.toNat ≤ 32)
    (hn_le : n.toNat + 2 * k.toNat ≤ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hx_loc : s.locals.lookup (ofString "x") = some (.val (.word x))) :
    let stepProg : ProgHOL 64 :=
      .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
        (.seq
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
          (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
        .skip
    ∀ s', evaluateHOLFiniteState s stepProg = (none, s') →
      ∃ n' x',
        s'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
        s'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
        x'.toNat < 2 ^ k.toNat ∧
        n'.toNat + k.toNat ≤ 64 := by
  dsimp only
  intro s' hrun
  rw [evaluateHOLFiniteState_ite] at hrun
  have hk_not64 : ¬ (¬ k.toNat = 0 ∧ 64 ≤ k.toNat) := by omega
  have hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64)) =
      some (.val (.word (if x >>> k.toNat = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx_loc, Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hk_not64]
  rw [hcond] at hrun
  dsimp only at hrun
  by_cases hz : x >>> k.toNat = 0#64
  · rw [if_pos hz] at hrun
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos h0, evaluateHOLFiniteState_skip] at hrun
    cases hrun
    refine ⟨n, x, hn, hx_loc, ?_, by omega⟩
    have hzt := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hzt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hzt
    have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos k.toNat
    exact (Nat.div_eq_zero_iff_lt hpos).mp hzt
  · rw [if_neg hz] at hrun
    have hnot0 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    rw [if_neg hnot0] at hrun
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    have hasgn_n : evaluateHOLFiniteState s
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k])) =
        (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_n] at hrun
    dsimp only at hrun
    let s1 := setVarHOLFinite (ofString "n") (.val (.word (n + k))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (n + k))) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word x)) := by
      have hne : ofString "n" ≠ ofString "x" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx_loc]
    have hasgn_x : evaluateHOLFiniteState s1
        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))) =
        (none, setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat))) s1) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hs1_x, wordShiftHOL, hk_not64,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_x] at hrun
    cases hrun
    refine ⟨n + k, x >>> k.toNat, ?_, ?_, ?_, ?_⟩
    · have hne : ofString "x" ≠ ofString "n" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hpow] at hx
      exact Nat.div_lt_of_lt_mul hx
    · have hadd : (n + k).toNat = n.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
      omega

private theorem evaluate_bit_length64_le {F : Type}
    (state : PanSemStateFiniteExact 64 F) (x : BitVec 64)
    (hx : state.locals.lookup (ofString "x") = some (.val (.word x))) :
    ∀ w, (evaluateHOLFiniteState state (fnBodyHOL Guest.Software.guestFn_bit_length64)).1 =
      some (.returned w) →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 64 := by
  intro w hrun
  unfold fnBodyHOL at hrun
  dsimp only [extractFn, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_x : s0.locals.lookup (ofString "x") = some (.val (.word x)) := by
    have hne : ofString "n" ≠ ofString "x" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx]
  have hno_ret_step : ∀ (k : BitVec 64) (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
          (.seq
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
            (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
          .skip)).1 ≠ some (.returned w) := by
    intro k st hc
    rw [evaluateHOLFiniteState_ite] at hc
    split at hc
    · split at hc
      · rw [evaluateHOLFiniteState_skip] at hc; simp at hc
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hc
        split at hc
        · simp at hc
        · split at hc
          · dsimp only at hc
            rw [evaluateHOLFiniteState_assign] at hc
            split at hc
            · simp at hc
            · split at hc <;> simp at hc
          · simp at hc
    · simp at hc
  have hstep_seq : ∀ {p1 p2 : ProgHOL 64} {st : PanSemStateFiniteExact 64 F},
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = some (.returned w) →
      (evaluateHOLFiniteState st p1).1 ≠ some (.returned w) →
      ∃ sm, evaluateHOLFiniteState st p1 = (none, sm) ∧
        (evaluateHOLFiniteState sm p2).1 = some (.returned w) := by
    intro p1 p2 st hs hnr
    rw [evaluateHOLFiniteState_seq_line780] at hs
    rcases hr1 : evaluateHOLFiniteState st p1 with ⟨r1, sm⟩
    rw [hr1] at hs hnr
    cases r1 with
    | none => exact ⟨sm, rfl, hs⟩
    | some rv =>
      dsimp only at hs hnr
      exact False.elim (hnr hs)
  obtain ⟨s1, hr1, hrun⟩ := hstep_seq hrun (hno_ret_step 32#64 s0)
  obtain ⟨n1, x1, hn1, hx1, hxb1, hnb1⟩ := bit_length64_step s0 32#64 0#64 x
    (by change x.toNat < 2 ^ 64; exact x.isLt) (by decide) (by decide) (by decide) hs0_n hs0_x s1 hr1
  obtain ⟨s2, hr2, hrun⟩ := hstep_seq hrun (hno_ret_step 16#64 s1)
  obtain ⟨n2, x2, hn2, hx2, hxb2, hnb2⟩ := bit_length64_step s1 16#64 n1 x1
    hxb1 (by decide) (by decide) (by change n1.toNat + 32 ≤ 64; exact hnb1) hn1 hx1 s2 hr2
  obtain ⟨s3, hr3, hrun⟩ := hstep_seq hrun (hno_ret_step 8#64 s2)
  obtain ⟨n3, x3, hn3, hx3, hxb3, hnb3⟩ := bit_length64_step s2 8#64 n2 x2
    hxb2 (by decide) (by decide) (by change n2.toNat + 16 ≤ 64; exact hnb2) hn2 hx2 s3 hr3
  obtain ⟨s4, hr4, hrun⟩ := hstep_seq hrun (hno_ret_step 4#64 s3)
  obtain ⟨n4, x4, hn4, hx4, hxb4, hnb4⟩ := bit_length64_step s3 4#64 n3 x3
    hxb3 (by decide) (by decide) (by change n3.toNat + 8 ≤ 64; exact hnb3) hn3 hx3 s4 hr4
  obtain ⟨s5, hr5, hrun⟩ := hstep_seq hrun (hno_ret_step 2#64 s4)
  obtain ⟨n5, x5, hn5, hx5, hxb5, hnb5⟩ := bit_length64_step s4 2#64 n4 x4
    hxb4 (by decide) (by decide) (by change n4.toNat + 4 ≤ 64; exact hnb4) hn4 hx4 s5 hr5
  obtain ⟨s6, hr6, hrun⟩ := hstep_seq hrun (hno_ret_step 1#64 s5)
  obtain ⟨n6, x6, hn6, hx6, hxb6, hnb6⟩ := bit_length64_step s5 1#64 n5 x5
    hxb5 (by decide) (by decide) (by change n5.toNat + 2 ≤ 64; exact hnb5) hn5 hx5 s6 hr6
  rw [evaluateHOLFiniteState_return] at hrun
  have hev_ret : @evalHOLExact 64 F _ s6.toExact
      (fun a => Classical.propDecidable (s6.memaddrs a))
      (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
      some (.val (.word (n6 + x6))) := by
    simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev_ret] at hrun
  dsimp only at hrun
  split at hrun
  · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
    subst hrun
    refine ⟨n6 + x6, rfl, ?_⟩
    change x6.toNat < 2 ^ 1 at hxb6
    change n6.toNat + 1 ≤ 64 at hnb6
    have hadd : (n6 + x6).toNat = n6.toNat + x6.toNat := BitVec.toNat_add_of_lt (by omega)
    omega
  · simp at hrun

private theorem seq_to_guestInv' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmidG := guestInv_evaluate state first (hPG state hP)
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hmidG hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simp [hr1])
    rw [hr1] at s1 k1; dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmidG hnt
    exact ⟨by omega, by omega⟩
  | some _ =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simpa [hr1] using hnt)
    rw [hr1] at s1 k1; dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem fb_fq_mul_small_of
    (h_bit_length64 : TerminatingFunBoundedOn GuestInv (ofString "bit_length64") K.«bit_length64»)
    (h_fq_add : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add») :
    TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small» := by
  fb_unfold 656 Guest.Software.guestFn_fq_mul_small
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.decCall_on (Q := locCapInv "i" 64) h_bit_length64
    · intro F s _ _ callee _ _ hg _ _
      exact guestInv_callEntry s callee hg
    · intro F s values body' callee ret' value post hcode hg hargs hfound hrun
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases ha : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "k")) with _ | v1
      · rw [ha] at hargs; cases hargs
      · rw [ha] at hargs; cases hargs
        rw [hcode] at hfound
        obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word lookup_bit_length64 hfound
        obtain ⟨b, rfl, hble⟩ := evaluate_bit_length64_le (callEntryStateHOLFinite s callee)
          w1 hw1 value (by rw [hrun])
        have hpostG : GuestInv post := by
          have := guestInv_evaluate (callEntryStateHOLFinite s callee)
            (fnBodyHOL Guest.Software.guestFn_bit_length64) (guestInv_callEntry s callee hg)
          rw [hrun] at this; exact this
        refine ⟨guestInv_setVar _ _ _ (guestInv_with_locals_clock post s.locals post.clock hpostG), ?_⟩
        simpa [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hble
    · exact seq_to_guestInv' (fun _ h => h.1)
        (while_down_first_capped_on .lower (Or.inr rfl) "i" (C := 64)
          (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' h_fq_add)
            (TerminatingProgBoundedOn.ite_on (call_guestInv' h_fq_add) (straightOn _ rfl)))
          rfl)
        (straightOn _ rfl)
  · fb_arith K.«fq_mul_small»

theorem fb_fq_mul_small :
    TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small» :=
  fb_fq_mul_small_of fb_bit_length64 fb_fq_add

example : type_of% fb_fq_mul_small =
    TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small» := rfl

/-! ### 4. Stride-32 ordinary-domain memory walk (`fe_add`, `fe_sub`, `fe_mul_small`) -/

def scaledUpRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then heapEnd - a.toNat + 15 else 0

theorem scaledUpRank_bound (a : BitVec 64) : scaledUpRank a ≤ domainBytes + 16 := by
  unfold scaledUpRank domainBytes
  split_ifs <;> omega

theorem scaledUpRank_add32_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    scaledUpRank (a + BitVec.ofNat 64 32) < scaledUpRank a := by
  have hend : heapEnd + 32 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 32).toNat = a.toNat + 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold scaledUpRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega

def scaled32UpMu (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => scaledUpRank (b + i * 32)
  | _, _ => 0

theorem scaled32UpMu_le (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaled32UpMu base counter s ≤ domainBytes + 16 := by
  unfold scaled32UpMu
  split
  · exact scaledUpRank_bound _
  · omega

private theorem scaled32_locals_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const 32#64]]) =
      some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧ address = b + i * 32 := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | nStruct _ _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using h.symm

private theorem eval_load_comb4_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (val : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load (.comb [.one, .one, .one, .one]) addrExp) = some val) :
    ∃ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        addrExp = some (.val (.word addr)) ∧
      s.memaddrs addr := by
  simp only [evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL, Bool.and_true, ↓reduceIte] at h
  split at h
  · rename_i addr haddr
    refine ⟨addr, haddr, ?_⟩
    by_contra hnd
    simp [memLoadHOLExact, memLoadsHOLExact, hnd] at h
  · cases h

theorem DomainTouch.dec_load_comb4 (name : MlS) (addrExp : ExpHOL 64) (inner : ProgHOL 64) :
    DomainTouch addrExp (.dec name (.comb [.one, .one, .one, .one])
      (.load (.comb [.one, .one, .one, .one]) addrExp) inner) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp at hflow
  · rename_i val hval
    obtain ⟨addr, haddr, hdom⟩ := eval_load_comb4_domain s addrExp val hval
    rw [hguest.memaddrs] at hdom
    have hi := ordinaryDomain_interval addr hdom
    exact ⟨addr, haddr, hi.1, by omega⟩

theorem while_scaled32_walk_guestInv (base counter : MlS) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 32#64]]) body)
    (hadd : CounterStep counter 1#64 body)
    (hbase : avoidsLocal base body = true) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 16 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 16)
    (scaled32UpMu base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled32UpMu_le base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := scaled32_locals_inv (decClockHOLFinite s) base counter addr haddr
  have hipost := hadd (decClockHOLFinite s) i hi hflow
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  have heq : b + (i + 1#64) * 32 = (b + i * 32) + BitVec.ofNat 64 32 := by bv_omega
  simpa only [scaled32UpMu, hipost, hbpost', hb, hi, heq]
    using scaledUpRank_add32_lt (b + i * 32) ⟨hlow, hhigh⟩

theorem fb_fe_add_of
    (h_fq_add : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.«fe_add» := by
  fb_unfold 663 Guest.Software.guestFn_fe_add
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_scaled32_walk_guestInv (ofString "a") (ofString "i") _
        (dec_guestInv _ _ _ (dec_guestInv _ _ _ (decCall_guestInv' h_fq_add (straightOn _ rfl))))
        (DomainTouch.dec_load_comb4 _ _ _) (by counter_step) rfl
    · exact straightOn _ rfl
  · rw [domainBytes_eq]
    unfold K.«fe_add»
    generalize_K
    omega

theorem fb_fe_add : TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.«fe_add» :=
  fb_fe_add_of fb_fq_add

example : type_of% fb_fe_add =
    TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.«fe_add» := rfl

theorem fb_fe_sub_of
    (h_fq_sub : TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.«fq_sub») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub» := by
  fb_unfold 664 Guest.Software.guestFn_fe_sub
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_scaled32_walk_guestInv (ofString "a") (ofString "i") _
        (dec_guestInv _ _ _ (dec_guestInv _ _ _ (decCall_guestInv' h_fq_sub (straightOn _ rfl))))
        (DomainTouch.dec_load_comb4 _ _ _) (by counter_step) rfl
    · exact straightOn _ rfl
  · rw [domainBytes_eq]
    unfold K.«fe_sub»
    generalize_K
    omega

theorem fb_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub» :=
  fb_fe_sub_of fb_fq_sub

example : type_of% fb_fe_sub =
    TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub» := rfl

theorem fb_fe_mul_small_of
    (h_fq_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small» := by
  fb_unfold 666 Guest.Software.guestFn_fe_mul_small
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_scaled32_walk_guestInv (ofString "a") (ofString "i") _
        (dec_guestInv _ _ _ (decCall_guestInv' h_fq_mul_small (straightOn _ rfl)))
        (DomainTouch.dec_load_comb4 _ _ _) (by counter_step) rfl
    · exact straightOn _ rfl
  · rw [domainBytes_eq]
    unfold K.«fe_mul_small»
    generalize_K
    omega

theorem fb_fe_mul_small :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small» :=
  fb_fe_mul_small_of fb_fq_mul_small

example : type_of% fb_fe_mul_small =
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small» := rfl

end InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2
