import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Common

/-! Verified `fb_*` callee bounds for Shards P13, P12, and P15 (excluding `u256_mod`, proved in
`P13DivMod.lean`). Imports only `R10Shards.Common` (zero `LeafStatements.lean` dependency). -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

/-! ### 1. Zero-callee straight-line primitives -/

theorem fb_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» := by
  fb_prove 3 Guest.Software.guestFn_trap_with K.«trap_with»

theorem fb_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark» := by
  fb_prove 8 Guest.Software.guestFn_heap_mark K.«heap_mark»

theorem fb_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release» := by
  fb_prove 9 Guest.Software.guestFn_heap_release K.«heap_release»

theorem fb_bswap64 : TerminatingFunBoundedOn GuestInv (ofString "bswap64") K.«bswap64» := by
  fb_prove 23 Guest.Software.guestFn_bswap64 K.«bswap64»

theorem fb_st_be32 : TerminatingFunBoundedOn GuestInv (ofString "st_be32") K.«st_be32» := by
  fb_prove 27 Guest.Software.guestFn_st_be32 K.«st_be32»

theorem fb_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero» := by
  fb_prove 42 Guest.Software.guestFn_u256_is_zero K.«u256_is_zero»

theorem fb_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt» := by
  fb_prove 46 Guest.Software.guestFn_u256_lt K.«u256_lt»

theorem fb_mul64x64 : TerminatingFunBoundedOn GuestInv (ofString "mul64x64") K.«mul64x64» := by
  fb_prove 59 Guest.Software.guestFn_mul64x64 K.«mul64x64»

theorem fb_nlz32 : TerminatingFunBoundedOn GuestInv (ofString "nlz32") K.«nlz32» := by
  fb_prove 62 Guest.Software.guestFn_nlz32 K.«nlz32»

theorem fb_u256_to_digits : TerminatingFunBoundedOn GuestInv (ofString "u256_to_digits") K.«u256_to_digits» := by
  fb_prove 64 Guest.Software.guestFn_u256_to_digits K.«u256_to_digits»

theorem fb_digits_to_u256 : TerminatingFunBoundedOn GuestInv (ofString "digits_to_u256") K.«digits_to_u256» := by
  fb_prove 65 Guest.Software.guestFn_digits_to_u256 K.«digits_to_u256»

theorem fb_bit_length64 : TerminatingFunBoundedOn GuestInv (ofString "bit_length64") K.«bit_length64» := by
  fb_prove 77 Guest.Software.guestFn_bit_length64 K.«bit_length64»

theorem fb_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word» := by
  fb_prove 440 Guest.Software.guestFn_sat_word K.«sat_word»

theorem fb_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat» := by
  fb_prove 441 Guest.Software.guestFn_add_sat K.«add_sat»

theorem fb_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» := by
  fb_prove 448 Guest.Software.guestFn_charge_gas K.«charge_gas»

theorem fb_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» := by
  fb_prove 453 Guest.Software.guestFn_stack_pop K.«stack_pop»

theorem fb_is_valid_jumpdest : TerminatingFunBoundedOn GuestInv (ofString "is_valid_jumpdest") K.«is_valid_jumpdest» := by
  fb_prove 464 Guest.Software.guestFn_is_valid_jumpdest K.«is_valid_jumpdest»

theorem fb_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» := by
  fb_prove 468 Guest.Software.guestFn_pc_add K.«pc_add»

theorem fb_require_not_static : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static» := by
  fb_prove 470 Guest.Software.guestFn_require_not_static K.«require_not_static»

theorem fb_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» := by
  fb_prove 550 Guest.Software.guestFn_block_env K.«block_env»

/-! ### 2. Loop-free compound callees -/

theorem fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» := by
  have _ := fb_trap_with
  fb_prove 7 Guest.Software.guestFn_alloc K.«alloc»

theorem fb_frame_mem_alloc : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_alloc") K.«frame_mem_alloc» := by
  have _ := fb_trap_with
  fb_prove 10 Guest.Software.guestFn_frame_mem_alloc K.«frame_mem_alloc»

theorem fb_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc» := by
  have _ := fb_trap_with
  fb_prove 13 Guest.Software.guestFn_scratch_alloc K.«scratch_alloc»

theorem fb_st_be64 : TerminatingFunBoundedOn GuestInv (ofString "st_be64") K.«st_be64» := by
  have _ := fb_bswap64
  have _ := fb_st_be32
  fb_prove 28 Guest.Software.guestFn_st_be64 K.«st_be64»

theorem fb_u256_to_be32 : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32» := by
  have _ := fb_bswap64
  have _ := fb_st_be64
  fb_prove 87 Guest.Software.guestFn_u256_to_be32 K.«u256_to_be32»

theorem fb_u256_bit_length : TerminatingFunBoundedOn GuestInv (ofString "u256_bit_length") K.«u256_bit_length» := by
  have _ := fb_bit_length64
  fb_prove 78 Guest.Software.guestFn_u256_bit_length K.«u256_bit_length»

theorem fb_ceil32 : TerminatingFunBoundedOn GuestInv (ofString "ceil32") K.«ceil32» := by
  have _ := fb_add_sat
  fb_prove 442 Guest.Software.guestFn_ceil32 K.«ceil32»

theorem fb_words_of : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of» := by
  have _ := fb_ceil32
  fb_prove 443 Guest.Software.guestFn_words_of K.«words_of»

theorem fb_memory_gas_cost : TerminatingFunBoundedOn GuestInv (ofString "memory_gas_cost") K.«memory_gas_cost» := by
  have _ := fb_words_of
  have _ := fb_mul64x64
  have _ := fb_add_sat
  fb_prove 457 Guest.Software.guestFn_memory_gas_cost K.«memory_gas_cost»

theorem fb_extend_memory_cost1 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost1") K.«extend_memory_cost1» := by
  have _ := fb_u256_is_zero
  have _ := fb_sat_word
  have _ := fb_add_sat
  have _ := fb_ceil32
  have _ := fb_memory_gas_cost
  fb_prove 458 Guest.Software.guestFn_extend_memory_cost1 K.«extend_memory_cost1»

theorem fb_extend_memory_cost2 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost2") K.«extend_memory_cost2» := by
  have _ := fb_extend_memory_cost1
  fb_prove 459 Guest.Software.guestFn_extend_memory_cost2 K.«extend_memory_cost2»

/-! ### 3. Memory walks (`memcpy`, `memzero`) and their loop-free callers -/

theorem fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy» := by
  fb_unfold 16 Guest.Software.guestFn_memcpy
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 32 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.load _)))
            (by counter_step) rfl (by decide) (by decide)
        · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 8 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.load _)))
            (by counter_step) rfl (by decide) (by decide)
      · exact straightOn _ rfl
    · apply TerminatingProgBoundedOn.seq_guestInv
      · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 8 _
          (straightOn _ rfl)
          (DomainTouch.seq _ _ _ (DomainTouch.storeByte _ _))
          (by counter_step) rfl (by decide) (by decide)
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_counter_guestInv .lower (Or.inr rfl) _ _ (straightOn _ rfl) (by incr_body) rfl
        · exact straightOn _ rfl
  · fb_arith K.«memcpy»

theorem fb_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero» := by
  fb_unfold 17 Guest.Software.guestFn_memzero
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 32 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.const _)))
            (by counter_step) rfl (by decide) (by decide)
        · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 8 _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.const _)))
            (by counter_step) rfl (by decide) (by decide)
      · exact straightOn _ rfl
    · apply TerminatingProgBoundedOn.seq_guestInv
      · exact while_memory_walk_guestInv (ofString "dst") (ofString "i") 8 _
          (straightOn _ rfl)
          (DomainTouch.seq _ _ _ (DomainTouch.storeByte _ _))
          (by counter_step) rfl (by decide) (by decide)
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_counter_guestInv .lower (Or.inr rfl) _ _ (straightOn _ rfl) (by incr_body) rfl
        · exact straightOn _ rfl
  · fb_arith K.«memzero»

theorem fb_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory» := by
  have _ := fb_frame_mem_alloc
  have _ := fb_memzero
  fb_prove 460 Guest.Software.guestFn_extend_memory K.«extend_memory»

theorem fb_charge_with_memory : TerminatingFunBoundedOn GuestInv (ofString "charge_with_memory") K.«charge_with_memory» := by
  have _ := fb_extend_memory_cost1
  have _ := fb_add_sat
  have _ := fb_charge_gas
  have _ := fb_extend_memory
  fb_prove 461 Guest.Software.guestFn_charge_with_memory K.«charge_with_memory»

theorem fb_buffer_read : TerminatingFunBoundedOn GuestInv (ofString "buffer_read") K.«buffer_read» := by
  have _ := fb_memcpy
  have _ := fb_memzero
  fb_prove 462 Guest.Software.guestFn_buffer_read K.«buffer_read»

theorem fb_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» := by
  have _ := fb_scratch_alloc
  have _ := fb_memcpy
  fb_prove 454 Guest.Software.guestFn_stack_push K.«stack_push»

theorem fb_stack_push_word : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word» := by
  have _ := fb_stack_push
  fb_prove 455 Guest.Software.guestFn_stack_push_word K.«stack_push_word»

theorem fb_stack_push_bool : TerminatingFunBoundedOn GuestInv (ofString "stack_push_bool") K.«stack_push_bool» := by
  have _ := fb_stack_push
  fb_prove 456 Guest.Software.guestFn_stack_push_bool K.«stack_push_bool»

theorem fb_lst_push : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push» := by
  have _ := fb_alloc
  have _ := fb_memcpy
  fb_prove 410 Guest.Software.guestFn_lst_push K.«lst_push»

theorem fb_log_append : TerminatingFunBoundedOn GuestInv (ofString "log_append") K.«log_append» := by
  have _ := fb_lst_push
  fb_prove 523 Guest.Software.guestFn_log_append K.«log_append»

/-! ### 4. `u256_from_be` and `address_to_u256` -/

theorem fb_u256_from_be : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be» := by
  have _ := fb_bswap64
  fb_prove 86 Guest.Software.guestFn_u256_from_be K.«u256_from_be»

theorem fb_address_to_u256 : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256» := by
  have _ := fb_u256_from_be
  fb_prove 445 Guest.Software.guestFn_address_to_u256 K.«address_to_u256»

end InitECandidate.Solver.Wave8GuestInv.P12_P15.Callees
