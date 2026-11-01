import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Common

/-! Verified `fb_*` callee bounds for Shards P13, P12, and P15 (excluding `u256_mod`, proved in
`P13DivMod.lean`). Imports only `R10Shards.Common` (zero `LeafStatements.lean` dependency). -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P13.Callees

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common

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

/-! ### 5. `keccak_f1600`, `keccak_absorb_block`, and `keccak256` -/

theorem fb_keccak_f1600 : TerminatingFunBoundedOn GuestInv (ofString "keccak_f1600") K.«keccak_f1600» := by
  fb_unfold 101 Guest.Software.guestFn_keccak_f1600
  apply TerminatingProgBoundedOn.weaken'
  · repeat apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_up_signed_const_guestInv _ 1 24 (straightOn _ rfl) (by counter_step) (by decide) (by decide)
    · exact straightOn _ rfl
  · fb_arith K.«keccak_f1600»

theorem fb_keccak_absorb_block : TerminatingFunBoundedOn GuestInv (ofString "keccak_absorb_block") K.«keccak_absorb_block» := by
  have _ := fb_keccak_f1600
  fb_unfold 102 Guest.Software.guestFn_keccak_absorb_block
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · exact while_up_signed_const_guestInv _ 8 136 (straightOn _ rfl) (by counter_step) (by decide) (by decide)
      · exact while_up_signed_const_guestInv _ 8 136 (straightOn _ rfl) (by counter_step) (by decide) (by decide)
    · fb_auto
  · fb_arith K.«keccak_absorb_block»

private def sourceBody (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

private def sourceDecTail (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .dec _ _ _ body => body | _ => .skip

private def sourceSeqTail (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .seq _ rest => rest | _ => .skip

private theorem outside_byte {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs (panByteAlignHOL b) := by
  intro h; rw [hg.memaddrs] at h; exact hb (ordinaryDomain_byte_interval b h)

private theorem outside_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) : ¬ s.memaddrs b := by
  intro h; rw [hg.memaddrs] at h; have hi := ordinaryDomain_interval b h; exact hb ⟨hi.1, by omega⟩

private noncomputable abbrev cEval {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
private noncomputable abbrev cEvalList {F : Type} (s : PanSemStateFiniteExact 64 F) (es : List (ExpHOL 64)) :=
  @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es

private theorem cEvalList_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : cEval s e = none) (hm : e ∈ es) : cEvalList s es = none := by
  induction es with
  | nil => simp at hm
  | cons first rest ih =>
    rcases List.mem_cons.mp hm with he | he
    · subst first; simp [cEvalList, evalListHOLExact, hn]
    · have ht := ih he
      simp only [cEvalList, evalListHOLExact] at ht ⊢
      rw [ht]
      cases hh : cEval s first <;> dsimp only [cEval] at hh <;> rw [hh]

private theorem cOp_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : cEval s e = none) (hm : e ∈ es) : cEval s (.op op es) = none := by
  have hl := cEvalList_none s e es hn hm
  simp only [cEval, evalHOLExact, hl]

private theorem cLoadByte_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (address : BitVec 64)
    (he : cEval s e = some (.val (.word address)))
    (hn : ¬ s.memaddrs (panByteAlignHOL address)) : cEval s (.loadByte e) = none := by
  cases s.memory (panByteAlignHOL address) with
  | word _ => simp [cEval, evalHOLExact, he, panMemLoadByteHOL, hn]

private theorem cLoad_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (address : BitVec 64)
    (he : cEval s e = some (.val (.word address)))
    (hn : ¬ s.memaddrs address) : cEval s (.load .one e) = none := by
  simp [cEval, evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hn]

private def ReadFailure {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  (evaluateHOLFiniteState s p).1 = some .error ∨ (evaluateHOLFiniteState s p).1 = some .timeOut

private theorem ReadFailure.seq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (first rest : ProgHOL 64) (h : ReadFailure s first) : ReadFailure s (.seq first rest) := by
  unfold ReadFailure at h ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s first with
  | mk result _ =>
    rw [hr] at h
    rcases h with h | h <;> simp only at h <;> subst result <;> simp

private theorem ReadFailure.ite {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (hy : ReadFailure s yes) (hn : ReadFailure s no) : ReadFailure s (.ite condition yes no) := by
  unfold ReadFailure at *
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · simp

private theorem ReadFailure.while {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64) (word : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word word)))
    (hw : word ≠ 0) (hb : ReadFailure (decClockHOLFinite s) body) :
    ReadFailure s (.while condition body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_while_fixClockRewrite, hc]
  simp only [if_pos hw]
  by_cases hz : s.clock = 0
  · simp [hz]
  · rw [if_neg hz]
    cases hr : evaluateHOLFiniteState (decClockHOLFinite s) body with
    | mk result _ =>
      rw [hr] at hb
      rcases hb with h | h <;> simp only at h <;> subst result <;> simp

private theorem ReadFailure.dec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64) (v : ValueHOL 64)
    (he : cEval s e = some v)
    (hb : ReadFailure (setVarHOLFinite name v s) body) :
    ReadFailure s (.dec name shape e body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  dsimp only [cEval] at he
  rw [he]
  dsimp only
  split
  · exact hb
  · simp

private theorem ReadFailure.store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address value : ExpHOL 64) (hv : cEval s value = none) :
    ReadFailure s (.store address value) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_store]
  split
  · simp only [hv]; simp
  · simp

private def keccakBranch : ProgHOL 64 := (.ite (.cmp .equal (.op .and [(.var .local (ofString "blk")), (.const (BitVec.ofNat 64 7))]) (.const (BitVec.ofNat 64 0))) (.while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 136))) (.seq (.store (.op .add [(.var .local (ofString "stp")), (.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")), (.var .local (ofString "i"))])), (.load .one (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i"))]))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 8))])))) (.while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 136))) (.seq (.store (.op .add [(.var .local (ofString "stp")), (.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")), (.var .local (ofString "i"))])), (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i"))])), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 1))])) (.const (BitVec.ofNat 64 8))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 2))])) (.const (BitVec.ofNat 64 16))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 3))])) (.const (BitVec.ofNat 64 24))), (.shift .lsl (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))])), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 1))])) (.const (BitVec.ofNat 64 8))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 2))])) (.const (BitVec.ofNat 64 16))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 3))])) (.const (BitVec.ofNat 64 24)))]) (.const (BitVec.ofNat 64 32)))])])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 8))])))))

private theorem keccak_branch_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hl : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) : ReadFailure s keccakBranch := by
  have ha : cEval (decClockHOLFinite s) (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i"))]) = some (.val (.word b)) := by
    simp [cEval, evalHOLExact, evalListHOLExact, decClockHOLFinite, hl, hi, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 136))) =
      some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLFinite, evalHOLExact, hi, wordCmpHOL, holAsmSignedLess]
  unfold keccakBranch
  apply ReadFailure.ite
  · apply ReadFailure.while s _ _ 1 hc (by decide)
    apply ReadFailure.seq
    apply ReadFailure.store_none
    have hn := cLoad_none (decClockHOLFinite s) _ b ha (outside_word s b hg hb)
    exact cOp_none (decClockHOLFinite s) .xor _ _ hn (by simp)
  · apply ReadFailure.while s _ _ 1 hc (by decide)
    apply ReadFailure.seq
    apply ReadFailure.store_none
    have hn := cLoadByte_none (decClockHOLFinite s) _ b ha (outside_byte s b hg hb)
    have ho : cEval (decClockHOLFinite s) (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i"))])), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 1))])) (.const (BitVec.ofNat 64 8))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 2))])) (.const (BitVec.ofNat 64 16))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 3))])) (.const (BitVec.ofNat 64 24))), (.shift .lsl (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))])), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 1))])) (.const (BitVec.ofNat 64 8))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 2))])) (.const (BitVec.ofNat 64 16))), (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")), (.var .local (ofString "i")), (.const (BitVec.ofNat 64 4)), (.const (BitVec.ofNat 64 3))])) (.const (BitVec.ofNat 64 24)))]) (.const (BitVec.ofNat 64 32)))]) = none :=
      cOp_none (decClockHOLFinite s) .or _ _ hn (by simp)
    exact cOp_none (decClockHOLFinite s) .xor _ _ ho (by simp)

private theorem keccak_absorb_block_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hl : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (sourceBody Guest.Software.guestFn_keccak_absorb_block) := by
  have hp : sourceBody Guest.Software.guestFn_keccak_absorb_block =
      .dec (ofString "i") .one (.const 0) (.seq keccakBranch
        (sourceSeqTail (sourceDecTail (sourceBody Guest.Software.guestFn_keccak_absorb_block)))) := rfl
  rw [hp]
  apply ReadFailure.dec s _ _ _ _ (.val (.word 0)) rfl
  apply ReadFailure.seq
  apply keccak_branch_outside _ b (guestInv_setVar _ _ s hg) _ _ hb
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
      show ofString "i" ≠ ofString "blk" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem call_discard_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) rs = true := by
  rw [evaluateHOLFiniteState_call] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp [emptyLocalsHOLFinite] at h; done) | skip
          dsimp only at h
          split at h
          · rename_i hrs
            exact ⟨vals, body, callee, rs, w, bpost, rfl, hlk, hclk, hrun, hrs⟩
          · simp at h

private theorem shape_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem two_args_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a, b] = some vals) :
    ∃ va vb, cEval s a = some va ∧ cEval s b = some vb ∧ vals = [va, vb] := by
  cases ha : cEval s a with
  | none => simp [evalListHOLFinite, evalListHOLExact, ha] at h
  | some va =>
    cases hb : cEval s b with
    | none => simp [evalListHOLFinite, evalListHOLExact, ha, hb] at h
    | some vb =>
      refine ⟨va, vb, rfl, rfl, ?_⟩
      simpa [evalListHOLFinite, evalListHOLExact, ha, hb] using h.symm

private theorem pan_two_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst two; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]

private theorem two_arg_lookup_inv_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] = some (foundBody, callee, foundRs)) :
    shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧
      shapeEqHOL ps2 (shapeOfHOLExact v2) = true ∧
      foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      foundRs = rs := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  rw [pan_two_arg_lookup code name first second ps1 ps2 rs body v1 v2 different hshapes.1 hshapes.2 lookup] at hfound
  cases hfound
  exact ⟨hshapes.1, hshapes.2, rfl, rfl, rfl⟩

private theorem touch_keccak_absorb_block (stateArg blockArg : ExpHOL 64) :
    DomainTouch blockArg (.call (some (none, none)) (ofString "keccak_absorb_block") [stateArg, blockArg]) := by
  intro F s hg hflow
  have hlookup : originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)], sourceBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
    lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl
  have hn : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "keccak_absorb_block") [stateArg, blockArg])).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue _ rfl s)
  have hrun : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "keccak_absorb_block") [stateArg, blockArg]) =
      (none, (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "keccak_absorb_block") [stateArg, blockArg])).2) :=
    Prod.ext hn rfl
  obtain ⟨vals, found, callee, rs, _, _, hargs, hlk, _, hcallee, _⟩ := call_discard_none hrun
  obtain ⟨vstate, vblock, _, hblock, rfl⟩ := two_args_eval s stateArg blockArg vals hargs
  rw [hg.code] at hlk
  obtain ⟨_, hshape, rfl, rfl, _⟩ := two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "keccak_absorb_block") (ofString "stp") (ofString "blk")
    .one .one .one (sourceBody Guest.Software.guestFn_keccak_absorb_block) vstate vblock
    (by decide) hlookup hlk
  obtain ⟨b, rfl⟩ := shape_one_word hshape
  refine ⟨b, hblock, ?_⟩
  by_contra hout
  have hf := keccak_absorb_block_outside (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "stp", vstate)).update (ofString "blk", .val (.word b)))) b
    (guestInv_callEntry _ _ hg)
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hout
  unfold ReadFailure at hf
  rw [hcallee] at hf
  simp at hf

theorem fb_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256» := by
  have _ := fb_memzero
  have _ := fb_memcpy
  have _ := fb_keccak_absorb_block
  fb_unfold 103 Guest.Software.guestFn_keccak256
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact while_memory_walk_guestInv (ofString "p") (ofString "i") 136 _
          (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_keccak_absorb_block) (straightOn _ rfl))
          (DomainTouch.seq _ _ _ (touch_keccak_absorb_block _ _))
          (by counter_step) rfl (by decide) (by decide)
      · fb_auto
  · have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
    unfold K.«keccak256»
    generalize_K
    generalize domainBytes = D at hD ⊢
    simp only [nat_max_eq, Nat.add_zero]
    omega

end InitECandidate.Solver.Wave8GuestInv.P13.Callees
