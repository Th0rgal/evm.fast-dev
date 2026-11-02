import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabNew

/-! Ported and proved remote opcode/RLP/htab leaves for Wave8GuestInv (zero `LeafStatements.lean`,
`C08.lean`, or `InitECandidate.Proofs.*` imports). -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1

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

/-! ### Local structural unfold helper (handles `shapeListToHOLStructural` for struct shapes) -/

local syntax "b1_unfold " num ident : tactic
local macro_rules
  | `(tactic| b1_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

local syntax "b1_prove " num ident ident : tactic
local macro_rules
  | `(tactic| b1_prove $idx $fn $k) => `(tactic|
      (b1_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

/-! ### 1. Right-shift byte-length loop combinator (`rlp_be_len`) -/

private def byteLen64 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n < 2 ^ 8 then 1
  else if n < 2 ^ 16 then 2
  else if n < 2 ^ 24 then 3
  else if n < 2 ^ 32 then 4
  else if n < 2 ^ 40 then 5
  else if n < 2 ^ 48 then 6
  else if n < 2 ^ 56 then 7
  else 8

private theorem byteLen64_le (n : Nat) : byteLen64 n ≤ 8 := by
  unfold byteLen64; split_ifs <;> omega

private theorem byteLen64_div256 (n : Nat) (h0 : 0 < n) (h64 : n < 2 ^ 64) :
    byteLen64 (n / 2 ^ 8) < byteLen64 n := by
  unfold byteLen64; split_ifs <;> omega

private def shr8Rank (x : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup x with
  | some (.val (.word w)) => byteLen64 w.toNat
  | _ => 0

private theorem while_shr8_guestInv (v : MlS) {rest : ProgHOL 64}
    (hrest : avoidsLocal v rest = true)
    (hstraight : extStraightLine (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) = true) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .notEqual (.var .local v) (.const 0))
        (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest))
      ((8 + 1) * (0 + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .notEqual (.var .local v) (.const 0))
    (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest)
    0 8 (shr8Rank v)
    (fun s hs => guestInv_decClock s hs)
    (straightOn _ hstraight)
    (fun s _ _ _ => by unfold shr8Rank; split; exact byteLen64_le _; exact Nat.zero_le _)
    ?_
  intro F s _ hs hact hflow
  refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨w, z, hlw, hz, hword⟩ := evalAt_cmp s .notEqual _ _ word hw
  have hz0 : z = 0#64 := by simpa [evalAt, evalHOLExact] using hz.symm
  subst hz0
  have hlookup : s.locals.lookup v = some (.val (.word w)) := by
    simpa [evalAt, evalHOLExact] using hlw
  have hwpos : 0 < w.toNat := by
    by_contra hc
    have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc)
    subst hw0
    simp [wordCmpHOL] at hword
    exact hnz hword
  have hass : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local v (.shift .lsr (.var .local v) (.const 8))) =
      (none, setVarHOLFinite v (.val (.word (w >>> 8))) (decClockHOLFinite s)) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, decClockHOLFinite, hlookup,
      wordShiftHOL, lookupKvarHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_seq_line780, hass] at hflow ⊢
  dsimp only at hflow ⊢
  have hkeep := evaluate_avoidsLocal_flowing v rest hrest
    (setVarHOLFinite v (.val (.word (w >>> 8))) (decClockHOLFinite s))
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hpost_lookup : (evaluateHOLFiniteState
      (setVarHOLFinite v (.val (.word (w >>> 8))) (decClockHOLFinite s)) rest).2.locals.lookup v =
      some (.val (.word (w >>> 8))) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hkeep
  have hshr : (w >>> 8).toNat = w.toNat / 2 ^ 8 := by
    have h1 : (w >>> 8).toNat = w.toNat >>> 8 := by simp
    rw [h1, Nat.shiftRight_eq_div_pow]
  simp only [shr8Rank, hpost_lookup, hlookup, hshr]
  exact byteLen64_div256 w.toNat hwpos w.isLt

/-! ### 2. RLP encoder & list-header leaves (`Primitives.lean` & `origin/wave8/leaves-rlp-opus55`) -/

theorem fb_rlp_be_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_be_len") K.«rlp_be_len» := by
  b1_unfold 118 Guest.Software.guestFn_rlp_be_len
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_shr8_guestInv _ rfl rfl
    · exact straightOn _ rfl
  · fb_arith K.«rlp_be_len»

theorem fb_rlp_put_be :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_put_be") K.«rlp_put_be» := by
  b1_unfold 119 Guest.Software.guestFn_rlp_put_be
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_down_unsigned_guestInv _ (straightOn _ rfl)
        (CounterStep.suffix _ _ _ (CounterStep.sub_one _) rfl)
    · exact straightOn _ rfl
  · fb_arith K.«rlp_put_be»

theorem fb_rlp_write_header :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_write_header") K.«rlp_write_header» := by
  have _ := fb_rlp_be_len
  have _ := fb_rlp_put_be
  b1_prove 120 Guest.Software.guestFn_rlp_write_header K.«rlp_write_header»

theorem fb_rlp_header_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_header_len") K.«rlp_header_len» := by
  have _ := fb_rlp_be_len
  b1_prove 121 Guest.Software.guestFn_rlp_header_len K.«rlp_header_len»

/-- RLP string/bytes encoder leaf (`rlp_encode_bytes`, exact `Primitives.lean` type). -/
theorem fb_rlp_encode_bytes :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes» := by
  have _ := fb_rlp_write_header
  have _ := fb_memcpy
  b1_prove 122 Guest.Software.guestFn_rlp_encode_bytes K.«rlp_encode_bytes»

/-- Alias `fb_rlp_encode_string` for the RLP string/bytes encoder leaf (`rlp_encode_bytes`). -/
theorem fb_rlp_encode_string :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes» :=
  fb_rlp_encode_bytes

/-- RLP word encoder leaf (`rlp_encode_word`, exact `Primitives.lean` type). -/
theorem fb_rlp_encode_word :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word» := by
  have _ := fb_rlp_be_len
  have _ := fb_rlp_put_be
  b1_prove 123 Guest.Software.guestFn_rlp_encode_word K.«rlp_encode_word»

/-- RLP list header encoder (`rlp_encode_list_header`). -/
theorem fb_rlp_encode_list_header :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header» := by
  have _ := fb_rlp_write_header
  b1_prove 124 Guest.Software.guestFn_rlp_encode_list_header K.«rlp_encode_list_header»

/-- RLP list header length (`rlp_list_header_len`). -/
theorem fb_rlp_list_header_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len» := by
  have _ := fb_rlp_header_len
  b1_prove 126 Guest.Software.guestFn_rlp_list_header_len K.«rlp_list_header_len»

/-- RLP encoded byte-string length (`rlp_bytes_encoded_len`). -/
theorem fb_rlp_bytes_encoded_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len» := by
  have _ := fb_rlp_header_len
  b1_prove 125 Guest.Software.guestFn_rlp_bytes_encoded_len K.«rlp_bytes_encoded_len»

/-- RLP encoded word length (`rlp_word_encoded_len`). -/
theorem fb_rlp_word_encoded_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_word_encoded_len") K.«rlp_word_encoded_len» := by
  have _ := fb_rlp_be_len
  b1_prove 127 Guest.Software.guestFn_rlp_word_encoded_len K.«rlp_word_encoded_len»

/-- RLP encoded value length (`rlp_value_encoded_len`). -/
theorem fb_rlp_value_encoded_len :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") K.«rlp_value_encoded_len» := by
  have _ := fb_rlp_bytes_encoded_len
  b1_prove 286 Guest.Software.guestFn_rlp_value_encoded_len K.«rlp_value_encoded_len»

/-- Withdrawal RLP encoded length (`withdrawal_rlp_len`). -/
theorem fb_withdrawal_rlp_len :
    TerminatingFunBoundedOn GuestInv (ofString "withdrawal_rlp_len") K.«withdrawal_rlp_len» := by
  have _ := fb_rlp_word_encoded_len
  have _ := fb_rlp_list_header_len
  b1_prove 837 Guest.Software.guestFn_withdrawal_rlp_len K.«withdrawal_rlp_len»

/-- RLP list finalizer (`rlp_finish_list`: writes list header + shifts payload). -/
theorem fb_rlp_finish_list :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_finish_list") K.«rlp_finish_list» := by
  have _ := fb_rlp_list_header_len
  have _ := fb_memcpy
  have _ := fb_rlp_encode_list_header
  b1_prove 833 Guest.Software.guestFn_rlp_finish_list K.«rlp_finish_list»

/-- Alias `fb_rlp_encode_list` for the RLP list finalizer (`rlp_finish_list`). -/
theorem fb_rlp_encode_list :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_finish_list") K.«rlp_finish_list» :=
  fb_rlp_finish_list

/-- Withdrawal RLP list encoder (`encode_withdrawal_rlp`, exact `Primitives.lean` type). -/
theorem fb_encode_withdrawal_rlp :
    TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp» := by
  have _ := fb_alloc
  have _ := fb_rlp_encode_word
  have _ := fb_rlp_encode_bytes
  have _ := fb_rlp_finish_list
  b1_prove 838 Guest.Software.guestFn_encode_withdrawal_rlp K.«encode_withdrawal_rlp»

/-! ### 3. `htab_new` & parameterized `fb_htab_new_spec` (`C08.lean` NEVER imported) -/

/-- `fb_htab_new` (exact `Primitives.lean` type). -/
theorem fb_htab_new :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» := by
  have _ := fb_alloc
  b1_prove 128 Guest.Software.guestFn_htab_new K.«htab_new»

/-- Local copy of `C00.FunSpec` (defined directly from `MemoryViews` / `PanSemStateFiniteExact`
without importing `ContractParts/C00.lean` or `C08.lean`). -/
def HtabFunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- Local copy of `C00.HtabNewReady` (definitionally equal to `InitECandidate.Solver.Wave8GuestInv.HtabNewReady`). -/
def HtabNewReadyLocal : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

/-- Local copy of `C00.HtabNewExit` (definitionally equal to `InitECandidate.Solver.Wave8GuestInv.HtabNewExit`). -/
def HtabNewExitLocal : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ AllocatorGrows s post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    hdr post w.toNat 0 = locN s "key_len" ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k

/-- Unconditional proof of `FunSpec HtabNewReady HtabNewExit (ofString "htab_new")`
(definitionally equal to `type_of% @htab_new_spec` in `Primitives.lean`), proved without
importing `C00.lean` or `C08.lean`. -/
theorem htab_new_spec :
    HtabFunSpec HtabNewReadyLocal HtabNewExitLocal (ofString "htab_new") :=
  SoloHtabNew.htab_new_entry_exit

/-- Parameterized `htab_new_spec` adapter (`fb_htab_new_spec`): avoids importing `C08.lean` (or even
`C00.lean`), lifting `SoloHtabNew.htab_new_entry_exit` into any caller-supplied `Spec` wrapper
matching the `FunSpec` introduction shape. -/
theorem fb_htab_new_spec
    {Spec : (∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) →
      (∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
        PanSemStateFiniteExact 64 F → Prop) → MlS → Prop}
    (hmk : ∀ {P Q}, HtabFunSpec P Q (ofString "htab_new") → Spec P Q (ofString "htab_new")) :
    Spec HtabNewReadyLocal HtabNewExitLocal (ofString "htab_new") :=
  hmk SoloHtabNew.htab_new_entry_exit

/-! ### 4. Small S02 leaves disjoint from Fast_RemoteLeavesB2 (exact `Primitives.lean` types) -/

theorem fb_u256_limb :
    TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» := by
  b1_prove 43 Guest.Software.guestFn_u256_limb K.«u256_limb»

theorem fb_u256_byte_length :
    TerminatingFunBoundedOn GuestInv (ofString "u256_byte_length") K.«u256_byte_length» := by
  have _ := fb_u256_bit_length
  b1_prove 79 Guest.Software.guestFn_u256_byte_length K.«u256_byte_length»

theorem fb_u256_to_be_min :
    TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min» := by
  have _ := fb_u256_byte_length
  have _ := fb_u256_limb
  b1_prove 88 Guest.Software.guestFn_u256_to_be_min K.«u256_to_be_min»

theorem fb_rlp_put_u256 :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_u256_to_be_min
  have _ := fb_rlp_encode_bytes
  have _ := fb_heap_release
  b1_prove 228 Guest.Software.guestFn_rlp_put_u256 K.«rlp_put_u256»

theorem fb_mpt_new :
    TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new» := by
  have _ := fb_alloc
  b1_prove 268 Guest.Software.guestFn_mpt_new K.«mpt_new»

theorem fb_sk_make :
    TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make» := by
  have _ := fb_memcpy
  b1_prove 360 Guest.Software.guestFn_sk_make K.«sk_make»

theorem fb_bal_init :
    TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init» := by
  have _ := fb_htab_new
  have _ := fb_alloc
  b1_prove 411 Guest.Software.guestFn_bal_init K.«bal_init»

theorem fb_udiv :
    TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv» := by
  have _ := P13.DivMod.fb_udivmod
  b1_prove 34 Guest.Software.guestFn_udiv K.«udiv»

theorem fb_check_gas_limit :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit» := by
  have _ := fb_udiv
  b1_prove 235 Guest.Software.guestFn_check_gas_limit K.«check_gas_limit»

theorem fb_encode_account :
    TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account» := by
  have _ := fb_rlp_encode_word
  have _ := fb_st_be64
  have _ := fb_rlp_encode_bytes
  b1_unfold 294 Guest.Software.guestFn_encode_account
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply decCall_guestInv' fb_rlp_encode_word
    apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply TerminatingProgBoundedOn.seq_guestInv
      · fb_auto
      · apply TerminatingProgBoundedOn.seq_guestInv
        · fb_auto
        · apply TerminatingProgBoundedOn.seq_guestInv
          · fb_auto
          · apply TerminatingProgBoundedOn.seq_guestInv
            · fb_auto
            · apply dec_guestInv
              apply TerminatingProgBoundedOn.seq_guestInv
              · exact while_up_unsigned_const_guestInv _ 32#64 (straightOn _ rfl) (by counter_step)
              · fb_auto
  · rw [show (32#64 : BitVec 64).toNat = 32 by decide]
    fb_arith K.«encode_account»

theorem fb_is_zero_bytes :
    TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.«is_zero_bytes» := by
  b1_prove 19 Guest.Software.guestFn_is_zero_bytes K.«is_zero_bytes»

theorem fb_ld_be64 :
    TerminatingFunBoundedOn GuestInv (ofString "ld_be64") K.«ld_be64» := by
  have _ := fb_bswap64
  b1_prove 24 Guest.Software.guestFn_ld_be64 K.«ld_be64»

theorem fb_extract_deposit_data :
    TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data» := by
  have _ := fb_heap_mark
  have _ := fb_is_zero_bytes
  have _ := fb_ld_be64
  have _ := fb_heap_release
  have _ := fb_memcpy
  b1_prove 841 Guest.Software.guestFn_extract_deposit_data K.«extract_deposit_data»

/-! ### 5. Small S10 opcode/gas leaves disjoint from Fast_RemoteLeavesB2 (exact `Primitives.lean` types) -/

theorem fb_u256_bit :
    TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» := by
  have _ := fb_u256_limb
  b1_prove 44 Guest.Software.guestFn_u256_bit K.«u256_bit»

theorem fb_u256_slt :
    TerminatingFunBoundedOn GuestInv (ofString "u256_slt") K.«u256_slt» := by
  b1_prove 48 Guest.Software.guestFn_u256_slt K.«u256_slt»

theorem fb_u256_sgt :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sgt") K.«u256_sgt» := by
  have _ := fb_u256_slt
  b1_prove 49 Guest.Software.guestFn_u256_sgt K.«u256_sgt»

theorem fb_u256_not :
    TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.«u256_not» := by
  b1_prove 51 Guest.Software.guestFn_u256_not K.«u256_not»

theorem fb_u256_and :
    TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.«u256_and» := by
  b1_prove 52 Guest.Software.guestFn_u256_and K.«u256_and»

theorem fb_u256_or :
    TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» := by
  b1_prove 53 Guest.Software.guestFn_u256_or K.«u256_or»

theorem fb_u256_sub :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» := by
  b1_prove 57 Guest.Software.guestFn_u256_sub K.«u256_sub»

theorem fb_u256_shl :
    TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by
  b1_prove 81 Guest.Software.guestFn_u256_shl K.«u256_shl»

theorem fb_u256_shr :
    TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» := by
  b1_prove 82 Guest.Software.guestFn_u256_shr K.«u256_shr»

theorem fb_u256_sar :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sar") K.«u256_sar» := by
  have _ := fb_u256_shr
  have _ := fb_u256_shl
  have _ := fb_u256_or
  b1_prove 83 Guest.Software.guestFn_u256_sar K.«u256_sar»

theorem fb_u256_signextend :
    TerminatingFunBoundedOn GuestInv (ofString "u256_signextend") K.«u256_signextend» := by
  have _ := fb_u256_bit
  have _ := fb_u256_shl
  have _ := fb_u256_or
  have _ := fb_u256_not
  have _ := fb_u256_and
  b1_prove 84 Guest.Software.guestFn_u256_signextend K.«u256_signextend»

theorem fb_check_gas :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas» := by
  b1_prove 447 Guest.Software.guestFn_check_gas K.«check_gas»

theorem fb_op_stop :
    TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop» := by
  have _ := fb_pc_add
  b1_prove 502 Guest.Software.guestFn_op_stop K.«op_stop»

theorem fb_op_sub :
    TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_u256_sub
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 477 Guest.Software.guestFn_op_sub K.«op_sub»

theorem fb_op_returndatasize :
    TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize» := by
  have _ := fb_charge_gas
  have _ := fb_stack_push_word
  have _ := fb_pc_add
  b1_prove 546 Guest.Software.guestFn_op_returndatasize K.«op_returndatasize»

theorem fb_op_slotnum :
    TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum» := by
  have _ := fb_charge_gas
  have _ := fb_block_env
  have _ := fb_stack_push_word
  have _ := fb_pc_add
  b1_prove 561 Guest.Software.guestFn_op_slotnum K.«op_slotnum»

theorem fb_op_prevrandao :
    TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao» := by
  have _ := fb_charge_gas
  have _ := fb_block_env
  have _ := fb_u256_from_be
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 560 Guest.Software.guestFn_op_prevrandao K.«op_prevrandao»

theorem fb_op_shl :
    TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_sat_word
  have _ := fb_u256_shl
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 497 Guest.Software.guestFn_op_shl K.«op_shl»

theorem fb_op_shr :
    TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_sat_word
  have _ := fb_u256_shr
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 498 Guest.Software.guestFn_op_shr K.«op_shr»

theorem fb_op_sar :
    TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_sat_word
  have _ := fb_u256_sar
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 499 Guest.Software.guestFn_op_sar K.«op_sar»

theorem fb_op_signextend :
    TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_sat_word
  have _ := fb_u256_signextend
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 485 Guest.Software.guestFn_op_signextend K.«op_signextend»

theorem fb_op_slt :
    TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_u256_slt
  have _ := fb_stack_push_bool
  have _ := fb_pc_add
  b1_prove 488 Guest.Software.guestFn_op_slt K.«op_slt»

theorem fb_u256_neg :
    TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» := by
  b1_prove 58 Guest.Software.guestFn_u256_neg K.«u256_neg»

theorem fb_u256_abs :
    TerminatingFunBoundedOn GuestInv (ofString "u256_abs") K.«u256_abs» := by
  have _ := fb_u256_neg
  b1_prove 72 Guest.Software.guestFn_u256_abs K.«u256_abs»

theorem fb_u256_smod :
    TerminatingFunBoundedOn GuestInv (ofString "u256_smod") K.«u256_smod» := by
  have _ := fb_u256_abs
  have _ := P13.DivMod.fb_u256_mod
  have _ := fb_u256_neg
  b1_prove 74 Guest.Software.guestFn_u256_smod K.«u256_smod»

theorem fb_op_smod :
    TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_u256_smod
  have _ := fb_stack_push
  have _ := fb_pc_add
  b1_prove 481 Guest.Software.guestFn_op_smod K.«op_smod»

theorem fb_op_sgt :
    TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt» := by
  have _ := fb_stack_pop
  have _ := fb_charge_gas
  have _ := fb_u256_sgt
  have _ := fb_stack_push_bool
  have _ := fb_pc_add
  b1_prove 489 Guest.Software.guestFn_op_sgt K.«op_sgt»

end InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1
