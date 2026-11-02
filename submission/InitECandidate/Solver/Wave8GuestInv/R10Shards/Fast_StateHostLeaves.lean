import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastStateHostLeaves

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees

local syntax "fb_unfold_ext " num ident : tactic
local macro_rules
  | `(tactic| fb_unfold_ext $idx $fn) => `(tactic|
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

local syntax "fb_arith_ext " ident : tactic
local macro_rules
  | `(tactic| fb_arith_ext $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       first | omega | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega)))

local syntax "fb_prove_ext " num ident ident : tactic
local macro_rules
  | `(tactic| fb_prove_ext $idx $fn $k) => `(tactic|
      (fb_unfold_ext $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith_ext $k))

theorem fb_ssz_fail : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail» := by
  fb_prove_ext 196 Guest.Software.guestFn_ssz_fail K.«ssz_fail»

theorem fb_host_input_byte : TerminatingFunBoundedOn GuestInv (ofString "host_input_byte") K.«host_input_byte» := by
  fb_prove_ext 197 Guest.Software.guestFn_host_input_byte K.«host_input_byte»

theorem fb_host_input_le32 : TerminatingFunBoundedOn GuestInv (ofString "host_input_le32") K.«host_input_le32» := by
  have _ := fb_host_input_byte
  fb_prove_ext 198 Guest.Software.guestFn_host_input_le32 K.«host_input_le32»

theorem fb_node_new_branch : TerminatingFunBoundedOn GuestInv (ofString "node_new_branch") K.«node_new_branch» := by
  have _ := fb_alloc
  have _ := fb_memzero
  fb_prove_ext 258 Guest.Software.guestFn_node_new_branch K.«node_new_branch»

theorem fb_mpt_new : TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new» := by
  have _ := fb_alloc
  fb_prove_ext 268 Guest.Software.guestFn_mpt_new K.«mpt_new»

theorem fb_state_snapshot : TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot» := by
  fb_prove_ext 358 Guest.Software.guestFn_state_snapshot K.«state_snapshot»

theorem fb_sk_make : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make» := by
  have _ := fb_memcpy
  fb_prove_ext 360 Guest.Software.guestFn_sk_make K.«sk_make»

theorem fb_blake2_init : TerminatingFunBoundedOn GuestInv (ofString "blake2_init") K.«blake2_init» := by
  have _ := fb_alloc
  fb_prove_ext 621 Guest.Software.guestFn_blake2_init K.«blake2_init»

theorem fb_sha256_pair : TerminatingFunBoundedOn GuestInv (ofString "sha256_pair") K.«sha256_pair» := by
  fb_prove_ext 96 Guest.Software.guestFn_sha256_pair K.«sha256_pair»

theorem fb_calculate_message_call_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas» := by
  have _ := fb_add_sat
  have _ := fb_u256_is_zero
  fb_prove_ext 602 Guest.Software.guestFn_calculate_message_call_gas K.«calculate_message_call_gas»

end InitECandidate.Solver.Wave8GuestInv.FastStateHostLeaves
