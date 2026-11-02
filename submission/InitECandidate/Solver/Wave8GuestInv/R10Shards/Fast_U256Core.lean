import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastU256Core

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
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod

macro "fb_unfold' " idx:num fn:ident : tactic => `(tactic|
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

macro "fb_prove' " idx:num fn:ident k:ident : tactic => `(tactic|
  (fb_unfold' $idx $fn
   apply TerminatingProgBoundedOn.weaken'
   · fb_auto
   · fb_arith $k))

theorem fb_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min» := by
  fb_prove' 31 Guest.Software.guestFn_min K.«min»

theorem fb_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max» := by
  fb_prove' 32 Guest.Software.guestFn_max K.«max»

theorem fb_udiv : TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv» := by
  have _ := fb_udivmod
  fb_prove' 34 Guest.Software.guestFn_udiv K.«udiv»

theorem fb_u256_from_word : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word» := by
  fb_prove' 39 Guest.Software.guestFn_u256_from_word K.«u256_from_word»

theorem fb_u256_fits_word : TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word» := by
  fb_prove' 41 Guest.Software.guestFn_u256_fits_word K.«u256_fits_word»

theorem fb_u256_eq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq» := by
  fb_prove' 45 Guest.Software.guestFn_u256_eq K.«u256_eq»

theorem fb_u256_gt : TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt» := by
  have _ := fb_u256_lt
  fb_prove' 47 Guest.Software.guestFn_u256_gt K.«u256_gt»

theorem fb_u256_add_carry : TerminatingFunBoundedOn GuestInv (ofString "u256_add_carry") K.«u256_add_carry» := by
  fb_prove' 55 Guest.Software.guestFn_u256_add_carry K.«u256_add_carry»

end InitECandidate.Solver.Wave8GuestInv.FastU256Core
