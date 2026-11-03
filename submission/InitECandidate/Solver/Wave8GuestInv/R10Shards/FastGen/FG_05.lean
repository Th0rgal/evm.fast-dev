import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyLeaves


set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastGen

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.FastGen

local syntax "fg_auto" : tactic
local macro_rules
  | `(tactic| fg_auto) => `(tactic| fg_step_auto)

local syntax "fg_auto_loops" : tactic
local macro_rules
  | `(tactic| fg_auto_loops) => `(tactic| fg_step_loops)

local syntax "fg_prove " num ident ident : tactic
local macro_rules
  | `(tactic| fg_prove $idx $fn $k) => `(tactic|
      (fg_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fg_auto
       · fg_arith $k))

theorem fb_fp_reduce :
    TerminatingFunBoundedOn GuestInv (ofString "fp_reduce") K.fp_reduce := by
  fg_prove 152 Guest.Software.guestFn_fp_reduce K.fp_reduce

theorem fb_fp_sqrt_of
    (h_fp_pow : TerminatingFunBoundedOn GuestInv (ofString "fp_pow") K.fp_pow) :
    TerminatingFunBoundedOn GuestInv (ofString "fp_sqrt") K.fp_sqrt := by
  have _ := h_fp_pow
  fg_prove 161 Guest.Software.guestFn_fp_sqrt K.fp_sqrt

theorem fb_fp_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fp_sub") K.fp_sub := by
  fg_prove 150 Guest.Software.guestFn_fp_sub K.fp_sub

theorem fb_fq12_cast :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_cast") K.fq12_cast := by
  fg_prove 678 Guest.Software.guestFn_fq12_cast K.fq12_cast

theorem fb_fq_add :
    TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.fq_add := by
  fg_prove 649 Guest.Software.guestFn_fq_add K.fq_add

theorem fb_fq_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fq_mul") K.fq_mul :=
  InitECandidate.Solver.Wave8GuestInv.Arith.fb_fq_mul

theorem fb_fq_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fq_neg") K.fq_neg := by
  fg_prove 651 Guest.Software.guestFn_fq_neg K.fq_neg

theorem fb_fq_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.fq_sub := by
  fg_prove 650 Guest.Software.guestFn_fq_sub K.fq_sub

end InitECandidate.Solver.Wave8GuestInv.FastGen
