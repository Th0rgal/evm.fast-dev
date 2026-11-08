import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv4a

/-! # OpHandlerSpec Group 05bEnv4 (`OpHandlers-A`): `eps_calculate_blob_gas_price` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

private theorem lookup_taylor_exponential_local :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor", .one), (ofString "numerator", .one), (ofString "denominator", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_taylor_exponential).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 232 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_taylor_exponential) rfl

theorem eps_calculate_blob_gas_price :
    EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "calculate_blob_gas_price") := by
  refine eps_of_wsSafe 233 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_blob_gas_price rfl ?_
  intro F s hs _
  dsimp only [extractFn, Guest.Software.guestFn_calculate_blob_gas_price,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    have hraw := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "taylor_exponential") vals body callee rs hl
    rw [hs.code] at hraw
    simp only [lookupCodeHOLExact, lookup_taylor_exponential_local] at hraw
    split at hraw
    · have hb : body = _ := (Prod.mk.inj (Option.some.inj hraw)).1.symm
      subst body
      exact taylor_exponential_wsSafe (hs.with_locals_clock callee (s.clock - 1))
    · simp at hraw
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
