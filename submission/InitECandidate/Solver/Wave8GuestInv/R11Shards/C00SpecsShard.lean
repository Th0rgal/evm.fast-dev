import InitECandidate.Solver.Wave8GuestInv.R11Shards.FrameException
import InitECandidate.Solver.Wave8GuestInv.R11Shards.FrameEpilogueSpec
import InitECandidate.Solver.Wave8GuestInv.Primitives

/-! R11Shards C00SpecsShard: exports `frame_epilogue_spec_of`, `frame_epilogue_spec_from_primitives`,
and `FrameException` specs (`ek_refill_frame_state_gas`, `ek_frame_halt`, `frame_exception_exec`,
`frame_exception_spec_of_evm_empty_word`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv

/-- `frame_epilogue_spec` specialized from `Primitives`. -/
theorem frame_epilogue_spec_from_primitives (P : Primitives) :
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue") :=
  frame_epilogue_spec_of P.ek_state_restore P.htab_set_spec P.htab_del_spec

end InitECandidate.Solver.Wave8GuestInv.R11Shards
