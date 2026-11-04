import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.DecodeStep

/-!
# Standalone Proof of `ww_rlp_list_to_slices`

Re-exports the verified write-frame contract for `rlp_list_to_slices`
(`Guest/SoftwareAst.lean:4631`).
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem «ww_rlp_list_to_slices_contract» :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "rlp_list_to_slices") :=
  «ww_rlp_list_to_slices»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
