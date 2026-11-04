import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.ValidVersionedHashes

/-!
# R16 Shard `HeaderHashRecoverWk`: Re-exports of C08 `WorldKeeps` Leaves

Re-exports proved `WorldKeeps` leaves from `HeaderHashRecover.*`:
- `wk_is_valid_versioned_hashes` (`ContractParts/C08.lean:602`)
-/

set_option autoImplicit false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem «wk_is_valid_versioned_hashes» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "is_valid_versioned_hashes") :=
  HeaderHashRecover.«wk_is_valid_versioned_hashes»

end InitECandidate.Solver.Wave8GuestInv.R16Shards
