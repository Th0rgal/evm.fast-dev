import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.is_valid_jumpdest
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.op_gt
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.op_iszero
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.op_jump

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Leaves.S09

instance : IsGuestInv InitECandidate.Solver.Wave8GuestInv.GuestInv where
  toData _ h := ⟨h.1, h.2, h.3, h.4⟩
  ofData _ h := ⟨h.1, h.2, h.3, h.4⟩

/-! Selected subset of the original audited delivery; rechecked locally. -/

end InitECandidate.Solver.Wave8Leaves.S09
