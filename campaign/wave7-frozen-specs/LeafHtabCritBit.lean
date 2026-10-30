import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.GuestBoundHtab

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafHtabCritBit` — Track B Leaf 01 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the remaining open-addressed / crit-bit hash-table functions in `Guest/SoftwareAst.lean`:
- `htab_set` (`while n != 0` / crit-bit walk `≤ 256` or terminating probe `≤ cap`),
- `htab_truncate` (`while (lds 1 (t + 24)) >+ n`),
- `htab_keys` (`while i < n` calling `memcpy`),
- `htab_union_into` (`while i < cap` calling `htab_set`),
- `nodedb_build` (`while cap <+ 2 * n + 2`, `while i <+ n` calling `keccak256` + `htab_set`).

Imports existing 0-`sorry` helpers from `GuestBoundHtab` (`lookup_htab_set`, `lookup_htab_truncate`,
`lookup_nodedb_build`, `funBounded_htab_union_into`, `funBounded_htab_keys_of_memcpy`,
`runBounded_keccak256_body`) and `PanTerminatingBounded`.

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafHtabCritBit

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestBoundHtab

def K_htab_set : Nat := 4 * (2 ^ 64 - 1) + 4096
def K_htab_truncate : Nat := 2 * (2 ^ 64 - 1) + 64
def K_htab_keys : Nat := 2 * (2 ^ 64 - 1) * 32 + 128
def K_htab_union_into : Nat := (2 ^ 64 - 1) * (K_htab_set + 16) + 64
def K_nodedb_build : Nat := (2 ^ 64 - 1) * (K_htab_set + 512) + 256

theorem terminatingFunBounded_htab_set :
    TerminatingFunBounded (ofString "htab_set") K_htab_set := by
  sorry

theorem terminatingFunBounded_htab_truncate :
    TerminatingFunBounded (ofString "htab_truncate") K_htab_truncate := by
  sorry

theorem terminatingFunBounded_htab_keys :
    TerminatingFunBounded (ofString "htab_keys") K_htab_keys := by
  sorry

theorem terminatingFunBounded_htab_union_into :
    TerminatingFunBounded (ofString "htab_union_into") K_htab_union_into := by
  sorry

theorem terminatingFunBounded_nodedb_build :
    TerminatingFunBounded (ofString "nodedb_build") K_nodedb_build := by
  sorry

end InitECandidate.Solver.LeafHtabCritBit
