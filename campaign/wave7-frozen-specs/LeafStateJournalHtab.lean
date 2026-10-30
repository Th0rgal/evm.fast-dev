import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafHtabCritBit
import InitECandidate.Solver.LeafMptWitnessWalk
import InitECandidate.Solver.LeafRlpValidate
import InitECandidate.Solver.GuestBoundHtab

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafStateJournalHtab` — Track B Leaf 11 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Bounds the EVM state/account/storage hash-table lookup, journal snapshot, and `state_restore` cluster:
- `htab_find_leaf` (L2427: crit-bit walk `≤ 256` steps),
- `htab_del` (L2581: crit-bit walk `≤ 256` steps),
- `state_restore` (L6386: `while journal_n >+ snap { journal_n = journal_n - 1; ... }`),
- `get_account`, `set_account`, `get_storage`, `set_storage`, `get_transient_storage`, `set_transient_storage`,
- `warm_address`, `warm_storage_key`.

Note on open-addressed / crit-bit probing: `TerminatingFunBounded` carries `out.1 ≠ some .timeOut`;
in any terminating probe loop on a power-of-2 capacity table (`mask = cap - 1`), any probe chain
exceeding `cap` visits a repeated index and loops forever (yielding `.timeOut` at every finite clock),
so every non-`.timeOut` probe finishes in `≤ cap ≤ 2^64 - 1` iterations!

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafStateJournalHtab

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafHtabCritBit
open InitECandidate.Solver.LeafMptWitnessWalk
open InitECandidate.Solver.LeafRlpValidate

def K_htab_find_leaf : Nat := 4 * (2 ^ 64 - 1) + 4096
def K_htab_del : Nat := 4 * (2 ^ 64 - 1) + 4096
def K_get_account : Nat := K_htab_find_leaf + K_trie_walk + K_decode_account_from_leaf + K_htab_set + 8192
def K_get_storage : Nat := K_get_account + K_htab_find_leaf + K_trie_walk + K_htab_set + 8192
def K_set_storage : Nat := K_get_storage + K_htab_set + 4096
def K_state_restore : Nat := 4 * (2 ^ 64 - 1) * (K_htab_set + K_htab_del + K_htab_truncate + 256) + 8192

theorem terminatingFunBounded_htab_find_leaf :
    TerminatingFunBounded (ofString "htab_find_leaf") K_htab_find_leaf := by
  sorry

theorem terminatingFunBounded_htab_del :
    TerminatingFunBounded (ofString "htab_del") K_htab_del := by
  sorry

theorem terminatingFunBounded_get_account :
    TerminatingFunBounded (ofString "get_account") K_get_account := by
  sorry

theorem terminatingFunBounded_get_storage :
    TerminatingFunBounded (ofString "get_storage") K_get_storage := by
  sorry

theorem terminatingFunBounded_set_storage :
    TerminatingFunBounded (ofString "set_storage") K_set_storage := by
  sorry

theorem terminatingFunBounded_state_restore :
    TerminatingFunBounded (ofString "state_restore") K_state_restore := by
  sorry

end InitECandidate.Solver.LeafStateJournalHtab
