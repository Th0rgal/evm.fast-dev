import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4O2

/-!
# Phase-4 instruction 24-26 runner and callee transports (re-export)

The `p4Run_g6` lane is split across two files:

* `WkPtxPhase4O1.lean` (§A-§F): low-cell survival, `IvlUnhit` transports,
  `fixedObjects` stability, `rc` field reads, and the logs-facts transports
  across a receipt-slice store.
* `WkPtxPhase4O2.lean` (§G-§I): callee transports for `LogsDisjFixed` and the
  out/fresh-list disjunction, the store-destination evaluations for the two
  receipt-slice stores, and `p4Run_g6` itself.

This module re-exports both, so downstream shards can keep importing
`WkPtxPhase4O`. -/
