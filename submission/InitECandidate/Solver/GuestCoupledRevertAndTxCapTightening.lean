import InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening`

**Negative result.** Coupling the revert cost with the shared block budget and the EIP-7825 tx cap
does not bring `6×` back under Yukon.

Model (same tick model as the upstream modules, hand-counted):
* tx `t`: `d_t` cold dirty keys (21 units), `w_t` warm no-op `SSTORE`s (1 unit), `21 d_t + w_t ≤ M`
  (`M = 167,772`, EIP-7825), `Σ (21 d_t + w_t) ≤ S`; `state_fresh_tx` empties `ts+32` per tx, so
  `|ts+32| ≤ d_t ≤ 7,989` (not 79,999).
* block probes `2·D·(W + D)` (merge envelope), local probes + revert `htab_del` `13·Σ d_t w_t`
  (the no-op `SSTORE`s in a reverting child are the `W` operations themselves; one `CALL` per tx
  suffices, its overhead is linear).

Witness (12 txs: 11 × `(4,114, 81,378)` + 1 × `(3,783, 75,065)`, total exactly `S`):
`blk = 99,962,905,240`, `Σ d w = 3,966,650,907`,
`lin + mergeLin + blk + 13 Σ dw = 155,688,931,265 > ⌊Yukon/6⌋ = 150,119,987,578`.
So within this model the coupled worst case is ≥ 155.69 G: no coupled bound below
`150,119,987,579` exists, and `kPanAccessCall = 159,893,274,708` stays the upper envelope.
-/

namespace InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening

open InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def M : Nat := 167772
def S : Nat := 2000000
def lin : Nat := 3659564234
def mergeLin : Nat := 500000000

/-- Coupled cost of a tx list `(d, w)`. -/
def coupledCost (l : List (Nat × Nat)) : Nat :=
  let D := (l.map Prod.fst).sum
  let W := (l.map Prod.snd).sum
  lin + mergeLin + 2 * D * (W + D) + 13 * (l.map (fun p => p.1 * p.2)).sum

/-- Feasibility: every tx under EIP-7825, block under `S`. -/
def feasible (l : List (Nat × Nat)) : Prop :=
  (∀ p ∈ l, 21 * p.1 + p.2 ≤ M) ∧ (l.map (fun p => 21 * p.1 + p.2)).sum ≤ S

def witness : List (Nat × Nat) := List.replicate 11 (4114, 81378) ++ [(3783, 75065)]

/-- 1. Per-tx cap on `|ts+32|` from EIP-7825: `7,989`. -/
theorem tx_cap : 21 * 7989 ≤ M ∧ M < 21 * 7990 := by decide

/-- 2. `ts+32` within one tx: `d ≤ 7,989` whenever `21 d + w ≤ M`. -/
theorem dx_le (d w : Nat) (h : 21 * d + w ≤ M) : d ≤ 7989 := by unfold M at h; omega

/-- 3. Witness txs saturate their caps and the block budget exactly. -/
theorem witness_budget :
    21 * 4114 + 81378 = M ∧ 21 * 3783 + 75065 ≤ M ∧
      (witness.map (fun p => 21 * p.1 + p.2)).sum = S := by decide

/-- 4. Witness is feasible. -/
theorem witness_feasible : feasible witness := by
  refine ⟨?_, by decide⟩
  intro p hp
  simp only [witness, List.mem_append, List.mem_replicate, List.mem_singleton] at hp
  rcases hp with ⟨_, rfl⟩ | rfl <;> decide

/-- 5. Witness totals. -/
theorem witness_totals :
    (witness.map Prod.fst).sum = 49037 ∧ (witness.map Prod.snd).sum = 970223 ∧
      (witness.map (fun p => p.1 * p.2)).sum = 3966650907 := by decide

/-- 6. Witness cost. -/
theorem witness_cost : coupledCost witness = 155688931265 := by decide

/-- 7. Target for a `6×` slope: `⌊(Yukon − 1)/6⌋ = 150,119,987,578`. -/
theorem six_target : 6 * 150119987578 < yukon ∧ yukon ≤ 6 * 150119987579 := by decide

/-- 8. **No coupled envelope can restore `6×`**: a feasible witness costs more than `Yukon/6`. -/
theorem no_six_restore :
    ∃ l, feasible l ∧ yukon < 6 * coupledCost l :=
  ⟨witness, witness_feasible, by rw [witness_cost]; decide⟩

/-- 9. The witness stays under the upstream envelope (consistency). -/
theorem witness_le_access : coupledCost witness ≤ kPanAccessCall := by
  rw [witness_cost]; decide

/-- 10. Resulting envelope: unchanged, `5×` passes, `6×` fails. -/
def kPanCoupledRevertTxCap : Nat := kPanAccessCall

theorem slopes :
    kPanCoupledRevertTxCap = 159893274708 ∧ 5 * kPanCoupledRevertTxCap < yukon ∧
      yukon < 6 * kPanCoupledRevertTxCap := by decide

end InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening
