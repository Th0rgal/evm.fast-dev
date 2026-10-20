import InitECandidate.Solver.GuestNodedbAndWitnessTableBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMptTraversalAndStateRootBound`

Hand transcription of `guest.pp.pnk` (wt-2).

* No `mpt_put`; the API is `mpt_get` (l.4038), `mpt_set` (l.4320), `mpt_root` (l.4542).
* No explicit depth counter. `trie_walk` (l.~3971) loops on a position `pos` over the nibble key:
  leaf (`k = 1`) returns; extension (`k = 2`) advances `pos += sl` (`sl ≤ nlen − pos`); branch
  advances `pos += 1`, and returns when `pos = nlen`. Keys are Keccak-256 (`trie_lookup`: 64 nibbles).
  **Assumption** (not checked by `trie_walk`): extensions have `sl ≥ 1` (standard MPT encoding).
  Then a descent makes `≤ 64 + 1 = 65` iterations.
* `nodedb_lookup` is **not** called per access: `decode_witness_to_mpt` (l.3954, via `_resolve_step`
  l.3755) decodes the witness eagerly at `state_init`, one lookup per witness reference.
  Cold `ws_get_storage` (l.5555): one `keccak256` of the key, then a pure in-memory `trie_walk`.
* `compute_state_root` (l.14660): per changed account, `mpt_from_witness` + `mpt_set` per changed
  slot (two passes), `mpt_root`; then the state trie. Each `mpt_set` walks `≤ 65` steps;
  `mpt_root` hashes dirty nodes, `≤ 65` per changed key.
* Changed / cold keys: each needs `≥ 2,000` gas, so `≤ 100,000` per 200M-gas block.
-/

namespace InitECandidate.Solver.GuestMptTraversalAndStateRootBound

/-- Abstract `trie_walk` step: branch (`+1`) or extension (`+sl`, `sl ≥ 1`). -/
inductive Step | branch | ext (sl : Nat)

def advance : Step → Nat
  | .branch => 1
  | .ext sl => sl

/-- 1. Each step advances the nibble position by ≥ 1 (under `sl ≥ 1`). -/
theorem advance_pos (s : Step) (h : ∀ sl, s = .ext sl → 1 ≤ sl) : 1 ≤ advance s := by
  cases s with
  | branch => decide
  | ext sl => exact h sl rfl

/-- 2. Steps of a walk consume `≤ 64` nibbles, so at most `64` advancing steps. -/
theorem steps_le (l : List Step) (h : ∀ s ∈ l, 1 ≤ advance s) (hsum : (l.map advance).sum ≤ 64) :
    l.length ≤ 64 := by
  have key : ∀ m : List Step, (∀ s ∈ m, 1 ≤ advance s) → m.length ≤ (m.map advance).sum := by
    intro m hm
    induction m with
    | nil => simp
    | cons x t ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hx := hm x (List.mem_cons_self ..)
      have := ih (fun s hs => hm s (List.mem_cons_of_mem _ hs))
      omega
  have := key l h
  omega

/-- 3. Walk iterations including the terminating leaf / empty child: `≤ 65`. -/
theorem walk_iters (l : List Step) (h : ∀ s ∈ l, 1 ≤ advance s) (hsum : (l.map advance).sum ≤ 64) :
    l.length + 1 ≤ 65 := by
  have := steps_le l h hsum; omega

/-- 4. Tight: 64 branch steps exactly consume a Keccak key. -/
theorem walk_tight : ((List.replicate 64 Step.branch).map advance).sum = 64 := by decide

/-- 5. Without the `sl ≥ 1` assumption the loop is not bounded by the key: an `ext 0` does not
advance. -/
theorem ext_zero_stalls : advance (.ext 0) = 0 := rfl

/-- 6. Cold accesses per block: `≤ 100,000`, tight. -/
theorem cold_le (c : Nat) (h : 2000 * c ≤ 200000000) : c ≤ 100000 := by omega

theorem cold_tight : 2000 * 100000 = 200000000 := by decide

/-- 7. Keccak calls of cold accesses in the block (one per key hash): `≤ 100,000`. Walk steps:
`≤ 65 · 100,000 = 6,500,000`. -/
theorem access_totals (c : Nat) (h : c ≤ 100000) : c ≤ 100000 ∧ 65 * c ≤ 6500000 := by omega

/-- 8. `compute_state_root`: `mpt_set` walk + `mpt_root` rehash per changed key, `≤ 2 · 65`,
over `≤ 100,000` keys: `≤ 13,000,000` node visits and `≤ 6,500,000` node hashes. -/
theorem state_root_totals (c : Nat) (h : c ≤ 100000) : 2 * 65 * c ≤ 13000000 ∧ 65 * c ≤ 6500000 := by
  omega

/-- 9. Witness lookups happen once per witness reference at init, bounded by the input entry
count `33,554,428`, not by gas. -/
theorem witness_lookups (n : Nat) (h : 4 * n ≤ 134217712) : n ≤ 33554428 := by omega

/-- 10. All per-access and state-root counts are linear: even at 1,000 ticks per node visit,
`13,000,000 · 1,000 + 6,500,000 · 1,000 = 19.5 G` ticks. -/
theorem linear_budget : 13000000 * 1000 + 6500000 * 1000 = 19500000000 := by decide

end InitECandidate.Solver.GuestMptTraversalAndStateRootBound
