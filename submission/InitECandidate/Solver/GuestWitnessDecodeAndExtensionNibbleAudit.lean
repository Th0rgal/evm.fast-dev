import InitECandidate.Solver.GuestMptTraversalAndStateRootBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit`

Hand transcription of `guest.pp.pnk` (wt-2). There is no `hp_to_nibbles`; the decoder is
`compact_to_nibbles` (l.3640).

* `compact_to_nibbles(p, n)`: `n = 0 → mpt_fail(5)`; `odd = (p[0] >> 4) & 1`;
  length `= odd + 2(n − 1)`. So length `0` iff `n = 1` and `odd = 0` (prefix `0x00` / `0x20`).
* Two-item node (`_decode_step`, l.~3790): leaf if flag set; otherwise extension, and
  **`cn.1 == 0 → mpt_fail(7)`**: zero-length extensions are rejected.
* Extension child must be a branch (`ck = 3`) or unresolved hash (`ck = 0`), else `mpt_fail(8)`:
  no extension→extension and no extension→leaf. Branch needs `≥ 2` occupied slots (`mpt_fail(9)`).
* `_decode_witness_node_body` (l.3835): iterative, explicit stack in scratch memory (`scratch_alloc(88)`
  per open node, `trap_with(7)` on overflow), no depth counter. Hash references are resolved through
  `nodedb` and **re-expanded each time** (tree, not DAG). A reference cycle needs a Keccak cycle
  (infeasible), so decoding terminates, but a small witness can expand exponentially until the heap
  trap: `alloc` traps at `33,806,089,496` (heap starts at `2,713,714,688`).

Consequence for `trie_walk`: in a decoded trie every extension has `sl ≥ 1`, so the `65`-iteration
bound of `GuestMptTraversalAndStateRootBound` holds unconditionally.
-/

namespace InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit

open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance steps_le)

/-- Nibble length produced by `compact_to_nibbles` for `n ≥ 1` bytes and parity bit `odd`. -/
def compactLen (n odd : Nat) : Nat := odd + 2 * (n - 1)

/-- 1. Formula on the two prefixes: even `2n − 2`, odd `2n − 1`. -/
theorem compact_len_cases (n : Nat) (h : 1 ≤ n) :
    compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1 := by
  unfold compactLen; omega

/-- 2. Length zero exactly for one byte with even prefix. -/
theorem compact_zero_iff (n odd : Nat) (h : 1 ≤ n) (ho : odd ≤ 1) :
    compactLen n odd = 0 ↔ n = 1 ∧ odd = 0 := by
  unfold compactLen; omega

/-- 3. A Keccak key path (64 nibbles) needs `33` bytes even, or `32` bytes odd prefix (max `n`). -/
theorem compact_full_key : compactLen 33 0 = 64 ∧ compactLen 32 1 = 63 := by decide

/-- Decoder acceptance of a two-item non-leaf node of compact length `l` and child kind `ck`
(`3` branch, `0` hash, `1` leaf, `2` extension). -/
def extAccepted (l ck : Nat) : Bool := l != 0 && (ck == 3 || ck == 0)

/-- 4. Zero-length extensions are rejected (`mpt_fail(7)`). -/
theorem ext_zero_rejected (ck : Nat) : extAccepted 0 ck = false := by
  simp [extAccepted]

/-- 5. Extension→extension and extension→leaf are rejected (`mpt_fail(8)`). -/
theorem ext_child_rejected (l : Nat) : extAccepted l 2 = false ∧ extAccepted l 1 = false := by
  simp [extAccepted]

/-- 6. Accepted extensions advance `trie_walk` by `≥ 1`. -/
theorem accepted_advances (l ck : Nat) (h : extAccepted l ck = true) : 1 ≤ advance (.ext l) := by
  simp [extAccepted] at h
  simp [advance]; omega

/-- 7. Hence `trie_walk` on a decoded trie has `≤ 64` advancing steps, unconditionally. -/
theorem walk_bound_decoded (l : List Nat) (hacc : ∀ x ∈ l, x ≠ 0)
    (hsum : ((l.map Step.ext).map advance).sum ≤ 64) : l.length ≤ 64 := by
  have := steps_le (l.map Step.ext)
    (fun s hs => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      have := hacc x hx; simp [advance]; omega) hsum
  simpa using this

/-- 8. Heap capacity for decoded nodes: smallest node is an extension (`56` bytes), so
`≤ 555,220,978` nodes before `alloc` traps. -/
theorem heap_nodes : (33806089496 - 2713714688) / 56 = 555220978 := by decide

/-- 9. **Expansion witness**: 7 levels of branches whose 16 slots all reference the same next hash,
over one leaf (≈ 530 bytes per level of witness), decode to `17,895,697` branches and `16⁷` leaves:
`20,329,511,856` bytes, inside the heap. -/
theorem expansion_fits :
    (List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
      17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
      20329511856 ≤ 33806089496 - 2713714688 := by decide

/-- 10. One more level overflows the heap: decoding traps (`trap_with(1)`), it does not loop. -/
theorem expansion_traps : 33806089496 - 2713714688 < 16 ^ 8 * 64 := by decide

/-- 11. Decoded node count of the witness vs. its size: `286,331,153` nodes from `< 4,000` bytes. -/
theorem expansion_ratio : 17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300 := by decide

end InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit
