import InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster`

**Code check (`guest.pp.pnk` wt-2).**
* `_mpt_insert_node` (l.4108) calls `node_invalidate(node)` (l.3749: clears `+8`/`+16`/`+24`,
  the cached RLP and hash) on **every** node of the descent path, then allocates at most
  `3` nodes (`_insert_into_leaf` → `_create_branch_from_two_leaves`: `1` branch + `≤ 2` leaves
  + `≤ 1` ext; `_split_extension`: branch + `≤ 1` ext + `1` leaf).
* `mpt_root` → `node_hash` → `node_rlp` → `_node_rlp_fill` (l.4415) re-encodes exactly the
  nodes with empty cache (`_node_needs_rlp`). So the rehashed set is the **union of the
  written keys' paths** in the final trie, not `3` nodes per write: every invalidated path node
  is rehashed once. New nodes lie on these paths.
* `compute_state_root` (l.14660): one storage trie per written account (`mpt_set` per dirty
  slot, `mpt_root` per account), then `mpt_set` per account in the state trie.

**Level bound.** Path node levels strictly increase (`0 … 64`). In one trie with `K` written
keys, distinct dirty nodes at level `d` are `≤ min(16^d, K)`, so dirty
`≤ D(K) = Σ_{d ≤ 64} min(16^d, K)` instead of `65 K`. Across many storage tries (one key per
account, deep witness paths per trie) the per-level sum is `Σ_a min(16^d, K_a)`, which reaches
`K` at every level: the `65 K` bound is then attained up to witness depth, so it stays the
unconditional bound.
-/

namespace InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def keys (G : Nat) : Nat := G / 100 / 21
def dirtyLevels (K : Nat) : Nat := ((List.range 65).map (fun d => min (16 ^ d) K)).foldl (· + ·) 0
def rootOld (G : Nat) : Nat := keys G * 65 * (30 + 633)
def rootLevel (G : Nat) : Nat := 65 * 30 * keys G + 633 * dirtyLevels (keys G)

def main200Single : Nat := 13378055156 - rootOld 200000000 + rootLevel 200000000
def main380Single : Nat := 21485139986 - rootOld 380000000 + rootLevel 380000000

/-- 1. Allocation per insert `≤ 3`, but rehashing covers the path: `3 K` vs `65 K`. -/
theorem alloc_vs_path : 3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470 := by decide

/-- 2. Level sums: `D(95,238) = 5,784,185`, `D(180,952) = 10,927,025` (vs `65 K`). -/
theorem level_sums : dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
    dirtyLevels 95238 < 65 * 95238 := by decide

/-- 3. Single-trie root rows: `3,847,103,205` (200M), `7,269,663,225` (380M). -/
theorem root_vals : rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
    rootOld 200000000 - rootLevel 200000000 = 257178405 := by decide

/-- 4. **Single-trie regime: `main200 = 13,120,876,751`, `68×` passes, `69×` fails.** -/
theorem main200_single : main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧
    yukon < 69 * main200Single := by decide

/-- 5. Single-trie regime: `main380 = 20,956,676,771`, `42×` passes, `43×` fails. -/
theorem main380_single : main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧
    yukon < 43 * main380Single := by decide

/-- 6. Many tries, one key each: per-level sum is `K` at every level ⇒ `65 K`; unconditional
`main200` stays `13,378,055,156` (`67×`, not `68×`). -/
theorem multi_trie : (List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
    67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156 := by decide

/-- 7. Sub-10 billion is out of reach by the root row alone: even with zero root ticks
`main200 > 9.2·10⁹`. -/
theorem no_sub_ten : 13378055156 - rootOld 200000000 = 9273773546 ∧
    9273773546 < 10000000000 ∧ 10000000000 < 13120876751 := by decide

end InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
