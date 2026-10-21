import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster`

(`submission/Proofs/Source.lean` does not exist in wt-2; counts are on `Guest/guest.pp.pnk`.
There is no `decode_trie_nodes_list`; witness lists go through `decode_bytes_list` (l.2973) →
`ssz_split_var_list` (l.2859), then `nodedb_build` (l.3691).)

**Witness entry, exact.** `ssz_split_var_list`: 1 `while` tick per entry. `nodedb_build`: 1
`while` + `keccak256` + `htab_set`. `keccak256(p, 0)` (l.1085): call 1, `memzero 200` aligned 8,
no full block, `memzero 136` 6, `memcpy 0` 1, `keccak_absorb_block` 1 + 17 + `keccak_f1600` 1,
aligned output 0 ⇒ **35**. All empty entries hash to the same key: `htab_set` finds it at the
first probe (`htab_find_slot` + `htab_hash` + 1 `while` + `memeq` ≈ 5): **`43` per empty entry**
(4 bytes, the SSZ offset). A distinct short entry (`≥ 5` bytes) pays a fresh insert with `L ≤ 8`
probes and amortized grow: **`79`**. Witness nodes: leaf/ext `79 + 48 = 127`, branch
`79 + 326 = 405` (Keccak of `≤ 135` bytes is one block). The previous `90`/`138`/`416` used the
generic `74`-tick Keccak.

**`PUSHn`, exact.** `tmp = alloc(32)` is 8-aligned, so `u256_from_be` takes the `while` path for
`n < 32` (`n` ticks) and the aligned path for `n = 32`. Fixed calls: `op_dispatch`, `op_push`,
`charge_gas`, `heap_mark`, `alloc`, `buffer_read`, `heap_release`, `stack_push`, `pc_add` + loop.
`PUSH31` with unaligned source: `memcpy 31` = 11, `memzero 0` = 1, `u256_from_be` 32 ⇒
**54 = 18 · 3**. A `PUSH` truncated by the code end (`memzero` of the tail) can reach `59`, but
only once per frame (execution stops after it); charged in the per-frame slack.
`JUMPDEST` 5/1 gas, `PUSH0` 13/2 gas, `STOP` 4/0 gas but ends the frame.
-/

namespace InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def fixed200 : Nat := 1391298018
def fixed380 : Nat := 1675717026

def keccakEmpty : Nat := 1 + 8 + 6 + 1 + (1 + 17 + 1)
def push31 : Nat := 7 + 11 + 1 + 32 + 3

/-- Cached Guest: `P` in gas units at `18` ticks/gas. -/
def costC (A K B E n2 n17 md ms P : Nat) : Nat :=
  349 * A + 2060 * K + 633 * B + 439 * E + 127 * n2 + 405 * n17 + 43 * md + 79 * ms + 18 * P
/-- Uncached Guest: adds `C` calls (`67,884`) and per-tx scans (`66,562`). -/
def costU (A K B E n2 n17 md ms P C T : Nat) : Nat :=
  costC A K B E n2 n17 md ms P + 67884 * C + 66562 * T

def mainCached200 : Nat := fixed200 + inputBytes + (214138410040 + 32) / 33
def mainCached380 : Nat := fixed380 + inputBytes + (114947567578464 + 11802) / 11803
def mainUncached200 : Nat := fixed200 + (25461560820280 + 230) / 231
def mainUncached380 : Nat := fixed380 + (47863280820280 + 230) / 231

/-- 1. Exact leaf counts: empty Keccak `35`, `PUSH31` `54 = 18 · 3`. -/
theorem leaf_counts : keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 := by decide

/-- 2. **Cached, 200M.** -/
theorem cached200 (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P ≤ 214138410040 := by
  unfold costC inputBytes at *; omega

/-- 3. **Cached, 380M.** -/
theorem cached380 (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 := by
  unfold costC inputBytes at *; omega

/-- 4. **Uncached full LP, 200M** (closes the `(B, E, N₂, N₁₇)` reserve). -/
theorem uncached200 (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 := by
  unfold costU costC inputBytes at *; omega

/-- 5. **Uncached full LP, 380M.** -/
theorem uncached380 (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 := by
  unfold costU costC inputBytes at *; omega

/-- 6. **Cached: `112×` at 200M, `77×` at 380M.** -/
theorem cached_slopes : mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
    yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 := by decide

/-- 7. **Uncached: `8×` at 200M, `4×` at 380M.** -/
theorem uncached_slopes : mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 := by decide

/-- 8. The `135×` target needs `main ≤ 6,671,999,447`: not reached. -/
theorem no_135 : yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200 := by decide

end InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
