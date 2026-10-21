import InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster`

`_resolve_step` (l.3755, `guest.pp.pnk` wt-2): `nodedb_lookup` is called only when the child
item is a string (`it.0 == 0`) of length exactly `32` (`it.2 != 32 ⇒ mpt_fail(10)`); inline
lists return without a probe, the empty string returns `<0,…>`. A 32-byte string is
`0xa0 ‖ h` = **33 bytes** inside the parent's RLP body.

Under DAG memoization (assumed fix; the current Guest re-expands hash refs as a tree) every
distinct node body is decoded once, and node bodies are disjoint slices of the input
(`I = 134,217,712`). Hence resolve probes in decode `≤ ⌊I/33⌋ = 4,067,203`, not
`16 · 33,554,428`. `decode_witness_to_mpt` (l.3954) adds one root probe per decoded trie: the
state root plus one per storage root (`ws_storage_trie` memoizes by root), each fetched by a
`≥ 2,000`-gas cold access ⇒ `≤ G/2000` extra probes.

`decodeMemo` and `buildNodedb` are kept: their node count `I/4` is already a byte bound, and
lowering it needs a minimum RLP size per *accepted* node that is not proved here.
-/

namespace InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def hashRefs : Nat := inputBytes / 33
def probes (G : Nat) : Nat := 2 * 8 * (hashRefs + G / 2000)

def main200 : Nat := 32905132252 - 8589933568 + probes 200000000
def main380 : Nat := 41010777082 - 8589933568 + probes 380000000

/-- 1. Byte coupling: `h` disjoint 33-byte refs fit in `I` only if `h ≤ ⌊I/33⌋`. -/
theorem refs_bound (h : Nat) (hb : 33 * h ≤ inputBytes) : h ≤ 4067203 := by
  unfold inputBytes at hb; omega

/-- 2. The bound is attained: `4,067,203` refs use `134,217,699 ≤ I` bytes; one more does not fit. -/
theorem refs_tight : 33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204 := by decide

/-- 3. Old call count is `132×` the byte bound. -/
theorem ratio : 132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs := by decide

/-- 4. Probe rows: `65,075,248` from decode, plus `1,600,000` (200M) root probes. -/
theorem probe_vals : 2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
    probes 380000000 = 68115248 := by decide

/-- 5. Gain: `8,523,258,320` ticks at 200M. -/
theorem gain : 8589933568 - probes 200000000 = 8523258320 := by decide

/-- 6. **`main200 = 24,381,873,932`: `36×` passes, `37×` fails.** -/
theorem main200_slope : main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200 := by
  decide

/-- 7. **`main380 = 32,488,958,762`: `27×` passes, `28×` fails.** -/
theorem main380_slope : main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380 := by
  decide

/-- 8. Exact margins at the passing factors. -/
theorem margins : yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900 := by
  decide

/-- 9. `decodeMemo` is now the largest row: `> 44 %` of `main200`. -/
theorem decode_dominates : 100 * 10938743528 > 44 * main200 := by decide

/-- 10. Without memoization (tree decode, `1,110,441,952` calls at `r = 8`) the byte argument
fails: the same body is reread, so the old row stands. -/
theorem tree_no_coupling : 2 * 8 * hashRefs < 2 * 8 * 1110441952 := by decide

end InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
