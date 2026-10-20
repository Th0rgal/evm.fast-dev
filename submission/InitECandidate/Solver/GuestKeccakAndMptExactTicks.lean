import InitECandidate.Solver.GuestEpilogueAndKeccakBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestKeccakAndMptExactTicks`

Tick accounting transcribed by hand from `Guest/guest.pp.pnk`, under the `PanSem` clock
rules of `Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean`:
* `.while`: 1 tick per executed body iteration (`decClockHOLFinite`), none for the exit test;
* `.call`: 1 tick (`callEntryStateHOLFinite`: `clock - 1`);
* `.extCall` (`@keccakf`, `@halt`, `@trap`): 0 ticks (no `decClock` in its equation);
* `.tick`: 1 tick (assumed absent from the pretty-printed source: none appears in it).
All other statements are free. Alignment-dependent branches take the worst case.

The counts are upper bounds ("≤"), not equalities derived from `PanSem` on the AST.
-/

namespace InitECandidate.Solver.GuestKeccakAndMptExactTicks

open InitECandidate.Solver
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestMainLoopGasInvariant
open InitECandidate.Solver.GuestEpilogueAndKeccakBound

/-! ## Leaf helpers (worst alignment) -/

/-- `memcpy`/`memzero` on `n` bytes, unaligned path: call + `n/8` + `n%8` iterations
(dominates the aligned path `n/32 + (n%32)/8 + n%8`). -/
def memTicks (n : Nat) : Nat := 1 + n / 8 + n % 8

/-- Aligned path is never worse than the unaligned one. -/
theorem mem_aligned_le (n : Nat) : 1 + n / 32 + (n % 32) / 8 + n % 8 ≤ memTicks n := by
  unfold memTicks; omega

/-- `keccak_f1600`: call + FFI `@keccakf` (0). -/
def keccakF1600Ticks : Nat := 1
/-- `keccak_absorb_block`: call + 17 XOR iterations + `keccak_f1600`. -/
def absorbTicks : Nat := 1 + 17 + keccakF1600Ticks

/-- `keccak256(p, n, out)`: call, `memzero(st,200)`, full blocks, `memzero(pad,136)`,
`memcpy(pad, ·, n % 136)`, padded block, output copy (`memcpy(out, st, 32)` worst). -/
def keccak256Ticks (n : Nat) : Nat :=
  1 + memTicks 200 + absorbTicks * (n / 136) + memTicks 136 + memTicks (n % 136)
    + absorbTicks + memTicks 32

/-- Extracted constants: `base = 74`, `blk = 19`. -/
def kBase : Nat := 74
def kBlk : Nat := 19

/-- 1. Per-block cost is exactly 19 ticks. -/
theorem absorbTicks_eq : absorbTicks = 19 := rfl

/-- 2. `keccak256` fits `keccakTicks 74 19 n`, tight at `n % 136 = 135`. -/
theorem keccak256Ticks_le (n : Nat) : keccak256Ticks n ≤ keccakTicks kBase kBlk n ∧
    keccak256Ticks 135 = keccakTicks kBase kBlk 135 := by
  refine ⟨?_, by decide⟩
  unfold keccak256Ticks keccakTicks kBase kBlk absorbTicks keccakF1600Ticks memTicks
  have : n % 136 < 136 := Nat.mod_lt _ (by decide)
  omega

/-- 3. The constants satisfy the sufficient bounds of `GuestEpilogueAndKeccakBound`. -/
theorem keccak_constants_ok : kBase ≤ slope * 6 ∧ kBlk ≤ slope * 24 ∧ kBase ≤ 1314 ∧ kBlk ≤ 5256 := by
  decide

/-- 4. Hence every `keccak256` call is amortised by its EVM gas `30 + 6⌈n/32⌉`. -/
theorem keccak256_amortized (n : Nat) : keccak256Ticks n ≤ slope * keccakGas n :=
  Nat.le_trans (keccak256Ticks_le n).1
    (keccakTicks_amortized kBase kBlk n keccak_constants_ok.1 keccak_constants_ok.2.1)

/-! ## MPT node cost (`_node_rlp_fill` frame + `_node_rlp_finish` + hash) -/

/-- `rlp_be_len`/`rlp_put_be` on a 64-bit value: call + ≤ 8 iterations. -/
def beTicks : Nat := 1 + 8
/-- `rlp_header_len`: call + `rlp_be_len`. -/
def headerLenTicks : Nat := 1 + beTicks
/-- `rlp_write_header`: call + `rlp_be_len` + `rlp_put_be`. -/
def writeHeaderTicks : Nat := 1 + beTicks + beTicks
/-- `rlp_encode_bytes` of `≤ maxNodeBytes` bytes. -/
def encodeBytesTicks : Nat := 1 + writeHeaderTicks + memTicks maxNodeBytes
/-- `node_write_ref` excluding the child's own hash: call + max(memcpy 32+1 alloc path, memcpy <32). -/
def writeRefTicks : Nat := 1 + max (1 + 1 + memTicks 32) (memTicks 31)
/-- `_node_rlp_finish`, branch case (dominates leaf/extension). -/
def finishTicks : Nat :=
  1 + 16 * (1 + 1) + (1 + 1 + headerLenTicks) + (1 + headerLenTicks) + 1
    + (1 + writeHeaderTicks) + 16 * (1 + writeRefTicks) + encodeBytesTicks
/-- `_node_rlp_begin`, leaf case (dominates): alloc, compact of 64 nibbles, two lengths. -/
def beginTicks : Nat := 1 + 1 + (1 + 32) + (1 + headerLenTicks) + (1 + 1 + headerLenTicks)
/-- `_node_rlp_fill` per node: ≤ 17 frame visits, ≤ 16 `_node_needs_rlp` probes,
one `scratch_alloc`, one begin, one finish. -/
def fillPerNodeTicks : Nat := 17 + 16 * (1 + 1) + 1 + beginTicks + finishTicks
/-- `node_hash`/`node_hash_cached` on one node: call + `node_rlp` call + alloc + keccak. -/
def nodeHashTicks : Nat := 1 + 1 + 1 + keccak256Ticks maxNodeBytes
/-- Extracted per-node cost. -/
def nodeTicksVal : Nat := fillPerNodeTicks + nodeHashTicks

/-- 5. Exact value of the extracted per-node bound. -/
theorem nodeTicksVal_eq : nodeTicksVal = 633 ∧ keccak256Ticks maxNodeBytes = 146 := by decide

/-- 6. `nodeTicks ≤ 6501`, so the per-key MPT epilogue (`64 · 633 = 40,512`) is amortised
by the 1900-gas fresh-key charge (`219 · 1900 = 416,100`). -/
theorem nodeTicks_ok : nodeTicksVal ≤ 6501 ∧ mptKeyTicks nodeTicksVal = 40512 ∧
    mptKeyTicks nodeTicksVal ≤ slope * minGasPerKey := by
  refine ⟨by decide, by decide, (mptKeyTicks_amortized_iff _).2 (by decide)⟩

/-- `mpt_root` constant part: call + `memcpy(out, ·, 32)`; node work is per key. -/
def epiBaseVal : Nat := 1 + memTicks 32 + 1

/-- 7. `epiBase` satisfies the prologue budget `prologueTicks + epiBase ≤ maxInputBytes`. -/
theorem epiBase_ok : epiBaseVal = 7 ∧
    SelfContainedMasterK.prologueTicks + epiBaseVal ≤ Guest.maxInputBytes :=
  ⟨rfl, (prologue_epiBase_le_iff epiBaseVal).2 (by decide)⟩

/-- 8. `AmortizedOk` with the extracted `epiPerKey = 40,512`: any iteration whose own ticks
fit `219 ·` (gas not spent on fresh keys) is accepted. -/
theorem amortizedOk_extracted (l : List Iter)
    (hl : ∀ it ∈ l, minGasPerKey * it.keys ≤ it.gas ∧
      it.ticks ≤ slope * (it.gas - minGasPerKey * it.keys)) :
    AmortizedOk (mptKeyTicks nodeTicksVal) l := by
  apply amortizedOk_of_keccak_and_keys nodeTicksVal nodeTicks_ok.1 l
  intro it hit
  obtain ⟨h1, h2⟩ := hl it hit
  have hk := nodeTicks_ok.2.2
  have : mptKeyTicks nodeTicksVal * it.keys ≤ slope * minGasPerKey * it.keys :=
    Nat.mul_le_mul_right _ hk
  exact ⟨by omega, h1⟩

/-- 9. A `KECCAK256` opcode iteration (no fresh key) satisfies the side condition of (8). -/
theorem keccak_iter_ok (n : Nat) :
    minGasPerKey * 0 ≤ keccakGas n ∧
      keccak256Ticks n ≤ slope * (keccakGas n - minGasPerKey * 0) := by
  refine ⟨Nat.zero_le _, ?_⟩
  simpa using keccak256_amortized n

/-- 10. End-to-end: with the extracted constants, a non-timeout run at the decomposed
`"main"` clock gives `kMin ≤ 43,934,217,712`. -/
theorem kMin_le_max_extracted (s : Flapjack.PanSemStateFiniteExact 64 Guest.HostMemory)
    (hex : ∃ k, SourceWitnessClockBound.NotTO s k) (l : List Iter)
    (hl : ∀ it ∈ l, minGasPerKey * it.keys ≤ it.gas ∧
      it.ticks ≤ slope * (it.gas - minGasPerKey * it.keys))
    (hg : totalGas l ≤ maxBlockGasLimit)
    (hrun : SourceWitnessClockBound.NotTO s
      (mainClock SelfContainedMasterK.prologueTicks epiBaseVal (mptKeyTicks nodeTicksVal) l)) :
    SourceWitnessClockBound.kMin s hex ≤ GuestGasAndHtabBound.maxGuestSourceClock :=
  kMin_le_max_of_epilogue s hex epiBaseVal nodeTicksVal l (by decide)
    (amortizedOk_extracted l hl) hg hrun

end InitECandidate.Solver.GuestKeccakAndMptExactTicks
