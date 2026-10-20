import InitECandidate.Solver.GuestMainLoopGasInvariant
import InitECandidate.Solver.SelfContainedMasterK

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestEpilogueAndKeccakBound`

Source facts (`Guest/guest.pp.pnk`):
* `keccak_f1600(stp)` (l.1065) is a single FFI call `@keccakf(stp, 0, stp, 200)`:
  the 24 rounds run outside `PanSem`, so its source cost is a constant number of ticks.
* `keccak256(p, n, out)` (l.1085) absorbs `n / 136` full blocks plus one padded block;
  each `keccak_absorb_block` is a 17-iteration XOR loop plus one `keccak_f1600`.
* `mpt_root` (l.4542) calls `node_hash` on the root; each touched key contributes
  `≤ 64` nibble levels, each hashing a node of `≤ 532` bytes (`≤ 4` keccak blocks).

Model: `keccakTicks base blk n = base + blk * (n / 136 + 1)`; a call charges EVM gas
`keccakGas n = 30 + 6 * ⌈n / 32⌉`. Per-key MPT epilogue: `64 * nodeTicks`, amortised
against `minGasPerKey = 1900`. The tick constants `base, blk, nodeTicks` are parameters
(their exact `PanSem` values are not derived here) with explicit sufficient bounds.
-/

namespace InitECandidate.Solver.GuestEpilogueAndKeccakBound

open InitECandidate.Solver
open InitECandidate.Solver.HtabLoadFactorBound
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.SourceWitnessClockBound
open InitECandidate.Solver.GuestMainLoopGasInvariant

/-- EVM `KECCAK256` gas on `n` bytes. -/
def keccakGas (n : Nat) : Nat := 30 + 6 * ((n + 31) / 32)

/-- Source ticks of `keccak256` on `n` bytes. -/
def keccakTicks (base blk n : Nat) : Nat := base + blk * (n / 136 + 1)

/-- Absorbed blocks of `keccak256` (full blocks + padded block). -/
def keccakBlocks (n : Nat) : Nat := n / 136 + 1

/-- Max MPT depth in nibbles, max hashed node size, and its keccak blocks. -/
def mptDepth : Nat := 64
def maxNodeBytes : Nat := 532

/-- Per-key MPT epilogue ticks. -/
def mptKeyTicks (nodeTicks : Nat) : Nat := mptDepth * nodeTicks

/-- 1. Gas covers absorbed blocks: `24 · (n / 136) ≤ 6 · ⌈n / 32⌉`. -/
theorem keccakGas_covers_blocks (n : Nat) : 24 * (n / 136) + 30 ≤ keccakGas n := by
  unfold keccakGas; omega

/-- 2. Keccak call amortisation: if `base ≤ 219·6` and `blk ≤ 219·24`, ticks ≤ `219 · gas`. -/
theorem keccakTicks_amortized (base blk n : Nat) (hb : base ≤ slope * 6) (hk : blk ≤ slope * 24) :
    keccakTicks base blk n ≤ slope * keccakGas n := by
  have hc := keccakGas_covers_blocks n
  unfold keccakTicks
  have h1 : blk * (n / 136 + 1) ≤ slope * 24 * (n / 136 + 1) := Nat.mul_le_mul_right _ hk
  have h2 : slope * (24 * (n / 136) + 30) ≤ slope * keccakGas n := Nat.mul_le_mul_left _ hc
  unfold slope at *; omega

/-- 3. A max-size MPT node fits in 4 keccak blocks. -/
theorem node_blocks : keccakBlocks maxNodeBytes = 4 := by decide

/-- 4. Per-key MPT epilogue amortised by the 1900-gas fresh-key charge iff `nodeTicks ≤ 6501`. -/
theorem mptKeyTicks_amortized_iff (nodeTicks : Nat) :
    mptKeyTicks nodeTicks ≤ slope * minGasPerKey ↔ nodeTicks ≤ 6501 := by
  unfold mptKeyTicks mptDepth slope minGasPerKey; omega

/-- 5. A node hash with keccak constants within the bounds of (2) costs `≤ 6570` ticks;
with `base + 4·blk ≤ 6501` it satisfies (4). -/
theorem node_hash_ticks_ok (base blk : Nat) (h : base + 4 * blk ≤ 6501) :
    mptKeyTicks (keccakTicks base blk maxNodeBytes) ≤ slope * minGasPerKey := by
  rw [mptKeyTicks_amortized_iff]; unfold keccakTicks; have : maxNodeBytes / 136 + 1 = 4 := by decide
  rw [this]; omega

/-- 6. Prologue + epilogue base fit `maxInputBytes` iff `epiBase ≤ 74,653,478`
(prologue = `SelfContainedMasterK.prologueTicks = 59,564,234`). -/
theorem prologue_epiBase_le_iff (epiBase : Nat) :
    SelfContainedMasterK.prologueTicks + epiBase ≤ Guest.maxInputBytes ↔ epiBase ≤ 74653478 := by
  unfold SelfContainedMasterK.prologueTicks; rw [maxInputBytes_eq]; omega

/-- 7. Building `AmortizedOk`: iterations that are either keccak calls or fresh-key
creations within the bounds above satisfy the interpreter invariant with
`epiPerKey = mptKeyTicks nodeTicks`. -/
theorem amortizedOk_of_keccak_and_keys (nodeTicks : Nat) (hn : nodeTicks ≤ 6501)
    (l : List Iter)
    (hl : ∀ it ∈ l, it.ticks + mptKeyTicks nodeTicks * it.keys ≤
      slope * (it.gas - minGasPerKey * it.keys) + slope * minGasPerKey * it.keys ∧
      minGasPerKey * it.keys ≤ it.gas) :
    AmortizedOk (mptKeyTicks nodeTicks) l := by
  intro it hit
  obtain ⟨h1, h2⟩ := hl it hit
  have hk := (mptKeyTicks_amortized_iff nodeTicks).2 hn
  have : slope * (it.gas - minGasPerKey * it.keys) + slope * minGasPerKey * it.keys =
      slope * it.gas := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.sub_add_cancel h2]
  omega

/-- 8. The keccak family of `SelfContainedMasterK` (30 gas, 60 ticks) respects the slope. -/
theorem keccak_family_slope :
    SelfContainedMasterK.worstTicks ≤ slope * SelfContainedMasterK.worstMinGas ∧
      SelfContainedMasterK.arithTicks ≤ slope * SelfContainedMasterK.arithMinGas := by decide

/-- 9. `refinedSourceClock` (459,564,194) lies below `maxGuestSourceClock` with margin. -/
theorem refinedSourceClock_le_max :
    SelfContainedMasterK.refinedSourceClock ≤ maxGuestSourceClock ∧
      maxGuestSourceClock - SelfContainedMasterK.refinedSourceClock = 43474653518 := by
  rw [(SelfContainedMasterK.refinedSourceClock_eq).1]; decide

/-- 10. Main: under the keccak/MPT constant bounds and `epiBase ≤ 74,653,478`, a non-timeout
run at `mainClock prologueTicks epiBase (mptKeyTicks nodeTicks) l` gives `kMin ≤ 43,934,217,712`. -/
theorem kMin_le_max_of_epilogue (s : Flapjack.PanSemStateFiniteExact 64 Guest.HostMemory)
    (hex : ∃ k, NotTO s k) (epiBase nodeTicks : Nat) (l : List Iter)
    (hepi : epiBase ≤ 74653478) (hamort : AmortizedOk (mptKeyTicks nodeTicks) l)
    (hg : totalGas l ≤ maxBlockGasLimit)
    (hrun : NotTO s (mainClock SelfContainedMasterK.prologueTicks epiBase (mptKeyTicks nodeTicks) l)) :
    kMin s hex ≤ maxGuestSourceClock :=
  (hbudget_of_interpreter_invariant s hex _ _ _ l hamort hg
    ((prologue_epiBase_le_iff epiBase).2 hepi) hrun).2

end InitECandidate.Solver.GuestEpilogueAndKeccakBound
