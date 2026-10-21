import InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster`

**`node2Ticks`** (same leaf helpers as `GuestKeccakAndMptExactTicks`, 2-item case of
`_node_rlp_fill` l.4415 / `_node_rlp_finish` l.4356 / `node_hash` l.4531):
≤ 2 frame visits + 1 `_node_needs_rlp` probe + `scratch_alloc` + `_node_rlp_begin` (`58`) +
finish (header lengths, list header, compact path `rlp_encode_bytes`, and either the value
`rlp_encode_bytes` or one `node_write_ref`: `227`) + hash. Keccak is kept at the generic
`532`-byte bound (`146`), not the 1-block size claimed in the prompt (the leaf value length is
not checked against `33` bytes in the code). Result **`439`** (branch: `633`).

**Joint LP** (variables `A K B E N₂ N₁₇ M`, all `≥ 0`):
`24A + 21K ≤ units`, `B + E ≤ 82A + 63K`, `B + E ≤ 66A + 64K`,
`B ≤ N₁₇ + K + A` (≤ 1 new branch per `mpt_set`), `E ≤ N₂ + 2(K + A)`,
`7N₂ + 22N₁₇ + 4M ≤ I`; maximise `1950K + 633B + 439E + 138N₂ + 416N₁₇ + 90M`
(refs `H` cost `0.5` tick/byte, dominated). Optima found by exact rational simplex, proved
here by `omega`.
-/

namespace InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def memTicks (n : Nat) : Nat := 1 + n / 8 + n % 8
def headerLenTicks : Nat := 1 + (1 + 8)
def writeHeaderTicks : Nat := 1 + (1 + 8) + (1 + 8)
def encodeBytesTicks : Nat := 1 + writeHeaderTicks + memTicks 532
def writeRefTicks : Nat := 1 + max (1 + 1 + memTicks 32) (memTicks 31)
def beginTicks : Nat := 1 + 1 + (1 + 32) + (1 + headerLenTicks) + (1 + 1 + headerLenTicks)
def finish2Ticks : Nat := 1 + (1 + 1 + headerLenTicks) + (1 + headerLenTicks) + 1
  + (1 + writeHeaderTicks) + encodeBytesTicks + max encodeBytesTicks (1 + writeRefTicks)
def keccakTicks532 : Nat := 1 + memTicks 200 + 19 * (532 / 136) + memTicks 136 + memTicks (532 % 136)
  + 19 + memTicks 32
def node2Ticks : Nat := 2 + 1 * 2 + 1 + beginTicks + finish2Ticks + (1 + 1 + 1 + keccakTicks532)

def inputBytes : Nat := 134217712
def keccakBlocks : Nat := 19 * (inputBytes / 136)
def cost (K B E n2 n17 m : Nat) : Nat := 1950 * K + 633 * B + 439 * E + 138 * n2 + 416 * n17 + 90 * m

def main200 : Nat := 6235124040 + keccakBlocks + 58999236680 / 9
def main380 : Nat := 10648364040 + keccakBlocks + 1179391270576 / 135

/-- 1. **`node2Ticks = 439`** (begin `58`, finish `227`, Keccak `146`). -/
theorem node2_val : beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439 := by
  decide

/-- 2. **Joint bound at 200M**: `9 · cost ≤ 58,999,236,680`. -/
theorem joint200 (A K B E n2 n17 m : Nat) (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    9 * cost K B E n2 n17 m ≤ 58999236680 := by
  unfold cost inputBytes at *; omega

/-- 3. **Joint bound at 380M**: `135 · cost ≤ 1,179,391,270,576`. -/
theorem joint380 (A K B E n2 n17 m : Nat) (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    135 * cost K B E n2 n17 m ≤ 1179391270576 := by
  unfold cost inputBytes at *; omega

/-- 4. Near-attainment at 200M (integer point): all-branch rehash fed by `5,961,084` witness
branches, `A = 5,556`, `K = 88,888`. -/
theorem near200 : 24 * 5556 + 21 * 88888 ≤ 2000000 ∧
    7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
    6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
      ≤ 20000 := by decide

/-- 5. **`main200 = 12,809,345,768`: `70×` passes, `71×` fails.** -/
theorem main200_slope : main200 = 12809345768 ∧ 70 * main200 < yukon ∧ yukon < 71 * main200 := by
  decide

/-- 6. **`main380 = 19,403,346,659`: `46×` passes, `47×` fails** (not `48×`). -/
theorem main380_slope : main380 = 19403346659 ∧ 46 * main380 < yukon ∧ yukon < 47 * main380 := by
  decide

/-- 7. Margins. -/
theorem margins : yukon - 70 * main200 = 4065721714 ∧ yukon - 46 * main380 = 8165979160 := by
  decide

end InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
