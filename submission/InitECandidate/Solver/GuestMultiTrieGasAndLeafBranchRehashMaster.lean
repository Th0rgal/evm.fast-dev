import InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster`

**Code check (`guest.pp.pnk` wt-2).**
* `op_sstore` (l.7499): cold slot `2,100` gas, warm `100`; a slot reaching `bs+32` needs a
  value change, `≥ 2,100 + …` gas in the first write; we keep `21` units/key.
* A storage trie for account `a` needs code running at `a`: a `CALL`-family access
  (`≥ 2,600` cold / `2,400` access-list), or `tx.to` (`12,000` intrinsic). We use
  **`24 A + 21 K ≤ units`**. `compute_state_root` (l.14660) also does one `mpt_set` per
  touched account in the state trie (`A` keys).
* Rehashed set = union of invalidated paths (`node_invalidate` l.3749, `_node_rlp_fill` l.4415).
  Dirty nodes `R ≤ Σ_d min(A·16^d, K) + Σ_d min(16^d, A) ≤ (1+16+65) A + 63 K` and
  `≤ 66 A + 64 K`.
* **Witness coupling.** Each `mpt_set` allocates `≤ 3` nodes; every other dirty node is a
  decoded witness node and is rehashed once (cache filled). So `W = R − 3(K + A)` witness nodes
  (`≥ 7` bytes each with SSZ offset) are taken from the `4 M + 7 N₂ + …` budget, cost
  `138` (build + decode) instead of `90 · 7/4` for empty entries.
* `_node_rlp_finish` (l.4356): 2-item nodes encode 2 items, branches 17; we keep the
  conservative `633` ticks per rehashed node (leaf/branch split not counted).

Rows: `base` = `main` minus old root row minus old witness row (`3,038,649,506`).
-/

namespace InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def keccakBlocks : Nat := 19 * (inputBytes / 136)
def base200 : Nat := 13378055156 - 4104281610 - 3038649506
def base380 : Nat := 21485139986 - 7798126440 - 3038649506

/-- Four times root + witness rows for `A` tries, `K` keys, `R` dirty nodes. -/
def rw4 (A K R : Nat) : Nat :=
  4 * (1950 * K + 633 * R + 138 * (R - 3 * K - 3 * A)) + 90 * (inputBytes - 7 * (R - 3 * K - 3 * A))

def main200 : Nat := base200 + keccakBlocks + (27655360747 + 3) / 4
def main380 : Nat := base380 + keccakBlocks + (41673550747 + 3) / 4

/-- 1. Bases: `6,235,124,040` and `10,648,364,040`. -/
theorem bases : base200 = 6235124040 ∧ base380 = 10648364040 := by decide

/-- 2. **Joint bound at 200M** over all `(A, K, R)` with the gas and dirty-node constraints. -/
theorem joint200 (A K R : Nat) (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K) (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 27655360747 := by
  unfold rw4 inputBytes at *; omega

/-- 3. **Joint bound at 380M.** -/
theorem joint380 (A K R : Nat) (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K) (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 41673550747 := by
  unfold rw4 inputBytes at *; omega

/-- 4. Integer near-optimum at 200M: `A = 5,555`, `K = 88,888`, `R = 82A + 63K`. -/
theorem near200 : rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
    24 * 5555 + 21 * 88888 ≤ 2000000 := by decide

/-- 5. **`main200 = 13,167,715,213`: `68×` passes, `69×` fails (unconditional in `A`).** -/
theorem main200_slope : main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200 := by
  decide

/-- 6. **`main380 = 21,085,502,713`: `42×` passes, `43×` fails.** -/
theorem main380_slope : main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380 := by
  decide

/-- 7. The worst case is not `A = 1`: many tries cost more than one. -/
theorem multi_worse : rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888) := by
  decide

/-- 8. Margins. -/
theorem margins : yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528 := by
  decide

end InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
