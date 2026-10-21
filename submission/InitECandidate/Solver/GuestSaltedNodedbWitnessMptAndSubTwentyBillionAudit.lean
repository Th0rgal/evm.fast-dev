import InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit`

**Dissection of `witnessMpt = 38,946,487,944`** (chain constants):
* memoized witness decode `10,938,743,528` (`τ < 1`, `≤ 33,554,428` nodes);
* `_resolve_step` probes `8,589,933,568` = `2 · r · 536,870,848` at **`r = 8`**: this row was
  **already priced salted** (no `L = 262,144` term anywhere in the chain);
* `mptPlusBuild − 619,060,000 = 19,417,810,848`: `19.5·10⁹` = `100,000` keys × `2·65` visits ×
  **`1,000` ticks/visit** (a placeholder), `536,870,848` for the two `nodedb_build` probes, minus
  the gas coupling of written keys.

**Recount with exact per-node ticks** (hand, `guest.pp.pnk` wt-2, from
`GuestKeccakAndMptExactTicks`: `nodeTicks = 633` per hashed node, Keccak `74 + 19` per 136-byte
block):
* `nodedb_build` ×2: `536,870,848` probes + `74 n + 19 ⌊I/136⌋` Keccak = `3,038,649,506`;
* cold walks (`get_storage` → `trie_lookup`, `≤ 65` nodes, `≤ 20` ticks/node): `G/2000` cold
  accesses × `1,300`;
* `compute_state_root`: written keys `≤ units/21`, `65` nodes each, `30` ticks insert + `633`
  rehash per node (`mpt_set` → `_mpt_insert_node`, `mpt_root` → `node_hash` → `node_rlp` + Keccak);
* tx/receipt tries: `2 · 16,666` keys × `7` levels × `663` = `154,693,812`.
`postEvm` recount: secp `500,040,000` + tries `154,693,812` + bloom `26,666,650` = `681,400,462`.
-/

namespace InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def decodeMemo : Nat := 10938743528
def probesR8 : Nat := 2 * 8 * 536870848
def buildNodedb : Nat := 536870848 + 74 * 33554428 + 19 * (134217712 / 136)
def walks (G : Nat) : Nat := G / 2000 * 65 * 20
def rootTicks (G : Nat) : Nat := G / 100 / 21 * 65 * (30 + 633)
def witnessMptSalted (G : Nat) : Nat := decodeMemo + probesR8 + buildNodedb + walks G + rootTicks G
def postEvmSalted : Nat := 500040000 + 2 * 16666 * 7 * 663 + 26666650
def otherRows : Nat := 268435424 + 300000000 + 20000000 + 2113920 + 10000

def main200 : Nat := 4831564234 + witnessMptSalted 200000000 + postEvmSalted + otherRows
def main380 : Nat := 9126364234 + witnessMptSalted 380000000 + postEvmSalted + otherRows

/-- 1. **Dissection** of the old `witnessMpt`. -/
theorem dissect : decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
    probesR8 = 8589933568 := by decide

/-- 2. The probe row was already at `r = 8`, i.e. salted: `2 · 8` ticks per call. -/
theorem probes_salted : probesR8 = 2 * 8 * (16 * 33554428) := by decide

/-- 3. The old MPT row used `1,000` ticks/visit; exact node work is `30 + 633 = 663`. -/
theorem visit_cost : 30 + 633 = 663 ∧ 663 < 1000 := by decide

/-- 4. Recounted rows: builds `3,038,649,506`, state root at 200M `4,104,281,610`. -/
theorem rows_200 : buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
    rootTicks 200000000 = 4104281610 := by decide

/-- 5. New `witnessMpt`: `26,801,608,212` (200M), `30,612,453,042` (380M). -/
theorem wm_vals : witnessMptSalted 200000000 = 26801608212 ∧
    witnessMptSalted 380000000 = 30612453042 := by decide

/-- 6. New `postEvm`: `681,400,462` (was `4,859,866,650`). -/
theorem post_val : postEvmSalted = 681400462 := by decide

/-- 7. **`main200 = 32,905,132,252`**, `27×` passes, `28×` fails. -/
theorem main200_slope : main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200 := by
  decide

/-- 8. **`main380`**: `21×` passes, `22×` fails. -/
theorem main380_slope : main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380 := by
  decide

/-- 9. `30×` is not reached: it needs `main200 < 30,023,997,515`. -/
theorem no_thirty : yukon / 30 = 30023997515 ∧ yukon < 30 * main200 := by decide

/-- 10. Dominant rows now: memo decode + probes = `19.5·10⁹`, `> 59 %` of `main200`. -/
theorem dominant : 100 * (decodeMemo + probesR8) > 59 * main200 := by decide

/-- 11. Lever: at `r = 1` (one probe per lookup, e.g. a perfect-hash `nodedb`) `main200` would
be `25,388,909,048`, `35×`. -/
theorem r1_lever : main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
    35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380 := by decide

end InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
