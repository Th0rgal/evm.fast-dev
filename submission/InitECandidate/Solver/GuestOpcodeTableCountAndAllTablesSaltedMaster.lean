import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster`

**Hash-table finds per 100-gas opcode** (hand count, `guest.pp.pnk` wt-2):
* warm `SLOAD` (`op_sload` l.7482, 100 gas): `is_warm_storage_key` → `htab_has(ev+176)` (1);
  `get_storage` (l.5658) → `htab_set(ts+24)` (find + insert: 2), `stor_lookup(ts+32)` (2:
  outer address table + inner key table), `stor_lookup(bs+32)` (2) ⇒ **7 finds**.
* `TLOAD` (l.7553): `htab_get(ts+64)` ⇒ 1. `TSTORE` (l.7564): `jset(ts+64)` = `htab_get` +
  `htab_set` (find + insert) ⇒ 3. Warm `BALANCE` & co (l.7583): `is_warm_address(ev+168)` (1) +
  `get_account` (`ts+8` set, `ts+16` get, `bs+16` get ⇒ ≤ 5) ⇒ ≤ 6.
* Cold accesses (≥ 2,000 gas = 20 units) do a bounded number of finds plus two trie walks
  (`≤ 65` steps each): far below the warm-`SLOAD` ratio per unit.
* Every journaled write is undone at most once (`state_restore`, `htab_del` shift `≤ 3 L`), and
  `htab_grow` rehashes amortize to `≤ 1` re-insert per insert.
We charge **`≤ 12` table operations per unit** (7 + 1 undo + 1 grow + slack) at
**`12 + 2 L = 28` ticks** each (`L = 8`): **`336` ticks/unit**.

**Salting the residual of `156,088,992,805`.** Its decomposition (`GuestElevenTablesSharedBudgetAbsorption`):
linear `3,659,564,234` + merge scan `500,000,000` + `151,929,428,571`, where the last term is the
absorbed bound of `blk` (unsalted `B²/40`), `13·loc` (unsalted per-tx `M·B/84`) and the
`ev+176`/`ev+168` truncation and probe terms. All of these are collision-run terms; with runs `≤ L`
they are covered by the per-unit table charge. So the salted envelope is
`linear + merge + 336 · units`.

`L = 8` is the expected run at load `≤ 1/2` under a secret salt, not a worst case.
-/

namespace InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Ticks of one salted table operation and of one 100-gas unit. -/
def opTicks (L : Nat) : Nat := 12 + 2 * L
def unitTicks : Nat := 12 * opTicks 8

/-- Non-gas rows of `main` (witness, MPT, post-EVM, prologue, BAL, requests, withdrawals, output). -/
def restMain : Nat := 200485906743 - 156088992805

def env200 : Nat := 3659564234 + 500000000 + unitTicks * 2000000
def env380 : Nat := (59564234 + 18 * 380000000) + 950000000 + unitTicks * 3800000

def main200AllSalted : Nat := env200 + restMain
def main380AllSalted : Nat := env380 + restMain

/-- 1. Warm-`SLOAD` find count `1 + 2 + 2 + 2 = 7` is the max over 100-gas opcodes counted
(`TLOAD 1`, `TSTORE 3`, warm account ops `≤ 6`). -/
theorem finds_max : 1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7 := by decide

/-- 2. Per-unit table ticks: `12 · 28 = 336`. -/
theorem unit_val : opTicks 8 = 28 ∧ unitTicks = 336 := by decide

/-- 3. Decomposition of the unsalted envelope: the collision part is `151,929,428,571`. -/
theorem env_split : 3659564234 + 500000000 + 151929428571 = 156088992805 ∧
    151929428571 = 100000000000 + 51929428571 := by decide

/-- 4. Salted envelopes: `4,831,564,234` (200M) and `9,126,364,234` (380M). -/
theorem env_vals : env200 = 4831564234 ∧ env380 = 9126364234 := by decide

/-- 5. Rest of `main`: `44,396,913,938`. -/
theorem rest_val : restMain = 44396913938 := by decide

/-- 6. **`main200_all_salted = 49,228,478,172`: `18×` passes, `19×` fails.** -/
theorem main200_slope : main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
    yukon < 19 * main200AllSalted := by decide

/-- 7. **`main380_all_salted = 53,523,278,172`: `16×` passes, `17×` fails.** -/
theorem main380_slope : main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
    yukon < 17 * main380AllSalted := by decide

/-- 8. Sensitivity of the per-unit table charge: `18×` holds up to `741` ticks/unit at 200M,
`16×` up to `1,065` at 380M (exact). -/
theorem unit_slack :
    18 * (3659564234 + 500000000 + 741 * 2000000 + restMain) < yukon ∧
      yukon ≤ 18 * (3659564234 + 500000000 + 742 * 2000000 + restMain) ∧
    16 * (59564234 + 18 * 380000000 + 950000000 + 1065 * 3800000 + restMain) < yukon ∧
      yukon ≤ 16 * (59564234 + 18 * 380000000 + 950000000 + 1066 * 3800000 + restMain) := by decide

/-- 9. Run-length sensitivity at `12` ops/unit: `18×` (200M) holds for `L ≤ 24`. -/
theorem run_slack : 12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25 := by decide

/-- 10. Gain over the partially salted totals of the previous module. -/
theorem gain : 102485906743 - 49228478172 = 53257428571 ∧
    154766000267 - 53523278172 = 101242722095 := by decide

/-- 11. The non-gas rows now dominate `main200` (`> 90 %`). -/
theorem rest_dominates : 10 * restMain > 9 * main200AllSalted := by decide

end InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
