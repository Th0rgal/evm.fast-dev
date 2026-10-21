import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster`

Hand reading of `guest.pp.pnk` (wt-2). Conditional on the three fixes: salted `htab_hash`,
DAG-memoized witness decode, `nwd ≤ 16` in `decode_payload`.

**System calls are off the block gas budget.** `process_unchecked_system_transaction` (l.14972)
gives each call `30,000,000` gas (`st m + 40, 30000000`) and the result is never added to
`bo + 0` / `bo + 8` (only user txs do, l.15325). `execute_block` makes 2 unchecked calls
(beacon roots, history) and `process_general_purpose_requests` (l.15413) makes 4 checked ones
(withdrawal / consolidation requests, builder deposit / exit). Total gas `200M + 6 · 30M = 380M`.
The code run is whatever the witness holds at those addresses. Standard contracts are small;
adversarial code gets the full `380M` budget, i.e. `3,800,000` units instead of `2,000,000`.

**`build_block_access_list_rlp`** (l.6494): two passes over `bs+24` / `bs+8` (`htab_set` into
`bal_*`), `sort_elems` (merge sort, `n log n`) on accounts, per account three more `sort_elems`
and encoding loops. Entries are keys accessed in the block, each `≥ 2,000` gas (cold) ⇒
`≤ 190,000` keys at `380M`; `n log n` at `≤ 18` levels and `≤ 40` ticks per merge step plus
encoding: `≤ 300,000,000` ticks (conservative hand bound). Deposit log scan in
`process_general_purpose_requests`: one pass over logs, `≤ 20,000,000`.

Envelope rescaling at `3.8M` units: quadratic block term `B²/40 = 361·10⁹`; non-quadratic part
`56,088,992,805` scaled by `380/200`.
-/

namespace InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Subsystem table (ticks). -/
def gasEnv200 : Nat := 156088992805    -- EVM + 12 tables + ts+64 (L ≤ 5,000), 200M gas
def witnessMpt : Nat := 38946487944    -- witness decode (memo) + resolve probes r=8 + coupled MPT/nodedb
def postEvm : Nat := 4859866650        -- secp256k1 + tx/receipt tries + logs_bloom
def prologue : Nat := 268435424        -- SSZ + HTR + headers, 2 ticks/byte
def withdrawals16 : Nat := 2113920     -- 16 withdrawals, unsalted f = 8
def balRlp : Nat := 300000000          -- build_block_access_list_rlp
def requests : Nat := 20000000         -- deposit scan + compute_requests_hash
def output : Nat := 10000              -- serialize_result + output_write

def restTerms : Nat := postEvm + prologue + withdrawals16 + balRlp + requests + output

def main200 : Nat := gasEnv200 + witnessMpt + restTerms

/-- 1. System calls: `6 · 30M` extra gas, total `380M`. -/
theorem system_gas : 2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 := by decide

/-- 2. Withdrawal row at the spec cap. -/
theorem wd_row : 132000 * 16 + 8 * (16 * 15) = withdrawals16 := by decide

/-- 3. Non-gas rows sum: `5,450,425,994`. -/
theorem rest_val : restTerms = 5450425994 := by decide

/-- 4. **Main total, standard system contracts (200M budget)**: `200,485,906,743`. -/
theorem main_val : main200 = 200485906743 := by decide

/-- 5. `1×` margin `700,234,018,731`; `4×` passes, quarter margin `24,694,074,625`; `5×` fails. -/
theorem main_slopes : yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
    yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 := by decide

/-- Envelope rescaled to `3.8M` units: `B²/40` + scaled non-quadratic part. -/
def gasEnv380 : Nat := 3800000 * 3800000 / 40 + (156088992805 - 100000000000) * 380 / 200

def main380 : Nat := gasEnv380 + witnessMpt + restTerms

/-- 6. Rescaled envelope `467,569,086,329`. -/
theorem env380_val : gasEnv380 = 467569086329 := by decide

/-- 7. **Main total, adversarial system code (380M)**: `511,966,000,267`. -/
theorem main380_val : main380 = 511966000267 := by decide

/-- 8. `1×` still passes (margin `388,753,925,207`); `2×` fails. -/
theorem main380_slopes : yukon - main380 = 388753925207 ∧ yukon < 2 * main380 := by decide

/-- 9. Without memoization (heap decode) at 200M: `4×` fails. -/
theorem heap_4x_fails : yukon < 4 * (gasEnv200 + 68277256888 + restTerms) := by decide

/-- 10. BAL bound: `≤ 190,000` cold keys at `380M`, merge sort `≤ 18` levels × `40` ticks,
times `2` (sort + encode) fits `300M`. -/
theorem bal_bound (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp := by
  constructor
  · omega
  · decide

/-- 11. Dominant rows: gas envelope is `≥ 77 %` of `main200`. -/
theorem env_dominates : 100 * gasEnv200 ≥ 77 * main200 := by decide

end InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
