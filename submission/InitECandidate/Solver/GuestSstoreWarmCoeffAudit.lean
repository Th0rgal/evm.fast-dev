import InitECandidate.Solver.GuestCoupledTxBlockStorageBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSstoreWarmCoeffAudit`

Line-by-line audit (hand transcription of `Guest/guest.pp.pnk`, wt-2) of the `htab_find_slot`
calls of a warm `op_sstore` whose key `k` is already in `ts+32` (dirty in this tx).

Real line numbers: `jset` 5441, `get_account_optional` 5616, `stor_lookup` 5650,
`get_storage` **5658**, `get_storage_original` **5673**, `set_storage` 5767,
`is_warm_storage_key` 7472, `op_sstore` 7499 (the request's 5740/5752 are off).

Call graph of a warm `op_sstore` (find = one `htab_find_slot`):
1. `is_warm_storage_key` → `htab_has(ev+176, sk)`                           — storage cluster, local
2. `get_storage_original` → `htab_has(ts+56, addr)`                          — address table
3.   → `stor_lookup(bs+32)`: `htab_get(bs+32 outer, addr)`                  — address table
4.   →                       `htab_get(inner, key)`                          — storage cluster, block
5. `get_storage` → `htab_set(ts+24, sk)` (find)                              — storage cluster, local
6.   → `stor_lookup(ts+32)`: `htab_get(ts+32 outer, addr)`                  — address table
7.   →                       `htab_get(inner, key)` — hit ⇒ **return**        — storage cluster, local
     (`stor_lookup(bs+32)` and `record_pre_state_read` are skipped)
8. `set_storage` → `get_account_optional` → `htab_set(ts+8, addr)`          — address table
9.   → `htab_get(ts+16, addr)`                                               — address table
10.  → `htab_get(ts+32 outer, addr)`                                         — address table
11.  → `jset(inner, key)`: `htab_get(inner, key)`                            — storage cluster, local
12.  →                     `htab_set(inner, key)` (find)                     — storage cluster, local

Storage-cluster finds: local {1,5,7,11,12} = 5, block {4} = 1. Each costs `pFind = 2` per slot,
giving `(a, b) = (10, 2)`. Address-table finds (2,3,6,8,9,10) scan clusters of distinct
*addresses*, which cost ≥ 21 units each to create and are bounded separately; with one target
address they hold a single entry.

Multi-address: `ev+176`/`ts+24` use the 52-byte key `addr‖key` and see *all* keys of the tx;
inner tables see only `d_a`. Since `Σ_a d_a·w_a ≤ (Σ d_a)(Σ w_a)`, spreading over addresses
never increases the inner-table term; concentrating on one address is the worst case.
-/

namespace InitECandidate.Solver.GuestSstoreWarmCoeffAudit

open InitECandidate.Solver.GuestCoupledTxBlockStorageBound (a b kPanCoupled)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestSloadExactProbeTicks (pFind)

/-- Which cluster a `htab_find_slot` call scans. -/
inductive Tab | localStor | blockStor | addr
  deriving DecidableEq, Repr

/-- `get_storage` on a key present (`hit = true`) or absent in `ts+32`. -/
def getStorage (hit : Bool) : List Tab :=
  [.localStor, .addr, .localStor] ++ (if hit then [] else [.addr, .blockStor])

/-- Ordered finds of a warm `op_sstore`; `dirty` = key already in `ts+32`. -/
def sstoreWarm (dirty : Bool) : List Tab :=
  [.localStor] ++ [.addr, .addr, .blockStor] ++ getStorage dirty ++
    [.addr, .addr, .addr, .localStor, .localStor]

/-- Finds of a warm `op_sload` (`is_warm_storage_key` + `get_storage`). -/
def sloadWarm (hit : Bool) : List Tab := [.localStor] ++ getStorage hit

def cnt (t : Tab) (l : List Tab) : Nat := l.count t

/-- 1. Graph size: 12 finds for a dirty warm `SSTORE`, 14 for a clean one. -/
theorem sstore_len : (sstoreWarm true).length = 12 ∧ (sstoreWarm false).length = 14 := by decide

/-- 2. Short-circuit: a hit in `ts+32` removes the `bs+32` lookup of `get_storage`. -/
theorem getStorage_shortcircuit :
    cnt .blockStor (getStorage true) = 0 ∧ cnt .blockStor (getStorage false) = 1 := by decide

/-- 3. Dirty warm `SSTORE`: exactly 5 local and 1 block storage-cluster finds. -/
theorem sstore_dirty_counts :
    cnt .localStor (sstoreWarm true) = 5 ∧ cnt .blockStor (sstoreWarm true) = 1 ∧
      cnt .addr (sstoreWarm true) = 6 := by decide

/-- 4. Certified coefficients `(a, b) = (10, 2)` = counts × `pFind`. -/
theorem coeffs_certified :
    cnt .localStor (sstoreWarm true) * pFind = a ∧ cnt .blockStor (sstoreWarm true) * pFind = b := by
  decide

/-- 5. Clean warm `SSTORE` (key warm but not yet written in this tx): 5 local, **2** block finds,
i.e. `(10, 4)`. It turns the key dirty (`jset`), so it happens at most once per warmed key; its
extra block scan is charged once per 21-unit key, not per 1-unit probe. -/
theorem sstore_clean_counts :
    cnt .localStor (sstoreWarm false) = 5 ∧ cnt .blockStor (sstoreWarm false) = 2 := by decide

/-- 6. Warm `SLOAD`: dirty-hit `(3,0)`, miss `(3,1)`; both dominated by `(5,1)`. -/
theorem sload_dominated :
    cnt .localStor (sloadWarm true) = 3 ∧ cnt .blockStor (sloadWarm true) = 0 ∧
      cnt .localStor (sloadWarm false) = 3 ∧ cnt .blockStor (sloadWarm false) = 1 ∧
      cnt .localStor (sloadWarm false) ≤ cnt .localStor (sstoreWarm true) ∧
      cnt .blockStor (sloadWarm false) ≤ cnt .blockStor (sstoreWarm true) := by decide

/-- 7. Sub-additivity across addresses: `Σ dₐwₐ ≤ (Σ dₐ)(Σ wₐ)`. -/
theorem multi_addr (l : List (Nat × Nat)) :
    (l.map (fun p => p.1 * p.2)).sum ≤ (l.map Prod.fst).sum * (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    obtain ⟨d, w⟩ := x
    simp only [List.map_cons, List.sum_cons]
    have h1 : d * w ≤ d * w := le_refl _
    have e : (d + (t.map Prod.fst).sum) * (w + (t.map Prod.snd).sum)
        = d * w + d * (t.map Prod.snd).sum + (t.map Prod.fst).sum * w
          + (t.map Prod.fst).sum * (t.map Prod.snd).sum := by ring
    omega

/-- 8. Tightness of (7): equality for a single address. -/
theorem multi_addr_tight (d w : Nat) :
    ([(d, w)].map (fun p => p.1 * p.2)).sum = ([(d, w)].map Prod.fst).sum * ([(d, w)].map Prod.snd).sum := by
  simp

/-- 9. Strict loss when spreading: two addresses `(1,1),(1,1)` give `2 < 4`. -/
theorem multi_addr_strict :
    ([(1, 1), (1, 1)].map (fun p : Nat × Nat => p.1 * p.2)).sum <
      ([(1, 1), (1, 1)].map Prod.fst).sum * ([(1, 1), (1, 1)].map Prod.snd).sum := by decide

/-- 10. Single target address: the address tables hold one entry, so each of the 6 address
finds scans exactly 1 slot: constant `6 · pFind = 12` ticks, no quadratic term. -/
theorem addr_constant : cnt .addr (sstoreWarm true) * pFind * 1 = 12 := by decide

/-- 11. Target budget: `23,132 + 6·kPanCoupled = 785,125,408,508 < Yukon`. -/
theorem target_budget :
    23132 + 6 * kPanCoupled = 785125408508 ∧ 23132 + 6 * kPanCoupled < yukon := by decide

/-- 12. Yukon margin of the target budget. -/
theorem target_margin : yukon - (23132 + 6 * kPanCoupled) = 115594516966 := by decide

end InitECandidate.Solver.GuestSstoreWarmCoeffAudit
