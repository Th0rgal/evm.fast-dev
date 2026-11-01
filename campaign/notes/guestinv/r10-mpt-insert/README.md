# R10 guarded MPT insertion

Base: `664524baaf0aff6938ff399c2017a85b8ccc0c59` (`wave8/spec-r10`).

`ContractParts/C10.lean` now proves `gbody__mpt_insert_node` by assembling
`R10Shards/GbodyMptInsert.lean`. The `GBody.«_mpt_insert_node»` declaration is
unchanged, including all 17 callee assumptions. The proof uses the original AST
and original R10 budget; it does not assume the unproved callee contract leaves.

The source leaves were assembled from these fetched commits:

| Branch | Commit |
| --- | --- |
| `wave8/gbody-decomposed` | `ead8ebe88649ba8113ae84c293972f00d0e8e290` |
| `wave8/gbody-leaf-mpt-ins-count-astra` | `10f1cdcee4ce6f8222b7bba8804afe583782b345` |
| `wave8/gbody-leaf-mpt-ins-k0` | `e8d1cdfa461daa4b2516a60016a26044f453c6b8` |
| `wave8/gbody-leaf-mpt-ins-k1` | `d95bd24656b35b003e03b1a14de11f6334b57ccd` |
| `wave8/gbody-leaf-mpt-ins-k2-astra` | `0c2b54c254661ad22a3b34e8198b46eeadc14151` |
| `wave8/gbody-leaf-mpt-ins-k3` | `0cf74fb5aa2e9734bbdd0117e00b32c75ed19436` |

The R10 port carries `vlen < 2^40` and `klen ≤ 64` through active iterations,
checks the stronger callee-entry contracts, and preserves the added node-cache
and value-length bounds. It also accounts for R10's lookup-realizability premise
in `FunSpec` and zero-length cases in interval disjointness.

The loop proof allows cycles of empty extension nodes. A genuine cache warmup
strictly reduces the count of dirty cells in `[sourceBase, heapLimit)`. Between
warmups and level changes, a repeated parent slot determines the same whole
state except its clock, so a terminating run cannot repeat it. The parent slot
uses a key in `Fin (2^28)` and the phase is at most `2^36`; thus the iteration
count fits the existing `2^66 + 1` multiplier. No acyclicity assumption is added.

## Replay

Use the repository's pinned stock Lean 4.33.1 and a preseeded dependency cone.
The requested release `wave8-cone-r7` was not available in this repository.
The available release `wave8-cone-cache` supplied
`wave8-cone-flapjack-initecandidate.tar.zst`, SHA-256
`e57619335600890bce4f43801c85a1d4fd1ebe2833dec71c7c9844b0c56b0369`.
Its `PanTerminatingBounded.lean` source is unchanged at this R10 base.
Pinned Mathlib artifacts were fetched with `lake exe cache get`.

```bash
export ELAN_HOME=/var/lib/orb-node/work/elan
export PATH="$ELAN_HOME/bin:$PATH"
python3 campaign/notes/guestinv/r10-mpt-insert/verify.py \
  --log-dir /var/lib/orb-node/work/r10-mpt-final-replay
```

The replay rebuilds the R10 target import closure and supplied generic helper
using `lake env lean -j4 -M 12288`, checks the unchanged GBody declaration,
rejects placeholders in all new proof modules, and checks the final audit:

```text
'InitECandidate.Solver.Wave8GuestInv.gbody__mpt_insert_node' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit checks the guarded body itself via `#print axioms`. The unconditional
`gb__mpt_insert_node` still depends on the existing, separately unproved callee
contracts, as it did before this change. Unrelated existing R10 placeholders
are outside this delivery.

## Optional postcondition spec

`mpt_insert_node_spec` in C00 remains unproved. `wave8/integration` also leaves
it unproved and contains no `Deliveries/MPT_INSERT` proof. The termination
leaves retain the typed heap only while `go ≠ 0`; the postcondition requires
returned-root typing and a frame on every normal return. Completing it needs
stronger final-state invariants and proofs of the currently unproved constructor,
invalidation, leaf insertion and extension splitting contracts. This delivery
does not replace those proof obligations with assumptions or change their types.
