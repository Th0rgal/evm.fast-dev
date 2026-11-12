import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.Sha256
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpEnc
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyStateInit
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyPayloadHeaderExport
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodySysTxExecBlock
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.EvmInvR32
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero

/-!
# R32 `execute_block` and callee-closure contracts (wave8 guest-inv lane)

This module is the R32 worker's additive deliverable for the wave8
`ExecBlock + Callee Leaf Closure` goal. It owns exactly one new file (this
one) and adds:

* (Goal 1, `hkgso`) the honest R32-guarded `get_storage_original`
  `EvmKeeps` together with the `WitnessDbOK`-to-`DbTableAt` suppliers for
  the R32 invariants, plus a documented impossibility note for the
  unguarded form;
* (Goal 2, `hexec`/`hph`/`wph`/`wsi`/`wvhs`) the callee-leaf closures for
  `payload_header` (`hph`) and `state_init` (`hsi`) at their finest honest
  leaves, the `execute_block` strong re-export, the R32 conjunction-guard
  bridge for `hexec`, the guarded `wsi` re-export, and the open-leaf
  documentation for `wph`/`wvhs`;
* a capstone that plugs the `hph`/`hsi` closures into
  `gbody_run_attempt_strong_of`, leaving only the genuinely open leaves as
  named premises.

Nothing else in the tree is modified; every supplier used below is an
existing unconditional theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ExecBlockAndCalleeClosureR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Goal 1: the honest R32-guarded `get_storage_original` (`hkgso`)

The R32 statement `HkgsoR32` (in `ContractParts.Group10HonestR32`) asks for
an `EvmKeeps` for `get_storage_original` at the bare `EvmAvoids` guard.
That unguarded form is not honestly provable with the closure facts
available in this tree:

* the only proved `get_storage_original` `EvmKeeps` in the tree
  (`R16Shards.EvmEkFk.ek_get_storage_original_strong`) carries the
  witness-DB well-formedness conjunct `WitnessDbOK` in its guard, and
  `EvmAvoids` alone does not entail `WitnessDbOK`: every consumer of the
  storage read in the tree (including `ek_get_storage_original_of_decode_witness`
  behind the decode-witness route) keeps the DB condition as an explicit
  premise, and the corresponding `hdb_ok` universals over a plain `WorldOK`
  state are false in general;
* re-issuing the dispatch slot without the conjunct would require
  replaying the fixed unguarded `op_sstore` implementation in the R10
  dispatch shards, which this module does not own.

The honest ceiling is therefore the R32-guarded variants below: the strong
guard `EvmAvoids ∧ WitnessDbOK`, an `EvmInvR32 ∧ EvmAvoids` repackaging,
and the `WitnessDbOK`-to-`DbTableAt` suppliers that make the R32
invariants (`EvmInvR32`, `WorldOKR32`) carry the DB condition explicitly.
-/

/-- The honest R32-guarded `get_storage_original` `EvmKeeps`: the strong
supplier from `R16Shards.EvmEkFk.StorageCreateFinish`, guard
`EvmAvoids ∧ WitnessDbOK`, buffers `heap_ptr`/`scratch_ptr`. This is the
strongest form available without re-issuing dispatch-shard slots. -/
theorem hkgso_r32_strong :
    EvmKeeps
      (fun s =>
        EvmAvoids
          (fun s =>
            [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
             (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
             (globN s "mpt_nib_scratch",
               if globN s "mpt_nib_scratch" = 0 then 0 else 64)]) s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.«ek_get_storage_original_strong»

/-- Guard-conjunction repackaging of the honest `hkgso` supplier at the
full R32 EVM invariant: `EvmInvR32` already embeds `WitnessDbOK`
(together with `EvmInv` and the `vm_system_address` materialization), so
the strong supplier transports to the `EvmInvR32 ∧ EvmAvoids` guard. -/
theorem hkgso_r32_evmInvR32 :
    EvmKeeps
      (fun s =>
        EvmInvR32 s ∧
        EvmAvoids
          (fun s =>
            [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
             (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
             (globN s "mpt_nib_scratch",
               if globN s "mpt_nib_scratch" = 0 then 0 else 64)]) s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := R16Shards.EvmEkFk.«ek_get_storage_original_strong»
  exact ⟨ps, body, rt, hlk, fun s hc hP hv hnt hr =>
    hb s hc ⟨hP.2, hP.1.2.1⟩ hv hnt hr⟩

/-- The `hdb_ok` supplier at the R32 EVM invariant: `EvmInvR32` embeds
`WitnessDbOK`, and the proved `dbTableAt_of_witnessDbOK_so` turns it into
the `DbTableAt` (witness DB table) fact whenever `ws ≠ 0`. -/
theorem hdb_ok_of_evmInvR32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmInvR32 s) (hws : globN s "ws" ≠ 0) :
    R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt s (memW s (globN s "ws")) :=
  R16Shards.EvmEkFk.StorageCreateFinish.dbTableAt_of_witnessDbOK_so h.2.1 hws

/-- The `hdb_ok` supplier at the R32 world invariant: `WorldOKR32` is
defined as `WorldOK` plus exactly the implication
`ws ≠ 0 → NodeDbSlicesBounded s (memW s ws)`, and
`NodeDbSlicesBounded` is an abbreviation for `DbTableAt`, so the
definition hands back the table fact directly. -/
theorem hdb_ok_of_worldOKR32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WorldOKR32 s) :
    globN s "ws" ≠ 0 →
      R16Shards.EvmEkFk.StorageCreateFinish.DbTableAt s (memW s (globN s "ws")) :=
  fun hws => h.2 hws

/-! ## 2. Goal 2, part A: the callee-leaf closures for `hph` and `hsi`

`gbody_payload_header` (module `R16Shards.TopGbodyWk.GbodyPayloadHeaderExport`)
discharges the 17-premise contract `GBody.«payload_header»`
(`ContractParts.C18`) at guard `InputReadyNwd`. Fifteen of its premises
are closed by existing unconditional theorems; the two `build_mpt_indexed`
leaves stay explicit. Likewise `gbody_state_init`
(module `R16Shards.GbodyStateInit`) discharges the 5-premise contract
`GBody.«state_init»` (`ContractParts.C19`) at guard `WorldOK`, with only
the `decode_witness_to_mpt` bound left explicit.
-/

/-- `hph` closure: the `payload_header` bound at guard `InputReadyNwd`
from the finest honest callee leaves. All closed suppliers are existing
unconditional theorems; the two open leaves are the `build_mpt_indexed`
bound (`hmpt`, guard `BuildMptIndexedReady`) and its `NoExtra` world-keep
(`wmpt`). -/
theorem hph_r32_of_mpt
    (hmpt : TerminatingFunBoundedOn BuildMptIndexedReady
      (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    (wmpt : WorldKeeps WorldOK
      (fun s =>
        [(locN s "out", 32),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed")) :
    TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header» :=
  R16Shards.TopGbodyWk.«gbody_payload_header»
    Merged.fb_alloc
    R11Adapters.«fb_block_rlp_length»
    hmpt
    R11Adapters.Sha.fb_compute_requests_hash
    Merged.fb_encode_execution_requests
    Wave8Leaves.Rlp.«fb_encode_withdrawal_rlp»
    PrimShardP10P30.fb_keccak256
    Merged.fb_memzero
    R13Shards.WkShard01.«wk_alloc»
    R13Shards.WkShard01.«rt_alloc»
    R16Shards.PrimC08Closure.«wk_block_rlp_length»
    wmpt
    R16Shards.PrimC08Closure.«wk_encode_withdrawal_rlp»
    Merged.dm_encode_withdrawal_rlp
    R16Shards.PrimC08Closure.«wk_keccak256»
    Wave8Contracts.M08.«wk_memzero»
    Wave8Contracts.M29.«zv_memzero»

/-- `hsi` closure: the `state_init` bound at guard `WorldOK` from the
finest honest callee leaves. Four of the five premises of
`GBody.«state_init»` are closed by existing unconditional theorems; the
one open leaf is the `decode_witness_to_mpt` bound (`hdwtm`, guard
`ArenaReady`). -/
theorem hsi_r32_of_dwtm
    (hdwtm : TerminatingFunBoundedOn ArenaReady
      (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt») :
    TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init» :=
  R16Shards.«gbody_state_init»
    Merged.fb_alloc
    hdwtm
    PrimShardP10P30.fb_htab_new
    R13Shards.WkShard01.«wk_alloc»
    R13Shards.WkShard01.«rt_alloc»

/-! ## 3. Goal 2, part B: `hexec` — the honest R32 shape

`gbody_execute_block_strong` (module `R16Shards.TopGbodyWk.GbodySysTxExecBlock`)
proves the 39-premise contract `GBody.«execute_block_strong»` at guard
`BlockReadyExecStrong`. The `run_attempt` spine
(`gbody_run_attempt_strong_of`) consumes `execute_block` at the weaker
`BlockReadyExecAttemptStrong` guard
(`BlockReadyStrong ∧ InputReadyStrong ∧ journal_cap ≠ 0`).

The two guards are NOT inter-derivable in the honest direction the spine
would need: `BlockReadyExecStrong` adds `ExecBlock.EntryAt`, which demands
per-transaction content bounds (`p + n ≤ heap_ptr` for every tx-array
item), `wd_rlp_slices` per-item bounds, and block-hash conditions that
`InputAtStrong` (the `runAttemptCells` facts behind `InputReadyStrong`)
does not provide; and `BlockReadyExecAttemptStrong` does not provide the
`si`/`hdr` locals or `EntryAt` that `BlockReadyExecStrong` demands. The
honest R32 ceiling is therefore the conjunction guard below: at
`BlockReadyExecR32` both the spine premise and the strong post hold.
-/

/-- `hexec` re-export: the proved strong `execute_block` contract. -/
theorem hexec_execStrong_r32 :
    R16Shards.TopGbodyWk.GBody.«execute_block_strong» :=
  R16Shards.TopGbodyWk.gbody_execute_block_strong

/-- The honest R32 `hexec` guard: both the `run_attempt`-spine premise
(`BlockReadyExecAttemptStrong`) and the strong `execute_block` guard
(`BlockReadyExecStrong`) hold. -/
def BlockReadyExecR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong s ∧
      R16Shards.TopGbodyWk.BlockReadyExecStrong s

/-- The strong `execute_block` bound transports to the R32
conjunction guard: `BlockReadyExecR32` is a conjunction whose second
component is exactly `BlockReadyExecStrong`. -/
theorem hexec_r32_of_execStrong
    (h : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecStrong
      (ofString "execute_block") K.«execute_block») :
    TerminatingFunBoundedOn BlockReadyExecR32
      (ofString "execute_block") K.«execute_block» :=
  h.mono (fun _ hs => hs.2)

/-- Bridge (forward direction): a state satisfying the strong
`execute_block` guard plus `InputReadyStrong` also satisfies the
`run_attempt`-spine premise `BlockReadyExecAttemptStrong`; the spine
guard's three components come from the strong guard's `BlockReadyStrong`
component, `InputReadyStrong`, and `EntryAt`'s `journal_cap ≠ 0`
conjunct. (The converse direction is the honest gap documented above.)
This is the guard-level glue a spine replay would use to consume
`hexec_r32_of_execStrong` at the spine premise shape. -/
theorem blockReadyExecAttemptStrong_of_execStrong_inputReadyStrong
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hE : R16Shards.TopGbodyWk.BlockReadyExecStrong s)
    (hIR : R16Shards.TopGbodyWk.InputReadyStrong s) :
    R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong s :=
  ⟨hE.1, hIR, hE.2.2.1⟩

/-! ## 4. Goal 2, part C: `wsi`, `wph`, `wvhs` — guarded re-exports and open leaves

The `run_attempt` spine keeps three world-level callee contracts open:

* `wsi` (`state_init` `WorldReturnsIn` at guard `StateInitReady`): no
  unconditional supplier exists; the proved guarded variant
  `StrongBridges.wk_state_init_strong` strengthens the guard to
  `StateInitReady ∧ NodeDbSlicesBounded s (locN s "nodedb")` (via
  `wk_state_init_of_decode_witness` on the `decode_witness_to_mpt`
  spec). Re-exported below.
* `wph` (`payload_header` `WorldKeeps` at guard `InputReady`, post
  `RetHeader`): only reduction theorems exist
  (`wk_payload_header_of_bodyEffect` /
  `wk_payload_header_of_heapByteEff`), which need a body-effect premise
  that the spine does not provide. No unconditional supplier; left open.
* `wvhs` (`validate_headers` `WorldKeeps` at guard `WorldOK`, post
  `RetHeadersStrong`): no supplier exists anywhere in the tree with the
  `RetHeadersStrong` post (the legacy C08 stub is unproved). Left open;
  the exact required shape is the `wvhs` premise of the capstone below.
-/

/-- The guarded `wsi` re-export: the proved strong variant of the
`state_init` world contract, guard
`StateInitReady ∧ NodeDbSlicesBounded s (locN s "nodedb")`. -/
theorem wsi_r32_guarded :
    WorldReturnsIn
      (fun s => StateInitReady s ∧
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (locN s "nodedb"))
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"])
      (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init") :=
  StrongBridges.wk_state_init_strong

/-! ## 5. Capstone: the `run_attempt` spine with `hph`/`hsi` discharged

`gbody_run_attempt_strong_of` proves the `run_attempt` bound at guard
`InputReadyStrong` from 25 premises. The capstone below substitutes the
two callee-closure theorems of part A for the spine's `hph`/`hsi`
premises, so the `payload_header` and `state_init` bounds are consumed
at their finest honest leaves (`hmpt`/`wmpt`/`hdwtm`). Every other
premise is kept verbatim, named exactly as in the spine. The genuinely
open leaves after this substitution are: `hexec` (the `EntryAt`
content-bounds gap documented in part B — consumable at the
conjunction guard via `hexec_r32_of_execStrong` in a spine replay),
`wph` (body-effect gap), `wvhs` (no supplier with `RetHeadersStrong`
post), and the seven strong-post world-keeps/bounds that are the
R31-lane open leaves (`whh`, `wnb`, plus the `alloc`/`memzero`/
`check_gas_limit`/`memeq`/`validate_header` world specs and the eight
remaining TFB bounds).
-/

theorem run_attempt_r32_of_leaves
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcgl : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hhh : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (hvvh : TerminatingFunBoundedOn GuestInv
      (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hnb : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»)
    (hvh : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»)
    (hvhs : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»)
    (wal : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
      (ofString "alloc"))
    (rocgl : ReadOnlyFn (ofString "check_gas_limit"))
    (whh : WorldKeeps (fun s => WorldOK s ∧ R16Shards.TopGbodyWk.HeaderOKStrongLocal s)
      (fun s =>
        [(locN s "out", 32),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash"))
    (wvvh : WorldKeeps WorldOK (fun _ => []) ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "is_valid_versioned_hashes"))
    (romeq : ReadOnlyFn (ofString "memeq"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (zvmz : ZeroFills (ofString "memzero"))
    (wnb : WorldKeeps WorldOK
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetNodeDb (ofString "nodedb_build"))
    (wph : WorldKeeps InputReady
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
         (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
         (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvh : WorldKeeps R16Shards.TopGbodyWk.ValidateHeaderReady
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "validate_header"))
    (wvhs : WorldKeeps WorldOK
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers"))
    (hmpt : TerminatingFunBoundedOn BuildMptIndexedReady
      (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    (wmpt : WorldKeeps WorldOK
      (fun s =>
        [(locN s "out", 32),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed"))
    (hdwtm : TerminatingFunBoundedOn ArenaReady
      (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt») :
    TerminatingFunBoundedOn R16Shards.TopGbodyWk.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt» :=
  R16Shards.TopGbodyWk.gbody_run_attempt_strong_of
    hal hcgl hexec hhh hvvh hmeq hmz hnb
    (hph_r32_of_mpt hmpt wmpt) (hsi_r32_of_dwtm hdwtm) hvh hvhs
    wal rtal rocgl whh wvvh romeq wmz zvmz wnb wph wsi wvh wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ExecBlockAndCalleeClosureR32
