import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecoverWk
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkHostPayloadHeaders
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1

/-! Wave 8 R32 (RunAttemptStrongR32): closure of the strong `run_attempt` bound.

`gbody_run_attempt_strong_of` (in `R16Shards.TopGbodyWk.GbodyRunAttempt`)
derives `TerminatingFunBoundedOn InputReadyStrong "run_attempt" K.«run_attempt»`
from 25 premises: 20 leaf contracts and 5 sub-`run_attempt` hypotheses. This
module supplies the 20 leaf premises from the proved, `sorry`-free deliveries
(`MergedLeaves`, `R11Adapters` closures, `R13Shards` shards, `R10Ports`,
`R16Shards.HeaderHashRecover*`, `Wave8Contracts.M08`/`M15`, and the
`WkHostPayloadHeaders` world steps), composing the `state_init` sub-bound from
its five proved leaves. The remaining 5 hypotheses stay explicit, named
premises of the exported theorem:

* `hexec` — the `execute_block` strong entry bound,
* `hph` — the `payload_header` entry bound at `InputReadyNwd`,
* `wph` — the `payload_header` world contract (`RetHeader`),
* `wsi` — the `state_init` world contract (`RetStateIn`),
* `wvhs` — the `validate_headers` strong world contract (`RetHeadersStrong`).

No `sorry`, `admit`, `axiom` or `native_decide` is used; every discharged
premise is a proved theorem from the imported (compiled, `sorry`-free)
modules listed above. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- The strong `run_attempt` terminating bound: `gbody_run_attempt_strong_of`
with all 20 leaf premises discharged from proved modules, and the five
sub-`run_attempt` hypotheses (`hexec`, `hph`, `wph`, `wsi`, `wvhs`) kept as
explicit named premises. -/
theorem gbody_run_attempt_strong_r32
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WorldKeeps InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers")) :
    TerminatingFunBoundedOn R16Shards.TopGbodyWk.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt» :=
  R16Shards.TopGbodyWk.gbody_run_attempt_strong_of
    Merged.fb_alloc
    R11Adapters.«fb_check_gas_limit»
    hexec
    R11Adapters.«fb_header_hash»
    R11Adapters.«fb_is_valid_versioned_hashes»
    Merged.fb_memeq
    Merged.fb_memzero
    R11Adapters.«fb_nodedb_build»
    hph
    (R13Shards.gbody_state_init Merged.fb_alloc
      ChainHandlersR31C1.g_decode_witness_to_mpt_r31 Merged.fb_htab_new
      R13Shards.WkShard01.«wk_alloc» R13Shards.WkShard01.«rt_alloc»)
    R11Adapters.«fb_validate_header»
    R11Adapters.«fb_validate_headers»
    R13Shards.WkShard01.«wk_alloc»
    R13Shards.WkShard01.«rt_alloc»
    R10Ports.ro_check_gas_limit
    R16Shards.HeaderHashRecover.«wk_header_hash_inside»
    R16Shards.«wk_is_valid_versioned_hashes»
    InitECandidate.Solver.Wave8Contracts.M15.«ro_memeq»
    InitECandidate.Solver.Wave8Contracts.M08.«wk_memzero»
    Merged.zv_memzero
    R16Shards.TopGbodyWk.«wk_nodedb_build»
    wph
    wsi
    R16Shards.TopGbodyWk.«wk_validate_header_strong»
    wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
