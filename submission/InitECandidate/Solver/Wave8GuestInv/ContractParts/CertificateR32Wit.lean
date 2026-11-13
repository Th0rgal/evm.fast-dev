import InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryWitR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeStatelessSlicesR32

/-! Wave 8 R32 (CertificateR32Wit): the honest certificate without the
`state_init` world premise.

`CertificateR32Null.certificateR32_of_witness_null` carries five leaf
premises, `hexec`, `hph`, `wph`, `wsi`, `wvhs`. `GbodyRunAttemptWitR32` bounds
`run_attempt` without `wsi` once the witness slices of the input are known to
be `WitnessSliceOK` at the `run_attempt` entry, and `MainEntryWitR32` carries
that fact from the `decode_host_input` exit through the main entry. This
module restates the certificate on top of the two.

* `certificateR32_of_witness_wit` — five leaf premises, `hexec`, `hph`, `wph`,
  `wdw`, `wvhs`: `wsi` is traded for the decode post `wdw` (when
  `decode_host_input` returns the word `w` from a `WorldOK` state, every
  16-byte slice record of the witness list of `w` is
  `StorageCreateFinish.WitnessSliceOK` in the exit state).
* `wdw_of_decode` — `wdw` is proved: it is the node-list component of
  `DecodeSlicesR32.wk_decode_host_input_slices_sound`.
* `certificateR32_wit` — four leaf premises, `hexec`, `hph`, `wph`, `wvhs`,
  verbatim those of `certificateR32_of_witness_null`. Neither `wsi` nor `wdw`
  is a premise. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Wit

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

/-- The honest R32 certificate with the decode post `wdw` in place of the
`state_init` world premise `wsi`: five leaf premises. -/
theorem certificateR32_of_witness_wit
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header") K.«payload_header»)
    (wph : WorldKeeps (GbodyRunAttemptNullR32.InputReadyZ True)
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
    (wdw : FunSpec WorldOK
      (fun _ r post => ∀ w : BitVec 64, r = some (.returned (.val (.word w))) →
        ∀ j, j < memW post (w.toNat + 48) →
          R16Shards.EvmEkFk.StorageCreateFinish.WitnessSliceOK post
            (memW post (w.toNat + 40) + 16 * j))
      (ofString "decode_host_input"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers")) :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (MainEntryWitR32.mainEntryR32_wit_of_leaves hexec hph wph wdw wvhs)))))

/-- The decode witness-slice post: the node-list component of
`DecodeSlicesR32.wk_decode_host_input_slices_sound`. -/
theorem wdw_of_decode : MainEntryWitR32.WdwLeaf := by
  obtain ⟨ps, b, rs, hl, hq⟩ := DecodeSlicesR32.wk_decode_host_input_slices_sound
  refine ⟨ps, b, rs, hl, fun {F} s hc hW hv hnt w hr => ?_⟩
  have hstep := hq s hc hW hv hnt (Or.inl ⟨_, hr⟩)
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  obtain ⟨S', Nd', _, _, _, _, hQ⟩ := hstep.2.2.2.2 S Nd hWT (fun i hi j hj => by
    change i ∈ [bufferRegion s ("ssz_offs", 64)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact bufferRegion_disj_le hWT ("ssz_offs", 64) (by decide) (by decide) 64 le_rfl j hj)
  exact (hQ.2 _ w hr rfl).1

/-- The honest R32 certificate from four leaf premises: `hexec`, `hph`, `wph`
at the null-tolerant guards and `wvhs`. -/
theorem certificateR32_wit
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header") K.«payload_header»)
    (wph : WorldKeeps (GbodyRunAttemptNullR32.InputReadyZ True)
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
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers")) :
    InitE.Certificate submission (.finite K_target) :=
  certificateR32_of_witness_wit w same hexec hph wph wdw_of_decode wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Wit
