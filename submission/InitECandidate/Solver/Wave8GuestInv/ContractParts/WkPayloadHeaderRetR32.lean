import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkHostPayloadHeaders

/-! Wave 8 R32 (WkPayloadHeaderRetR32): a reduction of the `payload_header`
world contract (the `wph` leaf of `CertificateR32Core`) whose return premise
is only asked on the normal-return branch.

`WkHostPayloadHeaders` has two reductions of this contract.
`wk_payload_header_of_bodyEffect` asks for a normal word return on every
`InputReady` state, which the guest body does not give (`throw BlockErr 7`).
`wk_payload_header_of_heapByteEff` asks for `RetHeader` of an arbitrary
result and exit state. `RetHeader` itself only speaks about `returned`
results, so the reduction below asks for the header-cell facts exactly
there, with the evaluation of the compiled body in scope.

This does not close `wph`: the two premises `hbody` and `hret` still have no
supplier. The body calls `build_mpt_indexed` on the transaction list, and the
only world contract for that callee is at `BuildMptIndexedReadyStrong`, which
asks a pointer bound for every transaction slice; `InputReady` carries none. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.WkPayloadHeaderRetR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

theorem lookup_payload_header_ret :
    originalRuntimeCode.lookup (ofString "payload_header") =
      some ([(ofString "si", .one)],
        sourceFnBody Guest.Software.guestFn_payload_header, .one) :=
  lookup_of_guestAst_getElem 864 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_payload_header) rfl

/-- The `payload_header` world contract from a `HeapByteEff` of the compiled body and the
header-cell facts of the returned word, the latter asked only when the body returns. -/
theorem wk_payload_header_of_bodyEffect_returned
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), InputReady s →
      WkBlockTxEnc.HeapByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
         (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
         (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)]
        ["heap_ptr", "scratch_ptr", "wd_rlp_slices"])
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), InputReady s →
      ∀ v : ValueHOL 64,
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).1 =
          some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧
          HeaderAt
            (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
            w.toNat ∧
          Inside (w.toNat, 248) sourceBase
            (globN
              (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
              "heap_ptr") ∧
          ∀ S Nd : List Nat, WorldTypedWith s S Nd →
            WorldTypedWith
              (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
              S Nd →
            worldOwned
              (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
              S Nd = worldOwned s S Nd →
            IvlsDisj [(w.toNat, 248)]
              (worldOwned
                (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_payload_header)).2
                S Nd)) :
    WorldKeeps InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header") := by
  refine ⟨[(ofString "si", .one)], sourceFnBody Guest.Software.guestFn_payload_header, .one,
    lookup_payload_header_ret, ?_⟩
  intro F s hc hIR ⟨vals, hl⟩ hnt hres
  exact PayloadWorldStepScratch.heapByteEff_to_worldStep_payload
    (R := fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
      (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
      (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
      (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
    (gw := ["heap_ptr", "scratch_ptr", "wd_rlp_slices"])
    (B := []) (by intro gs hgs; cases hgs)
    (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp)
    (inputReady_worldOK s hIR) (by simpa using hbody (F := F) s hIR)
    (fun S Nd hWT hWTp hown => by
      intro v hv
      obtain ⟨w, rfl, hH, hin, hdisj⟩ := hret (F := F) s hIR v hv
      exact ⟨w, rfl, hH, hin, hdisj S Nd hWT hWTp hown⟩)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.WkPayloadHeaderRetR32
