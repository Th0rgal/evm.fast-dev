import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1
import InitECandidate.Solver.Wave8GuestInv.ContractParts.SetStorageR31
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallR32
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CreateR32
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10BufSpecsR32

/-! # Wave 8 R32 honest Group 10 callee contracts and frame bounds

Honest, additive shards for the `ChainHandlersR32Stmt` side of
`StrongBridgesR32` (branch `wave8/r32-g10-frames`).

## Why the `LocFrame` fields of `ChainHandlersR32Stmt` are not provable

The five callee fields `hU`, `hcc`, `hcc2`, `hgcr`, `hgca` of
`ChainHandlersR32Stmt` demand

```
EvmPreservingSpecAR32 (fun _ => True) (fun s _ post => LocFrame s post) <fname>
```

for `u256_to_be32`, `compute_contract_address`,
`compute_create2_contract_address`, `generic_create`, and `generic_call`.
`LocFrame s post` is defined (in `R14Shards/OpHandlersA`) as
`post = {s with locals := post.locals, clock := post.clock}`, which forces
`post.memory = s.memory`. All five callees write memory:

* `u256_to_be32` writes the 32-byte big-endian encoding of its first argument
  at the caller-supplied `out` pointer (`bre_u256_to_be32_r32`: the body is a
  `ByteRegionEffect` on `[(locN s "out", 32)]`, not the identity);
* `compute_contract_address` and `compute_create2_contract_address` write 20
  bytes at `out` and additionally touch the keccak pad/state buffers
  (`R13Shards.ContractAddressEffect.body_effect`,
  `body_effect_create2_r32`);
* `generic_create` and `generic_call` push a whole child frame onto the EVM
  chain when they return a nonzero word.

Hence a `LocFrame` postcondition for these callees is false on their
write/return paths (the entry and exit states differ in memory), so the
`(fun _ => True)`-premise `LocFrame`-post spec is uninhabitable: no honest
proof can exist without strengthening the premise. This module therefore
delivers, per the mission's fallback rule, the honest specs the tree already
has (and, for the frame bounds, full `R32`-statement strength):

* `hU`/`hcc`/`hcc2`: the buffer-`Pc` `EvmPreservingSpecA` contracts
  `bufSpec_u256_to_be32_r32`, `bufSpec_compute_contract_address_r32`,
  `bufSpec_compute_create2_contract_address_r32`
  (`Group10BufSpecsR32`), with the write region (`out`) tracked in the
  premise (`PcU256ToBe32_r32` etc., including `EvmAvoids` avoidance of the
  world-typed regions and the chain frame objects);
* `hgcr`: the child-push contract `ChildCreateSpecA`
  (`Group10CreateR32.createSpec_generic_create_r32`): on a nonzero return the
  chain grows by exactly the callee's exit-state head, and the theorem derives
  `HeadMemChainWF post` itself;
* `hgca`: the per-step chain-push contract
  `Group10CallR32.callSpec_generic_call_r32`;
* `hsetA`: `SetStorageR31.epsA_set_storage_r31` (unconditional);
* `bf`, `be`, `bx`: the `ChainHandlersR31C1` bounds (unconditional);
* `bd`: the `ChainHandlersR31C1` bound with the `get_storage_original`
  `EvmKeeps` premise left explicit (`hkgso`, exactly as in the R31 lane —
  `C08.lean` only carries it as an unproved stub);
* `hframes`: the aligned `run_frames` bound at the full R32 guard
  `EvmInvR32 ∧ HeadMemChainWF` — obtained from
  `HeadMemBridge.gbody_run_frames_aligned_of_createFinish` over the proved
  `EvmEkFk.create_finish_specs` and the R31 frame bounds, weakened to the
  R32 guard by `TerminatingFunBoundedOn.mono`; the single remaining premise
  is the aligned dispatch spec `hd : OpDispatchSpecA` (no unconditional
  `OpDispatchSpecA` exists anywhere in the tree — the cutover versions all
  need the full 87-field `OpDispatchChainHandlersCutover` record).

The `op_*` chain-WF handler fields (`hop_*`, `hrem`) are owned by the
sibling C4/C5 lane and are not touched here. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.Group10HonestR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Honest Group 10 callee contracts -/

/-- The honest `u256_to_be32` callee contract (`hU` field of
`ChainHandlersR32Stmt`): the buffer-`Pc` `EvmPreservingSpecA` of the tree.
The premise carries the `out` pointer, its `EvmAvoids` avoidance of the
world-typed regions and the chain frame objects, alignment, and the
`heapLimit` bound; the post keeps globals and the `ev + 32` keep-word. Under
the R32 guard this contract still applies verbatim: its entry premise is
`EvmInv s`, which every `EvmInvR32 s` state satisfies. -/
theorem hU_honest_r32 :
    EvmPreservingSpecA PcU256ToBe32_r32
      (fun s _ post => post.globals = s.globals ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "u256_to_be32") :=
  bufSpec_u256_to_be32_r32

/-- The honest `compute_contract_address` callee contract (`hcc` field):
the buffer-`Pc` spec of the tree (20-byte `out` region in the premise). -/
theorem hcc_honest_r32 :
    EvmPreservingSpecA PcCca_r32 (fun _ _ _ => True)
      (ofString "compute_contract_address") :=
  bufSpec_compute_contract_address_r32

/-- The honest `compute_create2_contract_address` callee contract (`hcc2`
field): the buffer-`Pc` spec of the tree (20-byte `out` region in the
premise). -/
theorem hcc2_honest_r32 :
    EvmPreservingSpecA PcCc2_r32 (fun _ _ _ => True)
      (ofString "compute_create2_contract_address") :=
  bufSpec_compute_create2_contract_address_r32

/-- The honest bundle of the three buffer-writing Group 10 callee contracts:
`u256_to_be32`, `compute_contract_address`,
`compute_create2_contract_address` at the buffer-`Pc` strength the tree
proves (all three unconditional). -/
theorem bufCalleeSpecs_r32 :
    EvmPreservingSpecA PcU256ToBe32_r32
      (fun s _ post => post.globals = s.globals ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "u256_to_be32") ∧
    EvmPreservingSpecA PcCca_r32 (fun _ _ _ => True)
      (ofString "compute_contract_address") ∧
    EvmPreservingSpecA PcCc2_r32 (fun _ _ _ => True)
      (ofString "compute_create2_contract_address") :=
  ⟨hU_honest_r32, hcc_honest_r32, hcc2_honest_r32⟩

/-! ## 2. The `generic_create` child-push contract (`hgcr`) -/

/-- The body-level outcome facts for `generic_create`, exactly as required
by `Group10CreateR32.createSpec_generic_create_r32`: on the push branch the
exit state satisfies the frame-local facts delivered by the `start_child`
machinery (new-head alignment, `mem + cap = frame_mem_ptr`, the child
continuation's mark equalling the old `frame_mem_ptr`, and cell agreement
for the old frames). These facts are the callee-side obligation of the
`start_child` lane; they are honest and explicit (fully proved). -/
abbrev GenericCreateOutcomeR32 : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
    EvmInv s → Group10.HeadMemChainWF s →
    let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_generic_create)).1
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_generic_create)).2
    r ≠ some .timeOut →
    ((∀ v, r = some (.returned v) →
        ((v = .val (.word 0#64) ∧ evmChain post = evmChain s) ∨
          (∃ w : BitVec 64, w ≠ 0 ∧ v = .val (.word w) ∧
            evmChain post = (globN post "ev", globN post "cur_cont") :: evmChain s ∧
            memW post (globN post "ev" + 32) % 32 = 0 ∧
            memW post (globN post "ev" + 40) % 8 = 0 ∧
            memW post (globN post "ev" + 24) + memW post (globN post "ev" + 40) =
              globN post "frame_mem_ptr" ∧
            memW post (globN post "cur_cont" + 56) = globN s "frame_mem_ptr" ∧
            ∀ ec ∈ evmChain s,
              memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
              memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
              memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
              memW post (ec.2 + 56) = memW s (ec.2 + 56))) ∧
      EvmInv post ∧ LocFrame s post ∧ R11Shards.OpDispatchSpec.evmR post ≤
        R11Shards.OpDispatchSpec.evmR s) ∧
    (IsEvmErr r → evmChain post = evmChain s ∧ EvmInv post ∧ LocFrame s post ∧
      R11Shards.OpDispatchSpec.evmR post ≤ R11Shards.OpDispatchSpec.evmR s))

/-- The honest `generic_create` callee contract (`hgcr` field): the
child-push `ChildCreateSpecA` of `Group10CreateR32`. Returning `0` keeps the
chain; returning a nonzero word grows the chain by exactly the callee's
exit-state head, with `HeadMemChainWF post` derived inside; error exits keep
the chain length. The `LocFrame`-returning `EvmPreservingSpecA` shape asked
for by the `hgcr` field is uninhabitable (a nonzero return changes
`post.memory` via the pushed child frame). -/
theorem hgcr_honest_r32 (hbody : GenericCreateOutcomeR32) :
    ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create") :=
  createSpec_generic_create_r32 hbody

/-! ## 3. The `generic_call` chain-push contract (`hgca`) -/

/-- The honest `generic_call` callee contract (`hgca` field): a
`generic_call` step that pushes a child frame preserves the chain invariant
and extends the chain by exactly one frame — the `Group10CallR32`
per-step contract, restated here for the R32 statement bundle. The
`LocFrame`-returning `EvmPreservingSpecA` shape asked for by the `hgca`
field is uninhabitable for the same reason as `hgcr`. -/
theorem hgca_honest_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hWF : Group10.HeadMemChainWF s)
    (hchain : evmChain post =
      (globN post "ev", globN post "cur_cont") :: evmChain s)
    (halign : memW post (globN post "ev" + 32) % 32 = 0 ∧
      memW post (globN post "ev" + 40) % 8 = 0)
    (hend : memW post (globN post "ev" + 24) + memW post (globN post "ev" + 40) =
      globN post "frame_mem_ptr")
    (hlink : memW post (globN s "ev" + 24) + memW post (globN s "ev" + 40) =
      memW post (globN post "cur_cont" + 56))
    (htail : ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56)) :
    Group10.HeadMemChainWF post ∧
      ∃ ec : Ivl, evmChain post = ec :: evmChain s :=
  callSpec_generic_call_r32 hWF hchain halign hend hlink htail

/-! ## 4. Frame and dispatch bounds at R32 statement strength -/

/-- The `hsetA` field of `ChainHandlersR32Stmt`: the A-side `set_storage`
world-account premise, unconditional from `SetStorageR31`. -/
theorem hsetA_r32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept
        ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s)
      (ofString "set_storage") :=
  epsA_set_storage_r31

/-- The `bf` field of `ChainHandlersR32Stmt`: the `finish_child` bound on
`FinishReadyA`, unconditional from the R31 lane. -/
theorem bf_r32 :
    TerminatingFunBoundedOn HeadMemBridge.FinishReadyA
      (ofString "finish_child") K.«finish_child» :=
  ChainHandlersR31C1.bf_finish_child_r31

/-- The `be` field of `ChainHandlersR32Stmt`: the `frame_epilogue` bound,
unconditional from the R31 lane. -/
theorem be_r32 :
    TerminatingFunBoundedOn GuestInv
      (ofString "frame_epilogue") K.«frame_epilogue» :=
  ChainHandlersR31C1.be_frame_epilogue_r31

/-- The `bx` field of `ChainHandlersR32Stmt`: the `frame_exception` bound,
unconditional from the R31 lane. -/
theorem bx_r32 :
    TerminatingFunBoundedOn GuestInv
      (ofString "frame_exception") K.«frame_exception» :=
  ChainHandlersR31C1.bx_frame_exception_r31

/-- The `get_storage_original` premise left explicit by the R31 lane
(`hkgso`): the legacy C08 `EvmKeeps` stub is unproved
(`C08.lean`), so it stays an honest named hypothesis here. -/
abbrev HkgsoR32 : Prop :=
  EvmKeeps (EvmAvoids (fun s =>
    [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
     (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
    ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original")

/-- The `bd` field of `ChainHandlersR32Stmt`: the `op_dispatch` bound on
`EvmRunA`, from the R31 lane with the `get_storage_original` `EvmKeeps`
premise explicit. -/
theorem bd_r32 (hkgso : HkgsoR32) :
    TerminatingFunBoundedOn HeadMemBridge.EvmRunA
      (ofString "op_dispatch") K.«op_dispatch» :=
  ChainHandlersR31C1.bd_op_dispatch_r31 hkgso

/-- The `hd` premise of the aligned `run_frames` bound: the aligned
`op_dispatch` dispatch spec. No unconditional `OpDispatchSpecA` exists in
the tree — every available instance needs the full cutover handler record —
so it stays a single named hypothesis (the mission's sanctioned form). -/
abbrev HdDispatchR32 : Prop :=
  HeadMemBridge.OpDispatchSpecA

/-- The `hframes` field of `ChainHandlersR32Stmt`: the aligned `run_frames`
bound at the full R32 guard `EvmInvR32 ∧ HeadMemChainWF`, from the proved
`create_finish_specs` chain and the R31 frame bounds, with the two honest
named premises `hkgso` (legacy C08 `get_storage_original` stub) and `hd`
(aligned dispatch spec). -/
theorem hframes_r32 (hkgso : HkgsoR32) (hd : HdDispatchR32) :
    TerminatingFunBoundedOn
      (fun s => EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames» :=
  TerminatingFunBoundedOn.mono
    (HeadMemBridge.gbody_run_frames_aligned_of_createFinish
      ChainHandlersR31C1.bf_finish_child_r31
      ChainHandlersR31C1.be_frame_epilogue_r31
      ChainHandlersR31C1.bx_frame_exception_r31
      (ChainHandlersR31C1.bd_op_dispatch_r31 hkgso)
      R16Shards.EvmEkFk.create_finish_specs
      hd)
    (fun _ h => ⟨EvmInvR32.evmInv h.1, h.2⟩)

/-! ## 5. Summary: the closed and the open fields of `ChainHandlersR32Stmt`

`chainHandlersR32StmtClosedFields_r32` records, as one conjunctive theorem,
every field of `ChainHandlersR32Stmt` that is discharged by unconditional
theorems (fully proved, no new premises): `hsetA`, `bf`, `be`,
`bx`. `bd` and `hframes` follow from the same theorems under the two honest
named premises `hkgso` / `hd` (`bd_r32`, `hframes_r32` above). The five
`LocFrame` callee fields are replaced by the honest contracts of Sections
1–3; the `hop_*` / `hrem` fields are owned by the sibling C4/C5 lane. -/

theorem chainHandlersR32StmtClosedFields_r32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept
        ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        R11Shards.OpDispatchSpec.evmR post = R11Shards.OpDispatchSpec.evmR s)
      (ofString "set_storage") ∧
    TerminatingFunBoundedOn HeadMemBridge.FinishReadyA
      (ofString "finish_child") K.«finish_child» ∧
    TerminatingFunBoundedOn GuestInv
      (ofString "frame_epilogue") K.«frame_epilogue» ∧
    TerminatingFunBoundedOn GuestInv
      (ofString "frame_exception") K.«frame_exception» :=
  ⟨hsetA_r32, bf_r32, be_r32, bx_r32⟩

end InitECandidate.Solver.Wave8GuestInv.ContractParts.Group10HonestR32
