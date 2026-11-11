import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4D

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4E: read-only and `create_ether` callee wrappers

These package the generic `ScBo` engines of `WkPtxPhase4B` with the callee
facts that never change: read-only callees satisfy `WorldKeepsScBo` with
empty buffers, and `create_ether` satisfies it over the account-mutation
buffers. -/

/-- The read-only callee runner: insts 2, 3, 5, 7, 8 and 9. -/
theorem p4Run_decCall_ro {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    {fname : MlS} (hro : ReadOnlyFn fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hnout : name ≠ ofString "out") (hntx : name ≠ ofString "tx")
    (hnidx : name ≠ ofString "index") (hnlogs : name ≠ ofString "logs")
    (hshn : ∀ nm ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] : List String), ofString nm ≠ name)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      P4Data entry (setVarHOLFinite name v { post with locals := s.locals }) s_pmc w_out →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite name v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall name sh fname args tail) s :=
  p4Run_decCall_scBo h hc (by intro p hp; cases hp) (by intro p hp; cases hp)
    (by intro g hg; cases hg) (by simp) (by simp) (by simp)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    name sh fname args tail
    (worldKeepsScBo_of_readOnly hro)
    (fun callee => PtxP1.worldOK_callEntry h.base.world callee)
    hnout hntx hnidx hnlogs hshn htail

/-- The `create_ether` runner: insts 10 and 11 (result discarded). -/
theorem p4Run_call0_create_ether {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      WorldStep (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P4Data entry { post with locals := s.locals } s_pmc w_out →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail { post with locals := s.locals }) :
    PtxRelRunStrong entry
      (.seq (.call (some (none, none)) (ofString "create_ether") args) tail) s :=
  p4Run_call0_scBo h hc validBufList_acctMutBufs
    (by intro p hp
        simp only [acctMutBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by simp [ptxBufs], by decide⟩)
    (by intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (ofString "create_ether") args tail
    wkScBo_create_ether
    (fun callee => PtxP1.worldOK_callEntry h.base.world callee)
    htail
