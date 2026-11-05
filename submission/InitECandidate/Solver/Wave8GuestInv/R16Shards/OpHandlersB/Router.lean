import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Router
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group07Transient
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group02
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group03
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group01
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateAccountOps
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevert

/-! # OpDispatch Router Assembly (`op_dispatch_spec_of_remaining`)

Pre-`C00` router shard assembling `op_dispatch_spec_of_handlers` (`R11Shards/OpDispatchSpec/Router.lean`)
with all already-proved unconditional `OpHandlerSpec` leaves:
- Group 06a control-flow (`R16Shards.OpHandlersB.Group06ControlFlow`):
  `op_stop`, `op_jump`, `op_jumpi`, `op_pc`, `op_gas`, `op_jumpdest` (6)
- Group 07a transient storage (`R16Shards.OpHandlersB.Group07Transient`):
  `op_tload`, `op_tstore` (2)
- Group 02 comparisons (`R16Shards.OpHandlers.Group02`):
  `op_lt`, `op_gt`, `op_slt`, `op_sgt`, `op_eq`, `op_iszero` (6)
- Group 03 bitwise & shift (`R16Shards.OpHandlers.Group03`):
  `op_and`, `op_or`, `op_xor`, `op_not`, `op_byte`, `op_shl`, `op_shr`, `op_sar`, `op_clz` (9)

Shadow-cutover extension (`op_dispatch_spec_of'`): additionally wires
- Group 01 arithmetic (`R16Shards.OpHandlers.Group01`):
  `op_add`, `op_mul`, `op_sub`, `op_div`, `op_sdiv`, `op_mod`, `op_smod`, `op_addmod`, `op_mulmod`,
  `op_exp`, `op_signextend` (11)
- Group 04 environment (`R16Shards.OpHandlers.Group04` + `CalldataloadSpecs`):
  `op_address`, `op_origin`, `op_caller`, `op_callvalue`, `op_calldataload`, `op_calldatasize` (6)
- Group 05 (`R16Shards.OpHandlers.Group05`): `op_codesize`, `op_gasprice`, `op_returndatasize` (3)
- State/account ops (`R16Shards.OpHandlersB.StateAccountOps`, under `WorldAccountSpecs`):
  `op_balance`, `op_extcodesize`, `op_extcodehash`, `op_selfbalance`, `op_sload`, `op_sstore`,
  `op_selfdestruct` (7)

As each subsequent `OpHandlersB` group shard is completed, it is wired in here to monotonically
shrink the remaining obligation bundle for `op_dispatch_spec`.

Aligned extension (`op_dispatch_aligned_spec_of`): `op_keccak` (Group04), `op_return` and
`op_revert` (`OpHandlersB.Group09LogReturnRevert`) are only proved under the stronger precondition
`EvmRun s ∧ HeadMemAligned s`. Since every handler is entered through `callEntryStateHOLFinite`
(locals/clock only), `HeadMemAligned` transfers to the callee entry, so the `DispatchSpecWalk`
argument replays verbatim with `OpHandlerSpecA := FunSpec (EvmRun ∧ HeadMemAligned) OpDispatchPost`.
The resulting `op_dispatch` contract (`OpDispatchAlignedSpec`) has the same postcondition as
`OpHandlerSpec` and the `EvmRun ∧ HeadMemAligned` precondition, which is exactly what the
`HeadMemAlignedBridge` consumer (`OpDispatchSpecA`, via `headMemChainWF_headMemAligned`) can feed.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-A` scope (Groups 01, 04, 05, 06b). -/
def RemainingOpHandlersASpec : Prop :=
  OpHandlerSpec (ofString "op_add") ∧
  OpHandlerSpec (ofString "op_mul") ∧
  OpHandlerSpec (ofString "op_sub") ∧
  OpHandlerSpec (ofString "op_div") ∧
  OpHandlerSpec (ofString "op_sdiv") ∧
  OpHandlerSpec (ofString "op_mod") ∧
  OpHandlerSpec (ofString "op_smod") ∧
  OpHandlerSpec (ofString "op_addmod") ∧
  OpHandlerSpec (ofString "op_mulmod") ∧
  OpHandlerSpec (ofString "op_exp") ∧
  OpHandlerSpec (ofString "op_signextend") ∧
  OpHandlerSpec (ofString "op_keccak") ∧
  OpHandlerSpec (ofString "op_address") ∧
  OpHandlerSpec (ofString "op_origin") ∧
  OpHandlerSpec (ofString "op_caller") ∧
  OpHandlerSpec (ofString "op_callvalue") ∧
  OpHandlerSpec (ofString "op_calldataload") ∧
  OpHandlerSpec (ofString "op_calldatasize") ∧
  OpHandlerSpec (ofString "op_codesize") ∧
  OpHandlerSpec (ofString "op_gasprice") ∧
  OpHandlerSpec (ofString "op_returndatasize") ∧
  OpHandlerSpec (ofString "op_blockhash") ∧
  OpHandlerSpec (ofString "op_coinbase") ∧
  OpHandlerSpec (ofString "op_timestamp") ∧
  OpHandlerSpec (ofString "op_number") ∧
  OpHandlerSpec (ofString "op_prevrandao") ∧
  OpHandlerSpec (ofString "op_gaslimit") ∧
  OpHandlerSpec (ofString "op_chainid") ∧
  OpHandlerSpec (ofString "op_basefee") ∧
  OpHandlerSpec (ofString "op_blobhash") ∧
  OpHandlerSpec (ofString "op_blobbasefee") ∧
  OpHandlerSpec (ofString "op_slotnum") ∧
  OpHandlerSpec (ofString "op_pop") ∧
  OpHandlerSpec (ofString "op_mload") ∧
  OpHandlerSpec (ofString "op_mstore") ∧
  OpHandlerSpec (ofString "op_mstore8") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  OpHandlerSpec (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange")

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-B` scope (Groups 07–10). -/
def RemainingOpHandlersBSpec : Prop :=
  OpHandlerSpec (ofString "op_balance") ∧
  OpHandlerSpec (ofString "op_calldatacopy") ∧
  OpHandlerSpec (ofString "op_codecopy") ∧
  OpHandlerSpec (ofString "op_extcodesize") ∧
  OpHandlerSpec (ofString "op_extcodecopy") ∧
  OpHandlerSpec (ofString "op_returndatacopy") ∧
  OpHandlerSpec (ofString "op_extcodehash") ∧
  OpHandlerSpec (ofString "op_selfbalance") ∧
  OpHandlerSpec (ofString "op_sload") ∧
  OpHandlerSpec (ofString "op_sstore") ∧
  OpHandlerSpec (ofString "op_mcopy") ∧
  OpHandlerSpec (ofString "op_log") ∧
  OpHandlerSpec (ofString "op_create") ∧
  OpHandlerSpec (ofString "op_call") ∧
  OpHandlerSpec (ofString "op_callcode") ∧
  OpHandlerSpec (ofString "op_return") ∧
  OpHandlerSpec (ofString "op_delegatecall") ∧
  OpHandlerSpec (ofString "op_create2") ∧
  OpHandlerSpec (ofString "op_staticcall") ∧
  OpHandlerSpec (ofString "op_revert") ∧
  OpHandlerSpec (ofString "op_selfdestruct")

theorem allOpHandlersSpec_of_remaining
    (hA : RemainingOpHandlersASpec)
    (hB : RemainingOpHandlersBSpec) :
    AllOpHandlersSpec := by
  rcases hA with
    ⟨h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     h_op_keccak, h_op_address, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_codesize, h_op_gasprice,
     h_op_returndatasize,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_msize,
     h_op_push, h_op_dup, h_op_swap, h_op_dupn, h_op_swapn, h_op_exchange⟩
  rcases hB with
    ⟨h_op_balance, h_op_calldatacopy, h_op_codecopy, h_op_extcodesize,
     h_op_extcodecopy, h_op_returndatacopy, h_op_extcodehash, h_op_selfbalance,
     h_op_sload, h_op_sstore, h_op_mcopy, h_op_log,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall, h_op_revert, h_op_selfdestruct⟩
  exact
    ⟨op_stop_spec, h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     op_lt_spec, op_gt_spec, op_slt_spec, op_sgt_spec, op_eq_spec, op_iszero_spec,
     op_and_spec, op_or_spec, op_xor_spec, op_not_spec, op_byte_spec, op_shl_spec, op_shr_spec, op_sar_spec, op_clz_spec,
     h_op_keccak, h_op_address, h_op_balance, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_calldatacopy,
     h_op_codesize, h_op_codecopy, h_op_gasprice, h_op_extcodesize, h_op_extcodecopy,
     h_op_returndatasize, h_op_returndatacopy, h_op_extcodehash,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_selfbalance, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_sload, h_op_sstore,
     op_jump_spec, op_jumpi_spec, op_pc_spec, h_op_msize, op_gas_spec, op_jumpdest_spec,
     op_tload_spec, op_tstore_spec, h_op_mcopy, h_op_push,
     h_op_dup, h_op_swap,
     h_op_log, h_op_dupn, h_op_swapn, h_op_exchange,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall,
     h_op_revert, h_op_selfdestruct⟩

/-- Parameterized `op_dispatch_spec` wired to all proved leaves in `Group06ControlFlow`, `Group07Transient`, `Group02`, and `Group03`. -/
theorem op_dispatch_spec_of
    (hA : RemainingOpHandlersASpec)
    (hB : RemainingOpHandlersBSpec) :
    OpHandlerSpec (ofString "op_dispatch") :=
  op_dispatch_spec_of_handlers (allOpHandlersSpec_of_remaining hA hB)

/-! ## Shadow-cutover: shrunken remaining bundles with Groups 01/04/05 + StateAccountOps wired -/

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-A` scope after Groups 01, 04 (env), 05 are wired
(still open: `op_keccak` (needs `HeadMemAligned` bridge), block-context, memory, stack ops). -/
def RemainingOpHandlersASpec' : Prop :=
  OpHandlerSpec (ofString "op_keccak") ∧
  OpHandlerSpec (ofString "op_blockhash") ∧
  OpHandlerSpec (ofString "op_coinbase") ∧
  OpHandlerSpec (ofString "op_timestamp") ∧
  OpHandlerSpec (ofString "op_number") ∧
  OpHandlerSpec (ofString "op_prevrandao") ∧
  OpHandlerSpec (ofString "op_gaslimit") ∧
  OpHandlerSpec (ofString "op_chainid") ∧
  OpHandlerSpec (ofString "op_basefee") ∧
  OpHandlerSpec (ofString "op_blobhash") ∧
  OpHandlerSpec (ofString "op_blobbasefee") ∧
  OpHandlerSpec (ofString "op_slotnum") ∧
  OpHandlerSpec (ofString "op_pop") ∧
  OpHandlerSpec (ofString "op_mload") ∧
  OpHandlerSpec (ofString "op_mstore") ∧
  OpHandlerSpec (ofString "op_mstore8") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  OpHandlerSpec (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange")

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-B` scope after `StateAccountOps` is wired. -/
def RemainingOpHandlersBSpec' : Prop :=
  OpHandlerSpec (ofString "op_calldatacopy") ∧
  OpHandlerSpec (ofString "op_codecopy") ∧
  OpHandlerSpec (ofString "op_extcodecopy") ∧
  OpHandlerSpec (ofString "op_returndatacopy") ∧
  OpHandlerSpec (ofString "op_mcopy") ∧
  OpHandlerSpec (ofString "op_log") ∧
  OpHandlerSpec (ofString "op_create") ∧
  OpHandlerSpec (ofString "op_call") ∧
  OpHandlerSpec (ofString "op_callcode") ∧
  OpHandlerSpec (ofString "op_return") ∧
  OpHandlerSpec (ofString "op_delegatecall") ∧
  OpHandlerSpec (ofString "op_create2") ∧
  OpHandlerSpec (ofString "op_staticcall") ∧
  OpHandlerSpec (ofString "op_revert")

theorem remainingOpHandlersASpec_of' (hA : RemainingOpHandlersASpec') : RemainingOpHandlersASpec := by
  rcases hA with
    ⟨h_op_keccak,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_msize,
     h_op_push, h_op_dup, h_op_swap, h_op_dupn, h_op_swapn, h_op_exchange⟩
  exact
    ⟨op_add_spec, op_mul_spec, op_sub_spec, op_div_spec, op_sdiv_spec, op_mod_spec, op_smod_spec,
     op_addmod_spec, op_mulmod_spec, op_exp_spec, op_signextend_spec,
     h_op_keccak, op_address_spec, op_origin_spec, op_caller_spec, op_callvalue_spec,
     op_calldataload_spec, op_calldatasize_spec, op_codesize_spec, op_gasprice_spec,
     op_returndatasize_spec,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_msize,
     h_op_push, h_op_dup, h_op_swap, h_op_dupn, h_op_swapn, h_op_exchange⟩

theorem remainingOpHandlersBSpec_of' (hW : WorldAccountSpecs) (hB : RemainingOpHandlersBSpec') :
    RemainingOpHandlersBSpec := by
  rcases hB with
    ⟨h_op_calldatacopy, h_op_codecopy, h_op_extcodecopy, h_op_returndatacopy,
     h_op_mcopy, h_op_log,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall, h_op_revert⟩
  exact
    ⟨op_balance_spec hW, h_op_calldatacopy, h_op_codecopy, op_extcodesize_spec hW,
     h_op_extcodecopy, h_op_returndatacopy, op_extcodehash_spec hW, op_selfbalance_spec hW,
     op_sload_spec hW, op_sstore_spec hW, h_op_mcopy, h_op_log,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall, h_op_revert, op_selfdestruct_spec hW⟩

/-- Parameterized `op_dispatch_spec` with Groups 01/02/03/04/05/06a/07a and `StateAccountOps` wired
(50 of 87 handlers discharged; 23 A-side + 14 B-side obligations remain). -/
theorem op_dispatch_spec_of'
    (hW : WorldAccountSpecs)
    (hA : RemainingOpHandlersASpec')
    (hB : RemainingOpHandlersBSpec') :
    OpHandlerSpec (ofString "op_dispatch") :=
  op_dispatch_spec_of (remainingOpHandlersASpec_of' hA) (remainingOpHandlersBSpec_of' hW hB)


/-! ## Aligned router: `op_dispatch` under `EvmRun ∧ HeadMemAligned`

`HeadMemAligned` (Group04) only mentions globals and the head frame's memory cells, and every
handler is entered via `callEntryStateHOLFinite` (locals/clock only), so the structural
`DispatchSpecWalk` argument of `R11Shards/OpDispatchSpec/Walk.lean` replays verbatim with the
stronger precondition. This lets the aligned-only leaves (`op_keccak_aligned_spec`,
`op_return_aligned_spec`, `op_revert_aligned_spec`) be consumed without weakening them. -/

open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8Contracts.M23

/-- `OpHandlerSpec` under the aligned precondition. -/
def OpHandlerSpecA (fname : MlS) : Prop :=
  FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost fname

theorem opHandlerSpecA_of {fname : MlS} (h : OpHandlerSpec fname) : OpHandlerSpecA fname := by
  obtain ⟨ps, body, ret, hl, hrun⟩ := h
  exact ⟨ps, body, ret, hl, fun s hc hP hex hnt => hrun s hc hP.1 hex hnt⟩

theorem headMemAligned_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : HeadMemAligned s) :
    HeadMemAligned (callEntryStateHOLFinite s callee) := h

structure DispatchSpecWalkA (p : ProgHOL 64) : Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → EvmRun s ∧ HeadMemAligned s →
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none →
      (evaluateHOLFiniteState s p).2 = s) ∧
    ((evaluateHOLFiniteState s p).1 ≠ none →
      OpDispatchPost s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2)

theorem DispatchSpecWalkA.skip : DispatchSpecWalkA .skip := by
  refine ⟨fun s _ _ _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

theorem DispatchSpecWalkA.raise (e : ExpHOL 64) :
    DispatchSpecWalkA (.raise (ofString "EvmErr") e) := by
  refine ⟨fun {F} s _ hRun _ => ⟨fun hn => (raise_ne_none s _ e hn).elim, fun _ => ?_⟩⟩
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine ⟨?_, fun _ => ?_⟩
      · rintro ⟨_, h⟩
        cases h
      · have hInv' : EvmInv (emptyLocalsHOLFinite s) :=
          localsFree_evmInv s (emptyLocalsHOLFinite s).locals s.clock hRun.1.1
        have hcongr := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
        exact ⟨hInv', hcongr.2.2.1, le_of_eq hcongr.2.1⟩
    · exact opDispatchPost_error s s
  · exact opDispatchPost_error s s

theorem DispatchSpecWalkA.seqRaiseReturn (e1 e2 : ExpHOL 64) :
    DispatchSpecWalkA (.seq (.raise (ofString "EvmErr") e1) (.return e2)) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "EvmErr") e1) with ⟨r, mid⟩
  simp only [hr] at hnt ⊢
  cases r with
  | none =>
    have hnn := raise_ne_none s (ofString "EvmErr") e1
    rw [hr] at hnn
    exact (hnn rfl).elim
  | some _ =>
    have h1 := (DispatchSpecWalkA.raise e1).run s hcode hRun (by rw [hr]; exact hnt)
    rw [hr] at h1
    refine ⟨?_, fun _ => h1.2 (by simp)⟩
    intro h
    cases h

theorem return_const0_post {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {v : ValueHOL 64}
    (hpost : OpDispatchPost (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    OpDispatchPost s
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).1
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).2 := by
  rw [evaluateHOLFiniteState_return]
  have hc0 : @evalHOLExact 64 F _ ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (cpost.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  rw [hc0]; dsimp only
  have hsz : sizeOfShapeWithContextHOL cpost.structs
      (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]; dsimp only
  obtain ⟨hInv_cp, hPot_cp⟩ := hpost.1 ⟨v, rfl⟩
  have hcongr_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
  have hcongr_ret := evm_congr (s := cpost)
    (t := emptyLocalsHOLFinite { cpost with locals := s.locals }) rfl rfl
  have hInv_ret : EvmInv (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    localsFree_evmInv cpost _ cpost.clock hInv_cp
  refine ⟨fun _ => ⟨hInv_ret, by rw [hcongr_ret.1, ← hcongr_ce.1]; exact hPot_cp⟩, ?_⟩
  rintro ⟨_, h⟩
  cases h

theorem call_exception_post {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {eid : MlS} {ev : ValueHOL 64}
    (hQ : OpDispatchPost (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    OpDispatchPost s (some (.exception eid ev)) cpost.emptyLocalsHOLFinite := by
  by_cases heid : eid = ofString "EvmErr"
  · subst heid
    exact opDispatchPost_congr_lc (s := s) (s' := callEntryStateHOLFinite s callee)
      (post := cpost) (post' := cpost.emptyLocalsHOLFinite) rfl rfl rfl hQ
  · refine opDispatchPost_other (by intro _ h; cases h) ?_
    rintro ⟨_, h⟩
    injection h with h'; injection h' with h1 _; exact heid h1

theorem DispatchSpecWalkA.callReturn {fname : MlS}
    (hf : OpHandlerSpecA fname) (args : List (ExpHOL 64)) :
    DispatchSpecWalkA (.seq (.call (some (none, none)) fname args) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s s
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s s
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
        have hce_run : EvmRun (callEntryStateHOLFinite s callee) ∧ HeadMemAligned (callEntryStateHOLFinite s callee) :=
          ⟨evmRun_callEntry s callee hRun.1, headMemAligned_callEntry s callee hRun.2⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        have hQ (hsafe : res ≠ some .timeOut) :
            OpDispatchPost (callEntryStateHOLFinite s callee) res cpost := by
          have hbody : body' = body :=
            lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
              retShape ret' values callee (by rw [hcode]; exact hlook) hl
          subst body'
          have hce_ex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
              some (body, (callEntryStateHOLFinite s callee).locals, retShape) := by
            refine ⟨values, ?_⟩
            rw [← hcode] at hlook ⊢
            have hret : ret' = retShape := by
              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                s.code.lookup fname values body callee ret' hl
              simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
              split at hx
              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              · cases hx
            subst hret; exact hl
          have := hspec (callEntryStateHOLFinite s callee) hce_code hce_run hce_ex (by rw [hrun]; exact hsafe)
          rw [hrun] at this; exact this
        cases res with
        | none => exact opDispatchPost_error s cpost
        | some r0 =>
          cases r0 with
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte]
              exact return_const0_post (hQ (by simp))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s cpost
          | timeOut => simp at hnt
          | exception eid ev =>
            exact call_exception_post (hQ (by simp))
          | «break» =>
            exact opDispatchPost_error s cpost
          | «continue» =>
            exact opDispatchPost_error s cpost
          | finalFfi f =>
            refine opDispatchPost_other (s := s) (t := cpost.emptyLocalsHOLFinite)
              (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error =>
            exact opDispatchPost_error s cpost.emptyLocalsHOLFinite

theorem DispatchSpecWalkA.seq {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkA p) (h2 : DispatchSpecWalkA q) :
    DispatchSpecWalkA (.seq p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState s p with ⟨r1, mid⟩
  simp only [hr1] at hnt ⊢
  cases r1 with
  | none =>
    have hp := h1.run s hcode hRun (by rw [hr1]; simp)
    rw [hr1] at hp
    have hmid : mid = s := hp.1 rfl
    subst mid
    exact h2.run s hcode hRun hnt
  | some _ =>
    have hp := h1.run s hcode hRun (by rw [hr1]; exact hnt)
    rw [hr1] at hp
    refine ⟨?_, fun _ => hp.2 (by simp)⟩
    intro h
    cases h

theorem DispatchSpecWalkA.ite (c : ExpHOL 64) {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkA p) (h2 : DispatchSpecWalkA q) :
    DispatchSpecWalkA (.ite c p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w _
    by_cases hw : w = 0
    · simp only [hw, ↓reduceIte]
      intro hnt
      exact h2.run s hcode hRun hnt
    · simp only [hw, ↓reduceIte]
      intro hnt
      exact h1.run s hcode hRun hnt
  · intro _
    refine ⟨?_, fun _ => opDispatchPost_error s s⟩
    intro h
    cases h

theorem opDispatchSpecGroupA01
    (h_op_stop : OpHandlerSpecA (ofString "op_stop"))
    (h_op_add : OpHandlerSpecA (ofString "op_add"))
    (h_op_mul : OpHandlerSpecA (ofString "op_mul"))
    (h_op_sub : OpHandlerSpecA (ofString "op_sub"))
    (h_op_div : OpHandlerSpecA (ofString "op_div"))
    (h_op_sdiv : OpHandlerSpecA (ofString "op_sdiv"))
    (h_op_mod : OpHandlerSpecA (ofString "op_mod"))
    (h_op_smod : OpHandlerSpecA (ofString "op_smod"))
    (h_op_addmod : OpHandlerSpecA (ofString "op_addmod"))
    (h_op_mulmod : OpHandlerSpecA (ofString "op_mulmod"))
    (h_op_exp : OpHandlerSpecA (ofString "op_exp"))
    (h_op_signextend : OpHandlerSpecA (ofString "op_signextend")) :
    DispatchSpecWalkA dispatchGroup01 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_stop _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_add _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mul _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sub _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_div _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sdiv _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mod _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_smod _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_addmod _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mulmod _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_exp _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_signextend _) DispatchSpecWalkA.skip)))))))))))

theorem opDispatchSpecGroupA02
    (h_op_lt : OpHandlerSpecA (ofString "op_lt"))
    (h_op_gt : OpHandlerSpecA (ofString "op_gt"))
    (h_op_slt : OpHandlerSpecA (ofString "op_slt"))
    (h_op_sgt : OpHandlerSpecA (ofString "op_sgt"))
    (h_op_eq : OpHandlerSpecA (ofString "op_eq"))
    (h_op_iszero : OpHandlerSpecA (ofString "op_iszero"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup02 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_lt _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_gt _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_slt _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sgt _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_eq _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_iszero _) DispatchSpecWalkA.skip)
      ht)))))

theorem opDispatchSpecGroupA03
    (h_op_and : OpHandlerSpecA (ofString "op_and"))
    (h_op_or : OpHandlerSpecA (ofString "op_or"))
    (h_op_xor : OpHandlerSpecA (ofString "op_xor"))
    (h_op_not : OpHandlerSpecA (ofString "op_not"))
    (h_op_byte : OpHandlerSpecA (ofString "op_byte"))
    (h_op_shl : OpHandlerSpecA (ofString "op_shl"))
    (h_op_shr : OpHandlerSpecA (ofString "op_shr"))
    (h_op_sar : OpHandlerSpecA (ofString "op_sar"))
    (h_op_clz : OpHandlerSpecA (ofString "op_clz")) :
    DispatchSpecWalkA dispatchGroup03 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_and _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_or _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_xor _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_not _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_byte _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_shl _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_shr _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sar _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_clz _) DispatchSpecWalkA.skip))))))))

theorem opDispatchSpecGroupA04
    (h_op_keccak : OpHandlerSpecA (ofString "op_keccak"))
    (h_op_address : OpHandlerSpecA (ofString "op_address"))
    (h_op_balance : OpHandlerSpecA (ofString "op_balance"))
    (h_op_origin : OpHandlerSpecA (ofString "op_origin"))
    (h_op_caller : OpHandlerSpecA (ofString "op_caller"))
    (h_op_callvalue : OpHandlerSpecA (ofString "op_callvalue"))
    (h_op_calldataload : OpHandlerSpecA (ofString "op_calldataload"))
    (h_op_calldatasize : OpHandlerSpecA (ofString "op_calldatasize"))
    (h_op_calldatacopy : OpHandlerSpecA (ofString "op_calldatacopy"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup04 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_keccak _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_address _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_balance _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_origin _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_caller _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_callvalue _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_calldataload _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_calldatasize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_calldatacopy _) DispatchSpecWalkA.skip)
      ht))))))))

theorem opDispatchSpecGroupA05
    (h_op_codesize : OpHandlerSpecA (ofString "op_codesize"))
    (h_op_codecopy : OpHandlerSpecA (ofString "op_codecopy"))
    (h_op_gasprice : OpHandlerSpecA (ofString "op_gasprice"))
    (h_op_extcodesize : OpHandlerSpecA (ofString "op_extcodesize"))
    (h_op_extcodecopy : OpHandlerSpecA (ofString "op_extcodecopy"))
    (h_op_returndatasize : OpHandlerSpecA (ofString "op_returndatasize"))
    (h_op_returndatacopy : OpHandlerSpecA (ofString "op_returndatacopy"))
    (h_op_extcodehash : OpHandlerSpecA (ofString "op_extcodehash")) :
    DispatchSpecWalkA dispatchGroup05 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_codesize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_codecopy _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_gasprice _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_extcodesize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_extcodecopy _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_returndatasize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_returndatacopy _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_extcodehash _) DispatchSpecWalkA.skip)))))))

theorem opDispatchSpecGroupA06
    (h_op_blockhash : OpHandlerSpecA (ofString "op_blockhash"))
    (h_op_coinbase : OpHandlerSpecA (ofString "op_coinbase"))
    (h_op_timestamp : OpHandlerSpecA (ofString "op_timestamp"))
    (h_op_number : OpHandlerSpecA (ofString "op_number"))
    (h_op_prevrandao : OpHandlerSpecA (ofString "op_prevrandao"))
    (h_op_gaslimit : OpHandlerSpecA (ofString "op_gaslimit"))
    (h_op_chainid : OpHandlerSpecA (ofString "op_chainid"))
    (h_op_selfbalance : OpHandlerSpecA (ofString "op_selfbalance"))
    (h_op_basefee : OpHandlerSpecA (ofString "op_basefee"))
    (h_op_blobhash : OpHandlerSpecA (ofString "op_blobhash"))
    (h_op_blobbasefee : OpHandlerSpecA (ofString "op_blobbasefee"))
    (h_op_slotnum : OpHandlerSpecA (ofString "op_slotnum"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup06 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_blockhash _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_coinbase _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_timestamp _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_number _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_prevrandao _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_gaslimit _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_chainid _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_selfbalance _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_basefee _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_blobhash _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_blobbasefee _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_slotnum _) DispatchSpecWalkA.skip)
      ht)))))))))))

theorem opDispatchSpecGroupA07
    (h_op_pop : OpHandlerSpecA (ofString "op_pop"))
    (h_op_mload : OpHandlerSpecA (ofString "op_mload"))
    (h_op_mstore : OpHandlerSpecA (ofString "op_mstore"))
    (h_op_mstore8 : OpHandlerSpecA (ofString "op_mstore8"))
    (h_op_sload : OpHandlerSpecA (ofString "op_sload"))
    (h_op_sstore : OpHandlerSpecA (ofString "op_sstore"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup07 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_pop _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mload _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mstore _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mstore8 _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sload _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_sstore _) DispatchSpecWalkA.skip)
      ht)))))

theorem opDispatchSpecGroupA08
    (h_op_jump : OpHandlerSpecA (ofString "op_jump"))
    (h_op_jumpi : OpHandlerSpecA (ofString "op_jumpi"))
    (h_op_pc : OpHandlerSpecA (ofString "op_pc"))
    (h_op_msize : OpHandlerSpecA (ofString "op_msize"))
    (h_op_gas : OpHandlerSpecA (ofString "op_gas"))
    (h_op_jumpdest : OpHandlerSpecA (ofString "op_jumpdest"))
    (h_op_tload : OpHandlerSpecA (ofString "op_tload"))
    (h_op_tstore : OpHandlerSpecA (ofString "op_tstore"))
    (h_op_mcopy : OpHandlerSpecA (ofString "op_mcopy"))
    (h_op_push : OpHandlerSpecA (ofString "op_push")) :
    DispatchSpecWalkA dispatchGroup08 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jump _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jumpi _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_pc _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_msize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_gas _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jumpdest _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_tload _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_tstore _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mcopy _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_push _) DispatchSpecWalkA.skip)))))))))

theorem opDispatchSpecGroupA09
    (h_op_push : OpHandlerSpecA (ofString "op_push"))
    (h_op_dup : OpHandlerSpecA (ofString "op_dup"))
    (h_op_swap : OpHandlerSpecA (ofString "op_swap"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup09 tail) := by
  exact
    DispatchSpecWalkA.seq
      (DispatchSpecWalkA.ite _
        (DispatchSpecWalkA.seq
          (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_push _) DispatchSpecWalkA.skip)
          (DispatchSpecWalkA.seq
            (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_dup _) DispatchSpecWalkA.skip)
            (DispatchSpecWalkA.callReturn h_op_swap _)))
        DispatchSpecWalkA.skip)
      ht

theorem opDispatchSpecGroupA10
    (h_op_log : OpHandlerSpecA (ofString "op_log"))
    (h_op_dupn : OpHandlerSpecA (ofString "op_dupn"))
    (h_op_swapn : OpHandlerSpecA (ofString "op_swapn"))
    (h_op_exchange : OpHandlerSpecA (ofString "op_exchange"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup10 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_log _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_dupn _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_swapn _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_exchange _) DispatchSpecWalkA.skip)
      ht)))

theorem opDispatchSpecGroupA11
    (h_op_create : OpHandlerSpecA (ofString "op_create"))
    (h_op_call : OpHandlerSpecA (ofString "op_call"))
    (h_op_callcode : OpHandlerSpecA (ofString "op_callcode"))
    (h_op_return : OpHandlerSpecA (ofString "op_return"))
    (h_op_delegatecall : OpHandlerSpecA (ofString "op_delegatecall"))
    (h_op_create2 : OpHandlerSpecA (ofString "op_create2"))
    (h_op_staticcall : OpHandlerSpecA (ofString "op_staticcall"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalkA tail) :
    DispatchSpecWalkA (dispatchGroup11 tail) := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_create _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_call _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_callcode _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_return _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_delegatecall _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_create2 _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_staticcall _) DispatchSpecWalkA.skip)
      ht))))))

theorem opDispatchSpecGroupA12
    (h_op_revert : OpHandlerSpecA (ofString "op_revert"))
    (h_op_selfdestruct : OpHandlerSpecA (ofString "op_selfdestruct")) :
    DispatchSpecWalkA dispatchGroup12 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_revert _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_selfdestruct _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.seqRaiseReturn _ _))

def AllOpHandlersSpecA : Prop :=
  OpHandlerSpecA (ofString "op_stop") ∧
  OpHandlerSpecA (ofString "op_add") ∧
  OpHandlerSpecA (ofString "op_mul") ∧
  OpHandlerSpecA (ofString "op_sub") ∧
  OpHandlerSpecA (ofString "op_div") ∧
  OpHandlerSpecA (ofString "op_sdiv") ∧
  OpHandlerSpecA (ofString "op_mod") ∧
  OpHandlerSpecA (ofString "op_smod") ∧
  OpHandlerSpecA (ofString "op_addmod") ∧
  OpHandlerSpecA (ofString "op_mulmod") ∧
  OpHandlerSpecA (ofString "op_exp") ∧
  OpHandlerSpecA (ofString "op_signextend") ∧
  OpHandlerSpecA (ofString "op_lt") ∧
  OpHandlerSpecA (ofString "op_gt") ∧
  OpHandlerSpecA (ofString "op_slt") ∧
  OpHandlerSpecA (ofString "op_sgt") ∧
  OpHandlerSpecA (ofString "op_eq") ∧
  OpHandlerSpecA (ofString "op_iszero") ∧
  OpHandlerSpecA (ofString "op_and") ∧
  OpHandlerSpecA (ofString "op_or") ∧
  OpHandlerSpecA (ofString "op_xor") ∧
  OpHandlerSpecA (ofString "op_not") ∧
  OpHandlerSpecA (ofString "op_byte") ∧
  OpHandlerSpecA (ofString "op_shl") ∧
  OpHandlerSpecA (ofString "op_shr") ∧
  OpHandlerSpecA (ofString "op_sar") ∧
  OpHandlerSpecA (ofString "op_clz") ∧
  OpHandlerSpecA (ofString "op_keccak") ∧
  OpHandlerSpecA (ofString "op_address") ∧
  OpHandlerSpecA (ofString "op_balance") ∧
  OpHandlerSpecA (ofString "op_origin") ∧
  OpHandlerSpecA (ofString "op_caller") ∧
  OpHandlerSpecA (ofString "op_callvalue") ∧
  OpHandlerSpecA (ofString "op_calldataload") ∧
  OpHandlerSpecA (ofString "op_calldatasize") ∧
  OpHandlerSpecA (ofString "op_calldatacopy") ∧
  OpHandlerSpecA (ofString "op_codesize") ∧
  OpHandlerSpecA (ofString "op_codecopy") ∧
  OpHandlerSpecA (ofString "op_gasprice") ∧
  OpHandlerSpecA (ofString "op_extcodesize") ∧
  OpHandlerSpecA (ofString "op_extcodecopy") ∧
  OpHandlerSpecA (ofString "op_returndatasize") ∧
  OpHandlerSpecA (ofString "op_returndatacopy") ∧
  OpHandlerSpecA (ofString "op_extcodehash") ∧
  OpHandlerSpecA (ofString "op_blockhash") ∧
  OpHandlerSpecA (ofString "op_coinbase") ∧
  OpHandlerSpecA (ofString "op_timestamp") ∧
  OpHandlerSpecA (ofString "op_number") ∧
  OpHandlerSpecA (ofString "op_prevrandao") ∧
  OpHandlerSpecA (ofString "op_gaslimit") ∧
  OpHandlerSpecA (ofString "op_chainid") ∧
  OpHandlerSpecA (ofString "op_selfbalance") ∧
  OpHandlerSpecA (ofString "op_basefee") ∧
  OpHandlerSpecA (ofString "op_blobhash") ∧
  OpHandlerSpecA (ofString "op_blobbasefee") ∧
  OpHandlerSpecA (ofString "op_slotnum") ∧
  OpHandlerSpecA (ofString "op_pop") ∧
  OpHandlerSpecA (ofString "op_mload") ∧
  OpHandlerSpecA (ofString "op_mstore") ∧
  OpHandlerSpecA (ofString "op_mstore8") ∧
  OpHandlerSpecA (ofString "op_sload") ∧
  OpHandlerSpecA (ofString "op_sstore") ∧
  OpHandlerSpecA (ofString "op_jump") ∧
  OpHandlerSpecA (ofString "op_jumpi") ∧
  OpHandlerSpecA (ofString "op_pc") ∧
  OpHandlerSpecA (ofString "op_msize") ∧
  OpHandlerSpecA (ofString "op_gas") ∧
  OpHandlerSpecA (ofString "op_jumpdest") ∧
  OpHandlerSpecA (ofString "op_tload") ∧
  OpHandlerSpecA (ofString "op_tstore") ∧
  OpHandlerSpecA (ofString "op_mcopy") ∧
  OpHandlerSpecA (ofString "op_push") ∧
  OpHandlerSpecA (ofString "op_dup") ∧
  OpHandlerSpecA (ofString "op_swap") ∧
  OpHandlerSpecA (ofString "op_log") ∧
  OpHandlerSpecA (ofString "op_dupn") ∧
  OpHandlerSpecA (ofString "op_swapn") ∧
  OpHandlerSpecA (ofString "op_exchange") ∧
  OpHandlerSpecA (ofString "op_create") ∧
  OpHandlerSpecA (ofString "op_call") ∧
  OpHandlerSpecA (ofString "op_callcode") ∧
  OpHandlerSpecA (ofString "op_return") ∧
  OpHandlerSpecA (ofString "op_delegatecall") ∧
  OpHandlerSpecA (ofString "op_create2") ∧
  OpHandlerSpecA (ofString "op_staticcall") ∧
  OpHandlerSpecA (ofString "op_revert") ∧
  OpHandlerSpecA (ofString "op_selfdestruct")

theorem dispatchCode_walkA (h : AllOpHandlersSpecA) :
    DispatchSpecWalkA dispatchCode := by
  rcases h with
    ⟨h_op_stop, h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     h_op_lt, h_op_gt, h_op_slt, h_op_sgt, h_op_eq, h_op_iszero,
     h_op_and, h_op_or, h_op_xor, h_op_not, h_op_byte, h_op_shl, h_op_shr, h_op_sar, h_op_clz,
     h_op_keccak, h_op_address, h_op_balance, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_calldatacopy,
     h_op_codesize, h_op_codecopy, h_op_gasprice, h_op_extcodesize, h_op_extcodecopy,
     h_op_returndatasize, h_op_returndatacopy, h_op_extcodehash,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_selfbalance, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_sload, h_op_sstore,
     h_op_jump, h_op_jumpi, h_op_pc, h_op_msize, h_op_gas, h_op_jumpdest,
     h_op_tload, h_op_tstore, h_op_mcopy, h_op_push,
     h_op_dup, h_op_swap,
     h_op_log, h_op_dupn, h_op_swapn, h_op_exchange,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall,
     h_op_revert, h_op_selfdestruct⟩
  exact
    DispatchSpecWalkA.seq
      (DispatchSpecWalkA.ite _
        (DispatchSpecWalkA.seq
          (DispatchSpecWalkA.ite _
            (opDispatchSpecGroupA01 h_op_stop h_op_add h_op_mul h_op_sub h_op_div h_op_sdiv
              h_op_mod h_op_smod h_op_addmod h_op_mulmod h_op_exp h_op_signextend)
            (opDispatchSpecGroupA02 h_op_lt h_op_gt h_op_slt h_op_sgt h_op_eq h_op_iszero
              (opDispatchSpecGroupA03 h_op_and h_op_or h_op_xor h_op_not h_op_byte h_op_shl
                h_op_shr h_op_sar h_op_clz)))
          (DispatchSpecWalkA.raise _))
        DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.seq
        (DispatchSpecWalkA.ite _
          (DispatchSpecWalkA.seq
            (DispatchSpecWalkA.ite _
              (opDispatchSpecGroupA04 h_op_keccak h_op_address h_op_balance h_op_origin
                h_op_caller h_op_callvalue h_op_calldataload h_op_calldatasize h_op_calldatacopy
                (opDispatchSpecGroupA05 h_op_codesize h_op_codecopy h_op_gasprice h_op_extcodesize
                  h_op_extcodecopy h_op_returndatasize h_op_returndatacopy h_op_extcodehash))
              (opDispatchSpecGroupA06 h_op_blockhash h_op_coinbase h_op_timestamp h_op_number
                h_op_prevrandao h_op_gaslimit h_op_chainid h_op_selfbalance h_op_basefee
                h_op_blobhash h_op_blobbasefee h_op_slotnum
                (opDispatchSpecGroupA07 h_op_pop h_op_mload h_op_mstore h_op_mstore8
                  h_op_sload h_op_sstore
                  (opDispatchSpecGroupA08 h_op_jump h_op_jumpi h_op_pc h_op_msize h_op_gas
                    h_op_jumpdest h_op_tload h_op_tstore h_op_mcopy h_op_push))))
            (DispatchSpecWalkA.raise _))
          DispatchSpecWalkA.skip)
        (opDispatchSpecGroupA09 h_op_push h_op_dup h_op_swap
          (opDispatchSpecGroupA10 h_op_log h_op_dupn h_op_swapn h_op_exchange
            (opDispatchSpecGroupA11 h_op_create h_op_call h_op_callcode h_op_return
              h_op_delegatecall h_op_create2 h_op_staticcall
              (opDispatchSpecGroupA12 h_op_revert h_op_selfdestruct)))))


/-- Aligned `op_dispatch` contract: same postcondition as `OpHandlerSpec`, precondition
`EvmRun ∧ HeadMemAligned`. -/
def OpDispatchAlignedSpec : Prop := OpHandlerSpecA (ofString "op_dispatch")

theorem op_dispatch_aligned_spec_of_handlers (h : AllOpHandlersSpecA) : OpDispatchAlignedSpec := by
  refine ⟨_, _, _, lookup_op_dispatch, ?_⟩
  intro F s hcode hRun _ hnt
  change OpDispatchPost s (evaluateHOLFiniteState s dispatchCode).1 (evaluateHOLFiniteState s dispatchCode).2
  rcases hres : evaluateHOLFiniteState s dispatchCode with ⟨r, post⟩
  cases r with
  | none =>
    exact opDispatchPost_other (by intro _ hv; cases hv) (by rintro ⟨_, hv⟩; cases hv)
  | some r0 =>
    have hwalk := (dispatchCode_walkA h).run s hcode hRun hnt
    rw [hres] at hwalk
    exact hwalk.2 (by simp)

/-- Remaining `OpHandlersA`-scope leaves for the aligned router: `RemainingOpHandlersASpec'`
minus `op_keccak` (discharged by `op_keccak_aligned_spec`). -/
def RemainingOpHandlersASpecAligned : Prop :=
  OpHandlerSpec (ofString "op_blockhash") ∧
  OpHandlerSpec (ofString "op_coinbase") ∧
  OpHandlerSpec (ofString "op_timestamp") ∧
  OpHandlerSpec (ofString "op_number") ∧
  OpHandlerSpec (ofString "op_prevrandao") ∧
  OpHandlerSpec (ofString "op_gaslimit") ∧
  OpHandlerSpec (ofString "op_chainid") ∧
  OpHandlerSpec (ofString "op_basefee") ∧
  OpHandlerSpec (ofString "op_blobhash") ∧
  OpHandlerSpec (ofString "op_blobbasefee") ∧
  OpHandlerSpec (ofString "op_slotnum") ∧
  OpHandlerSpec (ofString "op_pop") ∧
  OpHandlerSpec (ofString "op_mload") ∧
  OpHandlerSpec (ofString "op_mstore") ∧
  OpHandlerSpec (ofString "op_mstore8") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  OpHandlerSpec (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange")

/-- Remaining `OpHandlersB`-scope leaves for the aligned router: `RemainingOpHandlersBSpec'`
minus `op_return`/`op_revert` (discharged by `Group09LogReturnRevert`). -/
def RemainingOpHandlersBSpecAligned : Prop :=
  OpHandlerSpec (ofString "op_calldatacopy") ∧
  OpHandlerSpec (ofString "op_codecopy") ∧
  OpHandlerSpec (ofString "op_extcodecopy") ∧
  OpHandlerSpec (ofString "op_returndatacopy") ∧
  OpHandlerSpec (ofString "op_mcopy") ∧
  OpHandlerSpec (ofString "op_log") ∧
  OpHandlerSpec (ofString "op_create") ∧
  OpHandlerSpec (ofString "op_call") ∧
  OpHandlerSpec (ofString "op_callcode") ∧
  OpHandlerSpec (ofString "op_delegatecall") ∧
  OpHandlerSpec (ofString "op_create2") ∧
  OpHandlerSpec (ofString "op_staticcall")

theorem allOpHandlersSpecA_of_remaining
    (hW : WorldAccountSpecs)
    (hA : RemainingOpHandlersASpecAligned)
    (hB : RemainingOpHandlersBSpecAligned) :
    AllOpHandlersSpecA := by
  rcases hA with
    ⟨h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_msize,
     h_op_push, h_op_dup, h_op_swap, h_op_dupn, h_op_swapn, h_op_exchange⟩
  rcases hB with
    ⟨h_op_calldatacopy, h_op_codecopy, h_op_extcodecopy, h_op_returndatacopy,
     h_op_mcopy, h_op_log,
     h_op_create, h_op_call, h_op_callcode, h_op_delegatecall,
     h_op_create2, h_op_staticcall⟩
  exact
    ⟨opHandlerSpecA_of op_stop_spec, opHandlerSpecA_of op_add_spec, opHandlerSpecA_of op_mul_spec,
     opHandlerSpecA_of op_sub_spec, opHandlerSpecA_of op_div_spec, opHandlerSpecA_of op_sdiv_spec,
     opHandlerSpecA_of op_mod_spec, opHandlerSpecA_of op_smod_spec,
     opHandlerSpecA_of op_addmod_spec, opHandlerSpecA_of op_mulmod_spec,
     opHandlerSpecA_of op_exp_spec, opHandlerSpecA_of op_signextend_spec,
     opHandlerSpecA_of op_lt_spec, opHandlerSpecA_of op_gt_spec, opHandlerSpecA_of op_slt_spec,
     opHandlerSpecA_of op_sgt_spec, opHandlerSpecA_of op_eq_spec, opHandlerSpecA_of op_iszero_spec,
     opHandlerSpecA_of op_and_spec, opHandlerSpecA_of op_or_spec, opHandlerSpecA_of op_xor_spec,
     opHandlerSpecA_of op_not_spec, opHandlerSpecA_of op_byte_spec, opHandlerSpecA_of op_shl_spec,
     opHandlerSpecA_of op_shr_spec, opHandlerSpecA_of op_sar_spec, opHandlerSpecA_of op_clz_spec,
     op_keccak_aligned_spec, opHandlerSpecA_of op_address_spec,
     opHandlerSpecA_of (op_balance_spec hW), opHandlerSpecA_of op_origin_spec,
     opHandlerSpecA_of op_caller_spec, opHandlerSpecA_of op_callvalue_spec,
     opHandlerSpecA_of op_calldataload_spec, opHandlerSpecA_of op_calldatasize_spec,
     opHandlerSpecA_of h_op_calldatacopy,
     opHandlerSpecA_of op_codesize_spec, opHandlerSpecA_of h_op_codecopy,
     opHandlerSpecA_of op_gasprice_spec, opHandlerSpecA_of (op_extcodesize_spec hW),
     opHandlerSpecA_of h_op_extcodecopy,
     opHandlerSpecA_of op_returndatasize_spec, opHandlerSpecA_of h_op_returndatacopy,
     opHandlerSpecA_of (op_extcodehash_spec hW),
     opHandlerSpecA_of h_op_blockhash, opHandlerSpecA_of h_op_coinbase,
     opHandlerSpecA_of h_op_timestamp, opHandlerSpecA_of h_op_number,
     opHandlerSpecA_of h_op_prevrandao, opHandlerSpecA_of h_op_gaslimit,
     opHandlerSpecA_of h_op_chainid, opHandlerSpecA_of (op_selfbalance_spec hW),
     opHandlerSpecA_of h_op_basefee, opHandlerSpecA_of h_op_blobhash,
     opHandlerSpecA_of h_op_blobbasefee, opHandlerSpecA_of h_op_slotnum,
     opHandlerSpecA_of h_op_pop, opHandlerSpecA_of h_op_mload, opHandlerSpecA_of h_op_mstore,
     opHandlerSpecA_of h_op_mstore8, opHandlerSpecA_of (op_sload_spec hW),
     opHandlerSpecA_of (op_sstore_spec hW),
     opHandlerSpecA_of op_jump_spec, opHandlerSpecA_of op_jumpi_spec, opHandlerSpecA_of op_pc_spec,
     opHandlerSpecA_of h_op_msize, opHandlerSpecA_of op_gas_spec, opHandlerSpecA_of op_jumpdest_spec,
     opHandlerSpecA_of op_tload_spec, opHandlerSpecA_of op_tstore_spec, opHandlerSpecA_of h_op_mcopy,
     opHandlerSpecA_of h_op_push,
     opHandlerSpecA_of h_op_dup, opHandlerSpecA_of h_op_swap,
     opHandlerSpecA_of h_op_log, opHandlerSpecA_of h_op_dupn, opHandlerSpecA_of h_op_swapn,
     opHandlerSpecA_of h_op_exchange,
     opHandlerSpecA_of h_op_create, opHandlerSpecA_of h_op_call, opHandlerSpecA_of h_op_callcode,
     op_return_aligned_spec, opHandlerSpecA_of h_op_delegatecall,
     opHandlerSpecA_of h_op_create2, opHandlerSpecA_of h_op_staticcall,
     op_revert_aligned_spec, opHandlerSpecA_of (op_selfdestruct_spec hW)⟩

/-- Aligned `op_dispatch_spec` with Groups 01/02/03/04 (incl. `op_keccak`)/05/06a/07a,
`StateAccountOps`, and Group09 `op_return`/`op_revert` wired
(53 of 87 handlers discharged; 22 A-side + 12 B-side obligations remain). -/
theorem op_dispatch_aligned_spec_of
    (hW : WorldAccountSpecs)
    (hA : RemainingOpHandlersASpecAligned)
    (hB : RemainingOpHandlersBSpecAligned) :
    OpDispatchAlignedSpec :=
  op_dispatch_aligned_spec_of_handlers (allOpHandlersSpecA_of_remaining hW hA hB)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
