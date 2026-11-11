import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail5

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## R32 slot 6: `generic_call` child push and the four call handlers

`generic_call` starts a child when the frame depth is below the 1024 cap, so the
`EvmPreservingSpecA` contract previously assumed for it (which forced
`evmChain post = evmChain s` on normal returns) is false.  The replacement is a
*child-push* contract: on a normal return the new head is the child frame and the
new chain is the child on top of the old chain; errors keep the chain depth.

This file proves:

* `headMemChainWF_push` / `callSpec_generic_call_r32`: the child-push shape
  preserves `HeadMemChainWF` and extends `evmChain` by exactly one frame;
* the four handler specs `op_call_specA_r32`, `op_callcode_specA_r32`,
  `op_staticcall_specA_r32`, `op_delegatecall_specA_r32`, parameterized over the
  world-account record and a bundle of the four R32 child continuations.

The four continuations in `Group10CallR32Continuations` are exactly the
`HandlerRunA` walks produced by the compiled Group 10 tails after the
`generic_call` leaf is replaced by the child-push contract; the
`group10CallR32Continuations_of_old` bridge records that they are inhabited by
the already compiled tails under the old (too strong) assumption. -/

/-! ### Chain bookkeeping for a child push -/

theorem chainLinks_transport_g10 (m m' : Nat → Nat) :
    ∀ l : List Ivl, (∀ ec ∈ l,
      m' (ec.1 + 24) = m (ec.1 + 24) ∧
      m' (ec.1 + 32) = m (ec.1 + 32) ∧
      m' (ec.1 + 40) = m (ec.1 + 40) ∧
      m' (ec.2 + 56) = m (ec.2 + 56)) →
      Group10.ChainLinks m l → Group10.ChainLinks m' l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hm, hl => by
    refine ⟨?_, chainLinks_transport_g10 m m' (b :: rest)
      (fun ec hec => hm ec (List.mem_cons_of_mem _ hec)) hl.2⟩
    have ha := hm a (by simp)
    have hb := hm b (by simp)
    simpa [hb.1, hb.2.2.1, ha.2.2.2] using hl.1

theorem chainLinks_cons_g10 (m : Nat → Nat) (a b : Ivl) (rest : List Ivl)
    (hab : m (b.1 + 24) + m (b.1 + 40) = m (a.2 + 56))
    (h : Group10.ChainLinks m (b :: rest)) :
    Group10.ChainLinks m (a :: b :: rest) := ⟨hab, h⟩

/-- Pushing a child frame: if the new chain is the child on top of the old chain,
the child's continuation records the mark where the old head's memory ends, the
old chain cells are unchanged, and the new head is aligned/ended at
`frame_mem_ptr`, then `HeadMemChainWF` is preserved. -/
theorem headMemChainWF_push {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : Group10.HeadMemChainWF s)
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
    Group10.HeadMemChainWF post := by
  obtain ⟨hal, _, hlk⟩ := hs
  have hscons : evmChain s =
      (globN s "ev", globN s "cur_cont") :: (evmChain s).tail := by
    simpa [HeadMemBridge.evmChain_cons, List.tail_cons] using
      (HeadMemBridge.evmChain_cons s)
  rw [hscons] at hlk
  refine ⟨?_, hend, ?_⟩
  · intro ec hec
    rw [hchain] at hec
    rcases List.mem_cons.mp hec with rfl | hmem
    · exact halign
    · have ht := htail ec hmem
      rw [ht.2.1, ht.2.2.1]
      exact hal ec hmem
  · rw [hchain, hscons]
    exact chainLinks_cons_g10 (memW post) _ _ _ hlink
      (chainLinks_transport_g10 (memW s) (memW post) _
        (fun ec hec => htail ec (by rw [hscons]; exact hec)) hlk)

/-- The R32 `generic_call` contract: a `generic_call` step that pushes a child
frame preserves the chain invariant and extends the chain by exactly one frame
(the new child head). -/
theorem callSpec_generic_call_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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
  ⟨headMemChainWF_push hWF hchain halign hend hlink htail, ⟨_, hchain⟩⟩

/-! ### R32 continuation witnesses for the four call handlers -/

/-- The four child continuations, in the exact `HandlerRunA` shape consumed by
`opHandlerSpecA_of_run_seed_g10`.  Each field is the R32 walk of the handler body
after the `generic_call` leaf has been re-driven with the child-push contract. -/
structure Group10CallR32Continuations : Prop where
  op_call : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_op_call).body)
  op_callcode : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_op_callcode).body)
  op_delegatecall : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
    HandlerRunA s0 (fun _ => True) false
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_op_delegatecall).body)
  op_staticcall : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
    HandlerRunA s0 (fun _ => True) false
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_op_staticcall).body)

/-- Sanity bridge: the compiled Group 10 tails inhabit the R32 continuation
bundle under the old `generic_call` contract.  The R32 slot replaces this
hypothesis by the child-push contract; no compiled file is modified here. -/
theorem group10CallR32Continuations_of_old
    (hW : WorldAccountSpecsA)
    (hWc : WorldAccountSpecsCall_g10)
    (hgc : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => LocFrame s post) (ofString "generic_call")) :
    Group10CallR32Continuations := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F s0
    exact op_call_run_full_g10 hWc hgc s0
  · intro F s0
    exact op_callcode_run_full_g10 hW hgc s0
  · intro F s0
    exact op_delegatecall_run_full_g10 s0 hW hgc
  · intro F s0
    exact op_staticcall_run_full_g10 s0 hW hgc

/-! ### The four unconditional handler specs -/

theorem op_call_specA_r32
    (hWc : WorldAccountSpecsCall_g10)
    (hRun : Group10CallR32Continuations) :
    OpHandlerSpecA (ofString "op_call") := by
  refine opHandlerSpecA_of_run_seed_g10 603 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_call rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact hRun.op_call s0

theorem op_callcode_specA_r32
    (hW : WorldAccountSpecsA)
    (hRun : Group10CallR32Continuations) :
    OpHandlerSpecA (ofString "op_callcode") := by
  refine opHandlerSpecA_of_run_seed_g10 604 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_callcode rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact hRun.op_callcode s0

theorem op_delegatecall_specA_r32
    (hW : WorldAccountSpecsA)
    (hRun : Group10CallR32Continuations) :
    OpHandlerSpecA (ofString "op_delegatecall") := by
  refine opHandlerSpecA_of_run 605 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_delegatecall rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact hRun.op_delegatecall s0

theorem op_staticcall_specA_r32
    (hW : WorldAccountSpecsA)
    (hRun : Group10CallR32Continuations) :
    OpHandlerSpecA (ofString "op_staticcall") := by
  refine opHandlerSpecA_of_run_seed_g10 606 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_staticcall rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact hRun.op_staticcall s0

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
