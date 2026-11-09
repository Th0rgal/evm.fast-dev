import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Backing
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Stores

/-!
# Wave 8 / R16k: the Phase 1 backing cut — full-entry replay

`PtxPhase1Backing.lean` supplies the backing-strengthened Phase 1 step lemmas
(`state_fresh_tx`, `encode_transaction`, the `encSlot` stores, `alloc`,
`recover_sender_with_chain_id`). This module replays the whole
`ptxPhase1_cut_strong` spine (guest spine 0..34) with `TxBacking` threaded
through every step, under the full entry guard `TxReadyFullStrong`
(`TxReadyStrong ∧ TxBacking ∧ TxValidEncodeReady ∧ TxValidRecoverReady`).

`TxValidEncodeReady` is consumed by `encode_transaction`;
`TxValidRecoverReady` is consumed by `recover_sender_with_chain_id`. From the
recover step onward the guard carries only `(StageP n ∧ TxBacking)`, threaded
by the ScBo adapter `decCallResumeBk_scbo` (mutating callees:
`check_transaction`, `get_account`, `calculate_blob_gas_price`,
`increment_nonce`, `set_account_balance`) and the read-only adapter
`decCallResumeBk_ro_tx` (`validate_transaction`, `calculate_total_blob_gas`,
`fee_mul`, `min`, `u256_sub`); local `dec`s preserve `TxBacking` by
`txBacking_set_local`.

`ptxPhase1_backing_cut_full` is the primary theorem (tail guard
`PtxValidatedBackingStrong`). A `PtxPhase1BackingCut` (entry
`TxReadyBackingStrong`) then follows from any entry implication
`hent : TxReadyBackingStrong → TxReadyFullStrong`
(`ptxPhase1BackingCut_of_full`); `hent` is exactly the external obligation the
Wk tier itself takes as a hypothesis
(`wk_process_transaction_strong_of_callees_and_entry`).
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Contracts.M12

open private checkTxBufs validBufList_checkTxBufs
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

/-! ## A read-only adapter without recover-validity -/

/-- Backing strengthening of any `DecCallResumeOn` whose callee is read-only,
without threading recover-validity (consumed before this region). A read-only
callee returns the entry state with only locals and clock replaced, so
`TxBacking` (memory/global transport) survives. -/
theorem decCallResumeBk_ro_tx {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)}
    (hr : DecCallResumeOn P Q name fname args)
    (hro : ReadOnlyFn fname)
    (hPg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s) :
    DecCallResumeOn (fun s => P s ∧ TxBacking s) (fun s => Q s ∧ TxBacking s) name fname args := by
  intro F state values body callee ret v post hc hp ha hl hb
  have hspec := FunSpec.at_lookup hro state hc values body callee ret hl
    (guestInv_callEntry state callee (hPg state hp.1)) (by rw [hb]; simp)
  rw [hb] at hspec
  have hro_eq : post = { callEntryStateHOLFinite state callee with
      locals := post.locals, clock := post.clock } := by
    have h1 := hspec (Or.inl ⟨v, rfl⟩)
    simpa using h1
  have hmem : ∀ x, memW post x = memW state x := by
    intro x
    rw [hro_eq]
    simp [memW, callEntryStateHOLFinite]
  have hgb : globN post "bo" = globN state "bo" := by
    rw [hro_eq]
    simp [globN, callEntryStateHOLFinite]
  have hset_mem : ∀ x, memW (setVarHOLFinite name v { post with locals := state.locals }) x =
      memW state x := by
    intro x
    have h0 : memW (setVarHOLFinite name v { post with locals := state.locals }) x =
        memW post x := by simp [setVarHOLFinite, memW]
    rw [h0, hmem x]
  have hset_gb : globN (setVarHOLFinite name v { post with locals := state.locals }) "bo" =
      globN state "bo" := by
    have h0 : globN (setVarHOLFinite name v { post with locals := state.locals }) "bo" =
        globN post "bo" := by simp [setVarHOLFinite, globN]
    rw [h0, hgb]
  exact ⟨hr state values body callee ret v post hc hp.1 ha hl hb,
    txBacking_state_congr hset_mem hset_gb hp.2⟩

/-! ## Local bookkeeping with backing -/

/-- The stage locals-only invariant conjoined with `TxBacking`. -/
theorem bk_localsOnly_stage (n : Nat) :
    LocalsOnly (R16Shards.PtxP1.stageNames n)
      (fun s => R16Shards.PtxP1.StageP n s ∧ TxBacking s) :=
  fun {F} s locals k hl hp =>
    ⟨R16Shards.PtxP1.localsOnly_stage n s locals k hl hp.1,
      (R16Shards.txBacking_with_locals s locals k).2 hp.2⟩

/-- Buffer validity for the single `u256_ws` scratch buffer. -/
theorem validBufList_u256_ws : ValidBufList [("u256_ws", 640)] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact ⟨640, by decide, by decide, by decide⟩

/-! ## The `bal_index` assign -/

/-- The `bal_index` global assign preserves `TxBacking` (the globals update
does not touch memory, and `bo` is a different global), `TxValidEncodeReady`
and `TxValidRecoverReady` (the assign does not touch the heap: `heap_ptr` is
unchanged, so both validity facts transport by the unhit lemmas; locals are
untouched by a global assign). -/
theorem phase1_bk_assign_triple :
    Hoare (fun s => TxReadyStrong s ∧ TxBacking s ∧
        TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (.assign .global (ofString "bal_index")
        (.op .add [.var .local (ofString "index"), .const 1#64]))
      (fun r t => r = none → TxBacking t ∧ TxValidEncodeReady t ∧ TxValidRecoverReady t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  revert hr
  split
  · simp
  · rename_i v hv
    split
    · intro _
      obtain ⟨w, rfl⟩ := R16Shards.PtxP1.eval_is_word_op hv
      have hAp : ArenaReady
          (setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s) :=
        arenaReady_setGlobal_word_ne hP.1.1.1.1 (ofString "bal_index") w
          (by decide) (by decide) (by decide)
      have hhp : globN (setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s)
          "heap_ptr" = globN s "heap_ptr" := by
        simp [globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "bal_index" ≠ ofString "heap_ptr" by decide]
      have hbo : globN (setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s)
          "bo" = globN s "bo" := by
        simp [globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "bal_index" ≠ ofString "bo" by decide]
      refine ⟨txBacking_state_congr (fun _ => rfl) hbo hP.2.1, ?_, ?_⟩
      · exact txValidEncodeAt_step_heap_unhit hP.1.1.1.1 hAp (by rw [hhp])
          (fun _ _ _ => rfl) hP.2.2.1
      · exact txValidRecoverReadyAt_step_heap_unhit hP.1.1.1.1 hAp.1 (by rw [hhp])
          (fun _ _ _ => rfl) hP.2.2.2
    · simp

/-! ## The blob branch -/

/-- The blob branch with backing: `calculate_blob_gas_price` is ScBo with the
single `u256_ws` buffer, `fee_mul` is read-only, and the final local assign
preserves `TxBacking` by `txBacking_set_local`. -/
theorem phase1_bk_blobBranch (h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s) R16Shards.PtxP1.blobBranch
      (fun r s => r = none → R16Shards.PtxP1.StageP 2 s ∧ TxBacking s) := by
  apply Hoare.decCall_fall (names := R16Shards.PtxP1.stageNames 2)
    (R := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s) (by decide)
    (bk_localsOnly_stage 2)
  · intro F s vs body callee ret v post hc hp ha hl hb
    exact decCallResumeBk_scbo (Q := R16Shards.PtxP1.StageP 2)
      (R16Shards.PtxP1.resume_scratch_stage (n := 2) (name := ofString "bgp")
        h.wk_calculate_blob_gas_price
      (gs := [("u256_ws", 640, 640)]) (by unfold R16Shards.PtxP1.ScratchSpec; decide) (fun _ => rfl)
      (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp)
      (by decide) (by decide) _)
      (fun _ hp => ⟨hp.1.1.1, hp.1.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1⟩)
      wkScBo_calculate_blob_gas_price validBufList_u256_ws (by decide) (by decide)
      s vs body callee ret v post hc hp ha hl hb
  · apply Hoare.decCall_fall (names := R16Shards.PtxP1.stageNames 2)
      (R := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s) (by decide)
      (bk_localsOnly_stage 2)
    · intro F s vs body callee ret v post hc hp ha hl hb
      exact decCallResumeBk_ro_tx (Q := R16Shards.PtxP1.StageP 2)
        (R16Shards.PtxP1.resume_ro_stage (n := 2) (name := ofString "bgf") h.ro_fee_mul
          (by decide) _)
        h.ro_fee_mul (fun _ hp => hp.1.1.1.1.1)
        s vs body callee ret v post hc hp ha hl hb
    · apply Hoare.assign
      · intro F s v hp _
        exact fun _ => ⟨LocalsOnly.setVar (R16Shards.PtxP1.localsOnly_stage 2) (by decide) v s
            hp.1, txBacking_set_local _ _ hp.2⟩
      · exact fun _ _ hr => by cases hr

/-! ## Suffix pieces with backing -/

/-- Backing-strengthened `phase1_nonce_shapes`: `increment_nonce` is ScBo with
the account-mutation buffers; the stage part comes from
`stage_after_scratchStep` and the backing part from `txBacking_of_scbo_step`
(globals/records keep plus the block-out unhit side condition of the ScBo
step). -/
theorem phase1_bk_nonce_shapes (h : PtxCallees) :
    Hoare (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "sender")])
      (fun r s => r = none → (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧
        PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · refine Hoare.call0_resume ?_
    intro F s vs body callee ret v post hc hP _ hl hb
    have hspec := R16Shards.PtxP1.funSpec_at_lookup wkScBo_increment_nonce
      s hc vs body callee ret hl
      (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) (by rw [hb]; simp)
    rw [hb] at hspec
    have hscbo := hspec (Or.inl ⟨v, rfl⟩)
    have hstep := hscbo.1.1
    have hst1 : R16Shards.PtxP1.StageP 4 { post with locals := s.locals } :=
      R16Shards.PtxP1.stage_after_scratchStep hstep hP.1
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64),
          ("sk_buf", 64, 52)])
        (by unfold R16Shards.PtxP1.ScratchSpec; decide) rfl (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by decide) (by decide)
    have hbonz : globN (callEntryStateHOLFinite s callee) "bo" ≠ 0 := hP.1.1.1.2.1
    have hbkp : TxBacking post :=
      txBacking_of_scbo_returned (s := callEntryStateHOLFinite s callee) (post := post)
        (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) hbonz hP.1.1.2.2.1 hP.1.1.2.2.2.1
        ((R16Shards.txBacking_with_locals s callee (s.clock - 1)).2 hP.2)
        R16Shards.EvmEkFk.validBufList_acctMutBufs (by decide) (by decide) hscbo
    exact ⟨hst1, (R16Shards.txBacking_with_locals post s.locals post.clock).2 hbkp⟩
  · exact phase1_call0_shapes _ _

/-- Backing-strengthened `phase1_sub_balance_shapes`: `u256_sub` is read-only. -/
theorem phase1_bk_sub_balance_shapes (h : PtxCallees) (args : List (ExpHOL 64)) :
    Hoare (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub") args)
      (fun r s => r = none → (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · exact Hoare.callLocal_resume (decCallResumeBk_ro_tx
      (R16Shards.PtxP1.resume_ro_stage h.ro_u256_sub (by decide) _) h.ro_u256_sub
      (fun _ hp => hp.1.1.1.1.1))
  · exact phase1_call_balance_shapes _ _

/-- Backing-strengthened `phase1_set_balance_shapes`: `set_account_balance` is
ScBo with the account-mutation buffers. -/
theorem phase1_bk_set_balance_shapes (h : PtxCallees) (args : List (ExpHOL 64)) :
    Hoare (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.call (some (none, none)) (ofString "set_account_balance") args)
      (fun r s => r = none → (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · refine Hoare.call0_resume ?_
    intro F s vs body callee ret v post hc hP _ hl hb
    have hspec := R16Shards.PtxP1.funSpec_at_lookup wkScBo_set_account_balance
      s hc vs body callee ret hl
      (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) (by rw [hb]; simp)
    rw [hb] at hspec
    have hscbo := hspec (Or.inl ⟨v, rfl⟩)
    have hstep := hscbo.1.1
    have hst1 : R16Shards.PtxP1.StageP 4 { post with locals := s.locals } :=
      R16Shards.PtxP1.stage_after_scratchStep hstep hP.1
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64),
          ("sk_buf", 64, 52)])
        (by unfold R16Shards.PtxP1.ScratchSpec; decide) rfl (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by decide) (by decide)
    have hbonz : globN (callEntryStateHOLFinite s callee) "bo" ≠ 0 := hP.1.1.1.2.1
    have hbkp : TxBacking post :=
      txBacking_of_scbo_returned (s := callEntryStateHOLFinite s callee) (post := post)
        (R16Shards.PtxP1.worldOK_callEntry hP.1.1.1.1 callee) hbonz hP.1.1.2.2.1 hP.1.1.2.2.2.1
        ((R16Shards.txBacking_with_locals s callee (s.clock - 1)).2 hP.2)
        R16Shards.EvmEkFk.validBufList_acctMutBufs (by decide) (by decide) hscbo
    exact ⟨hst1, (R16Shards.txBacking_with_locals post s.locals post.clock).2 hbkp⟩
  · exact phase1_call0_shapes _ _

theorem phase1_bk_set_balance_tail_strong (h : PtxCallees) (args : List (ExpHOL 64))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedBackingStrong tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (none, none)) (ofString "set_account_balance") args) (.seq .skip tail))
      ((K.set_account_balance + 1) + (0 + b)) := by
  apply seq_bound_trans
    (Q := fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_set_account_balance none args s hc
      hp.1.1.1.1.1.1.1
  · exact phase1_bk_set_balance_shapes h args
  · apply seq_bound_trans (Q := PtxValidatedBackingStrong)
    · intro F s hc hp
      exact R16Shards.PtxP1.bound_of_clock
        (P := fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
        (fun s => R16Shards.PtxP1.clock_skip s) s hc hp
    · exact Hoare.skip (fun _ hp _ => ⟨phase1_stage4_strong hp.1.1 hp.2, hp.1.2⟩)
    · exact htail

theorem phase1_bk_sub_balance_tail_strong (h : PtxCallees) (args : List (ExpHOL 64))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub") args) tail)
      ((K.u256_sub + 1) + b) := by
  apply seq_bound_trans
    (Q := fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub
      (some (.local, ofString "bal")) args s hc hp.1.1.1.1.1.1.1
  · exact phase1_bk_sub_balance_shapes h args
  · exact htail

theorem phase1_bk_nonce_balance_decl_strong (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "sender")])
        (.dec (ofString "bal") (.comb [.one, .one, .one, .one])
          (.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "acct"), .const 8])) tail))
      ((K.increment_nonce + 1) + b) := by
  apply seq_bound_trans
    (Q := fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_increment_nonce none _ s hc
      hp.1.1.1.1.1.1.1
  · exact phase1_bk_nonce_shapes h
  · apply dec_bound_trans
      (Q := fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
    · intro F s v hp he
      exact ⟨⟨LocalsOnly.setVar (R16Shards.PtxP1.localsOnly_stage 4) (by decide) v s hp.1.1,
        txBacking_set_local _ _ hp.1.2⟩,
        ptxPhase2LocalShapes_set_other s hp.2 _ v (by decide)⟩
    · exact htail

/-- The complete Phase 1 suffix after the reservoir declaration, with backing. -/
theorem phase1_bk_balance_suffix (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedBackingStrong tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 4 s ∧ TxBacking s) ∧ PtxPhase2LocalShapes s)
      (phase1BalanceSuffix tail)
      ((K.increment_nonce + 1) + ((K.u256_sub + 1) + ((K.u256_sub + 1) +
        ((K.set_account_balance + 1) + (0 + b))))) := by
  unfold phase1BalanceSuffix
  apply phase1_bk_nonce_balance_decl_strong h
  apply phase1_bk_sub_balance_tail_strong h
  apply phase1_bk_sub_balance_tail_strong h
  exact phase1_bk_set_balance_tail_strong h _ htail

/-! ## The main replay -/

/-- **The Phase 1 backing cut, full-entry form** (spine 0..34): the whole
`ptxPhase1` replay with `TxBacking` (and the two validity envelopes) threaded
from `TxReadyFullStrong` at the entry to `PtxValidatedBackingStrong` at the
tail. -/
theorem ptxPhase1_backing_cut_full (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedBackingStrong tail b) :
    TerminatingProgBoundedOn TxReadyFullStrong (ptxPhase1 tail) (ptxCost1 + b) := by
  open R16Shards.PtxP1 in
  have hb : TerminatingProgBoundedOn
      (fun s => StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (ptxPhase1 tail) (phase1Budget b) := by
    unfold phase1Budget ptxPhase1 ptxCode
    simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil, spinePlug]
    refine seq_bound_trans
      (Q := fun s => StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (bound_mono
        (Q := fun s => StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
        (TerminatingProgBoundedOn.call_guestInv h.fb_state_fresh_tx none [])
        (fun _ hp => hp.1.1.1.1.1.1)) ?_ ?_
    · exact hoare_state_fresh_tx_bk
    refine seq_bound_trans
      (Q := fun s => (StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s) ∧
        PtxLocalShapeMap [("tx", .one), ("index", .one)] s)
      (bound_of_clock
        (P := fun {F} s => StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
        (fun s => clock_assign s .global (ofString "bal_index")
        (.op .add [.var .local (ofString "index"), .const 1#64]))) ?_ ?_
    · refine ⟨fun s hc hp hn hr => ?_⟩
      have hh := phase1_assign_bal_index_shapes.run s hc hp.1 hn hr
      have hh2 := phase1_bk_assign_triple.run s hc ⟨hp.1.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ hn hr
      refine ⟨⟨hh.1, hh2.1, hh2.2.1, hh2.2.2⟩, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · obtain ⟨w, hw⟩ := hh.2 "tx" (by simp)
        exact ⟨_, hw, by simp [shapeOfHOLExact]⟩
      · obtain ⟨w, hw⟩ := hh.2 "index" (by simp)
        exact ⟨_, hw, by simp [shapeOfHOLExact]⟩
    refine phase1_call_shape_map
      (P := fun {F} s => StageP 0 s ∧ TxBacking s ∧ TxValidEncodeReady s ∧ TxValidRecoverReady s)
      (Q := fun s => EncReady s ∧ TxBacking s ∧ TxValidRecoverReady s)
      h.fb_encode_transaction _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 0 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb hs
      exact resume_encode_bk s vs body callee ret v post hc
        ⟨hp.1.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ ha hl hb hs
    refine seq_bound_trans ?_ (phase1_frame_map (store_encSlot_bk false) (phase1_map_store _ _ _)) ?_
    · intro F s hc hp
      intro hn
      rw [clock_store]
      exact ⟨by omega, le_rfl⟩
    refine seq_bound_trans ?_ (phase1_frame_map (store_encSlot_bk true) (phase1_map_store _ _ _)) ?_
    · intro F s hc hp
      intro hn
      rw [clock_store]
      exact ⟨by omega, le_rfl⟩
    apply seq_bound_trans
      (Q := fun s => (StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s) ∧
        PtxLocalShapeMap [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] s)
    · intro F s hc hp
      intro hn
      rw [clock_skip]
      exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ =>
        ⟨⟨stage0 hp.1.1.1, ⟨hp.1.2.1, hp.1.2.2⟩⟩, hp.2⟩)
    refine phase1_call_keep_map
      (P := fun {F} s => StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (Q := fun {F} s => StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s)
      h.fb_tx_chain_id "cid" (.comb [.one, .one]) [.var .local (ofString "tx")]
      (fun s vs body callee ret hc hp ha hl => stage_entry 0 _ _ s vs body callee ret hc hp.1 ha hl)
      (decCallResumeBk_ro (resume_ro_stage (n := 0) (name := ofString "cid")
        h.ro_tx_chain_id (by decide) [.var .local (ofString "tx")]) h.ro_tx_chain_id
        (by decide) (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · decide
    refine seq_bound_trans ?_
      (phase1_frame_map
        (phase1_chainGuard_keeps (fun s => StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s))
        (phase1_chainGuard_keeps _)) ?_
    · intro F s hc hp
      exact chainGuard_bound s hc hp.1.1
    refine phase1_call_shape_map
      (P := fun {F} s => StageP 0 s ∧ TxBacking s ∧ TxValidRecoverReady s)
      (Q := fun s => R16Shards.PtxP1.SenderAllocated s ∧ TxBacking s ∧ TxValidRecoverReady s)
      h.fb_alloc _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 0 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb hsh
      exact resume_alloc_sender_bk h s vs body callee ret v post hc hp ha hl hb hsh
    refine seq_bound_trans ?_
      (phase1_frame_map
        (P := fun {F} s => R16Shards.PtxP1.SenderAllocated s ∧ TxBacking s ∧ TxValidRecoverReady s)
        (Q := fun {F} s => R16Shards.PtxP1.StageP 1 s ∧ TxBacking s)
        (Hoare.mono (hoare_recover_sender_bk h) (fun _ hp => ⟨hp.1, hp.2.2, hp.2.1⟩))
        (phase1_map_call0 _ _ _)) ?_
    · intro F s hc hp
      exact TerminatingProgBoundedOn.call_guestInv h.fb_recover_sender_with_chain_id none _
        s hc hp.1.1.1.1.1.1.1
    apply seq_bound_trans (Q := fun s => (StageP 1 s ∧ TxBacking s) ∧
      PtxLocalShapeMap [("sender", ShapeHOL.one), ("enc", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]),
        ("tx", ShapeHOL.one), ("index", ShapeHOL.one)] s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_call_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 1 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s)
      h.fb_validate_transaction _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 1 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact decCallResumeBk_ro_tx (resume_validate h) h.ro_validate_transaction
        (fun _ hp => hp.1.1.1.1.1) s vs body callee ret v post hc hp ha hl hb
    apply seq_bound_trans (Q := fun s => (StageP 2 s ∧ TxBacking s) ∧
      PtxLocalShapeMap [("intrinsic", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("sender", ShapeHOL.one), ("enc", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]),
        ("tx", ShapeHOL.one), ("index", ShapeHOL.one)] s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_dec_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    refine phase1_call_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s)
      h.fb_check_transaction _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 2 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact decCallResumeBk_scbo (resume_scratch_stage h.wk_check_transaction
          (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64),
            ("sk_buf", 64, 52), ("u256_ws", 640, 640)])
          (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _)
        (fun _ hp => ⟨hp.1.1.1, hp.1.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1⟩)
        wkScBo_check_transaction validBufList_checkTxBufs (by decide) (by decide)
        s vs body callee ret v post hc hp ha hl hb
    apply seq_bound_trans (Q := fun s => (StageP 2 s ∧ TxBacking s) ∧
      PtxLocalShapeMap [("price", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("intrinsic_gas", ShapeHOL.one), ("intrinsic", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("sender", ShapeHOL.one), ("enc", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]),
        ("tx", ShapeHOL.one), ("index", ShapeHOL.one)] s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_call_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s)
      h.fb_calculate_total_blob_gas _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 2 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact decCallResumeBk_ro_tx (resume_ro_stage h.ro_calculate_total_blob_gas (by decide) _)
        h.ro_calculate_total_blob_gas (fun _ hp => hp.1.1.1.1.1)
        s vs body callee ret v post hc hp ha hl hb
    refine phase1_call_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      h.fb_get_account "acct" .one [.var .local (ofString "sender")]
      (fun s vs body callee ret hc hp ha hl => stage_entry 2 _ _ s vs body callee ret hc hp.1 ha hl)
      (decCallResumeBk_scbo (resume_scratch_stage (n := 2) (name := ofString "acct")
          h.wk_get_account
          (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)])
          (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide)
          [.var .local (ofString "sender")])
        (fun _ hp => ⟨hp.1.1.1, hp.1.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1⟩)
        wkScBo_get_account R16Shards.EvmEkFk.validBufList_wsAcctBufs (by decide) (by decide))
      ?_ ?_
    · decide
    apply seq_bound_trans (Q := fun s => (StageP 2 s ∧ TxBacking s) ∧
      PtxLocalShapeMap [("tx_blob_gas_used", ShapeHOL.one),
        ("price", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("intrinsic_gas", ShapeHOL.one), ("intrinsic", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("sender", ShapeHOL.one), ("enc", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]),
        ("tx", ShapeHOL.one), ("index", ShapeHOL.one)] s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_dec_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    apply seq_bound_trans (Q := fun s => (StageP 2 s ∧ TxBacking s) ∧
      PtxLocalShapeMap [("tx_blob_gas_used", ShapeHOL.one),
        ("price", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("intrinsic_gas", ShapeHOL.one), ("intrinsic", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]),
        ("sender", ShapeHOL.one), ("enc", ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]),
        ("tx", ShapeHOL.one), ("index", ShapeHOL.one)] s)
    · apply TerminatingProgBoundedOn.ite_on
      · intro F s hc hp
        exact blobBranch_bound h s hc hp.1.1
      · intro F s hc hp hn
        rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · apply Hoare.ite
      · apply Hoare.mono (phase1_frame_map (phase1_bk_blobBranch h) ?_) (fun _ hp => hp.1)
        apply Hoare.decCall_fall (by decide) (phase1_map_localsOnly _)
        · intro F s vs body callee ret v post hc hp ha hl hb
          exact ptxLocalShapeMap_resume s post hp _ v (by decide)
        · apply Hoare.decCall_fall (by decide) (phase1_map_localsOnly _)
          · intro F s vs body callee ret v post hc hp ha hl hb
            exact ptxLocalShapeMap_resume s post hp _ v (by decide)
          · apply Hoare.assign
            · intro F s v hp _ _
              exact LocalsOnly.setVar (phase1_map_localsOnly _) (by decide) v s hp
            · exact fun _ _ hr => by cases hr
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => by cases hr
    refine phase1_dec_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    refine phase1_call_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      h.fb_fee_mul _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 2 _ _ s vs body callee ret hc hp.1 ha hl)
      (decCallResumeBk_ro_tx (resume_ro_stage h.ro_fee_mul (by decide) _) h.ro_fee_mul
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · decide
    refine phase1_dec_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    refine phase1_dec_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 2 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    refine phase1_dec_keep_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 2 s ∧ TxBacking s)
      (Q := fun s => StageP 3 s ∧ TxBacking s) _ _ _
      (fun s v hp hv => ⟨declare_regular_budget s v hp.1 hv, txBacking_set_local _ _ hp.2⟩)
      (by decide) ?_
    refine phase1_call_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 3 s ∧ TxBacking s)
      (Q := fun s => StageP 4 s ∧ TxBacking s) h.fb_min _ _ _
      (fun s vs body callee ret hc hp ha hl => stage_entry 3 _ _ s vs body callee ret hc hp.1 ha hl)
      ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact decCallResumeBk_ro_tx (resume_min h) h.ro_min (fun _ hp => hp.1.1.1.1.1)
        s vs body callee ret v post hc hp ha hl hb
    refine phase1_dec_shape_map
      (P := fun {F} s => R16Shards.PtxP1.StageP 4 s ∧ TxBacking s)
      (Q := fun s => StageP 4 s ∧ TxBacking s) _ _ _
      (fun s v hp _ => ⟨LocalsOnly.setVar (localsOnly_stage 4) (by decide) v s hp.1,
        txBacking_set_local _ _ hp.2⟩) (by decide) ?_
    apply bound_mono (phase1_bk_balance_suffix h htail)
    intro F s hp
    refine ⟨⟨hp.1.1, hp.1.2⟩, phase1_map_strong hp.2 ?_ (by simp) (by simp) (by simp)⟩
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have he : R16Shards.PtxP1.phase1Budget b = ptxCost1 + b := by
    simp only [R16Shards.PtxP1.phase1Budget, ptxCost1, Nat.add_zero, Nat.zero_add, Nat.max_zero,
      Nat.add_comm, Nat.add_left_comm]
  rw [he] at hb
  intro F s hc hp
  exact hb s hc ⟨R16Shards.PtxP1.stage0 hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-! ## The cut -/

/-- The honest `hent`-parameterized adapter: the full-entry cut yields a
`PtxPhase1BackingCut` under any entry implication
`TxReadyBackingStrong → TxReadyFullStrong`. This is exactly the external
obligation the Wk tier itself takes as a hypothesis
(`wk_process_transaction_strong_of_callees_and_entry`), made explicit here
rather than assumed. -/
theorem ptxPhase1BackingCut_of_full
    (hfull : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxValidatedBackingStrong tail b →
      TerminatingProgBoundedOn TxReadyFullStrong (ptxPhase1 tail) (ptxCost1 + b))
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyBackingStrong s → TxReadyFullStrong s) :
    PtxPhase1BackingCut :=
  fun tail b ht => R16Shards.PtxP1.bound_mono (hfull tail b ht) (fun s hs => hent s hs)

/-- The Phase 1 backing cut from the full-entry replay, with the entry
implication as an explicit hypothesis. -/
theorem ptxPhase1_backing_cut (h : PtxCallees)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyBackingStrong s → TxReadyFullStrong s) :
    PtxPhase1BackingCut :=
  ptxPhase1BackingCut_of_full (fun tail b ht => ptxPhase1_backing_cut_full h ht) hent

end InitECandidate.Solver.Wave8GuestInv.R13Shards
