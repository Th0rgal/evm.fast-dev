import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Compose
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def phase1Budget (b : Nat) : Nat := ((K.state_fresh_tx + 1) + (((0) + (((K.encode_transaction) + (((0) + (((0) + (((0) + (((K.tx_chain_id) + (((0) + (((K.alloc) + (((K.recover_sender_with_chain_id + 1) + (((0) + (((K.validate_transaction) + (((0) + (((K.check_transaction) + (((0) + (((K.calculate_total_blob_gas) + (((K.get_account) + (((0) + (((max ((K.calculate_blob_gas_price + 1) + (K.fee_mul + 1)) 0) + (((K.fee_mul) + (((K.min) + (((K.increment_nonce + 1) + (((K.u256_sub + 1) + (((K.u256_sub + 1) + (((K.set_account_balance + 1) + (((0) + (b))))))))))) + 1)) + 1)))))) + 1)) + 1)))) + 1)))) + 1)))))) + 1)))) + 1)))))))) + 1)))))

theorem phase1_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidated tail b) :
    TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 tail) (ptxCost1 + b) := by
  have hb : TerminatingProgBoundedOn (StageP 0) (ptxPhase1 tail) (phase1Budget b) := by
      unfold phase1Budget ptxPhase1 ptxCode
      -- 0: refresh transaction state.
      refine seq_bound (Q := StageP 0) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_state_fresh_tx none [])
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
      · exact hoare_call_scratch_stage h.wk_state_fresh_tx (gs := []) (by simp [ScratchSet])
          (fun _ => rfl) (by decide) (by decide) (boKeep := [0,8,16,24,32,40,48,56,64,72,80])
          (by simp) (by decide) []
      -- 1: record the transaction index.
      refine seq_bound (Q := StageP 0) (bound_of_clock (fun s => clock_assign s _ _ _)) ?_ ?_
      · apply Hoare.assign
        · intro F s v hp hv
          exact fun _ => stage0 (txReadyStrong_assign_bal_index hp.1 v)
        · exact fun _ _ hr => by cases hr
      -- 2: obtain the pair used by the two output-array stores.
      refine decCall_shape_bound (Q := EncReady) h.fb_encode_transaction _ _ _ (stage_entry 0 _ _) ?_ ?_
      · intro F s vs body callee ret v post hc hp ha hl hr hsh
        exact resume_encode h s vs body callee ret v post hc hp.1 ha hl hr hsh
      -- 3--5: output encoding and resume the invariant without the temporary pair.
      refine seq_bound (Q := EncReady) (bound_of_clock (fun s => clock_store s _ _)) (store_encSlot false) ?_
      refine seq_bound (Q := EncReady) (bound_of_clock (fun s => clock_store s _ _)) (store_encSlot true) ?_
      refine seq_bound (Q := StageP 0) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => stage0 hp.1)) ?_
      -- 6--7: chain-id lookup and rejecting guard.
      refine TerminatingProgBoundedOn.decCall_on h.fb_tx_chain_id _ _ _ (stage_entry 0 _ _)
        (resume_ro_stage h.ro_tx_chain_id (by decide) _) ?_
      refine seq_bound (Q := StageP 0) chainGuard_bound chainGuard_hoare ?_
      -- 8--10: fresh sender buffer and recovery.
      refine TerminatingProgBoundedOn.decCall_on (Q := SenderAllocated) h.fb_alloc _ _ _ (stage_entry 0 _ _)
        (resume_alloc_sender h) ?_
      refine seq_bound (Q := StageP 1) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_recover_sender_with_chain_id none _)
        (fun _ hp => hp.1.1.1.1.1)) (hoare_recover_sender h) ?_
      refine seq_bound (Q := StageP 1) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
      -- 11--13: validation supplies the intrinsic-gas bound.
      refine TerminatingProgBoundedOn.decCall_on h.fb_validate_transaction _ _ _ (stage_entry 1 _ _)
        (resume_validate h) ?_
      refine seq_bound (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
      -- 14--19: fee checks, account lookup, and the blob-fee local.
      refine TerminatingProgBoundedOn.decCall_on (Q := StageP 2) h.fb_check_transaction _ _ _ (stage_entry 2 _ _) ?_ ?_
      · exact resume_scratch_stage h.wk_check_transaction
          (gs := [("keccak_pad",136),("keccak_st",200),("mpt_nib_scratch",64),("sk_buf",64),("u256_ws",640)])
          (by unfold ScratchSet; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide) (by decide) _
      refine seq_bound (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
      refine TerminatingProgBoundedOn.decCall_on h.fb_calculate_total_blob_gas _ _ _ (stage_entry 2 _ _)
        (resume_ro_stage h.ro_calculate_total_blob_gas (by decide) _) ?_
      refine TerminatingProgBoundedOn.decCall_on (Q := StageP 2) h.fb_get_account _ _ _ (stage_entry 2 _ _) ?_ ?_
      · exact resume_scratch_stage h.wk_get_account
          (gs := [("keccak_pad",136),("keccak_st",200),("mpt_nib_scratch",64)])
          (by unfold ScratchSet; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide) (by decide) _
      refine seq_bound (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
      -- 20: the optional blob-fee calculation.
      refine seq_bound (Q := StageP 2) (TerminatingProgBoundedOn.ite_on (blobBranch_bound h) (bound_of_clock clock_skip)) ?_ ?_
      · exact Hoare.ite (Hoare.mono (blobBranch_hoare h) (fun _ hp => hp.1))
          (Hoare.skip (fun _ hp _ => hp.1)) (fun _ _ hr => by cases hr)
      -- 21--25: arithmetic locals and the bounded regular gas budget.
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
      refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _ (stage_entry 2 _ _)
        (resume_ro_stage h.ro_fee_mul (by decide) _) ?_
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
      refine dec_bound declare_regular_budget ?_
      -- 26--29: min caps message gas; the world update preserves it.
      refine TerminatingProgBoundedOn.decCall_on h.fb_min _ _ _ (stage_entry 3 _ _) (resume_min h) ?_
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 4) _ (by decide) _ _ ?_
      refine seq_bound (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_increment_nonce none _)
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
      · exact hoare_call_scratch_stage h.wk_increment_nonce
          (gs := [("keccak_pad",136),("keccak_st",200),("mpt_nib_scratch",64),("sk_buf",64)])
          (by unfold ScratchSet; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide) _
      refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 4) _ (by decide) _ _ ?_
      -- 30--33: subtract the fees, write the balance, and enter the caller's tail.
      refine seq_bound (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub (some (.local,ofString "bal")) _)
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
      · exact Hoare.callLocal_resume (resume_ro_stage h.ro_u256_sub (by decide) _)
      refine seq_bound (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub (some (.local,ofString "bal")) _)
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
      · exact Hoare.callLocal_resume (resume_ro_stage h.ro_u256_sub (by decide) _)
      refine seq_bound (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_set_account_balance none _)
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
      · exact hoare_call_scratch_stage h.wk_set_account_balance
          (gs := [("keccak_pad",136),("keccak_st",200),("mpt_nib_scratch",64),("sk_buf",64)])
          (by unfold ScratchSet; decide) (fun _ => rfl) (by decide) (by decide)
          (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide) _
      exact seq_bound (Q := PtxValidated) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => stage4_validated hp)) htail
  have he : phase1Budget b = ptxCost1 + b := by
    simp only [phase1Budget,ptxCost1,Nat.add_zero,Nat.zero_add,Nat.max_zero,
      Nat.add_comm,Nat.add_left_comm]
  rw [he] at hb
  intro F s hc hp
  exact hb s hc (stage0 hp)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
