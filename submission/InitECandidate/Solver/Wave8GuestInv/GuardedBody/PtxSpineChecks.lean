import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts

/-! Regression checks for the shared native transaction decomposition.

These checks use the published `PtxCuts` definitions directly. They verify
checkpoint positions, actual continuation placement, reconstruction, and symbolic
phase budgets; semantic phase bounds remain the responsibility of the leaves.
-/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.SpineChecks
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitE

abbrev cost := ptxCost
abbrev phase1 := ptxPhase1
abbrev phase2 := ptxPhase2
abbrev phase3 := ptxPhase3
abbrev phase4 := ptxPhase4
abbrev phase5 := ptxPhase5

theorem phases_eq : ptxCode = phase1 (phase2 (phase3 (phase4 phase5))) :=
  ptx_phases_eq

theorem checkpoint34 :
    ∃ body : ProgHOL 64, spineAt 34 ptxCode =
      .decCall (ofString "te") .one (ofString "te_new") [] body := by
  unfold ptxCode
  exact ⟨_, rfl⟩

theorem checkpoint98 :
    ∃ body : ProgHOL 64, spineAt 98 ptxCode =
      .decCall (ofString "out") .one (ofString "process_message_call")
        [.var .local (ofString "m")] body := by
  unfold ptxCode
  exact ⟨_, rfl⟩

theorem checkpoint99 :
    ∃ (e : ExpHOL 64) (body : ProgHOL 64), spineAt 99 ptxCode =
      .dec (ofString "used_before_refund") .one e body := by
  unfold ptxCode
  exact ⟨_, _, rfl⟩

theorem checkpoint139 :
    ∃ (e : ExpHOL 64) (body : ProgHOL 64), spineAt 139 ptxCode =
      .dec (ofString "del") .one e body := by
  unfold ptxCode
  exact ⟨_, _, rfl⟩

theorem checkpoint144 :
    ∃ e : ExpHOL 64, spineAt 144 ptxCode = .return e := by
  unfold ptxCode
  exact ⟨_, rfl⟩

/-- Each proposed cut actually installs its continuation at the claimed depth. -/
theorem phase1_tail (tail : ProgHOL 64) : spineAt 34 (phase1 tail) = tail := by
  unfold phase1 ptxPhase1 ptxCode
  rfl

theorem phase2_tail (tail : ProgHOL 64) : spineAt 64 (phase2 tail) = tail := by
  unfold phase2 ptxPhase2 ptxCode
  rfl

theorem phase3_tail (tail : ProgHOL 64) : spineAt 1 (phase3 tail) = tail := by
  unfold phase3 ptxPhase3 ptxCode
  rfl

theorem phase4_tail (tail : ProgHOL 64) : spineAt 40 (phase4 tail) = tail := by
  unfold phase4 ptxPhase4 ptxCode
  rfl

theorem phase1_injective : Function.Injective phase1 := by
  intro tail₁ tail₂ h
  have htail := congrArg (spineAt 34) h
  simpa only [phase1_tail] using htail

/-- These are syntactic charge equalities, not semantic termination bounds. -/
theorem cost_phase1 : cost (phase1 .skip) = ptxCost1 := by
  unfold phase1 ptxPhase1 ptxCode
  change ((K.«state_fresh_tx» + 1) + (0 + ((K.«encode_transaction» + 1) + (0 + (0 + (0 + ((K.«tx_chain_id» + 1) + ((Nat.max (Nat.max 0 0) 0) + ((K.«alloc» + 1) + ((K.«recover_sender_with_chain_id» + 1) + (0 + ((K.«validate_transaction» + 1) + (0 + ((K.«check_transaction» + 1) + (0 + ((K.«calculate_total_blob_gas» + 1) + ((K.«get_account» + 1) + (0 + ((Nat.max ((K.«calculate_blob_gas_price» + 1) + ((K.«fee_mul» + 1) + 0)) 0) + ((K.«fee_mul» + 1) + ((K.«min» + 1) + ((K.«increment_nonce» + 1) + ((K.«u256_sub» + 1) + ((K.«u256_sub» + 1) + ((K.«set_account_balance» + 1) + (0 + 0)))))))))))))))))))))))))) = ptxCost1
  simp only [ptxCost1, Nat.add_zero, Nat.zero_add, Nat.max_self, Nat.add_assoc]

private theorem cost_phase2_algebra (k : MlS → Nat) (w : Nat) :
    ((k (ofString "te_new") + 1) + (0 + (0 + (0 + (0 + (0 + (0 + ((k (ofString "tx_has_access_list") + 1) + ((Nat.max 0 0) + ((k (ofString "alloc") + 1) + (0 + ((w * ((0 + (0 + 0)) + 1)) + ((k (ofString "alloc") + 1) + (0 + ((w * (((w * (((k (ofString "memcpy") + 1) + ((k (ofString "memcpy") + 1) + (0 + 0))) + 1)) + 0) + 1)) + (0 + (0 + (0 + (0 + ((k (ofString "tx_is_blob") + 1) + ((Nat.max (0 + 0) 0) + ((k (ofString "tx_is_setcode") + 1) + ((Nat.max (0 + 0) 0) + (0 + (0 + ((k (ofString "alloc") + 1) + ((k (ofString "keccak256") + 1) + (0 + (0 + (0 + (0 + ((k (ofString "msg_new") + 1) + (0 + (0 + (0 + (0 + (0 + (0 + (0 + ((k (ofString "htab_new") + 1) + (0 + ((k (ofString "htab_set") + 1) + (0 + (0 + ((w * (((k (ofString "htab_set") + 1) + 0) + 1)) + (0 + ((w * (((k (ofString "htab_set") + 1) + 0) + 1)) + (0 + ((k (ofString "htab_new") + 1) + (0 + ((w * (((k (ofString "htab_set") + 1) + 0) + 1)) + (0 + ((k (ofString "alloc") + 1) + ((Nat.max ((k (ofString "get_account") + 1) + ((k (ofString "alloc") + 1) + ((k (ofString "compute_contract_address") + 1) + (0 + (0 + (0 + (0 + (0 + 0)))))))) (0 + (0 + (0 + (0 + (0 + 0)))))) + (0 + (0 + ((k (ofString "htab_set") + 1) + (0 + (0 + (0 + 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) =
      (k (ofString "te_new") + 1) + (k (ofString "tx_has_access_list") + 1) + (k (ofString "alloc") + 1) + w * (0 + 1) + (k (ofString "alloc") + 1) + w * (w * ((k (ofString "memcpy") + 1) + (k (ofString "memcpy") + 1) + 1) + 1) + (k (ofString "tx_is_blob") + 1) + (k (ofString "tx_is_setcode") + 1) + (k (ofString "alloc") + 1) + (k (ofString "keccak256") + 1) + (k (ofString "msg_new") + 1) + (k (ofString "htab_new") + 1) + (k (ofString "htab_set") + 1) + w * ((k (ofString "htab_set") + 1) + 1) + w * ((k (ofString "htab_set") + 1) + 1) + (k (ofString "htab_new") + 1) + w * ((k (ofString "htab_set") + 1) + 1) + (k (ofString "alloc") + 1) + Nat.max ((k (ofString "get_account") + 1) + (k (ofString "alloc") + 1) + (k (ofString "compute_contract_address") + 1)) (0) + (k (ofString "htab_set") + 1) := by
  simp only [Nat.add_zero, Nat.zero_add, Nat.max_self, Nat.add_assoc]

theorem cost_phase2 : cost (phase2 .skip) = ptxCost2 := by
  unfold phase2 ptxPhase2 ptxCode
  exact cost_phase2_algebra ptxCharge (2 ^ 64 + 1)

theorem cost_phase3 : cost (phase3 .skip) = ptxCost3 := by
  unfold phase3 ptxPhase3 ptxCode
  change ((K.«process_message_call» + 1) + 0) = ptxCost3
  simp only [ptxCost3, Nat.add_zero]

private theorem cost_phase4_algebra (k : MlS → Nat) (w : Nat) :
    ((k (ofString "udiv_small5") + 1) + ((k (ofString "min") + 1) + ((k (ofString "max") + 1) + ((k (ofString "fee_mul") + 1) + ((k (ofString "u256_sub") + 1) + ((k (ofString "fee_mul") + 1) + ((k (ofString "create_ether") + 1) + ((k (ofString "create_ether") + 1) + ((Nat.max 0 0) + ((k (ofString "max") + 1) + (0 + (0 + (0 + (0 + (0 + ((Nat.max (k (ofString "lst_new") + 1) 0) + ((Nat.max 0 0) + ((k (ofString "encode_receipt") + 1) + (0 + (0 + (0 + ((w * (((k (ofString "lst_push") + 1) + (0 + 0)) + 1)) + ((Nat.max 0 0) + ((k (ofString "lst_new") + 1) + (0 + (0 + ((w * ((0 + 0) + 1)) + ((k (ofString "lst_push") + 1) + (0 + 0))))))))))))))))))))))))))))) =
      (k (ofString "udiv_small5") + 1) + (k (ofString "min") + 1) + (k (ofString "max") + 1) + (k (ofString "fee_mul") + 1) + (k (ofString "u256_sub") + 1) + (k (ofString "fee_mul") + 1) + (k (ofString "create_ether") + 1) + (k (ofString "create_ether") + 1) + (k (ofString "max") + 1) + Nat.max ((k (ofString "lst_new") + 1)) (0) + (k (ofString "encode_receipt") + 1) + w * ((k (ofString "lst_push") + 1) + 1) + (k (ofString "lst_new") + 1) + w * (0 + 1) + (k (ofString "lst_push") + 1) := by
  simp only [Nat.add_zero, Nat.zero_add, Nat.max_self, Nat.add_assoc]

theorem cost_phase4 : cost (phase4 .skip) = ptxCost4 := by
  unfold phase4 ptxPhase4 ptxCode
  exact cost_phase4_algebra ptxCharge (2 ^ 64 + 1)

private theorem cost_phase5_algebra (k : MlS → Nat) (w : Nat) :
    ((Nat.max (0 + (w * (((k (ofString "htab_item") + 1) + ((Nat.max (k (ofString "clear_account_preserving_balance") + 1) 0) + 0)) + 1))) 0) + ((k (ofString "incorporate_tx_into_block") + 1) + ((Nat.max ((k (ofString "scratch_release") + 1) + (k (ofString "frame_mem_release") + 1)) 0) + 0))) =
      Nat.max (w * ((k (ofString "htab_item") + 1) + Nat.max ((k (ofString "clear_account_preserving_balance") + 1)) (0) + 1)) (0) + (k (ofString "incorporate_tx_into_block") + 1) + Nat.max ((k (ofString "scratch_release") + 1) + (k (ofString "frame_mem_release") + 1)) (0) := by
  simp only [Nat.add_zero, Nat.zero_add, Nat.add_assoc]

theorem cost_phase5 : cost (phase5) = ptxCost5 := by
  unfold phase5 ptxPhase5 ptxCode
  exact cost_phase5_algebra ptxCharge (2 ^ 64 + 1)


end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.SpineChecks
