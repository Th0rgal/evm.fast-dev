import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Base

/-! Loop-free leaves in shard s06 (`wave8/leaves-s06`): 18 of 24 leaves in `s06.txt`.

Each theorem proves the exact spec statement `TerminatingFunBoundedOn GuestInv (ofString "f") K.«f»`,
taking as explicit hypotheses the spec statements of any cross-shard callee leaves it requires.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8GuestInv.S06

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

attribute [local irreducible] TerminatingProgBoundedOn

variable {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [GuestInvLike GuestInv]

/-- 1. `incorporate_child_on_error` (idx 591): loop-free, no external callees. -/
theorem fb_incorporate_child_on_error :
    TerminatingFunBoundedOn GuestInv
      (ofString "incorporate_child_on_error") K.«incorporate_child_on_error» := by
  apply onFun_le 591 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_incorporate_child_on_error _ rfl
  · htab_unfold Guest.Software.guestFn_incorporate_child_on_error
    htab_walk
  · htab_bound K.«incorporate_child_on_error»

/-- 3. `pc_add` (idx 468): loop-free, no external callees. -/
theorem fb_pc_add :
    TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» := by
  apply onFun_le 468 (by rw [guestAst_len]; decide) Guest.Software.guestFn_pc_add _ rfl
  · htab_unfold Guest.Software.guestFn_pc_add
    htab_walk
  · htab_bound K.«pc_add»

/-- 4. `set_retdata` (idx 595): loop-free, calls `alloc` (local helper `on_alloc`) and `memcpy`. -/
theorem fb_set_retdata_of
    (hmemcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata» := by
  have halloc := on_alloc (GuestInv := GuestInv)
  apply onFun_le 595 (by rw [guestAst_len]; decide) Guest.Software.guestFn_set_retdata _ rfl
  · htab_unfold Guest.Software.guestFn_set_retdata
    htab_walk
  · htab_bound K.«set_retdata»

/-- 5. `stack_push` (idx 454): loop-free, calls `scratch_alloc` (`on_scratch_alloc`) and `memcpy`. -/
theorem fb_stack_push_of
    (hmemcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» := by
  have hscr := on_scratch_alloc (GuestInv := GuestInv)
  apply onFun_le 454 (by rw [guestAst_len]; decide) Guest.Software.guestFn_stack_push _ rfl
  · htab_unfold Guest.Software.guestFn_stack_push
    htab_walk
  · htab_bound K.«stack_push»

/-- 8. `stack_pop` (idx 453): loop-free, no external callees. -/
theorem fb_stack_pop :
    TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» := by
  apply onFun_le 453 (by rw [guestAst_len]; decide) Guest.Software.guestFn_stack_pop _ rfl
  · htab_unfold Guest.Software.guestFn_stack_pop
    htab_walk
  · htab_bound K.«stack_pop»

/-- 9. `op_add` (idx 475): loop-free, calls `charge_gas`, `stack_pop`, `u256_add`, `stack_push`, `pc_add`. -/
theorem fb_op_add_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hadd : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add» := by
  apply onFun_le 475 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_add _ rfl
  · htab_unfold Guest.Software.guestFn_op_add
    htab_walk
  · htab_bound K.«op_add»

/-- 10. `op_addmod` (idx 482): loop-free, calls `charge_gas`, `stack_pop`, `u256_addmod`, `stack_push`, `pc_add`. -/
theorem fb_op_addmod_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (haddmod : TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.«u256_addmod»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod» := by
  apply onFun_le 482 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_addmod _ rfl
  · htab_unfold Guest.Software.guestFn_op_addmod
    htab_walk
  · htab_bound K.«op_addmod»

/-- 11. `op_address` (idx 531): loop-free, calls `charge_gas`, `address_to_u256`, `stack_push`, `pc_add`. -/
theorem fb_op_address_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (haddr : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address» := by
  apply onFun_le 531 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_address _ rfl
  · htab_unfold Guest.Software.guestFn_op_address
    htab_walk
  · htab_bound K.«op_address»

/-- 12. `op_and` (idx 492): loop-free, calls `charge_gas`, `stack_pop`, `stack_push`, `pc_add`. -/
theorem fb_op_and_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and» := by
  apply onFun_le 492 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_and _ rfl
  · htab_unfold Guest.Software.guestFn_op_and
    htab_walk
  · htab_bound K.«op_and»

/-- 13. `to_address_masked` (idx 444): loop-free, calls `st_be32`, `st_be64`. -/
theorem fb_to_address_masked :
    TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked» := by
  have h32 := on_st_be32 (GuestInv := GuestInv)
  have h64 := on_st_be64 (GuestInv := GuestInv)
  apply onFun_le 444 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_to_address_masked _ rfl
  · htab_unfold Guest.Software.guestFn_to_address_masked
    htab_walk
  · htab_bound K.«to_address_masked»

/-- 14. `warm_after_charge` (idx 474): loop-free, calls `warm_address`. -/
theorem fb_warm_after_charge_of
    (hwarm : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address») :
    TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge» := by
  apply onFun_le 474 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_warm_after_charge _ rfl
  · htab_unfold Guest.Software.guestFn_warm_after_charge
    htab_walk
  · htab_bound K.«warm_after_charge»

/-- 15. `op_balance` (idx 532): loop-free, calls `stack_pop`, `to_address_masked`, `access_gas_cost`, `charge_gas`, `warm_after_charge`, `get_account`, `stack_push`, `pc_add`. -/
theorem fb_op_balance_of
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hmask : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (hcost : TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost»)
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hwarm : TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge»)
    (hacct : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance» := by
  apply onFun_le 532 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_balance _ rfl
  · htab_unfold Guest.Software.guestFn_op_balance
    htab_walk
  · htab_bound K.«op_balance»

/-- 16. `block_env` (idx 550): loop-free, no external callees. -/
theorem fb_block_env :
    TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» := by
  apply onFun_le 550 (by rw [guestAst_len]; decide) Guest.Software.guestFn_block_env _ rfl
  · htab_unfold Guest.Software.guestFn_block_env
    htab_walk
  · htab_bound K.«block_env»

/-- 17. `op_basefee` (idx 551): loop-free, calls `charge_gas`, `block_env`, `stack_push`, `pc_add`. -/
theorem fb_op_basefee_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hblk : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee» := by
  apply onFun_le 551 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_basefee _ rfl
  · htab_unfold Guest.Software.guestFn_op_basefee
    htab_walk
  · htab_bound K.«op_basefee»

/-- 21. `op_blobhash` (idx 552): loop-free, calls `charge_gas`, `stack_pop`, `sat_word`, `u256_from_be`, `stack_push`, `pc_add`. -/
theorem fb_op_blobhash_of
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hsat : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (hbe : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash» := by
  apply onFun_le 552 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blobhash _ rfl
  · htab_unfold Guest.Software.guestFn_op_blobhash
    htab_walk
  · htab_bound K.«op_blobhash»

/-- 22. `track_ancestor_access` (idx 402): loop-free, no external callees. -/
theorem fb_track_ancestor_access :
    TerminatingFunBoundedOn GuestInv
      (ofString "track_ancestor_access") K.«track_ancestor_access» := by
  apply onFun_le 402 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_track_ancestor_access _ rfl
  · htab_unfold Guest.Software.guestFn_track_ancestor_access
    htab_walk
  · htab_bound K.«track_ancestor_access»

/-- 23. `op_blockhash` (idx 554): loop-free, calls `stack_pop`, `charge_gas`, `block_env`, `sat_word`, `u256_from_be`, `track_ancestor_access`, `stack_push`, `pc_add`. -/
theorem fb_op_blockhash_of
    (hpop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (hgas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (hblk : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (hsat : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (hbe : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be»)
    (htrk : TerminatingFunBoundedOn GuestInv
      (ofString "track_ancestor_access") K.«track_ancestor_access»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (hpc : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash» := by
  apply onFun_le 554 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blockhash _ rfl
  · htab_unfold Guest.Software.guestFn_op_blockhash
    htab_walk
  · htab_bound K.«op_blockhash»

/-- 24. `stack_push_word` (idx 455): loop-free, calls `stack_push`. -/
theorem fb_stack_push_word_of
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») :
    TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word» := by
  apply onFun_le 455 (by rw [guestAst_len]; decide) Guest.Software.guestFn_stack_push_word _ rfl
  · htab_unfold Guest.Software.guestFn_stack_push_word
    htab_walk
  · htab_bound K.«stack_push_word»

end InitECandidate.Solver.Wave8GuestInv.S06
