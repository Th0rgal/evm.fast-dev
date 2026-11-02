import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Counter
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Nodes

/-! Counted-loop leaves: `htab_keys` (`while i < n`, `memcpy` per key), `lst_upsert_idx`
(`while i < n`, then `lst_push`). `memcpy` is the bytes family's leaf, a hypothesis. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

attribute [local irreducible] TerminatingProgBoundedOn

/-- Prove `IncrBody c body` structurally. -/
macro "incr_body" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

/-- A counted `while` (signed `<`) whose body is walked by `htab_walk`. -/
macro "counted_while" : tactic => `(tactic|
  (apply while_counter_guestInv .less (Or.inl rfl)
   · htab_walk
   · incr_body
   · rfl))

theorem fb_htab_keys_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.«htab_keys» := by
  have ha := on_alloc
  apply onFun_le 144 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_keys _ rfl
  · htab_unfold Guest.Software.guestFn_htab_keys
    htab_walk
    counted_while
    all_goals htab_walk
  · unfold K.«htab_keys»
    omega

theorem fb_lst_upsert_idx_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx» := by
  have hp := fb_lst_push_of hc
  apply onFun_le 413 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_upsert_idx _ rfl
  · htab_unfold Guest.Software.guestFn_lst_upsert_idx
    htab_walk
    counted_while
    all_goals htab_walk
  · htab_bound K.«lst_upsert_idx»

end InitECandidate.Solver.Wave8GuestInv.Htab
