import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Eval

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptScratch_lookup : originalRuntimeCode.lookup (ofString "scratch_alloc") =
    some ((sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

theorem mptScratch_return (h : MptDeleteCallees)
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (hc : s.code = originalRuntimeCode) (hs : ArenaReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 40] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "scratch_alloc") values = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ArenaReady post ∧ AllocatorGrows s post ∧
      FreshScratch s post w.toNat 40 ∧ globN post "scratch_ptr" = w.toNat ∧
      post.be = s.be ∧
      FrameOutside s post
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  obtain ⟨arg, rfl, harg⟩ := mptOneArg_eval ha
  have heq := evalAt_const s 40 arg harg
  subst arg
  have hn := mptOneParam_lookup s.code (ofString "scratch_alloc") (ofString "n") .one .one
    (sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2.2.1 (.val (.word 40))
    (by rw [hc]; exact mptScratch_lookup) hl
  have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).2 hs
  have hn40 : locN (callEntryStateHOLFinite s callee) "n" = 40 := by
    simp only [locN, callEntryStateHOLFinite, hn]
    rfl
  have hrn := FunSpec.at_lookup h.rt_scratch_alloc s hc _ _ _ _ hl hae (by rw [hr]; simp)
  rw [hr] at hrn
  obtain ⟨w, rfl, hat, hg, hfresh, hsp⟩ := hrn _ rfl
  rw [hn40] at hfresh
  have hw := FunSpec.at_lookup h.ww_scratch_alloc s hc _ _ _ _ hl hae (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨_, _, _, hframe, _⟩ := hw (Or.inl ⟨.val (.word w), rfl⟩)
  have hm := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  rw [hr] at hm
  exact ⟨w, rfl, hat, hg, hfresh, hsp, hm.2.2.1, hframe⟩

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
