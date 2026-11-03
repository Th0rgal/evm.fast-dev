import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind3Memory
import InitECandidate.Solver.GuestTrapOutcomes

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded

def mptInvalidateBody : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
        (.return (.const 0))))

theorem mptInvalidate_lookup : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some ([(ofString "nd", .one)], mptInvalidateBody, .one) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

theorem mpt_store_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n off : BitVec 64) (hl : s.locals.lookup (ofString "nd") = some (.val (.word n)))
    (hd : s.memaddrs (n + off)) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
      (none, {s with memory := fun a => if a = n + off then .word 0 else s.memory a}) := by
  rw [evaluateHOLFiniteState_store]
  simp [evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
    flattenHOL, panMemStoresHOL, panMemStoreHOL, hd]

theorem mptInvalidate_body_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (hl : s.locals.lookup (ofString "nd") = some (.val (.word n)))
    (h8 : s.memaddrs (n + 8#64)) (h16 : s.memaddrs (n + 16#64)) (h24 : s.memaddrs (n + 24#64)) :
    evaluateHOLFiniteState s mptInvalidateBody =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite (clearCache s n.toNat)) := by
  let s1 : PanSemStateFiniteExact 64 F :=
    {s with memory := fun a => if a = n + 8#64 then .word 0 else s.memory a}
  let s2 : PanSemStateFiniteExact 64 F :=
    {s1 with memory := fun a => if a = n + 16#64 then .word 0 else s1.memory a}
  let s3 : PanSemStateFiniteExact 64 F :=
    {s2 with memory := fun a => if a = n + 24#64 then .word 0 else s2.memory a}
  have h1 := mpt_store_zero s n 8 hl h8
  have h2 := mpt_store_zero s1 n 16 hl h16
  have h3 := mpt_store_zero s2 n 24 hl h24
  rw [mptInvalidateBody, evaluateHOLFiniteState_seq_line780, h1]
  change evaluateHOLFiniteState s1 _ = _
  rw [evaluateHOLFiniteState_seq_line780, h2]
  change evaluateHOLFiniteState s2 _ = _
  rw [evaluateHOLFiniteState_seq_line780, h3]
  change evaluateHOLFiniteState s3 (.return (.const 0)) = _
  have hs : s3 = clearCache s n.toNat := by
    have he (k : Nat) : BitVec.ofNat 64 (n.toNat + k) = n + BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    dsimp only [s3, s2, s1, clearCache]
    congr 1
    funext a
    rw [he 8, he 16, he 24]
    by_cases h8 : a = n + 8#64 <;> by_cases h16 : a = n + 16#64 <;>
      by_cases h24 : a = n + 24#64 <;> simp [h8, h16, h24]
  rw [hs, evaluateHOLFiniteState_return]
  simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

/-- The actual invalidation call has exactly the advertised cache effect. -/
theorem mptInvalidate_call_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (h8 : s.memaddrs (n + 8#64)) (h16 : s.memaddrs (n + 16#64)) (h24 : s.memaddrs (n + 24#64)) :
    evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")]) =
      if s.clock = 0 then (some .timeOut, emptyLocalsHOLFinite s)
      else (none, {clearCache s n.toNat with clock := s.clock - 1}) := by
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "node")] =
      some [.val (.word n)] := by
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hl]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "node_invalidate") (ofString "nd")
    mptInvalidateBody n (by rw [hc]; exact mptInvalidate_lookup)
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hlook]
  dsimp only
  split
  · rfl
  · rw [mptInvalidate_body_eval (callEntryStateHOLFinite s
        (HolFiniteMapExact.empty.update (ofString "nd", .val (.word n)))) n (by simp [callEntryStateHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]) h8 h16 h24]
    simp only [shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
    rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
