import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Invariant
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Expressions

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1

/-- The phase-two entry predicate places no shape restriction on `price`. -/
theorem validated_set_price {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxValidated s) (v : ValueHOL 64) :
    PtxValidated (setVarHOLFinite (ofString "price") v s) := by
  have hlookup : ∀ name : String, ofString name ≠ ofString "price" →
      (s.locals.update (ofString "price", v)).lookup (ofString name) =
        s.locals.lookup (ofString name) := by
    intro name hn
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  have ht := txReadyStrong_with_locals s (s.locals.update (ofString "price", v))
    s.clock (hlookup "tx" (by decide)) (hlookup "index" (by decide)) h.1
  have hs := locN_congr s (s.locals.update (ofString "price", v)) s.clock
    "sender" (hlookup "sender" (by decide))
  have hm := locN_congr s (s.locals.update (ofString "price", v)) s.clock
    "mgas" (hlookup "mgas" (by decide))
  change PtxValidated { s with locals := s.locals.update (ofString "price", v) }
  refine ⟨ht, ?_, ?_, ?_⟩
  · change Inside (locN { s with locals := s.locals.update (ofString "price", v), clock := s.clock }
      "sender", 24) sourceBase (globN s "heap_ptr")
    rw [hs]
    exact h.2.1
  · change WordsOK s (locN { s with locals := s.locals.update (ofString "price", v), clock := s.clock }
      "sender", 24)
    rw [hs]
    exact h.2.2.1
  · rw [hm]
    exact h.2.2.2

/-- A permitted `price` value can flatten to more words than the whole `te` allocation. -/
theorem validated_large_price {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxValidated s) :
    let v : ValueHOL 64 := .rStruct (List.replicate 26 (.val (.word 0)))
    PtxValidated (setVarHOLFinite (ofString "price") v s) ∧
      (flattenHOL v).length = 26 := by
  refine ⟨validated_set_price s h _, ?_⟩
  simp [flattenHOL, List.replicate_succ]

/-- `locN` maps structures to zero, so its numeric bound does not constrain
the first word written by the later `store (m + 40) mgas`. -/
theorem validated_struct_mgas {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxValidated s) (w : BitVec 64) :
    let v : ValueHOL 64 := .rStruct [.val (.word w)]
    PtxValidated (setVarHOLFinite (ofString "mgas") v s) ∧
      flattenHOL v = [.word w] := by
  have hlookup : ∀ name : String, ofString name ≠ ofString "mgas" →
      (s.locals.update (ofString "mgas", .rStruct [.val (.word w)])).lookup (ofString name) =
        s.locals.lookup (ofString name) := by
    intro name hn
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  have ht := txReadyStrong_with_locals s
    (s.locals.update (ofString "mgas", .rStruct [.val (.word w)])) s.clock
    (hlookup "tx" (by decide)) (hlookup "index" (by decide)) h.1
  have hs := locN_congr s (s.locals.update (ofString "mgas", .rStruct [.val (.word w)]))
    s.clock "sender" (hlookup "sender" (by decide))
  refine ⟨⟨ht, ?_, ?_, ?_⟩, by simp [flattenHOL]⟩
  · change Inside (locN { s with locals := s.locals.update (ofString "mgas", .rStruct [.val (.word w)]), clock := s.clock }
      "sender", 24) sourceBase (globN s "heap_ptr")
    rw [hs]
    exact h.2.1
  · change WordsOK s (locN { s with locals := s.locals.update (ofString "mgas", .rStruct [.val (.word w)]), clock := s.clock } "sender", 24)
    rw [hs]
    exact h.2.2.1
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The actual local expression used by the message gas store evaluates to
the structured value, even when the entry predicate's numeric view is zero. -/
theorem validated_mgas_store_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxValidated s) :
    let v : ValueHOL 64 := .rStruct [.val (.word (BitVec.ofNat 64 (2 ^ 63)))]
    let t := setVarHOLFinite (ofString "mgas") v s
    PtxValidated t ∧ locN t "mgas" = 0 ∧
      InitECandidate.Solver.Wave8GuestInv.evalAt t
        (.var .local (ofString "mgas")) = some v ∧
      flattenHOL v = [.word (BitVec.ofNat 64 (2 ^ 63))] := by
  refine ⟨(validated_struct_mgas s h _).1, ?_, ?_, (validated_struct_mgas s h _).2⟩
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [InitECandidate.Solver.Wave8GuestInv.evalAt, evalHOLExact,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The store primitive accepts a one-field structure exactly as a one-word
write. Successful storage does not provide a missing scalar-shape check. -/
theorem structured_word_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x w : BitVec 64) (mem' : BitVec 64 → HolWordLab 64)
    (hst : @panMemStoresHOL 64 _ x
      (flattenHOL (.rStruct [.val (.word w)])) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    memW { s with memory := mem' } x.toNat = w.toNat := by
  have hw := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w)
    (by simpa [flattenHOL] using hst)
  simp [memW, hw.2.1]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
