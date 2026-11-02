import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Expressions
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Stages
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

theorem lookup_encode_transaction : originalRuntimeCode.lookup (ofString "encode_transaction") =
    some ((sourceFunctionEntry Guest.Software.guestFn_encode_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 329 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_transaction) rfl

theorem lookup_alloc : originalRuntimeCode.lookup (ofString "alloc") =
    some ((sourceFunctionEntry Guest.Software.guestFn_alloc).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_min : originalRuntimeCode.lookup (ofString "min") =
    some ((sourceFunctionEntry Guest.Software.guestFn_min).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

theorem lookup_recover_sender_with_chain_id : originalRuntimeCode.lookup (ofString "recover_sender_with_chain_id") =
    some ((sourceFunctionEntry Guest.Software.guestFn_recover_sender_with_chain_id).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 343 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_recover_sender_with_chain_id) rfl

theorem shape_one_word {v : ValueHOL 64} (h : shapeOfHOLExact v = .one) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact] at h
  · simp [shapeOfHOLExact] at h

theorem shape_pair_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] := by
  rw [shapeEqHOL_eq_true] at h
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · simp [shapeOfHOLExact] at h
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at h
    rcases fs with _ | ⟨v0, _ | ⟨v1, _ | vs⟩⟩
    · simp at h
    · simp at h
    · simp only [List.map, List.cons.injEq] at h
      obtain ⟨h0, h1, _⟩ := h
      obtain ⟨a, rfl⟩ := shape_one_word h0
      obtain ⟨b, rfl⟩ := shape_one_word h1
      exact ⟨a, b, rfl⟩
    · simp at h
  · simp [shapeOfHOLExact] at h

theorem params_one_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p : MlS) (sh : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh)], body, ret)) (e : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v, evalAt s e = some v ∧ callee.lookup p = some v := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases he : evalAt s e with _ | v
  · simp only [evalListHOLExact, he] at ha'; cases ha'
  · exact ⟨v, rfl, callee_param_one_exp s fname p sh body ret hi e v vs body' callee ret' he ha hl⟩

theorem params_two_values {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p q : MlS) (sh1 sh2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh1), (q, sh2)], body, ret)) (e1 e2 : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v1 v2, evalAt s e1 = some v1 ∧ evalAt s e2 = some v2 ∧
      callee.lookup p = some v1 ∧ callee.lookup q = some v2 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalListHOLExact, h1] at ha'; cases ha'
  rcases h2 : evalAt s e2 with _ | v2
  · simp only [evalListHOLExact, h1, h2] at ha'; cases ha'
  have hp := callee_param_two s fname p q sh1 sh2 body ret hi e1 e2 v1 v2 vs body' callee ret' h1 h2 ha hl
  exact ⟨v1,v2,rfl,rfl,hp.2⟩

theorem params_three_values {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p q r : MlS) (sh1 sh2 sh3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh1), (q, sh2), (r, sh3)], body, ret)) (e1 e2 e3 : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2,e3] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v1 v2 v3, evalAt s e1 = some v1 ∧ evalAt s e2 = some v2 ∧ evalAt s e3 = some v3 ∧
      callee.lookup p = some v1 ∧ callee.lookup q = some v2 ∧ callee.lookup r = some v3 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalListHOLExact, h1] at ha'; cases ha'
  rcases h2 : evalAt s e2 with _ | v2
  · simp only [evalListHOLExact, h1, h2] at ha'; cases ha'
  rcases h3 : evalAt s e3 with _ | v3
  · simp only [evalListHOLExact, h1, h2, h3] at ha'; cases ha'
  have hp := callee_param_three s fname p q r sh1 sh2 sh3 body ret hi e1 e2 e3 v1 v2 v3 vs body' callee ret' h1 h2 h3 ha hl
  exact ⟨v1,v2,v3,rfl,rfl,rfl,hp⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
