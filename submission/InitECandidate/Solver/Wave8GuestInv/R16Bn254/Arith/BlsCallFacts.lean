import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.BlsArithmetic
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseCallFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def blsU384Shape : ShapeHOL := .comb [.one, .one, .one, .one, .one, .one]
def blsCarryShape : ShapeHOL := .comb [.one, .one, .one, .one, .one, .one, .one]

private theorem bls_shape_one {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem bls_shape_u384 {v : ValueHOL 64}
    (h : shapeEqHOL blsU384Shape (shapeOfHOLExact v) = true) :
    ∃ a : Limbs384, v = a.toValue := by
  cases v with
  | val wl => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fields =>
    cases fields with
    | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    | cons v0 tail0 =>
        cases tail0 with
        | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
        | cons v1 tail1 =>
            cases tail1 with
            | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
            | cons v2 tail2 =>
                cases tail2 with
                | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
                | cons v3 tail3 =>
                    cases tail3 with
                    | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
                    | cons v4 tail4 =>
                        cases tail4 with
                        | nil => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
                        | cons v5 tail5 =>
                            cases tail5 with
                            | cons _ _ => simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
                            | nil =>
                              simp only [blsU384Shape, shapeOfHOLExact, List.map_cons, List.map_nil,
                                shapeEqHOL, shapeEqHOL.shapeEqListHOL, Bool.and_eq_true, and_true] at h
                              obtain ⟨w0, rfl⟩ := bls_shape_one h.1
                              obtain ⟨w1, rfl⟩ := bls_shape_one h.2.1
                              obtain ⟨w2, rfl⟩ := bls_shape_one h.2.2.1
                              obtain ⟨w3, rfl⟩ := bls_shape_one h.2.2.2.1
                              obtain ⟨w4, rfl⟩ := bls_shape_one h.2.2.2.2.1
                              obtain ⟨w5, rfl⟩ := bls_shape_one h.2.2.2.2.2
                              exact ⟨⟨w0, w1, w2, w3, w4, w5⟩, rfl⟩

theorem arith_one_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name param : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (value : ValueHOL width)
    (hshape : shapeEqHOL ps (shapeOfHOLExact value) = true)
    (lookup : code name = some ([(param, ps)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [value] =
      some (body, HolFiniteMapExact.empty.update (param, value), rs) := by
  have raw : lookupCodeHOLExact code name [value] =
      some (body, (fun key => if key = param then some value else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases he : key = param
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · simp [he, Ne.symm he, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

theorem bls_call_local_u384_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hi : originalRuntimeCode.lookup fname = some (params, body, blsU384Shape))
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fname args) = (none, post)) :
    ∃ r : Limbs384, post.locals = s.locals.update (dest, r.toValue) := by
  obtain ⟨values, found, callee, rs, value, bpost, _, hlk, _, _, hshape, hlocals, _⟩ := arith_call_local_none hr
  have hrs := arith_lookup_return_shape s.code.lookup fname params body blsU384Shape
    (by rw [hc]; exact hi) values found callee rs hlk
  subst rs
  have hreverse : shapeEqHOL blsU384Shape (shapeOfHOLExact value) = true :=
    (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp hshape).symm
  obtain ⟨r, rfl⟩ := bls_shape_u384 hreverse
  exact ⟨r, hlocals⟩

theorem arith_lookup_bls_fp_shr1 :
    originalRuntimeCode.lookup (ofString "bls_fp_shr1") =
      some ([(ofString "x", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_shr1, blsU384Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 710 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_shr1) rfl

theorem arith_lookup_bls_fp_half_can :
    originalRuntimeCode.lookup (ofString "bls_fp_half_can") =
      some ([(ofString "x", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_half_can, blsU384Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 711 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_half_can) rfl

theorem arith_lookup_bls_fp_lt_raw :
    originalRuntimeCode.lookup (ofString "bls_fp_lt_raw") =
      some ([(ofString "a", blsU384Shape), (ofString "b", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_lt_raw, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 699 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_lt_raw) rfl

theorem arith_lookup_bls_fp_add_raw :
    originalRuntimeCode.lookup (ofString "bls_fp_add_raw") =
      some ([(ofString "a", blsU384Shape), (ofString "b", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_add_raw, blsCarryShape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 700 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_add_raw) rfl

theorem arith_lookup_bls_fp_sub_raw :
    originalRuntimeCode.lookup (ofString "bls_fp_sub_raw") =
      some ([(ofString "a", blsU384Shape), (ofString "b", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_sub_raw, blsCarryShape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 701 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_sub_raw) rfl

theorem arith_lookup_bls_fp_sub :
    originalRuntimeCode.lookup (ofString "bls_fp_sub") =
      some ([(ofString "a", blsU384Shape), (ofString "b", blsU384Shape)], arithSourceBody Guest.Software.guestFn_bls_fp_sub, blsU384Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 703 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bls_fp_sub) rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
