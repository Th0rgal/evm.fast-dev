import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256Compare
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256SubSemantics
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256CarryRank

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def arithU256Shape : ShapeHOL := .comb [.one, .one, .one, .one]

private theorem arith_shape_one {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem arith_shape_u256 {v : ValueHOL 64}
    (h : shapeEqHOL arithU256Shape (shapeOfHOLExact v) = true) :
    ∃ a : Limbs256, v = a.toValue := by
  cases v with
  | val wl => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fields =>
    cases fields with
    | nil => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    | cons v0 tail =>
      cases tail with
      | nil => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
      | cons v1 tail =>
        cases tail with
        | nil => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
        | cons v2 tail =>
          cases tail with
          | nil => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
          | cons v3 tail =>
            cases tail with
            | cons _ _ => simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
            | nil =>
              simp only [arithU256Shape, shapeOfHOLExact, List.map_cons, List.map_nil,
                shapeEqHOL, shapeEqHOL.shapeEqListHOL, Bool.and_eq_true, and_true] at h
              obtain ⟨w0, rfl⟩ := arith_shape_one h.1
              obtain ⟨w1, rfl⟩ := arith_shape_one h.2.1
              obtain ⟨w2, rfl⟩ := arith_shape_one h.2.2.1
              obtain ⟨w3, rfl⟩ := arith_shape_one h.2.2.2
              exact ⟨⟨w0, w1, w2, w3⟩, rfl⟩

private theorem pan_two_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
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
    by_cases two : key = second
    · subst two
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem two_arg_lookup_inv {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] = some (foundBody, callee, foundRs)) :
    foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      foundRs = rs := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  rw [pan_two_arg_lookup code name first second ps1 ps2 rs body v1 v2 different hshapes.1 hshapes.2 lookup] at hfound
  cases hfound
  exact ⟨rfl, rfl, rfl⟩

theorem arith_two_arg_lookup_inv_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (different : first ≠ second)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] = some (foundBody, callee, foundRs)) :
    shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧
      shapeEqHOL ps2 (shapeOfHOLExact v2) = true ∧
      foundBody = body ∧
      callee = (HolFiniteMapExact.empty.update (first, v1)).update (second, v2) ∧
      foundRs = rs := by
  have hshapes : shapeEqHOL ps1 (shapeOfHOLExact v1) = true ∧ shapeEqHOL ps2 (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup, different] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  exact ⟨hshapes.1, hshapes.2,
    two_arg_lookup_inv code name first second ps1 ps2 rs body v1 v2 different lookup hfound⟩

theorem arith_seq_none {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.seq a b) = (none, post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧
      evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  cases ha : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [ha] at h
    cases r with
    | none => exact ⟨mid, rfl, h⟩
    | some _ => simp at h

theorem arith_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hrem hmeta
          dsimp only at hmeta hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at h; dsimp only at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp at h; done) | skip
          simp only [] at h
          split at h
          · rename_i hboth
            obtain ⟨he, hp⟩ := Prod.mk.inj h
            have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
              simp [Bool.and_eq_true] at hboth; exact hboth.1
            let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name w { bpost with locals := s.locals }
            let inner : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState resumed cont).2
            refine ⟨vals, body, callee, rs, w, bpost, resumed, inner, rfl, hlk, hclk, hrun, hsh, rfl, hmeta,
              Prod.ext he rfl, by rw [← hp]⟩
          · simp at h

theorem arith_call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dest fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fn args) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) rs = true ∧
      post.locals = s.locals.update (dest, w) ∧
      post.code = s.code := by
  rw [evaluateHOLFiniteState_call] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hmeta
          dsimp only at hmeta
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp [emptyLocalsHOLFinite] at h; done) | skip
          dsimp only at h
          split at h
          · rename_i hrs
            split at h
            · simp [setKvarHOLFinite, setVarHOLFinite] at h
              refine ⟨vals, body, callee, rs, w, bpost, rfl, hlk, hclk, hrun, hrs, ?_, ?_⟩
              · rw [← h]
              · rw [← h]; exact hmeta
            · simp at h
          · simp at h

theorem arith_lookup_u256_add_carry :
    originalRuntimeCode.lookup (ofString "u256_add_carry") =
      some ([(ofString "a", arithU256Shape), (ofString "b", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_u256_add_carry, .comb [.one, .one, .one, .one, .one]) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 55 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_add_carry) rfl

theorem arith_lookup_u256_lt :
    originalRuntimeCode.lookup (ofString "u256_lt") =
      some ([(ofString "a", arithU256Shape), (ofString "b", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_u256_lt, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 46 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_lt) rfl

theorem arith_lookup_u256_sub :
    originalRuntimeCode.lookup (ofString "u256_sub") =
      some ([(ofString "a", arithU256Shape), (ofString "b", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_u256_sub, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 57 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_sub) rfl
end InitECandidate.Solver.Wave8GuestInv.Arith
