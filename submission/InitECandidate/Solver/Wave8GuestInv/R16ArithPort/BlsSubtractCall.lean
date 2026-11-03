import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCallFacts
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCompare
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCarrySemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL subCarry384

theorem bls_lt_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp left right : MlS) (a b : Limbs384) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hr : evaluateHOLFiniteState s
      (.decCall temp .one (ofString "bls_fp_lt_raw") [.var .local left, .var .local right] cont) = (none, post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      resumed.locals = s.locals.update (temp, .val (.word (if a.toNat < b.toNat then 1 else 0))) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hvalues : values = [a.toValue, b.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right] = some [a.toValue, b.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "bls_fp_lt_raw") (ofString "a") (ofString "b")
    blsU384Shape blsU384Shape .one
    (arithSourceBody Guest.Software.guestFn_bls_fp_lt_raw) a.toValue b.toValue
    (by decide) arith_lookup_bls_fp_lt_raw hlk
  have hret := eval_bls_fp_lt_raw_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [hret] at hrun
  have hv : value = .val (.word (if a.toNat < b.toNat then 1 else 0)) := by
    simpa [lt384_correct] using (Prod.mk.inj hrun).1.symm
  refine ⟨resumed, inner, ?_, hcode, hcont, hpost⟩
  simpa [hv] using hlocals

theorem bls_sub_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp left right : MlS) (a b : Limbs384) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hr : evaluateHOLFiniteState s
      (.decCall temp blsCarryShape (ofString "bls_fp_sub_raw") [.var .local left, .var .local right] cont) = (none, post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      resumed.locals = s.locals.update (temp, carry384Value (subCarry384 a b)) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hvalues : values = [a.toValue, b.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right] = some [a.toValue, b.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "bls_fp_sub_raw") (ofString "a") (ofString "b")
    blsU384Shape blsU384Shape blsCarryShape
    (arithSourceBody Guest.Software.guestFn_bls_fp_sub_raw) a.toValue b.toValue
    (by decide) arith_lookup_bls_fp_sub_raw hlk
  obtain ⟨ret, hret, _⟩ := eval_bls_fp_sub_raw_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [hret] at hrun
  have hv : value = carry384Value (subCarry384 a b) := by
    simpa using (Prod.mk.inj hrun).1.symm
  refine ⟨resumed, inner, ?_, hcode, hcont, hpost⟩
  simpa [hv] using hlocals

def blsTakeSixExpr (temp : MlS) : ExpHOL 64 :=
  .rstruct [.rfield 0 (.var .local temp), .rfield 1 (.var .local temp), .rfield 2 (.var .local temp), .rfield 3 (.var .local temp), .rfield 4 (.var .local temp), .rfield 5 (.var .local temp)]

theorem blsTakeSix_assign {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest temp : MlS) (old r : Limbs384) (c : BitVec 64)
    (hd : s.locals.lookup dest = some old.toValue)
    (ht : s.locals.lookup temp = some (carry384Value (r, c))) :
    evaluateHOLFiniteState s (.assign .local dest (blsTakeSixExpr temp)) =
      (none, setVarHOLFinite dest r.toValue s) := by
  simp [blsTakeSixExpr, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
    ht, carry384Value, Limbs384.toValue, lookupKvarHOLExact, hd,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]

def blsSubUpdate (temp counter other coefficient otherCoeff : MlS) : ProgHOL 64 :=
  .decCall temp blsCarryShape (ofString "bls_fp_sub_raw")
    [.var .local counter, .var .local other]
    (.seq (.assign .local counter (blsTakeSixExpr temp))
      (.call (some (some (.local, coefficient), none)) (ofString "bls_fp_sub")
        [.var .local coefficient, .var .local otherCoeff]))

theorem blsSubUpdate_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp counter other coefficient otherCoeff : MlS) (a b : Limbs384)
    (htc : temp ≠ counter) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hb : s.locals.lookup other = some b.toValue)
    (hr : evaluateHOLFiniteState s (blsSubUpdate temp counter other coefficient otherCoeff) = (none, post)) :
    ∃ x : Limbs384, post.locals = HolFiniteMapExact.resVarEq
      (((s.locals.update (temp, carry384Value (subCarry384 a b))).update
        (counter, (subCarry384 a b).1.toValue)).update (coefficient, x.toValue))
      (temp, s.locals.lookup temp) := by
  unfold blsSubUpdate at hr
  obtain ⟨resumed, inner, hlocals, hcode, hcont, hpost⟩ :=
    bls_sub_decCall_none temp counter other a b _ hc ha hb hr
  obtain ⟨mid, hassign, hcall⟩ := arith_seq_none hcont
  have hcounter : resumed.locals.lookup counter = some a.toValue := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE, htc] using ha
  have htemp : resumed.locals.lookup temp = some (carry384Value (subCarry384 a b)) := by
    rw [hlocals]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have he := blsTakeSix_assign resumed counter temp a (subCarry384 a b).1 (subCarry384 a b).2 hcounter htemp
  rw [he] at hassign
  have hmid := (Prod.mk.inj hassign).2
  subst mid
  have hmc : (setVarHOLFinite counter (subCarry384 a b).1.toValue resumed).code = originalRuntimeCode := hcode.trans hc
  obtain ⟨x, hx⟩ := bls_call_local_u384_none coefficient (ofString "bls_fp_sub")
    [.var .local coefficient, .var .local otherCoeff] _ _ hmc arith_lookup_bls_fp_sub hcall
  refine ⟨x, ?_⟩
  rw [hpost, hx]
  simp only [setVarHOLFinite, hlocals]
end InitECandidate.Solver.Wave8GuestInv.Arith
