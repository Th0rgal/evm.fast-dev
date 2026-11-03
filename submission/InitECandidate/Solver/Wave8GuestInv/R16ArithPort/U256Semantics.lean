import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256Arithmetic

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def arithSourceBody (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

attribute [local irreducible] wordAddCarryHOL

private theorem eval_dec_ret {F : Type}
    {name : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    {st : PanSemStateFiniteExact 64 F} {v retVal : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e = some v)
    (hsh : shapeEqHOL sh (shapeOfHOLExact v) = true)
    (hbody : ∀ st' : PanSemStateFiniteExact 64 F,
      st'.locals = st.locals.update (name, v) →
      ∃ post,
        evaluateHOLFiniteState st' body = (some (.returned retVal), post) ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite st') :
    ∃ post',
      evaluateHOLFiniteState st (.dec name sh e body) = (some (.returned retVal), post') ∧
      emptyLocalsHOLFinite post' = emptyLocalsHOLFinite st := by
  obtain ⟨post, hrun, hemp⟩ := hbody (setVarHOLFinite name v st) rfl
  refine ⟨{ post with locals := HolFiniteMapExact.resVarEq post.locals (name, st.locals.lookup name) }, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hev]
    dsimp only
    rw [if_pos hsh, hrun]
  · have hemp' : emptyLocalsHOLFinite { post with locals := HolFiniteMapExact.resVarEq post.locals (name, st.locals.lookup name) } =
        emptyLocalsHOLFinite post := rfl
    rw [hemp', hemp]
    rfl

private theorem eval_prim_seq_ret {F : Type}
    {name : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tail : ProgHOL 64}
    {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {v retVal : ValueHOL 64}
    (hargs : @evalListHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) args = some vals)
    (hpo : panPrimopHOLExact op vals = some v)
    (hval : st.isValidValueHOLFinite .local name v = true)
    (htail : ∀ st' : PanSemStateFiniteExact 64 F,
      st'.locals = st.locals.update (name, v) →
      ∃ post,
        evaluateHOLFiniteState st' tail = (some (.returned retVal), post) ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite st') :
    ∃ post',
      evaluateHOLFiniteState st (.seq (.primitive name op args) tail) = (some (.returned retVal), post') ∧
      emptyLocalsHOLFinite post' = emptyLocalsHOLFinite st := by
  obtain ⟨post, hrun, hemp⟩ := htail (setVarHOLFinite name v st) rfl
  refine ⟨post, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]
    dsimp only
    rw [hpo]
    dsimp only
    rw [if_pos hval]
    exact hrun
  · rw [hemp]; rfl

def carryPairValue (p : BitVec 64 × BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word p.1), .val (.word p.2)]

def addCarry256Value (a b : Limbs256) : ValueHOL 64 :=
  let r := addCarry256 a b
  .rStruct [.val (.word r.1.l0), .val (.word r.1.l1), .val (.word r.1.l2),
    .val (.word r.1.l3), .val (.word r.2)]

theorem eval_u256_add_carry_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a b : Limbs256)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue) :
    ∃ post,
      evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_u256_add_carry) =
        (some (.returned (addCarry256Value a b)), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite s := by
  have hbody : arithSourceBody Guest.Software.guestFn_u256_add_carry = .dec (ofString "r0") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)]) (.seq (.primitive (ofString "r0") .addCarry [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b")), .const (0#64)]) (.dec (ofString "r1") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)]) (.seq (.primitive (ofString "r1") .addCarry [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b")), .rfield 1 (.var .local (ofString "r0"))]) (.dec (ofString "r2") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)]) (.seq (.primitive (ofString "r2") .addCarry [.rfield 2 (.var .local (ofString "a")), .rfield 2 (.var .local (ofString "b")), .rfield 1 (.var .local (ofString "r1"))]) (.dec (ofString "r3") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)]) (.seq (.primitive (ofString "r3") .addCarry [.rfield 3 (.var .local (ofString "a")), .rfield 3 (.var .local (ofString "b")), .rfield 1 (.var .local (ofString "r2"))]) (.return (.rstruct [.rfield 0 (.var .local (ofString "r0")), .rfield 0 (.var .local (ofString "r1")), .rfield 0 (.var .local (ofString "r2")), .rfield 0 (.var .local (ofString "r3")), .rfield 1 (.var .local (ofString "r3"))]))))))))) := rfl
  rw [hbody]
  have hlk_eq {m : HolFiniteMapExact MlS (ValueHOL 64)} (k : MlS) (v : ValueHOL 64) :
      (m.update (k, v)).lookup k = some v := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {m : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : MlS} (v : ValueHOL 64) (hne : k1 ≠ k2) :
      (m.update (k1, v)).lookup k2 = m.lookup k2 := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  let t0 := wordAddCarryHOL a.l0 b.l0 0
  let t1 := wordAddCarryHOL a.l1 b.l1 t0.2
  let t2 := wordAddCarryHOL a.l2 b.l2 t1.2
  let t3 := wordAddCarryHOL a.l3 b.l3 t2.2
  refine eval_dec_ret (v := carryPairValue (0, 0))
    (by simp [evalHOLExact, evalListHOLExact, carryPairValue])
    (by simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact, carryPairValue]) ?_
  intro s1 hl1
  have hs1_a : s1.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl1, hlk_ne _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl1, hlk_ne _ (by decide)]; exact hb
  have hs1_r0 : s1.locals.lookup (ofString "r0") = some (carryPairValue (0, 0)) := by rw [hl1]; exact hlk_eq _ _
  refine eval_prim_seq_ret (vals := [.val (.word a.l0), .val (.word b.l0), .val (.word (0))]) (v := carryPairValue t0)
    (by simp [evalHOLExact, evalListHOLExact, Limbs256.toValue, carryPairValue, hs1_a, hs1_b, hs1_r0])
    (by rfl)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite,
      hs1_r0, carryPairValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]) ?_
  intro s2 hl2
  have hs2_a : s2.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_a
  have hs2_b : s2.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_b
  have hs2_r0 : s2.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl2]; exact hlk_eq _ _
  refine eval_dec_ret (v := carryPairValue (0, 0))
    (by simp [evalHOLExact, evalListHOLExact, carryPairValue])
    (by simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact, carryPairValue]) ?_
  intro s3 hl3
  have hs3_a : s3.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_a
  have hs3_b : s3.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_b
  have hs3_r0 : s3.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_r0
  have hs3_r1 : s3.locals.lookup (ofString "r1") = some (carryPairValue (0, 0)) := by rw [hl3]; exact hlk_eq _ _
  refine eval_prim_seq_ret (vals := [.val (.word a.l1), .val (.word b.l1), .val (.word (t0.2))]) (v := carryPairValue t1)
    (by simp [evalHOLExact, evalListHOLExact, Limbs256.toValue, carryPairValue, hs3_a, hs3_b, hs3_r0, hs3_r1])
    (by rfl)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite,
      hs3_r1, carryPairValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]) ?_
  intro s4 hl4
  have hs4_a : s4.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_a
  have hs4_b : s4.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_b
  have hs4_r0 : s4.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_r0
  have hs4_r1 : s4.locals.lookup (ofString "r1") = some (carryPairValue t1) := by rw [hl4]; exact hlk_eq _ _
  refine eval_dec_ret (v := carryPairValue (0, 0))
    (by simp [evalHOLExact, evalListHOLExact, carryPairValue])
    (by simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact, carryPairValue]) ?_
  intro s5 hl5
  have hs5_a : s5.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_a
  have hs5_b : s5.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_b
  have hs5_r0 : s5.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_r0
  have hs5_r1 : s5.locals.lookup (ofString "r1") = some (carryPairValue t1) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_r1
  have hs5_r2 : s5.locals.lookup (ofString "r2") = some (carryPairValue (0, 0)) := by rw [hl5]; exact hlk_eq _ _
  refine eval_prim_seq_ret (vals := [.val (.word a.l2), .val (.word b.l2), .val (.word (t1.2))]) (v := carryPairValue t2)
    (by simp [evalHOLExact, evalListHOLExact, Limbs256.toValue, carryPairValue, hs5_a, hs5_b, hs5_r0, hs5_r1, hs5_r2])
    (by rfl)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite,
      hs5_r2, carryPairValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]) ?_
  intro s6 hl6
  have hs6_a : s6.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_a
  have hs6_b : s6.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_b
  have hs6_r0 : s6.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_r0
  have hs6_r1 : s6.locals.lookup (ofString "r1") = some (carryPairValue t1) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_r1
  have hs6_r2 : s6.locals.lookup (ofString "r2") = some (carryPairValue t2) := by rw [hl6]; exact hlk_eq _ _
  refine eval_dec_ret (v := carryPairValue (0, 0))
    (by simp [evalHOLExact, evalListHOLExact, carryPairValue])
    (by simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact, carryPairValue]) ?_
  intro s7 hl7
  have hs7_a : s7.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_a
  have hs7_b : s7.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_b
  have hs7_r0 : s7.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_r0
  have hs7_r1 : s7.locals.lookup (ofString "r1") = some (carryPairValue t1) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_r1
  have hs7_r2 : s7.locals.lookup (ofString "r2") = some (carryPairValue t2) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_r2
  have hs7_r3 : s7.locals.lookup (ofString "r3") = some (carryPairValue (0, 0)) := by rw [hl7]; exact hlk_eq _ _
  refine eval_prim_seq_ret (vals := [.val (.word a.l3), .val (.word b.l3), .val (.word (t2.2))]) (v := carryPairValue t3)
    (by simp [evalHOLExact, evalListHOLExact, Limbs256.toValue, carryPairValue, hs7_a, hs7_b, hs7_r0, hs7_r1, hs7_r2, hs7_r3])
    (by rfl)
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite,
      hs7_r3, carryPairValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]) ?_
  intro s8 hl8
  have hs8_a : s8.locals.lookup (ofString "a") = some (a.toValue) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_a
  have hs8_b : s8.locals.lookup (ofString "b") = some (b.toValue) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_b
  have hs8_r0 : s8.locals.lookup (ofString "r0") = some (carryPairValue t0) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_r0
  have hs8_r1 : s8.locals.lookup (ofString "r1") = some (carryPairValue t1) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_r1
  have hs8_r2 : s8.locals.lookup (ofString "r2") = some (carryPairValue t2) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_r2
  have hs8_r3 : s8.locals.lookup (ofString "r3") = some (carryPairValue t3) := by rw [hl8]; exact hlk_eq _ _
  refine ⟨emptyLocalsHOLFinite s8, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_return]
    simp [evalHOLExact, evalListHOLExact, hs8_a, hs8_b, hs8_r0, hs8_r1, hs8_r2, hs8_r3, carryPairValue,
      addCarry256Value, addCarry256, t0, t1, t2, t3,
      shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  · rfl
end InitECandidate.Solver.Wave8GuestInv.Arith
