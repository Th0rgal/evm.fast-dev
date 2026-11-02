import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Base

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Wave 8 Shard `s06` — `taylor_exponential`, `calculate_blob_gas_price`, and `op_blobbasefee`

Proves:
- `fb_taylor_exponential` (idx 232)
- `fb_calculate_blob_gas_price` (idx 233)
- `fb_op_blobbasefee` (idx 553)

Provenance: `taylorExpLoopBody_none` and `taylorExpRankVal_step` and their helper lemmas are
adapted from `submission/InitECandidate/Solver/GuestBoundCryptoDiv.lean` (lines 1674–2958),
combined with `TerminatingProgBoundedOn.while_rank` and `TerminatingProgBoundedOn.decCall_on`
from `campaign/specs-proposed/GuestInv.lean`.
-/

namespace InitECandidate.Solver.Wave8GuestInv.S06

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Guest.Software
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded

/-! ## 1. `u256` value & body semantics helpers (from `GuestBoundCryptoDiv.lean`) -/

private def u256Val (w0 w1 w2 w3 : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]

private abbrev u256ZeroVal : ValueHOL 64 := u256Val 0 0 0 0

private def u256ShapeHOL : ShapeHOL := .comb [.one, .one, .one, .one]

private theorem lookup_u256_from_word :
    originalRuntimeCode.lookup (ofString "u256_from_word") =
      some ([(ofString "w", .one)], sourceFnBody Guest.Software.guestFn_u256_from_word, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 39 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_from_word) rfl

private theorem lookup_u256_is_zero :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", u256ShapeHOL)], sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

private theorem lookup_mul64x64 :
    originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 59 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mul64x64) rfl

private theorem lookup_u256_mul :
    originalRuntimeCode.lookup (ofString "u256_mul") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_mul, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 60 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mul) rfl

private theorem lookup_u256_divmod :
    originalRuntimeCode.lookup (ofString "u256_divmod") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_divmod,
        .comb [.one, .one, .one, .one, .one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 69 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_divmod) rfl

private theorem lookup_u256_div :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", u256ShapeHOL), (ofString "b", u256ShapeHOL)],
        sourceFnBody Guest.Software.guestFn_u256_div, u256ShapeHOL) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem pan_one_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name parameter : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (val : ValueHOL width)
    (hshape : shapeEqHOL ps (shapeOfHOLExact val) = true)
    (lookup : code name = some ([(parameter, ps)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [val] =
      some (body, HolFiniteMapExact.empty.update (parameter, val), rs) := by
  have raw : lookupCodeHOLExact code name [val] =
      some (body, (fun key => if key = parameter then some val else none), rs) := by
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
    by_cases same : key = parameter
    · subst same
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have different : parameter ≠ key := Ne.symm same
      simp [same, different, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

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

private theorem eval_u256_from_word_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w))) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_from_word) =
      (some (.returned (u256Val w 0 0 0)), emptyLocalsHOLFinite s) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_from_word =
      .return (.rstruct [.var .local (ofString "w"), .const (0#64), .const (0#64), .const (0#64)]) := rfl
  rw [hbody, evaluateHOLFiniteState_return]
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rstruct [.var .local (ofString "w"), .const (0#64), .const (0#64), .const (0#64)]) =
      some (u256Val w 0 0 0) := by
    simp [evalHOLExact, evalListHOLExact, hw, u256Val]
  rw [hev]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s.structs
      (shapeOfHOLExact (u256Val w 0 0 0)) ≤ 32 := by
    simp [u256Val, shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz]

private theorem eval_u256_is_zero_body_zero {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (ha : s.locals.lookup (ofString "a") = some u256ZeroVal) :
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_is_zero) =
      (some (.returned (.val (.word 1))), emptyLocalsHOLFinite s) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
      .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
          .rfield 1 (.var .local (ofString "a")),
          .rfield 2 (.var .local (ofString "a")),
          .rfield 3 (.var .local (ofString "a"))]) (.const (0#64)))
        (.return (.const (1#64))) .skip)
        (.return (.const (0#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hor4_0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
        .rfield 1 (.var .local (ofString "a")),
        .rfield 2 (.var .local (ofString "a")),
        .rfield 3 (.var .local (ofString "a"))]) (.const (0#64))) = some (.val (.word 1)) := by
    simp [evalHOLExact, evalListHOLExact, ha, u256ZeroVal, u256Val, valueIsWord, valueWord, hor4_0, hcmp0]
  rw [hcond]
  dsimp only
  rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))]
  rw [evaluateHOLFiniteState_return]
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const (1#64)) =
      some (.val (.word 1)) := rfl
  rw [hev]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s.structs
      (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]

private theorem mul64x64_body_eq : sourceFnBody Guest.Software.guestFn_mul64x64 =
    .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
      (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
        (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
          (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
            (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
              (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                  (.seq
                    (.primitive (ofString "mid") .addCarry
                      [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                       .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                       .const (0#64)])
                    (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                      (.seq
                        (.primitive (ofString "lo") .addCarry
                          [.var .local (ofString "p00"),
                           .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                           .const (0#64)])
                        (.dec (ofString "hi") .one
                          (.op .add
                            [.var .local (ofString "p11"),
                             .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                             .rfield 1 (.var .local (ofString "lo"))])
                          (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl

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

private theorem eval_mul64x64_body_zero_left {F : Type}
    (s : PanSemStateFiniteExact 64 F) (wb : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word (0#64))))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word wb))) :
    ∃ post,
      evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64) =
        (some (.returned (.rStruct [.val (.word (0#64)), .val (.word (0#64))])), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite s := by
  rw [mul64x64_body_eq]
  have hlk_eq {m : HolFiniteMapExact MlS (ValueHOL 64)} (k : MlS) (v : ValueHOL 64) :
      (m.update (k, v)).lookup k = some v := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {m : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : MlS} (v : ValueHOL 64) (hne : k1 ≠ k2) :
      (m.update (k1, v)).lookup k2 = m.lookup k2 := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hand0 : wordOpHOL .and [0#64, 4294967295#64] = some 0#64 := by decide
  have hlsr0 : wordShiftHOL .lsr (0#64) 32 = some 0#64 := by decide
  have hlsl0 : wordShiftHOL .lsl (0#64) 32 = some 0#64 := by decide
  have hadd4_0 : wordOpHOL .add [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have h32 : (32#64).toNat = 32 := rfl
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0#64)) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  have hpo0 : panPrimopHOLExact PrimOp.addCarry ([.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    simp [panPrimopHOLExact, wordAddCarryHOL]
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand0]) hsh1 ?_
  intro s1 hl1
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl1]; exact hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word (0#64))) := by rw [hl1, hlk_ne _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl1, hlk_ne _ (by decide)]; exact hb
  clear hl1 ha hb s
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, hs1_a, h32, hlsr0]) hsh1 ?_
  intro s2 hl2
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl2]; exact hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl2, hlk_ne _ (by decide)]; exact hs1_b
  clear hl2 hs1_a0 hs1_a hs1_b s1
  have hwb0 : ∃ wb0 : BitVec 64, wordOpHOL .and [wb, 4294967295#64] = some wb0 :=
    ⟨_, rfl⟩
  obtain ⟨wb0, hwb0⟩ := hwb0
  refine eval_dec_ret (v := .val (.word wb0))
    (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hwb0])
    (by simp [shapeEqHOL, shapeOfHOLExact]) ?_
  intro s3 hl3
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl3]; exact hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word wb)) := by rw [hl3, hlk_ne _ (by decide)]; exact hs2_b
  clear hl3 hs2_a1 hs2_a0 hs2_b hwb0 s2
  have hwb1 : ∃ wb1 : BitVec 64, wordShiftHOL .lsr wb 32 = some wb1 :=
    ⟨wb >>> 32, by simp [wordShiftHOL]⟩
  obtain ⟨wb1, hwb1⟩ := hwb1
  refine eval_dec_ret (v := .val (.word wb1))
    (by simp [evalHOLExact, hs3_b, h32, hwb1])
    (by simp [shapeEqHOL, shapeOfHOLExact]) ?_
  intro s4 hl4
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl4]; exact hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl4, hlk_ne _ (by decide)]; exact hs3_a0
  clear hl4 hs3_b0 hs3_a1 hs3_a0 hs3_b hwb1 s3
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL]) hsh1 ?_
  intro s5 hl5
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl5]; exact hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl5, hlk_ne _ (by decide)]; exact hs4_a0
  clear hl5 hs4_b1 hs4_b0 hs4_a1 hs4_a0 s4
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL]) hsh1 ?_
  intro s6 hl6
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl6]; exact hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl6, hlk_ne _ (by decide)]; exact hs5_a0
  clear hl6 hs5_p00 hs5_b1 hs5_b0 hs5_a1 hs5_a0 s5
  refine eval_dec_ret (v := .rStruct [.val (.word (0#64)), .val (.word (0#64))])
    (by simp [evalHOLExact, evalListHOLExact]) hsh2 ?_
  intro s7 hl7
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl7]; exact hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word wb1)) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word wb0)) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word (0#64))) := by rw [hl7, hlk_ne _ (by decide)]; exact hs6_a0
  clear hl7 hs6_p11 hs6_p00 hs6_b1 hs6_b0 hs6_a1 hs6_a0 s6
  refine eval_prim_seq_ret
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL])
    hpo0
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]) ?_
  intro s8 hl8
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl8]; exact hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl8, hlk_ne _ (by decide)]; exact hs7_p00
  clear hl8 hs7_mid hs7_p11 hs7_p00 hs7_b1 hs7_b0 hs7_a1 hs7_a0 s7
  refine eval_dec_ret (v := .rStruct [.val (.word (0#64)), .val (.word (0#64))])
    (by simp [evalHOLExact, evalListHOLExact]) hsh2 ?_
  intro s9 hl9
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl9]; exact hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word (0#64))) := by rw [hl9, hlk_ne _ (by decide)]; exact hs8_p00
  clear hl9 hs8_mid hs8_p11 hs8_p00 s8
  refine eval_prim_seq_ret
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl0])
    hpo0
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]) ?_
  intro s10 hl10
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl10]; exact hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl10, hlk_ne _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word (0#64))) := by rw [hl10, hlk_ne _ (by decide)]; exact hs9_p11
  clear hl10 hs9_lo hs9_mid hs9_p11 hs9_p00 s9
  refine eval_dec_ret (v := .val (.word (0#64)))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr0, hlsl0, hadd4_0]) hsh1 ?_
  intro s11 hl11
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word (0#64))) := by rw [hl11]; exact hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by rw [hl11, hlk_ne _ (by decide)]; exact hs10_lo
  clear hl11 hs10_lo hs10_mid hs10_p11 s10
  refine ⟨emptyLocalsHOLFinite s11, ?_, rfl⟩
  rw [evaluateHOLFiniteState_return]
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret]
  dsimp only
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz]

private theorem one_arg_lookup_inv {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name param : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (v : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (lookup : code name = some ([(param, ps)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v] = some (foundBody, callee, foundRs)) :
    foundBody = body ∧ callee = HolFiniteMapExact.empty.update (param, v) ∧ foundRs = rs := by
  have hshape : shapeEqHOL ps (shapeOfHOLExact v) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup] at raw
      exact raw.1
  rw [pan_one_arg_lookup code name param ps rs body v hshape lookup] at hfound
  cases hfound
  exact ⟨rfl, rfl, rfl⟩

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

private theorem shape_one_is_word {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl =>
    cases wl with
    | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem seq_none {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
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

private theorem dec_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec name sh e body) = (none, post)) :
    ∃ v inner,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      shapeEqHOL sh (shapeOfHOLExact v) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · rename_i hsh
      cases hb : evaluateHOLFiniteState (setVarHOLFinite name v s) body with
      | mk r inner =>
        rw [hb] at h
        obtain ⟨he, hp⟩ := Prod.mk.inj h
        subst he
        exact ⟨v, inner, hv, hsh, hb, by rw [← hp]⟩
    · simp at h

private theorem decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

private theorem decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {retVal : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (some (.returned retVal), post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned retVal), inner) := by
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
            obtain ⟨he, _hp⟩ := Prod.mk.inj h
            have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
              simp [Bool.and_eq_true] at hboth; exact hboth.1
            let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name w { bpost with locals := s.locals }
            let inner : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState resumed cont).2
            refine ⟨vals, body, callee, rs, w, bpost, resumed, inner, rfl, hlk, hclk, hrun, hsh, rfl, hmeta,
              Prod.ext he rfl⟩
          · simp at h

private theorem call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

private theorem return_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {retVal v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (h : evaluateHOLFiniteState s (.return e) = (some (.returned retVal), post)) :
    retVal = v := by
  rw [evaluateHOLFiniteState_return, hev] at h
  dsimp only at h
  split at h
  · simp at h; exact h.1.symm
  · simp at h

private theorem decCall_return_not_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name fn : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.decCall name sh fn args (.return e))).1 ≠ none := by
  intro hnone
  cases h : evaluateHOLFiniteState s (.decCall name sh fn args (.return e)) with
  | mk r post =>
    rw [h] at hnone; dsimp only at hnone; subst hnone
    obtain ⟨_, _, _, _, _, _, resumed, inner, _, _, _, _, _, _, _, hret, _⟩ := decCall_none h
    rw [evaluateHOLFiniteState_return] at hret
    split at hret
    · simp at hret
    · split at hret <;> simp at hret

private theorem seq_returned_first {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} {retVal : ValueHOL 64}
    (hnn : (evaluateHOLFiniteState s a).1 ≠ none)
    (h : evaluateHOLFiniteState s (.seq a b) = (some (.returned retVal), post)) :
    evaluateHOLFiniteState s a = (some (.returned retVal), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  cases ha : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [ha] at h hnn
    cases r with
    | none => exact False.elim (hnn rfl)
    | some _ => exact h

private theorem one_arg_lookup_inv_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name param : MlS) (ps rs : ShapeHOL) (body : ProgHOL width) (v : ValueHOL width)
    {foundBody : ProgHOL width} {callee : HolFiniteMapExact MlS (ValueHOL width)} {foundRs : ShapeHOL}
    (lookup : code name = some ([(param, ps)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code name [v] = some (foundBody, callee, foundRs)) :
    shapeEqHOL ps (shapeOfHOLExact v) = true ∧
      foundBody = body ∧ callee = HolFiniteMapExact.empty.update (param, v) ∧ foundRs = rs := by
  have hshape : shapeEqHOL ps (shapeOfHOLExact v) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup] at raw
      exact raw.1
  exact ⟨hshape, one_arg_lookup_inv code name param ps rs body v lookup hfound⟩

private theorem returned_u256_mul_body_zero_left {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal : ValueHOL 64} {wb : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some u256ZeroVal)
    (hb : s.locals.lookup (ofString "b") = some (u256Val wb 0 0 0))
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_mul) =
      (some (.returned retVal), post)) :
    retVal = u256ZeroVal := by
  have hbody : ∃ slow, sourceFnBody Guest.Software.guestFn_u256_mul =
      .seq
        (.ite (.cmp .equal
            (.op .or [.rfield 1 (.var .local (ofString "a")),
                      .rfield 2 (.var .local (ofString "a")),
                      .rfield 3 (.var .local (ofString "a")),
                      .rfield 1 (.var .local (ofString "b")),
                      .rfield 2 (.var .local (ofString "b")),
                      .rfield 3 (.var .local (ofString "b"))])
            (.const (0#64)))
          (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
            [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
            (.return (.rstruct
              [.rfield 0 (.var .local (ofString "p")),
               .rfield 1 (.var .local (ofString "p")),
               .const (0#64), .const (0#64)])))
          .skip)
        slow := ⟨_, rfl⟩
  obtain ⟨slow, hbody⟩ := hbody
  rw [hbody] at h
  have hor0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 1 (.var .local (ofString "a")),
                  .rfield 2 (.var .local (ofString "a")),
                  .rfield 3 (.var .local (ofString "a")),
                  .rfield 1 (.var .local (ofString "b")),
                  .rfield 2 (.var .local (ofString "b")),
                  .rfield 3 (.var .local (ofString "b"))])
        (.const (0#64))) = some (.val (.word (1#64))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, u256ZeroVal, u256Val, valueIsWord, valueWord, hor0, hcmp0]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 1 (.var .local (ofString "a")),
                    .rfield 2 (.var .local (ofString "a")),
                    .rfield 3 (.var .local (ofString "a")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)])))
        .skip) =
      evaluateHOLFiniteState s
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)]))) := by
    rw [evaluateHOLFiniteState_ite, hcond]
    simp
  have hnn : (evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 1 (.var .local (ofString "a")),
                    .rfield 2 (.var .local (ofString "a")),
                    .rfield 3 (.var .local (ofString "a")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct
            [.rfield 0 (.var .local (ofString "p")),
             .rfield 1 (.var .local (ofString "p")),
             .const (0#64), .const (0#64)])))
        .skip)).1 ≠ none := by
    rw [hite]
    exact decCall_return_not_none s _ _ _ _ _
  have h1 := seq_returned_first hnn h
  rw [hite] at h1
  obtain ⟨vals, body, callee, rs, w, bpost, resumed, inner, hargs, hlk, _, hrun, _, hres_l, _, hret⟩ :=
    decCall_returned h1
  have hvals : vals = [.val (.word (0#64)), .val (.word wb)] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))] =
        some [.val (.word (0#64)), .val (.word wb)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb, u256ZeroVal, u256Val]
    exact Option.some.inj (hargs.symm.trans hev)
  subst hvals
  have hlk_orig : originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) := lookup_mul64x64
  rw [hcode] at hlk
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "mul64x64")
    (ofString "a") (ofString "b") .one .one (.comb [.one, .one])
    (sourceFnBody Guest.Software.guestFn_mul64x64) (.val (.word (0#64))) (.val (.word wb))
    (by decide) hlk_orig hlk
  obtain ⟨mpost, hmrun, _⟩ := eval_mul64x64_body_zero_left
    (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "a", .val (.word (0#64)))).update
        (ofString "b", .val (.word wb)))) wb
    (by
      have hne : ofString "b" ≠ ofString "a" := by decide
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hw : w = .rStruct [.val (.word (0#64)), .val (.word (0#64))] := by
    rw [hmrun] at hrun; simp at hrun; exact hrun.1.symm
  subst hw
  have hp_lk : resumed.locals.lookup (ofString "p") =
      some (.rStruct [.val (.word (0#64)), .val (.word (0#64))]) := by
    rw [hres_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  exact return_returned_inv
    (by simp [evalHOLExact, evalListHOLExact, hp_lk, u256ZeroVal, u256Val]) hret

private theorem returned_u256_divmod_body_zero_right {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal : ValueHOL 64}
    (hb : s.locals.lookup (ofString "b") = some u256ZeroVal)
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_divmod) =
      (some (.returned retVal), post)) :
    retVal = .rStruct
      [.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)),
       .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))] := by
  have hbody : ∃ rest, sourceFnBody Guest.Software.guestFn_u256_divmod =
      .seq
        (.ite (.cmp .equal
            (.op .or [.rfield 0 (.var .local (ofString "b")),
                      .rfield 1 (.var .local (ofString "b")),
                      .rfield 2 (.var .local (ofString "b")),
                      .rfield 3 (.var .local (ofString "b"))])
            (.const (0#64)))
          (.return (.rstruct
            [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
             .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
          .skip)
        rest := ⟨_, rfl⟩
  obtain ⟨rest, hbody⟩ := hbody
  rw [hbody] at h
  have hor0 : wordOpHOL .or [0#64, 0#64, 0#64, 0#64] = some 0#64 := by decide
  have hcmp0 : Compiler.Encoders.Asm.wordCmpHOL .equal (0#64) (0#64) = true := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local (ofString "b")),
                  .rfield 1 (.var .local (ofString "b")),
                  .rfield 2 (.var .local (ofString "b")),
                  .rfield 3 (.var .local (ofString "b"))])
        (.const (0#64))) = some (.val (.word (1#64))) := by
    simp [evalHOLExact, evalListHOLExact, hb, u256ZeroVal, u256Val, valueIsWord, valueWord, hor0, hcmp0]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 0 (.var .local (ofString "b")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
        .skip) =
      evaluateHOLFiniteState s
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)])) := by
    rw [evaluateHOLFiniteState_ite, hcond]
    simp
  have hnn : (evaluateHOLFiniteState s
      (.ite (.cmp .equal
          (.op .or [.rfield 0 (.var .local (ofString "b")),
                    .rfield 1 (.var .local (ofString "b")),
                    .rfield 2 (.var .local (ofString "b")),
                    .rfield 3 (.var .local (ofString "b"))])
          (.const (0#64)))
        (.return (.rstruct
          [.const (0#64), .const (0#64), .const (0#64), .const (0#64),
           .const (0#64), .const (0#64), .const (0#64), .const (0#64)]))
        .skip)).1 ≠ none := by
    rw [hite, evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  have h1 := seq_returned_first hnn h
  rw [hite] at h1
  exact return_returned_inv (by simp [evalHOLExact, evalListHOLExact]) h1

private theorem returned_u256_div_body_zero_right {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {retVal va : ValueHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some va)
    (hb : s.locals.lookup (ofString "b") = some u256ZeroVal)
    (h : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_div) =
      (some (.returned retVal), post)) :
    retVal = u256ZeroVal := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_div =
      .decCall (ofString "qr")
        (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
        (ofString "u256_divmod")
        [.var .local (ofString "a"), .var .local (ofString "b")]
        (.return (.rstruct
          [.rfield 0 (.var .local (ofString "qr")),
           .rfield 1 (.var .local (ofString "qr")),
           .rfield 2 (.var .local (ofString "qr")),
           .rfield 3 (.var .local (ofString "qr"))])) := rfl
  rw [hbody] at h
  obtain ⟨vals, body, callee, rs, w, bpost, resumed, inner, hargs, hlk, _, hrun, _, hres_l, _, hret⟩ :=
    decCall_returned h
  have hvals : vals = [va, u256ZeroVal] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "a"), .var .local (ofString "b")] = some [va, u256ZeroVal] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst hvals
  rw [hcode] at hlk
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_divmod")
    (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL
    (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
    (sourceFnBody Guest.Software.guestFn_u256_divmod) va u256ZeroVal
    (by decide) lookup_u256_divmod hlk
  have hw := returned_u256_divmod_body_zero_right
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hrun
  subst hw
  have hqr_lk : resumed.locals.lookup (ofString "qr") =
      some (.rStruct
        [.val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)),
         .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64)), .val (.word (0#64))]) := by
    rw [hres_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  exact return_returned_inv
    (by simp [evalHOLExact, evalListHOLExact, hqr_lk, u256ZeroVal, u256Val]) hret

private theorem assign_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {e : ExpHOL 64}
    (h : evaluateHOLFiniteState s (.assign .local name e) = (none, post)) :
    ∃ v,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      post.locals = s.locals.update (name, v) ∧
      post.code = s.code := by
  rw [evaluateHOLFiniteState_assign] at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · simp [setKvarHOLFinite, setVarHOLFinite] at h
      exact ⟨v, hv, by rw [← h], by rw [← h]⟩
    · simp at h

/-! ## 2. `taylor_exponential` loop body & ranking measure -/

private def taylorExpCond : ExpHOL 64 :=
  .cmp .equal (.var .local (ofString "nz")) (.const (0#64))

private def taylorExpTail : ProgHOL 64 :=
  .decCall (ofString "di") u256ShapeHOL (ofString "u256_from_word")
    [.var .local (ofString "i")]
    (.seq
      (.call (some (some (.local, ofString "di"), none)) (ofString "u256_mul")
        [.var .local (ofString "di"), .var .local (ofString "den")])
      (.seq
        (.call (some (some (.local, ofString "acc"), none)) (ofString "u256_div")
          [.var .local (ofString "p"), .var .local (ofString "di")])
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (1#64)]))
          (.call (some (some (.local, ofString "nz"), none)) (ofString "u256_is_zero")
            [.var .local (ofString "acc")]))))

private def taylorExpLoopBody : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "out"), none)) (ofString "u256_add")
      [.var .local (ofString "out"), .var .local (ofString "acc")])
    (.decCall (ofString "prod")
      (.comb [.one, .one, .one, .one, .one, .one, .one, .one])
      (ofString "u256_mul_full")
      [.var .local (ofString "acc"), .var .local (ofString "num")]
      (.seq
        (.ite (.cmp .notEqual
            (.op .or [.rfield 4 (.var .local (ofString "prod")),
                      .rfield 5 (.var .local (ofString "prod")),
                      .rfield 6 (.var .local (ofString "prod")),
                      .rfield 7 (.var .local (ofString "prod"))])
            (.const (0#64)))
          (.call (some (none, none)) (ofString "trap_with") [.const (3#64)])
          .skip)
        (.dec (ofString "p") u256ShapeHOL
          (.rstruct [.rfield 0 (.var .local (ofString "prod")),
                     .rfield 1 (.var .local (ofString "prod")),
                     .rfield 2 (.var .local (ofString "prod")),
                     .rfield 3 (.var .local (ofString "prod"))])
          taylorExpTail)))

private theorem taylorExpTail_none {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wi wden : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hden : s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (h : evaluateHOLFiniteState s taylorExpTail = (none, post)) :
    ∃ wnz' : BitVec 64,
      post.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) ∧
      post.locals.lookup (ofString "nz") = some (.val (.word wnz')) ∧
      (wi = 0#64 → wnz' = 1#64) := by
  unfold taylorExpTail at h
  obtain ⟨vals1, body1, callee1, rs1, wdi, bpost1, s1, inner1, hargs1, hlk1, _, hrun1, _, hl1, hc1, hcont1, hpost_l⟩ :=
    decCall_none h
  have hvals1 : vals1 = [.val (.word wi)] := by
    have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "i")] = some [.val (.word wi)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hi]
    exact Option.some.inj (hargs1.symm.trans hev)
  subst hvals1
  rw [hcode] at hlk1
  obtain ⟨rfl, rfl, _⟩ := one_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_from_word")
    (ofString "w") .one u256ShapeHOL (sourceFnBody Guest.Software.guestFn_u256_from_word)
    (.val (.word wi)) lookup_u256_from_word hlk1
  have hfrom := eval_u256_from_word_body
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "w", .val (.word wi)))) wi
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hwdi : wdi = u256Val wi 0 0 0 := by
    rw [hfrom] at hrun1; simp at hrun1; exact hrun1.1.symm
  subst hwdi
  have hs1_code : s1.code = originalRuntimeCode := hc1.trans hcode
  have hs1_di : s1.locals.lookup (ofString "di") = some (u256Val wi 0 0 0) := by
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "di" ≠ ofString "den" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "di" ≠ ofString "i" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hi]
  obtain ⟨s2, hc_mul, hcont2⟩ := seq_none hcont1
  obtain ⟨vals2, body2, callee2, rs2, wdi2, bpost2, hargs2, hlk2, _, hrun2, _, hl2, hc2⟩ :=
    call_local_none hc_mul
  have hvals2 : vals2 = [u256Val wi 0 0 0, u256Val wden 0 0 0] := by
    have hev : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "di"), .var .local (ofString "den")] =
        some [u256Val wi 0 0 0, u256Val wden 0 0 0] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_di, hs1_den]
    exact Option.some.inj (hargs2.symm.trans hev)
  subst hvals2
  rw [hs1_code] at hlk2
  obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_mul")
    (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL u256ShapeHOL
    (sourceFnBody Guest.Software.guestFn_u256_mul) (u256Val wi 0 0 0) (u256Val wden 0 0 0)
    (by decide) lookup_u256_mul hlk2
  have hs2_code : s2.code = originalRuntimeCode := hc2.trans hs1_code
  have hs2_di : s2.locals.lookup (ofString "di") = some wdi2 := by
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "di" ≠ ofString "i" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_i]
  have hwdi2_zero : wi = 0#64 → wdi2 = u256ZeroVal := by
    intro hwi0
    subst hwi0
    have hne : ofString "b" ≠ ofString "a" := by decide
    exact returned_u256_mul_body_zero_left (wb := wden)
      (by simp [callEntryStateHOLFinite, hs1_code])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, u256ZeroVal])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hrun2
  obtain ⟨s3, hc_div, hcont3⟩ := seq_none hcont2
  obtain ⟨vals3, body3, callee3, rs3, wacc, bpost3, hargs3, hlk3, _, hrun3, _, hl3, hc3⟩ :=
    call_local_none hc_div
  have hs3_code : s3.code = originalRuntimeCode := hc3.trans hs2_code
  have hs3_acc : s3.locals.lookup (ofString "acc") = some wacc := by
    rw [hl3]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "acc" ≠ ofString "i" := by decide
    rw [hl3]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_i]
  have hwacc_zero : wi = 0#64 → wacc = u256ZeroVal := by
    intro hwi0
    have hdi0 := hwdi2_zero hwi0
    cases hp : s2.locals.lookup (ofString "p") with
    | none =>
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp] at hargs3
    | some vp =>
      have hvals3 : vals3 = [vp, wdi2] := by
        have hev : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
            [.var .local (ofString "p"), .var .local (ofString "di")] = some [vp, wdi2] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hs2_di]
        exact Option.some.inj (hargs3.symm.trans hev)
      subst hvals3
      subst hdi0
      rw [hs2_code] at hlk3
      obtain ⟨rfl, rfl, _⟩ := two_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_div")
        (ofString "a") (ofString "b") u256ShapeHOL u256ShapeHOL u256ShapeHOL
        (sourceFnBody Guest.Software.guestFn_u256_div) vp u256ZeroVal
        (by decide) lookup_u256_div hlk3
      have hne : ofString "b" ≠ ofString "a" := by decide
      exact returned_u256_div_body_zero_right (va := vp)
        (by simp [callEntryStateHOLFinite, hs2_code])
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne])
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hrun3
  obtain ⟨s4, hc_asgn, hc_nz⟩ := seq_none hcont3
  obtain ⟨vi, hevi, hl4, hc4⟩ := assign_local_none hc_asgn
  have hvi : vi = .val (.word (wi + 1#64)) := by
    have hev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const (1#64)]) = some (.val (.word (wi + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, hs3_i, valueIsWord, valueWord, wordOpHOL, wordOp]
    exact Option.some.inj (hevi.symm.trans hev)
  subst hvi
  have hs4_code : s4.code = originalRuntimeCode := hc4.trans hs3_code
  have hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) := by
    rw [hl4]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_acc : s4.locals.lookup (ofString "acc") = some wacc := by
    have hne : ofString "i" ≠ ofString "acc" := by decide
    rw [hl4]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_acc]
  obtain ⟨vals5, body5, callee5, rs5, wnz, bpost5, hargs5, hlk5, _, hrun5, hrs5, hl5, _⟩ :=
    call_local_none hc_nz
  have hvals5 : vals5 = [wacc] := by
    have hev : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
        [.var .local (ofString "acc")] = some [wacc] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs4_acc]
    exact Option.some.inj (hargs5.symm.trans hev)
  subst hvals5
  rw [hs4_code] at hlk5
  obtain ⟨rfl, rfl, rfl⟩ := one_arg_lookup_inv originalRuntimeCode.lookup (ofString "u256_is_zero")
    (ofString "a") u256ShapeHOL .one (sourceFnBody Guest.Software.guestFn_u256_is_zero)
    wacc lookup_u256_is_zero hlk5
  obtain ⟨wnz', hwnz'⟩ := shape_one_is_word hrs5
  subst hwnz'
  have hinner_i : inner1.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) := by
    have hne : ofString "nz" ≠ ofString "i" := by decide
    rw [hl5]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs4_i]
  have hinner_nz : inner1.locals.lookup (ofString "nz") = some (.val (.word wnz')) := by
    rw [hl5]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨wnz', ?_, ?_, ?_⟩
  · have hne : ofString "i" ≠ ofString "di" := by decide
    rw [hpost_l, PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hinner_i
  · have hne : ofString "nz" ≠ ofString "di" := by decide
    rw [hpost_l, PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hinner_nz
  · intro hwi0
    have hacc0 := hwacc_zero hwi0
    subst hacc0
    have hisz := eval_u256_is_zero_body_zero
      (callEntryStateHOLFinite s4 (HolFiniteMapExact.empty.update (ofString "a", u256ZeroVal)))
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rw [hisz] at hrun5
    simp at hrun5
    exact hrun5.1.symm

private theorem taylorExpLoopBody_none {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wi wden : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hden : s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0))
    (h : evaluateHOLFiniteState s taylorExpLoopBody = (none, post)) :
    ∃ wnz' : BitVec 64,
      post.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) ∧
      post.locals.lookup (ofString "nz") = some (.val (.word wnz')) ∧
      post.code = s.code ∧
      (wi = 0#64 → wnz' = 1#64) := by
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s taylorExpLoopBody).1
  have havoid_den := evaluate_avoidsLocal_flowing (ofString "den") taylorExpLoopBody (by decide) s
    (by rw [h]; exact Or.inl rfl)
  rw [h] at hmeta havoid_den
  dsimp only at hmeta havoid_den
  have hpost_den : post.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) :=
    havoid_den.trans hden
  unfold taylorExpLoopBody at h
  obtain ⟨s1, hc_add, hcont1⟩ := seq_none h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hl1, hc1⟩ := call_local_none hc_add
  have hs1_code : s1.code = originalRuntimeCode := hc1.trans hcode
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "out" ≠ ofString "i" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hi]
  have hs1_den : s1.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "out" ≠ ofString "den" := by decide
    rw [hl1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
  obtain ⟨_, _, _, _, _, _, s2, inner2, _, _, _, _, _, hl2, hc2, hcont2, hpost_l2⟩ := decCall_none hcont1
  have hs2_code : s2.code = originalRuntimeCode := hc2.trans hs1_code
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    have hne : ofString "prod" ≠ ofString "i" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_i]
  have hs2_den : s2.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := by
    have hne : ofString "prod" ≠ ofString "den" := by decide
    rw [hl2]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_den]
  obtain ⟨s3, hc_ite, hcont3⟩ := seq_none hcont2
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notEqual
        (.op .or [.rfield 4 (.var .local (ofString "prod")),
                  .rfield 5 (.var .local (ofString "prod")),
                  .rfield 6 (.var .local (ofString "prod")),
                  .rfield 7 (.var .local (ofString "prod"))])
        (.const (0#64)))
      (.call (some (none, none)) (ofString "trap_with") [.const (3#64)])
      .skip
  have hm3 := (PanRunBounded.evaluateHOLFiniteState_metadata s2 iteProg).1
  have ha3_i := evaluate_avoidsLocal_flowing (ofString "i") iteProg (by decide) s2
    (by rw [hc_ite]; exact Or.inl rfl)
  have ha3_den := evaluate_avoidsLocal_flowing (ofString "den") iteProg (by decide) s2
    (by rw [hc_ite]; exact Or.inl rfl)
  rw [hc_ite] at hm3 ha3_i ha3_den
  dsimp only at hm3 ha3_i ha3_den
  have hs3_code : s3.code = originalRuntimeCode := hm3.trans hs2_code
  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word wi)) := ha3_i.trans hs2_i
  have hs3_den : s3.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) := ha3_den.trans hs2_den
  obtain ⟨vp, inner3, _, _, htail, hinner2_l⟩ := dec_none hcont3
  have hs4_code : (setVarHOLFinite (ofString "p") vp s3).code = originalRuntimeCode := hs3_code
  have hs4_i : (setVarHOLFinite (ofString "p") vp s3).locals.lookup (ofString "i") =
      some (.val (.word wi)) := by
    have hne : ofString "p" ≠ ofString "i" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_i]
  have hs4_den : (setVarHOLFinite (ofString "p") vp s3).locals.lookup (ofString "den") =
      some (u256Val wden 0 0 0) := by
    have hne : ofString "p" ≠ ofString "den" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs3_den]
  obtain ⟨wnz', hi3, hnz3, hzero3⟩ := taylorExpTail_none hs4_code hs4_i hs4_den htail
  refine ⟨wnz', hpost_den, ?_, ?_, hmeta, hzero3⟩
  · have hne1 : ofString "i" ≠ ofString "prod" := by decide
    have hne2 : ofString "i" ≠ ofString "p" := by decide
    rw [hpost_l2, PanRunBounded.resVarEq_lookup, if_neg hne1,
        hinner2_l, PanRunBounded.resVarEq_lookup, if_neg hne2]
    exact hi3
  · have hne1 : ofString "nz" ≠ ofString "prod" := by decide
    have hne2 : ofString "nz" ≠ ofString "p" := by decide
    rw [hpost_l2, PanRunBounded.resVarEq_lookup, if_neg hne1,
        hinner2_l, PanRunBounded.resVarEq_lookup, if_neg hne2]
    exact hnz3

private def taylorExpRankVal (wi wnz : BitVec 64) : Nat :=
  if wnz ≠ 0#64 then 0
  else if wi = 0#64 then 1
  else 2 ^ 64 - wi.toNat + 1

private theorem taylorExpRankVal_step (wi wnz' : BitVec 64)
    (hzero : wi = 0#64 → wnz' = 1#64) :
    taylorExpRankVal (wi + 1#64) wnz' + 1 ≤ taylorExpRankVal wi (0#64) := by
  have h1lt : (1#64).toNat = 1 := rfl
  by_cases hwi0 : wi = 0#64
  · have hnz1 : wnz' = 1#64 := hzero hwi0
    subst hwi0; subst hnz1
    decide
  · have hwi_pos : 0 < wi.toNat := by
      cases Nat.eq_zero_or_pos wi.toNat with
      | inl hz => exact False.elim (hwi0 (BitVec.eq_of_toNat_eq hz))
      | inr hp => exact hp
    have hwi_lt : wi.toNat < 2 ^ 64 := wi.isLt
    unfold taylorExpRankVal
    rw [if_neg (by decide : ¬ (0#64 : BitVec 64) ≠ 0#64), if_neg hwi0]
    by_cases hnz' : wnz' ≠ 0#64
    · rw [if_pos hnz']
      omega
    · rw [if_neg hnz']
      by_cases hwrap : wi + 1#64 = 0#64
      · rw [if_pos hwrap]
        omega
      · rw [if_neg hwrap]
        have hadd : (wi + 1#64).toNat = (wi.toNat + 1) % 2 ^ 64 := by
          simp [BitVec.toNat_add, h1lt]
        have hlt2 : wi.toNat + 1 < 2 ^ 64 := by
          by_contra hge
          have heq : wi.toNat + 1 = 2 ^ 64 := by omega
          apply hwrap
          apply BitVec.eq_of_toNat_eq
          rw [hadd, heq, Nat.mod_self]
          rfl
        rw [hadd, Nat.mod_eq_of_lt hlt2]
        omega

private theorem noTopCont_taylorExpLoopBody : noTopContinue taylorExpLoopBody = true := rfl

/-! ## 3. Guarded loop & pre-loop combinators for `fb_taylor_exponential` -/

variable {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [GuestInvLike GuestInv]

def TaylorDenInv (GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧ ∃ wden : BitVec 64, s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0)

def TaylorLoopInv (GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧ ∃ wden wi wnz : BitVec 64,
    s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) ∧
    s.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    s.locals.lookup (ofString "nz") = some (.val (.word wnz))

def taylorMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "nz") with
  | some (.val (.word wi)), some (.val (.word wnz)) => taylorExpRankVal wi wnz
  | _, _ => 0

theorem localsOnly_taylorDenInv : LocalsOnly ["den"] (TaylorDenInv GuestInv) := by
  intro F s locals k hloc ⟨hG, wden, hden⟩
  refine ⟨guestInv_with_locals_clock s locals k hG, wden, ?_⟩
  rw [hloc "den" (by simp)]
  exact hden

theorem decCallResume_taylorDenInv (name fname : MlS) (args : List (ExpHOL 64))
    (hne : name ≠ ofString "den") :
    DecCallResumeOn (TaylorDenInv GuestInv) (TaylorDenInv GuestInv) name fname args := by
  intro F state values body callee ret value post _ ⟨hG, wden, hden⟩ _ _ hrun
  have hGpost : GuestInv post := by
    have h := guestInv_evaluate (callEntryStateHOLFinite state callee) body
      (guestInv_callEntry state callee hG)
    rwa [hrun] at h
  refine ⟨guestInv_setVar name value _
    (guestInv_with_locals_clock post state.locals post.clock hGpost), wden, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]

theorem decCallResume_u256_from_word_den :
    DecCallResumeOn GuestInv (TaylorDenInv GuestInv) (ofString "den") (ofString "u256_from_word")
      [.var .local (ofString "denominator")] := by
  intro F state values body callee ret value post hcode hG hargs hlk hrun
  have hGpost : GuestInv post := by
    have h := guestInv_evaluate (callEntryStateHOLFinite state callee) body
      (guestInv_callEntry state callee hG)
    rwa [hrun] at h
  refine ⟨guestInv_setVar _ value _
    (guestInv_with_locals_clock post state.locals post.clock hGpost), ?_⟩
  have hvals_len : ∃ v0, values = [v0] := by
    cases h0 : state.locals.lookup (ofString "denominator") with
    | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0] at hargs
    | some v0 =>
      have hev : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.var .local (ofString "denominator")] = some [v0] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0]
      exact ⟨v0, Option.some.inj (hargs.symm.trans hev)⟩
  obtain ⟨v0, rfl⟩ := hvals_len
  rw [hcode] at hlk
  obtain ⟨hsh0, rfl, hcallee, rfl⟩ := one_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "u256_from_word") (ofString "w") .one u256ShapeHOL
    (sourceFnBody Guest.Software.guestFn_u256_from_word) v0 lookup_u256_from_word hlk
  have hsh0' : shapeEqHOL (shapeOfHOLExact v0) .one = true := by
    cases v0 with
    | val wl => cases wl with | word _ => simp [shapeOfHOLExact, shapeEqHOL]
    | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh0
    | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh0
  obtain ⟨wden, rfl⟩ := shape_one_is_word hsh0'
  have hfrom := eval_u256_from_word_body (callEntryStateHOLFinite state callee) wden
    (by rw [hcallee]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [hfrom] at hrun
  simp at hrun
  rcases hrun with ⟨rfl, _⟩
  exact ⟨wden, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

def TaylorDenIInv (GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧ ∃ wden wi : BitVec 64,
    s.locals.lookup (ofString "den") = some (u256Val wden 0 0 0) ∧
    s.locals.lookup (ofString "i") = some (.val (.word wi))

theorem localsOnly_taylorDenIInv : LocalsOnly ["den", "i"] (TaylorDenIInv GuestInv) := by
  intro F s locals k hloc ⟨hG, wden, wi, hden, hi⟩
  refine ⟨guestInv_with_locals_clock s locals k hG, wden, wi, ?_, ?_⟩
  · rw [hloc "den" (by simp)]; exact hden
  · rw [hloc "i" (by simp)]; exact hi

theorem seq_avoids_taylorDenInv {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn GuestInv first a)
    (havoid : avoidsLocal (ofString "den") first = true)
    (h2 : TerminatingProgBoundedOn (TaylorDenInv GuestInv) second b) :
    TerminatingProgBoundedOn (TaylorDenInv GuestInv) (.seq first second) (a + b) := by
  intro F state hcode ⟨hG, wden, hden⟩
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hav := evaluate_avoidsLocal_flowing (ofString "den") first havoid state
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hav hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hG hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    have hGmid : GuestInv mid := by
      have h := guestInv_evaluate state first hG
      rwa [hr1] at h
    have hmidInv : TaylorDenInv GuestInv mid :=
      ⟨hGmid, wden, (hav (Or.inl rfl)).trans hden⟩
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmidInv hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hG hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_taylorLoop_guestInv {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn (TaylorLoopInv GuestInv) first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn (TaylorLoopInv GuestInv) (.seq first second) (a + b) := by
  intro F state hcode hInv
  have hG : GuestInv state := hInv.1
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hInv hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    have hGmid : GuestInv mid := by
      have h := guestInv_evaluate state first hG
      rwa [hr1] at h
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hGmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hInv hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem decConst_i_taylorDenInv (k : BitVec 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn (TaylorDenIInv GuestInv) body K) :
    TerminatingProgBoundedOn (TaylorDenInv GuestInv) (.dec (ofString "i") .one (.const k) body) K := by
  intro F state hcode ⟨hG, wden, hden⟩
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.const k) =
      some (.val (.word k)) := rfl
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word k) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev] at hnt ⊢
  dsimp only at hnt ⊢
  rw [if_pos hsh] at hnt ⊢
  have hInv : TaylorDenIInv GuestInv (setVarHOLFinite (ofString "i") (.val (.word k)) state) := by
    refine ⟨guestInv_setVar _ _ state hG, wden, k, ?_, ?_⟩
    · have hne : ofString "i" ≠ ofString "den" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hb := hbody (setVarHOLFinite (ofString "i") (.val (.word k)) state) hcode hInv hnt
  simpa [setVarHOLFinite] using hb

theorem decCallResume_u256_is_zero_nz :
    DecCallResumeOn (TaylorDenIInv GuestInv) (TaylorLoopInv GuestInv) (ofString "nz") (ofString "u256_is_zero")
      [.var .local (ofString "acc")] := by
  intro F state values body callee ret value post hcode ⟨hG, wden, wi, hden, hi⟩ hargs hlk hrun
  have hGpost : GuestInv post := by
    have h := guestInv_evaluate (callEntryStateHOLFinite state callee) body
      (guestInv_callEntry state callee hG)
    rwa [hrun] at h
  refine ⟨guestInv_setVar _ value _
    (guestInv_with_locals_clock post state.locals post.clock hGpost), ?_⟩
  have hvals_len : ∃ v0, values = [v0] := by
    cases h0 : state.locals.lookup (ofString "acc") with
    | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0] at hargs
    | some v0 =>
      have hev : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          [.var .local (ofString "acc")] = some [v0] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, h0]
      exact ⟨v0, Option.some.inj (hargs.symm.trans hev)⟩
  obtain ⟨v0, rfl⟩ := hvals_len
  rw [hcode] at hlk
  obtain ⟨rfl, hcallee, rfl⟩ := one_arg_lookup_inv originalRuntimeCode.lookup
    (ofString "u256_is_zero") (ofString "a") u256ShapeHOL .one
    (sourceFnBody Guest.Software.guestFn_u256_is_zero) v0 lookup_u256_is_zero hlk
  have hret_word : ∃ wnz : BitVec 64, value = .val (.word wnz) := by
    have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
        .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
            .rfield 1 (.var .local (ofString "a")),
            .rfield 2 (.var .local (ofString "a")),
            .rfield 3 (.var .local (ofString "a"))]) (.const (0#64)))
          (.return (.const (1#64))) .skip)
          (.return (.const (0#64))) := rfl
    rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun
    split at hrun
    · split at hrun
      · rw [evaluateHOLFiniteState_skip] at hrun
        dsimp only at hrun
        rw [evaluateHOLFiniteState_return] at hrun
        have hev0 : @evalHOLExact 64 F _ (callEntryStateHOLFinite state callee).toExact
            (fun a => Classical.propDecidable ((callEntryStateHOLFinite state callee).memaddrs a))
            (.const (0#64)) = some (.val (.word (0#64))) := rfl
        rw [hev0] at hrun; dsimp only at hrun
        simp [shapeEqHOL, shapeOfHOLExact] at hrun
        exact ⟨0#64, hrun.1.symm⟩
      · rw [evaluateHOLFiniteState_return] at hrun
        have hev1 : @evalHOLExact 64 F _ (callEntryStateHOLFinite state callee).toExact
            (fun a => Classical.propDecidable ((callEntryStateHOLFinite state callee).memaddrs a))
            (.const (1#64)) = some (.val (.word (1#64))) := rfl
        rw [hev1] at hrun; dsimp only at hrun
        simp [shapeEqHOL, shapeOfHOLExact] at hrun
        exact ⟨1#64, hrun.1.symm⟩
    · simp at hrun
  obtain ⟨wnz, rfl⟩ := hret_word
  refine ⟨wden, wi, wnz, ?_, ?_, ?_⟩
  · have hne : ofString "nz" ≠ ofString "den" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hden]
  · have hne : ofString "nz" ≠ ofString "i" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hi]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem taylorWhile_bounded
    {B : Nat} (hbody : TerminatingProgBoundedOn GuestInv taylorExpLoopBody B) :
    TerminatingProgBoundedOn (TaylorLoopInv GuestInv) (.while taylorExpCond taylorExpLoopBody)
      (((2 ^ 64 + 1) + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank taylorMu
    (fun s ⟨hG, wden, wi, wnz, hden, hi, hnz⟩ =>
      ⟨guestInv_decClock s hG, wden, wi, wnz, hden, hi, hnz⟩)
    (fun s hcode ⟨hG, _⟩ => hbody s hcode hG) ?_ ?_
  · intro F s _ ⟨_, _, wi, wnz, _, hi, hnz⟩ _
    simp only [taylorMu, hi, hnz, taylorExpRankVal]
    have := wi.isLt
    split_ifs <;> omega
  · intro F s hcode ⟨hG, wden, wi, wnz, hden, hi, hnz⟩ hact hflow
    have hnoCont := evaluate_noTopContinue taylorExpLoopBody noTopCont_taylorExpLoopBody
      (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) taylorExpLoopBody).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnoCont
    obtain ⟨word, hw, hne0⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s .equal _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : a = wnz := by
      have : some (ValueHOL.val (.word a)) = some (ValueHOL.val (.word wnz)) := ha.symm.trans hnz
      injection this with h1; injection h1 with h2; injection h2
    have hbb : b = 0#64 := by
      have : some (ValueHOL.val (.word b)) = some (ValueHOL.val (.word 0#64)) := hb.symm
      injection this with h1; injection h1 with h2; injection h2
    subst a; subst b
    have hwnz0 : wnz = 0#64 := by
      by_contra hne
      have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal wnz 0#64 = false := by
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]
      rw [hcmp] at hword
      simp at hword
      exact hne0 hword
    subst wnz
    rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) taylorExpLoopBody with ⟨res, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨wnz', hden', hi', hnz', _, hzero'⟩ :=
      taylorExpLoopBody_none (s := decClockHOLFinite s) hcode hi hden hrun
    have hstep := taylorExpRankVal_step wi wnz' hzero'
    have hGpost : GuestInv post := by
      have := guestInv_evaluate (decClockHOLFinite s) taylorExpLoopBody (guestInv_decClock s hG)
      rwa [hrun] at this
    refine ⟨⟨hGpost, wden, wi + 1#64, wnz', hden', hi', hnz'⟩, ?_⟩
    simp only [taylorMu, hi', hnz', hi, hnz]
    omega

/-! ## 4. Leaf #18: `fb_taylor_exponential` (idx 232) -/

attribute [local irreducible] TerminatingProgBoundedOn

theorem fb_taylor_exponential_of
    (h_u256_from_word : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word»)
    (h_u256_mul : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add»)
    (h_u256_mul_full : TerminatingFunBoundedOn GuestInv (ofString "u256_mul_full") K.«u256_mul_full»)
    (h_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with»)
    (h_u256_div : TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div») :
    TerminatingFunBoundedOn GuestInv (ofString "taylor_exponential") K.«taylor_exponential» := by
  apply onFun_le 232 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_taylor_exponential _ rfl
  · htab_unfold Guest.Software.guestFn_taylor_exponential
    apply TerminatingProgBoundedOn.decCall_on h_u256_from_word _ _ _
      (callEntryOn_guestInv _ _) decCallResume_u256_from_word_den
    apply TerminatingProgBoundedOn.decCall_on h_u256_from_word _ _ _
      (fun s v b c r hc ⟨hG, _⟩ ha hl => callEntryOn_guestInv _ _ s v b c r hc hG ha hl)
      (decCallResume_taylorDenInv _ _ _ (by decide))
    apply TerminatingProgBoundedOn.decCall_on h_u256_from_word _ _ _
      (fun s v b c r hc ⟨hG, _⟩ ha hl => callEntryOn_guestInv _ _ s v b c r hc hG ha hl)
      (decCallResume_taylorDenInv _ _ _ (by decide))
    apply seq_avoids_taylorDenInv (TerminatingProgBoundedOn.call_guestInv h_u256_mul _ _) rfl
    apply TerminatingProgBoundedOn.dec_onLocals localsOnly_taylorDenInv _
      (by intro n hn; simp at hn; subst hn; decide)
    apply decConst_i_taylorDenInv (1#64)
    apply TerminatingProgBoundedOn.dec_onLocals localsOnly_taylorDenIInv _
      (by intro n hn; simp at hn; rcases hn with rfl | rfl <;> decide)
    apply TerminatingProgBoundedOn.decCall_on h_u256_is_zero _ _ _
      (fun s v b c r hc ⟨hG, _⟩ ha hl => callEntryOn_guestInv _ _ s v b c r hc hG ha hl)
      decCallResume_u256_is_zero_nz
    apply seq_taylorLoop_guestInv
    · apply taylorWhile_bounded
      htab_walk
    · htab_walk
  · htab_bound K.«taylor_exponential»

/-! ## 5. Leaf #19: `fb_calculate_blob_gas_price` (idx 233) -/

theorem fb_calculate_blob_gas_price_of
    (h_taylor_exponential : TerminatingFunBoundedOn GuestInv (ofString "taylor_exponential") K.«taylor_exponential») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price» := by
  apply onFun_le 233 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_blob_gas_price _ rfl
  · htab_unfold Guest.Software.guestFn_calculate_blob_gas_price
    htab_walk
  · htab_bound K.«calculate_blob_gas_price»

/-! ## 6. Leaf #20: `fb_op_blobbasefee` (idx 553) -/

theorem fb_op_blobbasefee_of
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (h_calculate_blob_gas_price : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee» := by
  apply onFun_le 553 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_blobbasefee _ rfl
  · htab_unfold Guest.Software.guestFn_op_blobbasefee
    htab_walk
  · htab_bound K.«op_blobbasefee»

end InitECandidate.Solver.Wave8GuestInv.S06

