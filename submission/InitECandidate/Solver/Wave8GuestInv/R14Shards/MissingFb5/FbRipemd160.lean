import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

/-! Bounded termination proof for `fb_ripemd160` on `GuestInv`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R14Shards.MissingFb5

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees

private theorem fb_st_le32 :
    TerminatingFunBoundedOn GuestInv (ofString "st_le32") K.«st_le32» := by
  fb_prove 25 Guest.Software.guestFn_st_le32 K.«st_le32»

private theorem fb_st_le64 :
    TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64» := by
  have _ := fb_st_le32
  fb_prove 26 Guest.Software.guestFn_st_le64 K.«st_le64»

private theorem fb_rmd_f :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_f") K.«rmd_f» := by
  fb_prove 613 Guest.Software.guestFn_rmd_f K.«rmd_f»

private theorem fb_rmd_k :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_k") K.«rmd_k» := by
  fb_prove 614 Guest.Software.guestFn_rmd_k K.«rmd_k»

private theorem fb_rmd_kp :
    TerminatingFunBoundedOn GuestInv (ofString "rmd_kp") K.«rmd_kp» := by
  fb_prove 615 Guest.Software.guestFn_rmd_kp K.«rmd_kp»

private theorem fb_ripemd160_block :
    TerminatingFunBoundedOn GuestInv (ofString "ripemd160_block") K.«ripemd160_block» := by
  have _ := fb_rmd_f
  have _ := fb_rmd_k
  have _ := fb_rmd_kp
  fb_unfold 616 Guest.Software.guestFn_ripemd160_block
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 16)
        (straightOn _ rfl) (by counter_step) (by decide) (by decide)
    · apply dec_guestInv; apply dec_guestInv; apply dec_guestInv; apply dec_guestInv; apply dec_guestInv
      apply dec_guestInv; apply dec_guestInv; apply dec_guestInv; apply dec_guestInv; apply dec_guestInv
      apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · apply while_up_signed_const_guestInv (ofString "j") 1#64 (BitVec.ofNat 64 80)
        · fb_auto
        · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_
          refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_
          refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          exact CounterStep.assign _ 1#64
        · decide
        · decide
      · fb_auto
  · fb_arith K.«ripemd160_block»

private def sourceBody (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

private def sourceDecTail (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .dec _ _ _ body => body | _ => .skip

private def sourceSeqTail (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .seq _ rest => rest | _ => .skip

private noncomputable abbrev cEval {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

private noncomputable abbrev cEvalList {F : Type} (s : PanSemStateFiniteExact 64 F) (es : List (ExpHOL 64)) :=
  @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es

private theorem cEvalList_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : cEval s e = none) (hm : e ∈ es) : cEvalList s es = none := by
  induction es with
  | nil => simp at hm
  | cons first rest ih =>
    rcases List.mem_cons.mp hm with he | he
    · subst first; simp [cEvalList, evalListHOLExact, hn]
    · have ht := ih he
      simp only [cEvalList, evalListHOLExact] at ht ⊢
      rw [ht]
      cases hh : cEval s first <;> dsimp only [cEval] at hh <;> rw [hh]

private theorem cOp_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (e : ExpHOL 64) (es : List (ExpHOL 64))
    (hn : cEval s e = none) (hm : e ∈ es) : cEval s (.op op es) = none := by
  have hl := cEvalList_none s e es hn hm
  simp only [cEval, evalHOLExact, hl]

private theorem cLoadByte_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (address : BitVec 64)
    (he : cEval s e = some (.val (.word address)))
    (hn : ¬ s.memaddrs (panByteAlignHOL address)) : cEval s (.loadByte e) = none := by
  cases s.memory (panByteAlignHOL address) with
  | word _ => simp [cEval, evalHOLExact, he, panMemLoadByteHOL, hn]

private theorem outside_byte {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs (panByteAlignHOL b) := by
  intro h; rw [hg.memaddrs] at h; exact hb (ordinaryDomain_byte_interval b h)

private def ReadFailure {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  (evaluateHOLFiniteState s p).1 = some .error ∨ (evaluateHOLFiniteState s p).1 = some .timeOut

private theorem ReadFailure.seq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (first rest : ProgHOL 64) (h : ReadFailure s first) : ReadFailure s (.seq first rest) := by
  unfold ReadFailure at h ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s first with
  | mk result post =>
    rw [hr] at h
    rcases h with h | h <;> simp only at h <;> subst result <;> simp

private theorem ReadFailure.while {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64) (word : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word word)))
    (hw : word ≠ 0) (hb : ReadFailure (decClockHOLFinite s) body) :
    ReadFailure s (.while condition body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_while_fixClockRewrite, hc]
  simp only [if_pos hw]
  by_cases hz : s.clock = 0
  · simp [hz]
  · rw [if_neg hz]
    cases hr : evaluateHOLFiniteState (decClockHOLFinite s) body with
    | mk result post =>
      rw [hr] at hb
      rcases hb with h | h <;> simp only at h <;> subst result <;> simp

private theorem ReadFailure.dec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64) (v : ValueHOL 64)
    (he : cEval s e = some v)
    (hb : ReadFailure (setVarHOLFinite name v s) body) :
    ReadFailure s (.dec name shape e body) := by
  unfold ReadFailure at hb ⊢
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  dsimp only [cEval] at he
  rw [he]
  dsimp only
  split
  · exact hb
  · simp

private theorem ReadFailure.store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address value : ExpHOL 64) (hv : cEval s value = none) :
    ReadFailure s (.store address value) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_store]
  split
  · simp only [hv]; simp
  · simp

private def ripemdFirstLoop : ProgHOL 64 :=
  (.while (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16)))
    (.seq
      (.store (.op .add [(.var .global (ofString "rmd_x")),
          (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 8))])])
        (.op .or [
          (.loadByte (.op .add [(.var .local (ofString "blk")),
            (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))])])),
          (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),
            (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))]),
            (.const (BitVec.ofNat 64 1))])) (.const (BitVec.ofNat 64 8))),
          (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),
            (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))]),
            (.const (BitVec.ofNat 64 2))])) (.const (BitVec.ofNat 64 16))),
          (.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),
            (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))]),
            (.const (BitVec.ofNat 64 3))])) (.const (BitVec.ofNat 64 24)))]))
      (.assign .local (ofString "i")
        (.op .add [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 1))]))))

private theorem ripemd_loop_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hl : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) : ReadFailure s ripemdFirstLoop := by
  have ha : cEval (decClockHOLFinite s)
      (.op .add [(.var .local (ofString "blk")),
        (.panop .mul [(.var .local (ofString "i")), (.const (BitVec.ofNat 64 4))])]) =
      some (.val (.word b)) := by
    simp [cEval, evalHOLExact, evalListHOLExact, decClockHOLFinite, hl, hi,
      wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL]
  have hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 16))) =
      some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLFinite, evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess]
  unfold ripemdFirstLoop
  apply ReadFailure.while s _ _ 1 hc (by decide)
  apply ReadFailure.seq
  apply ReadFailure.store_none
  have hn := cLoadByte_none (decClockHOLFinite s) _ b ha (outside_byte s b hg hb)
  exact cOp_none (decClockHOLFinite s) .or _ _ hn (by simp)

private theorem ripemd160_block_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hl : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (sourceBody Guest.Software.guestFn_ripemd160_block) := by
  have hp : sourceBody Guest.Software.guestFn_ripemd160_block =
      .dec (ofString "i") .one (.const 0) (.seq ripemdFirstLoop
        (sourceSeqTail (sourceDecTail (sourceBody Guest.Software.guestFn_ripemd160_block)))) := rfl
  rw [hp]
  apply ReadFailure.dec s _ _ _ _ (.val (.word 0)) rfl
  apply ReadFailure.seq
  apply ripemd_loop_outside _ b (guestInv_setVar _ _ s hg) _ _ hb
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
      show ofString "i" ≠ ofString "blk" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem call_discard_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) rs = true := by
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
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp [emptyLocalsHOLFinite] at h; done) | skip
          dsimp only at h
          split at h
          · rename_i hrs
            exact ⟨vals, body, callee, rs, w, bpost, rfl, hlk, hclk, hrun, hrs⟩
          · simp at h

private theorem shape_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem two_args_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a, b] = some vals) :
    ∃ va vb, cEval s a = some va ∧ cEval s b = some vb ∧ vals = [va, vb] := by
  cases ha : cEval s a with
  | none => simp [evalListHOLFinite, evalListHOLExact, ha] at h
  | some va =>
    cases hb : cEval s b with
    | none => simp [evalListHOLFinite, evalListHOLExact, ha, hb] at h
    | some vb =>
      refine ⟨va, vb, rfl, rfl, ?_⟩
      simpa [evalListHOLFinite, evalListHOLExact, ha, hb] using h.symm

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
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst two; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]

private theorem two_arg_lookup_inv_shape {width : Nat} [NeZero width]
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
  rw [pan_two_arg_lookup code name first second ps1 ps2 rs body v1 v2 different hshapes.1 hshapes.2 lookup] at hfound
  cases hfound
  exact ⟨hshapes.1, hshapes.2, rfl, rfl, rfl⟩

private theorem touch_ripemd160_block (stateArg blockArg : ExpHOL 64) :
    DomainTouch blockArg (.call (some (none, none)) (ofString "ripemd160_block") [stateArg, blockArg]) := by
  intro F s hg hflow
  have hlookup : originalRuntimeCode.lookup (ofString "ripemd160_block") =
      some ([(ofString "hp", .one), (ofString "blk", .one)], sourceBody Guest.Software.guestFn_ripemd160_block, .one) :=
    lookup_of_guestAst_getElem 616 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ripemd160_block) rfl
  have hn : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ripemd160_block") [stateArg, blockArg])).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue _ rfl s)
  have hrun : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ripemd160_block") [stateArg, blockArg]) =
      (none, (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ripemd160_block") [stateArg, blockArg])).2) :=
    Prod.ext hn rfl
  obtain ⟨vals, found, callee, rs, _, _, hargs, hlk, _, hcallee, _⟩ := call_discard_none hrun
  obtain ⟨vstate, vblock, _, hblock, rfl⟩ := two_args_eval s stateArg blockArg vals hargs
  rw [hg.code] at hlk
  obtain ⟨_, hshape, rfl, rfl, _⟩ := two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "ripemd160_block") (ofString "hp") (ofString "blk")
    .one .one .one (sourceBody Guest.Software.guestFn_ripemd160_block) vstate vblock
    (by decide) hlookup hlk
  obtain ⟨b, rfl⟩ := shape_one_word hshape
  refine ⟨b, hblock, ?_⟩
  by_contra hout
  have hf := ripemd160_block_outside (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "hp", vstate)).update (ofString "blk", .val (.word b)))) b
    (guestInv_callEntry _ _ hg)
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hout
  unfold ReadFailure at hf
  rw [hcallee] at hf
  simp at hf

theorem «fb_ripemd160» :
    TerminatingFunBoundedOn GuestInv (ofString "ripemd160") K.«ripemd160» := by
  have _ := fb_ripemd160_block
  have _ := fb_memzero
  have _ := fb_memcpy
  have _ := fb_st_le64
  have _ := fb_st_le32
  fb_unfold 617 Guest.Software.guestFn_ripemd160
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
    apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
    apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
    apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
    apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_memory_walk_guestInv (ofString "p") (ofString "i") 64 _
        (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_ripemd160_block) (straightOn _ rfl))
        (DomainTouch.seq _ _ _ (touch_ripemd160_block _ _))
        (by counter_step) rfl (by decide) (by decide)
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memzero)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
      apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
      apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · fb_auto
      · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_st_le64)
        apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_ripemd160_block)
        apply TerminatingProgBoundedOn.seq_guestInv
        · fb_auto
        · apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
          apply TerminatingProgBoundedOn.seq_guestInv
          · exact while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 5)
              (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_st_le32) (straightOn _ rfl))
              (by counter_step) (by decide) (by decide)
          · exact straightOn _ rfl
  · unfold K.«ripemd160»
    rw [domainBytes_eq]
    generalize_K
    simp only [nat_max_eq]
    omega

end InitECandidate.Solver.Wave8GuestInv.R14Shards.MissingFb5
