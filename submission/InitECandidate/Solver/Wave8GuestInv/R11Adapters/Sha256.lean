import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbAuto2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees

/-! Clean `fb_*` bounds for the SHA-256 cone (`sha256_state_init`, `sha256_block`,
`sha256_finish`, `sha256`) and `compute_requests_hash`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters.Sha

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common
open InitECandidate.Solver.Wave8GuestInv.R11Adapters

theorem fb_sha256_state_init :
    TerminatingFunBoundedOn GuestInv (ofString "sha256_state_init") K.«sha256_state_init» := by
  fb_prove2 92 Guest.Software.guestFn_sha256_state_init K.«sha256_state_init»

theorem fb_sha256_block :
    TerminatingFunBoundedOn GuestInv (ofString "sha256_block") K.«sha256_block» := by
  fb_prove2 93 Guest.Software.guestFn_sha256_block K.«sha256_block»

theorem fb_sha256_finish :
    TerminatingFunBoundedOn GuestInv (ofString "sha256_finish") K.«sha256_finish» := by
  have _ := P12_P15.Callees.fb_st_be32
  fb_prove2 94 Guest.Software.guestFn_sha256_finish K.«sha256_finish»

private def sourceBody (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

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

private theorem outside_byte {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs (panByteAlignHOL b) := by
  intro h; rw [hg.memaddrs] at h; exact hb (ordinaryDomain_byte_interval b h)

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

private theorem sha256_block_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hl : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    (evaluateHOLFiniteState s (sourceBody Guest.Software.guestFn_sha256_block)).1 = some .error := by
  have hn := outside_byte s b hg hb
  have hload : cEval s (.loadByte (.op .add [(.var .local (ofString "blk")), (.const (BitVec.ofNat 64 0))])) = none := by
    cases hm : s.memory (panByteAlignHOL b) with
    | word _ =>
      simp [cEval, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
        panMemLoadByteHOL, hn]
  have hshift : ∀ c : ExpHOL 64, cEval s (.shift .lsl
      (.loadByte (.op .add [(.var .local (ofString "blk")), (.const (BitVec.ofNat 64 0))])) c) = none := by
    intro c
    simp only [cEval, evalHOLExact] at hload ⊢
    rw [hload]
  obtain ⟨xs, c, r, hp⟩ : ∃ xs c r, sourceBody Guest.Software.guestFn_sha256_block =
      .dec (ofString "w0") .one (.op .or (.shift .lsl
        (.loadByte (.op .add [(.var .local (ofString "blk")), (.const (BitVec.ofNat 64 0))])) c :: xs)) r :=
    ⟨_, _, _, rfl⟩
  have hinit : cEval s (.op .or (.shift .lsl
        (.loadByte (.op .add [(.var .local (ofString "blk")), (.const (BitVec.ofNat 64 0))])) c :: xs)) = none := by
    exact cOp_none s .or _ _ (hshift c) (by simp)
  rw [hp, evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [cEval] at hinit
  rw [hinit]

private theorem touch_sha256_block (stateArg blockArg : ExpHOL 64) :
    DomainTouch blockArg (.call (some (none, none)) (ofString "sha256_block") [stateArg, blockArg]) := by
  intro F s hg hflow
  have hlookup : originalRuntimeCode.lookup (ofString "sha256_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)], sourceBody Guest.Software.guestFn_sha256_block, .one) :=
    lookup_of_guestAst_getElem 93 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_block) rfl
  have hn : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256_block") [stateArg, blockArg])).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue _ rfl s)
  have hrun : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256_block") [stateArg, blockArg]) =
      (none, (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "sha256_block") [stateArg, blockArg])).2) :=
    Prod.ext hn rfl
  obtain ⟨vals, found, callee, rs, _, _, hargs, hlk, _, hcallee, _⟩ := call_discard_none hrun
  obtain ⟨vstate, vblock, _, hblock, rfl⟩ := two_args_eval s stateArg blockArg vals hargs
  rw [hg.code] at hlk
  obtain ⟨_, hshape, rfl, rfl, _⟩ := two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "sha256_block") (ofString "stp") (ofString "blk")
    .one .one .one (sourceBody Guest.Software.guestFn_sha256_block) vstate vblock
    (by decide) hlookup hlk
  obtain ⟨b, rfl⟩ := shape_one_word hshape
  refine ⟨b, hblock, ?_⟩
  by_contra hout
  have hf := sha256_block_outside (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "stp", vstate)).update (ofString "blk", .val (.word b)))) b
    (guestInv_callEntry _ _ hg)
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hout
  rw [hcallee] at hf
  simp at hf

theorem fb_sha256 : TerminatingFunBoundedOn GuestInv (ofString "sha256") K.«sha256» := by
  have _ := fb_sha256_state_init
  have _ := fb_sha256_block
  have _ := fb_sha256_finish
  have _ := P12_P15.Callees.fb_memzero
  have _ := P12_P15.Callees.fb_memcpy
  have _ := P12_P15.Callees.fb_st_be64
  fb_unfold 95 Guest.Software.guestFn_sha256
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact while_memory_walk_guestInv (ofString "p") (ofString "i") 64 _
          (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_sha256_block) (straightOn _ rfl))
          (DomainTouch.seq _ _ _ (touch_sha256_block _ _))
          (by counter_step) rfl (by decide) (by decide)
      · fb_auto
  · have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
    unfold K.«sha256»
    generalize_K
    generalize domainBytes = D at hD ⊢
    simp only [nat_max_eq, Nat.add_zero]
    omega

theorem fb_compute_requests_hash :
    TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash» := by
  have _ := fb_sha256
  have _ := P12_P15.Callees.fb_heap_mark
  have _ := P12_P15.Callees.fb_heap_release
  have _ := P12_P15.Callees.fb_alloc
  fb_prove2 840 Guest.Software.guestFn_compute_requests_hash K.«compute_requests_hash»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters.Sha
