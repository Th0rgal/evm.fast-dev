import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

namespace Group10

/-! ## Part 0: shape helpers and `u256_is_zero` value semantics

This shard supplies the helper lemmas for the three CALL-family handler theorems
in `Group10CallsCreatesTail2`.  It is deliberately split off from the tail shard
because the combined single-file estimate exceeded the 1500-line cap. -/

/-- A value whose shape is `comb [.one, .one]` is a record of two words. -/
theorem shape_comb2_words_g10 {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (ShapeHOL.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] := by
  cases v with
  | val lab => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct nm fs => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fs =>
    simp only [shapeOfHOLExact] at h
    have hlist : fs.map shapeOfHOLExact = [.one, .one] :=
      ShapeHOL.comb.inj ((shapeEqHOL_eq_true _ _).mp h)
    cases fs with
    | nil => simp at hlist
    | cons x rest =>
      cases rest with
      | nil => simp [List.map_cons, List.map_nil] at hlist
      | cons y rest' =>
        cases rest' with
        | nil =>
          simp [List.map_cons, List.map_nil] at hlist
          obtain ⟨a, rfl⟩ : ∃ w, x = .val (.word w) := by
            cases x with
            | val lab =>
              cases lab with
              | word w => exact ⟨w, rfl⟩
            | rStruct fs2 => simp [shapeOfHOLExact] at hlist
            | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
          obtain ⟨b, rfl⟩ : ∃ w, y = .val (.word w) := by
            cases y with
            | val lab =>
              cases lab with
              | word w => exact ⟨w, rfl⟩
            | rStruct fs2 => simp [shapeOfHOLExact] at hlist
            | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
          exact ⟨a, b, rfl⟩
        | cons z _ =>
          simp only [List.map_cons] at hlist
          simp at hlist

/-- A value whose shape is `comb` of four `.one`s is a record of four words. -/
theorem shape_comb4_words_g10 {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v)
      (ShapeHOL.comb [.one, .one, .one, .one]) = true) :
    ∃ a b c d : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  cases v with
  | val lab => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct nm fs => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fs =>
    simp only [shapeOfHOLExact] at h
    have hlist : fs.map shapeOfHOLExact = [.one, .one, .one, .one] :=
      ShapeHOL.comb.inj ((shapeEqHOL_eq_true _ _).mp h)
    have hf_len : fs.length = 4 := by
      have := congrArg List.length hlist
      simp at this
      exact this
    cases fs with
    | nil => simp at hf_len
    | cons x rest =>
      cases rest with
      | nil => simp at hf_len
      | cons y rest2 =>
        cases rest2 with
        | nil => simp at hf_len
        | cons z rest3 =>
          cases rest3 with
          | nil => simp at hf_len
          | cons u rest4 =>
            cases rest4 with
            | nil =>
              simp only [List.map_cons, List.map_nil] at hlist
              obtain ⟨a, rfl⟩ : ∃ w, x = .val (.word w) := by
                cases x with
                | val lab =>
                  cases lab with
                  | word w => exact ⟨w, rfl⟩
                | rStruct fs2 => simp [shapeOfHOLExact] at hlist
                | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
              obtain ⟨b, rfl⟩ : ∃ w, y = .val (.word w) := by
                cases y with
                | val lab =>
                  cases lab with
                  | word w => exact ⟨w, rfl⟩
                | rStruct fs2 => simp [shapeOfHOLExact] at hlist
                | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
              obtain ⟨c, rfl⟩ : ∃ w, z = .val (.word w) := by
                cases z with
                | val lab =>
                  cases lab with
                  | word w => exact ⟨w, rfl⟩
                | rStruct fs2 => simp [shapeOfHOLExact] at hlist
                | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
              obtain ⟨d, rfl⟩ : ∃ w, u = .val (.word w) := by
                cases u with
                | val lab =>
                  cases lab with
                  | word w => exact ⟨w, rfl⟩
                | rStruct fs2 => simp [shapeOfHOLExact] at hlist
                | nStruct nm fs2 => simp [shapeOfHOLExact] at hlist
              exact ⟨a, b, c, d, rfl⟩
            | cons _ _ =>
              simp only [List.map_cons] at hlist
              simp at hlist

/-! ### 0b. Locality and `u256_is_zero` value semantics -/

/-- Programs that only touch locals, the clock, or terminate.  (Copy of
`R13Shards.HtabSetSpec.locOnlyW` with the `while` case dropped, which the
helper bodies in this shard never use.) -/
def locOnlyW_g10 : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnlyW_g10 body
  | .seq first second => locOnlyW_g10 first && locOnlyW_g10 second
  | .ite _ yes no => locOnlyW_g10 yes && locOnlyW_g10 no
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrameW_eval_g10 {F : Type} (p : ProgHOL 64) (hp : locOnlyW_g10 p = true)
    (s : PanSemStateFiniteExact 64 F) : LocFrame s (evaluateHOLFiniteState s p).2 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | assign kind name e =>
    cases kind with
    | global => simp [shape, locOnlyW_g10] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | dec name sh init body =>
    have hb : locOnlyW_g10 body = true := by simpa [shape, locOnlyW_g10] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrameW_eval_g10 body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | seq first second =>
    have h12 : locOnlyW_g10 first = true ∧ locOnlyW_g10 second = true := by
      simpa [shape, locOnlyW_g10, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrameW_eval_g10 first h12.1 s
    have hle0 := evaluateHOLFiniteState_clock_le s first
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1 hle0
    dsimp only at ih1 hle0 ⊢
    have mclk : mid.clock ≤ s.clock := hle0
    cases r1 with
    | none => exact ih1.trans (locFrameW_eval_g10 second h12.2 mid)
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : locOnlyW_g10 yes = true ∧ locOnlyW_g10 no = true := by
      simpa [shape, locOnlyW_g10, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrameW_eval_g10 no h12.2 s
      · exact locFrameW_eval_g10 yes h12.1 s
    · exact LocFrame.refl s
  | primitive _ _ _ | store _ _ | store32 _ _ | storeByte _ _ | call _
  | decCall _ _ _ _ | extCall _ | shMemLoad _ _ _ _ | shMemStore _ _ _
  | tick | «while» _ _ =>
    rw [shape] at hp
    simp [locOnlyW_g10] at hp

theorem locOnlyW_g10_u256_is_zero :
    locOnlyW_g10 (sourceFnBody Guest.Software.guestFn_u256_is_zero) = true := by
  show locOnlyW_g10
    (sourceFunctionEntry
      (Decl.function
        { name := "u256_is_zero", inline := false, exported := false,
          params := [("a", Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])],
          body :=
            (Prog.ite
                  (Exp.cmp Cmp.equal
                    (Exp.op BinOp.or
                      [Exp.rField 0 (Exp.var VarKind.local "a"),
                        Exp.rField 1 (Exp.var VarKind.local "a"),
                        Exp.rField 2 (Exp.var VarKind.local "a"),
                        Exp.rField 3 (Exp.var VarKind.local "a")])
                    (Exp.const 0#64))
                  (Prog.return (Exp.const 1#64)) Prog.skip).seq
              (Prog.return (Exp.const 0#64)),
          returnShape := Shape.one })).2.2.1 = true
  rfl

/-- Exact value semantics of `u256_is_zero` (copy of the private
`Group09LogReturnRevert.u256_is_zero_body_exact_g09`). -/
theorem u256_is_zero_body_exact_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c d : BitVec 64)
    (ha : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_is_zero)).1 =
      some (.returned v)) :
    v = .val (.word (if a ||| b ||| c ||| d = 0#64 then 1#64 else 0#64)) := by
  have hbody : sourceFnBody Guest.Software.guestFn_u256_is_zero =
      .seq (.ite (.cmp .equal (.op .or [.rfield 0 (.var .local (ofString "a")),
          .rfield 1 (.var .local (ofString "a")),
          .rfield 2 (.var .local (ofString "a")),
          .rfield 3 (.var .local (ofString "a"))]) (.const 0#64))
        (.return (.const 1#64)) .skip)
        (.return (.const 0#64)) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hor : OrOp.or a (OrOp.or b (OrOp.or c (OrOp.or d 0#64))) = a ||| b ||| c ||| d := by
    change a ||| (b ||| (c ||| (d ||| 0#64))) = ((a ||| b) ||| c) ||| d
    simp [BitVec.or_assoc]
  by_cases h : a ||| b ||| c ||| d = 0#64
  · simpa [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL] using hret.symm
  · simpa [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp, valueIsWord,
      valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hor, h,
      evaluateHOLFiniteState_return, evaluateHOLFiniteState_skip,
      shapeOfHOLExact, sizeOfShapeWithContextHOL] using hret.symm

private theorem lookup_u256_is_zero_g10 :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

/-- Value-semantics spec for `u256_is_zero`: the result is a word in `{0, 1}`
that is `1` exactly when the four limbs of the bound parameter `a` are all
zero.  At the `decCall` call sites of this shard the parameter `a` is bound to
a four-word record value, so the `∀ w0 w1 w2 w3` clause applies with the limbs
of the argument. -/
theorem epsA_u256_is_zero_sem_g10 :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ z : BitVec 64, v = .val (.word z) ∧
        (z = 0#64 ∨ z = 1#64) ∧
        (∀ w0 w1 w2 w3 : BitVec 64,
          s.locals.lookup (ofString "a") =
            some (.rStruct [.val (.word w0), .val (.word w1),
              .val (.word w2), .val (.word w3)]) →
            (z = 1#64 → (w0 ||| w1 ||| w2 ||| w3) = 0#64)))
      (ofString "u256_is_zero") := by
  refine ⟨_, _, _, lookup_u256_is_zero_g10, ?_⟩
  intro F s hcode hInv hWF _ ⟨vals, hl⟩ _
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "u256_is_zero") vals _ _ _ hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_u256_is_zero_g10] at hx
  split at hx
  · rename_i hcond
    injection hx with hx_eq
    have hmap := congrArg (fun x => x.2.1) hx_eq
    rcases vals with _ | ⟨v1, _ | _⟩
    · simp at hcond
    · have hall := hcond.2.2
      have hraw : shapeEqHOL (ShapeHOL.comb [.one, .one, .one, .one])
          (shapeOfHOLExact v1) = true := by
        by_contra hns
        simp [hns] at hall
      have hsh : shapeEqHOL (shapeOfHOLExact v1)
          (ShapeHOL.comb [.one, .one, .one, .one]) = true :=
        (shapeEqHOL_eq_true _ _).mpr (((shapeEqHOL_eq_true _ _).mp hraw).symm)
      obtain ⟨w0, w1, w2, w3, rfl⟩ := shape_comb4_words_g10 hsh
      have ha : s.locals.lookup (ofString "a") =
          some (.rStruct [.val (.word w0), .val (.word w1),
            .val (.word w2), .val (.word w3)]) := by
        have hget := congrFun hmap.symm (ofString "a")
        simpa [List.map, List.zip, List.foldl] using hget
      have hlf : LocFrame s
          ((evaluateHOLFiniteState s
            (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2) :=
        locFrameW_eval_g10 _ locOnlyW_g10_u256_is_zero s
      have hlf' : LocFrame s
          ((evaluateHOLFiniteState s
            (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2) := hlf
      have hmem : ((evaluateHOLFiniteState s
          (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2).memory = s.memory := by
        unfold LocFrame at hlf
        rw [hlf]
      have hglob : ((evaluateHOLFiniteState s
          (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2).globals = s.globals := by
        unfold LocFrame at hlf'
        rw [hlf']
      have hInv_p : EvmInv
          ((evaluateHOLFiniteState s
            (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2) := by
        have h := localsFree_evmInv s
          ((evaluateHOLFiniteState s
            (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2).locals
          ((evaluateHOLFiniteState s
            (sourceFnBody Guest.Software.guestFn_u256_is_zero)).2).clock hInv
        rwa [← hlf] at h
      dsimp only
      refine ⟨fun v hv => ?_, fun herr => ?_⟩
      · have hz := u256_is_zero_body_exact_g10 s w0 w1 w2 w3 ha v hv
        have key : ∀ (x : BitVec 64),
            x = (if w0 ||| w1 ||| w2 ||| w3 = 0#64 then 1#64 else 0#64) →
            (x = 0#64 ∨ x = 1#64) ∧
            (x = 1#64 → w0 ||| w1 ||| w2 ||| w3 = 0#64) := by
          intro x hx
          by_cases hor0 : w0 ||| w1 ||| w2 ||| w3 = 0#64
          · rw [if_pos hor0] at hx
            exact ⟨Or.inr hx, fun _ => hor0⟩
          · rw [if_neg hor0] at hx
            refine ⟨Or.inl hx, fun h1 => ?_⟩
            exfalso
            rw [hx] at h1
            exact absurd h1 (by decide)
        exact ⟨⟨hInv_p, headMemChainWF_of_locFrame hWF hlf⟩, evmChain_congr hmem hglob,
          le_of_eq (evm_congr hmem hglob).2.1, hlf,
          (if w0 ||| w1 ||| w2 ||| w3 = 0#64 then 1#64 else 0#64), hz,
          (key _ rfl).1,
          fun w0' w1' w2' w3' hlook => by
            have heq : some (ValueHOL.rStruct [.val (.word w0), .val (.word w1),
                .val (.word w2), .val (.word w3)])
                = some (ValueHOL.rStruct [.val (.word w0'), .val (.word w1'),
                  .val (.word w2'), .val (.word w3')]) :=
              ha.symm.trans hlook
            simp only [Option.some.injEq, ValueHOL.rStruct.injEq, List.cons.injEq,
              ValueHOL.val.injEq, HolWordLab.word.injEq] at heq
            obtain ⟨e0, e1, e2, e3⟩ := heq
            rw [← e0, ← e1, ← e2]
            rw [← e3.1]
            exact (key _ rfl).2⟩
      · exact ⟨⟨hInv_p, headMemChainWF_of_locFrame hWF hlf⟩, evmChain_congr hmem hglob,
          le_of_eq (evm_congr hmem hglob).2.1⟩
    · have hlen := hcond.2.1
      simp only [List.length_cons, List.length_nil] at hlen
      omega
  · cases hx

private theorem step_ro_call_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)}
    {v : ValueHOL 64} {cont : ProgHOL 64}
    (hfn : opRoCallees fname = true)
    (hst_c : st.code = originalRuntimeCode)
    (hst_lf : LocFrame s st)
    (hr : (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 =
      some (.returned v)) :
    ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      st'.code = originalRuntimeCode ∧
      LocFrame s st' ∧
      st'.locals = st.locals.update ((nm), .val (.word w)) ∧
      (∃ vals body callee rs,
        evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
        lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 =
          some (.returned (.val (.word w)))) ∧
      (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
    rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
    · rw [hargs] at hr; simp at hr
    · rw [hargs] at hr; dsimp only at hr
      rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · rw [hl] at hr; simp at hr
      · rw [hl] at hr; dsimp only at hr
        split at hr
        · simp at hr
        · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
              some (body, callee, rs) := by
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
              (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr

/-- Prefix lemma for `calculate_message_call_gas`: the stipend local is pinned
to `0` or `2300`, and `2300` only when the four limbs of the `value` local
have nonzero bitwise-or. -/
private theorem cmc_stipend_link_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (_hex : s.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)))
    (_hmc : s.locals.lookup (ofString "memory_cost") = some (.val (.word 0#64)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).1 =
      some (.returned v)) :
    ∃ st : BitVec 64,
      (st = 0#64 ∨ st = 2300#64) ∧
      (st = 2300#64 → ∀ q0 q1 q2 q3 : BitVec 64,
        s.locals.lookup (ofString "value") =
          some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
            .val (.word q2), .val (.word q3)]) →
        (q0 ||| q1 ||| q2 ||| q3) ≠ 0#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_calculate_message_call_gas =
      .decCall (ofString "vz") .one (ofString "u256_is_zero")
        [.var .local (ofString "value")]
        (.dec (ofString "stipend") .one (.const 0#64)
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "vz")) (.const 0#64))
              (.assign .local (ofString "stipend") (.const 2300#64))
              .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
                [.var .local (ofString "extra_gas"), .var .local (ofString "memory_cost")]
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need")))
                  (.decCall (ofString "c") .one (ofString "add_sat")
                      [.var .local (ofString "gas"), .var .local (ofString "extra_gas")]
                    (.decCall (ofString "s") .one (ofString "add_sat")
                        [.var .local (ofString "gas"), .var .local (ofString "stipend")]
                      (.return (.rstruct [.var .local (ofString "c"),
                        .var .local (ofString "s")]))))
                  .skip)
                (.dec (ofString "avail") .one
                    (.op .sub [.op .sub [.var .local (ofString "gas_left"),
                      .var .local (ofString "memory_cost")],
                      .var .local (ofString "extra_gas")])
                  (.dec (ofString "mx") .one
                      (.op .sub [.var .local (ofString "avail"),
                        .shift .lsr (.var .local (ofString "avail")) (.const 6#64)])
                    (.dec (ofString "g") .one (.var .local (ofString "gas"))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g")))
                          (.assign .local (ofString "g") (.var .local (ofString "mx")))
                          .skip)
                        (.return (.rstruct
                          [.op .add [.var .local (ofString "g"),
                            .var .local (ofString "extra_gas")],
                           .op .add [.var .local (ofString "g"),
                            .var .local (ofString "stipend")]])))))))))) := rfl
  rw [hbody] at hret
  have sup_ne : ∀ (nm k : MlS) (val : ValueHOL 64) (st : PanSemStateFiniteExact 64 F),
      nm ≠ k → (setVarHOLFinite nm val st).locals.lookup k = st.locals.lookup k := by
    intro nm k val st hne
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  obtain ⟨zw, s1, hs1_c, -, hs1_loc,
    ⟨vals_v, hbody_v, hcal_v, hrs_v, ⟨hargs_v, hlook_v, hrun_v⟩⟩, hr1⟩ := step_ro_call_g10 s
    (show opRoCallees (ofString "u256_is_zero") = true by decide) hcode (LocFrame.refl s) hret
  -- the u256_is_zero semantics: zw is the limb-or indicator of the value local
  have hzw_sem : ∀ q0 q1 q2 q3 : BitVec 64,
      s.locals.lookup (ofString "value") =
        some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
          .val (.word q2), .val (.word q3)]) →
      zw = if q0 ||| q1 ||| q2 ||| q3 = 0#64 then 1#64 else 0#64 := by
    intro q0 q1 q2 q3 hval
    have hvals : vals_v = [ValueHOL.rStruct [.val (.word q0), .val (.word q1),
        .val (.word q2), .val (.word q3)]] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hval] at hargs_v
      exact hargs_v.symm
    subst hvals
    have hmap := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "u256_is_zero") _ hbody_v hcal_v hrs_v hlook_v
    simp only [Flapjack.lookupCodeHOLExact, lookup_u256_is_zero_g10] at hmap
    split at hmap
    · rename_i hcond
      have heq := Option.some.inj hmap
      rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
      have hget := congrFun hloc.symm (ofString "a")
      have ha : (callEntryStateHOLFinite s hcal_v).locals.lookup (ofString "a") =
          some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
            .val (.word q2), .val (.word q3)]) := by
        have hget' : hcal_v.lookup (ofString "a") =
            some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
              .val (.word q2), .val (.word q3)]) := by
          simpa [List.map, List.zip, List.foldl] using hget
        simpa [callEntryStateHOLFinite] using hget'
      have hrun' : (evaluateHOLFiniteState (callEntryStateHOLFinite s hcal_v)
          (sourceFnBody Guest.Software.guestFn_u256_is_zero)).1 =
          some (.returned (.val (.word zw))) := hrun_v
      have hz := u256_is_zero_body_exact_g10 (callEntryStateHOLFinite s hcal_v)
        q0 q1 q2 q3 ha _ hrun'
      simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hz
      exact hz
    · cases hmap
  -- dec stipend = 0
  rw [evaluateHOLFiniteState_dec_total] at hr1; dsimp only at hr1
  have hc0 : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.const 0#64) = some (.val (.word 0#64)) := by simp [evalHOLExact]
  rw [hc0] at hr1; dsimp only at hr1
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hr1; dsimp only at hr1
  set sp := setVarHOLFinite (ofString "stipend") (.val (.word 0#64)) s1 with sp_def
  have hsp_vz : sp.locals.lookup (ofString "vz") = some (.val (.word zw)) := by
    rw [sp_def, sup_ne _ _ _ _ (show ofString "stipend" ≠ ofString "vz" by decide), hs1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hsp_stip : sp.locals.lookup (ofString "stipend") = some (.val (.word 0#64)) := by
    rw [sp_def]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hcmp : @evalHOLExact 64 F _ sp.toExact (fun x => Classical.propDecidable (sp.memaddrs x))
      (.cmp .equal (.var .local (ofString "vz")) (.const 0#64)) =
      some (.val (.word (if zw = 0#64 then 1#64 else 0#64))) := by
    simp [evalHOLExact, hsp_vz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hr1; dsimp only at hr1
  by_cases hz0 : zw = 0#64
  · refine ⟨2300#64, Or.inr rfl, fun _ q0 q1 q2 q3 hval => ?_⟩
    rw [if_pos hz0] at hr1
    rw [if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hr1
    rw [evaluateHOLFiniteState_assign] at hr1
    have h23 : @evalHOLExact 64 F _ sp.toExact (fun x => Classical.propDecidable (sp.memaddrs x))
        (.const 2300#64) = some (.val (.word 2300#64)) := by simp [evalHOLExact]
    rw [h23] at hr1; dsimp only at hr1
    have hvalid : sp.isValidValueHOLFinite .local (ofString "stipend")
        (.val (.word 2300#64)) = true := by
      simp [isValidValueHOLFinite_eq, isValidValueHOLExact, lookupKvarHOLExact,
        hsp_stip, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvalid] at hr1; dsimp only at hr1
    intro hcon
    have hor4 := hzw_sem q0 q1 q2 q3 hval
    rw [hz0] at hor4
    rw [if_pos hcon] at hor4
    exact absurd hor4 (by decide)
  · refine ⟨0#64, Or.inl rfl, fun h2300 => ?_⟩
    rw [if_neg hz0] at hr1
    rw [if_pos (show (0#64 : BitVec 64) = 0 by rfl)] at hr1
    rw [evaluateHOLFiniteState_skip] at hr1
    exact absurd h2300 (by decide)

private theorem add_sat_zero_zero_g10h {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word 0#64)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word 0#64)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    v = .val (.word 0#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  have hzz : ((0#64 : BitVec 64) + 0#64) = 0#64 := by norm_num
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (0#64 + 0#64))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0#64 + 0#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (0#64 + 0#64))) s with hs1_def
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (0#64 + 0#64))) := by
    simp [hs1_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word 0#64)) := by
    simp [hs1_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (0#64 + 0#64) < (0#64 : BitVec 64) then 1#64 else 0#64))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have h00lt : ¬ ((0#64 : BitVec 64) + 0#64 < (0#64 : BitVec 64)) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [if_neg h00lt] at hret
  rw [if_pos h00] at hret
  rw [evaluateHOLFiniteState_skip] at hret
  dsimp only at hret
  rw [evaluateHOLFiniteState_return] at hret
  have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.var .local (ofString "s")) = some (.val (.word (0#64 + 0#64))) := hs1_s
  rw [hev_s] at hret; dsimp only at hret
  have hsz1 : sizeOfShapeWithContextHOL s1.structs
      (shapeOfHOLExact (.val (.word (0#64 + 0#64)) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz1] at hret; dsimp only at hret
  rw [hzz] at hret
  injection hret with h1; injection h1 with hv
  exact hv.symm

/-- Full link for `calculate_message_call_gas` under `extra_gas = memory_cost = 0`:
the result is `[g, g + stipend]` with `g ≤ gas_left`, the stipend classification
`st ∈ {0, 2300}` where `2300` forces the limb-or of the `value` local nonzero,
and the exact relation `w1 ≤ w0 + st` (not merely `+ 2300`) needed by the
op_call gas ledger. -/
private theorem cmc_exact_link_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hex : s.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)))
    (hmc : s.locals.lookup (ofString "memory_cost") = some (.val (.word 0#64)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).1 =
      some (.returned v)) :
    ∃ (w0 w1 gl st : BitVec 64),
      v = ValueHOL.rStruct [.val (.word w0), .val (.word w1)] ∧
      s.locals.lookup (ofString "gas_left") = some (.val (.word gl)) ∧
      w0.toNat ≤ gl.toNat ∧ w1.toNat ≤ w0.toNat + st.toNat ∧
      (st = 0#64 ∨ (st = 2300#64 ∧ ∀ q0 q1 q2 q3 : BitVec 64,
        s.locals.lookup (ofString "value") =
          some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
            .val (.word q2), .val (.word q3)]) →
        (q0 ||| q1 ||| q2 ||| q3) ≠ 0#64)) := by
  have hbody : sourceFnBody Guest.Software.guestFn_calculate_message_call_gas =
      .decCall (ofString "vz") .one (ofString "u256_is_zero")
        [.var .local (ofString "value")]
        (.dec (ofString "stipend") .one (.const 0#64)
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "vz")) (.const 0#64))
              (.assign .local (ofString "stipend") (.const 2300#64))
              .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
                [.var .local (ofString "extra_gas"), .var .local (ofString "memory_cost")]
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need")))
                  (.decCall (ofString "c") .one (ofString "add_sat")
                      [.var .local (ofString "gas"), .var .local (ofString "extra_gas")]
                    (.decCall (ofString "s") .one (ofString "add_sat")
                        [.var .local (ofString "gas"), .var .local (ofString "stipend")]
                      (.return (.rstruct [.var .local (ofString "c"),
                        .var .local (ofString "s")]))))
                  .skip)
                (.dec (ofString "avail") .one
                    (.op .sub [.op .sub [.var .local (ofString "gas_left"),
                      .var .local (ofString "memory_cost")],
                      .var .local (ofString "extra_gas")])
                  (.dec (ofString "mx") .one
                      (.op .sub [.var .local (ofString "avail"),
                        .shift .lsr (.var .local (ofString "avail")) (.const 6#64)])
                    (.dec (ofString "g") .one (.var .local (ofString "gas"))
                      (.seq
                        (.ite (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g")))
                          (.assign .local (ofString "g") (.var .local (ofString "mx")))
                          .skip)
                        (.return (.rstruct
                          [.op .add [.var .local (ofString "g"),
                            .var .local (ofString "extra_gas")],
                           .op .add [.var .local (ofString "g"),
                            .var .local (ofString "stipend")]])))))))))) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  have h6 : BitVec.toNat (6#64 : BitVec 64) = 6 := by decide
  have lup_ne : ∀ (L : HolFiniteMapExact MlS (ValueHOL 64)) (nm k : MlS) (val : ValueHOL 64),
      nm ≠ k → (L.update (nm, val)).lookup k = L.lookup k := by
    intro L nm k val hne
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have sup_ne : ∀ (nm k : MlS) (val : ValueHOL 64) (st : PanSemStateFiniteExact 64 F),
      nm ≠ k → (setVarHOLFinite nm val st).locals.lookup k = st.locals.lookup k := by
    intro nm k val st hne
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have kup_ne : ∀ (nm k : MlS) (val : ValueHOL 64) (st : PanSemStateFiniteExact 64 F),
      nm ≠ k → (setKvarHOLFinite .local nm val st).locals.lookup k = st.locals.lookup k := by
    intro nm k val st hne
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc,
    ⟨vals_v, hbody_v, hcal_v, hrs_v, ⟨hargs_v, hlook_v, hrun_v⟩⟩, hr1⟩ :=
    step_ro_call_g10 s
    (show opRoCallees (ofString "u256_is_zero") = true by decide) hcode (LocFrame.refl s) hret
  have hzw_sem : ∀ q0 q1 q2 q3 : BitVec 64,
      s.locals.lookup (ofString "value") =
        some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
          .val (.word q2), .val (.word q3)]) →
      zw = if q0 ||| q1 ||| q2 ||| q3 = 0#64 then 1#64 else 0#64 := by
    intro q0 q1 q2 q3 hval
    have hvals : vals_v = [ValueHOL.rStruct [.val (.word q0), .val (.word q1),
        .val (.word q2), .val (.word q3)]] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hval] at hargs_v
      exact hargs_v.symm
    subst hvals
    have hmap := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "u256_is_zero") _ hbody_v hcal_v hrs_v hlook_v
    simp only [Flapjack.lookupCodeHOLExact, lookup_u256_is_zero_g10] at hmap
    split at hmap
    · rename_i hcond
      have heq := Option.some.inj hmap
      rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
      have hget := congrFun hloc.symm (ofString "a")
      have ha : (callEntryStateHOLFinite s hcal_v).locals.lookup (ofString "a") =
          some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
            .val (.word q2), .val (.word q3)]) := by
        have hget' : hcal_v.lookup (ofString "a") =
            some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
              .val (.word q2), .val (.word q3)]) := by
          simpa [List.map, List.zip, List.foldl] using hget
        simpa [callEntryStateHOLFinite] using hget'
      have hrun' : (evaluateHOLFiniteState (callEntryStateHOLFinite s hcal_v)
          (sourceFnBody Guest.Software.guestFn_u256_is_zero)).1 =
          some (.returned (.val (.word zw))) := hrun_v
      have hz := u256_is_zero_body_exact_g10 (callEntryStateHOLFinite s hcal_v)
        q0 q1 q2 q3 ha _ hrun'
      simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hz
      exact hz
    · cases hmap
  have hb_gas1 : s1.locals.lookup (ofString "gas") = s.locals.lookup (ofString "gas") := by
    rw [hs1_loc]; exact lup_ne _ _ _ _ (show ofString "vz" ≠ ofString "gas" by decide)
  have hb_gl1 : s1.locals.lookup (ofString "gas_left") = s.locals.lookup (ofString "gas_left") := by
    rw [hs1_loc]; exact lup_ne _ _ _ _ (show ofString "vz" ≠ ofString "gas_left" by decide)
  have hex1 : s1.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)) := by
    rw [hs1_loc, lup_ne _ _ _ _ (show ofString "vz" ≠ ofString "extra_gas" by decide)]
    exact hex
  have hmc1 : s1.locals.lookup (ofString "memory_cost") = some (.val (.word 0#64)) := by
    rw [hs1_loc, lup_ne _ _ _ _ (show ofString "vz" ≠ ofString "memory_cost" by decide)]
    exact hmc
  have htail : ∀ (sx : PanSemStateFiniteExact 64 F) (sw : BitVec 64) (T : ProgHOL 64),
      sx.code = originalRuntimeCode →
      LocFrame s sx →
      (sw = 0#64 ∨ sw = 2300#64) →
      sx.locals.lookup (ofString "stipend") = some (.val (.word sw)) →
      sx.locals.lookup (ofString "extra_gas") = some (.val (.word 0)) →
      sx.locals.lookup (ofString "memory_cost") = some (.val (.word 0)) →
      sx.locals.lookup (ofString "gas") = s.locals.lookup (ofString "gas") →
      sx.locals.lookup (ofString "gas_left") = s.locals.lookup (ofString "gas_left") →
      T = .decCall (ofString "need") .one (ofString "add_sat")
          [.var .local (ofString "extra_gas"), .var .local (ofString "memory_cost")]
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need")))
            (.decCall (ofString "c") .one (ofString "add_sat")
                [.var .local (ofString "gas"), .var .local (ofString "extra_gas")]
              (.decCall (ofString "s") .one (ofString "add_sat")
                  [.var .local (ofString "gas"), .var .local (ofString "stipend")]
                (.return (.rstruct [.var .local (ofString "c"),
                  .var .local (ofString "s")]))))
            .skip)
          (.dec (ofString "avail") .one
              (.op .sub [.op .sub [.var .local (ofString "gas_left"),
                .var .local (ofString "memory_cost")],
                .var .local (ofString "extra_gas")])
            (.dec (ofString "mx") .one
                (.op .sub [.var .local (ofString "avail"),
                  .shift .lsr (.var .local (ofString "avail")) (.const 6#64)])
              (.dec (ofString "g") .one (.var .local (ofString "gas"))
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g")))
                    (.assign .local (ofString "g") (.var .local (ofString "mx")))
                    .skip)
                  (.return (.rstruct
                    [.op .add [.var .local (ofString "g"),
                      .var .local (ofString "extra_gas")],
                     .op .add [.var .local (ofString "g"),
                      .var .local (ofString "stipend")]]))))))) →
      (evaluateHOLFiniteState sx T).1 = some (.returned v) →
      ∃ (w0 w1 gl : BitVec 64),
        v = ValueHOL.rStruct [.val (.word w0), .val (.word w1)] ∧
        s.locals.lookup (ofString "gas_left") = some (.val (.word gl)) ∧
        w0.toNat ≤ gl.toNat ∧ w1.toNat ≤ w0.toNat + sw.toNat := by
    intro sx sw T hsx_c hsx_lf hsw_case hsx_stip hsx_ex hsx_mc hb_gas hb_gl hT hr
    subst hT
    obtain ⟨nw, sn, hsn_c, hsn_lf, hsn_loc, ⟨vals_n, body_n, cal_n, rs_n, hargs_n, hl_orig_n, hrun_n⟩, hr⟩ :=
      step_ro_call_g10 s (by decide) hsx_c hsx_lf hr
    have hsn_gl : sn.locals.lookup (ofString "gas_left") =
        sx.locals.lookup (ofString "gas_left") := by
      rw [hsn_loc]; exact lup_ne _ _ _ _ (show ofString "need" ≠ ofString "gas_left" by decide)
    have hsn_gas : sn.locals.lookup (ofString "gas") =
        sx.locals.lookup (ofString "gas") := by
      rw [hsn_loc]; exact lup_ne _ _ _ _ (show ofString "need" ≠ ofString "gas" by decide)
    have hsn_ex : sn.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)) := by
      rw [hsn_loc, lup_ne _ _ _ _ (show ofString "need" ≠ ofString "extra_gas" by decide)]
      exact hsx_ex
    have hsn_mc : sn.locals.lookup (ofString "memory_cost") = some (.val (.word 0#64)) := by
      rw [hsn_loc, lup_ne _ _ _ _ (show ofString "need" ≠ ofString "memory_cost" by decide)]
      exact hsx_mc
    -- pin the add_sat arguments (extra_gas = 0, memory_cost = 0) and derive nw = 0
    have hvals_n : vals_n = [.val (.word 0#64), .val (.word 0#64)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsx_ex, hsx_mc] at hargs_n
      exact hargs_n.symm
    subst hvals_n
    obtain ⟨rfl, rfl, nw0', nw1', hvals_n2, hcal_a, hcal_b⟩ :=
      R14Shards.OpHandlersA.two_word_arg_lookup (show ofString "a" ≠ ofString "b" by decide)
        lookup_add_sat hl_orig_n
    simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hvals_n2
    rcases hvals_n2 with ⟨h0eq, h1eq⟩
    subst h0eq
    subst h1eq
    have hnw_ret := add_sat_zero_zero_g10h (sx.callEntryStateHOLFinite cal_n) hcal_a hcal_b
      (.val (.word nw)) hrun_n
    have hnw : nw = 0#64 := by
      injection hnw_ret with h1; injection h1 with h2
    subst hnw
    have hsn_need : sn.locals.lookup (ofString "need") = some (.val (.word 0#64)) := by
      rw [hsn_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr
    -- the ite (gas_left < need): need = 0, never fires
    obtain ⟨gval, hgl0w⟩ : ∃ gw : BitVec 64,
        sn.locals.lookup (ofString "gas_left") = some (.val (.word gw)) := by
      rcases hgl : sn.locals.lookup (ofString "gas_left") with _ | ⟨v⟩ | v | v
      · exfalso
        simp [evalHOLExact, hgl, hsn_need] at hr
      · rcases hv : v with ⟨gw⟩
        subst hv
        exact ⟨gw, rfl⟩
      · exfalso
        simp [evalHOLExact, hgl, hsn_need] at hr
      · exfalso
        simp [evalHOLExact, hgl, hsn_need] at hr
    have hcmp_gl : @evalHOLExact 64 F _ sn.toExact (fun x => Classical.propDecidable (sn.memaddrs x))
        (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need"))) =
        some (.val (.word (if gval.toNat < (0#64 : BitVec 64).toNat then 1#64 else 0#64))) := by
      simp [evalHOLExact, hgl0w, hsn_need, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_gl] at hr; dsimp only at hr
    have hgl0lt : ¬ (gval.toNat < (0#64 : BitVec 64).toNat) := by exact Nat.not_lt_zero _
    rw [if_neg hgl0lt] at hr
    rw [if_pos h00] at hr
    rw [evaluateHOLFiniteState_skip] at hr
    dsimp only at hr
    -- dec avail = gas_left - memory_cost - extra_gas
    rw [evaluateHOLFiniteState_dec_total] at hr; dsimp only at hr
    have heavail : @evalHOLExact 64 F _ sn.toExact (fun x => Classical.propDecidable (sn.memaddrs x))
        (.op .sub [.op .sub [.var .local (ofString "gas_left"),
          .var .local (ofString "memory_cost")], .var .local (ofString "extra_gas")]) =
        some (.val (.word ((gval - 0#64) - 0#64))) := by
      simp [evalHOLExact, evalListHOLExact, hgl0w, hsn_mc, hsn_ex, wordOpHOL, wordOp,
        valueIsWord, valueWord]
    rw [heavail] at hr; dsimp only at hr
    have hsh_avail : shapeEqHOL .one
        (shapeOfHOLExact (.val (.word ((gval - 0#64) - 0#64)))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_avail] at hr; dsimp only at hr
    set sa := setVarHOLFinite (ofString "avail") (.val (.word ((gval - 0#64) - 0#64))) sn with sa_def
    have hsa_c : sa.code = originalRuntimeCode := hsn_c
    have hsa_lf : LocFrame s sa := hsn_lf.with_locals_clock _ sn.clock
    have hsa_gl : sa.locals.lookup (ofString "gas_left") = some (.val (.word gval)) := by
      rw [sa_def, sup_ne _ _ _ _ (show ofString "avail" ≠ ofString "gas_left" by decide)]
      exact hgl0w
    have havail_lk : sa.locals.lookup (ofString "avail") =
        some (.val (.word ((gval - 0#64) - 0#64))) := by
      rw [sa_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- dec mx = avail - (avail >>> 6)
    rw [evaluateHOLFiniteState_dec_total] at hr; dsimp only at hr
    have hmx : @evalHOLExact 64 F _ sa.toExact (fun x => Classical.propDecidable (sa.memaddrs x))
        (.op .sub [.var .local (ofString "avail"),
          .shift .lsr (.var .local (ofString "avail")) (.const 6#64)]) =
        some (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) := by
      simp [evalHOLExact, evalListHOLExact, havail_lk, wordShiftHOL, wordOpHOL, wordOp,
        valueIsWord, valueWord, h6]
    rw [hmx] at hr; dsimp only at hr
    have hsh_mx : shapeEqHOL .one
        (shapeOfHOLExact (.val (.word (((gval - 0#64) - 0#64) -
          (((gval - 0#64) - 0#64) >>> 6))))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_mx] at hr; dsimp only at hr
    have hsh6 : ((((gval - 0#64) - 0#64) >>> 6 : BitVec 64)).toNat =
        ((gval - 0#64) - 0#64).toNat / 64 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hshiftle : (((gval - 0#64) - 0#64) >>> 6 : BitVec 64) ≤ ((gval - 0#64) - 0#64) := by
      rw [BitVec.le_def, hsh6]
      exact Nat.div_le_self _ _
    have hsub2 : ((gval - 0#64 : BitVec 64)).toNat ≤ gval.toNat := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.zero_le _))]
      show gval.toNat - 0 ≤ gval.toNat
      omega
    have hsub : (((gval - 0#64) - 0#64 : BitVec 64)).toNat ≤ gval.toNat := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.zero_le _))]
      show ((gval - 0#64 : BitVec 64)).toNat - 0 ≤ gval.toNat
      omega
    have hmx_le : ((((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)) : BitVec 64).toNat ≤
        gval.toNat := by
      rw [BitVec.toNat_sub_of_le hshiftle, hsh6]
      omega
    set sm := setVarHOLFinite (ofString "mx")
      (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) sa with sm_def
    have hsm_c : sm.code = originalRuntimeCode := hsa_c
    have hsm_lf : LocFrame s sm := hsa_lf.with_locals_clock _ sa.clock
    -- dec g = gas
    rw [evaluateHOLFiniteState_dec_total] at hr; dsimp only at hr
    have hsm_gas : sm.locals.lookup (ofString "gas") = s.locals.lookup (ofString "gas") := by
      rw [sm_def, sa_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsn_loc,
        show ofString "mx" ≠ ofString "gas" by decide,
        show ofString "avail" ≠ ofString "gas" by decide,
        show ofString "need" ≠ ofString "gas" by decide, hb_gas]
    obtain ⟨gfw, hgas_sm'⟩ : ∃ gw : BitVec 64,
        @evalHOLExact 64 F _ sm.toExact (fun x => Classical.propDecidable (sm.memaddrs x))
          (.var .local (ofString "gas")) = some (.val (.word gw)) := by
      rcases hgas_sm : @evalHOLExact 64 F _ sm.toExact (fun x => Classical.propDecidable (sm.memaddrs x))
          (.var .local (ofString "gas")) with _ | ⟨v⟩ | v | v
      · exfalso
        rw [hgas_sm] at hr
        simp [shapeOfHOLExact, shapeEqHOL] at hr
      · rcases hv : v with ⟨gw⟩
        subst hv
        exact ⟨gw, rfl⟩
      · exfalso
        rw [hgas_sm] at hr
        simp [shapeOfHOLExact, shapeEqHOL] at hr
      · exfalso
        rw [hgas_sm] at hr
        simp [shapeOfHOLExact, shapeEqHOL] at hr
    rw [hgas_sm'] at hr
    dsimp only at hr
    have hsh_g : shapeEqHOL .one (shapeOfHOLExact (.val (.word gfw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_g] at hr
    dsimp only at hr
    set sg := setVarHOLFinite (ofString "g") (.val (.word gfw)) sm with sg_def
    have hsg_c : sg.code = originalRuntimeCode := hsm_c
    have hsg_lf : LocFrame s sg := hsm_lf.with_locals_clock _ sm.clock
    have hsg_extra : sg.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)) := by
      rw [sg_def, sm_def, sa_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsn_loc,
        show ofString "g" ≠ ofString "extra_gas" by decide,
        show ofString "mx" ≠ ofString "extra_gas" by decide,
        show ofString "avail" ≠ ofString "extra_gas" by decide,
        show ofString "need" ≠ ofString "extra_gas" by decide, hsx_ex]
    have hsg_stip : sg.locals.lookup (ofString "stipend") = some (.val (.word sw)) := by
      rw [sg_def, sm_def, sa_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsn_loc,
        show ofString "g" ≠ ofString "stipend" by decide,
        show ofString "mx" ≠ ofString "stipend" by decide,
        show ofString "avail" ≠ ofString "stipend" by decide,
        show ofString "need" ≠ ofString "stipend" by decide, hsx_stip]
    have hsg_gl : sg.locals.lookup (ofString "gas_left") = some (.val (.word gval)) := by
      rw [sg_def, sm_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "g" ≠ ofString "gas_left" by decide,
        show ofString "mx" ≠ ofString "gas_left" by decide, hsa_gl]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr
    have hsg_mx : sg.locals.lookup (ofString "mx") =
        some (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) := by
      rw [sg_def, sm_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "g" ≠ ofString "mx" by decide]
    have hsg_g : sg.locals.lookup (ofString "g") = some (.val (.word gfw)) := by
      rw [sg_def, sm_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_g : @evalHOLExact 64 F _ sg.toExact (fun x => Classical.propDecidable (sg.memaddrs x))
        (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g"))) =
        some (.val (.word (if ((((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)) : BitVec 64).toNat <
          gfw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hsg_mx, hsg_g, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp [BitVec.lt_def]
    rw [hcmp_g] at hr; dsimp only at hr
    have hfin : ∀ (sf : PanSemStateFiniteExact 64 F) (gv : BitVec 64),
        sf.locals.lookup (ofString "g") = some (.val (.word gv)) →
        sf.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)) →
        sf.locals.lookup (ofString "stipend") = some (.val (.word sw)) →
        gv.toNat ≤ gval.toNat →
        (evaluateHOLFiniteState sf
          (.return (.rstruct [.op .add [.var .local (ofString "g"),
            .var .local (ofString "extra_gas")],
            .op .add [.var .local (ofString "g"), .var .local (ofString "stipend")]]))).1 =
          some (.returned v) →
        ∃ (w0 w1 : BitVec 64),
          v = ValueHOL.rStruct [.val (.word w0), .val (.word w1)] ∧
          w0.toNat ≤ gval.toNat ∧ w1.toNat ≤ w0.toNat + sw.toNat := by
      intro sf gv hgv hex' hstip' hgv_le hretf
      rw [evaluateHOLFiniteState_return] at hretf
      have hev_ret : @evalHOLExact 64 F _ sf.toExact (fun x => Classical.propDecidable (sf.memaddrs x))
          (.rstruct [.op .add [.var .local (ofString "g"), .var .local (ofString "extra_gas")],
            .op .add [.var .local (ofString "g"), .var .local (ofString "stipend")]]) =
          some (.rStruct [.val (.word (gv + 0#64)), .val (.word (gv + sw))]) := by
        simp [evalHOLExact, evalListHOLExact, hgv, hex', hstip', wordOpHOL, wordOp,
          valueIsWord, valueWord]
      rw [hev_ret] at hretf; dsimp only at hretf
      have hsz : sizeOfShapeWithContextHOL sf.structs
          (shapeOfHOLExact (.rStruct [.val (.word (gv + 0#64)), .val (.word (gv + sw))] : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
      rw [if_pos hsz] at hretf; dsimp only at hretf
      injection hretf with h1; injection h1 with hv
      refine ⟨gv + 0#64, gv + sw, hv.symm, ?_, ?_⟩
      · rw [BitVec.toNat_add]; simp; omega
      · rw [BitVec.toNat_add]
        simp only [BitVec.add_zero]
        exact Nat.mod_le _ _
    by_cases hmxlt : ((((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)) : BitVec 64).toNat <
        gfw.toNat
    · rw [if_pos hmxlt] at hr; rw [if_neg h10] at hr
      rw [evaluateHOLFiniteState_assign] at hr
      have hmx_ev : @evalHOLExact 64 F _ sg.toExact (fun x => Classical.propDecidable (sg.memaddrs x))
          (.var .local (ofString "mx")) =
          some (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) := by
        simp only [evalHOLExact, hsg_mx]
      rw [hmx_ev] at hr
      dsimp only at hr
      have hvalid_g : sg.isValidValueHOLFinite .local (ofString "g")
          (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) = true := by
        simp [isValidValueHOLFinite_eq, isValidValueHOLExact, lookupKvarHOLExact,
          hsg_g, shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hvalid_g] at hr
      dsimp only at hr
      obtain ⟨w0, w1, hveq, hw0, hw1⟩ :=
        hfin (setKvarHOLFinite .local (ofString "g")
          (.val (.word (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)))) sg)
          (((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6))
          (by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          (by rw [kup_ne _ _ _ _ (show ofString "g" ≠ ofString "extra_gas" by decide)]; exact hsg_extra)
          (by rw [kup_ne _ _ _ _ (show ofString "g" ≠ ofString "stipend" by decide)]; exact hsg_stip)
          hmx_le hr
      refine ⟨w0, w1, gval, hveq, ?_, hw0, hw1⟩
      rw [← hb_gl, ← hsn_gl]; exact hgl0w
    · rw [if_neg hmxlt] at hr; rw [if_pos h00] at hr
      rw [evaluateHOLFiniteState_skip] at hr; dsimp only at hr
      have hle1 : gfw.toNat ≤ ((((gval - 0#64) - 0#64) - (((gval - 0#64) - 0#64) >>> 6)) : BitVec 64).toNat := by
        omega
      obtain ⟨w0, w1, hveq, hw0, hw1⟩ := hfin sg gfw hsg_g hsg_extra hsg_stip (by omega) hr
      refine ⟨w0, w1, gval, hveq, ?_, hw0, hw1⟩
      rw [← hb_gl, ← hsn_gl]; exact hgl0w
  rw [evaluateHOLFiniteState_dec_total] at hr1; dsimp only at hr1
  have hc0 : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.const 0#64) = some (.val (.word 0#64)) := by simp [evalHOLExact]
  rw [hc0] at hr1; dsimp only at hr1
  rw [if_pos hsh0] at hr1; dsimp only at hr1
  have hs1_z : s1.locals.lookup (ofString "vz") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  set s2 := setVarHOLFinite (ofString "stipend") (.val (.word 0#64)) s1 with s2_def
  have hs2_lf : LocFrame s s2 := hs1_lf.with_locals_clock _ s1.clock
  have hs2_z : s2.locals.lookup (ofString "vz") = some (.val (.word zw)) := by
    rw [s2_def, sup_ne _ _ _ _ (show ofString "stipend" ≠ ofString "vz" by decide)]
    exact hs1_z
  have hcmp_z : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
      (.cmp .equal (.var .local (ofString "vz")) (.const 0#64)) =
      some (.val (.word (if zw = 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs2_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  have hne_eg : ofString "stipend" ≠ ofString "extra_gas" := by decide
  have hne_mc : ofString "stipend" ≠ ofString "memory_cost" := by decide
  have hne_g : ofString "stipend" ≠ ofString "gas" := by decide
  have hne_gl : ofString "stipend" ≠ ofString "gas_left" := by decide
  by_cases hz0 : zw = 0#64
  · rw [if_pos hz0] at hr1; rw [if_neg h10] at hr1
    rw [evaluateHOLFiniteState_assign] at hr1
    have hcon2300 : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
        (.const 2300#64) = some (.val (.word 2300#64)) := by simp [evalHOLExact]
    rw [hcon2300] at hr1
    dsimp only at hr1
    have hs2_stip0 : s2.locals.lookup (ofString "stipend") = some (.val (.word 0#64)) := by
      rw [s2_def]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hvalid2300 : s2.isValidValueHOLFinite .local (ofString "stipend")
        (.val (.word 2300#64)) = true := by
      simp [isValidValueHOLFinite_eq, isValidValueHOLExact, lookupKvarHOLExact,
        hs2_stip0, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvalid2300] at hr1
    dsimp only at hr1
    obtain ⟨w0, w1, gl, hveq2, hgl2, hw0, hw1⟩ :=
      htail (setKvarHOLFinite .local (ofString "stipend") (.val (.word 2300#64)) s2) 2300#64 _
        hs1_c (hs2_lf.with_locals_clock _ s2.clock)
        (Or.inr rfl)
        (by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [kup_ne _ _ _ _ hne_eg, sup_ne _ _ _ _ hne_eg]; exact hex1)
        (by rw [kup_ne _ _ _ _ hne_mc, sup_ne _ _ _ _ hne_mc]; exact hmc1)
        (by rw [kup_ne _ _ _ _ hne_g, sup_ne _ _ _ _ hne_g]; exact hb_gas1)
        (by rw [kup_ne _ _ _ _ hne_gl, sup_ne _ _ _ _ hne_gl]; exact hb_gl1)
        rfl hr1
    refine ⟨w0, w1, gl, 2300#64, hveq2, hgl2, hw0, hw1, Or.inr ⟨rfl, ?_⟩⟩
    intro q0 q1 q2 q3 hval hcon
    have hor4 := hzw_sem q0 q1 q2 q3 hval
    rw [hz0] at hor4
    rw [if_pos hcon] at hor4
    exact absurd hor4 (by decide)
  · rw [if_neg hz0] at hr1; rw [if_pos h00] at hr1
    rw [evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨w0, w1, gl, hveq2, hgl2, hw0, hw1⟩ :=
      htail s2 0#64 _ hs1_c hs2_lf
        (Or.inl rfl)
        (by simp [s2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [s2_def, sup_ne _ _ _ _ hne_eg]; exact hex1)
        (by rw [s2_def, sup_ne _ _ _ _ hne_mc]; exact hmc1)
        (by rw [s2_def, sup_ne _ _ _ _ hne_g]; exact hb_gas1)
        (by rw [s2_def, sup_ne _ _ _ _ hne_gl]; exact hb_gl1)
        rfl hr1
    exact ⟨w0, w1, gl, 0#64, hveq2, hgl2, hw0, hw1, Or.inl rfl⟩

/-- Spec for `calculate_message_call_gas` under `extra_gas = memory_cost = 0`:
the result is a two-word record `[w0, w1]` with `w0 ≤ gas_left`,
`w1 ≤ w0 + st` for the stipend `st`, and the stipend classification
`st ∈ {0, 2300}` where `st = 2300` forces the limb-or of the `value` local
to be nonzero. -/
theorem epsA_cmc_g10 :
    EvmPreservingSpecA
      (fun s => s.locals.lookup (ofString "extra_gas") = some (.val (.word 0#64)) ∧
        s.locals.lookup (ofString "memory_cost") = some (.val (.word 0#64)))
      (fun s v post => LocFrame s post ∧
        ∃ gl w0 w1 st : BitVec 64,
          v = ValueHOL.rStruct [.val (.word w0), .val (.word w1)] ∧
          s.locals.lookup (ofString "gas_left") = some (.val (.word gl)) ∧
          w0.toNat ≤ gl.toNat ∧ w1.toNat ≤ w0.toNat + st.toNat ∧
          (st = 0#64 ∨ (st = 2300#64 ∧
            ∀ q0 q1 q2 q3 : BitVec 64,
              s.locals.lookup (ofString "value") =
                some (ValueHOL.rStruct [.val (.word q0), .val (.word q1),
                  .val (.word q2), .val (.word q3)]) →
              (q0 ||| q1 ||| q2 ||| q3) ≠ 0#64)))
      (ofString "calculate_message_call_gas") := by
  obtain ⟨_, hbody_key, hret_key, hlook_key, hrun_key⟩ :=
    epsA_calculate_message_call_gas_vals_g10
  rw [lookup_calculate_message_call_gas] at hlook_key
  have heq := Option.some.inj hlook_key
  rcases Prod.mk.inj heq with ⟨_, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hbb, hrr⟩
  subst hbb; subst hrr
  refine ⟨_, sourceFnBody Guest.Software.guestFn_calculate_message_call_gas,
    ShapeHOL.comb [.one, .one], lookup_calculate_message_call_gas, ?_⟩
  intro F s hcode hInv hWF hP hvals hnt
  have hro : readOnlyProg opRoCallees
      (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas) = true := by decide
  have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good
    (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas) hro s hcode
  have hres (hr : InitECandidate.Solver.Wave8GuestInv.Resumes (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).1) :
      let post := (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).2
      (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
        evmChain post = evmChain s ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
          LocFrame s post := by
    have hlf := hsafe.to_resumes hr
    dsimp only
    let post := (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).2
    have hInv_p : EvmInv post := by
      have h := InitECandidate.Solver.Wave8GuestInv.localsFree_evmInv s post.locals post.clock hInv
      rwa [← hlf] at h
    have hm : post.memory = s.memory := by
      change (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).2.memory = s.memory
      conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by
      change (evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn_calculate_message_call_gas)).2.globals = s.globals
      conv_lhs => rw [hlf]
    have hc := evm_congr hm hg
    exact ⟨⟨hInv_p, headMemChainWF_of_locFrame hWF hlf⟩,
      evmChain_congr hm hg, le_of_eq hc.2.1, hlf⟩
  refine ⟨fun v hv => ?_, fun hve => ?_⟩
  · obtain ⟨hret_case, -⟩ := hrun_key s hcode hInv hWF hP hvals hnt
    obtain ⟨⟨h1, h2⟩, h3, h4, hlf, -⟩ := hret_case v hv
    obtain ⟨w0, w1, gl, st, hveq, hgl_lk, hw0, hw1, hstcase⟩ :=
      cmc_exact_link_g10 s hcode hP.1 hP.2 v hv
    exact ⟨⟨h1, h2⟩, h3, h4, hlf, gl, w0, w1, st, hveq, hgl_lk, hw0, hw1, hstcase⟩
  · obtain ⟨v', hv⟩ := hve
    obtain ⟨⟨h1, h2⟩, h3, h4, -⟩ := hres (Or.inr ⟨_, v', hv, by decide⟩)
    exact ⟨⟨h1, h2⟩, h3, h4⟩

private theorem store_some_eq_error_g10h {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

private theorem evmInv_head_ev_bounds_g10h {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ heapEnd ∧ globN s "ev" + 280 ≤ 2 ^ 64 := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
  have hFW0 := hFW_all _ hhead
  have hin1 := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin2 := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  dsimp only at hin1 hin2
  have hfm1 := hAs.2.2.2.1
  have hfm2 := hAs.2.2.2.2.1
  rw [R11Shards.scratchStart_val] at hfm1
  rw [R11Shards.scratchEnd_val] at hin2
  rw [R11Shards.heapEnd_val]
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  rw [h264]
  exact ⟨by omega, by omega, by omega⟩

private theorem three_one_word_call_args_g10h {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem eval_seq_htab_set_ev_slot_unhit_g10h {F : Type}
    (s : PanSemStateFiniteExact 64 F) (off : Nat) (keyVar : MlS) (v_ret : ValueHOL 64)
    (hoff : off < 280)
    (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s)
    (ht0 : ∀ S, EvmInvAt s S → memW s (globN s "ev" + off) ∈ S)
    (hret : (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).1 = some (.returned v_ret)) :
    let post := (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).2
    ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧ R16Shards.IvlUnhit s post (ec.2, 104) := by
  dsimp only
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hret; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_g10h s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]))
        (.var .local keyVar) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hev_pos, _, hb_ev⟩ := evmInv_head_ev_bounds_g10h ⟨hAs, S, hInvAt⟩
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have htw_nat : tw.toNat = memW s (globN s "ev" + off) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + off)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        have hz_add : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
        rw [hz_add]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hevw_nat, h264,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + off)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + off))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      have ht0_S : memW s (globN s "ev" + off) ∈ S := ht0 S hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + off) := by
        simp [locN, hcal_t, htw_nat]
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩, ?_, ?_⟩
        · rw [hloc_ts]
          exact (R16Shards.StateRestoreEpilogue.htabWF_lc s entry_s.locals s.globals entry_s.clock _).mpr
            (hInvAt.1.1.2.1 _ ht0_S).1
        · rw [hloc_ts]
          intro i hi
          exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, _, _, _, hhp_s, _, hfr_s, _⟩ := hexit_s
      obtain ⟨⟨hT, _, _, _⟩, _, _, _, hFW_all, _, _, _, hFO_disj, _⟩ := hInvAt
      have hpost_mem : post_c.memory = cpost_s.memory := by
        rw [← hpost_c, hs2_eq]; rfl
      have hfr_sp : FrameOutside s post_c
          (htabFootprint s (memW s (globN s "ev" + off)))
          (globN s "heap_ptr", globN cpost_s "heap_ptr" - globN s "heap_ptr") := by
        intro a h1 h2
        rw [hpost_mem]
        exact hfr_s a h1 h2
      have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
      have hf_al2 : (globN cpost_s "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
        have := hAs.2.2.2.2.2.2.1; have := hAp_s.2.2.2.2.2.2.1; omega
      have ht0_al : ∀ j ∈ htabFootprint s (memW s (globN s "ev" + off)),
          j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
        have hw := ((hT.2.1 _ ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
      intro ec hec
      have hFW := hFW_all ec hec
      have h1 := hFW.1 (ec.1, 280) (by simp)
      have h2 := hFW.1 (ec.2, 104) (by simp)
      exact ⟨R16Shards.ivlUnhit_of_frameOutside ⟨h1.2.1, h1.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h1.1)),
             R16Shards.ivlUnhit_of_frameOutside ⟨h2.2.1, h2.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h2.1))⟩

theorem epsA_warm_address_keep32_g10 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "warm_address") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_warm_address
  have hlk_eq := lookup_warm_address.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_warm_address, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_address) (by decide) s hcode
  dsimp only at hs ⊢
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address) with ⟨r_wa, post⟩
  rw [hrun] at hs hv; dsimp only at hs hv ⊢
  obtain ⟨hInv_p, hch_p, hR_le, hg_p, hR_eq⟩ := hs.1 v hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  have hrun_b : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) = (r_wa, post) := by rwa [← hb]
  have hu : ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧
      R16Shards.IvlUnhit s post (ec.2, 104) := by
    have hu0 := eval_seq_htab_set_ev_slot_unhit_g10h s 168 (ofString "addr") v (by omega) hcode hInv
      (fun _ hIA => by
        have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
        exact (hIA.2.2.2.2.1 _ hhead).2.2.2.2.2.2.2.2.1)
      (by rw [hrun_b]; exact hv)
    dsimp only at hu0; rwa [hrun_b] at hu0
  have hev_eq : globN post "ev" = globN s "ev" :=
    OpHandlers.globN_eq_of_lookup_eq (hg_p (ofString "ev") (by decide)).symm
  have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    OpHandlers.globN_eq_of_lookup_eq (hg_p (ofString "frame_mem_ptr") (by decide)).symm
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  obtain ⟨-, -, hb_ev3⟩ := evmInv_head_ev_bounds_g10h hInv
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead
  have hev8 : globN s "ev" % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
  have h32 : memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) :=
    R16Shards.memW_eq_of_ivlUnhit (hu _ hhead).1 (by omega) hb_ev3 ⟨by omega, by omega⟩
  exact ⟨⟨hInv_p, headMemChainWF_of_unhit_g10 hInv hHMWF hch_p hu hev_eq hfmp_eq⟩, hch_p, hR_le, hg_p, hR_eq, h32⟩

end Group10

