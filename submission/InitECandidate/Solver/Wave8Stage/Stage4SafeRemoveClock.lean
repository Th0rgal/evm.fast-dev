import InitECandidate.Solver.Wave8Stage.Remove.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.Wave8Stage.Stage4FullInitSafety

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.SafeRemoveClock
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
open Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure
open InitECandidate.Solver.Wave8Stage.Remove.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
variable {width : Nat} [NeZero width]

/-- Runtime reachability replaces the false requirement that every installed
body, including the unused store-constants stub, is store-constants-free. -/
structure Ready {C F : Type} (bad : Nat) (s : StackSemStateFiniteExact width C F) : Prop where
  state : StateSafe bad s
  code : CodeSafe bad s
  oracle : ∀ i, (s.compileOracle i).2.1 = []

theorem Ready.withClock {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) (k : Nat) : Ready bad { s with clock := k } :=
  ⟨h.state.withClock k, h.code, h.oracle⟩

theorem Ready.decClock {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) : Ready bad (decClock s) := h.withClock (s.clock - 1)

theorem Ready.setVar {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) (r : Nat) (v : WordLocW width) (hv : ValueSafe bad v) :
    Ready bad (setVar r v s) := ⟨h.state.setVar_safe r v hv, h.code, h.oracle⟩

theorem Ready.findCode {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) (dest : Nat ⊕ Nat) (hd : ∀ n, dest = .inl n → n ≠ bad)
    (p : HolProg width) (hl : StackSemControl.findCode dest s.regs s.code = some p) : ProgramSafe bad p :=
  codeSafe_findCode h.code s.regs h.state.regs dest hd p hl

theorem Ready.findCode_erase {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) (link : Nat) (dest : Nat ⊕ Nat) (hd : ∀ n, dest = .inl n → n ≠ bad)
    (p : HolProg width) (hl : StackSemControl.findCode dest (s.regs.eraseEq link) s.code = some p) : ProgramSafe bad p :=
  codeSafe_findCode h.code _ (mapSafe_erase h.state.regs link) dest hd p hl

theorem Ready.after {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : Ready bad s) (p : HolProg width) (hp : ProgramSafe bad p)
    (post : StackSemStateFiniteExact width C F) {result : Option (StackSemResult width)}
    (run : evaluate (p, s) = (result, post)) : Ready bad post := by
  have hs := evaluate_safe p s hp h.state h.code h.oracle
  have hc := codeSafe_evaluate p s h.code h.oracle
  rw [run] at hs hc
  exact ⟨hs, hc.1, hc.2⟩

/-- Normalize a recursive `ClockOk` case result. -/
local macro "normZ" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, post, hc, run, relation⟩
    refine ⟨clock, post, hc, run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

/-- Lift a zero-clock base case (`∃ postTarget, evaluate (comp …, target) = …`). -/
local macro "baseZ" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨post, run, relation⟩
    refine ⟨0, post, Or.inl rfl, by rw [Nat.zero_add]; exact run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

private theorem correctnessMeasureZ {bad : Nat} {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ProgramSafe bad program → Ready bad source →
      ∀ (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
      ∀ (_hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
        stateRelHOL jump bounds pointer source target ∧ StackProps.regBound program pointer),
      ∃ clock postTarget, ClockOk clock result ∧
        evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
          (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source hm hnost hcode result postSource target pointer bounds jump hypothesis
  subst hm
  cases program
  case storeConsts a b c => simp [ProgramSafe, LeafAllowed] at hnost
  case stackAlloc count =>
    obtain ⟨clock, post, hc1, hc0, run, rel⟩ :=
      InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackAllocZ
        source result postSource target count pointer bounds jump hypothesis
    have hok : ClockOk clock result := by
      rcases hypothesis with ⟨sr, ne, _, _⟩
      cases result with
      | none => exact Or.inl (hc0 rfl)
      | some v =>
        refine Or.inr ⟨hc1, ?_⟩
        rw [StackSemEvaluate.evaluate_stackAlloc] at sr
        split at sr
        · exact absurd (Prod.mk.inj sr).1.symm ne
        · split at sr
          · exact ⟨_, (Prod.mk.inj sr).1.symm⟩
          · exact absurd (Prod.mk.inj sr).1 (by simp)
    refine ⟨clock, post, hok, run, ?_⟩
    cases result with
    | none => exact rel
    | some v => cases v <;> exact rel
  all_goals first
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.FFI.compCorrectFFIZ _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers.compCorrectGetZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers.compCorrectSetZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Bitmap.compCorrectBitmapLoadZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Install.compCorrectInstallZ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.DataBufferWrite.compCorrectDataBufferWriteZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectSkipZ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectHaltZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectAllocZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny.compCorrectStackLoadAnyZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny.compCorrectStackStoreAnyZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Locations.compCorrectLocValueZ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectTickZ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectReturnZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectRaiseZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectBreakZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectContinueZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.ShMemOp.compCorrectShMemOpZ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackFreeZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.HeapOperation.compCorrectOpCurrHeapZ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackLoadZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackStoreZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions.compCorrectInstZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.CodeBufferWrite.compCorrectCodeBufferWriteZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize.compCorrectStackGetSizeZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.Wave8Stage.Remove.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize.compCorrectStackSetSizeZ _ _ _ _ _ _ _ _ hypothesis)
    | skip
  case seq first second =>
    simp only [ProgramSafe] at hnost
    refine (by normZ result using (Seq.compCorrectSeqZ first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normZ r using (ih _ (seq_first_measure_lt first second source) first source rfl hnost.1 hcode r post t k off j h)
    · intro middle firstRun
      have hcm := hcode.after first hnost.1 middle firstRun
      have smaller := seq_second_measure_lt first second source ((none : Option (StackSemResult width)), middle)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate first source
      rw [firstRun] at unclamped
      rw [unclamped] at smaller
      intro r post t k off j h
      normZ r using (ih _ smaller second middle rfl hnost.2 hcm r post t k off j h)
  case ite comparison register operand first second =>
    simp only [ProgramSafe] at hnost
    refine (by normZ result using (If.compCorrectIfZ comparison register operand first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro left right _ _ _ r post t k off j h
      normZ r using (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl hnost.1 hcode r post t k off j h)
    · intro left right _ _ _ r post t k off j h
      normZ r using (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl hnost.2 hcode r post t k off j h)
  case loop body =>
    have hb : ProgramSafe bad body := by simpa only [ProgramSafe] using hnost
    refine (by normZ result using (Loop.compCorrectLoopZ body source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normZ r using (ih _ (loop_body_measure_lt body source) body source rfl hb hcode r post t k off j h)
    · intro bodyResult middle bodyRun _ nonzero
      have hcm := (hcode.after body hb middle bodyRun).decClock
      have unclamped := StackSemEvaluateClock.fixClockEvaluate body source
      rw [bodyRun] at unclamped
      have smaller := loop_reentry_measure_lt body source (bodyResult, middle)
        (by simpa only [unclamped] using nonzero)
      rw [unclamped] at smaller
      intro r post t k off j h
      normZ r using (ih _ smaller (.loop body) (decClock middle) rfl hnost hcm r post t k off j h)
  case jumpLower first second label =>
    simp only [ProgramSafe] at hnost
    refine (by normZ result using (JumpLower.compCorrectJumpLowerZ first second label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro left right program _ _ _ hlk nonzero r post t k off j h
      normZ r using (ih _ (callee_measure_lt program (.jumpLower first second label) source nonzero) program (decClock source) rfl (hcode.code _ _ hnost hlk) (hcode.decClock) r post t k off j h)
  case rawCall label =>
    simp only [ProgramSafe] at hnost
    refine (by normZ result using (RawCall.compCorrectRawCallZ label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro frame body hlk nonzero r post t k off j h
      have hfb := hcode.code _ _ hnost hlk
      simp only [ProgramSafe] at hfb
      normZ r using (ih _ (callee_measure_lt body (.rawCall label) source nonzero) body (decClock source) rfl hfb.2 (hcode.decClock) r post t k off j h)
  case call ret dest handler =>
    have hcall := hnost
    rw [ProgramSafe.eq_def] at hcall
    have hret : ∀ body link l1 l2, ret = some (body, link, l1, l2) → ProgramSafe bad body := by
      intro body link l1 l2 e
      subst ret
      exact hcall.2.1.1
    have hlab : ∀ body link l1 l2, ret = some (body, link, l1, l2) → l1 ≠ bad := by
      intro body link l1 l2 e
      subst ret
      exact hcall.2.1.2
    have hhd : ∀ hb hl1 hl2, handler = some (hb, hl1, hl2) → ProgramSafe bad hb := by
      intro hb hl1 hl2 e
      subst handler
      exact hcall.2.2
    refine (by normZ result using (CallAssembly.compCorrectCallZ ret dest handler source result postSource target pointer bounds jump ?_ ?_ ?_ hypothesis))
    · cases ret with
      | none =>
        intro program hlk _ nonzero r post t k off j h
        normZ r using (ih _ (callee_measure_lt program (.call none dest handler) source nonzero) program (decClock source) rfl (hcode.findCode dest hcall.1 program hlk) (hcode.decClock) r post t k off j h)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program hlk nonzero
        have smaller := callee_measure_lt program (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) source) nonzero
        intro r post t k off j h
        normZ r using (ih _ smaller program (decClock (setVar link (.loc l1 l2) source)) rfl (hcode.findCode_erase link dest hcall.1 program hlk) ((hcode.setVar link (.loc l1 l2) (hlab body link l1 l2 rfl)).decClock) r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program middle hlk nonzero calleeRun
        have hcm := ((hcode.setVar link (.loc l1 l2) (hlab body link l1 l2 rfl)).decClock).after program (hcode.findCode_erase link dest hcall.1 program hlk) middle calleeRun
        have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
        rw [calleeRun] at unclamped
        have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
          source link l1 l2 ((some (.result (.loc l1 l2)) : Option (StackSemResult width)), middle) nonzero
        rw [unclamped] at smaller
        intro r post t k off j h
        normZ r using (ih _ smaller body middle rfl (hret body link l1 l2 rfl) hcm r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases handler with
        | none => trivial
        | some handlerEntry =>
          rcases handlerEntry with ⟨handlerBody, hl1, hl2⟩
          intro program middle hlk nonzero calleeRun
          have hcm := ((hcode.setVar link (.loc l1 l2) (hlab body link l1 l2 rfl)).decClock).after program (hcode.findCode_erase link dest hcall.1 program hlk) middle calleeRun
          have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
          rw [calleeRun] at unclamped
          have smaller := call_continuation_measure_lt handlerBody
            (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
            source link l1 l2 ((some (.exception (.loc hl1 hl2)) : Option (StackSemResult width)), middle) nonzero
          rw [unclamped] at smaller
          intro r post t k off j h
          normZ r using (ih _ smaller handlerBody middle rfl (hhd handlerBody hl1 hl2 rfl) hcm r post t k off j h)

/-- StackRemove adds zero clock for safe reachable code, except at most one
tick on a final halt. Unreachable installed bodies are unrestricted. -/
theorem compCorrectZ {bad : Nat} {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hnost : ProgramSafe bad program) (hcode : Ready bad source)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound program pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer program,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  correctnessMeasureZ _ program source rfl hnost hcode result postSource target pointer bounds jump hypothesis


/-- The unfiltered StackRemove entry run preserves its exact result with at
most one additional tick, even though its table still contains stub 6. -/
theorem entry_result_add_one {C F : Type} {bad : Nat}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start k : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (hs : Ready bad source) (hn : start ≠ bad)
    (hrel : stateRelHOL jump bounds pointer source target)
    (hne : (evaluate (.call none (.inl start) none, { source with clock := k })).1 ≠ some .error)
    (hnt : (evaluate (.call none (.inl start) none, { source with clock := k })).1 ≠ some .timeOut) :
    (evaluate (.call none (.inl start) none, { target with clock := k + 1 })).1 =
      (evaluate (.call none (.inl start) none, { source with clock := k })).1 := by
  have hp : ProgramSafe bad (.call none (.inl start) none : HolProg width) := by
    simp [ProgramSafe, hn]
  have hr := StackRemove.RelationLaws.stateRelWithClock jump bounds pointer k source target hrel
  obtain ⟨extra, post, hb, run, _⟩ := compCorrectZ _ { source with clock := k } _ _
    { target with clock := k } pointer bounds jump hp (hs.withClock k)
    ⟨rfl, hne, hr, by simp [StackProps.regBound]⟩
  have hle : extra ≤ 1 := by rcases hb with rfl | ⟨hb, _⟩ <;> omega
  simp only [comp] at run
  have lifted := StackProps.evaluateAddClock (k + 1 - (extra + k)) _ _ _ _ ⟨run, hnt⟩
  have hc : extra + k + (k + 1 - (extra + k)) = k + 1 := by omega
  simpa only [hc, StackSemEvaluate.evaluate] using congrArg Prod.fst lifted


end InitECandidate.Solver.Wave8Stage.SafeRemoveClock
