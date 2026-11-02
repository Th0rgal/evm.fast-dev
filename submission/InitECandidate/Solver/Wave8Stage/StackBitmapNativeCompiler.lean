import InitECandidate.Solver.Wave8Stage.StackBitmapNativeHelpers
import Flapjack.Pancake.WordConvs.NoInstall

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapNativeCompiler
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm WordToStack.Native StackBitmapRefinement
open StackBitmapNativeHelpers

/-- Source fragment preserved by the native bitmap-refinement compiler. -/
def SourceSafe {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) : Prop :=
  noInstallSubprogsHOL p = true ∧ noAllocSubprogsHOL p = true


theorem comp_safe {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : SourceSafe program)
    (compiled : compNative conf perf program bs frame = (output,residual))
    (plain : perf = false) : Safe output := by
  subst perf
  have result := congrArg Prod.fst compiled
  cases program with
  | inst instruction =>
    simp only [compNative] at result
    rw [← result]
    exact inst_safe _ frame
  | move priority moves =>
    simp only [compNative] at result
    rw [← result]
    exact moves_safe _ frame
  | get destination name | locValue destination name =>
    simp only [compNative] at result
    rw [← result]
    exact write1_safe _ _ _ (fun _ => by trivial)
  | opCurrHeap operator destination source =>
    simp only [compNative] at result
    rw [← result, loads_safe]
    exact write1_safe _ _ _ (fun _ => by trivial)
  | set name exp =>
    cases name <;> cases exp <;>
      simp only [compNative] at result
    all_goals rw [← result]; first | trivial | rw [loads_safe]; trivial
  | install codeBuffer codeLength dataBuffer dataLength live =>
    simp [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at guard
  | shareInst operator name address =>
    simp only [compNative] at result
    cases h : expToAddrHOL address <;> simp only [h] at result
    all_goals rw [← result]
    · trivial
    · exact share_safe _ _ _ frame
  | alloc destination live =>
    simp [SourceSafe,noAllocSubprogsHOL,notCreatedSubprogsWithMemOp] at guard
  | mustTerminate body =>
    have bodyGuard : SourceSafe body := by
      simpa [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
    exact comp_safe conf false body bs frame output residual bodyGuard
      (by simpa only [compNative] using compiled) rfl
  | loop liveIn body liveOut =>
    have bodyGuard : SourceSafe body := by
      simpa [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
    have bodySafe := comp_safe conf false body bs frame
      (compNative conf false body bs frame).1 (compNative conf false body bs frame).2 bodyGuard rfl rfl
    simp only [compNative] at result
    rw [← result]
    exact bodySafe
  | seq first second | ite cmp reg ri first second =>
    have guards : SourceSafe first ∧ SourceSafe second := by
      simpa [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true, and_assoc, and_left_comm, and_comm] using guard
    have firstSafe := comp_safe conf false first bs frame
      (compNative conf false first bs frame).1 (compNative conf false first bs frame).2 guards.1 rfl rfl
    have secondSafe := comp_safe conf false second (compNative conf false first bs frame).2 frame
      (compNative conf false second (compNative conf false first bs frame).2 frame).1
      (compNative conf false second (compNative conf false first bs frame).2 frame).2 guards.2 rfl rfl
    simp only [compNative] at result
    rw [← result]
    first
      | simp [Safe, firstSafe, secondSafe]
      | cases ri with
        | reg n => simp [loads_safe, Safe, firstSafe, secondSafe]
        | imm i =>
          simp only []
          split <;> simp [loads_safe, Safe, firstSafe, secondSafe]
  | call returns destination args handler =>
    cases returns with
    | none =>
      simp only [compNative] at result
      rw [← result]
      simp only [Safe, dest_safe, seqStackFreeNative]
      split <;> simp [Safe]
    | some record =>
      match hRetRecord : record with
      | (values,live,retCode,label1,label2) =>
        cases handler with
        | none =>
          have retGuard : SourceSafe retCode := by
            simpa [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
          have retSafe := comp_safe conf false retCode (wLiveNative live bs frame).2 frame
            (compNative conf false retCode (wLiveNative live bs frame).2 frame).1
            (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 retGuard rfl rfl
          simp only [compNative] at result
          rw [← result]
          simp [Safe, dest_safe, live_safe,
            stackArgsNative, stackMove_safe, copyRet_safe, retSafe]
        | some record =>
          match hHandlerRecord : record with
          | (handleValue,handleCode,handleLabel1,handleLabel2) =>
            have guards : SourceSafe retCode ∧ SourceSafe handleCode := by
              simpa [SourceSafe, noInstallSubprogsHOL, noAllocSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true, and_assoc, and_left_comm, and_comm] using guard
            have retSafe := comp_safe conf false retCode (wLiveNative live bs frame).2 frame
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).1
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 guards.1 rfl rfl
            have handlerSafe := comp_safe conf false handleCode
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame
              (compNative conf false handleCode (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame).1
              (compNative conf false handleCode (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame).2 guards.2 rfl rfl
            simp only [compNative] at result
            rw [← result]
            simp [Safe, dest_safe, live_safe,
              pushHandlerNative, stackHandlerArgsNative, stackArgsNative,
              stackMove_safe, copyRet_safe, popHandlerNative, retSafe, handlerSafe]
  | skip =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | assign _ _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | store _ _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | raise _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | «break» _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | «continue» _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | tick =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | «return» _ _ =>
    simp only [compNative] at result
    rw [← result]
    simp only [loads_safe, seqStackFreeNative]
    split <;> simp [Safe]
  | storeConsts _ _ _ _ _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
  | codeBufferWrite _ _ =>
    simp only [compNative] at result
    rw [← result]
    rw [loads_safe]
    trivial
  | dataBufferWrite _ _ =>
    simp only [compNative] at result
    rw [← result]
    rw [loads_safe]
    trivial
  | ffi _ _ _ _ _ _ =>
    simp only [compNative] at result
    rw [← result]
    trivial
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

/-- The compiled frame prologue also lies in the refinement fragment. -/
theorem prog_safe {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (argc k : Nat)
    (bs : AppList (BitVec width) × Nat) (guard : SourceSafe p) :
    Safe (compileProgNative ac false p argc k bs).1 := by
  simp only [compileProgNative,Safe]
  exact ⟨True.intro,comp_safe ac false p bs _ _ _ guard rfl rfl⟩

/-- Every compiled association is safe, including shadowed labels. -/
theorem list_safe {width : Nat} [NeZero width] (ac : AsmConfigExact width) (k : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat)
    (guard : ∀ entry ∈ programs, SourceSafe entry.2.2) :
    ∀ entry ∈ (compileWordToStackNative ac false k programs bs).1, Safe entry.2 := by
  induction programs generalizing bs with
  | nil => simp [compileWordToStackNative]
  | cons first rest ih =>
    obtain ⟨name,argc,p⟩ := first
    simp only [compileWordToStackNative]
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact prog_safe ac p argc k bs (guard _ List.mem_cons_self)
    · exact ih _ (fun entry h => guard entry (List.mem_cons_of_mem _ h)) entry member

/-- The full native compiler, including both stubs, produces only code in
our evaluator refinement fragment. -/
theorem compile_codeSafe {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guard : ∀ entry ∈ programs, SourceSafe entry.2.2) :
    CodeSafe (sptFromAList (compileNative ac false programs).2.2.2) := by
  intro name body found
  rw [sptLookup_sptFromAList] at found
  have member := sptAListLookup_mem name _ body found
  simp only [compileNative,List.mem_cons,Prod.mk.injEq] at member
  rcases member with ⟨_,rfl⟩ | ⟨_,rfl⟩ | member
  · simp [raiseStubNative,Safe]
  · simp [storeConstsStubNative,Safe]
  · exact list_safe ac _ programs (.list [4],1) guard (name,body) member

end InitECandidate.Solver.Wave8Stage.StackBitmapNativeCompiler
