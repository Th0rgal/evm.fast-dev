import InitECandidate.Solver.Wave8Stage.WordCostControl
import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect
import Flapjack.Compiler.Backend.WordToWord.Proofs.Syntactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostCompilerControl
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm WordCostControl

/-- The exact optimization prefix of Word-to-Word, before allocation. The
selector uses its existing unconditionally certified executable rendering. -/
def preAllocation {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (twoRegisters : Bool) (arity : Nat) (program : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  let p := WordSimp.compileExp program
  let p := WordInst.instSelectExecutable ac (maxVarHOL p + 1) p
  let p := Flapjack.Compiler.Backend.WordAlloc.fullSsaCcTrans arity p
  let p := Flapjack.WordAlloc.removeDeadProg p
  let p := WordCse.wordCommonSubexpElim p
  let p := WordCopy.copyProp p
  let p := WordInst.threeToTwoRegProg twoRegisters p
  let p := WordUnreach.removeUnreach p
  Flapjack.WordAlloc.removeDeadProg p

/-- All earlier optimizer effects are retained by using their actual output;
only register allocation is projected away by its checked invariant. -/
theorem erase_compileSingle {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (twoRegisters : Bool) (registers algorithm name arity : Nat)
    (program : WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat)) :
    erase (WordToWord.compileSingle twoRegisters registers algorithm ac
      ((name,arity,program),colour)).2.2 =
      erase (preAllocation ac twoRegisters arity program) := by
  simpa only [WordToWord.compileSingle,preAllocation,WordInst.instSelectExecutable_eq] using
    erase_wordAlloc name ac algorithm registers (preAllocation ac twoRegisters arity program) colour

/-- The final cleanup is identical for a source with no MustTerminate blocks,
as established by the original Word-to-Word syntactic theorem. -/
theorem erase_fullCompileSingle {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (twoRegisters : Bool) (registers algorithm name arity : Nat)
    (program : WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat))
    (noMt : noMtSubprogsHOL program = true) :
    erase (WordToWord.fullCompileSingle twoRegisters registers algorithm ac
      ((name,arity,program),colour)).2.2 =
      erase (preAllocation ac twoRegisters arity program) := by
  rw [WordToWord.no_mt_full_compile_single _ _ _ _ _ noMt]
  exact erase_compileSingle ac twoRegisters registers algorithm name arity program colour

def project {width : Nat} [NeZero width]
    (entry : Nat × Nat × WordLangProgHOL (BitVec width)) : Nat × Nat × Control :=
  (entry.1,entry.2.1,erase entry.2.2)

def preProject {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (twoRegisters : Bool) (entry : Nat × Nat × WordLangProgHOL (BitVec width)) : Nat × Nat × Control :=
  (entry.1,entry.2.1,erase (preAllocation ac twoRegisters entry.2.1 entry.2.2))

private theorem fullCompileSingle_project {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (twoRegisters : Bool) (registers algorithm : Nat)
    (entry : Nat × Nat × WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat))
    (noMt : noMtSubprogsHOL entry.2.2 = true) :
    project (WordToWord.fullCompileSingle twoRegisters registers algorithm ac (entry,colour)) =
      preProject ac twoRegisters entry := by
  rcases entry with ⟨name,arity,program⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact erase_fullCompileSingle ac twoRegisters registers algorithm name arity program colour noMt

private theorem zip_project {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (twoRegisters : Bool) (registers algorithm : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (colours : List (Option (Spt Nat))) (length : colours.length = programs.length)
    (noMt : ∀ entry ∈ programs, noMtSubprogsHOL entry.2.2 = true) :
    ((programs.zip colours).map (WordToWord.fullCompileSingle twoRegisters registers algorithm ac)).map project =
      programs.map (preProject ac twoRegisters) := by
  induction programs generalizing colours with
  | nil => simp
  | cons entry rest ih =>
    cases colours with
    | nil => simp at length
    | cons colour colours =>
      simp only [List.zip_cons_cons,List.map_cons]
      rw [fullCompileSingle_project ac twoRegisters registers algorithm entry colour
        (noMt entry (by simp))]
      congr 1
      apply ih colours (by simpa using length)
      intro p member
      exact noMt p (List.mem_cons_of_mem _ member)

/-- Exact cost-control projection of the complete Word-to-Word output. It is
independent of the consumed allocation oracles, without discarding any of the
preceding optimization passes. This allows checking one concrete prefix per
function rather than every possible colouring. -/
theorem compile_project {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noMt : ∀ entry ∈ programs, noMtSubprogsHOL entry.2.2 = true) :
    (WordToWord.compile wc ac programs).2.map project =
      programs.map (preProject ac ac.twoRegArith) := by
  change ((programs.zip (WordToWord.nextNOracle programs.length wc.colOracle).1).map
    (WordToWord.fullCompileSingle ac.twoRegArith (ac.regCount - (5+ac.avoidRegs.length)) wc.regAlg ac)).map
      project = _
  exact zip_project ac ac.twoRegArith _ wc.regAlg programs _
    (WordToWord.nextNOracle_length _ _) noMt

#print axioms erase_compileSingle
#print axioms erase_fullCompileSingle
#print axioms compile_project
end InitECandidate.Solver.Wave8Stage.WordCostCompilerControl
