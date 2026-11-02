import InitECandidate.Solver.Wave8Stage.WordCostCertificates
import InitECandidate.Solver.Wave8Stage.WordToStackCostEntry

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostEntryCertificate
open Flapjack WordSemStateFiniteExact WordToStackSourceCost WordCostEffects WordCostCertificates
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- Certificates for every actual code lookup, including indirect calls. -/
def CodeCertified {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (dest : Option Nat) (xs : List (WordLocW width)) (sizes : Spt Nat)
    (values : List (WordLocW width)) (body : WordLangProgHOL (BitVec width)) (frame : Option Nat),
    wordSemFindCode dest xs code sizes = some (values,body,frame) →
    ∃ effects, Derives defs terminal body effects ∧ Subeffects effects (defs dest)

def TerminalOracle {F : Type}
    (terminal : Basis.Pure.MlString.MlString → Bool) (oracle : HolOracle F) : Prop :=
  ∀ (ffi : HolFfiState F) name, ffi.oracle = oracle → terminal name = true →
    ∀ config bytes, ∃ event, callFFIHOL ffi (.extCall name) config bytes = .final event

/-- Every entry result is paid by the entry tick when its callee's signed
summary is at most one. This bounds the actual simulation's source cost. -/
theorem entryCost_bound {width : Nat} [NeZero width] {C F : Type}
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (codeNoInstall : WordProps.noInstallCode code)
    (codeCertificates : CodeCertified defs terminal code)
    (terminalCalls : TerminalOracle terminal oracle)
    (start : Nat) (s : WordSemStateFiniteExact width C F)
    (world : s.code = code ∧ s.ffi.oracle = oracle)
    (entryBound : ∀ exit, AtMost (defs (some start) exit) 1)
    (ne : (evaluate (.call none (some start) [0] none) s).1 ≠ some .error)
    (nt : (evaluate (.call none (some start) [0] none) s).1 ≠ some .timeOut) :
    sourceCost (.call none (some start) [0] none) s ≤ s.clock := by
  have bounded := sound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
    (.call none (some start) [0] none) s _ (Derives.tail (some start) [0])
    (by simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]) world ne nt
  simp only [Fits,shift,netCost] at bounded
  generalize he : classify (evaluate (.call none (some start) [0] none) s).1 = exit at bounded
  cases hb : defs (some start) exit with
  | none => simp [hb,add,Covers] at bounded
  | some value =>
    have le := entryBound exit value ⟨value,hb,by omega⟩
    simp only [hb,add,covers_some] at bounded
    omega

/-- A genuine factor-two native entry budget, derived from syntactic cost
certificates and the compiler's native state relation. No cost inequality or
target execution is assumed. -/
theorem notTimeOut_two_mul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (registers start clock : Nat)
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (oracle : HolOracle F)
    (codeNoInstall : WordProps.noInstallCode code)
    (codeCertificates : CodeCertified defs terminal code)
    (terminalCalls : TerminalOracle terminal oracle)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (world : source.code = code ∧ source.ffi.oracle = oracle)
    (entryBound : ∀ exit, AtMost (defs (some start) exit) 1)
    (related : WordToStackProofs.stateRel ac registers 0 0 source target [] 0)
    (ne : (evaluate (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error)
    (nt : (evaluate (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {target with clock := 2*clock})).1 ≠ some .timeOut := by
  have bound := entryCost_bound defs terminal code oracle codeNoInstall codeCertificates terminalCalls
    start {source with clock := clock} world entryBound ne nt
  apply WordToStackCostEntry.notTimeOutOfCostBound ac start registers clock (2*clock)
    source target related ne nt
  dsimp only at bound
  omega

#print axioms entryCost_bound
#print axioms notTimeOut_two_mul
end InitECandidate.Solver.Wave8Stage.WordCostEntryCertificate
