import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPureSyntax
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256CallFacts
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256AddSemantics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

theorem memoryPureFunction_of_installed (name : MlS) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (shape : ShapeHOL)
    (installed : originalRuntimeCode.lookup name = some (parameters, body, shape))
    (hp : MemoryPure body) : MemoryPureFunction name := by
  intro values found callee rs hlk
  have he := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup name parameters
    body found shape rs values callee installed hlk
  subst found
  exact @hp

theorem memoryPure_noCalls (body : ProgHOL 64)
    (hs : memoryPureSyntax (fun _ => false) body = true) : MemoryPure body :=
  memoryPure_of_syntax (fun _ => false) (by intro n h; cases h) body hs

theorem u256Lt_memoryPure : MemoryPureFunction (ofString "u256_lt") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_u256_lt
  exact memoryPure_noCalls _ (by decide)

theorem u256Sub_memoryPure : MemoryPureFunction (ofString "u256_sub") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_u256_sub
  exact memoryPure_noCalls _ (by decide)

theorem u256Add_memoryPure : MemoryPureFunction (ofString "u256_add") := by
  apply memoryPureFunction_of_installed _ _ _ _ arith_lookup_u256_add
  exact memoryPure_noCalls _ (by decide)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
