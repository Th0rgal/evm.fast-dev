import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Assembly
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function150

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function151
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard87

noncomputable abbrev program := Word151.program

theorem wordFunction_eq : wordFunction oracle151 entry = (name, arity, program) :=
  Word151.wordFunction_eq

noncomputable def stackResult : StackLang.HolProg 64 × Nat × (AppList (BitVec 64) × Nat) :=
  (.seq (.stackAlloc (Stack151Frame.frame - Stack151Frame.stackArguments))
    Stack151Parts.suffix0.1, Stack151Frame.frame, Stack151Parts.suffix0.2)

theorem stackResult_eq : WordToStack.Native.compileProgNative
    riscvConfig false program arity registers Function150.stackResult.2.2 = stackResult := by
  apply StackCompileComposition.compile_program
    riscvConfig false program arity registers Stack151Frame.maximum
    Function150.stackResult.2.2 Stack151Parts.suffix0.2 Stack151Parts.suffix0.1
    Stack151Frame.maximum_eq
  change WordToStack.Native.compNative riscvConfig false
    (Stack151Parts.transform PrefixChecks.Shard87.prefixProgram)
    Function150.stackResult.2.2
    (registers, Stack151Frame.frame, Stack151Frame.stackVariables) = Stack151Parts.suffix0
  rw [Word151ClashTree.prefix_eq]
  exact Stack151Parts.suffix0_eq

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function151
