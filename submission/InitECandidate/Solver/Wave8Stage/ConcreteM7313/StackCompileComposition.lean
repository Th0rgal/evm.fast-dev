import Flapjack.Compiler.Backend.WordToStack.NativePrograms

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackCompileComposition
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem compile_seq (conf : AsmConfigExact 64) (perf : Bool)
    (first second : WordLangProgHOL (BitVec 64))
    (initial middle final : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (left right : HolProg 64)
    (hleft : WordToStack.Native.compNative conf perf first initial kf = (left, middle))
    (hright : WordToStack.Native.compNative conf perf second middle kf = (right, final)) :
    WordToStack.Native.compNative conf perf (.seq first second) initial kf =
      (.seq left right, final) := by
  simp only [WordToStack.Native.compNative, hleft, hright]

theorem compile_program (conf : AsmConfigExact 64) (perf : Bool)
    (program : WordLangProgHOL (BitVec 64)) (arguments registers maximum : Nat)
    (initial final : AppList (BitVec 64) × Nat) (body : HolProg 64)
    (hmax : maxVarHOL program = maximum)
    (hbody : WordToStack.Native.compNative conf perf program initial
      (registers,
        if max ((maximum / 2 + 1) - registers) (arguments - registers) = 0 then 0
        else max ((maximum / 2 + 1) - registers) (arguments - registers) + 1,
        max ((maximum / 2 + 1) - registers) (arguments - registers)) = (body, final)) :
    WordToStack.Native.compileProgNative conf perf program arguments registers initial =
      (.seq (.stackAlloc
        ((if max ((maximum / 2 + 1) - registers) (arguments - registers) = 0 then 0
          else max ((maximum / 2 + 1) - registers) (arguments - registers) + 1) -
          (arguments - registers))) body,
        (if max ((maximum / 2 + 1) - registers) (arguments - registers) = 0 then 0
          else max ((maximum / 2 + 1) - registers) (arguments - registers) + 1), final) := by
  simp only [WordToStack.Native.compileProgNative, hmax, hbody]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackCompileComposition
