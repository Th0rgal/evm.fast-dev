import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word192
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word193
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word194
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word195
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word196
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word197
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word198
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word199
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word200
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word201
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word202
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word203
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word204
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word205
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word206
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word207
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk08
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult192 := WordToStack.Native.compileProgNative
  riscvConfig false Word192.program PrefixChecks.Shard128.arity registers (.nil, 224)
theorem stackResult192_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word192.program
      PrefixChecks.Shard128.arity registers (prefixList, 224) =
    (stackResult192.1, stackResult192.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult192.2.2.1, 230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word192.program
    PrefixChecks.Shard128.arity registers prefixList 224
    stackResult192.1 stackResult192.2.1 stackResult192.2.2.1 230 stackResult192_eq
wave8_kernel_reduce stackResult193 := WordToStack.Native.compileProgNative
  riscvConfig false Word193.program PrefixChecks.Shard129.arity registers (.nil, 230)
theorem stackResult193_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word193.program
      PrefixChecks.Shard129.arity registers (prefixList, 230) =
    (stackResult193.1, stackResult193.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult193.2.2.1, 232)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word193.program
    PrefixChecks.Shard129.arity registers prefixList 230
    stackResult193.1 stackResult193.2.1 stackResult193.2.2.1 232 stackResult193_eq
wave8_kernel_reduce stackResult194 := WordToStack.Native.compileProgNative
  riscvConfig false Word194.program PrefixChecks.Shard130.arity registers (.nil, 232)
theorem stackResult194_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word194.program
      PrefixChecks.Shard130.arity registers (prefixList, 232) =
    (stackResult194.1, stackResult194.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult194.2.2.1, 233)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word194.program
    PrefixChecks.Shard130.arity registers prefixList 232
    stackResult194.1 stackResult194.2.1 stackResult194.2.2.1 233 stackResult194_eq
wave8_kernel_reduce stackResult195 := WordToStack.Native.compileProgNative
  riscvConfig false Word195.program PrefixChecks.Shard131.arity registers (.nil, 233)
theorem stackResult195_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word195.program
      PrefixChecks.Shard131.arity registers (prefixList, 233) =
    (stackResult195.1, stackResult195.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult195.2.2.1, 233)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word195.program
    PrefixChecks.Shard131.arity registers prefixList 233
    stackResult195.1 stackResult195.2.1 stackResult195.2.2.1 233 stackResult195_eq
wave8_kernel_reduce stackResult196 := WordToStack.Native.compileProgNative
  riscvConfig false Word196.program PrefixChecks.Shard132.arity registers (.nil, 233)
theorem stackResult196_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word196.program
      PrefixChecks.Shard132.arity registers (prefixList, 233) =
    (stackResult196.1, stackResult196.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult196.2.2.1, 233)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word196.program
    PrefixChecks.Shard132.arity registers prefixList 233
    stackResult196.1 stackResult196.2.1 stackResult196.2.2.1 233 stackResult196_eq
wave8_kernel_reduce stackResult197 := WordToStack.Native.compileProgNative
  riscvConfig false Word197.program PrefixChecks.Shard133.arity registers (.nil, 233)
theorem stackResult197_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word197.program
      PrefixChecks.Shard133.arity registers (prefixList, 233) =
    (stackResult197.1, stackResult197.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult197.2.2.1, 233)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word197.program
    PrefixChecks.Shard133.arity registers prefixList 233
    stackResult197.1 stackResult197.2.1 stackResult197.2.2.1 233 stackResult197_eq
wave8_kernel_reduce stackResult198 := WordToStack.Native.compileProgNative
  riscvConfig false Word198.program PrefixChecks.Shard134.arity registers (.nil, 233)
theorem stackResult198_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word198.program
      PrefixChecks.Shard134.arity registers (prefixList, 233) =
    (stackResult198.1, stackResult198.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult198.2.2.1, 235)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word198.program
    PrefixChecks.Shard134.arity registers prefixList 233
    stackResult198.1 stackResult198.2.1 stackResult198.2.2.1 235 stackResult198_eq
wave8_kernel_reduce stackResult199 := WordToStack.Native.compileProgNative
  riscvConfig false Word199.program PrefixChecks.Shard135.arity registers (.nil, 235)
theorem stackResult199_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word199.program
      PrefixChecks.Shard135.arity registers (prefixList, 235) =
    (stackResult199.1, stackResult199.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult199.2.2.1, 243)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word199.program
    PrefixChecks.Shard135.arity registers prefixList 235
    stackResult199.1 stackResult199.2.1 stackResult199.2.2.1 243 stackResult199_eq
wave8_kernel_reduce stackResult200 := WordToStack.Native.compileProgNative
  riscvConfig false Word200.program PrefixChecks.Shard136.arity registers (.nil, 243)
theorem stackResult200_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word200.program
      PrefixChecks.Shard136.arity registers (prefixList, 243) =
    (stackResult200.1, stackResult200.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult200.2.2.1, 251)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word200.program
    PrefixChecks.Shard136.arity registers prefixList 243
    stackResult200.1 stackResult200.2.1 stackResult200.2.2.1 251 stackResult200_eq
wave8_kernel_reduce stackResult201 := WordToStack.Native.compileProgNative
  riscvConfig false Word201.program PrefixChecks.Shard137.arity registers (.nil, 251)
theorem stackResult201_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word201.program
      PrefixChecks.Shard137.arity registers (prefixList, 251) =
    (stackResult201.1, stackResult201.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult201.2.2.1, 251)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word201.program
    PrefixChecks.Shard137.arity registers prefixList 251
    stackResult201.1 stackResult201.2.1 stackResult201.2.2.1 251 stackResult201_eq
wave8_kernel_reduce stackResult202 := WordToStack.Native.compileProgNative
  riscvConfig false Word202.program PrefixChecks.Shard138.arity registers (.nil, 251)
theorem stackResult202_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word202.program
      PrefixChecks.Shard138.arity registers (prefixList, 251) =
    (stackResult202.1, stackResult202.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult202.2.2.1, 253)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word202.program
    PrefixChecks.Shard138.arity registers prefixList 251
    stackResult202.1 stackResult202.2.1 stackResult202.2.2.1 253 stackResult202_eq
wave8_kernel_reduce stackResult203 := WordToStack.Native.compileProgNative
  riscvConfig false Word203.program PrefixChecks.Shard139.arity registers (.nil, 253)
theorem stackResult203_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word203.program
      PrefixChecks.Shard139.arity registers (prefixList, 253) =
    (stackResult203.1, stackResult203.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult203.2.2.1, 256)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word203.program
    PrefixChecks.Shard139.arity registers prefixList 253
    stackResult203.1 stackResult203.2.1 stackResult203.2.2.1 256 stackResult203_eq
wave8_kernel_reduce stackResult204 := WordToStack.Native.compileProgNative
  riscvConfig false Word204.program PrefixChecks.Shard140.arity registers (.nil, 256)
theorem stackResult204_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word204.program
      PrefixChecks.Shard140.arity registers (prefixList, 256) =
    (stackResult204.1, stackResult204.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult204.2.2.1, 257)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word204.program
    PrefixChecks.Shard140.arity registers prefixList 256
    stackResult204.1 stackResult204.2.1 stackResult204.2.2.1 257 stackResult204_eq
wave8_kernel_reduce stackResult205 := WordToStack.Native.compileProgNative
  riscvConfig false Word205.program PrefixChecks.Shard141.arity registers (.nil, 257)
theorem stackResult205_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word205.program
      PrefixChecks.Shard141.arity registers (prefixList, 257) =
    (stackResult205.1, stackResult205.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult205.2.2.1, 258)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word205.program
    PrefixChecks.Shard141.arity registers prefixList 257
    stackResult205.1 stackResult205.2.1 stackResult205.2.2.1 258 stackResult205_eq
wave8_kernel_reduce stackResult206 := WordToStack.Native.compileProgNative
  riscvConfig false Word206.program PrefixChecks.Shard142.arity registers (.nil, 258)
theorem stackResult206_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word206.program
      PrefixChecks.Shard142.arity registers (prefixList, 258) =
    (stackResult206.1, stackResult206.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult206.2.2.1, 258)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word206.program
    PrefixChecks.Shard142.arity registers prefixList 258
    stackResult206.1 stackResult206.2.1 stackResult206.2.2.1 258 stackResult206_eq
wave8_kernel_reduce stackResult207 := WordToStack.Native.compileProgNative
  riscvConfig false Word207.program PrefixChecks.Shard143.arity registers (.nil, 258)
theorem stackResult207_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word207.program
      PrefixChecks.Shard143.arity registers (prefixList, 258) =
    (stackResult207.1, stackResult207.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult207.2.2.1, 258)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word207.program
    PrefixChecks.Shard143.arity registers prefixList 258
    stackResult207.1 stackResult207.2.1 stackResult207.2.2.1 258 stackResult207_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard128.name, PrefixChecks.Shard128.arity, Word192.program),
  (PrefixChecks.Shard129.name, PrefixChecks.Shard129.arity, Word193.program),
  (PrefixChecks.Shard130.name, PrefixChecks.Shard130.arity, Word194.program),
  (PrefixChecks.Shard131.name, PrefixChecks.Shard131.arity, Word195.program),
  (PrefixChecks.Shard132.name, PrefixChecks.Shard132.arity, Word196.program),
  (PrefixChecks.Shard133.name, PrefixChecks.Shard133.arity, Word197.program),
  (PrefixChecks.Shard134.name, PrefixChecks.Shard134.arity, Word198.program),
  (PrefixChecks.Shard135.name, PrefixChecks.Shard135.arity, Word199.program),
  (PrefixChecks.Shard136.name, PrefixChecks.Shard136.arity, Word200.program),
  (PrefixChecks.Shard137.name, PrefixChecks.Shard137.arity, Word201.program),
  (PrefixChecks.Shard138.name, PrefixChecks.Shard138.arity, Word202.program),
  (PrefixChecks.Shard139.name, PrefixChecks.Shard139.arity, Word203.program),
  (PrefixChecks.Shard140.name, PrefixChecks.Shard140.arity, Word204.program),
  (PrefixChecks.Shard141.name, PrefixChecks.Shard141.arity, Word205.program),
  (PrefixChecks.Shard142.name, PrefixChecks.Shard142.arity, Word206.program),
  (PrefixChecks.Shard143.name, PrefixChecks.Shard143.arity, Word207.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard128.name, stackResult192.1),
  (PrefixChecks.Shard129.name, stackResult193.1),
  (PrefixChecks.Shard130.name, stackResult194.1),
  (PrefixChecks.Shard131.name, stackResult195.1),
  (PrefixChecks.Shard132.name, stackResult196.1),
  (PrefixChecks.Shard133.name, stackResult197.1),
  (PrefixChecks.Shard134.name, stackResult198.1),
  (PrefixChecks.Shard135.name, stackResult199.1),
  (PrefixChecks.Shard136.name, stackResult200.1),
  (PrefixChecks.Shard137.name, stackResult201.1),
  (PrefixChecks.Shard138.name, stackResult202.1),
  (PrefixChecks.Shard139.name, stackResult203.1),
  (PrefixChecks.Shard140.name, stackResult204.1),
  (PrefixChecks.Shard141.name, stackResult205.1),
  (PrefixChecks.Shard142.name, stackResult206.1),
  (PrefixChecks.Shard143.name, stackResult207.1)
]

noncomputable def frames : List Nat := [
  stackResult192.2.1,
  stackResult193.2.1,
  stackResult194.2.1,
  stackResult195.2.1,
  stackResult196.2.1,
  stackResult197.2.1,
  stackResult198.2.1,
  stackResult199.2.1,
  stackResult200.2.1,
  stackResult201.2.1,
  stackResult202.2.1,
  stackResult203.2.1,
  stackResult204.2.1,
  stackResult205.2.1,
  stackResult206.2.1,
  stackResult207.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult192.2.2.1) stackResult193.2.2.1) stackResult194.2.2.1) stackResult195.2.2.1) stackResult196.2.2.1) stackResult197.2.2.1) stackResult198.2.2.1) stackResult199.2.2.1) stackResult200.2.2.1) stackResult201.2.2.1) stackResult202.2.2.1) stackResult203.2.2.1) stackResult204.2.2.1) stackResult205.2.2.1) stackResult206.2.2.1) stackResult207.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 224) = (bodies, frames, (bitmapDelta, 258)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult192_from _
  apply compileWordToStack_cons
  · exact stackResult193_from _
  apply compileWordToStack_cons
  · exact stackResult194_from _
  apply compileWordToStack_cons
  · exact stackResult195_from _
  apply compileWordToStack_cons
  · exact stackResult196_from _
  apply compileWordToStack_cons
  · exact stackResult197_from _
  apply compileWordToStack_cons
  · exact stackResult198_from _
  apply compileWordToStack_cons
  · exact stackResult199_from _
  apply compileWordToStack_cons
  · exact stackResult200_from _
  apply compileWordToStack_cons
  · exact stackResult201_from _
  apply compileWordToStack_cons
  · exact stackResult202_from _
  apply compileWordToStack_cons
  · exact stackResult203_from _
  apply compileWordToStack_cons
  · exact stackResult204_from _
  apply compileWordToStack_cons
  · exact stackResult205_from _
  apply compileWordToStack_cons
  · exact stackResult206_from _
  apply compileWordToStack_cons
  · exact stackResult207_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 224) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 258)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 224 bodies frames bitmapDelta 258 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 128).take 16).zip
      [oracle192, oracle193, oracle194, oracle195, oracle196, oracle197, oracle198, oracle199, oracle200, oracle201, oracle202, oracle203, oracle204, oracle205, oracle206, oracle207]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle192 PrefixChecks.Shard128.entry,
    wordFunction oracle193 PrefixChecks.Shard129.entry,
    wordFunction oracle194 PrefixChecks.Shard130.entry,
    wordFunction oracle195 PrefixChecks.Shard131.entry,
    wordFunction oracle196 PrefixChecks.Shard132.entry,
    wordFunction oracle197 PrefixChecks.Shard133.entry,
    wordFunction oracle198 PrefixChecks.Shard134.entry,
    wordFunction oracle199 PrefixChecks.Shard135.entry,
    wordFunction oracle200 PrefixChecks.Shard136.entry,
    wordFunction oracle201 PrefixChecks.Shard137.entry,
    wordFunction oracle202 PrefixChecks.Shard138.entry,
    wordFunction oracle203 PrefixChecks.Shard139.entry,
    wordFunction oracle204 PrefixChecks.Shard140.entry,
    wordFunction oracle205 PrefixChecks.Shard141.entry,
    wordFunction oracle206 PrefixChecks.Shard142.entry,
    wordFunction oracle207 PrefixChecks.Shard143.entry] = words
  simp only [
    Word192.wordFunction_eq,
    Word193.wordFunction_eq,
    Word194.wordFunction_eq,
    Word195.wordFunction_eq,
    Word196.wordFunction_eq,
    Word197.wordFunction_eq,
    Word198.wordFunction_eq,
    Word199.wordFunction_eq,
    Word200.wordFunction_eq,
    Word201.wordFunction_eq,
    Word202.wordFunction_eq,
    Word203.wordFunction_eq,
    Word204.wordFunction_eq,
    Word205.wordFunction_eq,
    Word206.wordFunction_eq,
    Word207.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk08
