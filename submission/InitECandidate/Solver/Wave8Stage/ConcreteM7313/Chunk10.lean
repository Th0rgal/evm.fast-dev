import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word224
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word225
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word226
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word227
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word228
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word229
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word230
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word231
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word232
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word233
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word234
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word235
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word236
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word237
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word238
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word239
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk10
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult224 := WordToStack.Native.compileProgNative
  riscvConfig false Word224.program PrefixChecks.Shard160.arity registers (.nil, 298)
theorem stackResult224_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word224.program
      PrefixChecks.Shard160.arity registers (prefixList, 298) =
    (stackResult224.1, stackResult224.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult224.2.2.1, 323)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word224.program
    PrefixChecks.Shard160.arity registers prefixList 298
    stackResult224.1 stackResult224.2.1 stackResult224.2.2.1 323 stackResult224_eq
wave8_kernel_reduce stackResult225 := WordToStack.Native.compileProgNative
  riscvConfig false Word225.program PrefixChecks.Shard161.arity registers (.nil, 323)
theorem stackResult225_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word225.program
      PrefixChecks.Shard161.arity registers (prefixList, 323) =
    (stackResult225.1, stackResult225.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult225.2.2.1, 353)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word225.program
    PrefixChecks.Shard161.arity registers prefixList 323
    stackResult225.1 stackResult225.2.1 stackResult225.2.2.1 353 stackResult225_eq
wave8_kernel_reduce stackResult226 := WordToStack.Native.compileProgNative
  riscvConfig false Word226.program PrefixChecks.Shard162.arity registers (.nil, 353)
theorem stackResult226_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word226.program
      PrefixChecks.Shard162.arity registers (prefixList, 353) =
    (stackResult226.1, stackResult226.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult226.2.2.1, 358)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word226.program
    PrefixChecks.Shard162.arity registers prefixList 353
    stackResult226.1 stackResult226.2.1 stackResult226.2.2.1 358 stackResult226_eq
wave8_kernel_reduce stackResult227 := WordToStack.Native.compileProgNative
  riscvConfig false Word227.program PrefixChecks.Shard163.arity registers (.nil, 358)
theorem stackResult227_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word227.program
      PrefixChecks.Shard163.arity registers (prefixList, 358) =
    (stackResult227.1, stackResult227.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult227.2.2.1, 375)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word227.program
    PrefixChecks.Shard163.arity registers prefixList 358
    stackResult227.1 stackResult227.2.1 stackResult227.2.2.1 375 stackResult227_eq
wave8_kernel_reduce stackResult228 := WordToStack.Native.compileProgNative
  riscvConfig false Word228.program PrefixChecks.Shard164.arity registers (.nil, 375)
theorem stackResult228_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word228.program
      PrefixChecks.Shard164.arity registers (prefixList, 375) =
    (stackResult228.1, stackResult228.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult228.2.2.1, 382)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word228.program
    PrefixChecks.Shard164.arity registers prefixList 375
    stackResult228.1 stackResult228.2.1 stackResult228.2.2.1 382 stackResult228_eq
wave8_kernel_reduce stackResult229 := WordToStack.Native.compileProgNative
  riscvConfig false Word229.program PrefixChecks.Shard165.arity registers (.nil, 382)
theorem stackResult229_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word229.program
      PrefixChecks.Shard165.arity registers (prefixList, 382) =
    (stackResult229.1, stackResult229.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult229.2.2.1, 386)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word229.program
    PrefixChecks.Shard165.arity registers prefixList 382
    stackResult229.1 stackResult229.2.1 stackResult229.2.2.1 386 stackResult229_eq
wave8_kernel_reduce stackResult230 := WordToStack.Native.compileProgNative
  riscvConfig false Word230.program PrefixChecks.Shard166.arity registers (.nil, 386)
theorem stackResult230_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word230.program
      PrefixChecks.Shard166.arity registers (prefixList, 386) =
    (stackResult230.1, stackResult230.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult230.2.2.1, 396)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word230.program
    PrefixChecks.Shard166.arity registers prefixList 386
    stackResult230.1 stackResult230.2.1 stackResult230.2.2.1 396 stackResult230_eq
wave8_kernel_reduce stackResult231 := WordToStack.Native.compileProgNative
  riscvConfig false Word231.program PrefixChecks.Shard167.arity registers (.nil, 396)
theorem stackResult231_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word231.program
      PrefixChecks.Shard167.arity registers (prefixList, 396) =
    (stackResult231.1, stackResult231.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult231.2.2.1, 418)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word231.program
    PrefixChecks.Shard167.arity registers prefixList 396
    stackResult231.1 stackResult231.2.1 stackResult231.2.2.1 418 stackResult231_eq
wave8_kernel_reduce stackResult232 := WordToStack.Native.compileProgNative
  riscvConfig false Word232.program PrefixChecks.Shard168.arity registers (.nil, 418)
theorem stackResult232_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word232.program
      PrefixChecks.Shard168.arity registers (prefixList, 418) =
    (stackResult232.1, stackResult232.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult232.2.2.1, 423)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word232.program
    PrefixChecks.Shard168.arity registers prefixList 418
    stackResult232.1 stackResult232.2.1 stackResult232.2.2.1 423 stackResult232_eq
wave8_kernel_reduce stackResult233 := WordToStack.Native.compileProgNative
  riscvConfig false Word233.program PrefixChecks.Shard169.arity registers (.nil, 423)
theorem stackResult233_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word233.program
      PrefixChecks.Shard169.arity registers (prefixList, 423) =
    (stackResult233.1, stackResult233.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult233.2.2.1, 428)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word233.program
    PrefixChecks.Shard169.arity registers prefixList 423
    stackResult233.1 stackResult233.2.1 stackResult233.2.2.1 428 stackResult233_eq
wave8_kernel_reduce stackResult234 := WordToStack.Native.compileProgNative
  riscvConfig false Word234.program PrefixChecks.Shard170.arity registers (.nil, 428)
theorem stackResult234_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word234.program
      PrefixChecks.Shard170.arity registers (prefixList, 428) =
    (stackResult234.1, stackResult234.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult234.2.2.1, 431)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word234.program
    PrefixChecks.Shard170.arity registers prefixList 428
    stackResult234.1 stackResult234.2.1 stackResult234.2.2.1 431 stackResult234_eq
wave8_kernel_reduce stackResult235 := WordToStack.Native.compileProgNative
  riscvConfig false Word235.program PrefixChecks.Shard171.arity registers (.nil, 431)
theorem stackResult235_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word235.program
      PrefixChecks.Shard171.arity registers (prefixList, 431) =
    (stackResult235.1, stackResult235.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult235.2.2.1, 443)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word235.program
    PrefixChecks.Shard171.arity registers prefixList 431
    stackResult235.1 stackResult235.2.1 stackResult235.2.2.1 443 stackResult235_eq
wave8_kernel_reduce stackResult236 := WordToStack.Native.compileProgNative
  riscvConfig false Word236.program PrefixChecks.Shard172.arity registers (.nil, 443)
theorem stackResult236_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word236.program
      PrefixChecks.Shard172.arity registers (prefixList, 443) =
    (stackResult236.1, stackResult236.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult236.2.2.1, 446)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word236.program
    PrefixChecks.Shard172.arity registers prefixList 443
    stackResult236.1 stackResult236.2.1 stackResult236.2.2.1 446 stackResult236_eq
wave8_kernel_reduce stackResult237 := WordToStack.Native.compileProgNative
  riscvConfig false Word237.program PrefixChecks.Shard173.arity registers (.nil, 446)
theorem stackResult237_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word237.program
      PrefixChecks.Shard173.arity registers (prefixList, 446) =
    (stackResult237.1, stackResult237.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult237.2.2.1, 454)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word237.program
    PrefixChecks.Shard173.arity registers prefixList 446
    stackResult237.1 stackResult237.2.1 stackResult237.2.2.1 454 stackResult237_eq
wave8_kernel_reduce stackResult238 := WordToStack.Native.compileProgNative
  riscvConfig false Word238.program PrefixChecks.Shard174.arity registers (.nil, 454)
theorem stackResult238_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word238.program
      PrefixChecks.Shard174.arity registers (prefixList, 454) =
    (stackResult238.1, stackResult238.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult238.2.2.1, 456)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word238.program
    PrefixChecks.Shard174.arity registers prefixList 454
    stackResult238.1 stackResult238.2.1 stackResult238.2.2.1 456 stackResult238_eq
wave8_kernel_reduce stackResult239 := WordToStack.Native.compileProgNative
  riscvConfig false Word239.program PrefixChecks.Shard175.arity registers (.nil, 456)
theorem stackResult239_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word239.program
      PrefixChecks.Shard175.arity registers (prefixList, 456) =
    (stackResult239.1, stackResult239.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult239.2.2.1, 460)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word239.program
    PrefixChecks.Shard175.arity registers prefixList 456
    stackResult239.1 stackResult239.2.1 stackResult239.2.2.1 460 stackResult239_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard160.name, PrefixChecks.Shard160.arity, Word224.program),
  (PrefixChecks.Shard161.name, PrefixChecks.Shard161.arity, Word225.program),
  (PrefixChecks.Shard162.name, PrefixChecks.Shard162.arity, Word226.program),
  (PrefixChecks.Shard163.name, PrefixChecks.Shard163.arity, Word227.program),
  (PrefixChecks.Shard164.name, PrefixChecks.Shard164.arity, Word228.program),
  (PrefixChecks.Shard165.name, PrefixChecks.Shard165.arity, Word229.program),
  (PrefixChecks.Shard166.name, PrefixChecks.Shard166.arity, Word230.program),
  (PrefixChecks.Shard167.name, PrefixChecks.Shard167.arity, Word231.program),
  (PrefixChecks.Shard168.name, PrefixChecks.Shard168.arity, Word232.program),
  (PrefixChecks.Shard169.name, PrefixChecks.Shard169.arity, Word233.program),
  (PrefixChecks.Shard170.name, PrefixChecks.Shard170.arity, Word234.program),
  (PrefixChecks.Shard171.name, PrefixChecks.Shard171.arity, Word235.program),
  (PrefixChecks.Shard172.name, PrefixChecks.Shard172.arity, Word236.program),
  (PrefixChecks.Shard173.name, PrefixChecks.Shard173.arity, Word237.program),
  (PrefixChecks.Shard174.name, PrefixChecks.Shard174.arity, Word238.program),
  (PrefixChecks.Shard175.name, PrefixChecks.Shard175.arity, Word239.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard160.name, stackResult224.1),
  (PrefixChecks.Shard161.name, stackResult225.1),
  (PrefixChecks.Shard162.name, stackResult226.1),
  (PrefixChecks.Shard163.name, stackResult227.1),
  (PrefixChecks.Shard164.name, stackResult228.1),
  (PrefixChecks.Shard165.name, stackResult229.1),
  (PrefixChecks.Shard166.name, stackResult230.1),
  (PrefixChecks.Shard167.name, stackResult231.1),
  (PrefixChecks.Shard168.name, stackResult232.1),
  (PrefixChecks.Shard169.name, stackResult233.1),
  (PrefixChecks.Shard170.name, stackResult234.1),
  (PrefixChecks.Shard171.name, stackResult235.1),
  (PrefixChecks.Shard172.name, stackResult236.1),
  (PrefixChecks.Shard173.name, stackResult237.1),
  (PrefixChecks.Shard174.name, stackResult238.1),
  (PrefixChecks.Shard175.name, stackResult239.1)
]

noncomputable def frames : List Nat := [
  stackResult224.2.1,
  stackResult225.2.1,
  stackResult226.2.1,
  stackResult227.2.1,
  stackResult228.2.1,
  stackResult229.2.1,
  stackResult230.2.1,
  stackResult231.2.1,
  stackResult232.2.1,
  stackResult233.2.1,
  stackResult234.2.1,
  stackResult235.2.1,
  stackResult236.2.1,
  stackResult237.2.1,
  stackResult238.2.1,
  stackResult239.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult224.2.2.1) stackResult225.2.2.1) stackResult226.2.2.1) stackResult227.2.2.1) stackResult228.2.2.1) stackResult229.2.2.1) stackResult230.2.2.1) stackResult231.2.2.1) stackResult232.2.2.1) stackResult233.2.2.1) stackResult234.2.2.1) stackResult235.2.2.1) stackResult236.2.2.1) stackResult237.2.2.1) stackResult238.2.2.1) stackResult239.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 298) = (bodies, frames, (bitmapDelta, 460)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult224_from _
  apply compileWordToStack_cons
  · exact stackResult225_from _
  apply compileWordToStack_cons
  · exact stackResult226_from _
  apply compileWordToStack_cons
  · exact stackResult227_from _
  apply compileWordToStack_cons
  · exact stackResult228_from _
  apply compileWordToStack_cons
  · exact stackResult229_from _
  apply compileWordToStack_cons
  · exact stackResult230_from _
  apply compileWordToStack_cons
  · exact stackResult231_from _
  apply compileWordToStack_cons
  · exact stackResult232_from _
  apply compileWordToStack_cons
  · exact stackResult233_from _
  apply compileWordToStack_cons
  · exact stackResult234_from _
  apply compileWordToStack_cons
  · exact stackResult235_from _
  apply compileWordToStack_cons
  · exact stackResult236_from _
  apply compileWordToStack_cons
  · exact stackResult237_from _
  apply compileWordToStack_cons
  · exact stackResult238_from _
  apply compileWordToStack_cons
  · exact stackResult239_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 298) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 460)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 298 bodies frames bitmapDelta 460 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 160).take 16).zip
      [oracle224, oracle225, oracle226, oracle227, oracle228, oracle229, oracle230, oracle231, oracle232, oracle233, oracle234, oracle235, oracle236, oracle237, oracle238, oracle239]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle224 PrefixChecks.Shard160.entry,
    wordFunction oracle225 PrefixChecks.Shard161.entry,
    wordFunction oracle226 PrefixChecks.Shard162.entry,
    wordFunction oracle227 PrefixChecks.Shard163.entry,
    wordFunction oracle228 PrefixChecks.Shard164.entry,
    wordFunction oracle229 PrefixChecks.Shard165.entry,
    wordFunction oracle230 PrefixChecks.Shard166.entry,
    wordFunction oracle231 PrefixChecks.Shard167.entry,
    wordFunction oracle232 PrefixChecks.Shard168.entry,
    wordFunction oracle233 PrefixChecks.Shard169.entry,
    wordFunction oracle234 PrefixChecks.Shard170.entry,
    wordFunction oracle235 PrefixChecks.Shard171.entry,
    wordFunction oracle236 PrefixChecks.Shard172.entry,
    wordFunction oracle237 PrefixChecks.Shard173.entry,
    wordFunction oracle238 PrefixChecks.Shard174.entry,
    wordFunction oracle239 PrefixChecks.Shard175.entry] = words
  simp only [
    Word224.wordFunction_eq,
    Word225.wordFunction_eq,
    Word226.wordFunction_eq,
    Word227.wordFunction_eq,
    Word228.wordFunction_eq,
    Word229.wordFunction_eq,
    Word230.wordFunction_eq,
    Word231.wordFunction_eq,
    Word232.wordFunction_eq,
    Word233.wordFunction_eq,
    Word234.wordFunction_eq,
    Word235.wordFunction_eq,
    Word236.wordFunction_eq,
    Word237.wordFunction_eq,
    Word238.wordFunction_eq,
    Word239.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk10
