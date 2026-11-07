import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word176
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word177
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word178
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word179
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word180
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word181
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word182
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word183
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word184
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word185
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word186
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word187
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word188
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word189
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word190
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word191
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk07
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult176 := WordToStack.Native.compileProgNative
  riscvConfig false Word176.program PrefixChecks.Shard112.arity registers (.nil, 196)
theorem stackResult176_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word176.program
      PrefixChecks.Shard112.arity registers (prefixList, 196) =
    (stackResult176.1, stackResult176.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult176.2.2.1, 198)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word176.program
    PrefixChecks.Shard112.arity registers prefixList 196
    stackResult176.1 stackResult176.2.1 stackResult176.2.2.1 198 stackResult176_eq
wave8_kernel_reduce stackResult177 := WordToStack.Native.compileProgNative
  riscvConfig false Word177.program PrefixChecks.Shard113.arity registers (.nil, 198)
theorem stackResult177_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word177.program
      PrefixChecks.Shard113.arity registers (prefixList, 198) =
    (stackResult177.1, stackResult177.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult177.2.2.1, 200)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word177.program
    PrefixChecks.Shard113.arity registers prefixList 198
    stackResult177.1 stackResult177.2.1 stackResult177.2.2.1 200 stackResult177_eq
wave8_kernel_reduce stackResult178 := WordToStack.Native.compileProgNative
  riscvConfig false Word178.program PrefixChecks.Shard114.arity registers (.nil, 200)
theorem stackResult178_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word178.program
      PrefixChecks.Shard114.arity registers (prefixList, 200) =
    (stackResult178.1, stackResult178.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult178.2.2.1, 200)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word178.program
    PrefixChecks.Shard114.arity registers prefixList 200
    stackResult178.1 stackResult178.2.1 stackResult178.2.2.1 200 stackResult178_eq
wave8_kernel_reduce stackResult179 := WordToStack.Native.compileProgNative
  riscvConfig false Word179.program PrefixChecks.Shard115.arity registers (.nil, 200)
theorem stackResult179_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word179.program
      PrefixChecks.Shard115.arity registers (prefixList, 200) =
    (stackResult179.1, stackResult179.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult179.2.2.1, 201)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word179.program
    PrefixChecks.Shard115.arity registers prefixList 200
    stackResult179.1 stackResult179.2.1 stackResult179.2.2.1 201 stackResult179_eq
wave8_kernel_reduce stackResult180 := WordToStack.Native.compileProgNative
  riscvConfig false Word180.program PrefixChecks.Shard116.arity registers (.nil, 201)
theorem stackResult180_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word180.program
      PrefixChecks.Shard116.arity registers (prefixList, 201) =
    (stackResult180.1, stackResult180.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult180.2.2.1, 201)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word180.program
    PrefixChecks.Shard116.arity registers prefixList 201
    stackResult180.1 stackResult180.2.1 stackResult180.2.2.1 201 stackResult180_eq
wave8_kernel_reduce stackResult181 := WordToStack.Native.compileProgNative
  riscvConfig false Word181.program PrefixChecks.Shard117.arity registers (.nil, 201)
theorem stackResult181_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word181.program
      PrefixChecks.Shard117.arity registers (prefixList, 201) =
    (stackResult181.1, stackResult181.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult181.2.2.1, 202)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word181.program
    PrefixChecks.Shard117.arity registers prefixList 201
    stackResult181.1 stackResult181.2.1 stackResult181.2.2.1 202 stackResult181_eq
wave8_kernel_reduce stackResult182 := WordToStack.Native.compileProgNative
  riscvConfig false Word182.program PrefixChecks.Shard118.arity registers (.nil, 202)
theorem stackResult182_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word182.program
      PrefixChecks.Shard118.arity registers (prefixList, 202) =
    (stackResult182.1, stackResult182.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult182.2.2.1, 206)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word182.program
    PrefixChecks.Shard118.arity registers prefixList 202
    stackResult182.1 stackResult182.2.1 stackResult182.2.2.1 206 stackResult182_eq
wave8_kernel_reduce stackResult183 := WordToStack.Native.compileProgNative
  riscvConfig false Word183.program PrefixChecks.Shard119.arity registers (.nil, 206)
theorem stackResult183_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word183.program
      PrefixChecks.Shard119.arity registers (prefixList, 206) =
    (stackResult183.1, stackResult183.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult183.2.2.1, 210)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word183.program
    PrefixChecks.Shard119.arity registers prefixList 206
    stackResult183.1 stackResult183.2.1 stackResult183.2.2.1 210 stackResult183_eq
wave8_kernel_reduce stackResult184 := WordToStack.Native.compileProgNative
  riscvConfig false Word184.program PrefixChecks.Shard120.arity registers (.nil, 210)
theorem stackResult184_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word184.program
      PrefixChecks.Shard120.arity registers (prefixList, 210) =
    (stackResult184.1, stackResult184.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult184.2.2.1, 210)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word184.program
    PrefixChecks.Shard120.arity registers prefixList 210
    stackResult184.1 stackResult184.2.1 stackResult184.2.2.1 210 stackResult184_eq
wave8_kernel_reduce stackResult185 := WordToStack.Native.compileProgNative
  riscvConfig false Word185.program PrefixChecks.Shard121.arity registers (.nil, 210)
theorem stackResult185_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word185.program
      PrefixChecks.Shard121.arity registers (prefixList, 210) =
    (stackResult185.1, stackResult185.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult185.2.2.1, 210)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word185.program
    PrefixChecks.Shard121.arity registers prefixList 210
    stackResult185.1 stackResult185.2.1 stackResult185.2.2.1 210 stackResult185_eq
wave8_kernel_reduce stackResult186 := WordToStack.Native.compileProgNative
  riscvConfig false Word186.program PrefixChecks.Shard122.arity registers (.nil, 210)
theorem stackResult186_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word186.program
      PrefixChecks.Shard122.arity registers (prefixList, 210) =
    (stackResult186.1, stackResult186.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult186.2.2.1, 212)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word186.program
    PrefixChecks.Shard122.arity registers prefixList 210
    stackResult186.1 stackResult186.2.1 stackResult186.2.2.1 212 stackResult186_eq
wave8_kernel_reduce stackResult187 := WordToStack.Native.compileProgNative
  riscvConfig false Word187.program PrefixChecks.Shard123.arity registers (.nil, 212)
theorem stackResult187_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word187.program
      PrefixChecks.Shard123.arity registers (prefixList, 212) =
    (stackResult187.1, stackResult187.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult187.2.2.1, 214)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word187.program
    PrefixChecks.Shard123.arity registers prefixList 212
    stackResult187.1 stackResult187.2.1 stackResult187.2.2.1 214 stackResult187_eq
wave8_kernel_reduce stackResult188 := WordToStack.Native.compileProgNative
  riscvConfig false Word188.program PrefixChecks.Shard124.arity registers (.nil, 214)
theorem stackResult188_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word188.program
      PrefixChecks.Shard124.arity registers (prefixList, 214) =
    (stackResult188.1, stackResult188.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult188.2.2.1, 215)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word188.program
    PrefixChecks.Shard124.arity registers prefixList 214
    stackResult188.1 stackResult188.2.1 stackResult188.2.2.1 215 stackResult188_eq
wave8_kernel_reduce stackResult189 := WordToStack.Native.compileProgNative
  riscvConfig false Word189.program PrefixChecks.Shard125.arity registers (.nil, 215)
theorem stackResult189_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word189.program
      PrefixChecks.Shard125.arity registers (prefixList, 215) =
    (stackResult189.1, stackResult189.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult189.2.2.1, 217)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word189.program
    PrefixChecks.Shard125.arity registers prefixList 215
    stackResult189.1 stackResult189.2.1 stackResult189.2.2.1 217 stackResult189_eq
wave8_kernel_reduce stackResult190 := WordToStack.Native.compileProgNative
  riscvConfig false Word190.program PrefixChecks.Shard126.arity registers (.nil, 217)
theorem stackResult190_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word190.program
      PrefixChecks.Shard126.arity registers (prefixList, 217) =
    (stackResult190.1, stackResult190.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult190.2.2.1, 218)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word190.program
    PrefixChecks.Shard126.arity registers prefixList 217
    stackResult190.1 stackResult190.2.1 stackResult190.2.2.1 218 stackResult190_eq
wave8_kernel_reduce stackResult191 := WordToStack.Native.compileProgNative
  riscvConfig false Word191.program PrefixChecks.Shard127.arity registers (.nil, 218)
theorem stackResult191_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word191.program
      PrefixChecks.Shard127.arity registers (prefixList, 218) =
    (stackResult191.1, stackResult191.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult191.2.2.1, 224)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word191.program
    PrefixChecks.Shard127.arity registers prefixList 218
    stackResult191.1 stackResult191.2.1 stackResult191.2.2.1 224 stackResult191_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard112.name, PrefixChecks.Shard112.arity, Word176.program),
  (PrefixChecks.Shard113.name, PrefixChecks.Shard113.arity, Word177.program),
  (PrefixChecks.Shard114.name, PrefixChecks.Shard114.arity, Word178.program),
  (PrefixChecks.Shard115.name, PrefixChecks.Shard115.arity, Word179.program),
  (PrefixChecks.Shard116.name, PrefixChecks.Shard116.arity, Word180.program),
  (PrefixChecks.Shard117.name, PrefixChecks.Shard117.arity, Word181.program),
  (PrefixChecks.Shard118.name, PrefixChecks.Shard118.arity, Word182.program),
  (PrefixChecks.Shard119.name, PrefixChecks.Shard119.arity, Word183.program),
  (PrefixChecks.Shard120.name, PrefixChecks.Shard120.arity, Word184.program),
  (PrefixChecks.Shard121.name, PrefixChecks.Shard121.arity, Word185.program),
  (PrefixChecks.Shard122.name, PrefixChecks.Shard122.arity, Word186.program),
  (PrefixChecks.Shard123.name, PrefixChecks.Shard123.arity, Word187.program),
  (PrefixChecks.Shard124.name, PrefixChecks.Shard124.arity, Word188.program),
  (PrefixChecks.Shard125.name, PrefixChecks.Shard125.arity, Word189.program),
  (PrefixChecks.Shard126.name, PrefixChecks.Shard126.arity, Word190.program),
  (PrefixChecks.Shard127.name, PrefixChecks.Shard127.arity, Word191.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard112.name, stackResult176.1),
  (PrefixChecks.Shard113.name, stackResult177.1),
  (PrefixChecks.Shard114.name, stackResult178.1),
  (PrefixChecks.Shard115.name, stackResult179.1),
  (PrefixChecks.Shard116.name, stackResult180.1),
  (PrefixChecks.Shard117.name, stackResult181.1),
  (PrefixChecks.Shard118.name, stackResult182.1),
  (PrefixChecks.Shard119.name, stackResult183.1),
  (PrefixChecks.Shard120.name, stackResult184.1),
  (PrefixChecks.Shard121.name, stackResult185.1),
  (PrefixChecks.Shard122.name, stackResult186.1),
  (PrefixChecks.Shard123.name, stackResult187.1),
  (PrefixChecks.Shard124.name, stackResult188.1),
  (PrefixChecks.Shard125.name, stackResult189.1),
  (PrefixChecks.Shard126.name, stackResult190.1),
  (PrefixChecks.Shard127.name, stackResult191.1)
]

noncomputable def frames : List Nat := [
  stackResult176.2.1,
  stackResult177.2.1,
  stackResult178.2.1,
  stackResult179.2.1,
  stackResult180.2.1,
  stackResult181.2.1,
  stackResult182.2.1,
  stackResult183.2.1,
  stackResult184.2.1,
  stackResult185.2.1,
  stackResult186.2.1,
  stackResult187.2.1,
  stackResult188.2.1,
  stackResult189.2.1,
  stackResult190.2.1,
  stackResult191.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult176.2.2.1) stackResult177.2.2.1) stackResult178.2.2.1) stackResult179.2.2.1) stackResult180.2.2.1) stackResult181.2.2.1) stackResult182.2.2.1) stackResult183.2.2.1) stackResult184.2.2.1) stackResult185.2.2.1) stackResult186.2.2.1) stackResult187.2.2.1) stackResult188.2.2.1) stackResult189.2.2.1) stackResult190.2.2.1) stackResult191.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 196) = (bodies, frames, (bitmapDelta, 224)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult176_from _
  apply compileWordToStack_cons
  · exact stackResult177_from _
  apply compileWordToStack_cons
  · exact stackResult178_from _
  apply compileWordToStack_cons
  · exact stackResult179_from _
  apply compileWordToStack_cons
  · exact stackResult180_from _
  apply compileWordToStack_cons
  · exact stackResult181_from _
  apply compileWordToStack_cons
  · exact stackResult182_from _
  apply compileWordToStack_cons
  · exact stackResult183_from _
  apply compileWordToStack_cons
  · exact stackResult184_from _
  apply compileWordToStack_cons
  · exact stackResult185_from _
  apply compileWordToStack_cons
  · exact stackResult186_from _
  apply compileWordToStack_cons
  · exact stackResult187_from _
  apply compileWordToStack_cons
  · exact stackResult188_from _
  apply compileWordToStack_cons
  · exact stackResult189_from _
  apply compileWordToStack_cons
  · exact stackResult190_from _
  apply compileWordToStack_cons
  · exact stackResult191_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 196) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 224)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 196 bodies frames bitmapDelta 224 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 112).take 16).zip
      [oracle176, oracle177, oracle178, oracle179, oracle180, oracle181, oracle182, oracle183, oracle184, oracle185, oracle186, oracle187, oracle188, oracle189, oracle190, oracle191]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle176 PrefixChecks.Shard112.entry,
    wordFunction oracle177 PrefixChecks.Shard113.entry,
    wordFunction oracle178 PrefixChecks.Shard114.entry,
    wordFunction oracle179 PrefixChecks.Shard115.entry,
    wordFunction oracle180 PrefixChecks.Shard116.entry,
    wordFunction oracle181 PrefixChecks.Shard117.entry,
    wordFunction oracle182 PrefixChecks.Shard118.entry,
    wordFunction oracle183 PrefixChecks.Shard119.entry,
    wordFunction oracle184 PrefixChecks.Shard120.entry,
    wordFunction oracle185 PrefixChecks.Shard121.entry,
    wordFunction oracle186 PrefixChecks.Shard122.entry,
    wordFunction oracle187 PrefixChecks.Shard123.entry,
    wordFunction oracle188 PrefixChecks.Shard124.entry,
    wordFunction oracle189 PrefixChecks.Shard125.entry,
    wordFunction oracle190 PrefixChecks.Shard126.entry,
    wordFunction oracle191 PrefixChecks.Shard127.entry] = words
  simp only [
    Word176.wordFunction_eq,
    Word177.wordFunction_eq,
    Word178.wordFunction_eq,
    Word179.wordFunction_eq,
    Word180.wordFunction_eq,
    Word181.wordFunction_eq,
    Word182.wordFunction_eq,
    Word183.wordFunction_eq,
    Word184.wordFunction_eq,
    Word185.wordFunction_eq,
    Word186.wordFunction_eq,
    Word187.wordFunction_eq,
    Word188.wordFunction_eq,
    Word189.wordFunction_eq,
    Word190.wordFunction_eq,
    Word191.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk07
