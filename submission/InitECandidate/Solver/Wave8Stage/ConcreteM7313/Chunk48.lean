import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word832
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word833
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word834
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word835
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word836
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word837
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word838
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word839
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word840
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word841
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word842
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word843
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word844
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word845
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word846
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word847
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk48
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult832 := WordToStack.Native.compileProgNative
  riscvConfig false Word832.program PrefixChecks.Shard768.arity registers (.nil, 4127)
theorem stackResult832_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word832.program
      PrefixChecks.Shard768.arity registers (prefixList, 4127) =
    (stackResult832.1, stackResult832.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult832.2.2.1, 4142)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word832.program
    PrefixChecks.Shard768.arity registers prefixList 4127
    stackResult832.1 stackResult832.2.1 stackResult832.2.2.1 4142 stackResult832_eq
wave8_kernel_reduce stackResult833 := WordToStack.Native.compileProgNative
  riscvConfig false Word833.program PrefixChecks.Shard769.arity registers (.nil, 4142)
theorem stackResult833_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word833.program
      PrefixChecks.Shard769.arity registers (prefixList, 4142) =
    (stackResult833.1, stackResult833.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult833.2.2.1, 4147)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word833.program
    PrefixChecks.Shard769.arity registers prefixList 4142
    stackResult833.1 stackResult833.2.1 stackResult833.2.2.1 4147 stackResult833_eq
wave8_kernel_reduce stackResult834 := WordToStack.Native.compileProgNative
  riscvConfig false Word834.program PrefixChecks.Shard770.arity registers (.nil, 4147)
theorem stackResult834_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word834.program
      PrefixChecks.Shard770.arity registers (prefixList, 4147) =
    (stackResult834.1, stackResult834.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult834.2.2.1, 4155)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word834.program
    PrefixChecks.Shard770.arity registers prefixList 4147
    stackResult834.1 stackResult834.2.1 stackResult834.2.2.1 4155 stackResult834_eq
wave8_kernel_reduce stackResult835 := WordToStack.Native.compileProgNative
  riscvConfig false Word835.program PrefixChecks.Shard771.arity registers (.nil, 4155)
theorem stackResult835_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word835.program
      PrefixChecks.Shard771.arity registers (prefixList, 4155) =
    (stackResult835.1, stackResult835.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult835.2.2.1, 4157)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word835.program
    PrefixChecks.Shard771.arity registers prefixList 4155
    stackResult835.1 stackResult835.2.1 stackResult835.2.2.1 4157 stackResult835_eq
wave8_kernel_reduce stackResult836 := WordToStack.Native.compileProgNative
  riscvConfig false Word836.program PrefixChecks.Shard772.arity registers (.nil, 4157)
theorem stackResult836_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word836.program
      PrefixChecks.Shard772.arity registers (prefixList, 4157) =
    (stackResult836.1, stackResult836.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult836.2.2.1, 4180)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word836.program
    PrefixChecks.Shard772.arity registers prefixList 4157
    stackResult836.1 stackResult836.2.1 stackResult836.2.2.1 4180 stackResult836_eq
wave8_kernel_reduce stackResult837 := WordToStack.Native.compileProgNative
  riscvConfig false Word837.program PrefixChecks.Shard773.arity registers (.nil, 4180)
theorem stackResult837_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word837.program
      PrefixChecks.Shard773.arity registers (prefixList, 4180) =
    (stackResult837.1, stackResult837.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult837.2.2.1, 4198)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word837.program
    PrefixChecks.Shard773.arity registers prefixList 4180
    stackResult837.1 stackResult837.2.1 stackResult837.2.2.1 4198 stackResult837_eq
wave8_kernel_reduce stackResult838 := WordToStack.Native.compileProgNative
  riscvConfig false Word838.program PrefixChecks.Shard774.arity registers (.nil, 4198)
theorem stackResult838_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word838.program
      PrefixChecks.Shard774.arity registers (prefixList, 4198) =
    (stackResult838.1, stackResult838.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult838.2.2.1, 4202)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word838.program
    PrefixChecks.Shard774.arity registers prefixList 4198
    stackResult838.1 stackResult838.2.1 stackResult838.2.2.1 4202 stackResult838_eq
wave8_kernel_reduce stackResult839 := WordToStack.Native.compileProgNative
  riscvConfig false Word839.program PrefixChecks.Shard775.arity registers (.nil, 4202)
theorem stackResult839_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word839.program
      PrefixChecks.Shard775.arity registers (prefixList, 4202) =
    (stackResult839.1, stackResult839.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult839.2.2.1, 4205)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word839.program
    PrefixChecks.Shard775.arity registers prefixList 4202
    stackResult839.1 stackResult839.2.1 stackResult839.2.2.1 4205 stackResult839_eq
wave8_kernel_reduce stackResult840 := WordToStack.Native.compileProgNative
  riscvConfig false Word840.program PrefixChecks.Shard776.arity registers (.nil, 4205)
theorem stackResult840_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word840.program
      PrefixChecks.Shard776.arity registers (prefixList, 4205) =
    (stackResult840.1, stackResult840.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult840.2.2.1, 4208)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word840.program
    PrefixChecks.Shard776.arity registers prefixList 4205
    stackResult840.1 stackResult840.2.1 stackResult840.2.2.1 4208 stackResult840_eq
wave8_kernel_reduce stackResult841 := WordToStack.Native.compileProgNative
  riscvConfig false Word841.program PrefixChecks.Shard777.arity registers (.nil, 4208)
theorem stackResult841_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word841.program
      PrefixChecks.Shard777.arity registers (prefixList, 4208) =
    (stackResult841.1, stackResult841.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult841.2.2.1, 4208)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word841.program
    PrefixChecks.Shard777.arity registers prefixList 4208
    stackResult841.1 stackResult841.2.1 stackResult841.2.2.1 4208 stackResult841_eq
wave8_kernel_reduce stackResult842 := WordToStack.Native.compileProgNative
  riscvConfig false Word842.program PrefixChecks.Shard778.arity registers (.nil, 4208)
theorem stackResult842_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word842.program
      PrefixChecks.Shard778.arity registers (prefixList, 4208) =
    (stackResult842.1, stackResult842.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult842.2.2.1, 4214)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word842.program
    PrefixChecks.Shard778.arity registers prefixList 4208
    stackResult842.1 stackResult842.2.1 stackResult842.2.2.1 4214 stackResult842_eq
wave8_kernel_reduce stackResult843 := WordToStack.Native.compileProgNative
  riscvConfig false Word843.program PrefixChecks.Shard779.arity registers (.nil, 4214)
theorem stackResult843_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word843.program
      PrefixChecks.Shard779.arity registers (prefixList, 4214) =
    (stackResult843.1, stackResult843.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult843.2.2.1, 4222)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word843.program
    PrefixChecks.Shard779.arity registers prefixList 4214
    stackResult843.1 stackResult843.2.1 stackResult843.2.2.1 4222 stackResult843_eq
wave8_kernel_reduce stackResult844 := WordToStack.Native.compileProgNative
  riscvConfig false Word844.program PrefixChecks.Shard780.arity registers (.nil, 4222)
theorem stackResult844_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word844.program
      PrefixChecks.Shard780.arity registers (prefixList, 4222) =
    (stackResult844.1, stackResult844.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult844.2.2.1, 4226)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word844.program
    PrefixChecks.Shard780.arity registers prefixList 4222
    stackResult844.1 stackResult844.2.1 stackResult844.2.2.1 4226 stackResult844_eq
wave8_kernel_reduce stackResult845 := WordToStack.Native.compileProgNative
  riscvConfig false Word845.program PrefixChecks.Shard781.arity registers (.nil, 4226)
theorem stackResult845_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word845.program
      PrefixChecks.Shard781.arity registers (prefixList, 4226) =
    (stackResult845.1, stackResult845.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult845.2.2.1, 4232)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word845.program
    PrefixChecks.Shard781.arity registers prefixList 4226
    stackResult845.1 stackResult845.2.1 stackResult845.2.2.1 4232 stackResult845_eq
wave8_kernel_reduce stackResult846 := WordToStack.Native.compileProgNative
  riscvConfig false Word846.program PrefixChecks.Shard782.arity registers (.nil, 4232)
theorem stackResult846_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word846.program
      PrefixChecks.Shard782.arity registers (prefixList, 4232) =
    (stackResult846.1, stackResult846.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult846.2.2.1, 4235)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word846.program
    PrefixChecks.Shard782.arity registers prefixList 4232
    stackResult846.1 stackResult846.2.1 stackResult846.2.2.1 4235 stackResult846_eq
wave8_kernel_reduce stackResult847 := WordToStack.Native.compileProgNative
  riscvConfig false Word847.program PrefixChecks.Shard783.arity registers (.nil, 4235)
theorem stackResult847_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word847.program
      PrefixChecks.Shard783.arity registers (prefixList, 4235) =
    (stackResult847.1, stackResult847.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult847.2.2.1, 4240)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word847.program
    PrefixChecks.Shard783.arity registers prefixList 4235
    stackResult847.1 stackResult847.2.1 stackResult847.2.2.1 4240 stackResult847_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard768.name, PrefixChecks.Shard768.arity, Word832.program),
  (PrefixChecks.Shard769.name, PrefixChecks.Shard769.arity, Word833.program),
  (PrefixChecks.Shard770.name, PrefixChecks.Shard770.arity, Word834.program),
  (PrefixChecks.Shard771.name, PrefixChecks.Shard771.arity, Word835.program),
  (PrefixChecks.Shard772.name, PrefixChecks.Shard772.arity, Word836.program),
  (PrefixChecks.Shard773.name, PrefixChecks.Shard773.arity, Word837.program),
  (PrefixChecks.Shard774.name, PrefixChecks.Shard774.arity, Word838.program),
  (PrefixChecks.Shard775.name, PrefixChecks.Shard775.arity, Word839.program),
  (PrefixChecks.Shard776.name, PrefixChecks.Shard776.arity, Word840.program),
  (PrefixChecks.Shard777.name, PrefixChecks.Shard777.arity, Word841.program),
  (PrefixChecks.Shard778.name, PrefixChecks.Shard778.arity, Word842.program),
  (PrefixChecks.Shard779.name, PrefixChecks.Shard779.arity, Word843.program),
  (PrefixChecks.Shard780.name, PrefixChecks.Shard780.arity, Word844.program),
  (PrefixChecks.Shard781.name, PrefixChecks.Shard781.arity, Word845.program),
  (PrefixChecks.Shard782.name, PrefixChecks.Shard782.arity, Word846.program),
  (PrefixChecks.Shard783.name, PrefixChecks.Shard783.arity, Word847.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard768.name, stackResult832.1),
  (PrefixChecks.Shard769.name, stackResult833.1),
  (PrefixChecks.Shard770.name, stackResult834.1),
  (PrefixChecks.Shard771.name, stackResult835.1),
  (PrefixChecks.Shard772.name, stackResult836.1),
  (PrefixChecks.Shard773.name, stackResult837.1),
  (PrefixChecks.Shard774.name, stackResult838.1),
  (PrefixChecks.Shard775.name, stackResult839.1),
  (PrefixChecks.Shard776.name, stackResult840.1),
  (PrefixChecks.Shard777.name, stackResult841.1),
  (PrefixChecks.Shard778.name, stackResult842.1),
  (PrefixChecks.Shard779.name, stackResult843.1),
  (PrefixChecks.Shard780.name, stackResult844.1),
  (PrefixChecks.Shard781.name, stackResult845.1),
  (PrefixChecks.Shard782.name, stackResult846.1),
  (PrefixChecks.Shard783.name, stackResult847.1)
]

noncomputable def frames : List Nat := [
  stackResult832.2.1,
  stackResult833.2.1,
  stackResult834.2.1,
  stackResult835.2.1,
  stackResult836.2.1,
  stackResult837.2.1,
  stackResult838.2.1,
  stackResult839.2.1,
  stackResult840.2.1,
  stackResult841.2.1,
  stackResult842.2.1,
  stackResult843.2.1,
  stackResult844.2.1,
  stackResult845.2.1,
  stackResult846.2.1,
  stackResult847.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult832.2.2.1) stackResult833.2.2.1) stackResult834.2.2.1) stackResult835.2.2.1) stackResult836.2.2.1) stackResult837.2.2.1) stackResult838.2.2.1) stackResult839.2.2.1) stackResult840.2.2.1) stackResult841.2.2.1) stackResult842.2.2.1) stackResult843.2.2.1) stackResult844.2.2.1) stackResult845.2.2.1) stackResult846.2.2.1) stackResult847.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 4127) = (bodies, frames, (bitmapDelta, 4240)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult832_from _
  apply compileWordToStack_cons
  · exact stackResult833_from _
  apply compileWordToStack_cons
  · exact stackResult834_from _
  apply compileWordToStack_cons
  · exact stackResult835_from _
  apply compileWordToStack_cons
  · exact stackResult836_from _
  apply compileWordToStack_cons
  · exact stackResult837_from _
  apply compileWordToStack_cons
  · exact stackResult838_from _
  apply compileWordToStack_cons
  · exact stackResult839_from _
  apply compileWordToStack_cons
  · exact stackResult840_from _
  apply compileWordToStack_cons
  · exact stackResult841_from _
  apply compileWordToStack_cons
  · exact stackResult842_from _
  apply compileWordToStack_cons
  · exact stackResult843_from _
  apply compileWordToStack_cons
  · exact stackResult844_from _
  apply compileWordToStack_cons
  · exact stackResult845_from _
  apply compileWordToStack_cons
  · exact stackResult846_from _
  apply compileWordToStack_cons
  · exact stackResult847_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 4127) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4240)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 4127 bodies frames bitmapDelta 4240 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 768).take 16).zip
      [oracle832, oracle833, oracle834, oracle835, oracle836, oracle837, oracle838, oracle839, oracle840, oracle841, oracle842, oracle843, oracle844, oracle845, oracle846, oracle847]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle832 PrefixChecks.Shard768.entry,
    wordFunction oracle833 PrefixChecks.Shard769.entry,
    wordFunction oracle834 PrefixChecks.Shard770.entry,
    wordFunction oracle835 PrefixChecks.Shard771.entry,
    wordFunction oracle836 PrefixChecks.Shard772.entry,
    wordFunction oracle837 PrefixChecks.Shard773.entry,
    wordFunction oracle838 PrefixChecks.Shard774.entry,
    wordFunction oracle839 PrefixChecks.Shard775.entry,
    wordFunction oracle840 PrefixChecks.Shard776.entry,
    wordFunction oracle841 PrefixChecks.Shard777.entry,
    wordFunction oracle842 PrefixChecks.Shard778.entry,
    wordFunction oracle843 PrefixChecks.Shard779.entry,
    wordFunction oracle844 PrefixChecks.Shard780.entry,
    wordFunction oracle845 PrefixChecks.Shard781.entry,
    wordFunction oracle846 PrefixChecks.Shard782.entry,
    wordFunction oracle847 PrefixChecks.Shard783.entry] = words
  simp only [
    Word832.wordFunction_eq,
    Word833.wordFunction_eq,
    Word834.wordFunction_eq,
    Word835.wordFunction_eq,
    Word836.wordFunction_eq,
    Word837.wordFunction_eq,
    Word838.wordFunction_eq,
    Word839.wordFunction_eq,
    Word840.wordFunction_eq,
    Word841.wordFunction_eq,
    Word842.wordFunction_eq,
    Word843.wordFunction_eq,
    Word844.wordFunction_eq,
    Word845.wordFunction_eq,
    Word846.wordFunction_eq,
    Word847.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk48
