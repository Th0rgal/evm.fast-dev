import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word160
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word161
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word162
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word163
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word164
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word165
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word166
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word167
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word168
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word169
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word170
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word171
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word172
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word173
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word174
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word175
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk06
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult160 := WordToStack.Native.compileProgNative
  riscvConfig false Word160.program PrefixChecks.Shard96.arity registers (.nil, 146)
theorem stackResult160_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word160.program
      PrefixChecks.Shard96.arity registers (prefixList, 146) =
    (stackResult160.1, stackResult160.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult160.2.2.1, 147)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word160.program
    PrefixChecks.Shard96.arity registers prefixList 146
    stackResult160.1 stackResult160.2.1 stackResult160.2.2.1 147 stackResult160_eq
wave8_kernel_reduce stackResult161 := WordToStack.Native.compileProgNative
  riscvConfig false Word161.program PrefixChecks.Shard97.arity registers (.nil, 147)
theorem stackResult161_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word161.program
      PrefixChecks.Shard97.arity registers (prefixList, 147) =
    (stackResult161.1, stackResult161.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult161.2.2.1, 161)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word161.program
    PrefixChecks.Shard97.arity registers prefixList 147
    stackResult161.1 stackResult161.2.1 stackResult161.2.2.1 161 stackResult161_eq
wave8_kernel_reduce stackResult162 := WordToStack.Native.compileProgNative
  riscvConfig false Word162.program PrefixChecks.Shard98.arity registers (.nil, 161)
theorem stackResult162_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word162.program
      PrefixChecks.Shard98.arity registers (prefixList, 161) =
    (stackResult162.1, stackResult162.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult162.2.2.1, 163)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word162.program
    PrefixChecks.Shard98.arity registers prefixList 161
    stackResult162.1 stackResult162.2.1 stackResult162.2.2.1 163 stackResult162_eq
wave8_kernel_reduce stackResult163 := WordToStack.Native.compileProgNative
  riscvConfig false Word163.program PrefixChecks.Shard99.arity registers (.nil, 163)
theorem stackResult163_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word163.program
      PrefixChecks.Shard99.arity registers (prefixList, 163) =
    (stackResult163.1, stackResult163.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult163.2.2.1, 175)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word163.program
    PrefixChecks.Shard99.arity registers prefixList 163
    stackResult163.1 stackResult163.2.1 stackResult163.2.2.1 175 stackResult163_eq
wave8_kernel_reduce stackResult164 := WordToStack.Native.compileProgNative
  riscvConfig false Word164.program PrefixChecks.Shard100.arity registers (.nil, 175)
theorem stackResult164_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word164.program
      PrefixChecks.Shard100.arity registers (prefixList, 175) =
    (stackResult164.1, stackResult164.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult164.2.2.1, 177)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word164.program
    PrefixChecks.Shard100.arity registers prefixList 175
    stackResult164.1 stackResult164.2.1 stackResult164.2.2.1 177 stackResult164_eq
wave8_kernel_reduce stackResult165 := WordToStack.Native.compileProgNative
  riscvConfig false Word165.program PrefixChecks.Shard101.arity registers (.nil, 177)
theorem stackResult165_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word165.program
      PrefixChecks.Shard101.arity registers (prefixList, 177) =
    (stackResult165.1, stackResult165.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult165.2.2.1, 181)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word165.program
    PrefixChecks.Shard101.arity registers prefixList 177
    stackResult165.1 stackResult165.2.1 stackResult165.2.2.1 181 stackResult165_eq
wave8_kernel_reduce stackResult166 := WordToStack.Native.compileProgNative
  riscvConfig false Word166.program PrefixChecks.Shard102.arity registers (.nil, 181)
theorem stackResult166_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word166.program
      PrefixChecks.Shard102.arity registers (prefixList, 181) =
    (stackResult166.1, stackResult166.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult166.2.2.1, 183)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word166.program
    PrefixChecks.Shard102.arity registers prefixList 181
    stackResult166.1 stackResult166.2.1 stackResult166.2.2.1 183 stackResult166_eq
wave8_kernel_reduce stackResult167 := WordToStack.Native.compileProgNative
  riscvConfig false Word167.program PrefixChecks.Shard103.arity registers (.nil, 183)
theorem stackResult167_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word167.program
      PrefixChecks.Shard103.arity registers (prefixList, 183) =
    (stackResult167.1, stackResult167.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult167.2.2.1, 184)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word167.program
    PrefixChecks.Shard103.arity registers prefixList 183
    stackResult167.1 stackResult167.2.1 stackResult167.2.2.1 184 stackResult167_eq
wave8_kernel_reduce stackResult168 := WordToStack.Native.compileProgNative
  riscvConfig false Word168.program PrefixChecks.Shard104.arity registers (.nil, 184)
theorem stackResult168_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word168.program
      PrefixChecks.Shard104.arity registers (prefixList, 184) =
    (stackResult168.1, stackResult168.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult168.2.2.1, 186)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word168.program
    PrefixChecks.Shard104.arity registers prefixList 184
    stackResult168.1 stackResult168.2.1 stackResult168.2.2.1 186 stackResult168_eq
wave8_kernel_reduce stackResult169 := WordToStack.Native.compileProgNative
  riscvConfig false Word169.program PrefixChecks.Shard105.arity registers (.nil, 186)
theorem stackResult169_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word169.program
      PrefixChecks.Shard105.arity registers (prefixList, 186) =
    (stackResult169.1, stackResult169.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult169.2.2.1, 189)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word169.program
    PrefixChecks.Shard105.arity registers prefixList 186
    stackResult169.1 stackResult169.2.1 stackResult169.2.2.1 189 stackResult169_eq
wave8_kernel_reduce stackResult170 := WordToStack.Native.compileProgNative
  riscvConfig false Word170.program PrefixChecks.Shard106.arity registers (.nil, 189)
theorem stackResult170_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word170.program
      PrefixChecks.Shard106.arity registers (prefixList, 189) =
    (stackResult170.1, stackResult170.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult170.2.2.1, 191)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word170.program
    PrefixChecks.Shard106.arity registers prefixList 189
    stackResult170.1 stackResult170.2.1 stackResult170.2.2.1 191 stackResult170_eq
wave8_kernel_reduce stackResult171 := WordToStack.Native.compileProgNative
  riscvConfig false Word171.program PrefixChecks.Shard107.arity registers (.nil, 191)
theorem stackResult171_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word171.program
      PrefixChecks.Shard107.arity registers (prefixList, 191) =
    (stackResult171.1, stackResult171.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult171.2.2.1, 193)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word171.program
    PrefixChecks.Shard107.arity registers prefixList 191
    stackResult171.1 stackResult171.2.1 stackResult171.2.2.1 193 stackResult171_eq
wave8_kernel_reduce stackResult172 := WordToStack.Native.compileProgNative
  riscvConfig false Word172.program PrefixChecks.Shard108.arity registers (.nil, 193)
theorem stackResult172_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word172.program
      PrefixChecks.Shard108.arity registers (prefixList, 193) =
    (stackResult172.1, stackResult172.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult172.2.2.1, 193)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word172.program
    PrefixChecks.Shard108.arity registers prefixList 193
    stackResult172.1 stackResult172.2.1 stackResult172.2.2.1 193 stackResult172_eq
wave8_kernel_reduce stackResult173 := WordToStack.Native.compileProgNative
  riscvConfig false Word173.program PrefixChecks.Shard109.arity registers (.nil, 193)
theorem stackResult173_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word173.program
      PrefixChecks.Shard109.arity registers (prefixList, 193) =
    (stackResult173.1, stackResult173.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult173.2.2.1, 193)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word173.program
    PrefixChecks.Shard109.arity registers prefixList 193
    stackResult173.1 stackResult173.2.1 stackResult173.2.2.1 193 stackResult173_eq
wave8_kernel_reduce stackResult174 := WordToStack.Native.compileProgNative
  riscvConfig false Word174.program PrefixChecks.Shard110.arity registers (.nil, 193)
theorem stackResult174_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word174.program
      PrefixChecks.Shard110.arity registers (prefixList, 193) =
    (stackResult174.1, stackResult174.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult174.2.2.1, 195)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word174.program
    PrefixChecks.Shard110.arity registers prefixList 193
    stackResult174.1 stackResult174.2.1 stackResult174.2.2.1 195 stackResult174_eq
wave8_kernel_reduce stackResult175 := WordToStack.Native.compileProgNative
  riscvConfig false Word175.program PrefixChecks.Shard111.arity registers (.nil, 195)
theorem stackResult175_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word175.program
      PrefixChecks.Shard111.arity registers (prefixList, 195) =
    (stackResult175.1, stackResult175.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult175.2.2.1, 196)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word175.program
    PrefixChecks.Shard111.arity registers prefixList 195
    stackResult175.1 stackResult175.2.1 stackResult175.2.2.1 196 stackResult175_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard96.name, PrefixChecks.Shard96.arity, Word160.program),
  (PrefixChecks.Shard97.name, PrefixChecks.Shard97.arity, Word161.program),
  (PrefixChecks.Shard98.name, PrefixChecks.Shard98.arity, Word162.program),
  (PrefixChecks.Shard99.name, PrefixChecks.Shard99.arity, Word163.program),
  (PrefixChecks.Shard100.name, PrefixChecks.Shard100.arity, Word164.program),
  (PrefixChecks.Shard101.name, PrefixChecks.Shard101.arity, Word165.program),
  (PrefixChecks.Shard102.name, PrefixChecks.Shard102.arity, Word166.program),
  (PrefixChecks.Shard103.name, PrefixChecks.Shard103.arity, Word167.program),
  (PrefixChecks.Shard104.name, PrefixChecks.Shard104.arity, Word168.program),
  (PrefixChecks.Shard105.name, PrefixChecks.Shard105.arity, Word169.program),
  (PrefixChecks.Shard106.name, PrefixChecks.Shard106.arity, Word170.program),
  (PrefixChecks.Shard107.name, PrefixChecks.Shard107.arity, Word171.program),
  (PrefixChecks.Shard108.name, PrefixChecks.Shard108.arity, Word172.program),
  (PrefixChecks.Shard109.name, PrefixChecks.Shard109.arity, Word173.program),
  (PrefixChecks.Shard110.name, PrefixChecks.Shard110.arity, Word174.program),
  (PrefixChecks.Shard111.name, PrefixChecks.Shard111.arity, Word175.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard96.name, stackResult160.1),
  (PrefixChecks.Shard97.name, stackResult161.1),
  (PrefixChecks.Shard98.name, stackResult162.1),
  (PrefixChecks.Shard99.name, stackResult163.1),
  (PrefixChecks.Shard100.name, stackResult164.1),
  (PrefixChecks.Shard101.name, stackResult165.1),
  (PrefixChecks.Shard102.name, stackResult166.1),
  (PrefixChecks.Shard103.name, stackResult167.1),
  (PrefixChecks.Shard104.name, stackResult168.1),
  (PrefixChecks.Shard105.name, stackResult169.1),
  (PrefixChecks.Shard106.name, stackResult170.1),
  (PrefixChecks.Shard107.name, stackResult171.1),
  (PrefixChecks.Shard108.name, stackResult172.1),
  (PrefixChecks.Shard109.name, stackResult173.1),
  (PrefixChecks.Shard110.name, stackResult174.1),
  (PrefixChecks.Shard111.name, stackResult175.1)
]

noncomputable def frames : List Nat := [
  stackResult160.2.1,
  stackResult161.2.1,
  stackResult162.2.1,
  stackResult163.2.1,
  stackResult164.2.1,
  stackResult165.2.1,
  stackResult166.2.1,
  stackResult167.2.1,
  stackResult168.2.1,
  stackResult169.2.1,
  stackResult170.2.1,
  stackResult171.2.1,
  stackResult172.2.1,
  stackResult173.2.1,
  stackResult174.2.1,
  stackResult175.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult160.2.2.1) stackResult161.2.2.1) stackResult162.2.2.1) stackResult163.2.2.1) stackResult164.2.2.1) stackResult165.2.2.1) stackResult166.2.2.1) stackResult167.2.2.1) stackResult168.2.2.1) stackResult169.2.2.1) stackResult170.2.2.1) stackResult171.2.2.1) stackResult172.2.2.1) stackResult173.2.2.1) stackResult174.2.2.1) stackResult175.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 146) = (bodies, frames, (bitmapDelta, 196)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult160_from _
  apply compileWordToStack_cons
  · exact stackResult161_from _
  apply compileWordToStack_cons
  · exact stackResult162_from _
  apply compileWordToStack_cons
  · exact stackResult163_from _
  apply compileWordToStack_cons
  · exact stackResult164_from _
  apply compileWordToStack_cons
  · exact stackResult165_from _
  apply compileWordToStack_cons
  · exact stackResult166_from _
  apply compileWordToStack_cons
  · exact stackResult167_from _
  apply compileWordToStack_cons
  · exact stackResult168_from _
  apply compileWordToStack_cons
  · exact stackResult169_from _
  apply compileWordToStack_cons
  · exact stackResult170_from _
  apply compileWordToStack_cons
  · exact stackResult171_from _
  apply compileWordToStack_cons
  · exact stackResult172_from _
  apply compileWordToStack_cons
  · exact stackResult173_from _
  apply compileWordToStack_cons
  · exact stackResult174_from _
  apply compileWordToStack_cons
  · exact stackResult175_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 146) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 196)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 146 bodies frames bitmapDelta 196 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 96).take 16).zip
      [oracle160, oracle161, oracle162, oracle163, oracle164, oracle165, oracle166, oracle167, oracle168, oracle169, oracle170, oracle171, oracle172, oracle173, oracle174, oracle175]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle160 PrefixChecks.Shard96.entry,
    wordFunction oracle161 PrefixChecks.Shard97.entry,
    wordFunction oracle162 PrefixChecks.Shard98.entry,
    wordFunction oracle163 PrefixChecks.Shard99.entry,
    wordFunction oracle164 PrefixChecks.Shard100.entry,
    wordFunction oracle165 PrefixChecks.Shard101.entry,
    wordFunction oracle166 PrefixChecks.Shard102.entry,
    wordFunction oracle167 PrefixChecks.Shard103.entry,
    wordFunction oracle168 PrefixChecks.Shard104.entry,
    wordFunction oracle169 PrefixChecks.Shard105.entry,
    wordFunction oracle170 PrefixChecks.Shard106.entry,
    wordFunction oracle171 PrefixChecks.Shard107.entry,
    wordFunction oracle172 PrefixChecks.Shard108.entry,
    wordFunction oracle173 PrefixChecks.Shard109.entry,
    wordFunction oracle174 PrefixChecks.Shard110.entry,
    wordFunction oracle175 PrefixChecks.Shard111.entry] = words
  simp only [
    Word160.wordFunction_eq,
    Word161.wordFunction_eq,
    Word162.wordFunction_eq,
    Word163.wordFunction_eq,
    Word164.wordFunction_eq,
    Word165.wordFunction_eq,
    Word166.wordFunction_eq,
    Word167.wordFunction_eq,
    Word168.wordFunction_eq,
    Word169.wordFunction_eq,
    Word170.wordFunction_eq,
    Word171.wordFunction_eq,
    Word172.wordFunction_eq,
    Word173.wordFunction_eq,
    Word174.wordFunction_eq,
    Word175.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk06
