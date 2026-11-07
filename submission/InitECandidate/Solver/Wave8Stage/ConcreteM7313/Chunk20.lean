import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word384
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word385
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word386
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word387
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word388
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word389
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word390
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word391
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word392
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word393
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word394
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word395
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word396
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word397
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word398
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word399
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk20
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult384 := WordToStack.Native.compileProgNative
  riscvConfig false Word384.program PrefixChecks.Shard320.arity registers (.nil, 1129)
theorem stackResult384_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word384.program
      PrefixChecks.Shard320.arity registers (prefixList, 1129) =
    (stackResult384.1, stackResult384.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult384.2.2.1, 1132)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word384.program
    PrefixChecks.Shard320.arity registers prefixList 1129
    stackResult384.1 stackResult384.2.1 stackResult384.2.2.1 1132 stackResult384_eq
wave8_kernel_reduce stackResult385 := WordToStack.Native.compileProgNative
  riscvConfig false Word385.program PrefixChecks.Shard321.arity registers (.nil, 1132)
theorem stackResult385_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word385.program
      PrefixChecks.Shard321.arity registers (prefixList, 1132) =
    (stackResult385.1, stackResult385.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult385.2.2.1, 1134)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word385.program
    PrefixChecks.Shard321.arity registers prefixList 1132
    stackResult385.1 stackResult385.2.1 stackResult385.2.2.1 1134 stackResult385_eq
wave8_kernel_reduce stackResult386 := WordToStack.Native.compileProgNative
  riscvConfig false Word386.program PrefixChecks.Shard322.arity registers (.nil, 1134)
theorem stackResult386_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word386.program
      PrefixChecks.Shard322.arity registers (prefixList, 1134) =
    (stackResult386.1, stackResult386.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult386.2.2.1, 1147)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word386.program
    PrefixChecks.Shard322.arity registers prefixList 1134
    stackResult386.1 stackResult386.2.1 stackResult386.2.2.1 1147 stackResult386_eq
wave8_kernel_reduce stackResult387 := WordToStack.Native.compileProgNative
  riscvConfig false Word387.program PrefixChecks.Shard323.arity registers (.nil, 1147)
theorem stackResult387_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word387.program
      PrefixChecks.Shard323.arity registers (prefixList, 1147) =
    (stackResult387.1, stackResult387.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult387.2.2.1, 1156)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word387.program
    PrefixChecks.Shard323.arity registers prefixList 1147
    stackResult387.1 stackResult387.2.1 stackResult387.2.2.1 1156 stackResult387_eq
wave8_kernel_reduce stackResult388 := WordToStack.Native.compileProgNative
  riscvConfig false Word388.program PrefixChecks.Shard324.arity registers (.nil, 1156)
theorem stackResult388_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word388.program
      PrefixChecks.Shard324.arity registers (prefixList, 1156) =
    (stackResult388.1, stackResult388.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult388.2.2.1, 1161)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word388.program
    PrefixChecks.Shard324.arity registers prefixList 1156
    stackResult388.1 stackResult388.2.1 stackResult388.2.2.1 1161 stackResult388_eq
wave8_kernel_reduce stackResult389 := WordToStack.Native.compileProgNative
  riscvConfig false Word389.program PrefixChecks.Shard325.arity registers (.nil, 1161)
theorem stackResult389_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word389.program
      PrefixChecks.Shard325.arity registers (prefixList, 1161) =
    (stackResult389.1, stackResult389.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult389.2.2.1, 1166)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word389.program
    PrefixChecks.Shard325.arity registers prefixList 1161
    stackResult389.1 stackResult389.2.1 stackResult389.2.2.1 1166 stackResult389_eq
wave8_kernel_reduce stackResult390 := WordToStack.Native.compileProgNative
  riscvConfig false Word390.program PrefixChecks.Shard326.arity registers (.nil, 1166)
theorem stackResult390_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word390.program
      PrefixChecks.Shard326.arity registers (prefixList, 1166) =
    (stackResult390.1, stackResult390.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult390.2.2.1, 1166)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word390.program
    PrefixChecks.Shard326.arity registers prefixList 1166
    stackResult390.1 stackResult390.2.1 stackResult390.2.2.1 1166 stackResult390_eq
wave8_kernel_reduce stackResult391 := WordToStack.Native.compileProgNative
  riscvConfig false Word391.program PrefixChecks.Shard327.arity registers (.nil, 1166)
theorem stackResult391_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word391.program
      PrefixChecks.Shard327.arity registers (prefixList, 1166) =
    (stackResult391.1, stackResult391.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult391.2.2.1, 1168)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word391.program
    PrefixChecks.Shard327.arity registers prefixList 1166
    stackResult391.1 stackResult391.2.1 stackResult391.2.2.1 1168 stackResult391_eq
wave8_kernel_reduce stackResult392 := WordToStack.Native.compileProgNative
  riscvConfig false Word392.program PrefixChecks.Shard328.arity registers (.nil, 1168)
theorem stackResult392_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word392.program
      PrefixChecks.Shard328.arity registers (prefixList, 1168) =
    (stackResult392.1, stackResult392.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult392.2.2.1, 1170)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word392.program
    PrefixChecks.Shard328.arity registers prefixList 1168
    stackResult392.1 stackResult392.2.1 stackResult392.2.2.1 1170 stackResult392_eq
wave8_kernel_reduce stackResult393 := WordToStack.Native.compileProgNative
  riscvConfig false Word393.program PrefixChecks.Shard329.arity registers (.nil, 1170)
theorem stackResult393_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word393.program
      PrefixChecks.Shard329.arity registers (prefixList, 1170) =
    (stackResult393.1, stackResult393.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult393.2.2.1, 1171)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word393.program
    PrefixChecks.Shard329.arity registers prefixList 1170
    stackResult393.1 stackResult393.2.1 stackResult393.2.2.1 1171 stackResult393_eq
wave8_kernel_reduce stackResult394 := WordToStack.Native.compileProgNative
  riscvConfig false Word394.program PrefixChecks.Shard330.arity registers (.nil, 1171)
theorem stackResult394_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word394.program
      PrefixChecks.Shard330.arity registers (prefixList, 1171) =
    (stackResult394.1, stackResult394.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult394.2.2.1, 1172)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word394.program
    PrefixChecks.Shard330.arity registers prefixList 1171
    stackResult394.1 stackResult394.2.1 stackResult394.2.2.1 1172 stackResult394_eq
wave8_kernel_reduce stackResult395 := WordToStack.Native.compileProgNative
  riscvConfig false Word395.program PrefixChecks.Shard331.arity registers (.nil, 1172)
theorem stackResult395_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word395.program
      PrefixChecks.Shard331.arity registers (prefixList, 1172) =
    (stackResult395.1, stackResult395.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult395.2.2.1, 1174)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word395.program
    PrefixChecks.Shard331.arity registers prefixList 1172
    stackResult395.1 stackResult395.2.1 stackResult395.2.2.1 1174 stackResult395_eq
wave8_kernel_reduce stackResult396 := WordToStack.Native.compileProgNative
  riscvConfig false Word396.program PrefixChecks.Shard332.arity registers (.nil, 1174)
theorem stackResult396_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word396.program
      PrefixChecks.Shard332.arity registers (prefixList, 1174) =
    (stackResult396.1, stackResult396.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult396.2.2.1, 1175)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word396.program
    PrefixChecks.Shard332.arity registers prefixList 1174
    stackResult396.1 stackResult396.2.1 stackResult396.2.2.1 1175 stackResult396_eq
wave8_kernel_reduce stackResult397 := WordToStack.Native.compileProgNative
  riscvConfig false Word397.program PrefixChecks.Shard333.arity registers (.nil, 1175)
theorem stackResult397_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word397.program
      PrefixChecks.Shard333.arity registers (prefixList, 1175) =
    (stackResult397.1, stackResult397.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult397.2.2.1, 1180)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word397.program
    PrefixChecks.Shard333.arity registers prefixList 1175
    stackResult397.1 stackResult397.2.1 stackResult397.2.2.1 1180 stackResult397_eq
wave8_kernel_reduce stackResult398 := WordToStack.Native.compileProgNative
  riscvConfig false Word398.program PrefixChecks.Shard334.arity registers (.nil, 1180)
theorem stackResult398_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word398.program
      PrefixChecks.Shard334.arity registers (prefixList, 1180) =
    (stackResult398.1, stackResult398.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult398.2.2.1, 1183)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word398.program
    PrefixChecks.Shard334.arity registers prefixList 1180
    stackResult398.1 stackResult398.2.1 stackResult398.2.2.1 1183 stackResult398_eq
wave8_kernel_reduce stackResult399 := WordToStack.Native.compileProgNative
  riscvConfig false Word399.program PrefixChecks.Shard335.arity registers (.nil, 1183)
theorem stackResult399_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word399.program
      PrefixChecks.Shard335.arity registers (prefixList, 1183) =
    (stackResult399.1, stackResult399.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult399.2.2.1, 1184)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word399.program
    PrefixChecks.Shard335.arity registers prefixList 1183
    stackResult399.1 stackResult399.2.1 stackResult399.2.2.1 1184 stackResult399_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard320.name, PrefixChecks.Shard320.arity, Word384.program),
  (PrefixChecks.Shard321.name, PrefixChecks.Shard321.arity, Word385.program),
  (PrefixChecks.Shard322.name, PrefixChecks.Shard322.arity, Word386.program),
  (PrefixChecks.Shard323.name, PrefixChecks.Shard323.arity, Word387.program),
  (PrefixChecks.Shard324.name, PrefixChecks.Shard324.arity, Word388.program),
  (PrefixChecks.Shard325.name, PrefixChecks.Shard325.arity, Word389.program),
  (PrefixChecks.Shard326.name, PrefixChecks.Shard326.arity, Word390.program),
  (PrefixChecks.Shard327.name, PrefixChecks.Shard327.arity, Word391.program),
  (PrefixChecks.Shard328.name, PrefixChecks.Shard328.arity, Word392.program),
  (PrefixChecks.Shard329.name, PrefixChecks.Shard329.arity, Word393.program),
  (PrefixChecks.Shard330.name, PrefixChecks.Shard330.arity, Word394.program),
  (PrefixChecks.Shard331.name, PrefixChecks.Shard331.arity, Word395.program),
  (PrefixChecks.Shard332.name, PrefixChecks.Shard332.arity, Word396.program),
  (PrefixChecks.Shard333.name, PrefixChecks.Shard333.arity, Word397.program),
  (PrefixChecks.Shard334.name, PrefixChecks.Shard334.arity, Word398.program),
  (PrefixChecks.Shard335.name, PrefixChecks.Shard335.arity, Word399.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard320.name, stackResult384.1),
  (PrefixChecks.Shard321.name, stackResult385.1),
  (PrefixChecks.Shard322.name, stackResult386.1),
  (PrefixChecks.Shard323.name, stackResult387.1),
  (PrefixChecks.Shard324.name, stackResult388.1),
  (PrefixChecks.Shard325.name, stackResult389.1),
  (PrefixChecks.Shard326.name, stackResult390.1),
  (PrefixChecks.Shard327.name, stackResult391.1),
  (PrefixChecks.Shard328.name, stackResult392.1),
  (PrefixChecks.Shard329.name, stackResult393.1),
  (PrefixChecks.Shard330.name, stackResult394.1),
  (PrefixChecks.Shard331.name, stackResult395.1),
  (PrefixChecks.Shard332.name, stackResult396.1),
  (PrefixChecks.Shard333.name, stackResult397.1),
  (PrefixChecks.Shard334.name, stackResult398.1),
  (PrefixChecks.Shard335.name, stackResult399.1)
]

noncomputable def frames : List Nat := [
  stackResult384.2.1,
  stackResult385.2.1,
  stackResult386.2.1,
  stackResult387.2.1,
  stackResult388.2.1,
  stackResult389.2.1,
  stackResult390.2.1,
  stackResult391.2.1,
  stackResult392.2.1,
  stackResult393.2.1,
  stackResult394.2.1,
  stackResult395.2.1,
  stackResult396.2.1,
  stackResult397.2.1,
  stackResult398.2.1,
  stackResult399.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult384.2.2.1) stackResult385.2.2.1) stackResult386.2.2.1) stackResult387.2.2.1) stackResult388.2.2.1) stackResult389.2.2.1) stackResult390.2.2.1) stackResult391.2.2.1) stackResult392.2.2.1) stackResult393.2.2.1) stackResult394.2.2.1) stackResult395.2.2.1) stackResult396.2.2.1) stackResult397.2.2.1) stackResult398.2.2.1) stackResult399.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1129) = (bodies, frames, (bitmapDelta, 1184)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult384_from _
  apply compileWordToStack_cons
  · exact stackResult385_from _
  apply compileWordToStack_cons
  · exact stackResult386_from _
  apply compileWordToStack_cons
  · exact stackResult387_from _
  apply compileWordToStack_cons
  · exact stackResult388_from _
  apply compileWordToStack_cons
  · exact stackResult389_from _
  apply compileWordToStack_cons
  · exact stackResult390_from _
  apply compileWordToStack_cons
  · exact stackResult391_from _
  apply compileWordToStack_cons
  · exact stackResult392_from _
  apply compileWordToStack_cons
  · exact stackResult393_from _
  apply compileWordToStack_cons
  · exact stackResult394_from _
  apply compileWordToStack_cons
  · exact stackResult395_from _
  apply compileWordToStack_cons
  · exact stackResult396_from _
  apply compileWordToStack_cons
  · exact stackResult397_from _
  apply compileWordToStack_cons
  · exact stackResult398_from _
  apply compileWordToStack_cons
  · exact stackResult399_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1129) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1184)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1129 bodies frames bitmapDelta 1184 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 320).take 16).zip
      [oracle384, oracle385, oracle386, oracle387, oracle388, oracle389, oracle390, oracle391, oracle392, oracle393, oracle394, oracle395, oracle396, oracle397, oracle398, oracle399]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle384 PrefixChecks.Shard320.entry,
    wordFunction oracle385 PrefixChecks.Shard321.entry,
    wordFunction oracle386 PrefixChecks.Shard322.entry,
    wordFunction oracle387 PrefixChecks.Shard323.entry,
    wordFunction oracle388 PrefixChecks.Shard324.entry,
    wordFunction oracle389 PrefixChecks.Shard325.entry,
    wordFunction oracle390 PrefixChecks.Shard326.entry,
    wordFunction oracle391 PrefixChecks.Shard327.entry,
    wordFunction oracle392 PrefixChecks.Shard328.entry,
    wordFunction oracle393 PrefixChecks.Shard329.entry,
    wordFunction oracle394 PrefixChecks.Shard330.entry,
    wordFunction oracle395 PrefixChecks.Shard331.entry,
    wordFunction oracle396 PrefixChecks.Shard332.entry,
    wordFunction oracle397 PrefixChecks.Shard333.entry,
    wordFunction oracle398 PrefixChecks.Shard334.entry,
    wordFunction oracle399 PrefixChecks.Shard335.entry] = words
  simp only [
    Word384.wordFunction_eq,
    Word385.wordFunction_eq,
    Word386.wordFunction_eq,
    Word387.wordFunction_eq,
    Word388.wordFunction_eq,
    Word389.wordFunction_eq,
    Word390.wordFunction_eq,
    Word391.wordFunction_eq,
    Word392.wordFunction_eq,
    Word393.wordFunction_eq,
    Word394.wordFunction_eq,
    Word395.wordFunction_eq,
    Word396.wordFunction_eq,
    Word397.wordFunction_eq,
    Word398.wordFunction_eq,
    Word399.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk20
