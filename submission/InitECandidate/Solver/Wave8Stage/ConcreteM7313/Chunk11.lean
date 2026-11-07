import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word240
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word241
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word242
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word243
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word244
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word245
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word246
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word247
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word248
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word249
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word250
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word251
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word252
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word253
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word254
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word255
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk11
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult240 := WordToStack.Native.compileProgNative
  riscvConfig false Word240.program PrefixChecks.Shard176.arity registers (.nil, 460)
theorem stackResult240_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word240.program
      PrefixChecks.Shard176.arity registers (prefixList, 460) =
    (stackResult240.1, stackResult240.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult240.2.2.1, 466)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word240.program
    PrefixChecks.Shard176.arity registers prefixList 460
    stackResult240.1 stackResult240.2.1 stackResult240.2.2.1 466 stackResult240_eq
wave8_kernel_reduce stackResult241 := WordToStack.Native.compileProgNative
  riscvConfig false Word241.program PrefixChecks.Shard177.arity registers (.nil, 466)
theorem stackResult241_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word241.program
      PrefixChecks.Shard177.arity registers (prefixList, 466) =
    (stackResult241.1, stackResult241.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult241.2.2.1, 469)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word241.program
    PrefixChecks.Shard177.arity registers prefixList 466
    stackResult241.1 stackResult241.2.1 stackResult241.2.2.1 469 stackResult241_eq
wave8_kernel_reduce stackResult242 := WordToStack.Native.compileProgNative
  riscvConfig false Word242.program PrefixChecks.Shard178.arity registers (.nil, 469)
theorem stackResult242_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word242.program
      PrefixChecks.Shard178.arity registers (prefixList, 469) =
    (stackResult242.1, stackResult242.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult242.2.2.1, 475)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word242.program
    PrefixChecks.Shard178.arity registers prefixList 469
    stackResult242.1 stackResult242.2.1 stackResult242.2.2.1 475 stackResult242_eq
wave8_kernel_reduce stackResult243 := WordToStack.Native.compileProgNative
  riscvConfig false Word243.program PrefixChecks.Shard179.arity registers (.nil, 475)
theorem stackResult243_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word243.program
      PrefixChecks.Shard179.arity registers (prefixList, 475) =
    (stackResult243.1, stackResult243.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult243.2.2.1, 480)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word243.program
    PrefixChecks.Shard179.arity registers prefixList 475
    stackResult243.1 stackResult243.2.1 stackResult243.2.2.1 480 stackResult243_eq
wave8_kernel_reduce stackResult244 := WordToStack.Native.compileProgNative
  riscvConfig false Word244.program PrefixChecks.Shard180.arity registers (.nil, 480)
theorem stackResult244_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word244.program
      PrefixChecks.Shard180.arity registers (prefixList, 480) =
    (stackResult244.1, stackResult244.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult244.2.2.1, 482)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word244.program
    PrefixChecks.Shard180.arity registers prefixList 480
    stackResult244.1 stackResult244.2.1 stackResult244.2.2.1 482 stackResult244_eq
wave8_kernel_reduce stackResult245 := WordToStack.Native.compileProgNative
  riscvConfig false Word245.program PrefixChecks.Shard181.arity registers (.nil, 482)
theorem stackResult245_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word245.program
      PrefixChecks.Shard181.arity registers (prefixList, 482) =
    (stackResult245.1, stackResult245.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult245.2.2.1, 482)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word245.program
    PrefixChecks.Shard181.arity registers prefixList 482
    stackResult245.1 stackResult245.2.1 stackResult245.2.2.1 482 stackResult245_eq
wave8_kernel_reduce stackResult246 := WordToStack.Native.compileProgNative
  riscvConfig false Word246.program PrefixChecks.Shard182.arity registers (.nil, 482)
theorem stackResult246_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word246.program
      PrefixChecks.Shard182.arity registers (prefixList, 482) =
    (stackResult246.1, stackResult246.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult246.2.2.1, 482)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word246.program
    PrefixChecks.Shard182.arity registers prefixList 482
    stackResult246.1 stackResult246.2.1 stackResult246.2.2.1 482 stackResult246_eq
wave8_kernel_reduce stackResult247 := WordToStack.Native.compileProgNative
  riscvConfig false Word247.program PrefixChecks.Shard183.arity registers (.nil, 482)
theorem stackResult247_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word247.program
      PrefixChecks.Shard183.arity registers (prefixList, 482) =
    (stackResult247.1, stackResult247.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult247.2.2.1, 486)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word247.program
    PrefixChecks.Shard183.arity registers prefixList 482
    stackResult247.1 stackResult247.2.1 stackResult247.2.2.1 486 stackResult247_eq
wave8_kernel_reduce stackResult248 := WordToStack.Native.compileProgNative
  riscvConfig false Word248.program PrefixChecks.Shard184.arity registers (.nil, 486)
theorem stackResult248_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word248.program
      PrefixChecks.Shard184.arity registers (prefixList, 486) =
    (stackResult248.1, stackResult248.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult248.2.2.1, 505)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word248.program
    PrefixChecks.Shard184.arity registers prefixList 486
    stackResult248.1 stackResult248.2.1 stackResult248.2.2.1 505 stackResult248_eq
wave8_kernel_reduce stackResult249 := WordToStack.Native.compileProgNative
  riscvConfig false Word249.program PrefixChecks.Shard185.arity registers (.nil, 505)
theorem stackResult249_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word249.program
      PrefixChecks.Shard185.arity registers (prefixList, 505) =
    (stackResult249.1, stackResult249.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult249.2.2.1, 507)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word249.program
    PrefixChecks.Shard185.arity registers prefixList 505
    stackResult249.1 stackResult249.2.1 stackResult249.2.2.1 507 stackResult249_eq
wave8_kernel_reduce stackResult250 := WordToStack.Native.compileProgNative
  riscvConfig false Word250.program PrefixChecks.Shard186.arity registers (.nil, 507)
theorem stackResult250_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word250.program
      PrefixChecks.Shard186.arity registers (prefixList, 507) =
    (stackResult250.1, stackResult250.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult250.2.2.1, 510)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word250.program
    PrefixChecks.Shard186.arity registers prefixList 507
    stackResult250.1 stackResult250.2.1 stackResult250.2.2.1 510 stackResult250_eq
wave8_kernel_reduce stackResult251 := WordToStack.Native.compileProgNative
  riscvConfig false Word251.program PrefixChecks.Shard187.arity registers (.nil, 510)
theorem stackResult251_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word251.program
      PrefixChecks.Shard187.arity registers (prefixList, 510) =
    (stackResult251.1, stackResult251.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult251.2.2.1, 515)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word251.program
    PrefixChecks.Shard187.arity registers prefixList 510
    stackResult251.1 stackResult251.2.1 stackResult251.2.2.1 515 stackResult251_eq
wave8_kernel_reduce stackResult252 := WordToStack.Native.compileProgNative
  riscvConfig false Word252.program PrefixChecks.Shard188.arity registers (.nil, 515)
theorem stackResult252_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word252.program
      PrefixChecks.Shard188.arity registers (prefixList, 515) =
    (stackResult252.1, stackResult252.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult252.2.2.1, 518)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word252.program
    PrefixChecks.Shard188.arity registers prefixList 515
    stackResult252.1 stackResult252.2.1 stackResult252.2.2.1 518 stackResult252_eq
wave8_kernel_reduce stackResult253 := WordToStack.Native.compileProgNative
  riscvConfig false Word253.program PrefixChecks.Shard189.arity registers (.nil, 518)
theorem stackResult253_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word253.program
      PrefixChecks.Shard189.arity registers (prefixList, 518) =
    (stackResult253.1, stackResult253.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult253.2.2.1, 524)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word253.program
    PrefixChecks.Shard189.arity registers prefixList 518
    stackResult253.1 stackResult253.2.1 stackResult253.2.2.1 524 stackResult253_eq
wave8_kernel_reduce stackResult254 := WordToStack.Native.compileProgNative
  riscvConfig false Word254.program PrefixChecks.Shard190.arity registers (.nil, 524)
theorem stackResult254_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word254.program
      PrefixChecks.Shard190.arity registers (prefixList, 524) =
    (stackResult254.1, stackResult254.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult254.2.2.1, 532)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word254.program
    PrefixChecks.Shard190.arity registers prefixList 524
    stackResult254.1 stackResult254.2.1 stackResult254.2.2.1 532 stackResult254_eq
wave8_kernel_reduce stackResult255 := WordToStack.Native.compileProgNative
  riscvConfig false Word255.program PrefixChecks.Shard191.arity registers (.nil, 532)
theorem stackResult255_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word255.program
      PrefixChecks.Shard191.arity registers (prefixList, 532) =
    (stackResult255.1, stackResult255.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult255.2.2.1, 534)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word255.program
    PrefixChecks.Shard191.arity registers prefixList 532
    stackResult255.1 stackResult255.2.1 stackResult255.2.2.1 534 stackResult255_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard176.name, PrefixChecks.Shard176.arity, Word240.program),
  (PrefixChecks.Shard177.name, PrefixChecks.Shard177.arity, Word241.program),
  (PrefixChecks.Shard178.name, PrefixChecks.Shard178.arity, Word242.program),
  (PrefixChecks.Shard179.name, PrefixChecks.Shard179.arity, Word243.program),
  (PrefixChecks.Shard180.name, PrefixChecks.Shard180.arity, Word244.program),
  (PrefixChecks.Shard181.name, PrefixChecks.Shard181.arity, Word245.program),
  (PrefixChecks.Shard182.name, PrefixChecks.Shard182.arity, Word246.program),
  (PrefixChecks.Shard183.name, PrefixChecks.Shard183.arity, Word247.program),
  (PrefixChecks.Shard184.name, PrefixChecks.Shard184.arity, Word248.program),
  (PrefixChecks.Shard185.name, PrefixChecks.Shard185.arity, Word249.program),
  (PrefixChecks.Shard186.name, PrefixChecks.Shard186.arity, Word250.program),
  (PrefixChecks.Shard187.name, PrefixChecks.Shard187.arity, Word251.program),
  (PrefixChecks.Shard188.name, PrefixChecks.Shard188.arity, Word252.program),
  (PrefixChecks.Shard189.name, PrefixChecks.Shard189.arity, Word253.program),
  (PrefixChecks.Shard190.name, PrefixChecks.Shard190.arity, Word254.program),
  (PrefixChecks.Shard191.name, PrefixChecks.Shard191.arity, Word255.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard176.name, stackResult240.1),
  (PrefixChecks.Shard177.name, stackResult241.1),
  (PrefixChecks.Shard178.name, stackResult242.1),
  (PrefixChecks.Shard179.name, stackResult243.1),
  (PrefixChecks.Shard180.name, stackResult244.1),
  (PrefixChecks.Shard181.name, stackResult245.1),
  (PrefixChecks.Shard182.name, stackResult246.1),
  (PrefixChecks.Shard183.name, stackResult247.1),
  (PrefixChecks.Shard184.name, stackResult248.1),
  (PrefixChecks.Shard185.name, stackResult249.1),
  (PrefixChecks.Shard186.name, stackResult250.1),
  (PrefixChecks.Shard187.name, stackResult251.1),
  (PrefixChecks.Shard188.name, stackResult252.1),
  (PrefixChecks.Shard189.name, stackResult253.1),
  (PrefixChecks.Shard190.name, stackResult254.1),
  (PrefixChecks.Shard191.name, stackResult255.1)
]

noncomputable def frames : List Nat := [
  stackResult240.2.1,
  stackResult241.2.1,
  stackResult242.2.1,
  stackResult243.2.1,
  stackResult244.2.1,
  stackResult245.2.1,
  stackResult246.2.1,
  stackResult247.2.1,
  stackResult248.2.1,
  stackResult249.2.1,
  stackResult250.2.1,
  stackResult251.2.1,
  stackResult252.2.1,
  stackResult253.2.1,
  stackResult254.2.1,
  stackResult255.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult240.2.2.1) stackResult241.2.2.1) stackResult242.2.2.1) stackResult243.2.2.1) stackResult244.2.2.1) stackResult245.2.2.1) stackResult246.2.2.1) stackResult247.2.2.1) stackResult248.2.2.1) stackResult249.2.2.1) stackResult250.2.2.1) stackResult251.2.2.1) stackResult252.2.2.1) stackResult253.2.2.1) stackResult254.2.2.1) stackResult255.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 460) = (bodies, frames, (bitmapDelta, 534)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult240_from _
  apply compileWordToStack_cons
  · exact stackResult241_from _
  apply compileWordToStack_cons
  · exact stackResult242_from _
  apply compileWordToStack_cons
  · exact stackResult243_from _
  apply compileWordToStack_cons
  · exact stackResult244_from _
  apply compileWordToStack_cons
  · exact stackResult245_from _
  apply compileWordToStack_cons
  · exact stackResult246_from _
  apply compileWordToStack_cons
  · exact stackResult247_from _
  apply compileWordToStack_cons
  · exact stackResult248_from _
  apply compileWordToStack_cons
  · exact stackResult249_from _
  apply compileWordToStack_cons
  · exact stackResult250_from _
  apply compileWordToStack_cons
  · exact stackResult251_from _
  apply compileWordToStack_cons
  · exact stackResult252_from _
  apply compileWordToStack_cons
  · exact stackResult253_from _
  apply compileWordToStack_cons
  · exact stackResult254_from _
  apply compileWordToStack_cons
  · exact stackResult255_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 460) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 534)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 460 bodies frames bitmapDelta 534 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 176).take 16).zip
      [oracle240, oracle241, oracle242, oracle243, oracle244, oracle245, oracle246, oracle247, oracle248, oracle249, oracle250, oracle251, oracle252, oracle253, oracle254, oracle255]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle240 PrefixChecks.Shard176.entry,
    wordFunction oracle241 PrefixChecks.Shard177.entry,
    wordFunction oracle242 PrefixChecks.Shard178.entry,
    wordFunction oracle243 PrefixChecks.Shard179.entry,
    wordFunction oracle244 PrefixChecks.Shard180.entry,
    wordFunction oracle245 PrefixChecks.Shard181.entry,
    wordFunction oracle246 PrefixChecks.Shard182.entry,
    wordFunction oracle247 PrefixChecks.Shard183.entry,
    wordFunction oracle248 PrefixChecks.Shard184.entry,
    wordFunction oracle249 PrefixChecks.Shard185.entry,
    wordFunction oracle250 PrefixChecks.Shard186.entry,
    wordFunction oracle251 PrefixChecks.Shard187.entry,
    wordFunction oracle252 PrefixChecks.Shard188.entry,
    wordFunction oracle253 PrefixChecks.Shard189.entry,
    wordFunction oracle254 PrefixChecks.Shard190.entry,
    wordFunction oracle255 PrefixChecks.Shard191.entry] = words
  simp only [
    Word240.wordFunction_eq,
    Word241.wordFunction_eq,
    Word242.wordFunction_eq,
    Word243.wordFunction_eq,
    Word244.wordFunction_eq,
    Word245.wordFunction_eq,
    Word246.wordFunction_eq,
    Word247.wordFunction_eq,
    Word248.wordFunction_eq,
    Word249.wordFunction_eq,
    Word250.wordFunction_eq,
    Word251.wordFunction_eq,
    Word252.wordFunction_eq,
    Word253.wordFunction_eq,
    Word254.wordFunction_eq,
    Word255.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk11
