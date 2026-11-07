import InitECandidate.Solver.Wave8Stage.ConcreteBackendBound
import InitECandidate.Solver.GuestPrefixChecks

/-!
# Proofs-free Stage 5 top-level transfer & certificate assembly (`StageTransfer`)

Assembles `Wave8GuestInv.StageTransfer`, `Wave8GuestInv.TargetClockBound`, and
`InitE.Certificate Wave8GuestInv.submission (.finite K_target)` directly from the
Proofs-free Stage 5 backend infrastructure (`ConcreteBackendBound`, `DirectBackendBound`,
`AllTables`, `AllBounded`, `ConcreteStageTransferBridge`), without importing
`InitECandidate.Proofs`, `ConcreteOracleWitness`, or unbuilt `PrefixChecks/AllChecked`.

Downstream consumers (`Solution.lean` / final cutover integrator) can discharge
`StageTransfer` and `InitE.Certificate` in one line via:
* `stageTransfer_of_concreteBackendBound`: given `w`, `w.oracles = ConcreteM7313.oracles`,
  `GuestStageTransfer.WordChecked` (supplied by `GuestPrefixChecks.word_all_checked`),
  and `DirectBackendBound.concreteBackendBound`; or
* `stageTransfer_of_missing_segments`: directly from `Segment00To27` (`Chunk00..27`) and
  `Segment34To49` (`Chunk34..49`), with `Chunk28..33`, `Chunk50`, `Frames28..33`,
  `Bounded28..33,50`, and `nativeStubs_bounded` already wired in.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.StageTransfer
open InitE Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.ConcreteM7313

/-- Assemble `Wave8GuestInv.StageTransfer` from a concrete compilation witness matching
`ConcreteM7313.oracles`, `GuestStageTransfer.WordChecked`, and
`DirectBackendBound.concreteBackendBound`. -/
theorem stageTransfer_of_concreteBackendBound
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (backend : DirectBackendBound.concreteBackendBound) :
    Wave8GuestInv.StageTransfer :=
  DirectBackendBound.concreteStageTransfer w same checked backend

/-- Assemble `Wave8GuestInv.StageTransfer` directly from `Segment00To27` (`Chunk00..27`)
and `Segment34To49` (`Chunk34..49`), with `Chunk28..33`, `Chunk50`, `Frames28..33`,
`Bounded28..33`, `Bounded50`, and `nativeStubs_bounded` already discharged. -/
theorem stageTransfer_of_missing_segments
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (seg00To27 : ConcreteBackendBound.Segment00To27)
    (seg34To49 : ConcreteBackendBound.Segment34To49) :
    Wave8GuestInv.StageTransfer :=
  DirectBackendBound.concreteStageTransfer w same checked
    (ConcreteBackendBound.concreteBackendBound_of_missing_segments seg00To27 seg34To49)

/-- Assemble `Wave8GuestInv.StageTransfer` from any full-guest table (`Table50`) whose
frame map equals `GlobalFrameInfo.info` and whose lowered bodies satisfy
`Bounded GlobalFrameInfo.info`. -/
theorem stageTransfer_of_table
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies : List (Nat × StackLang.HolProg 64))
    (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat)
    (info : Spt Nat)
    (hwords : (ConcreteCompilerWord.source.zip oracles).map
      (fun p => BackendDecomposition.wordFunction p.2 p.1) = words)
    (hcompiled : WordToStack.Native.compileWordToStackNative
      Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig false
      BackendDecomposition.registers words (.list [4], 1) = (bodies, frames, bitmaps))
    (hcollected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln = info)
    (hinfo : info = GlobalFrameInfo.info)
    (hbounded : LoweredBudget.Bounded GlobalFrameInfo.info bodies) :
    Wave8GuestInv.StageTransfer :=
  DirectBackendBound.concreteStageTransfer w same checked
    (ConcreteBackendBound.concreteBackendBound_of_table
      words bodies frames bitmaps info hwords hcompiled hcollected hinfo hbounded)

/-- Close `Wave8GuestInv.TargetClockBound` from `stageTransfer_of_missing_segments` and
any covered-source uniform non-timeout proof `source`. -/
theorem targetClockBound_of_missing_segments
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (seg00To27 : ConcreteBackendBound.Segment00To27)
    (seg34To49 : ConcreteBackendBound.Segment34To49)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) :
    Wave8GuestInv.TargetClockBound :=
  stageTransfer_of_missing_segments w same checked seg00To27 seg34To49 source

/-- Close `InitE.Certificate Wave8GuestInv.submission (.finite K_target)` from `w`,
`w.oracles = ConcreteM7313.oracles`, `WordChecked`, `Segment00To27`, `Segment34To49`,
and `Wave8GuestInv.Primitives` (`0` `sorryAx`). -/
theorem certificate_of_missing_segments_and_primitives
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (seg00To27 : ConcreteBackendBound.Segment00To27)
    (seg34To49 : ConcreteBackendBound.Segment34To49)
    (P : Wave8GuestInv.Primitives) :
    InitE.Certificate Wave8GuestInv.submission (.finite K_target) :=
  Wave8GuestInv.certificate_of_primitives w
    (stageTransfer_of_missing_segments w same checked seg00To27 seg34To49) P

/-- Close `InitE.Certificate Wave8GuestInv.submission (.finite K_target)` from `w`,
`w.oracles = ConcreteM7313.oracles`, `WordChecked`, `Segment00To27`, `Segment34To49`,
and a covered-source uniform non-timeout proof (`0` `sorryAx`). -/
theorem certificate_of_missing_segments
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (seg00To27 : ConcreteBackendBound.Segment00To27)
    (seg34To49 : ConcreteBackendBound.Segment34To49)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) :
    InitE.Certificate Wave8GuestInv.submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (targetClockBound_of_missing_segments w same checked seg00To27 seg34To49 source)

theorem stageTransfer
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles) :
    Wave8GuestInv.StageTransfer :=
  DirectBackendBound.concreteStageTransfer w same
    GuestPrefixChecks.word_all_checked ConcreteBackendBound.concreteBackendBound

theorem targetClockBound
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) :
    Wave8GuestInv.TargetClockBound :=
  stageTransfer w same source

theorem certificate_of_witness
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles) :
    InitE.Certificate Wave8GuestInv.submission (.finite K_target) :=
  Wave8GuestInv.certificate_of_stage_transfer w (stageTransfer w same)

end InitECandidate.Solver.Wave8Stage.StageTransfer
