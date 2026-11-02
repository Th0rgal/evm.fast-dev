import InitECandidate.Solver.Wave8Stage.InitCodeHeap

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.PipelineInitHeap
open Classical Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Successful total pipeline initialization follows from the machine heap
contract. No properties of the supplied Stack program or compiler oracle are
required: they are installed after running the initializer. -/
theorem fullMakeInit_success {width : Nat} [NeZero width] {C F : Type}
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (pre : InitCodeHeap.heapPre sp bitmaps dataSp
      (s2 scc dc maxHeap sp offset code lab saveRegs oracle) frame)
    (fits : bitmaps.length + dataSp + 1 < 2 ^ width)
    (maxOk : maxStackAlloc ≤ maxHeap) :
    ∃ aux, (FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps code lab saveRegs
      dataSp oracle).2 = some aux := by
  have result := InitCodeHeap.initCode_heap (StackToLab.isGenGc dc.gcKind) maxHeap sp bitmaps
    dataSp (s2 scc dc maxHeap sp offset code lab saveRegs oracle) scc.jump offset
    (sptFromAList (code1 dc code)) (coracle1 oracle) frame pre fits maxOk
  cases run : StackSemEvaluate.evaluate (initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp,
      s2 scc dc maxHeap sp offset code lab saveRegs oracle) with
  | mk res post =>
    rw [run] at result
    cases res with
    | some _ => exact result.elim
    | none =>
      refine ⟨InitReduce.initReduce (StackToLab.isGenGc dc.gcKind) scc.jump offset sp
        (sptFromAList (code1 dc code)) bitmaps dataSp (coracle1 oracle) post,?_⟩
      rw [fullMakeInit_eq]
      dsimp only
      unfold InitMake.makeInitOpt
      rw [run]
      exact if_pos result.2.2.1

end InitECandidate.Solver.Wave8Stage.PipelineInitHeap
