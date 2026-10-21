import InitECandidate.Proofs.StackAnalysis.Data704
import InitECandidate.Proofs.StackAnalysis.Entries
import Lean
import Flapjack.RiscV.NativeSource
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
set_option Elab.async false
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.StackAnalysis
def frame704 : Nat := 0
def slim704 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip
theorem frame704_eq : InitECandidate.Proofs.StackFrameComputation.frameSize (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) optimized704.2.1 optimized704.2.2 = frame704 := by cbv
theorem slim704_eq : WordDepth.Executable.slim optimized704.2.2 = slim704 := by cbv
theorem frameEntry704_eq : frameEntry optimized704 = (704, frame704) := by
  unfold frameEntry
  rw [frame704_eq]
  rfl
theorem slimEntry704_eq : slimEntry optimized704 = (704, 13, slim704) := by
  unfold slimEntry
  rw [slim704_eq]
  rfl
#print axioms frame704_eq
#print axioms slim704_eq
end InitECandidate.Proofs.StackAnalysis
