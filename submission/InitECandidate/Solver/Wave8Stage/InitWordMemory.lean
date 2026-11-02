import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Proofs.MachineWordMemory

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.InitWordMemory
open Classical InitE Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- On every aligned data cell, the original good-initial-state contract
uniquely determines the supplied Word/Loc memory from the machine bytes. -/
theorem goodInitState_memory {S Q : Type}
    (mc : MachineConfig 64 S Q) (ms : S) (bytes : List (BitVec 8)) (cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (dm sdm : BitVec 64 → Bool)
    (initialized : goodInitState mc ms bytes cbspace t m dm sdm)
    (endian : mc.target.config.bigEndian = false)
    (a : BitVec 64) (aligned : a.toNat % 8 = 0) (inside : dm a = true) :
    m a = packedWordMemory (mc.target.getByte ms) a := by
  have good : goodDimindex 64 := .inr rfl
  have alignA : holByteAlign a = a := holByteAlign_of_aligned good a aligned
  obtain ⟨related,_,_,_,_,_,_,_,_,_,inDomain,closed,_,_,_,wordMemory,_,_⟩ := initialized
  obtain ⟨w,_,wordEq⟩ := wordMemory a
  rw [alignA] at wordEq
  have lane : ∀ i : Fin 8, mc.target.getByte ms (a + BitVec.ofNat 64 i.val) =
      HolByte.getByte (BitVec.ofNat 64 i.val) w false := by
    intro i
    have alignLane : holByteAlign (a + BitVec.ofNat 64 i.val) = a :=
      holByteAlign_aligned_add good a aligned i.val i.isLt
    have domainLane : dm (a + BitVec.ofNat 64 i.val) = true :=
      closed _ (by rw [alignLane]; exact inside)
    obtain ⟨v,byteEq,memoryEq⟩ := wordMemory (a + BitVec.ofNat 64 i.val)
    rw [alignLane,wordEq] at memoryEq
    cases memoryEq
    rw [related.2.2.1 _ (inDomain _ domainLane),byteEq,endian]
    simp only [HolByte.getByte]
    rw [byteIndex_aligned_add good a aligned i.val i.isLt]
    congr 2
    simp [HolByte.byteIndex,BitVec.toNat_ofNat,Nat.mod_eq_of_lt i.isLt]
  rw [wordEq]
  apply congrArg WordLocW.word
  exact (packedMemoryWord_of_bytes (mc.target.getByte ms) a w
    (InitCodeThm.byteAligned_iff good a |>.2 aligned) lane).symm

#print axioms goodInitState_memory
end InitECandidate.Solver.Wave8Stage.InitWordMemory
