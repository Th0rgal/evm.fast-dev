import InitECandidate.Proofs.HeaderInstallation
import InitECandidate.Solver.FastBaselineState
import InitECandidate.Proofs.CompilerOracles
import InitECandidate.Solver.Wave8Stage.InitWordMemory

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteInitMemory
open Classical InitE Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver.FastEnv
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

abbrev dataDomain (oracles : List (Option (Spt Nat))) (t : AsmState 64)
    (bitmapsDm : BitVec 64 → Bool) : BitVec 64 → Bool :=
  fun addr => decide (t.regs (StackNames.findNameSpt
    (oracleCompilerConfig oracles).stackConf.regNames 2) ≤ addr ∧
    addr < t.regs (StackNames.findNameSpt
      (oracleCompilerConfig oracles).stackConf.regNames 4)) || bitmapsDm addr

theorem registers (oracles : List (Option (Spt Nat)))
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (dataDomain oracles t bitmapsDm) sdm) :
    t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2) =
      BitVec.ofNat 64 sourceBase ∧
    t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 3) =
      BitVec.ofNat 64 stackStart ∧
    t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4) =
      BitVec.ofNat 64 ramEnd := by
  have relation := initialized.1.2.2.2.1
  constructor
  · have idx : StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2 = 11 := by
      simp only [oracleCompilerConfig,RiscVConfig.pancakeRiscVBackendConfig,
        Flapjack.Compiler.pancakeBackendConf,RiscVConfig.riscvBackendConfig,
        StackNames.findNameSpt,RiscVConfig.riscvNames]
      simp [sptLookup,sptInsert]
    rw [idx]
    have value : baselineMachineConfig.target.getReg baselineInstalledState 11 = BitVec.ofNat 64 sourceBase := rfl
    exact (relation 11 ⟨by decide,by decide⟩).symm.trans value
  constructor
  · have idx : StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 3 = 12 := by
      simp only [oracleCompilerConfig,RiscVConfig.pancakeRiscVBackendConfig,
        Flapjack.Compiler.pancakeBackendConf,RiscVConfig.riscvBackendConfig,
        StackNames.findNameSpt,RiscVConfig.riscvNames]
      simp [sptLookup,sptInsert]
    rw [idx]
    have value : baselineMachineConfig.target.getReg baselineInstalledState 12 = BitVec.ofNat 64 stackStart := rfl
    exact (relation 12 ⟨by decide,by decide⟩).symm.trans value
  · have idx : StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4 = 13 := by
      simp only [oracleCompilerConfig,RiscVConfig.pancakeRiscVBackendConfig,
        Flapjack.Compiler.pancakeBackendConf,RiscVConfig.riscvBackendConfig,
        StackNames.findNameSpt,RiscVConfig.riscvNames]
      simp [sptLookup,sptInsert]
    rw [idx]
    have value : baselineMachineConfig.target.getReg baselineInstalledState 13 = BitVec.ofNat 64 ramEnd := rfl
    exact (relation 13 ⟨by decide,by decide⟩).symm.trans value

/-- All aligned heap/stack words are determined by the installed machine,
regardless of the supplied bitmap domain. -/
theorem heap_word (oracles : List (Option (Spt Nat)))
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (dataDomain oracles t bitmapsDm) sdm)
    (a : BitVec 64) (aligned : a.toNat % 8 = 0)
    (inside : sourceBase ≤ a.toNat ∧ a.toNat < ramEnd) :
    m a = packedWordMemory installedMemory a := by
  obtain ⟨reg2,_,reg4⟩ := registers oracles t m bitmapsDm sdm initialized
  have domain : dataDomain oracles t bitmapsDm a = true := by
    simp only [dataDomain,reg2,reg4,Bool.or_eq_true,decide_eq_true_eq]
    left
    have baseSmall : sourceBase % 2^64 = sourceBase := by decide
    have endSmall : ramEnd % 2^64 = ramEnd := by decide
    simpa only [BitVec.le_def,BitVec.lt_def,BitVec.toNat_ofNat,baseSmall,endSmall] using inside
  exact InitWordMemory.goodInitState_memory baselineMachineConfig baselineInstalledState
    InitECandidate.nativeCode 3788 t m _ sdm initialized rfl a aligned domain

/-- The five bootstrap header words are fixed by `goodInitState`. -/
theorem headers (oracles : List (Option (Spt Nat)))
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (dataDomain oracles t bitmapsDm) sdm)
    (i : Fin 5) :
    m (BitVec.ofNat 64 (sourceBase+8*i.val)) = .word Guest.startupHeaders[i] := by
  have hi := i.isLt
  rw [heap_word oracles t m bitmapsDm sdm initialized]
  · exact congrArg WordLocW.word (baseline_source_headers i)
  · simp only [BitVec.toNat_ofNat]
    have small : sourceBase+8*i.val < 2^64 := by
      norm_num [sourceBase] at *
      omega
    rw [Nat.mod_eq_of_lt small]
    norm_num [sourceBase,Nat.add_mod,Nat.mul_mod_right]
  · simp only [BitVec.toNat_ofNat]
    have small : sourceBase+8*i.val < 2^64 := by
      norm_num [sourceBase] at *
      omega
    rw [Nat.mod_eq_of_lt small]
    norm_num [sourceBase,ramEnd,ramStart,ramSize] at *
    omega

#print axioms headers

#print axioms registers
#print axioms heap_word
end InitECandidate.Solver.Wave8Stage.ConcreteInitMemory
