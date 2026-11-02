import InitECandidate.Proofs.CompilerConfigLiteral
import InitECandidate.Proofs.BootstrapMemory

set_option autoImplicit false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget

@[irreducible] def baselineNames : List HolFfiName := baselineLabConfig.ffiNames.getD []

@[irreducible] def baselineMmio : List ShmemInfoNum := baselineLabConfig.shmemExtra

def dispatchAddress (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((1+i)*ffiOffset)

def baselineEntryPcs : List (BitVec 64) :=
  ((List.range 2).map fun i => BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i)*ffiOffset)) ++
    (baselineMmio.map fun rec => BitVec.ofNat 64 nativePc + BitVec.ofNat 64 rec.entryPc)

/-- Only ordinary dispatch addresses are removed. Native MMIO instructions
remain loaded program bytes and are intercepted through ffiEntryPcs. -/
def programDomain (a : BitVec 64) : Prop :=
  bootstrapDomain a

noncomputable def baselineMachineConfig : MachineConfig 64 riscv_state RiscVProjection :=
  challengeMachineConfig (BitVec.ofNat 64 nativePc) programDomain machineSharedDomain
    baselineNames 2 baselineMmio

/-- Explicit reduced integer RISC-V machine: machine privilege, identity
translation, no pending transfer and no exception. -/
def machineStateOfAsm (t : AsmState 64) : riscv_state :=
  { (default : riscv_state) with
    MEM8 := t.mem
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MPRV := 3, VM := 0 }
      mcpuid := { (default : mcpuid) with ArchBase := 2 } }
    c_PC := fun _ => t.pc
    c_gpr := fun _ r => t.regs r.toNat
    c_NextFetch := fun _ => none
    exception := .NoException }

noncomputable def baselineInstalledState : riscv_state := machineStateOfAsm installedAsm

end InitECandidate.Solver.FastEnv
