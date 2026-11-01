import InitECandidate.Proofs.BootstrapMemory
import InitECandidate.Proofs.CompilerConfigLiteral

/-! The actual baseline machine definitions, separated from installation
proofs. Definition bodies are copied without alteration from FastBaselineEnv;
only their owning namespace differs. The ROM and challenge machine constructor
are the original imported objects, not replacement constants. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteBaseline
open Classical InitE InitECandidate.Proofs
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc

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

theorem machineStateOfAsm_mode (t : AsmState 64) :
    ((machineStateOfAsm t).c_MCSR (machineStateOfAsm t).procID).mstatus.MPRV = 3 ∧
    ((machineStateOfAsm t).c_MCSR (machineStateOfAsm t).procID).mstatus.VM = 0 :=
  ⟨rfl,rfl⟩

theorem machineStateOfAsm_ok (t : AsmState 64) (hpc : holAligned 2 t.pc = true) :
    riscvOk (machineStateOfAsm t) = true := by
  exact (riscvOk_iff _).mpr ⟨rfl,rfl,rfl,rfl,hpc⟩

theorem machineStateOfAsm_relation (t : AsmState 64) (hpc : holAligned 2 t.pc = true) :
    targetStateRel riscvTarget t (machineStateOfAsm t) := by
  refine ⟨machineStateOfAsm_ok t hpc, rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro i hi
    have hilt : i < 32 := hi.1
    change t.regs (BitVec.ofNat 5 i).toNat = t.regs i
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt]
  · intro i hi
    have : i < 0 := hi
    omega

noncomputable def baselineInstalledState : riscv_state := machineStateOfAsm installedAsm

/-- The fixed startup environment: submitted ROM, zero ordinary RAM/registers,
and public input/output bytes supplied by the common host oracle. -/
noncomputable def baselineInitialState (input : Guest.InputBlob) : riscv_state :=
  { (machineStateOfAsm initialAsm) with MEM8 := (fun a =>
      if (machineSharedDomain a) then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) }

theorem baselineInitialState_mode (input : Guest.InputBlob) :
    ((baselineInitialState input).c_MCSR (baselineInitialState input).procID).mstatus.MPRV = 3 ∧
    ((baselineInitialState input).c_MCSR (baselineInitialState input).procID).mstatus.VM = 0 :=
  ⟨rfl,rfl⟩

theorem baselineInitialState_related (input : Guest.InputBlob) :
    targetStateRel riscvTarget initialAsm (baselineInitialState input) := by
  have canonical := machineStateOfAsm_relation initialAsm (by decide)
  refine ⟨?_,canonical.2.1,?_,canonical.2.2.2.1,?_⟩
  · exact (riscvOk_iff (baselineInitialState input)).mpr ⟨rfl,rfl,rfl,rfl,by change holAligned 2 (BitVec.ofNat 64 initialPc) = true; decide⟩
  · intro a domain
    change (if (machineSharedDomain a) then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) = initialMemory a
    exact if_neg domain.1.2
  · intro r hr
    have : r < 0 := hr
    omega

theorem baselineInitialState_ram_zero (input : Guest.InputBlob) (a : BitVec 64)
    (ram : ramStart ≤ a.toNat) (ordinary : ¬ machineSharedDomain a) :
    (baselineInitialState input).MEM8 a = 0 := by
  change (if (machineSharedDomain a) then _ else initialMemory a) = 0
  rw [if_neg ordinary]
  exact initial_ram_zero a ram

theorem baselineInitialState_registers_zero (input : Guest.InputBlob) (r : BitVec 5) :
    (baselineInitialState input).c_gpr (baselineInitialState input).procID r = 0 := rfl


/-- The actual installed code base; the native-image shift belongs only to
the code-buffer position. -/
theorem installed_pc :
    baselineMachineConfig.target.getPc baselineInstalledState = (0x80001070 : BitVec 64) := rfl

theorem target_is_riscv : baselineMachineConfig.target = riscvTarget := rfl

#print axioms machineStateOfAsm_relation
#print axioms baselineInitialState_related
#print axioms installed_pc
end InitECandidate.Solver.Wave8Stage.ConcreteBaseline
