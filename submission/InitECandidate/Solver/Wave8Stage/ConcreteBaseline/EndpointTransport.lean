import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.Configuration
import InitECandidate.Solver.Wave8Stage.InitializedTransfer

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteBaseline
open InitE InitECandidate.Proofs
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3

/-- Only fields observed by the installation contract must agree. -/
structure InstallationAgreement {S Q : Type} (mc : MachineConfig 64 S Q)
    (before after : S) : Prop where
  ok : mc.target.stateOk after = true
  pc : mc.target.getPc after = mc.target.getPc before
  bytes : ∀ a, mc.progAddresses a → mc.target.getByte after a = mc.target.getByte before a
  regs : ∀ r, r < mc.target.config.regCount ∧ mc.target.config.avoidRegs.contains r = false →
    mc.target.getReg after r = mc.target.getReg before r
  fpRegs : ∀ r, r < mc.target.config.fpRegCount →
    mc.target.getFpReg after r = mc.target.getFpReg before r

theorem goodInitState_transport {S Q : Type} {mc : MachineConfig 64 S Q}
    {before after : S} (agreement : InstallationAgreement mc before after)
    {bytes : List (BitVec 8)} {cbspace : Nat} {t : AsmState 64}
    {m : BitVec 64 → WordLocW 64} {dm sdm : BitVec 64 → Bool}
    (initial : goodInitState mc before bytes cbspace t m dm sdm) :
    goodInitState mc after bytes cbspace t m dm sdm := by
  rcases initial with ⟨related, configured, pc, start, aligned, next, ffi, cache,
    loaded, inMem, domain, byteDomain, shared, sharedByte, disjoint, packed, buffer, size⟩
  have relation : targetStateRel mc.target t after := by
    refine ⟨agreement.ok, agreement.pc.trans related.2.1, ?_, ?_, ?_⟩
    · intro a ha
      rw [agreement.bytes a (by rw [← configured.2.2.2.1]; exact ha)]
      exact related.2.2.1 a ha
    · intro r hr
      rw [agreement.regs r hr]
      exact related.2.2.2.1 r hr
    · intro r hr
      rw [agreement.fpRegs r hr]
      exact related.2.2.2.2 r hr
  have code : codeLoaded bytes mc after := by
    classical
    have memory : (fun a => if mc.progAddresses a then some (mc.target.getByte after a) else none) =
        (fun a => if mc.progAddresses a then some (mc.target.getByte before a) else none) := by
      funext a
      by_cases ha : mc.progAddresses a
      · simp only [if_pos ha, agreement.bytes a ha]
      · simp only [if_neg ha]
    simpa only [codeLoaded, agreement.pc, memory] using loaded
  exact ⟨relation, configured, by rw [agreement.pc]; exact pc, start, aligned,
    next, ffi, cache, code, inMem, domain, byteDomain, shared, sharedByte,
    disjoint, packed, buffer, size⟩

theorem baseline_endpoint_agreement (post : riscv_state)
    (related : targetStateRel riscvTarget installedAsm post) :
    InstallationAgreement baselineMachineConfig baselineInstalledState post := by
  have canonical := machineStateOfAsm_relation installedAsm (by decide)
  refine ⟨related.1, related.2.1.trans canonical.2.1.symm, ?_, ?_, ?_⟩
  · intro a ha
    exact (related.2.2.1 a ha).trans (canonical.2.2.1 a ha).symm
  · intro r hr
    exact (related.2.2.2.1 r hr).trans (canonical.2.2.2.1 r hr).symm
  · intro r hr
    exact (related.2.2.2.2 r hr).trans (canonical.2.2.2.2 r hr).symm

/-- The complete Lab relation transports to the actual startup endpoint.
The outer machine-state argument to shareMemStateRel is definitionally unused. -/
theorem stateRel_transport {S Q F : Type} {mc : MachineConfig 64 S Q}
    {before after : S} (agreement : InstallationAgreement mc before after)
    (code : LabProgHOL 64) (labs : Spt (Spt Nat)) (base : BitVec 64)
    (lab : LabSem.State 64 Config F) (t : AsmState 64)
    (related : LabToTarget.stateRel (mc, code, labs, base) lab t before) :
    LabToTarget.stateRel (mc, code, labs, base) lab t after := by
  have relation : targetStateRel mc.target t after := by
    refine ⟨agreement.ok, agreement.pc.trans related.1.2.1, ?_, ?_, ?_⟩
    · intro a ha
      exact (agreement.bytes a (by rw [related.2.2.1]; exact ha)).trans (related.1.2.2.1 a ha)
    · intro r hr
      exact (agreement.regs r hr).trans (related.1.2.2.2.1 r hr)
    · intro r hr
      exact (agreement.fpRegs r hr).trans (related.1.2.2.2.2 r hr)
  exact ⟨relation, related.2⟩

/-- All fourteen standard initialization guards survive the actual endpoint. -/
theorem initialization_transport {mc : MachineConfig 64 riscv_state RiscVProjection}
    {before after : riscv_state} (agreement : InstallationAgreement mc before after)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : InitializedTransfer.Initialization mc before code code2 labs clock i cbspace
      t m dm sdm coracle names info shiftedInfo) :
    InitializedTransfer.Initialization mc after code code2 labs clock i cbspace
      t m dm sdm coracle names info shiftedInfo := by
  rcases init with ⟨a,b,c,d,e,f,g,h,j,k,l,n,o,p⟩
  exact ⟨a,b,c,d,e,goodInitState_transport agreement f,g,
    by simpa only [agreement.pc] using h,j,k,l,n,o,
    by simpa only [agreement.pc] using p⟩

#print axioms goodInitState_transport
#print axioms baseline_endpoint_agreement
#print axioms stateRel_transport
#print axioms initialization_transport
end InitECandidate.Solver.Wave8Stage.ConcreteBaseline
