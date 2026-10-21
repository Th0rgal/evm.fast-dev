import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.BaselineMemoryDomains

/- Small metadata literals are checked against the compiler configuration once.
The predicates keep finite-index bound proofs independent of that large
configuration; ordinary decide checks the resulting small literal goals. -/
open scoped InitECandidate.Proofs.CompilerComputation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitE
open Flapjack

private def admissionMmio : List Compiler.Backend.LabToTarget.ShmemInfoNum :=
  [{ entryPc := 5216, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 11, exitPc := 5220 }, { entryPc := 5260, nbytes := BitVec.ofNat 8 0, addrReg := 13, addrOff := 0, reg := 12, exitPc := 5264 }, { entryPc := 5292, nbytes := BitVec.ofNat 8 0, addrReg := 12, addrOff := 0, reg := 10, exitPc := 5296 }, { entryPc := 9888, nbytes := BitVec.ofNat 8 0, addrReg := 10, addrOff := 0, reg := 11, exitPc := 9892 }, { entryPc := 10184, nbytes := BitVec.ofNat 8 0, addrReg := 12, addrOff := 0, reg := 12, exitPc := 10188 }, { entryPc := 10268, nbytes := BitVec.ofNat 8 1, addrReg := 5, addrOff := 0, reg := 13, exitPc := 10272 }, { entryPc := 902772, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 902776 }, { entryPc := 902972, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 902976 }, { entryPc := 903172, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 903176 }, { entryPc := 903372, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 903376 }, { entryPc := 903572, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 903576 }, { entryPc := 903772, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 903776 }, { entryPc := 903972, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 903976 }]

-- Reduce the large configuration projection once, before finite checks.
private theorem admission_mmio_eq : baselineMmio = admissionMmio := by
  unfold baselineMmio
  change baselineLabConfig.shmemExtra = admissionMmio
  rfl

private def admissionEntryPcs : List (BitVec 64) :=
  [BitVec.ofNat 64 2147488096,
    BitVec.ofNat 64 2147488080,
    BitVec.ofNat 64 2147488064,
    BitVec.ofNat 64 2147488048,
    BitVec.ofNat 64 2147488032,
    BitVec.ofNat 64 2147488016,
    BitVec.ofNat 64 2147488000,
    BitVec.ofNat 64 2147487984,
    BitVec.ofNat 64 2147487968,
    BitVec.ofNat 64 2147487952,
    BitVec.ofNat 64 2147487936,
    BitVec.ofNat 64 2147487920,
    BitVec.ofNat 64 2147487904,
    BitVec.ofNat 64 2147487888,
    BitVec.ofNat 64 2147487872,
    BitVec.ofNat 64 2147487856,
    BitVec.ofNat 64 2147487840,
    BitVec.ofNat 64 2147487824,
    BitVec.ofNat 64 2147487808,
    BitVec.ofNat 64 2147487792,
    BitVec.ofNat 64 2147493360,
    BitVec.ofNat 64 2147493404,
    BitVec.ofNat 64 2147493436,
    BitVec.ofNat 64 2147498032,
    BitVec.ofNat 64 2147498328,
    BitVec.ofNat 64 2147498412,
    BitVec.ofNat 64 2148390916,
    BitVec.ofNat 64 2148391116,
    BitVec.ofNat 64 2148391316,
    BitVec.ofNat 64 2148391516,
    BitVec.ofNat 64 2148391716,
    BitVec.ofNat 64 2148391916,
    BitVec.ofNat 64 2148392116]

private theorem admission_entry_pcs_eq : baselineEntryPcs = admissionEntryPcs := by
  unfold baselineEntryPcs
  rw [admission_mmio_eq]
  rfl

private theorem admission_names_length :
    baselineNames.length = 2 + baselineMmio.length := by
  calc
    baselineNames.length = baselineEntryPcs.length :=
      baseline_finite_facts.2.2.2.2
    _ = 2 + baselineMmio.length := by
      simp only [baselineEntryPcs, List.length_append, List.length_map, List.length_range]

private theorem admission_entry_nodup : baselineEntryPcs.Nodup := by
  simp only [admission_entry_pcs_eq]
  decide

private def admissionEntryConditions (pcs : List (BitVec 64)) : Prop :=
  ∀ i : Fin pcs.length,
    initialPc < pcs[i].toNat ∧ pcs[i].toNat < initialPc + 1028080 ∧
    holAligned 2 pcs[i] = true ∧
    pcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
    pcs[i] ≠ BitVec.ofNat 64 nativePc - 32

private def admissionMmioBounds
    (mmio : List Compiler.Backend.LabToTarget.ShmemInfoNum) : Prop :=
  ∀ i : Fin mmio.length,
    mmio[i].entryPc < 979140 ∧ nativePc + mmio[i].exitPc < initialPc + 1028080


private theorem admission_entry_conditions :
    (∀ i : Fin baselineEntryPcs.length,
      initialPc < baselineEntryPcs[i].toNat ∧
      baselineEntryPcs[i].toNat < initialPc + 1028080 ∧
      holAligned 2 baselineEntryPcs[i] = true ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 32) := by
  change admissionEntryConditions baselineEntryPcs
  rw [admission_entry_pcs_eq]
  unfold admissionEntryConditions
  decide


private theorem admission_mmio_bounds :
    (∀ i : Fin baselineMmio.length,
      baselineMmio[i].entryPc < 979140 ∧
      nativePc + baselineMmio[i].exitPc < initialPc + 1028080) := by
  change admissionMmioBounds baselineMmio
  rw [admission_mmio_eq]
  unfold admissionMmioBounds
  decide


-- Preserve the exported contract and all downstream projection selectors.
theorem baseline_submission_finite :
    baselineNames.length = 2 + baselineMmio.length ∧
    baselineEntryPcs.Nodup ∧
    (∀ i : Fin baselineEntryPcs.length,
      initialPc < baselineEntryPcs[i].toNat ∧
      baselineEntryPcs[i].toNat < initialPc + 1028080 ∧
      holAligned 2 baselineEntryPcs[i] = true ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 32) ∧
    (∀ i : Fin baselineMmio.length,
      baselineMmio[i].entryPc < 979140 ∧
      nativePc + baselineMmio[i].exitPc < initialPc + 1028080) := by
  exact ⟨admission_names_length, admission_entry_nodup,
    admission_entry_conditions, admission_mmio_bounds⟩

#print axioms baseline_submission_finite
end InitE
