import InitECandidate.Proofs.BootstrapMemory
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem installed_memory_bitmap_copy (index byte : Nat)
    (hi : index < 4603) (hj : byte < 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte) =
      initialMemory (BitVec.ofNat 64 (initDataRom+24+8*index+byte)) := by
  have ha : (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte).toNat =
      initDataRam+24+8*index+byte := by
    rw [BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [initDataRam]; omega)]
  have hs : ¬ (sourceBase ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < sourceBase+40) := by
    simp only [sourceBase,initDataRam]; omega
  have hd : ¬ (initDataRam ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < initDataRam+24) := by omega
  have hb : initDataRam+24 ≤ initDataRam+24+8*index+byte ∧
      initDataRam+24+8*index+byte < initDataEnd := by
    simp only [initDataRam,initDataEnd]; omega
  rw [installedMemory,ha,if_neg hs,if_neg hd,if_pos hb]
  have hrom : initDataRom+(initDataRam+24+8*index+byte)-initDataRam = initDataRom+24+8*index+byte := by omega
  rw [hrom]


end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
