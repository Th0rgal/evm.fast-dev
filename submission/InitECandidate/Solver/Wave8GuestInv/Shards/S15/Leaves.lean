import InitECandidate.Solver.Wave8GuestInv.Shards.S15.Core

/-! All 3 leaves for Wave 8 shard s15 (`wave8/leaves-s15`).
Imports only the light cone via `campaign.leaves.s15.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S15

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_output_write_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P) :
    TerminatingFunBoundedOn P (ofString "output_write")
      ((2 ^ 64 + 1) * (0 + 1)) := by
  fb_prove hP 30 Guest.Software.guestFn_output_write

theorem fb_serialize_result_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_memcpy K_st_le64 : Nat}
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_st_le64 : TerminatingFunBoundedOn P (ofString "st_le64") K_st_le64) :
    TerminatingFunBoundedOn P (ofString "serialize_result")
      ((K_memcpy + 1) + (K_st_le64 + 1)) := by
  fb_prove hP 219 Guest.Software.guestFn_serialize_result

theorem fb_ssz_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc) :
    TerminatingFunBoundedOn P (ofString "ssz_init")
      ((K_alloc + 1) + (K_alloc + 1) + (K_alloc + 1)) := by
  fb_prove hP 185 Guest.Software.guestFn_ssz_init

end InitECandidate.Solver.Wave8Leaves.S15
