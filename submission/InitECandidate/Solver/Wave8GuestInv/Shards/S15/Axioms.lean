import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S15.Leaves

/-! Axioms and `type_of%` evidence for shard s15 (`wave8/leaves-s15`).

Each `example` checks that the proved theorem has the exact spec statement
(`type_of% Wave8GuestInv.«fb_f»`), taking as explicit hypotheses the spec statements of any
callee leaves it requires.
Every `#print axioms` line must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.S15

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Leaves.S15

theorem metadataInv_guestInv : MetadataInv (@Wave8GuestInv.GuestInv) :=
  fun hcode hmem hsh hbase h => Wave8GuestInv.guestInv_congr hcode hmem hsh hbase h

-- 1. fb_output_write (idx 30)
theorem fb_output_write_of :
    type_of% Wave8GuestInv.«fb_output_write» :=
  fb_output_write_on metadataInv_guestInv

example : type_of% @fb_output_write_of =
    (type_of% Wave8GuestInv.«fb_output_write») := rfl

-- 2. fb_serialize_result (idx 219)
theorem fb_serialize_result_of :
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_st_le64» →
    type_of% Wave8GuestInv.«fb_serialize_result» :=
  fb_serialize_result_on metadataInv_guestInv

example : type_of% @fb_serialize_result_of =
    (type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_st_le64» →
     type_of% Wave8GuestInv.«fb_serialize_result») := rfl

-- 3. fb_ssz_init (idx 185)
theorem fb_ssz_init_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_init» :=
  fb_ssz_init_on metadataInv_guestInv

example : type_of% @fb_ssz_init_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_ssz_init») := rfl


end InitECandidate.Solver.Wave8GuestInv.S15
