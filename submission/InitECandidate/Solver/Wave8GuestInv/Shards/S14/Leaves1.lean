import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

/-! Loop-free leaves batch 1 for Wave 8 shard s14 (`wave8/leaves-s14`).
Imports only the light cone via `campaign.leaves.s14.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_header_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_memzero : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero) :
    TerminatingFunBoundedOn P (ofString "header_init")
      ((K_alloc + 1) + (K_memzero + 1)) := by
  fb_prove hP 238 Guest.Software.guestFn_header_init

theorem fb_htr_u64_at_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_memzero K_memcpy : Nat}
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy) :
    TerminatingFunBoundedOn P (ofString "htr_u64_at")
      ((K_memzero + 1) + (K_memcpy + 1)) := by
  fb_prove hP 195 Guest.Software.guestFn_htr_u64_at

theorem fb_mix_in_length_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_memzero K_st_le64 K_sha256_pair : Nat}
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_st_le64 : TerminatingFunBoundedOn P (ofString "st_le64") K_st_le64)
    (h_sha256_pair : TerminatingFunBoundedOn P (ofString "sha256_pair") K_sha256_pair) :
    TerminatingFunBoundedOn P (ofString "mix_in_length")
      ((K_memzero + 1) + (K_st_le64 + 1) + (K_sha256_pair + 1)) := by
  fb_prove hP 187 Guest.Software.guestFn_mix_in_length

theorem fb_htr_plist_chunks_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_merkleize_progressive K_mix_in_length : Nat}
    (h_merkleize_progressive : TerminatingFunBoundedOn P (ofString "merkleize_progressive") K_merkleize_progressive)
    (h_mix_in_length : TerminatingFunBoundedOn P (ofString "mix_in_length") K_mix_in_length) :
    TerminatingFunBoundedOn P (ofString "htr_plist_chunks")
      ((K_merkleize_progressive + 1) + (K_mix_in_length + 1)) := by
  fb_prove hP 189 Guest.Software.guestFn_htr_plist_chunks

theorem fb_mem_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (_hP : MetadataInv P) :
    TerminatingFunBoundedOn P (ofString "mem_init") 0 := by
  fb_prove _hP 6 Guest.Software.guestFn_mem_init

theorem fb_mpt_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_keccak256 : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_keccak256 : TerminatingFunBoundedOn P (ofString "keccak256") K_keccak256) :
    TerminatingFunBoundedOn P (ofString "mpt_init")
      ((K_alloc + 1) + (K_alloc + 1) + (K_alloc + 1) + (K_alloc + 1) + (K_alloc + 1) + (K_keccak256 + 1) + (K_keccak256 + 1)) := by
  fb_prove hP 247 Guest.Software.guestFn_mpt_init

theorem fb_htr_bytes_list_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_pack_bytes K_merkleize K_heap_release K_mix_in_length : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_pack_bytes : TerminatingFunBoundedOn P (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release)
    (h_mix_in_length : TerminatingFunBoundedOn P (ofString "mix_in_length") K_mix_in_length) :
    TerminatingFunBoundedOn P (ofString "htr_bytes_list")
      ((K_heap_mark + 1) + (K_pack_bytes + 1) + (K_merkleize + 1) + (K_heap_release + 1) + (K_mix_in_length + 1)) := by
  fb_prove hP 194 Guest.Software.guestFn_htr_bytes_list

theorem fb_htr_pbytes_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_pack_bytes K_htr_plist_chunks K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_pack_bytes : TerminatingFunBoundedOn P (ofString "pack_bytes") K_pack_bytes)
    (h_htr_plist_chunks : TerminatingFunBoundedOn P (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_pbytes")
      ((K_heap_mark + 1) + (K_pack_bytes + 1) + (K_htr_plist_chunks + 1) + (K_heap_release + 1)) := by
  fb_prove hP 190 Guest.Software.guestFn_htr_pbytes

end InitECandidate.Solver.Wave8Leaves.S14
