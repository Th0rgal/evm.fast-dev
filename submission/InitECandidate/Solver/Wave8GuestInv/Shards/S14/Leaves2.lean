import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

/-! Loop-free leaves batch 2 (9 leaves) for Wave 8 shard s14 (`wave8/leaves-s14`).
Imports only the light cone via `campaign.leaves.s14.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_htr_bytes_vector_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_memzero K_memcpy K_heap_mark K_pack_bytes K_merkleize K_heap_release : Nat}
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_pack_bytes : TerminatingFunBoundedOn P (ofString "pack_bytes") K_pack_bytes)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_bytes_vector")
      (Nat.max ((K_memzero + 1) + (K_memcpy + 1)) (0) + (K_heap_mark + 1) + (K_pack_bytes + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 193 Guest.Software.guestFn_htr_bytes_vector

theorem fb_htr_bdep_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_bytes_vector K_memcpy K_htr_u64_at K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_htr_u64_at : TerminatingFunBoundedOn P (ofString "htr_u64_at") K_htr_u64_at)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_bdep")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_bytes_vector + 1) + (K_memcpy + 1) + (K_htr_u64_at + 1) + (K_htr_bytes_vector + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 214 Guest.Software.guestFn_htr_bdep

theorem fb_htr_bexit_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_bytes_vector K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_bexit")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_bytes_vector + 1) + (K_htr_bytes_vector + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 215 Guest.Software.guestFn_htr_bexit

theorem fb_htr_cons_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_bytes_vector K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_cons")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_bytes_vector + 1) + (K_htr_bytes_vector + 1) + (K_htr_bytes_vector + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 213 Guest.Software.guestFn_htr_cons

theorem fb_htr_deposit_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_bytes_vector K_memcpy K_htr_u64_at K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_htr_u64_at : TerminatingFunBoundedOn P (ofString "htr_u64_at") K_htr_u64_at)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_deposit")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_bytes_vector + 1) + (K_memcpy + 1) + (K_htr_u64_at + 1) + (K_htr_bytes_vector + 1) + (K_htr_u64_at + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 211 Guest.Software.guestFn_htr_deposit

theorem fb_htr_withdrawal_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_u64_at K_htr_bytes_vector K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_u64_at : TerminatingFunBoundedOn P (ofString "htr_u64_at") K_htr_u64_at)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_withdrawal")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_u64_at + 1) + (K_htr_u64_at + 1) + (K_htr_bytes_vector + 1) + (K_htr_u64_at + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 208 Guest.Software.guestFn_htr_withdrawal

theorem fb_htr_wdreq_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_bytes_vector K_htr_u64_at K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_htr_u64_at : TerminatingFunBoundedOn P (ofString "htr_u64_at") K_htr_u64_at)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_wdreq")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_bytes_vector + 1) + (K_htr_bytes_vector + 1) + (K_htr_u64_at + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 212 Guest.Software.guestFn_htr_wdreq

theorem fb_htr_requests_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_request_list K_htr_pcontainer K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_request_list : TerminatingFunBoundedOn P (ofString "htr_request_list") K_htr_request_list)
    (h_htr_pcontainer : TerminatingFunBoundedOn P (ofString "htr_pcontainer") K_htr_pcontainer)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_requests")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_request_list + 1) + (K_htr_request_list + 1) + (K_htr_request_list + 1) + (K_htr_request_list + 1) + (K_htr_request_list + 1) + (K_htr_pcontainer + 1) + (K_heap_release + 1)) := by
  fb_prove hP 217 Guest.Software.guestFn_htr_requests

theorem fb_htr_new_payload_request_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_payload K_htr_plist_chunks K_memcpy K_htr_requests K_merkleize K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_payload : TerminatingFunBoundedOn P (ofString "htr_payload") K_htr_payload)
    (h_htr_plist_chunks : TerminatingFunBoundedOn P (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_htr_requests : TerminatingFunBoundedOn P (ofString "htr_requests") K_htr_requests)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_new_payload_request")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_htr_payload + 1) + (K_htr_plist_chunks + 1) + (K_memcpy + 1) + (K_htr_requests + 1) + (K_merkleize + 1) + (K_heap_release + 1)) := by
  fb_prove hP 218 Guest.Software.guestFn_htr_new_payload_request

end InitECandidate.Solver.Wave8Leaves.S14
