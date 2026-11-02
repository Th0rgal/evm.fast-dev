import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

/-! Counted-loop leaves (5 leaves) for Wave 8 shard s14 (`wave8/leaves-s14`).
Imports only the light cone via `campaign.leaves.s14.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_evm_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_heap_release K_keccak256 K_memzero : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release)
    (h_keccak256 : TerminatingFunBoundedOn P (ofString "keccak256") K_keccak256)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero) :
    TerminatingFunBoundedOn P (ofString "evm_init")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_heap_release + 1) + (K_alloc + 1) + (K_keccak256 + 1) + (K_alloc + 1) + (2 ^ 64 + 1) * (0 + 1) + (K_alloc + 1) + (K_memzero + 1) + (K_alloc + 1) + (K_memzero + 1) + (K_alloc + 1) + (K_alloc + 1)) := by
  fb_prove hP 566 Guest.Software.guestFn_evm_init

theorem fb_fork_init_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_memzero K_addr_from_words K_st_be64 : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_addr_from_words : TerminatingFunBoundedOn P (ofString "addr_from_words") K_addr_from_words)
    (h_st_be64 : TerminatingFunBoundedOn P (ofString "st_be64") K_st_be64) :
    TerminatingFunBoundedOn P (ofString "fork_init")
      ((K_alloc + 1) + (K_memzero + 1) + (K_alloc + 1) + (K_memzero + 1) + (2 ^ 64 + 1) * (0 + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_addr_from_words + 1) + (K_alloc + 1) + (K_st_be64 + 1) + (K_st_be64 + 1) + (K_st_be64 + 1) + (K_st_be64 + 1)) := by
  fb_prove hP 861 Guest.Software.guestFn_fork_init

theorem fb_htr_pcontainer_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_merkleize_progressive K_memzero K_sha256_pair K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_merkleize_progressive : TerminatingFunBoundedOn P (ofString "merkleize_progressive") K_merkleize_progressive)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_sha256_pair : TerminatingFunBoundedOn P (ofString "sha256_pair") K_sha256_pair)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_pcontainer")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_merkleize_progressive + 1) + (K_memzero + 1) + (2 ^ 64 + 1) * (0 + 1) + (K_sha256_pair + 1) + (K_heap_release + 1)) := by
  fb_prove hP 191 Guest.Software.guestFn_htr_pcontainer

theorem fb_htr_payload_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_memcpy K_htr_bytes_vector K_htr_u64_at K_htr_bytes_list
     K_htr_pbytes K_htr_plist_chunks K_heap_release K_htr_withdrawal K_htr_pcontainer : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_htr_bytes_vector : TerminatingFunBoundedOn P (ofString "htr_bytes_vector") K_htr_bytes_vector)
    (h_htr_u64_at : TerminatingFunBoundedOn P (ofString "htr_u64_at") K_htr_u64_at)
    (h_htr_bytes_list : TerminatingFunBoundedOn P (ofString "htr_bytes_list") K_htr_bytes_list)
    (h_htr_pbytes : TerminatingFunBoundedOn P (ofString "htr_pbytes") K_htr_pbytes)
    (h_htr_plist_chunks : TerminatingFunBoundedOn P (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release)
    (h_htr_withdrawal : TerminatingFunBoundedOn P (ofString "htr_withdrawal") K_htr_withdrawal)
    (h_htr_pcontainer : TerminatingFunBoundedOn P (ofString "htr_pcontainer") K_htr_pcontainer) :
    TerminatingFunBoundedOn P (ofString "htr_payload")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_memcpy + 1) + (K_htr_bytes_vector + 1) + (K_memcpy + 1) + (K_memcpy + 1) + (K_htr_bytes_vector + 1) + (K_memcpy + 1) + (K_htr_u64_at + 1) + (K_htr_u64_at + 1) + (K_htr_u64_at + 1) + (K_htr_u64_at + 1) + (K_htr_bytes_list + 1) + (K_memcpy + 1) + (K_memcpy + 1) + (K_heap_mark + 1) + (K_alloc + 1) + (2 ^ 64 + 1) * ((K_htr_pbytes + 1) + 1) + (K_htr_plist_chunks + 1) + (K_heap_release + 1) + (K_alloc + 1) + (2 ^ 64 + 1) * ((K_htr_withdrawal + 1) + 1) + (K_htr_plist_chunks + 1) + (K_heap_release + 1) + (K_htr_u64_at + 1) + (K_htr_u64_at + 1) + (K_htr_pbytes + 1) + (K_htr_u64_at + 1) + (K_htr_pcontainer + 1) + (K_heap_release + 1)) := by
  fb_prove hP 210 Guest.Software.guestFn_htr_payload

theorem fb_htr_request_list_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_heap_mark K_alloc K_htr_deposit K_htr_wdreq K_htr_cons K_htr_bdep K_htr_bexit
     K_htr_plist_chunks K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htr_deposit : TerminatingFunBoundedOn P (ofString "htr_deposit") K_htr_deposit)
    (h_htr_wdreq : TerminatingFunBoundedOn P (ofString "htr_wdreq") K_htr_wdreq)
    (h_htr_cons : TerminatingFunBoundedOn P (ofString "htr_cons") K_htr_cons)
    (h_htr_bdep : TerminatingFunBoundedOn P (ofString "htr_bdep") K_htr_bdep)
    (h_htr_bexit : TerminatingFunBoundedOn P (ofString "htr_bexit") K_htr_bexit)
    (h_htr_plist_chunks : TerminatingFunBoundedOn P (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "htr_request_list")
      ((K_heap_mark + 1) + (K_alloc + 1) + (2 ^ 64 + 1) * (Nat.max ((K_htr_deposit + 1)) (0) + Nat.max ((K_htr_wdreq + 1)) (0) + Nat.max ((K_htr_cons + 1)) (0) + Nat.max ((K_htr_bdep + 1)) (0) + Nat.max ((K_htr_bexit + 1)) (0) + 1) + (K_htr_plist_chunks + 1) + (K_heap_release + 1)) := by
  fb_prove hP 216 Guest.Software.guestFn_htr_request_list

end InitECandidate.Solver.Wave8Leaves.S14
