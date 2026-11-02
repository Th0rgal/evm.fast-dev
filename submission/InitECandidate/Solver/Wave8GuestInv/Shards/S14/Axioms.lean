import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Leaves1
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Leaves2
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Loops
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Merkleize
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Progressive

/-! Axioms and `type_of%` evidence for shard s14 (`wave8/leaves-s14`).

Each `example` checks that the proved theorem has the exact spec statement
(`type_of% Wave8GuestInv.«fb_f»`), taking as explicit hypotheses the spec statements of any
callee leaves it requires.
Every `#print axioms` line must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.S14

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Leaves.S14

theorem metadataInv_guestInv : MetadataInv (@Wave8GuestInv.GuestInv) :=
  fun hcode hmem hsh hbase h => Wave8GuestInv.guestInv_congr hcode hmem hsh hbase h

theorem ordinaryMem_guestInv : OrdinaryMem (@Wave8GuestInv.GuestInv) :=
  fun _ h => h.memaddrs

-- 1. fb_evm_init (idx 566)
theorem fb_evm_init_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_evm_init» :=
  fb_evm_init_on metadataInv_guestInv

example : type_of% @fb_evm_init_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_keccak256» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_evm_init») := rfl

-- 2. fb_fork_init (idx 861)
theorem fb_fork_init_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_addr_from_words» →
    type_of% Wave8GuestInv.«fb_st_be64» →
    type_of% Wave8GuestInv.«fb_fork_init» :=
  fb_fork_init_on metadataInv_guestInv

example : type_of% @fb_fork_init_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_addr_from_words» →
     type_of% Wave8GuestInv.«fb_st_be64» →
     type_of% Wave8GuestInv.«fb_fork_init») := rfl

-- 3. fb_header_init (idx 238)
theorem fb_header_init_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_header_init» :=
  fb_header_init_on metadataInv_guestInv

example : type_of% @fb_header_init_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_header_init») := rfl

-- 4. fb_merkleize (idx 186)
theorem fb_merkleize_of :
    type_of% Wave8GuestInv.«fb_ceil_log2» →
    type_of% Wave8GuestInv.«fb_max» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_sha256_pair» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_merkleize» :=
  fb_merkleize_on metadataInv_guestInv

example : type_of% @fb_merkleize_of =
    (type_of% Wave8GuestInv.«fb_ceil_log2» →
     type_of% Wave8GuestInv.«fb_max» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_sha256_pair» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_merkleize») := rfl

-- 5. fb_htr_bytes_vector (idx 193)
theorem fb_htr_bytes_vector_of :
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_pack_bytes» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» :=
  fb_htr_bytes_vector_on metadataInv_guestInv

example : type_of% @fb_htr_bytes_vector_of =
    (type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_pack_bytes» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector») := rfl

-- 6. fb_htr_u64_at (idx 195)
theorem fb_htr_u64_at_of :
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» :=
  fb_htr_u64_at_on metadataInv_guestInv

example : type_of% @fb_htr_u64_at_of =
    (type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_htr_u64_at») := rfl

-- 7. fb_htr_bdep (idx 214)
theorem fb_htr_bdep_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_bdep» :=
  fb_htr_bdep_on metadataInv_guestInv

example : type_of% @fb_htr_bdep_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_htr_u64_at» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_bdep») := rfl

-- 8. fb_htr_bexit (idx 215)
theorem fb_htr_bexit_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_bexit» :=
  fb_htr_bexit_on metadataInv_guestInv

example : type_of% @fb_htr_bexit_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_bexit») := rfl

-- 9. fb_mix_in_length (idx 187)
theorem fb_mix_in_length_of :
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_st_le64» →
    type_of% Wave8GuestInv.«fb_sha256_pair» →
    type_of% Wave8GuestInv.«fb_mix_in_length» :=
  fb_mix_in_length_on metadataInv_guestInv

example : type_of% @fb_mix_in_length_of =
    (type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_st_le64» →
     type_of% Wave8GuestInv.«fb_sha256_pair» →
     type_of% Wave8GuestInv.«fb_mix_in_length») := rfl

-- 10. fb_htr_bytes_list (idx 194)
theorem fb_htr_bytes_list_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_pack_bytes» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_mix_in_length» →
    type_of% Wave8GuestInv.«fb_htr_bytes_list» :=
  fb_htr_bytes_list_on metadataInv_guestInv

example : type_of% @fb_htr_bytes_list_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_pack_bytes» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_mix_in_length» →
     type_of% Wave8GuestInv.«fb_htr_bytes_list») := rfl

-- 11. fb_htr_cons (idx 213)
theorem fb_htr_cons_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_cons» :=
  fb_htr_cons_on metadataInv_guestInv

example : type_of% @fb_htr_cons_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_cons») := rfl

-- 12. fb_htr_deposit (idx 211)
theorem fb_htr_deposit_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_deposit» :=
  fb_htr_deposit_on metadataInv_guestInv

example : type_of% @fb_htr_deposit_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_htr_u64_at» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_deposit») := rfl

-- 13. fb_merkleize_progressive (idx 188)
theorem fb_merkleize_progressive_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_sha256_pair» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_merkleize_progressive» :=
  fb_merkleize_progressive_on metadataInv_guestInv ordinaryMem_guestInv

example : type_of% @fb_merkleize_progressive_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_sha256_pair» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_merkleize_progressive») := rfl

-- 14. fb_htr_plist_chunks (idx 189)
theorem fb_htr_plist_chunks_of :
    type_of% Wave8GuestInv.«fb_merkleize_progressive» →
    type_of% Wave8GuestInv.«fb_mix_in_length» →
    type_of% Wave8GuestInv.«fb_htr_plist_chunks» :=
  fb_htr_plist_chunks_on metadataInv_guestInv

example : type_of% @fb_htr_plist_chunks_of =
    (type_of% Wave8GuestInv.«fb_merkleize_progressive» →
     type_of% Wave8GuestInv.«fb_mix_in_length» →
     type_of% Wave8GuestInv.«fb_htr_plist_chunks») := rfl

-- 15. fb_htr_pbytes (idx 190)
theorem fb_htr_pbytes_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_pack_bytes» →
    type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_pbytes» :=
  fb_htr_pbytes_on metadataInv_guestInv

example : type_of% @fb_htr_pbytes_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_pack_bytes» →
     type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_pbytes») := rfl

-- 16. fb_htr_pcontainer (idx 191)
theorem fb_htr_pcontainer_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_merkleize_progressive» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_sha256_pair» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_pcontainer» :=
  fb_htr_pcontainer_on metadataInv_guestInv

example : type_of% @fb_htr_pcontainer_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_merkleize_progressive» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_sha256_pair» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_pcontainer») := rfl

-- 17. fb_htr_withdrawal (idx 208)
theorem fb_htr_withdrawal_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_withdrawal» :=
  fb_htr_withdrawal_on metadataInv_guestInv

example : type_of% @fb_htr_withdrawal_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_u64_at» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_withdrawal») := rfl

-- 18. fb_htr_payload (idx 210)
theorem fb_htr_payload_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» →
    type_of% Wave8GuestInv.«fb_htr_bytes_list» →
    type_of% Wave8GuestInv.«fb_htr_pbytes» →
    type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_withdrawal» →
    type_of% Wave8GuestInv.«fb_htr_pcontainer» →
    type_of% Wave8GuestInv.«fb_htr_payload» :=
  fb_htr_payload_on metadataInv_guestInv

example : type_of% @fb_htr_payload_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_htr_u64_at» →
     type_of% Wave8GuestInv.«fb_htr_bytes_list» →
     type_of% Wave8GuestInv.«fb_htr_pbytes» →
     type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_withdrawal» →
     type_of% Wave8GuestInv.«fb_htr_pcontainer» →
     type_of% Wave8GuestInv.«fb_htr_payload») := rfl

-- 19. fb_htr_wdreq (idx 212)
theorem fb_htr_wdreq_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
    type_of% Wave8GuestInv.«fb_htr_u64_at» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_wdreq» :=
  fb_htr_wdreq_on metadataInv_guestInv

example : type_of% @fb_htr_wdreq_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_bytes_vector» →
     type_of% Wave8GuestInv.«fb_htr_u64_at» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_wdreq») := rfl

-- 20. fb_htr_request_list (idx 216)
theorem fb_htr_request_list_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_deposit» →
    type_of% Wave8GuestInv.«fb_htr_wdreq» →
    type_of% Wave8GuestInv.«fb_htr_cons» →
    type_of% Wave8GuestInv.«fb_htr_bdep» →
    type_of% Wave8GuestInv.«fb_htr_bexit» →
    type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_request_list» :=
  fb_htr_request_list_on metadataInv_guestInv

example : type_of% @fb_htr_request_list_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_deposit» →
     type_of% Wave8GuestInv.«fb_htr_wdreq» →
     type_of% Wave8GuestInv.«fb_htr_cons» →
     type_of% Wave8GuestInv.«fb_htr_bdep» →
     type_of% Wave8GuestInv.«fb_htr_bexit» →
     type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_request_list») := rfl

-- 21. fb_htr_requests (idx 217)
theorem fb_htr_requests_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_request_list» →
    type_of% Wave8GuestInv.«fb_htr_pcontainer» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_requests» :=
  fb_htr_requests_on metadataInv_guestInv

example : type_of% @fb_htr_requests_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_request_list» →
     type_of% Wave8GuestInv.«fb_htr_pcontainer» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_requests») := rfl

-- 22. fb_htr_new_payload_request (idx 218)
theorem fb_htr_new_payload_request_of :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htr_payload» →
    type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_htr_requests» →
    type_of% Wave8GuestInv.«fb_merkleize» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_htr_new_payload_request» :=
  fb_htr_new_payload_request_on metadataInv_guestInv

example : type_of% @fb_htr_new_payload_request_of =
    (type_of% Wave8GuestInv.«fb_heap_mark» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htr_payload» →
     type_of% Wave8GuestInv.«fb_htr_plist_chunks» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_htr_requests» →
     type_of% Wave8GuestInv.«fb_merkleize» →
     type_of% Wave8GuestInv.«fb_heap_release» →
     type_of% Wave8GuestInv.«fb_htr_new_payload_request») := rfl

-- 23. fb_mem_init (idx 6)
theorem fb_mem_init_of :
    type_of% Wave8GuestInv.«fb_mem_init» :=
  fb_mem_init_on metadataInv_guestInv

example : type_of% @fb_mem_init_of =
    (type_of% Wave8GuestInv.«fb_mem_init») := rfl

-- 24. fb_mpt_init (idx 247)
theorem fb_mpt_init_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_mpt_init» :=
  fb_mpt_init_on metadataInv_guestInv

example : type_of% @fb_mpt_init_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_keccak256» →
     type_of% Wave8GuestInv.«fb_mpt_init») := rfl


end InitECandidate.Solver.Wave8GuestInv.S14
