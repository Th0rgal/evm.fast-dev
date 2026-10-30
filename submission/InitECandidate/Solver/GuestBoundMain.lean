import InitECandidate.Solver.PanRunBoundedExt

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestBoundMain

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound

theorem funBounded_attempt_l1 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l1") (K + 1 + 0 + 0) :=
  funBounded_of_guestAst 880 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l1 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq (ProgBounded.handledCall hrun _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l2 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l2") (K + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 881 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l2 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l1 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l3 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l3") (K + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 882 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l3 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l2 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l4 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l4") (K + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 883 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l4 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l3 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l5 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l5")
      (K + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 884 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l5 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l4 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l6 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l6")
      (K + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 885 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l6 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l5 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_attempt_l7 (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "attempt_l7")
      (K + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0 + 1 + 0 + 0) :=
  funBounded_of_guestAst 886 (by rw [guestAst_len]; decide) Guest.Software.guestFn_attempt_l7 _ rfl
    (ProgBounded.dec _ _ _
      (ProgBounded.seq
        (ProgBounded.handledCall (funBounded_attempt_l6 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl)))

theorem funBounded_main
    (K_mem_init : Nat) (h_mem_init : FunBounded (ofString "mem_init") K_mem_init)
    (K_sha256_init : Nat) (h_sha256_init : FunBounded (ofString "sha256_init") K_sha256_init)
    (K_keccak_init : Nat) (h_keccak_init : FunBounded (ofString "keccak_init") K_keccak_init)
    (K_ssz_init : Nat) (h_ssz_init : FunBounded (ofString "ssz_init") K_ssz_init)
    (K_mpt_init : Nat) (h_mpt_init : FunBounded (ofString "mpt_init") K_mpt_init)
    (K_u256_ws_init : Nat) (h_u256_ws_init : FunBounded (ofString "u256_ws_init") K_u256_ws_init)
    (K_secp256k1_init : Nat) (h_secp256k1_init : FunBounded (ofString "secp256k1_init") K_secp256k1_init)
    (K_bn254_init : Nat) (h_bn254_init : FunBounded (ofString "bn254_init") K_bn254_init)
    (K_bls_precompiles_init : Nat)
    (h_bls_precompiles_init : FunBounded (ofString "bls_precompiles_init") K_bls_precompiles_init)
    (K_ripemd160_init : Nat) (h_ripemd160_init : FunBounded (ofString "ripemd160_init") K_ripemd160_init)
    (K_blake2_init : Nat) (h_blake2_init : FunBounded (ofString "blake2_init") K_blake2_init)
    (K_header_init : Nat) (h_header_init : FunBounded (ofString "header_init") K_header_init)
    (K_evm_init : Nat) (h_evm_init : FunBounded (ofString "evm_init") K_evm_init)
    (K_fork_init : Nat) (h_fork_init : FunBounded (ofString "fork_init") K_fork_init)
    (K_alloc : Nat) (h_alloc : FunBounded (ofString "alloc") K_alloc)
    (K_memzero : Nat) (h_memzero : FunBounded (ofString "memzero") K_memzero)
    (K_decode_host_input : Nat)
    (h_decode_host_input : FunBounded (ofString "decode_host_input") K_decode_host_input)
    (K_serialize_result : Nat)
    (h_serialize_result : FunBounded (ofString "serialize_result") K_serialize_result)
    (K_output_write : Nat) (h_output_write : FunBounded (ofString "output_write") K_output_write)
    (K_htr_new_payload_request : Nat)
    (h_htr_new_payload_request : FunBounded (ofString "htr_new_payload_request") K_htr_new_payload_request)
    (K_verify_stateless_new_payload : Nat)
    (h_verify_stateless_new_payload :
      FunBounded (ofString "verify_stateless_new_payload") K_verify_stateless_new_payload) :
    FunBounded (ofString "main")
      (K_mem_init + K_sha256_init + K_keccak_init + K_ssz_init + K_mpt_init + K_u256_ws_init +
        K_secp256k1_init + K_bn254_init + K_bls_precompiles_init + K_ripemd160_init + K_blake2_init +
        K_header_init + K_evm_init + K_fork_init + 3 * K_alloc + K_memzero + K_decode_host_input +
        2 * K_serialize_result + 2 * K_output_write + K_htr_new_payload_request +
        K_verify_stateless_new_payload + 25) :=
  funBounded_of_guestAst 889 (by rw [guestAst_len]; decide) Guest.Software.guestFn_main _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call h_mem_init _ _)
      (ProgBounded.seq (ProgBounded.call h_sha256_init _ _)
      (ProgBounded.seq (ProgBounded.call h_keccak_init _ _)
      (ProgBounded.seq (ProgBounded.call h_ssz_init _ _)
      (ProgBounded.seq (ProgBounded.call h_mpt_init _ _)
      (ProgBounded.seq (ProgBounded.call h_u256_ws_init _ _)
      (ProgBounded.seq (ProgBounded.call h_secp256k1_init _ _)
      (ProgBounded.seq (ProgBounded.call h_bn254_init _ _)
      (ProgBounded.seq (ProgBounded.call h_bls_precompiles_init _ _)
      (ProgBounded.seq (ProgBounded.call h_ripemd160_init _ _)
      (ProgBounded.seq (ProgBounded.call h_blake2_init _ _)
      (ProgBounded.seq (ProgBounded.call h_header_init _ _)
      (ProgBounded.seq (ProgBounded.call h_evm_init _ _)
      (ProgBounded.seq (ProgBounded.call h_fork_init _ _)
      (ProgBounded.decCall h_alloc _ _ _
        (ProgBounded.decCall h_alloc _ _ _
          (ProgBounded.seq (ProgBounded.call h_memzero _ _)
            (ProgBounded.dec _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.handledCall h_decode_host_input _ _ _ _
                    (ProgBounded.decCall h_serialize_result _ _ _
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.seq (ProgBounded.call h_output_write _ _)
                          (ProgBounded.straight _ rfl)))))
                  (ProgBounded.decCall h_alloc _ _ _
                    (ProgBounded.seq (ProgBounded.call h_htr_new_payload_request _ _)
                      (ProgBounded.decCall h_verify_stateless_new_payload _ _ _
                        (ProgBounded.decCall h_serialize_result _ _ _
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.seq (ProgBounded.call h_output_write _ _)
                              (ProgBounded.straight _ rfl)))))))))))))))))))))))))))
      (by omega))

open InitECandidate.Solver.PanRunBoundedExt

theorem funBounded_u256_ws_init : FunBounded (ofString "u256_ws_init") 2 :=
  funBounded_of_guestAst 38 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_ws_init 2 rfl
    (ProgBounded.weaken
      (ProgBounded.seq
        (ProgBounded.iteMax _ (ProgBounded.alloc _ _) (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (by decide))

theorem funBounded_sha256_init : FunBounded (ofString "sha256_init") 4 :=
  funBounded_of_guestAst 91 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_sha256_init 4 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.straight _ rfl)))
      (by decide))

theorem funBounded_secp256k1_init : FunBounded (ofString "secp256k1_init") 0 :=
  funBounded_of_guestAst 148 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_secp256k1_init 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_keccak_init : FunBounded (ofString "keccak_init") 6 :=
  funBounded_of_guestAst 100 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_keccak_init 6 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.straight _ rfl))))
      (by decide))

theorem funBounded_ssz_init : FunBounded (ofString "ssz_init") 6 :=
  funBounded_of_guestAst 185 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_init 6 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.seq (ProgBounded.alloc _ _)
              (ProgBounded.straight _ rfl)))))
      (by decide))

theorem funBounded_header_init : FunBounded (ofString "header_init") 11 :=
  funBounded_of_guestAst 238 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_header_init 11 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (progBounded_memzero_const _ _ _ (by decide))
            (ProgBounded.straight _ rfl))))
      (by decide))

theorem funBounded_bn254_init : FunBounded (ofString "bn254_init") 4 :=
  funBounded_of_guestAst 648 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bn254_init 4 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.straight _ rfl)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.straight _ rfl)
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.seq (ProgBounded.straight _ rfl)
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.seq (ProgBounded.straight _ rfl)
                              (ProgBounded.seq (ProgBounded.straight _ rfl)
                                (ProgBounded.seq (ProgBounded.straight _ rfl)
                                  (ProgBounded.seq (ProgBounded.alloc _ _)
                                    (ProgBounded.straight _ rfl))))))))))))))))
      (by decide))

theorem funBounded_ripemd160_init : FunBounded (ofString "ripemd160_init") 8 :=
  funBounded_of_guestAst 612 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ripemd160_init 8 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.seq (ProgBounded.alloc _ _)
              (ProgBounded.seq (ProgBounded.alloc _ _)
                (ProgBounded.straight _ rfl))))))
      (by decide))

theorem funBounded_blake2_init : FunBounded (ofString "blake2_init") 6 :=
  funBounded_of_guestAst 621 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_blake2_init 6 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.seq (ProgBounded.alloc _ _)
              (ProgBounded.straight _ rfl)))))
      (by decide))

theorem funBounded_bls_consts_init : FunBounded (ofString "bls_consts_init") 2 :=
  funBounded_of_guestAst 696 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bls_consts_init 2 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.straight _ rfl)))
      (by decide))

theorem funBounded_bls_lib_init : FunBounded (ofString "bls_lib_init") 3 :=
  funBounded_of_guestAst 801 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bls_lib_init 3 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call funBounded_bls_consts_init _ _)
        (ProgBounded.straight _ rfl))
      (by decide))

theorem funBounded_bls_precompiles_init : FunBounded (ofString "bls_precompiles_init") 6 :=
  funBounded_of_guestAst 811 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_bls_precompiles_init 6 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.call funBounded_bls_lib_init _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.straight _ rfl))))
      (by decide))

theorem funBounded_serialize_result : FunBounded (ofString "serialize_result") 15 :=
  funBounded_of_guestAst 219 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_serialize_result 15 rfl
    (ProgBounded.weaken
      (ProgBounded.seq (progBounded_memcpy_const _ _ _ _ (by decide))
        (ProgBounded.seq (ProgBounded.straight _ rfl)
          (ProgBounded.seq (ProgBounded.call funBounded_st_le64 _ _)
            (ProgBounded.straight _ rfl))))
      (by decide))

theorem funBounded_fork_init : FunBounded (ofString "fork_init") 202 := by
  refine funBounded_of_guestAst 861 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_fork_init 202 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_fork_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.alloc _ _)
      (ProgBounded.seq (progBounded_memzero_const _ _ _ (by decide))
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (progBounded_memzero_mul_const _ _ _ _ (by decide))
            (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 17 1 0
              (by decide) (by decide) (by decide)
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.alloc _ _)
                  (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                    (ProgBounded.seq (ProgBounded.alloc _ _)
                      (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                        (ProgBounded.seq (ProgBounded.alloc _ _)
                          (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                            (ProgBounded.seq (ProgBounded.alloc _ _)
                              (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                                (ProgBounded.seq (ProgBounded.alloc _ _)
                                  (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                                    (ProgBounded.seq (ProgBounded.alloc _ _)
                                      (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                                        (ProgBounded.seq (ProgBounded.alloc _ _)
                                          (ProgBounded.seq (ProgBounded.call funBounded_addr_from_words _ _)
                                            (ProgBounded.seq (ProgBounded.alloc _ _)
                                              (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
                                                (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
                                                  (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
                                                    (ProgBounded.seq (ProgBounded.call funBounded_st_be64 _ _)
                                                      (ProgBounded.straight _ rfl))))))))))))))))))))))))))
    (by decide)

theorem funBounded_verify_stateless_new_payload
    (K : Nat) (hrun : FunBounded (ofString "run_attempt") K) :
    FunBounded (ofString "verify_stateless_new_payload") (K + 8) :=
  funBounded_of_guestAst 887 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_verify_stateless_new_payload _ rfl
    (ProgBounded.weaken
      (ProgBounded.dec _ _ _
        (ProgBounded.dec _ _ _
          (ProgBounded.seq
            (ProgBounded.handledCall (funBounded_attempt_l7 K hrun) _ _ _ _ (ProgBounded.straight _ rfl))
            (ProgBounded.straight _ rfl))))
      (by omega))

theorem funBounded_mpt_init_of_keccak256
    (K_keccak256 : Nat) (h_keccak256 : FunBounded (ofString "keccak256") K_keccak256) :
    FunBounded (ofString "mpt_init") (2 * K_keccak256 + 12) :=
  funBounded_of_guestAst 247 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_init _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.seq (ProgBounded.alloc _ _)
              (ProgBounded.seq (ProgBounded.alloc _ _)
                (ProgBounded.seq (ProgBounded.straight _ rfl)
                  (ProgBounded.seq (ProgBounded.call h_keccak256 _ _)
                    (ProgBounded.seq (ProgBounded.call h_keccak256 _ _)
                      (ProgBounded.straight _ rfl)))))))))
      (by omega))

private theorem progBounded_seq_straight (p q : ProgHOL 64) {k : Nat}
    (hp : extStraightLine p = true) (hq : ProgBounded q k) :
    ProgBounded (.seq p q) k :=
  ProgBounded.weaken (ProgBounded.seq (ProgBounded.straight p hp) hq) (Nat.zero_add k).le

theorem funBounded_decode_host_input
    (K_precheck K_input_blob K_decode_stateless : Nat)
    (h_precheck : FunBounded (ofString "precheck_host_ssz_header") K_precheck)
    (h_input_blob : FunBounded (ofString "input_blob") K_input_blob)
    (h_decode_stateless : FunBounded (ofString "decode_stateless_input") K_decode_stateless) :
    FunBounded (ofString "decode_host_input") (K_precheck + K_input_blob + K_decode_stateless + 3) :=
  funBounded_of_guestAst 200 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_host_input _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call h_precheck _ _)
        (ProgBounded.decCall h_input_blob _ _ _
          (ProgBounded.tail h_decode_stateless _)))
      (by omega))

theorem funBounded_htr_new_payload_request
    (K_htr_payload K_htr_plist_chunks K_htr_requests K_merkleize : Nat)
    (h_htr_payload : FunBounded (ofString "htr_payload") K_htr_payload)
    (h_htr_plist_chunks : FunBounded (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_htr_requests : FunBounded (ofString "htr_requests") K_htr_requests)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize) :
    FunBounded (ofString "htr_new_payload_request")
      (K_htr_payload + K_htr_plist_chunks + K_htr_requests + K_merkleize + 20) := by
  refine funBounded_of_guestAst 218 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htr_new_payload_request _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htr_new_payload_request,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.seq (ProgBounded.call h_htr_payload _ _)
          (ProgBounded.seq (ProgBounded.call h_htr_plist_chunks _ _)
              (ProgBounded.seq (progBounded_memcpy_const _ _ _ 32#64 (by decide))
              (ProgBounded.seq (ProgBounded.call h_htr_requests _ _)
                (ProgBounded.seq (ProgBounded.call h_merkleize _ _)
                  (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
                    (ProgBounded.straight _ rfl)))))))))
    ?_
  have h32 : (32#64).toNat = 32 := rfl
  rw [h32]
  omega

private theorem shMemStoreHOLExact_locals {F : Type}
    (state : PanSemStateExact 64 F) [DecidablePred state.shMemaddrs]
    (word address : BitVec 64) (nb : Nat) :
    (shMemStoreHOLExact state word address nb).2.locals = state.locals := by
  unfold shMemStoreHOLExact
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · split <;> rfl
    · rfl

private theorem evaluate_shMemStore_locals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize) (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.locals = state.locals := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · apply HolFiniteMapExact.ext
    change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).2.locals = state.locals.lookup
    exact shMemStoreHOLExact_locals state.toExact _ _ (nbOpHOL operator)
  · rfl

theorem funBounded_output_write :
    FunBounded (ofString "output_write") (2 ^ 64 - 1) := by
  refine funBounded_of_guestAst 30 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_output_write _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_output_write,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_clk : s0.clock = state.clock := rfl
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  let storeStmt : ProgHOL 64 :=
    .shMemStore .op8 (.op .add [.const 2688614400, .var .local (ofString "i")])
      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
  let incrStmt : ProgHOL 64 :=
    .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])
  let loopBody : ProgHOL 64 := .seq storeStmt incrStmt
  have hloop : RunBounded s0
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) loopBody)
      (2 ^ 64 - 1) := by
    cases hn : s0.locals.lookup (ofString "n") with
    | none =>
      unfold RunBounded
      rw [evaluateHOLFiniteState_while_total]
      have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
        rw [evalHOLFinite_eq_toExact]
        simp [evalHOLExact, hs0_i, hn]
      rw [hguard]
      simp
    | some v =>
      cases v with
      | rStruct _ =>
        unfold RunBounded
        rw [evaluateHOLFiniteState_while_total]
        have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hs0_i, hn]
        rw [hguard]
        simp
      | nStruct _ _ =>
        unfold RunBounded
        rw [evaluateHOLFiniteState_while_total]
        have hguard : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = none := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, hs0_i, hn]
        rw [hguard]
        simp
      | val wl =>
        cases wl with
        | word K =>
          unfold RunBounded
          have haux :
              ∀ m : Nat, ∀ (st : PanSemStateFiniteExact 64 F),
                st.code = originalRuntimeCode →
                ∀ w : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word w)) →
                st.locals.lookup (ofString "n") = some (.val (.word K)) →
                w.toNat ≤ K.toNat → K.toNat - w.toNat = m → m ≤ st.clock →
                let r := evaluateHOLFiniteState st
                  (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) loopBody)
                st.clock ≤ r.2.clock + m ∧ r.2.clock ≤ st.clock ∧ r.1 ≠ some .timeOut := by
            intro m
            induction m using Nat.strongRecOn with
            | ind m ih =>
              intro st hst_code w hw hK hw_le hm hst_clk
              have hcond := eval_variable_counted_condition st (ofString "i") (ofString "n")
                .lower (Or.inr rfl) K w (fun h => by cases h) hw_le hw hK
              dsimp only
              rw [evaluateHOLFiniteState_while_total, hcond]
              by_cases hlt : w.toNat < K.toNat
              · rw [if_pos hlt]
                simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
                have hclk_nz : st.clock ≠ 0 := by omega
                rw [if_neg hclk_nz, fixClockHOLFinite_evaluateState]
                let st1 := decClockHOLFinite st
                have hbody_bound := (ProgBounded.straight loopBody rfl) st1 hst_code (by omega)
                have hbody_nc := evaluate_noTopContinue loopBody rfl st1
                have hbody_meta := PanRunBounded.evaluateHOLFiniteState_metadata st1 loopBody
                have hstore_loc := evaluate_shMemStore_locals st1 .op8
                  (.op .add [.const 2688614400, .var .local (ofString "i")])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
                rcases hb : evaluateHOLFiniteState st1 loopBody with ⟨res, mid⟩
                rw [hb] at hbody_bound hbody_nc hbody_meta
                dsimp only at hbody_bound hbody_nc hbody_meta
                change st.clock - 1 ≤ mid.clock + 0 ∧ mid.clock ≤ st.clock - 1 ∧ res ≠ some .timeOut at hbody_bound
                cases res with
                | none =>
                  dsimp only
                  have hseq : evaluateHOLFiniteState st1 (.seq storeStmt incrStmt) = (none, mid) := hb
                  rw [evaluateHOLFiniteState_seq_line780] at hseq
                  rcases hs : evaluateHOLFiniteState st1 storeStmt with ⟨rs, smid⟩
                  rw [hs] at hseq hstore_loc
                  cases rs with
                  | some r => simp at hseq
                  | none =>
                    dsimp only at hseq hstore_loc
                    have hsmid_loc : smid.locals = st.locals := hstore_loc
                    have hsmid_i : smid.locals.lookup (ofString "i") = some (.val (.word w)) := by
                      rw [hsmid_loc]; exact hw
                    have hsmid_n : smid.locals.lookup (ofString "n") = some (.val (.word K)) := by
                      rw [hsmid_loc]; exact hK
                    have hassign : evaluateHOLFiniteState smid incrStmt =
                        (none, setVarHOLFinite (ofString "i") (.val (.word (w + 1))) smid) := by
                      simp [incrStmt, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
                        hsmid_i, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                        isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                    rw [hassign] at hseq
                    obtain ⟨_, rfl⟩ := Prod.mk.inj hseq
                    have hmid_i : (setVarHOLFinite (ofString "i") (.val (.word (w + 1))) smid).locals.lookup (ofString "i") =
                        some (.val (.word (w + 1))) := by
                      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    have hmid_n : (setVarHOLFinite (ofString "i") (.val (.word (w + 1))) smid).locals.lookup (ofString "n") =
                        some (.val (.word K)) := by
                      have hne : ofString "i" ≠ ofString "n" := by decide
                      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hsmid_n]
                    have hnat : (w + 1).toNat = w.toNat + 1 := by
                      rw [BitVec.toNat_add_of_lt (by have := K.isLt; simp; omega)]
                      rfl
                    obtain ⟨t1, t2, t3⟩ := ih (K.toNat - (w + 1).toNat) (by rw [hnat]; omega)
                      _ (hbody_meta.1.trans hst_code) (w + 1) hmid_i hmid_n (by rw [hnat]; omega) rfl (by omega)
                    exact ⟨by omega, by omega, t3⟩
                | some r =>
                  cases r with
                  | «continue» => exact absurd rfl hbody_nc
                  | timeOut => exact absurd rfl hbody_bound.2.2
                  | «break» | error | returned _ | exception _ _ | finalFfi _ =>
                    exact ⟨by simp; omega, by simp; omega, by simp⟩
              · rw [if_neg hlt]
                simp
          have h := haux K.toNat s0 hs0_code 0 hs0_i hn (by simp) (by simp)
            (by rw [hs0_clk]; have := K.isLt; omega)
          exact ⟨by have := h.1; rw [hs0_clk] at this; have := K.isLt; omega,
            by have := h.2.1; rw [hs0_clk] at this; exact this, h.2.2⟩
  exact (RunBounded.seq hloop (a := 2 ^ 64 - 1) (b := 0)
    (by rw [hs0_clk]; omega)
    (fun next _ nextCode nextBudget =>
      (ProgBounded.straight _ rfl) next (nextCode.trans hs0_code) nextBudget)).weaken (by omega)

theorem funBounded_ssz_fail : FunBounded (ofString "ssz_fail") 0 :=
  funBounded_of_guestAst 196 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_fail 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_host_input_byte : FunBounded (ofString "host_input_byte") 0 :=
  funBounded_of_guestAst 197 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_host_input_byte 0 rfl (ProgBounded.straight _ rfl)

theorem funBounded_host_input_le32 : FunBounded (ofString "host_input_le32") 4 :=
  funBounded_of_guestAst 198 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_host_input_le32 4 rfl
    (ProgBounded.weaken
      (ProgBounded.decCall funBounded_host_input_byte _ _ _
        (ProgBounded.decCall funBounded_host_input_byte _ _ _
          (ProgBounded.decCall funBounded_host_input_byte _ _ _
            (ProgBounded.decCall funBounded_host_input_byte _ _ _
              (ProgBounded.straight _ rfl)))))
      (by decide))

private theorem lookup_keccak256 :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
  lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

private theorem evalListHOLFinite_three_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1 v3, vs = [v1, .val (.word K), v3] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs
    rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
    · rw [h3] at hargs; cases hargs
    · rw [h3] at hargs; cases hargs; exact ⟨v1, v3, rfl⟩

private theorem three_arg_lookup_mid (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 p3 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp23 : p2 ≠ p3)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    {v1 v3 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K), v3] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p2 = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, .val (.word K), v3] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | val wl1 =>
    cases wl1 with
    | word w1 =>
      cases v3 with
      | rStruct _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | nStruct _ _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | val wl3 =>
        cases wl3 with
        | word w3 =>
          rw [pan_three_word_lookup code fn p1 p2 p3 body w1 K w3 hp12 hp13 hp23 hlookup_fn] at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hp23, Ne.symm hp23]

private theorem runBounded_keccak256_small_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hlt : K.toNat < 136)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 240 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_keccak256) (K.toNat / 8 + 240) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_keccak256,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.dec
  intro stpVal _
  let s1 := setVarHOLFinite (ofString "stp") stpVal state
  have hs1_clk : s1.clock = state.clock := rfl
  have hs1_code : s1.code = originalRuntimeCode := hcode
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "stp" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hmz200 : ProgBounded
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64]) 33 :=
    ProgBounded.weaken (progBounded_memzero_const none (.var .local (ofString "stp")) 200#64 (by decide)) (by decide)
  have hmz200_run := hmz200 s1 hs1_code (by rw [hs1_clk]; omega)
  have hmz200_fn := evaluate_avoidsLocal_flowing (ofString "n")
    (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64]) rfl s1
  have hmz200_meta := PanRunBounded.evaluateHOLFiniteState_metadata s1
    (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64])
  change RunBounded s1 _ (K.toNat / 8 + 240)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hrun1 : evaluateHOLFiniteState s1
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200#64]) with ⟨r1, s2⟩
  rw [hrun1] at hmz200_run hmz200_fn hmz200_meta
  dsimp only at hmz200_run hmz200_fn hmz200_meta ⊢
  cases r1 with
  | some r =>
    dsimp only
    exact ⟨by omega, hmz200_run.2.1, hmz200_run.2.2⟩
  | none =>
    dsimp only
    have hs2_code : s2.code = originalRuntimeCode := hmz200_meta.1.trans hs1_code
    have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) :=
      (hmz200_fn (Or.inl rfl)).trans hs1_n
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
    let s3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s2
    have hs3_clk : s3.clock = s2.clock := rfl
    have hs3_code : s3.code = originalRuntimeCode := hs2_code
    have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word K)) := by
      have hne : ofString "i" ≠ ofString "n" := by decide
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_n]
    change s1.clock ≤ (evaluateHOLFiniteState s3 _).2.clock + (K.toNat / 8 + 240) ∧
      (evaluateHOLFiniteState s3 _).2.clock ≤ s1.clock ∧
      (evaluateHOLFiniteState s3 _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    have hwhile_exit :
        evaluateHOLFiniteState s3
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136#64]))
            (.seq
              (.call (some (none, none)) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136#64])))) =
        (none, s3) := by
      rw [evaluateHOLFiniteState_while_total]
      have hcond : evalHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136#64])) =
          some (.val (.word 0)) := by
        rw [evalHOLFinite_eq_toExact]
        have hlt_bv : K < 136#64 := by
          rw [BitVec.lt_def]
          exact hlt
        simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp,
          valueIsWord, valueWord, Compiler.Encoders.Asm.wordCmpHOL, hlt_bv]
      rw [hcond]
      simp
    rw [hwhile_exit]
    dsimp only
    have hrem_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word K)) := by
      simp [evalHOLExact, evalListHOLExact, hs3_n, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [hrem_eval]
    simp only [shapeOfHOLExact, shapeEqHOL, if_true]
    let s4 := setVarHOLFinite (ofString "rem") (.val (.word K)) s3
    have hs4_clk : s4.clock = s3.clock := rfl
    have hs4_code : s4.code = originalRuntimeCode := hs3_code
    have hs4_rem : s4.locals.lookup (ofString "rem") = some (.val (.word K)) := by
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change s1.clock ≤ (evaluateHOLFiniteState s4 _).2.clock + (K.toNat / 8 + 240) ∧
      (evaluateHOLFiniteState s4 _).2.clock ≤ s1.clock ∧
      (evaluateHOLFiniteState s4 _).1 ≠ some .timeOut
    have hmz136 : ProgBounded
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136#64]) 25 :=
      ProgBounded.weaken (progBounded_memzero_const none (.var .global (ofString "keccak_pad")) 136#64 (by decide)) (by decide)
    have hmz136_run := hmz136 s4 hs4_code (by omega)
    have hmz136_frem := evaluate_avoidsLocal_flowing (ofString "rem")
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136#64]) rfl s4
    have hmz136_meta := PanRunBounded.evaluateHOLFiniteState_metadata s4
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136#64])
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hrun2 : evaluateHOLFiniteState s4
        (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136#64]) with ⟨r2, s5⟩
    rw [hrun2] at hmz136_run hmz136_frem hmz136_meta
    dsimp only at hmz136_run hmz136_frem hmz136_meta ⊢
    cases r2 with
    | some r =>
      dsimp only
      exact ⟨by omega, by omega, hmz136_run.2.2⟩
    | none =>
      dsimp only
      have hs5_code : s5.code = originalRuntimeCode := hmz136_meta.1.trans hs4_code
      have hs5_rem : s5.locals.lookup (ofString "rem") = some (.val (.word K)) :=
        (hmz136_frem (Or.inl rfl)).trans hs4_rem
      rw [evaluateHOLFiniteState_seq_line780]
      have heq_mc :
          evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "memcpy")
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .var .local (ofString "rem")]) =
          evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "memcpy")
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .const K]) := by
        have hargs_eq :
            evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .var .local (ofString "rem")] =
            evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.var .global (ofString "keccak_pad"),
               .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
               .const K] := by
          simp only [evalListHOLFinite_eq_toExact, evalListHOLExact]
          have hrem_k : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
              (.var .local (ofString "rem")) =
              @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a)) (.const K) := by
            simp [evalHOLExact, hs5_rem]
          rw [hrem_k]
        rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, hargs_eq]
      have hmc_rem : RunBounded s5
          (.call (some (none, none)) (ofString "memcpy")
            [.var .global (ofString "keccak_pad"),
             .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
             .var .local (ofString "rem")])
          (K.toNat / 8 + 8) := by
        unfold RunBounded
        rw [heq_mc]
        exact progBounded_memcpy_const none
          (.var .global (ofString "keccak_pad"))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
          K (by omega) s5 hs5_code (by omega)
      have hmc_meta := PanRunBounded.evaluateHOLFiniteState_metadata s5
        (.call (some (none, none)) (ofString "memcpy")
          [.var .global (ofString "keccak_pad"),
           .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
           .var .local (ofString "rem")])
      unfold RunBounded at hmc_rem
      rcases hrun3 : evaluateHOLFiniteState s5
          (.call (some (none, none)) (ofString "memcpy")
            [.var .global (ofString "keccak_pad"),
             .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
             .var .local (ofString "rem")]) with ⟨r3, s6⟩
      rw [hrun3] at hmc_rem hmc_meta
      dsimp only at hmc_rem hmc_meta ⊢
      cases r3 with
      | some r =>
        dsimp only
        exact ⟨by omega, by omega, hmc_rem.2.2⟩
      | none =>
        dsimp only
        have hs6_code : s6.code = originalRuntimeCode := hmc_meta.1.trans hs5_code
        have htail : ProgBounded
            (.seq
              (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1#64))
              (.seq
                (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135#64])
                  (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135#64]), .const 128#64]))
                (.seq
                  (.call (some (none, none)) (ofString "keccak_absorb_block")
                    [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
                  (.seq
                    (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7#64]) (.const 0#64))
                      (.seq
                        (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
                        (.seq
                          (.store (.op .add [.var .local (ofString "out"), .const 8#64])
                            (.load .one (.op .add [.var .local (ofString "stp"), .const 8#64])))
                          (.seq
                            (.store (.op .add [.var .local (ofString "out"), .const 16#64])
                              (.load .one (.op .add [.var .local (ofString "stp"), .const 16#64])))
                            (.store (.op .add [.var .local (ofString "out"), .const 24#64])
                              (.load .one (.op .add [.var .local (ofString "stp"), .const 24#64]))))))
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32#64]))
                    (.return (.const 0#64))))))
            174 := by
          refine progBounded_seq_straight _ _ rfl (progBounded_seq_straight _ _ rfl ?_)
          refine ProgBounded.weaken
            (ProgBounded.seq (ProgBounded.call funBounded_keccak_absorb_block _ _)
              (ProgBounded.seq
                (ProgBounded.iteMax _ (ProgBounded.straight _ rfl)
                  (progBounded_memcpy_const _ _ _ 32#64 (by decide)))
                (ProgBounded.straight _ rfl)))
            ?_
          have h32 : (32#64).toNat = 32 := rfl
          rw [h32]
          omega
        have ht := htail s6 hs6_code (by omega)
        exact ⟨by omega, by omega, ht.2.2⟩

theorem progBounded_keccak256_small_const (destination : Option (VarKind × MlS)) (p out : ExpHOL 64)
    (K : BitVec 64) (hlt : K.toNat < 136) :
    ProgBounded (.call (some (destination, none)) (ofString "keccak256") [p, .const K, out])
      (K.toNat / 8 + 241) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [p, .const K, out] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, rfl⟩ := evalListHOLFinite_three_word2 state p (.const K) out K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_mid originalRuntimeCode.lookup
        (ofString "keccak256") (ofString "p") (ofString "n") (ofString "out")
        (sourceFnBody Guest.Software.guestFn_keccak256)
        (by decide) (by decide) (by decide) lookup_keccak256 hfound
      exact runBounded_keccak256_small_body (callEntryStateHOLFinite state locals) K hlt hcode hn
        (by change K.toNat / 8 + 240 ≤ state.clock - 1; omega))

theorem funBounded_mpt_init : FunBounded (ofString "mpt_init") 492 := by
  refine funBounded_of_guestAst 247 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mpt_init 492 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_mpt_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.alloc _ _)
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (ProgBounded.alloc _ _)
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.seq (ProgBounded.alloc _ _)
              (progBounded_seq_straight _ _ rfl
                (ProgBounded.seq (progBounded_keccak256_small_const _ _ _ 1#64 (by decide))
                  (ProgBounded.seq (progBounded_keccak256_small_const _ _ _ 0#64 (by decide))
                    (ProgBounded.straight _ rfl)))))))))
    (by decide)

theorem funBounded_evm_init : FunBounded (ofString "evm_init") 302 := by
  refine funBounded_of_guestAst 566 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_evm_init 302 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_evm_init,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.decCall funBounded_heap_mark _ _ _
      (ProgBounded.decCall (tailCost := 299) funBounded_alloc _ _ _ ?_))
    (by decide)
  iterate 33 refine progBounded_seq_straight _ _ rfl ?_
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.call funBounded_heap_release _ _)
      (ProgBounded.seq (ProgBounded.alloc _ _)
        (ProgBounded.seq (progBounded_keccak256_small_const _ _ _ 33#64 (by decide))
          (ProgBounded.seq (ProgBounded.alloc _ _)
            (ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 20 1 0
              (by decide) (by decide) (by decide)
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
              (progBounded_seq_straight _ _ rfl
                (ProgBounded.seq (ProgBounded.alloc _ _)
                  (ProgBounded.seq (progBounded_memzero_const _ _ 24#64 (by decide))
                    (ProgBounded.seq (ProgBounded.alloc _ _)
                      (ProgBounded.seq (progBounded_memzero_const _ _ 8#64 (by decide))
                        (ProgBounded.seq (ProgBounded.alloc _ _)
                          (ProgBounded.seq (ProgBounded.alloc _ _)
                            (ProgBounded.straight _ rfl)))))))))))))
    (by decide)

private theorem evaluate_shMemLoad_local_none {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize) (name : MlS) (address : ExpHOL 64)
    {post : PanSemStateFiniteExact 64 F}
    (hrun : evaluateHOLFiniteState state (.shMemLoad operator .local name address) = (none, post)) :
    ∃ val : BitVec 64,
      post.locals = state.locals.update (name, .val (.word val)) ∧
      post.code = state.code ∧
      post.clock = state.clock := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at hrun
  split at hrun
  · rename_i addr haddr
    split at hrun
    · rename_i old hlookup
      unfold shMemLoadHOLFiniteExact at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl, rfl, rfl⟩
        · simp at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl, rfl, rfl⟩
        · simp at hrun
    · simp at hrun
  · simp at hrun

theorem funBounded_input_blob_verified : FunBounded (ofString "input_blob") 134217728 := by
  refine funBounded_of_guestAst 29 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_input_blob 134217728 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_input_blob,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s1 := setVarHOLFinite (ofString "len") (.val (.word 0#64)) state
  have hs1_clk : s1.clock = state.clock := rfl
  have hs1_code : s1.code = originalRuntimeCode := hcode
  change RunBounded s1 _ 134217728
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  have hload0_bound := (ProgBounded.straight
    (.shMemLoad .opW .local (ofString "len") (.const 1073741832#64)) rfl) s1 hs1_code (by omega)
  rcases hload0 : evaluateHOLFiniteState s1
      (.shMemLoad .opW .local (ofString "len") (.const 1073741832#64)) with ⟨r0, s2⟩
  rw [hload0] at hload0_bound
  dsimp only at hload0_bound ⊢
  cases r0 with
  | some r =>
    dsimp only
    exact ⟨by omega, hload0_bound.2.1, hload0_bound.2.2⟩
  | none =>
    dsimp only
    obtain ⟨lenVal, hs2_loc, hs2_code_eq, hs2_clk⟩ := evaluate_shMemLoad_local_none s1 .opW (ofString "len")
      (.const 1073741832#64) hload0
    have hs2_code : s2.code = originalRuntimeCode := hs2_code_eq.trans hs1_code
    have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenVal)) := by
      rw [hs2_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780]
    have hguard_eval :
        @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .lower (.const 1073741808#64) (.var .local (ofString "len"))) =
        some (.val (.word (if 1073741808 < lenVal.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hs2_len, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hgt : 1073741808 < lenVal.toNat
      · have hbv : (1073741808#64 : BitVec 64) < lenVal := by
          rw [BitVec.lt_def]
          exact hgt
        simp [hgt, hbv]
      · have hbv : ¬ ((1073741808#64 : BitVec 64) < lenVal) := by
          rw [BitVec.lt_def]
          exact hgt
        simp [hgt, hbv]
    rw [evaluateHOLFiniteState_ite, hguard_eval]
    by_cases hgt : 1073741808 < lenVal.toNat
    · rw [if_pos hgt]
      simp only [show ¬ ((1 : BitVec 64) = 0) by decide, if_false]
      have htrap_bound := (ProgBounded.call funBounded_trap_with none [.const 8#64]) s2 hs2_code (by omega)
      have htrap_nonone := evaluate_call_trap_with_no_none s2 8#64 hs2_code
      rcases htrap : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 8#64]) with ⟨rt, st⟩
      rw [htrap] at htrap_bound htrap_nonone
      cases rt with
      | none => exact absurd rfl htrap_nonone
      | some r =>
        dsimp only at htrap_bound ⊢
        exact ⟨by omega, by omega, htrap_bound.2.2⟩
    · rw [if_neg hgt]
      simp only [if_true, evaluateHOLFiniteState_skip]
      have hlen_le : lenVal.toNat ≤ 1073741808 := by omega
      have hargs_alloc : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.op .add [.var .local (ofString "len"), .const 8#64]] =
          some [.val (.word (lenVal + 8#64))] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hs2_len, wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨allocParams, allocBody, allocRs, halloc_lookup, halloc_prog⟩ := funBounded_alloc
      have hdc := RunBounded.decCall (state := s2) (name := ofString "p") (shape := .one)
        (function := ofString "alloc")
        (arguments := [.op .add [.var .local (ofString "len"), .const 8#64]])
        (values := [.val (.word (lenVal + 8#64))])
        (bodyCost := 1) (tailCost := 134217726)
        hargs_alloc (by omega)
        (fun body locals returnShape hfound => by
          rw [hs2_code] at hfound
          have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
            (ofString "alloc") allocParams allocBody body allocRs returnShape
            [.val (.word (lenVal + 8#64))] locals halloc_lookup hfound
          subst body
          have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s2 locals) allocBody
          refine ⟨halloc_prog (callEntryStateHOLFinite s2 locals) hs2_code (by change 1 ≤ s2.clock - 1; omega), ?_⟩
          intro pVal post hran hpost_clk
          rw [hran] at hmeta
          let s3 := setVarHOLFinite (ofString "p") pVal { post with locals := s2.locals }
          have hs3_clk : s3.clock = post.clock := rfl
          have hs3_code : s3.code = originalRuntimeCode := hmeta.1.trans hs2_code
          have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word lenVal)) := by
            have hne : ofString "p" ≠ ofString "len" := by decide
            simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs2_len]
          change RunBounded s3 _ 134217726
          apply RunBounded.decConst
          apply RunBounded.decConst
          let s4 := setVarHOLFinite (ofString "w") (.val (.word 0#64))
            (setVarHOLFinite (ofString "i") (.val (.word 0#64)) s3)
          have hs4_clk : s4.clock = post.clock := rfl
          have hs4_code : s4.code = originalRuntimeCode := hs3_code
          have hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
            have hne : ofString "w" ≠ ofString "i" := by decide
            simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
          have hs4_len : s4.locals.lookup (ofString "len") = some (.val (.word lenVal)) := by
            have hne1 : ofString "w" ≠ ofString "len" := by decide
            have hne2 : ofString "i" ≠ ofString "len" := by decide
            simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne1, hne2, hs3_len]
          let loadW : ProgHOL 64 :=
            .shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840#64, .var .local (ofString "i")])
          let storeW : ProgHOL 64 :=
            .store (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) (.var .local (ofString "w"))
          let incrI : ProgHOL 64 :=
            .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])
          let loopBody : ProgHOL 64 := .seq loadW (.seq storeW incrI)
          have hloop : RunBounded s4
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) loopBody)
              134217726 := by
            unfold RunBounded
            have haux :
                ∀ m : Nat, ∀ (st : PanSemStateFiniteExact 64 F),
                  st.code = originalRuntimeCode →
                  ∀ w : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word w)) →
                  st.locals.lookup (ofString "len") = some (.val (.word lenVal)) →
                  w.toNat ≤ lenVal.toNat + 7 →
                  (lenVal.toNat + 7 - w.toNat) / 8 = m →
                  m ≤ st.clock →
                  let r := evaluateHOLFiniteState st
                    (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) loopBody)
                  st.clock ≤ r.2.clock + m ∧ r.2.clock ≤ st.clock ∧ r.1 ≠ some .timeOut := by
              intro m
              induction m using Nat.strongRecOn with
              | ind m ih =>
                intro st hst_code w hw hlen hw_le hm hst_clk
                have hcond :
                    evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
                      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
                    some (.val (.word (if w.toNat < lenVal.toNat then 1 else 0))) := by
                  rw [evalHOLFinite_eq_toExact]
                  simp only [evalHOLExact, hw, hlen, Compiler.Encoders.Asm.wordCmpHOL]
                  by_cases hlt : w.toNat < lenVal.toNat
                  · simp [hlt, BitVec.lt_def]
                  · simp [hlt, BitVec.lt_def]
                dsimp only
                rw [evaluateHOLFiniteState_while_total, hcond]
                by_cases hlt : w.toNat < lenVal.toNat
                · rw [if_pos hlt]
                  simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
                  have hm_pos : 0 < m := by
                    have h8 : 8 ≤ lenVal.toNat + 7 - w.toNat := by omega
                    have hd := Nat.div_pos h8 (by decide : 0 < 8)
                    omega
                  have hclk_nz : st.clock ≠ 0 := by omega
                  rw [if_neg hclk_nz, fixClockHOLFinite_evaluateState]
                  let st1 := decClockHOLFinite st
                  have hbody_bound := (ProgBounded.straight loopBody rfl) st1 hst_code (by omega)
                  have hbody_nc := evaluate_noTopContinue loopBody rfl st1
                  have hbody_meta := PanRunBounded.evaluateHOLFiniteState_metadata st1 loopBody
                  rcases hb : evaluateHOLFiniteState st1 loopBody with ⟨res, mid⟩
                  rw [hb] at hbody_bound hbody_nc hbody_meta
                  dsimp only at hbody_bound hbody_nc hbody_meta
                  change st.clock - 1 ≤ mid.clock + 0 ∧ mid.clock ≤ st.clock - 1 ∧ res ≠ some .timeOut at hbody_bound
                  cases res with
                  | none =>
                    dsimp only
                    have hseq1 : evaluateHOLFiniteState st1 (.seq loadW (.seq storeW incrI)) = (none, mid) := hb
                    rw [evaluateHOLFiniteState_seq_line780] at hseq1
                    rcases hl : evaluateHOLFiniteState st1 loadW with ⟨rl, smid1⟩
                    rw [hl] at hseq1
                    cases rl with
                    | some r => simp at hseq1
                    | none =>
                      dsimp only at hseq1
                      obtain ⟨wLoaded, hsmid1_loc, _, _⟩ := evaluate_shMemLoad_local_none st1 .opW (ofString "w")
                        (.op .add [.const 1073741840#64, .var .local (ofString "i")]) hl
                      rw [evaluateHOLFiniteState_seq_line780] at hseq1
                      have hstore_frame := evaluate_store_control_frame smid1
                        (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
                        (.var .local (ofString "w"))
                      rcases hst : evaluateHOLFiniteState smid1 storeW with ⟨rst, smid2⟩
                      rw [hst] at hseq1 hstore_frame
                      cases rst with
                      | some r => simp at hseq1
                      | none =>
                        dsimp only at hseq1 hstore_frame
                        have hsmid2_i : smid2.locals.lookup (ofString "i") = some (.val (.word w)) := by
                          rw [hstore_frame.2.1, hsmid1_loc]
                          have hne : ofString "w" ≠ ofString "i" := by decide
                          simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
                          exact hw
                        have hsmid2_len : smid2.locals.lookup (ofString "len") = some (.val (.word lenVal)) := by
                          rw [hstore_frame.2.1, hsmid1_loc]
                          have hne : ofString "w" ≠ ofString "len" := by decide
                          simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
                          exact hlen
                        have hassign : evaluateHOLFiniteState smid2 incrI =
                            (none, setVarHOLFinite (ofString "i") (.val (.word (w + 8#64))) smid2) := by
                          simp [incrI, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
                            hsmid2_i, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                            isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                        rw [hassign] at hseq1
                        obtain ⟨_, rfl⟩ := Prod.mk.inj hseq1
                        have hmid_i : (setVarHOLFinite (ofString "i") (.val (.word (w + 8#64))) smid2).locals.lookup (ofString "i") =
                            some (.val (.word (w + 8#64))) := by
                          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        have hmid_len : (setVarHOLFinite (ofString "i") (.val (.word (w + 8#64))) smid2).locals.lookup (ofString "len") =
                            some (.val (.word lenVal)) := by
                          have hne : ofString "i" ≠ ofString "len" := by decide
                          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hsmid2_len]
                        have h8nat : (8#64).toNat = 8 := rfl
                        have hnat : (w + 8#64).toNat = w.toNat + 8 := by
                          rw [BitVec.toNat_add_of_lt (by rw [h8nat]; omega), h8nat]
                        have hdiv_step : (lenVal.toNat + 7 - w.toNat) / 8 =
                            (lenVal.toNat + 7 - (w + 8#64).toNat) / 8 + 1 := by
                          have hsub : lenVal.toNat + 7 - (w + 8#64).toNat + 8 = lenVal.toNat + 7 - w.toNat := by
                            rw [hnat]; omega
                          rw [← hsub, Nat.add_div_right _ (by decide : 0 < 8)]
                        let m' := (lenVal.toNat + 7 - (w + 8#64).toNat) / 8
                        obtain ⟨t1, t2, t3⟩ := ih m' (by omega)
                          _ (hbody_meta.1.trans hst_code) (w + 8#64) hmid_i hmid_len
                          (by rw [hnat]; omega) rfl (by omega)
                        exact ⟨by omega, by omega, t3⟩
                  | some r =>
                    cases r with
                    | «continue» => exact absurd rfl hbody_nc
                    | timeOut => exact absurd rfl hbody_bound.2.2
                    | «break» | error | returned _ | exception _ _ | finalFfi _ =>
                      exact ⟨by simp; omega, by simp; omega, by simp⟩
                · rw [if_neg hlt]
                  simp
            have hm0_le : (lenVal.toNat + 7) / 8 ≤ 134217726 := by omega
            have h0nat : (0#64).toNat = 0 := rfl
            have h := haux ((lenVal.toNat + 7) / 8) s4 hs4_code 0#64 hs4_i hs4_len
              (by rw [h0nat]; omega)
              (by rw [h0nat]; simp)
              (by rw [hs4_clk]; omega)
            exact ⟨by have := h.1; omega, h.2.1, h.2.2⟩
          exact (RunBounded.seq hloop (a := 134217726) (b := 0)
            (by rw [hs4_clk]; omega)
            (fun next _ nextCode nextBudget =>
              (ProgBounded.straight
                (.return (.rstruct [.var .local (ofString "p"), .var .local (ofString "len")]))
                rfl) next (nextCode.trans hs4_code) nextBudget)).weaken (by omega))
      unfold RunBounded at hdc
      exact ⟨by omega, by omega, hdc.2.2⟩

private theorem lookup_ssz_check_offsets :
    originalRuntimeCode.lookup (ofString "ssz_check_offsets") =
      some ([(ofString "offs", .one), (ofString "n", .one), (ofString "fixed", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_ssz_check_offsets, .one) :=
  lookup_of_guestAst_getElem 201 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_check_offsets) rfl

private theorem evalListHOLFinite_four_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 e4 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3, e4] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1 v3 v4, vs = [v1, .val (.word K), v3, v4] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs
    rcases h3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
    · rw [h3] at hargs; cases hargs
    · rw [h3] at hargs
      rcases h4 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e4 with _ | v4
      · rw [h4] at hargs; cases hargs
      · rw [h4] at hargs; cases hargs; exact ⟨v1, v3, v4, rfl⟩

private theorem pan_four_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name p1 p2 p3 p4 : MlS) (body : ProgHOL width) (w1 w2 w3 w4 : BitVec width)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp14 : p1 ≠ p4)
    (hp23 : p2 ≠ p3) (hp24 : p2 ≠ p4) (hp34 : p3 ≠ p4)
    (lookup : code name = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update
          (p3, .val (.word w3))).update (p4, .val (.word w4)), .one) := by
  have raw : lookupCodeHOLExact code name [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (fun key =>
          if key = p4 then some (.val (.word w4))
          else if key = p3 then some (.val (.word w3))
          else if key = p2 then some (.val (.word w2))
          else if key = p1 then some (.val (.word w1))
          else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, hp12, hp13, hp14, hp23, hp24, hp34]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases h4 : key = p4
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have hb4 := Ne.symm h4
      by_cases h3 : key = p3
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hp34, Ne.symm hp34]
      · have hb3 := Ne.symm h3
        by_cases h2 : key = p2
        · subst key
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            hp24, Ne.symm hp24, hp23, Ne.symm hp23]
        · have hb2 := Ne.symm h2
          by_cases h1 : key = p1
          · subst key
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              hp14, Ne.symm hp14, hp13, Ne.symm hp13, hp12, Ne.symm hp12]
          · have hb1 := Ne.symm h1
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              h1, h2, h3, h4, hb1, hb2, hb3, hb4]

private theorem four_arg_lookup_second (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 p3 p4 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp14 : p1 ≠ p4)
    (hp23 : p2 ≠ p3) (hp24 : p2 ≠ p4) (hp34 : p3 ≠ p4)
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one))
    {v1 v3 v4 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K), v3, v4] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup p2 = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, .val (.word K), v3, v4] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | val wl1 =>
    cases wl1 with
    | word w1 =>
      cases v3 with
      | rStruct _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | nStruct _ _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | val wl3 =>
        cases wl3 with
        | word w3 =>
          cases v4 with
          | rStruct _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
          | nStruct _ _ =>
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
            split at hfound
            · cases hfound
            · rename_i _ _ _ raw; simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
          | val wl4 =>
            cases wl4 with
            | word w4 =>
              rw [pan_four_word_lookup code fn p1 p2 p3 p4 body w1 K w3 w4 hp12 hp13 hp14 hp23 hp24 hp34 hlookup_fn] at hfound
              cases hfound
              simp [HolFiniteMapExact.lookup_update, FUPDATE, hp23, Ne.symm hp23, hp24, Ne.symm hp24]

private theorem runBounded_ssz_check_offsets_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hlt : K.toNat < 2 ^ 63)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : 3 * K.toNat + 1 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_ssz_check_offsets) (3 * K.toNat + 1) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ssz_check_offsets,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hite0 : ProgBounded
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip) 0 :=
    ProgBounded.straight _ rfl
  have hite0_run := hite0 state hcode (by omega)
  have hite0_fn := evaluate_avoidsLocal_flowing (ofString "n")
    (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip) rfl state
  have hite0_meta := PanRunBounded.evaluateHOLFiniteState_metadata state
    (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip)
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hrun0 : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip) with ⟨r0, s1⟩
  rw [hrun0] at hite0_run hite0_fn hite0_meta
  dsimp only at hite0_run hite0_fn hite0_meta ⊢
  cases r0 with
  | some r =>
    dsimp only
    exact ⟨by omega, hite0_run.2.1, hite0_run.2.2⟩
  | none =>
    dsimp only
    have hs1_code : s1.code = originalRuntimeCode := hite0_meta.1.trans hcode
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) :=
      (hite0_fn (Or.inl rfl)).trans atN
    have hrest : RunBounded s1
        (.dec (ofString "i") .one (.const 0#64)
          (.seq
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
              (.dec (ofString "o") .one
                (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
                (.seq
                  (.ite (.cmp .notEqual (.const 0#64)
                    (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
                      .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
                    (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64])
                    .skip)
                  (.seq
                    (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
                      (.ite (.cmp .lower (.var .local (ofString "o"))
                        (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                          .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
                        (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64])
                        .skip)
                      .skip)
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))))
            (.seq
              (.ite (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed")))
                (.call (some (none, none)) (ofString "ssz_fail") [.const 12#64])
                .skip)
              (.return (.const 0#64)))))
        (3 * K.toNat + 1) := by
      apply RunBounded.decConst
      let s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
      have hs2_clk : s2.clock = s1.clock := rfl
      have hs2_code : s2.code = originalRuntimeCode := hs1_code
      have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word K)) := by
        have hne : ofString "i" ≠ ofString "n" := by decide
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_n]
      have hc1 : ProgBounded
          (.ite (.cmp .notEqual (.const 0#64)
            (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
              .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
            (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64])
            .skip) 1 :=
        ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl)
      have hc2 : ProgBounded
          (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
            (.ite (.cmp .lower (.var .local (ofString "o"))
              (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
              (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64])
              .skip)
            .skip) 1 :=
        ProgBounded.iteMax _
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl)
      have hcb : CountedBody (ofString "i") 1
          (.dec (ofString "o") .one
            (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
            (.seq
              (.ite (.cmp .notEqual (.const 0#64)
                (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
                  .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
                (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64])
                .skip)
              (.seq
                (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
                  (.ite (.cmp .lower (.var .local (ofString "o"))
                    (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                      .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
                    (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64])
                    .skip)
                  .skip)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))
          2 := by
        refine CountedBody.dec _ _ _ (by decide) ?_
        exact CountedBody.seq _ hc1 rfl rfl (CountedBody.seq _ hc2 rfl rfl CountedBody.incr)
      have h0nat : (0#64).toNat = 0 := rfl
      have hloop_raw := variableCountedWhile_run (ofString "i") (ofString "n") .less (Or.inl rfl) K
        (fun _ => hlt) hcb rfl K.toNat s2 hs2_code 0#64 hs2_i hs2_n
        (by rw [h0nat]; omega) (by rw [h0nat]; simp)
        (by rw [hs2_clk]; omega)
      have hloop : RunBounded s2
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
            (.dec (ofString "o") .one
              (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
              (.seq
                (.ite (.cmp .notEqual (.const 0#64)
                  (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
                    .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
                  (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64])
                  .skip)
                (.seq
                  (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
                    (.ite (.cmp .lower (.var .local (ofString "o"))
                      (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                        .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
                      (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64])
                      .skip)
                    .skip)
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))))
          (3 * K.toNat) := by
        unfold RunBounded
        exact ⟨by have := hloop_raw.1; omega, hloop_raw.2.1, hloop_raw.2.2⟩
      have htail : ProgBounded
          (.seq
            (.ite (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed")))
              (.call (some (none, none)) (ofString "ssz_fail") [.const 12#64])
              .skip)
            (.return (.const 0#64))) 1 :=
        ProgBounded.seq
          (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
          (ProgBounded.straight _ rfl)
      exact RunBounded.seq hloop (a := 3 * K.toNat) (b := 1)
        (by rw [hs2_clk]; omega)
        (fun next _ nextCode nextBudget => htail next (nextCode.trans hs2_code) nextBudget)
    unfold RunBounded at hrest
    exact ⟨by omega, by omega, hrest.2.2⟩

theorem progBounded_ssz_check_offsets_const (destination : Option (VarKind × MlS))
    (offs fixed len : ExpHOL 64) (K : BitVec 64) (hlt : K.toNat < 2 ^ 63) :
    ProgBounded (.call (some (destination, none)) (ofString "ssz_check_offsets") [offs, .const K, fixed, len])
      (3 * K.toNat + 2) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [offs, .const K, fixed, len] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v3, v4, rfl⟩ := evalListHOLFinite_four_word2 state offs (.const K) fixed len K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := four_arg_lookup_second originalRuntimeCode.lookup
        (ofString "ssz_check_offsets") (ofString "offs") (ofString "n") (ofString "fixed") (ofString "len")
        (sourceFnBody Guest.Software.guestFn_ssz_check_offsets)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        lookup_ssz_check_offsets hfound
      exact runBounded_ssz_check_offsets_body (callEntryStateHOLFinite state locals) K hlt hcode hn
        (by change 3 * K.toNat + 1 ≤ state.clock - 1; omega))

theorem funBounded_precheck_host_ssz_header : FunBounded (ofString "precheck_host_ssz_header") 85 := by
  refine funBounded_of_guestAst 199 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_precheck_host_ssz_header 85 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_precheck_host_ssz_header,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine ProgBounded.weaken
    (ProgBounded.dec _ _ _
      (progBounded_seq_straight _ _ rfl
        (progBounded_seq_straight _ _ rfl
          (ProgBounded.seq
            (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
            (ProgBounded.decCall funBounded_host_input_byte _ _ _
              (ProgBounded.decCall funBounded_host_input_byte _ _ _
                (ProgBounded.seq
                  (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                  (ProgBounded.dec _ _ _
                    (ProgBounded.seq
                      (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                      (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                        (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                          (progBounded_seq_straight _ _ rfl
                            (progBounded_seq_straight _ _ rfl
                              (ProgBounded.seq
                                (progBounded_ssz_check_offsets_const _ _ _ _ 2#64 (by decide))
                                (ProgBounded.dec _ _ _
                                  (ProgBounded.seq
                                    (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                                    (ProgBounded.dec _ _ _
                                      (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                        (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                          (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                            (progBounded_seq_straight _ _ rfl
                                              (progBounded_seq_straight _ _ rfl
                                                (progBounded_seq_straight _ _ rfl
                                                  (ProgBounded.seq
                                                    (progBounded_ssz_check_offsets_const _ _ _ _ 3#64 (by decide))
                                                    (ProgBounded.dec _ _ _
                                                      (ProgBounded.seq
                                                        (ProgBounded.iteMax _ (ProgBounded.call funBounded_ssz_fail _ _) (ProgBounded.straight _ rfl))
                                                        (ProgBounded.dec _ _ _
                                                          (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                                            (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                                              (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                                                (ProgBounded.decCall funBounded_host_input_le32 _ _ _
                                                                  (progBounded_seq_straight _ _ rfl
                                                                    (progBounded_seq_straight _ _ rfl
                                                                      (progBounded_seq_straight _ _ rfl
                                                                        (progBounded_seq_straight _ _ rfl
                                                                          (ProgBounded.seq
                                                                            (progBounded_ssz_check_offsets_const _ _ _ _ 4#64 (by decide))
                                                                            (ProgBounded.straight _ rfl)))))))))))))))))))))))))))))))))))))
    (by decide)

theorem funBounded_decode_host_input_reduced
    (K_decode_stateless : Nat)
    (h_decode_stateless : FunBounded (ofString "decode_stateless_input") K_decode_stateless) :
    FunBounded (ofString "decode_host_input") (K_decode_stateless + 134217816) :=
  funBounded_of_guestAst 200 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_decode_host_input _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call funBounded_precheck_host_ssz_header _ _)
        (ProgBounded.decCall funBounded_input_blob_verified _ _ _
          (ProgBounded.tail h_decode_stateless _)))
      (by omega))

theorem funBounded_main_concrete
    (K_decode_stateless K_htr_payload K_htr_plist_chunks K_htr_requests K_merkleize K_run_attempt : Nat)
    (h_decode_stateless : FunBounded (ofString "decode_stateless_input") K_decode_stateless)
    (h_htr_payload : FunBounded (ofString "htr_payload") K_htr_payload)
    (h_htr_plist_chunks : FunBounded (ofString "htr_plist_chunks") K_htr_plist_chunks)
    (h_htr_requests : FunBounded (ofString "htr_requests") K_htr_requests)
    (h_merkleize : FunBounded (ofString "merkleize") K_merkleize)
    (h_run_attempt : FunBounded (ofString "run_attempt") K_run_attempt) :
    FunBounded (ofString "main")
      (K_decode_stateless + K_htr_payload + K_htr_plist_chunks + K_htr_requests +
        K_merkleize + K_run_attempt + 2 * (2 ^ 64 - 1) + 134218964) := by
  have hmz32 : ProgBounded
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "z32"), .const (BitVec.ofNat 64 32)]) 12 :=
    ProgBounded.weaken (progBounded_memzero_const _ _ (BitVec.ofNat 64 32) (by decide)) (by decide)
  exact funBounded_of_guestAst 889 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_main _ rfl
    (ProgBounded.weaken
      (ProgBounded.seq (ProgBounded.call funBounded_mem_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_sha256_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_keccak_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_ssz_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_mpt_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_u256_ws_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_secp256k1_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_bn254_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_bls_precompiles_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_ripemd160_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_blake2_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_header_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_evm_init _ _)
      (ProgBounded.seq (ProgBounded.call funBounded_fork_init _ _)
      (ProgBounded.decCall funBounded_alloc _ _ _
        (ProgBounded.decCall funBounded_alloc _ _ _
          (ProgBounded.seq hmz32
            (ProgBounded.dec _ _ _
              (ProgBounded.dec _ _ _
                (ProgBounded.seq
                  (ProgBounded.handledCall
                    (funBounded_decode_host_input_reduced K_decode_stateless h_decode_stateless) _ _ _ _
                    (ProgBounded.decCall funBounded_serialize_result _ _ _
                      (ProgBounded.seq (ProgBounded.straight _ rfl)
                        (ProgBounded.seq (ProgBounded.call funBounded_output_write _ _)
                          (ProgBounded.straight _ rfl)))))
                  (ProgBounded.decCall funBounded_alloc _ _ _
                    (ProgBounded.seq
                      (ProgBounded.call
                        (funBounded_htr_new_payload_request K_htr_payload K_htr_plist_chunks
                          K_htr_requests K_merkleize h_htr_payload h_htr_plist_chunks h_htr_requests h_merkleize)
                        _ _)
                      (ProgBounded.decCall
                        (funBounded_verify_stateless_new_payload K_run_attempt h_run_attempt) _ _ _
                        (ProgBounded.decCall funBounded_serialize_result _ _ _
                          (ProgBounded.seq (ProgBounded.straight _ rfl)
                            (ProgBounded.seq (ProgBounded.call funBounded_output_write _ _)
                              (ProgBounded.straight _ rfl)))))))))))))))))))))))))))
      (by generalize (2 : Nat) ^ 64 - 1 = W; omega))

end InitECandidate.Solver.GuestBoundMain
