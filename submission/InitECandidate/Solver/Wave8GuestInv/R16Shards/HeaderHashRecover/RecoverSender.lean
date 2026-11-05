import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## Section 1: Precondition Bridge (`TxValidRecoverReadyAt` / `TxValidRecoverReady`) -/

def TxValidRecoverReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (tx : Nat) : Prop :=
  TxValidAt s tx ∧
  (0 < memW s (tx + 216) → Inside (memW s (tx + 208), 24 * memW s (tx + 216)) sourceBase (globN s "heap_ptr")) ∧
  (0 < memW s (tx + 280) → Inside (memW s (tx + 272), 120 * memW s (tx + 280)) sourceBase (globN s "heap_ptr"))

def TxValidRecoverReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxValidRecoverReadyAt s (locN s "tx")

/-! ## Section 2: `Guest.Software.guestAst` Lookups -/

private theorem lookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

private theorem lookup_st_be32 :
    originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
  lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be32) rfl

private theorem lookup_st_be64 :
    originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)], sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
  lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be64) rfl

private theorem lookup_u256_to_be32 :
    originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be32, .one) :=
  lookup_of_guestAst_getElem 87 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be32) rfl

private theorem lookup_u256_to_be_min :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be_min, .one) :=
  lookup_of_guestAst_getElem 88 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be_min) rfl

private theorem lookup_fn_mul :
    originalRuntimeCode.lookup (ofString "fn_mul") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_fn_mul, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 162 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fn_mul) rfl

private theorem lookup_ec_set_infinity :
    originalRuntimeCode.lookup (ofString "ec_set_infinity") =
      some ([(ofString "pt", .one)], sourceFnBody Guest.Software.guestFn_ec_set_infinity, .one) :=
  lookup_of_guestAst_getElem 167 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_set_infinity) rfl

private theorem lookup_ec_set_affine :
    originalRuntimeCode.lookup (ofString "ec_set_affine") =
      some ([(ofString "pt", .one),
             (ofString "x", .comb [.one, .one, .one, .one]),
             (ofString "y", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_ec_set_affine, .one) :=
  lookup_of_guestAst_getElem 168 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_set_affine) rfl

private theorem lookup_ec_double :
    originalRuntimeCode.lookup (ofString "ec_double") =
      some ([(ofString "pt", .one)], sourceFnBody Guest.Software.guestFn_ec_double, .one) :=
  lookup_of_guestAst_getElem 170 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_double) rfl

private theorem lookup_ec_add_affine :
    originalRuntimeCode.lookup (ofString "ec_add_affine") =
      some ([(ofString "pt", .one),
             (ofString "ax", .comb [.one, .one, .one, .one]),
             (ofString "ay", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_ec_add_affine, .one) :=
  lookup_of_guestAst_getElem 171 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_add_affine) rfl

private theorem lookup_ec_mul2 :
    originalRuntimeCode.lookup (ofString "ec_mul2") =
      some ([(ofString "out", .one),
             (ofString "k1", .comb [.one, .one, .one, .one]),
             (ofString "ax", .comb [.one, .one, .one, .one]),
             (ofString "ay", .comb [.one, .one, .one, .one]),
             (ofString "k2", .comb [.one, .one, .one, .one]),
             (ofString "bx", .comb [.one, .one, .one, .one]),
             (ofString "by", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_ec_mul2, .one) :=
  lookup_of_guestAst_getElem 174 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_mul2) rfl

private theorem lookup_ec_to_affine :
    originalRuntimeCode.lookup (ofString "ec_to_affine") =
      some ([(ofString "pt", .one)], sourceFnBody Guest.Software.guestFn_ec_to_affine, .one) :=
  lookup_of_guestAst_getElem 175 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ec_to_affine) rfl

private theorem lookup_secp256k1_decompress_r :
    originalRuntimeCode.lookup (ofString "secp256k1_decompress_r") =
      some ([(ofString "r", .comb [.one, .one, .one, .one]),
             (ofString "recid", .one),
             (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r, .one) :=
  lookup_of_guestAst_getElem 177 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_secp256k1_decompress_r) rfl

private theorem lookup_secp256k1_recover :
    originalRuntimeCode.lookup (ofString "secp256k1_recover") =
      some ([(ofString "msg_hash", .one),
             (ofString "r", .comb [.one, .one, .one, .one]),
             (ofString "s", .comb [.one, .one, .one, .one]),
             (ofString "recid", .one),
             (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_secp256k1_recover, .one) :=
  lookup_of_guestAst_getElem 178 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_secp256k1_recover) rfl

private theorem lookup_tx_put_u256 :
    originalRuntimeCode.lookup (ofString "tx_put_u256") =
      some ([(ofString "dst", .one), (ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_tx_put_u256, .one) :=
  lookup_of_guestAst_getElem 318 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_u256) rfl

private theorem lookup_tx_u256_encoded_len :
    originalRuntimeCode.lookup (ofString "tx_u256_encoded_len") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len, .one) :=
  lookup_of_guestAst_getElem 319 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_u256_encoded_len) rfl

private theorem lookup_tx_put_to :
    originalRuntimeCode.lookup (ofString "tx_put_to") =
      some ([(ofString "dst", .one), (ofString "to", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_to, .one) :=
  lookup_of_guestAst_getElem 320 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_to) rfl

private theorem lookup_access_list_payload_len :
    originalRuntimeCode.lookup (ofString "access_list_payload_len") =
      some ([(ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_access_list_payload_len, .one) :=
  lookup_of_guestAst_getElem 321 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_access_list_payload_len) rfl

private theorem lookup_tx_put_access_list :
    originalRuntimeCode.lookup (ofString "tx_put_access_list") =
      some ([(ofString "dst", .one), (ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_access_list, .one) :=
  lookup_of_guestAst_getElem 322 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_access_list) rfl

private theorem lookup_tx_put_blob_hashes :
    originalRuntimeCode.lookup (ofString "tx_put_blob_hashes") =
      some ([(ofString "dst", .one), (ofString "buf", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes, .one) :=
  lookup_of_guestAst_getElem 323 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_blob_hashes) rfl

private theorem lookup_auth_payload_len :
    originalRuntimeCode.lookup (ofString "auth_payload_len") =
      some ([(ofString "a", .one)],
        sourceFnBody Guest.Software.guestFn_auth_payload_len, .one) :=
  lookup_of_guestAst_getElem 324 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_auth_payload_len) rfl

private theorem lookup_auth_list_payload_len :
    originalRuntimeCode.lookup (ofString "auth_list_payload_len") =
      some ([(ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_auth_list_payload_len, .one) :=
  lookup_of_guestAst_getElem 325 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_auth_list_payload_len) rfl

private theorem lookup_tx_put_authorizations :
    originalRuntimeCode.lookup (ofString "tx_put_authorizations") =
      some ([(ofString "dst", .one), (ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_authorizations, .one) :=
  lookup_of_guestAst_getElem 326 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_authorizations) rfl

private theorem lookup_tx_encode_bound :
    originalRuntimeCode.lookup (ofString "tx_encode_bound") =
      some ([(ofString "tx", .one)],
        sourceFnBody Guest.Software.guestFn_tx_encode_bound, .one) :=
  lookup_of_guestAst_getElem 327 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_encode_bound) rfl

private theorem lookup_tx_encode_generic :
    originalRuntimeCode.lookup (ofString "tx_encode_generic") =
      some ([(ofString "tx", .one), (ofString "mode", .one), (ofString "chain_id", .one)],
        sourceFnBody Guest.Software.guestFn_tx_encode_generic, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 328 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_encode_generic) rfl

private theorem lookup_tx_signing_hash_mode :
    originalRuntimeCode.lookup (ofString "tx_signing_hash_mode") =
      some ([(ofString "tx", .one), (ofString "mode", .one), (ofString "chain_id", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_tx_signing_hash_mode, .one) :=
  lookup_of_guestAst_getElem 331 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_signing_hash_mode) rfl

private theorem lookup_signing_hash_pre155 :
    originalRuntimeCode.lookup (ofString "signing_hash_pre155") =
      some ([(ofString "tx", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_pre155, .one) :=
  lookup_of_guestAst_getElem 332 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_pre155) rfl

private theorem lookup_signing_hash_155 :
    originalRuntimeCode.lookup (ofString "signing_hash_155") =
      some ([(ofString "tx", .one), (ofString "chain_id", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_155, .one) :=
  lookup_of_guestAst_getElem 333 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_155) rfl

private theorem lookup_signing_hash_2930 :
    originalRuntimeCode.lookup (ofString "signing_hash_2930") =
      some ([(ofString "tx", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_2930, .one) :=
  lookup_of_guestAst_getElem 334 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_2930) rfl

private theorem lookup_signing_hash_1559 :
    originalRuntimeCode.lookup (ofString "signing_hash_1559") =
      some ([(ofString "tx", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_1559, .one) :=
  lookup_of_guestAst_getElem 335 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_1559) rfl

private theorem lookup_signing_hash_4844 :
    originalRuntimeCode.lookup (ofString "signing_hash_4844") =
      some ([(ofString "tx", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_4844, .one) :=
  lookup_of_guestAst_getElem 336 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_4844) rfl

private theorem lookup_signing_hash_7702 :
    originalRuntimeCode.lookup (ofString "signing_hash_7702") =
      some ([(ofString "tx", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_signing_hash_7702, .one) :=
  lookup_of_guestAst_getElem 337 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signing_hash_7702) rfl

private theorem lookup_signature_recovery_parameters :
    originalRuntimeCode.lookup (ofString "signature_recovery_parameters") =
      some ([(ofString "tx", .one), (ofString "chain_id", .one), (ofString "out_hash", .one)],
        sourceFnBody Guest.Software.guestFn_signature_recovery_parameters, .one) :=
  lookup_of_guestAst_getElem 339 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_signature_recovery_parameters) rfl

private theorem lookup_recover_transaction_public_key :
    originalRuntimeCode.lookup (ofString "recover_transaction_public_key") =
      some ([(ofString "tx", .one), (ofString "chain_id", .one), (ofString "out64", .one)],
        sourceFnBody Guest.Software.guestFn_recover_transaction_public_key, .one) :=
  lookup_of_guestAst_getElem 340 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_recover_transaction_public_key) rfl

private theorem lookup_sender_address_from_public_key :
    originalRuntimeCode.lookup (ofString "sender_address_from_public_key") =
      some ([(ofString "pubkey65", .one), (ofString "out20", .one)],
        sourceFnBody Guest.Software.guestFn_sender_address_from_public_key, .one) :=
  lookup_of_guestAst_getElem 341 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sender_address_from_public_key) rfl

private theorem lookup_recover_sender_with_chain_id :
    originalRuntimeCode.lookup (ofString "recover_sender_with_chain_id") =
      some ([(ofString "tx", .one), (ofString "chain_id", .one), (ofString "out20", .one)],
        sourceFnBody Guest.Software.guestFn_recover_sender_with_chain_id, .one) :=
  lookup_of_guestAst_getElem 343 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_recover_sender_with_chain_id) rfl

/-! ## Section 3: Closed Read-Only Callee Table `recRoCallees` -/

private theorem readOnlyProg_mono {g1 g2 : MlS → Bool}
    (hsub : ∀ f, g1 f = true → g2 f = true) :
    ∀ p : ProgHOL 64, readOnlyProg g1 p = true → readOnlyProg g2 p = true
  | .dec _ _ _ b, h => readOnlyProg_mono hsub b h
  | .seq a b, h => by
    simp only [readOnlyProg, Bool.and_eq_true] at h ⊢
    exact ⟨readOnlyProg_mono hsub a h.1, readOnlyProg_mono hsub b h.2⟩
  | .ite _ a b, h => by
    simp only [readOnlyProg, Bool.and_eq_true] at h ⊢
    exact ⟨readOnlyProg_mono hsub a h.1, readOnlyProg_mono hsub b h.2⟩
  | .while _ b, h => readOnlyProg_mono hsub b h
  | .decCall _ _ f _ b, h => by
    simp only [readOnlyProg, Bool.and_eq_true] at h ⊢
    exact ⟨hsub f h.1, readOnlyProg_mono hsub b h.2⟩
  | .call none f _, h => hsub f h
  | .call (some (none, none)) f _, h => by
    simp only [readOnlyProg, Bool.or_eq_true] at h ⊢
    exact h.imp id (hsub f)
  | .call (some (some (.local, _), none)) f _, h => hsub f h
  | .call (some (some (.global, _), _)) _ _, h => by simp [readOnlyProg] at h
  | .call (some (_, some _)) _ _, h => by simp [readOnlyProg] at h
  | .assign .local _ _, _ => rfl
  | .assign .global _ _, h => by simp [readOnlyProg] at h
  | .primitive _ _ _, _ => rfl
  | .skip, _ | .break, _ | .continue, _ | .annot _ _, _ | .raise _ _, _ | .return _, _ => rfl
  | .store _ _, h | .storeByte _ _, h | .shMemLoad _ _ _ _, h
  | .shMemStore _ _ _, h | .extCall _ _ _ _ _, h => by simp [readOnlyProg] at h

private def recRoCallees (f : MlS) : Bool :=
  opRoCallees f ||
  f == ofString "min" ||
  f == ofString "max" ||
  f == ofString "rlp_be_len" ||
  f == ofString "rlp_header_len" ||
  f == ofString "rlp_bytes_encoded_len" ||
  f == ofString "rlp_list_header_len" ||
  f == ofString "rlp_word_encoded_len" ||
  f == ofString "fp_add" ||
  f == ofString "fp_sub" ||
  f == ofString "fp_neg" ||
  f == ofString "fp_reduce" ||
  f == ofString "fp_mul" ||
  f == ofString "fp_sqr" ||
  f == ofString "fp_pow" ||
  f == ofString "fp_inv_fermat" ||
  f == ofString "modinv_bin" ||
  f == ofString "mod_half" ||
  f == ofString "mod_sub" ||
  f == ofString "fp_inv" ||
  f == ofString "fp_sqrt" ||
  f == ofString "fn_inv" ||
  f == ofString "ec_is_infinity" ||
  f == ofString "ec_on_curve" ||
  f == ofString "tx_u256_encoded_len" ||
  f == ofString "access_list_payload_len" ||
  f == ofString "auth_payload_len" ||
  f == ofString "auth_list_payload_len" ||
  f == ofString "tx_encode_bound" ||
  f == ofString "tx_chain_id"

private theorem recRoCallees_good :
    ∀ function, recRoCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg recRoCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [recRoCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with ((((((((((((((((((((((((((((hop | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · exact readOnlyProg_mono (fun g hg => by simp [recRoCallees, hg]) body
      (opRoCallees_good function hop values body callee rs hfound)
  · exact installed_body_readOnly 31 (by rw [guestAst_len]; decide) Guest.Software.guestFn_min rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 118 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_be_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 121 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_header_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 125 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_bytes_encoded_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 126 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_list_header_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 127 (by rw [guestAst_len]; decide) Guest.Software.guestFn_rlp_word_encoded_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 149 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_add rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 150 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_sub rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 151 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_neg rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 152 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_reduce rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 153 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_mul rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 154 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_sqr rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 155 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_pow rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 156 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_inv_fermat rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 157 (by rw [guestAst_len]; decide) Guest.Software.guestFn_modinv_bin rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 158 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mod_half rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 159 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mod_sub rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 160 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_inv rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 161 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fp_sqrt rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 166 (by rw [guestAst_len]; decide) Guest.Software.guestFn_fn_inv rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 169 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ec_is_infinity rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 176 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ec_on_curve rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 319 (by rw [guestAst_len]; decide) Guest.Software.guestFn_tx_u256_encoded_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 321 (by rw [guestAst_len]; decide) Guest.Software.guestFn_access_list_payload_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 324 (by rw [guestAst_len]; decide) Guest.Software.guestFn_auth_payload_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 325 (by rw [guestAst_len]; decide) Guest.Software.guestFn_auth_list_payload_len rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 327 (by rw [guestAst_len]; decide) Guest.Software.guestFn_tx_encode_bound rfl recRoCallees (by decide) hfound
  · exact installed_body_readOnly 338 (by rw [guestAst_len]; decide) Guest.Software.guestFn_tx_chain_id rfl recRoCallees (by decide) hfound

private theorem wsSafe_of_recRo {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {prog : ProgHOL 64} (hcode : s.code = originalRuntimeCode)
    (hro : readOnlyProg recRoCallees prog = true) :
    WsSafe s Rl (evaluateHOLFiniteState s prog) :=
  WsSafe.of_safeOrTrapped (evaluate_readOnlyProg recRoCallees recRoCallees_good prog hro s hcode)

/-! ## Section 4: `HeapByteEff` / `M23.ByteRegionEffect` / `WsSafe` Bridges -/

private theorem wsEnv_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s) : WsEnv s s := by
  refine ⟨hc, hW.1.1.memaddrs, rfl, ?_⟩
  by_cases hz : globN s "u256_ws" = 0
  · exact Or.inl hz
  · obtain ⟨hAR, S0, hWT0⟩ := hW
    have hmem : (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩
    rw [if_neg hz] at hmem
    rcases hWT0.2.2.1.1 _ hmem with h0 | ⟨hal, _⟩
    · dsimp only at h0; omega
    · have hhl : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
      have hse : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
      obtain ⟨_, hhp_hi, _, hfp_sp, _⟩ := hAR.2
      rcases hal with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (dsimp only at hhi; exact Or.inr (by omega))

private theorem heapByteEff_of_m23_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : Wave8Contracts.M23.ByteRegionEffect s post Rl) :
    HeapByteEff s post Rl gw := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, heff.memaddrs, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun k _ => by rw [heff.globals], ?_, ?_, ?_⟩
  · intro a hne; by_contra hna; exact hne (heff.out_dom a hna)
  · intro a hne; left
    have hdom : ordinaryDomain a := by
      rw [← hAR.1.memaddrs]; by_contra hna; exact hne (heff.out_dom a hna)
    have ha_ord := (WkBlockTxEnc.ordinaryDomain_iff a).1 hdom
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
    by_contra hno
    apply hne
    apply mem_eq_of_bytes_eq heff.be a hdom
    intro k hk
    apply heff.byte_frame (a.toNat + k) (by omega)
    intro i hi ⟨hb1, hb2⟩
    exact hno ⟨i, hi, by omega, by omega, by omega⟩
  · intro b hb hne; left
    by_contra hno
    apply hne; apply heff.byte_frame b hb
    intro i hi hin; exact hno ⟨i, hi, hin⟩

private theorem heapByteEff_of_byteFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (hbf : M13.ByteFrame Rl s post) :
    HeapByteEff s post Rl gw := by
  have hcode : post.code = s.code := by rw [hbf.1]
  have hma : post.memaddrs = s.memaddrs := by rw [hbf.1]
  have hsh : post.shMemaddrs = s.shMemaddrs := by rw [hbf.1]
  have hba : post.baseAddr = s.baseAddr := by rw [hbf.1]
  have hbe : post.be = s.be := by rw [hbf.1]
  have hg : post.globals = s.globals := by rw [hbf.1]
  have hG : GuestInv post := guestInv_congr hcode hma hsh hba hAR.1
  have hA : ArenaOK post := arenaOK_congr hg hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hg]
  refine ⟨⟨hG, hA⟩, hma, by rw [hg_eq], hg_eq _, by rw [hg_eq], hbe,
    fun k _ => by rw [hg],
    fun a hne => (hbf.2.1 a hne).1,
    fun a hne => ?_,
    fun b hb hne => Or.inl (hbf.2.2 b hb hne)⟩
  have hdom : ordinaryDomain a := by rw [← hAR.1.memaddrs]; exact (hbf.2.1 a hne).1
  have ha_ord := (WkBlockTxEnc.ordinaryDomain_iff a).1 hdom
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
  by_contra hno
  apply hne
  apply mem_eq_of_bytes_eq hbe a hdom
  intro k hk
  by_contra hbk
  obtain ⟨r, hr, hri1, hri2⟩ := hbf.2.2 (a.toNat + k) (by omega) hbk
  exact hno (Or.inl ⟨r, hr, by omega, by omega, by omega⟩)

/-! ## Section 5: Multi-Word Store Helper (`panMemStores_bre`) & Curve Operations -/

private theorem panMemStores_eff_rec
    (dom : BitVec 64 → Prop) [DecidablePred dom] (be : Bool)
    (hdom_ord : dom = ordinaryDomain) :
    ∀ (ws : List (HolWordLab 64)) (addr : BitVec 64)
      (mem mem' : BitVec 64 → HolWordLab 64),
      addr.toNat + 8 * ws.length < 2 ^ 64 →
      panMemStoresHOL addr ws dom mem = some mem' →
      (∀ x : BitVec 64, mem' x ≠ mem x →
        dom x ∧ addr.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ addr.toNat + 8 * ws.length) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        (M13.memByteAt mem' be (BitVec.ofNat 64 b)).toNat ≠ (M13.memByteAt mem be (BitVec.ofNat 64 b)).toNat →
        addr.toNat ≤ b ∧ b < addr.toNat + 8 * ws.length)
  | [], _, mem, mem', _, hst => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst; subst hst
    exact ⟨fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  | w :: rest, addr, mem, mem', hlt, hst => by
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hd : dom addr
    · simp only [hd, ↓reduceIte] at hst
      have hbw : (panBytesInWord 64 : BitVec 64).toNat = 8 := rfl
      have hnext_add : (addr + panBytesInWord 64).toNat = addr.toNat + 8 := by
        apply BitVec.toNat_add_of_lt
        rw [hbw]; simp [List.length_cons] at hlt; omega
      have hlt_rest : (addr + panBytesInWord 64).toNat + 8 * rest.length < 2 ^ 64 := by
        rw [hnext_add]; simp [List.length_cons] at hlt; omega
      let mid := fun current => if current = addr then w else mem current
      obtain ⟨ih_c, ih_b⟩ := panMemStores_eff_rec dom be hdom_ord rest (addr + panBytesInWord 64) mid mem' hlt_rest hst
      have hd_ord : addr.toNat % 8 = 0 := by
        rw [hdom_ord, WkBlockTxEnc.ordinaryDomain_iff] at hd; exact hd.1
      refine ⟨?_, ?_⟩
      · intro x hne
        by_cases hxm : mem' x = mid x
        · rw [hxm] at hne
          by_cases hxa : x = addr
          · subst hxa; simp only [List.length_cons]; exact ⟨hd, le_rfl, by omega⟩
          · simp [mid, hxa] at hne
        · obtain ⟨hdx, hx1, hx2⟩ := ih_c x hxm
          rw [hnext_add] at hx1 hx2
          simp only [List.length_cons]; exact ⟨hdx, by omega, by omega⟩
      · intro b hb64 hne
        by_cases hbm : (M13.memByteAt mem' be (BitVec.ofNat 64 b)).toNat =
            (M13.memByteAt mid be (BitVec.ofNat 64 b)).toNat
        · rw [hbm] at hne
          by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
          · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
            rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hc_nat
            simp only [List.length_cons]; omega
          · unfold M13.memByteAt M13.memWordAt at hne; simp [mid, hal] at hne
        · obtain ⟨hb1, hb2⟩ := ih_b b hb64 hbm
          rw [hnext_add] at hb1 hb2
          simp only [List.length_cons]; omega
    · simp [hd] at hst

private theorem wsSafe_store_multi {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst val : ExpHOL 64} (sz : Nat)
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hval_len : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      8 * (flattenHOL v).length ≤ sz)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      addr.toNat + sz < 2 ^ 64 ∧ ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + sz ≤ i.1 + i.2) :
    WsSafe s Rl (evaluateHOLFiniteState s (.store dst val)) ∧
    ((evaluateHOLFiniteState s (.store dst val)).1 = none →
      (evaluateHOLFiniteState s (.store dst val)).2.locals = s.locals) := by
  rcases hrun : evaluateHOLFiniteState s (.store dst val) with ⟨r, post⟩
  refine ⟨⟨fun hn => ?_, fun hr => ?_⟩, fun hn => ?_⟩
  · dsimp only at hn; subst hn
    have hrun0 := hrun
    rw [evaluateHOLFiniteState_store] at hrun0
    revert hrun0
    rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
    · simp
    · rcases dv with ⟨⟨addr⟩⟩ | _ | _ <;> try simp
      rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
      · simp
      · dsimp only
        split
        · rename_i mem' hmem
          intro hrun0
          injection hrun0 with _ hpost; subst hpost
          have hlen := hval_len vv hv
          obtain ⟨hlt_sz, ivl, hivl, hi1, hi2⟩ := hin addr hx
          obtain ⟨hc, hb⟩ := @panMemStores_eff_rec s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a))
            s.be hma_ord (flattenHOL vv) addr s.memory mem' (by omega) hmem
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl,
            fun a hna => by by_contra hne; exact hna (hc a hne).1,
            fun a hno => by
              by_contra hne
              obtain ⟨_, h1, h2⟩ := hc a hne
              exact hno ivl hivl ⟨by omega, by omega⟩,
            fun b hb64 hno => by
              by_contra hne
              rw [M13.memB_eq_memByteAt, M13.memB_eq_memByteAt] at hne
              obtain ⟨h1, h2⟩ := hb b hb64 hne
              exact hno ivl hivl ⟨by omega, by omega⟩⟩
        · simp
  · have hcf := (evaluate_store_control_frame s dst val).1
    rw [hrun] at hcf; dsimp only at hcf hr
    rcases hcf with h | h <;> (rw [h] at hr; rcases hr with ⟨_, h'⟩ | ⟨_, _, h', _⟩ <;> simp at h')
  · dsimp only at hn; subst hn
    have hloc := (evaluate_store_control_frame s dst val).2.1
    rw [hrun] at hloc; exact hloc

/-! ## Section 6: `u256_mulmod`, `fn_mul`, `st_be32`, `st_be64`, `u256_to_be32`, and Curve Specs -/

private theorem bv_add_off_nat_gen (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 128) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [WkBlockTxEnc.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (w : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) = some (.val (.word w)) := hloc

private theorem eval_local_add_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem wsSafe_mono {F : Type} {s : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : WsSafe s R1 out)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    WsSafe s R2 out :=
  ⟨fun hn => (h.1 hn).mono hsub, fun hr => (h.2 hr).mono hsub⟩

private theorem wsSafe_storeByte {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst val : ExpHOL 64}
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat < i.1 + i.2) :
    WsSafe s Rl (evaluateHOLFiniteState s (.storeByte dst val)) ∧
    ((evaluateHOLFiniteState s (.storeByte dst val)).1 = none →
      (evaluateHOLFiniteState s (.storeByte dst val)).2.locals = s.locals) := by
  rcases hrun : evaluateHOLFiniteState s (.storeByte dst val) with ⟨r, post⟩
  refine ⟨⟨fun hn => ?_, fun hr => ?_⟩, fun hn => ?_⟩
  · dsimp only at hn; subst hn
    exact (Wave8Contracts.M23.ByteRegionEffect.of_storeByte hrun hin).1
  · have hrun0 := hrun
    rw [evaluateHOLFiniteState_storeByte] at hrun0
    revert hrun0
    rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
    · intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    · rcases dv with ⟨⟨addr⟩⟩ | _ | _ <;>
        try (intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h)
      rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
      · intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rcases vv with ⟨⟨vw⟩⟩ | _ | _ <;>
          try (intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h)
        dsimp only
        split
        · intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · intro h; injection h with hr' _; subst hr'; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · dsimp only at hn; subst hn
    exact (Wave8Contracts.M23.ByteRegionEffect.of_storeByte hrun hin).2

private theorem evalList_two_first {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {v1 v2 : ValueHOL 64}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = some [v1, v2]) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 := by
  simp only [evalListHOLFinite, evalListHOLExact] at h
  rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | x1
  · simp [he1] at h
  · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | x2
    · simp [he1, he2] at h
    · simp [he1, he2] at h; rw [h.1]

private theorem wsSafe_call_assign_local {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm fname : MlS} {args : List (ExpHOL 64)}
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)) ∧
    (∀ x : MlS, x ≠ nm →
      (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).2.locals.lookup x =
        s.locals.lookup x) := by
  refine ⟨?_, ?_⟩
  · rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · dsimp only
        by_cases hz : s.clock = 0
        · rw [if_pos hz]
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        · rw [if_neg hz]
          have hc := hcal vals body callee rs hargs hl hz
          have he_ce : Wave8Contracts.M23.ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
            (Wave8Contracts.M23.ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
          rw [hrun] at hc
          cases rb with
          | none =>
            exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
          | some r0 =>
            cases r0 with
            | returned v =>
              have he_cp := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
              dsimp only
              split
              · split
                · exact ⟨fun _ => he_cp.with_locals_clock _ cpost.clock,
                    fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
                · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
              · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
            | exception eid ev =>
              exact ⟨fun h => by simp at h,
                fun hr => by
                  rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                  · simp at h
                  · injection h with h'; injection h' with h1 h2; subst h1 h2
                    exact (he_ce.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))).with_locals_clock _ cpost.clock⟩
            | timeOut | error | «break» | «continue» | finalFfi _ =>
              exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · intro x hne hn
    have hna : notAssignedLocal x (.call (some (some (.local, nm), none)) fname args) = true := by
      simp [notAssignedLocal, bne_iff_ne, Ne.symm hne]
    exact evaluate_notAssignedLocal _ hna s (by rw [hn]; rfl)

private theorem wsSafe_call_void_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hn : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) (x : MlS) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals.lookup x =
      s.locals.lookup x :=
  evaluate_notAssignedLocal (x := x) _ rfl s (by rw [hn]; rfl)

private theorem st_be32_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F} {p : BitVec 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hplt : p.toNat < heapEnd) :
    WsSafe s [(p.toNat, 4)]
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map]
  have hstep0 := wsSafe_storeByte (s := s) (Rl := [(p.toNat, 4)])
    (dst := .var .local (ofString "p"))
    (val := .shift .lsr (.var .local (ofString "v")) (.const 24#64))
    (fun addr ha _ => by
      rw [eval_local_word s "p" p hp] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact ⟨(p.toNat, 4), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
  refine WsSafe.seq hstep0.1 fun hn0 _ => ?_
  set s1 := (evaluateHOLFiniteState s _).2
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hstep0.2 hn0]; exact hp
  have hstep1 := wsSafe_storeByte (s := s1) (Rl := [(p.toNat, 4)])
    (dst := .op .add [.var .local (ofString "p"), .const 1#64])
    (val := .shift .lsr (.var .local (ofString "v")) (.const 16#64))
    (fun addr ha _ => by
      rw [eval_local_add_const s1 "p" p 1 hp1] at ha
      injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
      have hnat := bv_add_off_nat_gen p 1 hplt (by omega)
      exact ⟨(p.toNat, 4), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
  refine WsSafe.seq hstep1.1 fun hn1 _ => ?_
  set s2 := (evaluateHOLFiniteState s1 _).2
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hstep1.2 hn1]; exact hp1
  have hstep2 := wsSafe_storeByte (s := s2) (Rl := [(p.toNat, 4)])
    (dst := .op .add [.var .local (ofString "p"), .const 2#64])
    (val := .shift .lsr (.var .local (ofString "v")) (.const 8#64))
    (fun addr ha _ => by
      rw [eval_local_add_const s2 "p" p 2 hp2] at ha
      injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
      have hnat := bv_add_off_nat_gen p 2 hplt (by omega)
      exact ⟨(p.toNat, 4), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
  refine WsSafe.seq hstep2.1 fun hn2 _ => ?_
  set s3 := (evaluateHOLFiniteState s2 _).2
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hstep2.2 hn2]; exact hp2
  have hstep3 := wsSafe_storeByte (s := s3) (Rl := [(p.toNat, 4)])
    (dst := .op .add [.var .local (ofString "p"), .const 3#64])
    (val := .var .local (ofString "v"))
    (fun addr ha _ => by
      rw [eval_local_add_const s3 "p" p 3 hp3] at ha
      injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
      have hnat := bv_add_off_nat_gen p 3 hplt (by omega)
      exact ⟨(p.toNat, 4), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
  exact WsSafe.seq hstep3.1 fun _ _ => WsSafe.return_exp _ _ _

private theorem lookup_two_words_locals {fname : MlS} {p1 p2 : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hneq : p1 ≠ p2)
    (hlk : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      callee.lookup p1 = some (.val (.word w1)) ∧
      callee.lookup p2 = some (.val (.word w2)) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w1, rfl⟩ := eval_word_of_shape_one (Or.inl hshapes.2.2.1)
      obtain ⟨w2, rfl⟩ := eval_word_of_shape_one (Or.inl hshapes.2.2.2)
      refine ⟨hb, w1, w2, rfl, ?_, ?_⟩
      · simpa [FUPDATE_LIST, FUPDATE, hneq] using congrFun hfn p1
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn p2
    · simp at hraw
  · simp [List.length] at hraw

private theorem st_be64_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F} {p : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hplt : p.toNat + 8 ≤ heapEnd) :
    WsSafe s [(p.toNat, 8)]
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)) := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)
    refine WsSafe.decCall ?_ ?_
    · intro vals body callee rs _ hl _
      rw [hcode] at hl
      exact wsSafe_of_recRo hcode (installed_body_readOnly 23 (by rw [guestAst_len]; decide)
        Guest.Software.guestFn_bswap64 rfl recRoCallees (by decide) hl)
    · intro _ _ _ _ vw cpost _ _ _ _ heff_bs hsh_vw _
      obtain ⟨wv, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_vw)
      set m0 := setVarHOLFinite (ofString "w") (.val (.word wv)) { cpost with locals := s.locals }
      have hp_m0 : m0.locals.lookup (ofString "p") = some (.val (.word p)) := by
        simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "w" ≠ ofString "p" by decide, hp]
      have hw_m0 : m0.locals.lookup (ofString "w") = some (.val (.word wv)) := by
        simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      refine WsSafe.seq (WsSafe.store_word (heff_bs.memaddrs.trans hma)
        (fun v hv => by rw [eval_local_word m0 "w" wv hw_m0] at hv; injection hv with h'; exact ⟨wv, h'.symm⟩)
        (fun addr ha _ => by
          rw [eval_local_word m0 "p" p hp_m0] at ha
          injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
          exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩))
        (fun _ _ => WsSafe.return_exp _ _ _)
  · intro hn_ite heff_ite
    set s1 := (evaluateHOLFiniteState s (.ite _ _ _)).2
    have hna_p : notAssignedLocal (ofString "p")
        (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7#64]) (.const 0#64))
          (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
            (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) (.return (.const 0#64))))
          .skip) = true := by decide
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by
      have heq := evaluate_notAssignedLocal _ hna_p s (by rw [hn_ite]; rfl)
      exact heq.trans hp
    have hcall0 : WsSafe s1 [(p.toNat, 8)]
        (evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "st_be32")
          [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32#64)])) := by
      refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
      rw [heff_ite.code.trans hcode] at hl
      obtain ⟨rfl, w1, w2, rfl, hp_cal, _⟩ := lookup_two_words_locals (by decide) lookup_st_be32 hl
      have hw1 : w1 = p := by
        have h1 := evalList_two_first hargs
        rw [show @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.var .local (ofString "p")) = some (.val (.word p)) from hp1] at h1
        injection h1 with h'; injection h' with h''; injection h'' with h'''; exact h'''.symm
      subst hw1
      exact wsSafe_mono (st_be32_wsSafe_bound (heff_ite.memaddrs.trans hma) hp_cal (by omega))
        (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact ⟨(w1.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
    refine WsSafe.seq hcall0 fun hn_c0 heff_c0 => ?_
    set s2 := (evaluateHOLFiniteState s1 _).2
    have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by
      rw [wsSafe_call_void_locals hn_c0]; exact hp1
    have hcall1 : WsSafe s2 [(p.toNat, 8)]
        (evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "st_be32")
          [.op .add [.var .local (ofString "p"), .const 4#64], .var .local (ofString "v")])) := by
      refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
      rw [heff_c0.code.trans (heff_ite.code.trans hcode)] at hl
      obtain ⟨rfl, w1, w2, rfl, hp_cal, _⟩ := lookup_two_words_locals (by decide) lookup_st_be32 hl
      have hp2_add := eval_local_add_const s2 "p" p 4 hp2
      have hw1 : w1 = p + 4#64 := by
        have h1 := evalList_two_first hargs
        rw [hp2_add] at h1
        injection h1 with h'; injection h' with h''; injection h'' with h'''; exact h'''.symm
      subst hw1
      have hnat := bv_add_off_nat_gen p 4 (by omega) (by omega)
      exact wsSafe_mono (st_be32_wsSafe_bound (heff_c0.memaddrs.trans (heff_ite.memaddrs.trans hma)) hp_cal (by rw [hnat]; omega))
        (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact WsSafe.seq hcall1 fun _ _ => WsSafe.return_exp _ _ _

private theorem lookup_comb4_word_locals {aNm outNm : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hne : aNm ≠ outNm)
    (hlk : originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(aNm, .comb [.one, .one, .one, .one]), (outNm, .one)], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_to_be32") vals = some (body, callee, rs)) :
    body = body0 ∧
    ∃ va, ∃ w : BitVec 64, vals = [va, .val (.word w)] ∧
      callee.lookup outNm = some (.val (.word w)) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨v2, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w, rfl⟩ := eval_word_of_shape_one (Or.inl hshapes.2.2.2)
      refine ⟨hb, va, w, rfl, ?_⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn outNm
    · simp at hraw
  · simp [List.length] at hraw

private theorem call_assign_word_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm fname : MlS} {args : List (ExpHOL 64)} {w0 : BitVec 64}
    (hw0 : s.locals.lookup nm = some (.val (.word w0)))
    (hn : (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).1 = none) :
    ∃ w : BitVec 64,
      (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).2.locals.lookup nm =
        some (.val (.word w)) := by
  rcases hrun : evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args) with ⟨r, post⟩
  have hr : r = none := by rw [← hn, hrun]
  subst hr
  dsimp only
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hb] at hrun
        cases rb with
        | none => simp at hrun
        | some r0 =>
          cases r0 with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · split at hrun
              · rename_i hv
                injection hrun with _ hpost; subst hpost
                simp only [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact] at hv
                obtain ⟨w, rfl⟩ := eval_word_of_shape_one (Or.inr hv)
                exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              · simp at hrun
            · simp at hrun
          | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun

private theorem u256_to_be32_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F} {out : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hlt : out.toNat + 32 ≤ heapEnd) :
    WsSafe s [(out.toNat, 32)]
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be32)) := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be32 =
      FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_u256_to_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  have hcall_bs : ∀ (t : PanSemStateFiniteExact 64 F) (htc : t.code = originalRuntimeCode)
      {w0 : BitVec 64} (hw0 : t.locals.lookup (ofString "w") = some (.val (.word w0)))
      (arg : ExpHOL 64),
      WsSafe t [(out.toNat, 32)]
        (evaluateHOLFiniteState t (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [arg])) ∧
      ((evaluateHOLFiniteState t (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [arg])).1 = none →
        (evaluateHOLFiniteState t (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [arg])).2.locals.lookup (ofString "out") =
          t.locals.lookup (ofString "out") ∧
        ∃ w1 : BitVec 64,
          (evaluateHOLFiniteState t (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [arg])).2.locals.lookup (ofString "w") =
            some (.val (.word w1))) := by
    intro t htc w0 hw0 arg
    have h := wsSafe_call_assign_local (s := t) (Rl := [(out.toNat, 32)])
      (nm := ofString "w") (fname := ofString "bswap64") (args := [arg])
      fun vals body callee rs _ hl _ => by
        rw [htc] at hl
        exact wsSafe_of_recRo htc (recRoCallees_good (ofString "bswap64") (by decide) vals body callee rs hl)
    exact ⟨h.1, fun hn => ⟨h.2 (ofString "out") (by decide) hn, call_assign_word_post hw0 hn⟩⟩
  have hst_off : ∀ (t : PanSemStateFiniteExact 64 F) (htm : t.memaddrs = ordinaryDomain)
      {wv : BitVec 64} (hw : t.locals.lookup (ofString "w") = some (.val (.word wv)))
      (off : Nat) (hoff : off + 8 ≤ 32) (dstExp : ExpHOL 64)
      (hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dstExp =
        some (.val (.word (out + BitVec.ofNat 64 off)))),
      WsSafe t [(out.toNat, 32)] (evaluateHOLFiniteState t (.store dstExp (.var .local (ofString "w")))) ∧
      ((evaluateHOLFiniteState t (.store dstExp (.var .local (ofString "w")))).1 = none →
        (evaluateHOLFiniteState t (.store dstExp (.var .local (ofString "w")))).2.locals = t.locals) := by
    intro t htm wv hw off hoff dstExp hdst
    have hnat := bv_add_off_nat_gen out off (by omega) (by omega)
    exact wsSafe_store_multi (s := t) (Rl := [(out.toNat, 32)])
      (dst := dstExp) (val := .var .local (ofString "w")) 8 htm
      (fun v hv => by
        rw [eval_local_word t "w" wv hw] at hv
        injection hv with h'; subst h'
        simp [flattenHOL])
      (fun addr ha => by
        rw [hdst] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
        have hhe : heapEnd ≤ 2 ^ 64 - 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
        exact ⟨by omega, (out.toNat, 32), List.mem_singleton.2 rfl, by omega, by omega⟩)
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)) ?_
  · refine WsSafe.decCall
      (fun vals body callee rs _ hl _ => by
        rw [hcode] at hl
        exact wsSafe_of_recRo hcode (recRoCallees_good (ofString "bswap64") (by decide) vals body callee rs hl))
      fun _ _ _ _ v cpost _ _ _ _ heff_bs hsh _ => ?_
    obtain ⟨wv0, rfl⟩ := eval_word_of_shape_one (Or.inr hsh)
    set m0 := setVarHOLFinite (ofString "w") (.val (.word wv0)) { cpost with locals := s.locals }
    have ho_m0 : m0.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "out" by decide, hout]
    have hw_m0 : m0.locals.lookup (ofString "w") = some (.val (.word wv0)) := by
      simp [m0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hst0 := hst_off m0 (heff_bs.memaddrs.trans hma) hw_m0 0 (by omega) (.var .local (ofString "out"))
      (by simpa [BitVec.add_zero] using eval_local_word m0 "out" out ho_m0)
    refine WsSafe.seq hst0.1 fun hn_s0 heff_s0 => ?_
    set s1 := (evaluateHOLFiniteState m0 _).2
    have ho_s1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hst0.2 hn_s0]; exact ho_m0
    have hw_s1 : s1.locals.lookup (ofString "w") = some (.val (.word wv0)) := by rw [hst0.2 hn_s0]; exact hw_m0
    have hc_s1 : s1.code = originalRuntimeCode := heff_s0.code.trans (heff_bs.code.trans hcode)
    have hm_s1 : s1.memaddrs = ordinaryDomain := heff_s0.memaddrs.trans (heff_bs.memaddrs.trans hma)
    have hbs1 := hcall_bs s1 hc_s1 hw_s1 (.rfield 2 (.var .local (ofString "a")))
    refine WsSafe.seq hbs1.1 fun hn_b1 heff_b1 => ?_
    obtain ⟨ho_m1_eq, wv1, hw_m1⟩ := hbs1.2 hn_b1
    set m1 := (evaluateHOLFiniteState s1 _).2
    have ho_m1 : m1.locals.lookup (ofString "out") = some (.val (.word out)) := ho_m1_eq.trans ho_s1
    have hst1 := hst_off m1 (heff_b1.memaddrs.trans hm_s1) hw_m1 8 (by omega)
      (.op .add [.var .local (ofString "out"), .const 8#64])
      (eval_local_add_const m1 "out" out 8 ho_m1)
    refine WsSafe.seq hst1.1 fun hn_s1 heff_s1 => ?_
    set s2 := (evaluateHOLFiniteState m1 _).2
    have ho_s2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hst1.2 hn_s1]; exact ho_m1
    have hw_s2 : s2.locals.lookup (ofString "w") = some (.val (.word wv1)) := by rw [hst1.2 hn_s1]; exact hw_m1
    have hc_s2 : s2.code = originalRuntimeCode := heff_s1.code.trans (heff_b1.code.trans hc_s1)
    have hm_s2 : s2.memaddrs = ordinaryDomain := heff_s1.memaddrs.trans (heff_b1.memaddrs.trans hm_s1)
    have hbs2 := hcall_bs s2 hc_s2 hw_s2 (.rfield 1 (.var .local (ofString "a")))
    refine WsSafe.seq hbs2.1 fun hn_b2 heff_b2 => ?_
    obtain ⟨ho_m2_eq, wv2, hw_m2⟩ := hbs2.2 hn_b2
    set m2 := (evaluateHOLFiniteState s2 _).2
    have ho_m2 : m2.locals.lookup (ofString "out") = some (.val (.word out)) := ho_m2_eq.trans ho_s2
    have hst2 := hst_off m2 (heff_b2.memaddrs.trans hm_s2) hw_m2 16 (by omega)
      (.op .add [.var .local (ofString "out"), .const 16#64])
      (eval_local_add_const m2 "out" out 16 ho_m2)
    refine WsSafe.seq hst2.1 fun hn_s2 heff_s2 => ?_
    set s3 := (evaluateHOLFiniteState m2 _).2
    have ho_s3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hst2.2 hn_s2]; exact ho_m2
    have hw_s3 : s3.locals.lookup (ofString "w") = some (.val (.word wv2)) := by rw [hst2.2 hn_s2]; exact hw_m2
    have hc_s3 : s3.code = originalRuntimeCode := heff_s2.code.trans (heff_b2.code.trans hc_s2)
    have hm_s3 : s3.memaddrs = ordinaryDomain := heff_s2.memaddrs.trans (heff_b2.memaddrs.trans hm_s2)
    have hbs3 := hcall_bs s3 hc_s3 hw_s3 (.rfield 0 (.var .local (ofString "a")))
    refine WsSafe.seq hbs3.1 fun hn_b3 heff_b3 => ?_
    obtain ⟨ho_m3_eq, wv3, hw_m3⟩ := hbs3.2 hn_b3
    set m3 := (evaluateHOLFiniteState s3 _).2
    have ho_m3 : m3.locals.lookup (ofString "out") = some (.val (.word out)) := ho_m3_eq.trans ho_s3
    have hst3 := hst_off m3 (heff_b3.memaddrs.trans hm_s3) hw_m3 24 (by omega)
      (.op .add [.var .local (ofString "out"), .const 24#64])
      (eval_local_add_const m3 "out" out 24 ho_m3)
    exact WsSafe.seq hst3.1 fun _ _ => WsSafe.return_exp _ _ _
  · intro hn_ite heff_ite
    set u0 := (evaluateHOLFiniteState s (.ite _ _ _)).2
    have ho_u0 : u0.locals.lookup (ofString "out") = some (.val (.word out)) := by
      exact (evaluate_notAssignedLocal (x := ofString "out") _ (by decide) s (by rw [hn_ite]; rfl)).trans hout
    have hc_u0 : u0.code = originalRuntimeCode := heff_ite.code.trans hcode
    have hm_u0 : u0.memaddrs = ordinaryDomain := heff_ite.memaddrs.trans hma
    have hbe64_step : ∀ (t : PanSemStateFiniteExact 64 F) (htc : t.code = originalRuntimeCode)
        (htm : t.memaddrs = ordinaryDomain)
        (hto : t.locals.lookup (ofString "out") = some (.val (.word out)))
        (off : Nat) (hoff : off + 8 ≤ 32) (pExp vExp : ExpHOL 64)
        (hpExp : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) pExp =
          some (.val (.word (out + BitVec.ofNat 64 off)))),
        WsSafe t [(out.toNat, 32)]
          (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])) ∧
        ((evaluateHOLFiniteState t (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 = none →
          (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2.locals.lookup (ofString "out") =
            some (.val (.word out))) := by
      intro t htc htm hto off hoff pExp vExp hpExp
      refine ⟨WsSafe.call_void fun vals body callee rs hargs hl _ => ?_, fun hn => ?_⟩
      · rw [htc] at hl
        obtain ⟨rfl, w1, w2, rfl, hp_cal, _⟩ := lookup_two_words_locals (by decide) lookup_st_be64 hl
        have h1 := evalList_two_first hargs
        rw [hpExp] at h1
        have hw1 : w1 = out + BitVec.ofNat 64 off := by
          injection h1 with h'; injection h' with h''; injection h'' with h'''; exact h'''.symm
        subst hw1
        have hnat := bv_add_off_nat_gen out off (by omega) (by omega)
        exact wsSafe_mono (st_be64_wsSafe_bound htc htm hp_cal (by rw [hnat]; omega))
          (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact ⟨(out.toNat, 32), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
      · rw [wsSafe_call_void_locals hn]; exact hto
    have hc0 := hbe64_step u0 hc_u0 hm_u0 ho_u0 0 (by omega)
      (.var .local (ofString "out")) (.rfield 3 (.var .local (ofString "a")))
      (by simpa [BitVec.add_zero] using eval_local_word u0 "out" out ho_u0)
    refine WsSafe.seq hc0.1 fun hn0 heff0 => ?_
    set u1 := (evaluateHOLFiniteState u0 _).2
    have hc1 := hbe64_step u1 (heff0.code.trans hc_u0) (heff0.memaddrs.trans hm_u0) (hc0.2 hn0) 8 (by omega)
      (.op .add [.var .local (ofString "out"), .const 8#64]) (.rfield 2 (.var .local (ofString "a")))
      (eval_local_add_const u1 "out" out 8 (hc0.2 hn0))
    refine WsSafe.seq hc1.1 fun hn1 heff1 => ?_
    set u2 := (evaluateHOLFiniteState u1 _).2
    have hc2 := hbe64_step u2 (heff1.code.trans (heff0.code.trans hc_u0)) (heff1.memaddrs.trans (heff0.memaddrs.trans hm_u0)) (hc1.2 hn1) 16 (by omega)
      (.op .add [.var .local (ofString "out"), .const 16#64]) (.rfield 1 (.var .local (ofString "a")))
      (eval_local_add_const u2 "out" out 16 (hc1.2 hn1))
    refine WsSafe.seq hc2.1 fun hn2 heff2 => ?_
    set u3 := (evaluateHOLFiniteState u2 _).2
    have hc3 := hbe64_step u3 (heff2.code.trans (heff1.code.trans (heff0.code.trans hc_u0)))
      (heff2.memaddrs.trans (heff1.memaddrs.trans (heff0.memaddrs.trans hm_u0))) (hc2.2 hn2) 24 (by omega)
      (.op .add [.var .local (ofString "out"), .const 24#64]) (.rfield 0 (.var .local (ofString "a")))
      (eval_local_add_const u3 "out" out 24 (hc2.2 hn2))
    exact WsSafe.seq hc3.1 fun _ _ => WsSafe.return_exp _ _ _

/-! ## Section 7: `u256_mulmod`, `fn_mul`, and Elliptic Curve Operations -/

private theorem shapeEqHOL_symm' {a b : ShapeHOL} (h : shapeEqHOL a b = true) :
    shapeEqHOL b a = true :=
  (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp h).symm

private theorem evalList_two_eq' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = some vals) :
    ∃ v1 v2,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some v2 ∧
      vals = [v1, v2] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  refine ⟨v1, v2, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2] using h.symm

private theorem evalList_three_eq' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some v2 ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some v3 ∧
      vals = [v1, v2, v3] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

private theorem eval_u256_ws_plus' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {off : Nat} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "u256_ws"), .const (BitVec.ofNat 64 off)]) = some v) :
    v = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off)) := by
  simp only [evalHOLExact, evalListHOLExact, wordOpHOL] at hev
  rcases hgl : s.globals.lookup (ofString "u256_ws") with _ | gv
  · simp [hgl] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _ <;> simp [hgl, valueIsWord, valueWord, wordOp] at hev
    have hgw := eval_global_word_eq_ofNat he.globals hgl
    rw [hgw] at hev
    simpa [BitVec.add_zero] using hev.symm

private theorem eval_or4_ne_zero' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {b0 b1 b2 b3 : BitVec 64}
    (hb : s.locals.lookup nm =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (hcmp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 0#64))) :
    (b0 ||| b1 ||| b2 ||| b3) ≠ 0 := by
  intro hz
  have h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 1#64)) := by
    simp only [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    have hz' : OrOp.or b0 (OrOp.or b1 (OrOp.or b2 (OrOp.or b3 0))) = 0#64 := by
      change (b0 ||| (b1 ||| (b2 ||| (b3 ||| 0#64)))) = 0#64
      simpa [BitVec.or_zero, BitVec.or_assoc] using hz
    rw [hz']
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [h1] at hcmp
  simp at hcmp

private theorem ite_return_skip_none' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond retExp : ExpHOL 64}
    (hn : (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).1 = none) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word 0#64)) ∧
    (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          exact ⟨rfl, by simp [evaluateHOLFiniteState_skip]⟩
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_return] at hn
          exfalso; revert hn
          split; · simp
          split <;> simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem ite_tail_skip_none' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {fname : MlS} {args : List (ExpHOL 64)}
    (hn : (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).1 = none) :
    (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          simp [evaluateHOLFiniteState_skip]
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_call] at hn
          exfalso; revert hn
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, cal, rs⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, cp⟩
                cases rb with
                | none => simp
                | some r0 =>
                  cases r0 with
                  | returned _ => dsimp only; split <;> simp
                  | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem lookup_u256_mod' :
    originalRuntimeCode.lookup (ofString "u256_mod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 71 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mod) rfl

private theorem lookup_u256_mulmod' :
    originalRuntimeCode.lookup (ofString "u256_mulmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mulmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 76 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mulmod) rfl

private theorem lookup_two_comb4_locals' {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ a0 a1 a2 a3, callee.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) ∧
    (∃ b0 b1 b2 b3, callee.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.1)
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2)
      refine ⟨hb, ⟨a0, a1, a2, a3, ?_⟩, ⟨b0, b1, b2, b3, ?_⟩⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "a" ≠ ofString "b" by decide] using congrFun hfn (ofString "a")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "b")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_three_comb4_locals' {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ m0 m1 m2 m3, callee.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | ⟨vm, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨m0, m1, m2, m3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2.2)
      refine ⟨hb, ⟨m0, m1, m2, m3, ?_⟩⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "m")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_u256_to_digits_locals'
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "u256_to_digits") vals = some (body, callee, rs)) :
    ∃ vp va, vals = [vp, va] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_digits).body ∧
      callee.lookup (ofString "p") = some vp ∧
      callee.lookup (ofString "a") = some va ∧
      shapeEqHOL (shapeOfHOLExact vp) .one = true ∧
      shapeEqHOL (shapeOfHOLExact va) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_u256_to_digits, List.length] at hraw
  rcases vals with _ | ⟨vp, _ | ⟨va, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vp, va, rfl, hb,
        by simpa [FUPDATE_LIST, FUPDATE, show ofString "p" ≠ ofString "a" by decide] using congrFun hfn (ofString "p"),
        by simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "a"),
        shapeEqHOL_symm' hshapes.2.2.1, shapeEqHOL_symm' hshapes.2.2.2⟩
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_digits_divmod_locals'
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") vals = some (body, callee, rs)) :
    ∃ vu vm vd, vals = [vu, vm, vd] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_digits_divmod).body ∧
      callee.lookup (ofString "u") = some vu ∧
      callee.lookup (ofString "m") = some vm ∧
      callee.lookup (ofString "d") = some vd ∧
      shapeEqHOL (shapeOfHOLExact vu) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vm) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vd) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod, List.length] at hraw
  rcases vals with _ | ⟨vu, _ | ⟨vm, _ | ⟨vd, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vu, vm, vd, rfl, hb,
        by simpa [FUPDATE_LIST, FUPDATE, show ofString "u" ≠ ofString "d" by decide,
          show ofString "u" ≠ ofString "m" by decide] using congrFun hfn (ofString "u"),
        by simpa [FUPDATE_LIST, FUPDATE, show ofString "m" ≠ ofString "d" by decide] using congrFun hfn (ofString "m"),
        by simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "d"),
        shapeEqHOL_symm' hshapes.2.2.1, shapeEqHOL_symm' hshapes.2.2.2.1, shapeEqHOL_symm' hshapes.2.2.2.2⟩
    · simp at hraw
  · simp [List.length] at hraw

private theorem call_u256_mod_wsSafe' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_mod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, _⟩ := lookup_two_comb4_locals' lookup_u256_mod' hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    have he_c : WsEnv s0 (callEntryStateHOLFinite s callee) := he.with_locals_clock callee _
    rw [he_c.code] at hl'
    obtain ⟨rfl, _, ⟨b0, b1, b2, b3, hb_c⟩⟩ := lookup_two_comb4_locals' lookup_u256_divmod hl'
    exact u256_divmod_wsSafe (he_c.with_locals_clock callee' _) hb_c
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem call_void_u256_to_digits_wsSafe' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {pExp aExp : ExpHOL 64} {off : Nat}
    (hoff : off + 64 ≤ 640)
    (hp : ∀ vp, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp = some vp →
      vp = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).2.locals = s.locals) := by
  refine ⟨WsSafe.call_void ?_, ?_⟩
  · intro vals body callee rs hargs hl _
    obtain ⟨v1, v2, hv1, _, rfl⟩ := evalList_two_eq' hargs
    have hv1_eq := hp v1 hv1; subst hv1_eq
    rw [he.code] at hl
    obtain ⟨_, _, hinj_v, rfl, hp_cal, ha_cal, _, hsh_a⟩ := lookup_u256_to_digits_locals' hl
    simp only [List.cons.injEq] at hinj_v
    obtain ⟨rfl, rfl, _⟩ := hinj_v
    obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inr hsh_a)
    exact (u256_to_digits_wsSafe_and_post (he.with_locals_clock callee _) hoff hp_cal ha_cal).1
  · rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, aExp] with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup (ofString "u256_to_digits") vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
          cases rb with
          | none => simp
          | some r0 =>
            cases r0 with
            | returned _ => dsimp only; split <;> simp
            | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp

private theorem call_tail_digits_divmod_wsSafe' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {uExp dExp : ExpHOL 64} {mv : Nat} {d0 d1 d2 d3 : BitVec 64}
    (hm_le : mv ≤ 16)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dExp =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)]))
    (hd_nz : (d0 ||| d1 ||| d2 ||| d3) ≠ 0) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (.call none (ofString "digits_divmod") [uExp, .const (BitVec.ofNat 64 mv), dExp])) := by
  refine WsSafe.call_tail ?_
  intro vals body callee rs hargs hl _
  obtain ⟨v1, v2, v3, _, hv2, hv3, rfl⟩ := evalList_three_eq' hargs
  have hv2_eq : v2 = .val (.word (BitVec.ofNat 64 mv)) := by simpa [evalHOLExact] using hv2.symm
  have hv3_eq : v3 = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)] := by
    rw [hd] at hv3; exact Option.some.inj hv3.symm
  subst hv2_eq hv3_eq
  rw [he.code] at hl
  obtain ⟨_, _, _, hinj3, rfl, hu_c, hm_c, hd_c, hsh_u, _, _⟩ := lookup_digits_divmod_locals' hl
  simp only [List.cons.injEq] at hinj3
  obtain ⟨rfl, rfl, rfl, _⟩ := hinj3
  obtain ⟨uw, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_u)
  exact digits_divmod_wsSafe (he.with_locals_clock callee _) hu_c hm_c hd_c hm_le hd_nz

private theorem u256_mulmod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {m0 m1 m2 m3 : BitVec 64}
    (hm : s.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)])) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_mulmod)) := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_mulmod =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_mulmod).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_u256_mulmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_m0 _
  obtain ⟨hcmp_m0, hs_m0⟩ := ite_return_skip_none' hn_m0
  have hm_nz : (m0 ||| m1 ||| m2 ||| m3) ≠ 0 := eval_or4_ne_zero' hm hcmp_m0
  rw [hs_m0]
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus' he hvu]
  set s1 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) s
  have hs1_env : WsEnv s0 s1 := he.with_locals_clock _ _
  have hu_s1 : s1.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s1, setVarHOLFinite, FUPDATE]
  have hm_s1 : s1.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    simp [s1, setVarHOLFinite, FUPDATE, show ofString "u" ≠ ofString "m" by decide, hm]
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)
    refine WsSafe.decCall_ro hs1_env (by decide) fun vp cpost_p hs2_env _ _ => ?_
    set s2 := setVarHOLFinite (ofString "p") vp { cpost_p with locals := s1.locals }
    refine WsSafe.seq
      (WsSafe.ite
        (fun _ _ _ => WsSafe.call_tail fun _ _ _ _ _ hl _ => call_u256_mod_wsSafe' hs2_env hl)
        (fun _ => WsSafe.skip _ _)) ?_
    intro hn_p1 _
    rw [ite_tail_skip_none' hn_p1]
    have hu_s2 : s2.locals.lookup (ofString "u") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) := by
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "u" by decide, hu_s1]
    have htd_p := call_void_u256_to_digits_wsSafe' hs2_env
      (pExp := .var .local (ofString "u"))
      (aExp := .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64])
      (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s2] using hv.symm)
    refine WsSafe.seq htd_p.1 fun hn_tdp heff_tdp => ?_
    set s3 := (evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "u256_to_digits")
        [.var .local (ofString "u"),
         .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])).2
    have hs3_env : WsEnv s0 s3 := hs2_env.step heff_tdp
    have hm_s3 : s3.locals.lookup (ofString "m") =
        some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
      rw [htd_p.2 hn_tdp]
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "m" by decide, hm_s1]
    exact call_tail_digits_divmod_wsSafe' hs3_env (by omega)
      (by simp only [evalHOLExact]; exact hm_s3) hm_nz
  intro hn_fast _
  have hs_fast := by
    let p_fast : ProgHOL 64 :=
      .ite (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                                  .rfield 2 (.var .local (ofString "a")),
                                  .rfield 3 (.var .local (ofString "a")),
                                  .rfield 1 (.var .local (ofString "b")),
                                  .rfield 2 (.var .local (ofString "b")),
                                  .rfield 3 (.var .local (ofString "b"))]) (.const 0#64))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.seq
            (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "p"))) (.const 0#64))
              (.call none (ofString "u256_mod")
                [.rstruct [.rfield 0 (.var .local (ofString "p")), .const 0#64, .const 0#64, .const 0#64],
                 .var .local (ofString "m")])
              .skip)
            (.seq
              (.call (some (none, none)) (ofString "u256_to_digits")
                [.var .local (ofString "u"),
                 .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])
              (.call none (ofString "digits_divmod")
                [.var .local (ofString "u"), .const 4#64, .var .local (ofString "m")]))))
        .skip
    show (evaluateHOLFiniteState s1 p_fast).2 = s1
    change (evaluateHOLFiniteState s1 p_fast).1 = none at hn_fast
    dsimp only [p_fast] at hn_fast ⊢
    rw [evaluateHOLFiniteState_ite] at hn_fast ⊢
    rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                             .rfield 2 (.var .local (ofString "a")),
                             .rfield 3 (.var .local (ofString "a")),
                             .rfield 1 (.var .local (ofString "b")),
                             .rfield 2 (.var .local (ofString "b")),
                             .rfield 3 (.var .local (ofString "b"))]) (.const 0#64)) with _ | v
    · simp [hcond] at hn_fast
    · cases v with
      | val hl =>
        cases hl with
        | word w =>
          simp only [hcond] at hn_fast ⊢
          by_cases hw0 : w = 0
          · subst hw0; simp [evaluateHOLFiniteState_skip]
          · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_decCall_fixClockRewrite] at hn_fast
            exfalso; revert hn_fast
            rcases evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vals
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64") vals with _ | ⟨bd, cal, rs⟩
              · simp
              · dsimp only; split
                · simp
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal) bd with ⟨rb, cp⟩
                  cases rb with
                  | none => simp
                  | some r0 =>
                    cases r0 with
                    | returned rv =>
                      dsimp only; split
                      · rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState _ (.ite _ _ _) with ⟨ri, si⟩
                        cases ri; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState si (.call (some (none, none)) _ _) with ⟨rc1, sc1⟩
                        cases rc1; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_call]
                        rcases evalListHOLFinite sc1 (h := fun a => Classical.propDecidable (sc1.memaddrs a)) _ with _ | vals2
                        · simp
                        · dsimp only
                          rcases lookupCodeHOLFinite sc1.code.lookup (ofString "digits_divmod") vals2 with _ | ⟨bd2, cal2, rs2⟩
                          · simp
                          · dsimp only; split
                            · simp
                            · rcases evaluateHOLFiniteState (callEntryStateHOLFinite sc1 cal2) bd2 with ⟨rb2, cp2⟩
                              cases rb2 with
                              | none => simp
                              | some r2 =>
                                cases r2 with
                                | returned _ => dsimp only; split <;> simp
                                | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
                      · simp
                    | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
      | rStruct _ => simp [hcond] at hn_fast
      | nStruct _ _ => simp [hcond] at hn_fast
  rw [hs_fast]
  refine WsSafe.decCall_ro hs1_env (by decide) fun vf cpost_f hs4_env _ _ => ?_
  set s4 := setVarHOLFinite (ofString "f") vf { cpost_f with locals := s1.locals }
  have hu_s4 : s4.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "u" by decide, hu_s1]
  have htd_lo := call_void_u256_to_digits_wsSafe' hs4_env
    (pExp := .var .local (ofString "u"))
    (aExp := .rstruct [.rfield 0 (.var .local (ofString "f")), .rfield 1 (.var .local (ofString "f")),
                       .rfield 2 (.var .local (ofString "f")), .rfield 3 (.var .local (ofString "f"))])
    (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s4] using hv.symm)
  refine WsSafe.seq htd_lo.1 fun hn_lo heff_lo => ?_
  set s5 := (evaluateHOLFiniteState s4 _).2
  have hs5_env : WsEnv s0 s5 := hs4_env.step heff_lo
  have hs5_loc : s5.locals = s4.locals := htd_lo.2 hn_lo
  have hu_s5 : s5.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs5_loc]; exact hu_s4
  have htd_hi := call_void_u256_to_digits_wsSafe' hs5_env
    (pExp := .op .add [.var .local (ofString "u"), .const 64#64])
    (aExp := .rstruct [.rfield 4 (.var .local (ofString "f")), .rfield 5 (.var .local (ofString "f")),
                       .rfield 6 (.var .local (ofString "f")), .rfield 7 (.var .local (ofString "f"))])
    (off := 488) (by omega)
    (fun v hv => by
      simp only [evalHOLExact, evalListHOLExact, hu_s5, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr] at hv
      injection hv with hv'
      rw [← hv']; congr 2
      rw [show (64#64 + 0 : BitVec 64) = 64#64 from BitVec.add_zero _, BitVec.add_assoc]
      congr 1)
  refine WsSafe.seq htd_hi.1 fun hn_hi heff_hi => ?_
  set s6 := (evaluateHOLFiniteState s5 _).2
  have hs6_env : WsEnv s0 s6 := hs5_env.step heff_hi
  have hm_s6 : s6.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    rw [htd_hi.2 hn_hi, hs5_loc]
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "m" by decide, hm_s1]
  exact call_tail_digits_divmod_wsSafe' hs6_env (by omega)
    (by simp only [evalHOLExact]; exact hm_s6) hm_nz

private theorem untypedGlobalBufIvls_subset_rec {F : Type} (s : PanSemStateFiniteExact 64 F)
    {Rl : List Ivl}
    {iv : Ivl} (hiv : iv ∈ untypedGlobalBufIvls s) :
    iv ∈ Rl ++ [("u256_ws", 640), ("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)].map (bufferRegion s) := by
  exact List.mem_append_right _ hiv

private theorem fn_mul_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_fn_mul)) := by
  have hb : sourceFnBody Guest.Software.guestFn_fn_mul =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_fn_mul).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_fn_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map]
  refine WsSafe.call_tail fun vals body callee rs _ hl _ => ?_
  rw [he.code] at hl
  obtain ⟨rfl, m0, m1, m2, m3, hm_c⟩ := lookup_three_comb4_locals' lookup_u256_mulmod' hl
  exact u256_mulmod_wsSafe (he.with_locals_clock callee _) hm_c

/-! ## Section 8: Elliptic Curve Operations & `secp256k1_recover` -/

private def comb4Val {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) : Prop :=
  ∃ w0 w1 w2 w3 : BitVec 64,
    s.locals.lookup nm = some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)])

private def comb5Val {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) : Prop :=
  ∃ w0 w1 w2 w3 w4 : BitVec 64,
    s.locals.lookup nm = some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)])

private def isComb4Shape : ShapeHOL → Bool
  | .comb [.one, .one, .one, .one] => true
  | _ => false

private def isComb5Shape : ShapeHOL → Bool
  | .comb [.one, .one, .one, .one, .one] => true
  | _ => false

private def isLocalVarEq (ptVar : MlS) : ExpHOL 64 → Bool
  | .var .local nm => nm == ptVar
  | _ => false

private def isPtStoreTarget (ptVar : MlS) : ExpHOL 64 → Bool
  | .var .local nm => nm == ptVar
  | .op .add [.var .local nm, .const off] => nm == ptVar && (off == 32#64 || off == 64#64)
  | _ => false

private def isComb4StoreVal (c4vars c5vars : List MlS) : ExpHOL 64 → Bool
  | .var .local nm => c4vars.contains nm
  | .load sh _ => isComb4Shape sh
  | .rstruct [.const _, .const _, .const _, .const _] => true
  | .rstruct [.rfield 0 (.var .local nm0), .rfield 1 (.var .local nm1),
              .rfield 2 (.var .local nm2), .rfield 3 (.var .local nm3)] =>
      c5vars.contains nm0 && c5vars.contains nm1 && c5vars.contains nm2 && c5vars.contains nm3
  | _ => false

private def ecPtProg (cal1 cal2 : MlS → Bool) (ptVar : MlS) (c4vars c5vars : List MlS) : ProgHOL 64 → Bool
  | .skip | .raise _ _ | .return _ => true
  | .assign .local nm e =>
      if c4vars.contains nm then !(nm == ptVar) && !(c5vars.contains nm) && isComb4StoreVal c4vars c5vars e
      else !(nm == ptVar) && !(c5vars.contains nm)
  | .dec nm sh init body =>
      !(nm == ptVar) &&
      (if isComb4Shape sh && isComb4StoreVal c4vars c5vars init then
         !(c5vars.contains nm) && ecPtProg cal1 cal2 ptVar (nm :: c4vars) c5vars body
       else !(c4vars.contains nm) && !(c5vars.contains nm) && ecPtProg cal1 cal2 ptVar c4vars c5vars body)
  | .decCall nm sh fname _ cont =>
      recRoCallees fname && !(nm == ptVar) &&
      (if isComb4Shape sh then !(c5vars.contains nm) && ecPtProg cal1 cal2 ptVar (nm :: c4vars) c5vars cont
       else if isComb5Shape sh then !(c4vars.contains nm) && ecPtProg cal1 cal2 ptVar c4vars (nm :: c5vars) cont
       else !(c4vars.contains nm) && !(c5vars.contains nm) && ecPtProg cal1 cal2 ptVar c4vars c5vars cont)
  | .call (some (some (.local, nm), none)) fname _ =>
      recRoCallees fname && !(nm == ptVar) && !(c5vars.contains nm)
  | .call (some (none, none)) fname args =>
      (fname == ofString "trap_with") || recRoCallees fname ||
      (cal1 fname &&
       match args with | [e] => isLocalVarEq ptVar e | _ => false) ||
      (cal2 fname &&
       match args with
       | [e, ax, ay] => isLocalVarEq ptVar e && isComb4StoreVal c4vars c5vars ax && isComb4StoreVal c4vars c5vars ay
       | _ => false)
  | .call none fname _ => recRoCallees fname
  | .store dst val => isPtStoreTarget ptVar dst && isComb4StoreVal c4vars c5vars val
  | .ite _ a b => ecPtProg cal1 cal2 ptVar c4vars c5vars a && ecPtProg cal1 cal2 ptVar c4vars c5vars b
  | .seq a b => ecPtProg cal1 cal2 ptVar c4vars c5vars a && ecPtProg cal1 cal2 ptVar c4vars c5vars b
  | .while _ body => ecPtProg cal1 cal2 ptVar c4vars c5vars body
  | _ => false

private def ecCal1Base (f : MlS) : Bool := f == ofString "ec_set_infinity"
private def ecCal1Full (f : MlS) : Bool :=
  f == ofString "ec_set_infinity" || f == ofString "ec_double" || f == ofString "ec_to_affine"
private def ecCal2Base (f : MlS) : Bool := f == ofString "ec_set_affine"
private def ecCal2Full (f : MlS) : Bool :=
  f == ofString "ec_set_affine" || f == ofString "ec_add_affine"

private theorem ecPtProg_ec_set_infinity :
    ecPtProg ecCal1Base ecCal2Base (ofString "pt") [] []
      (sourceFnBody Guest.Software.guestFn_ec_set_infinity) = true := by
  decide

private theorem ecPtProg_ec_set_affine :
    ecPtProg ecCal1Base ecCal2Base (ofString "pt") [ofString "x", ofString "y"] []
      (sourceFnBody Guest.Software.guestFn_ec_set_affine) = true := by
  decide

private theorem ecPtProg_ec_double :
    ecPtProg ecCal1Base ecCal2Base (ofString "pt") [] []
      (sourceFnBody Guest.Software.guestFn_ec_double) = true := by
  decide

private theorem ecPtProg_ec_add_affine :
    ecPtProg ecCal1Full ecCal2Base (ofString "pt") [ofString "ax", ofString "ay"] []
      (sourceFnBody Guest.Software.guestFn_ec_add_affine) = true := by
  decide

private theorem ecPtProg_ec_to_affine :
    ecPtProg ecCal1Base ecCal2Base (ofString "pt") [] []
      (sourceFnBody Guest.Software.guestFn_ec_to_affine) = true := by
  decide

private theorem ecPtProg_secp256k1_decompress_r :
    ecPtProg ecCal1Base ecCal2Base (ofString "out") [ofString "r"] []
      (sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r) = true := by
  decide

private def ecMul2TailLoopOk : ProgHOL 64 → Bool
  | .while _ lbody =>
      ecPtProg ecCal1Full ecCal2Full (ofString "out")
        [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [] lbody
  | .seq (.while _ lbody) _ =>
      ecPtProg ecCal1Full ecCal2Full (ofString "out")
        [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [] lbody
  | .seq _ b => ecMul2TailLoopOk b
  | .dec _ _ _ b => ecMul2TailLoopOk b
  | .decCall _ _ _ _ b => ecMul2TailLoopOk b
  | _ => false

private theorem ecMul2TailLoopOk_true :
    ecMul2TailLoopOk (sourceFnBody Guest.Software.guestFn_ec_mul2) = true := by
  decide

private theorem isComb4Val_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c4vars c5vars : List MlS} {e : ExpHOL 64} {v : ValueHOL 64}
    (hc4 : ∀ x ∈ c4vars, comb4Val s x)
    (hc5 : ∀ x ∈ c5vars, comb5Val s x)
    (he : isComb4StoreVal c4vars c5vars e = true)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  cases e with
  | var k nm =>
    cases k with
    | global => simp [isComb4StoreVal] at he
    | «local» =>
      simp only [isComb4StoreVal, List.contains_iff_mem] at he
      obtain ⟨w0, w1, w2, w3, hloc⟩ := hc4 nm he
      simp only [evalHOLExact, hloc, Option.some.injEq] at hv
      exact ⟨w0, w1, w2, w3, hv.symm⟩
  | load sh addr =>
    simp only [isComb4StoreVal] at he
    cases sh with
    | one => simp [isComb4Shape] at he
    | named _ => simp [isComb4Shape] at he
    | comb shs =>
      rcases shs with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | _⟩⟩⟩⟩ <;> try simp [isComb4Shape] at he
      cases s0 <;> try simp [isComb4Shape] at he
      cases s1 <;> try simp [isComb4Shape] at he
      cases s2 <;> try simp [isComb4Shape] at he
      cases s3 <;> try simp [isComb4Shape] at he
      simp only [evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL, Bool.and_self, ↓reduceIte] at hv
      split at hv
      · rename_i a _
        unfold memLoadHOLExact at hv
        let dec := fun x : BitVec 64 => Classical.propDecidable (s.memaddrs x)
        rcases hm0 : @memLoadsHOLExact 64 _ [.one, .one, .one, .one] a s.memaddrs dec s.memory s.structs with _ | vs0
        · rw [hm0] at hv; simp at hv
        · rw [hm0] at hv; simp only [Option.some.injEq] at hv; subst hv
          have hone : ∀ {x : BitVec 64} {vx : ValueHOL 64},
              @memLoadHOLExact 64 _ .one x s.memaddrs dec s.memory s.structs = some vx →
              ∃ wx : BitVec 64, vx = .val (.word wx) := by
            intro x vx hl
            simp only [memLoadHOLExact, panMemLoadHOL] at hl
            split at hl
            · cases hcell : s.memory x with
              | word wx => rw [hcell] at hl; injection hl with hl'; exact ⟨wx, hl'.symm⟩
            · simp at hl
          unfold memLoadsHOLExact at hm0
          rcases hl1 : @memLoadHOLExact 64 _ .one a s.memaddrs dec s.memory s.structs with _ | v1
          · rw [hl1] at hm0; simp at hm0
          · rw [hl1] at hm0
            rcases hm1 : @memLoadsHOLExact 64 _ [.one, .one, .one] _ s.memaddrs dec s.memory s.structs with _ | vs1
            · rw [hm1] at hm0; simp at hm0
            · rw [hm1] at hm0; simp only [Option.some.injEq] at hm0; subst hm0
              unfold memLoadsHOLExact at hm1
              rcases hl2 : @memLoadHOLExact 64 _ .one _ s.memaddrs dec s.memory s.structs with _ | v2
              · rw [hl2] at hm1; simp at hm1
              · rw [hl2] at hm1
                rcases hm2 : @memLoadsHOLExact 64 _ [.one, .one] _ s.memaddrs dec s.memory s.structs with _ | vs2
                · rw [hm2] at hm1; simp at hm1
                · rw [hm2] at hm1; simp only [Option.some.injEq] at hm1; subst hm1
                  unfold memLoadsHOLExact at hm2
                  rcases hl3 : @memLoadHOLExact 64 _ .one _ s.memaddrs dec s.memory s.structs with _ | v3
                  · rw [hl3] at hm2; simp at hm2
                  · rw [hl3] at hm2
                    rcases hm3 : @memLoadsHOLExact 64 _ [.one] _ s.memaddrs dec s.memory s.structs with _ | vs3
                    · rw [hm3] at hm2; simp at hm2
                    · rw [hm3] at hm2; simp only [Option.some.injEq] at hm2; subst hm2
                      unfold memLoadsHOLExact at hm3
                      rcases hl4 : @memLoadHOLExact 64 _ .one _ s.memaddrs dec s.memory s.structs with _ | v4
                      · rw [hl4] at hm3; simp at hm3
                      · rw [hl4] at hm3
                        rcases hm4 : @memLoadsHOLExact 64 _ [] _ s.memaddrs dec s.memory s.structs with _ | vs4
                        · rw [hm4] at hm3; simp at hm3
                        · rw [hm4] at hm3; simp only [Option.some.injEq] at hm3; subst hm3
                          unfold memLoadsHOLExact at hm4; simp only [Option.some.injEq] at hm4; subst hm4
                          obtain ⟨w1, rfl⟩ := hone hl1
                          obtain ⟨w2, rfl⟩ := hone hl2
                          obtain ⟨w3, rfl⟩ := hone hl3
                          obtain ⟨w4, rfl⟩ := hone hl4
                          exact ⟨w1, w2, w3, w4, rfl⟩
      · simp at hv
  | rstruct es =>
    rcases es with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩⟩ <;> try simp [isComb4StoreVal] at he
    cases e0 with
    | const c0 =>
      cases e1 with
      | const c1 =>
        cases e2 with
        | const c2 =>
          cases e3 with
          | const c3 =>
            simp only [evalHOLExact, evalListHOLExact, Option.map, Option.some.injEq] at hv
            exact ⟨c0, c1, c2, c3, hv.symm⟩
          | _ => simp [isComb4StoreVal] at he
        | _ => simp [isComb4StoreVal] at he
      | _ => simp [isComb4StoreVal] at he
    | rfield i0 sub0 =>
      cases i0 with
      | zero =>
        cases sub0 with
        | var k0 nm0 =>
          cases k0 with
          | global => simp [isComb4StoreVal] at he
          | «local» =>
            cases e1 with
            | rfield i1 sub1 =>
              rcases i1 with _ | i1'
              · simp [isComb4StoreVal] at he
              · rcases i1' with _ | _
                · cases sub1 with
                  | var k1 nm1 =>
                    cases k1 with
                    | global => simp [isComb4StoreVal] at he
                    | «local» =>
                      cases e2 with
                      | rfield i2 sub2 =>
                        rcases i2 with _ | ⟨_ | ⟨_ | _⟩⟩ <;> try simp [isComb4StoreVal] at he
                        cases sub2 with
                        | var k2 nm2 =>
                          cases k2 with
                          | global => simp [isComb4StoreVal] at he
                          | «local» =>
                            cases e3 with
                            | rfield i3 sub3 =>
                              rcases i3 with _ | ⟨_ | ⟨_ | ⟨_ | _⟩⟩⟩ <;> try simp [isComb4StoreVal] at he
                              cases sub3 with
                              | var k3 nm3 =>
                                cases k3 with
                                | global => simp [isComb4StoreVal] at he
                                | «local» =>
                                  simp only [isComb4StoreVal, Bool.and_eq_true, List.contains_iff_mem] at he
                                  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := he
                                  obtain ⟨w00, w01, w02, w03, w04, hl0⟩ := hc5 nm0 (decide_eq_true_iff.1 h0)
                                  obtain ⟨w10, w11, w12, w13, w14, hl1⟩ := hc5 nm1 (decide_eq_true_iff.1 h1)
                                  obtain ⟨w20, w21, w22, w23, w24, hl2⟩ := hc5 nm2 (decide_eq_true_iff.1 h2)
                                  obtain ⟨w30, w31, w32, w33, w34, hl3⟩ := hc5 nm3 (decide_eq_true_iff.1 h3)
                                  simp only [evalHOLExact, evalListHOLExact, hl0, hl1, hl2, hl3] at hv
                                  dsimp only [Option.map] at hv
                                  injection hv with hv'
                                  exact ⟨w00, w11, w22, w33, hv'.symm⟩
                              | _ => simp [isComb4StoreVal] at he
                            | _ => simp [isComb4StoreVal] at he
                        | _ => simp [isComb4StoreVal] at he
                      | _ => simp [isComb4StoreVal] at he
                  | _ => simp [isComb4StoreVal] at he
                · simp [isComb4StoreVal] at he
            | _ => simp [isComb4StoreVal] at he
        | _ => simp [isComb4StoreVal] at he
      | succ _ => simp [isComb4StoreVal] at he
    | _ => simp [isComb4StoreVal] at he
  | _ => simp [isComb4StoreVal] at he

private def PtFrame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ptVar : MlS) (base : BitVec 64) : Prop :=
  s.locals.lookup ptVar = some (.val (.word base))

private def ptIvls (base : BitVec 64) : List Ivl :=
  [(base.toNat, 32), (base.toNat + 32, 32), (base.toNat + 64, 32)]

private theorem eval_local_mls_add_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup nm = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local nm, .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem ptStore_addr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar : MlS} {base : BitVec 64} {dst : ExpHOL 64} {addr : BitVec 64}
    (hpt : PtFrame s ptVar base) (hbase : base.toNat + 96 ≤ heapEnd)
    (ht : isPtStoreTarget ptVar dst = true)
    (ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word addr))) :
    addr.toNat + 32 ≤ base.toNat + 96 ∧ (addr.toNat, 32) ∈ ptIvls base := by
  have hpt0 : s.locals.lookup ptVar = some (.val (.word base)) := hpt
  cases dst with
  | var k nm =>
    cases k with
    | global => simp [isPtStoreTarget] at ht
    | «local» =>
      simp only [isPtStoreTarget, beq_iff_eq] at ht
      subst ht
      simp only [evalHOLExact, hpt0, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at ha
      subst ha
      exact ⟨by omega, by simp [ptIvls]⟩
  | op bop args =>
    cases bop with
    | add =>
      rcases args with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩ <;> simp [isPtStoreTarget] at ht
      cases e0 with
      | var k nm =>
        cases k with
        | global => simp [isPtStoreTarget] at ht
        | «local» =>
          cases e1 with
          | const off =>
            simp only [isPtStoreTarget, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at ht
            obtain ⟨rfl, hoff⟩ := ht
            rcases hoff with rfl | rfl
            · have hadd := eval_local_mls_add_const s nm base 32 hpt0
              rw [hadd] at ha
              injection ha with h1; injection h1 with h2; injection h2 with h3
              have hnat := bv_add_off_nat_gen base 32 (by omega) (by omega)
              rw [← h3, hnat]
              exact ⟨by omega, by simp [ptIvls]⟩
            · have hadd := eval_local_mls_add_const s nm base 64 hpt0
              rw [hadd] at ha
              injection ha with h1; injection h1 with h2; injection h2 with h3
              have hnat := bv_add_off_nat_gen base 64 (by omega) (by omega)
              rw [← h3, hnat]
              exact ⟨by omega, by simp [ptIvls]⟩
          | _ => simp [isPtStoreTarget] at ht
      | _ => simp [isPtStoreTarget] at ht
    | _ => simp [isPtStoreTarget] at ht
  | _ => simp [isPtStoreTarget] at ht

private theorem evalList_one_eq' {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1] = some vals) :
    ∃ v1,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 ∧
      vals = [v1] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  refine ⟨v1, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1] using h.symm

private theorem isLocalVarEq_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar : MlS} {base : BitVec 64} {e : ExpHOL 64} {v : ValueHOL 64}
    (hpt : PtFrame s ptVar base)
    (heq : isLocalVarEq ptVar e = true)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v) :
    v = .val (.word base) := by
  have hpt0 : s.locals.lookup ptVar = some (.val (.word base)) := hpt
  cases e with
  | var k nm =>
    cases k with
    | global => simp [isLocalVarEq] at heq
    | «local» =>
      simp only [isLocalVarEq, beq_iff_eq] at heq
      subst heq
      simp only [evalHOLExact, hpt0, Option.some.injEq] at hv
      exact hv.symm
  | _ => simp [isLocalVarEq] at heq

private theorem lookup_one_word_local' {fname p1 : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname = some ([(p1, .one)], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      callee.lookup p1 = some (.val (.word w1)) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w1, rfl⟩ := eval_word_of_shape_one (Or.inl hshapes.2.2)
      refine ⟨hb, w1, rfl, ?_⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn p1
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_pt_two_comb4_locals' {fname p1 p2 p3 : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlk : originalRuntimeCode.lookup fname =
      some ([(p1, .one),
             (p2, .comb [.one, .one, .one, .one]),
             (p3, .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    ∃ (w1 : BitVec 64) (v2 v3 : ValueHOL 64),
      vals = [.val (.word w1), v2, v3] ∧
      callee.lookup p1 = some (.val (.word w1)) ∧
      (∃ a0 a1 a2 a3, callee.lookup p2 =
        some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) ∧
      (∃ b0 b1 b2 b3, callee.lookup p3 =
        some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w1, rfl⟩ := eval_word_of_shape_one (Or.inl hshapes.2.2.1)
      obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2.1)
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2.2)
      refine ⟨hb, w1, _, _, rfl, ?_, ⟨a0, a1, a2, a3, ?_⟩, ⟨b0, b1, b2, b3, ?_⟩⟩
      · simpa [FUPDATE_LIST, FUPDATE, hne12, hne13] using congrFun hfn p1
      · simpa [FUPDATE_LIST, FUPDATE, hne23] using congrFun hfn p2
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn p3
    · simp at hraw
  · simp [List.length] at hraw

private theorem call_assign_comb4_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm fname : MlS} {args : List (ExpHOL 64)}
    (hc4 : comb4Val s nm)
    (hn : (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).1 = none) :
    comb4Val (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).2 nm := by
  obtain ⟨w0, w1, w2, w3, hw0⟩ := hc4
  rcases hrun : evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args) with ⟨r, post⟩
  have hr : r = none := by rw [← hn, hrun]
  subst hr
  dsimp only
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hb] at hrun
        cases rb with
        | none => simp at hrun
        | some r0 =>
          cases r0 with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · split at hrun
              · rename_i hv
                injection hrun with _ hpost; subst hpost
                simp only [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, List.map] at hv
                obtain ⟨u0, u1, u2, u3, rfl⟩ := eval_comb4_of_shape (Or.inr hv)
                exact ⟨u0, u1, u2, u3,
                  by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
              · simp at hrun
            · simp at hrun
          | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun

private theorem pt_store_wsSafe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {dst val : ExpHOL 64}
    (hm : s.memaddrs = ordinaryDomain) (hpt : PtFrame s ptVar base)
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hc4 : ∀ x ∈ c4vars, comb4Val s x) (hc5 : ∀ x ∈ c5vars, comb5Val s x)
    (hdst : isPtStoreTarget ptVar dst = true)
    (hval : isComb4StoreVal c4vars c5vars val = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.store dst val)) := by
  refine (wsSafe_store_multi 32 hm ?_ ?_).1
  · intro v hv
    obtain ⟨_, _, _, _, rfl⟩ := isComb4Val_eval hc4 hc5 hval hv
    simp [flattenHOL]
  · intro addr ha
    obtain ⟨hlen, hiv⟩ := ptStore_addr hpt hbase hdst ha
    have h264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
    exact ⟨by omega, (addr.toNat, 32), hiv, le_rfl, le_rfl⟩

private theorem ec_set_infinity_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s (ofString "pt") base) (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ec_set_infinity)) := by
  have hb : sourceFnBody Guest.Software.guestFn_ec_set_infinity =
      FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_ec_set_infinity).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_ec_set_infinity,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, List.map]
  have step : ∀ (t : PanSemStateFiniteExact 64 F), t.memaddrs = ordinaryDomain →
      PtFrame t (ofString "pt") base → ∀ dst val,
      isPtStoreTarget (ofString "pt") dst = true → isComb4StoreVal [] [] val = true →
      WsSafe t (ptIvls base) (evaluateHOLFiniteState t (.store dst val)) :=
    fun _ htm htp _ _ hd hv => pt_store_wsSafe htm htp hbase (by simp) (by simp) hd hv
  refine WsSafe.seq (step s hm hpt _ _ (by decide) (by decide)) fun hn0 he0 => ?_
  set s1 := (evaluateHOLFiniteState s _).2
  have hp1 : PtFrame s1 (ofString "pt") base := by
    unfold PtFrame at *; rw [store_none_locals hn0]; exact hpt
  refine WsSafe.seq (step s1 (he0.memaddrs.trans hm) hp1 _ _ (by decide) (by decide)) fun hn1 he1 => ?_
  set s2 := (evaluateHOLFiniteState s1 _).2
  have hp2 : PtFrame s2 (ofString "pt") base := by
    unfold PtFrame at *; rw [store_none_locals hn1]; exact hp1
  exact WsSafe.seq (step s2 (he1.memaddrs.trans (he0.memaddrs.trans hm)) hp2 _ _ (by decide) (by decide))
    fun _ _ => WsSafe.return_exp _ _ _

private theorem ec_set_affine_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s (ofString "pt") base)
    (hx : comb4Val s (ofString "x")) (hy : comb4Val s (ofString "y"))
    (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ec_set_affine)) := by
  have hb : sourceFnBody Guest.Software.guestFn_ec_set_affine =
      FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_ec_set_affine).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_ec_set_affine,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, List.map]
  have hc4_of : ∀ (t : PanSemStateFiniteExact 64 F), t.locals = s.locals →
      ∀ z ∈ [ofString "x", ofString "y"], comb4Val t z := by
    intro t htl z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · simpa [comb4Val, htl] using hx
    · simpa [comb4Val, htl] using hy
  have step : ∀ (t : PanSemStateFiniteExact 64 F), t.memaddrs = ordinaryDomain →
      t.locals = s.locals → ∀ dst val,
      isPtStoreTarget (ofString "pt") dst = true →
      isComb4StoreVal [ofString "x", ofString "y"] [] val = true →
      WsSafe t (ptIvls base) (evaluateHOLFiniteState t (.store dst val)) :=
    fun t htm htl _ _ hd hv =>
      pt_store_wsSafe htm (by simpa [PtFrame, htl] using hpt) hbase (hc4_of t htl) (by simp) hd hv
  refine WsSafe.seq (step s hm rfl _ _ (by decide) (by decide)) fun hn0 he0 => ?_
  set s1 := (evaluateHOLFiniteState s _).2
  have hl1 : s1.locals = s.locals := store_none_locals hn0
  refine WsSafe.seq (step s1 (he0.memaddrs.trans hm) hl1 _ _ (by decide) (by decide)) fun hn1 he1 => ?_
  set s2 := (evaluateHOLFiniteState s1 _).2
  have hl2 : s2.locals = s.locals := (store_none_locals hn1).trans hl1
  exact WsSafe.seq (step s2 (he1.memaddrs.trans (he0.memaddrs.trans hm)) hl2 _ _ (by decide) (by decide))
    fun _ _ => WsSafe.return_exp _ _ _

private def EcPtInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ptVar : MlS) (base : BitVec 64) (c4vars c5vars : List MlS) : Prop :=
  s.code = originalRuntimeCode ∧ s.memaddrs = ordinaryDomain ∧
  PtFrame s ptVar base ∧ (∀ x ∈ c4vars, comb4Val s x) ∧
  (∀ x ∈ c5vars, comb5Val s x)

private theorem ecPtInv_of_locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ptVar : MlS} {base : BitVec 64} {c4vars c5vars : List MlS} {Rl : List Ivl}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (he : Wave8Contracts.M23.ByteRegionEffect s t Rl) (hl : t.locals = s.locals) :
    EcPtInv t ptVar base c4vars c5vars := by
  refine ⟨he.code.trans hi.1, he.memaddrs.trans hi.2.1, ?_, ?_, ?_⟩
  · simpa [PtFrame, hl] using hi.2.2.1
  · simpa [comb4Val, hl] using hi.2.2.2.1
  · simpa [comb5Val, hl] using hi.2.2.2.2

private theorem ecPtInv_set_comb4 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {w0 w1 w2 w3 : BitVec 64}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hne : nm ≠ ptVar) (hn5 : nm ∉ c5vars) :
    EcPtInv (setVarHOLFinite nm
      (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) s)
      ptVar base (nm :: c4vars) c5vars := by
  refine ⟨hi.1, hi.2.1, ?_, ?_, ?_⟩
  · simpa [PtFrame, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hi.2.2.1
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨w0, w1, w2, w3, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
    · by_cases hnx : nm = x
      · subst hnx
        exact ⟨w0, w1, w2, w3, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simpa [comb4Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.1 x hx
  · intro x hx
    have hnx : nm ≠ x := fun h => hn5 (h.symm ▸ hx)
    simpa [comb5Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.2 x hx

private theorem ecPt_assign_comb4_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS} {e : ExpHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hne : nm ≠ ptVar) (hn5 : nm ∉ c5vars)
    (he : isComb4StoreVal c4vars c5vars e = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.assign .local nm e)) ∧
    ((evaluateHOLFiniteState s (.assign .local nm e)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.assign .local nm e)).2 ptVar base c4vars c5vars) := by
  refine ⟨WsSafe.assign_local s _ nm e, ?_⟩
  rw [evaluateHOLFiniteState_assign]
  split
  · intro h; simp at h
  · rename_i v hv
    split
    · obtain ⟨w0, w1, w2, w3, rfl⟩ := isComb4Val_eval hi.2.2.2.1 hi.2.2.2.2 he hv
      intro _
      have hh := ecPtInv_set_comb4 (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) hi hne hn5
      exact ⟨hh.1, hh.2.1, hh.2.2.1, fun x hx => hh.2.2.2.1 x (List.mem_cons_of_mem _ hx), hh.2.2.2.2⟩
    · intro h; simp at h

private theorem pt_store_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {dst val : ExpHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars) (hbase : base.toNat + 96 ≤ heapEnd)
    (hdst : isPtStoreTarget ptVar dst = true)
    (hval : isComb4StoreVal c4vars c5vars val = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.store dst val)) ∧
    ((evaluateHOLFiniteState s (.store dst val)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.store dst val)).2 ptVar base c4vars c5vars) := by
  have hs := pt_store_wsSafe hi.2.1 hi.2.2.1 hbase hi.2.2.2.1 hi.2.2.2.2 hdst hval
  exact ⟨hs, fun hn => ecPtInv_of_locals hi (hs.1 hn) (store_none_locals hn)⟩

private theorem ecPt_call_assign_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar nm fname : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {args : List (ExpHOL 64)}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hro : recRoCallees fname = true) (hne : nm ≠ ptVar) (hn5 : nm ∉ c5vars) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)) ∧
    ((evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)).2
        ptVar base c4vars c5vars) := by
  have hs := wsSafe_call_assign_local (s := s) (Rl := ptIvls base) (nm := nm)
    (fname := fname) (args := args) (fun vals body callee rs _ hl _ => by
      rw [hi.1] at hl
      exact wsSafe_of_recRo hi.1 (recRoCallees_good fname hro vals body callee rs hl))
  refine ⟨hs.1, fun hn => ⟨(hs.1.1 hn).code.trans hi.1,
    (hs.1.1 hn).memaddrs.trans hi.2.1, ?_, ?_, ?_⟩⟩
  · exact (hs.2 ptVar (Ne.symm hne) hn).trans hi.2.2.1
  · intro x hx
    by_cases hxn : x = nm
    · subst hxn
      exact call_assign_comb4_post (hi.2.2.2.1 x hx) hn
    · simpa [comb4Val, hs.2 x hxn hn] using hi.2.2.2.1 x hx
  · intro x hx
    have hxn : x ≠ nm := fun h => hn5 (h ▸ hx)
    simpa [comb5Val, hs.2 x hxn hn] using hi.2.2.2.2 x hx

private theorem ecPt_call_void_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {args : List (ExpHOL 64)}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hs : WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args))) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.call (some (none, none)) fname args)) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2
        ptVar base c4vars c5vars) := by
  refine ⟨hs, fun hn => ⟨(hs.1 hn).code.trans hi.1, (hs.1 hn).memaddrs.trans hi.2.1, ?_, ?_, ?_⟩⟩
  · exact (wsSafe_call_void_locals hn ptVar).trans hi.2.2.1
  · intro x hx
    simpa [comb4Val, wsSafe_call_void_locals hn x] using hi.2.2.2.1 x hx
  · intro x hx
    simpa [comb5Val, wsSafe_call_void_locals hn x] using hi.2.2.2.2 x hx

private theorem ecCal1Base_wsSafe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64} {e : ExpHOL 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s ptVar base) (hbase : base.toNat + 96 ≤ heapEnd)
    (hf : ecCal1Base fname = true) (he : isLocalVarEq ptVar e = true) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (none, none)) fname [e])) := by
  have hfn : fname = ofString "ec_set_infinity" := by simpa [ecCal1Base] using hf
  subst hfn
  refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
  obtain ⟨v, hv, rfl⟩ := evalList_one_eq' hargs
  have hve := isLocalVarEq_eval hpt he hv
  subst hve
  rw [hc] at hl
  obtain ⟨rfl, w, hvals, hp⟩ := lookup_one_word_local' lookup_ec_set_infinity hl
  have hw : w = base := by simpa using hvals.symm
  subst hw
  exact ec_set_infinity_wsSafe_bound hm hp hbase

private theorem ecCal2Base_wsSafe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64}
    {e ax ay : ExpHOL 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s ptVar base) (hbase : base.toNat + 96 ≤ heapEnd)
    (hf : ecCal2Base fname = true) (he : isLocalVarEq ptVar e = true) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (none, none)) fname [e, ax, ay])) := by
  have hfn : fname = ofString "ec_set_affine" := by simpa [ecCal2Base] using hf
  subst hfn
  refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
  obtain ⟨v, vx, vy, hv, _, _, rfl⟩ := evalList_three_eq' hargs
  have hve := isLocalVarEq_eval hpt he hv
  subst hve
  rw [hc] at hl
  obtain ⟨rfl, w, v2, v3, hvals, hp, hx, hy⟩ :=
    lookup_pt_two_comb4_locals' (by decide) (by decide) (by decide) lookup_ec_set_affine hl
  have hw : w = base := by
    have hh := (List.cons.inj hvals).1
    simpa using hh.symm
  subst hw
  exact ec_set_affine_wsSafe_bound hm hp hx hy hbase

private theorem ec_decCall_ro_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Q : PanSemStateFiniteExact 64 F → Prop} {Rl : List Ivl}
    {nm fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : s.code = originalRuntimeCode) (hf : recRoCallees fname = true)
    (hcont : ∀ (v : ValueHOL 64) (cp : PanSemStateFiniteExact 64 F),
      Wave8Contracts.M23.ByteRegionEffect s cp Rl →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      WsSafe (setVarHOLFinite nm v { cp with locals := s.locals }) Rl
        (evaluateHOLFiniteState (setVarHOLFinite nm v { cp with locals := s.locals }) cont) ∧
      ((evaluateHOLFiniteState (setVarHOLFinite nm v { cp with locals := s.locals }) cont).1 = none →
        Q (restoreLocal nm (s.locals.lookup nm)
          (evaluateHOLFiniteState (setVarHOLFinite nm v { cp with locals := s.locals }) cont).2))) :
    WsSafe s Rl (evaluateHOLFiniteState s (.decCall nm sh fname args cont)) ∧
    ((evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1 = none →
      Q (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).2) := by
  have hcal : ∀ vals body callee rs,
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
    intro vals body callee rs hl
    rw [hc] at hl
    exact wsSafe_of_recRo hc (recRoCallees_good fname hf vals body callee rs hl)
  refine ⟨WsSafe.decCall (fun _ _ _ _ _ hl _ => hcal _ _ _ _ hl)
    (fun _ _ _ _ v cp _ _ _ _ he hsh _ => (hcont v cp he hsh).1), ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · intro h; simp at h
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · intro h; simp at h
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]; intro h; simp at h
      · rw [if_neg hz]
        have hs := hcal vals body callee rs hl
        have he0 : Wave8Contracts.M23.ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (Wave8Contracts.M23.ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cp⟩
        rw [hr] at hs
        cases rb with
        | none => intro h; simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              have he := he0.trans (hs.2 (Or.inl ⟨v, rfl⟩))
              have hq := (hcont v cp he (Bool.and_eq_true_iff.1 hsh).1).2
              rcases hrcont : evaluateHOLFiniteState
                (setVarHOLFinite nm v { cp with locals := s.locals }) cont with ⟨rc, sp⟩
              rw [hrcont] at hq
              exact hq
            · intro h; simp at h
          | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ =>
            intro h; simp at h

private theorem ecPtInv_restore {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (ht : EcPtInv t ptVar base c4vars c5vars) (hne : nm ≠ ptVar) :
    EcPtInv (restoreLocal nm (s.locals.lookup nm) t) ptVar base c4vars c5vars := by
  refine ⟨ht.1, ht.2.1, ?_, ?_, ?_⟩
  · simpa [PtFrame, restoreLocal, PanRunBounded.resVarEq_lookup, Ne.symm hne] using ht.2.2.1
  · intro x hx
    by_cases hnx : x = nm
    · subst x
      simpa [comb4Val, restoreLocal, PanRunBounded.resVarEq_lookup] using hi.2.2.2.1 nm hx
    · simpa [comb4Val, restoreLocal, PanRunBounded.resVarEq_lookup, hnx] using ht.2.2.2.1 x hx
  · intro x hx
    by_cases hnx : x = nm
    · subst x
      simpa [comb5Val, restoreLocal, PanRunBounded.resVarEq_lookup] using hi.2.2.2.2 nm hx
    · simpa [comb5Val, restoreLocal, PanRunBounded.resVarEq_lookup, hnx] using ht.2.2.2.2 x hx

private theorem ecPtInv_set_untracked {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS} {v : ValueHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hne : nm ≠ ptVar) (hn4 : nm ∉ c4vars) (hn5 : nm ∉ c5vars) :
    EcPtInv (setVarHOLFinite nm v s) ptVar base c4vars c5vars := by
  refine ⟨hi.1, hi.2.1, ?_, ?_, ?_⟩
  · simpa [PtFrame, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hi.2.2.1
  · intro x hx
    have hnx : nm ≠ x := fun h => hn4 (h.symm ▸ hx)
    simpa [comb4Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.1 x hx
  · intro x hx
    have hnx : nm ≠ x := fun h => hn5 (h.symm ▸ hx)
    simpa [comb5Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.2 x hx

private theorem ecPtInv_set_comb5 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {w0 w1 w2 w3 w4 : BitVec 64}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hne : nm ≠ ptVar) (hn4 : nm ∉ c4vars) :
    EcPtInv (setVarHOLFinite nm
      (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)]) s)
      ptVar base c4vars (nm :: c5vars) := by
  refine ⟨hi.1, hi.2.1, ?_, ?_, ?_⟩
  · simpa [PtFrame, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hi.2.2.1
  · intro x hx
    have hnx : nm ≠ x := fun h => hn4 (h.symm ▸ hx)
    simpa [comb4Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.1 x hx
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨w0, w1, w2, w3, w4, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
    · by_cases hnx : nm = x
      · subst hnx
        exact ⟨w0, w1, w2, w3, w4, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simpa [comb5Val, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx] using hi.2.2.2.2 x hx

private theorem ecPtProg_assign_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cal1 cal2 : MlS → Bool} {ptVar nm : MlS} {base : BitVec 64}
    {c4vars c5vars : List MlS} {e : ExpHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hp : ecPtProg cal1 cal2 ptVar c4vars c5vars (.assign .local nm e) = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.assign .local nm e)) ∧
    ((evaluateHOLFiniteState s (.assign .local nm e)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.assign .local nm e)).2 ptVar base c4vars c5vars) := by
  simp only [ecPtProg] at hp
  split at hp
  · have hne : nm ≠ ptVar := by
      have hh := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hp).1).1
      simpa using hh
    have hn5 : nm ∉ c5vars := by
      have hh := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hp).1).2
      simpa using hh
    exact ecPt_assign_comb4_wsSafe_post hi hne hn5 (Bool.and_eq_true_iff.1 hp).2
  · rename_i hnm
    have hn4 : nm ∉ c4vars := by simpa using hnm
    have hne : nm ≠ ptVar := by
      have hh := (Bool.and_eq_true_iff.1 hp).1
      simpa using hh
    have hn5 : nm ∉ c5vars := by
      have hh := (Bool.and_eq_true_iff.1 hp).2
      simpa using hh
    refine ⟨WsSafe.assign_local s _ nm e, ?_⟩
    rw [evaluateHOLFiniteState_assign]
    split
    · intro h; simp at h
    · rename_i v hv
      split
      · intro _
        exact ecPtInv_set_untracked hi hne hn4 hn5
      · intro h; simp at h

private theorem ecPtProg_void_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cal1 cal2 : MlS → Bool} {ptVar fname : MlS} {base : BitVec 64}
    {c4vars c5vars : List MlS} {args : List (ExpHOL 64)}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hcal1 : ∀ f e, cal1 f = true → isLocalVarEq ptVar e = true →
      WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.call (some (none, none)) f [e])))
    (hcal2 : ∀ f e ax ay, cal2 f = true → isLocalVarEq ptVar e = true →
      isComb4StoreVal c4vars c5vars ax = true → isComb4StoreVal c4vars c5vars ay = true →
      WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.call (some (none, none)) f [e, ax, ay])))
    (hp : ecPtProg cal1 cal2 ptVar c4vars c5vars (.call (some (none, none)) fname args) = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.call (some (none, none)) fname args)) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2
        ptVar base c4vars c5vars) := by
  apply ecPt_call_void_wsSafe_post hi
  simp only [ecPtProg, Bool.or_eq_true, Bool.and_eq_true] at hp
  rcases hp with ((htrap | hro) | h1) | h2
  · have hf : fname = ofString "trap_with" := by simpa using htrap
    subst hf
    exact wsSafe_of_recRo hi.1 (by simp [readOnlyProg])
  · exact wsSafe_of_recRo hi.1 (by simp [readOnlyProg, hro])
  · obtain ⟨hf, ha⟩ := h1
    rcases args with _ | ⟨e, _ | ⟨e2, rest⟩⟩
    · simp at ha
    · exact hcal1 fname e hf ha
    · simp at ha
  · obtain ⟨hf, ha⟩ := h2
    rcases args with _ | ⟨e, _ | ⟨ax, _ | ⟨ay, _ | rest⟩⟩⟩
    · simp at ha
    · simp at ha
    · simp at ha
    · simp only [Bool.and_eq_true] at ha
      exact hcal2 fname e ax ay hf ha.1.1 ha.1.2 ha.2
    · simp at ha

private theorem ecPtProg_base_void_wsSafe_post {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {args : List (ExpHOL 64)}
    (hi : EcPtInv s ptVar base c4vars c5vars) (hbase : base.toNat + 96 ≤ heapEnd)
    (hp : ecPtProg ecCal1Base ecCal2Base ptVar c4vars c5vars
      (.call (some (none, none)) fname args) = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s (.call (some (none, none)) fname args)) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      EcPtInv (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2
        ptVar base c4vars c5vars) := by
  exact ecPtProg_void_wsSafe_post hi
    (fun _ _ hf he => ecCal1Base_wsSafe hi.1 hi.2.1 hi.2.2.1 hbase hf he)
    (fun _ _ _ _ hf he _ _ => ecCal2Base_wsSafe hi.1 hi.2.1 hi.2.2.1 hbase hf he) hp

private theorem ecPtProg_noTopBreakContinue {cal1 cal2 : MlS → Bool} :
    ∀ {ptVar : MlS} {c4vars c5vars : List MlS} (p : ProgHOL 64),
      ecPtProg cal1 cal2 ptVar c4vars c5vars p = true → noTopBreakContinue p = true
  | _, _, _, .skip, _ | _, _, _, .raise _ _, _ | _, _, _, .return _, _ => rfl
  | _, _, _, .assign .local _ _, _ => rfl
  | _, _, _, .assign .global _ _, h => by simp [ecPtProg] at h
  | _, _, _, .store _ _, _ => rfl
  | pt, c4, c5, .seq a b, h => by
    simp only [ecPtProg, noTopBreakContinue, Bool.and_eq_true] at h ⊢
    exact ⟨ecPtProg_noTopBreakContinue a h.1, ecPtProg_noTopBreakContinue b h.2⟩
  | pt, c4, c5, .ite _ a b, h => by
    simp only [ecPtProg, noTopBreakContinue, Bool.and_eq_true] at h ⊢
    exact ⟨ecPtProg_noTopBreakContinue a h.1, ecPtProg_noTopBreakContinue b h.2⟩
  | _, _, _, .while _ _, _ => rfl
  | pt, c4, c5, .dec nm sh init b, h => by
    simp only [ecPtProg, noTopBreakContinue] at h ⊢
    have h2 := (Bool.and_eq_true_iff.1 h).2
    split at h2
    · exact ecPtProg_noTopBreakContinue b (Bool.and_eq_true_iff.1 h2).2
    · exact ecPtProg_noTopBreakContinue b (Bool.and_eq_true_iff.1 h2).2
  | pt, c4, c5, .decCall nm sh fn _ b, h => by
    simp only [ecPtProg, noTopBreakContinue] at h ⊢
    have h2 := (Bool.and_eq_true_iff.1 h).2
    split at h2
    · exact ecPtProg_noTopBreakContinue b (Bool.and_eq_true_iff.1 h2).2
    · split at h2
      · exact ecPtProg_noTopBreakContinue b (Bool.and_eq_true_iff.1 h2).2
      · exact ecPtProg_noTopBreakContinue b (Bool.and_eq_true_iff.1 h2).2
  | _, _, _, .call none _ _, _ => rfl
  | _, _, _, .call (some (none, none)) _ _, _ => rfl
  | _, _, _, .call (some (some (.local, _), none)) _ _, _ => rfl
  | _, _, _, .call (some (some (.global, _), none)) _ _, h => by simp [ecPtProg] at h
  | _, _, _, .call (some (_, some _)) _ _, h => by simp [ecPtProg] at h
  | _, _, _, .storeByte _ _, h | _, _, _, .break, h | _, _, _, .continue, h
  | _, _, _, .shMemLoad _ _ _ _, h | _, _, _, .shMemStore _ _ _, h
  | _, _, _, .extCall _ _ _ _ _, h | _, _, _, .annot _ _, h
  | _, _, _, .primitive _ _ _, h => by simp [ecPtProg] at h

private theorem ecPtInv_restore_cons4 {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (ht : EcPtInv t ptVar base (nm :: c4vars) c5vars) (hne : nm ≠ ptVar) :
    EcPtInv (restoreLocal nm (s.locals.lookup nm) t) ptVar base c4vars c5vars :=
  ecPtInv_restore hi
    ⟨ht.1, ht.2.1, ht.2.2.1, fun x hx => ht.2.2.2.1 x (List.mem_cons_of_mem _ hx), ht.2.2.2.2⟩
    hne

private theorem ecPtInv_restore_cons5 {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ptVar nm : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (ht : EcPtInv t ptVar base c4vars (nm :: c5vars)) (hne : nm ≠ ptVar) :
    EcPtInv (restoreLocal nm (s.locals.lookup nm) t) ptVar base c4vars c5vars :=
  ecPtInv_restore hi
    ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, fun x hx => ht.2.2.2.2 x (List.mem_cons_of_mem _ hx)⟩
    hne

private theorem isComb4Shape_eq {sh : ShapeHOL} (h : isComb4Shape sh = true) :
    sh = .comb [.one, .one, .one, .one] := by
  cases sh with
  | one | named _ => simp [isComb4Shape] at h
  | comb shs =>
    rcases shs with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | _⟩⟩⟩⟩ <;> try simp [isComb4Shape] at h
    cases s0 <;> try simp [isComb4Shape] at h
    cases s1 <;> try simp [isComb4Shape] at h
    cases s2 <;> try simp [isComb4Shape] at h
    cases s3 <;> try simp [isComb4Shape] at h
    rfl

private theorem isComb5Shape_eq {sh : ShapeHOL} (h : isComb5Shape sh = true) :
    sh = .comb [.one, .one, .one, .one, .one] := by
  cases sh with
  | one | named _ => simp [isComb5Shape] at h
  | comb shs =>
    rcases shs with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | _⟩⟩⟩⟩⟩ <;>
      try simp [isComb5Shape] at h
    cases s0 <;> try simp [isComb5Shape] at h
    cases s1 <;> try simp [isComb5Shape] at h
    cases s2 <;> try simp [isComb5Shape] at h
    cases s3 <;> try simp [isComb5Shape] at h
    cases s4 <;> try simp [isComb5Shape] at h
    rfl

private theorem ecPtProg_wsSafe_post {F : Type}
    {cal1 cal2 : MlS → Bool} {base : BitVec 64}
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hcal1 : ∀ (t : PanSemStateFiniteExact 64 F) ptVar f e,
      t.code = originalRuntimeCode → t.memaddrs = ordinaryDomain →
      PtFrame t ptVar base → cal1 f = true → isLocalVarEq ptVar e = true →
      WsSafe t (ptIvls base) (evaluateHOLFiniteState t (.call (some (none, none)) f [e])))
    (hcal2 : ∀ (t : PanSemStateFiniteExact 64 F) ptVar c4vars c5vars f e ax ay,
      EcPtInv t ptVar base c4vars c5vars → cal2 f = true → isLocalVarEq ptVar e = true →
      isComb4StoreVal c4vars c5vars ax = true → isComb4StoreVal c4vars c5vars ay = true →
      WsSafe t (ptIvls base) (evaluateHOLFiniteState t (.call (some (none, none)) f [e, ax, ay])))
    (p : ProgHOL 64) {ptVar : MlS} {c4vars c5vars : List MlS}
    {s : PanSemStateFiniteExact 64 F}
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hp : ecPtProg cal1 cal2 ptVar c4vars c5vars p = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s p) ∧
    ((evaluateHOLFiniteState s p).1 = none →
      EcPtInv (evaluateHOLFiniteState s p).2 ptVar base c4vars c5vars) := by
  cases shape : p with
  | skip =>
    exact ⟨WsSafe.skip s _, fun _ => by simpa [evaluateHOLFiniteState_skip] using hi⟩
  | «return» e =>
    refine ⟨WsSafe.return_exp s _ e, ?_⟩
    rw [evaluateHOLFiniteState_return]
    split
    · intro h; simp at h
    · split <;> (intro h; simp at h)
  | raise eid e =>
    refine ⟨wsSafe_of_recRo hi.1 rfl, ?_⟩
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (intro h; simp at h)
    · intro h; simp at h
  | assign k nm e =>
    cases k with
    | global => simp [shape, ecPtProg] at hp
    | «local» => exact ecPtProg_assign_wsSafe_post hi (by simpa [shape] using hp)
  | store dst val =>
    have hp' : isPtStoreTarget ptVar dst = true ∧ isComb4StoreVal c4vars c5vars val = true := by
      simpa [shape, ecPtProg, Bool.and_eq_true] using hp
    exact pt_store_wsSafe_post hi hbase hp'.1 hp'.2
  | seq a b =>
    have hp' : ecPtProg cal1 cal2 ptVar c4vars c5vars a = true ∧
        ecPtProg cal1 cal2 ptVar c4vars c5vars b = true := by
      simpa [shape, ecPtProg, Bool.and_eq_true] using hp
    exact WsSafe.seq_post (s := s) (Rl := ptIvls base) (p1 := a) (p2 := b)
      (P1 := fun t => EcPtInv t ptVar base c4vars c5vars)
      (Q := fun t => EcPtInv t ptVar base c4vars c5vars)
      (ecPtProg_wsSafe_post hbase hcal1 hcal2 a hi hp'.1)
      (fun _ hi1 => ecPtProg_wsSafe_post hbase hcal1 hcal2 b hi1 hp'.2)
  | ite cond a b =>
    have hp' : ecPtProg cal1 cal2 ptVar c4vars c5vars a = true ∧
        ecPtProg cal1 cal2 ptVar c4vars c5vars b = true := by
      simpa [shape, ecPtProg, Bool.and_eq_true] using hp
    exact WsSafe.ite_post (s := s) (Rl := ptIvls base)
      (Q := fun t => EcPtInv t ptVar base c4vars c5vars)
      (cond := cond) (yes := a) (no := b)
      (fun _ _ _ => ecPtProg_wsSafe_post hbase hcal1 hcal2 a hi hp'.1)
      (fun _ => ecPtProg_wsSafe_post hbase hcal1 hcal2 b hi hp'.2)
  | «while» cond body =>
    have hp' : ecPtProg cal1 cal2 ptVar c4vars c5vars body = true := by
      simpa [shape, ecPtProg] using hp
    have hnb := ecPtProg_noTopBreakContinue body hp'
    exact WsSafe.while_loop_post hnb (fun t => EcPtInv t ptVar base c4vars c5vars)
      (fun t ht => ht)
      (fun t _ ht _ _ => ecPtProg_wsSafe_post hbase hcal1 hcal2 body ht hp') s hi
  | dec nm sh init body =>
    rw [shape] at hp
    simp only [ecPtProg] at hp
    obtain ⟨hne_b, hrest⟩ := Bool.and_eq_true_iff.1 hp
    have hne : nm ≠ ptVar := by simpa using hne_b
    split at hrest
    · rename_i hc4
      obtain ⟨_, he_init⟩ := Bool.and_eq_true_iff.1 hc4
      obtain ⟨hn5_b, hb⟩ := Bool.and_eq_true_iff.1 hrest
      have hn5 : nm ∉ c5vars := by simpa using hn5_b
      refine WsSafe.dec_post (s := s) (Rl := ptIvls base)
        (Q := fun t => EcPtInv t ptVar base c4vars c5vars)
        (nm := nm) (sh := sh) (init := init) (body := body) fun v hv _ => ?_
      obtain ⟨w0, w1, w2, w3, rfl⟩ := isComb4Val_eval hi.2.2.2.1 hi.2.2.2.2 he_init hv
      have hres := ecPtProg_wsSafe_post hbase hcal1 hcal2 body
        (ecPtInv_set_comb4 (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) hi hne hn5) hb
      exact ⟨hres.1, fun hn => ecPtInv_restore_cons4 hi (hres.2 hn) hne⟩
    · obtain ⟨h45, hb⟩ := Bool.and_eq_true_iff.1 hrest
      obtain ⟨hn4_b, hn5_b⟩ := Bool.and_eq_true_iff.1 h45
      have hn4 : nm ∉ c4vars := by simpa using hn4_b
      have hn5 : nm ∉ c5vars := by simpa using hn5_b
      refine WsSafe.dec_post (s := s) (Rl := ptIvls base)
        (Q := fun t => EcPtInv t ptVar base c4vars c5vars)
        (nm := nm) (sh := sh) (init := init) (body := body) fun v _ _ => ?_
      have hres := ecPtProg_wsSafe_post hbase hcal1 hcal2 body
        (ecPtInv_set_untracked (v := v) hi hne hn4 hn5) hb
      exact ⟨hres.1, fun hn => ecPtInv_restore hi (hres.2 hn) hne⟩
  | decCall nm sh fname args cont =>
    rw [shape] at hp
    simp only [ecPtProg] at hp
    obtain ⟨hfn_nm, hrest⟩ := Bool.and_eq_true_iff.1 hp
    obtain ⟨hro, hne_b⟩ := Bool.and_eq_true_iff.1 hfn_nm
    have hne : nm ≠ ptVar := by simpa using hne_b
    refine ec_decCall_ro_wsSafe_post (s := s)
      (Q := fun t => EcPtInv t ptVar base c4vars c5vars) (Rl := ptIvls base)
      (nm := nm) (fname := fname) (sh := sh) (args := args) (cont := cont)
      hi.1 hro fun v cp he hsh => ?_
    have hicp : EcPtInv { cp with locals := s.locals } ptVar base c4vars c5vars :=
      ⟨he.code.trans hi.1, he.memaddrs.trans hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
    split at hrest
    · rename_i hs4
      obtain ⟨hn5_b, hb⟩ := Bool.and_eq_true_iff.1 hrest
      have hn5 : nm ∉ c5vars := by simpa using hn5_b
      rw [isComb4Shape_eq hs4] at hsh
      obtain ⟨w0, w1, w2, w3, rfl⟩ := eval_comb4_of_shape (Or.inr hsh)
      have hres := ecPtProg_wsSafe_post hbase hcal1 hcal2 cont
        (ecPtInv_set_comb4 (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) hicp hne hn5) hb
      exact ⟨hres.1, fun hn => ecPtInv_restore_cons4 hi (hres.2 hn) hne⟩
    · split at hrest
      · rename_i hs5
        obtain ⟨hn4_b, hb⟩ := Bool.and_eq_true_iff.1 hrest
        have hn4 : nm ∉ c4vars := by simpa using hn4_b
        rw [isComb5Shape_eq hs5] at hsh
        obtain ⟨w0, w1, w2, w3, w4, rfl⟩ := eval_comb5_of_shape (Or.inr hsh)
        have hres := ecPtProg_wsSafe_post hbase hcal1 hcal2 cont
          (ecPtInv_set_comb5 (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) hicp hne hn4) hb
        exact ⟨hres.1, fun hn => ecPtInv_restore_cons5 hi (hres.2 hn) hne⟩
      · obtain ⟨h45, hb⟩ := Bool.and_eq_true_iff.1 hrest
        obtain ⟨hn4_b, hn5_b⟩ := Bool.and_eq_true_iff.1 h45
        have hn4 : nm ∉ c4vars := by simpa using hn4_b
        have hn5 : nm ∉ c5vars := by simpa using hn5_b
        have hres := ecPtProg_wsSafe_post hbase hcal1 hcal2 cont
          (ecPtInv_set_untracked (v := v) hicp hne hn4 hn5) hb
        exact ⟨hres.1, fun hn => ecPtInv_restore hi (hres.2 hn) hne⟩
  | call ret fname args =>
    rw [shape] at hp
    cases ret with
    | none =>
      simp only [ecPtProg] at hp
      refine ⟨wsSafe_of_recRo hi.1 (by simp [readOnlyProg, hp]), ?_⟩
      rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
      · intro h; simp at h
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
        · intro h; simp at h
        · dsimp only; split
          · intro h; simp at h
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cp⟩
            cases rb with
            | none => intro h; simp at h
            | some r0 =>
              cases r0 with
              | returned _ => dsimp only; split <;> (intro h; simp at h)
              | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ =>
                intro h; simp at h
    | some rk =>
      rcases rk with ⟨rk1, rk2⟩
      cases rk2 with
      | some _ => simp [ecPtProg] at hp
      | none =>
        cases rk1 with
        | none =>
          exact ecPtProg_void_wsSafe_post hi
            (fun f e hf he => hcal1 s ptVar f e hi.1 hi.2.1 hi.2.2.1 hf he)
            (fun f e ax ay hf he hax hay => hcal2 s ptVar c4vars c5vars f e ax ay hi hf he hax hay)
            hp
        | some kv =>
          rcases kv with ⟨vk, nm⟩
          cases vk with
          | global => simp [ecPtProg] at hp
          | «local» =>
            simp only [ecPtProg, Bool.and_eq_true] at hp
            exact ecPt_call_assign_wsSafe_post hi hp.1.1
              (by simpa using hp.1.2) (by simpa using hp.2)
  | _ =>
    simp [shape, ecPtProg] at hp
termination_by sizeOf p
decreasing_by
  all_goals
    simp_wf
    subst shape
    simp +arith only [ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.decCall.sizeOf_spec]

private theorem ecPtProg_base_wsSafe_post {F : Type}
    {ptVar : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars) (hbase : base.toNat + 96 ≤ heapEnd)
    (hp : ecPtProg ecCal1Base ecCal2Base ptVar c4vars c5vars p = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s p) ∧
    ((evaluateHOLFiniteState s p).1 = none →
      EcPtInv (evaluateHOLFiniteState s p).2 ptVar base c4vars c5vars) :=
  ecPtProg_wsSafe_post hbase
    (fun _ _ _ _ hc hm hpt hf he => ecCal1Base_wsSafe hc hm hpt hbase hf he)
    (fun _ _ _ _ _ _ _ _ hit hf he _ _ => ecCal2Base_wsSafe hit.1 hit.2.1 hit.2.2.1 hbase hf he)
    p hi hp

private theorem ec_double_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s (ofString "pt") base) (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ec_double)) :=
  (ecPtProg_base_wsSafe_post ⟨hc, hm, hpt, by simp, by simp⟩ hbase ecPtProg_ec_double).1

private theorem ec_to_affine_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s (ofString "pt") base) (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ec_to_affine)) :=
  (ecPtProg_base_wsSafe_post ⟨hc, hm, hpt, by simp, by simp⟩ hbase ecPtProg_ec_to_affine).1

private theorem secp256k1_decompress_r_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hout : PtFrame s (ofString "out") base) (hr : comb4Val s (ofString "r"))
    (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r)) :=
  (ecPtProg_base_wsSafe_post ⟨hc, hm, hout, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hr, by simp⟩
    hbase ecPtProg_secp256k1_decompress_r).1

private theorem ecCal1Full_wsSafe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64} {e : ExpHOL 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s ptVar base) (hbase : base.toNat + 96 ≤ heapEnd)
    (hf : ecCal1Full fname = true) (he : isLocalVarEq ptVar e = true) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (none, none)) fname [e])) := by
  simp only [ecCal1Full, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (rfl | rfl) | rfl
  · exact ecCal1Base_wsSafe hc hm hpt hbase rfl he
  · refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
    obtain ⟨v, hv, rfl⟩ := evalList_one_eq' hargs
    have hve := isLocalVarEq_eval hpt he hv
    subst hve
    rw [hc] at hl
    obtain ⟨rfl, w, hvals, hp⟩ := lookup_one_word_local' lookup_ec_double hl
    have hw : w = base := by simpa using hvals.symm
    subst hw
    exact ec_double_wsSafe_bound hc hm hp hbase
  · refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
    obtain ⟨v, hv, rfl⟩ := evalList_one_eq' hargs
    have hve := isLocalVarEq_eval hpt he hv
    subst hve
    rw [hc] at hl
    obtain ⟨rfl, w, hvals, hp⟩ := lookup_one_word_local' lookup_ec_to_affine hl
    have hw : w = base := by simpa using hvals.symm
    subst hw
    exact ec_to_affine_wsSafe_bound hc hm hp hbase

private theorem ec_add_affine_wsSafe_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s (ofString "pt") base)
    (hax : comb4Val s (ofString "ax")) (hay : comb4Val s (ofString "ay"))
    (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ec_add_affine)) :=
  (ecPtProg_wsSafe_post hbase
    (fun _ _ _ _ hct hmt hptt hf he => ecCal1Full_wsSafe hct hmt hptt hbase hf he)
    (fun _ _ _ _ _ _ _ _ hit hf he _ _ => ecCal2Base_wsSafe hit.1 hit.2.1 hit.2.2.1 hbase hf he)
    _ ⟨hc, hm, hpt, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hax
      · exact hay, by simp⟩
    ecPtProg_ec_add_affine).1

private theorem ecCal2Full_wsSafe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ptVar fname : MlS} {base : BitVec 64} {e ax ay : ExpHOL 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hpt : PtFrame s ptVar base) (hbase : base.toNat + 96 ≤ heapEnd)
    (hf : ecCal2Full fname = true) (he : isLocalVarEq ptVar e = true) :
    WsSafe s (ptIvls base)
      (evaluateHOLFiniteState s (.call (some (none, none)) fname [e, ax, ay])) := by
  simp only [ecCal2Full, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · exact ecCal2Base_wsSafe hc hm hpt hbase rfl he
  · refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
    obtain ⟨v, vx, vy, hv, _, _, rfl⟩ := evalList_three_eq' hargs
    have hve := isLocalVarEq_eval hpt he hv
    subst hve
    rw [hc] at hl
    obtain ⟨rfl, w, v2, v3, hvals, hp, hx, hy⟩ :=
      lookup_pt_two_comb4_locals' (by decide) (by decide) (by decide) lookup_ec_add_affine hl
    have hw : w = base := by
      have hh := (List.cons.inj hvals).1
      simpa using hh.symm
    subst hw
    exact ec_add_affine_wsSafe_bound hc hm hp hx hy hbase

private theorem ecPtProg_full_wsSafe_post {F : Type}
    {ptVar : MlS} {base : BitVec 64} {c4vars c5vars : List MlS}
    {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    (hi : EcPtInv s ptVar base c4vars c5vars) (hbase : base.toNat + 96 ≤ heapEnd)
    (hp : ecPtProg ecCal1Full ecCal2Full ptVar c4vars c5vars p = true) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s p) ∧
    ((evaluateHOLFiniteState s p).1 = none →
      EcPtInv (evaluateHOLFiniteState s p).2 ptVar base c4vars c5vars) :=
  ecPtProg_wsSafe_post hbase
    (fun _ _ _ _ hc hm hpt hf he => ecCal1Full_wsSafe hc hm hpt hbase hf he)
    (fun _ _ _ _ _ _ _ _ hit hf he _ _ => ecCal2Full_wsSafe hit.1 hit.2.1 hit.2.2.1 hbase hf he)
    p hi hp

private def ecMul2TailLoop : ProgHOL 64 → ProgHOL 64
  | .while cond body => .while cond body
  | .seq (.while cond body) _ => .while cond body
  | .seq _ b => ecMul2TailLoop b
  | .dec _ _ _ b => ecMul2TailLoop b
  | .decCall _ _ _ _ b => ecMul2TailLoop b
  | _ => .skip

private def ecMul2Loop : ProgHOL 64 :=
  ecMul2TailLoop (sourceFnBody Guest.Software.guestFn_ec_mul2)

private theorem ecMul2TailLoop_checked (p : ProgHOL 64)
    (hp : ecMul2TailLoopOk p = true) :
    ecPtProg ecCal1Full ecCal2Full (ofString "out")
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] []
      (ecMul2TailLoop p) = true := by
  cases p with
  | «while» cond body => exact hp
  | seq a b =>
    cases a <;> simp only [ecMul2TailLoopOk, ecMul2TailLoop] at hp ⊢
    all_goals first | exact hp | exact ecMul2TailLoop_checked b hp
  | dec nm sh init b => exact ecMul2TailLoop_checked b hp
  | decCall nm sh fn args b => exact ecMul2TailLoop_checked b hp
  | _ => simp [ecMul2TailLoopOk] at hp
termination_by sizeOf p

private theorem ec_mul2_loop_wsSafe_post {F : Type}
    {s : PanSemStateFiniteExact 64 F} {base : BitVec 64}
    (hi : EcPtInv s (ofString "out") base
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [])
    (hbase : base.toNat + 96 ≤ heapEnd) :
    WsSafe s (ptIvls base) (evaluateHOLFiniteState s ecMul2Loop) ∧
    ((evaluateHOLFiniteState s ecMul2Loop).1 = none →
      EcPtInv (evaluateHOLFiniteState s ecMul2Loop).2 (ofString "out") base
        [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] []) :=
  ecPtProg_full_wsSafe_post hi hbase
    (ecMul2TailLoop_checked _ ecMul2TailLoopOk_true)

private theorem ec_mul2_loop_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base : BitVec 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hi : EcPtInv s (ofString "out") base
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [])
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hR : ∀ i ∈ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hr : (evaluateHOLFiniteState s ecMul2Loop).1 = none ∨
      Resumes (evaluateHOLFiniteState s ecMul2Loop).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s ecMul2Loop).2 Rl gw := by
  have hs := (ec_mul2_loop_wsSafe_post hi hbase).1
  have hb : Wave8Contracts.M23.ByteRegionEffect s (evaluateHOLFiniteState s ecMul2Loop).2
      (ptIvls base) := hr.elim hs.1 hs.2
  exact heff.trans ((heapByteEff_of_m23_bre (gw := gw) heff.arena hb).mono hR
    (fun _ h => h))

private def ecMul2Tail : ProgHOL 64 → ProgHOL 64
  | .seq (.while cond body) rest => .seq (.while cond body) rest
  | .seq _ b => ecMul2Tail b
  | .dec _ _ _ b => ecMul2Tail b
  | .decCall _ _ _ _ b => ecMul2Tail b
  | _ => .skip

private theorem ecMul2Tail_eq :
    ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2) =
      .seq ecMul2Loop
        (.seq (.call (some (none, none)) (ofString "heap_release")
          [.var .local (ofString "mark")]) (.return (.const 0))) := rfl

private theorem ec_mul2_tail_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base mark : BitVec 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hi : EcPtInv s (ofString "out") base
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [])
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hout : ∃ j ∈ Rl, j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2)
    (hmark : s.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (hmark_nat : mark.toNat = globN s0 "heap_ptr")
    (hAR0 : ArenaReady s0) (hgw : "heap_ptr" ∈ gw)
    (hnt : (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).2 Rl gw := by
  rw [ecMul2Tail_eq, evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hl : evaluateHOLFiniteState s ecMul2Loop with ⟨rl, mid⟩
  have hor : rl = none ∨ Resumes rl := by
    cases rl with
    | none => exact Or.inl rfl
    | some r => right; rw [hl] at hres; exact hres
  have hR : ∀ i ∈ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit) := by
    intro i hi _
    obtain ⟨j, hj, hj1, hj2⟩ := hout
    left; refine ⟨j, hj, ?_, ?_⟩
    all_goals
      simp only [ptIvls, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> dsimp only <;> omega
  have hm := ec_mul2_loop_heapByteEff heff hi hbase hR (by rw [hl]; exact hor)
  rw [hl] at hm
  rw [hl] at hnt hres
  cases rl with
  | some r => exact hm
  | none =>
    dsimp only at hnt hres ⊢
    have hm_mark : mid.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      have hna : notAssignedLocal (ofString "mark") ecMul2Loop = true := by decide
      have hh := evaluate_notAssignedLocal ecMul2Loop hna s (by rw [hl]; rfl)
      rw [hl] at hh
      exact hh.trans hmark
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) with ⟨rc, post⟩
    have hntc : rc ≠ some .timeOut := by
      rintro rfl; rw [hc] at hnt; exact hnt rfl
    have hrel := eval_call_heap_release mid (.var .local (ofString "mark")) mark Rl gw
      hm.arena.1.code hm hgw hm_mark (by rw [hmark_nat])
      (by rw [hmark_nat]; exact hAR0.2.1)
      (by rw [hmark_nat]; exact hAR0.2.2.1)
      (by rw [hmark_nat]; exact hAR0.2.2.2.2.2.2.1)
      (by rw [hc]; exact hntc)
    dsimp only at hrel
    rw [hc] at hrel
    obtain ⟨rfl, _, _, _, hp⟩ := hrel
    dsimp only at hp ⊢
    exact hp.trans (HeapByteEff.of_byteEff hp.arena
      (R13Shards.Keccak256.byteEff_return post (.const 0) Rl))

private theorem ptIvls_cover {base : BitVec 64} {Rl : List Ivl}
    (hout : ∃ j ∈ Rl, j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2) :
    ∀ i ∈ ptIvls base, ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
  intro i hi
  obtain ⟨j, hj, hj1, hj2⟩ := hout
  refine ⟨j, hj, ?_, ?_⟩
  all_goals
    simp only [ptIvls, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> dsimp only <;> omega

private theorem heapByteEff_step_of_wsSafe {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {R1 Rl : List Ivl} {gw : List String}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (heff : HeapByteEff s0 s Rl gw) (hs : WsSafe s R1 out)
    (hR : ∀ i ∈ R1, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hr : out.1 = none ∨ Resumes out.1) :
    HeapByteEff s0 out.2 Rl gw := by
  exact heff.trans ((heapByteEff_of_m23_bre (gw := gw) heff.arena
    (hr.elim hs.1 hs.2)).mono hR (fun _ h => h))

private theorem ecPtProg_full_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {ptVar : MlS} {base : BitVec 64}
    {c4vars c5vars : List MlS} {p : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hi : EcPtInv s ptVar base c4vars c5vars)
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hp : ecPtProg ecCal1Full ecCal2Full ptVar c4vars c5vars p = true)
    (hR : ∀ i ∈ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hr : (evaluateHOLFiniteState s p).1 = none ∨ Resumes (evaluateHOLFiniteState s p).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw ∧
    ((evaluateHOLFiniteState s p).1 = none →
      EcPtInv (evaluateHOLFiniteState s p).2 ptVar base c4vars c5vars) := by
  have hs := ecPtProg_full_wsSafe_post hi hbase hp
  exact ⟨heapByteEff_step_of_wsSafe heff hs.1 hR hr, hs.2⟩

private theorem secp256k1_decompress_r_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base : BitVec 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hout : PtFrame s (ofString "out") base) (hrv : comb4Val s (ofString "r"))
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hR : ∀ i ∈ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hr : Resumes (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r)).2 Rl gw := by
  exact heapByteEff_step_of_wsSafe heff
    (secp256k1_decompress_r_wsSafe_bound heff.arena.1.code heff.arena.1.memaddrs
      hout hrv hbase) hR (Or.inr hr)

private def ecMul2SumSetup : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "ec_set_affine")
      [.var .local (ofString "sum"), .var .local (ofString "ax"), .var .local (ofString "ay")])
    (.seq
      (.call (some (none, none)) (ofString "ec_add_affine")
        [.var .local (ofString "sum"), .var .local (ofString "bx"), .var .local (ofString "by")])
      (.decCall (ofString "sum_inf") .one (ofString "ec_is_infinity")
        [.var .local (ofString "sum")]
        (.ite (.cmp .equal (.var .local (ofString "sum_inf")) (.const 0))
          (.call (some (none, none)) (ofString "ec_to_affine") [.var .local (ofString "sum")])
          .skip)))

private theorem ecMul2SumSetup_checked :
    ecPtProg ecCal1Full ecCal2Full (ofString "sum")
      [ofString "ax", ofString "ay", ofString "bx", ofString "by"] [] ecMul2SumSetup = true := by
  decide

private theorem ec_mul2_sum_setup_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base : BitVec 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hi : EcPtInv s (ofString "sum") base
      [ofString "ax", ofString "ay", ofString "bx", ofString "by"] [])
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hfree : globN s0 "heap_ptr" ≤ base.toNat ∧ base.toNat + 96 ≤ heapLimit)
    (hr : (evaluateHOLFiniteState s ecMul2SumSetup).1 = none ∨
      Resumes (evaluateHOLFiniteState s ecMul2SumSetup).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s ecMul2SumSetup).2 Rl gw ∧
    ((evaluateHOLFiniteState s ecMul2SumSetup).1 = none →
      EcPtInv (evaluateHOLFiniteState s ecMul2SumSetup).2 (ofString "sum") base
        [ofString "ax", ofString "ay", ofString "bx", ofString "by"] []) := by
  have hs := ecPtProg_full_wsSafe_post hi hbase ecMul2SumSetup_checked
  have hb : HeapByteEff s (evaluateHOLFiniteState s ecMul2SumSetup).2 (ptIvls base) gw :=
    heapByteEff_of_m23_bre (gw := gw) heff.arena (hr.elim hs.1.1 hs.1.2)
  have hsub : ∀ i ∈ Rl ++ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s0 "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s0 "scratch_ptr") ∨
      (globN s0 "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit) := by
    intro i hi _
    rcases List.mem_append.1 hi with hiR | hiP
    · exact Or.inl ⟨i, hiR, le_rfl, le_rfl⟩
    · right; right
      simp only [ptIvls, List.mem_cons, List.not_mem_nil, or_false] at hiP
      rcases hiP with rfl | rfl | rfl <;> dsimp only <;> omega
  have heff' : HeapByteEff s0 s (Rl ++ ptIvls base) gw :=
    heff.mono (fun i hi _ => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩) (fun _ h => h)
  have hb' : HeapByteEff s (evaluateHOLFiniteState s ecMul2SumSetup).2 (Rl ++ ptIvls base) gw :=
    hb.mono (fun i hi _ => Or.inl ⟨i, List.mem_append_right _ hi, le_rfl, le_rfl⟩) (fun _ h => h)
  exact ⟨(heff'.trans hb').mono hsub (fun _ h => h), hs.2⟩

private theorem heapByteEff_seq_wsSafe {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {p cont : ProgHOL 64} {P : PanSemStateFiniteExact 64 F → Prop}
    (heff : HeapByteEff s0 s Rl gw)
    (hs : WsSafe s Rl (evaluateHOLFiniteState s p))
    (hpost : (evaluateHOLFiniteState s p).1 = none →
      P (evaluateHOLFiniteState s p).2)
    (hcont : ∀ t, HeapByteEff s0 t Rl gw → P t →
      (evaluateHOLFiniteState t cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState t cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState t cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.seq p cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq p cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq p cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hp : evaluateHOLFiniteState s p with ⟨r, mid⟩
  simp only [hp] at hs hpost hnt hres ⊢
  cases r with
  | none =>
    exact hcont mid (heff.trans (heapByteEff_of_m23_bre heff.arena (hs.1 rfl)))
      (hpost rfl) hnt hres
  | some r =>
    exact heff.trans (heapByteEff_of_m23_bre heff.arena (hs.2 hres))

private theorem heapByteEff_restoreLocal {F : Type}
    {s0 post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 post Rl gw) (nm : MlS) (old : Option (ValueHOL 64)) :
    HeapByteEff s0 (restoreLocal nm old post) Rl gw :=
  heff.locals_clock _ post.clock

private theorem heapByteEff_return {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw) (e : ExpHOL 64) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.return e)).2 Rl gw :=
  heff.trans (HeapByteEff.of_byteEff heff.arena
    (R13Shards.Keccak256.byteEff_return s e Rl))

private theorem return_fst_ne_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

private theorem heapByteEff_seq_wsSafe_sub {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {R1 Rl : List Ivl} {gw : List String}
    {p cont : ProgHOL 64} {P : PanSemStateFiniteExact 64 F → Prop}
    (heff : HeapByteEff s0 s Rl gw)
    (hs : WsSafe s R1 (evaluateHOLFiniteState s p))
    (hR : ∀ i ∈ R1, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hpost : (evaluateHOLFiniteState s p).1 = none →
      Wave8Contracts.M23.ByteRegionEffect s (evaluateHOLFiniteState s p).2 R1 →
      P (evaluateHOLFiniteState s p).2)
    (hcont : ∀ t, HeapByteEff s0 t Rl gw → P t →
      (evaluateHOLFiniteState t cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState t cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState t cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.seq p cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq p cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq p cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hp : evaluateHOLFiniteState s p with ⟨r, mid⟩
  have hstep : r = none ∨ Resumes r → HeapByteEff s0 mid Rl gw := fun hr => by
    have hh := heapByteEff_step_of_wsSafe heff hs hR (by rw [hp]; exact hr)
    simpa [hp] using hh
  simp only [hp] at hs hpost hnt hres ⊢
  cases r with
  | none =>
    exact hcont mid (hstep (Or.inl rfl)) (hpost rfl (hs.1 rfl)) hnt hres
  | some r =>
    exact hstep (Or.inr hres)

private theorem heapByteEff_seq_ite_return_skip {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cond retExp : ExpHOL 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcont : (evaluateHOLFiniteState s cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState s cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.seq (.ite cond (.return retExp) .skip) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.ite cond (.return retExp) .skip) cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq (.ite cond (.return retExp) .skip) cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp only [hcv] at hnt hres ⊢; exact heff
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcv] at hnt hres ⊢
      by_cases hcz : cw = 0
      · subst hcz
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hnt hres ⊢
        exact hcont hnt hres
      · simp only [hcz, ↓reduceIte] at hnt hres ⊢
        rcases hr : evaluateHOLFiniteState s (.return retExp) with ⟨rr, sr⟩
        cases rr with
        | none => exact absurd rfl (by have hn := return_fst_ne_none s retExp; rw [hr] at hn; exact hn)
        | some _ =>
          have hh := heapByteEff_return heff retExp
          rw [hr] at hh
          exact hh
    · simp only [hcv] at hnt hres ⊢; exact heff
    · simp only [hcv] at hnt hres ⊢; exact heff

private theorem heapByteEff_release_return {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {mExp retExp : ExpHOL 64} {mw : BitVec 64}
    (heff : HeapByteEff s0 s Rl gw) (hgw : "heap_ptr" ∈ gw)
    (hm_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hm_lo : globN s0 "heap_ptr" ≤ mw.toNat)
    (hm_lo_sb : sourceBase ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm8 : mw.toNat % 8 = 0)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "heap_release") [mExp]) (.return retExp))).1 ≠
        some .timeOut) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "heap_release") [mExp]) (.return retExp))).2 Rl gw ∧
    (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "heap_release") [mExp]) (.return retExp))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hc : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "heap_release") [mExp]) with ⟨rc, post⟩
  have hntc : rc ≠ some .timeOut := by
    rintro rfl; rw [hc] at hnt; exact hnt rfl
  have hrel := eval_call_heap_release s mExp mw Rl gw heff.arena.1.code heff hgw
    hm_ev hm_lo hm_lo_sb hm_hi hm8 (by rw [hc]; exact hntc)
  dsimp only at hrel
  rw [hc] at hrel
  obtain ⟨rfl, _, _, _, hp⟩ := hrel
  dsimp only at hp ⊢
  exact ⟨heapByteEff_return hp retExp, return_fst_ne_none post retExp⟩

private theorem heapByteEff_seq_ite_release_return_skip {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cond mExp retExp : ExpHOL 64} {mw : BitVec 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw) (hgw : "heap_ptr" ∈ gw)
    (hm_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hm_lo : globN s0 "heap_ptr" ≤ mw.toNat)
    (hm_lo_sb : sourceBase ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm8 : mw.toNat % 8 = 0)
    (hcont : (evaluateHOLFiniteState s cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState s cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.ite cond (.seq (.call (some (none, none)) (ofString "heap_release") [mExp])
          (.return retExp)) .skip) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.ite cond (.seq (.call (some (none, none)) (ofString "heap_release") [mExp])
          (.return retExp)) .skip) cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.seq (.ite cond (.seq (.call (some (none, none)) (ofString "heap_release") [mExp])
          (.return retExp)) .skip) cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp only [hcv] at hnt hres ⊢; exact heff
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcv] at hnt hres ⊢
      by_cases hcz : cw = 0
      · subst hcz
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hnt hres ⊢
        exact hcont hnt hres
      · simp only [hcz, ↓reduceIte] at hnt hres ⊢
        rcases hr : evaluateHOLFiniteState s
          (.seq (.call (some (none, none)) (ofString "heap_release") [mExp]) (.return retExp)) with ⟨rr, sr⟩
        simp only [hr] at hnt hres ⊢
        have hnt_r : rr ≠ some .timeOut := by
          rintro rfl; exact hnt rfl
        have hh := heapByteEff_release_return heff hgw hm_ev hm_lo hm_lo_sb hm_hi hm8
          (by rw [hr]; exact hnt_r)
        rw [hr] at hh
        cases rr with
        | none => exact absurd rfl hh.2
        | some _ => exact hh.1
    · simp only [hcv] at hnt hres ⊢; exact heff
    · simp only [hcv] at hnt hres ⊢; exact heff

private theorem heapByteEff_seq_ite_skip {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cond : ExpHOL 64} {yes cont : ProgHOL 64} {P : PanSemStateFiniteExact 64 F → Prop}
    (heff : HeapByteEff s0 s Rl gw)
    (hskip : P s)
    (hyes : (evaluateHOLFiniteState s yes).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s yes).1 = none ∨ Resumes (evaluateHOLFiniteState s yes).1) →
      HeapByteEff s0 (evaluateHOLFiniteState s yes).2 Rl gw ∧
      ((evaluateHOLFiniteState s yes).1 = none → P (evaluateHOLFiniteState s yes).2))
    (hcont : ∀ t, HeapByteEff s0 t Rl gw → P t →
      (evaluateHOLFiniteState t cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState t cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState t cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.seq (.ite cond yes .skip) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.ite cond yes .skip) cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq (.ite cond yes .skip) cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp only [hcv] at hnt hres ⊢; exact heff
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcv] at hnt hres ⊢
      by_cases hcz : cw = 0
      · subst hcz
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hnt hres ⊢
        exact hcont s heff hskip hnt hres
      · simp only [hcz, ↓reduceIte] at hnt hres ⊢
        rcases hy : evaluateHOLFiniteState s yes with ⟨ry, sy⟩
        simp only [hy] at hnt hres ⊢
        have hnty : ry ≠ some .timeOut := by
          rintro rfl; exact hnt rfl
        have hory : ry = none ∨ Resumes ry := by
          cases ry with
          | none => exact Or.inl rfl
          | some _ => exact Or.inr hres
        have hh := hyes (by rw [hy]; exact hnty) (by rw [hy]; exact hory)
        simp only [hy] at hh
        cases ry with
        | none => exact hcont sy hh.1 (hh.2 rfl) hnt hres
        | some _ => exact hh.1
    · simp only [hcv] at hnt hres ⊢; exact heff
    · simp only [hcv] at hnt hres ⊢; exact heff

private theorem heapByteEff_dec {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcont : ∀ (v : ValueHOL 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      let mid := setVarHOLFinite nm v s
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.dec nm sh init cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.dec nm sh init cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.dec nm sh init cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | v
  · simp only [hv] at hnt hres ⊢; exact heff
  · simp only [hv] at hnt hres ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hres ⊢
      have heff_mid : HeapByteEff s0 (setVarHOLFinite nm v s) Rl gw :=
        heff.locals_clock _ s.clock
      exact heapByteEff_restoreLocal (hcont v hv hsh heff_mid hnt hres) nm (s.locals.lookup nm)
    · simp only [hsh, ↓reduceIte]
      exact heff

private theorem heapByteEff_decCall_wsSafe {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {R1 Rl : List Ivl} {gw : List String}
    {nm fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) R1
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body))
    (hR : ∀ i ∈ R1, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hcont : ∀ (v : ValueHOL 64) (cp : PanSemStateFiniteExact 64 F),
      let mid := setVarHOLFinite nm v { cp with locals := s.locals }
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      mid.globals = s.globals →
      mid.locals.lookup nm = some v →
      (∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [hargs] at hnt hres ⊢; exact heff
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · simp only [hl] at hnt hres ⊢; exact heff
    · simp only [hl] at hnt hres ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte] at hnt; simp at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        have hc := hcal vals body callee rs hargs hl hz
        have he0 : Wave8Contracts.M23.ByteRegionEffect s (callEntryStateHOLFinite s callee) R1 :=
          (Wave8Contracts.M23.ByteRegionEffect.refl s R1).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cp⟩
        simp only [hrun] at hc hnt hres ⊢
        cases rb with
        | none =>
          simp at hres; exact False.elim (not_resumes_error hres)
        | some r0 =>
          cases r0 with
          | returned v =>
            dsimp only at hnt hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) rs) = true
            · simp only [hsh, ↓reduceIte] at hnt hres ⊢
              have hsh2 := (Bool.and_eq_true_iff.1 hsh).1
              have he_cp := he0.trans (hc.2 (Or.inl ⟨v, rfl⟩))
              have heff_cp : HeapByteEff s0 cp Rl gw :=
                heff.trans ((heapByteEff_of_m23_bre heff.arena he_cp).mono hR (fun _ h => h))
              set mid := setVarHOLFinite nm v { cp with locals := s.locals }
              have heff_mid : HeapByteEff s0 mid Rl gw := heff_cp.locals_clock _ cp.clock
              have hglob : mid.globals = s.globals := he_cp.globals
              have hloc_nm : mid.locals.lookup nm = some v := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hloc_other : ∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x := by
                intro x hne
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
              exact heapByteEff_restoreLocal
                (hcont v cp hsh2 hglob hloc_nm hloc_other heff_mid hnt hres)
                nm (s.locals.lookup nm)
            · simp only [hsh, ↓reduceIte] at hres; exact False.elim (not_resumes_error hres)
          | exception eid ev =>
            dsimp only at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h'; injection h' with h1 h2; subst h1 h2
              have he_cp := he0.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))
              have heff_cp : HeapByteEff s0 cp Rl gw :=
                heff.trans ((heapByteEff_of_m23_bre heff.arena he_cp).mono hR (fun _ h => h))
              exact heff_cp.locals_clock _ cp.clock
          | timeOut => simp at hnt
          | error | «break» | «continue» =>
            simp at hres; exact False.elim (not_resumes_error hres)
          | finalFfi _ =>
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem heapByteEff_decCall_ro {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {nm fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hro : recRoCallees fname = true)
    (hcont : ∀ (v : ValueHOL 64) (cp : PanSemStateFiniteExact 64 F),
      let mid := setVarHOLFinite nm v { cp with locals := s.locals }
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      mid.globals = s.globals →
      mid.locals.lookup nm = some v →
      (∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).2 Rl gw := by
  refine heapByteEff_decCall_wsSafe (R1 := []) heff (fun vals body callee rs _ hl _ => ?_)
    (fun _ hi => nomatch hi) hcont hnt hres
  have hc := heff.arena.1.code
  rw [hc] at hl
  exact wsSafe_of_recRo hc (recRoCallees_good fname hro vals body callee rs hl)

private theorem heapByteEff_decCall_heap_mark {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {lname : String} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcont : ∀ (mark : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mark.toNat = globN s "heap_ptr" →
      globN s0 "heap_ptr" ≤ mark.toNat →
      sourceBase ≤ mark.toNat →
      mark.toNat ≤ heapLimit →
      mark.toNat % 8 = 0 →
      mid.globals = s.globals →
      mid.locals.lookup (ofString lname) = some (.val (.word mark)) →
      (∀ x, x ≠ ofString lname → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).2 Rl gw := by
  obtain ⟨mark, mid, _, hmark_nat, hg_eq, _, hloc_eq, heff_s_mid, hnt_mid, heval_eq⟩ :=
    eval_decCall_heap_mark s lname cont Rl gw heff.arena.1.code heff.arena hnt
  rw [heval_eq] at hres ⊢
  dsimp only at hres ⊢
  have heff_mid : HeapByteEff s0 mid Rl gw := heff.trans heff_s_mid
  have hlo : globN s0 "heap_ptr" ≤ mark.toNat := by rw [hmark_nat]; exact heff.hp_le
  have hsb : sourceBase ≤ mark.toNat := by rw [hmark_nat]; exact heff.arena.2.1
  have hhi : mark.toNat ≤ heapLimit := by rw [hmark_nat]; exact heff.arena.2.2.1
  have hm8 : mark.toNat % 8 = 0 := by rw [hmark_nat]; exact heff.arena.2.2.2.2.2.2.1
  have hloc_nm : mid.locals.lookup (ofString lname) = some (.val (.word mark)) := by
    rw [hloc_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hloc_other : ∀ x, x ≠ ofString lname → mid.locals.lookup x = s.locals.lookup x := by
    intro x hne; rw [hloc_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  exact heapByteEff_restoreLocal
    (hcont mark mid hmark_nat hlo hsb hhi hm8 hg_eq hloc_nm hloc_other heff_mid hnt_mid hres)
    (ofString lname) (s.locals.lookup (ofString lname))

private theorem heapByteEff_decCall_alloc {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {lname : String} {nExp : ExpHOL 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw) (hgw : "heap_ptr" ∈ gw)
    (hcont : ∀ (hp n q : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
        some (.val (.word n)) →
      hp.toNat = globN s "heap_ptr" →
      hp.toNat % 8 = 0 →
      hp.toNat + n.toNat ≤ q.toNat →
      q.toNat ≤ heapLimit →
      hp.toNat + n.toNat ≤ heapEnd →
      mid.locals.lookup (ofString lname) = some (.val (.word hp)) →
      (∀ x, x ≠ ofString lname → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid (Rl ++ [(hp.toNat, n.toNat)]) gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 (Rl ++ [(hp.toNat, n.toNat)]) gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).2 Rl gw := by
  obtain ⟨hp, n, q, mid, hnev, hhp_nat, hhp8, _, hpq, hq_hi, _, _, _, _, hloc_eq,
    heff_s_mid, hnt_mid, hres_mid, heval_eq⟩ :=
    eval_decCall_alloc_resumes s lname nExp cont Rl gw heff.arena.1.code heff.arena hgw hnt hres
  rw [heval_eq]
  dsimp only
  have hhl_he : heapLimit ≤ heapEnd := by rw [WkBlockTxEnc.heapLimit_val, WkBlockTxEnc.heapEnd_val]; decide
  have hhe : hp.toNat + n.toNat ≤ heapEnd := by omega
  have heff_mid0 : HeapByteEff s0 mid Rl gw := heff.trans heff_s_mid
  have heff_mid : HeapByteEff s0 mid (Rl ++ [(hp.toNat, n.toNat)]) gw :=
    heff_mid0.mono (fun i hi _ => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩)
      (fun _ h => h)
  have hloc_nm : mid.locals.lookup (ofString lname) = some (.val (.word hp)) := by
    rw [hloc_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hloc_other : ∀ x, x ≠ ofString lname → mid.locals.lookup x = s.locals.lookup x := by
    intro x hne; rw [hloc_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  have hout := heapByteEff_restoreLocal
    (hcont hp n q mid hnev hhp_nat hhp8 hpq hq_hi hhe hloc_nm hloc_other heff_mid hnt_mid hres_mid)
    (ofString lname) (s.locals.lookup (ofString lname))
  refine hout.mono (fun i hi _ => ?_) (fun _ h => h)
  rcases List.mem_append.1 hi with hiR | hiA
  · exact Or.inl ⟨i, hiR, le_rfl, le_rfl⟩
  · simp only [List.mem_singleton] at hiA
    subst hiA
    have hlo : globN s0 "heap_ptr" ≤ hp.toNat := by rw [hhp_nat]; exact heff.hp_le
    exact Or.inr (Or.inr ⟨hlo, by dsimp only; omega⟩)

private theorem ec_mul2_tail_heapByteEff_gen {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base mark : BitVec 64} {Rl : List Ivl} {gw : List String}
    (heff : HeapByteEff s0 s Rl gw)
    (hi : EcPtInv s (ofString "out") base
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [])
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hout : ∃ j ∈ Rl, j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2)
    (hmark : s.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (hm_lo : globN s0 "heap_ptr" ≤ mark.toNat)
    (hm_sb : sourceBase ≤ mark.toNat)
    (hm_hi : mark.toNat ≤ heapLimit)
    (hm8 : mark.toNat % 8 = 0)
    (hgw : "heap_ptr" ∈ gw)
    (hnt : (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (ecMul2Tail (sourceFnBody Guest.Software.guestFn_ec_mul2))).2 Rl gw := by
  rw [ecMul2Tail_eq, evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hl : evaluateHOLFiniteState s ecMul2Loop with ⟨rl, mid⟩
  have hor : rl = none ∨ Resumes rl := by
    cases rl with
    | none => exact Or.inl rfl
    | some _ => right; rw [hl] at hres; exact hres
  have hR : ∀ i ∈ ptIvls base, 0 < i.2 →
      (∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit) :=
    fun i hi _ => Or.inl (ptIvls_cover hout i hi)
  have hm := ec_mul2_loop_heapByteEff heff hi hbase hR (by rw [hl]; exact hor)
  rw [hl] at hm
  simp only [hl] at hnt hres ⊢
  cases rl with
  | some _ => exact hm
  | none =>
    have hm_mark : mid.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      have hna : notAssignedLocal (ofString "mark") ecMul2Loop = true := by decide
      have hh := evaluate_notAssignedLocal ecMul2Loop hna s (by rw [hl]; rfl)
      rw [hl] at hh
      exact hh.trans hmark
    dsimp only at hm hnt ⊢
    exact (heapByteEff_release_return hm hgw
      (eval_local_word mid "mark" mark hm_mark) hm_lo hm_sb hm_hi hm8 hnt).1

private theorem ec_mul2_body_heapByteEff {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {base : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0) (hgw : "heap_ptr" ∈ gw)
    (hout_loc : PtFrame s0 (ofString "out") base)
    (hax : comb4Val s0 (ofString "ax")) (hay : comb4Val s0 (ofString "ay"))
    (hbx : comb4Val s0 (ofString "bx")) (hby : comb4Val s0 (ofString "by"))
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hout : ∃ j ∈ Rl, j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_ec_mul2)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_ec_mul2)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_ec_mul2)).2 Rl gw := by
  have hb : sourceFnBody Guest.Software.guestFn_ec_mul2 =
      FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_ec_mul2).body := rfl
  rw [hb] at hnt hres ⊢
  dsimp only [extractFn, Guest.Software.guestFn_ec_mul2,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  have heff0 := HeapByteEff.refl hAR0 Rl gw
  refine heapByteEff_seq_wsSafe_sub (P := fun t => ∀ x, t.locals.lookup x = s0.locals.lookup x) heff0
    (ecCal1Base_wsSafe hAR0.1.code hAR0.1.memaddrs hout_loc hbase rfl rfl)
    (fun i hi _ => Or.inl (ptIvls_cover hout i hi))
    (fun hn _ x => wsSafe_call_void_locals hn x) ?_ hnt hres
  intro s1 heff1 hloc1 hnt1 hres1
  refine heapByteEff_decCall_ro heff1 (by decide) ?_ hnt1 hres1
  intro _ _ _ _ _ _ hloc2 heff2 hnt2 hres2
  refine heapByteEff_decCall_ro heff2 (by decide) ?_ hnt2 hres2
  intro _ _ _ _ _ _ hloc3 heff3 hnt3 hres3
  refine heapByteEff_decCall_ro heff3 (by decide) ?_ hnt3 hres3
  intro _ _ _ _ _ _ hloc4 heff4 hnt4 hres4
  refine heapByteEff_seq_ite_return_skip heff4 ?_ hnt4 hres4
  intro hnt5 hres5
  refine heapByteEff_decCall_heap_mark heff4 ?_ hnt5 hres5
  intro mark s5 _ hm_lo hm_sb hm_hi hm8 _ hmark5 hloc5 heff5 hnt6 hres6
  refine heapByteEff_decCall_alloc heff5 hgw ?_ hnt6 hres6
  intro hp n96 _ s6 hn96 _ _ _ _ hhp_end hsum6 hloc6 heff6 hnt7 hres7
  have hn96_eq : n96 = 96#64 := by
    simp only [evalHOLExact] at hn96
    injection hn96 with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
  subst hn96_eq
  have hbase_sum : hp.toNat + 96 ≤ heapEnd := by simpa using hhp_end
  have hout6 : ∃ j ∈ Rl ++ [(hp.toNat, (96#64 : BitVec 64).toNat)],
      j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2 := by
    obtain ⟨j, hj, hj1, hj2⟩ := hout
    exact ⟨j, List.mem_append_left _ hj, hj1, hj2⟩
  have hsum_in6 : ∃ j ∈ Rl ++ [(hp.toNat, (96#64 : BitVec 64).toNat)],
      j.1 ≤ hp.toNat ∧ hp.toNat + 96 ≤ j.1 + j.2 :=
    ⟨(hp.toNat, 96), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩
  have hkeep6 : ∀ x, x ≠ ofString "sum" → x ≠ ofString "mark" → x ≠ ofString "i" →
      x ≠ ofString "len2" → x ≠ ofString "len1" → s6.locals.lookup x = s0.locals.lookup x := by
    intro x h1 h2 h3 h4 h5
    rw [hloc6 x h1, hloc5 x h2, hloc4 x h3, hloc3 x h4, hloc2 x h5, hloc1 x]
  have hout_s6 : PtFrame s6 (ofString "out") base := by
    unfold PtFrame; rw [hkeep6 (ofString "out") (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hout_loc
  have hmark_s6 : s6.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hloc6 (ofString "mark") (by decide)]; exact hmark5
  have hax_s6 : comb4Val s6 (ofString "ax") := by
    simpa [comb4Val, hkeep6 (ofString "ax") (by decide) (by decide) (by decide) (by decide) (by decide)] using hax
  have hay_s6 : comb4Val s6 (ofString "ay") := by
    simpa [comb4Val, hkeep6 (ofString "ay") (by decide) (by decide) (by decide) (by decide) (by decide)] using hay
  have hbx_s6 : comb4Val s6 (ofString "bx") := by
    simpa [comb4Val, hkeep6 (ofString "bx") (by decide) (by decide) (by decide) (by decide) (by decide)] using hbx
  have hby_s6 : comb4Val s6 (ofString "by") := by
    simpa [comb4Val, hkeep6 (ofString "by") (by decide) (by decide) (by decide) (by decide) (by decide)] using hby
  refine heapByteEff_seq_wsSafe_sub (P := fun t => ∀ x, t.locals.lookup x = s6.locals.lookup x) heff6
    (ecCal2Base_wsSafe heff6.arena.1.code heff6.arena.1.memaddrs hsum6 hbase_sum rfl rfl)
    (fun i hi _ => Or.inl (ptIvls_cover hsum_in6 i hi))
    (fun hn _ x => wsSafe_call_void_locals hn x) ?_ hnt7 hres7
  intro s7 heff7 hloc7 hnt8 hres8
  have hsum7 : PtFrame s7 (ofString "sum") hp := by unfold PtFrame; rw [hloc7]; exact hsum6
  refine heapByteEff_seq_wsSafe_sub (P := fun t => ∀ x, t.locals.lookup x = s6.locals.lookup x) heff7
    (ecCal2Full_wsSafe heff7.arena.1.code heff7.arena.1.memaddrs hsum7 hbase_sum (by decide) rfl)
    (fun i hi _ => Or.inl (ptIvls_cover hsum_in6 i hi))
    (fun hn _ x => (wsSafe_call_void_locals hn x).trans (hloc7 x)) ?_ hnt8 hres8
  intro s8 heff8 hloc8 hnt9 hres9
  refine heapByteEff_decCall_ro heff8 (by decide) ?_ hnt9 hres9
  intro v9 cp9 s9 _ _ _ hloc9 heff9 hnt10 hres10
  have hsum9 : PtFrame s9 (ofString "sum") hp := by
    unfold PtFrame; rw [hloc9 (ofString "sum") (by decide), hloc8]; exact hsum6
  refine heapByteEff_seq_ite_skip (P := fun t => ∀ x, x ≠ ofString "sum_inf" → t.locals.lookup x = s6.locals.lookup x)
    heff9 (fun x hx => by rw [hloc9 x hx, hloc8])
    (fun _ hory => by
      have hs_toa := ecCal1Full_wsSafe (fname := ofString "ec_to_affine")
        (e := ExpHOL.var VarKind.local (ofString "sum"))
        heff9.arena.1.code heff9.arena.1.memaddrs hsum9 hbase_sum (by decide) rfl
      refine ⟨heapByteEff_step_of_wsSafe heff9 hs_toa
        (fun i hi _ => Or.inl (ptIvls_cover hsum_in6 i hi)) hory, fun hn x hx => ?_⟩
      rw [wsSafe_call_void_locals hn x, hloc9 x hx, hloc8])
    ?_ hnt10 hres10
  intro s10 heff10 hloc10 hnt11 hres11
  refine heapByteEff_dec heff10 ?_ hnt11 hres11
  intro vsx _ hsh_sx mid11 heff11 hnt12 hres12
  refine heapByteEff_dec heff11 ?_ hnt12 hres12
  intro vsy _ hsh_sy s12 heff12 hnt13 hres13
  obtain ⟨sx0, sx1, sx2, sx3, rfl⟩ := eval_comb4_of_shape (v := vsx) (Or.inl hsh_sx)
  obtain ⟨sy0, sy1, sy2, sy3, rfl⟩ := eval_comb4_of_shape (v := vsy) (Or.inl hsh_sy)
  have hkeep12 : ∀ x, x ≠ ofString "sy" → x ≠ ofString "sx" → x ≠ ofString "sum_inf" →
      s12.locals.lookup x = s6.locals.lookup x := by
    intro x h1 h2 h3
    simp only [s12, mid11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, beq_iff_eq, Ne.symm h1, Ne.symm h2, ↓reduceIte]
    exact hloc10 x h3
  have hi12 : EcPtInv s12 (ofString "out") base
      [ofString "sx", ofString "sy", ofString "ax", ofString "ay", ofString "bx", ofString "by"] [] := by
    refine ⟨heff12.arena.1.code, heff12.arena.1.memaddrs, ?_, ?_, by simp⟩
    · unfold PtFrame; rw [hkeep12 (ofString "out") (by decide) (by decide) (by decide)]; exact hout_s6
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨sx0, sx1, sx2, sx3, by
          simp [s12, mid11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "sy" ≠ ofString "sx" by decide]⟩
      · exact ⟨sy0, sy1, sy2, sy3, by
          simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · simpa [comb4Val, hkeep12 (ofString "ax") (by decide) (by decide) (by decide)] using hax_s6
      · simpa [comb4Val, hkeep12 (ofString "ay") (by decide) (by decide) (by decide)] using hay_s6
      · simpa [comb4Val, hkeep12 (ofString "bx") (by decide) (by decide) (by decide)] using hbx_s6
      · simpa [comb4Val, hkeep12 (ofString "by") (by decide) (by decide) (by decide)] using hby_s6
  have hmark12 : s12.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hkeep12 (ofString "mark") (by decide) (by decide) (by decide)]; exact hmark_s6
  exact ec_mul2_tail_heapByteEff_gen heff12 hi12 hbase hout6 hmark12 hm_lo hm_sb hm_hi hm8 hgw hnt13 hres13

private theorem heapByteEff_call_void {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : MlS} {args : List (ExpHOL 64)}
    (heff : HeapByteEff s0 s Rl gw)
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 →
      HeapByteEff (callEntryStateHOLFinite s callee)
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hres : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl gw := by
  rw [evaluateHOLFiniteState_call] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [hargs] at hnt hres ⊢; exact heff
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · simp only [hl] at hnt hres ⊢; exact heff
    · simp only [hl] at hnt hres ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte] at hnt; simp at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cp⟩
        simp only [hr] at hnt hres ⊢
        have hstep : Resumes rb → HeapByteEff s0 cp Rl gw := by
          intro hresume
          have hh := hcal vals body callee rs hargs hl hz
            (by rw [hr]; intro he; subst he; exact hnt rfl) (by rw [hr]; exact hresume)
          rw [hr] at hh
          exact (heff.locals_clock callee (s.clock - 1)).trans hh
        cases rb with
        | none =>
          rcases hres with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hres ⊢
            split
            · exact (hstep (Or.inl ⟨v, rfl⟩)).locals_clock _ cp.clock
            · exact hstep (Or.inl ⟨v, rfl⟩)
          | exception eid ev =>
            dsimp only at hnt hres ⊢
            have hresume : Resumes (some (.exception eid ev)) := by
              rcases hres with h | h
              · simp at h
              · exact h
            exact (hstep hresume).locals_clock _ cp.clock
          | timeOut => simp at hnt
          | error | «break» | «continue» | finalFfi _ =>
            rcases hres with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem lookup_ec_mul2_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ec_mul2") vals = some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_ec_mul2 ∧
    ∃ (w : BitVec 64) (rest : List (ValueHOL 64)), vals = .val (.word w) :: rest ∧
      callee.lookup (ofString "out") = some (.val (.word w)) ∧
      (∀ nm ∈ [ofString "ax", ofString "ay", ofString "bx", ofString "by"],
        ∃ a b c d : BitVec 64, callee.lookup nm =
          some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  rw [lookupCodeHOLExact, lookup_ec_mul2] at hraw
  dsimp only at hraw
  rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, rest⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length] at hraw; split at hraw <;> [omega; simp at hraw])
  cases rest with
  | cons _ _ =>
    simp only [List.length, Nat.add_eq] at hraw
    split at hraw
    · omega
    · simp at hraw
  | nil =>
    simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hsh
      have hinj := Option.some.inj hraw
      have hb := (Prod.mk.inj hinj).1.symm
      have hfn := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w, rfl⟩ := eval_word_of_shape_one (Or.inl hsh.2.2.1)
      obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inl hsh.2.2.2.2.1)
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hsh.2.2.2.2.2.1)
      obtain ⟨c0, c1, c2, c3, rfl⟩ := eval_comb4_of_shape (Or.inl hsh.2.2.2.2.2.2.2.1)
      obtain ⟨d0, d1, d2, d3, rfl⟩ := eval_comb4_of_shape (Or.inl hsh.2.2.2.2.2.2.2.2)
      refine ⟨hb, w, _, rfl, ?_, ?_⟩
      · exact congrFun hfn (ofString "out")
      · intro nm hnm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
        rcases hnm with rfl | rfl | rfl | rfl
        · exact ⟨a0, a1, a2, a3, congrFun hfn (ofString "ax")⟩
        · exact ⟨b0, b1, b2, b3, congrFun hfn (ofString "ay")⟩
        · exact ⟨c0, c1, c2, c3, congrFun hfn (ofString "bx")⟩
        · exact ⟨d0, d1, d2, d3, congrFun hfn (ofString "by")⟩
    · simp at hraw

private theorem ec_mul2_call_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {base : BitVec 64} {Rl : List Ivl} {gw : List String}
    {dst : ExpHOL 64} {args : List (ExpHOL 64)}
    (heff : HeapByteEff s0 s Rl gw) (hgw : "heap_ptr" ∈ gw)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word base)))
    (hbase : base.toNat + 96 ≤ heapEnd)
    (hout : ∃ j ∈ Rl, j.1 ≤ base.toNat ∧ base.toNat + 96 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ec_mul2") (dst :: args))).1 ≠ some .timeOut)
    (hres : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ec_mul2") (dst :: args))).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ec_mul2") (dst :: args))).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "ec_mul2") (dst :: args))).2 Rl gw := by
  refine heapByteEff_call_void heff (fun vals body callee rs hargs hl _ hntb hresb => ?_) hnt hres
  rw [heff.arena.1.code] at hl
  obtain ⟨rfl, w, rest, hv, hp, hc4⟩ := lookup_ec_mul2_locals hl
  rw [hv] at hargs
  have hw : w = base := by
    simp only [evalListHOLFinite, evalListHOLExact, hdst] at hargs
    rcases htail : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | tail
    · simp [htail] at hargs
    · simp only [htail, Option.map, Option.some.injEq, List.cons.injEq] at hargs
      exact (HolWordLab.word.inj (ValueHOL.val.inj hargs.1)).symm
  subst hw
  have hentry : ArenaReady (callEntryStateHOLFinite s callee) :=
    (HeapByteEff.refl heff.arena Rl gw).locals_clock callee (s.clock - 1) |>.arena
  exact ec_mul2_body_heapByteEff hentry hgw hp
    (hc4 (ofString "ax") (by simp)) (hc4 (ofString "ay") (by simp))
    (hc4 (ofString "bx") (by simp)) (hc4 (ofString "by") (by simp))
    hbase hout hntb hresb

private theorem u256_to_be32_call_wsSafe {F : Type}
    {s : PanSemStateFiniteExact 64 F} {out : BitVec 64} {value dst : ExpHOL 64}
    (hc : s.code = originalRuntimeCode) (hm : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word out)))
    (hbound : out.toNat + 32 ≤ heapEnd) :
    WsSafe s [(out.toNat, 32)] (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "u256_to_be32") [value, dst])) := by
  refine WsSafe.call_void fun vals body callee rs hargs hl _ => ?_
  rw [hc] at hl
  obtain ⟨rfl, va, w, rfl, hp⟩ := lookup_comb4_word_locals
    (by decide) lookup_u256_to_be32 hl
  have hw : w = out := by
    simp only [evalListHOLFinite, evalListHOLExact, hdst] at hargs
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) value with _ | vv
    · simp [hv] at hargs
    · simp only [hv, Option.map, Option.some.injEq, List.cons.injEq] at hargs
      exact (HolWordLab.word.inj (ValueHOL.val.inj hargs.2.1)).symm
  subst hw
  exact u256_to_be32_wsSafe_bound hc hm hp hbound

private theorem lookup_decompress_r_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "secp256k1_decompress_r") vals =
      some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_secp256k1_decompress_r ∧
    ∃ (vr vrec : ValueHOL 64) (w : BitVec 64), vals = [vr, vrec, .val (.word w)] ∧
      callee.lookup (ofString "out") = some (.val (.word w)) ∧
      (∃ r0 r1 r2 r3 : BitVec 64, callee.lookup (ofString "r") =
        some (.rStruct [.val (.word r0), .val (.word r1), .val (.word r2), .val (.word r3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  rw [lookupCodeHOLExact, lookup_secp256k1_decompress_r] at hraw
  dsimp only at hraw
  rcases vals with _ | ⟨vr, _ | ⟨vrec, _ | ⟨vout, rest⟩⟩⟩
  all_goals try (simp only [List.length] at hraw; split at hraw <;> [omega; simp at hraw])
  cases rest with
  | cons _ _ =>
    simp only [List.length, Nat.add_eq] at hraw
    split at hraw
    · omega
    · simp at hraw
  | nil =>
    simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hsh
      have hinj := Option.some.inj hraw
      have hb := (Prod.mk.inj hinj).1.symm
      have hfn := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨r0, r1, r2, r3, rfl⟩ := eval_comb4_of_shape (Or.inl hsh.2.2.1)
      obtain ⟨w, rfl⟩ := eval_word_of_shape_one (Or.inl hsh.2.2.2.2)
      refine ⟨hb, _, _, w, rfl, congrFun hfn (ofString "out"), r0, r1, r2, r3, ?_⟩
      exact congrFun hfn (ofString "r")
    · simp at hraw

private theorem lookup_fn_mul_callee
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fn_mul") vals =
      some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_fn_mul := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  rw [lookupCodeHOLExact, lookup_fn_mul] at hraw
  dsimp only at hraw
  split at hraw
  · exact (Prod.mk.inj (Option.some.inj hraw)).1.symm
  · simp at hraw

private theorem heapByteEff_dec_or {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcont : ∀ (v : ValueHOL 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      let mid := setVarHOLFinite nm v s
      HeapByteEff s0 mid Rl gw →
      ((evaluateHOLFiniteState mid cont).1 = none ∨ Resumes (evaluateHOLFiniteState mid cont).1) →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hor : (evaluateHOLFiniteState s (.dec nm sh init cont)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.dec nm sh init cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.dec nm sh init cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total] at hor ⊢
  dsimp only at hor ⊢
  rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | v
  · simp only [hv]; exact heff
  · simp only [hv] at hor ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hor ⊢
      set mid := setVarHOLFinite nm v s
      have heff_mid : HeapByteEff s0 mid Rl gw := heff.locals_clock _ s.clock
      have hor_mid : (evaluateHOLFiniteState mid cont).1 = none ∨
          Resumes (evaluateHOLFiniteState mid cont).1 := by
        simpa using hor
      exact (hcont v hv hsh heff_mid hor_mid).locals_clock _ _
    · simp only [hsh, ↓reduceIte]; exact heff

private theorem untypedGlobalBufIvls_eq_of_globalsKept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {gw : List String}
    (hgw : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hkeep : GlobalsKept gw s post) :
    untypedGlobalBufIvls post = untypedGlobalBufIvls s := by
  have hneq : ∀ name : String,
      ofString name ≠ ofString "heap_ptr" →
      ofString name ≠ ofString "scratch_ptr" →
      globN post name = globN s name := by
    intro name h1 h2
    refine (M13.globN_eq_of_lookup_eq (hkeep _ ?_)).symm
    intro hm
    obtain ⟨g, hg, heq⟩ := List.mem_map.1 hm
    rcases hgw g hg with rfl | rfl
    · exact h1 heq.symm
    · exact h2 heq.symm
  unfold untypedGlobalBufIvls
  dsimp only [List.map]
  rw [hneq "u256_ws" (by decide) (by decide),
      hneq "sk_buf" (by decide) (by decide),
      hneq "keccak_pad" (by decide) (by decide),
      hneq "keccak_st" (by decide) (by decide),
      hneq "mpt_nib_scratch" (by decide) (by decide)]

private theorem secp256k1_recover_body_heapByteEff {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {out : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0) (hgw : "heap_ptr" ∈ gw)
    (hgw_ok : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hws_bnd : globN s0 "u256_ws" = 0 ∨ globN s0 "u256_ws" + 640 ≤ 2 ^ 64)
    (hws_in : ∀ iv ∈ untypedGlobalBufIvls s0, 0 < iv.2 →
      ∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2)
    (hout_loc : s0.locals.lookup (ofString "out") = some (.val (.word out)))
    (hout_end : out.toNat + 64 ≤ heapEnd)
    (hout_in : ∃ j ∈ Rl, j.1 ≤ out.toNat ∧ out.toNat + 64 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_secp256k1_recover)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_secp256k1_recover)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_secp256k1_recover)).2 Rl gw := by
  have hb : sourceFnBody Guest.Software.guestFn_secp256k1_recover =
      FrontendCodecComputation.progToHOLStructural (extractFn Guest.Software.guestFn_secp256k1_recover).body := rfl
  rw [hb] at hnt hres ⊢
  dsimp only [extractFn, Guest.Software.guestFn_secp256k1_recover,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  have heff0 := HeapByteEff.refl hAR0 Rl gw
  refine heapByteEff_decCall_ro heff0 (by decide) ?_ hnt hres
  intro _ _ s1 _ _ _ hloc1 heff1 hnt1 hres1
  refine heapByteEff_seq_ite_return_skip heff1 ?_ hnt1 hres1
  intro hnt2 hres2
  refine heapByteEff_decCall_ro heff1 (by decide) ?_ hnt2 hres2
  intro _ _ s2 _ _ _ hloc2 heff2 hnt3 hres3
  refine heapByteEff_seq_ite_return_skip heff2 ?_ hnt3 hres3
  intro hnt4 hres4
  refine heapByteEff_decCall_ro heff2 (by decide) ?_ hnt4 hres4
  intro _ _ s3 _ _ _ hloc3 heff3 hnt5 hres5
  refine heapByteEff_seq_ite_return_skip heff3 ?_ hnt5 hres5
  intro hnt6 hres6
  refine heapByteEff_decCall_ro heff3 (by decide) ?_ hnt6 hres6
  intro _ _ s4 _ _ _ hloc4 heff4 hnt7 hres7
  refine heapByteEff_seq_ite_return_skip heff4 ?_ hnt7 hres7
  intro hnt8 hres8
  refine heapByteEff_decCall_heap_mark heff4 ?_ hnt8 hres8
  intro mark s5 _ hm_lo hm_sb hm_hi hm8 _ hmark5 hloc5 heff5 hnt9 hres9
  refine heapByteEff_decCall_alloc heff5 hgw ?_ hnt9 hres9
  intro pq npq _ s6 hnpq _ _ _ _ hpq_end hpq6 hloc6 heff6 hnt10 hres10
  have hnpq_eq : npq = 96#64 := by
    simp only [evalHOLExact] at hnpq
    injection hnpq with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
  subst hnpq_eq
  refine heapByteEff_decCall_alloc heff6 hgw ?_ hnt10 hres10
  intro pr npr _ s7 hnpr _ _ _ _ hpr_end hpr7 hloc7 heff7 hnt11 hres11
  have hnpr_eq : npr = 96#64 := by
    simp only [evalHOLExact] at hnpr
    injection hnpr with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
  subst hnpr_eq
  set Rl2 := (Rl ++ [(pq.toNat, (96#64 : BitVec 64).toNat)]) ++ [(pr.toNat, (96#64 : BitVec 64).toNat)]
  have hpq_bound : pq.toNat + 96 ≤ heapEnd := by simpa using hpq_end
  have hpr_bound : pr.toNat + 96 ≤ heapEnd := by simpa using hpr_end
  have hpq_in : ∃ j ∈ Rl2, j.1 ≤ pq.toNat ∧ pq.toNat + 96 ≤ j.1 + j.2 :=
    ⟨(pq.toNat, 96), List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)), le_rfl, le_rfl⟩
  have hpr_in : ∃ j ∈ Rl2, j.1 ≤ pr.toNat ∧ pr.toNat + 96 ≤ j.1 + j.2 :=
    ⟨(pr.toNat, 96), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩
  have hout_in2 : ∃ j ∈ Rl2, j.1 ≤ out.toNat ∧ out.toNat + 64 ≤ j.1 + j.2 := by
    obtain ⟨j, hj, hj1, hj2⟩ := hout_in
    exact ⟨j, List.mem_append_left _ (List.mem_append_left _ hj), hj1, hj2⟩
  have hout7 : s7.locals.lookup (ofString "out") = some (.val (.word out)) := by
    rw [hloc7 (ofString "out") (by decide), hloc6 (ofString "out") (by decide),
        hloc5 (ofString "out") (by decide), hloc4 (ofString "out") (by decide),
        hloc3 (ofString "out") (by decide), hloc2 (ofString "out") (by decide),
        hloc1 (ofString "out") (by decide)]
    exact hout_loc
  have hmark7 : s7.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hloc7 (ofString "mark") (by decide), hloc6 (ofString "mark") (by decide)]
    exact hmark5
  have hpq7 : s7.locals.lookup (ofString "pq") = some (.val (.word pq)) := by
    rw [hloc7 (ofString "pq") (by decide)]; exact hpq6
  refine heapByteEff_decCall_wsSafe (R1 := ptIvls pr) heff7
    (fun vals body callee rs hargs hl _ => ?_)
    (fun i hi _ => Or.inl (ptIvls_cover hpr_in i hi)) ?_ hnt11 hres11
  · rw [heff7.arena.1.code] at hl
    obtain ⟨rfl, vr, vrec, w, rfl, hp_cal, hr_cal⟩ := lookup_decompress_r_locals hl
    have hw : w = pr := by
      rcases h1 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
        (.var .local (ofString "r")) with _ | x1
      · simp [evalListHOLFinite, evalListHOLExact, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
          (.var .local (ofString "recid")) with _ | x2
        · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at hargs
        · have h3 := eval_local_word s7 "pr" pr hpr7
          simp only [evalListHOLFinite, evalListHOLExact, h1, h2, h3, Option.map,
            Option.some.injEq, List.cons.injEq] at hargs
          exact (HolWordLab.word.inj (ValueHOL.val.inj hargs.2.2.1)).symm
    subst hw
    exact secp256k1_decompress_r_wsSafe_bound heff7.arena.1.code heff7.arena.1.memaddrs hp_cal hr_cal hpr_bound
  intro _ _ s8 _ _ _ hloc8 heff8 hnt12 hres12
  have hmark8 : s8.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hloc8 (ofString "mark") (by decide)]; exact hmark7
  refine heapByteEff_seq_ite_release_return_skip heff8 hgw
    (eval_local_word s8 "mark" mark hmark8) hm_lo hm_sb hm_hi hm8 ?_ hnt12 hres12
  intro hnt13 hres13
  refine heapByteEff_dec heff8 ?_ hnt13 hres13
  intro vrx _ _ s9 heff9 hnt14 hres14
  refine heapByteEff_dec heff9 ?_ hnt14 hres14
  intro vry _ _ s10 heff10 hnt15 hres15
  refine heapByteEff_decCall_ro heff10 (by decide) ?_ hnt15 hres15
  intro _ _ s11 _ _ _ hloc11 heff11 hnt16 hres16
  refine heapByteEff_decCall_ro heff11 (by decide) ?_ hnt16 hres16
  intro _ _ s12 _ _ _ hloc12 heff12 hnt17 hres17
  have hkeep12 : ∀ x, x ≠ ofString "elt" → x ≠ ofString "e" → x ≠ ofString "ry" →
      x ≠ ofString "rx" → x ≠ ofString "okr" → s12.locals.lookup x = s7.locals.lookup x := by
    intro x h1 h2 h3 h4 h5
    rw [hloc12 x h1, hloc11 x h2]
    simp only [s10, s9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      beq_iff_eq, Ne.symm h3, Ne.symm h4, ↓reduceIte]
    exact hloc8 x h5
  refine heapByteEff_seq_ite_skip
    (P := fun t => ∀ x, x ≠ ofString "e" → t.locals.lookup x = s12.locals.lookup x)
    heff12 (fun _ _ => rfl)
    (fun _ hory => by
      have hs_sub := wsSafe_call_assign_local (s := s12) (Rl := []) (nm := ofString "e")
        (fname := ofString "u256_sub")
        (args := [.var .local (ofString "e"),
          .rstruct [.const 13822214165235122497#64, .const 13451932020343611451#64,
                    .const 18446744073709551614#64, .const 18446744073709551615#64]])
        (fun vals body callee rs _ hl _ => by
          have hc := heff12.arena.1.code; rw [hc] at hl
          exact wsSafe_of_recRo hc (recRoCallees_good _ (by decide) vals body callee rs hl))
      refine ⟨heapByteEff_step_of_wsSafe heff12 hs_sub.1 (fun _ hi => nomatch hi) hory, fun hn x hx => ?_⟩
      exact hs_sub.2 x hx hn)
    ?_ hnt17 hres17
  intro s13 heff13 hloc13 hnt18 hres18
  refine heapByteEff_decCall_ro heff13 (by decide) ?_ hnt18 hres18
  intro _ _ s14 _ _ _ hloc14 heff14 hnt19 hres19
  refine heapByteEff_dec heff14 ?_ hnt19 hres19
  intro _ _ _ s15 heff15 hnt20 hres20
  refine heapByteEff_decCall_ro heff15 (by decide) ?_ hnt20 hres20
  intro _ _ s16 _ _ _ hloc16 heff16 hnt21 hres21
  refine heapByteEff_seq_ite_skip
    (P := fun t => ∀ x, x ≠ ofString "nege" → t.locals.lookup x = s16.locals.lookup x)
    heff16 (fun _ _ => rfl)
    (fun _ hory => by
      have hs_sub := wsSafe_call_assign_local (s := s16) (Rl := []) (nm := ofString "nege")
        (fname := ofString "u256_sub")
        (args := [.rstruct [.const 13822214165235122497#64, .const 13451932020343611451#64,
                            .const 18446744073709551614#64, .const 18446744073709551615#64],
                  .var .local (ofString "e")])
        (fun vals body callee rs _ hl _ => by
          have hc := heff16.arena.1.code; rw [hc] at hl
          exact wsSafe_of_recRo hc (recRoCallees_good _ (by decide) vals body callee rs hl))
      refine ⟨heapByteEff_step_of_wsSafe heff16 hs_sub.1 (fun _ hi => nomatch hi) hory, fun hn x hx => ?_⟩
      exact hs_sub.2 x hx hn)
    ?_ hnt21 hres21
  intro s17 heff17 hloc17 hnt22 hres22
  have hkeep17 : ∀ x, x ≠ ofString "nege" → x ≠ ofString "ez" → x ≠ ofString "rinv" →
      x ≠ ofString "elt" → x ≠ ofString "e" → x ≠ ofString "ry" →
      x ≠ ofString "rx" → x ≠ ofString "okr" → s17.locals.lookup x = s7.locals.lookup x := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8
    rw [hloc17 x h1, hloc16 x h2]
    simp only [s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      beq_iff_eq, Ne.symm h1, ↓reduceIte]
    rw [hloc14 x h3, hloc13 x h5]
    exact hkeep12 x h4 h5 h6 h7 h8
  have hgw_ws : ofString "u256_ws" ∉ gw.map ofString := by
    intro hm
    obtain ⟨g, hg, heq⟩ := List.mem_map.1 hm
    rcases hgw_ok g hg with rfl | rfl <;> exact absurd heq (by decide)
  have hws17_eq : globN s17 "u256_ws" = globN s0 "u256_ws" :=
    (M13.globN_eq_of_lookup_eq (heff17.globals (ofString "u256_ws") hgw_ws)).symm
  have hws17_env : WsEnv s17 s17 :=
    ⟨heff17.arena.1.code, heff17.arena.1.memaddrs, rfl, by rw [hws17_eq]; exact hws_bnd⟩
  have hws17_in : ∀ iv ∈ untypedGlobalBufIvls s17, 0 < iv.2 →
      (∃ j ∈ Rl2, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN s17 "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s17 "scratch_ptr") ∨
      (globN s17 "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit) := by
    intro iv hiv hpos
    rw [untypedGlobalBufIvls_eq_of_globalsKept hgw_ok heff17.globals] at hiv
    obtain ⟨j, hj, hj1, hj2⟩ := hws_in iv hiv hpos
    exact Or.inl ⟨j, List.mem_append_left _ (List.mem_append_left _ hj), hj1, hj2⟩
  refine heapByteEff_decCall_wsSafe (R1 := untypedGlobalBufIvls s17) heff17
    (fun vals body callee rs _ hl _ => by
      have hc := heff17.arena.1.code; rw [hc] at hl
      rw [lookup_fn_mul_callee hl]
      exact fn_mul_wsSafe (hws17_env.with_locals_clock callee _))
    hws17_in ?_ hnt22 hres22
  intro _ _ s18 _ hg18 _ hloc18 heff18 hnt23 hres23
  have hws18_eq : globN s18 "u256_ws" = globN s17 "u256_ws" := by simp [globN, hg18]
  have hws18_env : WsEnv s18 s18 :=
    ⟨heff18.arena.1.code, heff18.arena.1.memaddrs, rfl,
      by rw [hws18_eq, hws17_eq]; exact hws_bnd⟩
  have hws18_in : ∀ iv ∈ untypedGlobalBufIvls s18, 0 < iv.2 →
      (∃ j ∈ Rl2, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN s18 "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s18 "scratch_ptr") ∨
      (globN s18 "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit) := by
    intro iv hiv hpos
    rw [untypedGlobalBufIvls_eq_of_globalsKept hgw_ok heff18.globals] at hiv
    obtain ⟨j, hj, hj1, hj2⟩ := hws_in iv hiv hpos
    exact Or.inl ⟨j, List.mem_append_left _ (List.mem_append_left _ hj), hj1, hj2⟩
  refine heapByteEff_decCall_wsSafe (R1 := untypedGlobalBufIvls s18) heff18
    (fun vals body callee rs _ hl _ => by
      have hc := heff18.arena.1.code; rw [hc] at hl
      rw [lookup_fn_mul_callee hl]
      exact fn_mul_wsSafe (hws18_env.with_locals_clock callee _))
    hws18_in ?_ hnt23 hres23
  intro _ _ s19 _ _ _ hloc19 heff19 hnt24 hres24
  have hkeep19 : ∀ x, x ≠ ofString "u2" → x ≠ ofString "u1" →
      x ≠ ofString "nege" → x ≠ ofString "ez" → x ≠ ofString "rinv" →
      x ≠ ofString "elt" → x ≠ ofString "e" → x ≠ ofString "ry" →
      x ≠ ofString "rx" → x ≠ ofString "okr" → s19.locals.lookup x = s7.locals.lookup x := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [hloc19 x h1, hloc18 x h2]
    exact hkeep17 x h3 h4 h5 h6 h7 h8 h9 h10
  have hpq19 : s19.locals.lookup (ofString "pq") = some (.val (.word pq)) := by
    rw [hkeep19 (ofString "pq") (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hpq7
  rw [evaluateHOLFiniteState_seq_line780] at hnt24 hres24 ⊢
  rcases hmul : evaluateHOLFiniteState s19
    (.call (some (none, none)) (ofString "ec_mul2")
      [.var .local (ofString "pq"), .var .local (ofString "u1"),
       .rstruct [.const 6481385041966929816#64, .const 188021827762530521#64,
                 .const 6170039885052185351#64, .const 8772561819708210092#64],
       .rstruct [.const 11261198710074299576#64, .const 18237243440184513561#64,
                 .const 6747795201694173352#64, .const 5204712524664259685#64],
       .var .local (ofString "u2"), .var .local (ofString "rx"), .var .local (ofString "ry")]) with ⟨rmul, s20⟩
  have hnt_mul : rmul ≠ some .timeOut := by
    rintro rfl; rw [hmul] at hnt24; exact hnt24 rfl
  have hor_mul : rmul = none ∨ Resumes rmul := by
    cases rmul with
    | none => exact Or.inl rfl
    | some _ => right; rw [hmul] at hres24; exact hres24
  have heff20_raw := ec_mul2_call_heapByteEff heff19 hgw
    (eval_local_word s19 "pq" pq hpq19) hpq_bound hpq_in
    (by rw [hmul]; exact hnt_mul) (by rw [hmul]; exact hor_mul)
  rw [hmul] at heff20_raw
  dsimp only at heff20_raw
  simp only [hmul] at hnt24 hres24 ⊢
  cases rmul with
  | some _ => exact heff20_raw
  | none =>
    have hloc20 : ∀ x, s20.locals.lookup x = s19.locals.lookup x := fun x => by
      have hh := wsSafe_call_void_locals (s := s19)
        (fname := ofString "ec_mul2")
        (args := [.var .local (ofString "pq"), .var .local (ofString "u1"),
          .rstruct [.const 6481385041966929816#64, .const 188021827762530521#64,
                    .const 6170039885052185351#64, .const 8772561819708210092#64],
          .rstruct [.const 11261198710074299576#64, .const 18237243440184513561#64,
                    .const 6747795201694173352#64, .const 5204712524664259685#64],
          .var .local (ofString "u2"), .var .local (ofString "rx"), .var .local (ofString "ry")])
        (by rw [hmul]) x
      simpa [hmul] using hh
    have hpq20 : PtFrame s20 (ofString "pq") pq := by
      unfold PtFrame; rw [hloc20]; exact hpq19
    refine heapByteEff_decCall_wsSafe (R1 := ptIvls pq) heff20_raw
      (fun vals body callee rs hargs hl _ => by
        obtain ⟨v, hv, rfl⟩ := evalList_one_eq' hargs
        have hve := isLocalVarEq_eval hpq20 (ptVar := ofString "pq") rfl hv
        subst hve
        have hc := heff20_raw.arena.1.code; rw [hc] at hl
        obtain ⟨rfl, w, hvals, hp⟩ := lookup_one_word_local' lookup_ec_to_affine hl
        have hw : w = pq := by simpa using hvals.symm
        subst hw
        exact ec_to_affine_wsSafe_bound hc heff20_raw.arena.1.memaddrs hp hpq_bound)
      (fun i hi _ => Or.inl (ptIvls_cover hpq_in i hi)) ?_ hnt24 hres24
    intro _ _ s21 _ _ _ hloc21 heff21 hnt25 hres25
    have hmark21 : s21.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      rw [hloc21 (ofString "mark") (by decide), hloc20,
          hkeep19 (ofString "mark") (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmark7
    have hout21 : s21.locals.lookup (ofString "out") = some (.val (.word out)) := by
      rw [hloc21 (ofString "out") (by decide), hloc20,
          hkeep19 (ofString "out") (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hout7
    refine heapByteEff_seq_ite_skip
      (P := fun t => t.locals.lookup (ofString "mark") = some (.val (.word mark)))
      heff21 hmark21
      (fun hnt_yes hory => ?_)
      (fun s22 heff22 hmark22 hnt26 _ =>
        (heapByteEff_release_return heff22 hgw
          (eval_local_word s22 "mark" mark hmark22) hm_lo hm_sb hm_hi hm8 hnt26).1)
      hnt25 hres25
    have hna_yes : notAssignedLocal (ofString "mark")
      (.dec (ofString "qx")
        (.comb (FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one, .one]))
        (.load (.comb (FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one, .one]))
          (.var .local (ofString "pq")))
        (.dec (ofString "qy")
          (.comb (FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one, .one]))
          (.load (.comb (FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one, .one]))
            (.op .add [.var .local (ofString "pq"), .const 32#64]))
          (.seq
            (.call (some (none, none)) (ofString "u256_to_be32")
              [.var .local (ofString "qx"), .var .local (ofString "out")])
            (.call (some (none, none)) (ofString "u256_to_be32")
              [.var .local (ofString "qy"), .op .add [.var .local (ofString "out"), .const 32#64]])))) = true := by
      decide
    refine ⟨?_, fun hn => (evaluate_notAssignedLocal _ hna_yes s21 (by rw [hn]; rfl)).trans hmark21⟩
    clear hna_yes hnt_yes
    have hout32_end : (out + 32#64).toNat + 32 ≤ heapEnd := by
      have h264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
      have hnat := bv_add_off_nat_gen out 32 (by omega) (by omega)
      omega
    have hout_lo : ∃ j ∈ Rl2, j.1 ≤ out.toNat ∧ out.toNat + 32 ≤ j.1 + j.2 := by
      obtain ⟨j, hj, h1, h2⟩ := hout_in2; exact ⟨j, hj, h1, by omega⟩
    have hout_hi : ∃ j ∈ Rl2, j.1 ≤ (out + 32#64).toNat ∧ (out + 32#64).toNat + 32 ≤ j.1 + j.2 := by
      have h264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
      have hnat := bv_add_off_nat_gen out 32 (by omega) (by omega)
      obtain ⟨j, hj, h1, h2⟩ := hout_in2
      exact ⟨j, hj, by omega, by omega⟩
    have hbe_pair : ∀ (u : PanSemStateFiniteExact 64 F),
        HeapByteEff s0 u Rl2 gw →
        u.locals.lookup (ofString "out") = some (.val (.word out)) →
        let pairProg : ProgHOL 64 := .seq
          (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "qx"), .var .local (ofString "out")])
          (.call (some (none, none)) (ofString "u256_to_be32")
            [.var .local (ofString "qy"), .op .add [.var .local (ofString "out"), .const 32#64]])
        (evaluateHOLFiniteState u pairProg).1 = none ∨ Resumes (evaluateHOLFiniteState u pairProg).1 →
        HeapByteEff s0 (evaluateHOLFiniteState u pairProg).2 Rl2 gw := by
      intro u heffu houtu pairProg horp
      dsimp only [pairProg] at horp ⊢
      rw [evaluateHOLFiniteState_seq_line780] at horp ⊢
      rcases hc1 : evaluateHOLFiniteState u
        (.call (some (none, none)) (ofString "u256_to_be32")
          [.var .local (ofString "qx"), .var .local (ofString "out")]) with ⟨rc1, u1⟩
      have hor1 : rc1 = none ∨ Resumes rc1 := by
        cases rc1 with
        | none => exact Or.inl rfl
        | some _ => simp only [hc1] at horp; exact horp
      have hs1 := u256_to_be32_call_wsSafe (value := .var .local (ofString "qx"))
        heffu.arena.1.code heffu.arena.1.memaddrs
        (eval_local_word u "out" out houtu) (by omega)
      have heff_u1 := heapByteEff_step_of_wsSafe heffu hs1
        (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl hout_lo)
        (by rw [hc1]; exact hor1)
      rw [hc1] at heff_u1; dsimp only at heff_u1
      simp only [hc1] at horp ⊢
      cases rc1 with
      | some _ => exact heff_u1
      | none =>
        have hout_u1 : u1.locals.lookup (ofString "out") = some (.val (.word out)) := by
          have hh := wsSafe_call_void_locals (s := u) (fname := ofString "u256_to_be32")
            (args := [.var .local (ofString "qx"), .var .local (ofString "out")])
            (by rw [hc1]) (ofString "out")
          simpa [hc1] using hh.trans houtu
        have hs2 := u256_to_be32_call_wsSafe (value := .var .local (ofString "qy"))
          heff_u1.arena.1.code heff_u1.arena.1.memaddrs
          (eval_local_add_const u1 "out" out 32 hout_u1) hout32_end
        exact heapByteEff_step_of_wsSafe heff_u1 hs2
          (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl hout_hi)
          horp
    refine heapByteEff_dec_or heff21 ?_ hory
    intro vqx _ _ u_qx heff_qx hor_qx
    have hout_qx : u_qx.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [u_qx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "qx" ≠ ofString "out" by decide, hout21]
    refine heapByteEff_dec_or heff_qx ?_ hor_qx
    intro vqy _ _ u_qy heff_qy hor_qy
    have hout_qy : u_qy.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [u_qy, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "qy" ≠ ofString "out" by decide, hout_qx]
    exact hbe_pair u_qy heff_qy hout_qy hor_qy

private theorem heapByteEff_decCall {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {nm fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw)
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 →
      HeapByteEff s (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 Rl gw)
    (hcont : ∀ (v : ValueHOL 64) (cp : PanSemStateFiniteExact 64 F),
      let mid := setVarHOLFinite nm v { cp with locals := s.locals }
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      mid.locals.lookup nm = some v →
      (∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).2 Rl gw := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [hargs] at hnt hres ⊢; exact heff
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · simp only [hl] at hnt hres ⊢; exact heff
    · simp only [hl] at hnt hres ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte] at hnt; simp at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cp⟩
        have hc := hcal vals body callee rs hargs hl hz
        rw [hrun] at hc
        simp only [hrun] at hnt hres ⊢
        cases rb with
        | none =>
          simp at hres; exact False.elim (not_resumes_error hres)
        | some r0 =>
          cases r0 with
          | returned v =>
            dsimp only at hnt hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) rs) = true
            · simp only [hsh, ↓reduceIte] at hnt hres ⊢
              have hsh2 := (Bool.and_eq_true_iff.1 hsh).1
              have heff_cp : HeapByteEff s0 cp Rl gw :=
                heff.trans (hc (by simp) (Or.inl ⟨v, rfl⟩))
              set mid := setVarHOLFinite nm v { cp with locals := s.locals }
              have heff_mid : HeapByteEff s0 mid Rl gw := heff_cp.locals_clock _ cp.clock
              have hloc_nm : mid.locals.lookup nm = some v := by
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hloc_other : ∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x := by
                intro x hne
                simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
              exact heapByteEff_restoreLocal
                (hcont v cp hsh2 hloc_nm hloc_other heff_mid hnt hres)
                nm (s.locals.lookup nm)
            · simp only [hsh, ↓reduceIte] at hres; exact False.elim (not_resumes_error hres)
          | exception eid ev =>
            dsimp only at hres ⊢
            rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h'; injection h' with h1 h2; subst h1 h2
              have heff_cp : HeapByteEff s0 cp Rl gw :=
                heff.trans (hc (by simp) (Or.inr ⟨eid, ev, rfl, hne⟩))
              exact heff_cp.locals_clock _ cp.clock
          | timeOut => simp at hnt
          | error | «break» | «continue» =>
            simp at hres; exact False.elim (not_resumes_error hres)
          | finalFfi _ =>
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem lookup_secp256k1_recover_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "secp256k1_recover") vals =
      some (body, callee, rs)) :
    body = sourceFnBody Guest.Software.guestFn_secp256k1_recover ∧
    ∃ (v0 v1 v2 v3 : ValueHOL 64) (w : BitVec 64),
      vals = [v0, v1, v2, v3, .val (.word w)] ∧
      callee.lookup (ofString "out") = some (.val (.word w)) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  rw [lookupCodeHOLExact, lookup_secp256k1_recover] at hraw
  dsimp only at hraw
  rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, rest⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length] at hraw; split at hraw <;> [omega; simp at hraw])
  cases rest with
  | cons _ _ =>
    simp only [List.length, Nat.add_eq] at hraw
    split at hraw
    · omega
    · simp at hraw
  | nil =>
    simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hsh
      have hinj := Option.some.inj hraw
      have hb := (Prod.mk.inj hinj).1.symm
      have hfn := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨w, rfl⟩ := eval_word_of_shape_one (Or.inl hsh.2.2.2.2.2.2)
      exact ⟨hb, v0, v1, v2, v3, w, rfl, congrFun hfn (ofString "out")⟩
    · simp at hraw

private theorem secp256k1_recover_decCall_heapByteEff {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {nm : MlS} {e_mh e_r e_s e_rec e_out : ExpHOL 64} {out : BitVec 64} {cont : ProgHOL 64}
    (heff : HeapByteEff s0 s Rl gw) (hgw : "heap_ptr" ∈ gw)
    (hgw_ok : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hws_bnd : globN s "u256_ws" = 0 ∨ globN s "u256_ws" + 640 ≤ 2 ^ 64)
    (hws_in : ∀ iv ∈ untypedGlobalBufIvls s, 0 < iv.2 →
      ∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2)
    (hout_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e_out =
      some (.val (.word out)))
    (hout_end : out.toNat + 64 ≤ heapEnd)
    (hout_in : ∃ j ∈ Rl, j.1 ≤ out.toNat ∧ out.toNat + 64 ≤ j.1 + j.2)
    (hcont : ∀ (v : ValueHOL 64) (cp : PanSemStateFiniteExact 64 F),
      let mid := setVarHOLFinite nm v { cp with locals := s.locals }
      shapeEqHOL (shapeOfHOLExact v) .one = true →
      mid.locals.lookup nm = some v →
      (∀ x, x ≠ nm → mid.locals.lookup x = s.locals.lookup x) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall nm .one (ofString "secp256k1_recover") [e_mh, e_r, e_s, e_rec, e_out] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall nm .one (ofString "secp256k1_recover") [e_mh, e_r, e_s, e_rec, e_out] cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.decCall nm .one (ofString "secp256k1_recover") [e_mh, e_r, e_s, e_rec, e_out] cont)).2 Rl gw := by
  refine heapByteEff_decCall heff ?_ hcont hnt hres
  intro vals body callee rs hargs hl _ hnt_b hres_b
  rw [heff.arena.1.code] at hl
  obtain ⟨rfl, v0, v1, v2, v3, w, rfl, hout_cal⟩ := lookup_secp256k1_recover_locals hl
  have hw : w = out := by
    rcases h0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e_mh with _ | x0
    · simp [evalListHOLFinite, evalListHOLExact, h0] at hargs
    · rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e_r with _ | x1
      · simp [evalListHOLFinite, evalListHOLExact, h0, h1] at hargs
      · rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e_s with _ | x2
        · simp [evalListHOLFinite, evalListHOLExact, h0, h1, h2] at hargs
        · rcases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e_rec with _ | x3
          · simp [evalListHOLFinite, evalListHOLExact, h0, h1, h2, h3] at hargs
          · simp only [evalListHOLFinite, evalListHOLExact, h0, h1, h2, h3, hout_ev, Option.map,
              Option.some.injEq, List.cons.injEq] at hargs
            exact (HolWordLab.word.inj (ValueHOL.val.inj hargs.2.2.2.2.1)).symm
  subst hw
  have heff_entry : HeapByteEff s (callEntryStateHOLFinite s callee) Rl gw :=
    (HeapByteEff.refl heff.arena Rl gw).locals_clock callee (s.clock - 1)
  have hbody := secp256k1_recover_body_heapByteEff heff_entry.arena hgw hgw_ok
    hws_bnd hws_in hout_cal hout_end hout_in hnt_b hres_b
  exact heff_entry.trans hbody

end InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
