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

private theorem heapByteEff_decCall_rlp_encode_bytes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64)
    (heff : HeapByteEff s0 s Rl gw)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin : ∃ iv ∈ Rl, iv.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ iv.1 + iv.2)
    (hcont : ∀ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat →
      mid.globals = s.globals →
      mid.locals = s.locals.update (ofString lname, .val (.word len)) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).2 Rl gw := by
  obtain ⟨len, mid, hlen, _, hg, hl, hm, hntm, hresm, hout⟩ :=
    eval_decCall_rlp_encode_bytes s lname dstExp srcExp nExp dst0 src0 n0 cont Rl gw
      heff.arena.1.code heff.arena hdst hsrc hn hin hnt hres
  rw [hout]
  exact heapByteEff_restoreLocal
    (hcont len mid hlen hg hl (heff.trans hm) hntm hresm)
    (ofString lname) (s.locals.lookup (ofString lname))

private theorem heapByteEff_decCall_rlp_encode_list_header {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (lname : String) (dstExp pExp : ExpHOL 64)
    (dst0 pw : BitVec 64) (cont : ProgHOL 64)
    (heff : HeapByteEff s0 s Rl gw)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hin : ∃ iv ∈ Rl, iv.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure pw.toNat ≤ iv.1 + iv.2)
    (hcont : ∀ (hl : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      hl.toNat = rlpHeaderLenPure pw.toNat →
      1 ≤ hl.toNat → hl.toNat ≤ 9 →
      mid.globals = s.globals →
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) →
      HeapByteEff s0 mid Rl gw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid cont).1 →
      HeapByteEff s0 (evaluateHOLFiniteState mid cont).2 Rl gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).1) :
    HeapByteEff s0 (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).2 Rl gw := by
  obtain ⟨mid, hhl_nat, h1, h9, _, hg, hl_loc, hm, hntm, hresm, hout⟩ :=
    eval_decCall_rlp_encode_list_header s lname dstExp pExp dst0 pw cont Rl gw
      heff.arena.1.code heff.arena hdst hp hin hnt hres
  rw [hout]
  exact heapByteEff_restoreLocal
    (hcont (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)) mid hhl_nat h1 h9 hg hl_loc (heff.trans hm) hntm hresm)
    (ofString lname) (s.locals.lookup (ofString lname))

private theorem eval_call_local_rlp_encode_list_header {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp pExp : ExpHOL 64)
    (dst0 pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure pw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_list_header")
        [dstExp, pExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_list_header")
        [dstExp, pExp])
    (out.1 = none →
      ∃ hl : BitVec 64,
        hl.toNat = rlpHeaderLenPure pw.toNat ∧ 1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hb_elh : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
      .call none (ofString "rlp_write_header")
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pExp] = some [.val (.word dst0), .val (.word pw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hp]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 pw (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_list_header)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_len", ValueHOL.val (.word pw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_len" ≠ ofString "dst" by decide]
    have hent_p : ent.locals.lookup (ofString "payload_len") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hb_elh, evaluateHOLFiniteState_call] at hnt ⊢
    have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] =
        some [.val (.word dst0), .val (.word 192), .val (.word pw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_p]
    have hlk2 := pan_three_word_lookup ent.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 192 pw
      (by decide) (by decide) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact M11.lookup_rlp_write_header)
    simp only [ha2, hlk2] at hnt ⊢
    by_cases hcz2 : ent.clock = 0
    · simp [hcz2] at hnt
    · simp only [hcz2, ↓reduceIte] at hnt ⊢
      set cmap2 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 192))).update (ofString "n", ValueHOL.val (.word pw))
      set ent2 := callEntryStateHOLFinite ent cmap2
      have hent2_dst : ent2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent2_base : ent2.locals.lookup (ofString "base") = some (.val (.word 192)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word pw)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hwh : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; rw [hwh] at hnt; exact hnt rfl
      obtain ⟨hret, hnonret⟩ := eval_rlp_write_header_body_exact ent2 dst0 192 pw Rl
        hcode hAR.1.memaddrs hent2_dst hent2_base hent2_n hin_ivl (by rw [hwh]; exact hnt_wh)
      rw [hwh] at hret hnonret
      dsimp only at hret hnonret
      simp only [hwh] at hnt ⊢
      cases rwh with
      | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
        | returned rv =>
          obtain ⟨rfl, hdst_lt_he, heff_wh⟩ := hret rv rfl
          set hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word hl)) = true := by
            simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
          dsimp only
          rw [if_pos hsh]; dsimp only; rw [if_pos hsh]; rw [if_pos hval]
          let mid := setVarHOLFinite (ofString lname) (.val (.word hl))
            { swh.emptyLocalsHOLFinite with locals := s.locals }
          have heff0 : M11.ByteRegionEffect s ent2 Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent2.locals ent2.clock
          have heff_mid : M11.ByteRegionEffect s mid Rl :=
            ((heff0.trans heff_wh).with_locals_clock _ _).with_locals_clock mid.locals mid.clock
          have hbnd := rlpHeaderLenPure_bounds pw.toNat
          have hhl_nat : hl.toNat = rlpHeaderLenPure pw.toNat := by
            dsimp [hl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          exact ⟨fun _ => ⟨hl, hhl_nat, by omega, by omega, hdst_lt_he, heff_mid.globals, rfl,
            HeapByteEff.of_m11_bre hAR heff_mid⟩,
            fun h => False.elim (h rfl)⟩
        | «break» | «continue» | error =>
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem tx_encode_bound_cursor_slack
    (buf data_n al au bh p : Nat)
    (hp : p ≤ buf + 360 + data_n + al + au + bh) :
    p + 295 ≤ buf + (64 + 17 * 33 + 30 + data_n + al + au + bh) := by
  omega

private theorem rlp_word_encoded_len_body_short {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w)))
    (hlt : w < 128) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len)).1 =
      some (.returned (.val (.word 1))) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len =
      .seq
        (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
          (.return (.const 1)) .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hnle : ¬ (128#64 ≤ w) := by
    simp only [BitVec.lt_def] at hlt
    simp only [BitVec.le_def]
    have h128 : (128 : BitVec 64).toNat = 128 := rfl
    have h128' : (128#64).toNat = 128 := rfl
    omega
  simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL, hlt, hnle,
    evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem storeByte_local_dst_lt_heapEnd {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst0 : BitVec 64) (val : ExpHOL 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hdst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnone : (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none) :
    dst0.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  simp only [evalHOLExact, hdst] at hnone
  split at hnone
  · split at hnone
    · rename_i m' hst
      unfold panMemStoreByteWord8HOL at hst; dsimp only at hst
      cases hm : t.memory (panByteAlignHOL dst0) with
      | word cell =>
        by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
        · exact (M11.byteAlign_lt_heapEnd hma dst0 hdom).2
        · simp [hm, hdom] at hst
    · simp at hnone
  · simp at hnone

private theorem eval_tx_put_to_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 to0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hto : s.locals.lookup (ofString "to") = some (.val (.word to0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 21 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_to)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_to)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ len : BitVec 64, rv = .val (.word len) ∧ len.toNat ≤ 21 ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_tx_put_to =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "to")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
          .skip)
        (.call none (ofString "rlp_encode_bytes")
          [.var .local (ofString "dst"), .var .local (ofString "to"), .const 20]) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "to")) (.const 0)) =
      some (.val (.word (if to0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hto, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc1] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases htoz : to0 = 0
  · rw [if_pos htoz, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases (evaluate_storeByte_control_frame s (.var .local (ofString "dst")) (.const 128)).1 with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only
      have hdst_lt := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨1, hrv''.symm, by decide, hdst_lt, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
  · have h00 : (0 : BitVec 64) = 0 := rfl
    rw [if_neg htoz, if_pos h00, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_call] at hnt ⊢
    have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "dst"), .var .local (ofString "to"), .const 20] =
        some [.val (.word dst0), .val (.word to0), .val (.word 20)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hdst, hto]
    have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
      (ofString "dst") (ofString "src") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 to0 20
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_bytes)
    simp only [ha, hlk] at hnt ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · simp only [hcz, ↓reduceIte] at hnt ⊢
      set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word to0))).update (ofString "n", ValueHOL.val (.word 20))
      set ent := callEntryStateHOLFinite s cmap
      have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
      have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word to0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "src" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word 20)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have h20 : rlpHeaderLenPure (20 : BitVec 64).toNat + (20 : BitVec 64).toNat = 21 := by decide
      have hin20 : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
          dst0.toNat + rlpHeaderLenPure (20 : BitVec 64).toNat + (20 : BitVec 64).toNat ≤ ivl.1 + ivl.2 := by
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩
      rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
      have hnt_eb : reb ≠ some .timeOut := by
        rintro rfl; rw [heb] at hnt; exact hnt rfl
      obtain ⟨hret, hnonret⟩ := eval_rlp_encode_bytes_body_exact ent dst0 to0 20 Rl
        hcode hma hent_dst hent_src hent_n hin20 (by rw [heb]; exact hnt_eb)
      rw [heb] at hret hnonret
      dsimp only at hret hnonret
      simp only [heb] at hnt ⊢
      cases reb with
      | none => exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_eb
        | exception eid ev =>
          exact ⟨fun _ h => by simp at h, fun r' hr' _ => by
            injection hr' with hr''; subst hr''
            exact hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
        | returned rv =>
          obtain ⟨len, rfl, hlen, hdst_lt, heff_eb⟩ := hret rv rfl
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only; rw [if_pos hsh]
          have heff0 : M11.ByteRegionEffect s ent Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
          have heff_out : M11.ByteRegionEffect s seb.emptyLocalsHOLFinite Rl :=
            (heff0.trans heff_eb).with_locals_clock _ _
          refine ⟨fun rv' hrv' => ?_, fun r' hr' hnr => ?_⟩
          · injection hrv' with hrv''; injection hrv'' with hrv'''
            exact ⟨len, hrv'''.symm, by omega, hdst_lt, heff_out⟩
          · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
        | «break» | «continue» | error =>
          exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact not_resumes_error⟩
        | finalFfi _ =>
          exact ⟨fun _ h => by simp at h, fun r' hr' _ hres => by
            injection hr' with hr''; subst hr''
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem eval_call_local_tx_put_to {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp toExp : ExpHOL 64)
    (dst0 to0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hto : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) toExp =
      some (.val (.word to0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 21 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_to")
        [dstExp, toExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_to")
        [dstExp, toExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat ≤ 21 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, toExp] = some [.val (.word dst0), .val (.word to0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hto]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "tx_put_to")
    (ofString "dst") (ofString "to")
    (sourceFnBody Guest.Software.guestFn_tx_put_to) dst0 to0 (by decide)
    (by rw [hcode]; exact lookup_tx_put_to)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "to", ValueHOL.val (.word to0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "to" ≠ ofString "dst" by decide]
    have hent_to : ent.locals.lookup (ofString "to") = some (.val (.word to0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hpt : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_to) with ⟨rpt, spt⟩
    have hnt_pt : rpt ≠ some .timeOut := by
      rintro rfl; rw [hpt] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_tx_put_to_body_exact ent dst0 to0 Rl
      hcode hAR.1.memaddrs hent_dst hent_to hin_ivl (by rw [hpt]; exact hnt_pt)
    rw [hpt] at hret hnonret
    dsimp only at hret hnonret
    simp only [hpt] at hnt ⊢
    cases rpt with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_pt
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen21, hdst_lt, heff_pt⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { spt with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_pt).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen21, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 11: Deterministic RLP Word & `u256` Length Specs and `tx_put_u256` -/

private theorem lookup_rlp_word_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_word_encoded_len") =
      some ([(ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len, .one) :=
  lookup_of_guestAst_getElem 127 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_word_encoded_len) rfl

private def rlpWordEncodedLenPure (w : BitVec 64) : Nat :=
  if w.toNat < 128 then 1 else 1 + rlpBeLenAux 8 w.toNat

private theorem rlpWordEncodedLenPure_bounds (w : BitVec 64) :
    1 ≤ rlpWordEncodedLenPure w ∧ rlpWordEncodedLenPure w ≤ 9 := by
  unfold rlpWordEncodedLenPure
  split
  · omega
  · have := rlpBeLenAux_le 8 w.toNat; omega

private theorem eval_rlp_word_encoded_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w0)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (rlpWordEncodedLenPure w0))))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len =
      .seq
        (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
          (.return (.const 1)) .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
      some (.val (.word (if w0.toNat < 128 then 1 else 0))) := by
    simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
  rw [hev_c] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hw128 : w0.toNat < 128
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_pos hw128, if_neg h10, evaluateHOLFiniteState_return]
    have hc1 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) (.const 1#64) =
        some (.val (.word 1#64)) := rfl
    dsimp only [OfNat.ofNat, BitVec.ofNat] at hc1 ⊢
    rw [hc1]; simp [shapeOfHOLExact, rlpWordEncodedLenPure, hw128]
    exact (M13.LocFrame.refl s).emptyLocals
  · have h00 : (0 : BitVec 64) = 0 := rfl
    rw [if_neg hw128, if_pos h00, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
    have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "w")] = some [.val (.word w0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hw]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
      (sourceFnBody Guest.Software.guestFn_rlp_be_len) w0
      (by rw [hcode]; exact M11.lookup_rlp_be_len)
    simp only [ha, hlk] at hnt ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · simp only [hcz, ↓reduceIte] at hnt ⊢
      set cmap := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word w0))
      set ent := callEntryStateHOLFinite s cmap
      have hent_v : ent.locals.lookup (ofString "v") = some (.val (.word w0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨rbl, sbl⟩
      have hnt_bl : rbl ≠ some .timeOut := by
        rintro rfl; rw [hbl] at hnt; exact hnt rfl
      obtain ⟨hr_bl, hlf_bl⟩ := eval_rlp_be_len_body_exact ent w0 hent_v (by rw [hbl]; exact hnt_bl)
      rw [hbl] at hr_bl hlf_bl
      dsimp only at hr_bl hlf_bl
      subst hr_bl
      set ll := BitVec.ofNat 64 (rlpBeLenAux 8 w0.toNat)
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hbl, hsh, ↓reduceIte]
      set mid := setVarHOLFinite (ofString "ll") (.val (.word ll)) { sbl with locals := s.locals }
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_return]
      have hev_ret : @evalHOLExact 64 F _ mid.toExact
          (fun a => Classical.propDecidable (mid.memaddrs a))
          (.op .add [.const 1, .var .local (ofString "ll")]) =
          some (.val (.word (1 + ll))) := by
        simp [evalHOLExact, evalListHOLExact, hmid_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hev_ret]; dsimp only
      have hsz : sizeOfShapeWithContextHOL mid.structs
          (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]; dsimp only
      have h1ll : 1 + ll = BitVec.ofNat 64 (rlpWordEncodedLenPure w0) := by
        have hb8 := rlpBeLenAux_le 8 w0.toNat
        apply BitVec.eq_of_toNat_eq
        change (1 + ll).toNat = (BitVec.ofNat 64 (rlpWordEncodedLenPure w0)).toNat
        rw [BitVec.toNat_add]
        have h1_nat : (1 : BitVec 64).toNat = 1 := by decide
        have hll_nat : ll.toNat = rlpBeLenAux 8 w0.toNat := by
          dsimp [ll]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        rw [h1_nat, hll_nat, BitVec.toNat_ofNat]
        simp only [rlpWordEncodedLenPure, hw128, ↓reduceIte]
      rw [h1ll]
      have hlf_ent : M13.LocFrame s ent := by cases s; rfl
      exact ⟨rfl, ((((hlf_ent.trans hlf_bl).locals _).setVar _ _).emptyLocals).locals _⟩

private theorem eval_decCall_rlp_word_encoded_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (wExp : ExpHOL 64) (w0 : BitVec 64)
    (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hw_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp =
      some (.val (.word w0)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_word_encoded_len") [wExp] cont)).1 ≠
      some .timeOut) :
    let wl := BitVec.ofNat 64 (rlpWordEncodedLenPure w0)
    ∃ mid : PanSemStateFiniteExact 64 F,
      wl.toNat = rlpWordEncodedLenPure w0 ∧
      1 ≤ wl.toNat ∧ wl.toNat ≤ 9 ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word wl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_word_encoded_len") [wExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro wl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [wExp] =
      some [.val (.word w0)] := by simp [evalListHOLFinite, evalListHOLExact, hw_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_word_encoded_len") (ofString "w")
    (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len) w0
    (by rw [hcode]; exact lookup_rlp_word_encoded_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "w", ValueHOL.val (.word w0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_w : ent.locals.lookup (ofString "w") = some (.val (.word w0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hwl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len) with ⟨rwl, swl⟩
    have hnt_wl : rwl ≠ some .timeOut := by
      rintro rfl; rw [hwl] at hnt; exact hnt rfl
    obtain ⟨hr_wl, hlf_wl⟩ := eval_rlp_word_encoded_len_body_exact ent w0 hcode hent_w (by rw [hwl]; exact hnt_wl)
    rw [hwl] at hr_wl hlf_wl
    dsimp only at hr_wl hlf_wl
    subst hr_wl
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpWordEncodedLenPure w0))) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpWordEncodedLenPure w0))) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hwl] at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word wl)) { swl with locals := s.locals }
    have hlf_all : M13.LocFrame s mid := by
      have h1 : M13.LocFrame s ent := by cases s; rfl
      exact ((h1.trans hlf_wl).locals _).setVar _ _
    have hbnd := rlpWordEncodedLenPure_bounds w0
    have hwl_nat : wl.toNat = rlpWordEncodedLenPure w0 := by
      dsimp [wl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hwl_nat, by omega, by omega, hlf_all.globals, hlf_all.memory, rfl,
      HeapByteEff.of_locFrame hAR hlf_all Rl gw, hnt, rfl⟩

private theorem eval_rlp_encode_word_body_exact_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 w0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpWordEncodedLenPure w0 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ len : BitVec 64, rv = .val (.word len) ∧
        len.toNat = rlpWordEncodedLenPure w0 ∧
        1 ≤ len.toNat ∧ len.toNat ≤ 9 ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_word =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
          .skip)
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
            (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) (.return (.const 1)))
            .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
      some (.val (.word (if w0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc1] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases hwz : w0 = 0
  · rw [if_pos hwz, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases (evaluate_storeByte_control_frame s (.var .local (ofString "dst")) (.const 128)).1 with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only
      have hdst_lt := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        have := rlpWordEncodedLenPure_bounds w0
        exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
      have hlen_pure : rlpWordEncodedLenPure w0 = 1 := by
        subst hwz; simp [rlpWordEncodedLenPure]
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨1, hrv''.symm, hlen_pure.symm, by decide, by decide, hdst_lt, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
  · have h00 : (0 : BitVec 64) = 0 := rfl
    rw [if_neg hwz, if_pos h00, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
    have hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
        some (.val (.word (if w0.toNat < 128 then 1 else 0))) := by
      simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hc2] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hw128 : w0.toNat < 128
    · rw [if_pos hw128, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hsb : evaluateHOLFiniteState s
          (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
      simp only [hsb] at hnt ⊢
      rcases (evaluate_storeByte_control_frame s (.var .local (ofString "dst")) (.var .local (ofString "w"))).1 with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only
        have hdst_lt := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
        obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          have := rlpWordEncodedLenPure_bounds w0
          exact ⟨ivl, hivl, h1, by omega⟩)
        rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
        have hlen_pure : rlpWordEncodedLenPure w0 = 1 := by simp [rlpWordEncodedLenPure, hw128]
        refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
        · injection hrv with hrv'; injection hrv' with hrv''
          exact ⟨1, hrv''.symm, hlen_pure.symm, by decide, by decide, hdst_lt, heff1.with_locals_clock _ _⟩
        · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
    · rw [if_neg hw128, if_pos h00, evaluateHOLFiniteState_skip] at hnt ⊢
      dsimp only at hnt ⊢
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
      have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "w")] = some [.val (.word w0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hw]
      have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_rlp_be_len) w0
        (by rw [hcode]; exact M11.lookup_rlp_be_len)
      simp only [ha, hlk] at hnt ⊢
      by_cases hcz : s.clock = 0
      · simp [hcz] at hnt
      · simp only [hcz, ↓reduceIte] at hnt ⊢
        set cmap := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word w0))
        set ent := callEntryStateHOLFinite s cmap
        have hent_v : ent.locals.lookup (ofString "v") = some (.val (.word w0)) := by
          simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨rbl, sbl⟩
        have hnt_bl : rbl ≠ some .timeOut := by
          rintro rfl; rw [hbl] at hnt; exact hnt rfl
        obtain ⟨hr_bl, hlf_bl⟩ := eval_rlp_be_len_body_exact ent w0 hent_v (by rw [hbl]; exact hnt_bl)
        rw [hbl] at hr_bl hlf_bl
        dsimp only at hr_bl hlf_bl
        subst hr_bl
        set ll := BitVec.ofNat 64 (rlpBeLenAux 8 w0.toNat)
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hbl, hsh, ↓reduceIte] at hnt ⊢
        set mid := setVarHOLFinite (ofString "ll") (.val (.word ll)) { sbl with locals := s.locals }
        have hlf_s_mid : M13.LocFrame s mid := by
          have h1 : M13.LocFrame s ent := by cases s; rfl
          exact ((h1.trans hlf_bl).locals _).setVar _ _
        have heff_s_mid : M11.ByteRegionEffect s mid Rl := by
          have hseq := hlf_s_mid
          unfold M13.LocFrame at hseq
          rw [hseq]
          exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock mid.locals mid.clock
        have hmid_code : mid.code = originalRuntimeCode := heff_s_mid.code.trans hcode
        have hmid_ma : mid.memaddrs = ordinaryDomain := heff_s_mid.memaddrs.trans hma
        have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word w0)) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw,
            show ofString "ll" ≠ ofString "w" by decide]
        have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
            show ofString "ll" ≠ ofString "dst" by decide]
        have hb8 := rlpBeLenAux_le 8 w0.toNat
        have hll_nat : ll.toNat = rlpBeLenAux 8 w0.toNat := by
          dsimp [ll]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hlen_pure : rlpWordEncodedLenPure w0 = 1 + ll.toNat := by
          simp [rlpWordEncodedLenPure, hw128, hll_nat]
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hsb : evaluateHOLFiniteState mid
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
        simp only [hsb] at hnt ⊢
        rcases (evaluate_storeByte_control_frame mid (.var .local (ofString "dst"))
            (.op .add [.const 128, .var .local (ofString "ll")])).1 with hsn | hse
        · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hnt ⊢
          have hdst_lt := storeByte_local_dst_lt_heapEnd mid dst0 _ hmid_ma hmid_dst (by rw [hsb])
          obtain ⟨heff_hdr, hs2_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
            simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
            subst hdst_ev
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            exact ⟨ivl, hivl, h1, by omega⟩)
          have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
          have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [hs2_loc]; exact hmid_dst
          have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w0)) := by
            rw [hs2_loc]; exact hmid_w
          have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
            rw [hs2_loc]; exact hmid_ll
          have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
            have hhe := hdst_lt; rw [WkBlockTxEnc.heapEnd_val] at hhe
            rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
            have hhe := hdst_lt; rw [WkBlockTxEnc.heapEnd_val] at hhe; omega
          rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
          rcases hc_put : evaluateHOLFiniteState s2
            (.call (some (none, none)) (ofString "rlp_put_be")
              [.op .add [.var .local (ofString "dst"), .const 1],
               .var .local (ofString "w"),
               .var .local (ofString "ll")]) with ⟨rc, s3⟩
          have hnt_put : rc ≠ some .timeOut := by
            rintro rfl; rw [hc_put] at hnt; exact hnt rfl
          have hput := M11.eval_call_rlp_put_be s2
            (.op .add [.var .local (ofString "dst"), .const 1])
            (.var .local (ofString "w"))
            (.var .local (ofString "ll"))
            (dst0 + 1) w0 ll Rl hs2_code
            (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
            (by simp [evalHOLExact, hs2_w])
            (by simp [evalHOLExact, hs2_ll])
            hfit
            (fun _ => by
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
              exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
            (by rw [hc_put]; exact hnt_put)
          dsimp only at hput; rw [hc_put] at hput; simp only [hc_put] at hnt ⊢
          cases rc with
          | some r =>
            dsimp only
            have hnr := hput.2 (by simp)
            refine ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)), fun r' hr' _ => ?_⟩
            injection hr' with hr''; subst hr''; exact hnr
          | none =>
            dsimp only at hnt ⊢
            obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
            have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
              rw [hs3_loc]; exact hs2_ll
            rw [evaluateHOLFiniteState_return]
            have hev_ret : @evalHOLExact 64 F _ s3.toExact
                (fun a => Classical.propDecidable (s3.memaddrs a))
                (.op .add [.const 1, .var .local (ofString "ll")]) =
                some (.val (.word (1 + ll))) := by
              simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret]; dsimp only
            have hsz : sizeOfShapeWithContextHOL s3.structs
                (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]; dsimp only
            have h1ll_nat : (1 + ll).toNat = 1 + ll.toNat := by
              rw [BitVec.toNat_add]; change (1 + ll.toNat) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
            refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
            · injection hrv with hrv'; injection hrv' with hrv''
              exact ⟨1 + ll, hrv''.symm, by omega, by omega, by omega, hdst_lt,
                (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
            · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
        · rw [hsb] at hse; dsimp only at hse; subst hse
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩

private theorem eval_call_local_rlp_encode_word_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp wExp : ExpHOL 64)
    (dst0 w0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hw : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp =
      some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpWordEncodedLenPure w0 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_word")
        [dstExp, wExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_word")
        [dstExp, wExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpWordEncodedLenPure w0 ∧
        1 ≤ len.toNat ∧ len.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, wExp] = some [.val (.word dst0), .val (.word w0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hw]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word")
    (ofString "dst") (ofString "w")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_word) dst0 w0 (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_word)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "w", ValueHOL.val (.word w0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "dst" by decide]
    have hent_w : ent.locals.lookup (ofString "w") = some (.val (.word w0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hew : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨rew, sew⟩
    have hnt_ew : rew ≠ some .timeOut := by
      rintro rfl; rw [hew] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_word_body_exact_len ent dst0 w0 Rl
      hcode hAR.1.memaddrs hent_dst hent_w hin_ivl (by rw [hew]; exact hnt_ew)
    rw [hew] at hret hnonret
    dsimp only at hret hnonret
    simp only [hew] at hnt ⊢
    cases rew with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_ew
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen_eq, hlen1, hlen9, hdst_lt, heff_ew⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { sew with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_ew).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen_eq, hlen1, hlen9, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private def u256LimbPure (w0 w1 w2 w3 i : BitVec 64) : BitVec 64 :=
  if i = 0#64 then w0 else if i = 1#64 then w1 else if i = 2#64 then w2 else if i = 3#64 then w3 else 0#64

private theorem eval_u256_limb_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 i : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_limb)).1 =
      some (.returned (.val (.word (u256LimbPure w0 w1 w2 w3 i)))) := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_limb =
      .seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 0#64))
        (.return (.rfield 0 (.var .local (ofString "a")))) .skip)
      (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 1#64))
        (.return (.rfield 1 (.var .local (ofString "a")))) .skip)
      (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 2#64))
        (.return (.rfield 2 (.var .local (ofString "a")))) .skip)
      (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 3#64))
        (.return (.rfield 3 (.var .local (ofString "a")))) .skip)
        (.return (.const 0#64))))) := rfl
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hb]
  simp only [u256LimbPure]
  by_cases h0 : i = 0#64
  · subst h0
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
      evaluateHOLFiniteState_return, evalHOLFinite_eq_toExact, evalHOLExact,
      PanSemStateFiniteExact.toExact, ha, hi, Compiler.Encoders.Asm.wordCmpHOL,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  · simp only [h0, ↓reduceIte]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "i")) (.const 0#64)) = some (.val (.word 0#64)) := by
      simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, h0]
    rw [hc0]; dsimp only; rw [if_pos h00, evaluateHOLFiniteState_skip]; dsimp only
    by_cases h1 : i = 1#64
    · subst h1
      simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
        evaluateHOLFiniteState_return, evalHOLFinite_eq_toExact, evalHOLExact,
        PanSemStateFiniteExact.toExact, ha, hi, Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    · simp only [h1, ↓reduceIte]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .equal (.var .local (ofString "i")) (.const 1#64)) = some (.val (.word 0#64)) := by
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, h1]
      rw [hc1]; dsimp only; rw [if_pos h00, evaluateHOLFiniteState_skip]; dsimp only
      by_cases h2 : i = 2#64
      · subst h2
        simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
          evaluateHOLFiniteState_return, evalHOLFinite_eq_toExact, evalHOLExact,
          PanSemStateFiniteExact.toExact, ha, hi, Compiler.Encoders.Asm.wordCmpHOL,
          shapeOfHOLExact, sizeOfShapeWithContextHOL]
      · simp only [h2, ↓reduceIte]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        have hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .equal (.var .local (ofString "i")) (.const 2#64)) = some (.val (.word 0#64)) := by
          simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, h2]
        rw [hc2]; dsimp only; rw [if_pos h00, evaluateHOLFiniteState_skip]; dsimp only
        by_cases h3 : i = 3#64
        · subst h3
          simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite,
            evaluateHOLFiniteState_return, evalHOLFinite_eq_toExact, evalHOLExact,
            PanSemStateFiniteExact.toExact, ha, hi, Compiler.Encoders.Asm.wordCmpHOL,
            shapeOfHOLExact, sizeOfShapeWithContextHOL]
        · simp only [h3, ↓reduceIte]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
          have hc3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .equal (.var .local (ofString "i")) (.const 3#64)) = some (.val (.word 0#64)) := by
            simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, h3]
          rw [hc3]; dsimp only; rw [if_pos h00, evaluateHOLFiniteState_skip]; dsimp only
          simp [evaluateHOLFiniteState_return, evalHOLFinite_eq_toExact, evalHOLExact,
            shapeOfHOLExact, sizeOfShapeWithContextHOL]

private def bitStepPure (sh : Nat) (nx : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  if nx.2 >>> sh = 0#64 then nx else (nx.1 + BitVec.ofNat 64 sh, nx.2 >>> sh)

private def bitLength64Pure (x : BitVec 64) : BitVec 64 :=
  let s1 := bitStepPure 32 (0#64, x)
  let s2 := bitStepPure 16 s1
  let s3 := bitStepPure 8 s2
  let s4 := bitStepPure 4 s3
  let s5 := bitStepPure 2 s4
  let s6 := bitStepPure 1 s5
  s6.1 + s6.2

private def u256BitLengthPure (w0 w1 w2 w3 : BitVec 64) : BitVec 64 :=
  if w3 = 0#64 then
    if w2 = 0#64 then
      if w1 = 0#64 then bitLength64Pure w0
      else 64#64 + bitLength64Pure w1
    else 128#64 + bitLength64Pure w2
  else 192#64 + bitLength64Pure w3

private def u256ByteLengthPure (w0 w1 w2 w3 : BitVec 64) : BitVec 64 :=
  (u256BitLengthPure w0 w1 w2 w3 + 7#64) >>> (3 : Nat)

private def txU256EncodedLenPure (w0 w1 w2 w3 : BitVec 64) : Nat :=
  let n := (u256ByteLengthPure w0 w1 w2 w3).toNat
  if n = 0 then 1
  else if n = 1 ∧ w0.toNat < 128 then 1
  else 1 + n

private def bitStepProgLocal (sh : Nat) : ProgHOL 64 :=
  .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) (.const (BitVec.ofNat 64 0)))
    (.seq
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 sh)]))
      (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh)))))
    .skip

private theorem eval_bitStepProgLocal {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nv xv : BitVec 64) (sh : Nat)
    (hsh_lt : sh < 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nv)))
    (hx : s.locals.lookup (ofString "x") = some (.val (.word xv))) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (bitStepProgLocal sh) = (none, mid) ∧
      M13.LocFrame s mid ∧
      mid.locals.lookup (ofString "n") = some (.val (.word (bitStepPure sh (nv, xv)).1)) ∧
      mid.locals.lookup (ofString "x") = some (.val (.word (bitStepPure sh (nv, xv)).2)) := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hsh_bv : (BitVec.ofNat 64 sh).toNat = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh_cond : ¬ (sh ≠ 0 ∧ 64 ≤ sh) := by omega
  dsimp only [bitStepProgLocal, bitStepPure]
  rw [evaluateHOLFiniteState_ite]
  have hevc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) (.const 0#64)) =
      some (.val (.word (if (xv >>> sh) = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx, Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hsh_bv, hsh_cond]
  rw [hevc]; dsimp only
  by_cases hnz : (xv >>> sh) ≠ 0#64
  · have hne0 : ¬ ((xv >>> sh) = 0#64) := hnz
    have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    rw [if_neg hne0, if_neg h10, if_neg hne0, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    dsimp only
    have hev_add : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 sh)]) =
        some (.val (.word (nv + BitVec.ofNat 64 sh))) := by
      simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hev_add]; dsimp only
    have hval1 : isValidValueHOLFinite s .local (ofString "n") (.val (.word (nv + BitVec.ofNat 64 sh))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hn, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hval1]; dsimp only
    set s1 := setKvarHOLFinite .local (ofString "n") (.val (.word (nv + BitVec.ofNat 64 sh))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (nv + BitVec.ofNat 64 sh))) := by
      simp [s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word xv)) := by
      simp [s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
        show ofString "n" ≠ ofString "x" by decide]
    rw [evaluateHOLFiniteState_assign]
    have hev_sh : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) =
        some (.val (.word (xv >>> sh))) := by
      simp [evalHOLExact, hs1_x, wordShiftHOL, hsh_bv, hsh_cond]
    rw [hev_sh]; dsimp only
    have hval2 : isValidValueHOLFinite s1 .local (ofString "x") (.val (.word (xv >>> sh))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs1_x, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hval2]
    refine ⟨_, rfl, ((M13.LocFrame.refl s).setVar _ _).setVar _ _, ?_, ?_⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_n,
        show ofString "x" ≠ ofString "n" by decide]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · have heq0 : (xv >>> sh) = 0#64 := Classical.not_not.mp hnz
    have h00 : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos heq0, if_pos h00, if_pos heq0, evaluateHOLFiniteState_skip]
    exact ⟨s, rfl, M13.LocFrame.refl s, hn, hx⟩

private theorem eval_bit_length64_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x0 : BitVec 64)
    (hx : s.locals.lookup (ofString "x") = some (.val (.word x0))) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bit_length64)).1 =
      some (.returned (.val (.word (bitLength64Pure x0)))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bit_length64)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_bit_length64 =
      .dec (ofString "n") .one (.const 0#64)
        (.seq (bitStepProgLocal 32)
          (.seq (bitStepProgLocal 16)
            (.seq (bitStepProgLocal 8)
              (.seq (bitStepProgLocal 4)
                (.seq (bitStepProgLocal 2)
                  (.seq (bitStepProgLocal 1)
                    (.return (.op .add [.var .local (ofString "n"), .var .local (ofString "x")])))))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
  have h0_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [h0_ev]; dsimp only
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0]; dsimp only
  set s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) s
  have hn0 : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hx0 : s0.locals.lookup (ofString "x") = some (.val (.word x0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
      show ofString "n" ≠ ofString "x" by decide]
  obtain ⟨s1, hr1, hlf1, hn1, hx1⟩ := eval_bitStepProgLocal s0 0#64 x0 32 (by omega) hn0 hx0
  obtain ⟨s2, hr2, hlf2, hn2, hx2⟩ := eval_bitStepProgLocal s1 _ _ 16 (by omega) hn1 hx1
  obtain ⟨s3, hr3, hlf3, hn3, hx3⟩ := eval_bitStepProgLocal s2 _ _ 8 (by omega) hn2 hx2
  obtain ⟨s4, hr4, hlf4, hn4, hx4⟩ := eval_bitStepProgLocal s3 _ _ 4 (by omega) hn3 hx3
  obtain ⟨s5, hr5, hlf5, hn5, hx5⟩ := eval_bitStepProgLocal s4 _ _ 2 (by omega) hn4 hx4
  obtain ⟨s6, hr6, hlf6, hn6, hx6⟩ := eval_bitStepProgLocal s5 _ _ 1 (by omega) hn5 hx5
  rw [evaluateHOLFiniteState_seq_line780, hr1]; dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hr2]; dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hr3]; dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hr4]; dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hr5]; dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hr6]; dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev_ret : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
      (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
      some (.val (.word (bitLength64Pure x0))) := by
    simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord, bitLength64Pure]
  rw [hev_ret]; dsimp only
  have hsz : sizeOfShapeWithContextHOL s6.structs (shapeOfHOLExact (.val (.word (bitLength64Pure x0)) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  refine ⟨rfl, ?_⟩
  exact (((((((((M13.LocFrame.refl s).setVar _ _).trans hlf1).trans hlf2).trans hlf3).trans hlf4).trans hlf5).trans hlf6).emptyLocals).locals _

private theorem bitStepPure_bounds (sh nMax : Nat) (nx : BitVec 64 × BitVec 64)
    (hsh_pos : 0 < sh) (hsh_lt : sh < 64)
    (hx_lt : nx.2.toNat < 2 ^ (2 * sh)) (hn_le : nx.1.toNat ≤ nMax) (hsum : nMax + sh < 2 ^ 64) :
    (bitStepPure sh nx).1.toNat ≤ nMax + sh ∧
    (bitStepPure sh nx).2.toNat < 2 ^ sh ∧
    (nx.2 = 0#64 → bitStepPure sh nx = (nx.1, 0#64)) := by
  rcases nx with ⟨nv, xv⟩
  dsimp only at hx_lt hn_le ⊢
  have hsh_bv : (BitVec.ofNat 64 sh).toNat = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold bitStepPure; dsimp only
  by_cases hz : xv >>> sh = 0#64
  · rw [if_pos hz]; dsimp only
    have hdiv0 : xv.toNat / 2 ^ sh = 0 := by
      have := congrArg BitVec.toNat hz
      rwa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    exact ⟨by omega, Nat.lt_of_div_eq_zero (Nat.two_pow_pos sh) hdiv0, fun hx0 => by subst hx0; rfl⟩
  · rw [if_neg hz]; dsimp only
    refine ⟨?_, ?_, fun hx0 => False.elim (hz (by subst hx0; simp))⟩
    · rw [BitVec.toNat_add, hsh_bv, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hmul : 2 ^ (2 * sh) = 2 ^ sh * 2 ^ sh := by rw [Nat.two_mul, Nat.pow_add]
      rw [hmul] at hx_lt
      exact Nat.div_lt_of_lt_mul hx_lt

private theorem bitLength64Pure_le_64 (x0 : BitVec 64) :
    (bitLength64Pure x0).toNat ≤ 64 ∧
    (x0 = 0#64 → bitLength64Pure x0 = 0#64) ∧
    (x0 ≠ 0#64 → 1 ≤ (bitLength64Pure x0).toNat) ∧
    ((bitLength64Pure x0).toNat ≤ 8 → x0.toNat < 256) := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  unfold bitLength64Pure
  set s1 := bitStepPure 32 (0#64, x0)
  set s2 := bitStepPure 16 s1
  set s3 := bitStepPure 8 s2
  set s4 := bitStepPure 4 s3
  set s5 := bitStepPure 2 s4
  set s6 := bitStepPure 1 s5
  obtain ⟨hn1, hx1, hz1⟩ := bitStepPure_bounds 32 0 (0#64, x0) (by omega) (by omega) x0.isLt (Nat.le_refl 0) (by omega)
  change s1.1.toNat ≤ 0 + 32 at hn1; change s1.2.toNat < 2 ^ 32 at hx1
  obtain ⟨hn2, hx2, hz2⟩ := bitStepPure_bounds 16 32 s1 (by omega) (by omega) hx1 hn1 (by omega)
  change s2.1.toNat ≤ 32 + 16 at hn2; change s2.2.toNat < 2 ^ 16 at hx2
  obtain ⟨hn3, hx3, hz3⟩ := bitStepPure_bounds 8 48 s2 (by omega) (by omega) hx2 hn2 (by omega)
  change s3.1.toNat ≤ 48 + 8 at hn3; change s3.2.toNat < 2 ^ 8 at hx3
  obtain ⟨hn4, hx4, hz4⟩ := bitStepPure_bounds 4 56 s3 (by omega) (by omega) hx3 hn3 (by omega)
  change s4.1.toNat ≤ 56 + 4 at hn4; change s4.2.toNat < 2 ^ 4 at hx4
  obtain ⟨hn5, hx5, hz5⟩ := bitStepPure_bounds 2 60 s4 (by omega) (by omega) hx4 hn4 (by omega)
  change s5.1.toNat ≤ 60 + 2 at hn5; change s5.2.toNat < 2 ^ 2 at hx5
  obtain ⟨hn6, hx6, hz6⟩ := bitStepPure_bounds 1 62 s5 (by omega) (by omega) hx5 hn5 (by omega)
  change s6.1.toNat ≤ 62 + 1 at hn6; change s6.2.toNat < 2 ^ 1 at hx6
  have h21 : (2 ^ 1 : Nat) = 2 := rfl
  have hadd_nat : (s6.1 + s6.2).toNat = s6.1.toNat + s6.2.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hmono : ∀ (sh nMax : Nat) (nx : BitVec 64 × BitVec 64),
      sh < 64 → nx.1.toNat ≤ nMax → nMax + sh < 2 ^ 64 →
      nx.1.toNat ≤ (bitStepPure sh nx).1.toNat ∧
      (nx.2 ≠ 0#64 → (bitStepPure sh nx).2 ≠ 0#64) := by
    intro sh nMax ⟨nv, xv⟩ hsh hle hsm
    dsimp only at hle ⊢
    have hsh_bv : (BitVec.ofNat 64 sh).toNat = sh := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold bitStepPure; dsimp only
    by_cases hz : xv >>> sh = 0#64
    · rw [if_pos hz]; exact ⟨le_rfl, id⟩
    · rw [if_neg hz]; dsimp only
      refine ⟨?_, fun _ => hz⟩
      rw [BitVec.toNat_add, hsh_bv, Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hm1, hnz1⟩ := hmono 32 0 (0#64, x0) (by omega) (Nat.le_refl 0) (by omega)
  obtain ⟨hm2, hnz2⟩ := hmono 16 32 s1 (by omega) hn1 (by omega)
  obtain ⟨hm3, hnz3⟩ := hmono 8 48 s2 (by omega) hn2 (by omega)
  obtain ⟨hm4, hnz4⟩ := hmono 4 56 s3 (by omega) hn3 (by omega)
  obtain ⟨hm5, hnz5⟩ := hmono 2 60 s4 (by omega) hn4 (by omega)
  obtain ⟨hm6, hnz6⟩ := hmono 1 62 s5 (by omega) hn5 (by omega)
  change s1.1.toNat ≤ s2.1.toNat at hm2
  change s2.1.toNat ≤ s3.1.toNat at hm3
  change s3.1.toNat ≤ s4.1.toNat at hm4
  change s4.1.toNat ≤ s5.1.toNat at hm5
  change s5.1.toNat ≤ s6.1.toNat at hm6
  change (x0 ≠ 0#64 → s1.2 ≠ 0#64) at hnz1
  change (s1.2 ≠ 0#64 → s2.2 ≠ 0#64) at hnz2
  change (s2.2 ≠ 0#64 → s3.2 ≠ 0#64) at hnz3
  change (s3.2 ≠ 0#64 → s4.2 ≠ 0#64) at hnz4
  change (s4.2 ≠ 0#64 → s5.2 ≠ 0#64) at hnz5
  change (s5.2 ≠ 0#64 → s6.2 ≠ 0#64) at hnz6
  change (s6.1 + s6.2).toNat ≤ 64 ∧
    (x0 = 0#64 → s6.1 + s6.2 = 0#64) ∧
    (x0 ≠ 0#64 → 1 ≤ (s6.1 + s6.2).toNat) ∧
    ((s6.1 + s6.2).toNat ≤ 8 → x0.toNat < 256)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro hx0
    simp [s1, s2, s3, s4, s5, s6, bitStepPure, hx0]
  · intro hnz0
    have hs6_nz := hnz6 (hnz5 (hnz4 (hnz3 (hnz2 (hnz1 hnz0)))))
    have : 0 < s6.2.toNat := Nat.pos_of_ne_zero (fun h => hs6_nz (BitVec.eq_of_toNat_eq h))
    omega
  · intro hle8
    by_cases hx256 : x0.toNat < 256
    · exact hx256
    · exfalso
      by_cases h32 : x0 >>> 32 = 0#64
      · have hs1 : s1 = (0#64, x0) := by change (if x0 >>> 32 = 0#64 then _ else _) = _; rw [if_pos h32]
        by_cases h16 : x0 >>> 16 = 0#64
        · have hs2 : s2 = (0#64, x0) := by
            have : s2 = bitStepPure 16 s1 := rfl
            rw [this, hs1]; change (if x0 >>> 16 = 0#64 then _ else _) = _; rw [if_pos h16]
          have h8 : ¬ (x0 >>> 8 = 0#64) := by
            intro h8z
            have hdiv0 : x0.toNat / 2 ^ 8 = 0 := by
              have h8n : (x0 >>> (8 : Nat)).toNat = 0 := congrArg BitVec.toNat h8z
              rwa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h8n
            exact hx256 (Nat.lt_of_div_eq_zero (Nat.two_pow_pos 8) hdiv0)
          have hs3_eq : s3 = (8#64, x0 >>> 8) := by
            have : s3 = bitStepPure 8 s2 := rfl
            rw [this, hs2]; change (if x0 >>> 8 = 0#64 then _ else _) = _; rw [if_neg h8]; rfl
          have hs3 : s3.1.toNat = 8 := by rw [hs3_eq]; rfl
          have hs3_nz : s3.2 ≠ 0#64 := by rw [hs3_eq]; exact h8
          have hs6_nz := hnz6 (hnz5 (hnz4 hs3_nz))
          have : 0 < s6.2.toNat := Nat.pos_of_ne_zero (fun h => hs6_nz (BitVec.eq_of_toNat_eq h))
          have hs3_le : s3.1.toNat ≤ s6.1.toNat := le_trans hm4 (le_trans hm5 hm6)
          omega
        · have hs2_eq : s2 = (16#64, x0 >>> 16) := by
            have : s2 = bitStepPure 16 s1 := rfl
            rw [this, hs1]; change (if x0 >>> 16 = 0#64 then _ else _) = _; rw [if_neg h16]; rfl
          have hs2 : s2.1.toNat = 16 := by rw [hs2_eq]; rfl
          have hs2_le : s2.1.toNat ≤ s6.1.toNat := le_trans hm3 (le_trans hm4 (le_trans hm5 hm6))
          omega
      · have hs1_eq : s1 = (32#64, x0 >>> 32) := by
          change (if x0 >>> 32 = 0#64 then _ else _) = _; rw [if_neg h32]; rfl
        have hs1 : s1.1.toNat = 32 := by rw [hs1_eq]; rfl
        have hs1_le : s1.1.toNat ≤ s6.1.toNat := le_trans hm2 (le_trans hm3 (le_trans hm4 (le_trans hm5 hm6)))
        omega

private theorem u256ByteLengthPure_bounds (w0 w1 w2 w3 : BitVec 64) :
    (u256BitLengthPure w0 w1 w2 w3).toNat ≤ 256 ∧
    (u256ByteLengthPure w0 w1 w2 w3).toNat ≤ 32 ∧
    (u256ByteLengthPure w0 w1 w2 w3 = 0#64 ↔ w3 = 0#64 ∧ w2 = 0#64 ∧ w1 = 0#64 ∧ w0 = 0#64) ∧
    (u256ByteLengthPure w0 w1 w2 w3 = 1#64 → w3 = 0#64 ∧ w2 = 0#64 ∧ w1 = 0#64 ∧ w0.toNat < 256) ∧
    1 ≤ txU256EncodedLenPure w0 w1 w2 w3 ∧
    txU256EncodedLenPure w0 w1 w2 w3 ≤ 33 := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hpow3 : (2 ^ 3 : Nat) = 8 := rfl
  obtain ⟨hb0, hz0, hnz0, hle8_0⟩ := bitLength64Pure_le_64 w0
  obtain ⟨hb1, _, hnz1, _⟩ := bitLength64Pure_le_64 w1
  obtain ⟨hb2, _, hnz2, _⟩ := bitLength64Pure_le_64 w2
  obtain ⟨hb3, _, hnz3, _⟩ := bitLength64Pure_le_64 w3
  have hbit_le : (u256BitLengthPure w0 w1 w2 w3).toNat ≤ 256 := by
    unfold u256BitLengthPure
    by_cases h3 : w3 = 0#64
    · rw [if_pos h3]
      by_cases h2 : w2 = 0#64
      · rw [if_pos h2]
        by_cases h1 : w1 = 0#64
        · rw [if_pos h1]; omega
        · rw [if_neg h1, BitVec.toNat_add, show (64#64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
      · rw [if_neg h2, BitVec.toNat_add, show (128#64 : BitVec 64).toNat = 128 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [if_neg h3, BitVec.toNat_add, show (192#64 : BitVec 64).toNat = 192 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  have hbyte_nat : (u256ByteLengthPure w0 w1 w2 w3).toNat = ((u256BitLengthPure w0 w1 w2 w3).toNat + 7) / 8 := by
    unfold u256ByteLengthPure
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hpow3,
      BitVec.toNat_add, show (7#64 : BitVec 64).toNat = 7 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hbyte_le : (u256ByteLengthPure w0 w1 w2 w3).toNat ≤ 32 := by omega
  have hhi_ge9 : ¬ (w3 = 0#64 ∧ w2 = 0#64 ∧ w1 = 0#64) → 65 ≤ (u256BitLengthPure w0 w1 w2 w3).toNat := by
    intro hnhi
    unfold u256BitLengthPure
    by_cases h3 : w3 = 0#64
    · rw [if_pos h3]
      by_cases h2 : w2 = 0#64
      · rw [if_pos h2]
        have h1 : w1 ≠ 0#64 := fun h1 => hnhi ⟨h3, h2, h1⟩
        rw [if_neg h1, BitVec.toNat_add, show (64#64 : BitVec 64).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]
        have := hnz1 h1; omega
      · rw [if_neg h2, BitVec.toNat_add, show (128#64 : BitVec 64).toNat = 128 from rfl, Nat.mod_eq_of_lt (by omega)]
        have := hnz2 h2; omega
    · rw [if_neg h3, BitVec.toNat_add, show (192#64 : BitVec 64).toNat = 192 from rfl, Nat.mod_eq_of_lt (by omega)]
      have := hnz3 h3; omega
  refine ⟨hbit_le, hbyte_le, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h0
      have h0n : (u256ByteLengthPure w0 w1 w2 w3).toNat = 0 := by rw [h0]; rfl
      by_cases hhi : w3 = 0#64 ∧ w2 = 0#64 ∧ w1 = 0#64
      · obtain ⟨h3, h2, h1⟩ := hhi
        refine ⟨h3, h2, h1, ?_⟩
        by_contra hw0
        have hw0_pos := hnz0 hw0
        have hbit_eq : u256BitLengthPure w0 w1 w2 w3 = bitLength64Pure w0 := by
          simp [u256BitLengthPure, h3, h2, h1]
        rw [hbit_eq] at hbyte_nat
        omega
      · have := hhi_ge9 hhi; omega
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      apply BitVec.eq_of_toNat_eq
      have hbit_eq : u256BitLengthPure 0#64 0#64 0#64 0#64 = 0#64 := by
        simp [u256BitLengthPure, hz0 rfl]
      rw [hbyte_nat, hbit_eq]; rfl
  · intro h1
    have h1n : (u256ByteLengthPure w0 w1 w2 w3).toNat = 1 := by rw [h1]; rfl
    by_cases hhi : w3 = 0#64 ∧ w2 = 0#64 ∧ w1 = 0#64
    · obtain ⟨h3, h2, hw1⟩ := hhi
      have hbit_eq : u256BitLengthPure w0 w1 w2 w3 = bitLength64Pure w0 := by
        simp [u256BitLengthPure, h3, h2, hw1]
      rw [hbit_eq] at hbyte_nat
      exact ⟨h3, h2, hw1, hle8_0 (by omega)⟩
    · exfalso; have := hhi_ge9 hhi; omega
  · unfold txU256EncodedLenPure; dsimp only
    split <;> [omega; (split <;> omega)]
  · unfold txU256EncodedLenPure; dsimp only
    split <;> [omega; (split <;> omega)]

private theorem pan_u256_lookup
    (codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname p1 : MlS) (body : ProgHOL 64) (rs : ShapeHOL) (w0 w1 w2 w3 : BitVec 64)
    (hlook : codeLookup fname = some ([(p1, .comb [.one, .one, .one, .one])], body, rs)) :
    let v : ValueHOL 64 := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname [v] =
      some (body, HolFiniteMapExact.empty.update (p1, v), rs) := by
  intro v
  have raw : lookupCodeHOLExact codeLookup fname [v] =
      some (body, (fun key => if key = p1 then some v else none), rs) := by
    simp [lookupCodeHOLExact, hlook, v, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : key = p1
    · subst same
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have different : p1 ≠ key := Ne.symm same
      simp [same, different, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem eval_decCall_bit_length64 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (xExp : ExpHOL 64) (x0 : BitVec 64)
    (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) xExp =
      some (.val (.word x0)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "bit_length64") [xExp] cont)).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      M13.LocFrame s mid ∧
      mid.locals = s.locals.update (ofString lname, .val (.word (bitLength64Pure x0))) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "bit_length64") [xExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [xExp] =
      some [.val (.word x0)] := by simp [evalListHOLFinite, evalListHOLExact, hx]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "bit_length64") (ofString "x")
    (sourceFnBody Guest.Software.guestFn_bit_length64) x0
    (by rw [hcode]; exact M13.lookup_bit_length64)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "x", ValueHOL.val (.word x0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_x : ent.locals.lookup (ofString "x") = some (.val (.word x0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨rbl, sbl⟩
    obtain ⟨hr_bl, hlf_bl⟩ := eval_bit_length64_body_exact ent x0 hent_x
    rw [hbl] at hr_bl hlf_bl; dsimp only at hr_bl hlf_bl; subst hr_bl
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word (bitLength64Pure x0)) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word (bitLength64Pure x0)) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hbl, hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word (bitLength64Pure x0))) { sbl with locals := s.locals }
    have hlf_all : M13.LocFrame s mid := by
      have h1 : M13.LocFrame s ent := by cases s; rfl
      exact ((h1.trans hlf_bl).locals _).setVar _ _
    exact ⟨mid, hlf_all, rfl, hnt, rfl⟩

private theorem eval_u256_bit_length_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_bit_length)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_bit_length)).1 =
      some (.returned (.val (.word (u256BitLengthPure w0 w1 w2 w3)))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_bit_length)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_bit_length =
      .seq
        (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "a"))) (.const 0#64))
          (.decCall (ofString "n3") .one (ofString "bit_length64") [.rfield 3 (.var .local (ofString "a"))]
            (.return (.op .add [.const 192#64, .var .local (ofString "n3")])))
          .skip)
        (.seq
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "a"))) (.const 0#64))
            (.decCall (ofString "n2") .one (ofString "bit_length64") [.rfield 2 (.var .local (ofString "a"))]
              (.return (.op .add [.const 128#64, .var .local (ofString "n2")])))
            .skip)
          (.seq
            (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "a"))) (.const 0#64))
              (.decCall (ofString "n1") .one (ofString "bit_length64") [.rfield 1 (.var .local (ofString "a"))]
                (.return (.op .add [.const 64#64, .var .local (ofString "n1")])))
              .skip)
            (.call none (ofString "bit_length64") [.rfield 0 (.var .local (ofString "a"))]))) := rfl
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  rw [hb] at hnt ⊢
  unfold u256BitLengthPure
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hc3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.rfield 3 (.var .local (ofString "a"))) (.const 0#64)) =
      some (.val (.word (if w3 = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, ha, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc3] at hnt ⊢; dsimp only at hnt ⊢
  by_cases h3 : w3 = 0#64
  · rw [if_pos h3, if_pos h00] at hnt ⊢
    simp only [h3, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
    have hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.rfield 2 (.var .local (ofString "a"))) (.const 0#64)) =
        some (.val (.word (if w2 = 0#64 then 0#64 else 1#64))) := by
      simp [evalHOLExact, ha, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc2] at hnt ⊢; dsimp only at hnt ⊢
    by_cases h2 : w2 = 0#64
    · rw [if_pos h2, if_pos h00] at hnt ⊢
      simp only [h2, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
      have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notEqual (.rfield 1 (.var .local (ofString "a"))) (.const 0#64)) =
          some (.val (.word (if w1 = 0#64 then 0#64 else 1#64))) := by
        simp [evalHOLExact, ha, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc1] at hnt ⊢; dsimp only at hnt ⊢
      by_cases h1 : w1 = 0#64
      · rw [if_pos h1, if_pos h00] at hnt ⊢
        simp only [h1, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        rw [evaluateHOLFiniteState_call] at hnt ⊢
        have ha0 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.rfield 0 (.var .local (ofString "a"))] = some [.val (.word w0)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha]
        have hlk0 := pan_one_word_lookup s.code.lookup (ofString "bit_length64") (ofString "x")
          (sourceFnBody Guest.Software.guestFn_bit_length64) w0
          (by rw [hcode]; exact M13.lookup_bit_length64)
        simp only [ha0, hlk0] at hnt ⊢
        by_cases hcz : s.clock = 0
        · simp [hcz] at hnt
        · simp only [hcz, ↓reduceIte] at hnt ⊢
          set cmap := HolFiniteMapExact.empty.update (ofString "x", ValueHOL.val (.word w0))
          set ent := callEntryStateHOLFinite s cmap
          have hent_x : ent.locals.lookup (ofString "x") = some (.val (.word w0)) := by
            simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨rbl, sbl⟩
          obtain ⟨hr_bl, hlf_bl⟩ := eval_bit_length64_body_exact ent w0 hent_x
          rw [hbl] at hr_bl hlf_bl; dsimp only at hr_bl hlf_bl; subst hr_bl
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word (bitLength64Pure w0)) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hbl, hsh, ↓reduceIte]
          have h1_lf : M13.LocFrame s ent := by cases s; rfl
          exact ⟨trivial, (h1_lf.trans hlf_bl).locals _⟩
      · rw [if_neg h1, if_neg h10] at hnt ⊢
        simp only [h1, ↓reduceIte] at hnt ⊢
        have hf1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.rfield 1 (.var .local (ofString "a"))) = some (.val (.word w1)) := by
          simp [evalHOLExact, ha]
        rcases hdc_eq : evaluateHOLFiniteState s
            (.decCall (ofString "n1") .one (ofString "bit_length64") [.rfield 1 (.var .local (ofString "a"))]
              (.return (.op .add [.const 64#64, .var .local (ofString "n1")]))) with ⟨rdc, sdc⟩
        have hnt_dc : rdc ≠ some .timeOut := by
          rintro rfl; simp only [hdc_eq] at hnt; exact hnt rfl
        obtain ⟨mid, hlf_m, hmid_loc, _, hdc⟩ := eval_decCall_bit_length64 s "n1"
          (.rfield 1 (.var .local (ofString "a"))) w1
          (.return (.op .add [.const 64#64, .var .local (ofString "n1")]))
          hcode hf1 (by rw [hdc_eq]; exact hnt_dc)
        have hmid_n : mid.locals.lookup (ofString "n1") = some (.val (.word (bitLength64Pure w1))) := by
          rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hret : evaluateHOLFiniteState mid (.return (.op .add [.const 64#64, .var .local (ofString "n1")])) =
            (some (.returned (.val (.word (64#64 + bitLength64Pure w1)))), emptyLocalsHOLFinite mid) := by
          rw [evaluateHOLFiniteState_return]
          simp [evalHOLFinite_eq_toExact, evalHOLExact, evalListHOLExact, hmid_n,
            wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [hdc_eq, hret] at hdc; dsimp only at hdc
        injection hdc with hr_eq hs_eq; subst hr_eq hs_eq
        simp only [hdc_eq]
        exact ⟨trivial, (hlf_m.emptyLocals).locals _⟩
    · rw [if_neg h2, if_neg h10] at hnt ⊢
      simp only [h2, ↓reduceIte] at hnt ⊢
      have hf2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.rfield 2 (.var .local (ofString "a"))) = some (.val (.word w2)) := by
        simp [evalHOLExact, ha]
      rcases hdc_eq : evaluateHOLFiniteState s
          (.decCall (ofString "n2") .one (ofString "bit_length64") [.rfield 2 (.var .local (ofString "a"))]
            (.return (.op .add [.const 128#64, .var .local (ofString "n2")]))) with ⟨rdc, sdc⟩
      have hnt_dc : rdc ≠ some .timeOut := by
        rintro rfl; simp only [hdc_eq] at hnt; exact hnt rfl
      obtain ⟨mid, hlf_m, hmid_loc, _, hdc⟩ := eval_decCall_bit_length64 s "n2"
        (.rfield 2 (.var .local (ofString "a"))) w2
        (.return (.op .add [.const 128#64, .var .local (ofString "n2")]))
        hcode hf2 (by rw [hdc_eq]; exact hnt_dc)
      have hmid_n : mid.locals.lookup (ofString "n2") = some (.val (.word (bitLength64Pure w2))) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hret : evaluateHOLFiniteState mid (.return (.op .add [.const 128#64, .var .local (ofString "n2")])) =
          (some (.returned (.val (.word (128#64 + bitLength64Pure w2)))), emptyLocalsHOLFinite mid) := by
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLFinite_eq_toExact, evalHOLExact, evalListHOLExact, hmid_n,
          wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [hdc_eq, hret] at hdc; dsimp only at hdc
      injection hdc with hr_eq hs_eq; subst hr_eq hs_eq
      simp only [hdc_eq]
      exact ⟨trivial, (hlf_m.emptyLocals).locals _⟩
  · rw [if_neg h3, if_neg h10] at hnt ⊢
    simp only [h3, ↓reduceIte] at hnt ⊢
    have hf3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.rfield 3 (.var .local (ofString "a"))) = some (.val (.word w3)) := by
      simp [evalHOLExact, ha]
    rcases hdc_eq : evaluateHOLFiniteState s
        (.decCall (ofString "n3") .one (ofString "bit_length64") [.rfield 3 (.var .local (ofString "a"))]
          (.return (.op .add [.const 192#64, .var .local (ofString "n3")]))) with ⟨rdc, sdc⟩
    have hnt_dc : rdc ≠ some .timeOut := by
      rintro rfl; simp only [hdc_eq] at hnt; exact hnt rfl
    obtain ⟨mid, hlf_m, hmid_loc, _, hdc⟩ := eval_decCall_bit_length64 s "n3"
      (.rfield 3 (.var .local (ofString "a"))) w3
      (.return (.op .add [.const 192#64, .var .local (ofString "n3")]))
      hcode hf3 (by rw [hdc_eq]; exact hnt_dc)
    have hmid_n : mid.locals.lookup (ofString "n3") = some (.val (.word (bitLength64Pure w3))) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hret : evaluateHOLFiniteState mid (.return (.op .add [.const 192#64, .var .local (ofString "n3")])) =
        (some (.returned (.val (.word (192#64 + bitLength64Pure w3)))), emptyLocalsHOLFinite mid) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLFinite_eq_toExact, evalHOLExact, evalListHOLExact, hmid_n,
        wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hdc_eq, hret] at hdc; dsimp only at hdc
    injection hdc with hr_eq hs_eq; subst hr_eq hs_eq
    simp only [hdc_eq]
    exact ⟨trivial, (hlf_m.emptyLocals).locals _⟩

private theorem eval_u256_byte_length_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).1 =
      some (.returned (.val (.word (u256ByteLengthPure w0 w1 w2 w3)))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_u256_byte_length =
      .decCall (ofString "n") .one (ofString "u256_bit_length") [.var .local (ofString "a")]
        (.return (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64))) := rfl
  rw [hb, evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha_ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "a")] =
      some [.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha]
  have hlk := pan_u256_lookup s.code.lookup (ofString "u256_bit_length") (ofString "a")
    (sourceFnBody Guest.Software.guestFn_u256_bit_length) .one w0 w1 w2 w3
    (by rw [hcode]; exact M13.lookup_u256_bit_length)
  rw [ha_ev] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set vA := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    set cmap := HolFiniteMapExact.empty.update (ofString "a", vA)
    set ent := callEntryStateHOLFinite s cmap
    have hent_a : ent.locals.lookup (ofString "a") = some vA := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hbit : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_bit_length) with ⟨rbit, sbit⟩
    have hnt_bit : rbit ≠ some .timeOut := by
      rintro rfl; rw [hbit] at hnt; exact hnt rfl
    obtain ⟨hr_bit, hlf_bit⟩ := eval_u256_bit_length_body_exact ent w0 w1 w2 w3 hcode hent_a (by rw [hbit]; exact hnt_bit)
    rw [hbit] at hr_bit hlf_bit; dsimp only at hr_bit hlf_bit; subst hr_bit
    set nb := u256BitLengthPure w0 w1 w2 w3
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word nb) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word nb) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hbit, hsh, ↓reduceIte] at hnt ⊢
    set mid := setVarHOLFinite (ofString "n") (.val (.word nb)) { sbit with locals := s.locals }
    have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nb)) := by
      simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
    have hret : evaluateHOLFiniteState mid
        (.return (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64))) =
        (some (.returned (.val (.word (u256ByteLengthPure w0 w1 w2 w3)))), emptyLocalsHOLFinite mid) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLFinite_eq_toExact, evalHOLExact, evalListHOLExact, hmid_n,
        wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL, h3, u256ByteLengthPure, nb,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret]; dsimp only
    have h1_lf : M13.LocFrame s ent := by cases s; rfl
    exact ⟨rfl, ((((h1_lf.trans hlf_bit).locals _).setVar _ _).emptyLocals).locals _⟩

private theorem eval_decCall_u256_byte_length {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp : ExpHOL 64)
    (w0 w1 w2 w3 : BitVec 64) (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "u256_byte_length") [vExp] cont)).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      M13.LocFrame s mid ∧
      mid.locals = s.locals.update (ofString lname, .val (.word (u256ByteLengthPure w0 w1 w2 w3))) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "u256_byte_length") [vExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [vExp] =
      some [.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, hv]
  have hlk := pan_u256_lookup s.code.lookup (ofString "u256_byte_length") (ofString "a")
    (sourceFnBody Guest.Software.guestFn_u256_byte_length) .one w0 w1 w2 w3
    (by rw [hcode]; exact M13.lookup_u256_byte_length)
  rw [ha] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set vA := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    set cmap := HolFiniteMapExact.empty.update (ofString "a", vA)
    set ent := callEntryStateHOLFinite s cmap
    have hent_a : ent.locals.lookup (ofString "a") = some vA := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_byte_length) with ⟨rbl, sbl⟩
    have hnt_bl : rbl ≠ some .timeOut := by
      rintro rfl; rw [hbl] at hnt; exact hnt rfl
    obtain ⟨hr_bl, hlf_bl⟩ := eval_u256_byte_length_body_exact ent w0 w1 w2 w3 hcode hent_a (by rw [hbl]; exact hnt_bl)
    rw [hbl] at hr_bl hlf_bl; dsimp only at hr_bl hlf_bl; subst hr_bl
    set nb := u256ByteLengthPure w0 w1 w2 w3
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word nb) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word nb) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hbl, hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word nb)) { sbl with locals := s.locals }
    have hlf_all : M13.LocFrame s mid := by
      have h1 : M13.LocFrame s ent := by cases s; rfl
      exact ((h1.trans hlf_bl).locals _).setVar _ _
    exact ⟨mid, hlf_all, rfl, hnt, rfl⟩

private theorem eval_tx_u256_encoded_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hv : s.locals.lookup (ofString "v") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (txU256EncodedLenPure w0 w1 w2 w3))))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len =
      .decCall (ofString "n") .one (ofString "u256_byte_length") [.var .local (ofString "v")]
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64))
            (.return (.const 1#64)) .skip)
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
              (.ite (.cmp .lower (.rfield 0 (.var .local (ofString "v"))) (.const 128#64))
                (.return (.const 1#64)) .skip)
              .skip)
            (.return (.op .add [.const 1#64, .var .local (ofString "n")])))) := rfl
  rw [hb] at hnt ⊢
  have hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "v")) =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    simp [evalHOLExact, hv]
  obtain ⟨mid, hlf_m, hmid_loc, hnt_m, hdc⟩ := eval_decCall_u256_byte_length s "n"
    (.var .local (ofString "v")) w0 w1 w2 w3 _ hcode hv_ev hnt
  rw [hdc]
  set n0 := u256ByteLengthPure w0 w1 w2 w3
  have hn_le : n0.toNat ≤ 32 := (u256ByteLengthPure_bounds w0 w1 w2 w3).2.1
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, n0]
  have hmid_v : mid.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hv,
      show ofString "n" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_m ⊢
  have hc0 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) =
      some (.val (.word (if n0 = 0#64 then 1#64 else 0#64))) := by
    simp [evalHOLExact, hmid_n, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc0] at hnt_m ⊢; dsimp only at hnt_m ⊢
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have hn0_eq_z : (n0.toNat = 0) ↔ (n0 = 0#64) :=
    ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
  have hn0_eq_1 : (n0.toNat = 1) ↔ (n0 = 1#64) :=
    ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
  unfold txU256EncodedLenPure
  by_cases hnz : n0 = 0#64
  · rw [if_pos hnz, if_neg h10, if_pos (hn0_eq_z.mpr hnz)]
    have hret1 : evaluateHOLFiniteState mid (.return (.const 1#64)) =
        (some (.returned (.val (.word 1#64))), emptyLocalsHOLFinite mid) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLFinite_eq_toExact, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret1]; dsimp only
    exact ⟨rfl, (hlf_m.emptyLocals).locals _⟩
  · rw [if_neg hnz, if_pos h00, if_neg (mt hn0_eq_z.mp hnz), evaluateHOLFiniteState_skip]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hc1 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 1#64)) =
        some (.val (.word (if n0 = 1#64 then 1#64 else 0#64))) := by
      simp [evalHOLExact, hmid_n, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc1]; dsimp only
    have hret_add : evaluateHOLFiniteState mid (.return (.op .add [.const 1#64, .var .local (ofString "n")])) =
        (some (.returned (.val (.word (1#64 + n0)))), emptyLocalsHOLFinite mid) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLFinite_eq_toExact, evalHOLExact, evalListHOLExact, hmid_n,
        wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have h1add_eq : 1#64 + n0 = BitVec.ofNat 64 (1 + n0.toNat) := by
      apply BitVec.eq_of_toNat_eq
      have h1_bv : (1#64 : BitVec 64).toNat = 1 := rfl
      have hlt : 1 + n0.toNat < 2 ^ 64 := by omega
      simp only [BitVec.toNat_add, h1_bv, BitVec.toNat_ofNat]
    by_cases hn1 : n0 = 1#64
    · rw [if_pos hn1, if_neg h10, evaluateHOLFiniteState_ite]
      have hc128 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.cmp .lower (.rfield 0 (.var .local (ofString "v"))) (.const 128#64)) =
          some (.val (.word (if w0.toNat < 128 then 1#64 else 0#64))) := by
        simp [evalHOLExact, hmid_v, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      rw [hc128]; dsimp only
      by_cases hw128 : w0.toNat < 128
      · rw [if_pos hw128, if_neg h10, if_pos ⟨hn0_eq_1.mpr hn1, hw128⟩]
        have hret1 : evaluateHOLFiniteState mid (.return (.const 1#64)) =
            (some (.returned (.val (.word 1#64))), emptyLocalsHOLFinite mid) := by
          rw [evaluateHOLFiniteState_return]
          simp [evalHOLFinite_eq_toExact, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [hret1]; dsimp only
        exact ⟨rfl, (hlf_m.emptyLocals).locals _⟩
      · rw [if_neg hw128, if_pos h00, if_neg (fun h => hw128 h.2), evaluateHOLFiniteState_skip]
        dsimp only
        rw [hret_add, h1add_eq]; dsimp only
        exact ⟨rfl, (hlf_m.emptyLocals).locals _⟩
    · rw [if_neg hn1, if_pos h00, if_neg (fun h => hn1 (hn0_eq_1.mp h.1)), evaluateHOLFiniteState_skip]
      dsimp only
      rw [hret_add, h1add_eq]; dsimp only
      exact ⟨rfl, (hlf_m.emptyLocals).locals _⟩

private theorem eval_decCall_tx_u256_encoded_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp : ExpHOL 64)
    (w0 w1 w2 w3 : BitVec 64) (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "tx_u256_encoded_len") [vExp] cont)).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      M13.LocFrame s mid ∧
      mid.locals = s.locals.update (ofString lname,
        .val (.word (BitVec.ofNat 64 (txU256EncodedLenPure w0 w1 w2 w3)))) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "tx_u256_encoded_len") [vExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [vExp] =
      some [.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, hv]
  have hlk := pan_u256_lookup s.code.lookup (ofString "tx_u256_encoded_len") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len) .one w0 w1 w2 w3
    (by rw [hcode]; exact lookup_tx_u256_encoded_len)
  rw [ha] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set vA := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    set cmap := HolFiniteMapExact.empty.update (ofString "v", vA)
    set ent := callEntryStateHOLFinite s cmap
    have hent_v : ent.locals.lookup (ofString "v") = some vA := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hel : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len) with ⟨rel, sel⟩
    have hnt_el : rel ≠ some .timeOut := by
      rintro rfl; rw [hel] at hnt; exact hnt rfl
    obtain ⟨hr_el, hlf_el⟩ := eval_tx_u256_encoded_len_body_exact ent w0 w1 w2 w3 hcode hent_v (by rw [hel]; exact hnt_el)
    rw [hel] at hr_el hlf_el; dsimp only at hr_el hlf_el; subst hr_el
    set el := BitVec.ofNat 64 (txU256EncodedLenPure w0 w1 w2 w3)
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hel, hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word el)) { sel with locals := s.locals }
    have hlf_all : M13.LocFrame s mid := by
      have h1 : M13.LocFrame s ent := by cases s; rfl
      exact ((h1.trans hlf_el).locals _).setVar _ _
    exact ⟨mid, hlf_all, rfl, hnt, rfl⟩

private theorem pan_u256_word_lookup
    (codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL 64) (rs : ShapeHOL) (w0 w1 w2 w3 out0 : BitVec 64)
    (hne : p1 ≠ p2)
    (hlook : codeLookup fname = some ([(p1, .comb [.one, .one, .one, .one]), (p2, .one)], body, rs)) :
    let v : ValueHOL 64 := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname [v, .val (.word out0)] =
      some (body, (HolFiniteMapExact.empty.update (p1, v)).update (p2, .val (.word out0)), rs) := by
  intro v
  have raw : lookupCodeHOLExact codeLookup fname [v, .val (.word out0)] =
      some (body, (fun key => if key = p2 then some (.val (.word out0))
        else if key = p1 then some v else none), rs) := by
    simp [lookupCodeHOLExact, hlook, v, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, hne]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases one : key = p1
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hne, Ne.symm hne]
    · have backOne : p1 ≠ key := Ne.symm one
      by_cases two : key = p2
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · have backTwo : p2 ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

private theorem pan_word_u256_lookup
    (codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL 64) (rs : ShapeHOL) (dst0 w0 w1 w2 w3 : BitVec 64)
    (hne : p1 ≠ p2)
    (hlook : codeLookup fname = some ([(p1, .one), (p2, .comb [.one, .one, .one, .one])], body, rs)) :
    let v : ValueHOL 64 := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname [.val (.word dst0), v] =
      some (body, (HolFiniteMapExact.empty.update (p1, .val (.word dst0))).update (p2, v), rs) := by
  intro v
  have raw : lookupCodeHOLExact codeLookup fname [.val (.word dst0), v] =
      some (body, (fun key => if key = p2 then some v
        else if key = p1 then some (.val (.word dst0)) else none), rs) := by
    simp [lookupCodeHOLExact, hlook, v, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, hne]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases one : key = p1
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hne, Ne.symm hne]
    · have backOne : p1 ≠ key := Ne.symm one
      by_cases two : key = p2
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · have backTwo : p2 ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

private def toBeMinLoopBodyLocal : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
    (.decCall (ofString "l") .one (ofString "u256_limb")
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
      (.seq
        (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
          (.op .and
            [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
             .const 255#64]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def toBeMinWhileLocal : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) toBeMinLoopBodyLocal

private theorem eval_toBeMinLoopBodyLocal_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 out0 len iv : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hout_lo : sourceBase ≤ out0.toNat)
    (hout_hi : out0.toNat + 32 ≤ heapEnd)
    (hiv_lt : iv.toNat < len.toNat)
    (hlen_le : len.toNat ≤ 32)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hnt : (evaluateHOLFiniteState s toBeMinLoopBodyLocal).1 ≠ some .timeOut) :
    let res := evaluateHOLFiniteState s toBeMinLoopBodyLocal
    res.1 = none ∧
    M13.ByteFrame [(out0.toNat, 32)] s res.2 ∧
    res.2.code = originalRuntimeCode ∧
    res.2.memaddrs = ordinaryDomain ∧
    res.2.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) ∧
    res.2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
    res.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    res.2.locals.lookup (ofString "i") = some (.val (.word (iv + 1#64))) ∧
    (len = 1#64 → iv = 0#64 → M13.memByteAt res.2.memory res.2.be out0 = UInt8.ofNat (w0.toNat % 256)) := by
  intro res; dsimp only [res]
  dsimp only [toBeMinLoopBodyLocal] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  let posv := (len - 1#64) - iv
  have hev_pos : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")]) =
      some (.val (.word posv)) := by
    simp [evalHOLExact, evalListHOLExact, hlen, hi, wordOpHOL, wordOp, valueIsWord, valueWord, posv]
  rw [hev_pos] at hnt ⊢; dsimp only at hnt ⊢
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word posv) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh1] at hnt ⊢; dsimp only at hnt ⊢
  set s1 := setVarHOLFinite (ofString "pos") (.val (.word posv)) s
  have hs1_a : s1.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "pos" ≠ ofString "a" by decide]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "pos" ≠ ofString "out" by decide]
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen,
      show ofString "pos" ≠ ofString "len" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi,
      show ofString "pos" ≠ ofString "i" by decide]
  have hs1_pos : s1.locals.lookup (ofString "pos") = some (.val (.word posv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  let idx := posv >>> (3#64).toNat
  have ha_l : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)] =
      some [.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)], .val (.word idx)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_a, hs1_pos, wordShiftHOL, idx]
  have hlk_l := pan_u256_word_lookup s1.code.lookup (ofString "u256_limb") (ofString "a") (ofString "i")
    (sourceFnBody Guest.Software.guestFn_u256_limb) .one w0 w1 w2 w3 idx (by decide)
    (by change s.code.lookup _ = _; rw [hcode]; exact M13.lookup_u256_limb)
  rw [ha_l] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk_l] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s1.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    let vA := ValueHOL.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    let cmap := (HolFiniteMapExact.empty.update (ofString "a", vA)).update (ofString "i", .val (.word idx))
    set ent := callEntryStateHOLFinite s1 cmap
    have hent_a : ent.locals.lookup (ofString "a") = some vA := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "a" by decide]
    have hent_i : ent.locals.lookup (ofString "i") = some (.val (.word idx)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlf_l : M13.LocFrame ent (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_limb)).2 :=
      M13.locFrameW_eval _ rfl _
    have hr_l := eval_u256_limb_body_exact ent w0 w1 w2 w3 idx hent_a hent_i
    rcases hrun_l : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_limb) with ⟨rl, post_l⟩
    rw [hrun_l] at hr_l hlf_l; dsimp only at hr_l; subst hr_l
    set lv := u256LimbPure w0 w1 w2 w3 idx
    have hsh_l : (shapeEqHOL (shapeOfHOLExact (.val (.word lv) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word lv) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hrun_l, hsh_l, ↓reduceIte] at hnt ⊢
    set s2 := setVarHOLFinite (ofString "l") (.val (.word lv)) { post_l with locals := s1.locals }
    have hlf_s_s2 : M13.LocFrame s s2 := by
      have h0 : M13.LocFrame s ent := by cases s; rfl
      exact ((h0.trans hlf_l).locals _).setVar _ _
    have hs2_bf : M13.ByteFrame [(out0.toNat, 32)] s s2 := M13.ByteFrame.of_locFrame _ hlf_s_s2
    have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hma
    have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
        show ofString "l" ≠ ofString "out" by decide]
    have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
        show ofString "l" ≠ ofString "i" by decide]
    have hs2_l : s2.locals.lookup (ofString "l") = some (.val (.word lv)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs2_pos : s2.locals.lookup (ofString "pos") = some (.val (.word posv)) := by
      simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_pos,
        show ofString "l" ≠ ofString "pos" by decide]
    let dstExp : ExpHOL 64 := .op .add [.var .local (ofString "out"), .var .local (ofString "i")]
    let srcExp : ExpHOL 64 := .op .and
      [.shift .lsr (.var .local (ofString "l"))
        (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
       .const 255#64]
    let shAmt : BitVec 64 := (posv &&& 7#64) * 8#64
    let byteVal : BitVec 64 := (lv >>> shAmt.toNat) &&& 255#64
    have hdst_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) dstExp =
        some (.val (.word (out0 + iv))) := by
      simp [dstExp, evalHOLExact, evalListHOLExact, hs2_out, hs2_i, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hsrc_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) srcExp =
        some (.val (.word byteVal)) := by
      have hsh_lt : shAmt.toNat < 64 := by
        dsimp only [shAmt]
        rw [BitVec.toNat_mul, BitVec.toNat_and, show (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 by decide,
          Nat.and_two_pow_sub_one_eq_mod posv.toNat 3, show (8#64 : BitVec 64).toNat = 8 by decide]
        have hmod3 : posv.toNat % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
        have h264 : 2 ^ 64 = 18446744073709551616 := rfl
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have hnot64 : ¬ 64 ≤ shAmt.toNat := by omega
      have hws2 : wordShiftHOL .lsr lv shAmt.toNat = some (lv >>> shAmt.toNat) := by
        simp [wordShiftHOL, hnot64]
      have hsh_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]) =
          some (.val (.word shAmt)) := by
        simp [evalHOLExact, evalListHOLExact, hs2_pos, wordOpHOL, wordOp, panOpHOL,
          valueIsWord, valueWord, shAmt]
      have hlsr_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.shift .lsr (.var .local (ofString "l"))
            (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64])) =
          some (.val (.word (lv >>> shAmt.toNat))) := by
        change (match s2.locals.lookup (ofString "l"),
            @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]) with
          | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
            Option.map (fun word => ValueHOL.val (.word word)) (wordShiftHOL .lsr leftWord rightWord.toNat)
          | _, _ => none) = some (.val (.word (lv >>> shAmt.toNat)))
        rw [hs2_l, hsh_ev]; dsimp only; rw [hws2]; rfl
      have hel_and : @evalListHOLExact 64 F _ s2.toExact
          (fun a => Classical.propDecidable (s2.memaddrs a))
          [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
            .const 255#64] =
          some [ValueHOL.val (.word (lv >>> shAmt.toNat)), ValueHOL.val (.word 255#64)] := by
        unfold evalListHOLExact
        rw [hlsr_ev]
        rfl
      dsimp only [srcExp]
      unfold evalHOLExact
      rw [hel_and]
      simp [wordOpHOL, wordOp, valueIsWord, valueWord, byteVal]
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
    have haddr_nat : (out0 + iv).toNat = out0.toNat + iv.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hdom_addr : s2.memaddrs (panByteAlignHOL (out0 + iv)) := by
      rw [hs2_dom, WkBlockTxEnc.ordinaryDomain_iff]
      have hal := panByteAlign_toNat64 (out0 + iv)
      have hsb_mod : sourceBase % 8 = 0 := by rw [WkBlockTxEnc.sourceBase_val]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · omega
    have hbf_sb : M13.ByteFrame [(out0.toNat, 32)] s2 (evaluateHOLFiniteState s2 (.storeByte dstExp srcExp)).2 := by
      refine M13.byteFrame_storeByte s2 dstExp srcExp (fun addr hdst_a _ => ?_)
      rw [hdst_ev] at hdst_a
      have haddr_eq : addr = out0 + iv := (HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj hdst_a))).symm
      subst haddr_eq
      exact ⟨(out0.toNat, 32), by simp, by rw [haddr_nat]; omega, by rw [haddr_nat]; omega⟩
    obtain ⟨mem', hsb_eq, hbyte_same, _, _⟩ := M13.evaluate_storeByte_word hdst_ev hsrc_ev hdom_addr
    rw [hsb_eq] at hbf_sb; dsimp only at hbf_sb
    rw [evaluateHOLFiniteState_seq_line780, hsb_eq]; dsimp only
    set s3 : PanSemStateFiniteExact 64 F := { s2 with memory := mem' }
    rw [evaluateHOLFiniteState_assign]
    have hev_i1 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iv + 1#64))) := by
      have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := hs2_i
      simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hv_i1 : s3.isValidValueHOLFinite VarKind.local (ofString "i") (.val (.word (iv + 1#64))) = true := by
      have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := hs2_i
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs3_i, shapeOfHOLExact, shapeEqHOL]
    rw [hev_i1]; dsimp only; rw [if_pos hv_i1]; dsimp only
    have hsk : setKvarHOLFinite VarKind.local (ofString "i") (.val (.word (iv + 1#64))) s3 =
        setVarHOLFinite (ofString "i") (.val (.word (iv + 1#64))) s3 := rfl
    rw [hsk]
    let s4 := setVarHOLFinite (ofString "i") (.val (.word (iv + 1#64))) s3
    have hbf_all : M13.ByteFrame [(out0.toNat, 32)] s s4 := (hs2_bf.trans hbf_sb).setVar _ _
    let finalSt : PanSemStateFiniteExact 64 F :=
      let src1 : PanSemStateFiniteExact 64 F :=
        { s4 with locals := HolFiniteMapExact.resVarEq s4.locals (ofString "l", s1.locals.lookup (ofString "l")) }
      { src1 with locals := HolFiniteMapExact.resVarEq src1.locals (ofString "pos", s.locals.lookup (ofString "pos")) }
    have hbf_final : M13.ByteFrame [(out0.toNat, 32)] s finalSt := (hbf_all.locals _).locals _
    have hf_code : finalSt.code = originalRuntimeCode := by
      have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hcode
    have hf_dom : finalSt.memaddrs = ordinaryDomain := by
      have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hma
    have hl_ne : ∀ (m : HolFiniteMapExact MlS (ValueHOL 64)) (k q : MlS) (old : Option (ValueHOL 64)),
        k ≠ q → (HolFiniteMapExact.resVarEq m (k, old)).lookup q = m.lookup q := by
      intro m k q old hne
      rw [PanRunBounded.resVarEq_lookup, if_neg (Ne.symm hne)]
    refine ⟨rfl, hbf_final, hf_code, hf_dom, ?_, ?_, ?_, ?_, ?_⟩
    · change (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq s4.locals (ofString "l", s1.locals.lookup (ofString "l")))
        (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "a") = _
      rw [hl_ne _ _ _ _ (by decide), hl_ne _ _ _ _ (by decide)]
      have hs3_a : s3.locals.lookup (ofString "a") = some (.rStruct
          [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
        simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
          show ofString "l" ≠ ofString "a" by decide]
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_a,
        show ofString "i" ≠ ofString "a" by decide]
    · change (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq s4.locals (ofString "l", s1.locals.lookup (ofString "l")))
        (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "out") = _
      rw [hl_ne _ _ _ _ (by decide), hl_ne _ _ _ _ (by decide)]
      have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word out0)) := hs2_out
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
        show ofString "i" ≠ ofString "out" by decide]
    · change (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq s4.locals (ofString "l", s1.locals.lookup (ofString "l")))
        (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "len") = _
      rw [hl_ne _ _ _ _ (by decide), hl_ne _ _ _ _ (by decide)]
      have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word len)) := by
        simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_len,
          show ofString "l" ≠ ofString "len" by decide]
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
        show ofString "i" ≠ ofString "len" by decide]
    · change (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq s4.locals (ofString "l", s1.locals.lookup (ofString "l")))
        (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "i") = _
      rw [hl_ne _ _ _ _ (by decide), hl_ne _ _ _ _ (by decide)]
      simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · intro hlen1 hiv0
      subst hlen1; subst hiv0
      have hpos0 : posv = 0#64 := by decide
      have hidx0 : idx = 0#64 := by simp [idx, hpos0]
      have hlv0 : lv = w0 := by simp [lv, u256LimbPure, hidx0]
      have hsh0 : shAmt = 0#64 := by simp [shAmt, hpos0]
      have hbv_mod : byteVal.toNat % 256 = w0.toNat % 256 := by
        have hbv_eq : byteVal = w0 &&& 255#64 := by simp [byteVal, hlv0, hsh0]
        rw [hbv_eq, BitVec.toNat_and, show (255#64 : BitVec 64).toNat = 2 ^ 8 - 1 by decide,
          Nat.and_two_pow_sub_one_eq_mod w0.toNat 8, show 2 ^ 8 = 256 by decide]
        exact Nat.mod_mod _ 256
      have hout_add0 : out0 + 0#64 = out0 := by simp
      rw [hout_add0] at hbyte_same
      change M13.memByteAt mem' s2.be out0 = UInt8.ofNat (w0.toNat % 256)
      rw [hbyte_same, hbv_mod]

private theorem eval_toBeMinWhileLocal_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 out0 len iv : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hout_lo : sourceBase ≤ out0.toNat) (hout_hi : out0.toNat + 32 ≤ heapEnd)
    (hlen_le : len.toNat ≤ 32)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hnt : (evaluateHOLFiniteState s toBeMinWhileLocal).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s toBeMinWhileLocal).1 = none ∧
    M13.ByteFrame [(out0.toNat, 32)] s (evaluateHOLFiniteState s toBeMinWhileLocal).2 ∧
    (evaluateHOLFiniteState s toBeMinWhileLocal).2.code = originalRuntimeCode ∧
    (evaluateHOLFiniteState s toBeMinWhileLocal).2.memaddrs = ordinaryDomain ∧
    (evaluateHOLFiniteState s toBeMinWhileLocal).2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
    (evaluateHOLFiniteState s toBeMinWhileLocal).2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
    (len = 1#64 → iv = 0#64 →
      M13.memByteAt (evaluateHOLFiniteState s toBeMinWhileLocal).2.memory
        (evaluateHOLFiniteState s toBeMinWhileLocal).2.be out0 = UInt8.ofNat (w0.toNat % 256)) ∧
    (len ≠ 1#64 → iv.toNat = len.toNat →
      (evaluateHOLFiniteState s toBeMinWhileLocal).2.memory = s.memory ∧
      (evaluateHOLFiniteState s toBeMinWhileLocal).2.be = s.be) := by
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "a") = some (.rStruct
        [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) →
      st.locals.lookup (ofString "out") = some (.val (.word out0)) →
      st.locals.lookup (ofString "len") = some (.val (.word len)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState st toBeMinWhileLocal).1 ≠ some .timeOut →
      (evaluateHOLFiniteState st toBeMinWhileLocal).1 = none ∧
      M13.ByteFrame [(out0.toNat, 32)] st (evaluateHOLFiniteState st toBeMinWhileLocal).2 ∧
      (evaluateHOLFiniteState st toBeMinWhileLocal).2.code = originalRuntimeCode ∧
      (evaluateHOLFiniteState st toBeMinWhileLocal).2.memaddrs = ordinaryDomain ∧
      (evaluateHOLFiniteState st toBeMinWhileLocal).2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      (evaluateHOLFiniteState st toBeMinWhileLocal).2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      (len = 1#64 → w = 0#64 →
        M13.memByteAt (evaluateHOLFiniteState st toBeMinWhileLocal).2.memory
          (evaluateHOLFiniteState st toBeMinWhileLocal).2.be out0 = UInt8.ofNat (w0.toNat % 256)) ∧
      (w.toNat ≥ len.toNat →
        (evaluateHOLFiniteState st toBeMinWhileLocal).2.memory = st.memory ∧
        (evaluateHOLFiniteState st toBeMinWhileLocal).2.be = st.be) by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrec s.clock s iv rfl hcode hma ha hout hlen hi hnt
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun _ heq => h8 (by omega)⟩
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hst_dom hst_a hst_out hst_len hst_i hst_nt
    dsimp only [toBeMinWhileLocal] at hst_nt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hst_nt ⊢
    have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
        some (.val (.word (if w.toNat < len.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hst_i, hst_len, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
    rw [hevc] at hst_nt ⊢; dsimp only at hst_nt ⊢
    by_cases hlt_w : w.toNat < len.toNat
    · rw [if_pos hlt_w] at hst_nt ⊢
      have h1 : (1 : BitVec 64) ≠ 0 := by intro h; cases h
      rw [if_pos h1] at hst_nt ⊢
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz] at hst_nt; exact absurd rfl hst_nt
      · rw [if_neg hcz] at hst_nt ⊢
        rw [fixClockHOLFinite_evaluateState] at hst_nt ⊢
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) toBeMinLoopBodyLocal
        have hnt_body : (evaluateHOLFiniteState (decClockHOLFinite st) toBeMinLoopBodyLocal).1 ≠ some .timeOut := by
          intro hto; rw [hto] at hst_nt; exact hst_nt rfl
        have hstep := eval_toBeMinLoopBodyLocal_exact (decClockHOLFinite st) w0 w1 w2 w3 out0 len w
          hst_code hst_dom hout_lo hout_hi hlt_w hlen_le hst_a hst_out hst_len hst_i hnt_body
        dsimp only at hstep
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) toBeMinLoopBodyLocal with ⟨rb, mid⟩
        simp only [hbr] at hst_nt hcle hstep ⊢
        obtain ⟨rfl, hbf_b, hm_code, hm_dom, hm_a, hm_out, hm_len, hm_i, hm_byte1⟩ := hstep
        dsimp only at hst_nt ⊢
        have hclk_lt : mid.clock < clk := by change mid.clock ≤ st.clock - 1 at hcle; omega
        have hbf1 : M13.ByteFrame [(out0.toNat, 32)] st mid :=
          (M13.ByteFrame.of_locFrame [(out0.toNat, 32)] (s := st) (t := decClockHOLFinite st) rfl).trans hbf_b
        obtain ⟨hr_end, hbf_end, hc_end, hd_end, hl_end, ho_end, _, hmem_ge⟩ :=
          ih mid.clock hclk_lt mid (w + 1#64) rfl hm_code hm_dom hm_a hm_out hm_len hm_i hst_nt
        refine ⟨hr_end, hbf1.trans hbf_end, hc_end, hd_end, hl_end, ho_end, ?_, ?_⟩
        · intro hlen1 hw0
          have hb1 := hm_byte1 hlen1 hw0
          have hw1_ge : (w + 1#64).toNat ≥ len.toNat := by subst hlen1; subst hw0; decide
          obtain ⟨hmem_eq, hbe_eq⟩ := hmem_ge hw1_ge
          change M13.memByteAt (evaluateHOLFiniteState mid toBeMinWhileLocal).2.memory
            (evaluateHOLFiniteState mid toBeMinWhileLocal).2.be out0 = _
          rw [hmem_eq, hbe_eq]; exact hb1
        · intro hge; omega
    · rw [if_neg hlt_w] at hst_nt ⊢
      have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
      rw [if_neg h0]; dsimp only
      exact ⟨rfl, M13.ByteFrame.refl [(out0.toNat, 32)] st, hst_code, hst_dom, hst_len, hst_out,
        fun hlen1 hw0 => by subst hlen1; subst hw0; simp at hlt_w,
        fun _ => ⟨rfl, rfl⟩⟩

private theorem eval_u256_to_be_min_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w0 w1 w2 w3 out0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hout_lo : sourceBase ≤ out0.toNat) (hout_hi : out0.toNat + 32 ≤ heapEnd)
    (ha : s.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hnt : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).1 =
      some (.returned (.val (.word (u256ByteLengthPure w0 w1 w2 w3)))) ∧
    M13.ByteFrame [(out0.toNat, 32)] s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).2 ∧
    (u256ByteLengthPure w0 w1 w2 w3 = 1#64 →
      M13.memByteAt (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).2.memory
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).2.be out0 =
        UInt8.ofNat (w0.toNat % 256)) := by
  set len := u256ByteLengthPure w0 w1 w2 w3
  have hb : sourceFnBody Guest.Software.guestFn_u256_to_be_min =
      .decCall (ofString "len") .one (ofString "u256_byte_length") [.var .local (ofString "a")]
        (.dec (ofString "i") .one (.const 0#64)
          (.seq toBeMinWhileLocal (.return (.var .local (ofString "len"))))) := rfl
  rw [hb] at hnt ⊢
  obtain ⟨mid, hlf_mid, hmid_loc, hnt_mid, hdc_eq⟩ := eval_decCall_u256_byte_length s "len"
    (.var .local (ofString "a")) w0 w1 w2 w3
    (.dec (ofString "i") .one (.const 0#64)
      (.seq toBeMinWhileLocal (.return (.var .local (ofString "len")))))
    hcode ha hnt
  rw [hdc_eq]; dsimp only
  have hbf_s_mid : M13.ByteFrame [(out0.toNat, 32)] s mid :=
    M13.ByteFrame.of_locFrame [(out0.toNat, 32)] hlf_mid
  have hmid_code : mid.code = originalRuntimeCode := by rw [hbf_s_mid.1]; exact hcode
  have hmid_dom : mid.memaddrs = ordinaryDomain := by rw [hbf_s_mid.1]; exact hma
  rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢; dsimp only at hnt_mid ⊢
  have h0_ev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  rw [h0_ev] at hnt_mid ⊢; dsimp only at hnt_mid ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hnt_mid ⊢; dsimp only at hnt_mid ⊢
  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) mid
  have hs2_bf : M13.ByteFrame [(out0.toNat, 32)] s s2 := hbf_s_mid.setVar _ _
  have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
  have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hma
  have hs2_a : s2.locals.lookup (ofString "a") = some (.rStruct
      [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    simp [s2, setVarHOLFinite, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "i" ≠ ofString "a" by decide, show ofString "len" ≠ ofString "a" by decide]
  have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    simp [s2, setVarHOLFinite, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "i" ≠ ofString "out" by decide, show ofString "len" ≠ ofString "out" by decide]
  have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s2, setVarHOLFinite, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, len,
      show ofString "i" ≠ ofString "len" by decide]
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlen_le : len.toNat ≤ 32 := (u256ByteLengthPure_bounds w0 w1 w2 w3).2.1
  rw [evaluateHOLFiniteState_seq_line780] at hnt_mid ⊢
  rcases hw : evaluateHOLFiniteState s2 toBeMinWhileLocal with ⟨rw_res, s3⟩
  have hnt_w : rw_res ≠ some .timeOut := by
    rintro rfl; simp only [hw] at hnt_mid; exact hnt_mid rfl
  have hwh := eval_toBeMinWhileLocal_exact s2 w0 w1 w2 w3 out0 len 0#64
    hs2_code hs2_dom hout_lo hout_hi hlen_le hs2_a hs2_out hs2_len hs2_i (by rw [hw]; exact hnt_w)
  rw [hw] at hwh; dsimp only at hwh ⊢
  obtain ⟨rfl, hbf_w, _, _, hs3_len, _, hbyte_s3, _⟩ := hwh
  dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev_ret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.var .local (ofString "len")) = some (.val (.word len)) := by
    simp [evalHOLExact, hs3_len]
  rw [hev_ret]; dsimp only
  have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]; dsimp only
  have hbf_s_s3 : M13.ByteFrame [(out0.toNat, 32)] s s3 := hs2_bf.trans hbf_w
  have hbf_all : M13.ByteFrame [(out0.toNat, 32)] s
      { (s3.emptyLocalsHOLFinite) with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (s3.emptyLocalsHOLFinite).locals (ofString "i", mid.locals.lookup (ofString "i")))
          (ofString "len", s.locals.lookup (ofString "len")) } :=
    ((hbf_s_s3.emptyLocals).locals _).locals _
  exact ⟨rfl, hbf_all, fun h1 => hbyte_s3 h1 rfl⟩

private theorem eval_decCall_u256_to_be_min {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp outExp : ExpHOL 64)
    (w0 w1 w2 w3 out0 : BitVec 64) (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hout_lo : sourceBase ≤ out0.toNat) (hout_hi : out0.toNat + 32 ≤ heapEnd)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "u256_to_be_min") [vExp, outExp] cont)).1 ≠ some .timeOut) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.locals = s.locals.update (ofString lname, .val (.word (u256ByteLengthPure w0 w1 w2 w3))) ∧
      M13.ByteFrame [(out0.toNat, 32)] s mid ∧
      (u256ByteLengthPure w0 w1 w2 w3 = 1#64 →
        M13.memByteAt mid.memory mid.be out0 = UInt8.ofNat (w0.toNat % 256)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "u256_to_be_min") [vExp, outExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  set n0 := u256ByteLengthPure w0 w1 w2 w3
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [vExp, outExp] =
      some [.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)], .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hv, hout]
  have hlk := pan_u256_word_lookup s.code.lookup (ofString "u256_to_be_min")
    (ofString "a") (ofString "out")
    (sourceFnBody Guest.Software.guestFn_u256_to_be_min) .one w0 w1 w2 w3 out0
    (by decide) (by rw [hcode]; exact lookup_u256_to_be_min)
  dsimp only at hlk
  rw [ha] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    let vA : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    let cmap := (HolFiniteMapExact.empty.update (ofString "a", vA)).update (ofString "out", .val (.word out0))
    set ent := s.callEntryStateHOLFinite cmap
    have hent_a : ent.locals.lookup (ofString "a") = some vA := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "out" ≠ ofString "a" by decide]
    have hent_out : ent.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_to_be_min) with ⟨rb, post⟩
    have hnt_ent : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    obtain ⟨hr_body, hbf_ent, hbyte_post⟩ := eval_u256_to_be_min_body_exact ent w0 w1 w2 w3 out0
      hcode hma hout_lo hout_hi hent_a hent_out (by rw [hrun]; exact hnt_ent)
    simp only [hrun] at hr_body hbf_ent hbyte_post
    subst hr_body
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word (u256ByteLengthPure w0 w1 w2 w3)) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word (u256ByteLengthPure w0 w1 w2 w3)) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hrun, hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word n0)) { post with locals := s.locals }
    have hlf_s_ent : M13.LocFrame s ent := by cases s; rfl
    have hbf_mid : M13.ByteFrame [(out0.toNat, 32)] s mid :=
      (((M13.ByteFrame.of_locFrame [(out0.toNat, 32)] hlf_s_ent).trans hbf_ent).locals _).setVar _ _
    exact ⟨mid, rfl, hbf_mid, hbyte_post, hnt, rfl⟩

private theorem eval_decCall_rlp_encode_bytes_single_lt128 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 : BitVec 64) (bval : UInt8) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word 1#64)))
    (hsrc_al : src0.toNat % 8 = 0)
    (hsrc_lo : sourceBase ≤ src0.toNat)
    (hsrc_hi : src0.toNat < heapEnd)
    (hbyte : M13.memByteAt s.memory s.be src0 = bval)
    (hblt : bval.toNat < 128)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 1 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word 1#64)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  have hma : s.memaddrs = ordinaryDomain := hAR.1.memaddrs
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word 1#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 1#64
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word 1#64))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word 1#64)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
        .seq
          (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
            (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
              (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
                (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) (.return (.const 1)))
                .skip))
            .skip)
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
    have hent_ma : ent.memaddrs = ordinaryDomain := hma
    have hent_mem : ent.memory = s.memory := rfl
    have hent_be : ent.be = s.be := rfl
    have hsrc_align : panByteAlignHOL src0 = src0 := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64]; omega
    have hdom_src : ent.memaddrs (panByteAlignHOL src0) := by
      rw [hent_ma, hsrc_align, WkBlockTxEnc.ordinaryDomain_iff]
      exact ⟨hsrc_al, hsrc_lo, hsrc_hi⟩
    set b0 : BitVec 64 := BitVec.ofNat 64 bval.toNat
    have hlb : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.loadByte (.var .local (ofString "src"))) = some (.val (.word b0)) := by
      simp only [evalHOLExact, hent_src]
      unfold panMemLoadByteHOL; dsimp only
      unfold M13.memByteAt M13.memWordAt at hbyte
      rw [if_pos hdom_src]
      simp only [Option.map, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
      cases hm : s.memory (panByteAlignHOL src0) with
      | word cell =>
        rw [hm] at hbyte
        have hcell : (ent.memory (panByteAlignHOL src0)).1 = cell := by rw [hent_mem, hm]
        rw [hcell, hent_be, hbyte]
    have hb0_lt : b0 < 128 := by
      rw [BitVec.lt_def]
      have h128 : (128 : BitVec 64).toNat = 128 := rfl
      have hb0_nat : b0.toNat = bval.toNat := by
        dsimp [b0]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      omega
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rcases heb0 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have heb := heb0
    rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at heb
    have hev_n1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
        some (.val (.word 1)) := by
      simp [evalHOLExact, hent_n, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hev_n1] at heb; dsimp only at heb
    rw [if_neg h10, evaluateHOLFiniteState_dec_total] at heb
    dsimp only at heb
    have hsh_b : shapeEqHOL .one (shapeOfHOLExact (.val (.word b0) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [hlb] at heb; dsimp only at heb; rw [if_pos hsh_b] at heb
    set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) ent
    have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
        show ofString "b" ≠ ofString "dst" by decide]
    rw [evaluateHOLFiniteState_ite] at heb
    have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
        (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
        some (.val (.word 1)) := by
      simp [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL]
      exact hb0_lt
    rw [hev_blt] at heb; dsimp only at heb
    rw [if_neg h10, evaluateHOLFiniteState_seq_line780] at heb
    rcases hst : evaluateHOLFiniteState sb
        (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with ⟨rst, s1⟩
    rw [hst] at heb
    rcases (evaluate_storeByte_control_frame sb (.var .local (ofString "dst")) (.var .local (ofString "b"))).1 with hsn | hse
    · rw [hst] at hsn; dsimp only at hsn; subst hsn; dsimp only at heb
      have hdst_lt := storeByte_local_dst_lt_heapEnd sb dst0 _ hent_ma hsb_dst (by rw [hst])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hst (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hsb_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return] at heb
      have hret_c1 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.const 1) = some (.val (.word 1#64)) := rfl
      rw [hret_c1] at heb; dsimp only at heb
      have hsz1 : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1#64) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [if_pos hsz1] at heb; dsimp only at heb
      injection heb with hreb hseb
      subst hreb
      have hsh1 : (shapeEqHOL (shapeOfHOLExact (.val (.word 1#64) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word 1#64) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [heb0, hsh1, ↓reduceIte] at hnt hres ⊢
      let mid := setVarHOLFinite (ofString lname) (.val (.word 1#64))
        { seb with locals := s.locals }
      have heff_s_sb : M11.ByteRegionEffect s sb Rl :=
        (M11.ByteRegionEffect.refl s Rl).with_locals_clock sb.locals sb.clock
      have heff_seb : M11.ByteRegionEffect s seb Rl := by
        rw [← hseb]
        exact ((heff_s_sb.trans heff1).with_locals_clock s1.emptyLocalsHOLFinite.locals s1.emptyLocalsHOLFinite.clock).with_locals_clock _ s1.emptyLocalsHOLFinite.clock
      have heff_mid : M11.ByteRegionEffect s mid Rl :=
        heff_seb.with_locals_clock mid.locals mid.clock
      exact ⟨mid, hdst_lt, heff_mid.globals, rfl,
        HeapByteEff.of_m11_bre hAR heff_mid, hnt, hres, rfl⟩
    · rw [hst] at hse; dsimp only at hse; subst hse
      dsimp only at heb
      injection heb with hreb _
      subst hreb
      simp only [heb0] at hres
      exact False.elim (WkBlockTxEnc.not_resumes_error hres)

private theorem eval_decCall_rlp_encode_bytes_exact_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hsrc_al : src0.toNat % 8 = 0)
    (hsrc_lo : sourceBase ≤ src0.toNat)
    (hsrc_hi : src0.toNat < heapEnd)
    (hn0_hi : n0.toNat ≤ heapEnd)
    (hnotsingle : n0 = 1#64 → 128 ≤ (M13.memByteAt s.memory s.be src0).toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1) :
    ∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  have hma : s.memaddrs = ordinaryDomain := hAR.1.memaddrs
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_code : ent.code = originalRuntimeCode := hcode
    have hent_ma : ent.memaddrs = ordinaryDomain := hma
    have hent_mem : ent.memory = s.memory := rfl
    have hent_be : ent.be = s.be := rfl
    have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
        .seq
          (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
            (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
              (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
                (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
                  (.return (.const 1)))
                .skip))
            .skip)
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
    have htail : ∀ (t : PanSemStateFiniteExact 64 F),
        M11.ByteRegionEffect ent t Rl →
        t.locals = ent.locals →
        (evaluateHOLFiniteState t
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))))).1 ≠ some .timeOut →
        let out := evaluateHOLFiniteState t
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))))
        (∀ rv, out.1 = some (.returned rv) →
          ∃ len : BitVec 64, rv = .val (.word len) ∧
            len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧
            dst0.toNat < heapEnd ∧ M11.ByteRegionEffect ent out.2 Rl) ∧
        (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
      intro t heff_t ht_loc hnt_t
      dsimp only
      have ht_code : t.code = originalRuntimeCode := heff_t.code.trans hent_code
      have ht_ma : t.memaddrs = ordinaryDomain := heff_t.memaddrs.trans hent_ma
      have ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [ht_loc]; exact hent_dst
      have ht_src : t.locals.lookup (ofString "src") = some (.val (.word src0)) := by rw [ht_loc]; exact hent_src
      have ht_n : t.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [ht_loc]; exact hent_n
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_t ⊢
      have ha_t : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
          some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht_dst, ht_n]
      have hlk_wh := pan_three_word_lookup t.code.lookup (ofString "rlp_write_header")
        (ofString "dst") (ofString "base") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
        (by decide) (by decide) (by decide)
        (by rw [ht_code]; exact M11.lookup_rlp_write_header)
      simp only [ha_t, hlk_wh] at hnt_t ⊢
      by_cases hcz_t : t.clock = 0
      · simp [hcz_t] at hnt_t
      · simp only [hcz_t, ↓reduceIte] at hnt_t ⊢
        set cmap_wh := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
          (ofString "base", ValueHOL.val (.word 128))).update (ofString "n", ValueHOL.val (.word n0))
        set ent_wh := callEntryStateHOLFinite t cmap_wh
        have hwh_dst : ent_wh.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [ent_wh, cmap_wh, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
        have hwh_base : ent_wh.locals.lookup (ofString "base") = some (.val (.word 128)) := by
          simp [ent_wh, cmap_wh, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "base" by decide]
        have hwh_n : ent_wh.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          simp [ent_wh, cmap_wh, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rcases hwh : evaluateHOLFiniteState ent_wh (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
        have hnt_wh : rwh ≠ some .timeOut := by
          rintro rfl; simp only [hwh] at hnt_t; exact hnt_t rfl
        obtain ⟨hret_wh, hnonret_wh⟩ := WkBlockTxEnc.eval_rlp_write_header_body_exact ent_wh dst0 128 n0 Rl
          ht_code ht_ma hwh_dst hwh_base hwh_n
          (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
          (by rw [hwh]; exact hnt_wh)
        simp only [hwh] at hret_wh hnonret_wh hnt_t ⊢
        cases rwh with
        | none => exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact WkBlockTxEnc.not_resumes_error⟩
        | some r =>
          cases r with
          | timeOut => exact absurd rfl hnt_wh
          | exception eid ev =>
            refine ⟨fun _ h => by simp at h, fun r' hr' _ => ?_⟩
            injection hr' with hr''; subst hr''
            exact hnonret_wh (.exception eid ev) rfl (fun _ h => by cases h)
          | returned rv =>
            obtain ⟨rfl, hdst_lt, heff_wh⟩ := hret_wh rv rfl
            set h := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
            have hbnd := WkBlockTxEnc.rlpHeaderLenPure_bounds n0.toNat
            have hh_nat : h.toNat = rlpHeaderLenPure n0.toNat := by
              dsimp [h]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            dsimp only at hnt_t ⊢; rw [if_pos hsh] at hnt_t ⊢; dsimp only at hnt_t ⊢
            set mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := t.locals }
            have heff_t_mid : M11.ByteRegionEffect t mid Rl :=
              ((M11.ByteRegionEffect.refl t Rl |>.with_locals_clock ent_wh.locals ent_wh.clock).trans heff_wh).with_locals_clock mid.locals mid.clock
            have hmid_code : mid.code = originalRuntimeCode := heff_t_mid.code.trans ht_code
            have hmid_ma : mid.memaddrs = ordinaryDomain := heff_t_mid.memaddrs.trans ht_ma
            have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_dst,
                show ofString "h" ≠ ofString "dst" by decide]
            have hmid_src : mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_src,
                show ofString "h" ≠ ofString "src" by decide]
            have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_n,
                show ofString "h" ≠ ofString "n" by decide]
            have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat := by
              have hhe := hdst_lt; rw [WkBlockTxEnc.heapEnd_val] at hhe
              rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
            rcases hc_mc : evaluateHOLFiniteState mid
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")]) with ⟨rmc, smc⟩
            have hnt_mc : rmc ≠ some .timeOut := by
              rintro rfl; simp only [hc_mc] at hnt_t; exact hnt_t rfl
            have hmc := M11.eval_call_memcpy_bre_gen mid
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
              (.var .local (ofString "src"))
              (.var .local (ofString "n"))
              (dst0 + h) src0 n0 Rl hmid_code hmid_ma
              (by simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord])
              (by simp [evalHOLExact, hmid_src])
              (by simp [evalHOLExact, hmid_n])
              (fun off hoff _ => by
                obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
                exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
              (fun off hoff _ => by
                obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
                exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
              (by rw [hc_mc]; exact hnt_mc)
            dsimp only at hmc; simp only [hc_mc] at hmc hnt_t ⊢
            cases rmc with
            | some r' =>
              dsimp only
              have hnr := hmc.2 (by simp)
              refine ⟨fun rv' hrv' => False.elim (hnr (Or.inl ⟨rv', hrv'⟩)), fun r'' hr'' _ => ?_⟩
              injection hr'' with hr'''; subst hr'''; exact hnr
            | none =>
              dsimp only at hnt_t ⊢
              obtain ⟨heff_mc, hsmc_loc⟩ := hmc.1 rfl
              have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by
                rw [hsmc_loc]; exact hmid_h
              have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by
                rw [hsmc_loc]; exact hmid_n
              have hn0_lt : rlpHeaderLenPure n0.toNat + n0.toNat < 2 ^ 64 := by
                have hhe_val : heapEnd = 33806089704 := WkBlockTxEnc.heapEnd_val
                omega
              rw [evaluateHOLFiniteState_return]
              have hev_ret : @evalHOLExact 64 F _ smc.toExact
                  (fun a => Classical.propDecidable (smc.memaddrs a))
                  (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                  some (.val (.word (h + n0))) := by
                simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
              rw [hev_ret]; dsimp only
              have hsz : sizeOfShapeWithContextHOL smc.structs (shapeOfHOLExact (.val (.word (h + n0)) : ValueHOL 64)) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hsz]; dsimp only
              have hhn_eq : (h + n0).toNat = rlpHeaderLenPure n0.toNat + n0.toNat := by
                rw [BitVec.toNat_add, hh_nat, Nat.mod_eq_of_lt hn0_lt]
              refine ⟨fun rv' hrv' => ?_, fun r' hr' hnr => ?_⟩
              · injection hrv' with h1; injection h1 with h2
                exact ⟨h + n0, h2.symm, hhn_eq, hdst_lt,
                  (((heff_t.trans heff_t_mid).trans heff_mc).with_locals_clock _ _).with_locals_clock _ _⟩
              · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
          | «break» | «continue» | error =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact WkBlockTxEnc.not_resumes_error⟩
          | finalFfi _ =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ hr => by
              injection hr' with hr''; subst hr''
              rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    have hbody :
        let out := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (∀ rv, out.1 = some (.returned rv) →
          ∃ len : BitVec 64, rv = .val (.word len) ∧
            len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧
            dst0.toNat < heapEnd ∧ M11.ByteRegionEffect ent out.2 Rl) ∧
        (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
      dsimp only
      have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 ≠ some .timeOut := by
        intro hto; rw [hto] at hnt; exact hnt rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_ent ⊢
      have hev_n1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
          some (.val (.word (if n0 = 1 then 1 else 0))) := by
        simp [evalHOLExact, hent_n, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_n1] at hnt_ent ⊢; dsimp only at hnt_ent ⊢
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      by_cases hn1 : n0 = 1
      · rw [if_pos hn1, if_neg h10, evaluateHOLFiniteState_dec_total] at hnt_ent ⊢
        dsimp only at hnt_ent ⊢
        have hn1_64 : n0 = 1#64 := hn1
        have hbge : 128 ≤ (M13.memByteAt s.memory s.be src0).toNat := hnotsingle hn1_64
        set bval := M13.memByteAt s.memory s.be src0
        have hsrc_align : panByteAlignHOL src0 = src0 := by
          apply BitVec.eq_of_toNat_eq; rw [panByteAlign_toNat64]; omega
        have hdom_src : ent.memaddrs (panByteAlignHOL src0) := by
          rw [hent_ma, hsrc_align, WkBlockTxEnc.ordinaryDomain_iff]
          exact ⟨hsrc_al, hsrc_lo, hsrc_hi⟩
        set b0 : BitVec 64 := BitVec.ofNat 64 bval.toNat
        have hlb : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.loadByte (.var .local (ofString "src"))) = some (.val (.word b0)) := by
          simp only [evalHOLExact, hent_src]
          unfold panMemLoadByteHOL; dsimp only
          rw [if_pos hdom_src]
          simp only [Option.map, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
          have hcell : (ent.memory (panByteAlignHOL src0)).1 = M13.memWordAt s.memory (panByteAlignHOL src0) := by
            rw [hent_mem]; rfl
          rw [hcell, hent_be]; rfl
        have hsh_b : shapeEqHOL .one (shapeOfHOLExact (.val (.word b0) : ValueHOL 64)) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [hlb] at hnt_ent ⊢; dsimp only at hnt_ent ⊢
        rw [if_pos hsh_b] at hnt_ent ⊢
        set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) ent
        have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
          simp only [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, beq_self_eq_true, ↓reduceIte]
        have hb0_ge : ¬ (b0 < 128) := by
          rw [BitVec.lt_def]
          have h128 : (128 : BitVec 64).toNat = 128 := rfl
          have hb0_nat : b0.toNat = bval.toNat := by
            dsimp [b0]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := bval.toNat_lt; omega)
          omega
        rw [evaluateHOLFiniteState_ite] at hnt_ent ⊢
        have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
            (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
            some (.val (.word 0)) := by
          simp only [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL, hb0_ge, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [hev_blt] at hnt_ent ⊢; dsimp only at hnt_ent ⊢
        rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt_ent ⊢
        dsimp only at hnt_ent ⊢
        let s' : PanSemStateFiniteExact 64 F :=
          { sb with locals := HolFiniteMapExact.resVarEq sb.locals (ofString "b", ent.locals.lookup (ofString "b")) }
        have hs'_loc : s'.locals = ent.locals := by
          apply HolFiniteMapExact.ext; funext k
          change (HolFiniteMapExact.resVarEq sb.locals (ofString "b", ent.locals.lookup (ofString "b"))).lookup k = ent.locals.lookup k
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hk : k = ofString "b"
          · subst hk; simp
          · simp [hk, sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact htail s' ((M11.ByteRegionEffect.refl ent Rl).with_locals_clock s'.locals s'.clock) hs'_loc hnt_ent
      · rw [if_neg hn1, if_pos rfl, evaluateHOLFiniteState_skip] at hnt_ent ⊢
        dsimp only at hnt_ent ⊢
        exact htail ent (M11.ByteRegionEffect.refl ent Rl) rfl hnt_ent
    dsimp only at hbody
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; simp only [heb] at hnt; exact hnt rfl
    simp only [heb] at hbody hnt hres ⊢
    obtain ⟨hret, hnonret⟩ := hbody
    cases reb with
    | none => exact False.elim (WkBlockTxEnc.not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hres)
      | returned rv =>
        obtain ⟨len, rfl, hlen, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨len, mid, hlen, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid, hnt, hres, rfl⟩
      | «break» | «continue» | error =>
        exact False.elim (WkBlockTxEnc.not_resumes_error hres)
      | finalFfi _ =>
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem eval_tx_put_u256_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 w0 w1 w2 w3 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hv : s.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + txU256EncodedLenPure w0 w1 w2 w3 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_u256)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_u256)).1) :
    ∃ len : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_u256)).1 =
        some (.returned (.val (.word len))) ∧
      len.toNat = txU256EncodedLenPure w0 w1 w2 w3 ∧
      1 ≤ len.toNat ∧ len.toNat ≤ 33 ∧
      dst0.toNat < heapEnd ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_u256)).2.globals = s.globals ∧
      HeapByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_tx_put_u256)).2 Rl gw := by
  have hb : sourceFnBody Guest.Software.guestFn_tx_put_u256 =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "tmp") .one (ofString "alloc") [.const 32#64]
          (.decCall (ofString "n") .one (ofString "u256_to_be_min")
            [.var .local (ofString "v"), .var .local (ofString "tmp")]
            (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
              [.var .local (ofString "dst"), .var .local (ofString "tmp"), .var .local (ofString "n")]
              (.seq
                (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                (.return (.var .local (ofString "w"))))))) := rfl
  rw [hb] at hnt hres ⊢
  obtain ⟨mark, s1, hs_hp_lk, hmark_nat, hs1_glob, hs1_mem, hs1_loc, heff1, hnt1, hdc1⟩ :=
    WkBlockTxEnc.eval_decCall_heap_mark s "mark" _ Rl gw hcode hAR hnt
  rw [hdc1] at hres ⊢
  dsimp only at hres ⊢
  have hs1_code : s1.code = originalRuntimeCode := by rw [← hcode]; exact heff1.arena.1.code.trans hcode.symm
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hdst,
      show ofString "mark" ≠ ofString "dst" by decide]
  have hs1_v : s1.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hv,
      show ofString "mark" ≠ ofString "v" by decide]
  obtain ⟨tmp, n_alloc, q_alloc, s2, hn32_ev, htmp_nat, htmp_al, _, htmp_q, hq_lim, _,
      _, hs2_glob, hs2_mem, hs2_loc, heff2, hnt2, hres2, hdc2⟩ :=
    WkBlockTxEnc.eval_decCall_alloc_resumes s1 "tmp" (.const 32#64) _ Rl gw
      heff1.arena.1.code heff1.arena hgw hnt1 hres
  have hn32_eq : n_alloc = 32#64 := by
    simp only [evalHOLExact, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hn32_ev
    exact hn32_ev.symm
  subst hn32_eq
  rw [hdc2]
  dsimp only
  have heff_s_s2 : HeapByteEff s s2 Rl gw := heff1.trans heff2
  have hmark_eq_s1 : globN s1 "heap_ptr" = globN s "heap_ptr" := by simp [globN, hs1_glob]
  have htmp_eq_mark : tmp.toNat = globN s "heap_ptr" := htmp_nat.trans hmark_eq_s1
  have htmp_lo : sourceBase ≤ tmp.toNat := by rw [htmp_eq_mark]; exact hAR.2.1
  have h32_nat : (32#64 : BitVec 64).toNat = 32 := rfl
  have hhl_lt_he : heapLimit < heapEnd := by
    rw [WkBlockTxEnc.heapLimit_val, WkBlockTxEnc.heapEnd_val]; decide
  have htmp_hi32 : tmp.toNat + 32 ≤ heapLimit := by omega
  have htmp_hi_he : tmp.toNat + 32 ≤ heapEnd := by omega
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "tmp" ≠ ofString "mark" by decide]
  have hs2_tmp : s2.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_dst,
      show ofString "tmp" ≠ ofString "dst" by decide]
  have hs2_v : s2.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_v,
      show ofString "tmp" ≠ ofString "v" by decide]
  obtain ⟨s3, hs3_loc, hbf3, hbyte3, hnt3, hdc3⟩ := eval_decCall_u256_to_be_min s2 "n"
    (.var .local (ofString "v")) (.var .local (ofString "tmp")) w0 w1 w2 w3 tmp _
    heff2.arena.1.code heff2.arena.1.memaddrs htmp_lo htmp_hi_he
    (by simp [evalHOLExact, hs2_v]) (by simp [evalHOLExact, hs2_tmp]) hnt2
  rw [hdc3] at hres2 ⊢
  dsimp only at hres2 ⊢
  have heff3_raw : HeapByteEff s2 s3 [(tmp.toNat, 32)] gw :=
    heapByteEff_of_byteFrame heff2.arena hbf3
  have hs3_glob : s3.globals = s2.globals := by rw [hbf3.1]
  have heff_s_s2_ext : HeapByteEff s s2 ((tmp.toNat, 32) :: Rl) gw :=
    heff_s_s2.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ h => h)
  have heff_s2_s3_ext : HeapByteEff s2 s3 ((tmp.toNat, 32) :: Rl) gw :=
    heff3_raw.mono (fun i hi _ => by
      simp only [List.mem_singleton] at hi; subst hi
      exact Or.inl ⟨(tmp.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩) (fun _ h => h)
  have heff_s_s3 : HeapByteEff s s3 Rl gw :=
    (heff_s_s2_ext.trans heff_s2_s3_ext).mono (fun i hi _ => by
      rcases List.mem_cons.1 hi with rfl | hi_rl
      · exact Or.inr (Or.inr ⟨by omega, htmp_hi32⟩)
      · exact Or.inl ⟨i, hi_rl, le_rfl, le_rfl⟩) (fun _ h => h)
  set n0 := u256ByteLengthPure w0 w1 w2 w3
  have hbnd_u := u256ByteLengthPure_bounds w0 w1 w2 w3
  have hn0_le32 : n0.toNat ≤ 32 := hbnd_u.2.1
  have htxlen_lo : 1 ≤ txU256EncodedLenPure w0 w1 w2 w3 := hbnd_u.2.2.2.2.1
  have htxlen_hi : txU256EncodedLenPure w0 w1 w2 w3 ≤ 33 := hbnd_u.2.2.2.2.2
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, n0]
  have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_mark,
      show ofString "n" ≠ ofString "mark" by decide]
  have hs3_tmp : s3.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_tmp,
      show ofString "n" ≠ ofString "tmp" by decide]
  have hs3_dst : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_dst,
      show ofString "n" ≠ ofString "dst" by decide]
  have hstep4 : ∃ (len : BitVec 64) (s4 : PanSemStateFiniteExact 64 F),
      len.toNat = txU256EncodedLenPure w0 w1 w2 w3 ∧
      dst0.toNat < heapEnd ∧
      s4.globals = s3.globals ∧
      s4.locals = s3.locals.update (ofString "w", .val (.word len)) ∧
      HeapByteEff s3 s4 Rl gw ∧
      (evaluateHOLFiniteState s4
        (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
          (.return (.var .local (ofString "w"))))).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s3
        (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
          [.var .local (ofString "dst"), .var .local (ofString "tmp"), .var .local (ofString "n")]
          (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
            (.return (.var .local (ofString "w")))))) =
        ((evaluateHOLFiniteState s4
          (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
            (.return (.var .local (ofString "w"))))).1,
         { (evaluateHOLFiniteState s4
            (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
              (.return (.var .local (ofString "w"))))).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s4
            (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
              (.return (.var .local (ofString "w"))))).2.locals
             (ofString "w", s3.locals.lookup (ofString "w")) }) := by
    by_cases hsingle : n0 = 1#64 ∧ w0.toNat < 128
    · obtain ⟨hn1, hw0_lt⟩ := hsingle
      have hlen_pure1 : txU256EncodedLenPure w0 w1 w2 w3 = 1 := by
        have hn1_nat : n0.toNat = 1 := by rw [hn1]; rfl
        unfold txU256EncodedLenPure; dsimp only
        change (if n0.toNat = 0 then 1 else if n0.toNat = 1 ∧ w0.toNat < 128 then 1 else 1 + n0.toNat) = 1
        rw [if_neg (by omega), if_pos ⟨hn1_nat, hw0_lt⟩]
      have hb_eq : M13.memByteAt s3.memory s3.be tmp = UInt8.ofNat (w0.toNat % 256) := hbyte3 hn1
      have hblt : (UInt8.ofNat (w0.toNat % 256)).toNat < 128 := by
        have hm256 : w0.toNat % 256 = w0.toNat := Nat.mod_eq_of_lt (by omega)
        rw [hm256, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        exact hw0_lt
      obtain ⟨s4, hdst_lt, hs4_glob, hs4_loc, heff4, hnt4, _, hdc4⟩ :=
        eval_decCall_rlp_encode_bytes_single_lt128 s3 "w"
          (.var .local (ofString "dst")) (.var .local (ofString "tmp")) (.var .local (ofString "n"))
          dst0 tmp (UInt8.ofNat (w0.toNat % 256)) _ Rl gw
          heff_s_s3.arena.1.code heff_s_s3.arena
          (by simp [evalHOLExact, hs3_dst])
          (by simp [evalHOLExact, hs3_tmp])
          (by simp [evalHOLExact, hs3_n, hn1])
          htmp_al htmp_lo (by omega) hb_eq hblt
          (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; rw [hlen_pure1] at h2; exact ⟨ivl, hivl, h1, h2⟩)
          hnt3 hres2
      exact ⟨1#64, s4, hlen_pure1.symm, hdst_lt, hs4_glob, hs4_loc, heff4, hnt4, hdc4⟩
    · have hhdr_eq : rlpHeaderLenPure n0.toNat + n0.toNat = txU256EncodedLenPure w0 w1 w2 w3 := by
        have hhdr1 : rlpHeaderLenPure n0.toNat = 1 :=
          WkBlockTxEnc.rlpHeaderLenPure_of_le55 (by omega)
        rw [hhdr1]
        unfold txU256EncodedLenPure; dsimp only
        change 1 + n0.toNat = (if n0.toNat = 0 then 1 else if n0.toNat = 1 ∧ w0.toNat < 128 then 1 else 1 + n0.toNat)
        by_cases hnz : n0.toNat = 0
        · rw [if_pos hnz, hnz]
        · rw [if_neg hnz]
          have hns_nat : ¬ (n0.toNat = 1 ∧ w0.toNat < 128) := by
            rintro ⟨h1n, hwlt⟩
            exact hsingle ⟨BitVec.eq_of_toNat_eq h1n, hwlt⟩
          rw [if_neg hns_nat]
      have hnotsingle : n0 = 1#64 → 128 ≤ (M13.memByteAt s3.memory s3.be tmp).toNat := by
        intro hn1
        have hw0_256 : w0.toNat < 256 := (hbnd_u.2.2.2.1 hn1).2.2.2
        have hw0_ge : 128 ≤ w0.toNat := by
          by_contra hlt; exact hsingle ⟨hn1, by omega⟩
        have hb_eq := hbyte3 hn1
        rw [hb_eq, Nat.mod_eq_of_lt hw0_256, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw0_256]
        exact hw0_ge
      obtain ⟨len, s4, hlen_eq, hdst_lt, hs4_glob, hs4_loc, heff4, hnt4, _, hdc4⟩ :=
        eval_decCall_rlp_encode_bytes_exact_len s3 "w"
          (.var .local (ofString "dst")) (.var .local (ofString "tmp")) (.var .local (ofString "n"))
          dst0 tmp n0 _ Rl gw
          heff_s_s3.arena.1.code heff_s_s3.arena
          (by simp [evalHOLExact, hs3_dst])
          (by simp [evalHOLExact, hs3_tmp])
          (by simp [evalHOLExact, hs3_n])
          htmp_al htmp_lo (by omega) (by omega) hnotsingle
          (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
          hnt3 hres2
      exact ⟨len, s4, hlen_eq.trans hhdr_eq, hdst_lt, hs4_glob, hs4_loc, heff4, hnt4, hdc4⟩
  obtain ⟨len, s4, hlen_eq, hdst_lt, hs4_glob, hs4_loc, heff4, hnt4, hdc4⟩ := hstep4
  rw [hdc4]
  dsimp only
  have heff_s_s4 : HeapByteEff s s4 Rl gw := heff_s_s3.trans heff4
  have hs4_mark : s4.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_mark,
      show ofString "w" ≠ ofString "mark" by decide]
  have hs4_w : s4.locals.lookup (ofString "w") = some (.val (.word len)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt4 ⊢
  rcases hc_hr : evaluateHOLFiniteState s4
    (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) with ⟨rhr, s5⟩
  have hnt_hr : rhr ≠ some .timeOut := by
    rintro rfl; simp only [hc_hr] at hnt4; exact hnt4 rfl
  have hmark_lo_sb : sourceBase ≤ mark.toNat := by rw [hmark_nat]; exact hAR.2.1
  have hmark_hi : mark.toNat ≤ heapLimit := by rw [hmark_nat]; exact hAR.2.2.1
  have hmark_8 : mark.toNat % 8 = 0 := by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1
  have hhr := WkBlockTxEnc.eval_call_heap_release s4 (.var .local (ofString "mark")) mark Rl gw
    heff_s_s4.arena.1.code heff_s_s4 hgw
    (by simp [evalHOLExact, hs4_mark])
    (by rw [hmark_nat]) hmark_lo_sb hmark_hi hmark_8 (by rw [hc_hr]; exact hnt_hr)
  dsimp only at hhr
  simp only [hc_hr] at hhr hnt4 ⊢
  obtain ⟨rfl, hs5_loc, hs5_glob, _, heff_s_s5⟩ := hhr
  dsimp only
  have hs5_w : s5.locals.lookup (ofString "w") = some (.val (.word len)) := by
    rw [hs5_loc]; exact hs4_w
  rw [evaluateHOLFiniteState_return]
  have hev_ret : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
      (.var .local (ofString "w")) = some (.val (.word len)) := by
    simp [evalHOLExact, hs5_w]
  rw [hev_ret]; dsimp only
  have hsz : sizeOfShapeWithContextHOL s5.structs (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]; dsimp only
  have hs5_glob_eq : s5.globals = s.globals := by
    rw [hs5_glob, hs4_glob, hs3_glob, hs2_glob, hs1_glob]
    apply HolFiniteMapExact.ext; funext k
    by_cases hk : k = ofString "heap_ptr"
    · subst hk; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_hp_lk]
    · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  let finalPost : PanSemStateFiniteExact 64 F :=
    { s5.emptyLocalsHOLFinite with
      locals := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq s5.emptyLocalsHOLFinite.locals
              (ofString "w", s3.locals.lookup (ofString "w")))
            (ofString "n", s2.locals.lookup (ofString "n")))
          (ofString "tmp", s1.locals.lookup (ofString "tmp")))
        (ofString "mark", s.locals.lookup (ofString "mark")) }
  have heff_final : HeapByteEff s finalPost Rl gw :=
    (heff_s_s5.locals_clock s5.emptyLocalsHOLFinite.locals s5.emptyLocalsHOLFinite.clock).locals_clock
      finalPost.locals finalPost.clock
  exact ⟨len, rfl, hlen_eq, by omega, by omega, hdst_lt, hs5_glob_eq, heff_final⟩

private theorem eval_decCall_tx_put_u256 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp vExp : ExpHOL 64)
    (dst0 w0 w1 w2 w3 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + txU256EncodedLenPure w0 w1 w2 w3 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "tx_put_u256") [dstExp, vExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "tx_put_u256") [dstExp, vExp] cont)).1) :
    ∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat = txU256EncodedLenPure w0 w1 w2 w3 ∧
      1 ≤ len.toNat ∧ len.toNat ≤ 33 ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "tx_put_u256") [dstExp, vExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, vExp] =
      some [.val (.word dst0), .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hv]
  have hlk := pan_word_u256_lookup s.code.lookup (ofString "tx_put_u256")
    (ofString "dst") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_tx_put_u256) .one dst0 w0 w1 w2 w3
    (by decide) (by rw [hcode]; exact lookup_tx_put_u256)
  dsimp only at hlk
  rw [ha] at hnt hres ⊢; dsimp only at hnt hres ⊢; rw [hlk] at hnt hres ⊢; dsimp only at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    let vV : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    let cmap := (HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update (ofString "v", vV)
    set ent := s.callEntryStateHOLFinite cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "dst" by decide]
    have hent_v : ent.locals.lookup (ofString "v") = some vV := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlf_s_ent : M13.LocFrame s ent := by cases s; rfl
    have hent_ar : ArenaReady ent := hlf_s_ent.arenaReady hAR
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_u256) with ⟨rb, post⟩
    have hnt_ent : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    have hres_ent : Resumes rb := by
      cases rb with
      | none => simp only [hrun] at hres; exact False.elim (WkBlockTxEnc.not_resumes_error hres)
      | some r =>
        cases r with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev =>
          simp only [hrun] at hres
          rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        | timeOut => exact absurd rfl hnt_ent
        | finalFfi _ =>
          simp only [hrun] at hres
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | «break» | «continue» | error =>
          simp only [hrun] at hres; exact False.elim (WkBlockTxEnc.not_resumes_error hres)
    obtain ⟨len, hrb, hlen_eq, hlen1, hlen33, hdst_lt, hpost_glob, heff_ent⟩ :=
      eval_tx_put_u256_body_exact ent dst0 w0 w1 w2 w3 Rl gw hcode hent_ar hgw hent_dst hent_v hin_ivl
        (by rw [hrun]; exact hnt_ent) (by rw [hrun]; exact hres_ent)
    simp only [hrun] at hrb hpost_glob heff_ent
    subst hrb
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hrun, hsh, ↓reduceIte] at hnt hres ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { post with locals := s.locals }
    have heff_mid : HeapByteEff s mid Rl gw :=
      ((HeapByteEff.of_locFrame hAR hlf_s_ent Rl gw).trans heff_ent).locals_clock mid.locals mid.clock
    exact ⟨len, mid, hlen_eq, hlen1, hlen33, hdst_lt, hpost_glob, rfl, heff_mid, hnt, hres, rfl⟩

private theorem eval_call_local_tx_put_u256 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp vExp : ExpHOL 64)
    (dst0 w0 w1 w2 w3 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + txU256EncodedLenPure w0 w1 w2 w3 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_u256")
        [dstExp, vExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_u256")
        [dstExp, vExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = txU256EncodedLenPure w0 w1 w2 w3 ∧
        1 ≤ len.toNat ∧ len.toNat ≤ 33 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, vExp] =
      some [.val (.word dst0), .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hv]
  have hlk := pan_word_u256_lookup s.code.lookup (ofString "tx_put_u256")
    (ofString "dst") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_tx_put_u256) .one dst0 w0 w1 w2 w3
    (by decide) (by rw [hcode]; exact lookup_tx_put_u256)
  dsimp only at hlk
  rw [ha] at hnt ⊢; dsimp only at hnt ⊢; rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    let vV : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    let cmap := (HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update (ofString "v", vV)
    set ent := s.callEntryStateHOLFinite cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "dst" by decide]
    have hent_v : ent.locals.lookup (ofString "v") = some vV := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlf_s_ent : M13.LocFrame s ent := by cases s; rfl
    have hent_ar : ArenaReady ent := hlf_s_ent.arenaReady hAR
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_u256) with ⟨rb, post⟩
    have hnt_ent : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    simp only [hrun] at hnt ⊢
    cases rb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_ent
      | exception eid ev =>
        refine ⟨fun h => by simp at h, fun _ hres_call => ?_⟩
        have hres_ent : Resumes (some (.exception eid ev)) := by
          rcases hres_call with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨len, hrb, _⟩ := eval_tx_put_u256_body_exact ent dst0 w0 w1 w2 w3 Rl gw
          hcode hent_ar hgw hent_dst hent_v hin_ivl
          (by rw [hrun]; exact hnt_ent) (by rw [hrun]; exact hres_ent)
        simp only [hrun] at hrb; cases hrb
      | returned rv =>
        have hres_ent : Resumes (some (.returned rv)) := Or.inl ⟨rv, rfl⟩
        obtain ⟨len, hrb, hlen_eq, hlen1, hlen33, hdst_lt, hpost_glob, heff_ent⟩ :=
          eval_tx_put_u256_body_exact ent dst0 w0 w1 w2 w3 Rl gw
            hcode hent_ar hgw hent_dst hent_v hin_ivl
            (by rw [hrun]; exact hnt_ent) (by rw [hrun]; exact hres_ent)
        simp only [hrun] at hrb hpost_glob heff_ent
        injection hrb with hrv; injection hrv with hrv'
        subst hrv'
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { post with locals := s.locals }
        have heff_mid : HeapByteEff s mid Rl gw :=
          ((HeapByteEff.of_locFrame hAR hlf_s_ent Rl gw).trans heff_ent).locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen_eq, hlen1, hlen33, hdst_lt, hpost_glob, rfl, heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 12: Memory Frame & Word/U256 Load Helpers and `rlp_encode_bytes` Local Call -/

private theorem eval_call_local_rlp_encode_bytes_le {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; rw [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := WkBlockTxEnc.eval_rlp_encode_bytes_body_exact ent dst0 src0 n0 Rl
      hcode hAR.1.memaddrs hent_dst hent_src hent_n hin_ivl (by rw [heb]; exact hnt_eb)
    rw [heb] at hret hnonret
    dsimp only at hret hnonret
    simp only [heb] at hnt ⊢
    cases reb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen_le, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen_le, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem eval_call_local_rlp_encode_bytes_ge2 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hn_ne1 : n0 ≠ 1#64)
    (hn0_hi : n0.toNat ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_encode_bytes")
        [dstExp, srcExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hma : s.memaddrs = ordinaryDomain := hAR.1.memaddrs
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
        .seq
          (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
            (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
              (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
                (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b")))
                  (.return (.const 1)))
                .skip))
            .skip)
          (.decCall (ofString "h") .one (ofString "rlp_write_header")
            [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                 .var .local (ofString "src"),
                 .var .local (ofString "n")])
              (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
    have hbody :
        let outb := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (outb.1 ≠ some .timeOut) →
        (∀ rv, outb.1 = some (.returned rv) →
          ∃ len : BitVec 64, rv = .val (.word len) ∧
            len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧
            dst0.toNat < heapEnd ∧ M11.ByteRegionEffect ent outb.2 Rl) ∧
        (∀ r, outb.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
      intro outb hnt_ent
      dsimp only [outb] at hnt_ent ⊢
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_ent ⊢
      have hev_n1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
          some (.val (.word 0)) := by
        simp [evalHOLExact, hent_n, Compiler.Encoders.Asm.wordCmpHOL, hn_ne1]
      rw [hev_n1] at hnt_ent ⊢; dsimp only at hnt_ent ⊢
      rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt_ent ⊢
      dsimp only at hnt_ent ⊢
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_ent ⊢
      have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
          some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_n]
      have hlk2 := pan_three_word_lookup ent.code.lookup (ofString "rlp_write_header")
        (ofString "dst") (ofString "base") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
        (by decide) (by decide) (by decide)
        (by change s.code.lookup _ = _; rw [hcode]; exact M11.lookup_rlp_write_header)
      simp only [ha2, hlk2] at hnt_ent ⊢
      by_cases hcz2 : ent.clock = 0
      · simp [hcz2] at hnt_ent
      · simp only [hcz2, ↓reduceIte] at hnt_ent ⊢
        set cmap2 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
          (ofString "base", ValueHOL.val (.word 128))).update (ofString "n", ValueHOL.val (.word n0))
        set ent2 := callEntryStateHOLFinite ent cmap2
        have hent2_dst : ent2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
        have hent2_base : ent2.locals.lookup (ofString "base") = some (.val (.word 128)) := by
          simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "base" by decide]
        have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hin_wh : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure n0.toNat ≤ ivl.1 + ivl.2 := by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩
        rcases hwh : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
        have hnt_wh : rwh ≠ some .timeOut := by
          rintro rfl; simp only [hwh] at hnt_ent; exact hnt_ent rfl
        obtain ⟨hret_wh, hnonret_wh⟩ := WkBlockTxEnc.eval_rlp_write_header_body_exact ent2 dst0 128 n0 Rl
          hcode hma hent2_dst hent2_base hent2_n hin_wh (by rw [hwh]; exact hnt_wh)
        rw [hwh] at hret_wh hnonret_wh
        dsimp only at hret_wh hnonret_wh
        simp only [hwh] at hnt_ent ⊢
        cases rwh with
        | none =>
          exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact WkBlockTxEnc.not_resumes_error⟩
        | some r =>
          cases r with
          | timeOut => exact absurd rfl hnt_wh
          | exception eid ev =>
            refine ⟨fun _ h => by simp at h, fun r' hr' _ => ?_⟩
            injection hr' with hr''; subst hr''
            exact hnonret_wh (.exception eid ev) rfl (fun _ h => by cases h)
          | returned rv =>
            obtain ⟨rfl, hdst_lt, heff_wh⟩ := hret_wh rv rfl
            set h := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
            have hsh_h : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            dsimp only at hnt_ent ⊢
            rw [if_pos hsh_h] at hnt_ent ⊢
            set mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := ent.locals }
            have heff_ent_mid : M11.ByteRegionEffect ent mid Rl :=
              (((M11.ByteRegionEffect.refl ent Rl).with_locals_clock ent2.locals ent2.clock).trans heff_wh).with_locals_clock mid.locals mid.clock
            have hmid_code : mid.code = originalRuntimeCode := heff_ent_mid.code.trans hcode
            have hmid_ma : mid.memaddrs = ordinaryDomain := heff_ent_mid.memaddrs.trans hma
            have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
                show ofString "h" ≠ ofString "dst" by decide]
            have hmid_src : mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_src,
                show ofString "h" ≠ ofString "src" by decide]
            have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
                show ofString "h" ≠ ofString "n" by decide]
            have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hbnd := rlpHeaderLenPure_bounds n0.toNat
            have hh_nat : h.toNat = rlpHeaderLenPure n0.toNat := by
              dsimp [h]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            have hhe264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
            have hdsth_nat : (dst0 + h).toNat = dst0.toNat + rlpHeaderLenPure n0.toNat := by
              rw [BitVec.toNat_add, hh_nat]
              exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hdst_lt; omega)
            have hin_mc : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ (dst0 + h).toNat ∧
                (dst0 + h).toNat + n0.toNat ≤ ivl.1 + ivl.2 := by
              intro _; rw [hdsth_nat]; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
              exact ⟨ivl, hivl, by omega, h2⟩
            change (evaluateHOLFiniteState mid
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                   .var .local (ofString "src"),
                   .var .local (ofString "n")])
                (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).1 ≠ some .timeOut at hnt_ent
            rw [evaluateHOLFiniteState_seq_line780] at hnt_ent ⊢
            rcases hc_mc : evaluateHOLFiniteState mid
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                   .var .local (ofString "src"),
                   .var .local (ofString "n")]) with ⟨rmc, smc⟩
            have hnt_mc : rmc ≠ some .timeOut := by
              rintro rfl; simp only [hc_mc] at hnt_ent; exact hnt_ent rfl
            have hmc := M11.eval_call_memcpy_bre mid
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
              (.var .local (ofString "src"))
              (.var .local (ofString "n"))
              (dst0 + h) src0 n0 Rl hmid_code hmid_ma
              (by simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord])
              (by simp [evalHOLExact, hmid_src])
              (by simp [evalHOLExact, hmid_n])
              hin_mc
              (by rw [hc_mc]; exact hnt_mc)
            dsimp only at hmc
            rw [hc_mc] at hmc
            simp only [hc_mc] at hnt_ent ⊢
            cases rmc with
            | some r' =>
              have hnr := hmc.2 (by simp)
              refine ⟨fun rv' hrv' => False.elim (hnr (Or.inl ⟨rv', hrv'⟩)), fun r'' hr'' _ => ?_⟩
              injection hr'' with hr'''; subst hr'''; exact hnr
            | none =>
              dsimp only at hnt_ent ⊢
              obtain ⟨heff_mc, hsmc_loc⟩ := hmc.1 rfl
              have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by
                rw [hsmc_loc]; exact hmid_h
              have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by
                rw [hsmc_loc]; exact hmid_n
              rw [evaluateHOLFiniteState_return]
              have hev_ret : @evalHOLExact 64 F _ smc.toExact
                  (fun a => Classical.propDecidable (smc.memaddrs a))
                  (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                  some (.val (.word (h + n0))) := by
                simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
              rw [hev_ret]; dsimp only
              have hsz : sizeOfShapeWithContextHOL smc.structs (shapeOfHOLExact (.val (.word (h + n0)) : ValueHOL 64)) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hsz]; dsimp only
              have hhn_eq : (h + n0).toNat = rlpHeaderLenPure n0.toNat + n0.toNat := by
                rw [BitVec.toNat_add, hh_nat]
                exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hn0_hi; omega)
              refine ⟨fun rv' hrv' => ?_, fun r' hr' hnr => ?_⟩
              · injection hrv' with h1; injection h1 with h2
                exact ⟨h + n0, h2.symm, hhn_eq, hdst_lt,
                  ((heff_ent_mid.trans heff_mc).with_locals_clock _ _).with_locals_clock _ _⟩
              · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
          | «break» | «continue» | error =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact WkBlockTxEnc.not_resumes_error⟩
          | finalFfi _ =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ hr => by
              injection hr' with hr''; subst hr''
              rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; simp only [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := hbody (by rw [heb]; exact hnt_eb)
    simp only [heb] at hret hnonret hnt ⊢
    cases reb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
      | returned rv =>
        obtain ⟨len, rfl, hlen_eq, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨fun _ => ⟨len, hlen_eq, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem mem_eq_of_inside_fresh_ivls {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s0 cur Rl gw)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    {iv : Ivl} (hin_iv : Inside iv sourceBase (globN s0 "heap_ptr"))
    {a : Nat} (ha1 : iv.1 ≤ a) (ha2 : a + 8 ≤ iv.1 + iv.2) :
    cur.memory (BitVec.ofNat 64 a) = s0.memory (BitVec.ofNat 64 a) := by
  have hal : Allocated s0 iv := Or.inl hin_iv
  have hib : iv.1 + iv.2 ≤ 2 ^ 64 := M13.allocated_le_2pow64 hA0 hal
  have ha64 : a < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha64
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
  · apply mem_eq_of_bytes_eq heff.be _ hdom
    intro k hk
    rw [hbit]
    by_contra hne
    have hin : InIvl (a + k) iv := ⟨by omega, by omega⟩
    have hnfree := allocated_not_in_free hA0 (Or.inr hal) hin
    rcases heff.byte_frame (a + k) (by omega) hne with ⟨x, hx, hbx⟩ | hfg | hhf
    · obtain ⟨hx_ge, hx_hi⟩ := hRl_ge x hx
      obtain ⟨hb1, hb2⟩ := hbx
      exact hnfree.2 ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩
    · exact hnfree.1 hfg
    · exact hnfree.2 hhf
  · by_contra hne
    exact hdom (hma0 ▸ heff.out_dom _ hne)

private theorem wordAt_post_of_memaddrs {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hma_eq : post.memaddrs = s.memaddrs) {a : Nat} (hw : WordAt s a) : WordAt post a := by
  obtain ⟨_, hdom, _⟩ := hw
  cases hm : post.memory (BitVec.ofNat 64 a) with
  | word w' => exact ⟨w', hma_eq ▸ hdom, hm⟩

private theorem mem_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hwa : WordAt s addr.toNat) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one addrExp) =
      some (.val (.word (BitVec.ofNat 64 (memW s addr.toNat)))) := by
  have hb_eq : BitVec.ofNat 64 addr.toNat = addr := BitVec.ofNat_toNat 64 addr
  obtain ⟨w, hdom, hm⟩ := hwa
  rw [hb_eq] at hdom hm
  have hmw : memW s addr.toNat = w.toNat := by
    unfold memW; rw [hb_eq, hm]
  rw [hmw, BitVec.ofNat_toNat]
  simp [evalHOLExact, haddr, memLoadHOLExact, isWfShapeExactHOL, hdom, hm]

private theorem load_word_in_inside_fresh {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s0 cur Rl gw)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    {iv : Ivl} (hin_iv : Inside iv sourceBase (globN s0 "heap_ptr"))
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hwa0 : WordAt s0 addr.toNat)
    (ha1 : iv.1 ≤ addr.toNat) (ha2 : addr.toNat + 8 ≤ iv.1 + iv.2) :
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) (.load .one addrExp) =
      some (.val (.word (BitVec.ofNat 64 (memW s0 addr.toNat)))) := by
  have hm_eq := mem_eq_of_inside_fresh_ivls hA0 hma0 heff hRl_ge hin_iv ha1 ha2
  have hwa_cur : WordAt cur addr.toNat := wordAt_post_of_memaddrs heff.memaddrs hwa0
  have hload := mem_load_one_word cur addrExp addr haddr hwa_cur
  have hmw : memW cur addr.toNat = memW s0 addr.toNat := by unfold memW; rw [hm_eq]
  rw [hmw] at hload
  exact hload

private theorem mem_load_u256_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hfit : addr.toNat + 32 ≤ 2 ^ 64)
    (hwa0 : WordAt s addr.toNat)
    (hwa8 : WordAt s (addr.toNat + 8))
    (hwa16 : WordAt s (addr.toNat + 16))
    (hwa24 : WordAt s (addr.toNat + 24)) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load (.comb [.one, .one, .one, .one]) addrExp) =
      some (.rStruct
        [.val (.word (BitVec.ofNat 64 (memW s addr.toNat))),
         .val (.word (BitVec.ofNat 64 (memW s (addr.toNat + 8)))),
         .val (.word (BitVec.ofNat 64 (memW s (addr.toNat + 16)))),
         .val (.word (BitVec.ofNat 64 (memW s (addr.toNat + 24))))]) := by
  have hb0 : BitVec.ofNat 64 addr.toNat = addr := BitVec.ofNat_toNat 64 addr
  have hb8 : BitVec.ofNat 64 (addr.toNat + 8) = addr + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add]
    change (addr.toNat + 8) % 2 ^ 64 = (addr.toNat + 8) % 2 ^ 64
    rfl
  have hb16 : BitVec.ofNat 64 (addr.toNat + 16) = addr + 16#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add]
    change (addr.toNat + 16) % 2 ^ 64 = (addr.toNat + 16) % 2 ^ 64
    rfl
  have hb24 : BitVec.ofNat 64 (addr.toNat + 24) = addr + 24#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add]
    change (addr.toNat + 24) % 2 ^ 64 = (addr.toNat + 24) % 2 ^ 64
    rfl
  obtain ⟨w0, hd0, hm0⟩ := hwa0
  obtain ⟨w1, hd1, hm1⟩ := hwa8
  obtain ⟨w2, hd2, hm2⟩ := hwa16
  obtain ⟨w3, hd3, hm3⟩ := hwa24
  have hmw0 : BitVec.ofNat 64 (memW s addr.toNat) = w0 := by
    unfold memW; rw [hm0, BitVec.ofNat_toNat]; simp
  have hmw1 : BitVec.ofNat 64 (memW s (addr.toNat + 8)) = w1 := by
    unfold memW; rw [hm1, BitVec.ofNat_toNat]; simp
  have hmw2 : BitVec.ofNat 64 (memW s (addr.toNat + 16)) = w2 := by
    unfold memW; rw [hm2, BitVec.ofNat_toNat]; simp
  have hmw3 : BitVec.ofNat 64 (memW s (addr.toNat + 24)) = w3 := by
    unfold memW; rw [hm3, BitVec.ofNat_toNat]; simp
  rw [hb0] at hd0 hm0
  rw [hb8] at hd1 hm1
  rw [hb16] at hd2 hm2
  rw [hb24] at hd3 hm3
  rw [hmw0, hmw1, hmw2, hmw3]
  simp [evalHOLExact, haddr, memLoadHOLExact, memLoadsHOLExact, isWfShapeExactHOL,
    sizeOfShapeWithContextHOL, bytesInWordHOL, BitVec.add_assoc,
    hd0, hd1, hd2, hd3, hm0, hm1, hm2, hm3]

private theorem load_u256_in_inside_fresh {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hA0 : ArenaOK s0) (hma0 : s0.memaddrs = ordinaryDomain)
    (heff : HeapByteEff s0 cur Rl gw)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    {iv : Ivl} (hin_iv : Inside iv sourceBase (globN s0 "heap_ptr"))
    (addrExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hwa0 : WordAt s0 addr.toNat)
    (hwa8 : WordAt s0 (addr.toNat + 8))
    (hwa16 : WordAt s0 (addr.toNat + 16))
    (hwa24 : WordAt s0 (addr.toNat + 24))
    (ha1 : iv.1 ≤ addr.toNat) (ha2 : addr.toNat + 32 ≤ iv.1 + iv.2) :
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.load (.comb [.one, .one, .one, .one]) addrExp) =
      some (.rStruct
        [.val (.word (BitVec.ofNat 64 (memW s0 addr.toNat))),
         .val (.word (BitVec.ofNat 64 (memW s0 (addr.toNat + 8)))),
         .val (.word (BitVec.ofNat 64 (memW s0 (addr.toNat + 16)))),
         .val (.word (BitVec.ofNat 64 (memW s0 (addr.toNat + 24))))]) := by
  have hib : iv.1 + iv.2 ≤ 2 ^ 64 := M13.allocated_le_2pow64 hA0 (Or.inl hin_iv)
  have hfit : addr.toNat + 32 ≤ 2 ^ 64 := by omega
  have hm0 := mem_eq_of_inside_fresh_ivls (a := addr.toNat) hA0 hma0 heff hRl_ge hin_iv ha1 (by omega)
  have hm8 := mem_eq_of_inside_fresh_ivls (a := addr.toNat + 8) hA0 hma0 heff hRl_ge hin_iv (by omega) (by omega)
  have hm16 := mem_eq_of_inside_fresh_ivls (a := addr.toNat + 16) hA0 hma0 heff hRl_ge hin_iv (by omega) (by omega)
  have hm24 := mem_eq_of_inside_fresh_ivls (a := addr.toNat + 24) hA0 hma0 heff hRl_ge hin_iv (by omega) ha2
  have hload := mem_load_u256_words cur addrExp addr haddr hfit
    (wordAt_post_of_memaddrs heff.memaddrs hwa0)
    (wordAt_post_of_memaddrs heff.memaddrs hwa8)
    (wordAt_post_of_memaddrs heff.memaddrs hwa16)
    (wordAt_post_of_memaddrs heff.memaddrs hwa24)
  have hmw0 : memW cur addr.toNat = memW s0 addr.toNat := by unfold memW; rw [hm0]
  have hmw8 : memW cur (addr.toNat + 8) = memW s0 (addr.toNat + 8) := by unfold memW; rw [hm8]
  have hmw16 : memW cur (addr.toNat + 16) = memW s0 (addr.toNat + 16) := by unfold memW; rw [hm16]
  have hmw24 : memW cur (addr.toNat + 24) = memW s0 (addr.toNat + 24) := by unfold memW; rw [hm24]
  rw [hmw0, hmw8, hmw16, hmw24] at hload
  exact hload

private theorem call_noexc_ne_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (rk : Option (VarKind × MlS)) (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (rk, none)) fname args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (rk, none)) fname args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · simp
    · dsimp only
      by_cases hclk : s.clock = 0
      · simp [hclk]
      · rw [if_neg hclk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none => simp
        | some rb' =>
          cases rb' with
          | returned _ =>
            cases rk with
            | none => dsimp only; split <;> simp
            | some kv =>
              dsimp only
              split
              · split <;> simp
              · simp
          | _ => simp

/-! ## Section 13: Blob Hashes Encoding (`tx_put_blob_hashes`) -/

private def txPutBlobHashesLoopBody : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"),
       .op .add [.var .local (ofString "buf"),
         .panop .mul [.var .local (ofString "i"), .const 32#64]],
       .const 32#64])
    (.seq
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))

private def txPutBlobHashesWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    txPutBlobHashesLoopBody

private theorem eval_txPutBlobHashesWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (dst0 bufw nw pw iw : BitVec 64) (pstart : Nat)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hi_le : iw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = pstart + 33 * iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧ pstart + 33 * nw.toNat ≤ ivl.1 + ivl.2)
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hl_buf : s.locals.lookup (ofString "buf") = some (.val (.word bufw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hl_w : ∃ ww : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hnt : (evaluateHOLFiniteState s txPutBlobHashesWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s txPutBlobHashesWhile
    (out.1 = none →
      ∃ pf : BitVec 64,
        pf.toNat = pstart + 33 * nw.toNat ∧
        out.2.globals = s.globals ∧
        HeapByteEff s out.2 Rl gw ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pf))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  induction clk generalizing s pw iw with
  | zero =>
    intro out; dsimp only [out, txPutBlobHashesWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, txPutBlobHashesWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        have hev_src : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "buf"),
              .panop .mul [.var .local (ofString "i"), .const 32#64]]) =
            some (.val (.word (bufw + iw * 32#64))) := by
          have hz32 : iw * 32#64 + 0 = iw * 32#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_buf, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz32]
        have hhl32 : rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat = 33 := by
          have : (32#64 : BitVec 64).toNat = 32 := by decide
          rw [this, rlpHeaderLenPure_of_le55 (by decide)]
        have hin_eb : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
            pw.toNat + rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat ≤ ivl.1 + ivl.2 := by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          refine ⟨ivl, hivl, by omega, ?_⟩
          rw [Nat.add_assoc, hhl32]
          have : 33 * (iw.toNat + 1) ≤ 33 * nw.toNat := Nat.mul_le_mul_left _ (by omega)
          omega
        dsimp only [txPutBlobHashesLoopBody] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hc_eb : evaluateHOLFiniteState sd
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"),
               .op .add [.var .local (ofString "buf"),
                 .panop .mul [.var .local (ofString "i"), .const 32#64]],
               .const 32#64]) with ⟨rc, m1⟩
        have hnt_eb : rc ≠ some .timeOut := by rintro rfl; simp only [hc_eb] at hnt; exact hnt rfl
        have heb := eval_call_local_rlp_encode_bytes_ge2 sd "w"
          (.var .local (ofString "p"))
          (.op .add [.var .local (ofString "buf"),
            .panop .mul [.var .local (ofString "i"), .const 32#64]])
          (.const 32#64)
          pw (bufw + iw * 32#64) 32#64 Rl gw heff0_sd.arena.1.code heff0_sd.arena
          hl_w (by simp [evalHOLExact, show sd.locals = s.locals from rfl, hl_p])
          hev_src rfl (by decide) (by rw [WkBlockTxEnc.heapEnd_val]; decide) hin_eb
          (by rw [hc_eb]; exact hnt_eb)
        have hclk_eb := evaluateHOLFiniteState_clock_le sd
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .op .add [.var .local (ofString "buf"),
               .panop .mul [.var .local (ofString "i"), .const 32#64]],
             .const 32#64])
        have hnbc_eb := call_noexc_ne_break_continue sd (some (VarKind.local, ofString "w"))
          (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .op .add [.var .local (ofString "buf"),
             .panop .mul [.var .local (ofString "i"), .const 32#64]],
           .const 32#64]
        dsimp only at heb; rw [hc_eb] at heb hclk_eb hnbc_eb
        simp only [hc_eb] at hnt ⊢
        cases rc with
        | some rc' =>
          have hnr := heb.2 (by simp)
          cases rc' with
          | «break» => exact absurd rfl hnbc_eb.1
          | «continue» => exact absurd rfl hnbc_eb.2
          | _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨len, hlen_eq, hp_lt_he, hm1_glob, hm1_loc, heff_m1⟩ := heb.1 rfl
          rw [hhl32] at hlen_eq
          have hm1_w : m1.locals.lookup (ofString "w") = some (.val (.word len)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "p" by decide]; exact hl_p
          have hm1_i : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "i" by decide]; exact hl_i
          have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "dst" by decide]; exact hl_dst
          have hm1_buf : m1.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "buf" by decide]; exact hl_buf
          have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "n" by decide]; exact hl_n
          rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
          have hass_p : evaluateHOLFiniteState m1
              (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
              (none, setVarHOLFinite (ofString "p") (.val (.word (pw + len))) m1) := by
            rw [evaluateHOLFiniteState_assign]
            have hev_pw : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
                some (.val (.word (pw + len))) := by
              have hzl : len + 0 = len := BitVec.add_zero _
              simp [evalHOLExact, evalListHOLExact, hm1_p, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzl]
            rw [hev_pw]; dsimp only
            have hvv : isValidValueHOLFinite m1 .local (ofString "p") (.val (.word (pw + len))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm1_p, shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hvv]; rfl
          rw [hass_p] at hnt ⊢; dsimp only at hnt ⊢
          let m2 := setVarHOLFinite (ofString "p") (.val (.word (pw + len))) m1
          have hm2_i : m2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_i,
              show ofString "p" ≠ ofString "i" by decide]
          have hass_i : evaluateHOLFiniteState m2
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m2) := by
            rw [evaluateHOLFiniteState_assign]
            have hev_iw : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
                (.op .add [.var .local (ofString "i"), .const 1#64]) =
                some (.val (.word (iw + 1#64))) := by
              simp [evalHOLExact, evalListHOLExact, hm2_i, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_iw]; dsimp only
            have hvv : isValidValueHOLFinite m2 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm2_i, shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hvv]; rfl
          rw [hass_i] at hnt ⊢; dsimp only at hnt ⊢
          let m3 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m2
          have heff_s_m3 : HeapByteEff s m3 Rl gw :=
            (heff_sd.trans heff_m1).locals_clock m3.locals m3.clock
          have hm3_clk : m3.clock ≤ k := by
            change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_eb; omega
          have hhe264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
          have hiw'_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = iw.toNat + 1
            exact Nat.mod_eq_of_lt (by omega)
          have hpw'_nat : (pw + len).toNat = pstart + 33 * (iw + 1#64).toNat := by
            rw [hiw'_nat, BitVec.toNat_add, hlen_eq, hp_eq]
            have hp_lt_he' : pstart + 33 * iw.toNat < heapEnd := hp_eq ▸ hp_lt_he
            exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hp_lt_he'; omega)
          have hm3_dst : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
              show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide]
          have hm3_buf : m3.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_buf,
              show ofString "i" ≠ ofString "buf" by decide, show ofString "p" ≠ ofString "buf" by decide]
          have hm3_n : m3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
              show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide]
          have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word (pw + len))) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide]
          have hm3_i : m3.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
            simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hm3_w : ∃ ww : BitVec 64, m3.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            refine ⟨len, ?_⟩
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
              show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]
          have hrec := ih m3 (pw + len) (iw + 1#64) hm3_clk (heff0.trans heff_s_m3)
            (by omega) hpw'_nat hm3_dst hm3_buf hm3_n hm3_p hm3_i hm3_w hnt
          dsimp only at hrec
          refine ⟨fun hnone => ?_, hrec.2⟩
          obtain ⟨pf, hpf_eq, hm3_glob, heff_rec, hpf_dst, hpf_p⟩ := hrec.1 hnone
          exact ⟨pf, hpf_eq, hm3_glob.trans hm1_glob, heff_s_m3.trans heff_rec, hpf_dst, hpf_p⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩

private theorem eval_call_local_tx_put_blob_hashes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp bufExp nExp : ExpHOL 64)
    (dst0 bufw nw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hbuf : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) bufExp =
      some (.val (.word bufw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_blob_hashes")
        [dstExp, bufExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_blob_hashes")
        [dstExp, bufExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, bufExp, nExp] = some [.val (.word dst0), .val (.word bufw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hbuf, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "tx_put_blob_hashes")
    (ofString "dst") (ofString "buf") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes) dst0 bufw nw
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_tx_put_blob_hashes)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "buf", ValueHOL.val (.word bufw))).update (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_ar : ArenaReady ent := (show M13.LocFrame s ent by cases s; rfl).arenaReady hAR
    have heff_s_ent : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hAR Rl gw).locals_clock ent.locals ent.clock
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "buf" ≠ ofString "dst" by decide]
    have hent_buf : ent.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "buf" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes =
        .decCall (ofString "w") .one (ofString "rlp_encode_list_header")
          [.var .local (ofString "dst"), .panop .mul [.const 33#64, .var .local (ofString "n")]]
          (.dec (ofString "p") .one (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
            (.dec (ofString "i") .one (.const 0#64)
              (.seq txPutBlobHashesWhile
                (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]))))) := rfl
    have hmul33 : (33#64 * nw).toNat = 33 * nw.toNat := by
      rw [BitVec.toNat_mul]; change (33 * nw.toNat) % 2 ^ 64 = 33 * nw.toNat
      exact Nat.mod_eq_of_lt (by omega)
    have hbody :
        let outb := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes)
        (outb.1 ≠ some .timeOut) →
        (Resumes outb.1 →
          ∃ len : BitVec 64,
            outb.1 = some (.returned (.val (.word len))) ∧
            len.toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat ∧
            outb.2.globals = ent.globals ∧
            HeapByteEff ent outb.2 Rl gw) := by
      intro outb hnt_b hres_b
      dsimp only [outb] at hnt_b hres_b ⊢
      rw [hb] at hnt_b hres_b ⊢
      have hin_lh : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
          dst0.toNat + rlpHeaderLenPure (33#64 * nw).toNat ≤ ivl.1 + ivl.2 := by
        rw [hmul33]; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩
      obtain ⟨mid1, hhl_nat, hhl1, hhl9, hdst_lt_he, hm1_glob, hm1_loc, heff_m1, hnt_m1, hres_m1, hout_m1⟩ :=
        WkBlockTxEnc.eval_decCall_rlp_encode_list_header ent "w"
          (.var .local (ofString "dst"))
          (.panop .mul [.const 33#64, .var .local (ofString "n")])
          dst0 (33#64 * nw) _ Rl gw hcode hent_ar
          (by simp [evalHOLExact, hent_dst])
          (by simp [evalHOLExact, evalListHOLExact, hent_n, panOpHOL, valueIsWord, valueWord])
          hin_lh hnt_b hres_b
      rw [hout_m1]
      set w0 := BitVec.ofNat 64 (rlpHeaderLenPure (33#64 * nw).toNat)
      have hw0_nat : w0.toNat = rlpHeaderLenPure (33 * nw.toNat) := by
        have h1 : w0.toNat = rlpHeaderLenPure (33#64 * nw).toNat := hhl_nat
        rw [hmul33] at h1; exact h1
      have hm1_w : mid1.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, w0]
      have hm1_dst : mid1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hm1_buf : mid1.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_buf,
          show ofString "w" ≠ ofString "buf" by decide]
      have hm1_n : mid1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
          show ofString "w" ≠ ofString "n" by decide]
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_p0 : @evalHOLExact 64 F _ mid1.toExact (fun a => Classical.propDecidable (mid1.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
          some (.val (.word (dst0 + w0))) := by
        have hzw : w0 + 0 = w0 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hm1_dst, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzw]
      rw [hev_p0] at hnt_m1 hres_m1 ⊢
      dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢
      dsimp only at hnt_m1 hres_m1 ⊢
      set mid2 := setVarHOLFinite (ofString "p") (.val (.word (dst0 + w0))) mid1
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_i0 : @evalHOLExact 64 F _ mid2.toExact (fun a => Classical.propDecidable (mid2.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev_i0] at hnt_m1 hres_m1 ⊢
      dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢
      dsimp only at hnt_m1 hres_m1 ⊢
      set mid3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) mid2
      have heff_m1_m3 : HeapByteEff mid1 mid3 Rl gw :=
        (HeapByteEff.refl heff_m1.arena Rl gw).locals_clock mid3.locals mid3.clock
      have hhe264 : heapEnd < 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
      have hp0_nat : (dst0 + w0).toNat = dst0.toNat + rlpHeaderLenPure (33 * nw.toNat) := by
        rw [BitVec.toNat_add, hw0_nat]
        have hbnd := rlpHeaderLenPure_bounds (33 * nw.toNat)
        exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hdst_lt_he; omega)
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + rlpHeaderLenPure (33 * nw.toNat) ∧
          (dst0.toNat + rlpHeaderLenPure (33 * nw.toNat)) + 33 * nw.toNat ≤ ivl.1 + ivl.2 := by
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, by omega, h2⟩
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hres_m1 ⊢
      rcases hw_run : evaluateHOLFiniteState mid3 txPutBlobHashesWhile with ⟨rw_res, sw_post⟩
      have hnt_w : rw_res ≠ some .timeOut := by
        rintro rfl; simp only [hw_run] at hnt_m1; exact hnt_m1 rfl
      have hloop := eval_txPutBlobHashesWhile_exact mid3.clock ent mid3 Rl gw
        dst0 bufw nw (dst0 + w0) 0#64 (dst0.toNat + rlpHeaderLenPure (33 * nw.toNat))
        le_rfl (heff_m1.trans heff_m1_m3) hn_lt (by simp) (by simp [hp0_nat]) hin_loop
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_buf,
          show ofString "i" ≠ ofString "buf" by decide, show ofString "p" ≠ ofString "buf" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide])
        (by simp [mid3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ⟨w0, by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]⟩
        (by rw [hw_run]; exact hnt_w)
      dsimp only at hloop; rw [hw_run] at hloop
      simp only [hw_run] at hnt_m1 hres_m1 ⊢
      cases rw_res with
      | some r' =>
        exact False.elim (hloop.2 (by simp) hres_m1)
      | none =>
        dsimp only at hnt_m1 hres_m1 ⊢
        obtain ⟨pf, hpf_eq, hsw_glob, heff_w, hsw_dst, hsw_p⟩ := hloop.1 rfl
        dsimp only at hsw_glob heff_w hsw_dst hsw_p
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ sw_post.toExact (fun a => Classical.propDecidable (sw_post.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (pf - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hsw_p, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact])]
        dsimp only
        have hsub_nat : (pf - dst0).toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat := by
          rw [BitVec.toNat_sub_of_le]
          · omega
          · rw [BitVec.le_def]; omega
        refine ⟨pf - dst0, rfl, hsub_nat, hsw_glob.trans hm1_glob, ?_⟩
        exact (((((heff_m1.trans heff_m1_m3).trans heff_w).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    simp only [hrun] at hnt ⊢
    cases rb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev =>
        refine ⟨fun h => by simp at h, fun _ hres_call => ?_⟩
        have hres_ent : Resumes (some (.exception eid ev)) := by
          rcases hres_call with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨_, hrb, _⟩ := hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_ent)
        simp only [hrun] at hrb; cases hrb
      | returned rv =>
        obtain ⟨len, hrb, hlen_eq, hsb_glob, heff_ent⟩ :=
          hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
        simp only [hrun] at hrb hsb_glob heff_ent
        injection hrb with hrv; injection hrv with hrv'; subst hrv'
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]; rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { sb with locals := s.locals }
        exact ⟨fun _ => ⟨len, hlen_eq, hsb_glob, rfl,
          (heff_s_ent.trans heff_ent).locals_clock mid.locals mid.clock⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 14: Access List Encoding (`access_list_payload_len`, `tx_put_access_list`) -/

private theorem wordAt_of_wordsOK {F : Type} {s : PanSemStateFiniteExact 64 F} {iv : Ivl}
    (hw : WordsOK s iv) (k : Nat) (hk : 8 * k + 8 ≤ iv.2) :
    WordAt s (iv.1 + 8 * k) :=
  hw.2.2 k (by omega)

private theorem inside_fit_u64 {iv : Ivl} {hi : Nat}
    (hin : Inside iv sourceBase hi) (hhi : hi ≤ heapLimit) :
    iv.1 + iv.2 ≤ 2 ^ 64 := by
  have := hin.2
  rw [WkBlockTxEnc.heapLimit_val] at hhi
  omega

private def accessListEntryPayloadPure {F : Type} (s : PanSemStateFiniteExact 64 F) (recAddr : Nat) : Nat :=
  let inner := 33 * memW s (recAddr + 16)
  21 + rlpHeaderLenPure inner + inner

private def accessListEntryEncodedPure {F : Type} (s : PanSemStateFiniteExact 64 F) (recAddr : Nat) : Nat :=
  let entry := accessListEntryPayloadPure s recAddr
  rlpHeaderLenPure entry + entry

private def accessListPayloadPrefix {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => accessListPayloadPrefix s recs k' + accessListEntryEncodedPure s (recs + 24 * k')

private def accessSlotsPrefix {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) : Nat :=
  ((List.range k).map (fun i => memW s (recs + 24 * i + 16))).sum

private theorem accessSlotsPrefix_succ {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    accessSlotsPrefix s recs (k + 1) = accessSlotsPrefix s recs k + memW s (recs + 24 * k + 16) := by
  unfold accessSlotsPrefix
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

private theorem accessSlotsPrefix_mono {F : Type} (s : PanSemStateFiniteExact 64 F) (recs : Nat)
    {j k : Nat} (hjk : j ≤ k) :
    accessSlotsPrefix s recs j ≤ accessSlotsPrefix s recs k := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => rw [accessSlotsPrefix_succ]; omega

private theorem accessListEntry_slot_le_prefix {F : Type} (s : PanSemStateFiniteExact 64 F) (recs i n : Nat)
    (hi : i < n) :
    memW s (recs + 24 * i + 16) ≤ accessSlotsPrefix s recs n := by
  have h1 := accessSlotsPrefix_mono s recs (j := i + 1) (k := n) (by omega)
  rw [accessSlotsPrefix_succ] at h1
  omega

private theorem accessListPayloadPrefix_le {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    accessListPayloadPrefix s recs k ≤ 39 * k + 33 * accessSlotsPrefix s recs k := by
  induction k with
  | zero => simp [accessListPayloadPrefix, accessSlotsPrefix]
  | succ k' ih =>
    rw [accessListPayloadPrefix, accessSlotsPrefix_succ]
    unfold accessListEntryEncodedPure accessListEntryPayloadPure
    dsimp only
    have hb1 := rlpHeaderLenPure_bounds (33 * memW s (recs + 24 * k' + 16))
    have hb2 := rlpHeaderLenPure_bounds
      (21 + rlpHeaderLenPure (33 * memW s (recs + 24 * k' + 16)) + 33 * memW s (recs + 24 * k' + 16))
    omega

private theorem eval_decCall_rlp_list_header_len_clk {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (pExp : ExpHOL 64) (pw : BitVec 64)
    (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [pExp] cont)).1 ≠
      some .timeOut) :
    let hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      hl.toNat = rlpHeaderLenPure pw.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      mid.clock ≤ s.clock ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [pExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro hl
  have hb_lhl : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp] =
      some [.val (.word pw)] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_list_header_len") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_list_header_len) pw
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_list_header_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "payload_len", ValueHOL.val (.word pw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_p : ent.locals.lookup (ofString "payload_len") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hb_lhl, evaluateHOLFiniteState_call] at hnt ⊢
    have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "payload_len")] = some [.val (.word pw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_p]
    have hlk2 := pan_one_word_lookup ent.code.lookup (ofString "rlp_header_len") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_header_len) pw
      (by change s.code.lookup _ = _; rw [hcode]; exact WkBlockTxEnc.lookup_rlp_header_len)
    simp only [ha2, hlk2] at hnt ⊢
    by_cases hcz2 : ent.clock = 0
    · simp [hcz2] at hnt
    · simp only [hcz2, ↓reduceIte] at hnt ⊢
      set cmap2 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word pw))
      set ent2 := callEntryStateHOLFinite ent cmap2
      have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word pw)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hclk_hl := evaluateHOLFiniteState_clock_le ent2 (sourceFnBody Guest.Software.guestFn_rlp_header_len)
      rcases hhl : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rhl, shl⟩
      rw [hhl] at hclk_hl
      have hnt_hl : rhl ≠ some .timeOut := by
        rintro rfl; rw [hhl] at hnt; exact hnt rfl
      obtain ⟨hr_hl, hlf_hl⟩ := WkBlockTxEnc.eval_rlp_header_len_body_exact ent2 pw hcode hent2_n (by rw [hhl]; exact hnt_hl)
      rw [hhl] at hr_hl hlf_hl
      dsimp only at hr_hl hlf_hl
      subst hr_hl
      have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hhl] at hnt ⊢
      rw [if_pos hsh1] at hnt ⊢
      dsimp only at hnt ⊢
      rw [if_pos hsh2] at hnt ⊢
      let mid := setVarHOLFinite (ofString lname) (.val (.word hl)) { shl.emptyLocalsHOLFinite with locals := s.locals }
      have hmid_clk : mid.clock ≤ s.clock := by
        change shl.clock ≤ s.clock
        change shl.clock ≤ (s.clock - 1) - 1 at hclk_hl
        omega
      have hlf_all : M13.LocFrame s mid := by
        have h1 : M13.LocFrame s ent2 := by cases s; rfl
        exact (((h1.trans hlf_hl).emptyLocals).locals _).setVar _ _
      have hbnd := rlpHeaderLenPure_bounds pw.toNat
      have hhl_nat : hl.toNat = rlpHeaderLenPure pw.toNat := by
        dsimp [hl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      exact ⟨mid, hhl_nat, by omega, by omega, hmid_clk, hlf_all.globals, hlf_all.memory, rfl,
        HeapByteEff.of_locFrame hAR hlf_all Rl gw, hnt, rfl⟩

private theorem lookup_resVarEq_ne {V : Type} (m : HolFiniteMapExact MlS V)
    (v : MlS) (old : Option V) (x : MlS) (hne : x ≠ v) :
    (m.resVarEq (v, old)).lookup x = m.lookup x := by
  simp only [HolFiniteMapExact.resVarEq]
  cases old <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]

private abbrev alPayloadLenLoopBody : ProgHOL 64 :=
  .dec (ofString "inner") .one
    (.panop .mul [.const 33#64,
      .load .one (.op .add [.var .local (ofString "recs"),
        .panop .mul [.var .local (ofString "i"), .const 24#64],
        .const 16#64])])
    (.decCall (ofString "ih") .one (ofString "rlp_list_header_len") [.var .local (ofString "inner")]
      (.dec (ofString "entry") .one
        (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")])
        (.decCall (ofString "eh") .one (ofString "rlp_list_header_len") [.var .local (ofString "entry")]
          (.seq
            (.assign .local (ofString "total")
              (.op .add [.var .local (ofString "total"), .var .local (ofString "eh"), .var .local (ofString "entry")]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1#64]))))))

private abbrev alPayloadLenWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) alPayloadLenLoopBody

private theorem eval_alPayloadLenWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) (gw : List String)
    (recsw nw totalw iw : BitVec 64)
    (hcode : s0.code = originalRuntimeCode) (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots : accessSlotsPrefix s0 recsw.toNat nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat) ∧
      Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hi_le : iw.toNat ≤ nw.toNat)
    (htot_eq : totalw.toNat = accessListPayloadPrefix s0 recsw.toNat iw.toNat)
    (hl_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_total : s.locals.lookup (ofString "total") = some (.val (.word totalw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hnt : (evaluateHOLFiniteState s alPayloadLenWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s alPayloadLenWhile
    out.1 = none ∧
    out.2.globals = s.globals ∧
    out.2.memory = s.memory ∧
    HeapByteEff s out.2 Rl gw ∧
    out.2.locals.lookup (ofString "total") =
      some (.val (.word (BitVec.ofNat 64 (accessListPayloadPrefix s0 recsw.toNat nw.toNat)))) := by
  induction clk generalizing s totalw iw with
  | zero =>
    intro out; dsimp only [out, alPayloadLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      have hbw : BitVec.ofNat 64 (accessListPayloadPrefix s0 recsw.toNat nw.toNat) = totalw := by
        rw [← hieq, ← htot_eq]; simp
      rw [hbw]
      exact ⟨rfl, rfl, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_total⟩
  | succ k ih =>
    intro out; dsimp only [out, alPayloadLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        have ⟨hwok, hin_recs⟩ := hrecs_ok (by omega)
        have hfit_recs : recsw.toNat + 24 * nw.toNat ≤ 2 ^ 64 :=
          inside_fit_u64 hin_recs hAR0.2.2.1
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
        have haddr_nat : (recsw + (iw * 24#64 + 16#64)).toNat = recsw.toNat + 24 * iw.toNat + 16 := by
          have hi24 : (iw * 24#64).toNat = 24 * iw.toNat := by
            rw [BitVec.toNat_mul]; change (iw.toNat * 24) % 2 ^ 64 = 24 * iw.toNat
            rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
          have hi24_16 : (iw * 24#64 + 16#64).toNat = 24 * iw.toNat + 16 := by
            rw [BitVec.toNat_add, hi24]; change (24 * iw.toNat + 16) % 2 ^ 64 = 24 * iw.toNat + 16
            exact Nat.mod_eq_of_lt (by omega)
          rw [BitVec.toNat_add, hi24_16]
          exact Nat.mod_eq_of_lt (by omega)
        have hev_addr : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "recs"),
              .panop .mul [.var .local (ofString "i"), .const 24#64],
              .const 16#64]) =
            some (.val (.word (recsw + (iw * 24#64 + 16#64)))) := by
          have hz16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_recs, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz16]
        have hwa_ns : WordAt s0 (recsw + (iw * 24#64 + 16#64)).toNat := by
          rw [haddr_nat]
          have heq8 : recsw.toNat + 24 * iw.toNat + 16 = recsw.toNat + 8 * (3 * iw.toNat + 2) := by omega
          rw [heq8]
          exact wordAt_of_wordsOK hwok (3 * iw.toNat + 2) (by omega)
        have hload_ns := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs heff0_sd hRl_ge hin_recs
          (.op .add [.var .local (ofString "recs"),
            .panop .mul [.var .local (ofString "i"), .const 24#64], .const 16#64])
          (recsw + (iw * 24#64 + 16#64)) hev_addr hwa_ns
          (by rw [haddr_nat]; change recsw.toNat ≤ _; omega)
          (by rw [haddr_nat]; change (recsw.toNat + 24 * iw.toNat + 16) + 8 ≤ recsw.toNat + 24 * nw.toNat; omega)
        rw [haddr_nat] at hload_ns
        set nsw := BitVec.ofNat 64 (memW s0 (recsw.toNat + 24 * iw.toNat + 16))
        have hns_le : memW s0 (recsw.toNat + 24 * iw.toNat + 16) < 2 ^ 32 := by
          have := accessListEntry_slot_le_prefix s0 recsw.toNat iw.toNat nw.toNat hlt
          omega
        have hnsw_nat : nsw.toNat = memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
          dsimp [nsw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        set innerw := 33#64 * nsw
        have hinner_nat : innerw.toNat = 33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
          rw [show innerw = 33#64 * nsw from rfl, BitVec.toNat_mul, hnsw_nat]
          change (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        dsimp only [alPayloadLenLoopBody] at hnt ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hev_inner : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.panop .mul [.const 33#64,
              .load .one (.op .add [.var .local (ofString "recs"),
                .panop .mul [.var .local (ofString "i"), .const 24#64],
                .const 16#64])]) =
            some (.val (.word innerw)) := by
          have hc33 : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
              (.const 33#64) = some (.val (.word 33#64)) := rfl
          have h1 : nsw * 1#64 = nsw := BitVec.mul_one _
          unfold evalHOLExact evalListHOLExact
          rw [hc33]
          unfold evalListHOLExact
          rw [hload_ns]
          unfold evalListHOLExact
          simp [panOpHOL, valueIsWord, valueWord, innerw, h1]
        rw [hev_inner] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢; dsimp only at hnt ⊢
        set m1 := setVarHOLFinite (ofString "inner") (.val (.word innerw)) sd
        have hnt_m1 : (evaluateHOLFiniteState m1
            (.decCall (ofString "ih") .one (ofString "rlp_list_header_len") [.var .local (ofString "inner")]
              (.dec (ofString "entry") .one
                (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")])
                (.decCall (ofString "eh") .one (ofString "rlp_list_header_len") [.var .local (ofString "entry")]
                  (.seq
                    (.assign .local (ofString "total")
                      (.op .add [.var .local (ofString "total"), .var .local (ofString "eh"), .var .local (ofString "entry")]))
                    (.assign .local (ofString "i")
                      (.op .add [.var .local (ofString "i"), .const 1#64]))))))).1 ≠ some .timeOut := by
          intro hto; rw [hto] at hnt; exact hnt rfl
        have hm1_code : m1.code = originalRuntimeCode := heff0.arena.1.code
        have hm1_ar : ArenaReady m1 := localsFree_arenaReady s m1.locals m1.clock heff0.arena
        obtain ⟨m2, hih_nat, hih_ge, hih_le, hc1, hm2_glob, hm2_mem, hm2_loc, heff_m1_m2, hnt_m2, hout_m2⟩ :=
          eval_decCall_rlp_list_header_len_clk m1 "ih" (.var .local (ofString "inner")) innerw _ Rl gw
            hm1_code hm1_ar
            (by simp [evalHOLExact, m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt_m1
        rw [hout_m2] at hnt ⊢; dsimp only at hnt ⊢
        set ihw := BitVec.ofNat 64 (rlpHeaderLenPure innerw.toNat)
        have hm2_ih : m2.locals.lookup (ofString "ih") = some (.val (.word ihw)) := by
          rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ihw]
        have hm2_inner : m2.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
          rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m1, setVarHOLFinite,
            show ofString "ih" ≠ ofString "inner" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hnt_m2 hnt ⊢; dsimp only at hnt_m2 hnt ⊢
        set entryw := 21#64 + (ihw + innerw)
        have hev_entry : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
            (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]) =
            some (.val (.word entryw)) := by
          have hzi : innerw + 0 = innerw := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, hm2_ih, hm2_inner, wordOpHOL, wordOp, valueIsWord, valueWord, hzi, entryw]
        rw [hev_entry] at hnt_m2 hnt ⊢; dsimp only at hnt_m2 hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m2 hnt ⊢; dsimp only at hnt_m2 hnt ⊢
        set m3 := setVarHOLFinite (ofString "entry") (.val (.word entryw)) m2
        have hentry_nat : entryw.toNat = accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat) := by
          have hb_in := rlpHeaderLenPure_bounds (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
          have h1 : (ihw + innerw).toNat = rlpHeaderLenPure innerw.toNat + innerw.toNat := by
            rw [BitVec.toNat_add, hih_nat, hinner_nat]; exact Nat.mod_eq_of_lt (by omega)
          rw [show entryw = 21#64 + (ihw + innerw) from rfl, BitVec.toNat_add, h1, hinner_nat]
          unfold accessListEntryPayloadPure; dsimp only
          change (21 + (rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) +
            33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))) % 2 ^ 64 = _
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have hm3_code : m3.code = originalRuntimeCode := heff_m1_m2.arena.1.code
        have hm3_ar : ArenaReady m3 := localsFree_arenaReady m2 m3.locals m3.clock heff_m1_m2.arena
        obtain ⟨m4, heh_nat, heh_ge, heh_le, hc2, hm4_glob, hm4_mem, hm4_loc, heff_m3_m4, hnt_m4, hout_m4⟩ :=
          eval_decCall_rlp_list_header_len_clk m3 "eh" (.var .local (ofString "entry")) entryw _ Rl gw
            hm3_code hm3_ar
            (by simp [evalHOLExact, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt_m2
        rw [hout_m4] at hnt ⊢; dsimp only at hnt ⊢
        set ehw := BitVec.ofNat 64 (rlpHeaderLenPure entryw.toNat)
        have hm4_eh : m4.locals.lookup (ofString "eh") = some (.val (.word ehw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ehw]
        have hm4_entry : m4.locals.lookup (ofString "entry") = some (.val (.word entryw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m3, setVarHOLFinite,
            show ofString "eh" ≠ ofString "entry" by decide]
        have hm4_total : m4.locals.lookup (ofString "total") = some (.val (.word totalw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m3, hm2_loc, m1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_total,
            show ofString "eh" ≠ ofString "total" by decide,
            show ofString "entry" ≠ ofString "total" by decide,
            show ofString "ih" ≠ ofString "total" by decide,
            show ofString "inner" ≠ ofString "total" by decide]
        have hm4_i : m4.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m3, hm2_loc, m1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_i,
            show ofString "eh" ≠ ofString "i" by decide,
            show ofString "entry" ≠ ofString "i" by decide,
            show ofString "ih" ≠ ofString "i" by decide,
            show ofString "inner" ≠ ofString "i" by decide]
        have hm4_recs : m4.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m3, hm2_loc, m1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_recs,
            show ofString "eh" ≠ ofString "recs" by decide,
            show ofString "entry" ≠ ofString "recs" by decide,
            show ofString "ih" ≠ ofString "recs" by decide,
            show ofString "inner" ≠ ofString "recs" by decide]
        have hm4_n : m4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, m3, hm2_loc, m1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_n,
            show ofString "eh" ≠ ofString "n" by decide,
            show ofString "entry" ≠ ofString "n" by decide,
            show ofString "ih" ≠ ofString "n" by decide,
            show ofString "inner" ≠ ofString "n" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m4 hnt ⊢
        set totalw' := totalw + (ehw + entryw)
        have hass_tot : evaluateHOLFiniteState m4
            (.assign .local (ofString "total")
              (.op .add [.var .local (ofString "total"), .var .local (ofString "eh"), .var .local (ofString "entry")])) =
            (none, setVarHOLFinite (ofString "total") (.val (.word totalw')) m4) := by
          rw [evaluateHOLFiniteState_assign]
          have hev_t : @evalHOLExact 64 F _ m4.toExact (fun a => Classical.propDecidable (m4.memaddrs a))
              (.op .add [.var .local (ofString "total"), .var .local (ofString "eh"), .var .local (ofString "entry")]) =
              some (.val (.word totalw')) := by
            have hze : entryw + 0 = entryw := BitVec.add_zero _
            simp [evalHOLExact, evalListHOLExact, hm4_total, hm4_eh, hm4_entry,
              wordOpHOL, wordOp, valueIsWord, valueWord, hze, totalw']
          rw [hev_t]; dsimp only
          have hvv : isValidValueHOLFinite m4 .local (ofString "total") (.val (.word totalw')) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm4_total, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv]; rfl
        rw [hass_tot] at hnt_m4 hnt ⊢; dsimp only at hnt_m4 hnt ⊢
        set m5 := setVarHOLFinite (ofString "total") (.val (.word totalw')) m4
        have hm5_i : m5.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_i,
            show ofString "total" ≠ ofString "i" by decide]
        have hass_i : evaluateHOLFiniteState m5
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m5) := by
          rw [evaluateHOLFiniteState_assign]
          have hev_iw : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) =
              some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hm5_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_iw]; dsimp only
          have hvv : isValidValueHOLFinite m5 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm5_i, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv]; rfl
        rw [hass_i] at hnt_m4 hnt ⊢; dsimp only at hnt ⊢
        let m6 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m5
        let bodyPost : PanSemStateFiniteExact 64 F :=
          { m6 with
            locals :=
              ((((m6.locals.resVarEq (ofString "eh", m3.locals.lookup (ofString "eh"))).resVarEq
                (ofString "entry", m2.locals.lookup (ofString "entry"))).resVarEq
                (ofString "ih", m1.locals.lookup (ofString "ih"))).resVarEq
                (ofString "inner", sd.locals.lookup (ofString "inner"))) }
        have hbp_clk : bodyPost.clock ≤ k := by
          have hm1_clk : m1.clock = s.clock - 1 := rfl
          have hm3_clk : m3.clock = m2.clock := rfl
          have hbp_c : bodyPost.clock = m4.clock := rfl
          omega
        have heff_s_bp : HeapByteEff s bodyPost Rl gw := by
          have h1 : HeapByteEff s m2 Rl gw :=
            (heff_sd.locals_clock m1.locals m1.clock).trans heff_m1_m2
          have h2 : HeapByteEff m2 m4 Rl gw :=
            ((HeapByteEff.refl heff_m1_m2.arena Rl gw).locals_clock m3.locals m3.clock).trans heff_m3_m4
          exact (h1.trans h2).locals_clock bodyPost.locals bodyPost.clock
        have hiw'_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = iw.toNat + 1
          exact Nat.mod_eq_of_lt (by omega)
        have htot'_nat : totalw'.toNat = accessListPayloadPrefix s0 recsw.toNat (iw + 1#64).toNat := by
          rw [hiw'_nat, accessListPayloadPrefix]
          have hpref_le := accessListPayloadPrefix_le s0 recsw.toNat iw.toNat
          have hsl_le := accessSlotsPrefix_mono s0 recsw.toNat (j := iw.toNat) (k := nw.toNat) (by omega)
          have heh_ent_nat : (ehw + entryw).toNat = accessListEntryEncodedPure s0 (recsw.toNat + 24 * iw.toNat) := by
            rw [BitVec.toNat_add, heh_nat, hentry_nat]
            unfold accessListEntryEncodedPure accessListEntryPayloadPure
            dsimp only
            have hb1 := rlpHeaderLenPure_bounds (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
            have hb2 := rlpHeaderLenPure_bounds
              (21 + rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) + 33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
            exact Nat.mod_eq_of_lt (by omega)
          rw [show totalw' = totalw + (ehw + entryw) from rfl, BitVec.toNat_add, htot_eq, heh_ent_nat]
          unfold accessListEntryEncodedPure accessListEntryPayloadPure
          dsimp only
          have hb1 := rlpHeaderLenPure_bounds (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
          have hb2 := rlpHeaderLenPure_bounds
            (21 + rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) + 33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
          exact Nat.mod_eq_of_lt (by omega)
        have hbp_recs : bodyPost.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m6, m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_recs,
            show ofString "i" ≠ ofString "recs" by decide,
            show ofString "total" ≠ ofString "recs" by decide]
        have hbp_n : bodyPost.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m6, m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_n,
            show ofString "i" ≠ ofString "n" by decide,
            show ofString "total" ≠ ofString "n" by decide]
        have hbp_total : bodyPost.locals.lookup (ofString "total") = some (.val (.word totalw')) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m6, m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "total" by decide]
        have hbp_i : bodyPost.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hbp_glob : bodyPost.globals = s.globals := hm4_glob.trans hm2_glob
        have hbp_mem : bodyPost.memory = s.memory := hm4_mem.trans hm2_mem
        have hrec := ih bodyPost totalw' (iw + 1#64) hbp_clk (heff0.trans heff_s_bp)
          (by omega) htot'_nat hbp_recs hbp_n hbp_total hbp_i hnt
        dsimp only at hrec
        exact ⟨hrec.1, hrec.2.1.trans hbp_glob, hrec.2.2.1.trans hbp_mem,
          heff_s_bp.trans hrec.2.2.2.1, hrec.2.2.2.2⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      have hbw : BitVec.ofNat 64 (accessListPayloadPrefix s0 recsw.toNat nw.toNat) = totalw := by
        rw [← hieq, ← htot_eq]; simp
      rw [hbw]
      exact ⟨rfl, rfl, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_total⟩

private theorem eval_decCall_access_list_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (recsExp nExp : ExpHOL 64)
    (recsw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s0.code = originalRuntimeCode) (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots : accessSlotsPrefix s0 recsw.toNat nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat) ∧
      Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "access_list_payload_len") [recsExp, nExp] cont)).1 ≠
      some .timeOut) :
    let pl := BitVec.ofNat 64 (accessListPayloadPrefix s0 recsw.toNat nw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      pl.toNat = accessListPayloadPrefix s0 recsw.toNat nw.toNat ∧
      mid.clock ≤ s.clock ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word pl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "access_list_payload_len") [recsExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro pl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [recsExp, nExp] =
      some [.val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hrecs, hn]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "access_list_payload_len")
    (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_access_list_payload_len) recsw nw
    (by decide) (by rw [heff0.arena.1.code]; exact lookup_access_list_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "recs", ValueHOL.val (.word recsw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hb : sourceFnBody Guest.Software.guestFn_access_list_payload_len =
        .dec (ofString "total") .one (.const 0#64)
          (.dec (ofString "i") .one (.const 0#64)
            (.seq alPayloadLenWhile (.return (.var .local (ofString "total"))))) := rfl
    have hbody : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).1 ≠ some .timeOut →
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).1 =
          some (.returned (.val (.word pl))) ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2.globals = s.globals ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2.memory = s.memory ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2.clock ≤ s.clock ∧
        HeapByteEff s (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2 Rl gw := by
      intro hnt_b
      have hclk_b := evaluateHOLFiniteState_clock_le ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len)
      rw [hb] at hnt_b hclk_b ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      have hev0_t : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev0_t] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      set e1 := setVarHOLFinite (ofString "total") (.val (.word 0#64)) ent
      rw [evaluateHOLFiniteState_dec_total] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      have hev0_i : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev0_i] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      set e2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e1
      have heff_s_e2 : HeapByteEff s e2 Rl gw :=
        (HeapByteEff.refl heff0.arena Rl gw).locals_clock e2.locals e2.clock
      rw [evaluateHOLFiniteState_seq_line780] at hnt_b hclk_b ⊢
      rcases hw : evaluateHOLFiniteState e2 alPayloadLenWhile with ⟨rw_res, sw⟩
      have hnt_w : rw_res ≠ some .timeOut := by
        rintro rfl; simp only [hw] at hnt_b; exact hnt_b rfl
      have hloop := eval_alPayloadLenWhile_exact e2.clock s0 e2 Rl gw recsw nw 0#64 0#64
        hcode hAR0 hRl_ge le_rfl (heff0.trans heff_s_e2) hn_lt hslots hrecs_ok (by simp) (by simp [accessListPayloadPrefix])
        (by simp [e2, e1, ent, cmap, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "recs" by decide,
          show ofString "total" ≠ ofString "recs" by decide,
          show ofString "n" ≠ ofString "recs" by decide])
        (by simp [e2, e1, ent, cmap, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide,
          show ofString "total" ≠ ofString "n" by decide])
        (by simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "total" by decide])
        (by simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [hw]; exact hnt_w)
      dsimp only at hloop; rw [hw] at hloop
      obtain ⟨rfl, hsw_glob, hsw_mem, heff_w, hsw_tot⟩ := hloop
      dsimp only at hsw_glob hsw_mem heff_w hsw_tot
      simp only [hw] at hclk_b ⊢
      rw [evaluateHOLFiniteState_return] at hclk_b ⊢
      have hev_ret : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
          (.var .local (ofString "total")) = some (.val (.word pl)) := by
        simp [evalHOLExact, hsw_tot, pl]
      rw [hev_ret] at hclk_b ⊢; dsimp only at hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact])] at hclk_b ⊢
      dsimp only at hclk_b ⊢
      have hclk_le : sw.clock ≤ s.clock := by
        change sw.clock ≤ s.clock - 1 at hclk_b; omega
      exact ⟨rfl, hsw_glob, hsw_mem, hclk_le,
        (((heff_s_e2.trans heff_w).locals_clock _ _).locals_clock _ _).locals_clock _ _⟩
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_access_list_payload_len) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    obtain ⟨hrb, hsb_glob, hsb_mem, hsb_clk, heff_sb⟩ := hbody (by rw [hrun]; exact hnt_b)
    rw [hrun] at hrb hsb_glob hsb_mem hsb_clk heff_sb
    dsimp only at hrb hsb_glob hsb_mem hsb_clk heff_sb
    subst hrb
    simp only [hrun] at hnt ⊢
    have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh2] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word pl)) { sb.emptyLocalsHOLFinite with locals := s.locals }
    have hpl_nat : pl.toNat = accessListPayloadPrefix s0 recsw.toNat nw.toNat := by
      dsimp [pl]; rw [BitVec.toNat_ofNat]
      have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
      have hle := accessListPayloadPrefix_le s0 recsw.toNat nw.toNat
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hpl_nat, hsb_clk, hsb_glob, hsb_mem, rfl,
      heff_sb.locals_clock mid.locals mid.clock, hnt, rfl⟩

private def txPutAccessListKeysLoopBody : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"),
       .op .add [.var .local (ofString "keys"),
         .panop .mul [.var .local (ofString "j"), .const 32#64]],
       .const 32#64])
    (.seq
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))

private def txPutAccessListKeysWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "j")) (.var .local (ofString "ns")))
    txPutAccessListKeysLoopBody

private theorem eval_txPutAccessListKeysWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (dst0 recsw nw iw keysw nsw pw jw : BitVec 64) (pstart : Nat)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hns_lt : nsw.toNat < 2 ^ 32)
    (hj_le : jw.toNat ≤ nsw.toNat)
    (hp_eq : pw.toNat = pstart + 33 * jw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧ pstart + 33 * nsw.toNat ≤ ivl.1 + ivl.2)
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hl_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hl_keys : s.locals.lookup (ofString "keys") = some (.val (.word keysw)))
    (hl_ns : s.locals.lookup (ofString "ns") = some (.val (.word nsw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_j : s.locals.lookup (ofString "j") = some (.val (.word jw)))
    (hl_w : ∃ ww : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hnt : (evaluateHOLFiniteState s txPutAccessListKeysWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s txPutAccessListKeysWhile
    (out.1 = none →
      ∃ (pf wf : BitVec 64),
        pf.toNat = pstart + 33 * nsw.toNat ∧
        out.2.clock ≤ s.clock ∧
        out.2.globals = s.globals ∧
        HeapByteEff s out.2 Rl gw ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        out.2.locals.lookup (ofString "recs") = some (.val (.word recsw)) ∧
        out.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        out.2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pf)) ∧
        out.2.locals.lookup (ofString "w") = some (.val (.word wf))) ∧
    (out.1 ≠ none → out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1) := by
  induction clk generalizing s pw jw with
  | zero =>
    intro out; dsimp only [out, txPutAccessListKeysWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "j")) (.var .local (ofString "ns"))) =
        some (.val (.word (if jw.toNat < nsw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_j, hl_ns, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : jw.toNat < nsw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hjeq : jw.toNat = nsw.toNat := by omega
      obtain ⟨ww, hww⟩ := hl_w
      exact ⟨fun _ => ⟨pw, ww, by rw [← hjeq]; exact hp_eq, le_rfl, rfl,
        HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_recs, hl_n, hl_i, hl_p, hww⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, txPutAccessListKeysWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "j")) (.var .local (ofString "ns"))) =
        some (.val (.word (if jw.toNat < nsw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_j, hl_ns, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : jw.toNat < nsw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        have hev_src : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "keys"),
              .panop .mul [.var .local (ofString "j"), .const 32#64]]) =
            some (.val (.word (keysw + jw * 32#64))) := by
          have hz32 : jw * 32#64 + 0 = jw * 32#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_keys, hl_j, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz32]
        have hhl32 : rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat = 33 := by
          have : (32#64 : BitVec 64).toNat = 32 := by decide
          rw [this, rlpHeaderLenPure_of_le55 (by decide)]
        have hin_eb : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
            pw.toNat + rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat ≤ ivl.1 + ivl.2 := by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          refine ⟨ivl, hivl, by omega, ?_⟩
          rw [Nat.add_assoc, hhl32]
          have : 33 * (jw.toNat + 1) ≤ 33 * nsw.toNat := Nat.mul_le_mul_left _ (by omega)
          omega
        dsimp only [txPutAccessListKeysLoopBody] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hc_eb : evaluateHOLFiniteState sd
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"),
               .op .add [.var .local (ofString "keys"),
                 .panop .mul [.var .local (ofString "j"), .const 32#64]],
               .const 32#64]) with ⟨rc, m1⟩
        have hnt_eb : rc ≠ some .timeOut := by rintro rfl; simp only [hc_eb] at hnt; exact hnt rfl
        have heb := eval_call_local_rlp_encode_bytes_ge2 sd "w"
          (.var .local (ofString "p"))
          (.op .add [.var .local (ofString "keys"),
            .panop .mul [.var .local (ofString "j"), .const 32#64]])
          (.const 32#64)
          pw (keysw + jw * 32#64) 32#64 Rl gw heff0_sd.arena.1.code heff0_sd.arena
          hl_w (by simp [evalHOLExact, show sd.locals = s.locals from rfl, hl_p])
          hev_src rfl (by decide) (by rw [WkBlockTxEnc.heapEnd_val]; decide) hin_eb
          (by rw [hc_eb]; exact hnt_eb)
        have hclk_eb := evaluateHOLFiniteState_clock_le sd
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .op .add [.var .local (ofString "keys"),
               .panop .mul [.var .local (ofString "j"), .const 32#64]],
             .const 32#64])
        have hnbc_eb := call_noexc_ne_break_continue sd (some (VarKind.local, ofString "w"))
          (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .op .add [.var .local (ofString "keys"),
             .panop .mul [.var .local (ofString "j"), .const 32#64]],
           .const 32#64]
        dsimp only at heb; rw [hc_eb] at heb hclk_eb hnbc_eb
        simp only [hc_eb] at hnt ⊢
        cases rc with
        | some rc' =>
          have hnr := heb.2 (by simp)
          cases rc' with
          | «break» => exact absurd rfl hnbc_eb.1
          | «continue» => exact absurd rfl hnbc_eb.2
          | _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => ⟨by simp, by simp, hnr⟩⟩
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨len, hlen_eq, hp_lt_he, hm1_glob, hm1_loc, heff_m1⟩ := heb.1 rfl
          rw [hhl32] at hlen_eq
          have hm1_w : m1.locals.lookup (ofString "w") = some (.val (.word len)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "p" by decide]; exact hl_p
          have hm1_j : m1.locals.lookup (ofString "j") = some (.val (.word jw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "j" by decide]; exact hl_j
          have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "dst" by decide]; exact hl_dst
          have hm1_recs : m1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "recs" by decide]; exact hl_recs
          have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "n" by decide]; exact hl_n
          have hm1_i : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "i" by decide]; exact hl_i
          have hm1_keys : m1.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "keys" by decide]; exact hl_keys
          have hm1_ns : m1.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
            rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "w" ≠ ofString "ns" by decide]; exact hl_ns
          rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
          have hass_p : evaluateHOLFiniteState m1
              (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
              (none, setVarHOLFinite (ofString "p") (.val (.word (pw + len))) m1) := by
            rw [evaluateHOLFiniteState_assign]
            have hev_pw : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
                some (.val (.word (pw + len))) := by
              have hzl : len + 0 = len := BitVec.add_zero _
              simp [evalHOLExact, evalListHOLExact, hm1_p, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzl]
            rw [hev_pw]; dsimp only
            have hvv : isValidValueHOLFinite m1 .local (ofString "p") (.val (.word (pw + len))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm1_p, shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hvv]; rfl
          rw [hass_p] at hnt ⊢; dsimp only at hnt ⊢
          let m2 := setVarHOLFinite (ofString "p") (.val (.word (pw + len))) m1
          have hm2_j : m2.locals.lookup (ofString "j") = some (.val (.word jw)) := by
            simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_j,
              show ofString "p" ≠ ofString "j" by decide]
          have hass_j : evaluateHOLFiniteState m2
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])) =
              (none, setVarHOLFinite (ofString "j") (.val (.word (jw + 1#64))) m2) := by
            rw [evaluateHOLFiniteState_assign]
            have hev_jw : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
                (.op .add [.var .local (ofString "j"), .const 1#64]) =
                some (.val (.word (jw + 1#64))) := by
              simp [evalHOLExact, evalListHOLExact, hm2_j, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_jw]; dsimp only
            have hvv : isValidValueHOLFinite m2 .local (ofString "j") (.val (.word (jw + 1#64))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm2_j, shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hvv]; rfl
          rw [hass_j] at hnt ⊢; dsimp only at hnt ⊢
          let m3 := setVarHOLFinite (ofString "j") (.val (.word (jw + 1#64))) m2
          have heff_s_m3 : HeapByteEff s m3 Rl gw :=
            (heff_sd.trans heff_m1).locals_clock m3.locals m3.clock
          have hm3_clk_s : m3.clock ≤ s.clock := by
            change m1.clock ≤ s.clock; change m1.clock ≤ s.clock - 1 at hclk_eb; omega
          have hm3_clk : m3.clock ≤ k := by
            change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_eb; omega
          have hjw'_nat : (jw + 1#64).toNat = jw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (jw.toNat + 1) % 2 ^ 64 = jw.toNat + 1
            exact Nat.mod_eq_of_lt (by omega)
          have hpw'_nat : (pw + len).toNat = pstart + 33 * (jw + 1#64).toNat := by
            rw [hjw'_nat, BitVec.toNat_add, hlen_eq, hp_eq]
            have hp_lt_he' : pstart + 33 * jw.toNat < heapEnd := hp_eq ▸ hp_lt_he
            exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hp_lt_he'; omega)
          have hm3_dst : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
              show ofString "j" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide]
          have hm3_recs : m3.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
              show ofString "j" ≠ ofString "recs" by decide, show ofString "p" ≠ ofString "recs" by decide]
          have hm3_n : m3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
              show ofString "j" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide]
          have hm3_i : m3.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_i,
              show ofString "j" ≠ ofString "i" by decide, show ofString "p" ≠ ofString "i" by decide]
          have hm3_keys : m3.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_keys,
              show ofString "j" ≠ ofString "keys" by decide, show ofString "p" ≠ ofString "keys" by decide]
          have hm3_ns : m3.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_ns,
              show ofString "j" ≠ ofString "ns" by decide, show ofString "p" ≠ ofString "ns" by decide]
          have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word (pw + len))) := by
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "p" by decide]
          have hm3_j : m3.locals.lookup (ofString "j") = some (.val (.word (jw + 1#64))) := by
            simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hm3_w : ∃ ww : BitVec 64, m3.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            refine ⟨len, ?_⟩
            simp [m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
              show ofString "j" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]
          have hrec := ih m3 (pw + len) (jw + 1#64) hm3_clk (heff0.trans heff_s_m3)
            (by omega) hpw'_nat hm3_dst hm3_recs hm3_n hm3_i hm3_keys hm3_ns hm3_p hm3_j hm3_w hnt
          dsimp only at hrec
          refine ⟨fun hnone => ?_, hrec.2⟩
          obtain ⟨pf, wf, hpf_eq, hm_clk_rec, hm3_glob, heff_rec, hd, hr, hn', hi', hp', hw'⟩ := hrec.1 hnone
          exact ⟨pf, wf, hpf_eq, le_trans hm_clk_rec hm3_clk_s, hm3_glob.trans hm1_glob,
            heff_s_m3.trans heff_rec, hd, hr, hn', hi', hp', hw'⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hjeq : jw.toNat = nsw.toNat := by omega
      obtain ⟨ww, hww⟩ := hl_w
      exact ⟨fun _ => ⟨pw, ww, by rw [← hjeq]; exact hp_eq, le_rfl, rfl,
        HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_recs, hl_n, hl_i, hl_p, hww⟩,
        fun h => False.elim (h rfl)⟩

private theorem accessListPayloadPrefix_mono {F : Type} (s : PanSemStateFiniteExact 64 F) (recs : Nat)
    {j k : Nat} (hjk : j ≤ k) :
    accessListPayloadPrefix s recs j ≤ accessListPayloadPrefix s recs k := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => rw [accessListPayloadPrefix]; omega

private def txPutAccessListAfterIh : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "p"),
       .op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]])
    (.seq
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.seq
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "rec"), .const 0#64]),
           .const 20#64])
        (.seq
          (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.seq
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
              [.var .local (ofString "p"), .var .local (ofString "inner")])
            (.seq
              (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.dec (ofString "keys") .one
                (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64]))
                (.dec (ofString "j") .one (.const 0#64)
                  (.seq
                    txPutAccessListKeysWhile
                    (.assign .local (ofString "i")
                      (.op .add [.var .local (ofString "i"), .const 1#64]))))))))))

private def txPutAccessListLoopBody : ProgHOL 64 :=
  .dec (ofString "rec") .one
    (.op .add [.var .local (ofString "recs"),
      .panop .mul [.var .local (ofString "i"), .const 24#64]])
    (.dec (ofString "ns") .one
      (.load .one (.op .add [.var .local (ofString "rec"), .const 16#64]))
      (.dec (ofString "inner") .one
        (.panop .mul [.const 33#64, .var .local (ofString "ns")])
        (.decCall (ofString "ih") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "inner")]
          txPutAccessListAfterIh)))

private def txPutAccessListWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    txPutAccessListLoopBody

private theorem eval_txPutAccessListWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (dst0 recsw nw pw iw : BitVec 64) (pstart : Nat)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots : accessSlotsPrefix s0 recsw.toNat nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat) ∧
      Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hi_le : iw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧
      pstart + accessListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2)
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hl_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hl_w : ∃ ww : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hnt : (evaluateHOLFiniteState s txPutAccessListWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s txPutAccessListWhile
    (out.1 = none →
      ∃ pf : BitVec 64,
        pf.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat nw.toNat ∧
        out.2.globals = s.globals ∧
        HeapByteEff s out.2 Rl gw ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pf))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  induction clk generalizing s pw iw with
  | zero =>
    intro out; dsimp only [out, txPutAccessListWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, txPutAccessListWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        obtain ⟨hwok, hin_recs⟩ := hrecs_ok (by omega)
        have hfit := inside_fit_u64 hin_recs hAR0.2.2.1
        have hmul_nat : (iw * 24#64).toNat = 24 * iw.toNat := by
          rw [BitVec.toNat_mul]; change (iw.toNat * 24) % 2 ^ 64 = 24 * iw.toNat
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        set recw := recsw + iw * 24#64
        have hrec_nat : recw.toNat = recsw.toNat + 24 * iw.toNat := by
          rw [show recw = recsw + iw * 24#64 from rfl, BitVec.toNat_add, hmul_nat]
          have : 24 * iw.toNat + 24 ≤ 24 * nw.toNat := by omega
          exact Nat.mod_eq_of_lt (by omega)
        have hns_lt : memW s0 (recsw.toNat + 24 * iw.toNat + 16) < 2 ^ 32 := by
          have := accessListEntry_slot_le_prefix s0 recsw.toNat iw.toNat nw.toNat hlt
          omega
        set nsw := BitVec.ofNat 64 (memW s0 (recsw.toNat + 24 * iw.toNat + 16))
        have hnsw_nat : nsw.toNat = memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
          dsimp [nsw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        set innerw := 33#64 * nsw
        have hinner_nat : innerw.toNat = 33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
          rw [show innerw = 33#64 * nsw from rfl, BitVec.toNat_mul, hnsw_nat]
          change (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        dsimp only [txPutAccessListLoopBody] at hnt ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hev_rec : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "recs"),
              .panop .mul [.var .local (ofString "i"), .const 24#64]]) =
            some (.val (.word recw)) := by
          have hz24 : iw * 24#64 + 0 = iw * 24#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_recs, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, hz24, recw]
        rw [hev_rec] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢; dsimp only at hnt ⊢
        set d1 := setVarHOLFinite (ofString "rec") (.val (.word recw)) sd
        have heff_sd_d1 : HeapByteEff sd d1 Rl gw :=
          (HeapByteEff.refl heff0_sd.arena Rl gw).locals_clock d1.locals d1.clock
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hrec16_nat : (recw + 16#64).toNat = recsw.toNat + 24 * iw.toNat + 16 := by
          rw [BitVec.toNat_add, hrec_nat]
          have : 24 * iw.toNat + 24 ≤ 24 * nw.toNat := by omega
          change (recsw.toNat + 24 * iw.toNat + 16) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hwa16 : WordAt s0 (recw + 16#64).toNat := by
          rw [hrec16_nat]
          have h := wordAt_of_wordsOK hwok (3 * iw.toNat + 2) (by dsimp; omega)
          dsimp only at h
          have heq : recsw.toNat + 8 * (3 * iw.toNat + 2) = recsw.toNat + 24 * iw.toNat + 16 := by omega
          exact heq ▸ h
        have hload_ns : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "rec"), .const 16#64])) =
            some (.val (.word nsw)) := by
          have hl := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs (heff0_sd.trans heff_sd_d1) hRl_ge hin_recs
            (.op .add [.var .local (ofString "rec"), .const 16#64]) (recw + 16#64)
            (by simp [evalHOLExact, evalListHOLExact, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update,
              FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord])
            hwa16 (by dsimp; omega) (by dsimp; omega)
          rw [hrec16_nat] at hl
          exact hl
        rw [hload_ns] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢; dsimp only at hnt ⊢
        set d2 := setVarHOLFinite (ofString "ns") (.val (.word nsw)) d1
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hev_inner : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
            (.panop .mul [.const 33#64, .var .local (ofString "ns")]) =
            some (.val (.word innerw)) := by
          have h1 : nsw * 1#64 = nsw := BitVec.mul_one _
          simp [evalHOLExact, evalListHOLExact, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update,
            FUPDATE, panOpHOL, valueIsWord, valueWord, innerw, h1]
        rw [hev_inner] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢; dsimp only at hnt ⊢
        set d3 := setVarHOLFinite (ofString "inner") (.val (.word innerw)) d2
        have hnt_d3 : (evaluateHOLFiniteState d3
            (.decCall (ofString "ih") .one (ofString "rlp_list_header_len")
              [.var .local (ofString "inner")] txPutAccessListAfterIh)).1 ≠ some .timeOut := by
          intro hto; rw [hto] at hnt; exact hnt rfl
        have hd3_ar : ArenaReady d3 := localsFree_arenaReady s d3.locals d3.clock heff0.arena
        obtain ⟨m1, hih_nat, hih_ge, hih_le, hc_ih, hm1_glob, hm1_mem, hm1_loc, heff_d3_m1, hnt_m1, hout_m1⟩ :=
          eval_decCall_rlp_list_header_len_clk d3 "ih" (.var .local (ofString "inner")) innerw txPutAccessListAfterIh Rl gw
            heff0.arena.1.code hd3_ar
            (by simp [evalHOLExact, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt_d3
        rw [hout_m1] at hnt ⊢; dsimp only [txPutAccessListAfterIh] at hnt_m1 hnt ⊢
        set ihw := BitVec.ofNat 64 (rlpHeaderLenPure innerw.toNat)
        set entryw := 21#64 + (ihw + innerw)
        have hentry_nat : entryw.toNat = accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat) := by
          have hb_in := rlpHeaderLenPure_bounds (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
          have h1 : (ihw + innerw).toNat = rlpHeaderLenPure innerw.toNat + innerw.toNat := by
            rw [BitVec.toNat_add, hih_nat, hinner_nat]; exact Nat.mod_eq_of_lt (by omega)
          rw [show entryw = 21#64 + (ihw + innerw) from rfl, BitVec.toNat_add, h1, hinner_nat]
          unfold accessListEntryPayloadPure; dsimp only
          change (21 + (rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) +
            33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))) % 2 ^ 64 = _
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have hm1_ih : m1.locals.lookup (ofString "ih") = some (.val (.word ihw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ihw]
        have hm1_inner : m1.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, setVarHOLFinite,
            show ofString "ih" ≠ ofString "inner" by decide]
        have hm1_ns : m1.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, setVarHOLFinite,
            show ofString "ih" ≠ ofString "ns" by decide,
            show ofString "inner" ≠ ofString "ns" by decide]
        have hm1_rec : m1.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show ofString "ih" ≠ ofString "rec" by decide,
            show ofString "inner" ≠ ofString "rec" by decide,
            show ofString "ns" ≠ ofString "rec" by decide]
        have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_p,
            show ofString "ih" ≠ ofString "p" by decide,
            show ofString "inner" ≠ ofString "p" by decide,
            show ofString "ns" ≠ ofString "p" by decide,
            show ofString "rec" ≠ ofString "p" by decide]
        have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_dst,
            show ofString "ih" ≠ ofString "dst" by decide,
            show ofString "inner" ≠ ofString "dst" by decide,
            show ofString "ns" ≠ ofString "dst" by decide,
            show ofString "rec" ≠ ofString "dst" by decide]
        have hm1_recs : m1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_recs,
            show ofString "ih" ≠ ofString "recs" by decide,
            show ofString "inner" ≠ ofString "recs" by decide,
            show ofString "ns" ≠ ofString "recs" by decide,
            show ofString "rec" ≠ ofString "recs" by decide]
        have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_n,
            show ofString "ih" ≠ ofString "n" by decide,
            show ofString "inner" ≠ ofString "n" by decide,
            show ofString "ns" ≠ ofString "n" by decide,
            show ofString "rec" ≠ ofString "n" by decide]
        have hm1_i : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_i,
            show ofString "ih" ≠ ofString "i" by decide,
            show ofString "inner" ≠ ofString "i" by decide,
            show ofString "ns" ≠ ofString "i" by decide,
            show ofString "rec" ≠ ofString "i" by decide]
        have hm1_w : ∃ ww : BitVec 64, m1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
          obtain ⟨ww, hww⟩ := hl_w
          refine ⟨ww, ?_⟩
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d3, d2, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hww,
            show ofString "ih" ≠ ofString "w" by decide,
            show ofString "inner" ≠ ofString "w" by decide,
            show ofString "ns" ≠ ofString "w" by decide,
            show ofString "rec" ≠ ofString "w" by decide]
        have heff_s_m1 : HeapByteEff s m1 Rl gw :=
          ((heff_sd.locals_clock d3.locals d3.clock).trans heff_d3_m1)
        obtain ⟨ivl, hivl, hivl_lo, hivl_hi⟩ := hin_ivl
        have hpref_next_le : accessListPayloadPrefix s0 recsw.toNat (iw.toNat + 1) ≤
            accessListPayloadPrefix s0 recsw.toNat nw.toNat :=
          accessListPayloadPrefix_mono s0 recsw.toNat (by omega)
        have hpref_succ : accessListPayloadPrefix s0 recsw.toNat (iw.toNat + 1) =
            accessListPayloadPrefix s0 recsw.toNat iw.toNat +
            rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) +
            21 + rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) +
            33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
          rw [accessListPayloadPrefix]
          unfold accessListEntryEncodedPure accessListEntryPayloadPure
          dsimp only; omega
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
        rcases hc1_run : evaluateHOLFiniteState m1
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
              [.var .local (ofString "p"),
               .op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]]) with ⟨rc1, m2⟩
        have hnt_c1 : rc1 ≠ some .timeOut := by rintro rfl; simp only [hc1_run] at hnt_m1; exact hnt_m1 rfl
        have hc1_spec := eval_call_local_rlp_encode_list_header m1 "w"
          (.var .local (ofString "p"))
          (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")])
          pw entryw Rl gw heff_s_m1.arena.1.code heff_s_m1.arena hm1_w
          (by simp [evalHOLExact, hm1_p])
          (by
            have hzi : innerw + 0 = innerw := BitVec.add_zero _
            simp [evalHOLExact, evalListHOLExact, hm1_ih, hm1_inner, wordOpHOL, wordOp,
              valueIsWord, valueWord, hzi, entryw])
          ⟨ivl, hivl, by omega, by rw [hentry_nat]; omega⟩
          (by rw [hc1_run]; exact hnt_c1)
        have hclk_c1 := evaluateHOLFiniteState_clock_le m1
          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
            [.var .local (ofString "p"),
             .op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]])
        have hnbc_c1 := call_noexc_ne_break_continue m1 (some (VarKind.local, ofString "w"))
          (ofString "rlp_encode_list_header")
          [.var .local (ofString "p"),
           .op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]]
        dsimp only at hc1_spec; rw [hc1_run] at hc1_spec hclk_c1 hnbc_c1
        simp only [hc1_run] at hnt_m1 hnt ⊢
        cases rc1 with
        | some r =>
          have hnr := hc1_spec.2 (by simp)
          cases r with
          | «break» => exact absurd rfl hnbc_c1.1
          | «continue» => exact absurd rfl hnbc_c1.2
          | _ => dsimp only; exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | none =>
          dsimp only at hnt_m1 hnt ⊢
          obtain ⟨w1, hw1_nat, _, _, hp_lt_he, hm2_glob, hm2_loc, heff_m1_m2⟩ := hc1_spec.1 rfl
          dsimp only at hm2_glob hm2_loc heff_m1_m2 hclk_c1
          rw [hentry_nat] at hw1_nat
          rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
          have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word pw)) := by
            rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_p,
              show ofString "w" ≠ ofString "p" by decide]
          have hm2_w : m2.locals.lookup (ofString "w") = some (.val (.word w1)) := by
            rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hass_p1 : evaluateHOLFiniteState m2
              (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
              (none, setVarHOLFinite (ofString "p") (.val (.word (pw + w1))) m2) := by
            rw [evaluateHOLFiniteState_assign]
            have hev : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
                some (.val (.word (pw + w1))) := by
              have hz1 : w1 + 0 = w1 := BitVec.add_zero _
              simp [evalHOLExact, evalListHOLExact, hm2_p, hm2_w, wordOpHOL, wordOp, valueIsWord, valueWord, hz1]
            rw [hev]; dsimp only
            rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm2_p, shapeOfHOLExact, shapeEqHOL])]
            rfl
          rw [hass_p1] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
          set m3 := setVarHOLFinite (ofString "p") (.val (.word (pw + w1))) m2
          set p1 := pw + w1
          have heff_s_m3 : HeapByteEff s m3 Rl gw :=
            (heff_s_m1.trans heff_m1_m2).locals_clock m3.locals m3.clock
          have heff0_m3 : HeapByteEff s0 m3 Rl gw := heff0.trans heff_s_m3
          have hp1_nat : p1.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat +
              rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) := by
            rw [show p1 = pw + w1 from rfl, BitVec.toNat_add, hp_eq, hw1_nat]
            have hbnd := rlpHeaderLenPure_bounds (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat))
            have hp_lt_he' : pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat < heapEnd := hp_eq ▸ hp_lt_he
            exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hp_lt_he'; omega)
          have hm3_rec : m3.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
            simp [m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE, hm1_rec,
              show ofString "p" ≠ ofString "rec" by decide, show ofString "w" ≠ ofString "rec" by decide]
          have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word p1)) := by
            simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, p1]
          have hm3_w : ∃ ww : BitVec 64, m3.locals.lookup (ofString "w") = some (.val (.word ww)) :=
            ⟨w1, by simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_w,
              show ofString "p" ≠ ofString "w" by decide]⟩
          have hrec0_nat : (recw + 0#64).toNat = recsw.toNat + 24 * iw.toNat := by
            rw [BitVec.add_zero, hrec_nat]
          have hwa0 : WordAt s0 (recw + 0#64).toNat := by
            rw [hrec0_nat]
            have h := wordAt_of_wordsOK hwok (3 * iw.toNat) (by dsimp; omega)
            dsimp only at h
            have heq : recsw.toNat + 8 * (3 * iw.toNat) = recsw.toNat + 24 * iw.toNat := by omega
            exact heq ▸ h
          have hload_addr : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "rec"), .const 0#64])) =
              some (.val (.word (BitVec.ofNat 64 (memW s0 (recsw.toNat + 24 * iw.toNat))))) := by
            have hl := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs heff0_m3 hRl_ge hin_recs
              (.op .add [.var .local (ofString "rec"), .const 0#64]) (recw + 0#64)
              (by simp [evalHOLExact, evalListHOLExact, hm3_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
              hwa0 (by dsimp; omega) (by dsimp; omega)
            rw [hrec0_nat] at hl; exact hl
          have hhl20 : rlpHeaderLenPure (20#64 : BitVec 64).toNat + (20#64 : BitVec 64).toNat = 21 := by
            have : (20#64 : BitVec 64).toNat = 20 := by decide
            rw [this, rlpHeaderLenPure_of_le55 (by decide)]
          rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
          rcases hc2_run : evaluateHOLFiniteState m3
              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                [.var .local (ofString "p"),
                 .load .one (.op .add [.var .local (ofString "rec"), .const 0#64]),
                 .const 20#64]) with ⟨rc2, m4⟩
          have hnt_c2 : rc2 ≠ some .timeOut := by rintro rfl; simp only [hc2_run] at hnt_m1; exact hnt_m1 rfl
          have hc2_spec := eval_call_local_rlp_encode_bytes_ge2 m3 "w"
            (.var .local (ofString "p"))
            (.load .one (.op .add [.var .local (ofString "rec"), .const 0#64]))
            (.const 20#64)
            p1 (BitVec.ofNat 64 (memW s0 (recsw.toNat + 24 * iw.toNat))) 20#64
            Rl gw heff_s_m3.arena.1.code heff_s_m3.arena hm3_w
            (by simp [evalHOLExact, hm3_p])
            hload_addr rfl (by decide) (by rw [WkBlockTxEnc.heapEnd_val]; decide)
            ⟨ivl, hivl, by omega, by rw [Nat.add_assoc, hhl20]; omega⟩
            (by rw [hc2_run]; exact hnt_c2)
          have hclk_c2 := evaluateHOLFiniteState_clock_le m3
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "rec"), .const 0#64]),
               .const 20#64])
          have hnbc_c2 := call_noexc_ne_break_continue m3 (some (VarKind.local, ofString "w"))
            (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "rec"), .const 0#64]),
             .const 20#64]
          dsimp only at hc2_spec; rw [hc2_run] at hc2_spec hclk_c2 hnbc_c2
          simp only [hc2_run] at hnt_m1 hnt ⊢
          cases rc2 with
          | some r =>
            have hnr := hc2_spec.2 (by simp)
            cases r with
            | «break» => exact absurd rfl hnbc_c2.1
            | «continue» => exact absurd rfl hnbc_c2.2
            | _ => dsimp only; exact ⟨fun h => by simp at h, fun _ => hnr⟩
          | none =>
            dsimp only at hnt_m1 hnt ⊢
            obtain ⟨w2, hw2_nat, hp1_lt_he, hm4_glob, hm4_loc, heff_m3_m4⟩ := hc2_spec.1 rfl
            dsimp only at hm4_glob hm4_loc heff_m3_m4 hclk_c2
            rw [hhl20] at hw2_nat
            rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
            have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word p1)) := by
              rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_p,
                show ofString "w" ≠ ofString "p" by decide]
            have hm4_w : m4.locals.lookup (ofString "w") = some (.val (.word w2)) := by
              rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hass_p2 : evaluateHOLFiniteState m4
                (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
                (none, setVarHOLFinite (ofString "p") (.val (.word (p1 + w2))) m4) := by
              rw [evaluateHOLFiniteState_assign]
              have hev : @evalHOLExact 64 F _ m4.toExact (fun a => Classical.propDecidable (m4.memaddrs a))
                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
                  some (.val (.word (p1 + w2))) := by
                have hz2 : w2 + 0 = w2 := BitVec.add_zero _
                simp [evalHOLExact, evalListHOLExact, hm4_p, hm4_w, wordOpHOL, wordOp, valueIsWord, valueWord, hz2]
              rw [hev]; dsimp only
              rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm4_p, shapeOfHOLExact, shapeEqHOL])]
              rfl
            rw [hass_p2] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
            set m5 := setVarHOLFinite (ofString "p") (.val (.word (p1 + w2))) m4
            set p2 := p1 + w2
            have heff_s_m5 : HeapByteEff s m5 Rl gw :=
              (heff_s_m3.trans heff_m3_m4).locals_clock m5.locals m5.clock
            have hp2_nat : p2.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat +
                rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) + 21 := by
              rw [show p2 = p1 + w2 from rfl, BitVec.toNat_add, hp1_nat, hw2_nat]
              have hp1_lt_he' : pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat +
                  rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) < heapEnd :=
                hp1_nat ▸ hp1_lt_he
              exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hp1_lt_he'; omega)
            have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word p2)) := by
              simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, p2]
            have hm5_inner : m5.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
              simp [m5, setVarHOLFinite, hm4_loc, m3, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE, hm1_inner,
                show ofString "p" ≠ ofString "inner" by decide, show ofString "w" ≠ ofString "inner" by decide]
            have hm5_w : ∃ ww : BitVec 64, m5.locals.lookup (ofString "w") = some (.val (.word ww)) :=
              ⟨w2, by simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_w,
                show ofString "p" ≠ ofString "w" by decide]⟩
            rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
            rcases hc3_run : evaluateHOLFiniteState m5
                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
                  [.var .local (ofString "p"), .var .local (ofString "inner")]) with ⟨rc3, m6⟩
            have hnt_c3 : rc3 ≠ some .timeOut := by rintro rfl; simp only [hc3_run] at hnt_m1; exact hnt_m1 rfl
            have hc3_spec := eval_call_local_rlp_encode_list_header m5 "w"
              (.var .local (ofString "p")) (.var .local (ofString "inner"))
              p2 innerw Rl gw heff_s_m5.arena.1.code heff_s_m5.arena hm5_w
              (by simp [evalHOLExact, hm5_p])
              (by simp [evalHOLExact, hm5_inner])
              ⟨ivl, hivl, by omega, by rw [hinner_nat]; omega⟩
              (by rw [hc3_run]; exact hnt_c3)
            have hclk_c3 := evaluateHOLFiniteState_clock_le m5
              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "p"), .var .local (ofString "inner")])
            have hnbc_c3 := call_noexc_ne_break_continue m5 (some (VarKind.local, ofString "w"))
              (ofString "rlp_encode_list_header")
              [.var .local (ofString "p"), .var .local (ofString "inner")]
            dsimp only at hc3_spec; rw [hc3_run] at hc3_spec hclk_c3 hnbc_c3
            simp only [hc3_run] at hnt_m1 hnt ⊢
            cases rc3 with
            | some r =>
              have hnr := hc3_spec.2 (by simp)
              cases r with
              | «break» => exact absurd rfl hnbc_c3.1
              | «continue» => exact absurd rfl hnbc_c3.2
              | _ => dsimp only; exact ⟨fun h => by simp at h, fun _ => hnr⟩
            | none =>
              dsimp only at hnt_m1 hnt ⊢
              obtain ⟨w3, hw3_nat, _, _, hp2_lt_he, hm6_glob, hm6_loc, heff_m5_m6⟩ := hc3_spec.1 rfl
              dsimp only at hm6_glob hm6_loc heff_m5_m6 hclk_c3
              rw [hinner_nat] at hw3_nat
              rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
              have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word p2)) := by
                rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_p,
                  show ofString "w" ≠ ofString "p" by decide]
              have hm6_w : m6.locals.lookup (ofString "w") = some (.val (.word w3)) := by
                rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              have hass_p3 : evaluateHOLFiniteState m6
                  (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
                  (none, setVarHOLFinite (ofString "p") (.val (.word (p2 + w3))) m6) := by
                rw [evaluateHOLFiniteState_assign]
                have hev : @evalHOLExact 64 F _ m6.toExact (fun a => Classical.propDecidable (m6.memaddrs a))
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
                    some (.val (.word (p2 + w3))) := by
                  have hz3 : w3 + 0 = w3 := BitVec.add_zero _
                  simp [evalHOLExact, evalListHOLExact, hm6_p, hm6_w, wordOpHOL, wordOp, valueIsWord, valueWord, hz3]
                rw [hev]; dsimp only
                rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm6_p, shapeOfHOLExact, shapeEqHOL])]
                rfl
              rw [hass_p3] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              set m7 := setVarHOLFinite (ofString "p") (.val (.word (p2 + w3))) m6
              set p3 := p2 + w3
              have heff_s_m7 : HeapByteEff s m7 Rl gw :=
                (heff_s_m5.trans heff_m5_m6).locals_clock m7.locals m7.clock
              have heff0_m7 : HeapByteEff s0 m7 Rl gw := heff0.trans heff_s_m7
              have hp3_nat : p3.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat +
                  rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) + 21 +
                  rlpHeaderLenPure (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16)) := by
                rw [show p3 = p2 + w3 from rfl, BitVec.toNat_add, hp2_nat, hw3_nat]
                have hbnd := rlpHeaderLenPure_bounds (33 * memW s0 (recsw.toNat + 24 * iw.toNat + 16))
                have hp2_lt_he' : pstart + accessListPayloadPrefix s0 recsw.toNat iw.toNat +
                    rlpHeaderLenPure (accessListEntryPayloadPure s0 (recsw.toNat + 24 * iw.toNat)) + 21 < heapEnd :=
                  hp2_nat ▸ hp2_lt_he
                exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hp2_lt_he'; omega)
              have hm7_rec : m7.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
                simp [m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc, HolFiniteMapExact.lookup_update,
                  FUPDATE, hm1_rec, show ofString "p" ≠ ofString "rec" by decide,
                  show ofString "w" ≠ ofString "rec" by decide]
              have hrec8_nat : (recw + 8#64).toNat = recsw.toNat + 24 * iw.toNat + 8 := by
                rw [BitVec.toNat_add, hrec_nat]
                have : 24 * iw.toNat + 24 ≤ 24 * nw.toNat := by omega
                change (recsw.toNat + 24 * iw.toNat + 8) % 2 ^ 64 = _
                exact Nat.mod_eq_of_lt (by omega)
              have hwa8 : WordAt s0 (recw + 8#64).toNat := by
                rw [hrec8_nat]
                have h := wordAt_of_wordsOK hwok (3 * iw.toNat + 1) (by dsimp; omega)
                dsimp only at h
                have heq : recsw.toNat + 8 * (3 * iw.toNat + 1) = recsw.toNat + 24 * iw.toNat + 8 := by omega
                exact heq ▸ h
              set keysw := BitVec.ofNat 64 (memW s0 (recsw.toNat + 24 * iw.toNat + 8))
              have hload_keys : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) =
                  some (.val (.word keysw)) := by
                have hl := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs heff0_m7 hRl_ge hin_recs
                  (.op .add [.var .local (ofString "rec"), .const 8#64]) (recw + 8#64)
                  (by simp [evalHOLExact, evalListHOLExact, hm7_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
                  hwa8 (by dsimp; omega) (by dsimp; omega)
                rw [hrec8_nat] at hl; exact hl
              rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              rw [hload_keys] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              set m8 := setVarHOLFinite (ofString "keys") (.val (.word keysw)) m7
              rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              have hev_j0 : @evalHOLExact 64 F _ m8.toExact (fun a => Classical.propDecidable (m8.memaddrs a))
                  (.const 0#64) = some (.val (.word 0#64)) := rfl
              rw [hev_j0] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hnt ⊢; dsimp only at hnt_m1 hnt ⊢
              set m9 := setVarHOLFinite (ofString "j") (.val (.word 0#64)) m8
              have heff_s_m9 : HeapByteEff s m9 Rl gw :=
                heff_s_m7.locals_clock m9.locals m9.clock
              rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hnt ⊢
              rcases hkeys_run : evaluateHOLFiniteState m9 txPutAccessListKeysWhile with ⟨rk_res, sk⟩
              have hnt_k : rk_res ≠ some .timeOut := by
                rintro rfl; simp only [hkeys_run] at hnt_m1; exact hnt_m1 rfl
              have hin_keys : ∃ ivl ∈ Rl, ivl.1 ≤ p3.toNat ∧ p3.toNat + 33 * nsw.toNat ≤ ivl.1 + ivl.2 := by
                refine ⟨ivl, hivl, by omega, ?_⟩
                rw [hp3_nat, hnsw_nat]; omega
              have hkeys := eval_txPutAccessListKeysWhile_exact m9.clock s0 m9 Rl gw
                dst0 recsw nw iw keysw nsw p3 0#64 p3.toNat le_rfl (heff0.trans heff_s_m9)
                (by rw [hnsw_nat]; exact hns_lt) (by simp) (by simp) hin_keys
                (by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc,
                  HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
                  show ofString "j" ≠ ofString "dst" by decide, show ofString "keys" ≠ ofString "dst" by decide,
                  show ofString "p" ≠ ofString "dst" by decide, show ofString "w" ≠ ofString "dst" by decide])
                (by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc,
                  HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
                  show ofString "j" ≠ ofString "recs" by decide, show ofString "keys" ≠ ofString "recs" by decide,
                  show ofString "p" ≠ ofString "recs" by decide, show ofString "w" ≠ ofString "recs" by decide])
                (by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc,
                  HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
                  show ofString "j" ≠ ofString "n" by decide, show ofString "keys" ≠ ofString "n" by decide,
                  show ofString "p" ≠ ofString "n" by decide, show ofString "w" ≠ ofString "n" by decide])
                (by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc,
                  HolFiniteMapExact.lookup_update, FUPDATE, hm1_i,
                  show ofString "j" ≠ ofString "i" by decide, show ofString "keys" ≠ ofString "i" by decide,
                  show ofString "p" ≠ ofString "i" by decide, show ofString "w" ≠ ofString "i" by decide])
                (by simp [m9, m8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "j" ≠ ofString "keys" by decide])
                (by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, m5, hm4_loc, m3, hm2_loc,
                  HolFiniteMapExact.lookup_update, FUPDATE, hm1_ns,
                  show ofString "j" ≠ ofString "ns" by decide, show ofString "keys" ≠ ofString "ns" by decide,
                  show ofString "p" ≠ ofString "ns" by decide, show ofString "w" ≠ ofString "ns" by decide])
                (by simp [m9, m8, m7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, p3,
                  show ofString "j" ≠ ofString "p" by decide, show ofString "keys" ≠ ofString "p" by decide])
                (by simp [m9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                ⟨w3, by simp [m9, m8, m7, setVarHOLFinite, hm6_loc, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "j" ≠ ofString "w" by decide, show ofString "keys" ≠ ofString "w" by decide,
                  show ofString "p" ≠ ofString "w" by decide]⟩
                (by rw [hkeys_run]; exact hnt_k)
              dsimp only at hkeys; rw [hkeys_run] at hkeys
              simp only [hkeys_run] at hnt_m1 hnt ⊢
              cases rk_res with
              | some rk' =>
                obtain ⟨hnb, hnc, hnr⟩ := hkeys.2 (by simp)
                cases rk' with
                | «break» => exact absurd rfl hnb
                | «continue» => exact absurd rfl hnc
                | _ => dsimp only; exact ⟨fun h => by simp at h, fun _ => hnr⟩
              | none =>
                dsimp only at hnt_m1 hnt ⊢
                obtain ⟨pfk, wfk, hpfk_eq, hsk_clk, hsk_glob, heff_m9_sk, hsk_dst, hsk_recs, hsk_n, hsk_i, hsk_p, hsk_w⟩ :=
                  hkeys.1 rfl
                dsimp only at hsk_clk hsk_glob heff_m9_sk hsk_dst hsk_recs hsk_n hsk_i hsk_p hsk_w
                have hass_i : evaluateHOLFiniteState sk
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
                    (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) sk) := by
                  rw [evaluateHOLFiniteState_assign]
                  have hev : @evalHOLExact 64 F _ sk.toExact (fun a => Classical.propDecidable (sk.memaddrs a))
                      (.op .add [.var .local (ofString "i"), .const 1#64]) =
                      some (.val (.word (iw + 1#64))) := by
                    simp [evalHOLExact, evalListHOLExact, hsk_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                  rw [hev]; dsimp only
                  rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hsk_i, shapeOfHOLExact, shapeEqHOL])]
                  rfl
                rw [hass_i] at hnt_m1 hnt ⊢; dsimp only at hnt ⊢
                let m10 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) sk
                let bodyPost : PanSemStateFiniteExact 64 F :=
                  { m10 with
                    locals :=
                      ((((((m10.locals.resVarEq (ofString "j", m8.locals.lookup (ofString "j"))).resVarEq
                        (ofString "keys", m7.locals.lookup (ofString "keys"))).resVarEq
                        (ofString "ih", d3.locals.lookup (ofString "ih"))).resVarEq
                        (ofString "inner", d2.locals.lookup (ofString "inner"))).resVarEq
                        (ofString "ns", d1.locals.lookup (ofString "ns"))).resVarEq
                        (ofString "rec", sd.locals.lookup (ofString "rec"))) }
                have hbp_clk : bodyPost.clock ≤ k := by
                  have hd3_clk : d3.clock = s.clock - 1 := rfl
                  have hm3_c : m3.clock = m2.clock := rfl
                  have hm5_c : m5.clock = m4.clock := rfl
                  have hm9_c : m9.clock = m6.clock := rfl
                  have hbp_c : bodyPost.clock = sk.clock := rfl
                  omega
                have heff_s_bp : HeapByteEff s bodyPost Rl gw :=
                  (heff_s_m9.trans heff_m9_sk).locals_clock bodyPost.locals bodyPost.clock
                have hbp_glob : bodyPost.globals = s.globals := by
                  change sk.globals = s.globals
                  have h9 : m9.globals = m6.globals := rfl
                  have h5 : m5.globals = m4.globals := rfl
                  have h3 : m3.globals = m2.globals := rfl
                  have hd3g : d3.globals = s.globals := rfl
                  rw [hsk_glob, h9, hm6_glob, h5, hm4_glob, h3, hm2_glob, hm1_glob, hd3g]
                have hiw'_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
                  rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = iw.toNat + 1
                  exact Nat.mod_eq_of_lt (by omega)
                have hpfk_next : pfk.toNat = pstart + accessListPayloadPrefix s0 recsw.toNat (iw + 1#64).toNat := by
                  rw [hiw'_nat, hpfk_eq, hp3_nat, hnsw_nat, hpref_succ]
                  omega
                have hbp_dst : bodyPost.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsk_dst,
                    show ofString "i" ≠ ofString "dst" by decide]
                have hbp_recs : bodyPost.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsk_recs,
                    show ofString "i" ≠ ofString "recs" by decide]
                have hbp_n : bodyPost.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsk_n,
                    show ofString "i" ≠ ofString "n" by decide]
                have hbp_p : bodyPost.locals.lookup (ofString "p") = some (.val (.word pfk)) := by
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsk_p,
                    show ofString "i" ≠ ofString "p" by decide]
                have hbp_i : bodyPost.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hbp_w : ∃ ww : BitVec 64, bodyPost.locals.lookup (ofString "w") = some (.val (.word ww)) := by
                  refine ⟨wfk, ?_⟩
                  simp only [bodyPost]
                  repeat rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
                  simp [m10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsk_w,
                    show ofString "i" ≠ ofString "w" by decide]
                have hrec_ih := ih bodyPost pfk (iw + 1#64) hbp_clk (heff0.trans heff_s_bp)
                  (by omega) hpfk_next hbp_dst hbp_recs hbp_n hbp_p hbp_i hbp_w hnt
                dsimp only at hrec_ih
                refine ⟨fun hnone => ?_, hrec_ih.2⟩
                obtain ⟨pf, hpf_eq, hglob_rec, heff_rec, hfdst, hfp⟩ := hrec_ih.1 hnone
                exact ⟨pf, hpf_eq, hglob_rec.trans hbp_glob, heff_s_bp.trans heff_rec, hfdst, hfp⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩

private def txPutAccessListAfterPl : ProgHOL 64 :=
  .decCall (ofString "w") .one (ofString "rlp_encode_list_header")
    [.var .local (ofString "dst"), .var .local (ofString "pl")]
    (.dec (ofString "p") .one (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
      (.dec (ofString "i") .one (.const 0#64)
        (.seq txPutAccessListWhile
          (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))

private theorem eval_call_local_tx_put_access_list {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp recsExp nExp : ExpHOL 64)
    (dst0 recsw nw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode0 : s0.code = originalRuntimeCode) (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots : accessSlotsPrefix s0 recsw.toNat nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat) ∧
      Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat) +
        accessListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_access_list")
        [dstExp, recsExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_access_list")
        [dstExp, recsExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat) +
          accessListPayloadPrefix s0 recsw.toNat nw.toNat ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hcode : s.code = originalRuntimeCode := heff0.arena.1.code
  have hAR : ArenaReady s := heff0.arena
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, recsExp, nExp] = some [.val (.word dst0), .val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hrecs, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "tx_put_access_list")
    (ofString "dst") (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_tx_put_access_list) dst0 recsw nw
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_tx_put_access_list)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "recs", ValueHOL.val (.word recsw))).update (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have heff_s_ent : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hAR Rl gw).locals_clock ent.locals ent.clock
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "recs" ≠ ofString "dst" by decide]
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_tx_put_access_list =
        .decCall (ofString "pl") .one (ofString "access_list_payload_len")
          [.var .local (ofString "recs"), .var .local (ofString "n")]
          txPutAccessListAfterPl := rfl
    have hbody :
        let outb := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_access_list)
        (outb.1 ≠ some .timeOut) →
        (Resumes outb.1 →
          ∃ len : BitVec 64,
            outb.1 = some (.returned (.val (.word len))) ∧
            len.toNat = rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat) +
              accessListPayloadPrefix s0 recsw.toNat nw.toNat ∧
            outb.2.globals = ent.globals ∧
            HeapByteEff ent outb.2 Rl gw) := by
      intro outb hnt_b hres_b
      dsimp only [outb] at hnt_b hres_b ⊢
      rw [hb] at hnt_b hres_b ⊢
      obtain ⟨mid0, hpl_nat, _, hm0_glob, _, hm0_loc, heff_ent_m0, hnt_m0, hout_m0⟩ :=
        eval_decCall_access_list_payload_len s0 ent "pl"
          (.var .local (ofString "recs")) (.var .local (ofString "n"))
          recsw nw txPutAccessListAfterPl Rl gw hcode0 hAR0 hRl_ge (heff0.trans heff_s_ent)
          (by simp [evalHOLExact, hent_recs])
          (by simp [evalHOLExact, hent_n])
          hn_lt hslots hrecs_ok hnt_b
      rw [hout_m0] at hres_b ⊢
      dsimp only [txPutAccessListAfterPl] at hnt_m0 hres_b ⊢
      set plw := BitVec.ofNat 64 (accessListPayloadPrefix s0 recsw.toNat nw.toNat)
      have hm0_pl : mid0.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, plw]
      have hm0_dst : mid0.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
          show ofString "pl" ≠ ofString "dst" by decide]
      have hm0_recs : mid0.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_recs,
          show ofString "pl" ≠ ofString "recs" by decide]
      have hm0_n : mid0.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
          show ofString "pl" ≠ ofString "n" by decide]
      have hin_lh : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
          dst0.toNat + rlpHeaderLenPure plw.toNat ≤ ivl.1 + ivl.2 := by
        rw [hpl_nat]; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩
      obtain ⟨mid1, hhl_nat, _, _, hdst_lt_he, hm1_glob, hm1_loc, heff_m0_m1, hnt_m1, hres_m1, hout_m1⟩ :=
        WkBlockTxEnc.eval_decCall_rlp_encode_list_header mid0 "w"
          (.var .local (ofString "dst")) (.var .local (ofString "pl"))
          dst0 plw _ Rl gw heff_ent_m0.arena.1.code heff_ent_m0.arena
          (by simp [evalHOLExact, hm0_dst])
          (by simp [evalHOLExact, hm0_pl])
          hin_lh hnt_m0 hres_b
      rw [hout_m1]
      set w0 := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
      have hw0_nat : w0.toNat = rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat) := by
        have h1 : w0.toNat = rlpHeaderLenPure plw.toNat := hhl_nat
        rw [hpl_nat] at h1; exact h1
      have hm1_w : mid1.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, w0]
      have hm1_dst : mid1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hm1_recs : mid1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_recs,
          show ofString "w" ≠ ofString "recs" by decide]
      have hm1_n : mid1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_n,
          show ofString "w" ≠ ofString "n" by decide]
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_p0 : @evalHOLExact 64 F _ mid1.toExact (fun a => Classical.propDecidable (mid1.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
          some (.val (.word (dst0 + w0))) := by
        have hzw : w0 + 0 = w0 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hm1_dst, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzw]
      rw [hev_p0] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      set mid2 := setVarHOLFinite (ofString "p") (.val (.word (dst0 + w0))) mid1
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_i0 : @evalHOLExact 64 F _ mid2.toExact (fun a => Classical.propDecidable (mid2.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev_i0] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      set mid3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) mid2
      have heff_ent_m3 : HeapByteEff ent mid3 Rl gw :=
        (heff_ent_m0.trans heff_m0_m1).locals_clock mid3.locals mid3.clock
      set pstart := dst0.toNat + rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat)
      have hp0_nat : (dst0 + w0).toNat = pstart + accessListPayloadPrefix s0 recsw.toNat (0#64 : BitVec 64).toNat := by
        simp only [accessListPayloadPrefix, Nat.add_zero, pstart]
        rw [BitVec.toNat_add, hw0_nat]
        have hbnd := rlpHeaderLenPure_bounds (accessListPayloadPrefix s0 recsw.toNat nw.toNat)
        exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hdst_lt_he; omega)
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧
          pstart + accessListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 := by
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, by dsimp [pstart]; omega, h2⟩
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hres_m1 ⊢
      rcases hw_run : evaluateHOLFiniteState mid3 txPutAccessListWhile with ⟨rw_res, sw_post⟩
      have hnt_w : rw_res ≠ some .timeOut := by
        rintro rfl; simp only [hw_run] at hnt_m1; exact hnt_m1 rfl
      have hloop := eval_txPutAccessListWhile_exact mid3.clock s0 mid3 Rl gw
        dst0 recsw nw (dst0 + w0) 0#64 pstart hAR0 hRl_ge le_rfl
        ((heff0.trans heff_s_ent).trans heff_ent_m3)
        hn_lt hslots hrecs_ok (by simp) hp0_nat hin_loop
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
          show ofString "i" ≠ ofString "recs" by decide, show ofString "p" ≠ ofString "recs" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide])
        (by simp [mid3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ⟨w0, by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]⟩
        (by rw [hw_run]; exact hnt_w)
      dsimp only at hloop; rw [hw_run] at hloop
      simp only [hw_run] at hnt_m1 hres_m1 ⊢
      cases rw_res with
      | some r' =>
        exact False.elim (hloop.2 (by simp) hres_m1)
      | none =>
        dsimp only at hnt_m1 hres_m1 ⊢
        obtain ⟨pf, hpf_eq, hsw_glob, heff_w, hsw_dst, hsw_p⟩ := hloop.1 rfl
        dsimp only at hsw_glob heff_w hsw_dst hsw_p
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ sw_post.toExact (fun a => Classical.propDecidable (sw_post.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (pf - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hsw_p, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact])]
        dsimp only
        have hsub_nat : (pf - dst0).toNat =
            rlpHeaderLenPure (accessListPayloadPrefix s0 recsw.toNat nw.toNat) +
              accessListPayloadPrefix s0 recsw.toNat nw.toNat := by
          rw [BitVec.toNat_sub_of_le]
          · dsimp [pstart] at hpf_eq; omega
          · rw [BitVec.le_def]; dsimp [pstart] at hpf_eq; omega
        refine ⟨pf - dst0, rfl, hsub_nat, ?_, ?_⟩
        · change sw_post.globals = ent.globals
          have hm3g : mid3.globals = mid1.globals := rfl
          rw [hsw_glob, hm3g, hm1_glob, hm0_glob]
        · exact (((((heff_ent_m3.trans heff_w).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_access_list) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    simp only [hrun] at hnt ⊢
    cases rb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev =>
        refine ⟨fun h => by simp at h, fun _ hres_call => ?_⟩
        have hres_ent : Resumes (some (.exception eid ev)) := by
          rcases hres_call with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨_, hrb, _⟩ := hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_ent)
        simp only [hrun] at hrb; cases hrb
      | returned rv =>
        obtain ⟨len, hrb, hlen_eq, hsb_glob, heff_ent⟩ :=
          hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
        simp only [hrun] at hrb hsb_glob heff_ent
        injection hrb with hrv; injection hrv with hrv'; subst hrv'
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]; rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { sb with locals := s.locals }
        exact ⟨fun _ => ⟨len, hlen_eq, hsb_glob, rfl,
          (heff_s_ent.trans heff_ent).locals_clock mid.locals mid.clock⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## Section 15: Authorization List Encoding (`auth_payload_len`, `auth_list_payload_len`, `tx_put_authorizations`) -/

private def authPayloadPure {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s a))
    (BitVec.ofNat 64 (memW s (a + 8)))
    (BitVec.ofNat 64 (memW s (a + 16)))
    (BitVec.ofNat 64 (memW s (a + 24))) +
  21 +
  rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s (a + 40))) +
  rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s (a + 48))) +
  txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s (a + 56)))
    (BitVec.ofNat 64 (memW s (a + 64)))
    (BitVec.ofNat 64 (memW s (a + 72)))
    (BitVec.ofNat 64 (memW s (a + 80))) +
  txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s (a + 88)))
    (BitVec.ofNat 64 (memW s (a + 96)))
    (BitVec.ofNat 64 (memW s (a + 104)))
    (BitVec.ofNat 64 (memW s (a + 112)))

private theorem authPayloadPure_bounds {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    26 ≤ authPayloadPure s a ∧ authPayloadPure s a ≤ 138 := by
  unfold authPayloadPure
  have hc := u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s a)) (BitVec.ofNat 64 (memW s (a + 8)))
    (BitVec.ofNat 64 (memW s (a + 16))) (BitVec.ofNat 64 (memW s (a + 24)))
  have hn := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s (a + 40)))
  have hy := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s (a + 48)))
  have hr := u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s (a + 56))) (BitVec.ofNat 64 (memW s (a + 64)))
    (BitVec.ofNat 64 (memW s (a + 72))) (BitVec.ofNat 64 (memW s (a + 80)))
  have hs := u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s (a + 88))) (BitVec.ofNat 64 (memW s (a + 96)))
    (BitVec.ofNat 64 (memW s (a + 104))) (BitVec.ofNat 64 (memW s (a + 112)))
  have hc1 := hc.2.2.2.2.1; have hc2 := hc.2.2.2.2.2
  have hr1 := hr.2.2.2.2.1; have hr2 := hr.2.2.2.2.2
  have hs1 := hs.2.2.2.2.1; have hs2 := hs.2.2.2.2.2
  omega

private def authEntryEncodedPure {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  let pl := authPayloadPure s a
  rlpHeaderLenPure pl + pl

private theorem authEntryEncodedPure_bounds {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    27 ≤ authEntryEncodedPure s a ∧ authEntryEncodedPure s a ≤ 147 := by
  unfold authEntryEncodedPure
  dsimp only
  have hpl := authPayloadPure_bounds s a
  have hhdr := rlpHeaderLenPure_bounds (authPayloadPure s a)
  omega

private def authListPayloadPrefix {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => authListPayloadPrefix s recs k' + authEntryEncodedPure s (recs + 120 * k')

private theorem authListPayloadPrefix_le {F : Type} (s : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    authListPayloadPrefix s recs k ≤ 147 * k := by
  induction k with
  | zero => simp [authListPayloadPrefix]
  | succ k' ih =>
    rw [authListPayloadPrefix]
    have hb := authEntryEncodedPure_bounds s (recs + 120 * k')
    omega

private theorem authListPayloadPrefix_mono {F : Type} (s : PanSemStateFiniteExact 64 F) (recs : Nat)
    {j k : Nat} (hjk : j ≤ k) :
    authListPayloadPrefix s recs j ≤ authListPayloadPrefix s recs k := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => rw [authListPayloadPrefix]; omega

private def authPayloadLenStep5 : ProgHOL 64 :=
  .decCall (ofString "ls") .one (ofString "tx_u256_encoded_len")
    [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64])]
    (.return (.op .add
      [.var .local (ofString "lc"), .const 21#64, .var .local (ofString "ln"),
       .var .local (ofString "ly"), .var .local (ofString "lr"), .var .local (ofString "ls")]))

private def authPayloadLenStep4 : ProgHOL 64 :=
  .decCall (ofString "lr") .one (ofString "tx_u256_encoded_len")
    [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64])]
    authPayloadLenStep5

private def authPayloadLenStep3 : ProgHOL 64 :=
  .decCall (ofString "ly") .one (ofString "rlp_word_encoded_len")
    [.load .one (.op .add [.var .local (ofString "a"), .const 48#64])]
    authPayloadLenStep4

private def authPayloadLenStep2 : ProgHOL 64 :=
  .decCall (ofString "ln") .one (ofString "rlp_word_encoded_len")
    [.load .one (.op .add [.var .local (ofString "a"), .const 40#64])]
    authPayloadLenStep3

private theorem eval_decCall_auth_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (aExp : ExpHOL 64)
    (aw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (heff0 : HeapByteEff s0 s Rl gw)
    (ha_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) aExp =
      some (.val (.word aw)))
    (hrec_iv : ∃ iv : Ivl, WordsOK s0 iv ∧ Inside iv sourceBase (globN s0 "heap_ptr") ∧
      iv.1 ≤ aw.toNat ∧ aw.toNat + 120 ≤ iv.1 + iv.2 ∧ (aw.toNat - iv.1) % 8 = 0)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "auth_payload_len") [aExp] cont)).1 ≠
      some .timeOut) :
    let pl := BitVec.ofNat 64 (authPayloadPure s0 aw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      pl.toNat = authPayloadPure s0 aw.toNat ∧
      26 ≤ pl.toNat ∧ pl.toNat ≤ 138 ∧
      mid.clock ≤ s.clock ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word pl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "auth_payload_len") [aExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro pl
  obtain ⟨iv, hwok, hin_iv, ha_lo, ha_hi, ha_mod⟩ := hrec_iv
  have hfit_iv : iv.1 + iv.2 ≤ 2 ^ 64 := inside_fit_u64 hin_iv hAR0.2.2.1
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hwa_off : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 120 → WordAt s0 (aw.toNat + off) := by
    intro off hoff_mod hoff_le
    set k := (aw.toNat - iv.1 + off) / 8
    have heq : iv.1 + 8 * k = aw.toNat + off := by omega
    rw [← heq]
    exact wordAt_of_wordsOK hwok k (by omega)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [aExp] =
      some [.val (.word aw)] := by simp [evalListHOLFinite, evalListHOLExact, ha_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "auth_payload_len") (ofString "a")
    (sourceFnBody Guest.Software.guestFn_auth_payload_len) aw
    (by rw [heff0.arena.1.code]; exact lookup_auth_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word aw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_a : ent.locals.lookup (ofString "a") = some (.val (.word aw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_auth_payload_len =
        .decCall (ofString "lc") .one (ofString "tx_u256_encoded_len")
          [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64])]
          authPayloadLenStep2 := rfl
    have hbody : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).1 ≠ some .timeOut →
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).1 =
          some (.returned (.val (.word pl))) ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2.globals = s.globals ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2.memory = s.memory ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2.clock ≤ s.clock ∧
        HeapByteEff s (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2 Rl gw := by
      intro hnt_b
      have hclk_b := evaluateHOLFiniteState_clock_le ent (sourceFnBody Guest.Software.guestFn_auth_payload_len)
      have heff_s_ent : HeapByteEff s ent Rl gw :=
        (HeapByteEff.refl heff0.arena Rl gw).locals_clock ent.locals ent.clock
      rw [hb] at hnt_b hclk_b ⊢
      -- Step 1: lc = tx_u256_encoded_len(load u256 (a + 0))
      have hev_a0 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 0#64]) = some (.val (.word aw)) := by
        have h0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
        have haw0 : aw + 0#64 = aw := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hent_a, wordOpHOL, wordOp, valueIsWord, valueWord, h0, haw0]
      have hload_c := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs (heff0.trans heff_s_ent) hRl_ge hin_iv
        (.op .add [.var .local (ofString "a"), .const 0#64]) aw hev_a0
        (by simpa using hwa_off 0 (by omega) (by omega))
        (hwa_off 8 (by omega) (by omega))
        (hwa_off 16 (by omega) (by omega))
        (hwa_off 24 (by omega) (by omega))
        ha_lo (by omega)
      obtain ⟨e1, hlf_1, he1_loc, hnt_1, hdc_1⟩ :=
        eval_decCall_tx_u256_encoded_len ent "lc"
          (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64]))
          (BitVec.ofNat 64 (memW s0 aw.toNat))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 16)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))
          authPayloadLenStep2 heff0.arena.1.code hload_c hnt_b
      rw [hdc_1] at hclk_b ⊢
      dsimp only [authPayloadLenStep2] at hnt_1 hclk_b ⊢
      have heff_ent_e1 : HeapByteEff ent e1 Rl gw := HeapByteEff.of_locFrame heff_s_ent.arena hlf_1 Rl gw
      have he1_a : e1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [he1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_a,
          show ofString "lc" ≠ ofString "a" by decide]
      -- Step 2: ln = rlp_word_encoded_len(load u64 (a + 40))
      have haw40_nat : (aw + 40#64).toNat = aw.toNat + 40 := by
        rw [BitVec.toNat_add]; change (aw.toNat + 40) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hev_a40 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 40#64]) = some (.val (.word (aw + 40#64))) := by
        have h40 : (40#64 : BitVec 64) + 0 = 40#64 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, he1_a, wordOpHOL, wordOp, valueIsWord, valueWord, h40]
      have hload_n := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs ((heff0.trans heff_s_ent).trans heff_ent_e1)
        hRl_ge hin_iv (.op .add [.var .local (ofString "a"), .const 40#64]) (aw + 40#64) hev_a40
        (by rw [haw40_nat]; exact hwa_off 40 (by omega) (by omega))
        (by rw [haw40_nat]; omega) (by rw [haw40_nat]; omega)
      rw [haw40_nat] at hload_n
      obtain ⟨e2, hln_nat, _, _, he2_glob, he2_mem, he2_loc, heff_e1_e2, hnt_2, hdc_2⟩ :=
        eval_decCall_rlp_word_encoded_len e1 "ln"
          (.load .one (.op .add [.var .local (ofString "a"), .const 40#64]))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 40)))
          authPayloadLenStep3 Rl gw heff_ent_e1.arena.1.code heff_ent_e1.arena hload_n hnt_1
      rw [hdc_2] at hclk_b ⊢
      dsimp only [authPayloadLenStep3] at hnt_2 hclk_b ⊢
      have he2_a : e2.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [he2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, he1_a,
          show ofString "ln" ≠ ofString "a" by decide]
      -- Step 3: ly = rlp_word_encoded_len(load u64 (a + 48))
      have haw48_nat : (aw + 48#64).toNat = aw.toNat + 48 := by
        rw [BitVec.toNat_add]; change (aw.toNat + 48) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hev_a48 : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 48#64]) = some (.val (.word (aw + 48#64))) := by
        have h48 : (48#64 : BitVec 64) + 0 = 48#64 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, he2_a, wordOpHOL, wordOp, valueIsWord, valueWord, h48]
      have hload_y := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs
        (((heff0.trans heff_s_ent).trans heff_ent_e1).trans heff_e1_e2)
        hRl_ge hin_iv (.op .add [.var .local (ofString "a"), .const 48#64]) (aw + 48#64) hev_a48
        (by rw [haw48_nat]; exact hwa_off 48 (by omega) (by omega))
        (by rw [haw48_nat]; omega) (by rw [haw48_nat]; omega)
      rw [haw48_nat] at hload_y
      obtain ⟨e3, hly_nat, _, _, he3_glob, he3_mem, he3_loc, heff_e2_e3, hnt_3, hdc_3⟩ :=
        eval_decCall_rlp_word_encoded_len e2 "ly"
          (.load .one (.op .add [.var .local (ofString "a"), .const 48#64]))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 48)))
          authPayloadLenStep4 Rl gw heff_e1_e2.arena.1.code heff_e1_e2.arena hload_y hnt_2
      rw [hdc_3] at hclk_b ⊢
      dsimp only [authPayloadLenStep4] at hnt_3 hclk_b ⊢
      have he3_a : e3.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [he3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, he2_a,
          show ofString "ly" ≠ ofString "a" by decide]
      -- Step 4: lr = tx_u256_encoded_len(load u256 (a + 56))
      have haw56_nat : (aw + 56#64).toNat = aw.toNat + 56 := by
        rw [BitVec.toNat_add]; change (aw.toNat + 56) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hev_a56 : @evalHOLExact 64 F _ e3.toExact (fun a => Classical.propDecidable (e3.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 56#64]) = some (.val (.word (aw + 56#64))) := by
        have h56 : (56#64 : BitVec 64) + 0 = 56#64 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, he3_a, wordOpHOL, wordOp, valueIsWord, valueWord, h56]
      have hload_r := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs
        ((((heff0.trans heff_s_ent).trans heff_ent_e1).trans heff_e1_e2).trans heff_e2_e3)
        hRl_ge hin_iv (.op .add [.var .local (ofString "a"), .const 56#64]) (aw + 56#64) hev_a56
        (by rw [haw56_nat]; exact hwa_off 56 (by omega) (by omega))
        (by rw [haw56_nat]; exact hwa_off 64 (by omega) (by omega))
        (by rw [haw56_nat]; exact hwa_off 72 (by omega) (by omega))
        (by rw [haw56_nat]; exact hwa_off 80 (by omega) (by omega))
        (by rw [haw56_nat]; omega) (by rw [haw56_nat]; omega)
      simp only [haw56_nat, Nat.add_assoc] at hload_r
      obtain ⟨e4, hlf_4, he4_loc, hnt_4, hdc_4⟩ :=
        eval_decCall_tx_u256_encoded_len e3 "lr"
          (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64]))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 56)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 72)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
          authPayloadLenStep5 heff_e2_e3.arena.1.code hload_r hnt_3
      rw [hdc_4] at hclk_b ⊢
      dsimp only [authPayloadLenStep5] at hnt_4 hclk_b ⊢
      have heff_e3_e4 : HeapByteEff e3 e4 Rl gw := HeapByteEff.of_locFrame heff_e2_e3.arena hlf_4 Rl gw
      have he4_a : e4.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [he4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, he3_a,
          show ofString "lr" ≠ ofString "a" by decide]
      -- Step 5: ls = tx_u256_encoded_len(load u256 (a + 88))
      have haw88_nat : (aw + 88#64).toNat = aw.toNat + 88 := by
        rw [BitVec.toNat_add]; change (aw.toNat + 88) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hev_a88 : @evalHOLExact 64 F _ e4.toExact (fun a => Classical.propDecidable (e4.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 88#64]) = some (.val (.word (aw + 88#64))) := by
        have h88 : (88#64 : BitVec 64) + 0 = 88#64 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, he4_a, wordOpHOL, wordOp, valueIsWord, valueWord, h88]
      have hload_s := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs
        (((((heff0.trans heff_s_ent).trans heff_ent_e1).trans heff_e1_e2).trans heff_e2_e3).trans heff_e3_e4)
        hRl_ge hin_iv (.op .add [.var .local (ofString "a"), .const 88#64]) (aw + 88#64) hev_a88
        (by rw [haw88_nat]; exact hwa_off 88 (by omega) (by omega))
        (by rw [haw88_nat]; exact hwa_off 96 (by omega) (by omega))
        (by rw [haw88_nat]; exact hwa_off 104 (by omega) (by omega))
        (by rw [haw88_nat]; exact hwa_off 112 (by omega) (by omega))
        (by rw [haw88_nat]; omega) (by rw [haw88_nat]; omega)
      simp only [haw88_nat, Nat.add_assoc] at hload_s
      obtain ⟨e5, hlf_5, he5_loc, hnt_5, hdc_5⟩ :=
        eval_decCall_tx_u256_encoded_len e4 "ls"
          (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64]))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 88)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 104)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
          _ heff_e3_e4.arena.1.code hload_s hnt_4
      rw [hdc_5] at hclk_b ⊢
      have heff_e4_e5 : HeapByteEff e4 e5 Rl gw := HeapByteEff.of_locFrame heff_e3_e4.arena hlf_5 Rl gw
      set lcw := BitVec.ofNat 64 (txU256EncodedLenPure
        (BitVec.ofNat 64 (memW s0 aw.toNat))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 16)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 24))))
      set lnw := BitVec.ofNat 64 (rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 40))))
      set lyw := BitVec.ofNat 64 (rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 48))))
      set lrw := BitVec.ofNat 64 (txU256EncodedLenPure
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 56)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 72)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 80))))
      set lsw := BitVec.ofNat 64 (txU256EncodedLenPure
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 88)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 104)))
        (BitVec.ofNat 64 (memW s0 (aw.toNat + 112))))
      have he5_ls : e5.locals.lookup (ofString "ls") = some (.val (.word lsw)) := by
        rw [he5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lsw]
      have he5_lr : e5.locals.lookup (ofString "lr") = some (.val (.word lrw)) := by
        rw [he5_loc, he4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lrw,
          show ofString "ls" ≠ ofString "lr" by decide]
      have he5_ly : e5.locals.lookup (ofString "ly") = some (.val (.word lyw)) := by
        rw [he5_loc, he4_loc, he3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lyw,
          show ofString "ls" ≠ ofString "ly" by decide, show ofString "lr" ≠ ofString "ly" by decide]
      have he5_ln : e5.locals.lookup (ofString "ln") = some (.val (.word lnw)) := by
        rw [he5_loc, he4_loc, he3_loc, he2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lnw,
          show ofString "ls" ≠ ofString "ln" by decide, show ofString "lr" ≠ ofString "ln" by decide,
          show ofString "ly" ≠ ofString "ln" by decide]
      have he5_lc : e5.locals.lookup (ofString "lc") = some (.val (.word lcw)) := by
        rw [he5_loc, he4_loc, he3_loc, he2_loc, he1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lcw,
          show ofString "ls" ≠ ofString "lc" by decide, show ofString "lr" ≠ ofString "lc" by decide,
          show ofString "ly" ≠ ofString "lc" by decide, show ofString "ln" ≠ ofString "lc" by decide]
      rw [evaluateHOLFiniteState_return] at hclk_b ⊢
      have hev_ret : @evalHOLExact 64 F _ e5.toExact (fun a => Classical.propDecidable (e5.memaddrs a))
          (.op .add [.var .local (ofString "lc"), .const 21#64, .var .local (ofString "ln"),
            .var .local (ofString "ly"), .var .local (ofString "lr"), .var .local (ofString "ls")]) =
          some (.val (.word (lcw + (21#64 + (lnw + (lyw + (lrw + lsw))))))) := by
        have hzls : lsw + 0 = lsw := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, he5_lc, he5_ln, he5_ly, he5_lr, he5_ls,
          wordOpHOL, wordOp, valueIsWord, valueWord, hzls]
      have hsum_eq : lcw + (21#64 + (lnw + (lyw + (lrw + lsw)))) = pl := by
        apply BitVec.eq_of_toNat_eq
        have hc_b := (u256ByteLengthPure_bounds
          (BitVec.ofNat 64 (memW s0 aw.toNat)) (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 16))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))).2.2.2.2.2
        have hr_b := (u256ByteLengthPure_bounds
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))).2.2.2.2.2
        have hs_b := (u256ByteLengthPure_bounds
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))).2.2.2.2.2
        have hlc_nat : lcw.toNat = txU256EncodedLenPure
            (BitVec.ofNat 64 (memW s0 aw.toNat)) (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
            (BitVec.ofNat 64 (memW s0 (aw.toNat + 16))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 24))) := by
          dsimp [lcw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hlr_nat : lrw.toNat = txU256EncodedLenPure
            (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
            (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80))) := by
          dsimp [lrw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hls_nat : lsw.toNat = txU256EncodedLenPure
            (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
            (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112))) := by
          dsimp [lsw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hn_b := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s0 (aw.toNat + 40)))
        have hy_b := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s0 (aw.toNat + 48)))
        have hln_nat' : lnw.toNat = rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 40))) := hln_nat
        have hly_nat' : lyw.toNat = rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 48))) := hly_nat
        have hpl_b := authPayloadPure_bounds s0 aw.toNat
        have hpl_nat : pl.toNat = authPayloadPure s0 aw.toNat := by
          dsimp [pl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        rw [hpl_nat]
        unfold authPayloadPure
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
        simp only [hlc_nat, hln_nat', hly_nat', hlr_nat, hls_nat, show (21#64 : BitVec 64).toNat = 21 from rfl]
        omega
      rw [hev_ret, hsum_eq] at hclk_b ⊢; dsimp only at hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact])] at hclk_b ⊢
      dsimp only at hclk_b ⊢
      have hclk_le : e5.clock ≤ s.clock := by
        change e5.clock ≤ s.clock - 1 at hclk_b; omega
      have he5_glob : e5.globals = s.globals := by
        rw [hlf_5.globals, hlf_4.globals, he3_glob, he2_glob, hlf_1.globals]; rfl
      have he5_mem : e5.memory = s.memory := by
        rw [hlf_5.memory, hlf_4.memory, he3_mem, he2_mem, hlf_1.memory]; rfl
      have heff_all : HeapByteEff s e5 Rl gw :=
        ((((heff_s_ent.trans heff_ent_e1).trans heff_e1_e2).trans heff_e2_e3).trans heff_e3_e4).trans heff_e4_e5
      exact ⟨rfl, he5_glob, he5_mem, hclk_le,
        ((((((heff_all.locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _)⟩
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_payload_len) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    obtain ⟨hrb, hsb_glob, hsb_mem, hsb_clk, heff_sb⟩ := hbody (by rw [hrun]; exact hnt_b)
    rw [hrun] at hrb hsb_glob hsb_mem hsb_clk heff_sb
    dsimp only at hrb hsb_glob hsb_mem hsb_clk heff_sb
    subst hrb
    simp only [hrun] at hnt ⊢
    have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh2] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word pl)) { sb.emptyLocalsHOLFinite with locals := s.locals }
    have hpl_b := authPayloadPure_bounds s0 aw.toNat
    have hpl_nat : pl.toNat = authPayloadPure s0 aw.toNat := by
      dsimp [pl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hpl_nat, by omega, by omega, hsb_clk, hsb_glob, hsb_mem, rfl,
      heff_sb.locals_clock mid.locals mid.clock, hnt, rfl⟩

private def authListPayloadLenAfterPl : ProgHOL 64 :=
  .decCall (ofString "h") .one (ofString "rlp_list_header_len") [.var .local (ofString "pl")]
    (.seq
      (.assign .local (ofString "total")
        (.op .add [.var .local (ofString "total"), .var .local (ofString "h"), .var .local (ofString "pl")]))
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1#64])))

private def authListPayloadLenLoopBody : ProgHOL 64 :=
  .decCall (ofString "pl") .one (ofString "auth_payload_len")
    [.op .add [.var .local (ofString "recs"),
      .panop .mul [.var .local (ofString "i"), .const 120#64]]]
    authListPayloadLenAfterPl

private def authListPayloadLenWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    authListPayloadLenLoopBody

private theorem eval_authListPayloadLenWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (recsw nw totalw iw : BitVec 64)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat) ∧
      Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hi_le : iw.toNat ≤ nw.toNat)
    (htot_eq : totalw.toNat = authListPayloadPrefix s0 recsw.toNat iw.toNat)
    (hl_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_total : s.locals.lookup (ofString "total") = some (.val (.word totalw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hnt : (evaluateHOLFiniteState s authListPayloadLenWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s authListPayloadLenWhile
    out.1 = none ∧
    out.2.globals = s.globals ∧
    out.2.memory = s.memory ∧
    HeapByteEff s out.2 Rl gw ∧
    out.2.locals.lookup (ofString "total") =
      some (.val (.word (BitVec.ofNat 64 (authListPayloadPrefix s0 recsw.toNat nw.toNat)))) := by
  induction clk generalizing s totalw iw with
  | zero =>
    intro out; dsimp only [out, authListPayloadLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      have hbw : BitVec.ofNat 64 (authListPayloadPrefix s0 recsw.toNat nw.toNat) = totalw := by
        rw [← hieq, ← htot_eq]; simp
      rw [hbw]
      exact ⟨rfl, rfl, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_total⟩
  | succ k ih =>
    intro out; dsimp only [out, authListPayloadLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        have ⟨hwok, hin_recs⟩ := hrecs_ok (by omega)
        have hfit_recs : recsw.toNat + 120 * nw.toNat ≤ 2 ^ 64 :=
          inside_fit_u64 hin_recs hAR0.2.2.1
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
        set aw := recsw + iw * 120#64
        have haw_nat : aw.toNat = recsw.toNat + 120 * iw.toNat := by
          have hi120 : (iw * 120#64).toNat = 120 * iw.toNat := by
            rw [BitVec.toNat_mul]; change (iw.toNat * 120) % 2 ^ 64 = 120 * iw.toNat
            rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
          rw [show aw = recsw + iw * 120#64 from rfl, BitVec.toNat_add, hi120]
          exact Nat.mod_eq_of_lt (by omega)
        have hev_aw : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "recs"),
              .panop .mul [.var .local (ofString "i"), .const 120#64]]) =
            some (.val (.word aw)) := by
          have h0 : (iw * 120#64) + 0 = iw * 120#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_recs, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, h0, aw]
        have hnt_sd : (evaluateHOLFiniteState sd authListPayloadLenLoopBody).1 ≠ some .timeOut := by
          intro hto; rw [hto] at hnt; exact hnt rfl
        dsimp only [authListPayloadLenLoopBody] at hnt_sd hnt ⊢
        have hrec_iv : ∃ iv : Ivl, WordsOK s0 iv ∧ Inside iv sourceBase (globN s0 "heap_ptr") ∧
            iv.1 ≤ aw.toNat ∧ aw.toNat + 120 ≤ iv.1 + iv.2 ∧ (aw.toNat - iv.1) % 8 = 0 := by
          refine ⟨(recsw.toNat, 120 * nw.toNat), hwok, hin_recs, ?_, ?_, ?_⟩
          · dsimp only; rw [haw_nat]; omega
          · dsimp only; rw [haw_nat]; omega
          · dsimp only; rw [haw_nat]; omega
        obtain ⟨m1, hpl_nat, hpl_ge, hpl_le, hc1, hm1_glob, hm1_mem, hm1_loc, heff_sd_m1, hnt_m1, hout_m1⟩ :=
          eval_decCall_auth_payload_len s0 sd "pl"
            (.op .add [.var .local (ofString "recs"),
              .panop .mul [.var .local (ofString "i"), .const 120#64]])
            aw authListPayloadLenAfterPl Rl gw hAR0 hRl_ge heff0_sd hev_aw hrec_iv hnt_sd
        rw [hout_m1] at hnt ⊢; dsimp only [authListPayloadLenAfterPl] at hnt_m1 hnt ⊢
        set plw := BitVec.ofNat 64 (authPayloadPure s0 aw.toNat)
        have hm1_pl : m1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
          rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, plw]
        obtain ⟨m2, hh_nat, hh_ge, hh_le, hc2, hm2_glob, hm2_mem, hm2_loc, heff_m1_m2, hnt_m2, hout_m2⟩ :=
          eval_decCall_rlp_list_header_len_clk m1 "h" (.var .local (ofString "pl")) plw _ Rl gw
            heff_sd_m1.arena.1.code heff_sd_m1.arena
            (by simp [evalHOLExact, hm1_pl]) hnt_m1
        rw [hout_m2] at hnt ⊢; dsimp only at hnt ⊢
        set hw := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
        have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word hw)) := by
          rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hw]
        have hm2_pl : m2.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
          rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_pl,
            show ofString "h" ≠ ofString "pl" by decide]
        have hm2_total : m2.locals.lookup (ofString "total") = some (.val (.word totalw)) := by
          rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show sd.locals = s.locals from rfl, hl_total,
            show ofString "h" ≠ ofString "total" by decide,
            show ofString "pl" ≠ ofString "total" by decide]
        have hm2_i : m2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show sd.locals = s.locals from rfl, hl_i,
            show ofString "h" ≠ ofString "i" by decide,
            show ofString "pl" ≠ ofString "i" by decide]
        have hm2_recs : m2.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show sd.locals = s.locals from rfl, hl_recs,
            show ofString "h" ≠ ofString "recs" by decide,
            show ofString "pl" ≠ ofString "recs" by decide]
        have hm2_n : m2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          rw [hm2_loc, hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show sd.locals = s.locals from rfl, hl_n,
            show ofString "h" ≠ ofString "n" by decide,
            show ofString "pl" ≠ ofString "n" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m2 hnt ⊢
        set totalw' := totalw + (hw + plw)
        have hass_tot : evaluateHOLFiniteState m2
            (.assign .local (ofString "total")
              (.op .add [.var .local (ofString "total"), .var .local (ofString "h"), .var .local (ofString "pl")])) =
            (none, setVarHOLFinite (ofString "total") (.val (.word totalw')) m2) := by
          rw [evaluateHOLFiniteState_assign]
          have hev_t : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
              (.op .add [.var .local (ofString "total"), .var .local (ofString "h"), .var .local (ofString "pl")]) =
              some (.val (.word totalw')) := by
            have hzp : plw + 0 = plw := BitVec.add_zero _
            simp [evalHOLExact, evalListHOLExact, hm2_total, hm2_h, hm2_pl,
              wordOpHOL, wordOp, valueIsWord, valueWord, hzp, totalw']
          rw [hev_t]; dsimp only
          rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm2_total, shapeOfHOLExact, shapeEqHOL])]
          rfl
        rw [hass_tot] at hnt_m2 hnt ⊢; dsimp only at hnt_m2 hnt ⊢
        set m3 := setVarHOLFinite (ofString "total") (.val (.word totalw')) m2
        have hm3_i : m3.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_i,
            show ofString "total" ≠ ofString "i" by decide]
        have hass_i : evaluateHOLFiniteState m3
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m3) := by
          rw [evaluateHOLFiniteState_assign]
          have hev_iw : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) =
              some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hm3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_iw]; dsimp only
          rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm3_i, shapeOfHOLExact, shapeEqHOL])]
          rfl
        rw [hass_i] at hnt_m2 hnt ⊢; dsimp only at hnt ⊢
        let m4 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m3
        let bodyPost : PanSemStateFiniteExact 64 F :=
          { m4 with
            locals :=
              ((m4.locals.resVarEq (ofString "h", m1.locals.lookup (ofString "h"))).resVarEq
                (ofString "pl", sd.locals.lookup (ofString "pl"))) }
        have hbp_clk : bodyPost.clock ≤ k := by
          have hsd_clk : sd.clock = s.clock - 1 := rfl
          have hbp_c : bodyPost.clock = m2.clock := rfl
          omega
        have heff_s_bp : HeapByteEff s bodyPost Rl gw :=
          ((heff_sd.trans heff_sd_m1).trans heff_m1_m2).locals_clock bodyPost.locals bodyPost.clock
        have hiw'_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = iw.toNat + 1
          exact Nat.mod_eq_of_lt (by omega)
        have htot'_nat : totalw'.toNat = authListPayloadPrefix s0 recsw.toNat (iw + 1#64).toNat := by
          rw [hiw'_nat, authListPayloadPrefix]
          have hpref_le := authListPayloadPrefix_le s0 recsw.toNat iw.toNat
          have hhpl_nat : (hw + plw).toNat = authEntryEncodedPure s0 (recsw.toNat + 120 * iw.toNat) := by
            rw [BitVec.toNat_add, hh_nat, hpl_nat, haw_nat]
            unfold authEntryEncodedPure; dsimp only
            have hb_pl := authPayloadPure_bounds s0 (recsw.toNat + 120 * iw.toNat)
            have hb_hdr := rlpHeaderLenPure_bounds (authPayloadPure s0 (recsw.toNat + 120 * iw.toNat))
            exact Nat.mod_eq_of_lt (by omega)
          rw [show totalw' = totalw + (hw + plw) from rfl, BitVec.toNat_add, htot_eq, hhpl_nat]
          have hb_ent := authEntryEncodedPure_bounds s0 (recsw.toNat + 120 * iw.toNat)
          exact Nat.mod_eq_of_lt (by omega)
        have hbp_recs : bodyPost.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_recs,
            show ofString "i" ≠ ofString "recs" by decide,
            show ofString "total" ≠ ofString "recs" by decide]
        have hbp_n : bodyPost.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_n,
            show ofString "i" ≠ ofString "n" by decide,
            show ofString "total" ≠ ofString "n" by decide]
        have hbp_total : bodyPost.locals.lookup (ofString "total") = some (.val (.word totalw')) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "total" by decide]
        have hbp_i : bodyPost.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
          simp only [bodyPost]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
          simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hbp_glob : bodyPost.globals = s.globals := hm2_glob.trans hm1_glob
        have hbp_mem : bodyPost.memory = s.memory := hm2_mem.trans hm1_mem
        have hrec := ih bodyPost totalw' (iw + 1#64) hbp_clk (heff0.trans heff_s_bp)
          (by omega) htot'_nat hbp_recs hbp_n hbp_total hbp_i hnt
        dsimp only at hrec
        exact ⟨hrec.1, hrec.2.1.trans hbp_glob, hrec.2.2.1.trans hbp_mem,
          heff_s_bp.trans hrec.2.2.2.1, hrec.2.2.2.2⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      have hbw : BitVec.ofNat 64 (authListPayloadPrefix s0 recsw.toNat nw.toNat) = totalw := by
        rw [← hieq, ← htot_eq]; simp
      rw [hbw]
      exact ⟨rfl, rfl, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_total⟩

private theorem eval_decCall_auth_list_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (recsExp nExp : ExpHOL 64)
    (recsw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat) ∧
      Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "auth_list_payload_len") [recsExp, nExp] cont)).1 ≠
      some .timeOut) :
    let pl := BitVec.ofNat 64 (authListPayloadPrefix s0 recsw.toNat nw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      pl.toNat = authListPayloadPrefix s0 recsw.toNat nw.toNat ∧
      mid.clock ≤ s.clock ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word pl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "auth_list_payload_len") [recsExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro pl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [recsExp, nExp] =
      some [.val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hrecs, hn]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "auth_list_payload_len")
    (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_auth_list_payload_len) recsw nw
    (by decide) (by rw [heff0.arena.1.code]; exact lookup_auth_list_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "recs", ValueHOL.val (.word recsw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hb : sourceFnBody Guest.Software.guestFn_auth_list_payload_len =
        .dec (ofString "total") .one (.const 0#64)
          (.dec (ofString "i") .one (.const 0#64)
            (.seq authListPayloadLenWhile (.return (.var .local (ofString "total"))))) := rfl
    have hbody : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).1 ≠ some .timeOut →
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).1 =
          some (.returned (.val (.word pl))) ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2.globals = s.globals ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2.memory = s.memory ∧
        (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2.clock ≤ s.clock ∧
        HeapByteEff s (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2 Rl gw := by
      intro hnt_b
      have hclk_b := evaluateHOLFiniteState_clock_le ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)
      rw [hb] at hnt_b hclk_b ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      have hev0_t : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev0_t] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      set e1 := setVarHOLFinite (ofString "total") (.val (.word 0#64)) ent
      rw [evaluateHOLFiniteState_dec_total] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      have hev0_i : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev0_i] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_b hclk_b ⊢; dsimp only at hnt_b hclk_b ⊢
      set e2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e1
      have heff_s_e2 : HeapByteEff s e2 Rl gw :=
        (HeapByteEff.refl heff0.arena Rl gw).locals_clock e2.locals e2.clock
      rw [evaluateHOLFiniteState_seq_line780] at hnt_b hclk_b ⊢
      rcases hw : evaluateHOLFiniteState e2 authListPayloadLenWhile with ⟨rw_res, sw⟩
      have hnt_w : rw_res ≠ some .timeOut := by
        rintro rfl; simp only [hw] at hnt_b; exact hnt_b rfl
      have hloop := eval_authListPayloadLenWhile_exact e2.clock s0 e2 Rl gw recsw nw 0#64 0#64
        hAR0 hRl_ge le_rfl (heff0.trans heff_s_e2) hn_lt hrecs_ok (by simp) (by simp [authListPayloadPrefix])
        (by simp [e2, e1, ent, cmap, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "recs" by decide,
          show ofString "total" ≠ ofString "recs" by decide,
          show ofString "n" ≠ ofString "recs" by decide])
        (by simp [e2, e1, ent, cmap, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide,
          show ofString "total" ≠ ofString "n" by decide])
        (by simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "total" by decide])
        (by simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [hw]; exact hnt_w)
      dsimp only at hloop; rw [hw] at hloop
      obtain ⟨rfl, hsw_glob, hsw_mem, heff_w, hsw_tot⟩ := hloop
      dsimp only at hsw_glob hsw_mem heff_w hsw_tot
      simp only [hw] at hclk_b ⊢
      rw [evaluateHOLFiniteState_return] at hclk_b ⊢
      have hev_ret : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
          (.var .local (ofString "total")) = some (.val (.word pl)) := by
        simp [evalHOLExact, hsw_tot, pl]
      rw [hev_ret] at hclk_b ⊢; dsimp only at hclk_b ⊢
      rw [if_pos (by simp [shapeOfHOLExact])] at hclk_b ⊢
      dsimp only at hclk_b ⊢
      have hclk_le : sw.clock ≤ s.clock := by
        change sw.clock ≤ s.clock - 1 at hclk_b; omega
      exact ⟨rfl, hsw_glob, hsw_mem, hclk_le,
        (((heff_s_e2.trans heff_w).locals_clock _ _).locals_clock _ _).locals_clock _ _⟩
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_auth_list_payload_len) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    obtain ⟨hrb, hsb_glob, hsb_mem, hsb_clk, heff_sb⟩ := hbody (by rw [hrun]; exact hnt_b)
    rw [hrun] at hrb hsb_glob hsb_mem hsb_clk heff_sb
    dsimp only at hrb hsb_glob hsb_mem hsb_clk heff_sb
    subst hrb
    simp only [hrun] at hnt ⊢
    have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh2] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word pl)) { sb.emptyLocalsHOLFinite with locals := s.locals }
    have hpl_nat : pl.toNat = authListPayloadPrefix s0 recsw.toNat nw.toNat := by
      dsimp [pl]; rw [BitVec.toNat_ofNat]
      have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
      have hle := authListPayloadPrefix_le s0 recsw.toNat nw.toNat
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hpl_nat, hsb_clk, hsb_glob, hsb_mem, rfl,
      heff_sb.locals_clock mid.locals mid.clock, hnt, rfl⟩

private theorem eval_call_local_advance_pw {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (pw : BitVec 64) (pcur stepLen : Nat) (Rl : List Ivl) (gw : List String)
    (cont : ProgHOL 64)
    (hp_eq : pw.toNat = pcur)
    (hstep_fit : pcur + stepLen ≤ heapLimit)
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hcall :
      let outc := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) fname args)
      outc.1 ≠ some .timeOut →
      (outc.1 = none →
        ∃ len : BitVec 64,
          len.toNat = stepLen ∧
          outc.2.globals = s.globals ∧
          outc.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s outc.2 Rl gw) ∧
      (outc.1 ≠ none → ¬ Resumes outc.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) fname args)
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) fname args)
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))
    ((out.1 ≠ none ∧ out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1)) ∨
    ∃ (m : PanSemStateFiniteExact 64 F) (p' w' : BitVec 64),
      out = evaluateHOLFiniteState m cont ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      p'.toNat = pcur + stepLen ∧
      w'.toNat = stepLen ∧
      m.clock ≤ s.clock ∧
      m.globals = s.globals ∧
      m.locals = (s.locals.update (ofString "w", .val (.word w'))).update (ofString "p", .val (.word p')) ∧
      HeapByteEff s m Rl gw := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hrun : evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString "w"), none)) fname args) with ⟨rc, sc⟩
  have hclk_c := evaluateHOLFiniteState_clock_le s
    (.call (some (some (VarKind.local, ofString "w"), none)) fname args)
  have hnbc := call_noexc_ne_break_continue s (some (VarKind.local, ofString "w")) fname args
  dsimp only at hcall
  rw [hrun] at hcall hclk_c hnbc
  simp only [hrun] at hnt ⊢
  have hnt_rc : rc ≠ some .timeOut := by
    rintro rfl; exact hnt rfl
  have hcall' := hcall hnt_rc
  cases rc with
  | some r =>
    left
    have hnr := hcall'.2 (by simp)
    cases r with
    | timeOut => exact absurd rfl hnt
    | «break» => exact absurd rfl hnbc.1
    | «continue» => exact absurd rfl hnbc.2
    | _ => dsimp only; exact ⟨by simp, by simp, by simp, hnr⟩
  | none =>
    right
    dsimp only at hnt ⊢
    obtain ⟨w', hw'_nat, hsc_glob, hsc_loc, heff_sc⟩ := hcall'.1 rfl
    dsimp only at hsc_glob hsc_loc heff_sc hclk_c
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w')) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word (pw + w'))) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
          some (.val (.word (pw + w'))) := by
        have hzw : w' + 0 = w' := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzw]
      rw [hev]; dsimp only
      rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL])]
      rfl
    rw [hass] at hnt ⊢; dsimp only at hnt ⊢
    let m := setVarHOLFinite (ofString "p") (.val (.word (pw + w'))) sc
    have hp'_nat : (pw + w').toNat = pcur + stepLen := by
      rw [BitVec.toNat_add, hp_eq, hw'_nat]
      rw [WkBlockTxEnc.heapLimit_val] at hstep_fit
      exact Nat.mod_eq_of_lt (by omega)
    have hm_loc : m.locals = (s.locals.update (ofString "w", .val (.word w'))).update (ofString "p", .val (.word (pw + w'))) := by
      simp [m, setVarHOLFinite, hsc_loc]
    exact ⟨m, pw + w', w', rfl, hnt, hp'_nat, hw'_nat, hclk_c, hsc_glob, hm_loc,
      heff_sc.locals_clock m.locals m.clock⟩

private def txPutAuthAfter48 : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
      [.var .local (ofString "p"),
       .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64])])
    (.seq
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.seq
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64])])
        (.seq
          (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))

private def txPutAuthAfterPl : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "p"), .var .local (ofString "pl")])
    (.seq
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.seq
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64])])
        (.seq
          (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.seq
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "a"), .const 32#64]),
               .const 20#64])
            (.seq
              (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq
                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                  [.var .local (ofString "p"),
                   .load .one (.op .add [.var .local (ofString "a"), .const 40#64])])
                (.seq
                  (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                      [.var .local (ofString "p"),
                       .load .one (.op .add [.var .local (ofString "a"), .const 48#64])])
                    (.seq
                      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                      txPutAuthAfter48)))))))))

private def txPutAuthLoopBody : ProgHOL 64 :=
  .dec (ofString "a") .one
    (.op .add [.var .local (ofString "recs"),
      .panop .mul [.var .local (ofString "i"), .const 120#64]])
    (.decCall (ofString "pl") .one (ofString "auth_payload_len")
      [.var .local (ofString "a")]
      txPutAuthAfterPl)

private def txPutAuthWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    txPutAuthLoopBody

private theorem eval_txPutAuthAfter48 {F : Type}
    (s0 m5 : PanSemStateFiniteExact 64 F) (Rl : List Ivl) (gw : List String)
    (aw iw p5 w5 : BitVec 64) (pcur : Nat)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hgw : "heap_ptr" ∈ gw)
    (heff0_m5 : HeapByteEff s0 m5 Rl gw)
    (hin_iv : ∃ iv : Ivl, WordsOK s0 iv ∧ Inside iv sourceBase (globN s0 "heap_ptr") ∧
      iv.1 ≤ aw.toNat ∧ aw.toNat + 120 ≤ iv.1 + iv.2 ∧ (aw.toNat - iv.1) % 8 = 0)
    (hp5_nat : p5.toNat = pcur)
    (hm5_a : m5.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word p5)))
    (hm5_w : m5.locals.lookup (ofString "w") = some (.val (.word w5)))
    (hm5_i : m5.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hin_dst : ∃ ivl ∈ Rl, ivl.1 ≤ pcur ∧
      pcur +
        txU256EncodedLenPure
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80))) +
        txU256EncodedLenPure
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112))) ≤
        ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState m5 txPutAuthAfter48).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState m5 txPutAuthAfter48
    ((out.1 ≠ none ∧ out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1)) ∨
    ∃ (p7 w7 : BitVec 64),
      out.1 = none ∧
      p7.toNat = pcur +
        txU256EncodedLenPure
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80))) +
        txU256EncodedLenPure
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
          (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112))) ∧
      out.2.clock ≤ m5.clock ∧
      out.2.globals = m5.globals ∧
      out.2.locals = ((m5.locals.update (ofString "w", .val (.word w7))).update
        (ofString "p", .val (.word p7))).update (ofString "i", .val (.word (iw + 1#64))) ∧
      HeapByteEff m5 out.2 Rl gw := by
  intro out; dsimp only [out, txPutAuthAfter48] at hnt ⊢
  obtain ⟨iv, hwok, hin_recs, ha_lo, ha_hi, ha_mod⟩ := hin_iv
  have hfit_recs : iv.1 + iv.2 ≤ 2 ^ 64 := inside_fit_u64 hin_recs hAR0.2.2.1
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hwa_off : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 120 → WordAt s0 (aw.toNat + off) := by
    intro off hoff_mod hoff_le
    set q := (aw.toNat - iv.1 + off) / 8
    have heq : iv.1 + 8 * q = aw.toNat + off := by omega
    rw [← heq]
    exact wordAt_of_wordsOK hwok q (by omega)
  set sL6 := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
  set sL7 := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
  obtain ⟨ivl, hivl, hivl_lo, hivl_hi⟩ := hin_dst
  have hivl_hl : ivl.1 + ivl.2 ≤ heapLimit := (hRl_ge ivl hivl).2
  have haw56_nat : (aw + 56#64).toNat = aw.toNat + 56 := by
    rw [BitVec.toNat_add]; change (aw.toNat + 56) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
  have hev_m5_a56 : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a))
      (.op .add [.var .local (ofString "a"), .const 56#64]) = some (.val (.word (aw + 56#64))) := by
    have h56 : (56#64 : BitVec 64) + 0 = 56#64 := BitVec.add_zero _
    simp [evalHOLExact, evalListHOLExact, hm5_a, wordOpHOL, wordOp, valueIsWord, valueWord, h56]
  have hload_r := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs heff0_m5 hRl_ge hin_recs
    (.op .add [.var .local (ofString "a"), .const 56#64]) (aw + 56#64) hev_m5_a56
    (by rw [haw56_nat]; exact hwa_off 56 (by omega) (by omega))
    (by rw [haw56_nat]; exact hwa_off 64 (by omega) (by omega))
    (by rw [haw56_nat]; exact hwa_off 72 (by omega) (by omega))
    (by rw [haw56_nat]; exact hwa_off 80 (by omega) (by omega))
    (by rw [haw56_nat]; omega) (by rw [haw56_nat]; omega)
  simp only [haw56_nat, Nat.add_assoc] at hload_r
  have hc6_raw := eval_call_local_tx_put_u256 m5 "w"
    (.var .local (ofString "p"))
    (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64]))
    p5
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
    Rl gw heff0_m5.arena.1.code heff0_m5.arena hgw ⟨w5, hm5_w⟩
    (by simp [evalHOLExact, hm5_p]) hload_r
    ⟨ivl, hivl, by omega, by rw [hp5_nat]; omega⟩
  rcases eval_call_local_advance_pw m5 (ofString "tx_put_u256")
      [.var .local (ofString "p"),
       .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64])]
      p5 pcur sL6 Rl gw _ hp5_nat (by omega) hm5_p
      (fun hnt6 => by
        have h := hc6_raw hnt6; dsimp only at h
        exact ⟨fun hn => by
          obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
          exact ⟨len, hlen, hg, hl, he⟩, h.2⟩)
      hnt with ⟨hne, hnb, hnc, hnr⟩ | ⟨m6, p6, w6, hm6_out, hnt_m6, hp6_nat, _, hclk6, hm6_glob, hm6_loc, heff_m5_m6⟩
  · left; exact ⟨hne, hnb, hnc, hnr⟩
  · rw [hm6_out]
    have hm6_a : m6.locals.lookup (ofString "a") = some (.val (.word aw)) := by
      rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_a,
        show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
    have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word p6)) := by
      rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm6_w : m6.locals.lookup (ofString "w") = some (.val (.word w6)) := by
      rw [hm6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" by decide]
    have haw88_nat : (aw + 88#64).toNat = aw.toNat + 88 := by
      rw [BitVec.toNat_add]; change (aw.toNat + 88) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    have hev_m6_a88 : @evalHOLExact 64 F _ m6.toExact (fun a => Classical.propDecidable (m6.memaddrs a))
        (.op .add [.var .local (ofString "a"), .const 88#64]) = some (.val (.word (aw + 88#64))) := by
      have h88 : (88#64 : BitVec 64) + 0 = 88#64 := BitVec.add_zero _
      simp [evalHOLExact, evalListHOLExact, hm6_a, wordOpHOL, wordOp, valueIsWord, valueWord, h88]
    have hload_s := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs (heff0_m5.trans heff_m5_m6) hRl_ge hin_recs
      (.op .add [.var .local (ofString "a"), .const 88#64]) (aw + 88#64) hev_m6_a88
      (by rw [haw88_nat]; exact hwa_off 88 (by omega) (by omega))
      (by rw [haw88_nat]; exact hwa_off 96 (by omega) (by omega))
      (by rw [haw88_nat]; exact hwa_off 104 (by omega) (by omega))
      (by rw [haw88_nat]; exact hwa_off 112 (by omega) (by omega))
      (by rw [haw88_nat]; omega) (by rw [haw88_nat]; omega)
    simp only [haw88_nat, Nat.add_assoc] at hload_s
    have hc7_raw := eval_call_local_tx_put_u256 m6 "w"
      (.var .local (ofString "p"))
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64]))
      p6
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
      Rl gw heff_m5_m6.arena.1.code heff_m5_m6.arena hgw ⟨w6, hm6_w⟩
      (by simp [evalHOLExact, hm6_p]) hload_s
      ⟨ivl, hivl, by omega, by rw [hp6_nat]; omega⟩
    rcases eval_call_local_advance_pw m6 (ofString "tx_put_u256")
        [.var .local (ofString "p"),
         .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64])]
        p6 (pcur + sL6) sL7 Rl gw _ hp6_nat (by omega) hm6_p
        (fun hnt7 => by
          have h := hc7_raw hnt7; dsimp only at h
          exact ⟨fun hn => by
            obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
            exact ⟨len, hlen, hg, hl, he⟩, h.2⟩)
        hnt_m6 with ⟨hne, hnb, hnc, hnr⟩ | ⟨m7, p7, w7, hm7_out, _, hp7_nat, _, hclk7, hm7_glob, hm7_loc, heff_m6_m7⟩
    · left; exact ⟨hne, hnb, hnc, hnr⟩
    · right
      rw [hm7_out]
      have hm7_i : m7.locals.lookup (ofString "i") = some (.val (.word iw)) := by
        rw [hm7_loc, hm6_loc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_i,
          show ofString "p" ≠ ofString "i" by decide, show ofString "w" ≠ ofString "i" by decide]
      have hass_i : evaluateHOLFiniteState m7
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
          (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m7) := by
        rw [evaluateHOLFiniteState_assign]
        have hev : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
            (.op .add [.var .local (ofString "i"), .const 1#64]) =
            some (.val (.word (iw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hm7_i, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev]; dsimp only
        rw [if_pos (by simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hm7_i, shapeOfHOLExact, shapeEqHOL])]
        rfl
      rw [hass_i]; dsimp only
      let m8 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) m7
      have hm8_loc : m8.locals = ((m5.locals.update (ofString "w", .val (.word w7))).update
          (ofString "p", .val (.word p7))).update (ofString "i", .val (.word (iw + 1#64))) := by
        apply HolFiniteMapExact.ext; funext key
        simp only [m8, setVarHOLFinite, hm7_loc, hm6_loc, HolFiniteMapExact.lookup_update, FUPDATE]
        by_cases hi : ofString "i" = key
        · simp [hi]
        · by_cases hp : ofString "p" = key
          · simp [hi, hp]
          · by_cases hw : ofString "w" = key
            · simp [hi, hp, hw]
            · simp [hi, hp, hw]
      exact ⟨p7, w7, rfl, hp7_nat, le_trans hclk7 hclk6, hm7_glob.trans hm6_glob, hm8_loc,
        (heff_m5_m6.trans heff_m6_m7).locals_clock m8.locals m8.clock⟩

private theorem eval_txPutAuthAfterPl {F : Type}
    (s0 m0 : PanSemStateFiniteExact 64 F) (Rl : List Ivl) (gw : List String)
    (aw plw iw pw ww0 : BitVec 64) (c0 : Nat)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hgw : "heap_ptr" ∈ gw)
    (heff0_m0 : HeapByteEff s0 m0 Rl gw)
    (hin_iv : ∃ iv : Ivl, WordsOK s0 iv ∧ Inside iv sourceBase (globN s0 "heap_ptr") ∧
      iv.1 ≤ aw.toNat ∧ aw.toNat + 120 ≤ iv.1 + iv.2 ∧ (aw.toNat - iv.1) % 8 = 0)
    (hpl_nat : plw.toNat = authPayloadPure s0 aw.toNat)
    (hp_eq : pw.toNat = c0)
    (hm0_pl : m0.locals.lookup (ofString "pl") = some (.val (.word plw)))
    (hm0_a : m0.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hm0_p : m0.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hm0_w : m0.locals.lookup (ofString "w") = some (.val (.word ww0)))
    (hm0_i : m0.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hin_dst : ∃ ivl ∈ Rl, ivl.1 ≤ c0 ∧ c0 + authEntryEncodedPure s0 aw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState m0 txPutAuthAfterPl).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState m0 txPutAuthAfterPl
    ((out.1 ≠ none ∧ out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧ ¬ Resumes out.1)) ∨
    ∃ (p7 w7 : BitVec 64),
      out.1 = none ∧
      p7.toNat = c0 + authEntryEncodedPure s0 aw.toNat ∧
      out.2.clock ≤ m0.clock ∧
      out.2.globals = m0.globals ∧
      out.2.locals = ((m0.locals.update (ofString "w", .val (.word w7))).update
        (ofString "p", .val (.word p7))).update (ofString "i", .val (.word (iw + 1#64))) ∧
      HeapByteEff m0 out.2 Rl gw := by
  intro out; dsimp only [out, txPutAuthAfterPl] at hnt ⊢
  obtain ⟨iv, hwok, hin_recs, ha_lo, ha_hi, ha_mod⟩ := hin_iv
  have hfit_recs : iv.1 + iv.2 ≤ 2 ^ 64 := inside_fit_u64 hin_recs hAR0.2.2.1
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hwa_off : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 120 → WordAt s0 (aw.toNat + off) := by
    intro off hoff_mod hoff_le
    set q := (aw.toNat - iv.1 + off) / 8
    have heq : iv.1 + 8 * q = aw.toNat + off := by omega
    rw [← heq]
    exact wordAt_of_wordsOK hwok q (by omega)
  set sL1 := rlpHeaderLenPure (authPayloadPure s0 aw.toNat)
  set sL2 := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 aw.toNat)) (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 16))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))
  set sL4 := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 40)))
  set sL5 := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 48)))
  set sL6 := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 56))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 72))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
  set sL7 := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 88))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 104))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
  have hent_eq : authEntryEncodedPure s0 aw.toNat = sL1 + sL2 + 21 + sL4 + sL5 + sL6 + sL7 := by
    change rlpHeaderLenPure (authPayloadPure s0 aw.toNat) + authPayloadPure s0 aw.toNat =
      sL1 + sL2 + 21 + sL4 + sL5 + sL6 + sL7
    have hapl : authPayloadPure s0 aw.toNat = sL2 + 21 + sL4 + sL5 + sL6 + sL7 := rfl
    change sL1 + authPayloadPure s0 aw.toNat = _
    rw [hapl]; omega
  obtain ⟨ivl, hivl, hivl_lo, hivl_hi⟩ := hin_dst
  have hivl_hl : ivl.1 + ivl.2 ≤ heapLimit := (hRl_ge ivl hivl).2
  -- Call 1
  have hc1_raw := eval_call_local_rlp_encode_list_header m0 "w"
    (.var .local (ofString "p")) (.var .local (ofString "pl")) pw plw Rl gw
    heff0_m0.arena.1.code heff0_m0.arena ⟨ww0, hm0_w⟩
    (by simp [evalHOLExact, hm0_p]) (by simp [evalHOLExact, hm0_pl])
    ⟨ivl, hivl, by omega, by rw [hp_eq, hpl_nat]; omega⟩
  rcases eval_call_local_advance_pw m0 (ofString "rlp_encode_list_header")
      [.var .local (ofString "p"), .var .local (ofString "pl")]
      pw c0 sL1 Rl gw _ hp_eq (by omega) hm0_p
      (fun hnt1 => by
        have h := hc1_raw hnt1; dsimp only at h
        exact ⟨fun hn => by
          obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
          exact ⟨len, by rw [hlen, hpl_nat], hg, hl, he⟩, h.2⟩)
      hnt with ⟨hne, hnb, hnc, hnr⟩ | ⟨m1, p1, w1, hm1_out, hnt_m1, hp1_nat, _, hclk1, hm1_glob, hm1_loc, heff_m0_m1⟩
  · left; exact ⟨hne, hnb, hnc, hnr⟩
  · rw [hm1_out]
    have hm1_a : m1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_a,
        show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
    have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word p1)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_w : m1.locals.lookup (ofString "w") = some (.val (.word w1)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" by decide]
    -- Call 2
    have hev_m1_a0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
        (.op .add [.var .local (ofString "a"), .const 0#64]) = some (.val (.word aw)) := by
      have h0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
      have haw0 : aw + 0#64 = aw := BitVec.add_zero _
      simp [evalHOLExact, evalListHOLExact, hm1_a, wordOpHOL, wordOp, valueIsWord, valueWord, h0, haw0]
    have hload_c := load_u256_in_inside_fresh hAR0.2 hAR0.1.memaddrs (heff0_m0.trans heff_m0_m1) hRl_ge hin_recs
      (.op .add [.var .local (ofString "a"), .const 0#64]) aw hev_m1_a0
      (by simpa using hwa_off 0 (by omega) (by omega))
      (hwa_off 8 (by omega) (by omega))
      (hwa_off 16 (by omega) (by omega))
      (hwa_off 24 (by omega) (by omega))
      ha_lo (by omega)
    have hc2_raw := eval_call_local_tx_put_u256 m1 "w"
      (.var .local (ofString "p"))
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64]))
      p1
      (BitVec.ofNat 64 (memW s0 aw.toNat)) (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 16))) (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))
      Rl gw heff_m0_m1.arena.1.code heff_m0_m1.arena hgw ⟨w1, hm1_w⟩
      (by simp [evalHOLExact, hm1_p]) hload_c
      ⟨ivl, hivl, by omega, by rw [hp1_nat]; omega⟩
    rcases eval_call_local_advance_pw m1 (ofString "tx_put_u256")
        [.var .local (ofString "p"),
         .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64])]
        p1 (c0 + sL1) sL2 Rl gw _ hp1_nat (by omega) hm1_p
        (fun hnt2 => by
          have h := hc2_raw hnt2; dsimp only at h
          exact ⟨fun hn => by
            obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
            exact ⟨len, hlen, hg, hl, he⟩, h.2⟩)
        hnt_m1 with ⟨hne, hnb, hnc, hnr⟩ | ⟨m2, p2, w2, hm2_out, hnt_m2, hp2_nat, _, hclk2, hm2_glob, hm2_loc, heff_m1_m2⟩
    · left; exact ⟨hne, hnb, hnc, hnr⟩
    · rw [hm2_out]
      have hm2_a : m2.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_a,
          show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
      have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word p2)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm2_w : m2.locals.lookup (ofString "w") = some (.val (.word w2)) := by
        rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "w" by decide]
      -- Call 3
      have haw32_nat : (aw + 32#64).toNat = aw.toNat + 32 := by
        rw [BitVec.toNat_add]; change (aw.toNat + 32) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
      have hev_m2_a32 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
          (.op .add [.var .local (ofString "a"), .const 32#64]) = some (.val (.word (aw + 32#64))) := by
        have h32 : (32#64 : BitVec 64) + 0 = 32#64 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hm2_a, wordOpHOL, wordOp, valueIsWord, valueWord, h32]
      have hload_addr := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs ((heff0_m0.trans heff_m0_m1).trans heff_m1_m2)
        hRl_ge hin_recs (.op .add [.var .local (ofString "a"), .const 32#64]) (aw + 32#64) hev_m2_a32
        (by rw [haw32_nat]; exact hwa_off 32 (by omega) (by omega))
        (by rw [haw32_nat]; omega) (by rw [haw32_nat]; omega)
      rw [haw32_nat] at hload_addr
      have hhl20 : rlpHeaderLenPure (20#64 : BitVec 64).toNat + (20#64 : BitVec 64).toNat = 21 := by
        have : (20#64 : BitVec 64).toNat = 20 := by decide
        rw [this, rlpHeaderLenPure_of_le55 (by decide)]
      have hc3_raw := eval_call_local_rlp_encode_bytes_ge2 m2 "w"
        (.var .local (ofString "p"))
        (.load .one (.op .add [.var .local (ofString "a"), .const 32#64]))
        (.const 20#64)
        p2 (BitVec.ofNat 64 (memW s0 (aw.toNat + 32))) 20#64
        Rl gw heff_m1_m2.arena.1.code heff_m1_m2.arena ⟨w2, hm2_w⟩
        (by simp [evalHOLExact, hm2_p]) hload_addr rfl (by decide)
        (by rw [WkBlockTxEnc.heapEnd_val]; decide)
        ⟨ivl, hivl, by omega, by rw [Nat.add_assoc, hhl20, hp2_nat]; omega⟩
      rcases eval_call_local_advance_pw m2 (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "a"), .const 32#64]),
           .const 20#64]
          p2 (c0 + sL1 + sL2) 21 Rl gw _ hp2_nat (by omega) hm2_p
          (fun hnt3 => by
            have h := hc3_raw hnt3; dsimp only at h
            exact ⟨fun hn => by
              obtain ⟨len, hlen, _, hg, hl, he⟩ := h.1 hn
              exact ⟨len, by rw [hlen, hhl20], hg, hl, he⟩, h.2⟩)
          hnt_m2 with ⟨hne, hnb, hnc, hnr⟩ | ⟨m3, p3, w3, hm3_out, hnt_m3, hp3_nat, _, hclk3, hm3_glob, hm3_loc, heff_m2_m3⟩
      · left; exact ⟨hne, hnb, hnc, hnr⟩
      · rw [hm3_out]
        have hm3_a : m3.locals.lookup (ofString "a") = some (.val (.word aw)) := by
          rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_a,
            show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
        have hm3_p : m3.locals.lookup (ofString "p") = some (.val (.word p3)) := by
          rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hm3_w : m3.locals.lookup (ofString "w") = some (.val (.word w3)) := by
          rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "p" ≠ ofString "w" by decide]
        -- Call 4
        have haw40_nat : (aw + 40#64).toNat = aw.toNat + 40 := by
          rw [BitVec.toNat_add]; change (aw.toNat + 40) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hev_m3_a40 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
            (.op .add [.var .local (ofString "a"), .const 40#64]) = some (.val (.word (aw + 40#64))) := by
          have h40 : (40#64 : BitVec 64) + 0 = 40#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, hm3_a, wordOpHOL, wordOp, valueIsWord, valueWord, h40]
        have hload_n := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs
          (((heff0_m0.trans heff_m0_m1).trans heff_m1_m2).trans heff_m2_m3)
          hRl_ge hin_recs (.op .add [.var .local (ofString "a"), .const 40#64]) (aw + 40#64) hev_m3_a40
          (by rw [haw40_nat]; exact hwa_off 40 (by omega) (by omega))
          (by rw [haw40_nat]; omega) (by rw [haw40_nat]; omega)
        rw [haw40_nat] at hload_n
        have hc4_raw := eval_call_local_rlp_encode_word_exact m3 "w"
          (.var .local (ofString "p"))
          (.load .one (.op .add [.var .local (ofString "a"), .const 40#64]))
          p3 (BitVec.ofNat 64 (memW s0 (aw.toNat + 40)))
          Rl gw heff_m2_m3.arena.1.code heff_m2_m3.arena ⟨w3, hm3_w⟩
          (by simp [evalHOLExact, hm3_p]) hload_n
          ⟨ivl, hivl, by omega, by rw [hp3_nat]; omega⟩
        rcases eval_call_local_advance_pw m3 (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "a"), .const 40#64])]
            p3 (c0 + sL1 + sL2 + 21) sL4 Rl gw _ hp3_nat (by omega) hm3_p
            (fun hnt4 => by
              have h := hc4_raw hnt4; dsimp only at h
              exact ⟨fun hn => by
                obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
                exact ⟨len, hlen, hg, hl, he⟩, h.2⟩)
            hnt_m3 with ⟨hne, hnb, hnc, hnr⟩ | ⟨m4, p4, w4, hm4_out, hnt_m4, hp4_nat, _, hclk4, hm4_glob, hm4_loc, heff_m3_m4⟩
        · left; exact ⟨hne, hnb, hnc, hnr⟩
        · rw [hm4_out]
          have hm4_a : m4.locals.lookup (ofString "a") = some (.val (.word aw)) := by
            rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_a,
              show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
          have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word p4)) := by
            rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hm4_w : m4.locals.lookup (ofString "w") = some (.val (.word w4)) := by
            rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "p" ≠ ofString "w" by decide]
          -- Call 5
          have haw48_nat : (aw + 48#64).toNat = aw.toNat + 48 := by
            rw [BitVec.toNat_add]; change (aw.toNat + 48) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hev_m4_a48 : @evalHOLExact 64 F _ m4.toExact (fun a => Classical.propDecidable (m4.memaddrs a))
              (.op .add [.var .local (ofString "a"), .const 48#64]) = some (.val (.word (aw + 48#64))) := by
            have h48 : (48#64 : BitVec 64) + 0 = 48#64 := BitVec.add_zero _
            simp [evalHOLExact, evalListHOLExact, hm4_a, wordOpHOL, wordOp, valueIsWord, valueWord, h48]
          have hload_y := load_word_in_inside_fresh hAR0.2 hAR0.1.memaddrs
            ((((heff0_m0.trans heff_m0_m1).trans heff_m1_m2).trans heff_m2_m3).trans heff_m3_m4)
            hRl_ge hin_recs (.op .add [.var .local (ofString "a"), .const 48#64]) (aw + 48#64) hev_m4_a48
            (by rw [haw48_nat]; exact hwa_off 48 (by omega) (by omega))
            (by rw [haw48_nat]; omega) (by rw [haw48_nat]; omega)
          rw [haw48_nat] at hload_y
          have hc5_raw := eval_call_local_rlp_encode_word_exact m4 "w"
            (.var .local (ofString "p"))
            (.load .one (.op .add [.var .local (ofString "a"), .const 48#64]))
            p4 (BitVec.ofNat 64 (memW s0 (aw.toNat + 48)))
            Rl gw heff_m3_m4.arena.1.code heff_m3_m4.arena ⟨w4, hm4_w⟩
            (by simp [evalHOLExact, hm4_p]) hload_y
            ⟨ivl, hivl, by omega, by rw [hp4_nat]; omega⟩
          rcases eval_call_local_advance_pw m4 (ofString "rlp_encode_word")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "a"), .const 48#64])]
              p4 (c0 + sL1 + sL2 + 21 + sL4) sL5 Rl gw txPutAuthAfter48 hp4_nat (by omega) hm4_p
              (fun hnt5 => by
                have h := hc5_raw hnt5; dsimp only at h
                exact ⟨fun hn => by
                  obtain ⟨len, hlen, _, _, _, hg, hl, he⟩ := h.1 hn
                  exact ⟨len, hlen, hg, hl, he⟩, h.2⟩)
              hnt_m4 with ⟨hne, hnb, hnc, hnr⟩ | ⟨m5, p5, w5, hm5_out, hnt_m5, hp5_nat, _, hclk5, hm5_glob, hm5_loc, heff_m4_m5⟩
          · left; exact ⟨hne, hnb, hnc, hnr⟩
          · rw [hm5_out]
            have heff_m0_m5 : HeapByteEff m0 m5 Rl gw :=
              (((heff_m0_m1.trans heff_m1_m2).trans heff_m2_m3).trans heff_m3_m4).trans heff_m4_m5
            have hm5_a : m5.locals.lookup (ofString "a") = some (.val (.word aw)) := by
              rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm4_a,
                show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
            have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word p5)) := by
              rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hm5_w : m5.locals.lookup (ofString "w") = some (.val (.word w5)) := by
              rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "p" ≠ ofString "w" by decide]
            have hm5_i : m5.locals.lookup (ofString "i") = some (.val (.word iw)) := by
              rw [hm5_loc, hm4_loc, hm3_loc, hm2_loc, hm1_loc]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_i,
                show ofString "p" ≠ ofString "i" by decide, show ofString "w" ≠ ofString "i" by decide]
            rcases eval_txPutAuthAfter48 s0 m5 Rl gw aw iw p5 w5
                (c0 + sL1 + sL2 + 21 + sL4 + sL5)
                hAR0 hRl_ge hgw (heff0_m0.trans heff_m0_m5)
                ⟨iv, hwok, hin_recs, ha_lo, ha_hi, ha_mod⟩
                hp5_nat hm5_a hm5_p hm5_w hm5_i
                ⟨ivl, hivl, by omega, by omega⟩
                hnt_m5 with ⟨hne, hnb, hnc, hnr⟩ | ⟨p7, w7, hn_out, hp7_nat, hclk_tail, hglob_tail, hloc_tail, heff_tail⟩
            · left; exact ⟨hne, hnb, hnc, hnr⟩
            · right
              have hloc_collapse : (evaluateHOLFiniteState m5 txPutAuthAfter48).2.locals =
                  ((m0.locals.update (ofString "w", .val (.word w7))).update
                    (ofString "p", .val (.word p7))).update (ofString "i", .val (.word (iw + 1#64))) := by
                rw [hloc_tail, hm5_loc, hm4_loc, hm3_loc, hm2_loc, hm1_loc]
                apply HolFiniteMapExact.ext; funext key
                simp only [HolFiniteMapExact.lookup_update, FUPDATE]
                by_cases hi : ofString "i" = key
                · simp [hi]
                · by_cases hp : ofString "p" = key
                  · simp [hi, hp]
                  · by_cases hw : ofString "w" = key
                    · simp [hi, hp, hw]
                    · simp [hi, hp, hw]
              exact ⟨p7, w7, hn_out, by omega,
                le_trans hclk_tail (le_trans hclk5 (le_trans hclk4 (le_trans hclk3 (le_trans hclk2 hclk1)))),
                hglob_tail.trans (hm5_glob.trans (hm4_glob.trans (hm3_glob.trans (hm2_glob.trans hm1_glob)))),
                hloc_collapse, heff_m0_m5.trans heff_tail⟩

private theorem eval_txPutAuthWhile_exact {F : Type}
    (clk : Nat) (s0 s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (dst0 recsw nw pw iw : BitVec 64) (pstart : Nat)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hgw : "heap_ptr" ∈ gw)
    (hclk : s.clock ≤ clk)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat) ∧
      Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hi_le : iw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = pstart + authListPayloadPrefix s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧
      pstart + authListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2)
    (hl_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hl_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hl_p : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hl_w : ∃ ww : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word ww)))
    (hnt : (evaluateHOLFiniteState s txPutAuthWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s txPutAuthWhile
    (out.1 = none →
      ∃ pf : BitVec 64,
        pf.toNat = pstart + authListPayloadPrefix s0 recsw.toNat nw.toNat ∧
        out.2.globals = s.globals ∧
        HeapByteEff s out.2 Rl gw ∧
        out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word pf))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  induction clk generalizing s pw iw with
  | zero =>
    intro out; dsimp only [out, txPutAuthWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hz : s.clock = 0 := by omega
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩
  | succ k ih =>
    intro out; dsimp only [out, txPutAuthWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
    have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hl_i, hl_n, Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
      split_ifs <;> rfl
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hnt; exact absurd rfl hnt
      · rw [if_neg hz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set sd := decClockHOLFinite s
        have heff_sd : HeapByteEff s sd Rl gw :=
          (HeapByteEff.refl heff0.arena Rl gw).locals_clock sd.locals sd.clock
        have heff0_sd : HeapByteEff s0 sd Rl gw := heff0.trans heff_sd
        have ⟨hwok, hin_recs⟩ := hrecs_ok (by omega)
        have hfit_recs : recsw.toNat + 120 * nw.toNat ≤ 2 ^ 64 :=
          inside_fit_u64 hin_recs hAR0.2.2.1
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
        set aw := recsw + iw * 120#64
        have haw_nat : aw.toNat = recsw.toNat + 120 * iw.toNat := by
          have hi120 : (iw * 120#64).toNat = 120 * iw.toNat := by
            rw [BitVec.toNat_mul]; change (iw.toNat * 120) % 2 ^ 64 = 120 * iw.toNat
            rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
          rw [show aw = recsw + iw * 120#64 from rfl, BitVec.toNat_add, hi120]
          exact Nat.mod_eq_of_lt (by omega)
        dsimp only [txPutAuthLoopBody] at hnt ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hev_aw : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "recs"),
              .panop .mul [.var .local (ofString "i"), .const 120#64]]) =
            some (.val (.word aw)) := by
          have h0 : (iw * 120#64) + 0 = iw * 120#64 := BitVec.add_zero _
          simp [evalHOLExact, evalListHOLExact, show sd.locals = s.locals from rfl,
            hl_recs, hl_i, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, h0, aw]
        rw [hev_aw] at hnt ⊢; dsimp only at hnt ⊢
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢; dsimp only at hnt ⊢
        set d1 := setVarHOLFinite (ofString "a") (.val (.word aw)) sd
        have heff_sd_d1 : HeapByteEff sd d1 Rl gw :=
          (HeapByteEff.refl heff_sd.arena Rl gw).locals_clock d1.locals d1.clock
        have hnt_d1 : (evaluateHOLFiniteState d1
            (.decCall (ofString "pl") .one (ofString "auth_payload_len")
              [.var .local (ofString "a")] txPutAuthAfterPl)).1 ≠ some .timeOut := by
          intro hto; rw [hto] at hnt; exact hnt rfl
        have hrec_iv : ∃ iv : Ivl, WordsOK s0 iv ∧ Inside iv sourceBase (globN s0 "heap_ptr") ∧
            iv.1 ≤ aw.toNat ∧ aw.toNat + 120 ≤ iv.1 + iv.2 ∧ (aw.toNat - iv.1) % 8 = 0 := by
          refine ⟨(recsw.toNat, 120 * nw.toNat), hwok, hin_recs, ?_, ?_, ?_⟩
          · dsimp only; rw [haw_nat]; omega
          · dsimp only; rw [haw_nat]; omega
          · dsimp only; rw [haw_nat]; omega
        obtain ⟨m0, hpl_nat, _, _, hc_pl, hm0_glob, _, hm0_loc, heff_d1_m0, hnt_m0, hout_m0⟩ :=
          eval_decCall_auth_payload_len s0 d1 "pl" (.var .local (ofString "a")) aw txPutAuthAfterPl
            Rl gw hAR0 hRl_ge (heff0_sd.trans heff_sd_d1)
            (by simp [evalHOLExact, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hrec_iv hnt_d1
        rw [hout_m0] at hnt ⊢; dsimp only at hnt ⊢
        set plw := BitVec.ofNat 64 (authPayloadPure s0 aw.toNat)
        have heff_s_m0 : HeapByteEff s m0 Rl gw := (heff_sd.trans heff_sd_d1).trans heff_d1_m0
        obtain ⟨ww0, hww0⟩ := hl_w
        have hm0_pl : m0.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, plw]
        have hm0_a : m0.locals.lookup (ofString "a") = some (.val (.word aw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show ofString "pl" ≠ ofString "a" by decide]
        have hm0_p : m0.locals.lookup (ofString "p") = some (.val (.word pw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_p,
            show ofString "pl" ≠ ofString "p" by decide, show ofString "a" ≠ ofString "p" by decide]
        have hm0_w : m0.locals.lookup (ofString "w") = some (.val (.word ww0)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hww0,
            show ofString "pl" ≠ ofString "w" by decide, show ofString "a" ≠ ofString "w" by decide]
        have hm0_dst : m0.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_dst,
            show ofString "pl" ≠ ofString "dst" by decide, show ofString "a" ≠ ofString "dst" by decide]
        have hm0_recs : m0.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_recs,
            show ofString "pl" ≠ ofString "recs" by decide, show ofString "a" ≠ ofString "recs" by decide]
        have hm0_n : m0.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_n,
            show ofString "pl" ≠ ofString "n" by decide, show ofString "a" ≠ ofString "n" by decide]
        have hm0_i : m0.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, d1, setVarHOLFinite,
            show sd.locals = s.locals from rfl, hl_i,
            show ofString "pl" ≠ ofString "i" by decide, show ofString "a" ≠ ofString "i" by decide]
        obtain ⟨ivl, hivl, hivl_lo, hivl_hi⟩ := hin_ivl
        have hpref_next_le : authListPayloadPrefix s0 recsw.toNat (iw.toNat + 1) ≤
            authListPayloadPrefix s0 recsw.toNat nw.toNat :=
          authListPayloadPrefix_mono s0 recsw.toNat (by omega)
        have hpref_succ : authListPayloadPrefix s0 recsw.toNat (iw.toNat + 1) =
            authListPayloadPrefix s0 recsw.toNat iw.toNat + authEntryEncodedPure s0 aw.toNat := by
          rw [authListPayloadPrefix, ← haw_nat]
        rcases htail_run : evaluateHOLFiniteState m0 txPutAuthAfterPl with ⟨rt, st⟩
        have htail := eval_txPutAuthAfterPl s0 m0 Rl gw aw plw iw pw ww0
          (pstart + authListPayloadPrefix s0 recsw.toNat iw.toNat)
          hAR0 hRl_ge hgw (heff0.trans heff_s_m0) hrec_iv hpl_nat hp_eq
          hm0_pl hm0_a hm0_p hm0_w hm0_i
          ⟨ivl, hivl, by omega, by omega⟩
          hnt_m0
        dsimp only at htail; rw [htail_run] at htail
        simp only [htail_run] at hnt ⊢
        rcases htail with ⟨hne, hnb, hnc, hnr⟩ | ⟨p7, w7, rfl, hp7_nat, hclk_st, hst_glob, hst_loc, heff_m0_st⟩
        · cases rt with
          | none => exact absurd rfl hne
          | some r =>
            cases r with
            | «break» => exact absurd rfl hnb
            | «continue» => exact absurd rfl hnc
            | _ => dsimp only; exact ⟨fun h => by simp at h, fun _ => hnr⟩
        · dsimp only at hclk_st hst_glob hst_loc heff_m0_st hnt ⊢
          let bodyPost : PanSemStateFiniteExact 64 F :=
            { st with
              locals :=
                ((st.locals.resVarEq (ofString "pl", d1.locals.lookup (ofString "pl"))).resVarEq
                  (ofString "a", sd.locals.lookup (ofString "a"))) }
          have hbp_clk : bodyPost.clock ≤ k := by
            have hd1_c : d1.clock = s.clock - 1 := rfl
            have hbp_c : bodyPost.clock = st.clock := rfl
            omega
          have heff_s_bp : HeapByteEff s bodyPost Rl gw :=
            (heff_s_m0.trans heff_m0_st).locals_clock bodyPost.locals bodyPost.clock
          have hbp_glob : bodyPost.globals = s.globals := by
            change st.globals = s.globals
            have hd1g : d1.globals = s.globals := rfl
            rw [hst_glob, hm0_glob, hd1g]
          have hiw'_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = iw.toNat + 1
            exact Nat.mod_eq_of_lt (by omega)
          have hp7_next : p7.toNat = pstart + authListPayloadPrefix s0 recsw.toNat (iw + 1#64).toNat := by
            rw [hiw'_nat, hp7_nat, hpref_succ]; omega
          have hbp_dst : bodyPost.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_dst,
              show ofString "i" ≠ ofString "dst" by decide,
              show ofString "p" ≠ ofString "dst" by decide,
              show ofString "w" ≠ ofString "dst" by decide]
          have hbp_recs : bodyPost.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_recs,
              show ofString "i" ≠ ofString "recs" by decide,
              show ofString "p" ≠ ofString "recs" by decide,
              show ofString "w" ≠ ofString "recs" by decide]
          have hbp_n : bodyPost.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_n,
              show ofString "i" ≠ ofString "n" by decide,
              show ofString "p" ≠ ofString "n" by decide,
              show ofString "w" ≠ ofString "n" by decide]
          have hbp_p : bodyPost.locals.lookup (ofString "p") = some (.val (.word p7)) := by
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide]
          have hbp_i : bodyPost.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hbp_w : ∃ ww : BitVec 64, bodyPost.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            refine ⟨w7, ?_⟩
            simp only [bodyPost]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [lookup_resVarEq_ne _ _ _ _ (by decide)]
            rw [hst_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "w" by decide,
              show ofString "p" ≠ ofString "w" by decide]
          have hrec := ih bodyPost p7 (iw + 1#64) hbp_clk (heff0.trans heff_s_bp)
            (by omega) hp7_next hbp_dst hbp_recs hbp_n hbp_p hbp_i hbp_w hnt
          dsimp only at hrec
          exact ⟨fun hn => by
            obtain ⟨pf, hpf_eq, hpost_glob, heff_post, hpost_dst, hpost_p⟩ := hrec.1 hn
            exact ⟨pf, hpf_eq, hpost_glob.trans hbp_glob, heff_s_bp.trans heff_post, hpost_dst, hpost_p⟩,
            hrec.2⟩
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0#64 : BitVec 64) ≠ 0))]
      have hieq : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨pw, by rw [← hieq]; exact hp_eq, rfl, HeapByteEff.refl heff0.arena Rl gw, hl_dst, hl_p⟩,
        fun h => False.elim (h rfl)⟩

private def txPutAuthAfterTotal : ProgHOL 64 :=
  .decCall (ofString "w") .one (ofString "rlp_encode_list_header")
    [.var .local (ofString "dst"), .var .local (ofString "total")]
    (.dec (ofString "p") .one (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
      (.dec (ofString "i") .one (.const 0#64)
        (.seq txPutAuthWhile
          (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))

private theorem eval_call_local_tx_put_authorizations {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp recsExp nExp : ExpHOL 64)
    (dst0 recsw nw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (hRl_ge : ∀ x ∈ Rl, globN s0 "heap_ptr" ≤ x.1 ∧ x.1 + x.2 ≤ heapLimit)
    (hgw : "heap_ptr" ∈ gw)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat) ∧
      Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat) +
        authListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_authorizations")
        [dstExp, recsExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_authorizations")
        [dstExp, recsExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat) +
          authListPayloadPrefix s0 recsw.toNat nw.toNat ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hcode : s.code = originalRuntimeCode := heff0.arena.1.code
  have hAR : ArenaReady s := heff0.arena
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, recsExp, nExp] = some [.val (.word dst0), .val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hrecs, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "tx_put_authorizations")
    (ofString "dst") (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_tx_put_authorizations) dst0 recsw nw
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_tx_put_authorizations)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "recs", ValueHOL.val (.word recsw))).update (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have heff_s_ent : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hAR Rl gw).locals_clock ent.locals ent.clock
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "recs" ≠ ofString "dst" by decide]
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_tx_put_authorizations =
        .decCall (ofString "total") .one (ofString "auth_list_payload_len")
          [.var .local (ofString "recs"), .var .local (ofString "n")]
          txPutAuthAfterTotal := rfl
    have hbody :
        let outb := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_authorizations)
        (outb.1 ≠ some .timeOut) →
        (Resumes outb.1 →
          ∃ len : BitVec 64,
            outb.1 = some (.returned (.val (.word len))) ∧
            len.toNat = rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat) +
              authListPayloadPrefix s0 recsw.toNat nw.toNat ∧
            outb.2.globals = ent.globals ∧
            HeapByteEff ent outb.2 Rl gw) := by
      intro outb hnt_b hres_b
      dsimp only [outb] at hnt_b hres_b ⊢
      rw [hb] at hnt_b hres_b ⊢
      obtain ⟨mid0, hpl_nat, _, hm0_glob, _, hm0_loc, heff_ent_m0, hnt_m0, hout_m0⟩ :=
        eval_decCall_auth_list_payload_len s0 ent "total"
          (.var .local (ofString "recs")) (.var .local (ofString "n"))
          recsw nw txPutAuthAfterTotal Rl gw hAR0 hRl_ge (heff0.trans heff_s_ent)
          (by simp [evalHOLExact, hent_recs])
          (by simp [evalHOLExact, hent_n])
          hn_lt hrecs_ok hnt_b
      rw [hout_m0] at hres_b ⊢
      dsimp only [txPutAuthAfterTotal] at hnt_m0 hres_b ⊢
      set totw := BitVec.ofNat 64 (authListPayloadPrefix s0 recsw.toNat nw.toNat)
      have hm0_tot : mid0.locals.lookup (ofString "total") = some (.val (.word totw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, totw]
      have hm0_dst : mid0.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
          show ofString "total" ≠ ofString "dst" by decide]
      have hm0_recs : mid0.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_recs,
          show ofString "total" ≠ ofString "recs" by decide]
      have hm0_n : mid0.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm0_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
          show ofString "total" ≠ ofString "n" by decide]
      have hin_lh : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
          dst0.toNat + rlpHeaderLenPure totw.toNat ≤ ivl.1 + ivl.2 := by
        rw [hpl_nat]; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩
      obtain ⟨mid1, hhl_nat, _, _, hdst_lt_he, hm1_glob, hm1_loc, heff_m0_m1, hnt_m1, hres_m1, hout_m1⟩ :=
        WkBlockTxEnc.eval_decCall_rlp_encode_list_header mid0 "w"
          (.var .local (ofString "dst")) (.var .local (ofString "total"))
          dst0 totw _ Rl gw heff_ent_m0.arena.1.code heff_ent_m0.arena
          (by simp [evalHOLExact, hm0_dst])
          (by simp [evalHOLExact, hm0_tot])
          hin_lh hnt_m0 hres_b
      rw [hout_m1]
      set w0 := BitVec.ofNat 64 (rlpHeaderLenPure totw.toNat)
      have hw0_nat : w0.toNat = rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat) := by
        have h1 : w0.toNat = rlpHeaderLenPure totw.toNat := hhl_nat
        rw [hpl_nat] at h1; exact h1
      have hm1_w : mid1.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, w0]
      have hm1_dst : mid1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hm1_recs : mid1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_recs,
          show ofString "w" ≠ ofString "recs" by decide]
      have hm1_n : mid1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm0_n,
          show ofString "w" ≠ ofString "n" by decide]
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_p0 : @evalHOLExact 64 F _ mid1.toExact (fun a => Classical.propDecidable (mid1.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
          some (.val (.word (dst0 + w0))) := by
        have hzw : w0 + 0 = w0 := BitVec.add_zero _
        simp [evalHOLExact, evalListHOLExact, hm1_dst, hm1_w, wordOpHOL, wordOp, valueIsWord, valueWord, hzw]
      rw [hev_p0] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      set mid2 := setVarHOLFinite (ofString "p") (.val (.word (dst0 + w0))) mid1
      rw [evaluateHOLFiniteState_dec_total] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      have hev_i0 : @evalHOLExact 64 F _ mid2.toExact (fun a => Classical.propDecidable (mid2.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      rw [hev_i0] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt_m1 hres_m1 ⊢; dsimp only at hnt_m1 hres_m1 ⊢
      set mid3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) mid2
      have heff_ent_m3 : HeapByteEff ent mid3 Rl gw :=
        (heff_ent_m0.trans heff_m0_m1).locals_clock mid3.locals mid3.clock
      set pstart := dst0.toNat + rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat)
      have hp0_nat : (dst0 + w0).toNat = pstart + authListPayloadPrefix s0 recsw.toNat (0#64 : BitVec 64).toNat := by
        simp only [authListPayloadPrefix, Nat.add_zero, pstart]
        rw [BitVec.toNat_add, hw0_nat]
        have hbnd := rlpHeaderLenPure_bounds (authListPayloadPrefix s0 recsw.toNat nw.toNat)
        exact Nat.mod_eq_of_lt (by rw [WkBlockTxEnc.heapEnd_val] at hdst_lt_he; omega)
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ pstart ∧
          pstart + authListPayloadPrefix s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 := by
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, by dsimp [pstart]; omega, h2⟩
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m1 hres_m1 ⊢
      rcases hw_run : evaluateHOLFiniteState mid3 txPutAuthWhile with ⟨rw_res, sw_post⟩
      have hnt_w : rw_res ≠ some .timeOut := by
        rintro rfl; simp only [hw_run] at hnt_m1; exact hnt_m1 rfl
      have hloop := eval_txPutAuthWhile_exact mid3.clock s0 mid3 Rl gw
        dst0 recsw nw (dst0 + w0) 0#64 pstart hAR0 hRl_ge hgw le_rfl
        ((heff0.trans heff_s_ent).trans heff_ent_m3)
        hn_lt hrecs_ok (by simp) hp0_nat hin_loop
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
          show ofString "i" ≠ ofString "recs" by decide, show ofString "p" ≠ ofString "recs" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide])
        (by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide])
        (by simp [mid3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ⟨w0, by simp [mid3, mid2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]⟩
        (by rw [hw_run]; exact hnt_w)
      dsimp only at hloop; rw [hw_run] at hloop
      simp only [hw_run] at hnt_m1 hres_m1 ⊢
      cases rw_res with
      | some r' =>
        exact False.elim (hloop.2 (by simp) hres_m1)
      | none =>
        dsimp only at hnt_m1 hres_m1 ⊢
        obtain ⟨pf, hpf_eq, hsw_glob, heff_w, hsw_dst, hsw_p⟩ := hloop.1 rfl
        dsimp only at hsw_glob heff_w hsw_dst hsw_p
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ sw_post.toExact (fun a => Classical.propDecidable (sw_post.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (pf - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hsw_p, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact])]
        dsimp only
        have hsub_nat : (pf - dst0).toNat =
            rlpHeaderLenPure (authListPayloadPrefix s0 recsw.toNat nw.toNat) +
              authListPayloadPrefix s0 recsw.toNat nw.toNat := by
          rw [BitVec.toNat_sub_of_le]
          · dsimp [pstart] at hpf_eq; omega
          · rw [BitVec.le_def]; dsimp [pstart] at hpf_eq; omega
        refine ⟨pf - dst0, rfl, hsub_nat, ?_, ?_⟩
        · change sw_post.globals = ent.globals
          have hm3g : mid3.globals = mid1.globals := rfl
          rw [hsw_glob, hm3g, hm1_glob, hm0_glob]
        · exact (((((heff_ent_m3.trans heff_w).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
    rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_authorizations) with ⟨rb, sb⟩
    have hnt_b : rb ≠ some .timeOut := by
      rintro rfl; simp only [hrun] at hnt; exact hnt rfl
    simp only [hrun] at hnt ⊢
    cases rb with
    | none => exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev =>
        refine ⟨fun h => by simp at h, fun _ hres_call => ?_⟩
        have hres_ent : Resumes (some (.exception eid ev)) := by
          rcases hres_call with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨_, hrb, _⟩ := hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_ent)
        simp only [hrun] at hrb; cases hrb
      | returned rv =>
        obtain ⟨len, hrb, hlen_eq, hsb_glob, heff_ent⟩ :=
          hbody (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
        simp only [hrun] at hrb hsb_glob heff_ent
        injection hrb with hrv; injection hrv with hrv'; subst hrv'
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]; rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { sb with locals := s.locals }
        exact ⟨fun _ => ⟨len, hlen_eq, hsb_glob, rfl,
          (heff_s_ent.trans heff_ent).locals_clock mid.locals mid.clock⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => WkBlockTxEnc.not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
