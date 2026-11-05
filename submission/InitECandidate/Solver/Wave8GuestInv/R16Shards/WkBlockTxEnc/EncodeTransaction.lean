import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min

/-!
# R16k EncodeTransaction: `wk_encode_transaction_strong`

Strengthened `WorldKeeps` theorem for `encode_transaction` using the
`TxValidEncodeReady` precondition, which extends `TxValidAt` with `Inside`
conditions on every sub-array pointer read by `tx_encode_generic`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Section 1: Lookup theorems for tx functions -/

theorem lookup_tx_put_u256 :
    originalRuntimeCode.lookup (ofString "tx_put_u256") =
      some ([(ofString "dst", .one), (ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_tx_put_u256, .one) :=
  lookup_of_guestAst_getElem 318 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_u256) rfl

theorem lookup_tx_u256_encoded_len :
    originalRuntimeCode.lookup (ofString "tx_u256_encoded_len") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_tx_u256_encoded_len, .one) :=
  lookup_of_guestAst_getElem 319 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_u256_encoded_len) rfl

theorem lookup_tx_put_to :
    originalRuntimeCode.lookup (ofString "tx_put_to") =
      some ([(ofString "dst", .one), (ofString "to", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_to, .one) :=
  lookup_of_guestAst_getElem 320 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_to) rfl

theorem lookup_access_list_payload_len :
    originalRuntimeCode.lookup (ofString "access_list_payload_len") =
      some ([(ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_access_list_payload_len, .one) :=
  lookup_of_guestAst_getElem 321 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_access_list_payload_len) rfl

theorem lookup_tx_put_access_list :
    originalRuntimeCode.lookup (ofString "tx_put_access_list") =
      some ([(ofString "dst", .one), (ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_access_list, .one) :=
  lookup_of_guestAst_getElem 322 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_access_list) rfl

theorem lookup_tx_put_blob_hashes :
    originalRuntimeCode.lookup (ofString "tx_put_blob_hashes") =
      some ([(ofString "dst", .one), (ofString "buf", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes, .one) :=
  lookup_of_guestAst_getElem 323 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_blob_hashes) rfl

theorem lookup_auth_payload_len :
    originalRuntimeCode.lookup (ofString "auth_payload_len") =
      some ([(ofString "a", .one)],
        sourceFnBody Guest.Software.guestFn_auth_payload_len, .one) :=
  lookup_of_guestAst_getElem 324 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_auth_payload_len) rfl

theorem lookup_auth_list_payload_len :
    originalRuntimeCode.lookup (ofString "auth_list_payload_len") =
      some ([(ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_auth_list_payload_len, .one) :=
  lookup_of_guestAst_getElem 325 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_auth_list_payload_len) rfl

theorem lookup_tx_put_authorizations :
    originalRuntimeCode.lookup (ofString "tx_put_authorizations") =
      some ([(ofString "dst", .one), (ofString "recs", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_tx_put_authorizations, .one) :=
  lookup_of_guestAst_getElem 326 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_put_authorizations) rfl

theorem lookup_tx_encode_bound :
    originalRuntimeCode.lookup (ofString "tx_encode_bound") =
      some ([(ofString "tx", .one)],
        sourceFnBody Guest.Software.guestFn_tx_encode_bound, .one) :=
  lookup_of_guestAst_getElem 327 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_encode_bound) rfl

theorem lookup_tx_encode_generic :
    originalRuntimeCode.lookup (ofString "tx_encode_generic") =
      some ([(ofString "tx", .one), (ofString "mode", .one), (ofString "chain_id", .one)],
        sourceFnBody Guest.Software.guestFn_tx_encode_generic,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 328 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_encode_generic) rfl

theorem lookup_encode_transaction_strong :
    originalRuntimeCode.lookup (ofString "encode_transaction") =
      some ([(ofString "tx", .one)],
        sourceFnBody Guest.Software.guestFn_encode_transaction,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 329 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_transaction) rfl

/-! ## Section 2: FunLocFrame helpers for pure length-computation functions -/

theorem lookup_rlp_word_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_word_encoded_len") =
      some ([(ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_word_encoded_len, .one) :=
  lookup_of_guestAst_getElem 127 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_word_encoded_len) rfl

theorem funLocFrame_rlp_be_len : M13.FunLocFrame (ofString "rlp_be_len") :=
  M13.funLocFrame_of_locOnlyW 118 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_rlp_be_len rfl rfl

theorem funLocFrame_rlp_header_len : M13.FunLocFrame (ofString "rlp_header_len") := by
  refine ⟨_, _, _, lookup_rlp_header_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) funLocFrame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

theorem funLocFrame_rlp_list_header_len : M13.FunLocFrame (ofString "rlp_list_header_len") := by
  refine ⟨_, _, _, lookup_rlp_list_header_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_header_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact M13.locFrame_tailCall hcode funLocFrame_rlp_header_len _

theorem funLocFrame_rlp_word_encoded_len : M13.FunLocFrame (ofString "rlp_word_encoded_len") := by
  refine ⟨_, _, _, lookup_rlp_word_encoded_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_word_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_seq
  · exact M13.locFrameW_eval _ rfl s
  · intro m hm
    exact M13.locFrame_decCall (hm.code.trans hcode) funLocFrame_rlp_be_len _ _ _
      (fun t _ => M13.locFrameW_eval _ rfl t)

/-- `tx_u256_encoded_len` only reads locals and calls `u256_byte_length` (FunLocFrame). -/
theorem funLocFrame_tx_u256_encoded_len : M13.FunLocFrame (ofString "tx_u256_encoded_len") := by
  refine ⟨_, _, _, lookup_tx_u256_encoded_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_u256_encoded_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact M13.locFrame_decCall hcode M13.funLocFrame_u256_byte_length _ _ _
    (fun t _ => M13.locFrameW_eval _ rfl t)

/-- `access_list_payload_len` only calls `rlp_list_header_len` (FunLocFrame) in a while loop. -/
theorem funLocFrame_access_list_payload_len :
    M13.FunLocFrame (ofString "access_list_payload_len") := by
  refine ⟨_, _, _, lookup_access_list_payload_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_access_list_payload_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_seq
  · refine M13.locFrame_while _ ?_ _ hcode
    intro t htc
    apply M13.locFrame_dec; intro _
    apply M13.locFrame_decCall (by exact htc) funLocFrame_rlp_list_header_len _ _ _
    intro t1 hc1
    apply M13.locFrame_dec; intro _
    exact M13.locFrame_decCall (by exact hc1) funLocFrame_rlp_list_header_len _ _ _
      (fun t2 _ => M13.locFrameW_eval _ rfl t2)
  · intro _ _; exact M13.locFrameW_eval _ rfl _

/-- `auth_payload_len` calls `tx_u256_encoded_len` and `rlp_word_encoded_len` (FunLocFrame). -/
theorem funLocFrame_auth_payload_len : M13.FunLocFrame (ofString "auth_payload_len") := by
  refine ⟨_, _, _, lookup_auth_payload_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_auth_payload_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_decCall hcode funLocFrame_tx_u256_encoded_len _ _ _
  intro t1 hc1
  apply M13.locFrame_decCall hc1 funLocFrame_rlp_word_encoded_len _ _ _
  intro t2 hc2
  apply M13.locFrame_decCall hc2 funLocFrame_rlp_word_encoded_len _ _ _
  intro t3 hc3
  apply M13.locFrame_decCall hc3 funLocFrame_tx_u256_encoded_len _ _ _
  intro t4 hc4
  exact M13.locFrame_decCall hc4 funLocFrame_tx_u256_encoded_len _ _ _
    (fun t5 _ => M13.locFrameW_eval _ rfl t5)

/-- `auth_list_payload_len` calls `auth_payload_len` and `rlp_list_header_len` in a while loop. -/
theorem funLocFrame_auth_list_payload_len :
    M13.FunLocFrame (ofString "auth_list_payload_len") := by
  refine ⟨_, _, _, lookup_auth_list_payload_len, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_auth_list_payload_len,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_dec; intro _
  apply M13.locFrame_seq
  · refine M13.locFrame_while _ ?_ _ hcode
    intro t htc
    apply M13.locFrame_decCall htc funLocFrame_auth_payload_len _ _ _
    intro t1 hc1
    exact M13.locFrame_decCall hc1 funLocFrame_rlp_list_header_len _ _ _
      (fun t2 _ => M13.locFrameW_eval _ rfl t2)
  · intro _ _; exact M13.locFrameW_eval _ rfl _

/-- `tx_encode_bound` calls `access_list_payload_len` and `auth_list_payload_len` (FunLocFrame). -/
theorem funLocFrame_tx_encode_bound : M13.FunLocFrame (ofString "tx_encode_bound") := by
  refine ⟨_, _, _, lookup_tx_encode_bound, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_tx_encode_bound,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply M13.locFrame_decCall hcode funLocFrame_access_list_payload_len _ _ _
  intro t1 hc1
  apply M13.locFrame_decCall hc1 funLocFrame_auth_list_payload_len _ _ _
  intro t2 hc2
  apply M13.locFrame_dec
  intro _
  exact M13.locFrameW_eval _ rfl _

/-! ## Section 3: ByteFrame helpers for `u256_to_be_min` (local replicas of M13 private defs) -/

-- Local replicas of the private M13 `toBeMinLoopBody` / `toBeMinWhile` and their ByteFrame proofs.

/-! ### Local def replicas and helpers (must precede the theorems that use them) -/

private theorem txEnc_lookup_resVarEq_ne (m : HolFiniteMapExact MlS (ValueHOL 64))
    (k q : MlS) (old : Option (ValueHOL 64)) (hne : k ≠ q) :
    (m.resVarEq (k, old)).lookup q = m.lookup q := by
  unfold HolFiniteMapExact.resVarEq
  cases old with
  | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
  | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]

private def txEnc_toBeMinLoopBody : ProgHOL 64 :=
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

private def txEnc_toBeMinWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
    txEnc_toBeMinLoopBody

/-! ### Loop body / while ByteFrame proofs (replicas of private M13 proofs) -/

private theorem txEnc_toBeMinLoopBody_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hiv_lt : iv.toNat < len.toNat)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let res := evaluateHOLFiniteState s txEnc_toBeMinLoopBody
    M13.ByteFrame R s res.2 ∧
    res.1 ≠ some .continue ∧
    res.1 ≠ some .break ∧
    (res.1 = none →
      res.2.code = originalRuntimeCode ∧
      res.2.memaddrs = ordinaryDomain ∧
      res.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      res.2.locals.lookup (ofString "out") = outOpt ∧
      ∃ iv' : BitVec 64, res.2.locals.lookup (ofString "i") = some (.val (.word iv'))) := by
  dsimp only [txEnc_toBeMinLoopBody]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  let posv := (len - 1#64) - iv
  have hev_pos : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")]) =
      some (.val (.word posv)) := by
    simp [evalHOLExact, evalListHOLExact, hlen, hi, wordOpHOL, wordOp, valueIsWord, valueWord, posv]
  rw [hev_pos]; dsimp only
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word posv))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh1]; dsimp only
  set s1 := setVarHOLFinite (ofString "pos") (.val (.word posv)) s
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen,
      show ofString "pos" ≠ ofString "len" from M13.mls_ne rfl]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi,
      show ofString "pos" ≠ ofString "i" from M13.mls_ne rfl]
  have hs1_out : s1.locals.lookup (ofString "out") = outOpt := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "pos" ≠ ofString "out" from M13.mls_ne rfl]
  -- `decCall "l" .one "u256_limb" [...] cont`:
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, by simp, fun h => by simp at h⟩
  · rename_i values _
    split
    · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, by simp, fun h => by simp at h⟩
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "u256_limb")
        [(ofString "a", .comb [.one, .one, .one, .one]), (ofString "i", .one)]
        (sourceFnBody Guest.Software.guestFn_u256_limb) body' .one ret' values callee
        (by rw [show s1.code = originalRuntimeCode from hcode]; exact M13.lookup_u256_limb) hl
      subst hsame
      split
      · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.emptyLocals.locals _, by simp, by simp, fun h => by simp at h⟩
      · dsimp only
        have hlf_b : M13.LocFrame (callEntryStateHOLFinite s1 callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
              (sourceFnBody Guest.Software.guestFn_u256_limb)).2 :=
          M13.locFrameW_eval _ rfl _
        rcases hrun_l : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
            (sourceFnBody Guest.Software.guestFn_u256_limb) with ⟨rl, post_l⟩
        rw [hrun_l] at hlf_b
        have hbf_l : M13.ByteFrame R s post_l :=
          M13.ByteFrame.of_locFrame R (by unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl)
        rcases rl with _ | rl
        · exact ⟨hbf_l.locals _, by simp, by simp, fun h => by simp at h⟩
        · cases rl with
          | returned vl =>
            dsimp only
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "l") vl { post_l with locals := s1.locals }
              have hs2_bf : M13.ByteFrame R s s2 := (hbf_l.locals _).setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_len,
                  show ofString "l" ≠ ofString "len" from M13.mls_ne rfl]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
                  show ofString "l" ≠ ofString "i" from M13.mls_ne rfl]
              have hs2_out : s2.locals.lookup (ofString "out") = outOpt := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
                  show ofString "l" ≠ ofString "out" from M13.mls_ne rfl]
              -- `seq (storeByte ...) (assign "i" (i + 1))`:
              let sbProg : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hbf_sb : M13.ByteFrame R s2 (evaluateHOLFiniteState s2 sbProg).2 := by
                refine M13.byteFrame_storeByte s2 _ _ (fun addr hdst hdom => ?_)
                rcases hout_case : outOpt with _ | outVal
                · simp [evalHOLExact, evalListHOLExact, hs2_out, hout_case] at hdst
                · cases outVal with
                  | rStruct _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | nStruct _ _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | val wl =>
                    cases wl with
                    | word outW =>
                      have haddr_eq : addr = outW + iv := by
                        simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case,
                          wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        exact hdst.symm
                      subst haddr_eq
                      rw [hs2_dom] at hdom
                      have hsb_val : sourceBase = 2701131776 := rfl
                      have hnw := M13.add_no_wrap_of_memaddrs outW iv (by omega) hdom
                      exact ⟨(outW.toNat, 32), hR outW hout_case, by rw [hnw.2.1]; omega, by rw [hnw.2.1]; omega⟩
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hsb_run : evaluateHOLFiniteState s2 sbProg with ⟨rsb, s3⟩
              rw [hsb_run] at hbf_sb
              have hsb_ctrl := evaluate_storeByte_control_frame s2
                (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hsb_r : rsb = none ∨ rsb = some .error := by
                have h1 := hsb_ctrl.1; change (evaluateHOLFiniteState s2 sbProg).1 = _ ∨ (evaluateHOLFiniteState s2 sbProg).1 = _ at h1
                rw [hsb_run] at h1; exact h1
              have hs3_loc : s3.locals = s2.locals := by
                have h2 := hsb_ctrl.2.2.1; change (evaluateHOLFiniteState s2 sbProg).2.locals = s2.locals at h2
                rw [hsb_run] at h2; exact h2
              rcases hsb_r with rfl | rfl
              · dsimp only
                rw [evaluateHOLFiniteState_assign]
                have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                  rw [hs3_loc]; exact hs2_i
                have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word len)) := by
                  rw [hs3_loc]; exact hs2_len
                have hs3_out : s3.locals.lookup (ofString "out") = outOpt := by
                  rw [hs3_loc]; exact hs2_out
                have hev_inc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                    (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iv + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hev_inc]; dsimp only
                have hval_i : isValidValueHOLFinite s3 .local (ofString "i") (.val (.word (iv + 1#64))) = true := by
                  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_i, shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hval_i]; dsimp only
                have hbf_all : M13.ByteFrame R s (setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3) :=
                  (hs2_bf.trans hbf_sb).setVar _ _
                let finalSt :=
                  let __src2 := setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3
                  let __src1 : PanSemStateFiniteExact 64 F := { __src2 with locals := __src2.locals.resVarEq (ofString "l", s1.locals.lookup (ofString "l")) }
                  ({ __src1 with locals := __src1.locals.resVarEq (ofString "pos", s.locals.lookup (ofString "pos")) } : PanSemStateFiniteExact 64 F)
                have hbf_final : M13.ByteFrame R s finalSt := hbf_all.locals _ |>.locals _
                have hf_code : finalSt.code = originalRuntimeCode := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hcode
                have hf_dom : finalSt.memaddrs = ordinaryDomain := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hdom_eq
                refine ⟨hbf_final, by simp, by simp, fun _ => ⟨hf_code, hf_dom, ?_, ?_, iv + 1#64, ?_⟩⟩
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "len") = _
                  rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl), txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                    show ofString "i" ≠ ofString "len" from M13.mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "out") = _
                  rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl), txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
                    show ofString "i" ≠ ofString "out" from M13.mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "i") = _
                  rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl), txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · exact ⟨(hs2_bf.trans hbf_sb).locals _ |>.locals _, by simp, by simp, fun h => by simp at h⟩
            · exact ⟨hbf_l.locals _, by simp, by simp, fun h => by simp at h⟩
          | «break» => exact ⟨hbf_l.locals _, by simp, by simp, fun h => by simp at h⟩
          | «continue» => exact ⟨hbf_l.locals _, by simp, by simp, fun h => by simp at h⟩
          | _ => exact ⟨hbf_l.emptyLocals.locals _, by simp, by simp, fun h => by simp at h⟩

private theorem txEnc_toBeMinWhile_byteFrame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let post := (evaluateHOLFiniteState s txEnc_toBeMinWhile)
    M13.ByteFrame R s post.2 ∧
    (post.1 = none →
      post.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      post.2.locals.lookup (ofString "out") = outOpt) := by
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "len") = some (.val (.word len)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      st.locals.lookup (ofString "out") = outOpt →
      let post := (evaluateHOLFiniteState st txEnc_toBeMinWhile)
      M13.ByteFrame R st post.2 ∧
      (post.1 = none →
        post.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
        post.2.locals.lookup (ofString "out") = outOpt) by
    exact hrec s.clock s iv rfl hcode hdom_eq hlen hi hout
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hst_dom hst_len hst_i hst_out
    dsimp only [txEnc_toBeMinWhile]
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact]
    have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
        some (.val (.word (if w.toNat < len.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hst_i, hst_len, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
    rw [hevc]; dsimp only
    by_cases hlt_w : w.toNat < len.toNat
    · rw [if_pos hlt_w]
      have h1 : (1 : BitVec 64) ≠ 0 := by intro h; cases h
      rw [if_pos h1]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]
        exact ⟨(M13.ByteFrame.refl R st).emptyLocals, fun h => by simp at h⟩
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hstep := txEnc_toBeMinLoopBody_step (decClockHOLFinite st) R len w outOpt
          hst_code hst_dom hlt_w hlen_le hst_len hst_i hst_out hR
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) txEnc_toBeMinLoopBody
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) txEnc_toBeMinLoopBody with ⟨rb, mid⟩
        rw [hbr] at hstep hcle; dsimp only at hstep hcle
        have hclk_lt : mid.clock < clk := by change mid.clock ≤ st.clock - 1 at hcle; omega
        have hbf1 : M13.ByteFrame R st mid :=
          (M13.ByteFrame.of_locFrame R (s := st) (t := decClockHOLFinite st) rfl).trans hstep.1
        cases rb with
        | none =>
          obtain ⟨hm_code, hm_dom, hm_len, hm_out, w', hm_i⟩ := hstep.2.2.2 rfl
          obtain ⟨hih_bf, hih_cond⟩ :=
            ih mid.clock hclk_lt mid w' rfl hm_code hm_dom hm_len hm_i hm_out
          exact ⟨hbf1.trans hih_bf, hih_cond⟩
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hstep.2.1
          | «break» => exact absurd rfl hstep.2.2.1
          | _ => refine ⟨hbf1, fun h => ?_⟩; exact absurd h (by simp)
    · rw [if_neg hlt_w]
      have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
      rw [if_neg h0]
      exact ⟨M13.ByteFrame.refl R st, fun _ => ⟨hst_len, hst_out⟩⟩



/-- Convert `M13.ByteFrame Rl s post` to `HeapByteEff s post Rl gw`.
    Works because ByteFrame keeps globals unchanged (so hp_le is trivial). -/
private theorem heapByteEff_of_m13_byteFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (hbf : M13.ByteFrame Rl s post) :
    HeapByteEff s post Rl gw := by
  have hst_eq : post = { s with memory := post.memory, locals := post.locals, clock := post.clock } :=
    hbf.1
  have hg_eq : post.globals = s.globals := by rw [hst_eq]
  have hma_eq : post.memaddrs = s.memaddrs := by rw [hst_eq]
  have hbe_eq : post.be = s.be := by rw [hst_eq]
  have hcode_eq : post.code = s.code := by rw [hst_eq]
  have hAR_post : ArenaReady post :=
    ⟨guestInv_congr hcode_eq hma_eq (by rw [hst_eq]) (by rw [hst_eq]) hAR.1,
     arenaOK_congr hg_eq hAR.2⟩
  refine ⟨hAR_post, hma_eq, by simp [globN, hg_eq], by simp [globN, hg_eq],
    by simp [globN, hg_eq], hbe_eq, fun k _ => by rw [hg_eq],
    fun a hne => (hbf.2.1 a hne).1, ?_, fun b hb hne => Or.inl (hbf.2.2 b hb hne)⟩
  -- cell_frame: post.memory a ≠ s.memory a → ∃ i ∈ Rl, CellHitsPos a.toNat i
  -- We use byte_frame + mem_eq_of_bytes_eq: if no region covers a.toNat..a.toNat+8,
  -- then all bytes of a are unchanged, so the word is unchanged — contradiction.
  intro a hne; left
  have hdom : ordinaryDomain a := by
    rw [← hAR.1.memaddrs]; exact (hbf.2.1 a hne).1
  have ha_ord := (ordinaryDomain_iff a).1 hdom
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
  by_contra hno
  apply hne
  apply mem_eq_of_bytes_eq hbe_eq a hdom
  intro k hk
  by_contra hb_ne
  obtain ⟨i, hi, hin⟩ := hbf.2.2 (a.toNat + k) (by omega) hb_ne
  exact hno ⟨i, hi, ⟨by exact Nat.pos_of_ne_zero (fun h => by simp [h, InIvl] at hin; omega),
    by simp only [CellHits]; simp only [InIvl] at hin; omega⟩⟩

private theorem txEnc_heapByteEff_of_dec_word {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64} {w : BitVec 64}
    {body : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.dec x .one e body)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev]; dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh]
  exact hb.locals_clock _ (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2.clock

private theorem txEnc_heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]; exact hb

private theorem txEnc_heapByteEff_of_seq_some {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64}
    {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (some r, m))
    (hm : HeapByteEff s0 m Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]; exact hm

private theorem txEnc_heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]; exact hq.locals_clock L q.clock

/-- Byte-region validity: all bytes in `[ptr, ptr+len)` are in the ordinary domain. -/
def BytesOK {F : Type} (_s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  i.1 + i.2 ≤ heapEnd ∧ i.1 < heapEnd

/-- Extended validity condition for `encode_transaction` / `tx_encode_generic`. -/
def TxValidEncodeAt {F : Type} (s : PanSemStateFiniteExact 64 F) (tx : Nat) : Prop :=
  TxValidAt s tx ∧
  (memW s (tx + 152) ≠ 0 →
    BytesOK s (memW s (tx + 152), 20) ∧ Disj (memW s (tx + 152), 20) (heapFree s)) ∧
  BytesOK s (memW s (tx + 192), memW s (tx + 200)) ∧
  Disj (memW s (tx + 192), memW s (tx + 200)) (heapFree s) ∧
  (0 < memW s (tx + 216) →
    Inside (memW s (tx + 208), 24 * memW s (tx + 216)) sourceBase (globN s "heap_ptr") ∧
    ∀ i < memW s (tx + 216),
      let alRec := memW s (tx + 208) + 24 * i
      BytesOK s (memW s alRec, 20) ∧ Disj (memW s alRec, 20) (heapFree s) ∧
      (0 < memW s (alRec + 16) →
        Inside (memW s (alRec + 8), 32 * memW s (alRec + 16)) sourceBase (globN s "heap_ptr") ∧
        WordsOK s (memW s (alRec + 8), 32 * memW s (alRec + 16)))) ∧
  (memW s tx = 3 ∧ 0 < memW s (tx + 264) →
    Inside (memW s (tx + 256), 32 * memW s (tx + 264)) sourceBase (globN s "heap_ptr") ∧
    WordsOK s (memW s (tx + 256), 32 * memW s (tx + 264))) ∧
  (memW s tx = 4 ∧ 0 < memW s (tx + 280) →
    Inside (memW s (tx + 272), 120 * memW s (tx + 280)) sourceBase (globN s "heap_ptr") ∧
    ∀ i < memW s (tx + 280),
      let authRec := memW s (tx + 272) + 120 * i
      BytesOK s (memW s (authRec + 32), 20) ∧ Disj (memW s (authRec + 32), 20) (heapFree s))

/-- Entry condition for `wk_encode_transaction_strong`. -/
def TxValidEncodeReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxValidEncodeAt s (locN s "tx")

/-! ## Section 4: Lookup helper for mixed-shape `tx_put_u256` -/

/-- Mixed-shape lookup: dst:.one, v:.comb [.one,.one,.one,.one] -/
private theorem txEnc_bound_cursor_slack
    (buf data_n al au bh p : Nat)
    (hp : p ≤ buf + 360 + data_n + al + au + bh) :
    p + 295 ≤ buf + (64 + 17 * 33 + 30 + data_n + al + au + bh) := by
  omega

private theorem pan_word_comb4_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name dst_nm v_nm : MlS) (body : ProgHOL width)
    (dst : BitVec width) (v0 v1 v2 v3 : BitVec width)
    (different : dst_nm ≠ v_nm)
    (lookup : code name = some ([(dst_nm, .one), (v_nm, .comb [.one, .one, .one, .one])], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
        [.val (.word dst), .rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]] =
      some (body,
        (HolFiniteMapExact.empty.update (dst_nm, .val (.word dst))).update
          (v_nm, .rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]),
        .one) := by
  have hshape_comb : shapeEqHOL (.comb [.one, .one, .one, .one])
      (shapeOfHOLExact (.rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)] : ValueHOL width)) = true := by
    rw [(shapeEqHOL_eq_true _ _).2]
    simp only [shapeOfHOLExact, List.map]
  have raw : lookupCodeHOLExact code name
      [.val (.word dst), .rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)]] =
      some (body, (fun key =>
        if key = v_nm then some (.rStruct [.val (.word v0), .val (.word v1), .val (.word v2), .val (.word v3)])
        else if key = dst_nm then some (.val (.word dst)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, different, hshape_comb]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext; funext key
    by_cases hv : key = v_nm
    · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have hbv := Ne.symm hv
      by_cases hd : key = dst_nm
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, different, Ne.symm different, hv]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd, hv, Ne.symm hd, hbv]

/-- Mixed-shape lookup: a:.comb [.one,.one,.one,.one], out:.one → body, .one -/
private theorem pan_comb4_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name a_nm out_nm : MlS) (body : ProgHOL width)
    (a0 a1 a2 a3 : BitVec width) (out : BitVec width)
    (different : a_nm ≠ out_nm)
    (lookup : code name = some ([(a_nm, .comb [.one, .one, .one, .one]), (out_nm, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
        [.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)], .val (.word out)] =
      some (body,
        (HolFiniteMapExact.empty.update (a_nm, .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])).update
          (out_nm, .val (.word out)),
        .one) := by
  have hshape_comb : shapeEqHOL (.comb [.one, .one, .one, .one])
      (shapeOfHOLExact (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)] : ValueHOL width)) = true := by
    rw [(shapeEqHOL_eq_true _ _).2]; simp only [shapeOfHOLExact, List.map]
  have raw : lookupCodeHOLExact code name
      [.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)], .val (.word out)] =
      some (body, (fun key =>
        if key = out_nm then some (.val (.word out))
        else if key = a_nm then some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, different, hshape_comb]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext; funext key
    by_cases ho : key = out_nm
    · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · by_cases ha : key = a_nm
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
          different, Ne.symm different, ho]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ho, ha, Ne.symm ho, Ne.symm ha]

/-! ## Section 5: General while-loop HeapByteEff and sub-function helpers -/

/-- If `HeapByteEff s0 s Rl gw` and each body step preserves this, then
    `HeapByteEff s0 (eval s (.while cond body)).2 Rl gw`. -/
private theorem txEnc_heapByteEff_while {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (body : ProgHOL 64)
    (Rl : List Ivl) (gw : List String)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hb : ∀ t : PanSemStateFiniteExact 64 F,
      HeapByteEff s0 t Rl gw →
      HeapByteEff s0 (evaluateHOLFiniteState t body).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.while cond body)).2 Rl gw := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact heff0.locals_clock _ _
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hpre : HeapByteEff s0 (decClockHOLFinite s) Rl gw :=
          heff0.locals_clock (decClockHOLFinite s).locals (decClockHOLFinite s).clock
        have hpost := hb (decClockHOLFinite s) hpre
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
        rw [hbr] at hpost hrem; dsimp only at hpost hrem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at hrem; omega
        cases r1 with
        | none =>
          exact txEnc_heapByteEff_while s0 mid cond body Rl gw hpost hb
        | some res =>
          cases res with
          | «continue» =>
            exact txEnc_heapByteEff_while s0 mid cond body Rl gw hpost hb
          | _ => exact hpost
    · exact heff0
  · exact heff0
termination_by s.clock

/-- `HeapByteEff` for a `call (some (some lname, none)) fn args` that returns `none`:
    derive from equality proof. -/
private theorem txEnc_heapByteEff_of_call_local_eq_none {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F}
    {lname fn : MlS} {args : List (ExpHOL 64)}
    {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s (.call (some (some (VarKind.local, lname), none)) fn args) =
        (none, post))
    (hpost : HeapByteEff s0 post Rl gw) :
    HeapByteEff s0
        (evaluateHOLFiniteState s (.call (some (some (VarKind.local, lname), none)) fn args)).2
        Rl gw := by
  rw [heq]; exact hpost

/-- `HeapByteEff` for a `call (some (none, none)) fn args` that returns a result:
    derive from equality proof. -/
private theorem txEnc_heapByteEff_of_call_none_eq {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)}
    {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, post))
    (hpost : HeapByteEff s0 post Rl gw) :
    HeapByteEff s0
        (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2
        Rl gw := by
  rw [heq]; exact hpost

/-! ## Section 6: `wk_encode_transaction_strong` helpers -/

/-- Prove that evaluating the body of `u256_to_be_min` with `out = out_ptr` gives an
    `M13.ByteFrame [(out_ptr.toNat, 32)] ent post`. -/
private theorem txEnc_u256_to_be_min_byteFrame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (out_ptr : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hR : (out_ptr.toNat, 32) ∈ R)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out_ptr))) :
    M13.ByteFrame R s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_to_be_min)).2 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact M13.ByteFrame.refl R s
  · rename_i values _
    split
    · exact M13.ByteFrame.refl R s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_byte_length")
        [(ofString "a", .comb [.one, .one, .one, .one])]
        (sourceFnBody Guest.Software.guestFn_u256_byte_length) body' .one ret' values callee
        (by rw [hcode]; exact M13.lookup_u256_byte_length) hl
      subst hsame
      split
      · exact (M13.ByteFrame.refl R s).emptyLocals
      · dsimp only
        have hlf_bl := M13.locFrame_u256_byte_length_body (callEntryStateHOLFinite s callee) hcode
        rcases hrun_bl : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_u256_byte_length) with ⟨rbl, post_bl⟩
        rw [hrun_bl] at hlf_bl
        have hbf_bl : M13.ByteFrame R s post_bl :=
          M13.ByteFrame.of_locFrame R (by unfold M13.LocFrame at hlf_bl ⊢; dsimp only at hlf_bl; rw [hlf_bl]; rfl)
        rcases rbl with _ | rbl
        · exact hbf_bl
        · cases rbl with
          | returned vbl =>
            obtain ⟨len, rfl, hlen_le⟩ := M13.u256_byte_length_body_le_32
              (callEntryStateHOLFinite s callee) hcode vbl (by rw [hrun_bl])
            dsimp only
            split
            · dsimp only
              set s1 := setVarHOLFinite (ofString "len") (.val (.word len)) { post_bl with locals := s.locals }
              have hs1_bf : M13.ByteFrame R s s1 := (hbf_bl.locals _).setVar _ _
              rw [evaluateHOLFiniteState_dec_total]; dsimp only
              have h0_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                  (.const 0#64) = some (.val (.word 0#64)) := rfl
              rw [h0_ev]; dsimp only
              have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
                simp [shapeEqHOL, shapeOfHOLExact]
              rw [if_pos hsh0]; dsimp only
              set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
              have hs2_bf : M13.ByteFrame R s s2 := hs1_bf.setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "len" from M13.mls_ne rfl]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hs2_out : s2.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "out" from M13.mls_ne rfl,
                  show ofString "len" ≠ ofString "out" from M13.mls_ne rfl]
              have hR_mem : ∀ outW : BitVec 64,
                  s.locals.lookup (ofString "out") = some (.val (.word outW)) →
                  (outW.toNat, 32) ∈ R := by
                intro outW houtW; rw [hout] at houtW
                have heq : outW = out_ptr := by
                  have h1 : (.val (.word out_ptr) : ValueHOL 64) = .val (.word outW) := Option.some.inj houtW
                  have h2 : (.word out_ptr : HolWordLab 64) = .word outW := ValueHOL.val.inj h1
                  exact (HolWordLab.word.inj h2).symm
                subst heq; exact hR
              obtain ⟨hw_bf, hw_cond⟩ := txEnc_toBeMinWhile_byteFrame s2 R len 0#64
                (s.locals.lookup (ofString "out")) hs2_code hs2_dom hlen_le hs2_len hs2_i hs2_out hR_mem
              rcases hw_run : evaluateHOLFiniteState s2 txEnc_toBeMinWhile with ⟨rw_res, s3⟩
              rw [hw_run] at hw_bf hw_cond
              -- Unfold the while and loop-body defs in hw_run so we can rewrite the goal (which has inlined forms)
              unfold txEnc_toBeMinWhile txEnc_toBeMinLoopBody at hw_run
              rw [evaluateHOLFiniteState_seq_line780, hw_run]
              cases rw_res with
              | some _ =>
                -- Locals are restored by dec/decCall after the while; each .locals _ handles one resVarEq
                exact (hs2_bf.trans hw_bf).locals _ |>.locals _
              | none =>
                -- After while exits with none, `return "len"` only changes locals/clock (LocFrame).
                exact (hs2_bf.trans (hw_bf.trans (M13.ByteFrame.of_locFrame R
                  (M13.locFrameW_eval (.return (.var .local (ofString "len"))) rfl s3)))).locals _ |>.locals _
            · exact hbf_bl.locals _
          | «break» => exact hbf_bl.locals _
          | «continue» => exact hbf_bl.locals _
          | _ => exact hbf_bl.emptyLocals.locals _


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
    (by rw [hcode]; exact lookup_rlp_encode_list_header)
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
      (by rw [hcode]; exact lookup_rlp_encode_bytes)
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
            have hhe := hdst_lt; rw [heapEnd_val] at hhe
            rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
            have hhe := hdst_lt; rw [heapEnd_val] at hhe; omega
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
    (by rw [hcode]; exact lookup_rlp_encode_word)
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
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
    have haddr_nat : (out0 + iv).toNat = out0.toNat + iv.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hdom_addr : s2.memaddrs (panByteAlignHOL (out0 + iv)) := by
      rw [hs2_dom, ordinaryDomain_iff]
      have hal := panByteAlign_toNat64 (out0 + iv)
      have hsb_mod : sourceBase % 8 = 0 := by rw [sourceBase_val]
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
    (by decide) (by rw [hcode]; exact M13.lookup_u256_to_be_min)
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
    (by rw [hcode]; exact lookup_rlp_encode_bytes)
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
      rw [hent_ma, hsrc_align, ordinaryDomain_iff]
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
      exact False.elim (not_resumes_error hres)

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
    (by rw [hcode]; exact lookup_rlp_encode_bytes)
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
        obtain ⟨hret_wh, hnonret_wh⟩ := eval_rlp_write_header_body_exact ent_wh dst0 128 n0 Rl
          ht_code ht_ma hwh_dst hwh_base hwh_n
          (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
          (by rw [hwh]; exact hnt_wh)
        simp only [hwh] at hret_wh hnonret_wh hnt_t ⊢
        cases rwh with
        | none => exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
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
            have hbnd := rlpHeaderLenPure_bounds n0.toNat
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
              have hhe := hdst_lt; rw [heapEnd_val] at hhe
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
                have hhe_val : heapEnd = 33806089704 := heapEnd_val
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
            exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact not_resumes_error⟩
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
          rw [hent_ma, hsrc_align, ordinaryDomain_iff]
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
    | none => exact False.elim (not_resumes_error hres)
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
        exact False.elim (not_resumes_error hres)
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
    eval_decCall_heap_mark s "mark" _ Rl gw hcode hAR hnt
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
    eval_decCall_alloc_resumes s1 "tmp" (.const 32#64) _ Rl gw
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
    rw [heapLimit_val, heapEnd_val]; decide
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
    heapByteEff_of_m13_byteFrame heff2.arena hbf3
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
          rlpHeaderLenPure_of_le55 (by omega)
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
  have hhr := eval_call_heap_release s4 (.var .local (ofString "mark")) mark Rl gw
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
      | none => simp only [hrun] at hres; exact False.elim (not_resumes_error hres)
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
          simp only [hrun] at hres; exact False.elim (not_resumes_error hres)
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
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
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
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩


private theorem txEnc_mem_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private theorem txEnc_mem_eq_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    {base len : Nat} (hins : Inside (base, len) sourceBase (globN s0 "heap_ptr"))
    (addr : Nat) (haddr8 : addr % 8 = 0)
    (_hlo : base ≤ addr) (hhi : addr + 8 ≤ base + len) :
    st.memory (BitVec.ofNat 64 addr) = s0.memory (BitVec.ofNat 64 addr) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  obtain ⟨hb_lo, hb_hi⟩ := hins
  dsimp only at hb_lo hb_hi
  have haddr_lt : addr < 2 ^ 64 := by omega
  have ha_nat : (BitVec.ofNat 64 addr).toNat = addr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt haddr_lt
  by_contra hne
  have hsep : heapLimit = scratchStart := rfl
  have hhp8 : globN s0 "heap_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.1
  have hfp8 : globN s0 "frame_mem_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.1
  have hfp_lo : scratchStart ≤ globN s0 "frame_mem_ptr" := hAR0.2.2.2.1
  rcases heff.cell_frame (BitVec.ofNat 64 addr) hne with
    ⟨i, hi, hipos, hc1, hc2⟩ | ⟨_, g1, _⟩ | ⟨_, f1, _⟩
  · have := hRl_ge i hi hipos
    rw [ha_nat] at hc1 hc2; omega
  · unfold freeGap at g1; dsimp only at g1; rw [ha_nat] at g1; omega
  · unfold heapFree at f1; dsimp only at f1; rw [ha_nat] at f1; omega

private theorem txEnc_wordAt_memW_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    {base len : Nat} (hins : Inside (base, len) sourceBase (globN s0 "heap_ptr"))
    (hwok : WordsOK s0 (base, len))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ len) :
    WordAt st (base + off) ∧ memW st (base + off) = memW s0 (base + off) := by
  have hk : off / 8 < len / 8 := by omega
  have hwa0 : WordAt s0 (base + off) := by
    have h := hwok.2.2 (off / 8) hk
    have heq : base + 8 * (off / 8) = base + off := by omega
    rwa [heq] at h
  have hmeq := txEnc_mem_eq_below_hp hAR0 heff hRl_ge hins (base + off)
    (by have := hwok.1; omega) (by omega) (by omega)
  obtain ⟨w, hdom0, hmem0⟩ := hwa0
  refine ⟨⟨w, by rw [heff.memaddrs]; exact hdom0, by rw [hmeq]; exact hmem0⟩, ?_⟩
  unfold memW; rw [hmeq]

private theorem txEnc_wordsOK_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    {base len : Nat} (hins : Inside (base, len) sourceBase (globN s0 "heap_ptr"))
    (hwok : WordsOK s0 (base, len)) :
    WordsOK st (base, len) := by
  refine ⟨hwok.1, hwok.2.1, ?_⟩
  intro k hk
  exact (txEnc_wordAt_memW_below_hp hAR0 heff hRl_ge hins hwok (8 * k)
    (by omega) (by omega)).1

private theorem txEnc_eval_load_word_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    {bw : BitVec 64} {len : Nat}
    (hins : Inside (bw.toNat, len) sourceBase (globN s0 "heap_ptr"))
    (hwok : WordsOK s0 (bw.toNat, len))
    (nm : String) (hst_nm : st.locals.lookup (ofString nm) = some (.val (.word bw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ len) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s0 (bw.toNat + off))))) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hb_hi := hins.2
  dsimp only at hb_hi
  obtain ⟨hwa_st, hmw_eq⟩ := txEnc_wordAt_memW_below_hp hAR0 heff hRl_ge hins hwok off hoff8 hoff_hi
  have hadd : bw + BitVec.ofNat 64 off = BitVec.ofNat 64 (bw.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (bw.toNat + off)))) := by
    simp [evalHOLExact, evalListHOLExact, hst_nm, valueIsWord, valueWord, wordOpHOL, wordOp, hadd]
  have ha_nat : (BitVec.ofNat 64 (bw.toNat + off)).toNat = bw.toNat + off := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hev := txEnc_mem_load_one_word st _ (BitVec.ofNat 64 (bw.toNat + off)) haddr
    (by rw [ha_nat]; exact hwa_st)
  rw [ha_nat, hmw_eq] at hev
  exact hev

private theorem txEnc_eval_load_u256_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    {bw : BitVec 64} {len : Nat}
    (hins : Inside (bw.toNat, len) sourceBase (globN s0 "heap_ptr"))
    (hwok : WordsOK s0 (bw.toNat, len))
    (nm : String) (hst_nm : st.locals.lookup (ofString nm) = some (.val (.word bw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ len) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load (.comb [.one, .one, .one, .one])
        (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)])) =
      some (.rStruct [
        .val (.word (BitVec.ofNat 64 (memW s0 (bw.toNat + off)))),
        .val (.word (BitVec.ofNat 64 (memW s0 (bw.toNat + off + 8)))),
        .val (.word (BitVec.ofNat 64 (memW s0 (bw.toNat + off + 16)))),
        .val (.word (BitVec.ofNat 64 (memW s0 (bw.toNat + off + 24))))]) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hb_hi := hins.2
  dsimp only at hb_hi
  have hwa_at : ∀ j : Nat, j < 4 →
      WordAt st (bw.toNat + (off + 8 * j)) ∧
      memW st (bw.toNat + (off + 8 * j)) = memW s0 (bw.toNat + (off + 8 * j)) := by
    intro j hj
    exact txEnc_wordAt_memW_below_hp hAR0 heff hRl_ge hins hwok (off + 8 * j) (by omega) (by omega)
  obtain ⟨⟨w0, hdom0, hmem0⟩, hmw0⟩ := hwa_at 0 (by omega)
  obtain ⟨⟨w1, hdom1, hmem1⟩, hmw1⟩ := hwa_at 1 (by omega)
  obtain ⟨⟨w2, hdom2, hmem2⟩, hmw2⟩ := hwa_at 2 (by omega)
  obtain ⟨⟨w3, hdom3, hmem3⟩, hmw3⟩ := hwa_at 3 (by omega)
  let base : BitVec 64 := BitVec.ofNat 64 (bw.toNat + off)
  have hadd : bw + BitVec.ofNat 64 off = base := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb0 : BitVec.ofNat 64 (bw.toNat + (off + 8 * 0)) = base := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_ofNat]; omega
  have hb8 : base + 8#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb16 : base + 16#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 2)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb24 : base + 24#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 3)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hd0 : st.memaddrs base := by rw [← hb0]; exact hdom0
  have hd1 : st.memaddrs (base + 8#64) := by rw [hb8]; exact hdom1
  have hd2 : st.memaddrs (base + 16#64) := by rw [hb16]; exact hdom2
  have hd3 : st.memaddrs (base + 24#64) := by rw [hb24]; exact hdom3
  have hv0 : st.memory base = .word w0 := by rw [← hb0]; exact hmem0
  have hv1 : st.memory (base + 8#64) = .word w1 := by rw [hb8]; exact hmem1
  have hv2 : st.memory (base + 16#64) = .word w2 := by rw [hb16]; exact hmem2
  have hv3 : st.memory (base + 24#64) = .word w3 := by rw [hb24]; exact hmem3
  have hw0_eq : BitVec.ofNat 64 (memW s0 (bw.toNat + off)) = w0 := by
    have h0 : bw.toNat + off = bw.toNat + (off + 8 * 0) := by omega
    rw [h0, ← hmw0]; unfold memW; rw [hmem0]; simp
  have hw1_eq : BitVec.ofNat 64 (memW s0 (bw.toNat + off + 8)) = w1 := by
    have h1 : bw.toNat + off + 8 = bw.toNat + (off + 8 * 1) := by omega
    rw [h1, ← hmw1]; unfold memW; rw [hmem1]; simp
  have hw2_eq : BitVec.ofNat 64 (memW s0 (bw.toNat + off + 16)) = w2 := by
    have h2 : bw.toNat + off + 16 = bw.toNat + (off + 8 * 2) := by omega
    rw [h2, ← hmw2]; unfold memW; rw [hmem2]; simp
  have hw3_eq : BitVec.ofNat 64 (memW s0 (bw.toNat + off + 24)) = w3 := by
    have h3 : bw.toNat + off + 24 = bw.toNat + (off + 8 * 3) := by omega
    rw [h3, ← hmw3]; unfold memW; rw [hmem3]; simp
  rw [hw0_eq, hw1_eq, hw2_eq, hw3_eq]
  simp [evalHOLExact, evalListHOLExact, hst_nm, valueIsWord, valueWord, wordOpHOL, wordOp,
    isWfShapeExactHOL, memLoadHOLExact, memLoadsHOLExact, sizeOfShapeWithContextHOL,
    bytesInWordHOL, BitVec.add_assoc, hadd, hd0, hd1, hd2, hd3, hv0, hv1, hv2, hv3]

private theorem eval_call_local_rlp_encode_bytes_n_ne_one {F : Type}
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
    (hne1 : n0 ≠ 1)
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
    (by rw [hcode]; exact lookup_rlp_encode_bytes)
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
        let out_b := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
        (∀ rv, out_b.1 = some (.returned rv) →
          ∃ len : BitVec 64, rv = .val (.word len) ∧
            len.toNat = rlpHeaderLenPure n0.toNat + n0.toNat ∧
            dst0.toNat < heapEnd ∧ M11.ByteRegionEffect ent out_b.2 Rl) ∧
        (∀ r, out_b.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
      dsimp only
      have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 ≠ some .timeOut := by
        rcases heb_nt : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb_nt, _⟩
        rintro rfl
        simp [heb_nt] at hnt
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_ent ⊢
      have hev_n1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
          some (.val (.word (if n0 = 1 then 1 else 0))) := by
        simp [evalHOLExact, hent_n, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_n1, if_neg hne1] at hnt_ent ⊢
      dsimp only at hnt_ent ⊢
      rw [if_pos rfl, evaluateHOLFiniteState_skip] at hnt_ent ⊢
      dsimp only at hnt_ent ⊢
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_ent ⊢
      have ha_t : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
          some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_n]
      have hent_code : ent.code = originalRuntimeCode := hcode
      have hent_ma : ent.memaddrs = ordinaryDomain := hma
      have hlk_wh := pan_three_word_lookup ent.code.lookup (ofString "rlp_write_header")
        (ofString "dst") (ofString "base") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
        (by decide) (by decide) (by decide)
        (by rw [hent_code]; exact M11.lookup_rlp_write_header)
      simp only [ha_t, hlk_wh] at hnt_ent ⊢
      by_cases hcz_t : ent.clock = 0
      · simp [hcz_t] at hnt_ent
      · simp only [hcz_t, ↓reduceIte] at hnt_ent ⊢
        set cmap_wh := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
          (ofString "base", ValueHOL.val (.word 128))).update (ofString "n", ValueHOL.val (.word n0))
        set ent_wh := callEntryStateHOLFinite ent cmap_wh
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
          rintro rfl; simp only [hwh] at hnt_ent; exact hnt_ent rfl
        obtain ⟨hret_wh, hnonret_wh⟩ := eval_rlp_write_header_body_exact ent_wh dst0 128 n0 Rl
          hent_code hent_ma hwh_dst hwh_base hwh_n
          (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
          (by rw [hwh]; exact hnt_wh)
        rw [hwh] at hret_wh hnonret_wh; dsimp only at hret_wh hnonret_wh
        simp only [hwh] at hnt_ent ⊢
        cases rwh with
        | none =>
          dsimp only
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
        | some r =>
          cases r with
          | timeOut => exact absurd rfl hnt_wh
          | exception eid ev =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ => by
              injection hr' with hr''; subst hr''
              exact hnonret_wh (.exception eid ev) rfl (fun _ h => by cases h)⟩
          | returned rv =>
            obtain ⟨rfl, hdst_lt, heff_wh⟩ := hret_wh rv rfl
            set h := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
            have hbnd := rlpHeaderLenPure_bounds n0.toNat
            have hh_nat : h.toNat = rlpHeaderLenPure n0.toNat := by
              dsimp [h]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            have hsh_h : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            dsimp only at hnt_ent ⊢
            rw [if_pos hsh_h] at hnt_ent ⊢; dsimp only at hnt_ent ⊢
            set mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := ent.locals }
            have heff_mid : M11.ByteRegionEffect ent mid Rl :=
              (((M11.ByteRegionEffect.refl ent Rl).with_locals_clock ent_wh.locals ent_wh.clock).trans
                heff_wh).with_locals_clock mid.locals mid.clock
            have hmid_code : mid.code = originalRuntimeCode := heff_mid.code.trans hent_code
            have hmid_ma : mid.memaddrs = ordinaryDomain := heff_mid.memaddrs.trans hent_ma
            have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
                show ofString "h" ≠ ofString "dst" by decide]
            have hmid_src : mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_src,
                show ofString "h" ≠ ofString "src" by decide]
            have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
                show ofString "h" ≠ ofString "n" by decide]
            rw [evaluateHOLFiniteState_seq_line780] at hnt_ent ⊢
            rcases hc_mc : evaluateHOLFiniteState mid
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                   .var .local (ofString "src"),
                   .var .local (ofString "n")]) with ⟨rmc, smc⟩
            have hnt_mc : rmc ≠ some .timeOut := by
              rintro rfl; simp only [hc_mc] at hnt_ent; exact hnt_ent rfl
            have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
            have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat := by
              have hhe_val : heapEnd = 33806089704 := heapEnd_val
              rw [BitVec.toNat_add, hh_nat]; exact Nat.mod_eq_of_lt (by obtain ⟨_, _, _, _⟩ := hin_ivl; omega)
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
            dsimp only at hmc; simp only [hc_mc] at hmc hnt_ent ⊢
            cases rmc with
            | some r' =>
              dsimp only
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
              have hn0_lt : rlpHeaderLenPure n0.toNat + n0.toNat < 2 ^ 64 := by
                obtain ⟨_, _, _, _⟩ := hin_ivl
                have hhe_val : heapEnd = 33806089704 := heapEnd_val
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
                  ((heff_mid.trans heff_mc).with_locals_clock _ _).with_locals_clock _ _⟩
              · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
          | «break» | «continue» | error =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact not_resumes_error⟩
          | finalFfi _ =>
            dsimp only
            exact ⟨fun _ h => by simp at h, fun r' hr' _ hr => by
              injection hr' with hr''; subst hr''
              rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    obtain ⟨hret, hnonret⟩ := hbody
    rw [heb] at hret hnonret
    dsimp only at hret hnonret
    simp only [heb] at hnt ⊢
    cases reb with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt
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
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private def accessSlotEntryPayloadPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) : Nat :=
  let ns := memW s0 (recs + 24 * i + 16)
  let inner := 33 * ns
  21 + rlpHeaderLenPure inner + inner

private def accessSlotEntryTotalPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) : Nat :=
  let entry := accessSlotEntryPayloadPure s0 recs i
  rlpHeaderLenPure entry + entry

private def accessListPayloadSumPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (recs n : Nat) : Nat :=
  ((List.range n).map (fun i => accessSlotEntryTotalPure s0 recs i)).sum

private theorem accessSlotEntryPayloadPure_bound {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) :
    accessSlotEntryPayloadPure s0 recs i ≤ 30 + 33 * memW s0 (recs + 24 * i + 16) := by
  dsimp only [accessSlotEntryPayloadPure]
  have h1 := (rlpHeaderLenPure_bounds (33 * memW s0 (recs + 24 * i + 16))).2
  omega

private theorem accessSlotEntryTotalPure_bound {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) :
    accessSlotEntryTotalPure s0 recs i ≤ 39 + 33 * memW s0 (recs + 24 * i + 16) := by
  dsimp only [accessSlotEntryTotalPure]
  have h1 := accessSlotEntryPayloadPure_bound s0 recs i
  have h2 := (rlpHeaderLenPure_bounds (accessSlotEntryPayloadPure s0 recs i)).2
  omega

private theorem accessListPayloadSumPure_succ {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    accessListPayloadSumPure s0 recs (k + 1) =
      accessListPayloadSumPure s0 recs k + accessSlotEntryTotalPure s0 recs k := by
  simp [accessListPayloadSumPure, List.range_succ]

private theorem accessListPayloadSumPure_bound {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    accessListPayloadSumPure s0 recs k ≤
      39 * k + 33 * ((List.range k).map (fun i => memW s0 (recs + 24 * i + 16))).sum := by
  induction k with
  | zero => simp [accessListPayloadSumPure]
  | succ k ih =>
    rw [accessListPayloadSumPure_succ, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have hb := accessSlotEntryTotalPure_bound s0 recs k
    omega

private theorem range_map_sum_mono (f : Nat → Nat) {k n : Nat} (hkn : k ≤ n) :
    ((List.range k).map f).sum ≤ ((List.range n).map f).sum := by
  induction hkn with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    omega

private def authEntryPayloadPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  let lc := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (a + 0)))
    (BitVec.ofNat 64 (memW s0 (a + 8)))
    (BitVec.ofNat 64 (memW s0 (a + 16)))
    (BitVec.ofNat 64 (memW s0 (a + 24)))
  let ln := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (a + 40)))
  let ly := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (a + 48)))
  let lr := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (a + 56)))
    (BitVec.ofNat 64 (memW s0 (a + 64)))
    (BitVec.ofNat 64 (memW s0 (a + 72)))
    (BitVec.ofNat 64 (memW s0 (a + 80)))
  let ls := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (a + 88)))
    (BitVec.ofNat 64 (memW s0 (a + 96)))
    (BitVec.ofNat 64 (memW s0 (a + 104)))
    (BitVec.ofNat 64 (memW s0 (a + 112)))
  lc + 21 + ln + ly + lr + ls

private def authEntryTotalPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) : Nat :=
  let pl := authEntryPayloadPure s0 (recs + 120 * i)
  rlpHeaderLenPure pl + pl

private def authListPayloadSumPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (recs n : Nat) : Nat :=
  ((List.range n).map (fun i => authEntryTotalPure s0 recs i)).sum

private theorem accessSlotEntryPayloadPure_congr {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {recs i : Nat}
    (hm : memW t (recs + 24 * i + 16) = memW s (recs + 24 * i + 16)) :
    accessSlotEntryPayloadPure t recs i = accessSlotEntryPayloadPure s recs i := by
  simp only [accessSlotEntryPayloadPure, hm]

private theorem accessListPayloadSumPure_congr {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {recs n : Nat}
    (hm : ∀ i < n, memW t (recs + 24 * i + 16) = memW s (recs + 24 * i + 16)) :
    accessListPayloadSumPure t recs n = accessListPayloadSumPure s recs n := by
  unfold accessListPayloadSumPure
  congr 1
  apply List.map_congr_left
  intro i hi
  have he := accessSlotEntryPayloadPure_congr (hm i (List.mem_range.mp hi))
  simp only [accessSlotEntryTotalPure, he]

private theorem authEntryPayloadPure_congr {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {a : Nat}
    (hm : ∀ off, off % 8 = 0 → off + 8 ≤ 120 → memW t (a + off) = memW s (a + off)) :
    authEntryPayloadPure t a = authEntryPayloadPure s a := by
  unfold authEntryPayloadPure
  simp only [hm 0 (by decide) (by decide), hm 8 (by decide) (by decide),
    hm 16 (by decide) (by decide), hm 24 (by decide) (by decide),
    hm 40 (by decide) (by decide), hm 48 (by decide) (by decide),
    hm 56 (by decide) (by decide), hm 64 (by decide) (by decide),
    hm 72 (by decide) (by decide), hm 80 (by decide) (by decide),
    hm 88 (by decide) (by decide), hm 96 (by decide) (by decide),
    hm 104 (by decide) (by decide), hm 112 (by decide) (by decide)]

private theorem authListPayloadSumPure_congr {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {recs n : Nat}
    (hm : ∀ i < n, ∀ off, off % 8 = 0 → off + 8 ≤ 120 →
      memW t (recs + 120 * i + off) = memW s (recs + 120 * i + off)) :
    authListPayloadSumPure t recs n = authListPayloadSumPure s recs n := by
  unfold authListPayloadSumPure
  congr 1
  apply List.map_congr_left
  intro i hi
  have he := authEntryPayloadPure_congr (hm i (List.mem_range.mp hi))
  simp only [authEntryTotalPure, he]

private theorem authEntryPayloadPure_bounds {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (a : Nat) :
    26 ≤ authEntryPayloadPure s0 a ∧ authEntryPayloadPure s0 a ≤ 138 := by
  dsimp only [authEntryPayloadPure]
  have h1 := (u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (a + 0))) (BitVec.ofNat 64 (memW s0 (a + 8)))
    (BitVec.ofNat 64 (memW s0 (a + 16))) (BitVec.ofNat 64 (memW s0 (a + 24)))).2.2.2.2
  have h2 := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s0 (a + 40)))
  have h3 := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s0 (a + 48)))
  have h4 := (u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (a + 56))) (BitVec.ofNat 64 (memW s0 (a + 64)))
    (BitVec.ofNat 64 (memW s0 (a + 72))) (BitVec.ofNat 64 (memW s0 (a + 80)))).2.2.2.2
  have h5 := (u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (a + 88))) (BitVec.ofNat 64 (memW s0 (a + 96)))
    (BitVec.ofNat 64 (memW s0 (a + 104))) (BitVec.ofNat 64 (memW s0 (a + 112)))).2.2.2.2
  omega

private theorem authEntryTotalPure_bound {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs i : Nat) :
    authEntryTotalPure s0 recs i ≤ 147 := by
  dsimp only [authEntryTotalPure]
  have h1 := authEntryPayloadPure_bounds s0 (recs + 120 * i)
  have h2 := (rlpHeaderLenPure_bounds (authEntryPayloadPure s0 (recs + 120 * i))).2
  omega

private theorem authListPayloadSumPure_succ {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    authListPayloadSumPure s0 recs (k + 1) =
      authListPayloadSumPure s0 recs k + authEntryTotalPure s0 recs k := by
  simp [authListPayloadSumPure, List.range_succ]

private theorem authListPayloadSumPure_bound {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (recs k : Nat) :
    authListPayloadSumPure s0 recs k ≤ 147 * k := by
  induction k with
  | zero => simp [authListPayloadSumPure]
  | succ k ih =>
    rw [authListPayloadSumPure_succ]
    have hb := authEntryTotalPure_bound s0 recs k
    omega

private def accessLenLoopBody : ProgHOL 64 :=
  .dec (ofString "inner") .one
    (.panop .mul
      [.const 33#64,
       .load .one
         (.op .add
           [.var .local (ofString "recs"),
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

private def accessLenWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) accessLenLoopBody

private theorem txEnc_wordsOK_wordAt_memW {F : Type}
    {s st : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (hlf : M13.LocFrame s st)
    {bw : BitVec 64} {len : Nat}
    (hwok : WordsOK s (bw.toNat, len))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ len) (hlen_lt : len < 2 ^ 40) :
    WordAt st (bw.toNat + off) ∧
    memW st (bw.toNat + off) = memW s (bw.toNat + off) ∧
    bw.toNat + off < heapEnd := by
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hhe_val : heapEnd = 33806089704 := heapEnd_val
  have h240 : (2 ^ 40 : Nat) = 1099511627776 := rfl
  obtain ⟨hb8, hl8, hw_all⟩ := hwok
  dsimp only at hb8 hl8 hw_all
  have hk0 : 0 < len / 8 := by omega
  obtain ⟨_, hdom0, _⟩ := hw_all 0 hk0
  rw [hAR.1.memaddrs] at hdom0
  have hord0 := (ordinaryDomain_iff (BitVec.ofNat 64 (bw.toNat + 8 * 0))).1 hdom0
  have hb0_nat : (BitVec.ofNat 64 (bw.toNat + 8 * 0)).toNat = bw.toNat := by
    rw [Nat.add_zero, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt bw.isLt
  rw [hb0_nat] at hord0
  have hbw_lt_he : bw.toNat < heapEnd := hord0.2.2
  have hk : off / 8 < len / 8 := by omega
  have hwa_s : WordAt s (bw.toNat + off) := by
    have h := hw_all (off / 8) hk
    have heq : bw.toNat + 8 * (off / 8) = bw.toNat + off := by omega
    rwa [heq] at h
  obtain ⟨w, hdom_s, hmem_s⟩ := hwa_s
  have hdom_ord : ordinaryDomain (BitVec.ofNat 64 (bw.toNat + off)) := by
    rwa [hAR.1.memaddrs] at hdom_s
  have hord_off := (ordinaryDomain_iff (BitVec.ofNat 64 (bw.toNat + off))).1 hdom_ord
  have hoff_nat : (BitVec.ofNat 64 (bw.toNat + off)).toNat = bw.toNat + off := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hoff_nat] at hord_off
  have hma_eq : st.memaddrs = s.memaddrs := by unfold M13.LocFrame at hlf; rw [hlf]
  refine ⟨⟨w, by rw [hma_eq]; exact hdom_s, by rw [hlf.memory]; exact hmem_s⟩, ?_, hord_off.2.2⟩
  unfold memW; rw [hlf.memory]

private theorem txEnc_wordsOK_eval_load_word {F : Type}
    {s st : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (hlf : M13.LocFrame s st)
    {bw : BitVec 64} {len : Nat}
    (hwok : WordsOK s (bw.toNat, len))
    (nm : String) (hst_nm : st.locals.lookup (ofString nm) = some (.val (.word bw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ len) (hlen_lt : len < 2 ^ 40) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (bw.toNat + off))))) := by
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hwa_st, hmw_eq, hsum_lt⟩ :=
    txEnc_wordsOK_wordAt_memW hAR hlf hwok off hoff8 hoff_hi hlen_lt
  have hadd : bw + BitVec.ofNat 64 off = BitVec.ofNat 64 (bw.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (bw.toNat + off)))) := by
    simp [evalHOLExact, evalListHOLExact, hst_nm, valueIsWord, valueWord, wordOpHOL, wordOp, hadd]
  have ha_nat : (BitVec.ofNat 64 (bw.toNat + off)).toNat = bw.toNat + off := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hev := txEnc_mem_load_one_word st _ (BitVec.ofNat 64 (bw.toNat + off)) haddr
    (by rw [ha_nat]; exact hwa_st)
  rw [ha_nat, hmw_eq] at hev
  exact hev

private theorem txEnc_wordsOK_eval_load_u256 {F : Type}
    {s st : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (hlf : M13.LocFrame s st)
    {bw : BitVec 64} {len : Nat}
    (hwok : WordsOK s (bw.toNat, len))
    (nm : String) (hst_nm : st.locals.lookup (ofString nm) = some (.val (.word bw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ len) (hlen_lt : len < 2 ^ 40) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load (.comb [.one, .one, .one, .one])
        (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)])) =
      some (.rStruct [
        .val (.word (BitVec.ofNat 64 (memW s (bw.toNat + off)))),
        .val (.word (BitVec.ofNat 64 (memW s (bw.toNat + off + 8)))),
        .val (.word (BitVec.ofNat 64 (memW s (bw.toNat + off + 16)))),
        .val (.word (BitVec.ofNat 64 (memW s (bw.toNat + off + 24))))]) := by
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hwa_at : ∀ j : Nat, j < 4 →
      WordAt st (bw.toNat + (off + 8 * j)) ∧
      memW st (bw.toNat + (off + 8 * j)) = memW s (bw.toNat + (off + 8 * j)) ∧
      bw.toNat + (off + 8 * j) < heapEnd := by
    intro j hj
    exact txEnc_wordsOK_wordAt_memW hAR hlf hwok (off + 8 * j) (by omega) (by omega) hlen_lt
  obtain ⟨⟨w0, hdom0, hmem0⟩, hmw0, hlt0⟩ := hwa_at 0 (by omega)
  obtain ⟨⟨w1, hdom1, hmem1⟩, hmw1, hlt1⟩ := hwa_at 1 (by omega)
  obtain ⟨⟨w2, hdom2, hmem2⟩, hmw2, hlt2⟩ := hwa_at 2 (by omega)
  obtain ⟨⟨w3, hdom3, hmem3⟩, hmw3, hlt3⟩ := hwa_at 3 (by omega)
  let base : BitVec 64 := BitVec.ofNat 64 (bw.toNat + off)
  have hadd : bw + BitVec.ofNat 64 off = base := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb0 : BitVec.ofNat 64 (bw.toNat + (off + 8 * 0)) = base := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_ofNat]; omega
  have hb8 : base + 8#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb16 : base + 16#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 2)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb24 : base + 24#64 = BitVec.ofNat 64 (bw.toNat + (off + 8 * 3)) := by
    apply BitVec.eq_of_toNat_eq; simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hd0 : st.memaddrs base := by rw [← hb0]; exact hdom0
  have hd1 : st.memaddrs (base + 8#64) := by rw [hb8]; exact hdom1
  have hd2 : st.memaddrs (base + 16#64) := by rw [hb16]; exact hdom2
  have hd3 : st.memaddrs (base + 24#64) := by rw [hb24]; exact hdom3
  have hv0 : st.memory base = .word w0 := by rw [← hb0]; exact hmem0
  have hv1 : st.memory (base + 8#64) = .word w1 := by rw [hb8]; exact hmem1
  have hv2 : st.memory (base + 16#64) = .word w2 := by rw [hb16]; exact hmem2
  have hv3 : st.memory (base + 24#64) = .word w3 := by rw [hb24]; exact hmem3
  have hw0_eq : BitVec.ofNat 64 (memW s (bw.toNat + off)) = w0 := by
    have h0 : bw.toNat + off = bw.toNat + (off + 8 * 0) := by omega
    rw [h0, ← hmw0]; unfold memW; rw [hmem0]; simp
  have hw1_eq : BitVec.ofNat 64 (memW s (bw.toNat + off + 8)) = w1 := by
    have h1 : bw.toNat + off + 8 = bw.toNat + (off + 8 * 1) := by omega
    rw [h1, ← hmw1]; unfold memW; rw [hmem1]; simp
  have hw2_eq : BitVec.ofNat 64 (memW s (bw.toNat + off + 16)) = w2 := by
    have h2 : bw.toNat + off + 16 = bw.toNat + (off + 8 * 2) := by omega
    rw [h2, ← hmw2]; unfold memW; rw [hmem2]; simp
  have hw3_eq : BitVec.ofNat 64 (memW s (bw.toNat + off + 24)) = w3 := by
    have h3 : bw.toNat + off + 24 = bw.toNat + (off + 8 * 3) := by omega
    rw [h3, ← hmw3]; unfold memW; rw [hmem3]; simp
  rw [hw0_eq, hw1_eq, hw2_eq, hw3_eq]
  simp [evalHOLExact, evalListHOLExact, hst_nm, valueIsWord, valueWord, wordOpHOL, wordOp,
    isWfShapeExactHOL, memLoadHOLExact, memLoadsHOLExact, sizeOfShapeWithContextHOL,
    bytesInWordHOL, BitVec.add_assoc, hadd, hd0, hd1, hd2, hd3, hv0, hv1, hv2, hv3]

private theorem accessLenWhile_exact {F : Type}
    (clk : Nat) (s0 t : PanSemStateFiniteExact 64 F)
    (recsw nw iw totw : BitVec 64)
    (hclk : t.clock ≤ clk)
    (heff : HeapByteEff s0 t [] [])
    (hm_eq : t.memory = s0.memory)
    (hAR0 : ArenaReady s0)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun i => memW s0 (recsw.toNat + 24 * i + 16))).sum < 2 ^ 32)
    (hi_le : iw.toNat ≤ nw.toNat)
    (htot_eq : totw.toNat = accessListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_tot : t.locals.lookup (ofString "total") = some (.val (.word totw)))
    (hnt : (evaluateHOLFiniteState t accessLenWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t accessLenWhile
    out.1 = none ∧
    HeapByteEff s0 out.2 [] [] ∧
    out.2.memory = s0.memory ∧
    ∃ tot_f : BitVec 64,
      out.2.locals.lookup (ofString "total") = some (.val (.word tot_f)) ∧
      tot_f.toNat = accessListPayloadSumPure s0 recsw.toNat nw.toNat := by
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have h240 : (2 ^ 40 : Nat) = 1099511627776 := rfl
  induction clk generalizing t iw totw with
  | zero =>
    dsimp only [accessLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hcz : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hcz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, heff, hm_eq, totw, ht_tot, by rw [← hij]; exact htot_eq⟩
  | succ clk ih =>
    dsimp only [accessLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hcz : t.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        have hwok0 := hrecs_ok (by omega)
        set td := decClockHOLFinite t
        have htd_eff : HeapByteEff s0 td [] [] := heff.locals_clock t.locals (t.clock - 1)
        have htd_mem : td.memory = s0.memory := hm_eq
        have htd_AR : ArenaReady td := htd_eff.arena
        have htd_code : td.code = originalRuntimeCode := htd_AR.1.code
        have htd_recs : td.locals.lookup (ofString "recs") = some (.val (.word recsw)) := ht_recs
        have htd_n : td.locals.lookup (ofString "n") = some (.val (.word nw)) := ht_n
        have htd_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := ht_i
        have htd_tot : td.locals.lookup (ofString "total") = some (.val (.word totw)) := ht_tot
        have hcle_body := evaluateHOLFiniteState_clock_le td accessLenLoopBody
        have hnt_b : (evaluateHOLFiniteState td accessLenLoopBody).1 ≠ some .timeOut := by
          rcases hb_res : evaluateHOLFiniteState td accessLenLoopBody with ⟨rb, sb⟩
          rintro rfl; simp [hb_res] at hnt
        have hbody_step :
            let rb := evaluateHOLFiniteState td accessLenLoopBody
            rb.1 = none ∧
            HeapByteEff s0 rb.2 [] [] ∧
            rb.2.memory = s0.memory ∧
            rb.2.locals.lookup (ofString "recs") = some (.val (.word recsw)) ∧
            rb.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
            rb.2.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) ∧
            ∃ totw' : BitVec 64,
              rb.2.locals.lookup (ofString "total") = some (.val (.word totw')) ∧
              totw'.toNat = accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
          dsimp only [accessLenLoopBody] at hnt_b ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt_b ⊢; dsimp only at hnt_b ⊢
          have hoff_lt : 24 * iw.toNat + 16 + 8 ≤ 24 * nw.toNat := by omega
          have hwa_ns_0 : WordAt s0 (recsw.toNat + (24 * iw.toNat + 16)) := by
            have h := hwok0.2.2 (3 * iw.toNat + 2) (by omega)
            have heq : recsw.toNat + 8 * (3 * iw.toNat + 2) = recsw.toNat + (24 * iw.toNat + 16) := by omega
            rwa [heq] at h
          have hrec0_lt_he : recsw.toNat < heapEnd := by
            obtain ⟨_, hd0, _⟩ := hwok0.2.2 0 (by omega)
            rw [hAR0.1.memaddrs] at hd0
            have ho0 := (ordinaryDomain_iff (BitVec.ofNat 64 (recsw.toNat + 8 * 0))).1 hd0
            have hb0 : (BitVec.ofNat 64 (recsw.toNat + 8 * 0)).toNat = recsw.toNat := by
              rw [Nat.add_zero, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt recsw.isLt
            rw [hb0] at ho0
            exact ho0.2.2
          have hwa_ns : WordAt td (recsw.toNat + (24 * iw.toNat + 16)) := by
            obtain ⟨w, hd, hm⟩ := hwa_ns_0
            exact ⟨w, by rw [htd_eff.memaddrs]; exact hd, by rw [htd_mem]; exact hm⟩
          have hmw_ns : memW td (recsw.toNat + (24 * iw.toNat + 16)) =
              memW s0 (recsw.toNat + (24 * iw.toNat + 16)) := by
            unfold memW; rw [htd_mem]
          let addr_ns : BitVec 64 := recsw + (iw * 24#64 + (16#64 + 0#64))
          have haddr_ns_nat : addr_ns.toNat = recsw.toNat + (24 * iw.toNat + 16) := by
            have hhe_val : heapEnd = 33806089704 := heapEnd_val
            have hi24 : (iw * 24#64).toNat = 24 * iw.toNat := by
              rw [BitVec.toNat_mul]; change (iw.toNat * 24) % 2 ^ 64 = _; rw [Nat.mul_comm]
              exact Nat.mod_eq_of_lt (by omega)
            have h16 : (16#64 + 0#64 : BitVec 64).toNat = 16 := rfl
            have hsum1 : (iw * 24#64 + (16#64 + 0#64)).toNat = 24 * iw.toNat + 16 := by
              rw [BitVec.toNat_add, hi24, h16]; exact Nat.mod_eq_of_lt (by omega)
            change (recsw + (iw * 24#64 + (16#64 + 0#64))).toNat = _
            rw [BitVec.toNat_add, hsum1]; exact Nat.mod_eq_of_lt (by omega)
          have hev_addr_ns : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
              (.op .add
                [.var .local (ofString "recs"),
                 .panop .mul [.var .local (ofString "i"), .const 24#64],
                 .const 16#64]) = some (.val (.word addr_ns)) := by
            simp [evalHOLExact, evalListHOLExact, htd_recs, htd_i, panOpHOL, wordOpHOL, wordOp,
              valueIsWord, valueWord, addr_ns]
          have hev_ns := txEnc_mem_load_one_word td _ addr_ns hev_addr_ns
            (by rw [haddr_ns_nat]; exact hwa_ns)
          rw [haddr_ns_nat, hmw_ns] at hev_ns
          let nsNat := memW s0 (recsw.toNat + 24 * iw.toNat + 16)
          have hns_bound : nsNat < 2 ^ 32 := by
            have hmem_le : nsNat ≤
                ((List.range (iw.toNat + 1)).map (fun j => memW s0 (recsw.toNat + 24 * j + 16))).sum := by
              rw [List.range_succ, List.map_append, List.sum_append]
              simp only [List.map_singleton, List.sum_singleton]; dsimp [nsNat]; omega
            have hsub := range_map_sum_mono (fun j => memW s0 (recsw.toNat + 24 * j + 16))
              (by omega : iw.toNat + 1 ≤ nw.toNat)
            omega
          let nsw := BitVec.ofNat 64 nsNat
          let innerw : BitVec 64 := 33#64 * nsw
          have hnsw_eq : BitVec.ofNat 64 (memW s0 (recsw.toNat + (24 * iw.toNat + 16))) = nsw := by
            have : recsw.toNat + (24 * iw.toNat + 16) = recsw.toNat + 24 * iw.toNat + 16 := by omega
            rw [this]
          rw [hnsw_eq] at hev_ns
          have hinnerw_nat : innerw.toNat = 33 * nsNat := by
            change (33#64 * nsw).toNat = 33 * nsNat
            rw [BitVec.toNat_mul]
            have hnsw_nat : nsw.toNat = nsNat := by
              change (BitVec.ofNat 64 nsNat).toNat = nsNat
              rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            rw [hnsw_nat]
            change (33 * nsNat) % 2 ^ 64 = 33 * nsNat
            exact Nat.mod_eq_of_lt (by omega)
          have hev_inner : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
              (.panop .mul
                [.const 33#64,
                 .load .one
                   (.op .add
                     [.var .local (ofString "recs"),
                      .panop .mul [.var .local (ofString "i"), .const 24#64],
                      .const 16#64])]) = some (.val (.word innerw)) := by
            unfold evalHOLExact; unfold evalListHOLExact
            have hc33 : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                (.const 33#64) = some (.val (.word 33#64)) := rfl
            rw [hc33]; unfold evalListHOLExact; rw [hev_ns]; unfold evalListHOLExact
            simp [panOpHOL, valueIsWord, valueWord, innerw]
          rw [hev_inner] at hnt_b ⊢; dsimp only at hnt_b ⊢
          have hsh_in : shapeEqHOL .one (shapeOfHOLExact (.val (.word innerw) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_in] at hnt_b ⊢; dsimp only at hnt_b ⊢
          set s1 := setVarHOLFinite (ofString "inner") (.val (.word innerw)) td
          have hs1_eff : HeapByteEff s0 s1 [] [] := htd_eff.locals_clock s1.locals s1.clock
          have hs1_mem : s1.memory = s0.memory := htd_mem
          have hs1_AR : ArenaReady s1 := hs1_eff.arena
          have hs1_code : s1.code = originalRuntimeCode := hs1_AR.1.code
          have hs1_inner : s1.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨s2, hih_nat, hih1, hih9, _, hs2_mem_s1, hs2_loc, heff_s1_s2, hnt_s2, hdc_ih⟩ :=
            eval_decCall_rlp_list_header_len s1 "ih" (.var .local (ofString "inner")) innerw _ [] []
              hs1_code hs1_AR (by simp [evalHOLExact, hs1_inner]) hnt_b
          rw [hdc_ih]; dsimp only
          set ihw := BitVec.ofNat 64 (rlpHeaderLenPure innerw.toNat)
          have hs2_eff : HeapByteEff s0 s2 [] [] := hs1_eff.trans heff_s1_s2
          have hs2_mem : s2.memory = s0.memory := hs2_mem_s1.trans hs1_mem
          have hs2_AR : ArenaReady s2 := hs2_eff.arena
          have hs2_code : s2.code = originalRuntimeCode := hs2_AR.1.code
          have hs2_ih : s2.locals.lookup (ofString "ih") = some (.val (.word ihw)) := by
            rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ihw]
          have hs2_inner : s2.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
            rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_inner,
              show ofString "ih" ≠ ofString "inner" by decide]
          rw [evaluateHOLFiniteState_dec_total] at hnt_s2 ⊢; dsimp only at hnt_s2 ⊢
          let entryw : BitVec 64 := 21#64 + (ihw + (innerw + 0#64))
          have hentryw_nat : entryw.toNat = accessSlotEntryPayloadPure s0 recsw.toNat iw.toNat := by
            change (21#64 + (ihw + (innerw + 0#64))).toNat = accessSlotEntryPayloadPure s0 recsw.toNat iw.toNat
            rw [BitVec.add_zero]
            have hih_le : rlpHeaderLenPure (33 * nsNat) ≤ 9 := by rw [← hinnerw_nat, ← hih_nat]; exact hih9
            have hsum1 : (ihw + innerw).toNat = rlpHeaderLenPure (33 * nsNat) + 33 * nsNat := by
              rw [BitVec.toNat_add, hih_nat, hinnerw_nat]
              exact Nat.mod_eq_of_lt (by omega)
            rw [BitVec.toNat_add, hsum1]
            change (21 + (rlpHeaderLenPure (33 * nsNat) + 33 * nsNat)) % 2 ^ 64 = _
            rw [Nat.mod_eq_of_lt (by omega)]
            dsimp only [accessSlotEntryPayloadPure, nsNat]; omega
          have hev_entry : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]) =
              some (.val (.word entryw)) := by
            simp [evalHOLExact, evalListHOLExact, hs2_ih, hs2_inner, wordOpHOL, wordOp,
              valueIsWord, valueWord, entryw]
          rw [hev_entry] at hnt_s2 ⊢; dsimp only at hnt_s2 ⊢
          have hsh_en : shapeEqHOL .one (shapeOfHOLExact (.val (.word entryw) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_en] at hnt_s2 ⊢; dsimp only at hnt_s2 ⊢
          set s3 := setVarHOLFinite (ofString "entry") (.val (.word entryw)) s2
          have hs3_eff : HeapByteEff s0 s3 [] [] := hs2_eff.locals_clock s3.locals s3.clock
          have hs3_mem : s3.memory = s0.memory := hs2_mem
          have hs3_AR : ArenaReady s3 := hs3_eff.arena
          have hs3_code : s3.code = originalRuntimeCode := hs3_AR.1.code
          have hs3_entry : s3.locals.lookup (ofString "entry") = some (.val (.word entryw)) := by
            simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨s4, heh_nat, heh1, heh9, _, hs4_mem_s3, hs4_loc, heff_s3_s4, hnt_s4, hdc_eh⟩ :=
            eval_decCall_rlp_list_header_len s3 "eh" (.var .local (ofString "entry")) entryw _ [] []
              hs3_code hs3_AR (by simp [evalHOLExact, hs3_entry]) hnt_s2
          rw [hdc_eh]; dsimp only
          set ehw := BitVec.ofNat 64 (rlpHeaderLenPure entryw.toNat)
          have hs4_eff : HeapByteEff s0 s4 [] [] := hs3_eff.trans heff_s3_s4
          have hs4_mem : s4.memory = s0.memory := hs4_mem_s3.trans hs3_mem
          have hs4_eh : s4.locals.lookup (ofString "eh") = some (.val (.word ehw)) := by
            rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ehw]
          have hs4_entry : s4.locals.lookup (ofString "entry") = some (.val (.word entryw)) := by
            rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_entry,
              show ofString "eh" ≠ ofString "entry" by decide]
          have hs4_tot : s4.locals.lookup (ofString "total") = some (.val (.word totw)) := by
            rw [hs4_loc]; simp [s3, hs2_loc, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htd_tot,
              show ofString "eh" ≠ ofString "total" by decide,
              show ofString "entry" ≠ ofString "total" by decide,
              show ofString "ih" ≠ ofString "total" by decide,
              show ofString "inner" ≠ ofString "total" by decide]
          have hs4_i : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hs4_loc]; simp [s3, hs2_loc, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htd_i,
              show ofString "eh" ≠ ofString "i" by decide,
              show ofString "entry" ≠ ofString "i" by decide,
              show ofString "ih" ≠ ofString "i" by decide,
              show ofString "inner" ≠ ofString "i" by decide]
          have hs4_recs : s4.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
            rw [hs4_loc]; simp [s3, hs2_loc, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htd_recs,
              show ofString "eh" ≠ ofString "recs" by decide,
              show ofString "entry" ≠ ofString "recs" by decide,
              show ofString "ih" ≠ ofString "recs" by decide,
              show ofString "inner" ≠ ofString "recs" by decide]
          have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hs4_loc]; simp [s3, hs2_loc, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htd_n,
              show ofString "eh" ≠ ofString "n" by decide,
              show ofString "entry" ≠ ofString "n" by decide,
              show ofString "ih" ≠ ofString "n" by decide,
              show ofString "inner" ≠ ofString "n" by decide]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          let totw' : BitVec 64 := totw + (ehw + (entryw + 0#64))
          have hev_tot' : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
              (.op .add [.var .local (ofString "total"), .var .local (ofString "eh"), .var .local (ofString "entry")]) =
              some (.val (.word totw')) := by
            simp [evalHOLExact, evalListHOLExact, hs4_tot, hs4_eh, hs4_entry, wordOpHOL, wordOp,
              valueIsWord, valueWord, totw']
          rw [hev_tot']; dsimp only
          have hvv_tot : isValidValueHOLFinite s4 .local (ofString "total") (.val (.word totw')) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs4_tot, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv_tot]; dsimp only
          set s5 := setKvarHOLFinite .local (ofString "total") (.val (.word totw')) s4
          have hs5_i : s5.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_i,
              show ofString "total" ≠ ofString "i" by decide]
          rw [evaluateHOLFiniteState_assign]
          have hev_i' : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) =
              some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs5_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_i']; dsimp only
          have hvv_i : isValidValueHOLFinite s5 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs5_i, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv_i]; dsimp only
          set s6 := setKvarHOLFinite .local (ofString "i") (.val (.word (iw + 1#64))) s5
          have htot_prev_le := accessListPayloadSumPure_bound s0 recsw.toNat iw.toNat
          have hsub_slots := range_map_sum_mono (fun j => memW s0 (recsw.toNat + 24 * j + 16))
            (by omega : iw.toNat ≤ nw.toNat)
          have htotw'_nat : totw'.toNat = accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
            change (totw + (ehw + (entryw + 0#64))).toNat = _
            rw [BitVec.add_zero]
            have hent_b := accessSlotEntryPayloadPure_bound s0 recsw.toNat iw.toNat
            have hsum_eh : (ehw + entryw).toNat = accessSlotEntryTotalPure s0 recsw.toNat iw.toNat := by
              rw [BitVec.toNat_add, heh_nat, hentryw_nat]
              dsimp only [accessSlotEntryTotalPure]
              have hq := (rlpHeaderLenPure_bounds (accessSlotEntryPayloadPure s0 recsw.toNat iw.toNat)).2
              exact Nat.mod_eq_of_lt (by omega)
            rw [BitVec.toNat_add, htot_eq, hsum_eh, accessListPayloadSumPure_succ]
            have het_b := accessSlotEntryTotalPure_bound s0 recsw.toNat iw.toNat
            exact Nat.mod_eq_of_lt (by
              have : 39 * iw.toNat ≤ 39 * (2 ^ 32) := Nat.mul_le_mul_left 39 (by omega)
              omega)
          refine ⟨rfl, hs4_eff.locals_clock _ s6.clock, hs4_mem, ?_, ?_, ?_, totw', ?_, htotw'_nat⟩
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s6, s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_recs,
              show ofString "i" ≠ ofString "recs" from M13.mls_ne rfl,
              show ofString "total" ≠ ofString "recs" from M13.mls_ne rfl]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s6, s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_n,
              show ofString "i" ≠ ofString "n" from M13.mls_ne rfl,
              show ofString "total" ≠ ofString "n" from M13.mls_ne rfl]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s6, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s6, s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "total" from M13.mls_ne rfl]
        rcases hb_ev : evaluateHOLFiniteState td accessLenLoopBody with ⟨rb, sb⟩
        simp only [hb_ev] at hbody_step hcle_body hnt ⊢
        obtain ⟨rfl, hsb_eff, hsb_mem, hsb_recs, hsb_n, hsb_i, totw', hsb_tot, htotw'_nat⟩ := hbody_step
        dsimp only at hnt ⊢
        have hi1_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hclk_sb : sb.clock ≤ clk := by
          change sb.clock ≤ t.clock - 1 at hcle_body; omega
        exact ih sb (iw + 1#64) totw' hclk_sb hsb_eff hsb_mem
          (by rw [hi1_nat]; omega) (by rw [hi1_nat]; exact htotw'_nat)
          hsb_recs hsb_n hsb_i hsb_tot hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, heff, hm_eq, totw, ht_tot, by rw [← hij]; exact htot_eq⟩

private theorem eval_access_list_payload_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (recsw nw : BitVec 64)
    (hAR : ArenaReady s)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun i => memW s (recsw.toNat + 24 * i + 16))).sum < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s (recsw.toNat, 24 * nw.toNat))
    (hs_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hs_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64
        (accessListPayloadSumPure s recsw.toNat nw.toNat))))) ∧
    HeapByteEff s (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2 [] [] ∧
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_access_list_payload_len)).2.memory = s.memory := by
  have hb : sourceFnBody Guest.Software.guestFn_access_list_payload_len =
      .dec (ofString "total") .one (.const 0#64)
        (.dec (ofString "i") .one (.const 0#64)
          (.seq accessLenWhile (.return (.var .local (ofString "total"))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "total") (.val (.word 0#64)) s
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
  have hs2_recs : s2.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_recs,
      show ofString "total" ≠ ofString "recs" from M13.mls_ne rfl,
      show ofString "i" ≠ ofString "recs" from M13.mls_ne rfl]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_n,
      show ofString "total" ≠ ofString "n" from M13.mls_ne rfl,
      show ofString "i" ≠ ofString "n" from M13.mls_ne rfl]
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_tot : s2.locals.lookup (ofString "total") = some (.val (.word 0#64)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "total" from M13.mls_ne rfl]
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hw : evaluateHOLFiniteState s2 accessLenWhile with ⟨rw0, sw⟩
  have hnt_w : rw0 ≠ some .timeOut := by
    rintro rfl; simp [hw] at hnt
  have hloop := accessLenWhile_exact s2.clock s s2 recsw nw 0#64 0#64
    (Nat.le_refl _) ((HeapByteEff.refl hAR [] []).locals_clock s2.locals s2.clock)
    rfl hAR hn_lt hslots_lt (by simp)
    (by simp [accessListPayloadSumPure]) hrecs_ok hs2_recs hs2_n hs2_i hs2_tot
    (by rw [hw]; exact hnt_w)
  rw [hw] at hloop; dsimp only at hloop
  obtain ⟨rfl, hsw_eff, hsw_mem, tot_f, hsw_tot, htot_nat⟩ := hloop
  simp only [hw] at hnt ⊢
  rw [evaluateHOLFiniteState_return]
  have hev_tot : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
      (.var .local (ofString "total")) = some (.val (.word tot_f)) := by
    simp [evalHOLExact, hsw_tot]
  rw [hev_tot]; dsimp only
  have hsz : sizeOfShapeWithContextHOL sw.structs (shapeOfHOLExact (.val (.word tot_f) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  have htot : tot_f = BitVec.ofNat 64 (accessListPayloadSumPure s recsw.toNat nw.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← htot_nat, Nat.mod_eq_of_lt tot_f.isLt]
  rw [htot]
  exact ⟨rfl, hsw_eff.locals_clock _ _, hsw_mem⟩

private theorem eval_decCall_access_list_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (recsExp nExp : ExpHOL 64)
    (recsw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR : ArenaReady s)
    (hm0 : s.memory = s0.memory)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun i => memW s0 (recsw.toNat + 24 * i + 16))).sum < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s (recsw.toNat, 24 * nw.toNat))
    (hrecs_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      recsExp = some (.val (.word recsw)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      nExp = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "access_list_payload_len") [recsExp, nExp] cont)).1 ≠
      some .timeOut) :
    let pl := BitVec.ofNat 64 (accessListPayloadSumPure s0 recsw.toNat nw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      pl.toNat = accessListPayloadSumPure s0 recsw.toNat nw.toNat ∧
      pl.toNat ≤ 39 * nw.toNat + 33 * ((List.range nw.toNat).map
        (fun i => memW s0 (recsw.toNat + 24 * i + 16))).sum ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word pl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "access_list_payload_len") [recsExp, nExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro pl
  have hcode : s.code = originalRuntimeCode := hAR.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [recsExp, nExp] = some [.val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hrecs_ev, hn_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "access_list_payload_len")
    (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_access_list_payload_len) recsw nw (by decide)
    (by rw [hcode]; exact lookup_access_list_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "recs", ValueHOL.val (.word recsw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" from M13.mls_ne rfl]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent :=
      ((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).arena
    have hent_mem : ent.memory = s0.memory := hm0
    have hsum_eq : ∀ k, accessListPayloadSumPure ent recsw.toNat k =
        accessListPayloadSumPure s0 recsw.toNat k := by
      intro k; unfold accessListPayloadSumPure accessSlotEntryTotalPure accessSlotEntryPayloadPure memW
      rw [hent_mem]
    have hslots_ent : ((List.range nw.toNat).map
        (fun i => memW ent (recsw.toNat + 24 * i + 16))).sum < 2 ^ 32 := by
      unfold memW; rw [hent_mem]; exact hslots_lt
    have hrecs_ent : 0 < nw.toNat → WordsOK ent (recsw.toNat, 24 * nw.toNat) := by
      intro hpos
      obtain ⟨h1, h2, h3⟩ := hrecs_ok hpos
      exact ⟨h1, h2, fun k hk => by
        obtain ⟨w, hd, hm⟩ := h3 k hk
        exact ⟨w, hd, hm⟩⟩
    rcases hal : evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_access_list_payload_len) with ⟨ral, sal⟩
    have hnt_al : ral ≠ some .timeOut := by
      rintro rfl; rw [hal] at hnt; exact hnt rfl
    obtain ⟨hr_al, heff_al, hmem_al⟩ := eval_access_list_payload_len_body_exact ent recsw nw
      hent_AR hn_lt hslots_ent hrecs_ent hent_recs hent_n (by rw [hal]; exact hnt_al)
    rw [hal] at hr_al heff_al hmem_al
    dsimp only at hr_al heff_al hmem_al
    rw [hsum_eq] at hr_al
    subst hr_al
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hal] at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word pl)) { sal with locals := s.locals }
    have hmid_eff0 : HeapByteEff s mid [] [] :=
      (((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).trans heff_al).locals_clock
        mid.locals mid.clock
    have hmid_eff : HeapByteEff s mid Rl gw :=
      hmid_eff0.mono (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => False.elim (List.not_mem_nil h))
    have hbnd := accessListPayloadSumPure_bound s0 recsw.toNat nw.toNat
    have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
    have hpl_nat : pl.toNat = accessListPayloadSumPure s0 recsw.toNat nw.toNat := by
      dsimp [pl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hpl_nat, by rw [hpl_nat]; exact hbnd, hmem_al, rfl, hmid_eff, hnt, rfl⟩

private theorem eval_auth_payload_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (aw : BitVec 64)
    (hAR : ArenaReady s)
    (ha_ok : WordsOK s (aw.toNat, 120))
    (hs_a : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hnt : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_payload_len)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_payload_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (authEntryPayloadPure s aw.toNat))))) ∧
    HeapByteEff s (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2 [] [] ∧
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_payload_len)).2.memory = s.memory := by
  have hcode : s.code = originalRuntimeCode := hAR.1.code
  have h120_lt : 120 < 2 ^ 40 := by decide
  have hb : sourceFnBody Guest.Software.guestFn_auth_payload_len =
      .decCall (ofString "lc") .one (ofString "tx_u256_encoded_len")
        [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64])]
        (.decCall (ofString "ln") .one (ofString "rlp_word_encoded_len")
          [.load .one (.op .add [.var .local (ofString "a"), .const 40#64])]
          (.decCall (ofString "ly") .one (ofString "rlp_word_encoded_len")
            [.load .one (.op .add [.var .local (ofString "a"), .const 48#64])]
            (.decCall (ofString "lr") .one (ofString "tx_u256_encoded_len")
              [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64])]
              (.decCall (ofString "ls") .one (ofString "tx_u256_encoded_len")
                [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64])]
                (.return (.op .add [
                  .var .local (ofString "lc"), .const 21#64,
                  .var .local (ofString "ln"), .var .local (ofString "ly"),
                  .var .local (ofString "lr"), .var .local (ofString "ls")])))))) := rfl
  rw [hb] at hnt ⊢
  have hwok_pres : ∀ {t : PanSemStateFiniteExact 64 F}, HeapByteEff s t [] [] → t.memory = s.memory →
      WordsOK t (aw.toNat, 120) := by
    intro t heff hm
    obtain ⟨h1, h2, h3⟩ := ha_ok
    exact ⟨h1, h2, fun k hk => by
      obtain ⟨w, hd, hmw⟩ := h3 k hk
      exact ⟨w, by rw [heff.memaddrs]; exact hd, by rw [hm]; exact hmw⟩⟩
  -- Step 1: lc = tx_u256_encoded_len(load u256 (a + 0))
  have hev_c0 := txEnc_wordsOK_eval_load_u256 hAR (M13.LocFrame.refl s) ha_ok "a" hs_a 0
    (by decide) (by decide) h120_lt
  obtain ⟨m1, hlf1, hm1_loc, hnt1, hdc1⟩ := eval_decCall_tx_u256_encoded_len s "lc" _
    (BitVec.ofNat 64 (memW s (aw.toNat + 0))) (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 24)))
    _ hcode hev_c0 hnt
  rw [hdc1]
  have heff1 : HeapByteEff s m1 [] [] := HeapByteEff.of_locFrame hAR hlf1 [] []
  have hm1_mem : m1.memory = s.memory := hlf1.memory
  have hm1_AR : ArenaReady m1 := heff1.arena
  have hm1_code : m1.code = originalRuntimeCode := hm1_AR.1.code
  have hm1_a : m1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_a,
      show ofString "lc" ≠ ofString "a" from M13.mls_ne rfl]
  -- Step 2: ln = rlp_word_encoded_len(load word (a + 40))
  have hev_n := txEnc_wordsOK_eval_load_word hm1_AR (M13.LocFrame.refl m1) (hwok_pres heff1 hm1_mem)
    "a" hm1_a 40 (by decide) (by decide) h120_lt
  have hmw40 : memW m1 (aw.toNat + 40) = memW s (aw.toNat + 40) := by unfold memW; rw [hm1_mem]
  rw [hmw40] at hev_n
  obtain ⟨m2, hln_nat, hln1, hln9, _, hm2_mem_m1, hm2_loc, heff2_step, hnt2, hdc2⟩ :=
    eval_decCall_rlp_word_encoded_len m1 "ln" _ (BitVec.ofNat 64 (memW s (aw.toNat + 40)))
      _ [] [] hm1_code hm1_AR hev_n hnt1
  rw [hdc2]
  have heff2 : HeapByteEff s m2 [] [] := heff1.trans heff2_step
  have hm2_mem : m2.memory = s.memory := hm2_mem_m1.trans hm1_mem
  have hm2_AR : ArenaReady m2 := heff2.arena
  have hm2_code : m2.code = originalRuntimeCode := hm2_AR.1.code
  have hm2_a : m2.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_a,
      show ofString "ln" ≠ ofString "a" from M13.mls_ne rfl]
  -- Step 3: ly = rlp_word_encoded_len(load word (a + 48))
  have hev_y := txEnc_wordsOK_eval_load_word hm2_AR (M13.LocFrame.refl m2) (hwok_pres heff2 hm2_mem)
    "a" hm2_a 48 (by decide) (by decide) h120_lt
  have hmw48 : memW m2 (aw.toNat + 48) = memW s (aw.toNat + 48) := by unfold memW; rw [hm2_mem]
  rw [hmw48] at hev_y
  obtain ⟨m3, hly_nat, hly1, hly9, _, hm3_mem_m2, hm3_loc, heff3_step, hnt3, hdc3⟩ :=
    eval_decCall_rlp_word_encoded_len m2 "ly" _ (BitVec.ofNat 64 (memW s (aw.toNat + 48)))
      _ [] [] hm2_code hm2_AR hev_y hnt2
  rw [hdc3]
  have heff3 : HeapByteEff s m3 [] [] := heff2.trans heff3_step
  have hm3_mem : m3.memory = s.memory := hm3_mem_m2.trans hm2_mem
  have hm3_AR : ArenaReady m3 := heff3.arena
  have hm3_code : m3.code = originalRuntimeCode := hm3_AR.1.code
  have hm3_a : m3.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_a,
      show ofString "ly" ≠ ofString "a" from M13.mls_ne rfl]
  -- Step 4: lr = tx_u256_encoded_len(load u256 (a + 56))
  have hev_r := txEnc_wordsOK_eval_load_u256 hm3_AR (M13.LocFrame.refl m3) (hwok_pres heff3 hm3_mem)
    "a" hm3_a 56 (by decide) (by decide) h120_lt
  have hmw56 : ∀ d, memW m3 d = memW s d := fun d => by unfold memW; rw [hm3_mem]
  simp only [hmw56] at hev_r
  obtain ⟨m4, hlf4, hm4_loc, hnt4, hdc4⟩ := eval_decCall_tx_u256_encoded_len m3 "lr" _
    (BitVec.ofNat 64 (memW s (aw.toNat + 56))) (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 24)))
    _ hm3_code hev_r hnt3
  rw [hdc4]
  have heff4 : HeapByteEff s m4 [] [] := heff3.trans (HeapByteEff.of_locFrame hm3_AR hlf4 [] [])
  have hm4_mem : m4.memory = s.memory := hlf4.memory.trans hm3_mem
  have hm4_AR : ArenaReady m4 := heff4.arena
  have hm4_code : m4.code = originalRuntimeCode := hm4_AR.1.code
  have hm4_a : m4.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    rw [hm4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_a,
      show ofString "lr" ≠ ofString "a" from M13.mls_ne rfl]
  -- Step 5: ls = tx_u256_encoded_len(load u256 (a + 88))
  have hev_s := txEnc_wordsOK_eval_load_u256 hm4_AR (M13.LocFrame.refl m4) (hwok_pres heff4 hm4_mem)
    "a" hm4_a 88 (by decide) (by decide) h120_lt
  have hmw88 : ∀ d, memW m4 d = memW s d := fun d => by unfold memW; rw [hm4_mem]
  simp only [hmw88] at hev_s
  obtain ⟨m5, hlf5, hm5_loc, hnt5, hdc5⟩ := eval_decCall_tx_u256_encoded_len m4 "ls" _
    (BitVec.ofNat 64 (memW s (aw.toNat + 88))) (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 24)))
    _ hm4_code hev_s hnt4
  rw [hdc5]
  have heff5 : HeapByteEff s m5 [] [] := heff4.trans (HeapByteEff.of_locFrame hm4_AR hlf5 [] [])
  have hm5_mem : m5.memory = s.memory := hlf5.memory.trans hm4_mem
  let lcw := BitVec.ofNat 64 (txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s (aw.toNat + 0))) (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 0 + 24))))
  let lnw := BitVec.ofNat 64 (rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s (aw.toNat + 40))))
  let lyw := BitVec.ofNat 64 (rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s (aw.toNat + 48))))
  let lrw := BitVec.ofNat 64 (txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s (aw.toNat + 56))) (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 56 + 24))))
  let lsw := BitVec.ofNat 64 (txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s (aw.toNat + 88))) (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 8)))
    (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 88 + 24))))
  have hm5_lc : m5.locals.lookup (ofString "lc") = some (.val (.word lcw)) := by
    rw [hm5_loc, hm4_loc, hm3_loc, hm2_loc, hm1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, lcw,
      show ofString "ls" ≠ ofString "lc" from M13.mls_ne rfl,
      show ofString "lr" ≠ ofString "lc" from M13.mls_ne rfl,
      show ofString "ly" ≠ ofString "lc" from M13.mls_ne rfl,
      show ofString "ln" ≠ ofString "lc" from M13.mls_ne rfl]
  have hm5_ln : m5.locals.lookup (ofString "ln") = some (.val (.word lnw)) := by
    rw [hm5_loc, hm4_loc, hm3_loc, hm2_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, lnw,
      show ofString "ls" ≠ ofString "ln" from M13.mls_ne rfl,
      show ofString "lr" ≠ ofString "ln" from M13.mls_ne rfl,
      show ofString "ly" ≠ ofString "ln" from M13.mls_ne rfl]
  have hm5_ly : m5.locals.lookup (ofString "ly") = some (.val (.word lyw)) := by
    rw [hm5_loc, hm4_loc, hm3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, lyw,
      show ofString "ls" ≠ ofString "ly" from M13.mls_ne rfl,
      show ofString "lr" ≠ ofString "ly" from M13.mls_ne rfl]
  have hm5_lr : m5.locals.lookup (ofString "lr") = some (.val (.word lrw)) := by
    rw [hm5_loc, hm4_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, lrw,
      show ofString "ls" ≠ ofString "lr" from M13.mls_ne rfl]
  have hm5_ls : m5.locals.lookup (ofString "ls") = some (.val (.word lsw)) := by
    rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, lsw]
  rw [evaluateHOLFiniteState_return]
  let retw : BitVec 64 := lcw + (21#64 + (lnw + (lyw + (lrw + (lsw + 0#64)))))
  have hev_ret : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a))
      (.op .add [
        .var .local (ofString "lc"), .const 21#64,
        .var .local (ofString "ln"), .var .local (ofString "ly"),
        .var .local (ofString "lr"), .var .local (ofString "ls")]) =
      some (.val (.word retw)) := by
    simp [evalHOLExact, evalListHOLExact, hm5_lc, hm5_ln, hm5_ly, hm5_lr, hm5_ls,
      wordOpHOL, wordOp, valueIsWord, valueWord, retw]
  rw [hev_ret]; dsimp only
  have hsz : sizeOfShapeWithContextHOL m5.structs (shapeOfHOLExact (.val (.word retw) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  have hret_eq : retw = BitVec.ofNat 64 (authEntryPayloadPure s aw.toNat) := by
    have hc_b := (u256ByteLengthPure_bounds
      (BitVec.ofNat 64 (memW s (aw.toNat + 0))) (BitVec.ofNat 64 (memW s (aw.toNat + 8)))
      (BitVec.ofNat 64 (memW s (aw.toNat + 16))) (BitVec.ofNat 64 (memW s (aw.toNat + 24)))).2.2.2.2
    have hr_b := (u256ByteLengthPure_bounds
      (BitVec.ofNat 64 (memW s (aw.toNat + 56))) (BitVec.ofNat 64 (memW s (aw.toNat + 64)))
      (BitVec.ofNat 64 (memW s (aw.toNat + 72))) (BitVec.ofNat 64 (memW s (aw.toNat + 80)))).2.2.2.2
    have hs_b := (u256ByteLengthPure_bounds
      (BitVec.ofNat 64 (memW s (aw.toNat + 88))) (BitVec.ofNat 64 (memW s (aw.toNat + 96)))
      (BitVec.ofNat 64 (memW s (aw.toNat + 104))) (BitVec.ofNat 64 (memW s (aw.toNat + 112)))).2.2.2.2
    have hn_b := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s (aw.toNat + 40)))
    have hy_b := rlpWordEncodedLenPure_bounds (BitVec.ofNat 64 (memW s (aw.toNat + 48)))
    have ha08 : aw.toNat + 0 + 8 = aw.toNat + 8 := by omega
    have ha016 : aw.toNat + 0 + 16 = aw.toNat + 16 := by omega
    have ha024 : aw.toNat + 0 + 24 = aw.toNat + 24 := by omega
    have ha568 : aw.toNat + 56 + 8 = aw.toNat + 64 := by omega
    have ha5616 : aw.toNat + 56 + 16 = aw.toNat + 72 := by omega
    have ha5624 : aw.toNat + 56 + 24 = aw.toNat + 80 := by omega
    have ha888 : aw.toNat + 88 + 8 = aw.toNat + 96 := by omega
    have ha8816 : aw.toNat + 88 + 16 = aw.toNat + 104 := by omega
    have ha8824 : aw.toNat + 88 + 24 = aw.toNat + 112 := by omega
    apply BitVec.eq_of_toNat_eq
    dsimp only [retw, lcw, lnw, lyw, lrw, lsw, authEntryPayloadPure]
    rw [ha08, ha016, ha024, ha568, ha5616, ha5624, ha888, ha8816, ha8824]
    simp only [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hret_eq]
  exact ⟨rfl, heff5.locals_clock _ m5.clock, hm5_mem⟩

private theorem eval_decCall_auth_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (aExp : ExpHOL 64)
    (aw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR : ArenaReady s)
    (hm0 : s.memory = s0.memory)
    (ha_ok : WordsOK s (aw.toNat, 120))
    (ha_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      aExp = some (.val (.word aw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "auth_payload_len") [aExp] cont)).1 ≠
      some .timeOut) :
    let pl := BitVec.ofNat 64 (authEntryPayloadPure s0 aw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      pl.toNat = authEntryPayloadPure s0 aw.toNat ∧
      26 ≤ pl.toNat ∧ pl.toNat ≤ 138 ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word pl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "auth_payload_len") [aExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro pl
  have hcode : s.code = originalRuntimeCode := hAR.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [aExp] =
      some [.val (.word aw)] := by simp [evalListHOLFinite, evalListHOLExact, ha_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "auth_payload_len") (ofString "a")
    (sourceFnBody Guest.Software.guestFn_auth_payload_len) aw
    (by rw [hcode]; exact lookup_auth_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word aw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_a : ent.locals.lookup (ofString "a") = some (.val (.word aw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent :=
      ((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).arena
    have ha_ent : WordsOK ent (aw.toNat, 120) := by
      obtain ⟨h1, h2, h3⟩ := ha_ok
      exact ⟨h1, h2, fun k hk => by obtain ⟨w, hd, hm⟩ := h3 k hk; exact ⟨w, hd, hm⟩⟩
    have hpl_eq : authEntryPayloadPure ent aw.toNat = authEntryPayloadPure s0 aw.toNat := by
      unfold authEntryPayloadPure memW
      have hm_ent : ent.memory = s0.memory := hm0
      rw [hm_ent]
    rcases hap : evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_auth_payload_len) with ⟨rap, sap⟩
    have hnt_ap : rap ≠ some .timeOut := by
      rintro rfl; rw [hap] at hnt; exact hnt rfl
    obtain ⟨hr_ap, heff_ap, hmem_ap⟩ := eval_auth_payload_len_body_exact ent aw hent_AR ha_ent
      hent_a (by rw [hap]; exact hnt_ap)
    rw [hap] at hr_ap heff_ap hmem_ap
    dsimp only at hr_ap heff_ap hmem_ap
    rw [hpl_eq] at hr_ap
    subst hr_ap
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word pl) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hap] at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word pl)) { sap with locals := s.locals }
    have hmid_eff0 : HeapByteEff s mid [] [] :=
      (((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).trans heff_ap).locals_clock
        mid.locals mid.clock
    have hmid_eff : HeapByteEff s mid Rl gw :=
      hmid_eff0.mono (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => False.elim (List.not_mem_nil h))
    have hbnd := authEntryPayloadPure_bounds s0 aw.toNat
    have hpl_nat : pl.toNat = authEntryPayloadPure s0 aw.toNat := by
      dsimp [pl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hpl_nat, by omega, by omega, hmem_ap, rfl, hmid_eff, hnt, rfl⟩

private def authLenLoopBody : ProgHOL 64 :=
  .decCall (ofString "pl") .one (ofString "auth_payload_len")
    [.op .add
      [.var .local (ofString "recs"),
       .panop .mul [.var .local (ofString "i"), .const 120#64]]]
    (.decCall (ofString "h") .one (ofString "rlp_list_header_len")
      [.var .local (ofString "pl")]
      (.seq
        (.assign .local (ofString "total")
          (.op .add [.var .local (ofString "total"),
            .var .local (ofString "h"), .var .local (ofString "pl")]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def authLenWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    authLenLoopBody

private theorem authLenWhile_exact {F : Type}
    (clk : Nat) (s0 t : PanSemStateFiniteExact 64 F)
    (recsw nw iw totw : BitVec 64)
    (hclk : t.clock ≤ clk)
    (heff : HeapByteEff s0 t [] [])
    (hm_eq : t.memory = s0.memory)
    (hAR0 : ArenaReady s0)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hi_le : iw.toNat ≤ nw.toNat)
    (htot_eq : totw.toNat = authListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_tot : t.locals.lookup (ofString "total") = some (.val (.word totw)))
    (hnt : (evaluateHOLFiniteState t authLenWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t authLenWhile
    out.1 = none ∧
    HeapByteEff s0 out.2 [] [] ∧
    out.2.memory = s0.memory ∧
    ∃ tot_f : BitVec 64,
      out.2.locals.lookup (ofString "total") = some (.val (.word tot_f)) ∧
      tot_f.toNat = authListPayloadSumPure s0 recsw.toNat nw.toNat := by
  have hhe_lt : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  induction clk generalizing t iw totw with
  | zero =>
    dsimp only [authLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hcz : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hcz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, heff, hm_eq, totw, ht_tot, by rw [← hij]; exact htot_eq⟩
  | succ clk ih =>
    dsimp only [authLenWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hcz : t.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        have hwok0 := hrecs_ok (by omega)
        set td := decClockHOLFinite t
        have htd_eff : HeapByteEff s0 td [] [] := heff.locals_clock t.locals (t.clock - 1)
        have htd_mem : td.memory = s0.memory := hm_eq
        have htd_AR : ArenaReady td := htd_eff.arena
        have htd_recs : td.locals.lookup (ofString "recs") = some (.val (.word recsw)) := ht_recs
        have htd_n : td.locals.lookup (ofString "n") = some (.val (.word nw)) := ht_n
        have htd_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := ht_i
        have htd_tot : td.locals.lookup (ofString "total") = some (.val (.word totw)) := ht_tot
        have hcle_body := evaluateHOLFiniteState_clock_le td authLenLoopBody
        have hnt_b : (evaluateHOLFiniteState td authLenLoopBody).1 ≠ some .timeOut := by
          rcases hb_res : evaluateHOLFiniteState td authLenLoopBody with ⟨rb, sb⟩
          rintro rfl; simp [hb_res] at hnt
        have hbody_step :
            let rb := evaluateHOLFiniteState td authLenLoopBody
            rb.1 = none ∧
            HeapByteEff s0 rb.2 [] [] ∧
            rb.2.memory = s0.memory ∧
            rb.2.locals.lookup (ofString "recs") = some (.val (.word recsw)) ∧
            rb.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
            rb.2.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) ∧
            ∃ totw' : BitVec 64,
              rb.2.locals.lookup (ofString "total") = some (.val (.word totw')) ∧
              totw'.toNat = authListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
          dsimp only [authLenLoopBody] at hnt_b ⊢
          have hrec0_lt_he : recsw.toNat < heapEnd := by
            obtain ⟨_, hd0, _⟩ := hwok0.2.2 0 (by omega)
            rw [hAR0.1.memaddrs] at hd0
            have ho0 := (ordinaryDomain_iff (BitVec.ofNat 64 (recsw.toNat + 8 * 0))).1 hd0
            have hb0 : (BitVec.ofNat 64 (recsw.toNat + 8 * 0)).toNat = recsw.toNat := by
              rw [Nat.add_zero, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt recsw.isLt
            rw [hb0] at ho0; exact ho0.2.2
          let aw : BitVec 64 := recsw + (iw * 120#64 + 0#64)
          have haw_nat : aw.toNat = recsw.toNat + 120 * iw.toNat := by
            have hhe_val : heapEnd = 33806089704 := heapEnd_val
            have hi120 : (iw * 120#64).toNat = 120 * iw.toNat := by
              rw [BitVec.toNat_mul]; change (iw.toNat * 120) % 2 ^ 64 = _; rw [Nat.mul_comm]
              exact Nat.mod_eq_of_lt (by omega)
            change (recsw + (iw * 120#64 + 0#64)).toNat = _
            rw [BitVec.add_zero, BitVec.toNat_add, hi120]
            exact Nat.mod_eq_of_lt (by omega)
          have hev_a : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
              (.op .add [.var .local (ofString "recs"),
                .panop .mul [.var .local (ofString "i"), .const 120#64]]) =
              some (.val (.word aw)) := by
            simp [evalHOLExact, evalListHOLExact, htd_recs, htd_i, panOpHOL, wordOpHOL, wordOp,
              valueIsWord, valueWord, aw]
          have ha_ok_td : WordsOK td (aw.toNat, 120) := by
            rw [haw_nat]
            refine ⟨by have := hwok0.1; dsimp only at this ⊢; omega, by dsimp only, fun k hk => ?_⟩
            have hk_big : 15 * iw.toNat + k < (120 * nw.toNat) / 8 := by dsimp only at hk; omega
            obtain ⟨w, hd, hm⟩ := hwok0.2.2 (15 * iw.toNat + k) hk_big
            have heq : recsw.toNat + 8 * (15 * iw.toNat + k) =
                recsw.toNat + 120 * iw.toNat + 8 * k := by omega
            rw [heq] at hd hm
            exact ⟨w, by rw [htd_eff.memaddrs]; exact hd, by rw [htd_mem]; exact hm⟩
          obtain ⟨s1, hpl_nat, hpl26, hpl138, hs1_mem_td, hs1_loc, heff_s1, hnt_s1, hdc_pl⟩ :=
            eval_decCall_auth_payload_len s0 td "pl" _ aw _ [] [] htd_AR htd_mem ha_ok_td hev_a hnt_b
          rw [hdc_pl]
          set plw := BitVec.ofNat 64 (authEntryPayloadPure s0 aw.toNat)
          have hs1_eff : HeapByteEff s0 s1 [] [] := htd_eff.trans heff_s1
          have hs1_mem : s1.memory = s0.memory := hs1_mem_td.trans htd_mem
          have hs1_AR : ArenaReady s1 := hs1_eff.arena
          have hs1_code : s1.code = originalRuntimeCode := hs1_AR.1.code
          have hs1_pl : s1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
            rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨s2, hh_nat, hh1, hh9, _, hs2_mem_s1, hs2_loc, heff_s2, hnt_s2, hdc_h⟩ :=
            eval_decCall_rlp_list_header_len s1 "h" (.var .local (ofString "pl")) plw _ [] []
              hs1_code hs1_AR (by simp [evalHOLExact, hs1_pl]) hnt_s1
          rw [hdc_h]
          set hw := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
          have hs2_eff : HeapByteEff s0 s2 [] [] := hs1_eff.trans heff_s2
          have hs2_mem : s2.memory = s0.memory := hs2_mem_s1.trans hs1_mem
          have hs2_h : s2.locals.lookup (ofString "h") = some (.val (.word hw)) := by
            rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs2_pl : s2.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
            rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_pl,
              show ofString "h" ≠ ofString "pl" from M13.mls_ne rfl]
          have hs2_tot : s2.locals.lookup (ofString "total") = some (.val (.word totw)) := by
            rw [hs2_loc, hs1_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, htd_tot,
              show ofString "h" ≠ ofString "total" from M13.mls_ne rfl,
              show ofString "pl" ≠ ofString "total" from M13.mls_ne rfl]
          have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hs2_loc, hs1_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, htd_i,
              show ofString "h" ≠ ofString "i" from M13.mls_ne rfl,
              show ofString "pl" ≠ ofString "i" from M13.mls_ne rfl]
          have hs2_recs : s2.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
            rw [hs2_loc, hs1_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, htd_recs,
              show ofString "h" ≠ ofString "recs" from M13.mls_ne rfl,
              show ofString "pl" ≠ ofString "recs" from M13.mls_ne rfl]
          have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hs2_loc, hs1_loc]
            simp [HolFiniteMapExact.lookup_update, FUPDATE, htd_n,
              show ofString "h" ≠ ofString "n" from M13.mls_ne rfl,
              show ofString "pl" ≠ ofString "n" from M13.mls_ne rfl]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          let totw' : BitVec 64 := totw + (hw + (plw + 0#64))
          have hev_tot' : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.op .add [.var .local (ofString "total"),
                .var .local (ofString "h"), .var .local (ofString "pl")]) =
              some (.val (.word totw')) := by
            simp [evalHOLExact, evalListHOLExact, hs2_tot, hs2_h, hs2_pl,
              wordOpHOL, wordOp, valueIsWord, valueWord, totw']
          rw [hev_tot']; dsimp only
          have hvv_tot : isValidValueHOLFinite s2 .local (ofString "total") (.val (.word totw')) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs2_tot, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv_tot]; dsimp only
          set s3 := setKvarHOLFinite .local (ofString "total") (.val (.word totw')) s2
          have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            simp [s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_i,
              show ofString "total" ≠ ofString "i" from M13.mls_ne rfl]
          rw [evaluateHOLFiniteState_assign]
          have hev_i' : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) =
              some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_i']; dsimp only
          have hvv_i : isValidValueHOLFinite s3 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_i, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv_i]; dsimp only
          set s4 := setKvarHOLFinite .local (ofString "i") (.val (.word (iw + 1#64))) s3
          have htot_prev := authListPayloadSumPure_bound s0 recsw.toNat iw.toNat
          have htotw'_nat : totw'.toNat = authListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
            change (totw + (hw + (plw + 0#64))).toNat = _
            rw [BitVec.add_zero]
            have hpl_eq2 : plw.toNat = authEntryPayloadPure s0 (recsw.toNat + 120 * iw.toNat) := by
              rw [hpl_nat, haw_nat]
            have hsum_h : (hw + plw).toNat = authEntryTotalPure s0 recsw.toNat iw.toNat := by
              rw [BitVec.toNat_add, hh_nat, hpl_eq2]
              dsimp only [authEntryTotalPure]
              have hq := (rlpHeaderLenPure_bounds (authEntryPayloadPure s0 (recsw.toNat + 120 * iw.toNat))).2
              have hp := authEntryPayloadPure_bounds s0 (recsw.toNat + 120 * iw.toNat)
              exact Nat.mod_eq_of_lt (by omega)
            rw [BitVec.toNat_add, htot_eq, hsum_h, authListPayloadSumPure_succ]
            have het_b := authEntryTotalPure_bound s0 recsw.toNat iw.toNat
            exact Nat.mod_eq_of_lt (by
              have : 147 * iw.toNat ≤ 147 * (2 ^ 32) := Nat.mul_le_mul_left 147 (by omega)
              omega)
          refine ⟨rfl, hs2_eff.locals_clock _ s4.clock, hs2_mem, ?_, ?_, ?_, totw', ?_, htotw'_nat⟩
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s4, s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_recs,
              show ofString "i" ≠ ofString "recs" from M13.mls_ne rfl,
              show ofString "total" ≠ ofString "recs" from M13.mls_ne rfl]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s4, s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_n,
              show ofString "i" ≠ ofString "n" from M13.mls_ne rfl,
              show ofString "total" ≠ ofString "n" from M13.mls_ne rfl]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · rw [txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl),
                txEnc_lookup_resVarEq_ne _ _ _ _ (M13.mls_ne rfl)]
            simp [s4, s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "total" from M13.mls_ne rfl]
        rcases hb_ev : evaluateHOLFiniteState td authLenLoopBody with ⟨rb, sb⟩
        simp only [hb_ev] at hbody_step hcle_body hnt ⊢
        obtain ⟨rfl, hsb_eff, hsb_mem, hsb_recs, hsb_n, hsb_i, totw', hsb_tot, htotw'_nat⟩ := hbody_step
        dsimp only at hnt ⊢
        have hi1_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hclk_sb : sb.clock ≤ clk := by
          change sb.clock ≤ t.clock - 1 at hcle_body; omega
        exact ih sb (iw + 1#64) totw' hclk_sb hsb_eff hsb_mem
          (by rw [hi1_nat]; omega) (by rw [hi1_nat]; exact htotw'_nat)
          hsb_recs hsb_n hsb_i hsb_tot hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨rfl, heff, hm_eq, totw, ht_tot, by rw [← hij]; exact htot_eq⟩

private theorem eval_auth_list_payload_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (recsw nw : BitVec 64)
    (hAR : ArenaReady s)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s (recsw.toNat, 120 * nw.toNat))
    (hs_recs : s.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (hs_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64
        (authListPayloadSumPure s recsw.toNat nw.toNat))))) ∧
    HeapByteEff s (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2 [] [] ∧
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_auth_list_payload_len)).2.memory = s.memory := by
  have hb : sourceFnBody Guest.Software.guestFn_auth_list_payload_len =
      .dec (ofString "total") .one (.const 0#64)
        (.dec (ofString "i") .one (.const 0#64)
          (.seq authLenWhile (.return (.var .local (ofString "total"))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "total") (.val (.word 0#64)) s
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
  have hs2_recs : s2.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_recs,
      show ofString "total" ≠ ofString "recs" from M13.mls_ne rfl,
      show ofString "i" ≠ ofString "recs" from M13.mls_ne rfl]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_n,
      show ofString "total" ≠ ofString "n" from M13.mls_ne rfl,
      show ofString "i" ≠ ofString "n" from M13.mls_ne rfl]
  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_tot : s2.locals.lookup (ofString "total") = some (.val (.word 0#64)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "total" from M13.mls_ne rfl]
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hw : evaluateHOLFiniteState s2 authLenWhile with ⟨rw0, sw⟩
  have hnt_w : rw0 ≠ some .timeOut := by
    rintro rfl; simp [hw] at hnt
  have hloop := authLenWhile_exact s2.clock s s2 recsw nw 0#64 0#64
    (Nat.le_refl _) ((HeapByteEff.refl hAR [] []).locals_clock s2.locals s2.clock)
    rfl hAR hn_lt (by simp)
    (by simp [authListPayloadSumPure]) hrecs_ok hs2_recs hs2_n hs2_i hs2_tot
    (by rw [hw]; exact hnt_w)
  rw [hw] at hloop; dsimp only at hloop
  obtain ⟨rfl, hsw_eff, hsw_mem, tot_f, hsw_tot, htot_nat⟩ := hloop
  simp only [hw] at hnt ⊢
  rw [evaluateHOLFiniteState_return]
  have hev_tot : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
      (.var .local (ofString "total")) = some (.val (.word tot_f)) := by
    simp [evalHOLExact, hsw_tot]
  rw [hev_tot]; dsimp only
  have hsz : sizeOfShapeWithContextHOL sw.structs (shapeOfHOLExact (.val (.word tot_f) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  have htot : tot_f = BitVec.ofNat 64 (authListPayloadSumPure s recsw.toNat nw.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← htot_nat, Nat.mod_eq_of_lt tot_f.isLt]
  rw [htot]
  exact ⟨rfl, hsw_eff.locals_clock _ _, hsw_mem⟩

private theorem eval_decCall_auth_list_payload_len {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (recsExp nExp : ExpHOL 64)
    (recsw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR : ArenaReady s)
    (hm0 : s.memory = s0.memory)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ok : 0 < nw.toNat → WordsOK s (recsw.toNat, 120 * nw.toNat))
    (hrecs_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      recsExp = some (.val (.word recsw)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      nExp = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "auth_list_payload_len") [recsExp, nExp] cont)).1 ≠
      some .timeOut) :
    let au := BitVec.ofNat 64 (authListPayloadSumPure s0 recsw.toNat nw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      au.toNat = authListPayloadSumPure s0 recsw.toNat nw.toNat ∧
      au.toNat ≤ 147 * nw.toNat ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word au)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "auth_list_payload_len") [recsExp, nExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro au
  have hcode : s.code = originalRuntimeCode := hAR.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [recsExp, nExp] = some [.val (.word recsw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hrecs_ev, hn_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "auth_list_payload_len")
    (ofString "recs") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_auth_list_payload_len) recsw nw (by decide)
    (by rw [hcode]; exact lookup_auth_list_payload_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "recs", ValueHOL.val (.word recsw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" from M13.mls_ne rfl]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent :=
      ((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).arena
    have hent_mem : ent.memory = s0.memory := hm0
    have hsum_eq : authListPayloadSumPure ent recsw.toNat nw.toNat =
        authListPayloadSumPure s0 recsw.toNat nw.toNat := by
      unfold authListPayloadSumPure authEntryTotalPure authEntryPayloadPure memW
      rw [hent_mem]
    have hrecs_ent : 0 < nw.toNat → WordsOK ent (recsw.toNat, 120 * nw.toNat) := by
      intro hpos
      obtain ⟨h1, h2, h3⟩ := hrecs_ok hpos
      exact ⟨h1, h2, fun k hk => by obtain ⟨w, hd, hm⟩ := h3 k hk; exact ⟨w, hd, hm⟩⟩
    rcases hal : evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_auth_list_payload_len) with ⟨ral, sal⟩
    have hnt_al : ral ≠ some .timeOut := by
      rintro rfl; rw [hal] at hnt; exact hnt rfl
    obtain ⟨hr_al, heff_al, hmem_al⟩ := eval_auth_list_payload_len_body_exact ent recsw nw
      hent_AR hn_lt hrecs_ent hent_recs hent_n (by rw [hal]; exact hnt_al)
    rw [hal] at hr_al heff_al hmem_al
    dsimp only at hr_al heff_al hmem_al
    rw [hsum_eq] at hr_al
    subst hr_al
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word au) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word au) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hal] at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word au)) { sal with locals := s.locals }
    have hmid_eff0 : HeapByteEff s mid [] [] :=
      (((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).trans heff_al).locals_clock
        mid.locals mid.clock
    have hmid_eff : HeapByteEff s mid Rl gw :=
      hmid_eff0.mono (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => False.elim (List.not_mem_nil h))
    have hbnd := authListPayloadSumPure_bound s0 recsw.toNat nw.toNat
    have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
    have hau_nat : au.toNat = authListPayloadSumPure s0 recsw.toNat nw.toNat := by
      dsimp [au]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hau_nat, by rw [hau_nat]; exact hbnd, hmem_al, rfl, hmid_eff, hnt, rfl⟩

private def txEncodeBoundPure {F : Type} (s0 : PanSemStateFiniteExact 64 F) (tx : Nat) : Nat :=
  655 + memW s0 (tx + 200) +
  accessListPayloadSumPure s0 (memW s0 (tx + 208)) (memW s0 (tx + 216)) +
  authListPayloadSumPure s0 (memW s0 (tx + 272)) (memW s0 (tx + 280)) +
  33 * memW s0 (tx + 264)

private theorem eval_tx_encode_bound_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (txw : BitVec 64)
    (hAR : ArenaReady s)
    (htx_v : TxValidAt s txw.toNat)
    (hs_tx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hnt : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_tx_encode_bound)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_tx_encode_bound)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (txEncodeBoundPure s txw.toNat))))) ∧
    HeapByteEff s (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_tx_encode_bound)).2 [] [] ∧
    (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_tx_encode_bound)).2.memory = s.memory := by
  obtain ⟨htx_wok, _, _, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, hal_wok, hau_wok⟩ := htx_v
  have h384_lt : 384 < 2 ^ 40 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hb : sourceFnBody Guest.Software.guestFn_tx_encode_bound =
      .decCall (ofString "al") .one (ofString "access_list_payload_len")
        [.load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
         .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])]
        (.decCall (ofString "au") .one (ofString "auth_list_payload_len")
          [.load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
           .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])]
          (.dec (ofString "bh") .one
            (.panop .mul [.const 33#64,
              .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
            (.return (.op .add [
              .const 64#64,
              .panop .mul [.const 17#64, .const 33#64],
              .const 30#64,
              .load .one (.op .add [.var .local (ofString "tx"), .const 200#64]),
              .var .local (ofString "al"),
              .var .local (ofString "au"),
              .var .local (ofString "bh")])))) := rfl
  rw [hb] at hnt ⊢
  have hwok_pres : ∀ {t : PanSemStateFiniteExact 64 F}, HeapByteEff s t [] [] → t.memory = s.memory →
      WordsOK t (txw.toNat, 384) := by
    intro t heff hm
    obtain ⟨h1, h2, h3⟩ := htx_wok
    exact ⟨h1, h2, fun k hk => by
      obtain ⟨w, hd, hmw⟩ := h3 k hk
      exact ⟨w, by rw [heff.memaddrs]; exact hd, by rw [hm]; exact hmw⟩⟩
  have hmw_lt64 : ∀ off, off % 8 = 0 → off + 8 ≤ 384 → memW s (txw.toNat + off) < 2 ^ 64 := by
    intro off hoff8 hoff_hi
    obtain ⟨⟨w, _, hm⟩, _, _⟩ := txEnc_wordsOK_wordAt_memW hAR (M13.LocFrame.refl s) htx_wok off hoff8 hoff_hi h384_lt
    unfold memW; rw [hm]; simp [w.isLt]
  -- Step 1: al = access_list_payload_len(memW(tx+208), memW(tx+216))
  have hev_208 := txEnc_wordsOK_eval_load_word hAR (M13.LocFrame.refl s) htx_wok "tx" hs_tx 208
    (by decide) (by decide) h384_lt
  have hev_216 := txEnc_wordsOK_eval_load_word hAR (M13.LocFrame.refl s) htx_wok "tx" hs_tx 216
    (by decide) (by decide) h384_lt
  let alRecsW := BitVec.ofNat 64 (memW s (txw.toNat + 208))
  let alNW := BitVec.ofNat 64 (memW s (txw.toNat + 216))
  have halRecs_nat : alRecsW.toNat = memW s (txw.toNat + 208) := by
    dsimp [alRecsW]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (hmw_lt64 208 (by decide) (by decide))
  have halN_nat : alNW.toNat = memW s (txw.toNat + 216) := by
    dsimp [alNW]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨m1, hal_nat, hal_le, hm1_mem_s, hm1_loc, heff1, hnt1, hdc1⟩ :=
    eval_decCall_access_list_payload_len s s "al" _ _ alRecsW alNW _ [] [] hAR rfl
      (by rw [halN_nat]; exact hnal_lt)
      (by rw [halRecs_nat, halN_nat]; exact hslots_lt)
      (by rw [halRecs_nat, halN_nat]; exact hal_wok)
      hev_208 hev_216 hnt
  rw [hdc1]
  have hm1_AR : ArenaReady m1 := heff1.arena
  have hm1_tx : m1.locals.lookup (ofString "tx") = some (.val (.word txw)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_tx,
      show ofString "al" ≠ ofString "tx" from M13.mls_ne rfl]
  -- Step 2: au = auth_list_payload_len(memW(tx+272), memW(tx+280))
  have hev_272 := txEnc_wordsOK_eval_load_word hm1_AR (M13.LocFrame.refl m1) (hwok_pres heff1 hm1_mem_s)
    "tx" hm1_tx 272 (by decide) (by decide) h384_lt
  have hev_280 := txEnc_wordsOK_eval_load_word hm1_AR (M13.LocFrame.refl m1) (hwok_pres heff1 hm1_mem_s)
    "tx" hm1_tx 280 (by decide) (by decide) h384_lt
  have hmw_m1 : ∀ d, memW m1 d = memW s d := fun d => by unfold memW; rw [hm1_mem_s]
  rw [hmw_m1] at hev_272 hev_280
  let auRecsW := BitVec.ofNat 64 (memW s (txw.toNat + 272))
  let auNW := BitVec.ofNat 64 (memW s (txw.toNat + 280))
  have hauRecs_nat : auRecsW.toNat = memW s (txw.toNat + 272) := by
    dsimp [auRecsW]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (hmw_lt64 272 (by decide) (by decide))
  have hauN_nat : auNW.toNat = memW s (txw.toNat + 280) := by
    dsimp [auNW]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hau_wok_m1 : 0 < auNW.toNat → WordsOK m1 (auRecsW.toNat, 120 * auNW.toNat) := by
    rw [hauRecs_nat, hauN_nat]
    intro hpos
    obtain ⟨h1, h2, h3⟩ := hau_wok hpos
    exact ⟨h1, h2, fun k hk => by
      obtain ⟨w, hd, hmw⟩ := h3 k hk
      exact ⟨w, by rw [heff1.memaddrs]; exact hd, by rw [hm1_mem_s]; exact hmw⟩⟩
  obtain ⟨m2, hau_nat, hau_le, hm2_mem_m1, hm2_loc, heff2_step, hnt2, hdc2⟩ :=
    eval_decCall_auth_list_payload_len s m1 "au" _ _ auRecsW auNW _ [] [] hm1_AR hm1_mem_s
      (by rw [hauN_nat]; exact hnau_lt) hau_wok_m1 hev_272 hev_280 hnt1
  rw [hdc2]
  have heff2 : HeapByteEff s m2 [] [] := heff1.trans heff2_step
  have hm2_mem : m2.memory = s.memory := hm2_mem_m1.trans hm1_mem_s
  have hm2_AR : ArenaReady m2 := heff2.arena
  have hm2_tx : m2.locals.lookup (ofString "tx") = some (.val (.word txw)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_tx,
      show ofString "au" ≠ ofString "tx" from M13.mls_ne rfl]
  -- Step 3: dec "bh" = 33 * memW(tx+264)
  rw [evaluateHOLFiniteState_dec_total] at hnt2 ⊢; dsimp only at hnt2 ⊢
  have hev_264 := txEnc_wordsOK_eval_load_word hm2_AR (M13.LocFrame.refl m2) (hwok_pres heff2 hm2_mem)
    "tx" hm2_tx 264 (by decide) (by decide) h384_lt
  have hmw_m2 : ∀ d, memW m2 d = memW s d := fun d => by unfold memW; rw [hm2_mem]
  rw [hmw_m2] at hev_264
  let bhw : BitVec 64 := 33#64 * BitVec.ofNat 64 (memW s (txw.toNat + 264))
  have hbhw_nat : bhw.toNat = 33 * memW s (txw.toNat + 264) := by
    change (33#64 * BitVec.ofNat 64 (memW s (txw.toNat + 264))).toNat = _
    rw [BitVec.toNat_mul]
    have h1 : (33#64 : BitVec 64).toNat = 33 := rfl
    have h2 : (BitVec.ofNat 64 (memW s (txw.toNat + 264))).toNat = memW s (txw.toNat + 264) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; exact Nat.mod_eq_of_lt (by omega)
  have hev_bh : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
      (.panop .mul [.const 33#64,
        .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])]) =
      some (.val (.word bhw)) := by
    have hev_l : @evalListHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
        [.const 33#64, .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])] =
        some [.val (.word 33#64), .val (.word (BitVec.ofNat 64 (memW s (txw.toNat + 264))))] := by
      simp only [evalListHOLExact, hev_264]
      simp [evalHOLExact]
    simp only [evalHOLExact, hev_l]
    simp [panOpHOL, valueIsWord, valueWord, bhw]
  rw [hev_bh] at hnt2 ⊢; dsimp only at hnt2 ⊢
  have hsh_bh : shapeEqHOL .one (shapeOfHOLExact (.val (.word bhw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_bh] at hnt2 ⊢; dsimp only at hnt2 ⊢
  set m3 := setVarHOLFinite (ofString "bh") (.val (.word bhw)) m2
  have hm3_eff : HeapByteEff s m3 [] [] := heff2.locals_clock m3.locals m3.clock
  have hm3_mem : m3.memory = s.memory := hm2_mem
  have hm3_AR : ArenaReady m3 := hm3_eff.arena
  have hm3_tx : m3.locals.lookup (ofString "tx") = some (.val (.word txw)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_tx,
      show ofString "bh" ≠ ofString "tx" from M13.mls_ne rfl]
  let alw := BitVec.ofNat 64 (accessListPayloadSumPure s alRecsW.toNat alNW.toNat)
  let auw := BitVec.ofNat 64 (authListPayloadSumPure s auRecsW.toNat auNW.toNat)
  have hm3_al : m3.locals.lookup (ofString "al") = some (.val (.word alw)) := by
    simp [m3, setVarHOLFinite]; rw [hm2_loc, hm1_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, alw,
      show ofString "bh" ≠ ofString "al" from M13.mls_ne rfl,
      show ofString "au" ≠ ofString "al" from M13.mls_ne rfl]
  have hm3_au : m3.locals.lookup (ofString "au") = some (.val (.word auw)) := by
    simp [m3, setVarHOLFinite]; rw [hm2_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, auw,
      show ofString "bh" ≠ ofString "au" from M13.mls_ne rfl]
  have hm3_bh : m3.locals.lookup (ofString "bh") = some (.val (.word bhw)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hev_200 := txEnc_wordsOK_eval_load_word hm3_AR (M13.LocFrame.refl m3) (hwok_pres hm3_eff hm3_mem)
    "tx" hm3_tx 200 (by decide) (by decide) h384_lt
  have hmw_m3 : ∀ d, memW m3 d = memW s d := fun d => by unfold memW; rw [hm3_mem]
  rw [hmw_m3] at hev_200
  rw [evaluateHOLFiniteState_return]
  let dataw := BitVec.ofNat 64 (memW s (txw.toNat + 200))
  let retw : BitVec 64 := 64#64 + ((17#64 * 33#64) + (30#64 + (dataw + (alw + (auw + (bhw + 0#64))))))
  have hev_ret : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
      (.op .add [
        .const 64#64,
        .panop .mul [.const 17#64, .const 33#64],
        .const 30#64,
        .load .one (.op .add [.var .local (ofString "tx"), .const 200#64]),
        .var .local (ofString "al"),
        .var .local (ofString "au"),
        .var .local (ofString "bh")]) =
      some (.val (.word retw)) := by
    have hev_l : @evalListHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
        [.const 64#64,
         .panop .mul [.const 17#64, .const 33#64],
         .const 30#64,
         .load .one (.op .add [.var .local (ofString "tx"), .const 200#64]),
         .var .local (ofString "al"),
         .var .local (ofString "au"),
         .var .local (ofString "bh")] =
        some [.val (.word 64#64), .val (.word (17#64 * 33#64)), .val (.word 30#64),
          .val (.word dataw), .val (.word alw), .val (.word auw), .val (.word bhw)] := by
      simp only [evalListHOLExact, hev_200, dataw]
      simp [evalHOLExact, evalListHOLExact, hm3_al, hm3_au, hm3_bh, panOpHOL, valueIsWord, valueWord]
    simp only [evalHOLExact, hev_l]
    simp [wordOpHOL, wordOp, valueIsWord, valueWord, retw]
  rw [hev_ret]; dsimp only
  have hsz : sizeOfShapeWithContextHOL m3.structs (shapeOfHOLExact (.val (.word retw) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  have hret_eq : retw = BitVec.ofNat 64 (txEncodeBoundPure s txw.toNat) := by
    have hmul_17_33 : (17#64 * 33#64 : BitVec 64) = 561#64 := rfl
    have hd_nat : dataw.toNat = memW s (txw.toNat + 200) := by
      dsimp [dataw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have halw_nat : alw.toNat = accessListPayloadSumPure s (memW s (txw.toNat + 208)) (memW s (txw.toNat + 216)) := by
      dsimp [alw]; rw [← halRecs_nat, ← halN_nat]; exact hal_nat
    have hauw_nat : auw.toNat = authListPayloadSumPure s (memW s (txw.toNat + 272)) (memW s (txw.toNat + 280)) := by
      dsimp [auw]; rw [← hauRecs_nat, ← hauN_nat]; exact hau_nat
    rw [halRecs_nat, halN_nat] at hal_le
    rw [hauRecs_nat, hauN_nat] at hau_le
    have hslots_lt' : ((List.range (memW s (txw.toNat + 216))).map
        (fun i => memW s (memW s (txw.toNat + 208) + 24 * i + 16))).sum < 2 ^ 32 := hslots_lt
    apply BitVec.eq_of_toNat_eq
    dsimp only [retw, txEncodeBoundPure]
    rw [hmul_17_33, BitVec.add_zero]
    simp only [BitVec.toNat_add, hd_nat, halw_nat, hauw_nat, hbhw_nat, BitVec.toNat_ofNat]
    have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
    omega
  rw [hret_eq]
  exact ⟨rfl, hm3_eff.locals_clock _ m3.clock, hm3_mem⟩

private theorem eval_decCall_tx_encode_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (txExp : ExpHOL 64)
    (txw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hAR : ArenaReady s)
    (htx_v : TxValidAt s txw.toNat)
    (htx_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      txExp = some (.val (.word txw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "tx_encode_bound") [txExp] cont)).1 ≠
      some .timeOut) :
    let bnd := BitVec.ofNat 64 (txEncodeBoundPure s txw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      bnd.toNat = txEncodeBoundPure s txw.toNat ∧
      bnd.toNat < 2 ^ 40 ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word bnd)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "tx_encode_bound") [txExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro bnd
  have hcode : s.code = originalRuntimeCode := hAR.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [txExp] =
      some [.val (.word txw)] := by simp [evalListHOLFinite, evalListHOLExact, htx_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "tx_encode_bound") (ofString "tx")
    (sourceFnBody Guest.Software.guestFn_tx_encode_bound) txw
    (by rw [hcode]; exact lookup_tx_encode_bound)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word txw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word txw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent :=
      ((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).arena
    have hent_v : TxValidAt ent txw.toNat := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := htx_v
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    have hbnd_eq : txEncodeBoundPure ent txw.toNat = txEncodeBoundPure s txw.toNat := rfl
    rcases hbd : evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_tx_encode_bound) with ⟨rbd, sbd⟩
    have hnt_bd : rbd ≠ some .timeOut := by
      rintro rfl; rw [hbd] at hnt; exact hnt rfl
    obtain ⟨hr_bd, heff_bd, hmem_bd⟩ := eval_tx_encode_bound_body_exact ent txw hent_AR hent_v
      hent_tx (by rw [hbd]; exact hnt_bd)
    rw [hbd] at hr_bd heff_bd hmem_bd
    dsimp only at hr_bd heff_bd hmem_bd
    rw [hbnd_eq] at hr_bd
    subst hr_bd
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word bnd) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word bnd) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hbd] at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word bnd)) { sbd with locals := s.locals }
    have hmid_eff0 : HeapByteEff s mid [] [] :=
      (((HeapByteEff.refl hAR [] []).locals_clock ent.locals ent.clock).trans heff_bd).locals_clock
        mid.locals mid.clock
    have hmid_eff : HeapByteEff s mid Rl gw :=
      hmid_eff0.mono (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => False.elim (List.not_mem_nil h))
    obtain ⟨_, _, _, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, _, _⟩ := htx_v
    have hslots_lt' : ((List.range (memW s (txw.toNat + 216))).map
        (fun i => memW s (memW s (txw.toNat + 208) + 24 * i + 16))).sum < 2 ^ 32 := hslots_lt
    have hal_b := accessListPayloadSumPure_bound s (memW s (txw.toNat + 208)) (memW s (txw.toNat + 216))
    have hau_b := authListPayloadSumPure_bound s (memW s (txw.toNat + 272)) (memW s (txw.toNat + 280))
    have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
    have h240 : (2 ^ 40 : Nat) = 1099511627776 := rfl
    have hbnd_lt : txEncodeBoundPure s txw.toNat < 2 ^ 40 := by
      dsimp only [txEncodeBoundPure]; omega
    have hbnd_nat : bnd.toNat = txEncodeBoundPure s txw.toNat := by
      dsimp [bnd]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨mid, hbnd_nat, by rw [hbnd_nat]; exact hbnd_lt, hmem_bd, rfl, hmid_eff, hnt, rfl⟩

private theorem eval_decCall_rlp_encode_list_header_outcomes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp pExp : ExpHOL 64)
    (dst0 pw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure pw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).1 ≠
      some .timeOut) :
    let full := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)
    let hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
    (∃ mid : PanSemStateFiniteExact 64 F,
      hl.toNat = rlpHeaderLenPure pw.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      full =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) })) ∨
    (full.1 ≠ none ∧ ¬ Resumes full.1) := by
  intro full hl; dsimp only [full]
  have hb_elh : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
      .call none (ofString "rlp_write_header")
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pExp] = some [.val (.word dst0), .val (.word pw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hp]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 pw (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_list_header)
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
      | none => exact Or.inr ⟨by simp, not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          exact Or.inr ⟨by simp, hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
        | returned rv =>
          obtain ⟨rfl, hdst_lt_he, heff_wh⟩ := hret rv rfl
          have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only at hnt ⊢
          rw [if_pos hsh1] at hnt ⊢
          dsimp only at hnt ⊢
          rw [if_pos hsh2] at hnt ⊢
          let mid := setVarHOLFinite (ofString lname) (.val (.word hl))
            { swh.emptyLocalsHOLFinite with locals := s.locals }
          have heff0 : M11.ByteRegionEffect s ent2 Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent2.locals ent2.clock
          have heff_mid : M11.ByteRegionEffect s mid Rl :=
            ((heff0.trans heff_wh).with_locals_clock _ _).with_locals_clock mid.locals mid.clock
          have hbnd := rlpHeaderLenPure_bounds pw.toNat
          have hhl_nat : hl.toNat = rlpHeaderLenPure pw.toNat := by
            dsimp [hl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          exact Or.inl ⟨mid, hhl_nat, by omega, by omega, hdst_lt_he, heff_mid.globals, rfl,
            HeapByteEff.of_m11_bre hAR heff_mid, hnt, rfl⟩
        | «break» | «continue» | error =>
          exact Or.inr ⟨by simp, not_resumes_error⟩
        | finalFfi _ =>
          exact Or.inr ⟨by simp, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem txEnc_seq_call_assign_p_exact {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : String} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {pw : BitVec 64} {exactLen : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hp_sum : pw.toNat + exactLen < 2 ^ 64)
    (hcall :
      let out := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
      (out.1 = none →
        ∃ len : BitVec 64,
          len.toNat = exactLen ∧
          out.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s out.2 Rl gw) ∧
      (out.1 ≠ none → ¬ Resumes out.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut) :
    let full := evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))
    (∃ len : BitVec 64, ∃ m : PanSemStateFiniteExact 64 F,
      len.toNat = exactLen ∧
      (pw + len).toNat = pw.toNat + exactLen ∧
      m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      full = evaluateHOLFiniteState m cont) ∨
    (full.1 ≠ none ∧ ¬ Resumes full.1) := by
  intro full; dsimp only [full]
  dsimp only at hcall
  rcases hc : evaluateHOLFiniteState s
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args) with ⟨rc, sc⟩
  rw [hc] at hcall
  dsimp only at hcall
  rw [evaluateHOLFiniteState_seq_line780, hc] at hnt ⊢
  cases rc with
  | some r =>
    dsimp only
    exact Or.inr ⟨by simp, hcall.2 (by simp)⟩
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨len, hlen_eq, hsc_loc, heff_sc⟩ := hcall.1 rfl
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word len)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt ⊢
    have hev_add : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (pw + len))) := by
      have hpz : pw + (len + 0#64) = pw + len := by rw [BitVec.add_zero]
      simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, hpz]
    rw [hev_add] at hnt ⊢; dsimp only at hnt ⊢
    have hvv : isValidValueHOLFinite sc .local (ofString "p") (.val (.word (pw + len))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hsc_p, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvv] at hnt ⊢; dsimp only at hnt ⊢
    let m := setKvarHOLFinite .local (ofString "p") (.val (.word (pw + len))) sc
    have hm_loc : m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) := by
      change sc.locals.update (ofString "p", .val (.word (pw + len))) = _
      rw [hsc_loc]
    have hm_eff : HeapByteEff s0 m Rl gw :=
      (heff0.trans heff_sc).locals_clock m.locals m.clock
    have hplen_nat : (pw + len).toNat = pw.toNat + exactLen := by
      rw [BitVec.toNat_add, hlen_eq]; exact Nat.mod_eq_of_lt (by omega)
    exact Or.inl ⟨len, m, hlen_eq, hplen_nat, hm_loc, hm_eff, hnt, rfl⟩

private theorem txEnc_seq_call_assign_p {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : String} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hp_sum : pw.toNat + bound < 2 ^ 64)
    (hcall :
      let out := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
      (out.1 = none →
        ∃ len : BitVec 64,
          len.toNat ≤ bound ∧
          out.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s out.2 Rl gw) ∧
      (out.1 ≠ none → ¬ Resumes out.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut) :
    let full := evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))
    (∃ len : BitVec 64, ∃ m : PanSemStateFiniteExact 64 F,
      len.toNat ≤ bound ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      full = evaluateHOLFiniteState m cont) ∨
    (full.1 ≠ none ∧ ¬ Resumes full.1) := by
  intro full; dsimp only [full]
  dsimp only at hcall
  rcases hc : evaluateHOLFiniteState s
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args) with ⟨rc, sc⟩
  rw [hc] at hcall
  dsimp only at hcall
  rw [evaluateHOLFiniteState_seq_line780, hc] at hnt ⊢
  cases rc with
  | some r =>
    dsimp only
    exact Or.inr ⟨by simp, hcall.2 (by simp)⟩
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨len, hlen_le, hsc_loc, heff_sc⟩ := hcall.1 rfl
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word len)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt ⊢
    have hev_add : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (pw + len))) := by
      have hpz : pw + (len + 0#64) = pw + len := by rw [BitVec.add_zero]
      simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, hpz]
    rw [hev_add] at hnt ⊢; dsimp only at hnt ⊢
    have hvv : isValidValueHOLFinite sc .local (ofString "p") (.val (.word (pw + len))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hsc_p, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvv] at hnt ⊢; dsimp only at hnt ⊢
    let m := setKvarHOLFinite .local (ofString "p") (.val (.word (pw + len))) sc
    have hm_loc : m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) := by
      change sc.locals.update (ofString "p", .val (.word (pw + len))) = _
      rw [hsc_loc]
    have hm_eff : HeapByteEff s0 m Rl gw :=
      (heff0.trans heff_sc).locals_clock m.locals m.clock
    have hplen_nat : (pw + len).toNat = pw.toNat + len.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    exact Or.inl ⟨len, m, hlen_le, hplen_nat, hm_loc, hm_eff, hnt, rfl⟩

private def txEncNoContBreak : ProgHOL 64 → Bool
  | .skip => true
  | .annot _ _ => true
  | .assign _ _ _ => true
  | .store _ _ => true
  | .store32 _ _ => true
  | .storeByte _ _ => true
  | .return _ => true
  | .raise _ _ => true
  | .while _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call none _ _ => true
  | .seq p1 p2 => txEncNoContBreak p1 && txEncNoContBreak p2
  | .ite _ p1 p2 => txEncNoContBreak p1 && txEncNoContBreak p2
  | .dec _ _ _ b => txEncNoContBreak b
  | .decCall _ _ _ _ c => txEncNoContBreak c
  | _ => false

private theorem txEncNoContBreak_while (cond : ExpHOL 64) (body : ProgHOL 64) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break := by
  intro F s
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .break from
    this s.clock s rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          rcases hbOut : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [hbOut] at hrem
          dsimp only at hrem ⊢
          have hlt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
          cases r1 with
          | none => exact ih mid.clock hlt mid rfl
          | some r1' =>
            cases r1' with
            | «continue» => exact ih mid.clock hlt mid rfl
            | «break» => simp
            | _ => simp
      · simp
    · simp

private theorem txEncNoContBreak_sound : ∀ (p : ProgHOL 64), txEncNoContBreak p = true →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s p).1 ≠ some .break
  | .skip, _, _, _ => by simp
  | .annot _ _, _, _, _ => by simp
  | .assign k n e, _, _, s => by
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | .store a v, _, _, s => by
    rw [evaluateHOLFiniteState_store]
    repeat' split
    all_goals simp
  | .store32 a v, _, _, s => by
    rw [evaluateHOLFiniteState_store32]
    repeat' split
    all_goals simp
  | .storeByte a v, _, _, s => by
    rw [evaluateHOLFiniteState_storeByte]
    repeat' split
    all_goals simp
  | .return e, _, _, s => by
    rw [evaluateHOLFiniteState_return]
    repeat' split
    all_goals simp
  | .raise n e, _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    repeat' split
    all_goals (try simp)
    all_goals (split_ifs <;> simp)
  | .while c b, _, _, s => txEncNoContBreak_while c b s
  | .call none fn args, _, _, s => by
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rsh⟩
      · simp
      · dsimp only
        split_ifs
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
          cases bres with
          | none => simp
          | some br =>
            cases br with
            | returned _ => dsimp only; split_ifs <;> simp
            | _ => simp
  | .call (some (dest, none)) fn args, _, _, s => by
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rsh⟩
      · simp
      · dsimp only
        split_ifs
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
          cases bres with
          | none => simp
          | some br =>
            cases br with
            | returned _ =>
              cases dest with
              | none => dsimp only; split_ifs <;> simp
              | some _ => dsimp only; split_ifs <;> simp
            | _ => simp
  | .call (some (_, some _)) _ _, h, _, _ => by simp [txEncNoContBreak] at h
  | .seq p1 p2, h, _, s => by
    simp only [txEncNoContBreak, Bool.and_eq_true] at h
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
    cases r1 with
    | none => exact txEncNoContBreak_sound p2 h.2 s1
    | some _ =>
      have h1 := txEncNoContBreak_sound p1 h.1 s
      rw [hr1] at h1
      exact h1
  | .ite c p1 p2, h, _, s => by
    simp only [txEncNoContBreak, Bool.and_eq_true] at h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact txEncNoContBreak_sound p2 h.2 s
      · exact txEncNoContBreak_sound p1 h.1 s
    · simp
  | .dec _ _ _ b, h, _, s => by
    simp only [txEncNoContBreak] at h
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact txEncNoContBreak_sound b h _
      · simp
  | .decCall _ _ _ _ c, h, _, s => by
    simp only [txEncNoContBreak] at h
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | values
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup _ values with _ | ⟨body, callee, ret⟩
      · simp
      · dsimp only
        split_ifs
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
          cases bres with
          | none => simp
          | some br =>
            cases br with
            | returned _ =>
              dsimp only; split_ifs
              · exact txEncNoContBreak_sound c h _
              · simp
            | _ => simp
  | .break, h, _, _ => by simp [txEncNoContBreak] at h
  | .continue, h, _, _ => by simp [txEncNoContBreak] at h
  | .primitive _ _ _, h, _, _ => by simp [txEncNoContBreak] at h
  | .extCall _ _ _ _ _, h, _, _ => by simp [txEncNoContBreak] at h
  | .shMemLoad _ _ _ _, h, _, _ => by simp [txEncNoContBreak] at h
  | .shMemStore _ _ _, h, _, _ => by simp [txEncNoContBreak] at h

private def put32BytesLoopBody (bufNm idxNm : String) : ProgHOL 64 :=
  .seq
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"),
       .op .add [.var .local (ofString bufNm),
         .panop .mul [.var .local (ofString idxNm), .const 32#64]],
       .const 32#64])
    (.seq
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.assign .local (ofString idxNm)
        (.op .add [.var .local (ofString idxNm), .const 1#64])))

private def put32BytesWhile (bufNm idxNm cntNm : String) : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString idxNm)) (.var .local (ofString cntNm)))
    (put32BytesLoopBody bufNm idxNm)

private theorem put32BytesWhile_exact {F : Type}
    (clk : Nat) (s0 t : PanSemStateFiniteExact 64 F)
    (bufNm idxNm cntNm : String)
    (p_base bufw nw idxw pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hne_bi : ofString idxNm ≠ ofString bufNm)
    (hne_ic : ofString idxNm ≠ ofString cntNm)
    (hne_pb : ofString "p" ≠ ofString bufNm)
    (hne_pi : ofString "p" ≠ ofString idxNm)
    (hne_pc : ofString "p" ≠ ofString cntNm)
    (hne_wb : ofString "w" ≠ ofString bufNm)
    (hne_wi : ofString "w" ≠ ofString idxNm)
    (hne_wc : ofString "w" ≠ ofString cntNm)
    (hclk : t.clock ≤ clk)
    (heff : HeapByteEff s0 t Rl gw)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hi_le : idxw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = p_base.toNat + 33 * idxw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
      p_base.toNat + 33 * nw.toNat ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (ht_buf : t.locals.lookup (ofString bufNm) = some (.val (.word bufw)))
    (ht_cnt : t.locals.lookup (ofString cntNm) = some (.val (.word nw)))
    (ht_idx : t.locals.lookup (ofString idxNm) = some (.val (.word idxw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_w : ∃ w_old : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState t (put32BytesWhile bufNm idxNm cntNm)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t (put32BytesWhile bufNm idxNm cntNm)
    (out.1 = none →
      HeapByteEff s0 out.2 Rl gw ∧
      (∀ k, k ≠ ofString "p" → k ≠ ofString "w" → k ≠ ofString idxNm →
        out.2.locals.lookup k = t.locals.lookup k) ∧
      (∃ w_f : BitVec 64, out.2.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      ∃ p_f : BitVec 64,
        out.2.locals.lookup (ofString "p") = some (.val (.word p_f)) ∧
        p_f.toNat = p_base.toNat + 33 * nw.toNat) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hrlp32 : rlpHeaderLenPure 32 = 1 := by decide
  induction clk generalizing t idxw pw with
  | zero =>
    dsimp only [put32BytesWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString idxNm)) (.var .local (ofString cntNm))) =
        some (.val (.word (if idxw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_idx, ht_cnt, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : idxw.toNat < nw.toNat
    · have hcz : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hcz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hij : idxw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff, fun _ _ _ _ => rfl, ht_w, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
        fun h => False.elim (h rfl)⟩
  | succ clk ih =>
    dsimp only [put32BytesWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString idxNm)) (.var .local (ofString cntNm))) =
        some (.val (.word (if idxw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_idx, ht_cnt, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : idxw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hcz : t.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set td := decClockHOLFinite t
        have htd_eff : HeapByteEff s0 td Rl gw := heff.locals_clock t.locals (t.clock - 1)
        have htd_AR : ArenaReady td := htd_eff.arena
        have htd_code : td.code = originalRuntimeCode := htd_AR.1.code
        have htd_buf : td.locals.lookup (ofString bufNm) = some (.val (.word bufw)) := ht_buf
        have htd_cnt : td.locals.lookup (ofString cntNm) = some (.val (.word nw)) := ht_cnt
        have htd_idx : td.locals.lookup (ofString idxNm) = some (.val (.word idxw)) := ht_idx
        have htd_p : td.locals.lookup (ofString "p") = some (.val (.word pw)) := ht_p
        have htd_w : ∃ w_old : BitVec 64, td.locals.lookup (ofString "w") = some (.val (.word w_old)) := ht_w
        have hcle_body := evaluateHOLFiniteState_clock_le td (put32BytesLoopBody bufNm idxNm)
        have hnt_b : (evaluateHOLFiniteState td (put32BytesLoopBody bufNm idxNm)).1 ≠ some .timeOut := by
          rcases hb_res : evaluateHOLFiniteState td (put32BytesLoopBody bufNm idxNm) with ⟨rb, sb⟩
          rintro rfl; simp [hb_res] at hnt
        let srcw : BitVec 64 := bufw + (idxw * 32#64 + 0#64)
        have hev_src : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.op .add [.var .local (ofString bufNm),
              .panop .mul [.var .local (ofString idxNm), .const 32#64]]) =
            some (.val (.word srcw)) := by
          simp [evalHOLExact, evalListHOLExact, htd_buf, htd_idx, panOpHOL, wordOpHOL, wordOp,
            valueIsWord, valueWord, srcw]
        have hnt_call : (evaluateHOLFiniteState td
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"),
               .op .add [.var .local (ofString bufNm),
                 .panop .mul [.var .local (ofString idxNm), .const 32#64]],
               .const 32#64])).1 ≠ some .timeOut := by
          dsimp only [put32BytesLoopBody] at hnt_b
          rw [evaluateHOLFiniteState_seq_line780] at hnt_b
          rcases hc : evaluateHOLFiniteState td _ with ⟨rc, _⟩
          rintro rfl; simp [hc] at hnt_b
        have hin_p : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
            pw.toNat + rlpHeaderLenPure (32#64 : BitVec 64).toNat + (32#64 : BitVec 64).toNat ≤ ivl.1 + ivl.2 := by
          obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [h32, hrlp32]
          exact ⟨ivl, hivl, by omega, by omega⟩
        have hhe_val : heapEnd = 33806089704 := heapEnd_val
        have hcall := eval_call_local_rlp_encode_bytes_n_ne_one td "w"
          (.var .local (ofString "p"))
          (.op .add [.var .local (ofString bufNm),
            .panop .mul [.var .local (ofString idxNm), .const 32#64]])
          (.const 32#64)
          pw srcw 32#64 Rl gw htd_code htd_AR htd_w
          (by simp [evalHOLExact, htd_p]) hev_src rfl
          (by decide) (by change 32 ≤ heapEnd; omega) hin_p hnt_call
        dsimp only at hcall
        have hp_sum : pw.toNat + 33 < 2 ^ 64 := by
          obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega
        have hstep := txEnc_seq_call_assign_p_exact (s0 := s0) (s := td) (Rl := Rl) (gw := gw)
          (fname := "rlp_encode_bytes")
          (args := [.var .local (ofString "p"),
            .op .add [.var .local (ofString bufNm),
              .panop .mul [.var .local (ofString idxNm), .const 32#64]],
            .const 32#64])
          (cont := .assign .local (ofString idxNm) (.op .add [.var .local (ofString idxNm), .const 1#64]))
          (pw := pw) (exactLen := 33)
          htd_eff htd_p hp_sum
          ⟨fun hnone => by
            obtain ⟨len, hlen_eq, _, _, hloc, heff_c⟩ := hcall.1 hnone
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            rw [h32, hrlp32] at hlen_eq
            exact ⟨len, hlen_eq, hloc, heff_c⟩, hcall.2⟩
          hnt_b
        change _ at hstep
        rcases hstep with ⟨len, m, hlen_eq, hplen_nat, hm_loc, hm_eff, _, hfull_eq⟩ | ⟨hne_none, hnr⟩
        · have hm_idx : m.locals.lookup (ofString idxNm) = some (.val (.word idxw)) := by
            rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, htd_idx, hne_pi, hne_wi]
          have hm_ev : evaluateHOLFiniteState m
              (.assign .local (ofString idxNm) (.op .add [.var .local (ofString idxNm), .const 1#64])) =
              (none, setKvarHOLFinite .local (ofString idxNm) (.val (.word (idxw + 1#64))) m) := by
            rw [evaluateHOLFiniteState_assign]
            have hev_i : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
                (.op .add [.var .local (ofString idxNm), .const 1#64]) =
                some (.val (.word (idxw + 1#64))) := by
              simp [evalHOLExact, evalListHOLExact, hm_idx, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_i]; dsimp only
            have hvv_i : isValidValueHOLFinite m .local (ofString idxNm) (.val (.word (idxw + 1#64))) = true := by
              simp [isValidValueHOLFinite, lookupKvarHOLFinite, hm_idx, shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hvv_i]
          have hbody_eq : evaluateHOLFiniteState td (put32BytesLoopBody bufNm idxNm) =
              (none, setKvarHOLFinite .local (ofString idxNm) (.val (.word (idxw + 1#64))) m) := by
            dsimp only [put32BytesLoopBody]; rw [hfull_eq, hm_ev]
          rw [hbody_eq] at hcle_body hnt ⊢
          dsimp only at hcle_body hnt ⊢
          set sb := setKvarHOLFinite .local (ofString idxNm) (.val (.word (idxw + 1#64))) m
          have hsb_eff : HeapByteEff s0 sb Rl gw := hm_eff.locals_clock sb.locals sb.clock
          have hsb_clk : sb.clock ≤ clk := by
            change sb.clock ≤ t.clock - 1 at hcle_body; omega
          have hi1_nat : (idxw + 1#64).toNat = idxw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (idxw.toNat + 1) % 2 ^ 64 = _
            exact Nat.mod_eq_of_lt (by omega)
          have hsb_buf : sb.locals.lookup (ofString bufNm) = some (.val (.word bufw)) := by
            simp [sb, setKvarHOLFinite, setVarHOLFinite, hm_loc, HolFiniteMapExact.lookup_update, FUPDATE,
              htd_buf, hne_bi, hne_pb, hne_wb]
          have hsb_cnt : sb.locals.lookup (ofString cntNm) = some (.val (.word nw)) := by
            simp [sb, setKvarHOLFinite, setVarHOLFinite, hm_loc, HolFiniteMapExact.lookup_update, FUPDATE,
              htd_cnt, hne_ic, hne_pc, hne_wc]
          have hsb_idx : sb.locals.lookup (ofString idxNm) = some (.val (.word (idxw + 1#64))) := by
            simp [sb, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hsb_p : sb.locals.lookup (ofString "p") = some (.val (.word (pw + len))) := by
            simp [sb, setKvarHOLFinite, setVarHOLFinite, hm_loc, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hne_pi]
          have hsb_w : ∃ w_old : BitVec 64, sb.locals.lookup (ofString "w") = some (.val (.word w_old)) := by
            refine ⟨len, ?_⟩
            simp [sb, setKvarHOLFinite, setVarHOLFinite, hm_loc, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hne_wi, show ofString "p" ≠ ofString "w" from M13.mls_ne rfl]
          have hih := ih sb (idxw + 1#64) (pw + len) hsb_clk hsb_eff
            (by rw [hi1_nat]; omega) (by rw [hplen_nat, hi1_nat]; omega)
            hsb_buf hsb_cnt hsb_idx hsb_p hsb_w hnt
          dsimp only [put32BytesWhile] at hih
          refine ⟨fun hnone => ?_, hih.2⟩
          obtain ⟨heff_f, hloc_f, hw_f, p_f, hp_f, hpf_nat⟩ := hih.1 hnone
          refine ⟨heff_f, fun k hkp hkw hki => ?_, hw_f, p_f, hp_f, hpf_nat⟩
          rw [hloc_f k hkp hkw hki]
          simp [sb, td, decClockHOLFinite, setKvarHOLFinite, setVarHOLFinite, hm_loc,
            HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkp, Ne.symm hkw, Ne.symm hki]
        · have hb_def : evaluateHOLFiniteState td (put32BytesLoopBody bufNm idxNm) =
              evaluateHOLFiniteState td
                (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                    [.var .local (ofString "p"),
                     .op .add [.var .local (ofString bufNm),
                       .panop .mul [.var .local (ofString idxNm), .const 32#64]],
                     .const 32#64])
                  (.seq (.assign .local (ofString "p")
                      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                    (.assign .local (ofString idxNm)
                      (.op .add [.var .local (ofString idxNm), .const 1#64])))) := rfl
          have hncb := txEncNoContBreak_sound (put32BytesLoopBody bufNm idxNm) rfl td
          rcases hb_res : evaluateHOLFiniteState td (put32BytesLoopBody bufNm idxNm) with ⟨rb, sb⟩
          have hrb_eq := hb_def.symm.trans hb_res
          rw [hrb_eq] at hne_none hnr
          rw [hb_res] at hnt hncb
          dsimp only at hne_none hnr hnt hncb ⊢
          cases rb with
          | none => exact False.elim (hne_none rfl)
          | some r0 =>
            cases r0 with
            | timeOut => exact absurd rfl hnt
            | «continue» => exact absurd rfl hncb.1
            | «break» => exact absurd rfl hncb.2
            | returned _ | exception _ _ | error | finalFfi _ =>
              dsimp only
              exact ⟨fun h => by simp at h, fun _ => hnr⟩
    · rw [if_neg hlt]
      have hij : idxw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff, fun _ _ _ _ => rfl, ht_w, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
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
    (hin_ivl : ∃ ivl ∈ Rl,
      ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_blob_hashes")
        [dstExp, bufExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_blob_hashes")
        [dstExp, bufExp, nExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat ∧
        len.toNat ≤ 9 + 33 * nw.toNat ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hb_body : sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes =
      .decCall (ofString "w") .one (ofString "rlp_encode_list_header")
        [.var .local (ofString "dst"),
         .panop .mul [.const 33#64, .var .local (ofString "n")]]
        (.dec (ofString "p") .one
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
          (.dec (ofString "i") .one (.const 0#64)
            (.seq (put32BytesWhile "buf" "i" "n")
              (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]))))) := rfl
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
    have hent_eff : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hAR Rl gw).locals_clock ent.locals ent.clock
    have hent_AR : ArenaReady ent := hent_eff.arena
    have hent_code : ent.code = originalRuntimeCode := hcode
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "buf" ≠ ofString "dst" by decide]
    have hent_buf : ent.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "buf" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hnt_body : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes)).1 ≠
        some .timeOut := by
      rcases hx : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_blob_hashes) with ⟨rx, sx⟩
      rintro rfl; simp [hx] at hnt
    rw [hb_body] at hnt hnt_body ⊢
    let plw : BitVec 64 := 33#64 * nw + 0#64
    have hplw_nat : plw.toNat = 33 * nw.toNat := by
      change (33#64 * nw + 0#64).toNat = _
      rw [BitVec.add_zero, BitVec.toNat_mul]
      change (33 * nw.toNat) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hev_pl : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
        (.panop .mul [.const 33#64, .var .local (ofString "n")]) = some (.val (.word plw)) := by
      simp [evalHOLExact, evalListHOLExact, hent_n, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, plw]
    have hin_hdr : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure plw.toNat ≤ ivl.1 + ivl.2 := by
      obtain ⟨ivl, hivl, hlo, hhi, _⟩ := hin_ivl
      exact ⟨ivl, hivl, hlo, by rw [hplw_nat]; omega⟩
    have hdc := eval_decCall_rlp_encode_list_header_outcomes ent "w"
      (.var .local (ofString "dst")) (.panop .mul [.const 33#64, .var .local (ofString "n")])
      dst0 plw
      (.dec (ofString "p") .one
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
        (.dec (ofString "i") .one (.const 0#64)
          (.seq (put32BytesWhile "buf" "i" "n")
            (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))
      Rl gw hent_code hent_AR
      (by simp [evalHOLExact, hent_dst]) hev_pl hin_hdr hnt_body
    dsimp only at hdc
    rcases hdc with ⟨mid, hhl_nat, hhl_ge1, hhl_le9, _, _, hmid_loc, hmid_eff, hnt_mid, hbody_eq⟩ | ⟨hne_none, hnr⟩
    · rw [hbody_eq] at hnt ⊢
      let hl := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word hl)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl]
      have hmid_buf : mid.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_buf,
          show ofString "w" ≠ ofString "buf" by decide]
      have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
          show ofString "w" ≠ ofString "n" by decide]
      let p_base : BitVec 64 := dst0 + hl
      have hp_base_nat : p_base.toNat = dst0.toNat + rlpHeaderLenPure (33 * nw.toNat) := by
        change (dst0 + hl).toNat = _
        rw [BitVec.toNat_add, hhl_nat, hplw_nat]
        obtain ⟨ivl, _, _, hhi, hlim⟩ := hin_ivl
        exact Nat.mod_eq_of_lt (by omega)
      have hev_p0 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
          some (.val (.word p_base)) := by
        simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_base]
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      simp only [hev_p0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_p := setVarHOLFinite (ofString "p") (.val (.word p_base)) mid
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      have hev_i0 : @evalHOLExact 64 F _ s_p.toExact (fun a => Classical.propDecidable (s_p.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      simp only [hev_i0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_i := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s_p
      have hsi_eff : HeapByteEff s s_i Rl gw :=
        (hent_eff.trans hmid_eff).locals_clock s_i.locals s_i.clock
      have hsi_buf : s_i.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_buf,
          show ofString "i" ≠ ofString "buf" by decide, show ofString "p" ≠ ofString "buf" by decide]
      have hsi_n : s_i.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide]
      have hsi_i : s_i.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [s_i, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsi_p : s_i.locals.lookup (ofString "p") = some (.val (.word p_base)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide]
      have hsi_w : ∃ w0 : BitVec 64, s_i.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        refine ⟨hl, ?_⟩
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]
      have hsi_dst : s_i.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide]
      rw [evaluateHOLFiniteState_seq_line780] at hnt_mid ⊢
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧ p_base.toNat + 33 * nw.toNat ≤ ivl.1 + ivl.2 ∧
          ivl.1 + ivl.2 ≤ heapLimit := by
        obtain ⟨ivl, hivl, hlo, hhi, hlim⟩ := hin_ivl
        exact ⟨ivl, hivl, by rw [hp_base_nat]; omega, by rw [hp_base_nat]; omega, hlim⟩
      have hnt_loop : (evaluateHOLFiniteState s_i (put32BytesWhile "buf" "i" "n")).1 ≠ some .timeOut := by
        rintro hto; simp [hto] at hnt_mid
      have hloop := put32BytesWhile_exact s_i.clock s s_i "buf" "i" "n" p_base bufw nw 0#64 p_base Rl gw
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (Nat.le_refl _) hsi_eff (by omega) (by simp) (by simp)
        hin_loop hsi_buf hsi_n hsi_i hsi_p hsi_w hnt_loop
      dsimp only at hloop
      rcases hw : evaluateHOLFiniteState s_i (put32BytesWhile "buf" "i" "n") with ⟨rw_res, sw⟩
      rw [hw] at hloop hnt_mid
      dsimp only at hloop hnt_mid ⊢
      cases rw_res with
      | none =>
        obtain ⟨hsw_eff, hsw_loc, _, p_f, hp_f, hpf_nat⟩ := hloop.1 rfl
        have hsw_dst : sw.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hsw_loc (ofString "dst") (by decide) (by decide) (by decide)]
          exact hsi_dst
        rw [evaluateHOLFiniteState_return] at hnt_mid ⊢
        have hev_ret : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (p_f - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hp_f, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]
        have h132 : (1 : Nat) ≤ 32 := by decide
        simp only [sizeOfShapeWithContextHOL, shapeOfHOLExact, h132, ↓reduceIte]
        let len := p_f - dst0
        have hlen_nat : len.toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat := by
          change (p_f - dst0).toNat = _
          have hle_pf : dst0.toNat ≤ p_f.toNat := by rw [hpf_nat, hp_base_nat]; omega
          have hsub : p_f.toNat - dst0.toNat = rlpHeaderLenPure (33 * nw.toNat) + 33 * nw.toNat := by
            rw [hpf_nat, hp_base_nat]; omega
          have := BitVec.toNat_sub_of_le (x := p_f) (y := dst0) ((BitVec.le_def).2 hle_pf)
          omega
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        simp only [shapeEqHOL, hval, len, ↓reduceIte]
        set s_out := setKvarHOLFinite VarKind.local (ofString lname) (.val (.word len))
          { sw.emptyLocalsHOLFinite with locals := s.locals }
        have hout_eff : HeapByteEff s s_out Rl gw :=
          hsw_eff.locals_clock s_out.locals s_out.clock
        have hlen_le : len.toNat ≤ 9 + 33 * nw.toNat := by
          rw [hlen_nat]
          have := (rlpHeaderLenPure_bounds (33 * nw.toNat)).2; omega
        exact ⟨fun _ => ⟨len, hlen_nat, hlen_le, rfl, hout_eff⟩,
          fun h => False.elim (h rfl)⟩
      | some r =>
        have hnr_w := hloop.2 (by simp)
        have hncb_w := txEncNoContBreak_while
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
          (put32BytesLoopBody "buf" "i") s_i
        change (evaluateHOLFiniteState s_i (put32BytesWhile "buf" "i" "n")).1 ≠ some .continue ∧
          (evaluateHOLFiniteState s_i (put32BytesWhile "buf" "i" "n")).1 ≠ some .break at hncb_w
        rw [hw] at hncb_w
        dsimp only at hncb_w
        cases r with
        | timeOut => exact absurd rfl hnt_mid
        | «continue» => exact absurd rfl hncb_w.1
        | «break» => exact absurd rfl hncb_w.2
        | returned rv => exact False.elim (hnr_w (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr_w (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · rcases hb_out : evaluateHOLFiniteState ent
          (.decCall (ofString "w") .one (ofString "rlp_encode_list_header")
            [.var .local (ofString "dst"), .panop .mul [.const 33#64, .var .local (ofString "n")]]
            (.dec (ofString "p") .one
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
              (.dec (ofString "i") .one (.const 0#64)
                (.seq (put32BytesWhile "buf" "i" "n")
                  (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))) with ⟨rb, sb⟩
      rw [hb_out] at hne_none hnr hnt_body
      dsimp only at hne_none hnr hnt_body ⊢
      cases rb with
      | none => exact False.elim (hne_none rfl)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_body
        | returned rv => exact False.elim (hnr (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private def putAccessListLoopBody : ProgHOL 64 :=
  .dec (ofString "rec") .one
    (.op .add [.var .local (ofString "recs"),
      .panop .mul [.var .local (ofString "i"), .const 24#64]])
    (.dec (ofString "ns") .one
      (.load .one (.op .add [.var .local (ofString "rec"), .const 16#64]))
      (.dec (ofString "inner") .one
        (.panop .mul [.const 33#64, .var .local (ofString "ns")])
        (.decCall (ofString "ih") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "inner")]
          (.seq
            (.call (some (some (VarKind.local, ofString "w"), none))
              (ofString "rlp_encode_list_header")
              [.var .local (ofString "p"),
               .op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]])
            (.seq
              (.assign .local (ofString "p")
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq
                (.call (some (some (VarKind.local, ofString "w"), none))
                  (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"),
                   .load .one (.op .add [.var .local (ofString "rec"), .const 0#64]),
                   .const 20#64])
                (.seq
                  (.assign .local (ofString "p")
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (VarKind.local, ofString "w"), none))
                      (ofString "rlp_encode_list_header")
                      [.var .local (ofString "p"), .var .local (ofString "inner")])
                    (.seq
                      (.assign .local (ofString "p")
                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                      (.dec (ofString "keys") .one
                        (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64]))
                        (.dec (ofString "j") .one (.const 0#64)
                          (.seq
                            (put32BytesWhile "keys" "j" "ns")
                            (.assign .local (ofString "i")
                              (.op .add [.var .local (ofString "i"), .const 1#64]))))))))))))))

private def putAccessListWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    putAccessListLoopBody

private theorem putAccessListLoopBody_exact {F : Type}
    (s0 t : PanSemStateFiniteExact 64 F)
    (p_base dst0 recsw nw iw pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 t Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun k => memW s0 (recsw.toNat + 24 * k + 16))).sum < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat))
    (hi_lt : iw.toNat < nw.toNat)
    (hp_eq : pw.toNat = p_base.toNat + accessListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
      p_base.toNat + accessListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_w : ∃ w_old : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState t putAccessListLoopBody).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t putAccessListLoopBody
    (out.1 = none →
      HeapByteEff t out.2 Rl gw ∧
      out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      out.2.locals.lookup (ofString "recs") = some (.val (.word recsw)) ∧
      out.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      out.2.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) ∧
      (∃ w_f : BitVec 64, out.2.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      ∃ p_next : BitVec 64,
        out.2.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
        p_next.toNat = p_base.toNat + accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1)) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hrlp20 : rlpHeaderLenPure 20 = 1 := by decide
  have ht_AR : ArenaReady t := heff0.arena
  have hn_pos : 0 < nw.toNat := by omega
  have hins_all := hrecs_ins hn_pos
  have hwok_all := hrecs_ok hn_pos
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hrecs_hi : recsw.toNat + 24 * nw.toNat ≤ globN s0 "heap_ptr" := hins_all.2
  have hns_lt_slots : memW s0 (recsw.toNat + 24 * iw.toNat + 16) ≤
      ((List.range nw.toNat).map (fun k => memW s0 (recsw.toNat + 24 * k + 16))).sum := by
    have hex : iw.toNat + 1 ≤ nw.toNat := by omega
    have hm := range_map_sum_mono (fun k => memW s0 (recsw.toNat + 24 * k + 16)) hex
    rw [List.range_succ, List.map_append, List.sum_append] at hm
    simp only [List.map_singleton, List.sum_singleton] at hm
    omega
  have hns_lt : memW s0 (recsw.toNat + 24 * iw.toNat + 16) < 2 ^ 32 := by omega
  have htot_next_le : accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) ≤
      accessListPayloadSumPure s0 recsw.toNat nw.toNat := by
    unfold accessListPayloadSumPure
    exact range_map_sum_mono (fun k => accessSlotEntryTotalPure s0 recsw.toNat k) (by omega)
  have htot_eq_step := accessListPayloadSumPure_succ s0 recsw.toNat iw.toNat
  obtain ⟨ivl0, hivl0, hivl_lo, hivl_hi, hivl_lim⟩ := hin_ivl
  unfold putAccessListLoopBody at hnt ⊢
  let recw : BitVec 64 := recsw + (iw * 24#64 + 0#64)
  have hrecw_nat : recw.toNat = recsw.toNat + 24 * iw.toNat := by
    change (recsw + (iw * 24#64 + 0#64)).toNat = _
    rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_mul]
    have hmul_lt : iw.toNat * 24 < 2 ^ 64 := by omega
    have hmod1 : (iw.toNat * 24) % 2 ^ 64 = 24 * iw.toNat := by
      rw [Nat.mod_eq_of_lt hmul_lt]; omega
    change (recsw.toNat + (iw.toNat * 24) % 2 ^ 64) % 2 ^ 64 = _
    rw [hmod1]
    exact Nat.mod_eq_of_lt (by omega)
  have hev_rec : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .local (ofString "recs"), .panop .mul [.var .local (ofString "i"), .const 24#64]]) =
      some (.val (.word recw)) := by
    have h0 : recw + 0#64 = recw := BitVec.add_zero _
    simp [evalHOLExact, evalListHOLExact, ht_recs, ht_i, panOpHOL, wordOpHOL, wordOp,
      valueIsWord, valueWord, recw, h0]
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [hev_rec, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "rec") (.val (.word recw)) t
  have hs1_eff0 : HeapByteEff s0 s1 Rl gw := heff0.locals_clock s1.locals s1.clock
  have hs1_rec : s1.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hins_rec : Inside (recw.toNat, 24) sourceBase (globN s0 "heap_ptr") :=
    ⟨by rw [hrecw_nat]; have := hins_all.1; dsimp only at this ⊢; omega,
     by rw [hrecw_nat]; dsimp only at hrecs_hi ⊢; omega⟩
  have hwok_rec : WordsOK s0 (recw.toNat, 24) :=
    ⟨by rw [hrecw_nat]; have := hwok_all.1; omega, by omega, fun k hk => by
      have h := hwok_all.2.2 (3 * iw.toNat + k) (by omega)
      have heq : recsw.toNat + 8 * (3 * iw.toNat + k) = recw.toNat + 8 * k := by rw [hrecw_nat]; omega
      rwa [heq] at h⟩
  let nsw : BitVec 64 := BitVec.ofNat 64 (memW s0 (recw.toNat + 16))
  have hns_val : memW s0 (recw.toNat + 16) = memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
    rw [hrecw_nat]
  have hnsw_nat : nsw.toNat = memW s0 (recsw.toNat + 24 * iw.toNat + 16) := by
    change (BitVec.ofNat 64 (memW s0 (recw.toNat + 16))).toNat = _
    rw [hns_val, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hev_ns : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "rec"), .const 16#64])) =
      some (.val (.word nsw)) :=
    txEnc_eval_load_word_below_hp hAR0 hs1_eff0 hRl_ge hins_rec hwok_rec "rec" hs1_rec 16
      (by omega) (by omega)
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [hev_ns, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s2 := setVarHOLFinite (ofString "ns") (.val (.word nsw)) s1
  have hs2_ns : s2.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  let innerw : BitVec 64 := 33#64 * nsw + 0#64
  have hinnerw_nat : innerw.toNat = 33 * nsw.toNat := by
    change (33#64 * nsw + 0#64).toNat = _
    rw [BitVec.add_zero, BitVec.toNat_mul]
    change (33 * nsw.toNat) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hev_inner : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.panop .mul [.const 33#64, .var .local (ofString "ns")]) =
      some (.val (.word innerw)) := by
    simp [evalHOLExact, evalListHOLExact, hs2_ns, panOpHOL, wordOpHOL, wordOp,
      valueIsWord, valueWord, innerw]
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [hev_inner, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s3 := setVarHOLFinite (ofString "inner") (.val (.word innerw)) s2
  have hs3_efft : HeapByteEff t s3 Rl gw := (HeapByteEff.refl ht_AR Rl gw).locals_clock s3.locals s3.clock
  have hs3_eff0 : HeapByteEff s0 s3 Rl gw := heff0.trans hs3_efft
  have hs3_AR : ArenaReady s3 := hs3_eff0.arena
  have hs3_inner : s3.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨s4, hih_nat, hih_ge1, hih_le9, _, _, hs4_loc, hs4_eff, hnt4, hdc4⟩ :=
    eval_decCall_rlp_list_header_len s3 "ih" (.var .local (ofString "inner")) innerw _ Rl gw
      hs3_AR.1.code hs3_AR (by simp [evalHOLExact, hs3_inner]) hnt
  rw [hdc4]
  dsimp only
  let ihw : BitVec 64 := BitVec.ofNat 64 (rlpHeaderLenPure innerw.toNat)
  have hihw_nat : ihw.toNat = rlpHeaderLenPure (33 * nsw.toNat) := by
    change (BitVec.ofNat 64 (rlpHeaderLenPure innerw.toNat)).toNat = _
    rw [hih_nat, hinnerw_nat]
  have hih_le9' : rlpHeaderLenPure (33 * nsw.toNat) ≤ 9 := (rlpHeaderLenPure_bounds _).2
  have hs4_efft : HeapByteEff t s4 Rl gw := hs3_efft.trans hs4_eff
  have hs4_eff0 : HeapByteEff s0 s4 Rl gw := heff0.trans hs4_efft
  have hs4_AR : ArenaReady s4 := hs4_eff0.arena
  have hs4_ih : s4.locals.lookup (ofString "ih") = some (.val (.word ihw)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ihw]
  have hs4_inner : s4.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
    rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_inner,
      show ofString "ih" ≠ ofString "inner" by decide]
  have hs4_ns : s4.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
    rw [hs4_loc]; simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ih" ≠ ofString "ns" by decide, show ofString "inner" ≠ ofString "ns" by decide]
  have hs4_rec : s4.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
    rw [hs4_loc]; simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ih" ≠ ofString "rec" by decide, show ofString "inner" ≠ ofString "rec" by decide,
      show ofString "ns" ≠ ofString "rec" by decide]
  have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    rw [hs4_loc]; simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_p,
      show ofString "ih" ≠ ofString "p" by decide, show ofString "inner" ≠ ofString "p" by decide,
      show ofString "ns" ≠ ofString "p" by decide, show ofString "rec" ≠ ofString "p" by decide]
  obtain ⟨w_old0, hw_old0⟩ := ht_w
  have hs4_w : s4.locals.lookup (ofString "w") = some (.val (.word w_old0)) := by
    rw [hs4_loc]; simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw_old0,
      show ofString "ih" ≠ ofString "w" by decide, show ofString "inner" ≠ ofString "w" by decide,
      show ofString "ns" ≠ ofString "w" by decide, show ofString "rec" ≠ ofString "w" by decide]
  have hs4_other : ∀ k, k ≠ ofString "ih" → k ≠ ofString "inner" → k ≠ ofString "ns" → k ≠ ofString "rec" →
      s4.locals.lookup k = t.locals.lookup k := by
    intro k h1 h2 h3 h4
    rw [hs4_loc]
    simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]
  let entryw : BitVec 64 := 21#64 + (ihw + (innerw + 0#64))
  have hentryw_nat : entryw.toNat = accessSlotEntryPayloadPure s0 recsw.toNat iw.toNat := by
    change (21#64 + (ihw + (innerw + 0#64))).toNat = _
    rw [BitVec.add_zero]
    have hsum1 : (ihw + innerw).toNat = rlpHeaderLenPure (33 * nsw.toNat) + 33 * nsw.toNat := by
      rw [BitVec.toNat_add, hihw_nat, hinnerw_nat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, hsum1]
    dsimp only [accessSlotEntryPayloadPure]
    rw [← hnsw_nat]
    change (21 + (rlpHeaderLenPure (33 * nsw.toNat) + 33 * nsw.toNat)) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hev_entry : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
      (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")]) =
      some (.val (.word entryw)) := by
    simp [evalHOLExact, evalListHOLExact, hs4_ih, hs4_inner, wordOpHOL, wordOp,
      valueIsWord, valueWord, entryw]
  have hentry_tot_eq : rlpHeaderLenPure entryw.toNat + entryw.toNat =
      accessSlotEntryTotalPure s0 recsw.toNat iw.toNat := by
    dsimp only [accessSlotEntryTotalPure]; rw [hentryw_nat]
  have hp_entry_le : pw.toNat + accessSlotEntryTotalPure s0 recsw.toNat iw.toNat ≤ ivl0.1 + ivl0.2 := by
    rw [hp_eq]
    have : p_base.toNat + accessListPayloadSumPure s0 recsw.toNat iw.toNat +
        accessSlotEntryTotalPure s0 recsw.toNat iw.toNat =
        p_base.toNat + accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by omega
    omega
  have hcA := eval_call_local_rlp_encode_list_header s4 "w"
    (.var .local (ofString "p"))
    (.op .add [.const 21#64, .var .local (ofString "ih"), .var .local (ofString "inner")])
    pw entryw Rl gw hs4_AR.1.code hs4_AR ⟨w_old0, hs4_w⟩
    (by simp [evalHOLExact, hs4_p]) hev_entry
    ⟨ivl0, hivl0, by rw [hp_eq]; omega, by omega⟩
    (by
      intro hto
      have hnt4' := hnt4
      rw [evaluateHOLFiniteState_seq_line780] at hnt4'
      simp [hto] at hnt4')
  have hstepA := txEnc_seq_call_assign_p_exact hs4_efft hs4_p
    (exactLen := rlpHeaderLenPure entryw.toNat)
    (by have := (rlpHeaderLenPure_bounds entryw.toNat).2; omega)
    ⟨fun hnone => by obtain ⟨hl, h1, _, _, _, _, h2, h3⟩ := hcA.1 hnone; exact ⟨hl, h1, h2, h3⟩, hcA.2⟩
    hnt4
  dsimp only at hstepA
  rcases hstepA with ⟨lenA, s5, hlenA_eq, hp5_nat, hs5_loc, hs5_efft, hnt5, heqA⟩ | ⟨hneA, hnrA⟩
  · rw [heqA]
    let p5 := pw + lenA
    have hp5_val : p5.toNat = pw.toNat + rlpHeaderLenPure entryw.toNat := hp5_nat
    have hs5_eff0 : HeapByteEff s0 s5 Rl gw := heff0.trans hs5_efft
    have hs5_AR : ArenaReady s5 := hs5_eff0.arena
    have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word p5)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p5]
    have hs5_w : s5.locals.lookup (ofString "w") = some (.val (.word lenA)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" by decide]
    have hs5_rec : s5.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_rec,
        show ofString "p" ≠ ofString "rec" by decide, show ofString "w" ≠ ofString "rec" by decide]
    have hs5_inner : s5.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_inner,
        show ofString "p" ≠ ofString "inner" by decide, show ofString "w" ≠ ofString "inner" by decide]
    have hs5_ns : s5.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
      rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_ns,
        show ofString "p" ≠ ofString "ns" by decide, show ofString "w" ≠ ofString "ns" by decide]
    have hev_addr0 := txEnc_eval_load_word_below_hp hAR0 hs5_eff0 hRl_ge hins_rec hwok_rec "rec" hs5_rec 0
      (by omega) (by omega)
    have hcB := eval_call_local_rlp_encode_bytes_n_ne_one s5 "w"
      (.var .local (ofString "p"))
      (.load .one (.op .add [.var .local (ofString "rec"), .const 0#64]))
      (.const 20#64)
      p5 (BitVec.ofNat 64 (memW s0 (recw.toNat + 0))) 20#64 Rl gw
      hs5_AR.1.code hs5_AR ⟨lenA, hs5_w⟩
      (by simp [evalHOLExact, hs5_p]) hev_addr0 rfl (by decide)
      (by rw [heapEnd_val]; decide)
      ⟨ivl0, hivl0, by omega, by
        have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
        rw [h20, hrlp20]
        have heq_ent := hentryw_nat
        dsimp only [accessSlotEntryPayloadPure] at heq_ent
        have : 21 ≤ entryw.toNat := by omega
        omega⟩
      (by
        intro hto
        have hnt5' := hnt5
        rw [evaluateHOLFiniteState_seq_line780] at hnt5'
        simp [hto] at hnt5')
    have hstepB := txEnc_seq_call_assign_p_exact hs5_efft hs5_p
      (exactLen := 21) (by
        have : 21 ≤ entryw.toNat := by
          have heq_ent := hentryw_nat
          dsimp only [accessSlotEntryPayloadPure] at heq_ent; omega
        omega)
      ⟨fun hnone => by
        obtain ⟨len, h1, _, _, h2, h3⟩ := hcB.1 hnone
        have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
        rw [h20, hrlp20] at h1
        exact ⟨len, h1, h2, h3⟩, hcB.2⟩
      hnt5
    dsimp only at hstepB
    rcases hstepB with ⟨lenB, s6, hlenB_eq, hp6_nat, hs6_loc, hs6_efft, hnt6, heqB⟩ | ⟨hneB, hnrB⟩
    · rw [heqB]
      let p6 := p5 + lenB
      have hp6_val : p6.toNat = p5.toNat + 21 := hp6_nat
      have hs6_eff0 : HeapByteEff s0 s6 Rl gw := heff0.trans hs6_efft
      have hs6_AR : ArenaReady s6 := hs6_eff0.arena
      have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word p6)) := by
        rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p6]
      have hs6_w : s6.locals.lookup (ofString "w") = some (.val (.word lenB)) := by
        rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "w" by decide]
      have hs6_rec : s6.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
        rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_rec,
          show ofString "p" ≠ ofString "rec" by decide, show ofString "w" ≠ ofString "rec" by decide]
      have hs6_inner : s6.locals.lookup (ofString "inner") = some (.val (.word innerw)) := by
        rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_inner,
          show ofString "p" ≠ ofString "inner" by decide, show ofString "w" ≠ ofString "inner" by decide]
      have hs6_ns : s6.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
        rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_ns,
          show ofString "p" ≠ ofString "ns" by decide, show ofString "w" ≠ ofString "ns" by decide]
      have hcC := eval_call_local_rlp_encode_list_header s6 "w"
        (.var .local (ofString "p")) (.var .local (ofString "inner"))
        p6 innerw Rl gw hs6_AR.1.code hs6_AR ⟨lenB, hs6_w⟩
        (by simp [evalHOLExact, hs6_p]) (by simp [evalHOLExact, hs6_inner])
        ⟨ivl0, hivl0, by omega, by
          have heq_ent := hentryw_nat
          dsimp only [accessSlotEntryPayloadPure] at heq_ent
          rw [hinnerw_nat, hnsw_nat]
          omega⟩
        (by
          intro hto
          have hnt6' := hnt6
          rw [evaluateHOLFiniteState_seq_line780] at hnt6'
          simp [hto] at hnt6')
      have hstepC := txEnc_seq_call_assign_p_exact hs6_efft hs6_p
        (exactLen := rlpHeaderLenPure innerw.toNat)
        (by
          have heq_ent := hentryw_nat
          dsimp only [accessSlotEntryPayloadPure] at heq_ent
          rw [hinnerw_nat, hnsw_nat]
          omega)
        ⟨fun hnone => by obtain ⟨hl, h1, _, _, _, _, h2, h3⟩ := hcC.1 hnone; exact ⟨hl, h1, h2, h3⟩, hcC.2⟩
        hnt6
      dsimp only at hstepC
      rcases hstepC with ⟨lenC, s7, hlenC_eq, hp7_nat, hs7_loc, hs7_efft, hnt7, heqC⟩ | ⟨hneC, hnrC⟩
      · rw [heqC]
        let p7 := p6 + lenC
        have hp7_val : p7.toNat = p6.toNat + rlpHeaderLenPure innerw.toNat := hp7_nat
        have hs7_eff0 : HeapByteEff s0 s7 Rl gw := heff0.trans hs7_efft
        have hs7_p : s7.locals.lookup (ofString "p") = some (.val (.word p7)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p7]
        have hs7_w : s7.locals.lookup (ofString "w") = some (.val (.word lenC)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "p" ≠ ofString "w" by decide]
        have hs7_rec : s7.locals.lookup (ofString "rec") = some (.val (.word recw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_rec,
            show ofString "p" ≠ ofString "rec" by decide, show ofString "w" ≠ ofString "rec" by decide]
        have hs7_ns : s7.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_ns,
            show ofString "p" ≠ ofString "ns" by decide, show ofString "w" ≠ ofString "ns" by decide]
        have hs7_other : ∀ k, k ≠ ofString "p" → k ≠ ofString "w" →
            k ≠ ofString "ih" → k ≠ ofString "inner" → k ≠ ofString "ns" → k ≠ ofString "rec" →
            s7.locals.lookup k = t.locals.lookup k := by
          intro k hp_ne hw_ne h1 h2 h3 h4
          rw [hs7_loc, hs6_loc, hs5_loc]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hp_ne, hw_ne, hp_ne.symm, hw_ne.symm]
          exact hs4_other k h1 h2 h3 h4
        let keysw : BitVec 64 := BitVec.ofNat 64 (memW s0 (recw.toNat + 8))
        have hev_keys : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "rec"), .const 8#64])) =
            some (.val (.word keysw)) :=
          txEnc_eval_load_word_below_hp hAR0 hs7_eff0 hRl_ge hins_rec hwok_rec "rec" hs7_rec 8
            (by omega) (by omega)
        rw [evaluateHOLFiniteState_dec_total] at hnt7 ⊢
        simp only [hev_keys, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt7 ⊢
        set s8 := setVarHOLFinite (ofString "keys") (.val (.word keysw)) s7
        rw [evaluateHOLFiniteState_dec_total] at hnt7 ⊢
        have hev_j0 : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        simp only [hev_j0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt7 ⊢
        set s9 := setVarHOLFinite (ofString "j") (.val (.word 0#64)) s8
        have hs9_efft : HeapByteEff t s9 Rl gw := hs7_efft.locals_clock s9.locals s9.clock
        have hs9_keys : s9.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
          simp [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "j" ≠ ofString "keys" by decide]
        have hs9_j : s9.locals.lookup (ofString "j") = some (.val (.word 0#64)) := by
          simp [s9, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs9_ns : s9.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
          simp [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_ns,
            show ofString "j" ≠ ofString "ns" by decide, show ofString "keys" ≠ ofString "ns" by decide]
        have hs9_p : s9.locals.lookup (ofString "p") = some (.val (.word p7)) := by
          simp [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_p,
            show ofString "j" ≠ ofString "p" by decide, show ofString "keys" ≠ ofString "p" by decide]
        have hs9_w : ∃ w9 : BitVec 64, s9.locals.lookup (ofString "w") = some (.val (.word w9)) :=
          ⟨lenC, by simp [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs7_w,
            show ofString "j" ≠ ofString "w" by decide, show ofString "keys" ≠ ofString "w" by decide]⟩
        rw [evaluateHOLFiniteState_seq_line780] at hnt7 ⊢
        have hin_keys : ∃ ivl ∈ Rl, ivl.1 ≤ p7.toNat ∧
            p7.toNat + 33 * nsw.toNat ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit := by
          refine ⟨ivl0, hivl0, by omega, ?_, hivl_lim⟩
          have heq_ent := hentryw_nat
          dsimp only [accessSlotEntryPayloadPure] at heq_ent
          rw [hinnerw_nat] at hp7_val
          rw [hnsw_nat] at hp7_val ⊢
          omega
        have hnt_inner : (evaluateHOLFiniteState s9 (put32BytesWhile "keys" "j" "ns")).1 ≠ some .timeOut := by
          intro hto; simp [hto] at hnt7
        have hinner := put32BytesWhile_exact s9.clock t s9 "keys" "j" "ns" p7 keysw nsw 0#64 p7 Rl gw
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Nat.le_refl _) hs9_efft (by omega) (by simp) (by simp)
          hin_keys hs9_keys hs9_ns hs9_j hs9_p hs9_w hnt_inner
        dsimp only at hinner
        rcases hw_in : evaluateHOLFiniteState s9 (put32BytesWhile "keys" "j" "ns") with ⟨rin, sin⟩
        rw [hw_in] at hinner hnt7
        dsimp only at hinner hnt7 ⊢
        cases rin with
        | none =>
          obtain ⟨hsin_efft, hsin_loc, ⟨w_in, hw_in_lk⟩, p_next, hp_next_lk, hp_next_nat⟩ := hinner.1 rfl
          have hsin_i : sin.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hsin_loc (ofString "i") (by decide) (by decide) (by decide)]
            simp only [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "j" by decide, show ofString "i" ≠ ofString "keys" by decide,
              show ofString "j" ≠ ofString "i" by decide, show ofString "keys" ≠ ofString "i" by decide, ↓reduceIte]
            rw [hs7_other (ofString "i") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact ht_i
          rw [evaluateHOLFiniteState_assign] at hnt7 ⊢
          have hev_i1 : @evalHOLExact 64 F _ sin.toExact (fun a => Classical.propDecidable (sin.memaddrs a))
              (.op .add [.var .local (ofString "i"), .const 1#64]) =
              some (.val (.word (iw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hsin_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_i1] at hnt7 ⊢; dsimp only at hnt7 ⊢
          have hvv_i : isValidValueHOLFinite sin .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
            simp [isValidValueHOLFinite, lookupKvarHOLFinite, hsin_i, shapeOfHOLExact, shapeEqHOL]
          rw [if_pos hvv_i] at hnt7 ⊢; dsimp only at hnt7 ⊢
          let s10 := setKvarHOLFinite .local (ofString "i") (.val (.word (iw + 1#64))) sin
          have hloc_out : ∀ k, k ≠ ofString "ih" → k ≠ ofString "inner" → k ≠ ofString "ns" →
              k ≠ ofString "rec" → k ≠ ofString "keys" → k ≠ ofString "j" →
              ((HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq
                        (HolFiniteMapExact.resVarEq s10.locals (ofString "j", s8.locals.lookup (ofString "j")))
                        (ofString "keys", s7.locals.lookup (ofString "keys")))
                      (ofString "ih", s3.locals.lookup (ofString "ih")))
                    (ofString "inner", s2.locals.lookup (ofString "inner")))
                  (ofString "ns", s1.locals.lookup (ofString "ns")))
                (ofString "rec", t.locals.lookup (ofString "rec")))).lookup k = s10.locals.lookup k := by
            intro k h1 h2 h3 h4 h5 h6
            rw [txEnc_lookup_resVarEq_ne _ _ _ _ h4.symm,
                txEnc_lookup_resVarEq_ne _ _ _ _ h3.symm,
                txEnc_lookup_resVarEq_ne _ _ _ _ h2.symm,
                txEnc_lookup_resVarEq_ne _ _ _ _ h1.symm,
                txEnc_lookup_resVarEq_ne _ _ _ _ h5.symm,
                txEnc_lookup_resVarEq_ne _ _ _ _ h6.symm]
          have hp_next_tot : p_next.toNat =
              p_base.toNat + accessListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
            have heq_ent := hentryw_nat
            dsimp only [accessSlotEntryPayloadPure] at heq_ent
            rw [hinnerw_nat, hnsw_nat] at hp7_nat
            rw [hp_next_nat, hnsw_nat, hp7_nat, hp6_nat, hp5_nat, hp_eq, htot_eq_step, ← hentry_tot_eq]
            omega
          refine ⟨fun _ => ⟨hsin_efft.locals_clock _ _, ?_, ?_, ?_, ?_, ?_, p_next, ?_, hp_next_tot⟩,
            fun h => False.elim (h rfl)⟩
          · rw [hloc_out (ofString "dst") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "dst" by decide, ↓reduceIte]
            rw [hsin_loc (ofString "dst") (by decide) (by decide) (by decide)]
            simp only [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "dst" by decide, show ofString "keys" ≠ ofString "dst" by decide, ↓reduceIte]
            rw [hs7_other (ofString "dst") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact ht_dst
          · rw [hloc_out (ofString "recs") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "recs" by decide, ↓reduceIte]
            rw [hsin_loc (ofString "recs") (by decide) (by decide) (by decide)]
            simp only [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "recs" by decide, show ofString "keys" ≠ ofString "recs" by decide, ↓reduceIte]
            rw [hs7_other (ofString "recs") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact ht_recs
          · rw [hloc_out (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "n" by decide, ↓reduceIte]
            rw [hsin_loc (ofString "n") (by decide) (by decide) (by decide)]
            simp only [s9, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "n" by decide, show ofString "keys" ≠ ofString "n" by decide, ↓reduceIte]
            rw [hs7_other (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact ht_n
          · rw [hloc_out (ofString "i") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · refine ⟨w_in, ?_⟩
            rw [hloc_out (ofString "w") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "w" by decide, ↓reduceIte]
            exact hw_in_lk
          · rw [hloc_out (ofString "p") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide, ↓reduceIte]
            exact hp_next_lk
        | some r =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => hinner.2 (by simp)⟩
      · exact ⟨fun h => False.elim (hneC (by simpa using h)), fun _ hr => hnrC (by simpa using hr)⟩
    · exact ⟨fun h => False.elim (hneB (by simpa using h)), fun _ hr => hnrB (by simpa using hr)⟩
  · exact ⟨fun h => False.elim (hneA (by simpa using h)), fun _ hr => hnrA (by simpa using hr)⟩

private theorem putAccessListWhile_exact {F : Type}
    (clk : Nat) (s0 s_base t : PanSemStateFiniteExact 64 F)
    (p_base dst0 recsw nw iw pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hclk : t.clock ≤ clk)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 t Rl gw)
    (heff_b : HeapByteEff s_base t Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun k => memW s0 (recsw.toNat + 24 * k + 16))).sum < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat))
    (hi_le : iw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = p_base.toNat + accessListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
      p_base.toNat + accessListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_w : ∃ w_old : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState t putAccessListWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t putAccessListWhile
    (out.1 = none →
      HeapByteEff s_base out.2 Rl gw ∧
      out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      ∃ p_f : BitVec 64,
        out.2.locals.lookup (ofString "p") = some (.val (.word p_f)) ∧
        p_f.toNat = p_base.toNat + accessListPayloadSumPure s0 recsw.toNat nw.toNat) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  induction clk generalizing t iw pw with
  | zero =>
    dsimp only [putAccessListWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hcz : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hcz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff_b, ht_dst, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
        fun h => False.elim (h rfl)⟩
  | succ clk ih =>
    dsimp only [putAccessListWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hcz : t.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set td := decClockHOLFinite t
        have htd_eff0 : HeapByteEff s0 td Rl gw := heff0.locals_clock t.locals (t.clock - 1)
        have htd_effb : HeapByteEff s_base td Rl gw := heff_b.locals_clock t.locals (t.clock - 1)
        have hcle_body := evaluateHOLFiniteState_clock_le td putAccessListLoopBody
        have hnt_b : (evaluateHOLFiniteState td putAccessListLoopBody).1 ≠ some .timeOut := by
          rcases hb_res : evaluateHOLFiniteState td putAccessListLoopBody with ⟨rb, sb⟩
          rintro rfl; simp [hb_res] at hnt
        have hb_step := putAccessListLoopBody_exact s0 td p_base dst0 recsw nw iw pw Rl gw
          hAR0 htd_eff0 hRl_ge hn_lt hslots_lt hrecs_ins hrecs_ok hlt hp_eq hin_ivl
          ht_dst ht_recs ht_n ht_i ht_p ht_w hnt_b
        dsimp only at hb_step
        have hncb := txEncNoContBreak_sound putAccessListLoopBody rfl td
        change (evaluateHOLFiniteState td putAccessListLoopBody).1 ≠ some .continue ∧
          (evaluateHOLFiniteState td putAccessListLoopBody).1 ≠ some .break at hncb
        change (evaluateHOLFiniteState td putAccessListLoopBody).2.clock ≤ td.clock at hcle_body
        obtain ⟨rb, sb, hb_res⟩ : ∃ rb sb, evaluateHOLFiniteState td putAccessListLoopBody = (rb, sb) :=
          ⟨_, _, Prod.mk.eta.symm⟩
        rw [hb_res] at hb_step hcle_body hncb hnt ⊢
        dsimp only at hb_step hcle_body hncb hnt ⊢
        cases rb with
        | none =>
          obtain ⟨hsb_eff_td, hsb_dst, hsb_recs, hsb_n, hsb_i, hsb_w, p_next, hsb_p, hp_next_eq⟩ :=
            hb_step.1 rfl
          have hi1_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _
            exact Nat.mod_eq_of_lt (by omega)
          have hsb_clk : sb.clock ≤ clk := by
            change sb.clock ≤ t.clock - 1 at hcle_body; omega
          have hnt_ih : (evaluateHOLFiniteState sb putAccessListWhile).1 ≠ some .timeOut := hnt
          have hih := ih sb (iw + 1#64) p_next hsb_clk
            (htd_eff0.trans hsb_eff_td) (htd_effb.trans hsb_eff_td)
            (by rw [hi1_nat]; omega) (by rw [hi1_nat]; exact hp_next_eq)
            hsb_dst hsb_recs hsb_n hsb_i hsb_p hsb_w hnt_ih
          dsimp only [putAccessListWhile] at hih
          exact hih
        | some r0 =>
          have hnr := hb_step.2 (by simp)
          cases r0 with
          | timeOut => exact absurd rfl hnt
          | «continue» => exact absurd rfl hncb.1
          | «break» => exact absurd rfl hncb.2
          | returned _ | exception _ _ | error | finalFfi _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => hnr⟩
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff_b, ht_dst, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
        fun h => False.elim (h rfl)⟩

private theorem eval_call_local_tx_put_access_list {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp recsExp nExp : ExpHOL 64)
    (dst0 recsw nw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hslots_lt : ((List.range nw.toNat).map
      (fun k => memW s0 (recsw.toNat + 24 * k + 16))).sum < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 24 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 24 * nw.toNat))
    (hin_ivl : ∃ ivl ∈ Rl,
      ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (accessListPayloadSumPure s0 recsw.toNat nw.toNat) +
        accessListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_access_list")
        [dstExp, recsExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_access_list")
        [dstExp, recsExp, nExp])
    let al := accessListPayloadSumPure s0 recsw.toNat nw.toNat
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure al + al ∧
        len.toNat ≤ 9 + al ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out al; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hs_AR : ArenaReady s := heff0.arena
  have hcode : s.code = originalRuntimeCode := hs_AR.1.code
  have hb_body : sourceFnBody Guest.Software.guestFn_tx_put_access_list =
      .decCall (ofString "pl") .one (ofString "access_list_payload_len")
        [.var .local (ofString "recs"), .var .local (ofString "n")]
        (.decCall (ofString "w") .one (ofString "rlp_encode_list_header")
          [.var .local (ofString "dst"), .var .local (ofString "pl")]
          (.dec (ofString "p") .one
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
            (.dec (ofString "i") .one (.const 0#64)
              (.seq putAccessListWhile
                (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))) := rfl
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
    have hent_effs : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hs_AR Rl gw).locals_clock ent.locals ent.clock
    have hent_eff0 : HeapByteEff s0 ent Rl gw := heff0.trans hent_effs
    have hent_AR : ArenaReady ent := hent_eff0.arena
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "recs" ≠ ofString "dst" by decide]
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hnt_body : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_access_list)).1 ≠
        some .timeOut := by
      rcases hx : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_access_list) with ⟨rx, sx⟩
      rintro rfl; simp [hx] at hnt
    rw [hb_body] at hnt hnt_body ⊢
    have hent_mw : ∀ k < nw.toNat, memW ent (recsw.toNat + 24 * k + 16) =
        memW s0 (recsw.toNat + 24 * k + 16) := by
      intro k hk
      have h := (txEnc_wordAt_memW_below_hp hAR0 hent_eff0 hRl_ge
        (hrecs_ins (by omega)) (hrecs_ok (by omega)) (24 * k + 16) (by omega) (by omega)).2
      have heq : recsw.toNat + (24 * k + 16) = recsw.toNat + 24 * k + 16 := by omega
      rwa [heq] at h
    have hent_slots_lt : ((List.range nw.toNat).map
        (fun k => memW ent (recsw.toNat + 24 * k + 16))).sum < 2 ^ 32 := by
      have heq_map : (List.range nw.toNat).map (fun k => memW ent (recsw.toNat + 24 * k + 16)) =
          (List.range nw.toNat).map (fun k => memW s0 (recsw.toNat + 24 * k + 16)) :=
        List.map_congr_left (fun k hk => hent_mw k (List.mem_range.mp hk))
      rw [heq_map]; exact hslots_lt
    have hent_recs_ok : 0 < nw.toNat → WordsOK ent (recsw.toNat, 24 * nw.toNat) :=
      fun hpos => txEnc_wordsOK_below_hp hAR0 hent_eff0 hRl_ge (hrecs_ins hpos) (hrecs_ok hpos)
    have hal_congr : accessListPayloadSumPure ent recsw.toNat nw.toNat = al :=
      accessListPayloadSumPure_congr hent_mw
    obtain ⟨m1, hpl_nat, _, _, hm1_loc, hm1_eff, hnt1, hdc1⟩ :=
      eval_decCall_access_list_payload_len ent ent "pl"
        (.var .local (ofString "recs")) (.var .local (ofString "n"))
        recsw nw _ Rl gw hent_AR rfl hn_lt hent_slots_lt hent_recs_ok
        (by simp [evalHOLExact, hent_recs]) (by simp [evalHOLExact, hent_n]) hnt_body
    rw [hdc1] at hnt ⊢
    dsimp only at hnt ⊢
    let plw : BitVec 64 := BitVec.ofNat 64 (accessListPayloadSumPure ent recsw.toNat nw.toNat)
    have hplw_al : plw.toNat = accessListPayloadSumPure s0 recsw.toNat nw.toNat := hpl_nat.trans hal_congr
    have hm1_effs : HeapByteEff s m1 Rl gw := hent_effs.trans hm1_eff
    have hm1_eff0 : HeapByteEff s0 m1 Rl gw := heff0.trans hm1_effs
    have hm1_AR : ArenaReady m1 := hm1_eff0.arena
    have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
        show ofString "pl" ≠ ofString "dst" by decide]
    have hm1_recs : m1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_recs,
        show ofString "pl" ≠ ofString "recs" by decide]
    have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
        show ofString "pl" ≠ ofString "n" by decide]
    have hm1_pl : m1.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, plw]
    have hin_hdr : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure plw.toNat ≤ ivl.1 + ivl.2 := by
      obtain ⟨ivl, hivl, hlo, hhi, _⟩ := hin_ivl
      exact ⟨ivl, hivl, hlo, by rw [hplw_al]; omega⟩
    have hdc2 := eval_decCall_rlp_encode_list_header_outcomes m1 "w"
      (.var .local (ofString "dst")) (.var .local (ofString "pl"))
      dst0 plw
      (.dec (ofString "p") .one
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
        (.dec (ofString "i") .one (.const 0#64)
          (.seq putAccessListWhile
            (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))
      Rl gw hm1_AR.1.code hm1_AR
      (by simp [evalHOLExact, hm1_dst]) (by simp [evalHOLExact, hm1_pl]) hin_hdr hnt1
    dsimp only at hdc2
    rcases hdc2 with ⟨mid, hhl_nat, _, _, _, _, hmid_loc, hmid_eff, hnt_mid, hbody_eq⟩ | ⟨hne_none, hnr⟩
    · rw [hbody_eq] at hnt ⊢
      let hl := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
      have hhl_nat' : hl.toNat = rlpHeaderLenPure plw.toNat := hhl_nat
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word hl)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl]
      have hmid_recs : mid.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
          show ofString "w" ≠ ofString "recs" by decide]
      have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
          show ofString "w" ≠ ofString "n" by decide]
      let p_base : BitVec 64 := dst0 + hl
      have hp_base_nat : p_base.toNat =
          dst0.toNat + rlpHeaderLenPure (accessListPayloadSumPure s0 recsw.toNat nw.toNat) := by
        change (dst0 + hl).toNat = _
        rw [BitVec.toNat_add, hhl_nat', hplw_al]
        obtain ⟨ivl, _, _, hhi, hlim⟩ := hin_ivl
        have : dst0.toNat + rlpHeaderLenPure (accessListPayloadSumPure s0 recsw.toNat nw.toNat) < 2 ^ 64 := by omega
        exact Nat.mod_eq_of_lt this
      have hev_p0 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
           (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
           some (.val (.word p_base)) := by
        simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_base]
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      simp only [hev_p0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_p := setVarHOLFinite (ofString "p") (.val (.word p_base)) mid
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      have hev_i0 : @evalHOLExact 64 F _ s_p.toExact (fun a => Classical.propDecidable (s_p.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      simp only [hev_i0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_i := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s_p
      have hsi_effs : HeapByteEff s s_i Rl gw :=
        (hm1_effs.trans hmid_eff).locals_clock s_i.locals s_i.clock
      have hsi_eff0 : HeapByteEff s0 s_i Rl gw := heff0.trans hsi_effs
      have hsi_dst : s_i.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide]
      have hsi_recs : s_i.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_recs,
          show ofString "i" ≠ ofString "recs" by decide, show ofString "p" ≠ ofString "recs" by decide]
      have hsi_n : s_i.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide]
      have hsi_i : s_i.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [s_i, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsi_p : s_i.locals.lookup (ofString "p") = some (.val (.word p_base)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide]
      have hsi_w : ∃ w0 : BitVec 64, s_i.locals.lookup (ofString "w") = some (.val (.word w0)) :=
        ⟨hl, by simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]⟩
      rw [evaluateHOLFiniteState_seq_line780] at hnt_mid ⊢
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
          p_base.toNat + accessListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
          ivl.1 + ivl.2 ≤ heapLimit := by
        obtain ⟨ivl, hivl, hlo, hhi, hlim⟩ := hin_ivl
        exact ⟨ivl, hivl, by rw [hp_base_nat]; omega, by rw [hp_base_nat]; omega, hlim⟩
      have hnt_loop : (evaluateHOLFiniteState s_i putAccessListWhile).1 ≠ some .timeOut := by
        intro hto; simp [hto] at hnt_mid
      have hloop := putAccessListWhile_exact s_i.clock s0 s s_i p_base dst0 recsw nw 0#64 p_base Rl gw
        (Nat.le_refl _) hAR0 hsi_eff0 hsi_effs hRl_ge hn_lt hslots_lt hrecs_ins hrecs_ok
        (by simp) (by simp [accessListPayloadSumPure])
        hin_loop hsi_dst hsi_recs hsi_n hsi_i hsi_p hsi_w hnt_loop
      dsimp only at hloop
      rcases hw : evaluateHOLFiniteState s_i putAccessListWhile with ⟨rw_res, sw⟩
      rw [hw] at hloop hnt_mid
      dsimp only at hloop hnt_mid ⊢
      cases rw_res with
      | none =>
        obtain ⟨hsw_effs, hsw_dst, p_f, hp_f, hpf_nat⟩ := hloop.1 rfl
        rw [evaluateHOLFiniteState_return] at hnt_mid ⊢
        have hev_ret : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (p_f - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hp_f, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]
        have h132 : (1 : Nat) ≤ 32 := by decide
        simp only [sizeOfShapeWithContextHOL, shapeOfHOLExact, h132, ↓reduceIte]
        let len := p_f - dst0
        have hlen_nat : len.toNat = rlpHeaderLenPure al + al := by
          change (p_f - dst0).toNat = _
          dsimp only [al]
          have hle_pf : dst0.toNat ≤ p_f.toNat := by rw [hpf_nat, hp_base_nat]; omega
          have hsub : p_f.toNat - dst0.toNat =
              rlpHeaderLenPure (accessListPayloadSumPure s0 recsw.toNat nw.toNat) +
                accessListPayloadSumPure s0 recsw.toNat nw.toNat := by
            rw [hpf_nat, hp_base_nat]; omega
          have := BitVec.toNat_sub_of_le (x := p_f) (y := dst0) ((BitVec.le_def).2 hle_pf)
          omega
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        simp only [shapeEqHOL, hval, len, ↓reduceIte]
        set s_out := setKvarHOLFinite VarKind.local (ofString lname) (.val (.word len))
          { sw.emptyLocalsHOLFinite with locals := s.locals }
        have hout_eff : HeapByteEff s s_out Rl gw :=
          hsw_effs.locals_clock s_out.locals s_out.clock
        have hlen_le : len.toNat ≤ 9 + al := by
          rw [hlen_nat]; have := (rlpHeaderLenPure_bounds al).2; omega
        exact ⟨fun _ => ⟨len, hlen_nat, hlen_le, rfl, hout_eff⟩, fun h => False.elim (h rfl)⟩
      | some r =>
        have hnr_w := hloop.2 (by simp)
        have hncb_w := txEncNoContBreak_while
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
          putAccessListLoopBody s_i
        change (evaluateHOLFiniteState s_i putAccessListWhile).1 ≠ some .continue ∧
          (evaluateHOLFiniteState s_i putAccessListWhile).1 ≠ some .break at hncb_w
        rw [hw] at hncb_w
        dsimp only at hncb_w
        cases r with
        | timeOut => exact absurd rfl hnt_mid
        | «continue» => exact absurd rfl hncb_w.1
        | «break» => exact absurd rfl hncb_w.2
        | returned rv => exact False.elim (hnr_w (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr_w (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · rcases hb_out : evaluateHOLFiniteState m1
          (.decCall (ofString "w") .one (ofString "rlp_encode_list_header")
            [.var .local (ofString "dst"), .var .local (ofString "pl")]
            (.dec (ofString "p") .one
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
              (.dec (ofString "i") .one (.const 0#64)
                (.seq putAccessListWhile
                  (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))) with ⟨rb, sb⟩
      rw [hb_out] at hne_none hnr hnt1
      dsimp only at hne_none hnr hnt1 ⊢
      cases rb with
      | none => exact False.elim (hne_none rfl)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt1
        | returned rv => exact False.elim (hnr (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private def putAuthorizationsLoopBody : ProgHOL 64 :=
  .dec (ofString "a") .one
    (.op .add [.var .local (ofString "recs"),
      .panop .mul [.var .local (ofString "i"), .const 120#64]])
    (.decCall (ofString "pl") .one (ofString "auth_payload_len")
      [.var .local (ofString "a")]
      (.seq
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header")
          [.var .local (ofString "p"), .var .local (ofString "pl")])
        (.seq
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.seq
            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
              [.var .local (ofString "p"),
               .load (.comb [.one, .one, .one, .one])
                 (.op .add [.var .local (ofString "a"), .const 0#64])])
            (.seq
              (.assign .local (ofString "p")
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq
                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"),
                   .load .one (.op .add [.var .local (ofString "a"), .const 32#64]),
                   .const 20#64])
                (.seq
                  (.assign .local (ofString "p")
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                      [.var .local (ofString "p"),
                       .load .one (.op .add [.var .local (ofString "a"), .const 40#64])])
                    (.seq
                      (.assign .local (ofString "p")
                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                      (.seq
                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                          [.var .local (ofString "p"),
                           .load .one (.op .add [.var .local (ofString "a"), .const 48#64])])
                        (.seq
                          (.assign .local (ofString "p")
                            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                          (.seq
                            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                              [.var .local (ofString "p"),
                               .load (.comb [.one, .one, .one, .one])
                                 (.op .add [.var .local (ofString "a"), .const 56#64])])
                            (.seq
                              (.assign .local (ofString "p")
                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                              (.seq
                                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                  [.var .local (ofString "p"),
                                   .load (.comb [.one, .one, .one, .one])
                                     (.op .add [.var .local (ofString "a"), .const 88#64])])
                                (.seq
                                  (.assign .local (ofString "p")
                                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                  (.assign .local (ofString "i")
                                    (.op .add [.var .local (ofString "i"), .const 1#64])))))))))))))))))

private def putAuthorizationsWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    putAuthorizationsLoopBody

private theorem putAuthorizationsLoopBody_exact {F : Type}
    (s0 t : PanSemStateFiniteExact 64 F)
    (p_base dst0 recsw nw iw pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 t Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat))
    (hi_lt : iw.toNat < nw.toNat)
    (hp_eq : pw.toNat = p_base.toNat + authListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
      p_base.toNat + authListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_w : ∃ w_old : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState t putAuthorizationsLoopBody).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t putAuthorizationsLoopBody
    (out.1 = none →
      HeapByteEff t out.2 Rl gw ∧
      out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      out.2.locals.lookup (ofString "recs") = some (.val (.word recsw)) ∧
      out.2.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      out.2.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) ∧
      (∃ w_f : BitVec 64, out.2.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      ∃ p_next : BitVec 64,
        out.2.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
        p_next.toNat = p_base.toNat + authListPayloadSumPure s0 recsw.toNat (iw.toNat + 1)) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hrlp20 : rlpHeaderLenPure 20 = 1 := by decide
  have ht_AR : ArenaReady t := heff0.arena
  have hn_pos : 0 < nw.toNat := by omega
  have hins_all := hrecs_ins hn_pos
  have hwok_all := hrecs_ok hn_pos
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hrecs_hi : recsw.toNat + 120 * nw.toNat ≤ globN s0 "heap_ptr" := hins_all.2
  have htot_next_le : authListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) ≤
      authListPayloadSumPure s0 recsw.toNat nw.toNat := by
    unfold authListPayloadSumPure
    exact range_map_sum_mono (fun k => authEntryTotalPure s0 recsw.toNat k) (by omega)
  have htot_eq_step := authListPayloadSumPure_succ s0 recsw.toNat iw.toNat
  obtain ⟨ivl0, hivl0, hivl_lo, hivl_hi, hivl_lim⟩ := hin_ivl
  unfold putAuthorizationsLoopBody at hnt ⊢
  let aw : BitVec 64 := recsw + (iw * 120#64 + 0#64)
  have haw_nat : aw.toNat = recsw.toNat + 120 * iw.toNat := by
    change (recsw + (iw * 120#64 + 0#64)).toNat = _
    rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_mul]
    have hmul_lt : iw.toNat * 120 < 2 ^ 64 := by omega
    have hmod1 : (iw.toNat * 120) % 2 ^ 64 = 120 * iw.toNat := by
      rw [Nat.mod_eq_of_lt hmul_lt]; omega
    change (recsw.toNat + (iw.toNat * 120) % 2 ^ 64) % 2 ^ 64 = _
    rw [hmod1]
    exact Nat.mod_eq_of_lt (by omega)
  have hev_a : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .local (ofString "recs"), .panop .mul [.var .local (ofString "i"), .const 120#64]]) =
      some (.val (.word aw)) := by
    have h0 : aw + 0#64 = aw := BitVec.add_zero _
    simp [evalHOLExact, evalListHOLExact, ht_recs, ht_i, panOpHOL, wordOpHOL, wordOp,
      valueIsWord, valueWord, aw, h0]
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [hev_a, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "a") (.val (.word aw)) t
  have hs1_efft : HeapByteEff t s1 Rl gw := (HeapByteEff.refl ht_AR Rl gw).locals_clock s1.locals s1.clock
  have hs1_eff0 : HeapByteEff s0 s1 Rl gw := heff0.trans hs1_efft
  have hs1_AR : ArenaReady s1 := hs1_eff0.arena
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hins_a : Inside (aw.toNat, 120) sourceBase (globN s0 "heap_ptr") :=
    ⟨by rw [haw_nat]; have := hins_all.1; dsimp only at this ⊢; omega,
     by rw [haw_nat]; dsimp only at hrecs_hi ⊢; omega⟩
  have hwok_a0 : WordsOK s0 (aw.toNat, 120) :=
    ⟨by rw [haw_nat]; have := hwok_all.1; omega, by omega, fun k hk => by
      have h := hwok_all.2.2 (15 * iw.toNat + k) (by omega)
      have heq : recsw.toNat + 8 * (15 * iw.toNat + k) = aw.toNat + 8 * k := by rw [haw_nat]; omega
      rwa [heq] at h⟩
  have hwok_a1 : WordsOK s1 (aw.toNat, 120) :=
    txEnc_wordsOK_below_hp hAR0 hs1_eff0 hRl_ge hins_a hwok_a0
  have ha_congr : authEntryPayloadPure s1 aw.toNat = authEntryPayloadPure s0 aw.toNat :=
    authEntryPayloadPure_congr (fun off hoff8 hoff_hi =>
      (txEnc_wordAt_memW_below_hp hAR0 hs1_eff0 hRl_ge hins_a hwok_a0 off hoff8 hoff_hi).2)
  obtain ⟨s2, hpl_nat_s1, _, _, _, hs2_loc, hs2_eff, hnt2, hdc2⟩ :=
    eval_decCall_auth_payload_len s1 s1 "pl" (.var .local (ofString "a")) aw _ Rl gw
      hs1_AR rfl hwok_a1 (by simp [evalHOLExact, hs1_a]) hnt
  rw [hdc2]
  dsimp only
  let plw : BitVec 64 := BitVec.ofNat 64 (authEntryPayloadPure s1 aw.toNat)
  have hplw_nat : plw.toNat = authEntryPayloadPure s0 (recsw.toNat + 120 * iw.toNat) := by
    change (BitVec.ofNat 64 (authEntryPayloadPure s1 aw.toNat)).toNat = _
    rw [hpl_nat_s1, ha_congr, haw_nat]
  have hs2_efft : HeapByteEff t s2 Rl gw := hs1_efft.trans hs2_eff
  have hs2_eff0 : HeapByteEff s0 s2 Rl gw := heff0.trans hs2_efft
  have hs2_AR : ArenaReady s2 := hs2_eff0.arena
  have hs2_pl : s2.locals.lookup (ofString "pl") = some (.val (.word plw)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, plw]
  have hs2_a : s2.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
      show ofString "pl" ≠ ofString "a" by decide]
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    rw [hs2_loc]; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_p,
      show ofString "pl" ≠ ofString "p" by decide, show ofString "a" ≠ ofString "p" by decide]
  obtain ⟨w_old0, hw_old0⟩ := ht_w
  have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w_old0)) := by
    rw [hs2_loc]; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw_old0,
      show ofString "pl" ≠ ofString "w" by decide, show ofString "a" ≠ ofString "w" by decide]
  have hs2_other : ∀ k, k ≠ ofString "pl" → k ≠ ofString "a" →
      s2.locals.lookup k = t.locals.lookup k := by
    intro k h1 h2
    rw [hs2_loc]
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, h1.symm, h2.symm]
  let lc := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 0)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 16)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))
  let ln := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 40)))
  let ly := rlpWordEncodedLenPure (BitVec.ofNat 64 (memW s0 (aw.toNat + 48)))
  let lr := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 56)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 72)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
  let ls := txU256EncodedLenPure
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 88)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 104)))
    (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
  have hlc_le : lc ≤ 33 := (u256ByteLengthPure_bounds _ _ _ _).2.2.2.2.2
  have hln_le : ln ≤ 9 := (rlpWordEncodedLenPure_bounds _).2
  have hly_le : ly ≤ 9 := (rlpWordEncodedLenPure_bounds _).2
  have hlr_le : lr ≤ 33 := (u256ByteLengthPure_bounds _ _ _ _).2.2.2.2.2
  have hls_le : ls ≤ 33 := (u256ByteLengthPure_bounds _ _ _ _).2.2.2.2.2
  have hpl_decomp : plw.toNat = lc + 21 + ln + ly + lr + ls := by
    rw [hplw_nat, ← haw_nat]
    rfl
  have hentry_tot_eq : rlpHeaderLenPure plw.toNat + plw.toNat =
      authEntryTotalPure s0 recsw.toNat iw.toNat := by
    dsimp only [authEntryTotalPure]; rw [hplw_nat]
  have hp_entry_le : pw.toNat + authEntryTotalPure s0 recsw.toNat iw.toNat ≤ ivl0.1 + ivl0.2 := by
    rw [hp_eq]; omega
  -- Call 1: rlp_encode_list_header(p, pl)
  have hc1 := eval_call_local_rlp_encode_list_header s2 "w"
    (.var .local (ofString "p")) (.var .local (ofString "pl"))
    pw plw Rl gw hs2_AR.1.code hs2_AR ⟨w_old0, hs2_w⟩
    (by simp [evalHOLExact, hs2_p]) (by simp [evalHOLExact, hs2_pl])
    ⟨ivl0, hivl0, by rw [hp_eq]; omega, by omega⟩
    (by intro hto; have h := hnt2; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
  have hstep1 := txEnc_seq_call_assign_p_exact hs2_efft hs2_p
    (exactLen := rlpHeaderLenPure plw.toNat)
    (by have := (rlpHeaderLenPure_bounds plw.toNat).2; omega)
    ⟨fun hnone => by obtain ⟨hl, h1, _, _, _, _, h2, h3⟩ := hc1.1 hnone; exact ⟨hl, h1, h2, h3⟩, hc1.2⟩
    hnt2
  dsimp only at hstep1
  rcases hstep1 with ⟨len1, s3, hlen1_eq, hp3_nat, hs3_loc, hs3_efft, hnt3, heq1⟩ | ⟨hne1, hnr1⟩
  · rw [heq1]
    let p3 := pw + len1
    have hp3_val : p3.toNat = pw.toNat + rlpHeaderLenPure plw.toNat := hp3_nat
    have hs3_eff0 : HeapByteEff s0 s3 Rl gw := heff0.trans hs3_efft
    have hs3_AR : ArenaReady s3 := hs3_eff0.arena
    have hs3_p : s3.locals.lookup (ofString "p") = some (.val (.word p3)) := by
      rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p3]
    have hs3_w : s3.locals.lookup (ofString "w") = some (.val (.word len1)) := by
      rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" by decide]
    have hs3_a : s3.locals.lookup (ofString "a") = some (.val (.word aw)) := by
      rw [hs3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_a,
        show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
    -- Call 2: tx_put_u256(p, load comb4 (a + 0))
    have hev_u0 := txEnc_eval_load_u256_below_hp hAR0 hs3_eff0 hRl_ge hins_a hwok_a0 "a" hs3_a 0
      (by omega) (by omega)
    have hc2 := eval_call_local_tx_put_u256 s3 "w"
      (.var .local (ofString "p"))
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 0#64]))
      p3
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 0)))
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 8)))
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 16)))
      (BitVec.ofNat 64 (memW s0 (aw.toNat + 24)))
      Rl gw hs3_AR.1.code hs3_AR hgw ⟨len1, hs3_w⟩
      (by simp [evalHOLExact, hs3_p]) hev_u0
      ⟨ivl0, hivl0, by omega, by dsimp only [lc] at hpl_decomp; omega⟩
      (by intro hto; have h := hnt3; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
    have hstep2 := txEnc_seq_call_assign_p_exact hs3_efft hs3_p
      (exactLen := lc) (by omega)
      ⟨fun hnone => by obtain ⟨len, h1, _, _, _, _, h2, h3⟩ := hc2.1 hnone; exact ⟨len, h1, h2, h3⟩, hc2.2⟩
      hnt3
    dsimp only at hstep2
    rcases hstep2 with ⟨len2, s4, hlen2_eq, hp4_nat, hs4_loc, hs4_efft, hnt4, heq2⟩ | ⟨hne2, hnr2⟩
    · rw [heq2]
      let p4 := p3 + len2
      have hp4_val : p4.toNat = p3.toNat + lc := hp4_nat
      have hs4_eff0 : HeapByteEff s0 s4 Rl gw := heff0.trans hs4_efft
      have hs4_AR : ArenaReady s4 := hs4_eff0.arena
      have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word p4)) := by
        rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p4]
      have hs4_w : s4.locals.lookup (ofString "w") = some (.val (.word len2)) := by
        rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "w" by decide]
      have hs4_a : s4.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_a,
          show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
      -- Call 3: rlp_encode_bytes(p, load .one (a + 32), 20)
      have hev_a32 := txEnc_eval_load_word_below_hp hAR0 hs4_eff0 hRl_ge hins_a hwok_a0 "a" hs4_a 32
        (by omega) (by omega)
      have hc3 := eval_call_local_rlp_encode_bytes_n_ne_one s4 "w"
        (.var .local (ofString "p"))
        (.load .one (.op .add [.var .local (ofString "a"), .const 32#64]))
        (.const 20#64)
        p4 (BitVec.ofNat 64 (memW s0 (aw.toNat + 32))) 20#64 Rl gw
        hs4_AR.1.code hs4_AR ⟨len2, hs4_w⟩
        (by simp [evalHOLExact, hs4_p]) hev_a32 rfl (by decide)
        (by rw [heapEnd_val]; decide)
        ⟨ivl0, hivl0, by omega, by
          have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
          rw [h20, hrlp20]; omega⟩
        (by intro hto; have h := hnt4; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
      have hstep3 := txEnc_seq_call_assign_p_exact hs4_efft hs4_p
        (exactLen := 21) (by omega)
        ⟨fun hnone => by
          obtain ⟨len, h1, _, _, h2, h3⟩ := hc3.1 hnone
          have h20 : (20#64 : BitVec 64).toNat = 20 := rfl
          rw [h20, hrlp20] at h1
          exact ⟨len, h1, h2, h3⟩, hc3.2⟩
        hnt4
      dsimp only at hstep3
      rcases hstep3 with ⟨len3, s5, hlen3_eq, hp5_nat, hs5_loc, hs5_efft, hnt5, heq3⟩ | ⟨hne3, hnr3⟩
      · rw [heq3]
        let p5 := p4 + len3
        have hp5_val : p5.toNat = p4.toNat + 21 := hp5_nat
        have hs5_eff0 : HeapByteEff s0 s5 Rl gw := heff0.trans hs5_efft
        have hs5_AR : ArenaReady s5 := hs5_eff0.arena
        have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word p5)) := by
          rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p5]
        have hs5_w : s5.locals.lookup (ofString "w") = some (.val (.word len3)) := by
          rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "p" ≠ ofString "w" by decide]
        have hs5_a : s5.locals.lookup (ofString "a") = some (.val (.word aw)) := by
          rw [hs5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs4_a,
            show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
        -- Call 4: rlp_encode_word(p, load .one (a + 40))
        have hev_a40 := txEnc_eval_load_word_below_hp hAR0 hs5_eff0 hRl_ge hins_a hwok_a0 "a" hs5_a 40
          (by omega) (by omega)
        have hc4 := eval_call_local_rlp_encode_word_exact s5 "w"
          (.var .local (ofString "p"))
          (.load .one (.op .add [.var .local (ofString "a"), .const 40#64]))
          p5 (BitVec.ofNat 64 (memW s0 (aw.toNat + 40))) Rl gw
          hs5_AR.1.code hs5_AR ⟨len3, hs5_w⟩
          (by simp [evalHOLExact, hs5_p]) hev_a40
          ⟨ivl0, hivl0, by omega, by dsimp only [ln] at hpl_decomp; omega⟩
          (by intro hto; have h := hnt5; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
        have hstep4 := txEnc_seq_call_assign_p_exact hs5_efft hs5_p
          (exactLen := ln) (by omega)
          ⟨fun hnone => by obtain ⟨len, h1, _, _, _, _, h2, h3⟩ := hc4.1 hnone; exact ⟨len, h1, h2, h3⟩, hc4.2⟩
          hnt5
        dsimp only at hstep4
        rcases hstep4 with ⟨len4, s6, hlen4_eq, hp6_nat, hs6_loc, hs6_efft, hnt6, heq4⟩ | ⟨hne4, hnr4⟩
        · rw [heq4]
          let p6 := p5 + len4
          have hp6_val : p6.toNat = p5.toNat + ln := hp6_nat
          have hs6_eff0 : HeapByteEff s0 s6 Rl gw := heff0.trans hs6_efft
          have hs6_AR : ArenaReady s6 := hs6_eff0.arena
          have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word p6)) := by
            rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p6]
          have hs6_w : s6.locals.lookup (ofString "w") = some (.val (.word len4)) := by
            rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "p" ≠ ofString "w" by decide]
          have hs6_a : s6.locals.lookup (ofString "a") = some (.val (.word aw)) := by
            rw [hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs5_a,
              show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
          -- Call 5: rlp_encode_word(p, load .one (a + 48))
          have hev_a48 := txEnc_eval_load_word_below_hp hAR0 hs6_eff0 hRl_ge hins_a hwok_a0 "a" hs6_a 48
            (by omega) (by omega)
          have hc5 := eval_call_local_rlp_encode_word_exact s6 "w"
            (.var .local (ofString "p"))
            (.load .one (.op .add [.var .local (ofString "a"), .const 48#64]))
            p6 (BitVec.ofNat 64 (memW s0 (aw.toNat + 48))) Rl gw
            hs6_AR.1.code hs6_AR ⟨len4, hs6_w⟩
            (by simp [evalHOLExact, hs6_p]) hev_a48
            ⟨ivl0, hivl0, by omega, by dsimp only [ly] at hpl_decomp; omega⟩
            (by intro hto; have h := hnt6; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
          have hstep5 := txEnc_seq_call_assign_p_exact hs6_efft hs6_p
            (exactLen := ly) (by omega)
            ⟨fun hnone => by obtain ⟨len, h1, _, _, _, _, h2, h3⟩ := hc5.1 hnone; exact ⟨len, h1, h2, h3⟩, hc5.2⟩
            hnt6
          dsimp only at hstep5
          rcases hstep5 with ⟨len5, s7, hlen5_eq, hp7_nat, hs7_loc, hs7_efft, hnt7, heq5⟩ | ⟨hne5, hnr5⟩
          · rw [heq5]
            let p7 := p6 + len5
            have hp7_val : p7.toNat = p6.toNat + ly := hp7_nat
            have hs7_eff0 : HeapByteEff s0 s7 Rl gw := heff0.trans hs7_efft
            have hs7_AR : ArenaReady s7 := hs7_eff0.arena
            have hs7_p : s7.locals.lookup (ofString "p") = some (.val (.word p7)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p7]
            have hs7_w : s7.locals.lookup (ofString "w") = some (.val (.word len5)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "p" ≠ ofString "w" by decide]
            have hs7_a : s7.locals.lookup (ofString "a") = some (.val (.word aw)) := by
              rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs6_a,
                show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
            -- Call 6: tx_put_u256(p, load comb4 (a + 56))
            have hev_u56 := txEnc_eval_load_u256_below_hp hAR0 hs7_eff0 hRl_ge hins_a hwok_a0 "a" hs7_a 56
              (by omega) (by omega)
            have hc6 := eval_call_local_tx_put_u256 s7 "w"
              (.var .local (ofString "p"))
              (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 56#64]))
              p7
              (BitVec.ofNat 64 (memW s0 (aw.toNat + 56)))
              (BitVec.ofNat 64 (memW s0 (aw.toNat + 64)))
              (BitVec.ofNat 64 (memW s0 (aw.toNat + 72)))
              (BitVec.ofNat 64 (memW s0 (aw.toNat + 80)))
              Rl gw hs7_AR.1.code hs7_AR hgw ⟨len5, hs7_w⟩
              (by simp [evalHOLExact, hs7_p]) hev_u56
              ⟨ivl0, hivl0, by omega, by dsimp only [lr] at hpl_decomp; omega⟩
              (by intro hto; have h := hnt7; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
            have hstep6 := txEnc_seq_call_assign_p_exact hs7_efft hs7_p
              (exactLen := lr) (by omega)
              ⟨fun hnone => by obtain ⟨len, h1, _, _, _, _, h2, h3⟩ := hc6.1 hnone; exact ⟨len, h1, h2, h3⟩, hc6.2⟩
              hnt7
            dsimp only at hstep6
            rcases hstep6 with ⟨len6, s8, hlen6_eq, hp8_nat, hs8_loc, hs8_efft, hnt8, heq6⟩ | ⟨hne6, hnr6⟩
            · rw [heq6]
              let p8 := p7 + len6
              have hp8_val : p8.toNat = p7.toNat + lr := hp8_nat
              have hs8_eff0 : HeapByteEff s0 s8 Rl gw := heff0.trans hs8_efft
              have hs8_AR : ArenaReady s8 := hs8_eff0.arena
              have hs8_p : s8.locals.lookup (ofString "p") = some (.val (.word p8)) := by
                rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p8]
              have hs8_w : s8.locals.lookup (ofString "w") = some (.val (.word len6)) := by
                rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "p" ≠ ofString "w" by decide]
              have hs8_a : s8.locals.lookup (ofString "a") = some (.val (.word aw)) := by
                rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_a,
                  show ofString "p" ≠ ofString "a" by decide, show ofString "w" ≠ ofString "a" by decide]
              -- Call 7: tx_put_u256(p, load comb4 (a + 88))
              have hev_u88 := txEnc_eval_load_u256_below_hp hAR0 hs8_eff0 hRl_ge hins_a hwok_a0 "a" hs8_a 88
                (by omega) (by omega)
              have hc7 := eval_call_local_tx_put_u256 s8 "w"
                (.var .local (ofString "p"))
                (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 88#64]))
                p8
                (BitVec.ofNat 64 (memW s0 (aw.toNat + 88)))
                (BitVec.ofNat 64 (memW s0 (aw.toNat + 96)))
                (BitVec.ofNat 64 (memW s0 (aw.toNat + 104)))
                (BitVec.ofNat 64 (memW s0 (aw.toNat + 112)))
                Rl gw hs8_AR.1.code hs8_AR hgw ⟨len6, hs8_w⟩
                (by simp [evalHOLExact, hs8_p]) hev_u88
                ⟨ivl0, hivl0, by omega, by dsimp only [ls] at hpl_decomp; omega⟩
                (by intro hto; have h := hnt8; rw [evaluateHOLFiniteState_seq_line780] at h; simp [hto] at h)
              have hstep7 := txEnc_seq_call_assign_p_exact hs8_efft hs8_p
                (exactLen := ls) (by omega)
                ⟨fun hnone => by obtain ⟨len, h1, _, _, _, _, h2, h3⟩ := hc7.1 hnone; exact ⟨len, h1, h2, h3⟩, hc7.2⟩
                hnt8
              dsimp only at hstep7
              rcases hstep7 with ⟨len7, s9, hlen7_eq, hp9_nat, hs9_loc, hs9_efft, hnt9, heq7⟩ | ⟨hne7, hnr7⟩
              · rw [heq7]
                let p9 := p8 + len7
                have hp9_val : p9.toNat = p8.toNat + ls := hp9_nat
                have hs9_p : s9.locals.lookup (ofString "p") = some (.val (.word p9)) := by
                  rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, p9]
                have hs9_w : s9.locals.lookup (ofString "w") = some (.val (.word len7)) := by
                  rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "p" ≠ ofString "w" by decide]
                have hs9_other : ∀ k, k ≠ ofString "p" → k ≠ ofString "w" →
                    k ≠ ofString "pl" → k ≠ ofString "a" →
                    s9.locals.lookup k = t.locals.lookup k := by
                  intro k hp_ne hw_ne h1 h2
                  rw [hs9_loc, hs8_loc, hs7_loc, hs6_loc, hs5_loc, hs4_loc, hs3_loc]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, hp_ne, hw_ne, hp_ne.symm, hw_ne.symm]
                  exact hs2_other k h1 h2
                have hs9_i : s9.locals.lookup (ofString "i") = some (.val (.word iw)) := by
                  rw [hs9_other (ofString "i") (by decide) (by decide) (by decide) (by decide)]
                  exact ht_i
                rw [evaluateHOLFiniteState_assign] at hnt9 ⊢
                have hev_i1 : @evalHOLExact 64 F _ s9.toExact (fun a => Classical.propDecidable (s9.memaddrs a))
                    (.op .add [.var .local (ofString "i"), .const 1#64]) =
                    some (.val (.word (iw + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs9_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hev_i1] at hnt9 ⊢; dsimp only at hnt9 ⊢
                have hvv_i : isValidValueHOLFinite s9 .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
                  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_i, shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hvv_i] at hnt9 ⊢; dsimp only at hnt9 ⊢
                let s10 := setKvarHOLFinite .local (ofString "i") (.val (.word (iw + 1#64))) s9
                have hloc_out : ∀ k, k ≠ ofString "pl" → k ≠ ofString "a" →
                    ((HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq s10.locals (ofString "pl", s1.locals.lookup (ofString "pl")))
                      (ofString "a", t.locals.lookup (ofString "a")))).lookup k = s10.locals.lookup k := by
                  intro k h1 h2
                  rw [txEnc_lookup_resVarEq_ne _ _ _ _ h2.symm,
                      txEnc_lookup_resVarEq_ne _ _ _ _ h1.symm]
                have hp9_tot : p9.toNat =
                    p_base.toNat + authListPayloadSumPure s0 recsw.toNat (iw.toNat + 1) := by
                  rw [hp9_val, hp8_val, hp7_val, hp6_val, hp5_val, hp4_val, hp3_val,
                      hp_eq, htot_eq_step, ← hentry_tot_eq]
                  omega
                refine ⟨fun _ => ⟨hs9_efft.locals_clock _ _, ?_, ?_, ?_, ?_, ?_, p9, ?_, hp9_tot⟩,
                  fun h => False.elim (h rfl)⟩
                · rw [hloc_out (ofString "dst") (by decide) (by decide)]
                  simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "i" ≠ ofString "dst" by decide, ↓reduceIte]
                  rw [hs9_other (ofString "dst") (by decide) (by decide) (by decide) (by decide)]
                  exact ht_dst
                · rw [hloc_out (ofString "recs") (by decide) (by decide)]
                  simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "i" ≠ ofString "recs" by decide, ↓reduceIte]
                  rw [hs9_other (ofString "recs") (by decide) (by decide) (by decide) (by decide)]
                  exact ht_recs
                · rw [hloc_out (ofString "n") (by decide) (by decide)]
                  simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "i" ≠ ofString "n" by decide, ↓reduceIte]
                  rw [hs9_other (ofString "n") (by decide) (by decide) (by decide) (by decide)]
                  exact ht_n
                · rw [hloc_out (ofString "i") (by decide) (by decide)]
                  simp [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · refine ⟨len7, ?_⟩
                  rw [hloc_out (ofString "w") (by decide) (by decide)]
                  simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "i" ≠ ofString "w" by decide, ↓reduceIte]
                  exact hs9_w
                · rw [hloc_out (ofString "p") (by decide) (by decide)]
                  simp only [s10, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "i" ≠ ofString "p" by decide, ↓reduceIte]
                  exact hs9_p
              · exact ⟨fun h => False.elim (hne7 (by simpa using h)), fun _ hr => hnr7 (by simpa using hr)⟩
            · exact ⟨fun h => False.elim (hne6 (by simpa using h)), fun _ hr => hnr6 (by simpa using hr)⟩
          · exact ⟨fun h => False.elim (hne5 (by simpa using h)), fun _ hr => hnr5 (by simpa using hr)⟩
        · exact ⟨fun h => False.elim (hne4 (by simpa using h)), fun _ hr => hnr4 (by simpa using hr)⟩
      · exact ⟨fun h => False.elim (hne3 (by simpa using h)), fun _ hr => hnr3 (by simpa using hr)⟩
    · exact ⟨fun h => False.elim (hne2 (by simpa using h)), fun _ hr => hnr2 (by simpa using hr)⟩
  · exact ⟨fun h => False.elim (hne1 (by simpa using h)), fun _ hr => hnr1 (by simpa using hr)⟩

private theorem putAuthorizationsWhile_exact {F : Type}
    (clk : Nat) (s0 s_base t : PanSemStateFiniteExact 64 F)
    (p_base dst0 recsw nw iw pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hclk : t.clock ≤ clk)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 t Rl gw)
    (heff_b : HeapByteEff s_base t Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat))
    (hi_le : iw.toNat ≤ nw.toNat)
    (hp_eq : pw.toNat = p_base.toNat + authListPayloadSumPure s0 recsw.toNat iw.toNat)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
      p_base.toNat + authListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (ht_recs : t.locals.lookup (ofString "recs") = some (.val (.word recsw)))
    (ht_n : t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (ht_i : t.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ht_p : t.locals.lookup (ofString "p") = some (.val (.word pw)))
    (ht_w : ∃ w_old : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hnt : (evaluateHOLFiniteState t putAuthorizationsWhile).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState t putAuthorizationsWhile
    (out.1 = none →
      HeapByteEff s_base out.2 Rl gw ∧
      out.2.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      ∃ p_f : BitVec 64,
        out.2.locals.lookup (ofString "p") = some (.val (.word p_f)) ∧
        p_f.toNat = p_base.toNat + authListPayloadSumPure s0 recsw.toNat nw.toNat) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  induction clk generalizing t iw pw with
  | zero =>
    dsimp only [putAuthorizationsWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hcz : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
      rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0), if_pos hcz] at hnt
      exact absurd rfl hnt
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff_b, ht_dst, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
        fun h => False.elim (h rfl)⟩
  | succ clk ih =>
    dsimp only [putAuthorizationsWhile] at hnt ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt ⊢
    have hcond : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, ht_i, ht_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · rw [if_pos hlt, if_pos (by decide : (1#64 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hcz : t.clock = 0
      · rw [if_pos hcz] at hnt; exact absurd rfl hnt
      · rw [if_neg hcz] at hnt ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt ⊢
        set td := decClockHOLFinite t
        have htd_eff0 : HeapByteEff s0 td Rl gw := heff0.locals_clock t.locals (t.clock - 1)
        have htd_effb : HeapByteEff s_base td Rl gw := heff_b.locals_clock t.locals (t.clock - 1)
        have hcle_body := evaluateHOLFiniteState_clock_le td putAuthorizationsLoopBody
        have hnt_b : (evaluateHOLFiniteState td putAuthorizationsLoopBody).1 ≠ some .timeOut := by
          rcases hb_res : evaluateHOLFiniteState td putAuthorizationsLoopBody with ⟨rb, sb⟩
          rintro rfl; simp [hb_res] at hnt
        have hb_step := putAuthorizationsLoopBody_exact s0 td p_base dst0 recsw nw iw pw Rl gw
          hAR0 htd_eff0 hgw hRl_ge hn_lt hrecs_ins hrecs_ok hlt hp_eq hin_ivl
          ht_dst ht_recs ht_n ht_i ht_p ht_w hnt_b
        dsimp only at hb_step
        have hncb := txEncNoContBreak_sound putAuthorizationsLoopBody rfl td
        change (evaluateHOLFiniteState td putAuthorizationsLoopBody).1 ≠ some .continue ∧
          (evaluateHOLFiniteState td putAuthorizationsLoopBody).1 ≠ some .break at hncb
        change (evaluateHOLFiniteState td putAuthorizationsLoopBody).2.clock ≤ td.clock at hcle_body
        obtain ⟨rb, sb, hb_res⟩ : ∃ rb sb, evaluateHOLFiniteState td putAuthorizationsLoopBody = (rb, sb) :=
          ⟨_, _, Prod.mk.eta.symm⟩
        rw [hb_res] at hb_step hcle_body hncb hnt ⊢
        dsimp only at hb_step hcle_body hncb hnt ⊢
        cases rb with
        | none =>
          obtain ⟨hsb_eff_td, hsb_dst, hsb_recs, hsb_n, hsb_i, hsb_w, p_next, hsb_p, hp_next_eq⟩ :=
            hb_step.1 rfl
          have hi1_nat : (iw + 1#64).toNat = iw.toNat + 1 := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 = _
            exact Nat.mod_eq_of_lt (by omega)
          have hsb_clk : sb.clock ≤ clk := by
            change sb.clock ≤ t.clock - 1 at hcle_body; omega
          have hnt_ih : (evaluateHOLFiniteState sb putAuthorizationsWhile).1 ≠ some .timeOut := hnt
          have hih := ih sb (iw + 1#64) p_next hsb_clk
            (htd_eff0.trans hsb_eff_td) (htd_effb.trans hsb_eff_td)
            (by rw [hi1_nat]; omega) (by rw [hi1_nat]; exact hp_next_eq)
            hsb_dst hsb_recs hsb_n hsb_i hsb_p hsb_w hnt_ih
          dsimp only [putAuthorizationsWhile] at hih
          exact hih
        | some r0 =>
          have hnr := hb_step.2 (by simp)
          cases r0 with
          | timeOut => exact absurd rfl hnt
          | «continue» => exact absurd rfl hncb.1
          | «break» => exact absurd rfl hncb.2
          | returned _ | exception _ _ | error | finalFfi _ =>
            dsimp only
            exact ⟨fun h => by simp at h, fun _ => hnr⟩
    · rw [if_neg hlt]
      have hij : iw.toNat = nw.toNat := by omega
      exact ⟨fun _ => ⟨heff_b, ht_dst, pw, ht_p, by rw [← hij]; exact hp_eq⟩,
        fun h => False.elim (h rfl)⟩

private theorem eval_call_local_tx_put_authorizations {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp recsExp nExp : ExpHOL 64)
    (dst0 recsw nw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hrecs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) recsExp =
      some (.val (.word recsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hn_lt : nw.toNat < 2 ^ 32)
    (hrecs_ins : 0 < nw.toNat → Inside (recsw.toNat, 120 * nw.toNat) sourceBase (globN s0 "heap_ptr"))
    (hrecs_ok : 0 < nw.toNat → WordsOK s0 (recsw.toNat, 120 * nw.toNat))
    (hin_ivl : ∃ ivl ∈ Rl,
      ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure (authListPayloadSumPure s0 recsw.toNat nw.toNat) +
        authListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
      ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_authorizations")
        [dstExp, recsExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "tx_put_authorizations")
        [dstExp, recsExp, nExp])
    let au := authListPayloadSumPure s0 recsw.toNat nw.toNat
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat = rlpHeaderLenPure au + au ∧
        len.toNat ≤ 9 + au ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out au; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hs_AR : ArenaReady s := heff0.arena
  have hcode : s.code = originalRuntimeCode := hs_AR.1.code
  have hb_body : sourceFnBody Guest.Software.guestFn_tx_put_authorizations =
      .decCall (ofString "total") .one (ofString "auth_list_payload_len")
        [.var .local (ofString "recs"), .var .local (ofString "n")]
        (.decCall (ofString "w") .one (ofString "rlp_encode_list_header")
          [.var .local (ofString "dst"), .var .local (ofString "total")]
          (.dec (ofString "p") .one
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
            (.dec (ofString "i") .one (.const 0#64)
              (.seq putAuthorizationsWhile
                (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))) := rfl
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
    have hent_effs : HeapByteEff s ent Rl gw :=
      (HeapByteEff.refl hs_AR Rl gw).locals_clock ent.locals ent.clock
    have hent_eff0 : HeapByteEff s0 ent Rl gw := heff0.trans hent_effs
    have hent_AR : ArenaReady ent := hent_eff0.arena
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "recs" ≠ ofString "dst" by decide]
    have hent_recs : ent.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "recs" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hnt_body : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_authorizations)).1 ≠
        some .timeOut := by
      rcases hx : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_put_authorizations) with ⟨rx, sx⟩
      rintro rfl; simp [hx] at hnt
    rw [hb_body] at hnt hnt_body ⊢
    have hent_mw : ∀ k < nw.toNat, ∀ off, off % 8 = 0 → off + 8 ≤ 120 →
        memW ent (recsw.toNat + 120 * k + off) = memW s0 (recsw.toNat + 120 * k + off) := by
      intro k hk off hoff8 hoff_hi
      have h := (txEnc_wordAt_memW_below_hp hAR0 hent_eff0 hRl_ge
        (hrecs_ins (by omega)) (hrecs_ok (by omega)) (120 * k + off) (by omega) (by omega)).2
      have heq : recsw.toNat + (120 * k + off) = recsw.toNat + 120 * k + off := by omega
      rwa [heq] at h
    have hent_recs_ok : 0 < nw.toNat → WordsOK ent (recsw.toNat, 120 * nw.toNat) :=
      fun hpos => txEnc_wordsOK_below_hp hAR0 hent_eff0 hRl_ge (hrecs_ins hpos) (hrecs_ok hpos)
    have hau_congr : authListPayloadSumPure ent recsw.toNat nw.toNat =
        authListPayloadSumPure s0 recsw.toNat nw.toNat :=
      authListPayloadSumPure_congr hent_mw
    obtain ⟨m1, htot_nat, _, _, hm1_loc, hm1_eff, hnt1, hdc1⟩ :=
      eval_decCall_auth_list_payload_len ent ent "total"
        (.var .local (ofString "recs")) (.var .local (ofString "n"))
        recsw nw _ Rl gw hent_AR rfl hn_lt hent_recs_ok
        (by simp [evalHOLExact, hent_recs]) (by simp [evalHOLExact, hent_n]) hnt_body
    rw [hdc1] at hnt ⊢
    dsimp only at hnt ⊢
    let totw : BitVec 64 := BitVec.ofNat 64 (authListPayloadSumPure ent recsw.toNat nw.toNat)
    have htotw_au : totw.toNat = authListPayloadSumPure s0 recsw.toNat nw.toNat :=
      htot_nat.trans hau_congr
    have hm1_effs : HeapByteEff s m1 Rl gw := hent_effs.trans hm1_eff
    have hm1_eff0 : HeapByteEff s0 m1 Rl gw := heff0.trans hm1_effs
    have hm1_AR : ArenaReady m1 := hm1_eff0.arena
    have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
        show ofString "total" ≠ ofString "dst" by decide]
    have hm1_recs : m1.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_recs,
        show ofString "total" ≠ ofString "recs" by decide]
    have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_n,
        show ofString "total" ≠ ofString "n" by decide]
    have hm1_tot : m1.locals.lookup (ofString "total") = some (.val (.word totw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, totw]
    have hin_hdr : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure totw.toNat ≤ ivl.1 + ivl.2 := by
      obtain ⟨ivl, hivl, hlo, hhi, _⟩ := hin_ivl
      exact ⟨ivl, hivl, hlo, by rw [htotw_au]; omega⟩
    have hdc2 := eval_decCall_rlp_encode_list_header_outcomes m1 "w"
      (.var .local (ofString "dst")) (.var .local (ofString "total"))
      dst0 totw
      (.dec (ofString "p") .one
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
        (.dec (ofString "i") .one (.const 0#64)
          (.seq putAuthorizationsWhile
            (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))
      Rl gw hm1_AR.1.code hm1_AR
      (by simp [evalHOLExact, hm1_dst]) (by simp [evalHOLExact, hm1_tot]) hin_hdr hnt1
    dsimp only at hdc2
    rcases hdc2 with ⟨mid, hhl_nat, _, _, _, _, hmid_loc, hmid_eff, hnt_mid, hbody_eq⟩ | ⟨hne_none, hnr⟩
    · rw [hbody_eq] at hnt ⊢
      let hl := BitVec.ofNat 64 (rlpHeaderLenPure totw.toNat)
      have hhl_nat' : hl.toNat = rlpHeaderLenPure totw.toNat := hhl_nat
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_dst,
          show ofString "w" ≠ ofString "dst" by decide]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word hl)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl]
      have hmid_recs : mid.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_recs,
          show ofString "w" ≠ ofString "recs" by decide]
      have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_n,
          show ofString "w" ≠ ofString "n" by decide]
      let p_base : BitVec 64 := dst0 + hl
      have hp_base_nat : p_base.toNat =
          dst0.toNat + rlpHeaderLenPure (authListPayloadSumPure s0 recsw.toNat nw.toNat) := by
        change (dst0 + hl).toNat = _
        rw [BitVec.toNat_add, hhl_nat', htotw_au]
        obtain ⟨ivl, _, _, hhi, hlim⟩ := hin_ivl
        have : dst0.toNat + rlpHeaderLenPure (authListPayloadSumPure s0 recsw.toNat nw.toNat) < 2 ^ 64 := by omega
        exact Nat.mod_eq_of_lt this
      have hev_p0 : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
           (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")]) =
           some (.val (.word p_base)) := by
        simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_base]
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      simp only [hev_p0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_p := setVarHOLFinite (ofString "p") (.val (.word p_base)) mid
      rw [evaluateHOLFiniteState_dec_total] at hnt_mid ⊢
      have hev_i0 : @evalHOLExact 64 F _ s_p.toExact (fun a => Classical.propDecidable (s_p.memaddrs a))
          (.const 0#64) = some (.val (.word 0#64)) := rfl
      simp only [hev_i0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt_mid ⊢
      set s_i := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s_p
      have hsi_effs : HeapByteEff s s_i Rl gw :=
        (hm1_effs.trans hmid_eff).locals_clock s_i.locals s_i.clock
      have hsi_eff0 : HeapByteEff s0 s_i Rl gw := heff0.trans hsi_effs
      have hsi_dst : s_i.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_dst,
          show ofString "i" ≠ ofString "dst" by decide, show ofString "p" ≠ ofString "dst" by decide]
      have hsi_recs : s_i.locals.lookup (ofString "recs") = some (.val (.word recsw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_recs,
          show ofString "i" ≠ ofString "recs" by decide, show ofString "p" ≠ ofString "recs" by decide]
      have hsi_n : s_i.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_n,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide]
      have hsi_i : s_i.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [s_i, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsi_p : s_i.locals.lookup (ofString "p") = some (.val (.word p_base)) := by
        simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide]
      have hsi_w : ∃ w0 : BitVec 64, s_i.locals.lookup (ofString "w") = some (.val (.word w0)) :=
        ⟨hl, by simp [s_i, s_p, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_w,
          show ofString "i" ≠ ofString "w" by decide, show ofString "p" ≠ ofString "w" by decide]⟩
      rw [evaluateHOLFiniteState_seq_line780] at hnt_mid ⊢
      have hin_loop : ∃ ivl ∈ Rl, ivl.1 ≤ p_base.toNat ∧
          p_base.toNat + authListPayloadSumPure s0 recsw.toNat nw.toNat ≤ ivl.1 + ivl.2 ∧
          ivl.1 + ivl.2 ≤ heapLimit := by
        obtain ⟨ivl, hivl, hlo, hhi, hlim⟩ := hin_ivl
        exact ⟨ivl, hivl, by rw [hp_base_nat]; omega, by rw [hp_base_nat]; omega, hlim⟩
      have hnt_loop : (evaluateHOLFiniteState s_i putAuthorizationsWhile).1 ≠ some .timeOut := by
        intro hto; simp [hto] at hnt_mid
      have hloop := putAuthorizationsWhile_exact s_i.clock s0 s s_i p_base dst0 recsw nw 0#64 p_base Rl gw
        (Nat.le_refl _) hAR0 hsi_eff0 hsi_effs hgw hRl_ge hn_lt hrecs_ins hrecs_ok
        (by simp) (by simp [authListPayloadSumPure])
        hin_loop hsi_dst hsi_recs hsi_n hsi_i hsi_p hsi_w hnt_loop
      dsimp only at hloop
      rcases hw : evaluateHOLFiniteState s_i putAuthorizationsWhile with ⟨rw_res, sw⟩
      rw [hw] at hloop hnt_mid
      dsimp only at hloop hnt_mid ⊢
      cases rw_res with
      | none =>
        obtain ⟨hsw_effs, hsw_dst, p_f, hp_f, hpf_nat⟩ := hloop.1 rfl
        rw [evaluateHOLFiniteState_return] at hnt_mid ⊢
        have hev_ret : @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
            (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")]) =
            some (.val (.word (p_f - dst0))) := by
          simp [evalHOLExact, evalListHOLExact, hp_f, hsw_dst, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]
        have h132 : (1 : Nat) ≤ 32 := by decide
        simp only [sizeOfShapeWithContextHOL, shapeOfHOLExact, h132, ↓reduceIte]
        let len := p_f - dst0
        have hlen_nat : len.toNat = rlpHeaderLenPure au + au := by
          change (p_f - dst0).toNat = _
          dsimp only [au]
          have hle_pf : dst0.toNat ≤ p_f.toNat := by rw [hpf_nat, hp_base_nat]; omega
          have hsub : p_f.toNat - dst0.toNat =
              rlpHeaderLenPure (authListPayloadSumPure s0 recsw.toNat nw.toNat) +
                authListPayloadSumPure s0 recsw.toNat nw.toNat := by
            rw [hpf_nat, hp_base_nat]; omega
          have := BitVec.toNat_sub_of_le (x := p_f) (y := dst0) ((BitVec.le_def).2 hle_pf)
          omega
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        simp only [shapeEqHOL, hval, len, ↓reduceIte]
        set s_out := setKvarHOLFinite VarKind.local (ofString lname) (.val (.word len))
          { sw.emptyLocalsHOLFinite with locals := s.locals }
        have hout_eff : HeapByteEff s s_out Rl gw :=
          hsw_effs.locals_clock s_out.locals s_out.clock
        have hlen_le : len.toNat ≤ 9 + au := by
          rw [hlen_nat]; have := (rlpHeaderLenPure_bounds au).2; omega
        exact ⟨fun _ => ⟨len, hlen_nat, hlen_le, rfl, hout_eff⟩, fun h => False.elim (h rfl)⟩
      | some r =>
        have hnr_w := hloop.2 (by simp)
        have hncb_w := txEncNoContBreak_while
          (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
          putAuthorizationsLoopBody s_i
        change (evaluateHOLFiniteState s_i putAuthorizationsWhile).1 ≠ some .continue ∧
          (evaluateHOLFiniteState s_i putAuthorizationsWhile).1 ≠ some .break at hncb_w
        rw [hw] at hncb_w
        dsimp only at hncb_w
        cases r with
        | timeOut => exact absurd rfl hnt_mid
        | «continue» => exact absurd rfl hncb_w.1
        | «break» => exact absurd rfl hncb_w.2
        | returned rv => exact False.elim (hnr_w (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr_w (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · rcases hb_out : evaluateHOLFiniteState m1
          (.decCall (ofString "w") .one (ofString "rlp_encode_list_header")
            [.var .local (ofString "dst"), .var .local (ofString "total")]
            (.dec (ofString "p") .one
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "w")])
              (.dec (ofString "i") .one (.const 0#64)
                (.seq putAuthorizationsWhile
                  (.return (.op .sub [.var .local (ofString "p"), .var .local (ofString "dst")])))))) with ⟨rb, sb⟩
      rw [hb_out] at hne_none hnr hnt1
      dsimp only at hne_none hnr hnt1 ⊢
      cases rb with
      | none => exact False.elim (hne_none rfl)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt1
        | returned rv => exact False.elim (hnr (Or.inl ⟨rv, rfl⟩))
        | exception eid ev =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => hnr (by
            rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h; injection h with he hv; subst he hv
              exact Or.inr ⟨eid, ev, rfl, hne⟩)⟩
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem txEnc_seq_call_assign_p_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : String} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hp_sum : pw.toNat + bound < 2 ^ 64)
    (hcall :
      let out := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
      (out.1 = none →
        ∃ len : BitVec 64,
          len.toNat ≤ bound ∧
          out.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s out.2 Rl gw) ∧
      (out.1 ≠ none → ¬ Resumes out.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ bound ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  have hstep := txEnc_seq_call_assign_p heff0 hp hp_sum hcall hnt
  dsimp only at hstep
  rcases hstep with ⟨len, m, hlen_le, hplen_nat, hm_loc, hm_eff, hnt_m, heq⟩ | ⟨_, hnr⟩
  · rw [heq] at hres
    refine ⟨len, m, hlen_le, hplen_nat, ?_, ?_, ?_, hm_eff, hnt_m, hres, heq⟩
    · intro k hkw hkp
      rw [hm_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkw, Ne.symm hkp]
    · refine ⟨len, ?_⟩
      rw [hm_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" from M13.mls_ne rfl]
    · rw [hm_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · exact False.elim (hnr hres)

private theorem txEnc_seq_non_timeout {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s p1).1 ≠ some .timeOut := by
  intro hto
  rw [evaluateHOLFiniteState_seq_line780] at hnt
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  rw [h1] at hto hnt
  dsimp only at hto hnt
  subst hto
  exact hnt rfl

private theorem txEnc_seq_call_u256_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 33 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 33 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_u256_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt
  have hbnd_u := (u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))).2.2.2.2.2
  have hc := eval_call_local_tx_put_u256 s "w"
    (.var .local (ofString "p"))
    (.load (.comb [.one, .one, .one, .one])
      (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))
    Rl gw heff0.arena.1.code heff0.arena hgw hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩) hnt_c
  dsimp only at hc
  exact txEnc_seq_call_assign_p_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, _, hlen33, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen33, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_seq_call_word_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 9 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt
  have hc := eval_call_local_rlp_encode_word s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, h2⟩) hnt_c
  dsimp only at hc
  exact txEnc_seq_call_assign_p_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen9, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen9, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_assign_p_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : String} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hp_sum : pw.toNat + bound < 2 ^ 64)
    (hcall :
      let out := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
      (out.1 = none →
        ∃ len : BitVec 64,
          len.toNat ≤ bound ∧
          out.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s out.2 Rl gw) ∧
      (out.1 ≠ none → ¬ Resumes out.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ bound ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  dsimp only at hcall
  rcases hc : evaluateHOLFiniteState s
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args) with ⟨rc, sc⟩
  rw [hc] at hcall; dsimp only at hcall
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780, hc] at hnt hres ⊢
  cases rc with
  | some r =>
    dsimp only at hres
    exact False.elim (hcall.2 (by simp) hres)
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨len, hlen_le, hsc_loc, heff_sc⟩ := hcall.1 rfl
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word len)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_assign] at hnt hres ⊢
    have hev_add : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (pw + len))) := by
      have hpz : pw + (len + 0#64) = pw + len := by rw [BitVec.add_zero]
      simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, hpz]
    rw [hev_add] at hnt hres ⊢; dsimp only at hnt hres ⊢
    have hvv : isValidValueHOLFinite sc .local (ofString "p") (.val (.word (pw + len))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hsc_p, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvv] at hnt hres ⊢; dsimp only at hnt hres ⊢
    let m := setKvarHOLFinite .local (ofString "p") (.val (.word (pw + len))) sc
    have hm_loc : m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) := by
      change sc.locals.update (ofString "p", .val (.word (pw + len))) = _
      rw [hsc_loc]
    have hm_eff : HeapByteEff s0 m Rl gw :=
      (heff0.trans heff_sc).locals_clock m.locals m.clock
    have hplen_nat : (pw + len).toNat = pw.toNat + len.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨len, m, hlen_le, hplen_nat, ?_, ?_, ?_, hm_eff, hnt, hres, rfl⟩
    · intro k hkw hkp; rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkw, Ne.symm hkp]
    · refine ⟨len, ?_⟩; rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" from M13.mls_ne rfl]
    · rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem txEnc_call_word_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 9 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_rlp_encode_word s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, h2⟩) hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen9, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen9, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_u256_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 33 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 33 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
              [.var .local (ofString "p"),
               .load (.comb [.one, .one, .one, .one])
                 (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_u256_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hub := u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))
  have hc := eval_call_local_tx_put_u256 s "w"
    (.var .local (ofString "p"))
    (.load (.comb [.one, .one, .one, .one])
      (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))
    Rl gw heff0.arena.1.code heff0.arena hgw hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by have := hub.2.2.2.2.2; omega⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, _, hlen33, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen33, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_seq_call_to_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 21 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 21 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt
  have hc := eval_call_local_tx_put_to s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, h2⟩) hnt_c
  dsimp only at hc
  exact txEnc_seq_call_assign_p_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, hlen21, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen21, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_seq_call_bytes_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hdata_lt : memW s0 (txw.toNat + 200) < 2 ^ 32)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + memW s0 (txw.toNat + 200) ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + memW s0 (txw.toNat + 200) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_src := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 192 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 200 (by decide) (by decide)
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 200))
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 200) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 200))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds nw.toNat
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt
  have hc := eval_call_local_rlp_encode_bytes s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 192#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 200#64]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + 192))) nw
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_src hev_n
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩) hnt_c
  dsimp only at hc
  exact txEnc_seq_call_assign_p_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, hlen_le, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, by omega, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_ite_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cond : ExpHOL 64} {p_then p_else cont : ProgHOL 64}
    {cw pw : BitVec 64} {bound : Nat}
    (_heff0 : HeapByteEff s0 s Rl gw)
    (hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word cw)))
    (_hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hthen : cw ≠ 0#64 →
      (evaluateHOLFiniteState s (.seq p_then cont)).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s (.seq p_then cont)).1 →
      ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
        pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
        (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
        (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
        m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
        HeapByteEff s0 m Rl gw ∧
        (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
        Resumes (evaluateHOLFiniteState m cont).1 ∧
        evaluateHOLFiniteState s (.seq p_then cont) = evaluateHOLFiniteState m cont)
    (helse : cw = 0#64 →
      (evaluateHOLFiniteState s (.seq p_else cont)).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s (.seq p_else cont)).1 →
      ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
        pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
        (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
        (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
        m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
        HeapByteEff s0 m Rl gw ∧
        (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
        Resumes (evaluateHOLFiniteState m cont).1 ∧
        evaluateHOLFiniteState s (.seq p_else cont) = evaluateHOLFiniteState m cont)
    (hnt : (evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont)).1) :
    ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont) = evaluateHOLFiniteState m cont := by
  have heq_ite : evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont) =
      if cw = 0#64 then evaluateHOLFiniteState s (.seq p_else cont)
      else evaluateHOLFiniteState s (.seq p_then cont) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hc]
    dsimp only
    by_cases hcz : cw = 0#64
    · subst hcz; simp [evaluateHOLFiniteState_seq_line780]
    · have hcz0 : ¬ (cw = 0) := hcz
      rw [if_neg hcz0, if_neg hcz, evaluateHOLFiniteState_seq_line780]
  rw [heq_ite] at hnt hres ⊢
  by_cases hcz : cw = 0#64
  · rw [if_pos hcz] at hnt hres ⊢
    exact helse hcz hnt hres
  · rw [if_neg hcz] at hnt hres ⊢
    exact hthen hcz hnt hres

private theorem txEnc_skip_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_f : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_f)))
    (hnt : (evaluateHOLFiniteState s (.seq .skip cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq .skip cont)).1) :
    ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s (.seq .skip cont) = evaluateHOLFiniteState m cont := by
  have heq : evaluateHOLFiniteState s (.seq .skip cont) = evaluateHOLFiniteState s cont := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  rw [heq] at hnt hres ⊢
  exact ⟨pw, s, le_rfl, Nat.le_add_right _ _, fun _ _ _ => rfl, hw, hp, heff0, hnt, hres, rfl⟩

private theorem txEnc_call_access_list_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnal_lt : memW s0 (txw.toNat + 216) < 2 ^ 32)
    (hslots_lt : txAccessSlots s0 txw.toNat < 2 ^ 32)
    (hal_ins : 0 < memW s0 (txw.toNat + 216) →
      Inside (memW s0 (txw.toNat + 208), 24 * memW s0 (txw.toNat + 216)) sourceBase (globN s0 "heap_ptr"))
    (hal_wok : 0 < memW s0 (txw.toNat + 216) →
      WordsOK s0 (memW s0 (txw.toNat + 208), 24 * memW s0 (txw.toNat + 216)))
    (hmw208_lt : memW s0 (txw.toNat + 208) < 2 ^ 64)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + accessListPayloadSumPure s0 (memW s0 (txw.toNat + 208)) (memW s0 (txw.toNat + 216)) ≤
        ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + accessListPayloadSumPure s0 (memW s0 (txw.toNat + 208)) (memW s0 (txw.toNat + 216)) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_recs := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 208 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 216 (by decide) (by decide)
  let recsw := BitVec.ofNat 64 (memW s0 (txw.toNat + 208))
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 216))
  have hrecsw_nat : recsw.toNat = memW s0 (txw.toNat + 208) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 208))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmw208_lt
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 216) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 216))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (accessListPayloadSumPure s0 recsw.toNat nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_access_list s0 s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 208#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 216#64]))
    pw recsw nw Rl gw hAR0 heff0 hRl_ge hw
    (by simp [evalHOLExact, hp]) hev_recs hev_n
    (by rw [hnw_nat]; exact hnal_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hslots_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hal_ins)
    (by rw [hrecsw_nat, hnw_nat]; exact hal_wok)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hrecsw_nat, hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hrecsw_nat, hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_blob_hashes_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnbh_lt : memW s0 (txw.toNat + 264) < 2 ^ 32)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + 33 * memW s0 (txw.toNat + 264) ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + 33 * memW s0 (txw.toNat + 264) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_buf := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 256 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 264 (by decide) (by decide)
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 264))
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 264) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 264))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (33 * nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_blob_hashes s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 256#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 264#64]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + 256))) nw
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_buf hev_n
    (by rw [hnw_nat]; exact hnbh_lt)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_call_authorizations_step_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hnau_lt : memW s0 (txw.toNat + 280) < 2 ^ 32)
    (hau_ins : 0 < memW s0 (txw.toNat + 280) →
      Inside (memW s0 (txw.toNat + 272), 120 * memW s0 (txw.toNat + 280)) sourceBase (globN s0 "heap_ptr"))
    (hau_wok : 0 < memW s0 (txw.toNat + 280) →
      WordsOK s0 (memW s0 (txw.toNat + 272), 120 * memW s0 (txw.toNat + 280)))
    (hmw272_lt : memW s0 (txw.toNat + 272) < 2 ^ 64)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + authListPayloadSumPure s0 (memW s0 (txw.toNat + 272)) (memW s0 (txw.toNat + 280)) ≤
        ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + authListPayloadSumPure s0 (memW s0 (txw.toNat + 272)) (memW s0 (txw.toNat + 280)) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
               .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_recs := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 272 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 280 (by decide) (by decide)
  let recsw := BitVec.ofNat 64 (memW s0 (txw.toNat + 272))
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 280))
  have hrecsw_nat : recsw.toNat = memW s0 (txw.toNat + 272) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 272))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmw272_lt
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 280) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 280))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds (authListPayloadSumPure s0 recsw.toNat nw.toNat)
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_authorizations s0 s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 272#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 280#64]))
    pw recsw nw Rl gw hAR0 heff0 hgw hRl_ge hw
    (by simp [evalHOLExact, hp]) hev_recs hev_n
    (by rw [hnw_nat]; exact hnau_lt)
    (by rw [hrecsw_nat, hnw_nat]; exact hau_ins)
    (by rw [hrecsw_nat, hnw_nat]; exact hau_wok)
    (by
      obtain ⟨ivl, hivl, h1, h2, h3⟩ := hin_ivl
      rw [hrecsw_nat, hnw_nat] at hbnd_hl ⊢
      exact ⟨ivl, hivl, h1, by omega, h3⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_resumes heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen_le, hloc, heff_c⟩ := hc.1 hnone
      rw [hrecsw_nat, hnw_nat] at hlen_le
      exact ⟨len, hlen_le, hloc, heff_c⟩, hc.2⟩
    hnt hres

private theorem txEnc_trailer_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {buf bnd bodyw pw tw : BitVec 64}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_mem : (buf.toNat, bnd.toNat) ∈ Rl)
    (hbnd_ge10 : 10 ≤ bnd.toNat)
    (_hbuf_bnd_le_hl : buf.toNat + bnd.toNat ≤ heapLimit)
    (hbodyw_nat : bodyw.toNat = buf.toNat + 10)
    (hp_ge_body : bodyw.toNat ≤ pw.toNat)
    (hp_le_end : pw.toNat ≤ buf.toNat + bnd.toNat)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hbody : s.locals.lookup (ofString "body") = some (.val (.word bodyw)))
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hnt : (evaluateHOLFiniteState s
      (.dec (ofString "payload_len") .one
        (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload_len")]
          (.dec (ofString "start") .one
            (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "start"), .var .local (ofString "payload_len")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                  (.seq
                    (.assign .local (ofString "start")
                      (.op .sub [.var .local (ofString "start"), .const 1#64]))
                    (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                  .skip)
                (.return (.rstruct [
                  .var .local (ofString "start"),
                  .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.dec (ofString "payload_len") .one
        (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload_len")]
          (.dec (ofString "start") .one
            (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "start"), .var .local (ofString "payload_len")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                  (.seq
                    (.assign .local (ofString "start")
                      (.op .sub [.var .local (ofString "start"), .const 1#64]))
                    (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                  .skip)
                (.return (.rstruct [
                  .var .local (ofString "start"),
                  .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))).1) :
    HeapByteEff s0
      (evaluateHOLFiniteState s
        (.dec (ofString "payload_len") .one
          (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
          (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
            [.var .local (ofString "payload_len")]
            (.dec (ofString "start") .one
              (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
              (.seq
                (.call (some (none, none)) (ofString "rlp_encode_list_header")
                  [.var .local (ofString "start"), .var .local (ofString "payload_len")])
                (.seq
                  (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                    (.seq
                      (.assign .local (ofString "start")
                        (.op .sub [.var .local (ofString "start"), .const 1#64]))
                      (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                    .skip)
                  (.return (.rstruct [
                    .var .local (ofString "start"),
                    .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))).2
      Rl gw := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  -- 1. dec "payload_len" = p - body
  let plw : BitVec 64 := pw - bodyw
  have hplw_nat : plw.toNat = pw.toNat - bodyw.toNat := by
    change (pw - bodyw).toNat = _
    exact BitVec.toNat_sub_of_le hp_ge_body
  have hev_pl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")]) =
      some (.val (.word plw)) := by
    simp [evalHOLExact, evalListHOLExact, hp, hbody, wordOpHOL, wordOp, valueIsWord, valueWord, plw]
  have hsh_pl : shapeEqHOL .one (shapeOfHOLExact (.val (.word plw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_pl : ∀ cont_pl : ProgHOL 64,
      evaluateHOLFiniteState s
        (.dec (ofString "payload_len") .one
          (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")]) cont_pl) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).2.locals.resVarEq
           (ofString "payload_len", s.locals.lookup (ofString "payload_len")) }) := by
    intro cont_pl
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_pl]; dsimp only; rw [if_pos hsh_pl]
  rw [hdec_pl] at hnt hres; dsimp only at hnt hres
  apply txEnc_heapByteEff_of_eq_resVar (hdec_pl _)
  let u1 := setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s
  have heff_u1 : HeapByteEff s0 u1 Rl gw := heff0.locals_clock u1.locals u1.clock
  have hu1_pl : u1.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
      show ofString "payload_len" ≠ ofString "p" from M13.mls_ne rfl]
  have hu1_body : u1.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbody,
      show ofString "payload_len" ≠ ofString "body" from M13.mls_ne rfl]
  have hu1_t : u1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "payload_len" ≠ ofString "t" from M13.mls_ne rfl]
  -- 2. decCall "hl" = rlp_list_header_len(payload_len)
  obtain ⟨u2, hhl_nat, hhl_ge1, hhl_le9, _, _, hu2_loc, heff_u1_u2, hnt_u2, hdc_hl⟩ :=
    eval_decCall_rlp_list_header_len u1 "hl" (.var .local (ofString "payload_len")) plw _ Rl gw
      heff_u1.arena.1.code heff_u1.arena (by simp [evalHOLExact, hu1_pl]) hnt
  rw [hdc_hl] at hres; dsimp only at hres
  apply txEnc_heapByteEff_of_eq_resVar hdc_hl
  let hlw := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
  have heff_u2 : HeapByteEff s0 u2 Rl gw := heff_u1.trans heff_u1_u2
  have hu2_hl : u2.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlw]
  have hu2_pl : u2.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_pl,
      show ofString "hl" ≠ ofString "payload_len" from M13.mls_ne rfl]
  have hu2_p : u2.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_p,
      show ofString "hl" ≠ ofString "p" from M13.mls_ne rfl]
  have hu2_body : u2.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_body,
      show ofString "hl" ≠ ofString "body" from M13.mls_ne rfl]
  have hu2_t : u2.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_t,
      show ofString "hl" ≠ ofString "t" from M13.mls_ne rfl]
  -- 3. dec "start" = body - hl
  let startw : BitVec 64 := bodyw - hlw
  have hhl_le_body : hlw.toNat ≤ bodyw.toNat := by
    have : hlw.toNat ≤ 9 := hhl_le9
    omega
  have hstartw_nat : startw.toNat = bodyw.toNat - hlw.toNat := by
    change (bodyw - hlw).toNat = _
    exact BitVec.toNat_sub_of_le hhl_le_body
  have hev_st : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
      (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")]) =
      some (.val (.word startw)) := by
    simp [evalHOLExact, evalListHOLExact, hu2_body, hu2_hl, wordOpHOL, wordOp, valueIsWord, valueWord, startw]
  have hsh_st : shapeEqHOL .one (shapeOfHOLExact (.val (.word startw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_st : ∀ cont_st : ProgHOL 64,
      evaluateHOLFiniteState u2
        (.dec (ofString "start") .one
          (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")]) cont_st) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).2.locals.resVarEq
           (ofString "start", u2.locals.lookup (ofString "start")) }) := by
    intro cont_st
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_st]; dsimp only; rw [if_pos hsh_st]
  rw [hdec_st] at hnt_u2 hres; dsimp only at hnt_u2 hres
  apply txEnc_heapByteEff_of_eq_resVar (hdec_st _)
  let u3 := setVarHOLFinite (ofString "start") (.val (.word startw)) u2
  have heff_u3 : HeapByteEff s0 u3 Rl gw := heff_u2.locals_clock u3.locals u3.clock
  have hu3_st : u3.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hu3_pl : u3.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_pl,
      show ofString "start" ≠ ofString "payload_len" from M13.mls_ne rfl]
  have hu3_p : u3.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_p,
      show ofString "start" ≠ ofString "p" from M13.mls_ne rfl]
  have hu3_t : u3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_t,
      show ofString "start" ≠ ofString "t" from M13.mls_ne rfl]
  -- 4. call rlp_encode_list_header(start, payload_len)
  have hnt_elh := txEnc_seq_non_timeout u3 _ _ hnt_u2
  have hc_elh := eval_call_rlp_encode_list_header u3
    (.var .local (ofString "start")) (.var .local (ofString "payload_len"))
    startw plw Rl gw heff_u3.arena.1.code heff_u3.arena
    (by simp [evalHOLExact, hu3_st]) (by simp [evalHOLExact, hu3_pl])
    ⟨(buf.toNat, bnd.toNat), hRl_mem, by
      have hhle : hlw.toNat ≤ 9 := hhl_le9
      have hhge : 1 ≤ hlw.toNat := hhl_ge1
      have hheq : hlw.toNat = rlpHeaderLenPure plw.toNat := hhl_nat
      exact ⟨by omega, by omega⟩⟩
    hnt_elh
  dsimp only at hc_elh
  rcases helh : evaluateHOLFiniteState u3
    (.call (some (none, none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "start"), .var .local (ofString "payload_len")]) with ⟨relh, u4⟩
  rw [helh] at hc_elh; dsimp only at hc_elh
  rw [evaluateHOLFiniteState_seq_line780, helh] at hnt_u2 hres ⊢
  cases relh with
  | some r =>
    dsimp only at hres
    exact False.elim (hc_elh.2 (by simp) hres)
  | none =>
    dsimp only at hnt_u2 hres ⊢
    obtain ⟨_, heff_u3_u4, hu4_loc⟩ := hc_elh.1 rfl
    have heff_u4 : HeapByteEff s0 u4 Rl gw := heff_u3.trans heff_u3_u4
    have hu4_st : u4.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      rw [hu4_loc]; exact hu3_st
    have hu4_p : u4.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hu4_loc]; exact hu3_p
    have hu4_t : u4.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      rw [hu4_loc]; exact hu3_t
    -- 5. ite (t != 0) (start := start - 1; storeByte start t) skip ;; return ...
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_u2 hres ⊢
    have hc_t : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64)) =
        some (.val (.word (if tw ≠ 0#64 then 1#64 else 0#64))) := by
      simp [evalHOLExact, hu4_t, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc_t] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
    by_cases htz : tw = 0#64
    · -- t == 0: skip, then return
      have hcw0 : (if tw ≠ 0#64 then (1#64 : BitVec 64) else 0#64) = 0 := by simp [htz]
      rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt_u2 hres ⊢
      dsimp only at hnt_u2 hres ⊢
      rw [evaluateHOLFiniteState_return]
      split
      · exact heff_u4
      · split
        · exact heff_u4.locals_clock _ _
        · exact heff_u4.locals_clock _ _
    · -- t != 0: start := start - 1; storeByte start t; then return
      have hcw1 : ¬ ((if tw ≠ 0#64 then (1#64 : BitVec 64) else 0#64) = 0) := by
        have : (0 : BitVec 64) = 0#64 := rfl
        rw [this]; simp [htz]
      rw [if_neg hcw1, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt_u2 hres ⊢
      let st1 : BitVec 64 := startw - 1#64
      have h1_le_st : (1#64 : BitVec 64).toNat ≤ startw.toNat := by
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        have : hlw.toNat ≤ 9 := hhl_le9
        omega
      have hst1_nat : st1.toNat = startw.toNat - 1 := by
        change (startw - 1#64).toNat = _
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [BitVec.toNat_sub_of_le h1_le_st, h1]
      have hev_sub1 : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
          (.op .sub [.var .local (ofString "start"), .const 1#64]) = some (.val (.word st1)) := by
        simp [evalHOLExact, evalListHOLExact, hu4_st, wordOpHOL, wordOp, valueIsWord, valueWord, st1]
      rw [hev_sub1] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
      have hvv_st : isValidValueHOLFinite u4 .local (ofString "start") (.val (.word st1)) = true := by
        simp [isValidValueHOLFinite, lookupKvarHOLFinite, hu4_st, shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hvv_st] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
      set u5 := setKvarHOLFinite .local (ofString "start") (.val (.word st1)) u4
      have heff_u5 : HeapByteEff s0 u5 Rl gw := heff_u4.locals_clock u5.locals u5.clock
      have hu5_st : u5.locals.lookup (ofString "start") = some (.val (.word st1)) := by
        change (u4.locals.update (ofString "start", .val (.word st1))).lookup (ofString "start") = _
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨rsb, u6, hsb⟩ : ∃ rsb u6,
          evaluateHOLFiniteState u5
            (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))) = (rsb, u6) :=
        ⟨_, _, Prod.mk.eta.symm⟩
      rw [hsb] at hnt_u2 hres ⊢
      rcases (evaluate_storeByte_control_frame u5
        (.var .local (ofString "start")) (.var .local (ofString "t"))).1 with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn
        dsimp only at hnt_u2 hres ⊢
        have hbre_sb : M13.ByteRegionEffect u5 u6 Rl := by
          exact (M13.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
            simp only [evalHOLExact, hu5_st,
              Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
            subst hdst_ev
            refine ⟨(buf.toNat, bnd.toNat), hRl_mem, ?_, ?_⟩
            · have : hlw.toNat ≤ 9 := hhl_le9
              omega
            · have : 1 ≤ hlw.toNat := hhl_ge1
              omega)).1
        have heff_u6 : HeapByteEff s0 u6 Rl gw :=
          heff_u5.trans (HeapByteEff.of_m13_bre heff_u5.arena hbre_sb)
        rw [evaluateHOLFiniteState_return]
        split
        · exact heff_u6
        · split
          · exact heff_u6.locals_clock _ _
          · exact heff_u6.locals_clock _ _
      · rw [hsb] at hse; dsimp only at hse; subst hse
        dsimp only at hres
        exact False.elim (not_resumes_error hres)

private theorem eval_tx_encode_generic_mode0_resumes {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (tx0 : BitVec 64)
    (hAR_ent : ArenaReady ent)
    (htx_enc : TxValidEncodeAt ent tx0.toNat)
    (hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word tx0)))
    (hent_mode : ent.locals.lookup (ofString "mode") = some (.val (.word 0#64)))
    (hnt_body : (evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_tx_encode_generic)).1 ≠ some .timeOut)
    (hres_body : Resumes (evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_tx_encode_generic)).1) :
    HeapByteEff ent
      (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_encode_generic)).2
      [] ["heap_ptr"] := by
  obtain ⟨htx_v, _, _, _, hal_enc, hbh_enc, hau_enc⟩ := htx_enc
  obtain ⟨htx_wok, htx_ins, htx_t_le, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, hal_wok, hau_wok⟩ := htx_v
  have hgw : "heap_ptr" ∈ (["heap_ptr"] : List String) := by simp
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhe_val : heapEnd = 33806089704 := heapEnd_val
  have hhl_val : heapLimit = 2952790016 := heapLimit_val
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have h384_lt : 384 < 2 ^ 40 := by decide
  have hmw_lt64 : ∀ off, off % 8 = 0 → off + 8 ≤ 384 → memW ent (tx0.toNat + off) < 2 ^ 64 := by
    intro off hoff8 hoff_hi
    obtain ⟨⟨w, _, hm⟩, _, _⟩ := txEnc_wordsOK_wordAt_memW hAR_ent (M13.LocFrame.refl ent)
      htx_wok off hoff8 hoff_hi h384_lt
    unfold memW; rw [hm]; simp [w.isLt]
  have hb_gen : sourceFnBody Guest.Software.guestFn_tx_encode_generic =
      .decCall (ofString "bound") .one (ofString "tx_encode_bound") [.var .local (ofString "tx")]
        (.decCall (ofString "buf") .one (ofString "alloc") [.var .local (ofString "bound")]
          (.dec (ofString "body") .one (.op .add [.var .local (ofString "buf"), .const 10#64])
            (.dec (ofString "p") .one (.var .local (ofString "body"))
              (.dec (ofString "t") .one (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64]))
                (.dec (ofString "w") .one (.const 0#64)
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                      (.seq
                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                          [.var .local (ofString "p"),
                           .load .one (.op .add [.var .local (ofString "tx"), .const 8#64])])
                        (.assign .local (ofString "p")
                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                      .skip)
                    (.seq
                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                        [.var .local (ofString "p"),
                         .load (.comb [.one, .one, .one, .one])
                           (.op .add [.var .local (ofString "tx"), .const 16#64])])
                      (.seq
                        (.assign .local (ofString "p")
                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                        (.seq
                          (.ite (.cmp .notLower (.const 1#64) (.var .local (ofString "t")))
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                [.var .local (ofString "p"),
                                 .load (.comb [.one, .one, .one, .one])
                                   (.op .add [.var .local (ofString "tx"), .const 48#64])])
                              (.assign .local (ofString "p")
                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                            (.seq
                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                [.var .local (ofString "p"),
                                 .load (.comb [.one, .one, .one, .one])
                                   (.op .add [.var .local (ofString "tx"), .const 80#64])])
                              (.seq
                                (.assign .local (ofString "p")
                                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                (.seq
                                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                    [.var .local (ofString "p"),
                                     .load (.comb [.one, .one, .one, .one])
                                       (.op .add [.var .local (ofString "tx"), .const 112#64])])
                                  (.assign .local (ofString "p")
                                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))))))
                          (.seq
                            (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                              [.var .local (ofString "p"),
                               .load .one (.op .add [.var .local (ofString "tx"), .const 144#64])])
                            (.seq
                              (.assign .local (ofString "p")
                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                              (.seq
                                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
                                  [.var .local (ofString "p"),
                                   .load .one (.op .add [.var .local (ofString "tx"), .const 152#64])])
                                (.seq
                                  (.assign .local (ofString "p")
                                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                  (.seq
                                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                      [.var .local (ofString "p"),
                                       .load (.comb [.one, .one, .one, .one])
                                         (.op .add [.var .local (ofString "tx"), .const 160#64])])
                                    (.seq
                                      (.assign .local (ofString "p")
                                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                      (.seq
                                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                          [.var .local (ofString "p"),
                                           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
                                           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
                                        (.seq
                                          (.assign .local (ofString "p")
                                            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                          (.seq
                                            (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                                              (.seq
                                                (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_access_list")
                                                  [.var .local (ofString "p"),
                                                   .load .one (.op .add [.var .local (ofString "tx"), .const 208#64]),
                                                   .load .one (.op .add [.var .local (ofString "tx"), .const 216#64])])
                                                (.assign .local (ofString "p")
                                                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                                              .skip)
                                            (.seq
                                              (.ite (.cmp .equal (.var .local (ofString "t")) (.const 3#64))
                                                (.seq
                                                  (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                    [.var .local (ofString "p"),
                                                     .load (.comb [.one, .one, .one, .one])
                                                       (.op .add [.var .local (ofString "tx"), .const 224#64])])
                                                  (.seq
                                                    (.assign .local (ofString "p")
                                                      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                    (.seq
                                                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_blob_hashes")
                                                        [.var .local (ofString "p"),
                                                         .load .one (.op .add [.var .local (ofString "tx"), .const 256#64]),
                                                         .load .one (.op .add [.var .local (ofString "tx"), .const 264#64])])
                                                      (.assign .local (ofString "p")
                                                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))
                                                .skip)
                                              (.seq
                                                (.ite (.cmp .equal (.var .local (ofString "t")) (.const 4#64))
                                                  (.seq
                                                    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_authorizations")
                                                      [.var .local (ofString "p"),
                                                       .load .one (.op .add [.var .local (ofString "tx"), .const 272#64]),
                                                       .load .one (.op .add [.var .local (ofString "tx"), .const 280#64])])
                                                    (.assign .local (ofString "p")
                                                      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
                                                  .skip)
                                                (.seq
                                                  (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 0#64))
                                                    (.seq
                                                      (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                        [.var .local (ofString "p"),
                                                         .load (.comb [.one, .one, .one, .one])
                                                           (.op .add [.var .local (ofString "tx"), .const 288#64])])
                                                      (.seq
                                                        (.assign .local (ofString "p")
                                                          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                        (.seq
                                                          (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                            [.var .local (ofString "p"),
                                                             .load (.comb [.one, .one, .one, .one])
                                                               (.op .add [.var .local (ofString "tx"), .const 320#64])])
                                                          (.seq
                                                            (.assign .local (ofString "p")
                                                              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                            (.seq
                                                              (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
                                                                [.var .local (ofString "p"),
                                                                 .load (.comb [.one, .one, .one, .one])
                                                                   (.op .add [.var .local (ofString "tx"), .const 352#64])])
                                                              (.assign .local (ofString "p")
                                                                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))))
                                                    .skip)
                                                  (.seq
                                                    (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 2#64))
                                                      (.seq
                                                        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                          [.var .local (ofString "p"), .var .local (ofString "chain_id")])
                                                        (.seq
                                                          (.assign .local (ofString "p")
                                                            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                          (.seq
                                                            (.storeByte (.var .local (ofString "p")) (.const 128#64))
                                                            (.seq
                                                              (.storeByte (.op .add [.var .local (ofString "p"), .const 1#64]) (.const 128#64))
                                                              (.assign .local (ofString "p")
                                                                (.op .add [.var .local (ofString "p"), .const 2#64]))))))
                                                      .skip)
                                                    (.dec (ofString "payload_len") .one
                                                      (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
                                                      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
                                                        [.var .local (ofString "payload_len")]
                                                        (.dec (ofString "start") .one
                                                          (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
                                                          (.seq
                                                            (.call (some (none, none)) (ofString "rlp_encode_list_header")
                                                              [.var .local (ofString "start"), .var .local (ofString "payload_len")])
                                                            (.seq
                                                              (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                                                                (.seq
                                                                  (.assign .local (ofString "start")
                                                                    (.op .sub [.var .local (ofString "start"), .const 1#64]))
                                                                  (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                                                                .skip)
                                                              (.return (.rstruct [
                                                                .var .local (ofString "start"),
                                                                .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]]))))))))))))))))))))))))))))) := rfl
  rw [hb_gen] at hnt_body hres_body ⊢
  -- Step 1: bound = tx_encode_bound(tx)
  obtain ⟨m1, hbnd_nat, hbnd_lt40, hm1_mem, hm1_loc, heff_m1_empty, hnt1, hdc_bnd⟩ :=
    eval_decCall_tx_encode_bound ent "bound" (.var .local (ofString "tx")) tx0 _ [] []
      hAR_ent ⟨htx_wok, htx_ins, htx_t_le, hdata_lt, hnal_lt, hslots_lt, hnbh_lt, hnau_lt, hal_wok, hau_wok⟩
      (by simp [evalHOLExact, hent_tx]) hnt_body
  rw [hdc_bnd] at hres_body
  dsimp only at hres_body
  apply txEnc_heapByteEff_of_eq_resVar hdc_bnd
  let bnd := BitVec.ofNat 64 (txEncodeBoundPure ent tx0.toNat)
  have hm1_bnd : m1.locals.lookup (ofString "bound") = some (.val (.word bnd)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, bnd]
  have hm1_tx : m1.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_tx,
      show ofString "bound" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm1_mode : m1.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_mode,
      show ofString "bound" ≠ ofString "mode" from M13.mls_ne rfl]
  have hm1_hp_eq : globN m1 "heap_ptr" = globN ent "heap_ptr" := by
    unfold globN
    rw [← heff_m1_empty.globals (ofString "heap_ptr") (by simp)]
  -- Step 2: buf = alloc(bound)
  obtain ⟨buf, bnd', q, m2_raw, hev_bnd', hbuf_hp_m1, hbuf8, hq_nat, hbuf_bnd_le_q, hq_le_hl,
      hq8, hm2_hp, hm2_glob, hm2_mem, hm2_loc, heff_m1_m2_empty, hnt2_raw, hres2_raw, hdc_alloc⟩ :=
    eval_decCall_alloc_resumes m1 "buf" (.var .local (ofString "bound")) _ [] ["heap_ptr"]
      heff_m1_empty.arena.1.code heff_m1_empty.arena hgw hnt1 hres_body
  have hbnd'_eq : bnd' = bnd := by
    simp [evalHOLExact, hm1_bnd] at hev_bnd'
    exact hev_bnd'.symm
  subst hbnd'_eq
  rw [hdc_alloc] at hres_body
  dsimp only at hres_body
  apply txEnc_heapByteEff_of_eq_resVar hdc_alloc
  have hbuf_hp : buf.toNat = globN ent "heap_ptr" := hbuf_hp_m1.trans hm1_hp_eq
  have hbuf_bnd_le_hl : buf.toNat + bnd.toNat ≤ heapLimit := le_trans hbuf_bnd_le_q hq_le_hl
  let Rl : List Ivl := [(buf.toNat, bnd.toNat)]
  have hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN ent "heap_ptr" ≤ ivl.1 := by
    intro ivl hivl _
    simp [Rl] at hivl
    subst hivl
    rw [hbuf_hp]
  refine HeapByteEff.mono (R1 := Rl) (gw1 := ["heap_ptr"]) ?_ ?_ (fun _ h => h)
  swap
  · intro ivl hivl _
    simp [Rl] at hivl
    subst hivl
    right; right
    dsimp only
    rw [hbuf_hp]
    exact ⟨le_rfl, hbuf_hp ▸ hbuf_bnd_le_hl⟩
  have heff_ent_m2 : HeapByteEff ent m2_raw Rl ["heap_ptr"] :=
    (heff_m1_empty.mono (fun _ h => False.elim (List.not_mem_nil h))
      (fun _ h => False.elim (List.not_mem_nil h))).trans
      (heff_m1_m2_empty.mono (fun _ h => False.elim (List.not_mem_nil h)) (fun _ h => h))
  -- Unpack pure bound components
  let data_n := memW ent (tx0.toNat + 200)
  let al_sum := accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216))
  let au_sum := authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280))
  let bh_sum := 33 * memW ent (tx0.toNat + 264)
  have hbnd_decomp : bnd.toNat = 655 + data_n + al_sum + au_sum + bh_sum := by
    rw [hbnd_nat]; rfl
  have hm2_buf : m2_raw.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_tx : m2_raw.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_tx,
      show ofString "buf" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm2_mode : m2_raw.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mode,
      show ofString "buf" ≠ ofString "mode" from M13.mls_ne rfl]
  -- Step 3: dec "body" = buf + 10
  rw [evaluateHOLFiniteState_dec_total] at hnt2_raw hres2_raw
  dsimp only at hnt2_raw hres2_raw
  let bodyw : BitVec 64 := buf + 10#64
  have hbodyw_nat : bodyw.toNat = buf.toNat + 10 := by
    change (buf + 10#64).toNat = _
    rw [BitVec.toNat_add]
    have h10 : (10#64 : BitVec 64).toNat = 10 := rfl
    rw [h10]; exact Nat.mod_eq_of_lt (by omega)
  have hev_body : @evalHOLExact 64 F _ m2_raw.toExact (fun a => Classical.propDecidable (m2_raw.memaddrs a))
      (.op .add [.var .local (ofString "buf"), .const 10#64]) = some (.val (.word bodyw)) := by
    simp [evalHOLExact, evalListHOLExact, hm2_buf, wordOpHOL, wordOp, valueIsWord, valueWord, bodyw]
  have hsh_body : shapeEqHOL .one (shapeOfHOLExact (.val (.word bodyw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_body : ∀ cont_b : ProgHOL 64,
      evaluateHOLFiniteState m2_raw
        (.dec (ofString "body") .one (.op .add [.var .local (ofString "buf"), .const 10#64]) cont_b) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw) cont_b).2.locals.resVarEq
           (ofString "body", m2_raw.locals.lookup (ofString "body")) }) := by
    intro cont_b
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_body]; dsimp only; rw [if_pos hsh_body]
  apply txEnc_heapByteEff_of_eq_resVar (hdec_body _)
  rw [hev_body] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  rw [if_pos hsh_body] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  let m3 := setVarHOLFinite (ofString "body") (.val (.word bodyw)) m2_raw
  have heff_m3 : HeapByteEff ent m3 Rl ["heap_ptr"] := heff_ent_m2.locals_clock m3.locals m3.clock
  have hm3_body : m3.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm3_tx : m3.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_tx,
      show ofString "body" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm3_mode : m3.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm2_mode,
      show ofString "body" ≠ ofString "mode" from M13.mls_ne rfl]
  -- Step 4: dec "p" = body
  have hev_p0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
      (.var .local (ofString "body")) = some (.val (.word bodyw)) := by
    simp [evalHOLExact, hm3_body]
  have hdec_p : ∀ cont_p : ProgHOL 64,
      evaluateHOLFiniteState m3 (.dec (ofString "p") .one (.var .local (ofString "body")) cont_p) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3) cont_p).2.locals.resVarEq
           (ofString "p", m3.locals.lookup (ofString "p")) }) := by
    intro cont_p
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_p0]; dsimp only; rw [if_pos hsh_body]
  rw [hdec_p] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_heapByteEff_of_eq_resVar (hdec_p _)
  let m4 := setVarHOLFinite (ofString "p") (.val (.word bodyw)) m3
  have heff_m4 : HeapByteEff ent m4 Rl ["heap_ptr"] := heff_m3.locals_clock m4.locals m4.clock
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm4_body : m4.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_body,
      show ofString "p" ≠ ofString "body" from M13.mls_ne rfl]
  have hm4_tx : m4.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_tx,
      show ofString "p" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm4_mode : m4.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_mode,
      show ofString "p" ≠ ofString "mode" from M13.mls_ne rfl]
  -- Step 5: dec "t" = load .one (tx + 0)
  let tw := BitVec.ofNat 64 (memW ent tx0.toNat)
  have htw_nat : tw.toNat = memW ent tx0.toNat := by
    dsimp [tw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have htw_le4 : tw.toNat ≤ 4 := by rw [htw_nat]; exact htx_t_le
  have hev_t0 : @evalHOLExact 64 F _ m4.toExact (fun a => Classical.propDecidable (m4.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64])) = some (.val (.word tw)) := by
    have h0 := txEnc_eval_load_word_below_hp hAR_ent heff_m4 hRl_ge htx_ins htx_wok "tx" hm4_tx 0 (by decide) (by decide)
    simp only [Nat.add_zero] at h0
    exact h0
  have hsh_t : shapeEqHOL .one (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_t : ∀ cont_t : ProgHOL 64,
      evaluateHOLFiniteState m4
        (.dec (ofString "t") .one (.load .one (.op .add [.var .local (ofString "tx"), .const 0#64])) cont_t) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) m4) cont_t).2.locals.resVarEq
           (ofString "t", m4.locals.lookup (ofString "t")) }) := by
    intro cont_t
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_t0]; dsimp only; rw [if_pos hsh_t]
  rw [hdec_t] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_heapByteEff_of_eq_resVar (hdec_t _)
  let m5 := setVarHOLFinite (ofString "t") (.val (.word tw)) m4
  have heff_m5 : HeapByteEff ent m5 Rl ["heap_ptr"] := heff_m4.locals_clock m5.locals m5.clock
  have hm5_t : m5.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_p,
      show ofString "t" ≠ ofString "p" from M13.mls_ne rfl]
  have hm5_body : m5.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_body,
      show ofString "t" ≠ ofString "body" from M13.mls_ne rfl]
  have hm5_tx : m5.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_tx,
      show ofString "t" ≠ ofString "tx" from M13.mls_ne rfl]
  have hm5_mode : m5.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [m5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm4_mode,
      show ofString "t" ≠ ofString "mode" from M13.mls_ne rfl]
  -- Step 6: dec "w" = 0
  have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_w : ∀ cont_w : ProgHOL 64,
      evaluateHOLFiniteState m5 (.dec (ofString "w") .one (.const 0#64) cont_w) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5) cont_w).2.locals.resVarEq
           (ofString "w", m5.locals.lookup (ofString "w")) }) := by
    intro cont_w
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hc0 : @evalHOLExact 64 F _ m5.toExact (fun a => Classical.propDecidable (m5.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only; rw [if_pos hsh_0]
  rw [hdec_w] at hnt2_raw hres2_raw; dsimp only at hnt2_raw hres2_raw
  apply txEnc_heapByteEff_of_eq_resVar (hdec_w _)
  let s_cur0 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) m5
  have heff0 : HeapByteEff ent s_cur0 Rl ["heap_ptr"] := heff_m5.locals_clock s_cur0.locals s_cur0.clock
  have hs0_w : ∃ w_f : BitVec 64, s_cur0.locals.lookup (ofString "w") = some (.val (.word w_f)) :=
    ⟨0#64, by simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hs0_t : s_cur0.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_t,
      show ofString "w" ≠ ofString "t" from M13.mls_ne rfl]
  have hs0_p : s_cur0.locals.lookup (ofString "p") = some (.val (.word bodyw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_p,
      show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
  have hs0_body : s_cur0.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_body,
      show ofString "w" ≠ ofString "body" from M13.mls_ne rfl]
  have hs0_tx : s_cur0.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_tx,
      show ofString "w" ≠ ofString "tx" from M13.mls_ne rfl]
  have hs0_mode : s_cur0.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
    simp [s_cur0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm5_mode,
      show ofString "w" ≠ ofString "mode" from M13.mls_ne rfl]
  have hRl_mem : (buf.toNat, bnd.toNat) ∈ Rl := by simp [Rl]
  have hne_tw : ofString "t" ≠ ofString "w" := M13.mls_ne rfl
  have hne_tp : ofString "t" ≠ ofString "p" := M13.mls_ne rfl
  have hne_bw : ofString "body" ≠ ofString "w" := M13.mls_ne rfl
  have hne_bp : ofString "body" ≠ ofString "p" := M13.mls_ne rfl
  have hne_txw : ofString "tx" ≠ ofString "w" := M13.mls_ne rfl
  have hne_txp : ofString "tx" ≠ ofString "p" := M13.mls_ne rfl
  have hne_mw : ofString "mode" ≠ ofString "w" := M13.mls_ne rfl
  have hne_mp : ofString "mode" ≠ ofString "p" := M13.mls_ne rfl
  -- Field 1: ite (t != 0) (w := rlp_encode_word(p, load1(tx+8)); p := p+w) skip  (≤ 9)
  obtain ⟨p1, s1, hp1_lo, hp1_hi, hs1_frame, hs1_w, hs1_p, heff1, hnt1_s, hres1_s, heq1⟩ :=
    txEnc_ite_resumes (bound := 9) heff0
      (cw := if tw ≠ 0#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs0_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs0_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_word_step_resumes 8 hAR_ent heff0 hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs0_tx hs0_p hs0_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        exact ⟨bodyw + len, m, by omega, by omega, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_resumes heff0 hs0_p hs0_w hnt_br hres_br)
      hnt2_raw hres2_raw
  rw [heq1]
  have hs1_t : s1.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs1_frame _ hne_tw hne_tp).trans hs0_t
  have hs1_body : s1.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs1_frame _ hne_bw hne_bp).trans hs0_body
  have hs1_tx : s1.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs1_frame _ hne_txw hne_txp).trans hs0_tx
  have hs1_mode : s1.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs1_frame _ hne_mw hne_mp).trans hs0_mode
  -- Field 2: w := tx_put_u256(p, load4(tx+16)); p := p+w  (≤ 33; total ≤ 42)
  obtain ⟨len2, s2, hlen2_le, hp2_add, hs2_frame, hs2_w, hs2_p, heff2, hnt2_s, hres2_s, heq2⟩ :=
    txEnc_seq_call_u256_resumes 16 hAR_ent heff1 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs1_tx hs1_p hs1_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt1_s hres1_s
  rw [heq2]
  set p2 := p1 + len2
  have hp2_lo : bodyw.toNat ≤ p2.toNat := by omega
  have hp2_hi : p2.toNat ≤ bodyw.toNat + 42 := by omega
  have hs2_t : s2.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs2_frame _ hne_tw hne_tp).trans hs1_t
  have hs2_body : s2.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs2_frame _ hne_bw hne_bp).trans hs1_body
  have hs2_tx : s2.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs2_frame _ hne_txw hne_txp).trans hs1_tx
  have hs2_mode : s2.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs2_frame _ hne_mw hne_mp).trans hs1_mode
  -- Field 3: ite (cmp .notLower 1 t) (tx_put_u256(tx+48)) (tx_put_u256(tx+80); tx_put_u256(tx+112))  (≤ 66; total ≤ 108)
  obtain ⟨p3, s3, hp3_lo, hp3_hi_rel, hs3_frame, hs3_w, hs3_p, heff3, hnt3_s, hres3_s, heq3⟩ :=
    txEnc_ite_resumes (bound := 66) heff2
      (cw := if tw ≤ 1#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs2_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs2_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_u256_step_resumes 48 hAR_ent heff2 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs2_tx hs2_p hs2_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        exact ⟨p2 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => by
        -- else branch is (.seq (.call ... 80) (.seq (.assign p) (.seq (.call ... 112) (.assign p)))) ;; cont
        have heq_assoc : ∀ (a b c d : ProgHOL 64),
            evaluateHOLFiniteState s2 (.seq (.seq a (.seq b c)) d) =
            evaluateHOLFiniteState s2 (.seq a (.seq b (.seq c d))) := by
          intro a b c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s2 a with | mk ra sa =>
          cases ra with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa b with | mk rb sb =>
            cases rb <;> rfl
        rw [heq_assoc] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_resumes 80 hAR_ent heff2 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs2_tx hs2_p hs2_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs2_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_call_u256_step_resumes 112 hAR_ent heff_ma hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        exact ⟨p2 + lena + lenb, mb, by omega, by omega,
          fun k hkw hkp => (hfrb k hkw hkp).trans (hfra k hkw hkp),
          hwb, hpb, heff_mb, hnt_mb, hres_mb, heq_ma.trans heq_mb⟩)
      hnt2_s hres2_s
  rw [heq3]
  have hp3_ge_body : bodyw.toNat ≤ p3.toNat := le_trans hp2_lo hp3_lo
  have hp3_hi : p3.toNat ≤ bodyw.toNat + 108 := by omega
  have hs3_t : s3.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs3_frame _ hne_tw hne_tp).trans hs2_t
  have hs3_body : s3.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs3_frame _ hne_bw hne_bp).trans hs2_body
  have hs3_tx : s3.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs3_frame _ hne_txw hne_txp).trans hs2_tx
  have hs3_mode : s3.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs3_frame _ hne_mw hne_mp).trans hs2_mode
  -- Field 4: rlp_encode_word(p, load1(tx+144))  (≤ 9; total ≤ 117)
  obtain ⟨len4, s4, hlen4_le, hp4_add, hs4_frame, hs4_w, hs4_p, heff4, hnt4_s, hres4_s, heq4⟩ :=
    txEnc_seq_call_word_resumes 144 hAR_ent heff3 hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs3_tx hs3_p hs3_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt3_s hres3_s
  rw [heq4]
  set p4 := p3 + len4
  have hp4_lo : bodyw.toNat ≤ p4.toNat := by omega
  have hp4_hi : p4.toNat ≤ bodyw.toNat + 117 := by omega
  have hs4_t : s4.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs4_frame _ hne_tw hne_tp).trans hs3_t
  have hs4_body : s4.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs4_frame _ hne_bw hne_bp).trans hs3_body
  have hs4_tx : s4.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs4_frame _ hne_txw hne_txp).trans hs3_tx
  have hs4_mode : s4.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs4_frame _ hne_mw hne_mp).trans hs3_mode
  -- Field 5: tx_put_to(p, load1(tx+152))  (≤ 21; total ≤ 138)
  obtain ⟨len5, s5, hlen5_le, hp5_add, hs5_frame, hs5_w, hs5_p, heff5, hnt5_s, hres5_s, heq5⟩ :=
    txEnc_seq_call_to_resumes 152 hAR_ent heff4 hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs4_tx hs4_p hs4_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt4_s hres4_s
  rw [heq5]
  set p5 := p4 + len5
  have hp5_lo : bodyw.toNat ≤ p5.toNat := by omega
  have hp5_hi : p5.toNat ≤ bodyw.toNat + 138 := by omega
  have hs5_t : s5.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs5_frame _ hne_tw hne_tp).trans hs4_t
  have hs5_body : s5.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs5_frame _ hne_bw hne_bp).trans hs4_body
  have hs5_tx : s5.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs5_frame _ hne_txw hne_txp).trans hs4_tx
  have hs5_mode : s5.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs5_frame _ hne_mw hne_mp).trans hs4_mode
  -- Field 6: tx_put_u256(p, load4(tx+160))  (≤ 33; total ≤ 171)
  obtain ⟨len6, s6, hlen6_le, hp6_add, hs6_frame, hs6_w, hs6_p, heff6, hnt6_s, hres6_s, heq6⟩ :=
    txEnc_seq_call_u256_resumes 160 hAR_ent heff5 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
      hs5_tx hs5_p hs5_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
      hnt5_s hres5_s
  rw [heq6]
  set p6 := p5 + len6
  have hp6_lo : bodyw.toNat ≤ p6.toNat := by omega
  have hp6_hi : p6.toNat ≤ bodyw.toNat + 171 := by omega
  have hs6_t : s6.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs6_frame _ hne_tw hne_tp).trans hs5_t
  have hs6_body : s6.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs6_frame _ hne_bw hne_bp).trans hs5_body
  have hs6_tx : s6.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs6_frame _ hne_txw hne_txp).trans hs5_tx
  have hs6_mode : s6.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs6_frame _ hne_mw hne_mp).trans hs5_mode
  -- Field 7: rlp_encode_bytes(p, load1(tx+192), load1(tx+200))  (≤ 9 + data_n; total ≤ 180 + data_n)
  obtain ⟨len7, s7, hlen7_le, hp7_add, hs7_frame, hs7_w, hs7_p, heff7, hnt7_s, hres7_s, heq7⟩ :=
    txEnc_seq_call_bytes_resumes hAR_ent heff6 hRl_ge htx_ins htx_wok hdata_lt
      hs6_tx hs6_p hs6_w
      ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
        have : memW ent (tx0.toNat + 200) = data_n := rfl
        omega, hbuf_bnd_le_hl⟩
      hnt6_s hres6_s
  rw [heq7]
  set p7 := p6 + len7
  have hp7_lo : bodyw.toNat ≤ p7.toNat := by omega
  have hp7_hi : p7.toNat ≤ bodyw.toNat + 180 + data_n := by
    have : memW ent (tx0.toNat + 200) = data_n := rfl
    omega
  have hs7_t : s7.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs7_frame _ hne_tw hne_tp).trans hs6_t
  have hs7_body : s7.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs7_frame _ hne_bw hne_bp).trans hs6_body
  have hs7_tx : s7.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs7_frame _ hne_txw hne_txp).trans hs6_tx
  have hs7_mode : s7.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs7_frame _ hne_mw hne_mp).trans hs6_mode
  -- Field 8: ite (t != 0) (tx_put_access_list(p, load1(tx+208), load1(tx+216))) skip  (≤ 9 + al_sum; total ≤ 189 + data_n + al_sum)
  obtain ⟨p8, s8, hp8_lo, hp8_hi_rel, hs8_frame, hs8_w, hs8_p, heff8, hnt8_s, hres8_s, heq8⟩ :=
    txEnc_ite_resumes (bound := 9 + al_sum) heff7
      (cw := if tw ≠ 0#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs7_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs7_p
      (fun _ hnt_br hres_br => by
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_access_list_step_resumes hAR_ent heff7 hRl_ge htx_ins htx_wok
            hnal_lt hslots_lt (fun hpos => (hal_enc hpos).1) hal_wok
            (hmw_lt64 208 (by decide) (by decide))
            hs7_tx hs7_p hs7_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216)) = al_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have : accessListPayloadSumPure ent (memW ent (tx0.toNat + 208)) (memW ent (tx0.toNat + 216)) = al_sum := rfl
        exact ⟨p7 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_resumes heff7 hs7_p hs7_w hnt_br hres_br)
      hnt7_s hres7_s
  rw [heq8]
  have hp8_ge_body : bodyw.toNat ≤ p8.toNat := le_trans hp7_lo hp8_lo
  have hp8_hi : p8.toNat ≤ bodyw.toNat + 189 + data_n + al_sum := by omega
  have hs8_t : s8.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs8_frame _ hne_tw hne_tp).trans hs7_t
  have hs8_body : s8.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs8_frame _ hne_bw hne_bp).trans hs7_body
  have hs8_tx : s8.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs8_frame _ hne_txw hne_txp).trans hs7_tx
  have hs8_mode : s8.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs8_frame _ hne_mw hne_mp).trans hs7_mode
  -- Field 9: ite (t == 3) (tx_put_u256(tx+224); tx_put_blob_hashes(tx+256, tx+264)) skip  (≤ 42 + bh_sum; total ≤ 231 + data_n + al_sum + bh_sum)
  obtain ⟨p9, s9, hp9_lo, hp9_hi_rel, hs9_frame, hs9_w, hs9_p, heff9, hnt9_s, hres9_s, heq9⟩ :=
    txEnc_ite_resumes (bound := 42 + bh_sum) heff8
      (cw := if tw = 3#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs8_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs8_p
      (fun _ hnt_br hres_br => by
        have heq_assoc : ∀ (a b c d : ProgHOL 64),
            evaluateHOLFiniteState s8 (.seq (.seq a (.seq b c)) d) =
            evaluateHOLFiniteState s8 (.seq a (.seq b (.seq c d))) := by
          intro a b c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s8 a with | mk ra sa =>
          cases ra with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa b with | mk rb sb =>
            cases rb <;> rfl
        rw [heq_assoc] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_resumes 224 hAR_ent heff8 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs8_tx hs8_p hs8_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs8_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_call_blob_hashes_step_resumes hAR_ent heff_ma hRl_ge htx_ins htx_wok hnbh_lt
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : 33 * memW ent (tx0.toNat + 264) = bh_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        have : 33 * memW ent (tx0.toNat + 264) = bh_sum := rfl
        exact ⟨p8 + lena + lenb, mb, by omega, by omega,
          fun k hkw hkp => (hfrb k hkw hkp).trans (hfra k hkw hkp),
          hwb, hpb, heff_mb, hnt_mb, hres_mb, heq_ma.trans heq_mb⟩)
      (fun _ hnt_br hres_br => txEnc_skip_resumes heff8 hs8_p hs8_w hnt_br hres_br)
      hnt8_s hres8_s
  rw [heq9]
  have hp9_ge_body : bodyw.toNat ≤ p9.toNat := le_trans hp8_ge_body hp9_lo
  have hp9_hi : p9.toNat ≤ bodyw.toNat + 231 + data_n + al_sum + bh_sum := by omega
  have hs9_t : s9.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs9_frame _ hne_tw hne_tp).trans hs8_t
  have hs9_body : s9.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs9_frame _ hne_bw hne_bp).trans hs8_body
  have hs9_tx : s9.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs9_frame _ hne_txw hne_txp).trans hs8_tx
  have hs9_mode : s9.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs9_frame _ hne_mw hne_mp).trans hs8_mode
  -- Field 10: ite (t == 4) (tx_put_authorizations(tx+272, tx+280)) skip  (≤ 9 + au_sum; total ≤ 240 + data_n + al_sum + bh_sum + au_sum)
  obtain ⟨p10, s10, hp10_lo, hp10_hi_rel, hs10_frame, hs10_w, hs10_p, heff10, hnt10_s, hres10_s, heq10⟩ :=
    txEnc_ite_resumes (bound := 9 + au_sum) heff9
      (cw := if tw = 4#64 then 1#64 else 0#64)
      (by simp [evalHOLExact, hs9_t, Compiler.Encoders.Asm.wordCmpHOL])
      hs9_p
      (fun hc_t4 hnt_br hres_br => by
        have htw4 : tw = 4#64 := by
          by_contra hne4; simp [hne4] at hc_t4
        have hmem_t4 : memW ent tx0.toNat = 4 := by
          rw [← htw_nat, htw4]; rfl
        obtain ⟨len, m, hlen_le, hadd, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩ :=
          txEnc_call_authorizations_step_resumes hAR_ent heff9 hgw hRl_ge htx_ins htx_wok
            hnau_lt (fun hpos => (hau_enc ⟨hmem_t4, hpos⟩).1) hau_wok
            (hmw_lt64 272 (by decide) (by decide))
            hs9_tx hs9_p hs9_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by
              have : authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280)) = au_sum := rfl
              omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have : authListPayloadSumPure ent (memW ent (tx0.toNat + 272)) (memW ent (tx0.toNat + 280)) = au_sum := rfl
        exact ⟨p9 + len, m, by omega, by omega, hfr, hw, hp, heff_m, hnt_m, hres_m, heq_m⟩)
      (fun _ hnt_br hres_br => txEnc_skip_resumes heff9 hs9_p hs9_w hnt_br hres_br)
      hnt9_s hres9_s
  rw [heq10]
  have hp10_ge_body : bodyw.toNat ≤ p10.toNat := le_trans hp9_ge_body hp10_lo
  have hp10_hi : p10.toNat ≤ bodyw.toNat + 240 + data_n + al_sum + bh_sum + au_sum := by omega
  have hs10_t : s10.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs10_frame _ hne_tw hne_tp).trans hs9_t
  have hs10_body : s10.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs10_frame _ hne_bw hne_bp).trans hs9_body
  have hs10_tx : s10.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
    (hs10_frame _ hne_txw hne_txp).trans hs9_tx
  have hs10_mode : s10.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs10_frame _ hne_mw hne_mp).trans hs9_mode
  -- Field 11: ite (mode == 0) (tx_put_u256(tx+288); tx_put_u256(tx+320); tx_put_u256(tx+352)) skip  (≤ 99; total ≤ 339 + ...)
  obtain ⟨p11, s11, hp11_lo, hp11_hi_rel, hs11_frame, hs11_w, hs11_p, heff11, hnt11_s, hres11_s, heq11⟩ :=
    txEnc_ite_resumes (bound := 99) heff10
      (cw := 1#64)
      (by simp [evalHOLExact, hs10_mode, Compiler.Encoders.Asm.wordCmpHOL])
      hs10_p
      (fun _ hnt_br hres_br => by
        have heq_assoc3 : ∀ (a1 a2 b1 b2 c d : ProgHOL 64),
            evaluateHOLFiniteState s10 (.seq (.seq a1 (.seq a2 (.seq b1 (.seq b2 c)))) d) =
            evaluateHOLFiniteState s10 (.seq a1 (.seq a2 (.seq b1 (.seq b2 (.seq c d))))) := by
          intro a1 a2 b1 b2 c d
          simp only [evaluateHOLFiniteState_seq_line780]
          cases evaluateHOLFiniteState s10 a1 with | mk ra1 sa1 =>
          cases ra1 with
          | some _ => rfl
          | none =>
            dsimp only
            cases evaluateHOLFiniteState sa1 a2 with | mk ra2 sa2 =>
            cases ra2 with
            | some _ => rfl
            | none =>
              dsimp only
              cases evaluateHOLFiniteState sa2 b1 with | mk rb1 sb1 =>
              cases rb1 with
              | some _ => rfl
              | none =>
                dsimp only
                cases evaluateHOLFiniteState sb1 b2 with | mk rb2 sb2 =>
                cases rb2 <;> rfl
        rw [heq_assoc3] at hnt_br hres_br ⊢
        obtain ⟨lena, ma, hlena_le, hadda, hfra, hwa, hpa, heff_ma, hnt_ma, hres_ma, heq_ma⟩ :=
          txEnc_seq_call_u256_resumes 288 hAR_ent heff10 hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hs10_tx hs10_p hs10_w
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_br hres_br
        have hma_tx : ma.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfra _ hne_txw hne_txp).trans hs10_tx
        obtain ⟨lenb, mb, hlenb_le, haddb, hfrb, hwb, hpb, heff_mb, hnt_mb, hres_mb, heq_mb⟩ :=
          txEnc_seq_call_u256_resumes 320 hAR_ent heff_ma hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hma_tx hpa hwa
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_ma hres_ma
        have hmb_tx : mb.locals.lookup (ofString "tx") = some (.val (.word tx0)) :=
          (hfrb _ hne_txw hne_txp).trans hma_tx
        obtain ⟨lenc, mc, hlenc_le, haddc, hfrc, hwc, hpc, heff_mc, hnt_mc, hres_mc, heq_mc⟩ :=
          txEnc_call_u256_step_resumes 352 hAR_ent heff_mb hgw hRl_ge htx_ins htx_wok (by decide) (by decide)
            hmb_tx hpb hwb
            ⟨(buf.toNat, bnd.toNat), hRl_mem, by omega, by omega, hbuf_bnd_le_hl⟩
            hnt_mb hres_mb
        exact ⟨p10 + lena + lenb + lenc, mc, by omega, by omega,
          fun k hkw hkp => (hfrc k hkw hkp).trans ((hfrb k hkw hkp).trans (hfra k hkw hkp)),
          hwc, hpc, heff_mc, hnt_mc, hres_mc, heq_ma.trans (heq_mb.trans heq_mc)⟩)
      (fun hc0 => by cases hc0)
      hnt10_s hres10_s
  rw [heq11]
  have hp11_ge_body : bodyw.toNat ≤ p11.toNat := le_trans hp10_ge_body hp11_lo
  have hp11_le_end : p11.toNat ≤ buf.toNat + bnd.toNat := by omega
  have hs11_t : s11.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs11_frame _ hne_tw hne_tp).trans hs10_t
  have hs11_body : s11.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs11_frame _ hne_bw hne_bp).trans hs10_body
  have hs11_mode : s11.locals.lookup (ofString "mode") = some (.val (.word 0#64)) :=
    (hs11_frame _ hne_mw hne_mp).trans hs10_mode
  -- Field 12: ite (mode == 2) ... skip  (skipped since mode == 0)
  obtain ⟨p12, s12, hp12_lo, hp12_hi_rel, hs12_frame, _, hs12_p, heff12, hnt12_s, hres12_s, heq12⟩ :=
    txEnc_ite_resumes (bound := 0) heff11
      (cw := 0#64)
      (by simp [evalHOLExact, hs11_mode, Compiler.Encoders.Asm.wordCmpHOL])
      hs11_p
      (fun hc1 => False.elim (hc1 rfl))
      (fun _ hnt_br hres_br => txEnc_skip_resumes heff11 hs11_p hs11_w hnt_br hres_br)
      hnt11_s hres11_s
  rw [heq12]
  have hs12_t : s12.locals.lookup (ofString "t") = some (.val (.word tw)) :=
    (hs12_frame _ hne_tw hne_tp).trans hs11_t
  have hs12_body : s12.locals.lookup (ofString "body") = some (.val (.word bodyw)) :=
    (hs12_frame _ hne_bw hne_bp).trans hs11_body
  -- Trailer: payload_len, hl, start, rlp_encode_list_header, optional storeByte, return
  exact txEnc_trailer_resumes heff12 hRl_mem (by omega) hbuf_bnd_le_hl hbodyw_nat
    (le_trans hp11_ge_body hp12_lo) (by omega) hs12_p hs12_body hs12_t hnt12_s hres12_s

/-- Strengthened `WorldKeeps` for `encode_transaction`. -/
theorem «wk_encode_transaction_strong» :
    WorldKeeps (fun s => WorldOK s ∧ TxValidEncodeReady s) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction") := by
  refine ⟨_, _, _, lookup_encode_transaction_strong,
    fun {F} s hcode hW hparams hnt hres => ?_⟩
  have hWOK : WorldOK s := hW.1
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_transaction)).2
      ([] ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h) (by intro g hg; simp at hg; exact Or.inl hg)
      hWOK (fun _ _ _ _ _ => trivial)
  simp only [List.append_nil, List.map_nil]
  -- encode_transaction body is a tail call to tx_encode_generic with [tx, 0, 0]
  have hbody : sourceFnBody Guest.Software.guestFn_encode_transaction =
      .call none (ofString "tx_encode_generic")
        [.var .local (ofString "tx"), .const 0, .const 0] := rfl
  rw [hbody] at hnt hres ⊢
  -- Unfold the outer `call none "tx_encode_generic" [...]` via evaluateHOLFiniteState_call.
  rw [evaluateHOLFiniteState_call] at hnt hres ⊢
  -- Evaluate the argument list: [tx0, 0, 0]
  obtain ⟨vals, hl_tx⟩ := hparams
  obtain ⟨tx0, _, htx0⟩ := lookupCode_one_word_any lookup_encode_transaction_strong hl_tx
  have hAR : ArenaReady s := hW.1.1
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx"), .const 0, .const 0] =
      some [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, htx0]
  rw [ha] at hnt hres ⊢
  -- Look up tx_encode_generic
  have hlk : lookupCodeHOLFinite s.code.lookup (ofString "tx_encode_generic")
      [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
      some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
        ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
          (ofString "mode", ValueHOL.val (.word 0#64))).update
          (ofString "chain_id", ValueHOL.val (.word 0#64)),
        .comb [.one, .one]) := by
    have hraw : lookupCodeHOLExact s.code.lookup (ofString "tx_encode_generic")
        [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
        some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
          (fun key => if key = ofString "chain_id" then some (.val (.word 0#64))
            else if key = ofString "mode" then some (.val (.word 0#64))
            else if key = ofString "tx" then some (.val (.word tx0)) else none),
          .comb [.one, .one]) := by
      have hne1 : ofString "tx" ≠ ofString "mode" := by decide
      have hne2 : ofString "tx" ≠ ofString "chain_id" := by decide
      have hne3 : ofString "mode" ≠ ofString "chain_id" := by decide
      simp [lookupCodeHOLExact, hcode, lookup_tx_encode_generic, shapeOfHOLExact, shapeEqHOL,
        shapeEqHOL.shapeEqListHOL, hne1, hne2, hne3]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i missing; rw [hraw] at missing; cases missing
    · rename_i foundBody foundLocals foundShape found
      have equal := Option.some.inj (found.symm.trans hraw)
      obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_tx_encode_generic, locals, ShapeHOL.comb [.one, .one]))
      apply HolFiniteMapExact.ext; funext key
      by_cases hc : key = ofString "chain_id"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · by_cases hm : key = ofString "mode"
        · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            show ofString "chain_id" ≠ ofString "mode" from by decide, hc]
        · by_cases ht : key = ofString "tx"
          · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              show ofString "chain_id" ≠ ofString "tx" from by decide,
              show ofString "mode" ≠ ofString "tx" from by decide, hc, hm]
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              hc, hm, ht, Ne.symm hc, Ne.symm hm, Ne.symm ht]
  simp only [hlk] at hnt hres ⊢
  -- Check clock ≠ 0
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    -- Set up entry state
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
        (ofString "mode", ValueHOL.val (.word 0#64))).update (ofString "chain_id", ValueHOL.val (.word 0#64))
    let ent := callEntryStateHOLFinite s cmap
    have hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "tx" by decide,
        show ofString "mode" ≠ ofString "tx" by decide]
    have hent_mode : ent.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "mode" by decide]
    have hent_chain : ent.locals.lookup (ofString "chain_id") = some (.val (.word 0#64)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have heff_s_ent : HeapByteEff s ent [] ["heap_ptr"] :=
      (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock ent.locals ent.clock
    have hAR_ent : ArenaReady ent := heff_s_ent.arena
    -- The result of the outer call
    rcases hbody_ev : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_encode_generic) with ⟨rbody, sbody⟩
    change evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_tx_encode_generic) = (rbody, sbody) at hbody_ev
    simp only [hbody_ev] at hnt hres ⊢
    have hnt_body : rbody ≠ some .timeOut := by
      rintro rfl; exact hnt rfl
    have hres_body : Resumes rbody := by
      cases rbody with
      | none => exact False.elim (not_resumes_error hres)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_body
        | returned rv =>
          dsimp only at hres
          split at hres
          · exact Or.inl ⟨_, rfl⟩
          · exact False.elim (not_resumes_error hres)
        | exception eid ev =>
          exact hres
        | «break» | «continue» | error => exact False.elim (not_resumes_error hres)
        | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    -- The HeapByteEff proof for the body
    have htx_enc_ent : TxValidEncodeAt ent tx0.toNat := by
      have hloc_tx : locN s "tx" = tx0.toNat := by simp [locN, htx0]
      have hsrc : TxValidEncodeAt s tx0.toNat := hloc_tx ▸ hW.2
      exact hsrc
    have hbody_eff : HeapByteEff s sbody [] ["heap_ptr"] := by
      apply heff_s_ent.trans
      have hgen := eval_tx_encode_generic_mode0_resumes ent tx0 hAR_ent htx_enc_ent hent_tx hent_mode
        (by rw [hbody_ev]; exact hnt_body) (by rw [hbody_ev]; exact hres_body)
      rw [hbody_ev] at hgen
      exact hgen
    -- Now handle the return value case analysis
    cases rbody with
    | none =>
      exact hbody_eff
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_body
      | returned rv =>
        dsimp only
        split
        · exact hbody_eff.locals_clock _ _
        · exact hbody_eff
      | «break» | «continue» =>
        exact hbody_eff
      | exception eid ev =>
        exact hbody_eff.locals_clock _ _
      | error | finalFfi _ =>
        exact hbody_eff.locals_clock _ _

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
