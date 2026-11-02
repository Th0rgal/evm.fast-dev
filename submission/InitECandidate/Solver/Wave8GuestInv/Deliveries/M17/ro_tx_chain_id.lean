import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_tx_chain_id` (`tx_chain_id`, `Guest/SoftwareAst.lean:12365`, `guestAst[338]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

private def goodTxChainId (f : MlS) : Bool :=
  f == ofString "u256_fits_word" || f == ofString "u256_sub" || f == ofString "u256_shr"

private theorem lookup_u256_fits_word :
    originalRuntimeCode.lookup (ofString "u256_fits_word") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_fits_word).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 41 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_fits_word) rfl

private theorem lookup_u256_sub :
    originalRuntimeCode.lookup (ofString "u256_sub") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_sub).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 57 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_sub) rfl

private theorem lookup_u256_shr :
    originalRuntimeCode.lookup (ofString "u256_shr") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_shr).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 82 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_shr) rfl

private theorem goodTxChainId_bodies :
    ∀ fname, goodTxChainId fname = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      roProg goodTxChainId body = true := by
  intro fname hgood values body callee rs hfound
  unfold goodTxChainId at hgood
  simp only [Bool.or_eq_true, beq_iff_eq] at hgood
  rcases hgood with (rfl | rfl) | rfl
  · rw [body_eq_of_lookupCode lookup_u256_fits_word hfound]
    decide
  · rw [body_eq_of_lookupCode lookup_u256_sub hfound]
    decide
  · rw [body_eq_of_lookupCode lookup_u256_shr hfound]
    decide

theorem ro_tx_chain_id : ReadOnlyFn (ofString "tx_chain_id") :=
  readOnlyFn_of_guestAst_roProg 338 Guest.Software.guestFn_tx_chain_id
    goodTxChainId goodTxChainId_bodies
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
