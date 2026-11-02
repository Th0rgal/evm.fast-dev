import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Core

/-! Proof of `ro_stor_lookup` (`stor_lookup`, `Guest/SoftwareAst.lean:13233`, `guestAst[377]`). -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

private def goodStorLookup (f : MlS) : Bool :=
  f == ofString "htab_get" || f == ofString "htab_find_leaf" || f == ofString "memeq"

private theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_get).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

private theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_find_leaf).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

private theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memeq).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

private theorem goodStorLookup_bodies :
    ∀ fname, goodStorLookup fname = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      roProg goodStorLookup body = true := by
  intro fname hgood values body callee rs hfound
  unfold goodStorLookup at hgood
  simp only [Bool.or_eq_true, beq_iff_eq] at hgood
  rcases hgood with (rfl | rfl) | rfl
  · rw [body_eq_of_lookupCode lookup_htab_get hfound]
    decide
  · rw [body_eq_of_lookupCode lookup_htab_find_leaf hfound]
    decide
  · rw [body_eq_of_lookupCode lookup_memeq hfound]
    decide

theorem ro_stor_lookup : ReadOnlyFn (ofString "stor_lookup") :=
  readOnlyFn_of_guestAst_roProg 377 Guest.Software.guestFn_stor_lookup
    goodStorLookup goodStorLookup_bodies
    (by rw [guestAst_len]; decide) rfl (by decide)

end InitECandidate.Solver.Wave8GuestInv.M17
