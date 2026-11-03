import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Common

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M15

def nodedbCallees (f : MlS) : Bool :=
  f == ofString "htab_get" || f == ofString "htab_find_leaf" || f == ofString "memeq"

theorem nodedbCallees_good :
    ∀ function, nodedbCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg nodedbCallees body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [nodedbCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with (rfl | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_get) rfl
    change originalRuntimeCode.lookup (ofString "htab_get") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl

theorem ro_mpt_fail : InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn (ofString "mpt_fail") :=
  readOnlyFn_of_guestAst 246 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mpt_fail rfl
    nodedbCallees nodedbCallees_good rfl

theorem ro__node_needs_rlp : InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn (ofString "_node_needs_rlp") :=
  readOnlyFn_of_guestAst 283 (by rw [guestAst_len]; decide) Guest.Software.guestFn__node_needs_rlp rfl
    nodedbCallees nodedbCallees_good rfl

theorem ro_nodedb_lookup : InitECandidate.Solver.Wave8Contracts.M15.ReadOnlyFn (ofString "nodedb_lookup") :=
  readOnlyFn_of_guestAst 254 (by rw [guestAst_len]; decide) Guest.Software.guestFn_nodedb_lookup rfl
    nodedbCallees nodedbCallees_good rfl

end InitECandidate.Solver.Wave8GuestInv.R11Adapters.ReadOnlyLeaves

