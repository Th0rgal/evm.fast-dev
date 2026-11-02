import InitECandidate.Solver.Wave8GuestInv.Shards.S00.RlpWord

/-! Read-only support for trie_walk. The closure proof follows hdrGood_ro in
wave8/leaves-rlp-opus55, RlpStack.lean at 998817a20efa0796e7eb06992d98f332943646bc.
These helpers inspect actual callee bodies; no spec leaf proof is used. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00.Trie
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound

def good (f : MlS) : Bool := f == ofString "mpt_fail" || f == ofString "memeq"

theorem good_ro : ∀ function, good function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values =
      some (body, callee, rs) → roProg good body = true := by
  intro function hf values body callee rs hl
  simp only [good, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl
    subst hb
    rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memeq) rfl) hl
    subst hb
    rfl

theorem trie_readonly {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    Frame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_trie_walk)).2 :=
  evaluate_ro good good_ro _ rfl s hc

end InitECandidate.Solver.Wave8Leaves.S00.Trie
