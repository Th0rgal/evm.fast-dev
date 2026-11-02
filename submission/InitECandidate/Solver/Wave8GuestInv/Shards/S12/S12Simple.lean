/-
  s12 call-free transaction predicates.  These intentionally depend only on
  the light solver cone.  Each direct proof is generic in its invariant, so
  the full `GuestInv` definition is needed only by the final audit wrapper.
-/

import InitECandidate.Solver.Wave8GuestInv.Defs
import InitECandidate.Solver.Wave8GuestInv.Bounds
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.GuestTrapAndLookup
import Guest.SoftwareAst

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

/- Copied verbatim in substance from RlpWalk.lean on wave8/leaves-rlp-opus55. -/
theorem TerminatingProgBoundedOn.s12_weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

/- Copied verbatim in substance from RlpWalk.lean on wave8/leaves-rlp-opus55. -/
theorem s12_straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

syntax "s12_unfold " num ident : tactic
macro_rules
  | `(tactic| s12_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

theorem «fb_tx_has_access_list» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list» := by
  s12_unfold 315 Guest.Software.guestFn_tx_has_access_list
  apply TerminatingProgBoundedOn.s12_weaken'
  · exact s12_straightOn _ rfl
  · unfold K.«tx_has_access_list»
    omega

theorem «fb_tx_is_blob» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob» := by
  s12_unfold 865 Guest.Software.guestFn_tx_is_blob
  apply TerminatingProgBoundedOn.s12_weaken'
  · exact s12_straightOn _ rfl
  · unfold K.«tx_is_blob»
    omega

theorem «fb_tx_is_setcode» :
    TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode» := by
  s12_unfold 866 Guest.Software.guestFn_tx_is_setcode
  apply TerminatingProgBoundedOn.s12_weaken'
  · exact s12_straightOn _ rfl
  · unfold K.«tx_is_setcode»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
