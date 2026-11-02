import InitECandidate.Solver.Wave8GuestInv.Bounds
import InitECandidate.Solver.GuestTrapAndLookup

/-! Shared routine-leaf tactics for s10.

Provenance: adapted from `campaign/leaves/rlp/RlpCore.lean` on
`wave8/leaves-rlp-opus55`.  The only change is that `callee_fb` resolves an
explicit theorem hypothesis, rather than a theorem from the RLP namespace.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

/-! These two wrappers are copied in shape from the RLP worker's `RlpCore.lean`.
They keep the structural tactic's direct-callee contract explicit. -/
theorem call_guestInv' {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv hf destination arguments

theorem decCall_guestInv' {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv hf name shape arguments hcont

open Lean Elab Tactic Meta in
/-- Discharge a direct function-call goal with its matching explicit hypothesis. -/
elab "callee_fb" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some e := t.find? (fun e => e.isAppOfArity ``Flapjack.Basis.Pure.MlString.ofString 1 &&
      e.appArg!.isStringLit) | throwError "callee_fb: no function name in goal"
  let .lit (.strVal name) := e.appArg! | throwError "callee_fb: not a literal"
  let lctx ← getLCtx
  for decl in lctx do
    let lt ← instantiateMVars decl.type
    if lt.find? (fun x => x.isAppOfArity ``Flapjack.Basis.Pure.MlString.ofString 1 &&
        match x.appArg! with | .lit (.strVal other) => other == name | _ => false) |>.isSome then
      evalTactic (← `(tactic| exact $(mkIdent decl.userName):ident))
      return
  throwError "callee_fb: no explicit hypothesis for {name}"

syntax "fb_auto" : tactic
macro_rules
  | `(tactic| fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto
         · fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto
         · fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; callee_fb)
      | (apply decCall_guestInv'
         · callee_fb
         · fb_auto))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) (by with_unfolding_all rfl), ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

open Lean Elab Tactic Meta in
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8GuestInv.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (unfold $k:ident
       generalize_K
       try simp only [nat_max_eq]
       omega))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      set_option maxRecDepth 1000000 in
        (fb_unfold $idx $fn
         apply TerminatingProgBoundedOn.weaken'
         · fb_auto
         · fb_arith $k))

end InitECandidate.Solver.Wave8Leaves.S10
