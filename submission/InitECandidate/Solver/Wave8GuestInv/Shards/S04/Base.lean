-- Structural proof helpers adapted from RlpWalk.lean and RlpCore.lean on
-- wave8/leaves-rlp-opus55; exact source commit is recorded in those local copies.
-- Light-cone structural rules; no import of the full GuestInv specification.
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Light

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04.Base

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8Leaves.S04.Light InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn GuestInv prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

theorem dec_guestInv (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {K : Nat} (hbody : TerminatingProgBoundedOn GuestInv body K) :
    TerminatingProgBoundedOn GuestInv (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape init hbody

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

-- Callee bounds must come from explicit hypotheses.
open Lean Elab Tactic Meta in
elab "s04_known_fb" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  unless args.size == 3 do throwError "expected a function-bound goal"
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let ty ← instantiateMVars decl.type
      if ty.getAppFn == target.getAppFn && ty.getAppArgs.size == 3 then
        if ← withReducible <| isDefEq args[1]! ty.getAppArgs[1]! then
          evalTactic (← `(tactic| exact $(mkIdent decl.userName)))
          return
  throwError "no explicit callee hypothesis for {args[1]!}"

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

/-- Structural bound: straight-line code, `seq`, `ite`, `dec`, and calls. -/
syntax "s04_fb_auto" : tactic
macro_rules
  | `(tactic| s04_fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · s04_fb_auto
         · s04_fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · s04_fb_auto
         · s04_fb_auto)
      | (apply dec_guestInv; s04_fb_auto)
      | (apply call_guestInv'; s04_known_fb)
      | (apply decCall_guestInv'
         · s04_known_fb
         · s04_fb_auto)
)

/-- Look up `fname` at index `idx` of `guestAst` and unfold its HOL body. -/
syntax "s04_fb_unfold " num ident : tactic
macro_rules
  | `(tactic| s04_fb_unfold $idx $fn) => `(tactic|
      (have hLookup := originalRuntimeCode_lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl
       dsimp only [extractFn, $fn:ident] at hLookup
       refine ⟨_, _, _, hLookup, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

open Lean Elab Tactic Meta in
/-- Generalize every remaining `K.«g»` constant of the goal into an opaque variable. -/
elab "s04_generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8Leaves.S04.Light.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

/-- Close `bound ≤ K.f` (callee bounds stay atoms; walks use `domainBytes + 2 ≤ 2^64 + 1`). -/
syntax "s04_fb_arith " ident : tactic
macro_rules
  | `(tactic| s04_fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       s04_generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       omega))

syntax "s04_fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| s04_fb_prove $idx $fn $k) => `(tactic|
      (s04_fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · s04_fb_auto
       · s04_fb_arith $k))



end InitECandidate.Solver.Wave8Leaves.S04.Base
