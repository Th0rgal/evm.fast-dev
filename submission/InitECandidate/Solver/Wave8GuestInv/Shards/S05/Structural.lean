import InitECandidate.Solver.Wave8GuestInv.LeafStatements

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Campaign.Leaves.S05.Structural

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem weaken' {prog : ProgHOL 64} {K K' : Nat}
    (h : TerminatingProgBoundedOn GuestInv prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn GuestInv prog K' :=
  fun s hc hi => (h s hc hi).weaken hle

theorem straight (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn GuestInv prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

theorem dec {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {K : Nat} (h : TerminatingProgBoundedOn GuestInv body K) :
    TerminatingProgBoundedOn GuestInv (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape init h

theorem call {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (h : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv h destination arguments

theorem callHandle {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (h : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_guestInv h destination exn var hh arguments

theorem decCall {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (h : TerminatingFunBoundedOn GuestInv fname B)
    (hc : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation) (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv h name shape arguments hc

open Lean Elab Tactic Meta in
elab "s05_known" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let ty ← instantiateMVars decl.type
      if ty.getAppFn == target.getAppFn && ty.getAppArgs.size == args.size then
        if ← withReducible <| isDefEq args[1]! ty.getAppArgs[1]! then
          evalTactic (← `(tactic| exact $(mkIdent decl.userName)))
          return
  throwError "no explicit callee bound for {args[1]!}"

syntax "s05_auto" : tactic
macro_rules
  | `(tactic| s05_auto) => `(tactic| first
      | exact straight _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv <;> s05_auto)
      | (apply TerminatingProgBoundedOn.ite_on <;> s05_auto)
      | (apply dec; s05_auto)
      | (apply callHandle <;> first | s05_known | s05_auto)
      | (apply call; s05_known)
      | (apply decCall <;> first | s05_known | s05_auto))

end Campaign.Leaves.S05.Structural
