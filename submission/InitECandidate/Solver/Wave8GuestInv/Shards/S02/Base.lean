import InitECandidate.Solver.Wave8GuestInv.LeafStatements

/-! Shared local infrastructure for shard s02.

Provenance: adapted from `wave8/leaves-htab-opus55:campaign/leaves/htab/Base.lean`.
Only the guarded function wrapper and the structural walker are retained here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.S02

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (p : ProgHOL 64)
    (hs : extStraightLine p = true) : TerminatingProgBoundedOn P p 0 :=
  fun s hcode _ => TerminatingProgBounded.straight p hs s hcode

theorem onFun_of_guestAst {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  ⟨_, _, _, InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem i hi (extractFn d) hd,
    hprog⟩

theorem onFun_le {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (K : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d)) {K' : Nat}
    (hprog : TerminatingProgBoundedOn P
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) K')
    (hle : K' ≤ K) :
    TerminatingFunBoundedOn P (ofString (extractFn d).name) K :=
  (onFun_of_guestAst i hi d K' hd hprog).weaken hle

open Lean Elab Tactic Meta in
elab "callee_hyp" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``TerminatingFunBoundedOn 3 do throwError "callee_hyp: bad goal"
  let fn := g.getAppArgs[1]!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``TerminatingFunBoundedOn 3 && t.getAppArgs[1]! == fn then
      if ← isDefEq t g then
        (← getMainGoal).assign d.toExpr
        replaceMainGoal []
        return
  throwError "callee_hyp: no hypothesis for {fn}"

macro "s02_walk" : tactic => `(tactic| repeat (first
  | exact straightOn _ rfl
  | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
  | apply TerminatingProgBoundedOn.seq_guestInv
  | apply TerminatingProgBoundedOn.ite_on
  | (apply TerminatingProgBoundedOn.decCall_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.call_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.tailCall_guestInv; case hf => callee_hyp)))

macro "s02_bound" k:ident : tactic => `(tactic| (simp only [$k:ident, Nat.max_def]; (try split_ifs) <;> omega))

macro "s02_unfold" d:ident : tactic => `(tactic| dsimp only [extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

end InitECandidate.Solver.Wave8GuestInv.S02
