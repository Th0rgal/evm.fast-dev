import InitECandidate.Solver.Wave8GuestInv.Shards.S13.SpecLight

/-! Reused from campaign/leaves/htab/Base.lean at 3ea193df0cf872ba6789df0100aa8734e0f75704 (wave8/leaves-htab-opus55). Only the straight-line composition infrastructure is included. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Leaves.S13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]


/-! ## Unconditional bounds -/

theorem onOf {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64} {K : Nat}
    (h : TerminatingProgBounded p K) : TerminatingProgBoundedOn P p K :=
  fun s hcode _ => h s hcode

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (p : ProgHOL 64)
    (hs : extStraightLine p = true) : TerminatingProgBoundedOn P p 0 :=
  onOf (TerminatingProgBounded.straight p hs)

theorem progOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64} {K : Nat}
    (h : ProgBounded p K) : TerminatingProgBoundedOn P p K :=
  onOf (terminatingProgBounded_of_progBounded h)

theorem funOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {f : MlS} {K K' : Nat}
    (h : FunBounded f K) (hle : K ≤ K') : TerminatingFunBoundedOn P f K' :=
  (TerminatingFunBoundedOn.of_unconditional (terminatingFunBounded_of_funBounded h)).weaken hle

theorem TerminatingProgBoundedOn.weakenK {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P p K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P p K' :=
  fun s hcode hP => (h s hcode hP).weaken hle

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
/-- Close `TerminatingFunBoundedOn P (ofString "f") ?B` by the local hypothesis about the
syntactically same function name (comparing `MlS` literals by unification is very slow). -/
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

/-- Walk a body under `GuestInv`: straight-line subprograms cost `0`, `dec`/`seq`/`ite` are
decomposed, calls use a callee bound from the context. Loops are left as goals. -/
macro "htab_walk" : tactic => `(tactic| repeat (first
  | exact straightOn _ rfl
  | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
  | apply TerminatingProgBoundedOn.seq_guestInv
  | apply TerminatingProgBoundedOn.ite_on
  | (apply TerminatingProgBoundedOn.decCall_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.call_guestInv; case hf => callee_hyp)
  | (apply TerminatingProgBoundedOn.tailCall_guestInv; case hf => callee_hyp)))

/- Close `bound ≤ K.«f»` after unfolding `K.«f»`: split every `max`, then `omega`. -/
/- Symbolic arithmetic reused from rlp/RlpCore.lean at 998817a20efa0796e7eb06992d98f332943646bc. -/
open Lean Elab Tactic Meta in
/-- Generalize every remaining `K.«g»` constant of the goal into an opaque variable. -/
elab "s13_generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8Leaves.S13.Spec.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

macro "htab_bound" k:ident : tactic => `(tactic|
  (unfold $k:ident
   s13_generalize_K
   (try simp only [Nat.max_def])
   (try split_ifs) <;> omega))

/-- Reduce the structural translation of a guest function body. -/
macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

end InitECandidate.Solver.Wave8Leaves.S13
