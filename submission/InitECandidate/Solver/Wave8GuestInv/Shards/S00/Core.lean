import InitECandidate.Solver.Wave8GuestInv.Shards.S00.LightSpec

/-! Helpers adapted from wave8/leaves-rlp-opus55, 998817a20efa0796e7eb06992d98f332943646bc, RlpWalk/RlpCore.
Calls use explicit hypotheses only; no known_fb lookup of spec leaves. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8Leaves.S00Spec InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound


theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

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

/-- Wrapper around the revision-7 proved handler combinator. -/
theorem callHandle_guestInv' {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_guestInv hf destination exn var hh arguments

/- Construct structural proofs bottom-up, preserving program syntax and opaque
callee bounds instead of repeatedly unfolding the semantic predicate in `apply`. -/
open Lean Meta Elab Term in
partial def buildFbProof (program : Expr)
    (loopRule : Expr → Expr → TermElabM Expr := fun p _ => throwError "No loop rule for {p}") : TermElabM Expr := do
  let p ← whnf program
  let a := p.getAppArgs
  let ctor := p.getAppFn.constName?.getD Name.anonymous
  let callee := fun (name : Expr) => do
    for h in (← getLCtx) do
      unless h.isImplementationDetail do
        let t ← instantiateMVars h.type
        if t.isAppOf ``TerminatingFunBoundedOn then
          if ← isDefEq t.getAppArgs[1]! name then
            return h.toExpr
    throwError "No explicit callee hypothesis for {name}"
  if ctor == ``ProgHOL.seq then
    mkAppM ``TerminatingProgBoundedOn.seq_guestInv #[← buildFbProof a[2]! loopRule, ← buildFbProof a[3]! loopRule]
  else if ctor == ``ProgHOL.ite then
    let hy ← buildFbProof a[3]! loopRule
    let hn ← buildFbProof a[4]! loopRule
    mkAppOptM ``TerminatingProgBoundedOn.ite_on
      #[none, some a[2]!, none, none, none, none, some hy, some hn]
  else if ctor == ``ProgHOL.dec then
    mkAppM ``dec_guestInv #[a[2]!, a[3]!, a[4]!, ← buildFbProof a[5]! loopRule]
  else if ctor == ``ProgHOL.decCall then
    mkAppM ``TerminatingProgBoundedOn.decCall_guestInv
      #[← callee a[4]!, a[2]!, a[3]!, a[5]!, ← buildFbProof a[6]! loopRule]
  else if ctor == ``ProgHOL.call then
    let hf ← callee a[3]!
    let info ← whnf a[2]!
    if info.isAppOf ``Option.none then
      mkAppM ``TerminatingProgBoundedOn.tailCall_guestInv #[hf, a[4]!]
    else
      let pair ← whnf info.getAppArgs.back!
      let destination := pair.getAppArgs[2]!
      let handler ← whnf pair.getAppArgs.back!
      if handler.isAppOf ``Option.none then
        mkAppM ``TerminatingProgBoundedOn.call_guestInv #[hf, destination, a[4]!]
      else
        let triple ← whnf handler.getAppArgs.back!
        let rest ← whnf triple.getAppArgs.back!
        let hh ← buildFbProof rest.getAppArgs.back! loopRule
        mkAppM ``TerminatingProgBoundedOn.callHandle_guestInv
          #[hf, destination, triple.getAppArgs[2]!, rest.getAppArgs[2]!, hh, a[4]!]
  else if ctor == ``ProgHOL.while then
    loopRule p (← buildFbProof a[3]! loopRule)
  else
    mkAppM ``straightOn #[p, ← mkEqRefl (mkConst ``Bool.true)]

open Lean Elab Tactic Meta in
elab "fb_auto" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``TerminatingProgBoundedOn do
    throwError "fb_auto expects TerminatingProgBoundedOn"
  let proof ← withTransparency .reducible <| buildFbProof target.getAppArgs[1]!
  unless ← isDefEq (← inferType proof) target do
    throwError "Constructed structural bound does not match the goal"
  (← getMainGoal).assign proof
  replaceMainGoal []

/-- Look up `fname` at index `idx` of `guestAst` and unfold its HOL body. -/
syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

open Lean Elab Tactic Meta in
/-- Generalize every remaining `K.«g»` constant of the goal into an opaque variable. -/
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8Leaves.S00Spec.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

/-- Close `bound ≤ K.f` (callee bounds stay atoms; walks use `domainBytes + 2 ≤ 2^64 + 1`). -/
syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       omega))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

end InitECandidate.Solver.Wave8Leaves.S00
