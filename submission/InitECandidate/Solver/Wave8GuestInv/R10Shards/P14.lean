import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.GuestTrapAndLookup
import InitECandidate.Solver.GuestUniformClockBound

/-! Checked R10 primitive leaves for shard P14. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

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
      | (apply call_guestInv'; first | callee_hyp | assumption)
      | (apply decCall_guestInv'
         · first | callee_hyp | assumption
         · fb_auto)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; first | callee_hyp | assumption))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

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
       first | omega | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega)))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

theorem fb_op_mstore
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_with_memory : TerminatingFunBoundedOn GuestInv (ofString "charge_with_memory") K.«charge_with_memory»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_u256_to_be32 : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore» := by
  fb_prove 508 Guest.Software.guestFn_op_mstore K.«op_mstore»

theorem fb_op_mstore8
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_with_memory : TerminatingFunBoundedOn GuestInv (ofString "charge_with_memory") K.«charge_with_memory»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8» := by
  fb_prove 509 Guest.Software.guestFn_op_mstore8 K.«op_mstore8»

theorem fb_op_mul
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_mul : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul» := by
  fb_prove 476 Guest.Software.guestFn_op_mul K.«op_mul»

theorem fb_op_mulmod
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_mulmod : TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.«u256_mulmod»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod» := by
  fb_prove 483 Guest.Software.guestFn_op_mulmod K.«op_mulmod»

theorem fb_op_not
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not» := by
  fb_prove 495 Guest.Software.guestFn_op_not K.«op_not»

theorem fb_op_number
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (h_stack_push_word : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number» := by
  fb_prove 557 Guest.Software.guestFn_op_number K.«op_number»

theorem fb_op_or
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or» := by
  fb_prove 493 Guest.Software.guestFn_op_or K.«op_or»

#print axioms fb_op_mstore
#print axioms fb_op_mstore8
#print axioms fb_op_mul
#print axioms fb_op_mulmod
#print axioms fb_op_not
#print axioms fb_op_number
#print axioms fb_op_or

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P14
