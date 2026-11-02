import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterUpOn
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterSignedUpOn

/-! Counter proof automation reusing the arithmetic shard's proved CounterAdd rules. -/
namespace InitECandidate.Solver.Wave8Leaves.S00
open InitECandidate.Solver.Wave8Leaves.S00Spec
open InitECandidate.Solver.Wave8Leaves.S00Spec.Arith

syntax "s00_count" : tactic
macro_rules
  | `(tactic| s00_count) => `(tactic| first
      | exact CounterAdd.assign _ _
      | (apply CounterAdd.seq
         · decide
         · decide
         · s00_count)
      | (apply CounterAdd.dec
         · decide
         · s00_count)
      | (apply CounterAdd.decCall
         · decide
         · s00_count))

syntax "s00_counter_auto" : tactic
macro_rules
  | `(tactic| s00_counter_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · s00_counter_auto
         · s00_counter_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · s00_counter_auto
         · s00_counter_auto)
      | (apply dec_guestInv; s00_counter_auto)
      | (apply call_guestInv'; assumption)
      | (apply decCall_guestInv'
         · assumption
         · s00_counter_auto)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; assumption)
      | (apply while_up_signed_one_on
         · s00_counter_auto
         · s00_count)
      | (apply while_up_unsigned_one_on
         · s00_counter_auto
         · s00_count))

open Lean Elab Tactic Meta Term in
elab "fb_counter_auto" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let loopRule := fun (p hb : Expr) => do
    let pa := p.getAppArgs
    let cond ← whnf pa[2]!
    let ca := cond.getAppArgs
    unless cond.isAppOf ``Flapjack.Pancake.PanLang.ExpHOL.cmp do
      throwError "Expected counter comparison"
    let lhs ← whnf ca[3]!
    let counter := lhs.getAppArgs.back!
    let one ← elabTerm (← `((1 : BitVec 64))) none
    let countType ← mkAppM ``CounterAdd #[counter, one, pa[3]!]
    let hcount ← withTransparency .default <|
      elabTermEnsuringType (← `(by s00_count)) countType
    let cmp ← whnf ca[2]!
    let rule := if cmp.isConstOf ``Flapjack.Cmp.less then
      ``while_up_signed_one_on else ``while_up_unsigned_one_on
    mkAppM rule #[counter, ca[4]!, hb, hcount]
  let proof ← withTransparency .reducible <|
    buildFbProof target.getAppArgs[1]! loopRule
  unless ← isDefEq (← inferType proof) target do
    throwError "Constructed counter bound does not match goal"
  (← getMainGoal).assign proof
  replaceMainGoal []

end InitECandidate.Solver.Wave8Leaves.S00
