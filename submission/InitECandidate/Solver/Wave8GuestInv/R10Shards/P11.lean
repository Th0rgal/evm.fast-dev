import InitECandidate.Solver.Wave8GuestInv.Expressions

/-! Checked R10 primitive shard P11.  The hypotheses are precisely the direct
callees of each source declaration; no leaf statement is used as an oracle. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

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
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation) (B + Bc + 1) :=
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
      | (apply TerminatingProgBoundedOn.seq_guestInv; fb_auto; fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on; fb_auto; fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; callee_hyp)
      | (apply decCall_guestInv'; callee_hyp; fb_auto)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; callee_hyp))

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
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $(mkIdent (Name.mkSimple s!"kg{i}"))))

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

abbrev FB (name : String) (bound : Nat) :=
  TerminatingFunBoundedOn GuestInv (ofString name) bound

theorem fb_op_byte
    (stack_pop : FB "stack_pop" K.«stack_pop») (charge_gas : FB "charge_gas" K.«charge_gas»)
    (sat_word : FB "sat_word" K.«sat_word») (u256_byte : FB "u256_byte" K.«u256_byte»)
    (stack_push_word : FB "stack_push_word" K.«stack_push_word») (pc_add : FB "pc_add" K.«pc_add») :
    FB "op_byte" K.«op_byte» := by
  fb_prove 496 Guest.Software.guestFn_op_byte K.«op_byte»

theorem fb_op_caller
    (charge_gas : FB "charge_gas" K.«charge_gas») (address_to_u256 : FB "address_to_u256" K.«address_to_u256»)
    (stack_push : FB "stack_push" K.«stack_push») (pc_add : FB "pc_add" K.«pc_add») :
    FB "op_caller" K.«op_caller» := by
  fb_prove 534 Guest.Software.guestFn_op_caller K.«op_caller»

theorem fb_op_calldatasize
    (charge_gas : FB "charge_gas" K.«charge_gas») (stack_push_word : FB "stack_push_word" K.«stack_push_word»)
    (pc_add : FB "pc_add" K.«pc_add») : FB "op_calldatasize" K.«op_calldatasize» := by
  fb_prove 537 Guest.Software.guestFn_op_calldatasize K.«op_calldatasize»

theorem fb_op_calldataload
    (stack_pop : FB "stack_pop" K.«stack_pop») (charge_gas : FB "charge_gas" K.«charge_gas»)
    (sat_word : FB "sat_word" K.«sat_word») (heap_mark : FB "heap_mark" K.«heap_mark»)
    (alloc : FB "alloc" K.«alloc») (buffer_read : FB "buffer_read" K.«buffer_read»)
    (u256_from_be : FB "u256_from_be" K.«u256_from_be») (heap_release : FB "heap_release" K.«heap_release»)
    (stack_push : FB "stack_push" K.«stack_push») (pc_add : FB "pc_add" K.«pc_add») :
    FB "op_calldataload" K.«op_calldataload» := by
  fb_prove 536 Guest.Software.guestFn_op_calldataload K.«op_calldataload»

theorem fb_copy_from_buffer
    (stack_pop : FB "stack_pop" K.«stack_pop») (sat_word : FB "sat_word" K.«sat_word»)
    (words_of : FB "words_of" K.«words_of») (extend_memory_cost1 : FB "extend_memory_cost1" K.«extend_memory_cost1»)
    (add_sat : FB "add_sat" K.«add_sat») (charge_gas : FB "charge_gas" K.«charge_gas»)
    (extend_memory : FB "extend_memory" K.«extend_memory») (buffer_read : FB "buffer_read" K.«buffer_read»)
    (pc_add : FB "pc_add" K.«pc_add») : FB "copy_from_buffer" K.«copy_from_buffer» := by
  fb_prove 538 Guest.Software.guestFn_copy_from_buffer K.«copy_from_buffer»

theorem fb_op_calldatacopy (copy_from_buffer : FB "copy_from_buffer" K.«copy_from_buffer») :
    FB "op_calldatacopy" K.«op_calldatacopy» := by
  fb_prove 539 Guest.Software.guestFn_op_calldatacopy K.«op_calldatacopy»

theorem fb_op_call
    (stack_pop : FB "stack_pop" K.«stack_pop») (to_address_masked : FB "to_address_masked" K.«to_address_masked»)
    (extend_memory_cost2 : FB "extend_memory_cost2" K.«extend_memory_cost2») (is_warm_address : FB "is_warm_address" K.«is_warm_address»)
    (u256_is_zero : FB "u256_is_zero" K.«u256_is_zero») (add_sat : FB "add_sat" K.«add_sat»)
    (charge_gas : FB "charge_gas" K.«charge_gas») (warm_address : FB "warm_address" K.«warm_address»)
    (calculate_delegation_cost : FB "calculate_delegation_cost" K.«calculate_delegation_cost») (ext_code_of : FB "ext_code_of" K.«ext_code_of»)
    (sat_word : FB "sat_word" K.«sat_word») (calculate_message_call_gas : FB "calculate_message_call_gas" K.«calculate_message_call_gas»)
    (extend_memory : FB "extend_memory" K.«extend_memory») (get_account : FB "get_account" K.«get_account»)
    (u256_lt : FB "u256_lt" K.«u256_lt») (stack_push : FB "stack_push" K.«stack_push»)
    (set_retdata : FB "set_retdata" K.«set_retdata») (credit_state_gas_refund : FB "credit_state_gas_refund" K.«credit_state_gas_refund»)
    (is_account_alive : FB "is_account_alive" K.«is_account_alive») (charge_state_gas : FB "charge_state_gas" K.«charge_state_gas»)
    (generic_call : FB "generic_call" K.«generic_call») (pc_add : FB "pc_add" K.«pc_add») :
    FB "op_call" K.«op_call» := by
  fb_prove 603 Guest.Software.guestFn_op_call K.«op_call»

theorem fb_op_callcode
    (stack_pop : FB "stack_pop" K.«stack_pop») (to_address_masked : FB "to_address_masked" K.«to_address_masked»)
    (extend_memory_cost2 : FB "extend_memory_cost2" K.«extend_memory_cost2») (is_warm_address : FB "is_warm_address" K.«is_warm_address»)
    (u256_is_zero : FB "u256_is_zero" K.«u256_is_zero») (add_sat : FB "add_sat" K.«add_sat»)
    (charge_gas : FB "charge_gas" K.«charge_gas») (warm_address : FB "warm_address" K.«warm_address»)
    (calculate_delegation_cost : FB "calculate_delegation_cost" K.«calculate_delegation_cost») (ext_code_of : FB "ext_code_of" K.«ext_code_of»)
    (sat_word : FB "sat_word" K.«sat_word») (calculate_message_call_gas : FB "calculate_message_call_gas" K.«calculate_message_call_gas»)
    (extend_memory : FB "extend_memory" K.«extend_memory») (get_account : FB "get_account" K.«get_account»)
    (u256_lt : FB "u256_lt" K.«u256_lt») (stack_push : FB "stack_push" K.«stack_push»)
    (set_retdata : FB "set_retdata" K.«set_retdata») (generic_call : FB "generic_call" K.«generic_call»)
    (pc_add : FB "pc_add" K.«pc_add») : FB "op_callcode" K.«op_callcode» := by
  fb_prove 604 Guest.Software.guestFn_op_callcode K.«op_callcode»

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P11
