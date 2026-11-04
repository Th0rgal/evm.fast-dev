import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256Eval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

/-- All state fields except locals, memory and clock. This retains globals,
FFI, top address and every evaluator metadata field. -/
def arithContext {F : Type} (s : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  {s with locals := HolFiniteMapExact.empty, memory := fun _ => .word 0, clock := 0}

/-- Context preservation covers all outcomes, including errors and timeouts. -/
def ArithContextPure (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
    arithContext (evaluateHOLFiniteState s program).2 = arithContext s

theorem ArithContextPure.skip : ArithContextPure .skip := by
  intro F s hc
  rw [evaluateHOLFiniteState_skip]

theorem ArithContextPure.ret (e : ExpHOL 64) : ArithContextPure (.return e) := by
  intro F s hc
  rw [evaluateHOLFiniteState_return]
  repeat' first | split | rfl

theorem ArithContextPure.assign (name : MlS) (e : ExpHOL 64) :
    ArithContextPure (.assign .local name e) := by
  intro F s hc
  rw [evaluateHOLFiniteState_assign]
  repeat' first | split | rfl

theorem ArithContextPure.primitive (name : MlS) (op : PrimOp) (args : List (ExpHOL 64)) :
    ArithContextPure (.primitive name op args) := by
  intro F s hc
  rw [evaluateHOLFiniteState_primitive]
  repeat' first | split | rfl

theorem ArithContextPure.seq {p q : ProgHOL 64} (hp : ArithContextPure p) (hq : ArithContextPure q) :
    ArithContextPure (.seq p q) := by
  intro F s hc
  have hm := hp s hc
  have hcode := (evaluateHOLFiniteState_metadata s p).1
  rw [evaluateHOLFiniteState_seq_line780]
  cases hrun : evaluateHOLFiniteState s p with
  | mk res mid =>
    rw [hrun] at hm hcode
    cases res with
    | none => exact (hq mid (hcode.trans hc)).trans hm
    | some res => exact hm

theorem ArithContextPure.ite (e : ExpHOL 64) {p q : ProgHOL 64}
    (hp : ArithContextPure p) (hq : ArithContextPure q) : ArithContextPure (.ite e p q) := by
  intro F s hc
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hq s hc
    · exact hp s hc
  · rfl

theorem ArithContextPure.dec (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64)
    {p : ProgHOL 64} (hp : ArithContextPure p) : ArithContextPure (.dec name shape e p) := by
  intro F s hc
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · exact hp (setVarHOLFinite name _ s) hc
    · rfl

theorem ArithContextPure.store (destination value : ExpHOL 64) :
    ArithContextPure (.store destination value) := by
  intro F s hc
  rw [evaluateHOLFiniteState_store]
  repeat' first | split | rfl

theorem ArithContextPure.storeByte (destination value : ExpHOL 64) :
    ArithContextPure (.storeByte destination value) := by
  intro F s hc
  rw [evaluateHOLFiniteState_storeByte]
  repeat' first | split | rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
