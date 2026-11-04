import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256Eval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

/-- Memory preservation covers every result, including errors and timeouts. -/
def MemoryPure (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
    (evaluateHOLFiniteState s program).2.memory = s.memory

theorem MemoryPure.skip : MemoryPure .skip := by
  intro F s hc
  rw [evaluateHOLFiniteState_skip]

theorem MemoryPure.ret (e : ExpHOL 64) : MemoryPure (.return e) := by
  intro F s hc
  rw [evaluateHOLFiniteState_return]
  repeat' first | split | rfl

theorem MemoryPure.assign (kind : VarKind) (name : MlS) (e : ExpHOL 64) :
    MemoryPure (.assign kind name e) := by
  intro F s hc
  rw [evaluateHOLFiniteState_assign]
  repeat' first | split | rfl
  all_goals cases kind <;> rfl

theorem MemoryPure.primitive (name : MlS) (op : PrimOp) (args : List (ExpHOL 64)) :
    MemoryPure (.primitive name op args) := by
  intro F s hc
  rw [evaluateHOLFiniteState_primitive]
  repeat' first | split | rfl

theorem MemoryPure.seq {p q : ProgHOL 64} (hp : MemoryPure p) (hq : MemoryPure q) :
    MemoryPure (.seq p q) := by
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

theorem MemoryPure.ite (e : ExpHOL 64) {p q : ProgHOL 64}
    (hp : MemoryPure p) (hq : MemoryPure q) : MemoryPure (.ite e p q) := by
  intro F s hc
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hq s hc
    · exact hp s hc
  · rfl

theorem MemoryPure.dec (name : MlS) (shape : ShapeHOL) (e : ExpHOL 64)
    {p : ProgHOL 64} (hp : MemoryPure p) : MemoryPure (.dec name shape e p) := by
  intro F s hc
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · exact hp (setVarHOLFinite name _ s) hc
    · rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
