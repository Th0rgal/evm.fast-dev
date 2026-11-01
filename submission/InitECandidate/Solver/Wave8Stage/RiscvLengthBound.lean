import Flapjack.Compiler.Encoders.RiscV.Target

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.RiscvLengthBound

open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

macro "close_length" : tactic => `(tactic| first
  | exact (show 1 ≤ 6 from by decide)
  | exact (show 2 ≤ 6 from by decide)
  | exact (show 3 ≤ 6 from by decide)
  | exact (show 5 ≤ 6 from by decide)
  | exact (show 6 ≤ 6 from by decide))

theorem const32_length (r : BitVec 5) (i : BitVec 32) :
    (riscvConst32 r i).length = 2 := by
  unfold riscvConst32
  split <;> rfl

/-- The longest native lowering has six instructions, including arbitrary
64-bit constants and the carry/overflow operations. This counts emitted
instructions; the evaluator simulation bound is a separate obligation. -/
theorem ast_length_le_six (i : HolAsm 64) : (riscvAst i).length ≤ 6 := by
  cases i with
  | inst instruction =>
    cases instruction with
    | skip => close_length
    | const r c =>
      simp only [riscvAst]
      split
      · close_length
      · split
        · rw [const32_length]; close_length
        · split <;> simp only [List.length_append, const32_length,
            List.length_cons, List.length_nil] <;> close_length
    | arith arithmetic =>
      cases arithmetic with
      | binop op r s operand =>
        cases operand <;> cases op <;> close_length
      | shift op r s operand =>
        cases operand <;> cases op <;> close_length
      | div => close_length
      | longMul => close_length
      | longDiv => close_length
      | addCarry => close_length
      | addOverflow => close_length
      | subOverflow => close_length
    | mem op r address =>
      cases address
      cases op <;> close_length
  | jump offset =>
    simp only [riscvAst]
    split <;> close_length
  | jumpCmp comparison r operand offset =>
    cases operand <;> cases comparison <;> simp only [riscvAst] <;>
      split <;> close_length
  | call offset =>
    simp only [riscvAst]
    split <;> close_length
  | jumpReg => close_length
  | loc => close_length

#print axioms ast_length_le_six

end InitECandidate.Solver.Wave8Stage.RiscvLengthBound
