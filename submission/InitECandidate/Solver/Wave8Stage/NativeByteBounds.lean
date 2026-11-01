import InitECandidate.Solver.Wave8Stage.RiscvLengthBound
import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.Compiler.Backend.LabToTarget.NopEncoding

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.NativeByteBounds
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target
  Compiler.Backend.LabToTarget Flapjack.RiscV.TargetProof

/-- Every canonical native encoding is at most 24 bytes. -/
theorem encoding_length_le (i : HolAsm 64) : (riscvEnc i).length ≤ 24 := by
  rw [riscvEnc_length_eq]
  have := RiscvLengthBound.ast_length_le_six i
  omega

/-- Encoded instruction length plus NOP count exactly counts the native
instructions in a padded line. No bound is assumed on arbitrary valid padding. -/
theorem padded_length (i : HolAsm 64) (count : Nat) :
    (riscvEnc i ++ (List.replicate count (riscvEnc (.inst .skip))).flatten).length =
      4 * ((riscvAst i).length + count) := by
  have skip : (riscvEnc (.inst .skip)).length = 4 := rfl
  have padding : (List.replicate count (riscvEnc (.inst .skip))).flatten.length =
      count * 4 := by
    induction count with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.length_append, skip, ih]
      omega
  rw [List.length_append, riscvEnc_length_eq, padding]
  omega

/-- A bound on actual padded bytes bounds the native simulation budget. -/
theorem padded_cost_le (i : HolAsm 64) (bytes : List (BitVec 8))
    (count steps bound : Nat)
    (encoding : bytes = riscvEnc i ++
      (List.replicate count (riscvEnc (.inst .skip))).flatten)
    (size : bytes.length ≤ 4 * bound)
    (simulation : steps ≤ (riscvAst i).length) : steps + count ≤ bound := by
  rw [encoding, padded_length] at size
  omega

#print axioms encoding_length_le
#print axioms padded_cost_le
end InitECandidate.Solver.Wave8Stage.NativeByteBounds
