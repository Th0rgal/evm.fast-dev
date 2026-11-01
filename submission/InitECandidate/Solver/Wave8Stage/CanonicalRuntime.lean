import InitECandidate.Solver.Wave8Stage.QuantitativeCommon
import InitECandidate.Solver.Wave8Stage.LengthBoundedEncoder
import InitECandidate.Solver.Wave8Stage.CanonicalLineBounds
import Flapjack.Compiler.Backend.LabToTarget.Navigation

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CanonicalRuntime
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target
  Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabLang
  Compiler.Backend.LabSem Compiler.Backend.LabProps CanonicalLineBounds
  Flapjack.RiscV.TargetProof

/-- Zero-length labels and bounded instruction bytes bound every successive
physical PC difference, including the last instruction and exhausted code. -/
theorem positions (code : LabProgHOL 64) (h : ProgramBound (fun n => n = 0) code) :
    ∀ pos, posVal 0 pos code = pos ∧
      ∀ pc, posVal (pc + 1) pos code ≤ posVal pc pos code + 24 := by
  induction code with
  | nil => intro pos; exact ⟨by simp [posVal], fun _ => by simp [posVal]⟩
  | cons sec code ih =>
    obtain ⟨head, tail⟩ := (program_cons _ _ _).mp h
    clear h
    rcases sec with ⟨id, lines⟩
    induction lines with
    | nil => simpa only [posVal] using ih tail
    | cons line lines ihl =>
      obtain ⟨hb, ht⟩ := (lines_cons _ _ _).mp head
      have ready := ihl ht
      intro pos
      cases line with
      | label a b n =>
        change n = 0 at hb
        subst n
        simpa only [posVal, isLabelHOL, ↓reduceIte, lineLength, Nat.add_zero] using ready pos
      | asm a bytes n =>
        refine ⟨by simp [posVal, isLabelHOL], ?_⟩
        intro pc
        cases pc with
        | zero =>
          simpa only [posVal, isLabelHOL, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_add, Nat.add_sub_cancel, Nat.one_ne_zero, lineLength, (ready (pos + bytes.length)).1] using
            Nat.add_le_add_left hb.1 pos
        | succ pc =>
          simpa only [posVal, isLabelHOL, Bool.false_eq_true, ↓reduceIte,
            Nat.add_one_ne_zero, Nat.add_one_sub_one, lineLength] using
            (ready (pos + bytes.length)).2 pc
      | labAsm a w bytes n =>
        refine ⟨by simp [posVal, isLabelHOL], ?_⟩
        intro pc
        cases pc with
        | zero =>
          simpa only [posVal, isLabelHOL, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_add, Nat.add_sub_cancel, Nat.one_ne_zero, lineLength, (ready (pos + bytes.length)).1] using
            Nat.add_le_add_left hb.1 pos
        | succ pc =>
          simpa only [posVal, isLabelHOL, Bool.false_eq_true, ↓reduceIte,
            Nat.add_one_ne_zero, Nat.add_one_sub_one, lineLength] using
            (ready (pos + bytes.length)).2 pc

/-- Fetched-install exclusion is invariant under instruction similarity. -/
theorem noInstall_similar {width : Nat} [NeZero width] (source code : LabProgHOL width)
    (h : codeSimilar source code) (safe : LabProps.noInstall code) :
    LabProps.noInstall source := by
  intro pc w bytes n hf
  have hs := codeSimilar_asmFetchAux pc source code h
  rw [hf] at hs
  cases hc : asmFetchAux pc code with
  | none => rw [hc] at hs; cases hs
  | some line =>
    rw [hc] at hs
    cases hs with
    | some similar =>
      cases line with
      | label => exact similar.elim
      | asm => exact similar.elim
      | labAsm a w' bytes' n' =>
        change AsmWithLab.install = a at similar
        subst a
        exact safe pc w' bytes' n' hc

/-- Canonical compiler output satisfies the quantitative evaluator contract.
All numerical premises follow from checked encoder proofs and actual bytes. -/
theorem codeBound (code : LabProgHOL 64)
    (bounded : ProgramBound (fun n => n = 0) code) (safe : LabProps.noInstall code) :
    Quantitative.CodeBound riscvTarget code := by
  refine ⟨⟨fun i => (riscvAst i).length - 1, ?_, ?_⟩,
    fun source similar => noInstall_similar source code similar safe⟩
  · intro s1 i s2 ms h
    obtain ⟨n, hn, hw⟩ := LengthBoundedEncoder.bounded_by_length s1 i s2 ms h
    exact ⟨n, by change n ≤ (riscvAst i).length - 1; omega, hw⟩
  · intro pc i bytes count hpos heq
    have hp := (positions code bounded 0).2 pc
    have hbytes : bytes.length ≤ 24 := by omega
    have hlen := NativeByteBounds.padded_length i count
    change bytes = riscvEnc i ++ (List.replicate count (riscvEnc (.inst .skip))).flatten at heq
    rw [heq, hlen] at hbytes
    have positive : 0 < (riscvAst i).length := by
      have henc := (riscv_encoding i).2
      have : 0 < (riscvEnc i).length := List.length_pos_iff.mpr henc
      rw [riscvEnc_length_eq] at this
      omega
    change (riscvAst i).length - 1 + 1 + count * (0 + 1) ≤ 6
    omega

#print axioms positions
#print axioms noInstall_similar
#print axioms codeBound
end InitECandidate.Solver.Wave8Stage.CanonicalRuntime
