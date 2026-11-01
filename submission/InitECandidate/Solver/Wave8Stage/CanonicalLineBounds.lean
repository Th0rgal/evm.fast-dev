import InitECandidate.Solver.Wave8Stage.NativeByteBounds
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace InitECandidate.Solver.Wave8Stage.CanonicalLineBounds
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target
  Compiler.Backend.LabToTarget Compiler.Backend.LabLang Compiler.Backend.LabSem
  Flapjack.RiscV.TargetProof

/-- Before padding, instruction bytes and allocated lengths are at most 24;
allocated lengths are even. Label lengths are tracked separately. -/
def LineBound (labels : Nat → Prop) : LabLineHOL 64 → Prop
  | .label _ _ n => labels n
  | .asm _ bytes n => bytes.length ≤ 24 ∧ n ≤ 24 ∧ n % 2 = 0
  | .labAsm _ _ bytes n => bytes.length ≤ 24 ∧ n ≤ 24 ∧ n % 2 = 0

def LinesBound (labels : Nat → Prop) (lines : List (LabLineHOL 64)) : Prop :=
  ∀ line ∈ lines, LineBound labels line

def ProgramBound (labels : Nat → Prop) (code : LabProgHOL 64) : Prop :=
  ∀ sec ∈ code, LinesBound labels sec.lines

theorem lines_cons (P : Nat → Prop) (line : LabLineHOL 64)
    (lines : List (LabLineHOL 64)) :
    LinesBound P (line :: lines) ↔ LineBound P line ∧ LinesBound P lines := by
  simp [LinesBound]

theorem program_cons (P : Nat → Prop) (sec : Section (LabLineHOL 64))
    (code : LabProgHOL 64) :
    ProgramBound P (sec :: code) ↔ LinesBound P sec.lines ∧ ProgramBound P code := by
  simp [ProgramBound]

theorem lines_reverse (P : Nat → Prop) (lines : List (LabLineHOL 64))
    (h : LinesBound P lines) : LinesBound P lines.reverse := by
  simpa only [LinesBound, List.mem_reverse] using h

private theorem encoding_even (i : HolAsm 64) : (riscvEnc i).length % 2 = 0 := by
  have := (riscv_encoding i).1
  omega

theorem encLine_bound (line : LabLineHOL 64) :
    LineBound (fun _ => True) (encLine riscvEnc 4 line) := by
  cases line with
  | label => trivial
  | asm a bytes n =>
    exact ⟨NativeByteBounds.encoding_length_le _, NativeByteBounds.encoding_length_le _,
      encoding_even _⟩
  | labAsm a w bytes n =>
    exact ⟨NativeByteBounds.encoding_length_le _, NativeByteBounds.encoding_length_le _,
      encoding_even _⟩

theorem encSecList_bound (code : LabProgHOL 64) :
    ProgramBound (fun _ => True) (encSecList riscvEnc code) := by
  intro sec member line lineMember
  have skip : (riscvEnc (.inst .skip)).length = 4 := rfl
  simp only [encSecList, skip, List.mem_map] at member
  obtain ⟨original, _, rfl⟩ := member
  simp only [encSec, List.mem_map] at lineMember
  obtain ⟨originalLine, _, rfl⟩ := lineMember
  exact encLine_bound originalLine

/-- Every re-encoding pass preserves the bound, including earlier longer
branch encodings retained by `max`. -/
theorem encLinesAgain_bound (P : Nat → Prop) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (lines acc : List (LabLineHOL 64)) (ok : Bool)
    (hlines : LinesBound P lines) (hacc : LinesBound P acc) :
    LinesBound P (encLinesAgain labs ffis pos riscvEnc lines acc ok).1 := by
  induction lines generalizing pos acc ok with
  | nil => exact lines_reverse P acc hacc
  | cons line lines ih =>
    obtain ⟨head, tail⟩ := (lines_cons P line lines).mp hlines
    cases line with
    | label a b n =>
      exact ih (pos + n) (.label a b n :: acc) ok tail ((lines_cons _ _ _).mpr ⟨head,hacc⟩)
    | asm a bytes n =>
      exact ih (pos + n) (.asm a bytes n :: acc) ok tail ((lines_cons _ _ _).mpr ⟨head,hacc⟩)
    | labAsm a w bytes n =>
      simp only [encLinesAgain]
      split
      · exact ih (pos + n) (.labAsm a w bytes n :: acc) ok tail
          ((lines_cons _ _ _).mpr ⟨head,hacc⟩)
      · have hb := NativeByteBounds.encoding_length_le (labInst (getJumpOffset a ffis labs pos) a)
        have he := encoding_even (labInst (getJumpOffset a ffis labs pos) a)
        obtain ⟨_, hn, hnEven⟩ := head
        have hm : max (riscvEnc (labInst (getJumpOffset a ffis labs pos) a)).length n % 2 = 0 := by
          rcases Nat.le_total (riscvEnc (labInst (getJumpOffset a ffis labs pos) a)).length n with h | h
          · rw [Nat.max_eq_right h]; exact hnEven
          · rw [Nat.max_eq_left h]; exact he
        apply ih _ _ _ tail
        apply (lines_cons _ _ _).mpr
        exact ⟨⟨hb, by omega, hm⟩, hacc⟩

theorem encSecsAgain_bound (P : Nat → Prop) (pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (code : LabProgHOL 64) (h : ProgramBound P code) :
    ProgramBound P (encSecsAgain pos labs ffis riscvEnc code).1 := by
  induction code generalizing pos with
  | nil => intro sec member; cases member
  | cons sec code ih =>
    obtain ⟨head, tail⟩ := (program_cons P sec code).mp h
    cases sec with
    | mk id lines =>
      simp only [encSecsAgain]
      apply (program_cons P _ _).mpr
      exact ⟨encLinesAgain_bound P labs ffis pos lines [] true head
        (fun _ member => by cases member), ih _ tail⟩

/-- An even starting position makes every adjusted label length zero. -/
theorem linesUpdLabLen_bound (pos : Nat) (lines acc : List (LabLineHOL 64))
    (hpos : pos % 2 = 0) (hlines : LinesBound (fun _ => True) lines)
    (hacc : LinesBound (fun n => n = 0) acc) :
    LinesBound (fun n => n = 0) (linesUpdLabLen pos lines acc).1 ∧
      (linesUpdLabLen pos lines acc).2 % 2 = 0 := by
  induction lines generalizing pos acc with
  | nil => exact ⟨lines_reverse _ _ hacc, hpos⟩
  | cons line lines ih =>
    obtain ⟨head, tail⟩ := (lines_cons _ _ _).mp hlines
    cases line with
    | label a b n =>
      simp only [linesUpdLabLen, if_pos hpos, Nat.add_zero]
      exact ih pos (.label a b 0 :: acc) hpos tail
        ((lines_cons _ _ _).mpr ⟨rfl,hacc⟩)
    | asm a bytes n =>
      exact ih (pos + n) (.asm a bytes n :: acc) (by have := head.2.2; omega) tail
        ((lines_cons _ _ _).mpr ⟨head,hacc⟩)
    | labAsm a w bytes n =>
      exact ih (pos + n) (.labAsm a w bytes n :: acc) (by have := head.2.2; omega) tail
        ((lines_cons _ _ _).mpr ⟨head,hacc⟩)

theorem updLabLen_bound (pos : Nat) (code : LabProgHOL 64) (hpos : pos % 2 = 0)
    (hcode : ProgramBound (fun _ => True) code) :
    ProgramBound (fun n => n = 0) (updLabLen pos code) := by
  induction code generalizing pos with
  | nil => intro sec member; cases member
  | cons sec code ih =>
    obtain ⟨head,tail⟩ := (program_cons _ _ _).mp hcode
    cases sec with
    | mk id lines =>
      have ready := linesUpdLabLen_bound pos lines [] hpos head (fun _ m => by cases m)
      simp only [updLabLen]
      exact (program_cons _ _ _).mpr ⟨ready.1, ih _ ready.2 tail⟩

theorem padBytes_bound (bytes nop : List (BitVec 8)) (n : Nat)
    (hb : bytes.length ≤ 24) (hn : n ≤ 24) : (padBytes bytes n nop).length ≤ 24 := by
  change (if n ≤ bytes.length then bytes else
    (bytes ++ (List.replicate n nop).flatten).take n).length ≤ 24
  split
  · exact hb
  · rw [List.length_take]
    exact Nat.le_trans (Nat.min_le_left _ _) hn

/-- Canonical even-position code has no nonzero label padding to attach to
preceding instructions. Ordinary line padding stays inside its allocated size. -/
theorem padSection_bound (nop : List (BitVec 8)) (lines acc : List (LabLineHOL 64))
    (hlines : LinesBound (fun n => n = 0) lines)
    (hacc : LinesBound (fun n => n = 0) acc) :
    LinesBound (fun n => n = 0) (padSection nop lines acc) := by
  induction lines generalizing acc with
  | nil => exact lines_reverse _ _ hacc
  | cons line lines ih =>
    obtain ⟨head,tail⟩ := (lines_cons _ _ _).mp hlines
    cases line with
    | label a b n =>
      change n = 0 at head
      subst n
      simp only [padSection, if_pos rfl]
      exact ih (.label a b 0 :: acc) tail ((lines_cons _ _ _).mpr ⟨rfl,hacc⟩)
    | asm a bytes n =>
      apply ih _ tail
      apply (lines_cons _ _ _).mpr
      exact ⟨⟨padBytes_bound bytes nop n head.1 head.2.1, head.2⟩,hacc⟩
    | labAsm a w bytes n =>
      apply ih _ tail
      apply (lines_cons _ _ _).mpr
      exact ⟨⟨padBytes_bound bytes nop n head.1 head.2.1, head.2⟩,hacc⟩

theorem padCode_bound (nop : List (BitVec 8)) (code : LabProgHOL 64)
    (hcode : ProgramBound (fun n => n = 0) code) :
    ProgramBound (fun n => n = 0) (padCode nop code) := by
  induction code with
  | nil => intro sec member; cases member
  | cons sec code ih =>
    obtain ⟨head,tail⟩ := (program_cons _ _ _).mp hcode
    cases sec with
    | mk id lines =>
      exact (program_cons _ _ _).mpr ⟨padSection_bound nop lines [] head
        (fun _ m => by cases m), ih tail⟩

/-- Every successful canonical label-removal loop has bounded lines. The
compiler's even starting position is retained explicitly. -/
theorem removeLabelsLoop_bound (clock pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (code result : LabProgHOL 64) (resultLabs : Spt (Spt Nat))
    (hpos : pos % 2 = 0) (hcode : ProgramBound (fun _ => True) code)
    (run : removeLabelsLoop clock riscvConfig pos labs ffis code = some (result,resultLabs)) :
    ProgramBound (fun n => n = 0) result := by
  induction clock using Nat.strongRecOn generalizing code result resultLabs with
  | ind clock ih =>
    have first := encSecsAgain_bound (fun _ => True) pos (computeLabelsAlt pos code labs)
      ffis code hcode
    rw [removeLabelsLoop] at run
    dsimp only at run
    split at run
    · have ready := updLabLen_bound pos _ hpos first
      have second := encSecsAgain_bound (fun n => n = 0) pos
        (computeLabelsAlt pos (updLabLen pos (encSecsAgain pos
          (computeLabelsAlt pos code labs) ffis riscvEnc code).1) labs)
        ffis _ ready
      have padded := padCode_bound (riscvEnc (.inst .skip)) _ second
      split at run
      · cases run
        exact padded
      · cases run
    · split at run
      · cases run
      · exact ih (clock - 1) (by omega) _ result resultLabs first run

/-- The actual compiler establishes the bound from arbitrary input Lab lines;
no pre-existing byte bound or padding bound is assumed of the source. -/
theorem removeLabels_bound (clock pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (code result : LabProgHOL 64) (resultLabs : Spt (Spt Nat))
    (hpos : pos % 2 = 0)
    (run : removeLabels clock riscvConfig pos labs ffis code = some (result,resultLabs)) :
    ProgramBound (fun n => n = 0) result :=
  removeLabelsLoop_bound clock pos labs ffis _ result resultLabs hpos
    (encSecList_bound code) run

theorem line_bytes_le (code : LabProgHOL 64) (hcode : ProgramBound (fun n => n = 0) code)
    (sec : Section (LabLineHOL 64)) (line : LabLineHOL 64)
    (member : sec ∈ code) (lineMember : line ∈ sec.lines) : (lineBytes line).length ≤ 24 := by
  have bound := hcode sec member line lineMember
  cases line with
  | label => exact Nat.zero_le _
  | asm => exact bound.1
  | labAsm => exact bound.1

#print axioms encSecList_bound
#print axioms encSecsAgain_bound
#print axioms updLabLen_bound
#print axioms padCode_bound
#print axioms removeLabels_bound
end InitECandidate.Solver.Wave8Stage.CanonicalLineBounds
