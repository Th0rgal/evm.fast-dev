import InitECandidate.Solver.Wave8Stage.WordToStackSourceCost
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostControl
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- The control and extra-tick information read by a cost analysis. Register
names, expressions and cutsets are irrelevant to this syntactic projection.
Invalid marks allocation, installation and clock-resetting blocks. -/
inductive Control where
  | skip | tick | share | raise | result
  | ffi (name : Basis.Pure.MlString.MlString)
  | breakTo (label : Nat) | continueTo (label : Nat)
  | seq (first second : Control)
  | branch (first second : Control)
  | loop (body : Control)
  | call (ret : Option Control) (dest : Option Nat) (handler : Option Control)
  | invalid
  deriving Repr

def erase {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Control
  | .tick => .tick
  | .shareInst .. => .share
  | .raise _ => .raise
  | .return .. => .result
  | .ffi name .. => .ffi name
  | .break label => .breakTo label
  | .continue label => .continueTo label
  | .seq first second => .seq (erase first) (erase second)
  | .ite _ _ _ first second => .branch (erase first) (erase second)
  | .loop _ body _ => .loop (erase body)
  | .call ret dest _ handler => .call
      (match ret with | none => none | some (_,_,body,_,_) => some (erase body)) dest
      (match handler with | none => none | some (_,body,_,_) => some (erase body))
  | .alloc .. | .install .. | .mustTerminate .. => .invalid
  | _ => .skip
termination_by p => sizeOf p

/-- Accepted oracle colourings and allocator-produced colourings preserve the
complete cost control structure, for arbitrary register renamings. -/
theorem erase_applyColour {width : Nat} [NeZero width] (f : Nat → Nat)
    (p : WordLangProgHOL (BitVec width)) :
    erase (WordAlloc.applyColour f p) = erase p := by
  cases p with
  | seq first second =>
    simp only [WordAlloc.applyColour,erase,erase_applyColour f first,erase_applyColour f second]
  | ite cmp reg operand first second =>
    simp only [WordAlloc.applyColour,erase,erase_applyColour f first,erase_applyColour f second]
  | loop names body exits =>
    simp only [WordAlloc.applyColour,erase,erase_applyColour f body]
  | call ret dest args handler =>
    cases ret with
    | none =>
      cases handler with
      | none => simp only [WordAlloc.applyColour,erase]
      | some h =>
        rcases h with ⟨name,body,l1,l2⟩
        simp only [WordAlloc.applyColour,erase,
          erase_applyColour f body]
    | some ret =>
      rcases ret with ⟨names,live,body,l1,l2⟩
      cases handler with
      | none =>
        simp only [WordAlloc.applyColour,erase,
          erase_applyColour f body]
      | some h =>
        rcases h with ⟨name,hbody,h1,h2⟩
        simp only [WordAlloc.applyColour,erase,
          erase_applyColour f body,erase_applyColour f hbody]
  | _ => simp only [WordAlloc.applyColour,erase]
termination_by sizeOf p

theorem oracleColourOk_erase {width : Nat} [NeZero width]
    (k : Nat) (colour : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat))
    (accepted : WordAlloc.oracleColourOk k colour tree p forced = some q) :
    erase q = erase p := by
  unfold WordAlloc.oracleColourOk at accepted
  cases colour with
  | none => cases accepted
  | some colour =>
    dsimp only at accepted
    split at accepted
    · split at accepted
      · cases accepted
        exact erase_applyColour _ _
      · cases accepted
    · cases accepted

/-- Arbitrary allocation oracles cannot change this control projection: the
validated oracle route, computed allocation and failure fallback all agree. -/
theorem erase_wordAlloc {width : Nat} [NeZero width]
    (function : Nat) (ac : AsmConfigExact width) (algorithm registers : Nat)
    (p : WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat)) :
    erase (WordAlloc.wordAlloc function ac algorithm registers p colour) = erase p := by
  unfold WordAlloc.wordAlloc
  dsimp only
  generalize oracle : WordAlloc.oracleColourOk registers colour (WordAlloc.getClashTree p [])
    p (WordAlloc.getForced ac p []) = chosen
  cases chosen with
  | some q => exact oracleColourOk_erase registers colour _ p q _ oracle
  | none =>
    dsimp only
    split
    · exact erase_applyColour _ _
    · rfl

#print axioms erase_applyColour
#print axioms oracleColourOk_erase
#print axioms erase_wordAlloc
end InitECandidate.Solver.Wave8Stage.WordCostControl
