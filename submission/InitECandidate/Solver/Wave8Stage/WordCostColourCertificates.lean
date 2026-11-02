import InitECandidate.Solver.Wave8Stage.WordCostCertificates
import InitECandidate.Solver.Wave8Stage.WordCostCompilerControl

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostColourCertificates
open Flapjack WordCostCertificates WordCostEffects WordCostControl
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend

/-- Signed-cost certificates survive arbitrary register renaming, without
injectivity or register-allocation success assumptions. -/
theorem applyColour_derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (p : WordLangProgHOL (BitVec width)) (effects : Effects)
    (certificate : Derives defs terminal p effects) (f : Nat → Nat) :
    Derives defs terminal (Flapjack.WordAlloc.applyColour f p) effects := by
  induction certificate with
  | normal p erased => exact Derives.normal _ ((erase_applyColour f p).trans erased)
  | tick => exact Derives.tick
  | share op reg exp => exact Derives.share op (f reg) _
  | raise reg => exact Derives.raise (f reg)
  | result reg regs => exact Derives.result (f reg) (regs.map f)
  | breakTo label => exact Derives.breakTo label
  | continueTo label => exact Derives.continueTo label
  | ffi name p1 l1 p2 l2 names => exact Derives.ffi name (f p1) (f l1) (f p2) (f l2) _
  | seq left right ihLeft ihRight => exact Derives.seq ihLeft ihRight
  | branch cmp reg operand left right ihLeft ihRight =>
    exact Derives.branch cmp (f reg) _ ihLeft ihRight
  | loop names exits body cycle ih => exact Derives.loop _ _ ih cycle
  | tail dest args => exact Derives.tail dest (args.map f)
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers ihCont ihHandlers =>
    cases handler with
    | none =>
      simpa only [Flapjack.WordAlloc.applyColour,Option.map_none] using
        Derives.returning (names.map f) (Flapjack.WordAlloc.applyNummapsKey f live)
          (Flapjack.WordAlloc.applyColour f next) l1 l2 dest (args.map f) none contEffects handlerEffects
          ihCont (by intro name body h1 h2 equal; cases equal)
    | some h =>
      rcases h with ⟨oldName,oldBody,old1,old2⟩
      have hbody := ihHandlers oldName oldBody old1 old2 rfl
      simpa only [Flapjack.WordAlloc.applyColour,Option.map_some] using
        Derives.returning (names.map f) (Flapjack.WordAlloc.applyNummapsKey f live)
          (Flapjack.WordAlloc.applyColour f next) l1 l2 dest (args.map f)
          (some (f oldName,Flapjack.WordAlloc.applyColour f oldBody,old1,old2)) contEffects handlerEffects
          ihCont (by
            intro name body h1 h2 equal
            simp only [Option.some.injEq,Prod.mk.injEq] at equal
            obtain ⟨rfl,rfl,rfl,rfl⟩ := equal
            exact hbody)

/-- A validated oracle allocation carries its full effect certificate. -/
theorem oracleColourOk_derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (k : Nat) (colour : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) (effects : Effects)
    (certificate : Derives defs terminal p effects)
    (accepted : Flapjack.WordAlloc.oracleColourOk k colour tree p forced = some q) :
    Derives defs terminal q effects := by
  unfold Flapjack.WordAlloc.oracleColourOk at accepted
  cases colour with
  | none => cases accepted
  | some colour =>
    dsimp only at accepted
    split at accepted
    · split at accepted
      · cases accepted; exact applyColour_derives defs terminal p effects certificate _
      · cases accepted
    · cases accepted

/-- Both successful allocator routes and the fallback retain the certificate. -/
theorem wordAlloc_derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (function : Nat) (ac : AsmConfigExact width) (algorithm registers : Nat)
    (p : WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat)) (effects : Effects)
    (certificate : Derives defs terminal p effects) :
    Derives defs terminal (Flapjack.WordAlloc.wordAlloc function ac algorithm registers p colour) effects := by
  unfold Flapjack.WordAlloc.wordAlloc
  dsimp only
  generalize oracle : Flapjack.WordAlloc.oracleColourOk registers colour
    (Flapjack.WordAlloc.getClashTree p []) p (Flapjack.WordAlloc.getForced ac p []) = chosen
  cases chosen with
  | some q => exact oracleColourOk_derives defs terminal registers colour _ p q _ effects certificate oracle
  | none =>
    dsimp only
    split
    · exact applyColour_derives defs terminal p effects certificate _
    · exact certificate

/-- Certifying the actual optimization prefix suffices for the complete
Word-to-Word output, uniformly over every allocation oracle. -/
theorem fullCompileSingle_derives {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (ac : AsmConfigExact width) (twoRegisters : Bool) (registers algorithm name arity : Nat)
    (p : WordLangProgHOL (BitVec width)) (colour : Option (Spt Nat)) (effects : Effects)
    (noMt : noMtSubprogsHOL p = true)
    (certificate : Derives defs terminal
      (WordCostCompilerControl.preAllocation ac twoRegisters arity p) effects) :
    Derives defs terminal (WordToWord.fullCompileSingle twoRegisters registers algorithm ac
      ((name,arity,p),colour)).2.2 effects := by
  rw [WordToWord.no_mt_full_compile_single _ _ _ _ _ noMt]
  simpa only [WordToWord.compileSingle,WordCostCompilerControl.preAllocation,
    WordInst.instSelectExecutable_eq] using wordAlloc_derives defs terminal name ac algorithm registers
      (WordCostCompilerControl.preAllocation ac twoRegisters arity p) colour effects certificate

end InitECandidate.Solver.Wave8Stage.WordCostColourCertificates
