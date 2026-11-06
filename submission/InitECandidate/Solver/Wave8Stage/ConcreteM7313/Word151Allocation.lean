import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Bounds
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Allocation
open Flapjack Flapjack.Compiler.Backend
theorem accept (k : Nat) (col : Spt Nat) (tree : RegAlloc.ClashTree)
    (p : WordLangProgHOL (BitVec 64)) (forced : List (Nat × Nat))
    (he : WordAlloc.everyEvenColour col = true)
    (hc : (RegAlloc.checkClashTree (WordAlloc.totalColour col) tree .ln .ln).isSome = true)
    (hs : everyStackVarHOL (fun x => decide (2*k ≤ x)) (WordAlloc.applyColour (WordAlloc.totalColour col) p) = true)
    (hf : forced.all (fun (x,y) => WordAlloc.totalColour col x != WordAlloc.totalColour col y) = true) :
    WordAlloc.oracleColourOk k (some col) tree p forced = some (WordAlloc.applyColour (WordAlloc.totalColour col) p) := by
  simp only [WordAlloc.oracleColourOk, he, hc, hs, hf, Bool.and_self, ↓reduceIte]
open InitE Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard87
theorem alloc_of_accept (ra : WordToWord.RegAllocFn) (fc alg k : Nat)
    (c : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (p out : WordLangProgHOL (BitVec 64)) (col : Option (Spt Nat))
    (tree : RegAlloc.ClashTree) (ht : WordAlloc.getClashTree p [] = tree)
    (ha : WordAlloc.oracleColourOk k col tree p (WordAlloc.getForced c p []) = some out) :
    WordToWord.wordAllocWith ra fc c alg k p col = out := by
  simp only [WordToWord.wordAllocWith, ht, ha]
theorem accepted : WordAlloc.oracleColourOk registers oracle151
    Word151ClashTree.part0TreeSuffix prefixProgram (WordAlloc.getForced riscvConfig prefixProgram []) =
    some Word151Bounds.coloured :=
  accept registers (oracle151.getD .ln) Word151ClashTree.part0TreeSuffix prefixProgram
    (WordAlloc.getForced riscvConfig prefixProgram []) Word151ColourCheck.even
    Word151ColourCheck.checked Word151Bounds.stackBounds Word151Bounds.forcedBounds
theorem allocated_eq : WordToWord.wordAllocWith RegAlloc.regAllocExecutable
    name riscvConfig (oracleCompilerConfig []).wordToWordConf.regAlg registers prefixProgram oracle151 =
    Word151Bounds.coloured :=
  alloc_of_accept RegAlloc.regAllocExecutable name _ registers riscvConfig prefixProgram
    Word151Bounds.coloured oracle151 Word151ClashTree.part0TreeSuffix Word151ClashTree.tree_eq accepted
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Allocation
