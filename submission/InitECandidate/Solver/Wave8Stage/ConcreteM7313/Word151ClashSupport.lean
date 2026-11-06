import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000
namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
open Flapjack
noncomputable section
theorem clash_seq (p q : WordLangProgHOL (BitVec 64))
    (a b : RegAlloc.ClashTree)
    (hp : WordAlloc.getClashTree p [] = a)
    (hq : WordAlloc.getClashTree q [] = b) :
    WordAlloc.getClashTree (.seq p q) [] = .seq a b := by
  simp only [WordAlloc.getClashTree, hp, hq]

end
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
