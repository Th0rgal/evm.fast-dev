import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 245 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle245 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))
        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
