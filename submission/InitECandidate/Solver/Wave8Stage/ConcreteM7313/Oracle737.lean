import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 737 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle737 : Option (Spt Nat) :=
some (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 2)) 0 Flapjack.Spt.ln)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
