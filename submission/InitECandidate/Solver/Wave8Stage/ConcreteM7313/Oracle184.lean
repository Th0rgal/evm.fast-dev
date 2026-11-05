import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 184 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle184 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 8 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))) 6
              (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 1
                (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
            0
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 1
                (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 3 Flapjack.Spt.ln))
              6 (Flapjack.Spt.bn (Flapjack.Spt.ls 4) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 (Flapjack.Spt.ls 6))) 2
              (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 6 (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 0 Flapjack.Spt.ln)))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 (Flapjack.Spt.ls 5)) 6 (Flapjack.Spt.ls 5)) 2
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 4 Flapjack.Spt.ln) 6
                (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5
              (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 5 (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 1 (Flapjack.Spt.ls 7))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)) 2
                (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6 Flapjack.Spt.ln))
              3 (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3 Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 1 Flapjack.Spt.ln)) 0
              (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 1)))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 6)) 4 (Flapjack.Spt.ls 2)) 1
              (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 3 (Flapjack.Spt.ls 8))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
