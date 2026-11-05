import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 142 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle142 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 5)) 1
      (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4)))
    0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.ls 2)) 5
                (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln))
              5
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln)
                (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln)))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 8 (Flapjack.Spt.ls 8)))
              7
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln) 1
                (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 8 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 5
                (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln))
              6
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 1 (Flapjack.Spt.ls 2)) 3
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.ls 1))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 9 (Flapjack.Spt.ls 7))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9 (Flapjack.Spt.ls 9)))
              0
              (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 (Flapjack.Spt.ls 6))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 9 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 9)))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 9)) 1 Flapjack.Spt.ln)
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 3 (Flapjack.Spt.ls 1)) 4
                (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3 (Flapjack.Spt.ls 3))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 7 (Flapjack.Spt.ls 7)))
              9
              (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 9 (Flapjack.Spt.ls 9))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 7 (Flapjack.Spt.ls 9)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 6 (Flapjack.Spt.ls 6)))
              8
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 8)) 2
                (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8))))
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 7) Flapjack.Spt.ln))
              (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 1
                (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 (Flapjack.Spt.ls 7)))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
