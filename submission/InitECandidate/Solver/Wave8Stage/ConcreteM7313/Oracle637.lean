import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 637 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle637 : Option (Spt Nat) :=
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
              (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 0
                (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12))))
              5 (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 5))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 11 (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4))) 0
                (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
              1
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 6 (Flapjack.Spt.ls 8)) 11
                (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 2 (Flapjack.Spt.ls 8)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 2))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 8))))
              3
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 7))) 1
                (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 12))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 7 (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 12))) 4
                (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0))))
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 13)) 6
                (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0 (Flapjack.Spt.ls 2))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))
              4
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 5
                (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 0))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11))) 11
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 10))))
              0
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 12 (Flapjack.Spt.ls 7)) 4
                (Flapjack.Spt.bn (Flapjack.Spt.ls 14) (Flapjack.Spt.ls 9)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 11)))
              2
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 4 (Flapjack.Spt.ls 13)) 8
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 13))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))) 8
                (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4))))
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12))) 8
                (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 5 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9))))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
