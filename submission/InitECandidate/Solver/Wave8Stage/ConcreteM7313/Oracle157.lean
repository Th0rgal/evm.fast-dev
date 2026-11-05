import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 157 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle157 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 11)) 0
                (Flapjack.Spt.bn (Flapjack.Spt.ls 11) (Flapjack.Spt.ls 0)))
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 2))
                (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 7
                  (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 1 (Flapjack.Spt.ls 7)) 3
                (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 4)))
              7
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 10)) 2
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1))) 2
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1))))
              3
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 3)) 7
                (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 5)) 7
                (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 10)))
              1
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 7 (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7))) 22
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 22))) 0
                (Flapjack.Spt.bn (Flapjack.Spt.ls 9) (Flapjack.Spt.ls 10)))
              4
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 7)) 0
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 5)) 1
                (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 0)))
              2
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 2)) 7
                (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)) 3
                  (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 8))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7 (Flapjack.Spt.ls 2)) 7
                (Flapjack.Spt.bn (Flapjack.Spt.ls 9) (Flapjack.Spt.ls 7)))
              2
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 3)) 1
                (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)))))
            (Flapjack.Spt.bs
              (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 22 (Flapjack.Spt.ls 10))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 7))))
              0
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 7 (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7))))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) Flapjack.Spt.ln)))))
        Flapjack.Spt.ln)))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
