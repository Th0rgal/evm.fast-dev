import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 725 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle725 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 5)) 1
      (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 2 (Flapjack.Spt.ls 4)))
    0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21 (Flapjack.Spt.ls 2)) 14
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                1
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 40 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 5)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 0)) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 48 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 2))) 7
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 2))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 43 (Flapjack.Spt.ls 1)) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 5))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.ls 4)) 4
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 2))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 19 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 2))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 3)) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 17 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 2))))
                22
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 1))) 1
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 2)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 45 (Flapjack.Spt.ls 0)) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.ls 7)) 16
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 38 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 2))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 6))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 46 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 21))) 2
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 2))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 42 (Flapjack.Spt.ls 1)) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 12 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.ls 5)) 5
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 2))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 20 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 1)) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 49 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))) 6
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 2)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 41 (Flapjack.Spt.ls 0)) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 2))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 13 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.ls 8)) 15
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 39 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 1)) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 47 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 1))) 8
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 1))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 44 (Flapjack.Spt.ls 6)) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))) 21
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))) 3
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 1))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 18 (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1))) 0
                  (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
