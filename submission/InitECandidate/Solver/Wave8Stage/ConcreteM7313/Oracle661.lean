import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 661 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle661 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 3 (Flapjack.Spt.ls 5)) 1
      (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 8))))
    0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 1 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 21
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 2)) 16
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 10))))))
                  5
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 1 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))))
                22
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 1 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9)))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 21
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))))
                  17
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      1
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 12) (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)))))
                    29
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2 (Flapjack.Spt.ls 1)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 23 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 16))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9 Flapjack.Spt.ln) 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 8))))
                      2
                      (Flapjack.Spt.bs Flapjack.Spt.ln 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21 (Flapjack.Spt.ls 5)))))
                  4
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 24 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4 (Flapjack.Spt.ls 2)))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 (Flapjack.Spt.ls 14))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10 Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 8))) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 (Flapjack.Spt.ls 2)))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 (Flapjack.Spt.ls 21))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 20 Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 1)) 5
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 Flapjack.Spt.ln))))
                  0
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 7 Flapjack.Spt.ln) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 21 (Flapjack.Spt.ls 27))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 2))))
                      11
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      9
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 2)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                    4
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 7)))
                        12
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 2))))))
                  26
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.ls 0)))
                      4
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 2)) 6
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 2)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 0)) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))
                      17
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 2)) 20
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 2)) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                      11
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 2)))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 13 Flapjack.Spt.ln) 18
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 2)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 8))) 7
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      3
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 2 (Flapjack.Spt.ls 24)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.ls 4)) 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11))))
                      3
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 9)))))
                    18
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 7)))
                        12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 14
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)))))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 2 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 10))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 19) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 2)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 10)))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0 (Flapjack.Spt.ls 2)) 12
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 9)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 8))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 2 (Flapjack.Spt.ls 1)) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 2)) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 2)))))
                  8
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 2 (Flapjack.Spt.ls 1)) 1
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 16) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 10)))))
                    27
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      20
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 11)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 5 (Flapjack.Spt.ls 8)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 13
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 8))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 11 Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 8))))))
                  3
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 12)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 5 (Flapjack.Spt.ls 17)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 5 (Flapjack.Spt.ls 20)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.ls 4)))
                      11
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 4 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 7)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 5 (Flapjack.Spt.ls 19)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 12)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 6)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 8))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 4)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))))
                  6
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 9)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 8))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 1)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))))
                    16
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 (Flapjack.Spt.ls 10)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 5)))
                        12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 19
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                      5 (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 Flapjack.Spt.ln)))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      7
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 Flapjack.Spt.ln))))
                  25
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 4
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln))
                      5 (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 Flapjack.Spt.ln)))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 16 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 17
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln))
                      5 (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)))
                    9
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 13) Flapjack.Spt.ln) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 18 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 0)))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 20 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      0 (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 12 Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9))) 5
                        (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                      12
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 10))))))
                  19
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)))
                        2 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.ls 1))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 11
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 8))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                        13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3))))))
                  8
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 0
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                      3
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                        2 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.ls 1))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 8))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 2 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4)))
                        1
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10))))))
                  20
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 21) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9)))))
                    6
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2 (Flapjack.Spt.ls 1)) 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 2 (Flapjack.Spt.ls 1)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 15
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 12) (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 4))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 4)))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 2)) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 21)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 2)) 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 8))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15))))))
                  10
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 2)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 15)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 18)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 0))))
                      11
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 4 (Flapjack.Spt.ls 25)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 2)) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 14)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 23
                          (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 8))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 21) 4 (Flapjack.Spt.ls 5)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13))))))
                  7
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 2)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.ls 5)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 21 (Flapjack.Spt.ls 15))))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 16)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 0)) 6
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 9
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 8)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 18) (Flapjack.Spt.ls 0)) 16
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) Flapjack.Spt.ln))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 17
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 0)) 5
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.ls 0)) 18
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 19
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                    9
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 12
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                      11
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.ls 0)) 13
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 13)) 4
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                    14
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 7
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))) 5
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 20
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.ls 0)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))))
                  3
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1 (Flapjack.Spt.ls 0)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 9)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 7))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 2 (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 9)))))
                    3
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      2
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 13
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))))
                    2
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0 (Flapjack.Spt.ls 2)) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))))
                  5
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.ls 2)))
                      6
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 11
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6))))
                      9
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 2)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      20
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 2)) 13
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6))))
                      7
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 5))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 5)))))
                  12
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))
                      11
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 27 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 11 (Flapjack.Spt.ls 2)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 9))))))
                  8
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    20
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4)))
                      11
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11))))
                      12
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      11
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2)))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 0))))))
                  5
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 4)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)))))
                    6
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 5 (Flapjack.Spt.ls 4)) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                        12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 13 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln)))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      7
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 21 Flapjack.Spt.ln))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9 Flapjack.Spt.ln))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 13 Flapjack.Spt.ln)))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6 Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 17 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))) 5
                        (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 21
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 Flapjack.Spt.ln))
                      5 (Flapjack.Spt.bs (Flapjack.Spt.ls 21) 13 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 28 Flapjack.Spt.ln) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 19 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 6))) 5
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 Flapjack.Spt.ln))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      11
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 13 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 21 Flapjack.Spt.ln)))
                    15
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                      11
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))) 5
                        (Flapjack.Spt.bs Flapjack.Spt.ln 21
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 21
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3))) 13
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 10))))))
                  8
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                      18
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 1)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)))
                        0 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 1))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 8))))
                      0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                    4
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 1)) 13
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                      2
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 0)) 2
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)))
                        0 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 1)))))))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                        Flapjack.Spt.ln))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                        Flapjack.Spt.ln))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                        Flapjack.Spt.ln))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                        Flapjack.Spt.ln))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))
                        Flapjack.Spt.ln)))
                  Flapjack.Spt.ln))))))))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
