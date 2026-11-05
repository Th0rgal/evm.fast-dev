import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 151 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle151 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 7)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 6)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          30
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 8 (Flapjack.Spt.ls 14))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 12 (Flapjack.Spt.ls 6))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 (Flapjack.Spt.ls 2)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 9))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 4 (Flapjack.Spt.ls 0)))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 6)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                        23
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 4))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 8))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 12)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 1))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 7)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0 (Flapjack.Spt.ls 7)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 6)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 12))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14 (Flapjack.Spt.ls 9))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 6))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9 (Flapjack.Spt.ls 14)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.ls 4))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 1 (Flapjack.Spt.ls 7)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 5 (Flapjack.Spt.ls 8)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12 (Flapjack.Spt.ls 5))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 9 (Flapjack.Spt.ls 1))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 2))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          23
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 7)) 15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 14 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 4 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 9)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.ls 5)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                          31
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 4 (Flapjack.Spt.ls 0))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 (Flapjack.Spt.ls 6))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 10 (Flapjack.Spt.ls 2)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 6 (Flapjack.Spt.ls 8))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 1 (Flapjack.Spt.ls 12)))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 7)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 10)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 7)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 0 (Flapjack.Spt.ls 5))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 7 (Flapjack.Spt.ls 1))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 4))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 5)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 33
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9 (Flapjack.Spt.ls 14))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 12 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                        27
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 12 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 2 (Flapjack.Spt.ls 7))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7 (Flapjack.Spt.ls 8))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 10))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 4 (Flapjack.Spt.ls 0)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 1))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 14)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 4)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 (Flapjack.Spt.ls 5))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 7)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7 (Flapjack.Spt.ls 14))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 2))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 6)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 12))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)) 7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 10))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 1))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 21)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 6)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 0))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 16))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 12)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                          26
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 15))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 1 (Flapjack.Spt.ls 14)))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 1)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7 (Flapjack.Spt.ls 7)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 0 (Flapjack.Spt.ls 5))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11 (Flapjack.Spt.ls 1))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 14))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 12 (Flapjack.Spt.ls 0)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15 (Flapjack.Spt.ls 9))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 21)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 7)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 12 (Flapjack.Spt.ls 0))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 1)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 7 (Flapjack.Spt.ls 15))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 6))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 14 (Flapjack.Spt.ls 0)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 16 (Flapjack.Spt.ls 1))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          21
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 9 (Flapjack.Spt.ls 7)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 1)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 18))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 15 (Flapjack.Spt.ls 9))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)) 18
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 9)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 12))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 5)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 21)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0 (Flapjack.Spt.ls 6)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 14))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 5 (Flapjack.Spt.ls 5)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 19
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 2)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6 (Flapjack.Spt.ls 6))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 15 (Flapjack.Spt.ls 10)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 2)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 12 (Flapjack.Spt.ls 0)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 2)) 18
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 (Flapjack.Spt.ls 15)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 5))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 12))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 20 (Flapjack.Spt.ls 2))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 7)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 10 (Flapjack.Spt.ls 5)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 0))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 17))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 20)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 6)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 2)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 14))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 2)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 15))))
                        25
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 20
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.ls 12))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 7)))
                          21
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0 (Flapjack.Spt.ls 5)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 5)))
                          29
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 17 (Flapjack.Spt.ls 2)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 2)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 (Flapjack.Spt.ls 5))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 14 (Flapjack.Spt.ls 0))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15 (Flapjack.Spt.ls 10))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 6)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 7)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 12 (Flapjack.Spt.ls 0))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 6 (Flapjack.Spt.ls 15)))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.ls 7))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 4))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 21))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8 (Flapjack.Spt.ls 6)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 15 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 8 (Flapjack.Spt.ls 16))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 5 Flapjack.Spt.ln))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                          8
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 4))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 8))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 17
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 4 (Flapjack.Spt.ls 0)))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 15
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 4)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 16)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 0 (Flapjack.Spt.ls 5))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.ls 6))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 26 (Flapjack.Spt.ls 4))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 4)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 15))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 3
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 9)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9 (Flapjack.Spt.ls 9))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 21)))
                          21
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 32
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 16)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0 (Flapjack.Spt.ls 7)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 9))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 4)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 7 (Flapjack.Spt.ls 8))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 6))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 15 (Flapjack.Spt.ls 0)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.ls 5))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 16 (Flapjack.Spt.ls 4))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          13
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 9 (Flapjack.Spt.ls 7)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5))))
                        16
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 4)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 15)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9 (Flapjack.Spt.ls 18))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 7 (Flapjack.Spt.ls 9))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 18
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 Flapjack.Spt.ln)))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 21)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 6)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 15
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 4 (Flapjack.Spt.ls 0))))
                        1
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 19
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.ls 5)))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 15
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 4 (Flapjack.Spt.ls 0))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                          10
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 9 (Flapjack.Spt.ls 10)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.ls 15))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 10)))))))
                  0
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 17
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 4)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 (Flapjack.Spt.ls 8)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 0 (Flapjack.Spt.ls 5))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7 Flapjack.Spt.ln)))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.ls 6))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 20 (Flapjack.Spt.ls 4))))
                        12
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 10 (Flapjack.Spt.ls 5)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 10 (Flapjack.Spt.ls 17))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 10 (Flapjack.Spt.ls 20)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.ls 7))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 4)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 15))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 8))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 16
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 4 (Flapjack.Spt.ls 0)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 20
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 6 Flapjack.Spt.ln)))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 5)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 6)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          7
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 6
                            (Flapjack.Spt.ls 7))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 17 (Flapjack.Spt.ls 4)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 15 (Flapjack.Spt.ls 0))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 10))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 7)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0 (Flapjack.Spt.ls 6)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 10))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 4)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 6 (Flapjack.Spt.ls 8))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 32
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          9
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 27))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11 (Flapjack.Spt.ls 10)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 3 (Flapjack.Spt.ls 11))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 26))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 9 (Flapjack.Spt.ls 2)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 8)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 13 (Flapjack.Spt.ls 11)))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11))))
                        23
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 8)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10 (Flapjack.Spt.ls 8)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 31)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 27
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 13))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 28 (Flapjack.Spt.ls 8))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 21)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 2 (Flapjack.Spt.ls 3)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 11))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 30))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11 (Flapjack.Spt.ls 28)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 16)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 2 (Flapjack.Spt.ls 3))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 14 (Flapjack.Spt.ls 14))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 8))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9 (Flapjack.Spt.ls 14)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 25
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11 (Flapjack.Spt.ls 13))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 29)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 10)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 25)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 30 (Flapjack.Spt.ls 8)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 3 (Flapjack.Spt.ls 11))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 11))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8 (Flapjack.Spt.ls 2))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 33)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 21) 13 (Flapjack.Spt.ls 11))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 8)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10 (Flapjack.Spt.ls 8)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 28
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 32)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 14)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 13 (Flapjack.Spt.ls 11))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 8))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 14 (Flapjack.Spt.ls 11)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 29 (Flapjack.Spt.ls 8))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 1 (Flapjack.Spt.ls 3)))))))
                  22
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 14)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 11 (Flapjack.Spt.ls 27))))
                        2
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7 (Flapjack.Spt.ls 1))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 33
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11 (Flapjack.Spt.ls 13))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 28)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 9)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 3 (Flapjack.Spt.ls 11))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 3 (Flapjack.Spt.ls 11)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 26)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.ls 9))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 31 (Flapjack.Spt.ls 8))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 8)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 14))))
                        24
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 13 (Flapjack.Spt.ls 11)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 8 (Flapjack.Spt.ls 1))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 25)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 30)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 21
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 13)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 8)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9 (Flapjack.Spt.ls 8))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7 (Flapjack.Spt.ls 14))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          7
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 11))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 11))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 11)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 29)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 1 (Flapjack.Spt.ls 3))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 8)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 14 (Flapjack.Spt.ls 14))))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8 Flapjack.Spt.ln))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 15))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 11))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11 (Flapjack.Spt.ls 8)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15 (Flapjack.Spt.ls 8))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7 (Flapjack.Spt.ls 14)))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.ls 11)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 15 (Flapjack.Spt.ls 15))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11 (Flapjack.Spt.ls 8))))))
                    18
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 14))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.ls 9))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 9 (Flapjack.Spt.ls 11)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 9))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 14)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.ls 9))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 15 (Flapjack.Spt.ls 8))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 15)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 11 (Flapjack.Spt.ls 8))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 9 Flapjack.Spt.ln))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.ls 9)))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 11 (Flapjack.Spt.ls 11))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 9))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 9)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11 (Flapjack.Spt.ls 8))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 15 (Flapjack.Spt.ls 15)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9 (Flapjack.Spt.ls 14))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 11)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 15 (Flapjack.Spt.ls 15)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.ls 14))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 11))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 10)))))
                      9
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14 (Flapjack.Spt.ls 14))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.ls 10))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 7 (Flapjack.Spt.ls 11)))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 7
                            (Flapjack.Spt.ls 10))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15 (Flapjack.Spt.ls 8)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 8))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 11 (Flapjack.Spt.ls 8))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 10 Flapjack.Spt.ln))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 15))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 11))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11 (Flapjack.Spt.ls 11)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 10 Flapjack.Spt.ln)))
                        33
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 14))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15 (Flapjack.Spt.ls 8))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9 (Flapjack.Spt.ls 14)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.ls 8))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 15 (Flapjack.Spt.ls 15)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11 (Flapjack.Spt.ls 8)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 15))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 10))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 8)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.ls 10))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9 (Flapjack.Spt.ls 11))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8))
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 15 (Flapjack.Spt.ls 8))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 8 (Flapjack.Spt.ls 6)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 (Flapjack.Spt.ls 11))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 9))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9 (Flapjack.Spt.ls 12)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 9 (Flapjack.Spt.ls 4))))
                        35
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 7 (Flapjack.Spt.ls 0)))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7 (Flapjack.Spt.ls 8)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11 (Flapjack.Spt.ls 9))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.ls 8))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11 (Flapjack.Spt.ls 4))))
                        16
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 12 (Flapjack.Spt.ls 11)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 4 (Flapjack.Spt.ls 9))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 11))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 11)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 6)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 12 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 8 (Flapjack.Spt.ls 4))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 6 (Flapjack.Spt.ls 8))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 4 (Flapjack.Spt.ls 11)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 9 (Flapjack.Spt.ls 8))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 9 (Flapjack.Spt.ls 7)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 5))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 4)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 9))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 4 (Flapjack.Spt.ls 9))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.ls 12))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 9)))))
                      11
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 7)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 9 (Flapjack.Spt.ls 0))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 5 (Flapjack.Spt.ls 8)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 10)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8 (Flapjack.Spt.ls 0))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6 (Flapjack.Spt.ls 8))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11 (Flapjack.Spt.ls 10))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 4 (Flapjack.Spt.ls 10)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11 (Flapjack.Spt.ls 4))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 12 (Flapjack.Spt.ls 11)))))))
                  12
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 10 (Flapjack.Spt.ls 4)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 11))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 9 (Flapjack.Spt.ls 12))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 8))))
                        28
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 10 (Flapjack.Spt.ls 5)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 10))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 10)))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 10 (Flapjack.Spt.ls 7))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 4))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 4))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 6)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 9 (Flapjack.Spt.ls 0)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8 (Flapjack.Spt.ls 12))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 10)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.ls 8)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 (Flapjack.Spt.ls 8))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 7)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 4 (Flapjack.Spt.ls 11))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 11)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4 (Flapjack.Spt.ls 10))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 11)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 5)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 12 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 4)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 10 (Flapjack.Spt.ls 4)))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 11))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 11 (Flapjack.Spt.ls 6)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 (Flapjack.Spt.ls 14))))
                        32
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 10)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 6))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 10 (Flapjack.Spt.ls 1)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 11 (Flapjack.Spt.ls 11)))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 10)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 10)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 14))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 7 (Flapjack.Spt.ls 11))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 4))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 1 (Flapjack.Spt.ls 11)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 10))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 10)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 10)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 (Flapjack.Spt.ls 11))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 14 (Flapjack.Spt.ls 14))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 10))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 4 (Flapjack.Spt.ls 14)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 11 (Flapjack.Spt.ls 7)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          6
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 10 (Flapjack.Spt.ls 4)))))
                      8
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 10)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 5))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 14 (Flapjack.Spt.ls 11))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 10 (Flapjack.Spt.ls 1))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 10)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 11)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11 (Flapjack.Spt.ls 11))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 4)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5 (Flapjack.Spt.ls 10)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 9)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 14)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11 (Flapjack.Spt.ls 11))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6 (Flapjack.Spt.ls 9))))))
                    14
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 9)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 14 (Flapjack.Spt.ls 11)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 11)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 9 (Flapjack.Spt.ls 4))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 2 (Flapjack.Spt.ls 11)))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 14 (Flapjack.Spt.ls 14)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 9)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11 (Flapjack.Spt.ls 9))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 8 (Flapjack.Spt.ls 2))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 11 (Flapjack.Spt.ls 5)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 4 (Flapjack.Spt.ls 14))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 9)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 9)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 7)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 11 (Flapjack.Spt.ls 7))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 11)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 8 (Flapjack.Spt.ls 4))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 11 (Flapjack.Spt.ls 11)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9 (Flapjack.Spt.ls 2))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 9)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 6)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 14)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 9)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 5 (Flapjack.Spt.ls 11)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)) 12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5 (Flapjack.Spt.ls 9))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 7)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 4 (Flapjack.Spt.ls 14))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 11)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 14 (Flapjack.Spt.ls 11))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 9)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 11 (Flapjack.Spt.ls 9)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 5)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2 (Flapjack.Spt.ls 11))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 4)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 14 (Flapjack.Spt.ls 14))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11 (Flapjack.Spt.ls 10)))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 14 (Flapjack.Spt.ls 15))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 8 (Flapjack.Spt.ls 14))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 9 (Flapjack.Spt.ls 2)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15 (Flapjack.Spt.ls 4))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 4 (Flapjack.Spt.ls 0)))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10 (Flapjack.Spt.ls 8)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 15 (Flapjack.Spt.ls 15))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 4))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)))
                          10
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 14))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 2 (Flapjack.Spt.ls 9)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 4 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 17
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                          20
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0 (Flapjack.Spt.ls 5))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11))))
                        12
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0 (Flapjack.Spt.ls 7)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 2 (Flapjack.Spt.ls 9))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 15 (Flapjack.Spt.ls 4))))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.ls 8))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 15)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 8
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 14 (Flapjack.Spt.ls 4))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 10)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 5 (Flapjack.Spt.ls 14)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9 (Flapjack.Spt.ls 14))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 4 (Flapjack.Spt.ls 11))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 2))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 8)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 15 (Flapjack.Spt.ls 15)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 9)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 10)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 4 (Flapjack.Spt.ls 0))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10 (Flapjack.Spt.ls 8)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)))
                          17
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 15 (Flapjack.Spt.ls 15)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)))
                          11
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 4 (Flapjack.Spt.ls 0))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 8))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 17
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10 (Flapjack.Spt.ls 14))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 4 (Flapjack.Spt.ls 11)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6 (Flapjack.Spt.ls 14))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 1 (Flapjack.Spt.ls 10)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 15 (Flapjack.Spt.ls 4)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 15
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 0 (Flapjack.Spt.ls 5))))
                        34
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 7 (Flapjack.Spt.ls 1))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14 (Flapjack.Spt.ls 4))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 11 (Flapjack.Spt.ls 9)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          13
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14 (Flapjack.Spt.ls 15))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 10 (Flapjack.Spt.ls 14))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                        21
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 10 (Flapjack.Spt.ls 14)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11 (Flapjack.Spt.ls 9))))
                        13
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7 (Flapjack.Spt.ls 14))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)))
                          2
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 15 (Flapjack.Spt.ls 4))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 4 (Flapjack.Spt.ls 0)))))
                      10
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 14
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)))
                          3
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 8 (Flapjack.Spt.ls 1))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 12
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 15 (Flapjack.Spt.ls 15)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          9
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 11
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                          14
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14 (Flapjack.Spt.ls 4)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 10
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)))
                          12
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9 (Flapjack.Spt.ls 8))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)) 1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 15))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 10)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                          8
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 4 (Flapjack.Spt.ls 11))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 4)) 16
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0 (Flapjack.Spt.ls 6)))))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7)) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 9)))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1 (Flapjack.Spt.ls 10))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)) 7
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                          19
                          (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 15 (Flapjack.Spt.ls 4)))))))))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
