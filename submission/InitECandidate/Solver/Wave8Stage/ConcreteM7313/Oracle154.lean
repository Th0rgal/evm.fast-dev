import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 154 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle154 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 2)) 0
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
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 4)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 18)))
                            1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            14 (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7 (Flapjack.Spt.ls 3)))
                          9
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14))))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 9)) 14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 7)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 14)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)) 6
                              (Flapjack.Spt.ls 2))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20))))
                          1
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.ls 8)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 6)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)))
                            19
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 16)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 18)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)))
                            4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            1 (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14 (Flapjack.Spt.ls 14)))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20))))))
                      13
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                          33
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 16)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1 (Flapjack.Spt.ls 12)) 7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 16)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 3)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 14)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))))
                        25
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 18)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 16)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 14)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.ls 7)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 16))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 20))))
                          18
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 2 (Flapjack.Spt.ls 7)) 15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 18)))
                            0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15))))
                          28
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 1)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            6 (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 0)))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 0))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 12))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 16)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 12)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7 (Flapjack.Spt.ls 12)) 7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))))
                        26
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 13)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 12)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 13))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 18)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 15)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15))))
                          31
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            19
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)) 1
                              (Flapjack.Spt.ls 14))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 20))))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 15 (Flapjack.Spt.ls 9)) 6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                            18
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))))
                      16
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 18)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 12)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13))))
                          30
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 15))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 3)) 18
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 13)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                              (Flapjack.Spt.ls 6)))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 20))))))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 16)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 16)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 18)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14 (Flapjack.Spt.ls 5)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 3)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 18
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 12)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 18))))
                          11
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 3))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13))))))
                      11
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 2)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          28
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            20
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 18
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 7
                              (Flapjack.Spt.ls 15)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            18
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20))))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0 (Flapjack.Spt.ls 20)) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 0)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 4)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 18)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 20)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            8 (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0 (Flapjack.Spt.ls 6)))
                          10
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 1)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 14))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 17)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)))
                            6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12))))
                          11
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 0))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14))))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 16)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 3)) 5
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 12))) 7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 12))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))))
                          28
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9 (Flapjack.Spt.ls 6)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 19)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 14)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 3))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 16))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 1)) 9
                              (Flapjack.Spt.ls 19))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 17)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15))))
                          4
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)))
                            19
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 14)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 18)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 3)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 16
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 14)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))))
                      12
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 5
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)) 17
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20))))
                          15
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0 (Flapjack.Spt.ls 7)) 16
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 19
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 16)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 18)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            16
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 11))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 16)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13))))
                          4
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 15))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            29 (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 10)))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 20)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) 18
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 17)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 18)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 17))))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 13)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 20)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 18 (Flapjack.Spt.ls 3)) 9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 5
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 18))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 20)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 12)) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 3)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)) 15
                              (Flapjack.Spt.ls 0))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 14)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                          11
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            20
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 15))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 18
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 18)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14))))
                          10
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 21
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 17)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            18
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)) 7
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 14)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 2)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 12)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 15)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 20
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20))))
                          16
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5 Flapjack.Spt.ln) 10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 0)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 19)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 16)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 18)))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)))
                            4 (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14 (Flapjack.Spt.ls 14)))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 27
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 16)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 15))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            25
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)) 26
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 18)))
                            13
                            (Flapjack.Spt.bs Flapjack.Spt.ln 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          4
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 20))))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 3)))))
                        20
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 31
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 1)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 16)) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 32
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4 (Flapjack.Spt.ls 11)) 2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)) 30
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)) 28
                              (Flapjack.Spt.ls 8)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 30
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 20)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 16)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            27
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))))
                        29
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 16)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          24
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 29
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 25
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 2)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 18)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            32
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 10)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 12)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))))
                    15
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 24
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 16)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20))))
                          0
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10 (Flapjack.Spt.ls 8)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 17)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 16)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 1
                              (Flapjack.Spt.ls 4))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 32
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 16)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            31
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 14)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          4
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 15)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 24
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))))
                  22
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 29
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 20))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 27
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 1)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 16)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))))
                        1
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 28
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8 (Flapjack.Spt.ls 14)) 26
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 13)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            24
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 13))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 12)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 26
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 16)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18))))
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 3))))))
                      14
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 21 (Flapjack.Spt.ls 12)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 1)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 25
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 18)))
                            9
                            (Flapjack.Spt.bs Flapjack.Spt.ln 30
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 2)) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 13
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3)) 29
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 31
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)) 4
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          4
                          (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 13 (Flapjack.Spt.ls 11)) 13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 2)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            10
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 15)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0))))
                          13
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 18))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 3)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))))))
                  4
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 12)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 6)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 8)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 14)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 16)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 12)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 19)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 19)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 18))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            12
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 1))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 12)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))))
                        9
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 17)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            13
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0))))))))
                  0
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 13)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 6)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          11
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 17)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            15
                            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 14))
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 16)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 20)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 10
                              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bn (Flapjack.Spt.ls 19)
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 3))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))))
                        7
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 12))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 20))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 1)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 3)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 13)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 15)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 13)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 9)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 4)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 12)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 18)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 14)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 16)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 6)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 18)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 13))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)))))
                        27
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2))))
                          21
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 3)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 16)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 15)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 18))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 14)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 12
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 16)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13))))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))))
                        32
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 18))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))))))
                  5
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 2)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 18)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 20)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 4)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 13)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 16)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 12))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 15)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 14)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 18)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 16)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 5)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))))))
                  23
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 2)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 19)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 1))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 18)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            17
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 16)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 20))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13))))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 0)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))))
                        8
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 15)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 3)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 13)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 0)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 16)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))))
                      10
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 15))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))))))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 2)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 12))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 18)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 13)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 14)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 3)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1))))
                          11
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 0)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 19)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 0))))))))
                  3
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 12)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 2)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 20)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                          12
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 0)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 1))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 16)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 12)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 18)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 16)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 17)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 3)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 16)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 20))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 15)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 20 (Flapjack.Spt.ls 3)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 14)))))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 13)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 18)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))
                          1
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 2)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))
                        15
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19))))
                          3
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 12)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            12
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 12)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 2
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 2)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 17)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 14)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 13))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 12))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 14)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 3)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 18)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 1)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 13))))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 3)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))))
                        3
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 16)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 18))))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 14)))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 1)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 15))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 20)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 0)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 19)))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14)))
                            5
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 20))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 13)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))
                        19
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 19)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 18)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                          16
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 20)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))
                          17
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 3)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 12)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17)))
                            4
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 19)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 1)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0))))
                          14
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 13)) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))))
                        6
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 0)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 20)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 14)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))))
                        17
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 15)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 19))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 19))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 18)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 13)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14)))
                            6
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 16 (Flapjack.Spt.ls 3)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 12)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)))
                            11
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 4)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))))
                        18
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 17)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 17))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 1)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17))))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))
                          13
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 0)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 16)) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 0)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 0)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 20))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 16)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 15)))))))
                    1
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 14)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 13))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 17)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 2)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 15)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 12))))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 18)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 13))))
                          15
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17)) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 1)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 12)))
                            8
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.ls 0)) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 3)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 14)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1))))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 13)))
                            9
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17))))
                          10
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 20)))
                            10
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 19)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 17))))
                          20
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 12)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 17))))))
                      7
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 13)))
                            14
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 17))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 1)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 19)) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 17)))
                            2
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 19 (Flapjack.Spt.ls 1)) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0))))
                          19
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            16
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3)) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14)))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 1)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 14))))
                          0
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 20) 0
                              (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 17)))
                            1
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 3)) 11
                              (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 14)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 20)))
                            15
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 19))))
                          18
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 8
                              (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 15)))
                            3
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 14)) 6
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 2))))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 17)))
                            0
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 9
                              (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 18))))
                          2
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 15
                              (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 17)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)) 10
                              (Flapjack.Spt.bs Flapjack.Spt.ln 14 (Flapjack.Spt.ls 19)))))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 1
                              (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 19)))
                            7
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)) 14
                              (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 12))))
                          4
                          (Flapjack.Spt.bs
                            (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 14)))
                            13
                            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3)) 3
                              (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 3))))))))))))))
      Flapjack.Spt.ln))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
