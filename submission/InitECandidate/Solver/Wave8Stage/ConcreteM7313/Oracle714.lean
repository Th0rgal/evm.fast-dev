import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 714 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle714 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 11)) 3
        (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 9)))
      1
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 10)) 2
        (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4 (Flapjack.Spt.ls 8))))
    0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln) 33
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 36
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 30)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 6))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 10)))
                          27 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 35)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 4)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 0))))
                        7 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 23)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 1))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 4))) 36
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 31)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 31
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 29 (Flapjack.Spt.ls 4)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 29 Flapjack.Spt.ln) 36
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1))))
                        25
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                          0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 24 Flapjack.Spt.ln) 27
                          (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 35 (Flapjack.Spt.ls 5)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln)))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 3 (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.ls 0))
                        34
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 24 Flapjack.Spt.ln))))))
                7
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 34 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        3
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 10)))
                          (Flapjack.Spt.ls 5))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 40 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln))
                        33
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 25
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 5)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln))
                        6
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 40 (Flapjack.Spt.ls 6))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 33))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 5 (Flapjack.Spt.ls 6)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 39)) 35
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                      27
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 34))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 24 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 0)))))
                    35
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5)))))
                      36
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 35)) 27
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 30
                            (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 3)))
                          5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 32)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        24
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 5)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        5
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 0 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 41
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 28))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 1
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        41
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 33
                            (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 6)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 3))))
                        4
                        (Flapjack.Spt.bs Flapjack.Spt.ln 28
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 23)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln) 3
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 6
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        24
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 1 (Flapjack.Spt.ls 0))))
                      35
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7)) 28
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 33 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 23)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 27 (Flapjack.Spt.ls 5)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 2)) 36
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        26
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 38 (Flapjack.Spt.ls 5)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 0)) 39
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 37 (Flapjack.Spt.ls 0)) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 37 Flapjack.Spt.ln) 6
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        33
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 Flapjack.Spt.ln) (Flapjack.Spt.ls 25))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 Flapjack.Spt.ln) 36
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        25
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.ls 2)) 0 Flapjack.Spt.ln))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 0 Flapjack.Spt.ln) 42
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 32 (Flapjack.Spt.ls 3))))))
                  17
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 0 (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 0))))
                        5
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 31)) 27
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 30 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 6))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 35 (Flapjack.Spt.ls 37)))
                        41
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) 35
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))
                      28
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 4)) (Flapjack.Spt.ls 7))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 30)) 39
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 24))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        28
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 32
                            (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 22
                            (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 30))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 0)))
                          23
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 32))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))) 7
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 6)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 6))) 32
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 4)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln) 27
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)))
                      40
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 7)) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))
                    2
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 3
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 5 (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 39
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 0 (Flapjack.Spt.ls 0)))
                        30
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln))))))
                3
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 31 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) Flapjack.Spt.ln)))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 6 Flapjack.Spt.ln) 37
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 4 Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 40
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        5
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 22
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        6
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 27))))))
                  13
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 32 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 35)) 31
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                      23
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 6))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 34 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 2
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))))
                    31
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 39
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))
                        2
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 3))) 3
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))))
                      32
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 31)) 23
                          (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 26
                            (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 24)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 28)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 37 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 24
                            (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 4
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 24))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5 Flapjack.Spt.ln) 37
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 4)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 32)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 Flapjack.Spt.ln) 23
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 35))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 37))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 40 (Flapjack.Spt.ls 6)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 6)) 39
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)))
                      31
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 38)) 3
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4))))))
                    40
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 31)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 22 Flapjack.Spt.ln) 31
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 4))))
                        22
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 34 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 23 Flapjack.Spt.ln) 35
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 6))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7)))))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 5)) 40
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        4
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 2)) 32
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 35))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 23
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        38
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))))))
                  11
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 30)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 27)) 23
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 37)))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) 40
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34))))))
                    22
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 6))))
                        5
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) 31
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 5)))))
                      24
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)) 37
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 31
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 5))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 27)))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 13)))
                          25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 4))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38
                            (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 0)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 7))) 34
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 6)) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3))))
                        1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 26 Flapjack.Spt.ln) 6 Flapjack.Spt.ln))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 27 (Flapjack.Spt.ls 0)) 8
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 1 (Flapjack.Spt.ls 0)))
                        23
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))))
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 22 (Flapjack.Spt.ls 36)) 25
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 4 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 8 Flapjack.Spt.ln) 4 Flapjack.Spt.ln))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 32 (Flapjack.Spt.ls 5)) 5
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7))))
                        32
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 6 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 22
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))))))
                5
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 33 (Flapjack.Spt.ls 0)) 6
                          (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        40
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 12)))
                          (Flapjack.Spt.ls 31))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 38 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        31
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 23
                            (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 27)))))
                      0
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 6 (Flapjack.Spt.ls 2)) 4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 29))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 34 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 37)) 5
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))))
                      7
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 36
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 23))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 22 (Flapjack.Spt.ls 6)) 6
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))
                    33
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 40
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))) 41
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)))
                      34
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 33)) 25
                          (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 26)))
                          2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 30)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 26
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 1)))))
                      37
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))
                        2
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 39
                            (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 4))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        40
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 31 (Flapjack.Spt.ls 32))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 25
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 38))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 0)))
                        3
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln) 41
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 40 (Flapjack.Spt.ls 0))))
                      33
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln) 26
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.ls 4)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 30 Flapjack.Spt.ln) 4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0))))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 6
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 25 Flapjack.Spt.ln) 6
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))
                      42
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 24 Flapjack.Spt.ln) 34
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 0
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        24
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 25 (Flapjack.Spt.ls 4)) 37
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 35 Flapjack.Spt.ln) 4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 35 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        7
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.ls 3))))
                    26
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 30 (Flapjack.Spt.ls 5)) 34
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 22))))
                        23
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 1)) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 40 (Flapjack.Spt.ls 5)) 6
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 Flapjack.Spt.ln))
                        39
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln) (Flapjack.Spt.ls 30)))))
                  14
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 25
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 0)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 27 (Flapjack.Spt.ls 39)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 8))) 41
                          Flapjack.Spt.ln)))
                    24
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 33 Flapjack.Spt.ln))
                      26
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)) 3
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        5
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 25)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 30 (Flapjack.Spt.ls 31))))
                      2
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 3))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 30))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 36))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 23))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 30
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)) 25
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 22 (Flapjack.Spt.ls 0)) 6
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 2 (Flapjack.Spt.ls 0))))
                      5
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 23 Flapjack.Spt.ln) 30
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.ls 2)))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.ls 34))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 29 (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 4 (Flapjack.Spt.ls 5)) 38
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 30))))
                        28
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))))))
                1
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 41
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 0)) Flapjack.Spt.ln))
                      5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln) 35
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 27 Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 1)) 38
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        27
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 38))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 34 (Flapjack.Spt.ls 4))))))
                  19
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 30
                            (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 0))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 33)) 4
                          (Flapjack.Spt.ls 5)))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 32 (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 8)))
                          6 (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 1 (Flapjack.Spt.ls 0)))))
                    6
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 37 (Flapjack.Spt.ls 5)))
                        1
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)) 5
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))))
                      30
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 7))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 24
                            (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 22)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 36 (Flapjack.Spt.ls 0)) 6
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 23))))
                      5
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 3))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 35
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        35
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 30)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        0
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 33))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 35))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 3 Flapjack.Spt.ln))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 38
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 5 Flapjack.Spt.ln)))
                      4
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 37)) 22
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 38
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 26
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 7)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 0)))))
                    37
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 6 (Flapjack.Spt.ls 6)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 14)))
                          6 (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 Flapjack.Spt.ln)))
                      7
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 36)) 4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34))))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 38
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))
                        27
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                          0 (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln))))
                    1
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 30
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 5)) 6
                          (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))
                        7
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 26
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))))
                  9
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 4))) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 2))))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 10))) 38
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 7))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 3
                          (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 31)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 12))) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 2)))))
                      22
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 1))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 35
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        32 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 36))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 4)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 11)))
                          26 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 34)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))) 6
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 33
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 5))) 35
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 30)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln) 30
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 29))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))
                      42
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 6)) 35
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0))))
                        24
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 39 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                          1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))))
                    4
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 38)) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 7 (Flapjack.Spt.ls 0)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                        5
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 3 Flapjack.Spt.ln))))))
                6
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3 (Flapjack.Spt.ls 1)) 2
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 2
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
                      4
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 (Flapjack.Spt.ls 2)) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln))
                        39
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 5
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)))
                          (Flapjack.Spt.ls 32))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 39 (Flapjack.Spt.ls 2))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        6
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 24
                            (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 28)))))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        5
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 39 (Flapjack.Spt.ls 30))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 35 Flapjack.Spt.ln))
                        32
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 38)) 34
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 4
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))))
                      26
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 33))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 37
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 23
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 27)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 5))))))
                    34
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 33
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0)))))
                      35
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 34)) 26
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 1)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 28)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 31)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        23
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 27 (Flapjack.Spt.ls 4))))
                      0
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 32 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 40
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 27))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 Flapjack.Spt.ln) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 32 (Flapjack.Spt.ls 33))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 0))))
                        5
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 27
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 22)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.ls 5)))
                        0
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 (Flapjack.Spt.ls 1))))
                      34
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 31 (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5))))))
                    42
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 26 (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 0)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 6)) 35
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 6
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        25
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 3 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 26 Flapjack.Spt.ln) 7
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 6))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        32
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 24 Flapjack.Spt.ln))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 4)) 35
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 23))))
                        3
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        3
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 31 (Flapjack.Spt.ls 22))))))
                  18
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 32 (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 1))))
                        6
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 30)) 26
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 4))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 29 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 2)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))))
                    25
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 0 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 34
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) 34
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
                      27
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 40
                          (Flapjack.Spt.bn Flapjack.Spt.ln
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 23))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        27
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6
                            (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 0)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 41
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 5))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 22
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 5))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 36
                            (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 1
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 4))))
                        5
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 22))) 31
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 2)) 26
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 23 (Flapjack.Spt.ls 5)) 2
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 0 (Flapjack.Spt.ls 1))))
                      38
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 (Flapjack.Spt.ls 6)) 31
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 4 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33))))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 35)) 22
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 30 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)))
                      2
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 29 (Flapjack.Spt.ls 6)) 3
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 31 (Flapjack.Spt.ls 1)))
                        4
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 1
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))))))
                2
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 7 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 39
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 2))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 30)) 5 Flapjack.Spt.ln) 36
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5 Flapjack.Spt.ln) (Flapjack.Spt.ls 28))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 39
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        28
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) 1 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 35 (Flapjack.Spt.ls 26))))))
                  15
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 2 (Flapjack.Spt.ls 4))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 31
                            (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 1))))
                        6
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 7)) 30
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 29)))))
                      22
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 33 (Flapjack.Spt.ls 2)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln) 2
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 5))))))
                    30
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 3
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)) 38 (Flapjack.Spt.ls 5)))
                      31
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 30)) 22
                          (Flapjack.Spt.ls 6))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 25
                            (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 23)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 38 (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 0)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 (Flapjack.Spt.ls 0)) 5 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 2))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        36
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 5 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 4
                            (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 31)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        5
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 Flapjack.Spt.ln) 22
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 34))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 3))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 38 (Flapjack.Spt.ls 5)))
                        2
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln) 3
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 4) Flapjack.Spt.ln)))
                      30
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 36)) 7
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 40
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 3))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 27 Flapjack.Spt.ln) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5))))))
                    38
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 22
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7)))
                          2 (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 2 Flapjack.Spt.ln)))
                      40
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 5)) 30
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 6 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 33 Flapjack.Spt.ln) 0
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 22 (Flapjack.Spt.ls 1)) 34
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5 (Flapjack.Spt.ls 39)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 32 (Flapjack.Spt.ls 5)) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))))
                      6
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 32 (Flapjack.Spt.ls 6)) 39
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2 (Flapjack.Spt.ls 1)))
                        28
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2)))
                          1 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 27 (Flapjack.Spt.ls 4)) 31
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
                      1
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 4)) 2
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 0 Flapjack.Spt.ln))
                        37
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 27
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))))
                  10
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 7))) 6
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 26)) 22
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 3))) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 3
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 5))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1
                          (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 5))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) 30
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 38))))
                      23
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 36
                          (Flapjack.Spt.ls 1)))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        30
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 34))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1
                          (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 26)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 8)))
                          24
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 33))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 5))))
                        2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 5))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 9))) 33
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 28)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)) 28
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5 (Flapjack.Spt.ls 1)) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                      39
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 26 Flapjack.Spt.ln) 33
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 4))))
                        22
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)))
                          26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 37)) 24
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 32 (Flapjack.Spt.ls 4)) 5
                          Flapjack.Spt.ln))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 31 (Flapjack.Spt.ls 0)) 40
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 2)))
                        31
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))))
                4
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 32 (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln) 37
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 1))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))
                        38
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 30 Flapjack.Spt.ln))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 37 Flapjack.Spt.ln) 41
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                        30
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2
                          (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 4)))))
                      39
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 5 (Flapjack.Spt.ls 0)) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        2
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 33
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 36)) 32
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1)))))
                      24
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 35
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 5
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 0 Flapjack.Spt.ln))))
                    32
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 4) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 Flapjack.Spt.ln))
                        0
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 5))) 39
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 4)))))
                      33
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 32)) 24
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 27
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 4)))
                          4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 27)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 29)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 2)) 5 Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 Flapjack.Spt.ln) 2
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4 (Flapjack.Spt.ls 26))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 4))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                        6
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 38
                            (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 3))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 2 Flapjack.Spt.ln) 4
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        38
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 7 (Flapjack.Spt.ls 31))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 Flapjack.Spt.ln) 33
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 2))))
                        1
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2 Flapjack.Spt.ln) 24
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 6 (Flapjack.Spt.ls 36))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 2)) 40
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 25))))
                      32
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln) 25
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 30))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          5 (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 0)))))
                    39
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 24 (Flapjack.Spt.ls 6)) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)))))
                      3
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 23 Flapjack.Spt.ln) 32
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5))))
                        23
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 35 (Flapjack.Spt.ls 4))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 5)) 36
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 3 Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 3 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 1
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))
                        30
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4)))
                          2 (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 22 Flapjack.Spt.ln))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 29 Flapjack.Spt.ln) 33
                          (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 2)))
                        22
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 0)) 40 Flapjack.Spt.ln))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 5 (Flapjack.Spt.ls 0)) 5
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        40
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 4
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))))
                  12
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 29))))
                        1
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)) 24
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))))
                    23
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 35)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) 32
                          (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 6)))))
                      25
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 38
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                        25
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 4)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 28))))
                        6
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 1 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 29))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 34
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 2)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 22)) 4
                          (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln) 24
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 23))))
                        4
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 0 (Flapjack.Spt.ls 2))))
                      36
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 2)) 4
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 4))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5))) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.ls 4)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 1))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 4 Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 3)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 37
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 29))))
                        27
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 39
                            (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 5)))
                          2 Flapjack.Spt.ln)))))
                0
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 5)) 5
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 38 (Flapjack.Spt.ls 1)) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 38 Flapjack.Spt.ln) 2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                        34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 26 Flapjack.Spt.ln))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 33 (Flapjack.Spt.ls 0)) 37
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 2
                            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))))
                        4
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 (Flapjack.Spt.ls 0)) 2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))
                      5
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 24))))))
                  16
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 1 (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 2))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 5)) 28
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 31 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))))
                    27
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 36
                            (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 1))))
                        0
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)) 36
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))
                      4
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 3))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 23 (Flapjack.Spt.ls 31)) 41
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 35 (Flapjack.Spt.ls 2)) 5
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 1 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln) 2
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 6)))))
                      0
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 0)) 1
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln))
                        5
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 9)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 34
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 1)) 4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                        34
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 1 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 26
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 7)))))
                      2
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 5 Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 36 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 41 (Flapjack.Spt.ls 32))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 34))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 37 (Flapjack.Spt.ls 2)))
                        1
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln) 36
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 0 (Flapjack.Spt.ls 5))))
                      28
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 35))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 39
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 27))))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 25
                            (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 5)))
                          5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1))))))
                    36
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 2)))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 1 Flapjack.Spt.ln)))
                      37
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 37)) 28
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 1 (Flapjack.Spt.ls 5)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 31
                            (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 29)))
                          4
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31)
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 33))))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 5)) 32
                          (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 30 Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 30 (Flapjack.Spt.ls 1)) 37
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 2)))
                        26
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 6))) 2
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 25 Flapjack.Spt.ln) 6
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 5 (Flapjack.Spt.ls 32)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 36 Flapjack.Spt.ln) 5
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln)))
                      5
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 35 Flapjack.Spt.ln)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6))))
                        35
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 5
                            (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 5)))
                          (Flapjack.Spt.ls 7)))))
                  8
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 5))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 34)))
                        1
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 3))) 37
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0
                          (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 2))))
                        4
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 9))) 28
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 6)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 0))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 34
                          (Flapjack.Spt.ls 40)))))))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 33 (Flapjack.Spt.ls 39)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 38)) 31
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))
                      23
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))))
                    41
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 34))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 39 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln) 39
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)))
                      32
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 35)) 23
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 40 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 27 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)))))
                  40
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 23))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
                        37
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 30
                            (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 25)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))) 37
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 39))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 30
                            (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 28))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)) 31
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 34))))))
                    25
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 27)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) 23 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 36)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) 40
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))))))
                  22
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 35
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 39 Flapjack.Spt.ln) 30 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 31 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 37 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                        40 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 25 (Flapjack.Spt.ls 31)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 30)) 23
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 28 (Flapjack.Spt.ls 39)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 25))) 39
                          Flapjack.Spt.ln)))
                    33
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 31 (Flapjack.Spt.ls 35)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 33)) 31
                          Flapjack.Spt.ln))
                      24
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 33 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 27)))
                          Flapjack.Spt.ln))))
                  31
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 39)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 40) Flapjack.Spt.ln) 38
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 39 Flapjack.Spt.ln) 29
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 25)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 31))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 23
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 26))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38
                            (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 33)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 32 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 27)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln)))
                      39
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 31
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        22
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 36 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) 22 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 29 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 39 (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                        31
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))
                          Flapjack.Spt.ln)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 29 (Flapjack.Spt.ls 35)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 34)) 27
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))))
                    37
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 35 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 37)) 35
                          Flapjack.Spt.ln))
                      28
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 37 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 23 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)))))
                  35
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln) 33
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 23))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 29)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 33
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 35))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 26
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 23))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 27
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 30))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)) 36
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 31)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 35
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        26 (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 37)) 26 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 33 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
                        35 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 36)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 35 Flapjack.Spt.ln)))
                    29
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 31)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)) 27 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 39)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 23)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))))))
                  26
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 39
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln) 34
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 35 Flapjack.Spt.ln) 25 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 27))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 41
                            (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 22))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                        41
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 34
                            (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 29)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 36)) 23
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)))
                      36
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 27
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 31 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 25 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 25 Flapjack.Spt.ln) 36
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                        27
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 36
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 31 (Flapjack.Spt.ls 37)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 36)) 29
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))))
                    40
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 37 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 39)) 38
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)))
                      30
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 33))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 39 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 25 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)))))
                  37
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                        35
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 28
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 23)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 35
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 37))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 25
                            (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 29
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 32))))))
                    23
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 33)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)) 38
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 37 Flapjack.Spt.ln) 28 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 38)) 28 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 35 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        37 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 28)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 36 (Flapjack.Spt.ls 37)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 23))) 37
                          Flapjack.Spt.ln)))
                    31
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 33)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) 29 Flapjack.Spt.ln))
                      22
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 31 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 25)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)))))))
                  28
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 41
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln) 36
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 37 Flapjack.Spt.ln) 27 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 23)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 29))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 24))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 36
                            (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 31)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln)))
                      38
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 22 Flapjack.Spt.ln) 29
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 34 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 27 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 27 Flapjack.Spt.ln) 38
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))
                        29
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 39
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 27 (Flapjack.Spt.ls 33)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 32)) 25
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 38 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 27))) 41
                          Flapjack.Spt.ln)))
                    35
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 33 (Flapjack.Spt.ls 37)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 35)) 33
                          Flapjack.Spt.ln))
                      26
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 35 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)))))
                  33
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 41 Flapjack.Spt.ln) 31
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 27)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 31
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 33))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 25)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 25
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 28))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 38))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) 34
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln)))
                      42
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 33
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
                        24 (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)) 24 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 31 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 41
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                        33 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))) 29
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 32
                            (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 29))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) 33
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)))))
                    27
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 29)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)) 25 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 37)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) 41
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))))))
                  24
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 37
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 32
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 33 Flapjack.Spt.ln) 23
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln) 41
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 40) Flapjack.Spt.ln) 22
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 25))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 22)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                        40
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 32
                            (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 27)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 28))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 41
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)))
                      34
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 36)) 25
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 29 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))))
                    29
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 23 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 23 Flapjack.Spt.ln) 34
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                        25
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 35
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 32 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 37)) 30
                          Flapjack.Spt.ln))
                      22
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 23))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))))
                    39
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 33))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 38 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln) 37
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)))
                      31
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 34)) 22
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 38 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 26 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)))))
                  38
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 22))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        36
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 24)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 36
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 38))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 29
                            (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 27))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)) 30
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 33))))))
                    24
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 26)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 22 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 34)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) 29
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 34
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 38 Flapjack.Spt.ln) 29 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 30 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 36 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        38 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 30)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 29)) 22
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 37 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 24))) 38
                          Flapjack.Spt.ln)))
                    32
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 30 (Flapjack.Spt.ls 34)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 32)) 30
                          Flapjack.Spt.ln))
                      23
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 32 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 26)))
                          Flapjack.Spt.ln))))
                  30
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln) 37
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 38 Flapjack.Spt.ln) 28 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 24)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 30))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 22
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 25))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 37
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 32)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 31 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln)))
                      40
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 30
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 35 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 28 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 33 (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                        30
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 40
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 26))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 28 (Flapjack.Spt.ls 34)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 33)) 26
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 40 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 28)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))))
                    36
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 29))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 34 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 36)) 34
                          Flapjack.Spt.ln))
                      27
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 36 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 22 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)))))
                  34
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln) 32
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 22))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 28)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 32
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 34))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 24
                            (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 22))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 26
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 29))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 37))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 35
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 30)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 34
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                        25 (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 28)) 25 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 32 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))) 40
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 33
                            (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 30))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) 34
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)))))
                    28
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 30)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)) 26 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 38)))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 22)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))))))
                  25
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 38
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln) 33
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 34 Flapjack.Spt.ln) 24 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 40) Flapjack.Spt.ln) 42
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 26))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 23)))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        39
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 33
                            (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 28)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 37)) 22
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)))
                      35
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 38)) 26
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 30 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))))
                    42
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 24 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 24 Flapjack.Spt.ln) 35
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                        26
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 37
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 28))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 30 (Flapjack.Spt.ls 36)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 35)) 28
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))))
                    38
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 31))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 36 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 38)) 36
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))
                      29
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 32))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 28 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 24 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)))))
                  36
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        34
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27
                            (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 22)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 30)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 34
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 36))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 27
                            (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 24))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) 28
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 31))))))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)) 37
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 36 Flapjack.Spt.ln) 27
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40) Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 36)) 27 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 34 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        36 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 27))) 41
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 32)))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 22))) 36
                          Flapjack.Spt.ln)))
                    30
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                          (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 32)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) 28 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 30 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 24)))
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)))))))
                  27
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 40
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln) 35
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 36 Flapjack.Spt.ln) 26 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 22)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 28))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 23))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 35
                            (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 30)))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 38)) 24
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln)))
                      37
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln) 28
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 33 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 30))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 26 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 26 Flapjack.Spt.ln) 37
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                        28
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 38
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 24))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 26 (Flapjack.Spt.ls 32)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 31)) 24
                          Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 39 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 26))) 40
                          Flapjack.Spt.ln)))
                    34
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 27))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 32 (Flapjack.Spt.ls 36)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 34)) 32
                          Flapjack.Spt.ln))
                      25
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 28))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 34 Flapjack.Spt.ln))
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))))
                  32
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 40 Flapjack.Spt.ln) 30
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 26)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 30
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 32))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 24)))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 24
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 27))))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 28))))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 33
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 28)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln)))
                      41
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 32
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                        23
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.bn (Flapjack.Spt.ls 38) Flapjack.Spt.ln))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) 23 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 30 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 40
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                        32
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))
                          Flapjack.Spt.ln))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))) 38
                        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) (Flapjack.Spt.ls 40)))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 31
                            (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 25))))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)) 32
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)))))
                    26
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 28)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 35)))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 39
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))))))
                  23
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 36
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 40 Flapjack.Spt.ln) 31
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 32 Flapjack.Spt.ln) 22
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 38 Flapjack.Spt.ln) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                        39 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 24))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                        38
                        (Flapjack.Spt.bn Flapjack.Spt.ln
                          (Flapjack.Spt.bs Flapjack.Spt.ln 31
                            (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 26)))))
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34))))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 35))
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 40 Flapjack.Spt.ln))
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln) 40
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)))
                      33
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 37)) 24
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 28 Flapjack.Spt.ln)
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))))
                    39
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn
                        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 25))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)))
                      42
                      (Flapjack.Spt.bs
                        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 22 (Flapjack.Spt.ls 39)) 32
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                        24
                        (Flapjack.Spt.bn
                          (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 34
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                          (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))))))))))))))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
