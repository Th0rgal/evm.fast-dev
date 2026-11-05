import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 770 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle770 : Option (Spt Nat) :=
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
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 29 (Flapjack.Spt.ls 25))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 29 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48))))
                    28
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 40))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 9) Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  7
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 10) Flapjack.Spt.ln) 39
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 57 (Flapjack.Spt.ls 23)) 9
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 42) 30 (Flapjack.Spt.ls 22))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 12 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 34)) 17
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 34 Flapjack.Spt.ln)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 9) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 6 (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 15))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 15 (Flapjack.Spt.ls 24)) 5
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 37 Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 14) (Flapjack.Spt.ls 5))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)))
                      32
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 22 (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 56) 0
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 41)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 6))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) (Flapjack.Spt.ls 11))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 43))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) (Flapjack.Spt.ls 53))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 4)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))) 11
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 46 Flapjack.Spt.ln) 13
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 22 Flapjack.Spt.ln) 31 Flapjack.Spt.ln) 5
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 39
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 53 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 14) Flapjack.Spt.ln) 43
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 14) (Flapjack.Spt.ls 12)))
                      4
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 29))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 13 Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 10 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 41)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 6)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 17) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 27)))
                      25 Flapjack.Spt.ln)
                    7
                    (Flapjack.Spt.bs Flapjack.Spt.ln 37
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 46)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 1)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 25 Flapjack.Spt.ln) (Flapjack.Spt.ls 26))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 46))))
                    23
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)) (Flapjack.Spt.ls 0))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.ls 12)) Flapjack.Spt.ln)))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))) 8
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 53 Flapjack.Spt.ln) 32
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 22 Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 16 Flapjack.Spt.ln) 9
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                      6
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 10)) 15
                        (Flapjack.Spt.bs Flapjack.Spt.ln 27
                          (Flapjack.Spt.bs Flapjack.Spt.ln 57 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 11)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 10)) 6
                        (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 33))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 12) (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 31 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 5)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 13) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 3)))
                      29 (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs Flapjack.Spt.ln 44
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 53)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 2))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln) 6
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 22 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 28)) 0
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 46 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)))
                      34
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 17 (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln) 11 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 45)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 15) Flapjack.Spt.ln) 33
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 27))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 46) 29 (Flapjack.Spt.ls 12))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 34 Flapjack.Spt.ln) 35
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 38))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 32 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                      22 Flapjack.Spt.ln)
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 52)))
                      33
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 38 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 1))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 27 (Flapjack.Spt.ls 23))
                        (Flapjack.Spt.ls 31))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11))))
                    26
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 59 Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  7
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 12) Flapjack.Spt.ln) 29
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 55 Flapjack.Spt.ln) 34
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 25 Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 32 (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 31)) 13
                        (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 59))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 8)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 12)) 18
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 43 (Flapjack.Spt.ls 35))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 34 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 47)) 6 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)))
                      7 (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))) 47
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 55) 23
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 39)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 4))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln) 4
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 30)) (Flapjack.Spt.ls 9))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln) (Flapjack.Spt.ls 6))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))) 10
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 12 (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln) 27 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 8
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 47)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 51 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 13) Flapjack.Spt.ln) 55
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 15) Flapjack.Spt.ln))
                      2
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 0))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 38 Flapjack.Spt.ln) 59
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 23 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 40))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 7)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 19) (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 26)))
                      12 Flapjack.Spt.ln)
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)) Flapjack.Spt.ln) 39
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 10)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 1)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 23 Flapjack.Spt.ln) (Flapjack.Spt.ls 28))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 10))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) (Flapjack.Spt.ls 55))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 3)) (Flapjack.Spt.ls 4))))
                  1
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))) 38
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 50 Flapjack.Spt.ln) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 11 Flapjack.Spt.ln) 7 Flapjack.Spt.ln) 3
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 32
                        (Flapjack.Spt.bs Flapjack.Spt.ln 24
                          (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) Flapjack.Spt.ln))
                      5
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 33))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 8))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 45 Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 28 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 43)) 4
                        (Flapjack.Spt.ls 35))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 15) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs Flapjack.Spt.ln 12 (Flapjack.Spt.ls 0)))
                      27 (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                    7
                    (Flapjack.Spt.bs Flapjack.Spt.ln 41
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 50)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 0))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 11) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 41))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 9))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 26)) 3
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 39 Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 20) (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)))
                      39
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 25 (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 26
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 43)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 0)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 46)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 59 (Flapjack.Spt.ls 25)) 35
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 44) 26 (Flapjack.Spt.ls 24))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 54 (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 36))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 37 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 42))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 12) (Flapjack.Spt.ls 23)))
                      Flapjack.Spt.ln)
                    7
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 17)))
                      30
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 8)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 27)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 1)))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 28 (Flapjack.Spt.ls 24))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 7 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 13))))
                    27
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 10) Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) Flapjack.Spt.ln) 37
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 56 (Flapjack.Spt.ls 22)) 14
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 27 Flapjack.Spt.ln)))
                    7
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 46 (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 14
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 26 Flapjack.Spt.ln)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 13) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 12) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 2 (Flapjack.Spt.ls 9)) 4
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 59 (Flapjack.Spt.ls 36))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 51 (Flapjack.Spt.ls 23)) 2
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 7 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 11)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)))
                      31 (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)))
                    12
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 11
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 5))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 25 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 7 (Flapjack.Spt.ls 42))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 31)) (Flapjack.Spt.ls 51))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)) (Flapjack.Spt.ls 5))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))) 36
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 45) 26 (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln)))
                    15
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln) 10 Flapjack.Spt.ln) 2
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 30
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 52 (Flapjack.Spt.ls 4)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 11) Flapjack.Spt.ln) 35
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                      3
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 28))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 39 Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 9))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 3)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 11) (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
                      24 Flapjack.Spt.ln)
                    6
                    (Flapjack.Spt.bs Flapjack.Spt.ln 36
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 45)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 7)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 17) 24 Flapjack.Spt.ln) (Flapjack.Spt.ls 9))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)) (Flapjack.Spt.ls 56))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 7) (Flapjack.Spt.ls 5)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln) 31
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))
                      40
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 51 Flapjack.Spt.ln) 16
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37) Flapjack.Spt.ln)))
                    17
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 25 Flapjack.Spt.ln) 29
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                      7
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 28)) 7
                        (Flapjack.Spt.bs Flapjack.Spt.ln 25
                          (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 6)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 15) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 13) (Flapjack.Spt.ls 9)))
                      6
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 7)) 2
                        (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 32))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 46) (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 30 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 7)) 3
                        (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 2)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 7) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 31)))
                      28 (Flapjack.Spt.bn (Flapjack.Spt.ls 9) Flapjack.Spt.ln))
                    10
                    (Flapjack.Spt.bs Flapjack.Spt.ln 43
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 51)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 40)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 14) Flapjack.Spt.ln) 5
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 16) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.ls 8))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 6) (Flapjack.Spt.ls 38))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 27)) 4
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 8 Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 9) (Flapjack.Spt.ls 3))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)))
                      33
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 8 (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)))
                    14
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln) 22
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 59) 9
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 44)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 2)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 41)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 26)) 7
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 45) 34 (Flapjack.Spt.ls 25))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 55 (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 37))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 39 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))
                      Flapjack.Spt.ln)
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 51)))
                      31
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 32 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 28)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 3))))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 26 (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.ls 30))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 16))))
                    25
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 43 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) Flapjack.Spt.ln)))
                  8
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln) 34
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44)))
                      41
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 54 Flapjack.Spt.ln) 11
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 24 Flapjack.Spt.ln)))
                    19
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 39 (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 29)) 36
                        (Flapjack.Spt.bs Flapjack.Spt.ln 30
                          (Flapjack.Spt.bs Flapjack.Spt.ln 58 (Flapjack.Spt.ls 1)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 18) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 7)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 3 (Flapjack.Spt.ls 36)) 3
                        (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 34))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 14) (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 11 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 8)) 18 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))
                      30 (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)))
                    11
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 18))) 45
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 54) 22
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 12))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln) 3
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 23 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 7))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 57 (Flapjack.Spt.ls 29)) (Flapjack.Spt.ls 41))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)))
                      35
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 15 (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln)))
                    16
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln) 25 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs Flapjack.Spt.ln 16
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 46)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 12)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 18) Flapjack.Spt.ln) 54
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                      0
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 28))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 47) 37 (Flapjack.Spt.ls 26))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 8 (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 22 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.ls 46))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 18 (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                      23 Flapjack.Spt.ln)
                    5
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 53)))
                      34
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 39 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 17)))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 22 Flapjack.Spt.ln) (Flapjack.Spt.ls 27))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 6 (Flapjack.Spt.ls 44))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) (Flapjack.Spt.ls 54))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln) (Flapjack.Spt.ls 2))))
                  0
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))) 37
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 10 Flapjack.Spt.ln) 29
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln)))
                    18
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 23 Flapjack.Spt.ln) 26 Flapjack.Spt.ln) 4
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 10
                        (Flapjack.Spt.bs Flapjack.Spt.ln 22
                          (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 5)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 20) Flapjack.Spt.ln) 59
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 10)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 31))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 7) 17 Flapjack.Spt.ln)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 27 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 42)) 5
                        (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 4)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 16) Flapjack.Spt.ln)
                        (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 29)))
                      26 (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                    9
                    (Flapjack.Spt.bs Flapjack.Spt.ln 38
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 8))))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 11) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 11)) 5
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 37))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 53 (Flapjack.Spt.ls 25)) 6
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 38 Flapjack.Spt.ln))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 18) (Flapjack.Spt.ls 7))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)))
                      9 (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 0 (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)))
                    13
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln) Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 57) 12
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 42)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 10)))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 6) Flapjack.Spt.ln) 32 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 0 (Flapjack.Spt.ls 24)) 10
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 43) 31 (Flapjack.Spt.ls 14))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 33 (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 6 (Flapjack.Spt.ls 35))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 29 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.ls 41))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 22)))
                      Flapjack.Spt.ln)
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 50)))
                      29
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 34 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26)
                          (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 16))))))))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))) 29
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 23 Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 53)))
                      44
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 50) 26
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 28)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 34 Flapjack.Spt.ln))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) (Flapjack.Spt.ls 55))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 51 (Flapjack.Spt.ls 35)) (Flapjack.Spt.ls 56))
                      Flapjack.Spt.ln)
                    33
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))) 28
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 33))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 44))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 42) 35
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 28 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43)) (Flapjack.Spt.ls 32))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 43)) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                    44
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)))
                      39 (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 26 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 52))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 45) 39 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln) (Flapjack.Spt.ls 59)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 27)) (Flapjack.Spt.ls 46))
                      Flapjack.Spt.ln)
                    23
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 26)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 25)) 33
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 44) 22 (Flapjack.Spt.ls 36))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 36 Flapjack.Spt.ln) 30
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)) 36
                        (Flapjack.Spt.ls 27)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))
                      25 (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49)))
                      40
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 22
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 24)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 30 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 56))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) (Flapjack.Spt.ls 33))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 31)) (Flapjack.Spt.ls 53))
                      Flapjack.Spt.ln)
                    28
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))
                      24 Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 39)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 29)) 37
                        (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 40))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 40 Flapjack.Spt.ln) 33
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 23 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)) 41
                        (Flapjack.Spt.ls 34))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.ls 39)) Flapjack.Spt.ln)
                      Flapjack.Spt.ln)
                    37
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))) 32
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 43
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 22 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 37))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 48))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 34 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.ls 54)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 23)) (Flapjack.Spt.ls 38))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 25)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 25 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 55) 30
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 40) (Flapjack.Spt.ls 32))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 34 Flapjack.Spt.ln) 31
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) 39 Flapjack.Spt.ln)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))) 27
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 51)))
                      42
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 46) 25
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 26)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 32 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 58))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) (Flapjack.Spt.ls 53))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 33)) (Flapjack.Spt.ls 55))
                      Flapjack.Spt.ln)
                    30
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))) 26
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 46)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 31)) 40
                        (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 42))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 50 Flapjack.Spt.ln) 54
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 25 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41)) (Flapjack.Spt.ls 37))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 57 (Flapjack.Spt.ls 41)) Flapjack.Spt.ln)
                      Flapjack.Spt.ln)
                    41
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))) 34
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 50))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 24))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 43) 37 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln) (Flapjack.Spt.ls 35)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 25)) (Flapjack.Spt.ls 40))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 30)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 57 (Flapjack.Spt.ls 23)) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 42) (Flapjack.Spt.ls 34))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 38 Flapjack.Spt.ln) 28
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)) 34
                        (Flapjack.Spt.ls 24)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)) Flapjack.Spt.ln) 23
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                    47
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47)))
                      37
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 22)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 28 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 54))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 47) 46 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 29)) (Flapjack.Spt.ls 50))
                      Flapjack.Spt.ln)
                    26
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))
                      22 Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 29)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 27)) 35
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 46) 25 (Flapjack.Spt.ls 38))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 45 Flapjack.Spt.ln) 32
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)) 38
                        (Flapjack.Spt.ls 31))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 53 (Flapjack.Spt.ls 37)) (Flapjack.Spt.ls 43))
                      Flapjack.Spt.ln)
                    39
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))) 30
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 55 (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 35))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 46))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 54) 59
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 31 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46)) (Flapjack.Spt.ls 41)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 36 Flapjack.Spt.ln))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 23)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln) 22 Flapjack.Spt.ln) 46
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 53) 28
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 38) (Flapjack.Spt.ls 30))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 32 Flapjack.Spt.ln) 27
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)) 31 Flapjack.Spt.ln))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))) 28
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 22 Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 52)))
                      43
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 24
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 27)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 33 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 59))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) (Flapjack.Spt.ls 54))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 34)) (Flapjack.Spt.ls 42))
                      Flapjack.Spt.ln)
                    31
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))) 27
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 41)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 32)) 41
                        (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 43))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 51) 55
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 27 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42)) (Flapjack.Spt.ls 39))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 58 (Flapjack.Spt.ls 42)) Flapjack.Spt.ln)
                      Flapjack.Spt.ln)
                    43
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))) 35
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 25 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 40))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 51))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 25))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 44) 38 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln) (Flapjack.Spt.ls 43)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 26)) (Flapjack.Spt.ls 45))
                      Flapjack.Spt.ln)
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 31)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 24)) 32
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 43) (Flapjack.Spt.ls 35))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 39 Flapjack.Spt.ln) 29
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)) 35
                        (Flapjack.Spt.ls 25)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46)) Flapjack.Spt.ln) 24
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)))
                      38
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 23)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 29 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 59 (Flapjack.Spt.ls 55))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)) (Flapjack.Spt.ls 41))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 30)) (Flapjack.Spt.ls 51))
                      Flapjack.Spt.ln)
                    27
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))
                      23 Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 37)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 28)) 36
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 47) 27 (Flapjack.Spt.ls 39))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 46 Flapjack.Spt.ln) 46
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 22 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)) 40
                        (Flapjack.Spt.ls 26))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.ls 38)) (Flapjack.Spt.ls 59))
                      Flapjack.Spt.ln)
                    36
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40))) 31
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 35 (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 36))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 47))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 55) (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 26 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.ls 33)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 37 Flapjack.Spt.ln))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 24)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln) 24 Flapjack.Spt.ln) 47
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 54) 29
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 39) (Flapjack.Spt.ls 31))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 33 Flapjack.Spt.ln) 24
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)) 32 Flapjack.Spt.ln)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))) 26
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 50)))
                      41
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 45) 23
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 25)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 31 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 57))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)) (Flapjack.Spt.ls 51))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 32)) (Flapjack.Spt.ls 54))
                      Flapjack.Spt.ln)
                    29
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)))
                      25 Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 30)) 38
                        (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 41))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 41 Flapjack.Spt.ln) 34
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)) (Flapjack.Spt.ls 29))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 40)) Flapjack.Spt.ln)
                      Flapjack.Spt.ln)
                    38
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))) 33
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 59
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 23 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 38))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 49))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 57 (Flapjack.Spt.ls 23))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 42) 29 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.ls 55)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 24)) (Flapjack.Spt.ls 39))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln) 27 Flapjack.Spt.ln)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 22)) 31
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 41) (Flapjack.Spt.ls 33))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 35 Flapjack.Spt.ln) 26
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)) 33
                        (Flapjack.Spt.ls 22)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44)) Flapjack.Spt.ln) 22
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                    45
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46)))
                      36 (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 27 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 53))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 46) 32 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 28)) (Flapjack.Spt.ls 41))
                      Flapjack.Spt.ln)
                    25
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)) 34
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 45) 24 (Flapjack.Spt.ls 37))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 37 Flapjack.Spt.ln) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)) 37
                        (Flapjack.Spt.ls 30))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 52 (Flapjack.Spt.ls 36)) (Flapjack.Spt.ls 57))
                      Flapjack.Spt.ln)
                    34
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38))) 29
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 54 (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 34))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 45))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 53) 36
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 30 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)) (Flapjack.Spt.ls 46)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 35 Flapjack.Spt.ln))
                      Flapjack.Spt.ln)
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 56 (Flapjack.Spt.ls 22)))
                      Flapjack.Spt.ln))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln) Flapjack.Spt.ln) 45
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 51) 27
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 37) (Flapjack.Spt.ls 29))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 31 Flapjack.Spt.ln) 25
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)) 30
                        Flapjack.Spt.ln)))))))))))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
