import Flapjack.Misc.Sptree

/-! Concrete register-colouring oracle for compiler entry name 622 (data only). -/
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open Flapjack

def oracle622 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 7 (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.ls 19))) 3
        (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 5 (Flapjack.Spt.bs Flapjack.Spt.ln 9 (Flapjack.Spt.ls 17))))
      1
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 6 (Flapjack.Spt.bs Flapjack.Spt.ln 10 (Flapjack.Spt.ls 18))) 2
        (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 16)))))
    0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 49 Flapjack.Spt.ln) 22
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 Flapjack.Spt.ln)))
                    26
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2)) (Flapjack.Spt.ls 30))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 35 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 39 (Flapjack.Spt.ls 41)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 37 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 37
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 41)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 30)) 0 Flapjack.Spt.ln))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) 34
                        (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 36))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 8))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 3))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 36) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 47)) Flapjack.Spt.ln)))
                  4
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 48 (Flapjack.Spt.ls 27)))
                      26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 42) (Flapjack.Spt.ls 34))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))) 2
                      (Flapjack.Spt.bs Flapjack.Spt.ln 46
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 36)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5)) 42
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 0 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 34)) (Flapjack.Spt.ls 26)) 3
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 0)) (Flapjack.Spt.ls 25))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 4))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 33)))
                      36 (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                    52
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 44))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 13) 32 (Flapjack.Spt.ls 49)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 25)) 46
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                    46
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 45
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 49)))
                      35 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 39)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 43) (Flapjack.Spt.ls 40))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 43 (Flapjack.Spt.ls 27))))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) (Flapjack.Spt.ls 39)) 52
                      (Flapjack.Spt.bs Flapjack.Spt.ln 7
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 1 (Flapjack.Spt.ls 29))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 31 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)) (Flapjack.Spt.ls 25))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 31 Flapjack.Spt.ln))))
                  27
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 24)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 45 (Flapjack.Spt.ls 38)))
                      40 (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 28)) 14
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 3
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 17) Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 8)) 36
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 24)) 49
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))
                      46 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 43)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 42 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 47 (Flapjack.Spt.ls 3))))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 1) Flapjack.Spt.ln) 6
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 24 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 40))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 24 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 31)) 1
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                  2
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.bn (Flapjack.Spt.ls 12) (Flapjack.Spt.ls 29)))
                      28 (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 29)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) 24
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 9) 38 (Flapjack.Spt.ls 45)))
                      4
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 26)) 42
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
                    22
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 41
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 45)))
                      26
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 34)) 0
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 6)) (Flapjack.Spt.ls 35))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 39 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) (Flapjack.Spt.ls 38)) 35
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 48 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 33 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)) 31 (Flapjack.Spt.ls 27))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 33 Flapjack.Spt.ln))))
                  46
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 42 (Flapjack.Spt.ls 39))) 52
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 25)) 16
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 34)) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 27)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 0)))
                      41 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 45)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 45 (Flapjack.Spt.ls 24)))
                      23
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 49 (Flapjack.Spt.ls 4))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 22))) 0
                      (Flapjack.Spt.bs Flapjack.Spt.ln 33
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 34)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 40
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 5))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 28 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 33)) 6 (Flapjack.Spt.ls 22))
                      2 (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 28))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 31)))
                      29 (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40))))
                    35
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 43))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 47))) 0
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 28)) 33
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
                    27
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 43
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 47)))
                      30 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 36)) 0 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 45)) (Flapjack.Spt.ls 38))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 41 (Flapjack.Spt.ls 24))))
                    3
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 40 Flapjack.Spt.ln))
                      46
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln) 30
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 23))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 29 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) (Flapjack.Spt.ls 23))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 29 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 2))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 47 (Flapjack.Spt.ls 35)))
                      46 (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 26))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 29
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 15) 30 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 7)) 48
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 47 (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                      36 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 41)) Flapjack.Spt.ln)))
                  22
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 39 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 45 (Flapjack.Spt.ls 23))))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 31)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.bs (Flapjack.Spt.ls 19) 28 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 38)) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln)))
                    4
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 29)) 0 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.bn (Flapjack.Spt.ls 17) (Flapjack.Spt.ls 23)))
                      30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))) 3
                      (Flapjack.Spt.bs Flapjack.Spt.ln 5 (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 37))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 43)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 22)) 39
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 5))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 39
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 43)))
                      22 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 32)) 0 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 42)) (Flapjack.Spt.ls 32))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 37 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 35 Flapjack.Spt.ln))
                      30
                      (Flapjack.Spt.bs Flapjack.Spt.ln 10
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 22))))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 2 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 32 Flapjack.Spt.ln)))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)) (Flapjack.Spt.ls 31))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 34 Flapjack.Spt.ln))))
                  52
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 43 (Flapjack.Spt.ls 40)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 35 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 35
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 40)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 29)) 13 Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 35))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)))
                    2
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 28)) 52
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 35) Flapjack.Spt.ln))
                      52 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 46)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 47 (Flapjack.Spt.ls 26)))
                      25
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 50 (Flapjack.Spt.ls 33))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 24)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 2
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 35)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) 41
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 0)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 23 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 4)) (Flapjack.Spt.ls 24))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.ls 0)) (Flapjack.Spt.ls 23))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.bn (Flapjack.Spt.ls 9) (Flapjack.Spt.ls 32)))
                      33 (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))))
                    46
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 24 Flapjack.Spt.ln)
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 5))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 12) 34 (Flapjack.Spt.ls 48)))
                      2
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 23)) 45
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))
                    35
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 5
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 48)))
                      31 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 38)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 42) (Flapjack.Spt.ls 37))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 42 (Flapjack.Spt.ls 26))))
                    4
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)) (Flapjack.Spt.ls 41)) 41
                      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 0) Flapjack.Spt.ln) 31
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 4 (Flapjack.Spt.ls 0))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 27 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)) (Flapjack.Spt.ls 0))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 30 Flapjack.Spt.ln))))
                  22
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)))
                      39 (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 3 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 27))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 30
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 16) 31 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 31)) 49
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 22)) 48
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                      37 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 42)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 5))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 43 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 46 (Flapjack.Spt.ls 29))))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 9
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 0 (Flapjack.Spt.ls 30)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 26 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 39))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 22 Flapjack.Spt.ln)))
                    3
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 30)) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                  3
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.ls 0)))
                      31
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 0 (Flapjack.Spt.ls 38))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 17 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 40))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 22
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 37 (Flapjack.Spt.ls 44)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 24)) 40 Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 40
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 44)))
                      25
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 33)) 0
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 43)) (Flapjack.Spt.ls 34))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 38 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 36 Flapjack.Spt.ln))
                      31
                      (Flapjack.Spt.bs Flapjack.Spt.ln 3
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 24)))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 30 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)) (Flapjack.Spt.ls 29))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 32 Flapjack.Spt.ln))))
                  35
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 44 (Flapjack.Spt.ls 3)))
                      41
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 31 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 4 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 23)) 15
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 31
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 18) 27 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 33)) 52
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 6))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 26)) 50
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 2)))
                      40 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 44)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 1))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 44 (Flapjack.Spt.ls 22)))
                      22
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 48 (Flapjack.Spt.ls 31))))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 11 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 41))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 26 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 32)) 0 Flapjack.Spt.ln) 0
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.bn (Flapjack.Spt.ls 18) (Flapjack.Spt.ls 30)))
                      35 (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))))
                    27
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 30)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 52 (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 32))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 46))) 3
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 27)) 43
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2))))
                    26
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 42
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 46)))
                      27 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 35)) 0 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 44)) (Flapjack.Spt.ls 36))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 40 (Flapjack.Spt.ls 22))))
                    0
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 2)) (Flapjack.Spt.ls 37)) 36
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 28))))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 43
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 25 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 35)) 1 (Flapjack.Spt.ls 28))
                      4
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 0))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 27 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 3))
                        (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 34)))
                      37 (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 24))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 45))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)) 27
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 14) 33 Flapjack.Spt.ln))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 29)) 47
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
                    52
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 46 (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln)) 29
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 40)) Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 39) (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 41 Flapjack.Spt.ln))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 44 (Flapjack.Spt.ls 28))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 4)) (Flapjack.Spt.ls 43))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 35
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.ls 25)))))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 2)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 37)) 3
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 7))))
                    0
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 23)) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)) Flapjack.Spt.ln)))
                  0
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 49 (Flapjack.Spt.ls 28)))
                      27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))) 4
                      (Flapjack.Spt.bs Flapjack.Spt.ln 12
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 38))))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 6) 41 (Flapjack.Spt.ls 42)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 38 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 38
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 42)))
                      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 32 (Flapjack.Spt.ls 2)) 0 Flapjack.Spt.ln)))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 41)) (Flapjack.Spt.ls 33))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 36 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 34 Flapjack.Spt.ln)) 27
                      (Flapjack.Spt.bs Flapjack.Spt.ln 8
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 50 Flapjack.Spt.ln))))))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 49) (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.ls 27)))
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 31 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 28) (Flapjack.Spt.ls 38))) 30
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)) 50 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 32 Flapjack.Spt.ln)))
                    27
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)) (Flapjack.Spt.ls 27)) 41
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln) 30
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 48 (Flapjack.Spt.ls 29)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 34)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 32)) 49 Flapjack.Spt.ln))
                    27
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 24)) 50
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 42)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 39) Flapjack.Spt.ln) 36
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
                    30
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn (Flapjack.Spt.ls 45) (Flapjack.Spt.ls 38)))))
                  35
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 42)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 40)) (Flapjack.Spt.ls 26)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 31))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln))
                      30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 40 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47)) (Flapjack.Spt.ls 36))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 40 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn (Flapjack.Spt.ls 36) (Flapjack.Spt.ls 45)))
                      46 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 26)) 40 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 42 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 33)) Flapjack.Spt.ln))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 45) (Flapjack.Spt.ls 24)) 39
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32))))
                    46
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 24) (Flapjack.Spt.ls 33))) 23
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 46)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 44))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 27 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 50 (Flapjack.Spt.ls 35))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 26 Flapjack.Spt.ln))
                      36 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln) 24
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 40) 44 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 44 (Flapjack.Spt.ls 26)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))) 52
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 25)) 45 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 46 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 38)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 24)) Flapjack.Spt.ln) 29
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 27)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 41) (Flapjack.Spt.ls 33)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 38)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 36)) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 23))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln))
                      22 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 46)) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 36 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43)) (Flapjack.Spt.ls 32))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 36 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn (Flapjack.Spt.ls 32) (Flapjack.Spt.ls 41)))
                      29
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 35 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 38 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 29)) Flapjack.Spt.ln)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 47) (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.ls 24)))
                      41 (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 34))))
                    52
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 26) (Flapjack.Spt.ls 35))) 26
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)) 48 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 30 Flapjack.Spt.ln)))
                    22
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 23 Flapjack.Spt.ln))
                      46 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln) 26
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 42) 46 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 46 (Flapjack.Spt.ls 28)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 32)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 30)) 47 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 48 (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 39 (Flapjack.Spt.ls 40))
                        Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 40) (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)) 33
                      (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27))))
                    26
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 43) (Flapjack.Spt.ls 35)))))
                  22
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 40)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 38)) (Flapjack.Spt.ls 22)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 29))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln))
                      26
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)) (Flapjack.Spt.ls 22)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 38 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)) (Flapjack.Spt.ls 34))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 38 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn (Flapjack.Spt.ls 34) (Flapjack.Spt.ls 43)))
                      36 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 22)) 38 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 40 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 31)) Flapjack.Spt.ln))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 42) Flapjack.Spt.ln) 46
                      (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30))))
                    35
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 31)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)))))
                  52
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 44)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 42))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 23 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 48 (Flapjack.Spt.ls 33))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 22 Flapjack.Spt.ln))
                      35 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln) 22
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 42 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49)) (Flapjack.Spt.ls 38))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 42 (Flapjack.Spt.ls 22)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))) 40
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 28)) 43 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 33 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 35)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 22)) Flapjack.Spt.ln) 28
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 50)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 46 (Flapjack.Spt.ls 24)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 50 (Flapjack.Spt.ls 31)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 36)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 34)) 52 Flapjack.Spt.ln))
                    46
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 27)) 52
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 27) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 44)) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 52)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 34 Flapjack.Spt.ln)))
                    46
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41)) (Flapjack.Spt.ls 30))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 34 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 30) (Flapjack.Spt.ls 39))) 28
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 31 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 35 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 23)) Flapjack.Spt.ln))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 48) (Flapjack.Spt.bs Flapjack.Spt.ln 23 (Flapjack.Spt.ls 26)))
                      52 (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 35))))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 27) (Flapjack.Spt.ls 36))) 27
                      (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)) 49 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 31 Flapjack.Spt.ln)))
                    26
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)) (Flapjack.Spt.ls 25)) 40
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 33) Flapjack.Spt.ln) 27
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 47 (Flapjack.Spt.ls 23)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 33)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 31)) 48 Flapjack.Spt.ln))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 38 (Flapjack.Spt.ls 22)) 49
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 24) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 43 (Flapjack.Spt.ls 41)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 41) Flapjack.Spt.ln) 34
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28))))
                    27
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 44) (Flapjack.Spt.ls 36)))))
                  27
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 41)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 39)) (Flapjack.Spt.ls 24)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 30))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 32) Flapjack.Spt.ln))
                      27
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49)) (Flapjack.Spt.ls 24)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 39 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46)) (Flapjack.Spt.ls 35))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 39 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn (Flapjack.Spt.ls 35) (Flapjack.Spt.ls 44)))
                      37 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 24)) 39 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 27) 41 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 43)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 34 (Flapjack.Spt.ls 32)) Flapjack.Spt.ln))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 44) (Flapjack.Spt.ls 22)) 38
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 31))))
                    36
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 23) (Flapjack.Spt.ls 32))) 22
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 45)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 43))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 23) 25 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 34))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 36) 24 Flapjack.Spt.ln))
                      29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 29) Flapjack.Spt.ln) 23
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 39) 43 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 43 (Flapjack.Spt.ls 24)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48))) 41
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 32 (Flapjack.Spt.ls 23)) 33 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 32) 45 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 47)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 36)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 23)) Flapjack.Spt.ln) 35
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 26)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 40) (Flapjack.Spt.ls 30)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 37)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 35)) Flapjack.Spt.ln))
                    52
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 39 (Flapjack.Spt.ls 28))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 28) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 45)) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 31) 35 Flapjack.Spt.ln)))
                    52
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42)) (Flapjack.Spt.ls 31))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 35 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 31) (Flapjack.Spt.ls 40))) 35
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 42))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 28) 37 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 39)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 31 (Flapjack.Spt.ls 25)) Flapjack.Spt.ln)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.ls 46) (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 22)))
                      40 (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 33))))
                    41
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 25) (Flapjack.Spt.ls 34))) 25
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 32)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) 47 Flapjack.Spt.ln)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 29 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 36))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 28 Flapjack.Spt.ln))
                      37 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29)))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 31) Flapjack.Spt.ln) 25
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 41) 45 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 34) 45 (Flapjack.Spt.ls 27)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 31)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 35 (Flapjack.Spt.ls 29)) 46 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 35) 47
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 22) (Flapjack.Spt.ls 49)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 41 (Flapjack.Spt.ls 39)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 37 (Flapjack.Spt.ls 25)) Flapjack.Spt.ln) 32
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
                    22
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 28)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 42) (Flapjack.Spt.ls 34)))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 39)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 37)) Flapjack.Spt.ln))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 42 (Flapjack.Spt.ls 25))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 30) Flapjack.Spt.ln))
                      25 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 49 (Flapjack.Spt.ls 47)) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 33) 37 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 44)) (Flapjack.Spt.ls 33))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 26) 37 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn (Flapjack.Spt.ls 33) (Flapjack.Spt.ls 42)))
                      33 (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 37 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 25) 39 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 41)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 33 (Flapjack.Spt.ls 30)) Flapjack.Spt.ln))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 43) Flapjack.Spt.ln) 37
                      (Flapjack.Spt.bs Flapjack.Spt.ln 28 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 29))))
                    31
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 30)))
                      (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 37)))))
                  46
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 43)
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 41)) (Flapjack.Spt.ls 28)))
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 47 (Flapjack.Spt.ls 32))
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln))
                      31 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))))
                (Flapjack.Spt.bs
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln)
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 37) 41 Flapjack.Spt.ln)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 48)) (Flapjack.Spt.ls 37))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 41 Flapjack.Spt.ln))))
                  22
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bs Flapjack.Spt.ln 25 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))) 39
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 30 (Flapjack.Spt.ls 27)) 42 Flapjack.Spt.ln))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 30) 43 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 45)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 36 (Flapjack.Spt.ls 34)) Flapjack.Spt.ln)))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 34) Flapjack.Spt.ln) 31
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49)))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 45 (Flapjack.Spt.ls 22)))
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 38) 49 (Flapjack.Spt.ls 25)))))
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 35)
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 33)) 36 Flapjack.Spt.ln))
                    35
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 40 (Flapjack.Spt.ls 26)) 36
                        (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 44 (Flapjack.Spt.ls 43)) Flapjack.Spt.ln))))
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bs
                    (Flapjack.Spt.bn (Flapjack.Spt.ls 51)
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 49))
                        (Flapjack.Spt.bs (Flapjack.Spt.ls 29) 33 Flapjack.Spt.ln)))
                    35
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 40)) (Flapjack.Spt.ls 29)) 52
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 33 Flapjack.Spt.ln))))
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bs
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 29) (Flapjack.Spt.ls 37))) 31
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 32 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 46))))
                    (Flapjack.Spt.bn
                      (Flapjack.Spt.bs (Flapjack.Spt.ls 24) 34 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 38)))
                      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 29 (Flapjack.Spt.ls 28))
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 50)))))))))))))

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
