import InitECandidate.Proofs.WordStages.Optimize688
import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SmallSsaKernelComputation
import InitECandidate.Proofs.CompilerStages
import InitECandidate.Proofs.WordStages.Source704
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def optimizedBody704_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(14, 14), (2, 2), (26, 0), (4, 4), (6, 6), (8, 8), (10, 10), (12, 12), (16, 16), (18, 18), (20, 20), (22, 22),
    (24, 24)]

def optimizedBody704_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 0 0#64)

def optimizedBody704_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0)]

def optimizedBody704_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 2 2 14 0))

def optimizedBody704_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0), (16, 16), (4, 4), (2, 2)]

def optimizedBody704_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 4 4 16 0))

def optimizedBody704_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0), (18, 18), (6, 6), (4, 4)]

def optimizedBody704_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 6 6 18 0))

def optimizedBody704_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0), (20, 20), (8, 8), (6, 6)]

def optimizedBody704_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 8 8 20 0))

def optimizedBody704_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0), (22, 22), (10, 10), (8, 8)]

def optimizedBody704_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 10 10 22 0))

def optimizedBody704_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 0), (24, 24), (12, 12), (10, 10)]

def optimizedBody704_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 12 12 24 0))

def optimizedBody704_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (6, 6), (8, 8), (10, 10), (12, 12), (14, 0)]

def optimizedBody704_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 26 [2, 4, 6, 8, 10, 12, 14]

def optimizedBody704_16 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_14 optimizedBody704_15

def optimizedBody704_17 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_13 optimizedBody704_16

def optimizedBody704_18 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_12 optimizedBody704_17

def optimizedBody704_19 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_11 optimizedBody704_18

def optimizedBody704_20 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_10 optimizedBody704_19

def optimizedBody704_21 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_9 optimizedBody704_20

def optimizedBody704_22 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_8 optimizedBody704_21

def optimizedBody704_23 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_7 optimizedBody704_22

def optimizedBody704_24 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_6 optimizedBody704_23

def optimizedBody704_25 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_5 optimizedBody704_24

def optimizedBody704_26 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_4 optimizedBody704_25

def optimizedBody704_27 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_3 optimizedBody704_26

def optimizedBody704_28 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_2 optimizedBody704_27

def optimizedBody704_29 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_1 optimizedBody704_28

def optimizedBody704_30 : WordLangProgHOL (BitVec 64) :=
.seq optimizedBody704_0 optimizedBody704_29

def oracle704 : Option (Spt Nat) :=
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
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls 11) (Flapjack.Spt.ls 3)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 5) 1 (Flapjack.Spt.ls 3))
              (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 5 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 9 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 6)))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 11) 7 (Flapjack.Spt.ls 9))
              (Flapjack.Spt.bs (Flapjack.Spt.ls 10) 6 (Flapjack.Spt.bs Flapjack.Spt.ln 8 (Flapjack.Spt.ls 12))))
            (Flapjack.Spt.bn (Flapjack.Spt.ls 10) (Flapjack.Spt.ls 2)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 12 (Flapjack.Spt.ls 2))
              (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 4 (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 5))))
            (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.bs Flapjack.Spt.ln 13 (Flapjack.Spt.ls 0))))))
      Flapjack.Spt.ln))
def optimized704 : Nat × Nat × WordLangProgHOL (BitVec 64) :=
(704, 13, optimizedBody704_30)
theorem optimize704_eq : WordToWord.fullCompileSingleWith
  RegAlloc.regAllocExecutable riscvConfig.twoRegArith
  (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
  RiscVConfig.pancakeRiscVBackendConfig.wordToWordConf.regAlg
  riscvConfig (source704, oracle704) = optimized704 := by
  rw [InitECandidate.Proofs.CompilerStages.fullCompile_expanded]
  dsimp only
  rw [InitECandidate.Proofs.SmallSsaKernelComputation.fullSsaStructural_eq]
  kernel_rfl
#print axioms optimize704_eq
end InitECandidate.Proofs.WordStages
