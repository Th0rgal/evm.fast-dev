import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.StackAnalysis.Data704
import InitECandidate.Proofs.CompilerComputation
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.BackendStages
def stackBody704_0 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc 0

def stackBody704_1 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.or 13 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.reg 0)))

def stackBody704_2 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst (Flapjack.Compiler.Encoders.Asm.HolInst.const 0 0#64)

def stackBody704_3 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_4 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 1 1 7 0))

def stackBody704_5 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_6 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 2 2 8 0))

def stackBody704_7 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_8 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 3 3 9 0))

def stackBody704_9 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_10 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 4 4 10 0))

def stackBody704_11 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_12 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 5 5 11 0))

def stackBody704_13 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.skip

def stackBody704_14 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith (Flapjack.Compiler.Encoders.Asm.HolArith.addCarry 6 6 12 0))

def stackBody704_15 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.inst
  (Flapjack.Compiler.Encoders.Asm.HolInst.arith
    (Flapjack.Compiler.Encoders.Asm.HolArith.binop Flapjack.BinOp.or 7 0
      (Flapjack.Compiler.Encoders.Asm.HolRegImm.reg 0)))

def stackBody704_16 : StackLang.HolProg 64 :=
Flapjack.Compiler.Backend.StackLang.Prog.ret 13

def stackBody704_17 : StackLang.HolProg 64 :=
.seq stackBody704_15 stackBody704_16

def stackBody704_18 : StackLang.HolProg 64 :=
.seq stackBody704_14 stackBody704_17

def stackBody704_19 : StackLang.HolProg 64 :=
.seq stackBody704_13 stackBody704_18

def stackBody704_20 : StackLang.HolProg 64 :=
.seq stackBody704_12 stackBody704_19

def stackBody704_21 : StackLang.HolProg 64 :=
.seq stackBody704_11 stackBody704_20

def stackBody704_22 : StackLang.HolProg 64 :=
.seq stackBody704_10 stackBody704_21

def stackBody704_23 : StackLang.HolProg 64 :=
.seq stackBody704_9 stackBody704_22

def stackBody704_24 : StackLang.HolProg 64 :=
.seq stackBody704_8 stackBody704_23

def stackBody704_25 : StackLang.HolProg 64 :=
.seq stackBody704_7 stackBody704_24

def stackBody704_26 : StackLang.HolProg 64 :=
.seq stackBody704_6 stackBody704_25

def stackBody704_27 : StackLang.HolProg 64 :=
.seq stackBody704_5 stackBody704_26

def stackBody704_28 : StackLang.HolProg 64 :=
.seq stackBody704_4 stackBody704_27

def stackBody704_29 : StackLang.HolProg 64 :=
.seq stackBody704_3 stackBody704_28

def stackBody704_30 : StackLang.HolProg 64 :=
.seq stackBody704_2 stackBody704_29

def stackBody704_31 : StackLang.HolProg 64 :=
.seq stackBody704_1 stackBody704_30

def stackBody704_32 : StackLang.HolProg 64 :=
.seq stackBody704_0 stackBody704_31

def function704 (bitmapPrefix : AppList (BitVec 64)) : StackLang.HolProg 64 × Nat × (AppList (BitVec 64) × Nat) :=
(stackBody704_32, 0, bitmapPrefix, 3158)
theorem function704_eq (bitmapPrefix : AppList (BitVec 64)) : WordToStack.Native.compileProgNative riscvConfig false InitECandidate.Proofs.StackAnalysis.optimized704.2.2 InitECandidate.Proofs.StackAnalysis.optimized704.2.1 (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (bitmapPrefix, 3158) = function704 bitmapPrefix := by
  kernel_rfl
#print axioms function704_eq
end InitECandidate.Proofs.BackendStages
