import InitECandidate.Proofs.FrontendStages.Loop.Translate266
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody282_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64]))

def loopBody282_1 : HolLoopProg 64 :=
.mark loopBody282_0

def loopBody282_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody282_3 : HolLoopProg 64 :=
.mark loopBody282_2

def loopBody282_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody282_5 : HolLoopProg 64 :=
.mark loopBody282_4

def loopBody282_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody282_7 : HolLoopProg 64 :=
.mark loopBody282_6

def loopBody282_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1, 2, 3, 4]

def loopBody282_9 : HolLoopProg 64 :=
.mark loopBody282_8

def loopBody282_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody282_11 : HolLoopProg 64 :=
.mark loopBody282_10

def loopBody282_12 : HolLoopProg 64 :=
.seq loopBody282_9 loopBody282_11

def loopBody282_13 : HolLoopProg 64 :=
.mark loopBody282_12

def loopBody282_14 : HolLoopProg 64 :=
.seq loopBody282_7 loopBody282_13

def loopBody282_15 : HolLoopProg 64 :=
.mark loopBody282_14

def loopBody282_16 : HolLoopProg 64 :=
.seq loopBody282_5 loopBody282_15

def loopBody282_17 : HolLoopProg 64 :=
.mark loopBody282_16

def loopBody282_18 : HolLoopProg 64 :=
.seq loopBody282_3 loopBody282_17

def loopBody282_19 : HolLoopProg 64 :=
.mark loopBody282_18

def loopBody282_20 : HolLoopProg 64 :=
.seq loopBody282_1 loopBody282_19

def loopBody282_21 : HolLoopProg 64 :=
.mark loopBody282_20

def output282 : Nat × List Nat × HolLoopProg 64 :=
  (346, [0], loopBody282_21)
end InitECandidate.Proofs.FrontendStages.Loop
