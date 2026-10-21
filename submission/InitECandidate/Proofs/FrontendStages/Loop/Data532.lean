import InitECandidate.Proofs.FrontendStages.Loop.Translate516
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody532_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 160#64]))

def loopBody532_1 : HolLoopProg 64 :=
.mark loopBody532_0

def loopBody532_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody532_3 : HolLoopProg 64 :=
.mark loopBody532_2

def loopBody532_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody532_5 : HolLoopProg 64 :=
.mark loopBody532_4

def loopBody532_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody532_7 : HolLoopProg 64 :=
.mark loopBody532_6

def loopBody532_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.RegImm.reg 3) loopBody532_5 loopBody532_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody532_9 : HolLoopProg 64 :=
.mark loopBody532_8

def loopBody532_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody532_11 : HolLoopProg 64 :=
.mark loopBody532_10

def loopBody532_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody532_13 : HolLoopProg 64 :=
.mark loopBody532_12

def loopBody532_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
        Flapjack.HolLoopExp.const 24#64]))

def loopBody532_15 : HolLoopProg 64 :=
.mark loopBody532_14

def loopBody532_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody532_17 : HolLoopProg 64 :=
.mark loopBody532_16

def loopBody532_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 387) ([2]) (some (2, loopBody532_17, loopBody532_13, (Flapjack.Spt.ln)))

def loopBody532_19 : HolLoopProg 64 :=
.mark loopBody532_18

def loopBody532_20 : HolLoopProg 64 :=
.seq loopBody532_19 loopBody532_13

def loopBody532_21 : HolLoopProg 64 :=
.mark loopBody532_20

def loopBody532_22 : HolLoopProg 64 :=
.seq loopBody532_15 loopBody532_21

def loopBody532_23 : HolLoopProg 64 :=
.mark loopBody532_22

def loopBody532_24 : HolLoopProg 64 :=
.seq loopBody532_13 loopBody532_23

def loopBody532_25 : HolLoopProg 64 :=
.mark loopBody532_24

def loopBody532_26 : HolLoopProg 64 :=
.seq loopBody532_13 loopBody532_25

def loopBody532_27 : HolLoopProg 64 :=
.mark loopBody532_26

def loopBody532_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody532_27 loopBody532_13 (Flapjack.Spt.ln)

def loopBody532_29 : HolLoopProg 64 :=
.mark loopBody532_28

def loopBody532_30 : HolLoopProg 64 :=
.seq loopBody532_29 loopBody532_13

def loopBody532_31 : HolLoopProg 64 :=
.mark loopBody532_30

def loopBody532_32 : HolLoopProg 64 :=
.seq loopBody532_11 loopBody532_31

def loopBody532_33 : HolLoopProg 64 :=
.mark loopBody532_32

def loopBody532_34 : HolLoopProg 64 :=
.seq loopBody532_9 loopBody532_33

def loopBody532_35 : HolLoopProg 64 :=
.mark loopBody532_34

def loopBody532_36 : HolLoopProg 64 :=
.seq loopBody532_3 loopBody532_35

def loopBody532_37 : HolLoopProg 64 :=
.mark loopBody532_36

def loopBody532_38 : HolLoopProg 64 :=
.seq loopBody532_1 loopBody532_37

def loopBody532_39 : HolLoopProg 64 :=
.mark loopBody532_38

def loopBody532_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody532_41 : HolLoopProg 64 :=
.mark loopBody532_40

def loopBody532_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody532_43 : HolLoopProg 64 :=
.mark loopBody532_42

def loopBody532_44 : HolLoopProg 64 :=
.seq loopBody532_43 loopBody532_13

def loopBody532_45 : HolLoopProg 64 :=
.mark loopBody532_44

def loopBody532_46 : HolLoopProg 64 :=
.seq loopBody532_41 loopBody532_45

def loopBody532_47 : HolLoopProg 64 :=
.mark loopBody532_46

def loopBody532_48 : HolLoopProg 64 :=
.seq loopBody532_39 loopBody532_47

def loopBody532_49 : HolLoopProg 64 :=
.mark loopBody532_48

def output532 : Nat × List Nat × HolLoopProg 64 :=
  (596, [], loopBody532_49)
end InitECandidate.Proofs.FrontendStages.Loop
