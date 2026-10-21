import InitECandidate.Proofs.FrontendStages.Loop.Translate385
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody401_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 64#64]))

def loopBody401_1 : HolLoopProg 64 :=
.mark loopBody401_0

def loopBody401_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody401_3 : HolLoopProg 64 :=
.mark loopBody401_2

def loopBody401_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody401_5 : HolLoopProg 64 :=
.mark loopBody401_4

def loopBody401_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody401_7 : HolLoopProg 64 :=
.mark loopBody401_6

def loopBody401_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody401_5 loopBody401_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody401_9 : HolLoopProg 64 :=
.mark loopBody401_8

def loopBody401_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody401_11 : HolLoopProg 64 :=
.mark loopBody401_10

def loopBody401_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody401_13 : HolLoopProg 64 :=
.mark loopBody401_12

def loopBody401_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 4#64)

def loopBody401_15 : HolLoopProg 64 :=
.mark loopBody401_14

def loopBody401_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 1)

def loopBody401_17 : HolLoopProg 64 :=
.mark loopBody401_16

def loopBody401_18 : HolLoopProg 64 :=
.seq loopBody401_17 loopBody401_13

def loopBody401_19 : HolLoopProg 64 :=
.mark loopBody401_18

def loopBody401_20 : HolLoopProg 64 :=
.seq loopBody401_19 loopBody401_13

def loopBody401_21 : HolLoopProg 64 :=
.mark loopBody401_20

def loopBody401_22 : HolLoopProg 64 :=
.seq loopBody401_15 loopBody401_21

def loopBody401_23 : HolLoopProg 64 :=
.mark loopBody401_22

def loopBody401_24 : HolLoopProg 64 :=
.seq loopBody401_13 loopBody401_23

def loopBody401_25 : HolLoopProg 64 :=
.mark loopBody401_24

def loopBody401_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 8#64)

def loopBody401_27 : HolLoopProg 64 :=
.mark loopBody401_26

def loopBody401_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 1

def loopBody401_29 : HolLoopProg 64 :=
.mark loopBody401_28

def loopBody401_30 : HolLoopProg 64 :=
.seq loopBody401_27 loopBody401_29

def loopBody401_31 : HolLoopProg 64 :=
.mark loopBody401_30

def loopBody401_32 : HolLoopProg 64 :=
.seq loopBody401_25 loopBody401_31

def loopBody401_33 : HolLoopProg 64 :=
.mark loopBody401_32

def loopBody401_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody401_33 loopBody401_13 (Flapjack.Spt.ln)

def loopBody401_35 : HolLoopProg 64 :=
.mark loopBody401_34

def loopBody401_36 : HolLoopProg 64 :=
.seq loopBody401_35 loopBody401_13

def loopBody401_37 : HolLoopProg 64 :=
.mark loopBody401_36

def loopBody401_38 : HolLoopProg 64 :=
.seq loopBody401_11 loopBody401_37

def loopBody401_39 : HolLoopProg 64 :=
.mark loopBody401_38

def loopBody401_40 : HolLoopProg 64 :=
.seq loopBody401_9 loopBody401_39

def loopBody401_41 : HolLoopProg 64 :=
.mark loopBody401_40

def loopBody401_42 : HolLoopProg 64 :=
.seq loopBody401_3 loopBody401_41

def loopBody401_43 : HolLoopProg 64 :=
.mark loopBody401_42

def loopBody401_44 : HolLoopProg 64 :=
.seq loopBody401_1 loopBody401_43

def loopBody401_45 : HolLoopProg 64 :=
.mark loopBody401_44

def loopBody401_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody401_47 : HolLoopProg 64 :=
.mark loopBody401_46

def loopBody401_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody401_49 : HolLoopProg 64 :=
.mark loopBody401_48

def loopBody401_50 : HolLoopProg 64 :=
.seq loopBody401_49 loopBody401_13

def loopBody401_51 : HolLoopProg 64 :=
.mark loopBody401_50

def loopBody401_52 : HolLoopProg 64 :=
.seq loopBody401_47 loopBody401_51

def loopBody401_53 : HolLoopProg 64 :=
.mark loopBody401_52

def loopBody401_54 : HolLoopProg 64 :=
.seq loopBody401_45 loopBody401_53

def loopBody401_55 : HolLoopProg 64 :=
.mark loopBody401_54

def output401 : Nat × List Nat × HolLoopProg 64 :=
  (465, [0], loopBody401_55)
end InitECandidate.Proofs.FrontendStages.Loop
