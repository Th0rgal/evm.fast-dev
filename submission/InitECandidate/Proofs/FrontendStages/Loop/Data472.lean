import InitECandidate.Proofs.FrontendStages.Loop.Translate456
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody472_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody472_1 : HolLoopProg 64 :=
.mark loopBody472_0

def loopBody472_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody472_3 : HolLoopProg 64 :=
.mark loopBody472_2

def loopBody472_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody472_5 : HolLoopProg 64 :=
.mark loopBody472_4

def loopBody472_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody472_7 : HolLoopProg 64 :=
.mark loopBody472_6

def loopBody472_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody472_9 : HolLoopProg 64 :=
.mark loopBody472_8

def loopBody472_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody472_11 : HolLoopProg 64 :=
.mark loopBody472_10

def loopBody472_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 3 (Flapjack.RegImm.reg 4) loopBody472_9 loopBody472_11 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody472_13 : HolLoopProg 64 :=
.mark loopBody472_12

def loopBody472_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody472_15 : HolLoopProg 64 :=
.mark loopBody472_14

def loopBody472_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 48#64]),
      Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody472_17 : HolLoopProg 64 :=
.mark loopBody472_16

def loopBody472_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 2 2

def loopBody472_19 : HolLoopProg 64 :=
.mark loopBody472_18

def loopBody472_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody472_21 : HolLoopProg 64 :=
.mark loopBody472_20

def loopBody472_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody472_23 : HolLoopProg 64 :=
.mark loopBody472_22

def loopBody472_24 : HolLoopProg 64 :=
.seq loopBody472_23 loopBody472_1

def loopBody472_25 : HolLoopProg 64 :=
.mark loopBody472_24

def loopBody472_26 : HolLoopProg 64 :=
.seq loopBody472_21 loopBody472_25

def loopBody472_27 : HolLoopProg 64 :=
.mark loopBody472_26

def loopBody472_28 : HolLoopProg 64 :=
.seq loopBody472_19 loopBody472_27

def loopBody472_29 : HolLoopProg 64 :=
.mark loopBody472_28

def loopBody472_30 : HolLoopProg 64 :=
.seq loopBody472_17 loopBody472_29

def loopBody472_31 : HolLoopProg 64 :=
.mark loopBody472_30

def loopBody472_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody472_31 loopBody472_1 (Flapjack.Spt.ln)

def loopBody472_33 : HolLoopProg 64 :=
.mark loopBody472_32

def loopBody472_34 : HolLoopProg 64 :=
.seq loopBody472_33 loopBody472_1

def loopBody472_35 : HolLoopProg 64 :=
.mark loopBody472_34

def loopBody472_36 : HolLoopProg 64 :=
.seq loopBody472_15 loopBody472_35

def loopBody472_37 : HolLoopProg 64 :=
.mark loopBody472_36

def loopBody472_38 : HolLoopProg 64 :=
.seq loopBody472_13 loopBody472_37

def loopBody472_39 : HolLoopProg 64 :=
.mark loopBody472_38

def loopBody472_40 : HolLoopProg 64 :=
.seq loopBody472_7 loopBody472_39

def loopBody472_41 : HolLoopProg 64 :=
.mark loopBody472_40

def loopBody472_42 : HolLoopProg 64 :=
.seq loopBody472_5 loopBody472_41

def loopBody472_43 : HolLoopProg 64 :=
.mark loopBody472_42

def loopBody472_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody472_45 : HolLoopProg 64 :=
.mark loopBody472_44

def loopBody472_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody472_47 : HolLoopProg 64 :=
.mark loopBody472_46

def loopBody472_48 : HolLoopProg 64 :=
.seq loopBody472_47 loopBody472_1

def loopBody472_49 : HolLoopProg 64 :=
.mark loopBody472_48

def loopBody472_50 : HolLoopProg 64 :=
.seq loopBody472_45 loopBody472_49

def loopBody472_51 : HolLoopProg 64 :=
.mark loopBody472_50

def loopBody472_52 : HolLoopProg 64 :=
.seq loopBody472_43 loopBody472_51

def loopBody472_53 : HolLoopProg 64 :=
.mark loopBody472_52

def loopBody472_54 : HolLoopProg 64 :=
.seq loopBody472_3 loopBody472_53

def loopBody472_55 : HolLoopProg 64 :=
.mark loopBody472_54

def loopBody472_56 : HolLoopProg 64 :=
.seq loopBody472_1 loopBody472_55

def loopBody472_57 : HolLoopProg 64 :=
.mark loopBody472_56

def output472 : Nat × List Nat × HolLoopProg 64 :=
  (536, [], loopBody472_57)
end InitECandidate.Proofs.FrontendStages.Loop
