import InitECandidate.Proofs.FrontendStages.Loop.Translate239
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody255_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody255_1 : HolLoopProg 64 :=
.mark loopBody255_0

def loopBody255_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody255_3 : HolLoopProg 64 :=
.mark loopBody255_2

def loopBody255_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody255_5 : HolLoopProg 64 :=
.mark loopBody255_4

def loopBody255_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody255_7 : HolLoopProg 64 :=
.mark loopBody255_6

def loopBody255_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.RegImm.reg 3) loopBody255_5 loopBody255_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody255_9 : HolLoopProg 64 :=
.mark loopBody255_8

def loopBody255_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody255_11 : HolLoopProg 64 :=
.mark loopBody255_10

def loopBody255_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody255_13 : HolLoopProg 64 :=
.mark loopBody255_12

def loopBody255_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody255_15 : HolLoopProg 64 :=
.mark loopBody255_14

def loopBody255_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody255_17 : HolLoopProg 64 :=
.mark loopBody255_16

def loopBody255_18 : HolLoopProg 64 :=
.seq loopBody255_15 loopBody255_17

def loopBody255_19 : HolLoopProg 64 :=
.mark loopBody255_18

def loopBody255_20 : HolLoopProg 64 :=
.seq loopBody255_13 loopBody255_19

def loopBody255_21 : HolLoopProg 64 :=
.mark loopBody255_20

def loopBody255_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody255_21 loopBody255_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody255_23 : HolLoopProg 64 :=
.mark loopBody255_22

def loopBody255_24 : HolLoopProg 64 :=
.seq loopBody255_23 loopBody255_17

def loopBody255_25 : HolLoopProg 64 :=
.mark loopBody255_24

def loopBody255_26 : HolLoopProg 64 :=
.seq loopBody255_11 loopBody255_25

def loopBody255_27 : HolLoopProg 64 :=
.mark loopBody255_26

def loopBody255_28 : HolLoopProg 64 :=
.seq loopBody255_9 loopBody255_27

def loopBody255_29 : HolLoopProg 64 :=
.mark loopBody255_28

def loopBody255_30 : HolLoopProg 64 :=
.seq loopBody255_3 loopBody255_29

def loopBody255_31 : HolLoopProg 64 :=
.mark loopBody255_30

def loopBody255_32 : HolLoopProg 64 :=
.seq loopBody255_1 loopBody255_31

def loopBody255_33 : HolLoopProg 64 :=
.mark loopBody255_32

def loopBody255_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody255_35 : HolLoopProg 64 :=
.mark loopBody255_34

def loopBody255_36 : HolLoopProg 64 :=
.seq loopBody255_35 loopBody255_31

def loopBody255_37 : HolLoopProg 64 :=
.mark loopBody255_36

def loopBody255_38 : HolLoopProg 64 :=
.seq loopBody255_33 loopBody255_37

def loopBody255_39 : HolLoopProg 64 :=
.mark loopBody255_38

def loopBody255_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody255_41 : HolLoopProg 64 :=
.mark loopBody255_40

def loopBody255_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.RegImm.reg 3) loopBody255_5 loopBody255_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody255_43 : HolLoopProg 64 :=
.mark loopBody255_42

def loopBody255_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody255_21 loopBody255_17 (Flapjack.Spt.ln)

def loopBody255_45 : HolLoopProg 64 :=
.mark loopBody255_44

def loopBody255_46 : HolLoopProg 64 :=
.seq loopBody255_45 loopBody255_17

def loopBody255_47 : HolLoopProg 64 :=
.mark loopBody255_46

def loopBody255_48 : HolLoopProg 64 :=
.seq loopBody255_11 loopBody255_47

def loopBody255_49 : HolLoopProg 64 :=
.mark loopBody255_48

def loopBody255_50 : HolLoopProg 64 :=
.seq loopBody255_43 loopBody255_49

def loopBody255_51 : HolLoopProg 64 :=
.mark loopBody255_50

def loopBody255_52 : HolLoopProg 64 :=
.seq loopBody255_3 loopBody255_51

def loopBody255_53 : HolLoopProg 64 :=
.mark loopBody255_52

def loopBody255_54 : HolLoopProg 64 :=
.seq loopBody255_41 loopBody255_53

def loopBody255_55 : HolLoopProg 64 :=
.mark loopBody255_54

def loopBody255_56 : HolLoopProg 64 :=
.seq loopBody255_39 loopBody255_55

def loopBody255_57 : HolLoopProg 64 :=
.mark loopBody255_56

def loopBody255_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1#64)

def loopBody255_59 : HolLoopProg 64 :=
.mark loopBody255_58

def loopBody255_60 : HolLoopProg 64 :=
.seq loopBody255_59 loopBody255_19

def loopBody255_61 : HolLoopProg 64 :=
.mark loopBody255_60

def loopBody255_62 : HolLoopProg 64 :=
.seq loopBody255_57 loopBody255_61

def loopBody255_63 : HolLoopProg 64 :=
.mark loopBody255_62

def output255 : Nat × List Nat × HolLoopProg 64 :=
  (319, [0], loopBody255_63)
end InitECandidate.Proofs.FrontendStages.Loop
