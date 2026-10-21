import InitECandidate.Proofs.FrontendStages.Loop.Translate224
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody240_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody240_1 : HolLoopProg 64 :=
.mark loopBody240_0

def loopBody240_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 16#64)

def loopBody240_3 : HolLoopProg 64 :=
.mark loopBody240_2

def loopBody240_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody240_5 : HolLoopProg 64 :=
.mark loopBody240_4

def loopBody240_6 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody240_5, loopBody240_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody240_7 : HolLoopProg 64 :=
.mark loopBody240_6

def loopBody240_8 : HolLoopProg 64 :=
.seq loopBody240_7 loopBody240_1

def loopBody240_9 : HolLoopProg 64 :=
.mark loopBody240_8

def loopBody240_10 : HolLoopProg 64 :=
.seq loopBody240_3 loopBody240_9

def loopBody240_11 : HolLoopProg 64 :=
.mark loopBody240_10

def loopBody240_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 0#64])

def loopBody240_13 : HolLoopProg 64 :=
.mark loopBody240_12

def loopBody240_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody240_15 : HolLoopProg 64 :=
.mark loopBody240_14

def loopBody240_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody240_17 : HolLoopProg 64 :=
.mark loopBody240_16

def loopBody240_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody240_19 : HolLoopProg 64 :=
.mark loopBody240_18

def loopBody240_20 : HolLoopProg 64 :=
.seq loopBody240_19 loopBody240_1

def loopBody240_21 : HolLoopProg 64 :=
.mark loopBody240_20

def loopBody240_22 : HolLoopProg 64 :=
.seq loopBody240_17 loopBody240_21

def loopBody240_23 : HolLoopProg 64 :=
.mark loopBody240_22

def loopBody240_24 : HolLoopProg 64 :=
.seq loopBody240_23 loopBody240_1

def loopBody240_25 : HolLoopProg 64 :=
.mark loopBody240_24

def loopBody240_26 : HolLoopProg 64 :=
.seq loopBody240_15 loopBody240_25

def loopBody240_27 : HolLoopProg 64 :=
.mark loopBody240_26

def loopBody240_28 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_27

def loopBody240_29 : HolLoopProg 64 :=
.mark loopBody240_28

def loopBody240_30 : HolLoopProg 64 :=
.seq loopBody240_13 loopBody240_29

def loopBody240_31 : HolLoopProg 64 :=
.mark loopBody240_30

def loopBody240_32 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_31

def loopBody240_33 : HolLoopProg 64 :=
.mark loopBody240_32

def loopBody240_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64])

def loopBody240_35 : HolLoopProg 64 :=
.mark loopBody240_34

def loopBody240_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody240_37 : HolLoopProg 64 :=
.mark loopBody240_36

def loopBody240_38 : HolLoopProg 64 :=
.seq loopBody240_37 loopBody240_25

def loopBody240_39 : HolLoopProg 64 :=
.mark loopBody240_38

def loopBody240_40 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_39

def loopBody240_41 : HolLoopProg 64 :=
.mark loopBody240_40

def loopBody240_42 : HolLoopProg 64 :=
.seq loopBody240_35 loopBody240_41

def loopBody240_43 : HolLoopProg 64 :=
.mark loopBody240_42

def loopBody240_44 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_43

def loopBody240_45 : HolLoopProg 64 :=
.mark loopBody240_44

def loopBody240_46 : HolLoopProg 64 :=
.seq loopBody240_33 loopBody240_45

def loopBody240_47 : HolLoopProg 64 :=
.mark loopBody240_46

def loopBody240_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody240_49 : HolLoopProg 64 :=
.mark loopBody240_48

def loopBody240_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody240_51 : HolLoopProg 64 :=
.mark loopBody240_50

def loopBody240_52 : HolLoopProg 64 :=
.seq loopBody240_51 loopBody240_1

def loopBody240_53 : HolLoopProg 64 :=
.mark loopBody240_52

def loopBody240_54 : HolLoopProg 64 :=
.seq loopBody240_49 loopBody240_53

def loopBody240_55 : HolLoopProg 64 :=
.mark loopBody240_54

def loopBody240_56 : HolLoopProg 64 :=
.seq loopBody240_47 loopBody240_55

def loopBody240_57 : HolLoopProg 64 :=
.mark loopBody240_56

def loopBody240_58 : HolLoopProg 64 :=
.seq loopBody240_11 loopBody240_57

def loopBody240_59 : HolLoopProg 64 :=
.mark loopBody240_58

def loopBody240_60 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_59

def loopBody240_61 : HolLoopProg 64 :=
.mark loopBody240_60

def loopBody240_62 : HolLoopProg 64 :=
.seq loopBody240_1 loopBody240_61

def loopBody240_63 : HolLoopProg 64 :=
.mark loopBody240_62

def output240 : Nat × List Nat × HolLoopProg 64 :=
  (304, [0, 1], loopBody240_63)
end InitECandidate.Proofs.FrontendStages.Loop
