import InitECandidate.Proofs.FrontendStages.Loop.Translate596
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody612_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody612_1 : HolLoopProg 64 :=
.mark loopBody612_0

def loopBody612_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 5#64))

def loopBody612_3 : HolLoopProg 64 :=
.mark loopBody612_2

def loopBody612_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody612_5 : HolLoopProg 64 :=
.mark loopBody612_4

def loopBody612_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody612_7 : HolLoopProg 64 :=
.mark loopBody612_6

def loopBody612_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody612_9 : HolLoopProg 64 :=
.mark loopBody612_8

def loopBody612_10 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 675) ([4, 5]) (some (4, loopBody612_9, loopBody612_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody612_11 : HolLoopProg 64 :=
.mark loopBody612_10

def loopBody612_12 : HolLoopProg 64 :=
.seq loopBody612_11 loopBody612_1

def loopBody612_13 : HolLoopProg 64 :=
.mark loopBody612_12

def loopBody612_14 : HolLoopProg 64 :=
.seq loopBody612_7 loopBody612_13

def loopBody612_15 : HolLoopProg 64 :=
.mark loopBody612_14

def loopBody612_16 : HolLoopProg 64 :=
.seq loopBody612_5 loopBody612_15

def loopBody612_17 : HolLoopProg 64 :=
.mark loopBody612_16

def loopBody612_18 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_17

def loopBody612_19 : HolLoopProg 64 :=
.mark loopBody612_18

def loopBody612_20 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_19

def loopBody612_21 : HolLoopProg 64 :=
.mark loopBody612_20

def loopBody612_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2])

def loopBody612_23 : HolLoopProg 64 :=
.mark loopBody612_22

def loopBody612_24 : HolLoopProg 64 :=
.seq loopBody612_23 loopBody612_13

def loopBody612_25 : HolLoopProg 64 :=
.mark loopBody612_24

def loopBody612_26 : HolLoopProg 64 :=
.seq loopBody612_5 loopBody612_25

def loopBody612_27 : HolLoopProg 64 :=
.mark loopBody612_26

def loopBody612_28 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_27

def loopBody612_29 : HolLoopProg 64 :=
.mark loopBody612_28

def loopBody612_30 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_29

def loopBody612_31 : HolLoopProg 64 :=
.mark loopBody612_30

def loopBody612_32 : HolLoopProg 64 :=
.seq loopBody612_21 loopBody612_31

def loopBody612_33 : HolLoopProg 64 :=
.mark loopBody612_32

def loopBody612_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 1#64)])

def loopBody612_35 : HolLoopProg 64 :=
.mark loopBody612_34

def loopBody612_36 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 674) ([4, 5]) (some (4, loopBody612_9, loopBody612_1, (Flapjack.Spt.ln)))

def loopBody612_37 : HolLoopProg 64 :=
.mark loopBody612_36

def loopBody612_38 : HolLoopProg 64 :=
.seq loopBody612_37 loopBody612_1

def loopBody612_39 : HolLoopProg 64 :=
.mark loopBody612_38

def loopBody612_40 : HolLoopProg 64 :=
.seq loopBody612_35 loopBody612_39

def loopBody612_41 : HolLoopProg 64 :=
.mark loopBody612_40

def loopBody612_42 : HolLoopProg 64 :=
.seq loopBody612_5 loopBody612_41

def loopBody612_43 : HolLoopProg 64 :=
.mark loopBody612_42

def loopBody612_44 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_43

def loopBody612_45 : HolLoopProg 64 :=
.mark loopBody612_44

def loopBody612_46 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_45

def loopBody612_47 : HolLoopProg 64 :=
.mark loopBody612_46

def loopBody612_48 : HolLoopProg 64 :=
.seq loopBody612_33 loopBody612_47

def loopBody612_49 : HolLoopProg 64 :=
.mark loopBody612_48

def loopBody612_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody612_51 : HolLoopProg 64 :=
.mark loopBody612_50

def loopBody612_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody612_53 : HolLoopProg 64 :=
.mark loopBody612_52

def loopBody612_54 : HolLoopProg 64 :=
.seq loopBody612_53 loopBody612_1

def loopBody612_55 : HolLoopProg 64 :=
.mark loopBody612_54

def loopBody612_56 : HolLoopProg 64 :=
.seq loopBody612_51 loopBody612_55

def loopBody612_57 : HolLoopProg 64 :=
.mark loopBody612_56

def loopBody612_58 : HolLoopProg 64 :=
.seq loopBody612_49 loopBody612_57

def loopBody612_59 : HolLoopProg 64 :=
.mark loopBody612_58

def loopBody612_60 : HolLoopProg 64 :=
.seq loopBody612_3 loopBody612_59

def loopBody612_61 : HolLoopProg 64 :=
.mark loopBody612_60

def loopBody612_62 : HolLoopProg 64 :=
.seq loopBody612_1 loopBody612_61

def loopBody612_63 : HolLoopProg 64 :=
.mark loopBody612_62

def output612 : Nat × List Nat × HolLoopProg 64 :=
  (676, [0, 1], loopBody612_63)
end InitECandidate.Proofs.FrontendStages.Loop
