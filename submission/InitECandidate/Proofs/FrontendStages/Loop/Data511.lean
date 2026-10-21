import InitECandidate.Proofs.FrontendStages.Loop.Translate495
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody511_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody511_1 : HolLoopProg 64 :=
.mark loopBody511_0

def loopBody511_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody511_3 : HolLoopProg 64 :=
.mark loopBody511_2

def loopBody511_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody511_5 : HolLoopProg 64 :=
.mark loopBody511_4

def loopBody511_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody511_5, loopBody511_1, (Flapjack.Spt.ln)))

def loopBody511_7 : HolLoopProg 64 :=
.mark loopBody511_6

def loopBody511_8 : HolLoopProg 64 :=
.seq loopBody511_7 loopBody511_1

def loopBody511_9 : HolLoopProg 64 :=
.mark loopBody511_8

def loopBody511_10 : HolLoopProg 64 :=
.seq loopBody511_3 loopBody511_9

def loopBody511_11 : HolLoopProg 64 :=
.mark loopBody511_10

def loopBody511_12 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_11

def loopBody511_13 : HolLoopProg 64 :=
.mark loopBody511_12

def loopBody511_14 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_13

def loopBody511_15 : HolLoopProg 64 :=
.mark loopBody511_14

def loopBody511_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody511_5, loopBody511_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody511_17 : HolLoopProg 64 :=
.mark loopBody511_16

def loopBody511_18 : HolLoopProg 64 :=
.seq loopBody511_17 loopBody511_1

def loopBody511_19 : HolLoopProg 64 :=
.mark loopBody511_18

def loopBody511_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 40#64]))

def loopBody511_21 : HolLoopProg 64 :=
.mark loopBody511_20

def loopBody511_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody511_23 : HolLoopProg 64 :=
.mark loopBody511_22

def loopBody511_24 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 473) ([3]) (some (3, loopBody511_23, loopBody511_1, (Flapjack.Spt.ln)))

def loopBody511_25 : HolLoopProg 64 :=
.mark loopBody511_24

def loopBody511_26 : HolLoopProg 64 :=
.seq loopBody511_25 loopBody511_1

def loopBody511_27 : HolLoopProg 64 :=
.mark loopBody511_26

def loopBody511_28 : HolLoopProg 64 :=
.seq loopBody511_21 loopBody511_27

def loopBody511_29 : HolLoopProg 64 :=
.mark loopBody511_28

def loopBody511_30 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_29

def loopBody511_31 : HolLoopProg 64 :=
.mark loopBody511_30

def loopBody511_32 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_31

def loopBody511_33 : HolLoopProg 64 :=
.mark loopBody511_32

def loopBody511_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody511_35 : HolLoopProg 64 :=
.mark loopBody511_34

def loopBody511_36 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody511_23, loopBody511_1, (Flapjack.Spt.ln)))

def loopBody511_37 : HolLoopProg 64 :=
.mark loopBody511_36

def loopBody511_38 : HolLoopProg 64 :=
.seq loopBody511_37 loopBody511_1

def loopBody511_39 : HolLoopProg 64 :=
.mark loopBody511_38

def loopBody511_40 : HolLoopProg 64 :=
.seq loopBody511_35 loopBody511_39

def loopBody511_41 : HolLoopProg 64 :=
.mark loopBody511_40

def loopBody511_42 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_41

def loopBody511_43 : HolLoopProg 64 :=
.mark loopBody511_42

def loopBody511_44 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_43

def loopBody511_45 : HolLoopProg 64 :=
.mark loopBody511_44

def loopBody511_46 : HolLoopProg 64 :=
.seq loopBody511_33 loopBody511_45

def loopBody511_47 : HolLoopProg 64 :=
.mark loopBody511_46

def loopBody511_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody511_49 : HolLoopProg 64 :=
.mark loopBody511_48

def loopBody511_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody511_51 : HolLoopProg 64 :=
.mark loopBody511_50

def loopBody511_52 : HolLoopProg 64 :=
.seq loopBody511_51 loopBody511_1

def loopBody511_53 : HolLoopProg 64 :=
.mark loopBody511_52

def loopBody511_54 : HolLoopProg 64 :=
.seq loopBody511_49 loopBody511_53

def loopBody511_55 : HolLoopProg 64 :=
.mark loopBody511_54

def loopBody511_56 : HolLoopProg 64 :=
.seq loopBody511_47 loopBody511_55

def loopBody511_57 : HolLoopProg 64 :=
.mark loopBody511_56

def loopBody511_58 : HolLoopProg 64 :=
.seq loopBody511_19 loopBody511_57

def loopBody511_59 : HolLoopProg 64 :=
.mark loopBody511_58

def loopBody511_60 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_59

def loopBody511_61 : HolLoopProg 64 :=
.mark loopBody511_60

def loopBody511_62 : HolLoopProg 64 :=
.seq loopBody511_1 loopBody511_61

def loopBody511_63 : HolLoopProg 64 :=
.mark loopBody511_62

def loopBody511_64 : HolLoopProg 64 :=
.seq loopBody511_15 loopBody511_63

def loopBody511_65 : HolLoopProg 64 :=
.mark loopBody511_64

def output511 : Nat × List Nat × HolLoopProg 64 :=
  (575, [], loopBody511_65)
end InitECandidate.Proofs.FrontendStages.Loop
