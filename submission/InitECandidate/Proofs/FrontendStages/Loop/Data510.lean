import InitECandidate.Proofs.FrontendStages.Loop.Translate494
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody510_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody510_1 : HolLoopProg 64 :=
.mark loopBody510_0

def loopBody510_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody510_3 : HolLoopProg 64 :=
.mark loopBody510_2

def loopBody510_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody510_5 : HolLoopProg 64 :=
.mark loopBody510_4

def loopBody510_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody510_5, loopBody510_1, (Flapjack.Spt.ln)))

def loopBody510_7 : HolLoopProg 64 :=
.mark loopBody510_6

def loopBody510_8 : HolLoopProg 64 :=
.seq loopBody510_7 loopBody510_1

def loopBody510_9 : HolLoopProg 64 :=
.mark loopBody510_8

def loopBody510_10 : HolLoopProg 64 :=
.seq loopBody510_3 loopBody510_9

def loopBody510_11 : HolLoopProg 64 :=
.mark loopBody510_10

def loopBody510_12 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_11

def loopBody510_13 : HolLoopProg 64 :=
.mark loopBody510_12

def loopBody510_14 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_13

def loopBody510_15 : HolLoopProg 64 :=
.mark loopBody510_14

def loopBody510_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody510_5, loopBody510_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody510_17 : HolLoopProg 64 :=
.mark loopBody510_16

def loopBody510_18 : HolLoopProg 64 :=
.seq loopBody510_17 loopBody510_1

def loopBody510_19 : HolLoopProg 64 :=
.mark loopBody510_18

def loopBody510_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 80#64]))

def loopBody510_21 : HolLoopProg 64 :=
.mark loopBody510_20

def loopBody510_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody510_23 : HolLoopProg 64 :=
.mark loopBody510_22

def loopBody510_24 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 473) ([3]) (some (3, loopBody510_23, loopBody510_1, (Flapjack.Spt.ln)))

def loopBody510_25 : HolLoopProg 64 :=
.mark loopBody510_24

def loopBody510_26 : HolLoopProg 64 :=
.seq loopBody510_25 loopBody510_1

def loopBody510_27 : HolLoopProg 64 :=
.mark loopBody510_26

def loopBody510_28 : HolLoopProg 64 :=
.seq loopBody510_21 loopBody510_27

def loopBody510_29 : HolLoopProg 64 :=
.mark loopBody510_28

def loopBody510_30 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_29

def loopBody510_31 : HolLoopProg 64 :=
.mark loopBody510_30

def loopBody510_32 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_31

def loopBody510_33 : HolLoopProg 64 :=
.mark loopBody510_32

def loopBody510_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody510_35 : HolLoopProg 64 :=
.mark loopBody510_34

def loopBody510_36 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody510_23, loopBody510_1, (Flapjack.Spt.ln)))

def loopBody510_37 : HolLoopProg 64 :=
.mark loopBody510_36

def loopBody510_38 : HolLoopProg 64 :=
.seq loopBody510_37 loopBody510_1

def loopBody510_39 : HolLoopProg 64 :=
.mark loopBody510_38

def loopBody510_40 : HolLoopProg 64 :=
.seq loopBody510_35 loopBody510_39

def loopBody510_41 : HolLoopProg 64 :=
.mark loopBody510_40

def loopBody510_42 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_41

def loopBody510_43 : HolLoopProg 64 :=
.mark loopBody510_42

def loopBody510_44 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_43

def loopBody510_45 : HolLoopProg 64 :=
.mark loopBody510_44

def loopBody510_46 : HolLoopProg 64 :=
.seq loopBody510_33 loopBody510_45

def loopBody510_47 : HolLoopProg 64 :=
.mark loopBody510_46

def loopBody510_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody510_49 : HolLoopProg 64 :=
.mark loopBody510_48

def loopBody510_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody510_51 : HolLoopProg 64 :=
.mark loopBody510_50

def loopBody510_52 : HolLoopProg 64 :=
.seq loopBody510_51 loopBody510_1

def loopBody510_53 : HolLoopProg 64 :=
.mark loopBody510_52

def loopBody510_54 : HolLoopProg 64 :=
.seq loopBody510_49 loopBody510_53

def loopBody510_55 : HolLoopProg 64 :=
.mark loopBody510_54

def loopBody510_56 : HolLoopProg 64 :=
.seq loopBody510_47 loopBody510_55

def loopBody510_57 : HolLoopProg 64 :=
.mark loopBody510_56

def loopBody510_58 : HolLoopProg 64 :=
.seq loopBody510_19 loopBody510_57

def loopBody510_59 : HolLoopProg 64 :=
.mark loopBody510_58

def loopBody510_60 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_59

def loopBody510_61 : HolLoopProg 64 :=
.mark loopBody510_60

def loopBody510_62 : HolLoopProg 64 :=
.seq loopBody510_1 loopBody510_61

def loopBody510_63 : HolLoopProg 64 :=
.mark loopBody510_62

def loopBody510_64 : HolLoopProg 64 :=
.seq loopBody510_15 loopBody510_63

def loopBody510_65 : HolLoopProg 64 :=
.mark loopBody510_64

def output510 : Nat × List Nat × HolLoopProg 64 :=
  (574, [], loopBody510_65)
end InitECandidate.Proofs.FrontendStages.Loop
