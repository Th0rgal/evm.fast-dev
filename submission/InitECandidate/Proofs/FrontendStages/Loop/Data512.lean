import InitECandidate.Proofs.FrontendStages.Loop.Translate496
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody512_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody512_1 : HolLoopProg 64 :=
.mark loopBody512_0

def loopBody512_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody512_3 : HolLoopProg 64 :=
.mark loopBody512_2

def loopBody512_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody512_5 : HolLoopProg 64 :=
.mark loopBody512_4

def loopBody512_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody512_5, loopBody512_1, (Flapjack.Spt.ln)))

def loopBody512_7 : HolLoopProg 64 :=
.mark loopBody512_6

def loopBody512_8 : HolLoopProg 64 :=
.seq loopBody512_7 loopBody512_1

def loopBody512_9 : HolLoopProg 64 :=
.mark loopBody512_8

def loopBody512_10 : HolLoopProg 64 :=
.seq loopBody512_3 loopBody512_9

def loopBody512_11 : HolLoopProg 64 :=
.mark loopBody512_10

def loopBody512_12 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_11

def loopBody512_13 : HolLoopProg 64 :=
.mark loopBody512_12

def loopBody512_14 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_13

def loopBody512_15 : HolLoopProg 64 :=
.mark loopBody512_14

def loopBody512_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody512_5, loopBody512_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody512_17 : HolLoopProg 64 :=
.mark loopBody512_16

def loopBody512_18 : HolLoopProg 64 :=
.seq loopBody512_17 loopBody512_1

def loopBody512_19 : HolLoopProg 64 :=
.mark loopBody512_18

def loopBody512_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody512_21 : HolLoopProg 64 :=
.mark loopBody512_20

def loopBody512_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody512_23 : HolLoopProg 64 :=
.mark loopBody512_22

def loopBody512_24 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 473) ([3]) (some (3, loopBody512_23, loopBody512_1, (Flapjack.Spt.ln)))

def loopBody512_25 : HolLoopProg 64 :=
.mark loopBody512_24

def loopBody512_26 : HolLoopProg 64 :=
.seq loopBody512_25 loopBody512_1

def loopBody512_27 : HolLoopProg 64 :=
.mark loopBody512_26

def loopBody512_28 : HolLoopProg 64 :=
.seq loopBody512_21 loopBody512_27

def loopBody512_29 : HolLoopProg 64 :=
.mark loopBody512_28

def loopBody512_30 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_29

def loopBody512_31 : HolLoopProg 64 :=
.mark loopBody512_30

def loopBody512_32 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_31

def loopBody512_33 : HolLoopProg 64 :=
.mark loopBody512_32

def loopBody512_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody512_35 : HolLoopProg 64 :=
.mark loopBody512_34

def loopBody512_36 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody512_23, loopBody512_1, (Flapjack.Spt.ln)))

def loopBody512_37 : HolLoopProg 64 :=
.mark loopBody512_36

def loopBody512_38 : HolLoopProg 64 :=
.seq loopBody512_37 loopBody512_1

def loopBody512_39 : HolLoopProg 64 :=
.mark loopBody512_38

def loopBody512_40 : HolLoopProg 64 :=
.seq loopBody512_35 loopBody512_39

def loopBody512_41 : HolLoopProg 64 :=
.mark loopBody512_40

def loopBody512_42 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_41

def loopBody512_43 : HolLoopProg 64 :=
.mark loopBody512_42

def loopBody512_44 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_43

def loopBody512_45 : HolLoopProg 64 :=
.mark loopBody512_44

def loopBody512_46 : HolLoopProg 64 :=
.seq loopBody512_33 loopBody512_45

def loopBody512_47 : HolLoopProg 64 :=
.mark loopBody512_46

def loopBody512_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody512_49 : HolLoopProg 64 :=
.mark loopBody512_48

def loopBody512_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody512_51 : HolLoopProg 64 :=
.mark loopBody512_50

def loopBody512_52 : HolLoopProg 64 :=
.seq loopBody512_51 loopBody512_1

def loopBody512_53 : HolLoopProg 64 :=
.mark loopBody512_52

def loopBody512_54 : HolLoopProg 64 :=
.seq loopBody512_49 loopBody512_53

def loopBody512_55 : HolLoopProg 64 :=
.mark loopBody512_54

def loopBody512_56 : HolLoopProg 64 :=
.seq loopBody512_47 loopBody512_55

def loopBody512_57 : HolLoopProg 64 :=
.mark loopBody512_56

def loopBody512_58 : HolLoopProg 64 :=
.seq loopBody512_19 loopBody512_57

def loopBody512_59 : HolLoopProg 64 :=
.mark loopBody512_58

def loopBody512_60 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_59

def loopBody512_61 : HolLoopProg 64 :=
.mark loopBody512_60

def loopBody512_62 : HolLoopProg 64 :=
.seq loopBody512_1 loopBody512_61

def loopBody512_63 : HolLoopProg 64 :=
.mark loopBody512_62

def loopBody512_64 : HolLoopProg 64 :=
.seq loopBody512_15 loopBody512_63

def loopBody512_65 : HolLoopProg 64 :=
.mark loopBody512_64

def output512 : Nat × List Nat × HolLoopProg 64 :=
  (576, [], loopBody512_65)
end InitECandidate.Proofs.FrontendStages.Loop
