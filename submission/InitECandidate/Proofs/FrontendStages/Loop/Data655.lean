import InitECandidate.Proofs.FrontendStages.Loop.Translate639
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody655_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody655_1 : HolLoopProg 64 :=
.mark loopBody655_0

def loopBody655_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody655_3 : HolLoopProg 64 :=
.mark loopBody655_2

def loopBody655_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody655_5 : HolLoopProg 64 :=
.mark loopBody655_4

def loopBody655_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody655_7 : HolLoopProg 64 :=
.mark loopBody655_6

def loopBody655_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody655_9 : HolLoopProg 64 :=
.mark loopBody655_8

def loopBody655_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody655_11 : HolLoopProg 64 :=
.mark loopBody655_10

def loopBody655_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody655_13 : HolLoopProg 64 :=
.mark loopBody655_12

def loopBody655_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody655_15 : HolLoopProg 64 :=
.mark loopBody655_14

def loopBody655_16 : HolLoopProg 64 :=
.call (some ([6, 7, 8, 9, 10, 11], Flapjack.Spt.ln)) (some 713) ([12, 13, 14, 15, 16, 17]) (some (12, loopBody655_15, loopBody655_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))

def loopBody655_17 : HolLoopProg 64 :=
.mark loopBody655_16

def loopBody655_18 : HolLoopProg 64 :=
.seq loopBody655_17 loopBody655_1

def loopBody655_19 : HolLoopProg 64 :=
.mark loopBody655_18

def loopBody655_20 : HolLoopProg 64 :=
.seq loopBody655_13 loopBody655_19

def loopBody655_21 : HolLoopProg 64 :=
.mark loopBody655_20

def loopBody655_22 : HolLoopProg 64 :=
.seq loopBody655_11 loopBody655_21

def loopBody655_23 : HolLoopProg 64 :=
.mark loopBody655_22

def loopBody655_24 : HolLoopProg 64 :=
.seq loopBody655_9 loopBody655_23

def loopBody655_25 : HolLoopProg 64 :=
.mark loopBody655_24

def loopBody655_26 : HolLoopProg 64 :=
.seq loopBody655_7 loopBody655_25

def loopBody655_27 : HolLoopProg 64 :=
.mark loopBody655_26

def loopBody655_28 : HolLoopProg 64 :=
.seq loopBody655_5 loopBody655_27

def loopBody655_29 : HolLoopProg 64 :=
.mark loopBody655_28

def loopBody655_30 : HolLoopProg 64 :=
.seq loopBody655_3 loopBody655_29

def loopBody655_31 : HolLoopProg 64 :=
.mark loopBody655_30

def loopBody655_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody655_33 : HolLoopProg 64 :=
.mark loopBody655_32

def loopBody655_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12]

def loopBody655_35 : HolLoopProg 64 :=
.mark loopBody655_34

def loopBody655_36 : HolLoopProg 64 :=
.seq loopBody655_35 loopBody655_1

def loopBody655_37 : HolLoopProg 64 :=
.mark loopBody655_36

def loopBody655_38 : HolLoopProg 64 :=
.seq loopBody655_33 loopBody655_37

def loopBody655_39 : HolLoopProg 64 :=
.mark loopBody655_38

def loopBody655_40 : HolLoopProg 64 :=
.seq loopBody655_31 loopBody655_39

def loopBody655_41 : HolLoopProg 64 :=
.mark loopBody655_40

def loopBody655_42 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_41

def loopBody655_43 : HolLoopProg 64 :=
.mark loopBody655_42

def loopBody655_44 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_43

def loopBody655_45 : HolLoopProg 64 :=
.mark loopBody655_44

def loopBody655_46 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_45

def loopBody655_47 : HolLoopProg 64 :=
.mark loopBody655_46

def loopBody655_48 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_47

def loopBody655_49 : HolLoopProg 64 :=
.mark loopBody655_48

def loopBody655_50 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_49

def loopBody655_51 : HolLoopProg 64 :=
.mark loopBody655_50

def loopBody655_52 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_51

def loopBody655_53 : HolLoopProg 64 :=
.mark loopBody655_52

def loopBody655_54 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_53

def loopBody655_55 : HolLoopProg 64 :=
.mark loopBody655_54

def loopBody655_56 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_55

def loopBody655_57 : HolLoopProg 64 :=
.mark loopBody655_56

def loopBody655_58 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_57

def loopBody655_59 : HolLoopProg 64 :=
.mark loopBody655_58

def loopBody655_60 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_59

def loopBody655_61 : HolLoopProg 64 :=
.mark loopBody655_60

def loopBody655_62 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_61

def loopBody655_63 : HolLoopProg 64 :=
.mark loopBody655_62

def loopBody655_64 : HolLoopProg 64 :=
.seq loopBody655_1 loopBody655_63

def loopBody655_65 : HolLoopProg 64 :=
.mark loopBody655_64

def output655 : Nat × List Nat × HolLoopProg 64 :=
  (719, [0, 1, 2, 3, 4, 5], loopBody655_65)
end InitECandidate.Proofs.FrontendStages.Loop
