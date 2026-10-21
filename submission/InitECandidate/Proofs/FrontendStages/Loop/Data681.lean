import InitECandidate.Proofs.FrontendStages.Loop.Translate665
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody681_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody681_1 : HolLoopProg 64 :=
.mark loopBody681_0

def loopBody681_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody681_3 : HolLoopProg 64 :=
.mark loopBody681_2

def loopBody681_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody681_5 : HolLoopProg 64 :=
.mark loopBody681_4

def loopBody681_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody681_7 : HolLoopProg 64 :=
.mark loopBody681_6

def loopBody681_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody681_9 : HolLoopProg 64 :=
.mark loopBody681_8

def loopBody681_10 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 730) ([4, 5, 6]) (some (4, loopBody681_9, loopBody681_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody681_11 : HolLoopProg 64 :=
.mark loopBody681_10

def loopBody681_12 : HolLoopProg 64 :=
.seq loopBody681_11 loopBody681_1

def loopBody681_13 : HolLoopProg 64 :=
.mark loopBody681_12

def loopBody681_14 : HolLoopProg 64 :=
.seq loopBody681_7 loopBody681_13

def loopBody681_15 : HolLoopProg 64 :=
.mark loopBody681_14

def loopBody681_16 : HolLoopProg 64 :=
.seq loopBody681_5 loopBody681_15

def loopBody681_17 : HolLoopProg 64 :=
.mark loopBody681_16

def loopBody681_18 : HolLoopProg 64 :=
.seq loopBody681_3 loopBody681_17

def loopBody681_19 : HolLoopProg 64 :=
.mark loopBody681_18

def loopBody681_20 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_19

def loopBody681_21 : HolLoopProg 64 :=
.mark loopBody681_20

def loopBody681_22 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_21

def loopBody681_23 : HolLoopProg 64 :=
.mark loopBody681_22

def loopBody681_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody681_25 : HolLoopProg 64 :=
.mark loopBody681_24

def loopBody681_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody681_27 : HolLoopProg 64 :=
.mark loopBody681_26

def loopBody681_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 96#64])

def loopBody681_29 : HolLoopProg 64 :=
.mark loopBody681_28

def loopBody681_30 : HolLoopProg 64 :=
.seq loopBody681_29 loopBody681_13

def loopBody681_31 : HolLoopProg 64 :=
.mark loopBody681_30

def loopBody681_32 : HolLoopProg 64 :=
.seq loopBody681_27 loopBody681_31

def loopBody681_33 : HolLoopProg 64 :=
.mark loopBody681_32

def loopBody681_34 : HolLoopProg 64 :=
.seq loopBody681_25 loopBody681_33

def loopBody681_35 : HolLoopProg 64 :=
.mark loopBody681_34

def loopBody681_36 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_35

def loopBody681_37 : HolLoopProg 64 :=
.mark loopBody681_36

def loopBody681_38 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_37

def loopBody681_39 : HolLoopProg 64 :=
.mark loopBody681_38

def loopBody681_40 : HolLoopProg 64 :=
.seq loopBody681_23 loopBody681_39

def loopBody681_41 : HolLoopProg 64 :=
.mark loopBody681_40

def loopBody681_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody681_43 : HolLoopProg 64 :=
.mark loopBody681_42

def loopBody681_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody681_45 : HolLoopProg 64 :=
.mark loopBody681_44

def loopBody681_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 192#64])

def loopBody681_47 : HolLoopProg 64 :=
.mark loopBody681_46

def loopBody681_48 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 730) ([4, 5, 6]) (some (4, loopBody681_9, loopBody681_1, (Flapjack.Spt.ln)))

def loopBody681_49 : HolLoopProg 64 :=
.mark loopBody681_48

def loopBody681_50 : HolLoopProg 64 :=
.seq loopBody681_49 loopBody681_1

def loopBody681_51 : HolLoopProg 64 :=
.mark loopBody681_50

def loopBody681_52 : HolLoopProg 64 :=
.seq loopBody681_47 loopBody681_51

def loopBody681_53 : HolLoopProg 64 :=
.mark loopBody681_52

def loopBody681_54 : HolLoopProg 64 :=
.seq loopBody681_45 loopBody681_53

def loopBody681_55 : HolLoopProg 64 :=
.mark loopBody681_54

def loopBody681_56 : HolLoopProg 64 :=
.seq loopBody681_43 loopBody681_55

def loopBody681_57 : HolLoopProg 64 :=
.mark loopBody681_56

def loopBody681_58 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_57

def loopBody681_59 : HolLoopProg 64 :=
.mark loopBody681_58

def loopBody681_60 : HolLoopProg 64 :=
.seq loopBody681_1 loopBody681_59

def loopBody681_61 : HolLoopProg 64 :=
.mark loopBody681_60

def loopBody681_62 : HolLoopProg 64 :=
.seq loopBody681_41 loopBody681_61

def loopBody681_63 : HolLoopProg 64 :=
.mark loopBody681_62

def loopBody681_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody681_65 : HolLoopProg 64 :=
.mark loopBody681_64

def loopBody681_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody681_67 : HolLoopProg 64 :=
.mark loopBody681_66

def loopBody681_68 : HolLoopProg 64 :=
.seq loopBody681_67 loopBody681_1

def loopBody681_69 : HolLoopProg 64 :=
.mark loopBody681_68

def loopBody681_70 : HolLoopProg 64 :=
.seq loopBody681_65 loopBody681_69

def loopBody681_71 : HolLoopProg 64 :=
.mark loopBody681_70

def loopBody681_72 : HolLoopProg 64 :=
.seq loopBody681_63 loopBody681_71

def loopBody681_73 : HolLoopProg 64 :=
.mark loopBody681_72

def output681 : Nat × List Nat × HolLoopProg 64 :=
  (745, [0, 1, 2], loopBody681_73)
end InitECandidate.Proofs.FrontendStages.Loop
