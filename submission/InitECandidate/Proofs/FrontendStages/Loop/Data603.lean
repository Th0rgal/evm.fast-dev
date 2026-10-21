import InitECandidate.Proofs.FrontendStages.Loop.Translate587
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody603_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody603_1 : HolLoopProg 64 :=
.mark loopBody603_0

def loopBody603_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 12#64)

def loopBody603_3 : HolLoopProg 64 :=
.mark loopBody603_2

def loopBody603_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody603_5 : HolLoopProg 64 :=
.mark loopBody603_4

def loopBody603_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody603_7 : HolLoopProg 64 :=
.mark loopBody603_6

def loopBody603_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody603_5 loopBody603_7 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody603_9 : HolLoopProg 64 :=
.mark loopBody603_8

def loopBody603_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody603_11 : HolLoopProg 64 :=
.mark loopBody603_10

def loopBody603_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody603_13 : HolLoopProg 64 :=
.mark loopBody603_12

def loopBody603_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody603_15 : HolLoopProg 64 :=
.mark loopBody603_14

def loopBody603_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody603_17 : HolLoopProg 64 :=
.mark loopBody603_16

def loopBody603_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody603_19 : HolLoopProg 64 :=
.mark loopBody603_18

def loopBody603_20 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 665) ([4, 5]) (some (4, loopBody603_19, loopBody603_13, (Flapjack.Spt.ln)))

def loopBody603_21 : HolLoopProg 64 :=
.mark loopBody603_20

def loopBody603_22 : HolLoopProg 64 :=
.seq loopBody603_21 loopBody603_13

def loopBody603_23 : HolLoopProg 64 :=
.mark loopBody603_22

def loopBody603_24 : HolLoopProg 64 :=
.seq loopBody603_17 loopBody603_23

def loopBody603_25 : HolLoopProg 64 :=
.mark loopBody603_24

def loopBody603_26 : HolLoopProg 64 :=
.seq loopBody603_15 loopBody603_25

def loopBody603_27 : HolLoopProg 64 :=
.mark loopBody603_26

def loopBody603_28 : HolLoopProg 64 :=
.seq loopBody603_13 loopBody603_27

def loopBody603_29 : HolLoopProg 64 :=
.mark loopBody603_28

def loopBody603_30 : HolLoopProg 64 :=
.seq loopBody603_13 loopBody603_29

def loopBody603_31 : HolLoopProg 64 :=
.mark loopBody603_30

def loopBody603_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody603_33 : HolLoopProg 64 :=
.mark loopBody603_32

def loopBody603_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody603_35 : HolLoopProg 64 :=
.mark loopBody603_34

def loopBody603_36 : HolLoopProg 64 :=
.seq loopBody603_35 loopBody603_13

def loopBody603_37 : HolLoopProg 64 :=
.mark loopBody603_36

def loopBody603_38 : HolLoopProg 64 :=
.seq loopBody603_33 loopBody603_37

def loopBody603_39 : HolLoopProg 64 :=
.mark loopBody603_38

def loopBody603_40 : HolLoopProg 64 :=
.seq loopBody603_31 loopBody603_39

def loopBody603_41 : HolLoopProg 64 :=
.mark loopBody603_40

def loopBody603_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody603_41 loopBody603_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody603_43 : HolLoopProg 64 :=
.mark loopBody603_42

def loopBody603_44 : HolLoopProg 64 :=
.seq loopBody603_43 loopBody603_13

def loopBody603_45 : HolLoopProg 64 :=
.mark loopBody603_44

def loopBody603_46 : HolLoopProg 64 :=
.seq loopBody603_11 loopBody603_45

def loopBody603_47 : HolLoopProg 64 :=
.mark loopBody603_46

def loopBody603_48 : HolLoopProg 64 :=
.seq loopBody603_9 loopBody603_47

def loopBody603_49 : HolLoopProg 64 :=
.mark loopBody603_48

def loopBody603_50 : HolLoopProg 64 :=
.seq loopBody603_3 loopBody603_49

def loopBody603_51 : HolLoopProg 64 :=
.mark loopBody603_50

def loopBody603_52 : HolLoopProg 64 :=
.seq loopBody603_1 loopBody603_51

def loopBody603_53 : HolLoopProg 64 :=
.mark loopBody603_52

def loopBody603_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody603_55 : HolLoopProg 64 :=
.mark loopBody603_54

def loopBody603_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody603_57 : HolLoopProg 64 :=
.mark loopBody603_56

def loopBody603_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody603_59 : HolLoopProg 64 :=
.mark loopBody603_58

def loopBody603_60 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 666) ([4, 5, 6, 7]) (some (4, loopBody603_19, loopBody603_13, (Flapjack.Spt.ln)))

def loopBody603_61 : HolLoopProg 64 :=
.mark loopBody603_60

def loopBody603_62 : HolLoopProg 64 :=
.seq loopBody603_61 loopBody603_13

def loopBody603_63 : HolLoopProg 64 :=
.mark loopBody603_62

def loopBody603_64 : HolLoopProg 64 :=
.seq loopBody603_59 loopBody603_63

def loopBody603_65 : HolLoopProg 64 :=
.mark loopBody603_64

def loopBody603_66 : HolLoopProg 64 :=
.seq loopBody603_57 loopBody603_65

def loopBody603_67 : HolLoopProg 64 :=
.mark loopBody603_66

def loopBody603_68 : HolLoopProg 64 :=
.seq loopBody603_55 loopBody603_67

def loopBody603_69 : HolLoopProg 64 :=
.mark loopBody603_68

def loopBody603_70 : HolLoopProg 64 :=
.seq loopBody603_1 loopBody603_69

def loopBody603_71 : HolLoopProg 64 :=
.mark loopBody603_70

def loopBody603_72 : HolLoopProg 64 :=
.seq loopBody603_13 loopBody603_71

def loopBody603_73 : HolLoopProg 64 :=
.mark loopBody603_72

def loopBody603_74 : HolLoopProg 64 :=
.seq loopBody603_13 loopBody603_73

def loopBody603_75 : HolLoopProg 64 :=
.mark loopBody603_74

def loopBody603_76 : HolLoopProg 64 :=
.seq loopBody603_53 loopBody603_75

def loopBody603_77 : HolLoopProg 64 :=
.mark loopBody603_76

def loopBody603_78 : HolLoopProg 64 :=
.seq loopBody603_77 loopBody603_39

def loopBody603_79 : HolLoopProg 64 :=
.mark loopBody603_78

def output603 : Nat × List Nat × HolLoopProg 64 :=
  (667, [0, 1, 2], loopBody603_79)
end InitECandidate.Proofs.FrontendStages.Loop
