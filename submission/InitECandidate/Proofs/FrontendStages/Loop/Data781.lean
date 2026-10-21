import InitECandidate.Proofs.FrontendStages.Loop.Translate765
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody781_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody781_1 : HolLoopProg 64 :=
.mark loopBody781_0

def loopBody781_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody781_3 : HolLoopProg 64 :=
.mark loopBody781_2

def loopBody781_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody781_5 : HolLoopProg 64 :=
.mark loopBody781_4

def loopBody781_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody781_7 : HolLoopProg 64 :=
.mark loopBody781_6

def loopBody781_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 187) ([3, 4]) (some (3, loopBody781_7, loopBody781_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody781_9 : HolLoopProg 64 :=
.mark loopBody781_8

def loopBody781_10 : HolLoopProg 64 :=
.seq loopBody781_9 loopBody781_1

def loopBody781_11 : HolLoopProg 64 :=
.mark loopBody781_10

def loopBody781_12 : HolLoopProg 64 :=
.seq loopBody781_5 loopBody781_11

def loopBody781_13 : HolLoopProg 64 :=
.mark loopBody781_12

def loopBody781_14 : HolLoopProg 64 :=
.seq loopBody781_3 loopBody781_13

def loopBody781_15 : HolLoopProg 64 :=
.mark loopBody781_14

def loopBody781_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody781_17 : HolLoopProg 64 :=
.mark loopBody781_16

def loopBody781_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody781_19 : HolLoopProg 64 :=
.mark loopBody781_18

def loopBody781_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody781_21 : HolLoopProg 64 :=
.mark loopBody781_20

def loopBody781_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody781_23 : HolLoopProg 64 :=
.mark loopBody781_22

def loopBody781_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody781_21 loopBody781_23 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody781_25 : HolLoopProg 64 :=
.mark loopBody781_24

def loopBody781_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody781_27 : HolLoopProg 64 :=
.mark loopBody781_26

def loopBody781_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 128#64]))

def loopBody781_29 : HolLoopProg 64 :=
.mark loopBody781_28

def loopBody781_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody781_31 : HolLoopProg 64 :=
.mark loopBody781_30

def loopBody781_32 : HolLoopProg 64 :=
.seq loopBody781_31 loopBody781_1

def loopBody781_33 : HolLoopProg 64 :=
.mark loopBody781_32

def loopBody781_34 : HolLoopProg 64 :=
.seq loopBody781_29 loopBody781_33

def loopBody781_35 : HolLoopProg 64 :=
.mark loopBody781_34

def loopBody781_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody781_35 loopBody781_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody781_37 : HolLoopProg 64 :=
.mark loopBody781_36

def loopBody781_38 : HolLoopProg 64 :=
.seq loopBody781_37 loopBody781_1

def loopBody781_39 : HolLoopProg 64 :=
.mark loopBody781_38

def loopBody781_40 : HolLoopProg 64 :=
.seq loopBody781_27 loopBody781_39

def loopBody781_41 : HolLoopProg 64 :=
.mark loopBody781_40

def loopBody781_42 : HolLoopProg 64 :=
.seq loopBody781_25 loopBody781_41

def loopBody781_43 : HolLoopProg 64 :=
.mark loopBody781_42

def loopBody781_44 : HolLoopProg 64 :=
.seq loopBody781_19 loopBody781_43

def loopBody781_45 : HolLoopProg 64 :=
.mark loopBody781_44

def loopBody781_46 : HolLoopProg 64 :=
.seq loopBody781_17 loopBody781_45

def loopBody781_47 : HolLoopProg 64 :=
.mark loopBody781_46

def loopBody781_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody781_49 : HolLoopProg 64 :=
.mark loopBody781_48

def loopBody781_50 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 395) ([4]) (some (4, loopBody781_49, loopBody781_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody781_51 : HolLoopProg 64 :=
.mark loopBody781_50

def loopBody781_52 : HolLoopProg 64 :=
.seq loopBody781_51 loopBody781_1

def loopBody781_53 : HolLoopProg 64 :=
.mark loopBody781_52

def loopBody781_54 : HolLoopProg 64 :=
.seq loopBody781_5 loopBody781_53

def loopBody781_55 : HolLoopProg 64 :=
.mark loopBody781_54

def loopBody781_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody781_57 : HolLoopProg 64 :=
.mark loopBody781_56

def loopBody781_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody781_59 : HolLoopProg 64 :=
.mark loopBody781_58

def loopBody781_60 : HolLoopProg 64 :=
.seq loopBody781_59 loopBody781_1

def loopBody781_61 : HolLoopProg 64 :=
.mark loopBody781_60

def loopBody781_62 : HolLoopProg 64 :=
.seq loopBody781_57 loopBody781_61

def loopBody781_63 : HolLoopProg 64 :=
.mark loopBody781_62

def loopBody781_64 : HolLoopProg 64 :=
.seq loopBody781_55 loopBody781_63

def loopBody781_65 : HolLoopProg 64 :=
.mark loopBody781_64

def loopBody781_66 : HolLoopProg 64 :=
.seq loopBody781_1 loopBody781_65

def loopBody781_67 : HolLoopProg 64 :=
.mark loopBody781_66

def loopBody781_68 : HolLoopProg 64 :=
.seq loopBody781_1 loopBody781_67

def loopBody781_69 : HolLoopProg 64 :=
.mark loopBody781_68

def loopBody781_70 : HolLoopProg 64 :=
.seq loopBody781_47 loopBody781_69

def loopBody781_71 : HolLoopProg 64 :=
.mark loopBody781_70

def loopBody781_72 : HolLoopProg 64 :=
.seq loopBody781_15 loopBody781_71

def loopBody781_73 : HolLoopProg 64 :=
.mark loopBody781_72

def loopBody781_74 : HolLoopProg 64 :=
.seq loopBody781_1 loopBody781_73

def loopBody781_75 : HolLoopProg 64 :=
.mark loopBody781_74

def loopBody781_76 : HolLoopProg 64 :=
.seq loopBody781_1 loopBody781_75

def loopBody781_77 : HolLoopProg 64 :=
.mark loopBody781_76

def output781 : Nat × List Nat × HolLoopProg 64 :=
  (845, [0, 1], loopBody781_77)
end InitECandidate.Proofs.FrontendStages.Loop
