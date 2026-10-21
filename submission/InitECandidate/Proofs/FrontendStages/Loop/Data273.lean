import InitECandidate.Proofs.FrontendStages.Loop.Translate257
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody273_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody273_1 : HolLoopProg 64 :=
.mark loopBody273_0

def loopBody273_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody273_3 : HolLoopProg 64 :=
.mark loopBody273_2

def loopBody273_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody273_5 : HolLoopProg 64 :=
.mark loopBody273_4

def loopBody273_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody273_7 : HolLoopProg 64 :=
.mark loopBody273_6

def loopBody273_8 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 161) ([6, 7]) (some (6, loopBody273_7, loopBody273_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody273_9 : HolLoopProg 64 :=
.mark loopBody273_8

def loopBody273_10 : HolLoopProg 64 :=
.seq loopBody273_9 loopBody273_1

def loopBody273_11 : HolLoopProg 64 :=
.mark loopBody273_10

def loopBody273_12 : HolLoopProg 64 :=
.seq loopBody273_5 loopBody273_11

def loopBody273_13 : HolLoopProg 64 :=
.mark loopBody273_12

def loopBody273_14 : HolLoopProg 64 :=
.seq loopBody273_3 loopBody273_13

def loopBody273_15 : HolLoopProg 64 :=
.mark loopBody273_14

def loopBody273_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody273_17 : HolLoopProg 64 :=
.mark loopBody273_16

def loopBody273_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody273_19 : HolLoopProg 64 :=
.mark loopBody273_18

def loopBody273_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody273_21 : HolLoopProg 64 :=
.mark loopBody273_20

def loopBody273_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody273_23 : HolLoopProg 64 :=
.mark loopBody273_22

def loopBody273_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody273_21 loopBody273_23 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody273_25 : HolLoopProg 64 :=
.mark loopBody273_24

def loopBody273_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody273_27 : HolLoopProg 64 :=
.mark loopBody273_26

def loopBody273_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 18#64)

def loopBody273_29 : HolLoopProg 64 :=
.mark loopBody273_28

def loopBody273_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody273_31 : HolLoopProg 64 :=
.mark loopBody273_30

def loopBody273_32 : HolLoopProg 64 :=
.seq loopBody273_31 loopBody273_1

def loopBody273_33 : HolLoopProg 64 :=
.mark loopBody273_32

def loopBody273_34 : HolLoopProg 64 :=
.seq loopBody273_33 loopBody273_1

def loopBody273_35 : HolLoopProg 64 :=
.mark loopBody273_34

def loopBody273_36 : HolLoopProg 64 :=
.seq loopBody273_29 loopBody273_35

def loopBody273_37 : HolLoopProg 64 :=
.mark loopBody273_36

def loopBody273_38 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_37

def loopBody273_39 : HolLoopProg 64 :=
.mark loopBody273_38

def loopBody273_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 6#64)

def loopBody273_41 : HolLoopProg 64 :=
.mark loopBody273_40

def loopBody273_42 : HolLoopProg 64 :=
.seq loopBody273_41 loopBody273_7

def loopBody273_43 : HolLoopProg 64 :=
.mark loopBody273_42

def loopBody273_44 : HolLoopProg 64 :=
.seq loopBody273_39 loopBody273_43

def loopBody273_45 : HolLoopProg 64 :=
.mark loopBody273_44

def loopBody273_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody273_45 loopBody273_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody273_47 : HolLoopProg 64 :=
.mark loopBody273_46

def loopBody273_48 : HolLoopProg 64 :=
.seq loopBody273_47 loopBody273_1

def loopBody273_49 : HolLoopProg 64 :=
.mark loopBody273_48

def loopBody273_50 : HolLoopProg 64 :=
.seq loopBody273_27 loopBody273_49

def loopBody273_51 : HolLoopProg 64 :=
.mark loopBody273_50

def loopBody273_52 : HolLoopProg 64 :=
.seq loopBody273_25 loopBody273_51

def loopBody273_53 : HolLoopProg 64 :=
.mark loopBody273_52

def loopBody273_54 : HolLoopProg 64 :=
.seq loopBody273_19 loopBody273_53

def loopBody273_55 : HolLoopProg 64 :=
.mark loopBody273_54

def loopBody273_56 : HolLoopProg 64 :=
.seq loopBody273_17 loopBody273_55

def loopBody273_57 : HolLoopProg 64 :=
.mark loopBody273_56

def loopBody273_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody273_59 : HolLoopProg 64 :=
.mark loopBody273_58

def loopBody273_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody273_61 : HolLoopProg 64 :=
.mark loopBody273_60

def loopBody273_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7]

def loopBody273_63 : HolLoopProg 64 :=
.mark loopBody273_62

def loopBody273_64 : HolLoopProg 64 :=
.seq loopBody273_63 loopBody273_1

def loopBody273_65 : HolLoopProg 64 :=
.mark loopBody273_64

def loopBody273_66 : HolLoopProg 64 :=
.seq loopBody273_61 loopBody273_65

def loopBody273_67 : HolLoopProg 64 :=
.mark loopBody273_66

def loopBody273_68 : HolLoopProg 64 :=
.seq loopBody273_59 loopBody273_67

def loopBody273_69 : HolLoopProg 64 :=
.mark loopBody273_68

def loopBody273_70 : HolLoopProg 64 :=
.seq loopBody273_57 loopBody273_69

def loopBody273_71 : HolLoopProg 64 :=
.mark loopBody273_70

def loopBody273_72 : HolLoopProg 64 :=
.seq loopBody273_15 loopBody273_71

def loopBody273_73 : HolLoopProg 64 :=
.mark loopBody273_72

def loopBody273_74 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_73

def loopBody273_75 : HolLoopProg 64 :=
.mark loopBody273_74

def loopBody273_76 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_75

def loopBody273_77 : HolLoopProg 64 :=
.mark loopBody273_76

def loopBody273_78 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_77

def loopBody273_79 : HolLoopProg 64 :=
.mark loopBody273_78

def loopBody273_80 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_79

def loopBody273_81 : HolLoopProg 64 :=
.mark loopBody273_80

def loopBody273_82 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_81

def loopBody273_83 : HolLoopProg 64 :=
.mark loopBody273_82

def loopBody273_84 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_83

def loopBody273_85 : HolLoopProg 64 :=
.mark loopBody273_84

def loopBody273_86 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_85

def loopBody273_87 : HolLoopProg 64 :=
.mark loopBody273_86

def loopBody273_88 : HolLoopProg 64 :=
.seq loopBody273_1 loopBody273_87

def loopBody273_89 : HolLoopProg 64 :=
.mark loopBody273_88

def output273 : Nat × List Nat × HolLoopProg 64 :=
  (337, [0, 1], loopBody273_89)
end InitECandidate.Proofs.FrontendStages.Loop
