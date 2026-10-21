import InitECandidate.Proofs.FrontendStages.Loop.Translate189
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody205_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody205_1 : HolLoopProg 64 :=
.mark loopBody205_0

def loopBody205_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody205_3 : HolLoopProg 64 :=
.mark loopBody205_2

def loopBody205_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody205_5 : HolLoopProg 64 :=
.mark loopBody205_4

def loopBody205_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody205_7 : HolLoopProg 64 :=
.mark loopBody205_6

def loopBody205_8 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 161) ([6, 7]) (some (6, loopBody205_7, loopBody205_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody205_9 : HolLoopProg 64 :=
.mark loopBody205_8

def loopBody205_10 : HolLoopProg 64 :=
.seq loopBody205_9 loopBody205_1

def loopBody205_11 : HolLoopProg 64 :=
.mark loopBody205_10

def loopBody205_12 : HolLoopProg 64 :=
.seq loopBody205_5 loopBody205_11

def loopBody205_13 : HolLoopProg 64 :=
.mark loopBody205_12

def loopBody205_14 : HolLoopProg 64 :=
.seq loopBody205_3 loopBody205_13

def loopBody205_15 : HolLoopProg 64 :=
.mark loopBody205_14

def loopBody205_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody205_17 : HolLoopProg 64 :=
.mark loopBody205_16

def loopBody205_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody205_19 : HolLoopProg 64 :=
.mark loopBody205_18

def loopBody205_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody205_21 : HolLoopProg 64 :=
.mark loopBody205_20

def loopBody205_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody205_23 : HolLoopProg 64 :=
.mark loopBody205_22

def loopBody205_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody205_21 loopBody205_23 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody205_25 : HolLoopProg 64 :=
.mark loopBody205_24

def loopBody205_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody205_27 : HolLoopProg 64 :=
.mark loopBody205_26

def loopBody205_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 8#64)

def loopBody205_29 : HolLoopProg 64 :=
.mark loopBody205_28

def loopBody205_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody205_31 : HolLoopProg 64 :=
.mark loopBody205_30

def loopBody205_32 : HolLoopProg 64 :=
.seq loopBody205_31 loopBody205_1

def loopBody205_33 : HolLoopProg 64 :=
.mark loopBody205_32

def loopBody205_34 : HolLoopProg 64 :=
.seq loopBody205_33 loopBody205_1

def loopBody205_35 : HolLoopProg 64 :=
.mark loopBody205_34

def loopBody205_36 : HolLoopProg 64 :=
.seq loopBody205_29 loopBody205_35

def loopBody205_37 : HolLoopProg 64 :=
.mark loopBody205_36

def loopBody205_38 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_37

def loopBody205_39 : HolLoopProg 64 :=
.mark loopBody205_38

def loopBody205_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody205_41 : HolLoopProg 64 :=
.mark loopBody205_40

def loopBody205_42 : HolLoopProg 64 :=
.seq loopBody205_41 loopBody205_7

def loopBody205_43 : HolLoopProg 64 :=
.mark loopBody205_42

def loopBody205_44 : HolLoopProg 64 :=
.seq loopBody205_39 loopBody205_43

def loopBody205_45 : HolLoopProg 64 :=
.mark loopBody205_44

def loopBody205_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody205_45 loopBody205_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody205_47 : HolLoopProg 64 :=
.mark loopBody205_46

def loopBody205_48 : HolLoopProg 64 :=
.seq loopBody205_47 loopBody205_1

def loopBody205_49 : HolLoopProg 64 :=
.mark loopBody205_48

def loopBody205_50 : HolLoopProg 64 :=
.seq loopBody205_27 loopBody205_49

def loopBody205_51 : HolLoopProg 64 :=
.mark loopBody205_50

def loopBody205_52 : HolLoopProg 64 :=
.seq loopBody205_25 loopBody205_51

def loopBody205_53 : HolLoopProg 64 :=
.mark loopBody205_52

def loopBody205_54 : HolLoopProg 64 :=
.seq loopBody205_19 loopBody205_53

def loopBody205_55 : HolLoopProg 64 :=
.mark loopBody205_54

def loopBody205_56 : HolLoopProg 64 :=
.seq loopBody205_17 loopBody205_55

def loopBody205_57 : HolLoopProg 64 :=
.mark loopBody205_56

def loopBody205_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody205_59 : HolLoopProg 64 :=
.mark loopBody205_58

def loopBody205_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody205_61 : HolLoopProg 64 :=
.mark loopBody205_60

def loopBody205_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7]

def loopBody205_63 : HolLoopProg 64 :=
.mark loopBody205_62

def loopBody205_64 : HolLoopProg 64 :=
.seq loopBody205_63 loopBody205_1

def loopBody205_65 : HolLoopProg 64 :=
.mark loopBody205_64

def loopBody205_66 : HolLoopProg 64 :=
.seq loopBody205_61 loopBody205_65

def loopBody205_67 : HolLoopProg 64 :=
.mark loopBody205_66

def loopBody205_68 : HolLoopProg 64 :=
.seq loopBody205_59 loopBody205_67

def loopBody205_69 : HolLoopProg 64 :=
.mark loopBody205_68

def loopBody205_70 : HolLoopProg 64 :=
.seq loopBody205_57 loopBody205_69

def loopBody205_71 : HolLoopProg 64 :=
.mark loopBody205_70

def loopBody205_72 : HolLoopProg 64 :=
.seq loopBody205_15 loopBody205_71

def loopBody205_73 : HolLoopProg 64 :=
.mark loopBody205_72

def loopBody205_74 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_73

def loopBody205_75 : HolLoopProg 64 :=
.mark loopBody205_74

def loopBody205_76 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_75

def loopBody205_77 : HolLoopProg 64 :=
.mark loopBody205_76

def loopBody205_78 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_77

def loopBody205_79 : HolLoopProg 64 :=
.mark loopBody205_78

def loopBody205_80 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_79

def loopBody205_81 : HolLoopProg 64 :=
.mark loopBody205_80

def loopBody205_82 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_81

def loopBody205_83 : HolLoopProg 64 :=
.mark loopBody205_82

def loopBody205_84 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_83

def loopBody205_85 : HolLoopProg 64 :=
.mark loopBody205_84

def loopBody205_86 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_85

def loopBody205_87 : HolLoopProg 64 :=
.mark loopBody205_86

def loopBody205_88 : HolLoopProg 64 :=
.seq loopBody205_1 loopBody205_87

def loopBody205_89 : HolLoopProg 64 :=
.mark loopBody205_88

def output205 : Nat × List Nat × HolLoopProg 64 :=
  (269, [0, 1], loopBody205_89)
end InitECandidate.Proofs.FrontendStages.Loop
