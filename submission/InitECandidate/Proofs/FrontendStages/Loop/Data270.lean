import InitECandidate.Proofs.FrontendStages.Loop.Translate254
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody270_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody270_1 : HolLoopProg 64 :=
.mark loopBody270_0

def loopBody270_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody270_3 : HolLoopProg 64 :=
.mark loopBody270_2

def loopBody270_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody270_5 : HolLoopProg 64 :=
.mark loopBody270_4

def loopBody270_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody270_7 : HolLoopProg 64 :=
.mark loopBody270_6

def loopBody270_8 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 161) ([6, 7]) (some (6, loopBody270_7, loopBody270_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody270_9 : HolLoopProg 64 :=
.mark loopBody270_8

def loopBody270_10 : HolLoopProg 64 :=
.seq loopBody270_9 loopBody270_1

def loopBody270_11 : HolLoopProg 64 :=
.mark loopBody270_10

def loopBody270_12 : HolLoopProg 64 :=
.seq loopBody270_5 loopBody270_11

def loopBody270_13 : HolLoopProg 64 :=
.mark loopBody270_12

def loopBody270_14 : HolLoopProg 64 :=
.seq loopBody270_3 loopBody270_13

def loopBody270_15 : HolLoopProg 64 :=
.mark loopBody270_14

def loopBody270_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody270_17 : HolLoopProg 64 :=
.mark loopBody270_16

def loopBody270_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody270_19 : HolLoopProg 64 :=
.mark loopBody270_18

def loopBody270_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody270_21 : HolLoopProg 64 :=
.mark loopBody270_20

def loopBody270_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody270_23 : HolLoopProg 64 :=
.mark loopBody270_22

def loopBody270_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody270_21 loopBody270_23 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody270_25 : HolLoopProg 64 :=
.mark loopBody270_24

def loopBody270_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody270_27 : HolLoopProg 64 :=
.mark loopBody270_26

def loopBody270_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 15#64)

def loopBody270_29 : HolLoopProg 64 :=
.mark loopBody270_28

def loopBody270_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody270_31 : HolLoopProg 64 :=
.mark loopBody270_30

def loopBody270_32 : HolLoopProg 64 :=
.seq loopBody270_31 loopBody270_1

def loopBody270_33 : HolLoopProg 64 :=
.mark loopBody270_32

def loopBody270_34 : HolLoopProg 64 :=
.seq loopBody270_33 loopBody270_1

def loopBody270_35 : HolLoopProg 64 :=
.mark loopBody270_34

def loopBody270_36 : HolLoopProg 64 :=
.seq loopBody270_29 loopBody270_35

def loopBody270_37 : HolLoopProg 64 :=
.mark loopBody270_36

def loopBody270_38 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_37

def loopBody270_39 : HolLoopProg 64 :=
.mark loopBody270_38

def loopBody270_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 6#64)

def loopBody270_41 : HolLoopProg 64 :=
.mark loopBody270_40

def loopBody270_42 : HolLoopProg 64 :=
.seq loopBody270_41 loopBody270_7

def loopBody270_43 : HolLoopProg 64 :=
.mark loopBody270_42

def loopBody270_44 : HolLoopProg 64 :=
.seq loopBody270_39 loopBody270_43

def loopBody270_45 : HolLoopProg 64 :=
.mark loopBody270_44

def loopBody270_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody270_45 loopBody270_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody270_47 : HolLoopProg 64 :=
.mark loopBody270_46

def loopBody270_48 : HolLoopProg 64 :=
.seq loopBody270_47 loopBody270_1

def loopBody270_49 : HolLoopProg 64 :=
.mark loopBody270_48

def loopBody270_50 : HolLoopProg 64 :=
.seq loopBody270_27 loopBody270_49

def loopBody270_51 : HolLoopProg 64 :=
.mark loopBody270_50

def loopBody270_52 : HolLoopProg 64 :=
.seq loopBody270_25 loopBody270_51

def loopBody270_53 : HolLoopProg 64 :=
.mark loopBody270_52

def loopBody270_54 : HolLoopProg 64 :=
.seq loopBody270_19 loopBody270_53

def loopBody270_55 : HolLoopProg 64 :=
.mark loopBody270_54

def loopBody270_56 : HolLoopProg 64 :=
.seq loopBody270_17 loopBody270_55

def loopBody270_57 : HolLoopProg 64 :=
.mark loopBody270_56

def loopBody270_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody270_59 : HolLoopProg 64 :=
.mark loopBody270_58

def loopBody270_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody270_61 : HolLoopProg 64 :=
.mark loopBody270_60

def loopBody270_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7]

def loopBody270_63 : HolLoopProg 64 :=
.mark loopBody270_62

def loopBody270_64 : HolLoopProg 64 :=
.seq loopBody270_63 loopBody270_1

def loopBody270_65 : HolLoopProg 64 :=
.mark loopBody270_64

def loopBody270_66 : HolLoopProg 64 :=
.seq loopBody270_61 loopBody270_65

def loopBody270_67 : HolLoopProg 64 :=
.mark loopBody270_66

def loopBody270_68 : HolLoopProg 64 :=
.seq loopBody270_59 loopBody270_67

def loopBody270_69 : HolLoopProg 64 :=
.mark loopBody270_68

def loopBody270_70 : HolLoopProg 64 :=
.seq loopBody270_57 loopBody270_69

def loopBody270_71 : HolLoopProg 64 :=
.mark loopBody270_70

def loopBody270_72 : HolLoopProg 64 :=
.seq loopBody270_15 loopBody270_71

def loopBody270_73 : HolLoopProg 64 :=
.mark loopBody270_72

def loopBody270_74 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_73

def loopBody270_75 : HolLoopProg 64 :=
.mark loopBody270_74

def loopBody270_76 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_75

def loopBody270_77 : HolLoopProg 64 :=
.mark loopBody270_76

def loopBody270_78 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_77

def loopBody270_79 : HolLoopProg 64 :=
.mark loopBody270_78

def loopBody270_80 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_79

def loopBody270_81 : HolLoopProg 64 :=
.mark loopBody270_80

def loopBody270_82 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_81

def loopBody270_83 : HolLoopProg 64 :=
.mark loopBody270_82

def loopBody270_84 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_83

def loopBody270_85 : HolLoopProg 64 :=
.mark loopBody270_84

def loopBody270_86 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_85

def loopBody270_87 : HolLoopProg 64 :=
.mark loopBody270_86

def loopBody270_88 : HolLoopProg 64 :=
.seq loopBody270_1 loopBody270_87

def loopBody270_89 : HolLoopProg 64 :=
.mark loopBody270_88

def output270 : Nat × List Nat × HolLoopProg 64 :=
  (334, [0, 1], loopBody270_89)
end InitECandidate.Proofs.FrontendStages.Loop
