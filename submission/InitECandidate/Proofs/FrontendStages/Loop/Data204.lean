import InitECandidate.Proofs.FrontendStages.Loop.Translate188
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody204_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody204_1 : HolLoopProg 64 :=
.mark loopBody204_0

def loopBody204_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody204_3 : HolLoopProg 64 :=
.mark loopBody204_2

def loopBody204_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody204_5 : HolLoopProg 64 :=
.mark loopBody204_4

def loopBody204_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody204_7 : HolLoopProg 64 :=
.mark loopBody204_6

def loopBody204_8 : HolLoopProg 64 :=
.call (some ([3, 4, 5, 6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 161) ([7, 8]) (some (7, loopBody204_7, loopBody204_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody204_9 : HolLoopProg 64 :=
.mark loopBody204_8

def loopBody204_10 : HolLoopProg 64 :=
.seq loopBody204_9 loopBody204_1

def loopBody204_11 : HolLoopProg 64 :=
.mark loopBody204_10

def loopBody204_12 : HolLoopProg 64 :=
.seq loopBody204_5 loopBody204_11

def loopBody204_13 : HolLoopProg 64 :=
.mark loopBody204_12

def loopBody204_14 : HolLoopProg 64 :=
.seq loopBody204_3 loopBody204_13

def loopBody204_15 : HolLoopProg 64 :=
.mark loopBody204_14

def loopBody204_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody204_17 : HolLoopProg 64 :=
.mark loopBody204_16

def loopBody204_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody204_19 : HolLoopProg 64 :=
.mark loopBody204_18

def loopBody204_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody204_21 : HolLoopProg 64 :=
.mark loopBody204_20

def loopBody204_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody204_23 : HolLoopProg 64 :=
.mark loopBody204_22

def loopBody204_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody204_21 loopBody204_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody204_25 : HolLoopProg 64 :=
.mark loopBody204_24

def loopBody204_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody204_27 : HolLoopProg 64 :=
.mark loopBody204_26

def loopBody204_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 6#64)

def loopBody204_29 : HolLoopProg 64 :=
.mark loopBody204_28

def loopBody204_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 7)

def loopBody204_31 : HolLoopProg 64 :=
.mark loopBody204_30

def loopBody204_32 : HolLoopProg 64 :=
.seq loopBody204_31 loopBody204_1

def loopBody204_33 : HolLoopProg 64 :=
.mark loopBody204_32

def loopBody204_34 : HolLoopProg 64 :=
.seq loopBody204_33 loopBody204_1

def loopBody204_35 : HolLoopProg 64 :=
.mark loopBody204_34

def loopBody204_36 : HolLoopProg 64 :=
.seq loopBody204_29 loopBody204_35

def loopBody204_37 : HolLoopProg 64 :=
.mark loopBody204_36

def loopBody204_38 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_37

def loopBody204_39 : HolLoopProg 64 :=
.mark loopBody204_38

def loopBody204_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 3#64)

def loopBody204_41 : HolLoopProg 64 :=
.mark loopBody204_40

def loopBody204_42 : HolLoopProg 64 :=
.seq loopBody204_41 loopBody204_7

def loopBody204_43 : HolLoopProg 64 :=
.mark loopBody204_42

def loopBody204_44 : HolLoopProg 64 :=
.seq loopBody204_39 loopBody204_43

def loopBody204_45 : HolLoopProg 64 :=
.mark loopBody204_44

def loopBody204_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody204_45 loopBody204_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody204_47 : HolLoopProg 64 :=
.mark loopBody204_46

def loopBody204_48 : HolLoopProg 64 :=
.seq loopBody204_47 loopBody204_1

def loopBody204_49 : HolLoopProg 64 :=
.mark loopBody204_48

def loopBody204_50 : HolLoopProg 64 :=
.seq loopBody204_27 loopBody204_49

def loopBody204_51 : HolLoopProg 64 :=
.mark loopBody204_50

def loopBody204_52 : HolLoopProg 64 :=
.seq loopBody204_25 loopBody204_51

def loopBody204_53 : HolLoopProg 64 :=
.mark loopBody204_52

def loopBody204_54 : HolLoopProg 64 :=
.seq loopBody204_19 loopBody204_53

def loopBody204_55 : HolLoopProg 64 :=
.mark loopBody204_54

def loopBody204_56 : HolLoopProg 64 :=
.seq loopBody204_17 loopBody204_55

def loopBody204_57 : HolLoopProg 64 :=
.mark loopBody204_56

def loopBody204_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody204_59 : HolLoopProg 64 :=
.mark loopBody204_58

def loopBody204_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody204_61 : HolLoopProg 64 :=
.mark loopBody204_60

def loopBody204_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody204_21 loopBody204_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  Flapjack.Spt.ln)

def loopBody204_63 : HolLoopProg 64 :=
.mark loopBody204_62

def loopBody204_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 7#64)

def loopBody204_65 : HolLoopProg 64 :=
.mark loopBody204_64

def loopBody204_66 : HolLoopProg 64 :=
.seq loopBody204_65 loopBody204_35

def loopBody204_67 : HolLoopProg 64 :=
.mark loopBody204_66

def loopBody204_68 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_67

def loopBody204_69 : HolLoopProg 64 :=
.mark loopBody204_68

def loopBody204_70 : HolLoopProg 64 :=
.seq loopBody204_69 loopBody204_43

def loopBody204_71 : HolLoopProg 64 :=
.mark loopBody204_70

def loopBody204_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody204_71 loopBody204_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody204_73 : HolLoopProg 64 :=
.mark loopBody204_72

def loopBody204_74 : HolLoopProg 64 :=
.seq loopBody204_73 loopBody204_1

def loopBody204_75 : HolLoopProg 64 :=
.mark loopBody204_74

def loopBody204_76 : HolLoopProg 64 :=
.seq loopBody204_27 loopBody204_75

def loopBody204_77 : HolLoopProg 64 :=
.mark loopBody204_76

def loopBody204_78 : HolLoopProg 64 :=
.seq loopBody204_63 loopBody204_77

def loopBody204_79 : HolLoopProg 64 :=
.mark loopBody204_78

def loopBody204_80 : HolLoopProg 64 :=
.seq loopBody204_61 loopBody204_79

def loopBody204_81 : HolLoopProg 64 :=
.mark loopBody204_80

def loopBody204_82 : HolLoopProg 64 :=
.seq loopBody204_59 loopBody204_81

def loopBody204_83 : HolLoopProg 64 :=
.mark loopBody204_82

def loopBody204_84 : HolLoopProg 64 :=
.seq loopBody204_57 loopBody204_83

def loopBody204_85 : HolLoopProg 64 :=
.mark loopBody204_84

def loopBody204_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody204_87 : HolLoopProg 64 :=
.mark loopBody204_86

def loopBody204_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody204_89 : HolLoopProg 64 :=
.mark loopBody204_88

def loopBody204_90 : HolLoopProg 64 :=
.seq loopBody204_89 loopBody204_1

def loopBody204_91 : HolLoopProg 64 :=
.mark loopBody204_90

def loopBody204_92 : HolLoopProg 64 :=
.seq loopBody204_87 loopBody204_91

def loopBody204_93 : HolLoopProg 64 :=
.mark loopBody204_92

def loopBody204_94 : HolLoopProg 64 :=
.seq loopBody204_85 loopBody204_93

def loopBody204_95 : HolLoopProg 64 :=
.mark loopBody204_94

def loopBody204_96 : HolLoopProg 64 :=
.seq loopBody204_15 loopBody204_95

def loopBody204_97 : HolLoopProg 64 :=
.mark loopBody204_96

def loopBody204_98 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_97

def loopBody204_99 : HolLoopProg 64 :=
.mark loopBody204_98

def loopBody204_100 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_99

def loopBody204_101 : HolLoopProg 64 :=
.mark loopBody204_100

def loopBody204_102 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_101

def loopBody204_103 : HolLoopProg 64 :=
.mark loopBody204_102

def loopBody204_104 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_103

def loopBody204_105 : HolLoopProg 64 :=
.mark loopBody204_104

def loopBody204_106 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_105

def loopBody204_107 : HolLoopProg 64 :=
.mark loopBody204_106

def loopBody204_108 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_107

def loopBody204_109 : HolLoopProg 64 :=
.mark loopBody204_108

def loopBody204_110 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_109

def loopBody204_111 : HolLoopProg 64 :=
.mark loopBody204_110

def loopBody204_112 : HolLoopProg 64 :=
.seq loopBody204_1 loopBody204_111

def loopBody204_113 : HolLoopProg 64 :=
.mark loopBody204_112

def output204 : Nat × List Nat × HolLoopProg 64 :=
  (268, [0, 1, 2], loopBody204_113)
end InitECandidate.Proofs.FrontendStages.Loop
