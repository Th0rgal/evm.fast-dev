import InitECandidate.Proofs.FrontendStages.Loop.Translate330
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody346_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody346_1 : HolLoopProg 64 :=
.mark loopBody346_0

def loopBody346_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody346_3 : HolLoopProg 64 :=
.mark loopBody346_2

def loopBody346_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody346_5 : HolLoopProg 64 :=
.mark loopBody346_4

def loopBody346_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody346_7 : HolLoopProg 64 :=
.mark loopBody346_6

def loopBody346_8 : HolLoopProg 64 :=
.call (some ([1, 2], Flapjack.Spt.ls PUnit.unit)) (some 186) ([3, 4]) (some (3, loopBody346_7, loopBody346_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody346_9 : HolLoopProg 64 :=
.mark loopBody346_8

def loopBody346_10 : HolLoopProg 64 :=
.seq loopBody346_9 loopBody346_1

def loopBody346_11 : HolLoopProg 64 :=
.mark loopBody346_10

def loopBody346_12 : HolLoopProg 64 :=
.seq loopBody346_5 loopBody346_11

def loopBody346_13 : HolLoopProg 64 :=
.mark loopBody346_12

def loopBody346_14 : HolLoopProg 64 :=
.seq loopBody346_3 loopBody346_13

def loopBody346_15 : HolLoopProg 64 :=
.mark loopBody346_14

def loopBody346_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody346_17 : HolLoopProg 64 :=
.mark loopBody346_16

def loopBody346_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody346_19 : HolLoopProg 64 :=
.mark loopBody346_18

def loopBody346_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody346_21 : HolLoopProg 64 :=
.mark loopBody346_20

def loopBody346_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody346_23 : HolLoopProg 64 :=
.mark loopBody346_22

def loopBody346_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody346_21 loopBody346_23 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody346_25 : HolLoopProg 64 :=
.mark loopBody346_24

def loopBody346_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody346_27 : HolLoopProg 64 :=
.mark loopBody346_26

def loopBody346_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 24#64]))

def loopBody346_29 : HolLoopProg 64 :=
.mark loopBody346_28

def loopBody346_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody346_21 loopBody346_23 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody346_31 : HolLoopProg 64 :=
.mark loopBody346_30

def loopBody346_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody346_33 : HolLoopProg 64 :=
.mark loopBody346_32

def loopBody346_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody346_35 : HolLoopProg 64 :=
.mark loopBody346_34

def loopBody346_36 : HolLoopProg 64 :=
.seq loopBody346_35 loopBody346_1

def loopBody346_37 : HolLoopProg 64 :=
.mark loopBody346_36

def loopBody346_38 : HolLoopProg 64 :=
.seq loopBody346_33 loopBody346_37

def loopBody346_39 : HolLoopProg 64 :=
.mark loopBody346_38

def loopBody346_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody346_39 loopBody346_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody346_41 : HolLoopProg 64 :=
.mark loopBody346_40

def loopBody346_42 : HolLoopProg 64 :=
.seq loopBody346_41 loopBody346_1

def loopBody346_43 : HolLoopProg 64 :=
.mark loopBody346_42

def loopBody346_44 : HolLoopProg 64 :=
.seq loopBody346_27 loopBody346_43

def loopBody346_45 : HolLoopProg 64 :=
.mark loopBody346_44

def loopBody346_46 : HolLoopProg 64 :=
.seq loopBody346_31 loopBody346_45

def loopBody346_47 : HolLoopProg 64 :=
.mark loopBody346_46

def loopBody346_48 : HolLoopProg 64 :=
.seq loopBody346_29 loopBody346_47

def loopBody346_49 : HolLoopProg 64 :=
.mark loopBody346_48

def loopBody346_50 : HolLoopProg 64 :=
.seq loopBody346_23 loopBody346_49

def loopBody346_51 : HolLoopProg 64 :=
.mark loopBody346_50

def loopBody346_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody346_51 loopBody346_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody346_53 : HolLoopProg 64 :=
.mark loopBody346_52

def loopBody346_54 : HolLoopProg 64 :=
.seq loopBody346_53 loopBody346_1

def loopBody346_55 : HolLoopProg 64 :=
.mark loopBody346_54

def loopBody346_56 : HolLoopProg 64 :=
.seq loopBody346_27 loopBody346_55

def loopBody346_57 : HolLoopProg 64 :=
.mark loopBody346_56

def loopBody346_58 : HolLoopProg 64 :=
.seq loopBody346_25 loopBody346_57

def loopBody346_59 : HolLoopProg 64 :=
.mark loopBody346_58

def loopBody346_60 : HolLoopProg 64 :=
.seq loopBody346_19 loopBody346_59

def loopBody346_61 : HolLoopProg 64 :=
.mark loopBody346_60

def loopBody346_62 : HolLoopProg 64 :=
.seq loopBody346_17 loopBody346_61

def loopBody346_63 : HolLoopProg 64 :=
.mark loopBody346_62

def loopBody346_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody346_65 : HolLoopProg 64 :=
.mark loopBody346_64

def loopBody346_66 : HolLoopProg 64 :=
.seq loopBody346_65 loopBody346_13

def loopBody346_67 : HolLoopProg 64 :=
.mark loopBody346_66

def loopBody346_68 : HolLoopProg 64 :=
.seq loopBody346_63 loopBody346_67

def loopBody346_69 : HolLoopProg 64 :=
.mark loopBody346_68

def loopBody346_70 : HolLoopProg 64 :=
.seq loopBody346_69 loopBody346_63

def loopBody346_71 : HolLoopProg 64 :=
.mark loopBody346_70

def loopBody346_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody346_73 : HolLoopProg 64 :=
.mark loopBody346_72

def loopBody346_74 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ls PUnit.unit)) (some 392) ([4]) (some (4, loopBody346_73, loopBody346_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody346_75 : HolLoopProg 64 :=
.mark loopBody346_74

def loopBody346_76 : HolLoopProg 64 :=
.seq loopBody346_75 loopBody346_1

def loopBody346_77 : HolLoopProg 64 :=
.mark loopBody346_76

def loopBody346_78 : HolLoopProg 64 :=
.seq loopBody346_5 loopBody346_77

def loopBody346_79 : HolLoopProg 64 :=
.mark loopBody346_78

def loopBody346_80 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_79

def loopBody346_81 : HolLoopProg 64 :=
.mark loopBody346_80

def loopBody346_82 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_81

def loopBody346_83 : HolLoopProg 64 :=
.mark loopBody346_82

def loopBody346_84 : HolLoopProg 64 :=
.seq loopBody346_71 loopBody346_83

def loopBody346_85 : HolLoopProg 64 :=
.mark loopBody346_84

def loopBody346_86 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 399) ([4]) (some (4, loopBody346_73, loopBody346_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody346_87 : HolLoopProg 64 :=
.mark loopBody346_86

def loopBody346_88 : HolLoopProg 64 :=
.seq loopBody346_87 loopBody346_1

def loopBody346_89 : HolLoopProg 64 :=
.mark loopBody346_88

def loopBody346_90 : HolLoopProg 64 :=
.seq loopBody346_5 loopBody346_89

def loopBody346_91 : HolLoopProg 64 :=
.mark loopBody346_90

def loopBody346_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody346_93 : HolLoopProg 64 :=
.mark loopBody346_92

def loopBody346_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody346_95 : HolLoopProg 64 :=
.mark loopBody346_94

def loopBody346_96 : HolLoopProg 64 :=
.seq loopBody346_95 loopBody346_1

def loopBody346_97 : HolLoopProg 64 :=
.mark loopBody346_96

def loopBody346_98 : HolLoopProg 64 :=
.seq loopBody346_93 loopBody346_97

def loopBody346_99 : HolLoopProg 64 :=
.mark loopBody346_98

def loopBody346_100 : HolLoopProg 64 :=
.seq loopBody346_91 loopBody346_99

def loopBody346_101 : HolLoopProg 64 :=
.mark loopBody346_100

def loopBody346_102 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_101

def loopBody346_103 : HolLoopProg 64 :=
.mark loopBody346_102

def loopBody346_104 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_103

def loopBody346_105 : HolLoopProg 64 :=
.mark loopBody346_104

def loopBody346_106 : HolLoopProg 64 :=
.seq loopBody346_85 loopBody346_105

def loopBody346_107 : HolLoopProg 64 :=
.mark loopBody346_106

def loopBody346_108 : HolLoopProg 64 :=
.seq loopBody346_15 loopBody346_107

def loopBody346_109 : HolLoopProg 64 :=
.mark loopBody346_108

def loopBody346_110 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_109

def loopBody346_111 : HolLoopProg 64 :=
.mark loopBody346_110

def loopBody346_112 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_111

def loopBody346_113 : HolLoopProg 64 :=
.mark loopBody346_112

def loopBody346_114 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_113

def loopBody346_115 : HolLoopProg 64 :=
.mark loopBody346_114

def loopBody346_116 : HolLoopProg 64 :=
.seq loopBody346_1 loopBody346_115

def loopBody346_117 : HolLoopProg 64 :=
.mark loopBody346_116

def output346 : Nat × List Nat × HolLoopProg 64 :=
  (410, [0], loopBody346_117)
end InitECandidate.Proofs.FrontendStages.Loop
