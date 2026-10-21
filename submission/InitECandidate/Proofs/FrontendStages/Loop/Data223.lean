import InitECandidate.Proofs.FrontendStages.Loop.Translate207
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody223_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody223_1 : HolLoopProg 64 :=
.mark loopBody223_0

def loopBody223_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody223_3 : HolLoopProg 64 :=
.mark loopBody223_2

def loopBody223_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody223_5 : HolLoopProg 64 :=
.mark loopBody223_4

def loopBody223_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody223_7 : HolLoopProg 64 :=
.mark loopBody223_6

def loopBody223_8 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 92) ([5, 6]) (some (5, loopBody223_7, loopBody223_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody223_9 : HolLoopProg 64 :=
.mark loopBody223_8

def loopBody223_10 : HolLoopProg 64 :=
.seq loopBody223_9 loopBody223_1

def loopBody223_11 : HolLoopProg 64 :=
.mark loopBody223_10

def loopBody223_12 : HolLoopProg 64 :=
.seq loopBody223_5 loopBody223_11

def loopBody223_13 : HolLoopProg 64 :=
.mark loopBody223_12

def loopBody223_14 : HolLoopProg 64 :=
.seq loopBody223_3 loopBody223_13

def loopBody223_15 : HolLoopProg 64 :=
.mark loopBody223_14

def loopBody223_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody223_17 : HolLoopProg 64 :=
.mark loopBody223_16

def loopBody223_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody223_19 : HolLoopProg 64 :=
.mark loopBody223_18

def loopBody223_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody223_21 : HolLoopProg 64 :=
.mark loopBody223_20

def loopBody223_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody223_23 : HolLoopProg 64 :=
.mark loopBody223_22

def loopBody223_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody223_25 : HolLoopProg 64 :=
.mark loopBody223_24

def loopBody223_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody223_23 loopBody223_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody223_27 : HolLoopProg 64 :=
.mark loopBody223_26

def loopBody223_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody223_29 : HolLoopProg 64 :=
.mark loopBody223_28

def loopBody223_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 5])

def loopBody223_31 : HolLoopProg 64 :=
.mark loopBody223_30

def loopBody223_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody223_33 : HolLoopProg 64 :=
.mark loopBody223_32

def loopBody223_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 5])

def loopBody223_35 : HolLoopProg 64 :=
.mark loopBody223_34

def loopBody223_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody223_37 : HolLoopProg 64 :=
.mark loopBody223_36

def loopBody223_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody223_39 : HolLoopProg 64 :=
.mark loopBody223_38

def loopBody223_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody223_41 : HolLoopProg 64 :=
.mark loopBody223_40

def loopBody223_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody223_43 : HolLoopProg 64 :=
.mark loopBody223_42

def loopBody223_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody223_45 : HolLoopProg 64 :=
.mark loopBody223_44

def loopBody223_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.reg 10) loopBody223_43 loopBody223_45 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody223_47 : HolLoopProg 64 :=
.mark loopBody223_46

def loopBody223_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody223_49 : HolLoopProg 64 :=
.mark loopBody223_48

def loopBody223_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody223_51 : HolLoopProg 64 :=
.mark loopBody223_50

def loopBody223_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody223_53 : HolLoopProg 64 :=
.mark loopBody223_52

def loopBody223_54 : HolLoopProg 64 :=
.seq loopBody223_53 loopBody223_1

def loopBody223_55 : HolLoopProg 64 :=
.mark loopBody223_54

def loopBody223_56 : HolLoopProg 64 :=
.seq loopBody223_51 loopBody223_55

def loopBody223_57 : HolLoopProg 64 :=
.mark loopBody223_56

def loopBody223_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody223_57 loopBody223_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody223_59 : HolLoopProg 64 :=
.mark loopBody223_58

def loopBody223_60 : HolLoopProg 64 :=
.seq loopBody223_59 loopBody223_1

def loopBody223_61 : HolLoopProg 64 :=
.mark loopBody223_60

def loopBody223_62 : HolLoopProg 64 :=
.seq loopBody223_49 loopBody223_61

def loopBody223_63 : HolLoopProg 64 :=
.mark loopBody223_62

def loopBody223_64 : HolLoopProg 64 :=
.seq loopBody223_47 loopBody223_63

def loopBody223_65 : HolLoopProg 64 :=
.mark loopBody223_64

def loopBody223_66 : HolLoopProg 64 :=
.seq loopBody223_41 loopBody223_65

def loopBody223_67 : HolLoopProg 64 :=
.mark loopBody223_66

def loopBody223_68 : HolLoopProg 64 :=
.seq loopBody223_39 loopBody223_67

def loopBody223_69 : HolLoopProg 64 :=
.mark loopBody223_68

def loopBody223_70 : HolLoopProg 64 :=
.seq loopBody223_37 loopBody223_69

def loopBody223_71 : HolLoopProg 64 :=
.mark loopBody223_70

def loopBody223_72 : HolLoopProg 64 :=
.seq loopBody223_35 loopBody223_71

def loopBody223_73 : HolLoopProg 64 :=
.mark loopBody223_72

def loopBody223_74 : HolLoopProg 64 :=
.seq loopBody223_33 loopBody223_73

def loopBody223_75 : HolLoopProg 64 :=
.mark loopBody223_74

def loopBody223_76 : HolLoopProg 64 :=
.seq loopBody223_31 loopBody223_75

def loopBody223_77 : HolLoopProg 64 :=
.mark loopBody223_76

def loopBody223_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody223_79 : HolLoopProg 64 :=
.mark loopBody223_78

def loopBody223_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody223_81 : HolLoopProg 64 :=
.mark loopBody223_80

def loopBody223_82 : HolLoopProg 64 :=
.seq loopBody223_81 loopBody223_1

def loopBody223_83 : HolLoopProg 64 :=
.mark loopBody223_82

def loopBody223_84 : HolLoopProg 64 :=
.seq loopBody223_83 loopBody223_1

def loopBody223_85 : HolLoopProg 64 :=
.mark loopBody223_84

def loopBody223_86 : HolLoopProg 64 :=
.seq loopBody223_79 loopBody223_85

def loopBody223_87 : HolLoopProg 64 :=
.mark loopBody223_86

def loopBody223_88 : HolLoopProg 64 :=
.seq loopBody223_1 loopBody223_87

def loopBody223_89 : HolLoopProg 64 :=
.mark loopBody223_88

def loopBody223_90 : HolLoopProg 64 :=
.seq loopBody223_77 loopBody223_89

def loopBody223_91 : HolLoopProg 64 :=
.mark loopBody223_90

def loopBody223_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody223_93 : HolLoopProg 64 :=
.mark loopBody223_92

def loopBody223_94 : HolLoopProg 64 :=
.seq loopBody223_91 loopBody223_93

def loopBody223_95 : HolLoopProg 64 :=
.mark loopBody223_94

def loopBody223_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody223_97 : HolLoopProg 64 :=
.mark loopBody223_96

def loopBody223_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody223_95 loopBody223_97 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody223_99 : HolLoopProg 64 :=
.mark loopBody223_98

def loopBody223_100 : HolLoopProg 64 :=
.seq loopBody223_99 loopBody223_1

def loopBody223_101 : HolLoopProg 64 :=
.mark loopBody223_100

def loopBody223_102 : HolLoopProg 64 :=
.seq loopBody223_29 loopBody223_101

def loopBody223_103 : HolLoopProg 64 :=
.mark loopBody223_102

def loopBody223_104 : HolLoopProg 64 :=
.seq loopBody223_27 loopBody223_103

def loopBody223_105 : HolLoopProg 64 :=
.mark loopBody223_104

def loopBody223_106 : HolLoopProg 64 :=
.seq loopBody223_21 loopBody223_105

def loopBody223_107 : HolLoopProg 64 :=
.mark loopBody223_106

def loopBody223_108 : HolLoopProg 64 :=
.seq loopBody223_19 loopBody223_107

def loopBody223_109 : HolLoopProg 64 :=
.mark loopBody223_108

def loopBody223_110 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody223_109 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody223_111 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody223_112 : HolLoopProg 64 :=
.mark loopBody223_111

def loopBody223_113 : HolLoopProg 64 :=
.seq loopBody223_112 loopBody223_55

def loopBody223_114 : HolLoopProg 64 :=
.mark loopBody223_113

def loopBody223_115 : HolLoopProg 64 :=
.seq loopBody223_110 loopBody223_114

def loopBody223_116 : HolLoopProg 64 :=
.seq loopBody223_17 loopBody223_115

def loopBody223_117 : HolLoopProg 64 :=
.seq loopBody223_1 loopBody223_116

def loopBody223_118 : HolLoopProg 64 :=
.seq loopBody223_15 loopBody223_117

def loopBody223_119 : HolLoopProg 64 :=
.seq loopBody223_1 loopBody223_118

def loopBody223_120 : HolLoopProg 64 :=
.seq loopBody223_1 loopBody223_119

def output223 : Nat × List Nat × HolLoopProg 64 :=
  (287, [0, 1, 2, 3], loopBody223_120)
end InitECandidate.Proofs.FrontendStages.Loop
