import InitECandidate.Proofs.FrontendStages.Loop.Translate278
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody294_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody294_1 : HolLoopProg 64 :=
.mark loopBody294_0

def loopBody294_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody294_3 : HolLoopProg 64 :=
.mark loopBody294_2

def loopBody294_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 33#64)

def loopBody294_5 : HolLoopProg 64 :=
.mark loopBody294_4

def loopBody294_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 6 6 4 5)

def loopBody294_7 : HolLoopProg 64 :=
.mark loopBody294_6

def loopBody294_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody294_9 : HolLoopProg 64 :=
.mark loopBody294_8

def loopBody294_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody294_11 : HolLoopProg 64 :=
.mark loopBody294_10

def loopBody294_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody294_13 : HolLoopProg 64 :=
.mark loopBody294_12

def loopBody294_14 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 178) ([7, 8]) (some (4, loopBody294_13, loopBody294_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody294_15 : HolLoopProg 64 :=
.mark loopBody294_14

def loopBody294_16 : HolLoopProg 64 :=
.seq loopBody294_15 loopBody294_1

def loopBody294_17 : HolLoopProg 64 :=
.mark loopBody294_16

def loopBody294_18 : HolLoopProg 64 :=
.seq loopBody294_11 loopBody294_17

def loopBody294_19 : HolLoopProg 64 :=
.mark loopBody294_18

def loopBody294_20 : HolLoopProg 64 :=
.seq loopBody294_9 loopBody294_19

def loopBody294_21 : HolLoopProg 64 :=
.mark loopBody294_20

def loopBody294_22 : HolLoopProg 64 :=
.seq loopBody294_7 loopBody294_21

def loopBody294_23 : HolLoopProg 64 :=
.mark loopBody294_22

def loopBody294_24 : HolLoopProg 64 :=
.seq loopBody294_5 loopBody294_23

def loopBody294_25 : HolLoopProg 64 :=
.mark loopBody294_24

def loopBody294_26 : HolLoopProg 64 :=
.seq loopBody294_3 loopBody294_25

def loopBody294_27 : HolLoopProg 64 :=
.mark loopBody294_26

def loopBody294_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3])

def loopBody294_29 : HolLoopProg 64 :=
.mark loopBody294_28

def loopBody294_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody294_31 : HolLoopProg 64 :=
.mark loopBody294_30

def loopBody294_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody294_33 : HolLoopProg 64 :=
.mark loopBody294_32

def loopBody294_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody294_35 : HolLoopProg 64 :=
.mark loopBody294_34

def loopBody294_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody294_37 : HolLoopProg 64 :=
.mark loopBody294_36

def loopBody294_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody294_39 : HolLoopProg 64 :=
.mark loopBody294_38

def loopBody294_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody294_37 loopBody294_39 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody294_41 : HolLoopProg 64 :=
.mark loopBody294_40

def loopBody294_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody294_43 : HolLoopProg 64 :=
.mark loopBody294_42

def loopBody294_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody294_45 : HolLoopProg 64 :=
.mark loopBody294_44

def loopBody294_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 5#64)])

def loopBody294_47 : HolLoopProg 64 :=
.mark loopBody294_46

def loopBody294_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 32#64)

def loopBody294_49 : HolLoopProg 64 :=
.mark loopBody294_48

def loopBody294_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody294_51 : HolLoopProg 64 :=
.mark loopBody294_50

def loopBody294_52 : HolLoopProg 64 :=
.call (some
  ([3],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))) (some 176) ([6, 7, 8]) (some (6, loopBody294_51, loopBody294_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody294_53 : HolLoopProg 64 :=
.mark loopBody294_52

def loopBody294_54 : HolLoopProg 64 :=
.seq loopBody294_53 loopBody294_1

def loopBody294_55 : HolLoopProg 64 :=
.mark loopBody294_54

def loopBody294_56 : HolLoopProg 64 :=
.seq loopBody294_49 loopBody294_55

def loopBody294_57 : HolLoopProg 64 :=
.mark loopBody294_56

def loopBody294_58 : HolLoopProg 64 :=
.seq loopBody294_47 loopBody294_57

def loopBody294_59 : HolLoopProg 64 :=
.mark loopBody294_58

def loopBody294_60 : HolLoopProg 64 :=
.seq loopBody294_45 loopBody294_59

def loopBody294_61 : HolLoopProg 64 :=
.mark loopBody294_60

def loopBody294_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 3])

def loopBody294_63 : HolLoopProg 64 :=
.mark loopBody294_62

def loopBody294_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 6)

def loopBody294_65 : HolLoopProg 64 :=
.mark loopBody294_64

def loopBody294_66 : HolLoopProg 64 :=
.seq loopBody294_65 loopBody294_1

def loopBody294_67 : HolLoopProg 64 :=
.mark loopBody294_66

def loopBody294_68 : HolLoopProg 64 :=
.seq loopBody294_67 loopBody294_1

def loopBody294_69 : HolLoopProg 64 :=
.mark loopBody294_68

def loopBody294_70 : HolLoopProg 64 :=
.seq loopBody294_63 loopBody294_69

def loopBody294_71 : HolLoopProg 64 :=
.mark loopBody294_70

def loopBody294_72 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_71

def loopBody294_73 : HolLoopProg 64 :=
.mark loopBody294_72

def loopBody294_74 : HolLoopProg 64 :=
.seq loopBody294_61 loopBody294_73

def loopBody294_75 : HolLoopProg 64 :=
.mark loopBody294_74

def loopBody294_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody294_77 : HolLoopProg 64 :=
.mark loopBody294_76

def loopBody294_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody294_79 : HolLoopProg 64 :=
.mark loopBody294_78

def loopBody294_80 : HolLoopProg 64 :=
.seq loopBody294_79 loopBody294_1

def loopBody294_81 : HolLoopProg 64 :=
.mark loopBody294_80

def loopBody294_82 : HolLoopProg 64 :=
.seq loopBody294_81 loopBody294_1

def loopBody294_83 : HolLoopProg 64 :=
.mark loopBody294_82

def loopBody294_84 : HolLoopProg 64 :=
.seq loopBody294_77 loopBody294_83

def loopBody294_85 : HolLoopProg 64 :=
.mark loopBody294_84

def loopBody294_86 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_85

def loopBody294_87 : HolLoopProg 64 :=
.mark loopBody294_86

def loopBody294_88 : HolLoopProg 64 :=
.seq loopBody294_75 loopBody294_87

def loopBody294_89 : HolLoopProg 64 :=
.mark loopBody294_88

def loopBody294_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody294_91 : HolLoopProg 64 :=
.mark loopBody294_90

def loopBody294_92 : HolLoopProg 64 :=
.seq loopBody294_89 loopBody294_91

def loopBody294_93 : HolLoopProg 64 :=
.mark loopBody294_92

def loopBody294_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody294_95 : HolLoopProg 64 :=
.mark loopBody294_94

def loopBody294_96 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody294_93 loopBody294_95 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody294_97 : HolLoopProg 64 :=
.mark loopBody294_96

def loopBody294_98 : HolLoopProg 64 :=
.seq loopBody294_97 loopBody294_1

def loopBody294_99 : HolLoopProg 64 :=
.mark loopBody294_98

def loopBody294_100 : HolLoopProg 64 :=
.seq loopBody294_43 loopBody294_99

def loopBody294_101 : HolLoopProg 64 :=
.mark loopBody294_100

def loopBody294_102 : HolLoopProg 64 :=
.seq loopBody294_41 loopBody294_101

def loopBody294_103 : HolLoopProg 64 :=
.mark loopBody294_102

def loopBody294_104 : HolLoopProg 64 :=
.seq loopBody294_35 loopBody294_103

def loopBody294_105 : HolLoopProg 64 :=
.mark loopBody294_104

def loopBody294_106 : HolLoopProg 64 :=
.seq loopBody294_33 loopBody294_105

def loopBody294_107 : HolLoopProg 64 :=
.mark loopBody294_106

def loopBody294_108 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody294_107 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody294_109 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 0])

def loopBody294_110 : HolLoopProg 64 :=
.mark loopBody294_109

def loopBody294_111 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody294_112 : HolLoopProg 64 :=
.mark loopBody294_111

def loopBody294_113 : HolLoopProg 64 :=
.seq loopBody294_112 loopBody294_1

def loopBody294_114 : HolLoopProg 64 :=
.mark loopBody294_113

def loopBody294_115 : HolLoopProg 64 :=
.seq loopBody294_110 loopBody294_114

def loopBody294_116 : HolLoopProg 64 :=
.mark loopBody294_115

def loopBody294_117 : HolLoopProg 64 :=
.seq loopBody294_108 loopBody294_116

def loopBody294_118 : HolLoopProg 64 :=
.seq loopBody294_31 loopBody294_117

def loopBody294_119 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_118

def loopBody294_120 : HolLoopProg 64 :=
.seq loopBody294_29 loopBody294_119

def loopBody294_121 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_120

def loopBody294_122 : HolLoopProg 64 :=
.seq loopBody294_27 loopBody294_121

def loopBody294_123 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_122

def loopBody294_124 : HolLoopProg 64 :=
.seq loopBody294_1 loopBody294_123

def output294 : Nat × List Nat × HolLoopProg 64 :=
  (358, [0, 1, 2], loopBody294_124)
end InitECandidate.Proofs.FrontendStages.Loop
