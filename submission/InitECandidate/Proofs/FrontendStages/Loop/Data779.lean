import InitECandidate.Proofs.FrontendStages.Loop.Translate763
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody779_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody779_1 : HolLoopProg 64 :=
.mark loopBody779_0

def loopBody779_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody779_3 : HolLoopProg 64 :=
.mark loopBody779_2

def loopBody779_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody779_3, loopBody779_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody779_5 : HolLoopProg 64 :=
.mark loopBody779_4

def loopBody779_6 : HolLoopProg 64 :=
.seq loopBody779_5 loopBody779_1

def loopBody779_7 : HolLoopProg 64 :=
.mark loopBody779_6

def loopBody779_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64),
      Flapjack.HolLoopExp.const 8#64])

def loopBody779_9 : HolLoopProg 64 :=
.mark loopBody779_8

def loopBody779_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody779_11 : HolLoopProg 64 :=
.mark loopBody779_10

def loopBody779_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody779_11, loopBody779_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody779_13 : HolLoopProg 64 :=
.mark loopBody779_12

def loopBody779_14 : HolLoopProg 64 :=
.seq loopBody779_13 loopBody779_1

def loopBody779_15 : HolLoopProg 64 :=
.mark loopBody779_14

def loopBody779_16 : HolLoopProg 64 :=
.seq loopBody779_9 loopBody779_15

def loopBody779_17 : HolLoopProg 64 :=
.mark loopBody779_16

def loopBody779_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody779_19 : HolLoopProg 64 :=
.mark loopBody779_18

def loopBody779_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody779_21 : HolLoopProg 64 :=
.mark loopBody779_20

def loopBody779_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody779_23 : HolLoopProg 64 :=
.mark loopBody779_22

def loopBody779_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody779_25 : HolLoopProg 64 :=
.mark loopBody779_24

def loopBody779_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody779_27 : HolLoopProg 64 :=
.mark loopBody779_26

def loopBody779_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody779_25 loopBody779_27 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody779_29 : HolLoopProg 64 :=
.mark loopBody779_28

def loopBody779_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody779_31 : HolLoopProg 64 :=
.mark loopBody779_30

def loopBody779_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody779_33 : HolLoopProg 64 :=
.mark loopBody779_32

def loopBody779_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody779_35 : HolLoopProg 64 :=
.mark loopBody779_34

def loopBody779_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 4,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 5#64)])

def loopBody779_37 : HolLoopProg 64 :=
.mark loopBody779_36

def loopBody779_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody779_39 : HolLoopProg 64 :=
.mark loopBody779_38

def loopBody779_40 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 153) ([7, 8, 9]) (some (7, loopBody779_39, loopBody779_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody779_41 : HolLoopProg 64 :=
.mark loopBody779_40

def loopBody779_42 : HolLoopProg 64 :=
.seq loopBody779_41 loopBody779_1

def loopBody779_43 : HolLoopProg 64 :=
.mark loopBody779_42

def loopBody779_44 : HolLoopProg 64 :=
.seq loopBody779_37 loopBody779_43

def loopBody779_45 : HolLoopProg 64 :=
.mark loopBody779_44

def loopBody779_46 : HolLoopProg 64 :=
.seq loopBody779_35 loopBody779_45

def loopBody779_47 : HolLoopProg 64 :=
.mark loopBody779_46

def loopBody779_48 : HolLoopProg 64 :=
.seq loopBody779_33 loopBody779_47

def loopBody779_49 : HolLoopProg 64 :=
.mark loopBody779_48

def loopBody779_50 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_49

def loopBody779_51 : HolLoopProg 64 :=
.mark loopBody779_50

def loopBody779_52 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_51

def loopBody779_53 : HolLoopProg 64 :=
.mark loopBody779_52

def loopBody779_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody779_55 : HolLoopProg 64 :=
.mark loopBody779_54

def loopBody779_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody779_57 : HolLoopProg 64 :=
.mark loopBody779_56

def loopBody779_58 : HolLoopProg 64 :=
.seq loopBody779_57 loopBody779_1

def loopBody779_59 : HolLoopProg 64 :=
.mark loopBody779_58

def loopBody779_60 : HolLoopProg 64 :=
.seq loopBody779_59 loopBody779_1

def loopBody779_61 : HolLoopProg 64 :=
.mark loopBody779_60

def loopBody779_62 : HolLoopProg 64 :=
.seq loopBody779_55 loopBody779_61

def loopBody779_63 : HolLoopProg 64 :=
.mark loopBody779_62

def loopBody779_64 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_63

def loopBody779_65 : HolLoopProg 64 :=
.mark loopBody779_64

def loopBody779_66 : HolLoopProg 64 :=
.seq loopBody779_53 loopBody779_65

def loopBody779_67 : HolLoopProg 64 :=
.mark loopBody779_66

def loopBody779_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody779_69 : HolLoopProg 64 :=
.mark loopBody779_68

def loopBody779_70 : HolLoopProg 64 :=
.seq loopBody779_67 loopBody779_69

def loopBody779_71 : HolLoopProg 64 :=
.mark loopBody779_70

def loopBody779_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody779_73 : HolLoopProg 64 :=
.mark loopBody779_72

def loopBody779_74 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody779_71 loopBody779_73 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody779_75 : HolLoopProg 64 :=
.mark loopBody779_74

def loopBody779_76 : HolLoopProg 64 :=
.seq loopBody779_75 loopBody779_1

def loopBody779_77 : HolLoopProg 64 :=
.mark loopBody779_76

def loopBody779_78 : HolLoopProg 64 :=
.seq loopBody779_31 loopBody779_77

def loopBody779_79 : HolLoopProg 64 :=
.mark loopBody779_78

def loopBody779_80 : HolLoopProg 64 :=
.seq loopBody779_29 loopBody779_79

def loopBody779_81 : HolLoopProg 64 :=
.mark loopBody779_80

def loopBody779_82 : HolLoopProg 64 :=
.seq loopBody779_23 loopBody779_81

def loopBody779_83 : HolLoopProg 64 :=
.mark loopBody779_82

def loopBody779_84 : HolLoopProg 64 :=
.seq loopBody779_21 loopBody779_83

def loopBody779_85 : HolLoopProg 64 :=
.mark loopBody779_84

def loopBody779_86 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody779_85 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody779_87 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody779_88 : HolLoopProg 64 :=
.mark loopBody779_87

def loopBody779_89 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64))

def loopBody779_90 : HolLoopProg 64 :=
.mark loopBody779_89

def loopBody779_91 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody779_92 : HolLoopProg 64 :=
.mark loopBody779_91

def loopBody779_93 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 153) ([7, 8, 9]) (some (7, loopBody779_39, loopBody779_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody779_94 : HolLoopProg 64 :=
.mark loopBody779_93

def loopBody779_95 : HolLoopProg 64 :=
.seq loopBody779_94 loopBody779_1

def loopBody779_96 : HolLoopProg 64 :=
.mark loopBody779_95

def loopBody779_97 : HolLoopProg 64 :=
.seq loopBody779_92 loopBody779_96

def loopBody779_98 : HolLoopProg 64 :=
.mark loopBody779_97

def loopBody779_99 : HolLoopProg 64 :=
.seq loopBody779_90 loopBody779_98

def loopBody779_100 : HolLoopProg 64 :=
.mark loopBody779_99

def loopBody779_101 : HolLoopProg 64 :=
.seq loopBody779_88 loopBody779_100

def loopBody779_102 : HolLoopProg 64 :=
.mark loopBody779_101

def loopBody779_103 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_102

def loopBody779_104 : HolLoopProg 64 :=
.mark loopBody779_103

def loopBody779_105 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_104

def loopBody779_106 : HolLoopProg 64 :=
.mark loopBody779_105

def loopBody779_107 : HolLoopProg 64 :=
.seq loopBody779_86 loopBody779_106

def loopBody779_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody779_109 : HolLoopProg 64 :=
.mark loopBody779_108

def loopBody779_110 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody779_39, loopBody779_1, (Flapjack.Spt.ln)))

def loopBody779_111 : HolLoopProg 64 :=
.mark loopBody779_110

def loopBody779_112 : HolLoopProg 64 :=
.seq loopBody779_111 loopBody779_1

def loopBody779_113 : HolLoopProg 64 :=
.mark loopBody779_112

def loopBody779_114 : HolLoopProg 64 :=
.seq loopBody779_109 loopBody779_113

def loopBody779_115 : HolLoopProg 64 :=
.mark loopBody779_114

def loopBody779_116 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_115

def loopBody779_117 : HolLoopProg 64 :=
.mark loopBody779_116

def loopBody779_118 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_117

def loopBody779_119 : HolLoopProg 64 :=
.mark loopBody779_118

def loopBody779_120 : HolLoopProg 64 :=
.seq loopBody779_107 loopBody779_119

def loopBody779_121 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody779_122 : HolLoopProg 64 :=
.mark loopBody779_121

def loopBody779_123 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody779_124 : HolLoopProg 64 :=
.mark loopBody779_123

def loopBody779_125 : HolLoopProg 64 :=
.seq loopBody779_124 loopBody779_1

def loopBody779_126 : HolLoopProg 64 :=
.mark loopBody779_125

def loopBody779_127 : HolLoopProg 64 :=
.seq loopBody779_122 loopBody779_126

def loopBody779_128 : HolLoopProg 64 :=
.mark loopBody779_127

def loopBody779_129 : HolLoopProg 64 :=
.seq loopBody779_120 loopBody779_128

def loopBody779_130 : HolLoopProg 64 :=
.seq loopBody779_19 loopBody779_129

def loopBody779_131 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_130

def loopBody779_132 : HolLoopProg 64 :=
.seq loopBody779_17 loopBody779_131

def loopBody779_133 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_132

def loopBody779_134 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_133

def loopBody779_135 : HolLoopProg 64 :=
.seq loopBody779_7 loopBody779_134

def loopBody779_136 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_135

def loopBody779_137 : HolLoopProg 64 :=
.seq loopBody779_1 loopBody779_136

def output779 : Nat × List Nat × HolLoopProg 64 :=
  (843, [0, 1, 2], loopBody779_137)
end InitECandidate.Proofs.FrontendStages.Loop
