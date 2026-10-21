import InitECandidate.Proofs.FrontendStages.Loop.Translate307
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody323_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody323_1 : HolLoopProg 64 :=
.mark loopBody323_0

def loopBody323_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 16#64]))

def loopBody323_3 : HolLoopProg 64 :=
.mark loopBody323_2

def loopBody323_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody323_5 : HolLoopProg 64 :=
.mark loopBody323_4

def loopBody323_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody323_7 : HolLoopProg 64 :=
.mark loopBody323_6

def loopBody323_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody323_5 loopBody323_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody323_9 : HolLoopProg 64 :=
.mark loopBody323_8

def loopBody323_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody323_11 : HolLoopProg 64 :=
.mark loopBody323_10

def loopBody323_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody323_13 : HolLoopProg 64 :=
.mark loopBody323_12

def loopBody323_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 16#64])

def loopBody323_15 : HolLoopProg 64 :=
.mark loopBody323_14

def loopBody323_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 16#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody323_17 : HolLoopProg 64 :=
.mark loopBody323_16

def loopBody323_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody323_19 : HolLoopProg 64 :=
.mark loopBody323_18

def loopBody323_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody323_21 : HolLoopProg 64 :=
.mark loopBody323_20

def loopBody323_22 : HolLoopProg 64 :=
.seq loopBody323_21 loopBody323_13

def loopBody323_23 : HolLoopProg 64 :=
.mark loopBody323_22

def loopBody323_24 : HolLoopProg 64 :=
.seq loopBody323_19 loopBody323_23

def loopBody323_25 : HolLoopProg 64 :=
.mark loopBody323_24

def loopBody323_26 : HolLoopProg 64 :=
.seq loopBody323_25 loopBody323_13

def loopBody323_27 : HolLoopProg 64 :=
.mark loopBody323_26

def loopBody323_28 : HolLoopProg 64 :=
.seq loopBody323_17 loopBody323_27

def loopBody323_29 : HolLoopProg 64 :=
.mark loopBody323_28

def loopBody323_30 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_29

def loopBody323_31 : HolLoopProg 64 :=
.mark loopBody323_30

def loopBody323_32 : HolLoopProg 64 :=
.seq loopBody323_15 loopBody323_31

def loopBody323_33 : HolLoopProg 64 :=
.mark loopBody323_32

def loopBody323_34 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_33

def loopBody323_35 : HolLoopProg 64 :=
.mark loopBody323_34

def loopBody323_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 200#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 16#64]))
        (Flapjack.HolLoopExp.const 5#64)])

def loopBody323_37 : HolLoopProg 64 :=
.mark loopBody323_36

def loopBody323_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 1))

def loopBody323_39 : HolLoopProg 64 :=
.mark loopBody323_38

def loopBody323_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody323_41 : HolLoopProg 64 :=
.mark loopBody323_40

def loopBody323_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 16#64]))

def loopBody323_43 : HolLoopProg 64 :=
.mark loopBody323_42

def loopBody323_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody323_45 : HolLoopProg 64 :=
.mark loopBody323_44

def loopBody323_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody323_47 : HolLoopProg 64 :=
.mark loopBody323_46

def loopBody323_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody323_49 : HolLoopProg 64 :=
.mark loopBody323_48

def loopBody323_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody323_47 loopBody323_49 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody323_51 : HolLoopProg 64 :=
.mark loopBody323_50

def loopBody323_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody323_53 : HolLoopProg 64 :=
.mark loopBody323_52

def loopBody323_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody323_55 : HolLoopProg 64 :=
.mark loopBody323_54

def loopBody323_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody323_57 : HolLoopProg 64 :=
.mark loopBody323_56

def loopBody323_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 24#64]))

def loopBody323_59 : HolLoopProg 64 :=
.mark loopBody323_58

def loopBody323_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody323_61 : HolLoopProg 64 :=
.mark loopBody323_60

def loopBody323_62 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ls PUnit.unit)) (some 192) ([5, 6, 7]) (some (5, loopBody323_61, loopBody323_13, (Flapjack.Spt.ls PUnit.unit)))

def loopBody323_63 : HolLoopProg 64 :=
.mark loopBody323_62

def loopBody323_64 : HolLoopProg 64 :=
.seq loopBody323_63 loopBody323_13

def loopBody323_65 : HolLoopProg 64 :=
.mark loopBody323_64

def loopBody323_66 : HolLoopProg 64 :=
.seq loopBody323_59 loopBody323_65

def loopBody323_67 : HolLoopProg 64 :=
.mark loopBody323_66

def loopBody323_68 : HolLoopProg 64 :=
.seq loopBody323_57 loopBody323_67

def loopBody323_69 : HolLoopProg 64 :=
.mark loopBody323_68

def loopBody323_70 : HolLoopProg 64 :=
.seq loopBody323_55 loopBody323_69

def loopBody323_71 : HolLoopProg 64 :=
.mark loopBody323_70

def loopBody323_72 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_71

def loopBody323_73 : HolLoopProg 64 :=
.mark loopBody323_72

def loopBody323_74 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_73

def loopBody323_75 : HolLoopProg 64 :=
.mark loopBody323_74

def loopBody323_76 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ls PUnit.unit)) (some 193) ([5, 6]) (some (5, loopBody323_61, loopBody323_13, (Flapjack.Spt.ls PUnit.unit)))

def loopBody323_77 : HolLoopProg 64 :=
.mark loopBody323_76

def loopBody323_78 : HolLoopProg 64 :=
.seq loopBody323_77 loopBody323_13

def loopBody323_79 : HolLoopProg 64 :=
.mark loopBody323_78

def loopBody323_80 : HolLoopProg 64 :=
.seq loopBody323_57 loopBody323_79

def loopBody323_81 : HolLoopProg 64 :=
.mark loopBody323_80

def loopBody323_82 : HolLoopProg 64 :=
.seq loopBody323_55 loopBody323_81

def loopBody323_83 : HolLoopProg 64 :=
.mark loopBody323_82

def loopBody323_84 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_83

def loopBody323_85 : HolLoopProg 64 :=
.mark loopBody323_84

def loopBody323_86 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_85

def loopBody323_87 : HolLoopProg 64 :=
.mark loopBody323_86

def loopBody323_88 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody323_75 loopBody323_87 (Flapjack.Spt.ls PUnit.unit)

def loopBody323_89 : HolLoopProg 64 :=
.mark loopBody323_88

def loopBody323_90 : HolLoopProg 64 :=
.seq loopBody323_89 loopBody323_13

def loopBody323_91 : HolLoopProg 64 :=
.mark loopBody323_90

def loopBody323_92 : HolLoopProg 64 :=
.seq loopBody323_53 loopBody323_91

def loopBody323_93 : HolLoopProg 64 :=
.mark loopBody323_92

def loopBody323_94 : HolLoopProg 64 :=
.seq loopBody323_51 loopBody323_93

def loopBody323_95 : HolLoopProg 64 :=
.mark loopBody323_94

def loopBody323_96 : HolLoopProg 64 :=
.seq loopBody323_45 loopBody323_95

def loopBody323_97 : HolLoopProg 64 :=
.mark loopBody323_96

def loopBody323_98 : HolLoopProg 64 :=
.seq loopBody323_43 loopBody323_97

def loopBody323_99 : HolLoopProg 64 :=
.mark loopBody323_98

def loopBody323_100 : HolLoopProg 64 :=
.seq loopBody323_41 loopBody323_99

def loopBody323_101 : HolLoopProg 64 :=
.mark loopBody323_100

def loopBody323_102 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_101

def loopBody323_103 : HolLoopProg 64 :=
.mark loopBody323_102

def loopBody323_104 : HolLoopProg 64 :=
.seq loopBody323_39 loopBody323_103

def loopBody323_105 : HolLoopProg 64 :=
.mark loopBody323_104

def loopBody323_106 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_105

def loopBody323_107 : HolLoopProg 64 :=
.mark loopBody323_106

def loopBody323_108 : HolLoopProg 64 :=
.seq loopBody323_37 loopBody323_107

def loopBody323_109 : HolLoopProg 64 :=
.mark loopBody323_108

def loopBody323_110 : HolLoopProg 64 :=
.seq loopBody323_13 loopBody323_109

def loopBody323_111 : HolLoopProg 64 :=
.mark loopBody323_110

def loopBody323_112 : HolLoopProg 64 :=
.seq loopBody323_35 loopBody323_111

def loopBody323_113 : HolLoopProg 64 :=
.mark loopBody323_112

def loopBody323_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody323_115 : HolLoopProg 64 :=
.mark loopBody323_114

def loopBody323_116 : HolLoopProg 64 :=
.seq loopBody323_113 loopBody323_115

def loopBody323_117 : HolLoopProg 64 :=
.mark loopBody323_116

def loopBody323_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody323_119 : HolLoopProg 64 :=
.mark loopBody323_118

def loopBody323_120 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody323_117 loopBody323_119 (Flapjack.Spt.ls PUnit.unit)

def loopBody323_121 : HolLoopProg 64 :=
.mark loopBody323_120

def loopBody323_122 : HolLoopProg 64 :=
.seq loopBody323_121 loopBody323_13

def loopBody323_123 : HolLoopProg 64 :=
.mark loopBody323_122

def loopBody323_124 : HolLoopProg 64 :=
.seq loopBody323_11 loopBody323_123

def loopBody323_125 : HolLoopProg 64 :=
.mark loopBody323_124

def loopBody323_126 : HolLoopProg 64 :=
.seq loopBody323_9 loopBody323_125

def loopBody323_127 : HolLoopProg 64 :=
.mark loopBody323_126

def loopBody323_128 : HolLoopProg 64 :=
.seq loopBody323_3 loopBody323_127

def loopBody323_129 : HolLoopProg 64 :=
.mark loopBody323_128

def loopBody323_130 : HolLoopProg 64 :=
.seq loopBody323_1 loopBody323_129

def loopBody323_131 : HolLoopProg 64 :=
.mark loopBody323_130

def loopBody323_132 : HolLoopProg 64 :=
.loop (Flapjack.Spt.ls PUnit.unit) loopBody323_131 (Flapjack.Spt.ln)

def loopBody323_133 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody323_134 : HolLoopProg 64 :=
.mark loopBody323_133

def loopBody323_135 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody323_136 : HolLoopProg 64 :=
.mark loopBody323_135

def loopBody323_137 : HolLoopProg 64 :=
.seq loopBody323_136 loopBody323_13

def loopBody323_138 : HolLoopProg 64 :=
.mark loopBody323_137

def loopBody323_139 : HolLoopProg 64 :=
.seq loopBody323_134 loopBody323_138

def loopBody323_140 : HolLoopProg 64 :=
.mark loopBody323_139

def loopBody323_141 : HolLoopProg 64 :=
.seq loopBody323_132 loopBody323_140

def output323 : Nat × List Nat × HolLoopProg 64 :=
  (387, [0], loopBody323_141)
end InitECandidate.Proofs.FrontendStages.Loop
