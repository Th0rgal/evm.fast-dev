import InitECandidate.Proofs.FrontendStages.Loop.Translate700
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody716_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody716_1 : HolLoopProg 64 :=
.mark loopBody716_0

def loopBody716_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody716_3 : HolLoopProg 64 :=
.mark loopBody716_2

def loopBody716_4 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (5, loopBody716_3, loopBody716_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody716_5 : HolLoopProg 64 :=
.mark loopBody716_4

def loopBody716_6 : HolLoopProg 64 :=
.seq loopBody716_5 loopBody716_1

def loopBody716_7 : HolLoopProg 64 :=
.mark loopBody716_6

def loopBody716_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 288#64)

def loopBody716_9 : HolLoopProg 64 :=
.mark loopBody716_8

def loopBody716_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody716_11 : HolLoopProg 64 :=
.mark loopBody716_10

def loopBody716_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([6]) (some (6, loopBody716_11, loopBody716_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody716_13 : HolLoopProg 64 :=
.mark loopBody716_12

def loopBody716_14 : HolLoopProg 64 :=
.seq loopBody716_13 loopBody716_1

def loopBody716_15 : HolLoopProg 64 :=
.mark loopBody716_14

def loopBody716_16 : HolLoopProg 64 :=
.seq loopBody716_9 loopBody716_15

def loopBody716_17 : HolLoopProg 64 :=
.mark loopBody716_16

def loopBody716_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody716_19 : HolLoopProg 64 :=
.mark loopBody716_18

def loopBody716_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody716_21 : HolLoopProg 64 :=
.mark loopBody716_20

def loopBody716_22 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 774) ([7]) (some (7, loopBody716_21, loopBody716_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody716_23 : HolLoopProg 64 :=
.mark loopBody716_22

def loopBody716_24 : HolLoopProg 64 :=
.seq loopBody716_23 loopBody716_1

def loopBody716_25 : HolLoopProg 64 :=
.mark loopBody716_24

def loopBody716_26 : HolLoopProg 64 :=
.seq loopBody716_19 loopBody716_25

def loopBody716_27 : HolLoopProg 64 :=
.mark loopBody716_26

def loopBody716_28 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_27

def loopBody716_29 : HolLoopProg 64 :=
.mark loopBody716_28

def loopBody716_30 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_29

def loopBody716_31 : HolLoopProg 64 :=
.mark loopBody716_30

def loopBody716_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 6#64))

def loopBody716_33 : HolLoopProg 64 :=
.mark loopBody716_32

def loopBody716_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody716_35 : HolLoopProg 64 :=
.mark loopBody716_34

def loopBody716_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody716_37 : HolLoopProg 64 :=
.mark loopBody716_36

def loopBody716_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody716_39 : HolLoopProg 64 :=
.mark loopBody716_38

def loopBody716_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody716_41 : HolLoopProg 64 :=
.mark loopBody716_40

def loopBody716_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 9 (Flapjack.RegImm.reg 10) loopBody716_41 loopBody716_37 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_43 : HolLoopProg 64 :=
.mark loopBody716_42

def loopBody716_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody716_45 : HolLoopProg 64 :=
.mark loopBody716_44

def loopBody716_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody716_47 : HolLoopProg 64 :=
.mark loopBody716_46

def loopBody716_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 8)

def loopBody716_49 : HolLoopProg 64 :=
.mark loopBody716_48

def loopBody716_50 : HolLoopProg 64 :=
.seq loopBody716_49 loopBody716_1

def loopBody716_51 : HolLoopProg 64 :=
.mark loopBody716_50

def loopBody716_52 : HolLoopProg 64 :=
.seq loopBody716_51 loopBody716_1

def loopBody716_53 : HolLoopProg 64 :=
.mark loopBody716_52

def loopBody716_54 : HolLoopProg 64 :=
.seq loopBody716_47 loopBody716_53

def loopBody716_55 : HolLoopProg 64 :=
.mark loopBody716_54

def loopBody716_56 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_55

def loopBody716_57 : HolLoopProg 64 :=
.mark loopBody716_56

def loopBody716_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody716_59 : HolLoopProg 64 :=
.mark loopBody716_58

def loopBody716_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody716_61 : HolLoopProg 64 :=
.mark loopBody716_60

def loopBody716_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody716_41 loopBody716_37 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_63 : HolLoopProg 64 :=
.mark loopBody716_62

def loopBody716_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody716_65 : HolLoopProg 64 :=
.mark loopBody716_64

def loopBody716_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody716_67 : HolLoopProg 64 :=
.mark loopBody716_66

def loopBody716_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody716_69 : HolLoopProg 64 :=
.mark loopBody716_68

def loopBody716_70 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 778) ([9, 10]) (some (9, loopBody716_69, loopBody716_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody716_71 : HolLoopProg 64 :=
.mark loopBody716_70

def loopBody716_72 : HolLoopProg 64 :=
.seq loopBody716_71 loopBody716_1

def loopBody716_73 : HolLoopProg 64 :=
.mark loopBody716_72

def loopBody716_74 : HolLoopProg 64 :=
.seq loopBody716_67 loopBody716_73

def loopBody716_75 : HolLoopProg 64 :=
.mark loopBody716_74

def loopBody716_76 : HolLoopProg 64 :=
.seq loopBody716_65 loopBody716_75

def loopBody716_77 : HolLoopProg 64 :=
.mark loopBody716_76

def loopBody716_78 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_77

def loopBody716_79 : HolLoopProg 64 :=
.mark loopBody716_78

def loopBody716_80 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_79

def loopBody716_81 : HolLoopProg 64 :=
.mark loopBody716_80

def loopBody716_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody716_81 loopBody716_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_83 : HolLoopProg 64 :=
.mark loopBody716_82

def loopBody716_84 : HolLoopProg 64 :=
.seq loopBody716_83 loopBody716_1

def loopBody716_85 : HolLoopProg 64 :=
.mark loopBody716_84

def loopBody716_86 : HolLoopProg 64 :=
.seq loopBody716_45 loopBody716_85

def loopBody716_87 : HolLoopProg 64 :=
.mark loopBody716_86

def loopBody716_88 : HolLoopProg 64 :=
.seq loopBody716_63 loopBody716_87

def loopBody716_89 : HolLoopProg 64 :=
.mark loopBody716_88

def loopBody716_90 : HolLoopProg 64 :=
.seq loopBody716_61 loopBody716_89

def loopBody716_91 : HolLoopProg 64 :=
.mark loopBody716_90

def loopBody716_92 : HolLoopProg 64 :=
.seq loopBody716_59 loopBody716_91

def loopBody716_93 : HolLoopProg 64 :=
.mark loopBody716_92

def loopBody716_94 : HolLoopProg 64 :=
.seq loopBody716_57 loopBody716_93

def loopBody716_95 : HolLoopProg 64 :=
.mark loopBody716_94

def loopBody716_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 2,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 6)
                  (Flapjack.HolLoopExp.const 6#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 63#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody716_97 : HolLoopProg 64 :=
.mark loopBody716_96

def loopBody716_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody716_99 : HolLoopProg 64 :=
.mark loopBody716_98

def loopBody716_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody716_101 : HolLoopProg 64 :=
.mark loopBody716_100

def loopBody716_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody716_103 : HolLoopProg 64 :=
.mark loopBody716_102

def loopBody716_104 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.RegImm.reg 11) loopBody716_61 loopBody716_103 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_105 : HolLoopProg 64 :=
.mark loopBody716_104

def loopBody716_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody716_107 : HolLoopProg 64 :=
.mark loopBody716_106

def loopBody716_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody716_109 : HolLoopProg 64 :=
.mark loopBody716_108

def loopBody716_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 1)

def loopBody716_111 : HolLoopProg 64 :=
.mark loopBody716_110

def loopBody716_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody716_113 : HolLoopProg 64 :=
.mark loopBody716_112

def loopBody716_114 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 779) ([10, 11, 12]) (some (10, loopBody716_113, loopBody716_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody716_115 : HolLoopProg 64 :=
.mark loopBody716_114

def loopBody716_116 : HolLoopProg 64 :=
.seq loopBody716_115 loopBody716_1

def loopBody716_117 : HolLoopProg 64 :=
.mark loopBody716_116

def loopBody716_118 : HolLoopProg 64 :=
.seq loopBody716_111 loopBody716_117

def loopBody716_119 : HolLoopProg 64 :=
.mark loopBody716_118

def loopBody716_120 : HolLoopProg 64 :=
.seq loopBody716_109 loopBody716_119

def loopBody716_121 : HolLoopProg 64 :=
.mark loopBody716_120

def loopBody716_122 : HolLoopProg 64 :=
.seq loopBody716_67 loopBody716_121

def loopBody716_123 : HolLoopProg 64 :=
.mark loopBody716_122

def loopBody716_124 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_123

def loopBody716_125 : HolLoopProg 64 :=
.mark loopBody716_124

def loopBody716_126 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_125

def loopBody716_127 : HolLoopProg 64 :=
.mark loopBody716_126

def loopBody716_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody716_129 : HolLoopProg 64 :=
.mark loopBody716_128

def loopBody716_130 : HolLoopProg 64 :=
.seq loopBody716_129 loopBody716_1

def loopBody716_131 : HolLoopProg 64 :=
.mark loopBody716_130

def loopBody716_132 : HolLoopProg 64 :=
.seq loopBody716_131 loopBody716_1

def loopBody716_133 : HolLoopProg 64 :=
.mark loopBody716_132

def loopBody716_134 : HolLoopProg 64 :=
.seq loopBody716_127 loopBody716_133

def loopBody716_135 : HolLoopProg 64 :=
.mark loopBody716_134

def loopBody716_136 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody716_135 loopBody716_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_137 : HolLoopProg 64 :=
.mark loopBody716_136

def loopBody716_138 : HolLoopProg 64 :=
.seq loopBody716_137 loopBody716_1

def loopBody716_139 : HolLoopProg 64 :=
.mark loopBody716_138

def loopBody716_140 : HolLoopProg 64 :=
.seq loopBody716_107 loopBody716_139

def loopBody716_141 : HolLoopProg 64 :=
.mark loopBody716_140

def loopBody716_142 : HolLoopProg 64 :=
.seq loopBody716_105 loopBody716_141

def loopBody716_143 : HolLoopProg 64 :=
.mark loopBody716_142

def loopBody716_144 : HolLoopProg 64 :=
.seq loopBody716_101 loopBody716_143

def loopBody716_145 : HolLoopProg 64 :=
.mark loopBody716_144

def loopBody716_146 : HolLoopProg 64 :=
.seq loopBody716_99 loopBody716_145

def loopBody716_147 : HolLoopProg 64 :=
.mark loopBody716_146

def loopBody716_148 : HolLoopProg 64 :=
.seq loopBody716_97 loopBody716_147

def loopBody716_149 : HolLoopProg 64 :=
.mark loopBody716_148

def loopBody716_150 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_149

def loopBody716_151 : HolLoopProg 64 :=
.mark loopBody716_150

def loopBody716_152 : HolLoopProg 64 :=
.seq loopBody716_95 loopBody716_151

def loopBody716_153 : HolLoopProg 64 :=
.mark loopBody716_152

def loopBody716_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody716_155 : HolLoopProg 64 :=
.mark loopBody716_154

def loopBody716_156 : HolLoopProg 64 :=
.seq loopBody716_153 loopBody716_155

def loopBody716_157 : HolLoopProg 64 :=
.mark loopBody716_156

def loopBody716_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody716_159 : HolLoopProg 64 :=
.mark loopBody716_158

def loopBody716_160 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody716_157 loopBody716_159 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody716_161 : HolLoopProg 64 :=
.mark loopBody716_160

def loopBody716_162 : HolLoopProg 64 :=
.seq loopBody716_161 loopBody716_1

def loopBody716_163 : HolLoopProg 64 :=
.mark loopBody716_162

def loopBody716_164 : HolLoopProg 64 :=
.seq loopBody716_45 loopBody716_163

def loopBody716_165 : HolLoopProg 64 :=
.mark loopBody716_164

def loopBody716_166 : HolLoopProg 64 :=
.seq loopBody716_43 loopBody716_165

def loopBody716_167 : HolLoopProg 64 :=
.mark loopBody716_166

def loopBody716_168 : HolLoopProg 64 :=
.seq loopBody716_39 loopBody716_167

def loopBody716_169 : HolLoopProg 64 :=
.mark loopBody716_168

def loopBody716_170 : HolLoopProg 64 :=
.seq loopBody716_37 loopBody716_169

def loopBody716_171 : HolLoopProg 64 :=
.mark loopBody716_170

def loopBody716_172 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody716_171 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody716_173 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody716_174 : HolLoopProg 64 :=
.mark loopBody716_173

def loopBody716_175 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 776) ([9, 10]) (some (9, loopBody716_69, loopBody716_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody716_176 : HolLoopProg 64 :=
.mark loopBody716_175

def loopBody716_177 : HolLoopProg 64 :=
.seq loopBody716_176 loopBody716_1

def loopBody716_178 : HolLoopProg 64 :=
.mark loopBody716_177

def loopBody716_179 : HolLoopProg 64 :=
.seq loopBody716_67 loopBody716_178

def loopBody716_180 : HolLoopProg 64 :=
.mark loopBody716_179

def loopBody716_181 : HolLoopProg 64 :=
.seq loopBody716_174 loopBody716_180

def loopBody716_182 : HolLoopProg 64 :=
.mark loopBody716_181

def loopBody716_183 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_182

def loopBody716_184 : HolLoopProg 64 :=
.mark loopBody716_183

def loopBody716_185 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_184

def loopBody716_186 : HolLoopProg 64 :=
.mark loopBody716_185

def loopBody716_187 : HolLoopProg 64 :=
.seq loopBody716_172 loopBody716_186

def loopBody716_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody716_189 : HolLoopProg 64 :=
.mark loopBody716_188

def loopBody716_190 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 70) ([9]) (some (9, loopBody716_69, loopBody716_1, (Flapjack.Spt.ln)))

def loopBody716_191 : HolLoopProg 64 :=
.mark loopBody716_190

def loopBody716_192 : HolLoopProg 64 :=
.seq loopBody716_191 loopBody716_1

def loopBody716_193 : HolLoopProg 64 :=
.mark loopBody716_192

def loopBody716_194 : HolLoopProg 64 :=
.seq loopBody716_189 loopBody716_193

def loopBody716_195 : HolLoopProg 64 :=
.mark loopBody716_194

def loopBody716_196 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_195

def loopBody716_197 : HolLoopProg 64 :=
.mark loopBody716_196

def loopBody716_198 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_197

def loopBody716_199 : HolLoopProg 64 :=
.mark loopBody716_198

def loopBody716_200 : HolLoopProg 64 :=
.seq loopBody716_187 loopBody716_199

def loopBody716_201 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody716_202 : HolLoopProg 64 :=
.mark loopBody716_201

def loopBody716_203 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody716_204 : HolLoopProg 64 :=
.mark loopBody716_203

def loopBody716_205 : HolLoopProg 64 :=
.seq loopBody716_204 loopBody716_1

def loopBody716_206 : HolLoopProg 64 :=
.mark loopBody716_205

def loopBody716_207 : HolLoopProg 64 :=
.seq loopBody716_202 loopBody716_206

def loopBody716_208 : HolLoopProg 64 :=
.mark loopBody716_207

def loopBody716_209 : HolLoopProg 64 :=
.seq loopBody716_200 loopBody716_208

def loopBody716_210 : HolLoopProg 64 :=
.seq loopBody716_35 loopBody716_209

def loopBody716_211 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_210

def loopBody716_212 : HolLoopProg 64 :=
.seq loopBody716_33 loopBody716_211

def loopBody716_213 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_212

def loopBody716_214 : HolLoopProg 64 :=
.seq loopBody716_31 loopBody716_213

def loopBody716_215 : HolLoopProg 64 :=
.seq loopBody716_17 loopBody716_214

def loopBody716_216 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_215

def loopBody716_217 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_216

def loopBody716_218 : HolLoopProg 64 :=
.seq loopBody716_7 loopBody716_217

def loopBody716_219 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_218

def loopBody716_220 : HolLoopProg 64 :=
.seq loopBody716_1 loopBody716_219

def output716 : Nat × List Nat × HolLoopProg 64 :=
  (780, [0, 1, 2, 3], loopBody716_220)
end InitECandidate.Proofs.FrontendStages.Loop
