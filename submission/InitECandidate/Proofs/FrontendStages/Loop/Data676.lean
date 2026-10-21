import InitECandidate.Proofs.FrontendStages.Loop.Translate660
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody676_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody676_1 : HolLoopProg 64 :=
.mark loopBody676_0

def loopBody676_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody676_3 : HolLoopProg 64 :=
.mark loopBody676_2

def loopBody676_4 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (5, loopBody676_3, loopBody676_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_5 : HolLoopProg 64 :=
.mark loopBody676_4

def loopBody676_6 : HolLoopProg 64 :=
.seq loopBody676_5 loopBody676_1

def loopBody676_7 : HolLoopProg 64 :=
.mark loopBody676_6

def loopBody676_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 96#64)

def loopBody676_9 : HolLoopProg 64 :=
.mark loopBody676_8

def loopBody676_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody676_11 : HolLoopProg 64 :=
.mark loopBody676_10

def loopBody676_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([6]) (some (6, loopBody676_11, loopBody676_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_13 : HolLoopProg 64 :=
.mark loopBody676_12

def loopBody676_14 : HolLoopProg 64 :=
.seq loopBody676_13 loopBody676_1

def loopBody676_15 : HolLoopProg 64 :=
.mark loopBody676_14

def loopBody676_16 : HolLoopProg 64 :=
.seq loopBody676_9 loopBody676_15

def loopBody676_17 : HolLoopProg 64 :=
.mark loopBody676_16

def loopBody676_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 96#64)

def loopBody676_19 : HolLoopProg 64 :=
.mark loopBody676_18

def loopBody676_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody676_21 : HolLoopProg 64 :=
.mark loopBody676_20

def loopBody676_22 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([7]) (some (7, loopBody676_21, loopBody676_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_23 : HolLoopProg 64 :=
.mark loopBody676_22

def loopBody676_24 : HolLoopProg 64 :=
.seq loopBody676_23 loopBody676_1

def loopBody676_25 : HolLoopProg 64 :=
.mark loopBody676_24

def loopBody676_26 : HolLoopProg 64 :=
.seq loopBody676_19 loopBody676_25

def loopBody676_27 : HolLoopProg 64 :=
.mark loopBody676_26

def loopBody676_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody676_29 : HolLoopProg 64 :=
.mark loopBody676_28

def loopBody676_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody676_31 : HolLoopProg 64 :=
.mark loopBody676_30

def loopBody676_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody676_33 : HolLoopProg 64 :=
.mark loopBody676_32

def loopBody676_34 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 725) ([8, 9]) (some (8, loopBody676_33, loopBody676_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_35 : HolLoopProg 64 :=
.mark loopBody676_34

def loopBody676_36 : HolLoopProg 64 :=
.seq loopBody676_35 loopBody676_1

def loopBody676_37 : HolLoopProg 64 :=
.mark loopBody676_36

def loopBody676_38 : HolLoopProg 64 :=
.seq loopBody676_31 loopBody676_37

def loopBody676_39 : HolLoopProg 64 :=
.mark loopBody676_38

def loopBody676_40 : HolLoopProg 64 :=
.seq loopBody676_29 loopBody676_39

def loopBody676_41 : HolLoopProg 64 :=
.mark loopBody676_40

def loopBody676_42 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_41

def loopBody676_43 : HolLoopProg 64 :=
.mark loopBody676_42

def loopBody676_44 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_43

def loopBody676_45 : HolLoopProg 64 :=
.mark loopBody676_44

def loopBody676_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody676_47 : HolLoopProg 64 :=
.mark loopBody676_46

def loopBody676_48 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 727) ([8]) (some (8, loopBody676_33, loopBody676_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_49 : HolLoopProg 64 :=
.mark loopBody676_48

def loopBody676_50 : HolLoopProg 64 :=
.seq loopBody676_49 loopBody676_1

def loopBody676_51 : HolLoopProg 64 :=
.mark loopBody676_50

def loopBody676_52 : HolLoopProg 64 :=
.seq loopBody676_47 loopBody676_51

def loopBody676_53 : HolLoopProg 64 :=
.mark loopBody676_52

def loopBody676_54 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_53

def loopBody676_55 : HolLoopProg 64 :=
.mark loopBody676_54

def loopBody676_56 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_55

def loopBody676_57 : HolLoopProg 64 :=
.mark loopBody676_56

def loopBody676_58 : HolLoopProg 64 :=
.seq loopBody676_45 loopBody676_57

def loopBody676_59 : HolLoopProg 64 :=
.mark loopBody676_58

def loopBody676_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody676_61 : HolLoopProg 64 :=
.mark loopBody676_60

def loopBody676_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 6#64))

def loopBody676_63 : HolLoopProg 64 :=
.mark loopBody676_62

def loopBody676_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody676_65 : HolLoopProg 64 :=
.mark loopBody676_64

def loopBody676_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody676_67 : HolLoopProg 64 :=
.mark loopBody676_66

def loopBody676_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody676_69 : HolLoopProg 64 :=
.mark loopBody676_68

def loopBody676_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.RegImm.reg 11) loopBody676_69 loopBody676_65 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_71 : HolLoopProg 64 :=
.mark loopBody676_70

def loopBody676_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody676_73 : HolLoopProg 64 :=
.mark loopBody676_72

def loopBody676_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 8, Flapjack.HolLoopExp.const 1#64])

def loopBody676_75 : HolLoopProg 64 :=
.mark loopBody676_74

def loopBody676_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 9)

def loopBody676_77 : HolLoopProg 64 :=
.mark loopBody676_76

def loopBody676_78 : HolLoopProg 64 :=
.seq loopBody676_77 loopBody676_1

def loopBody676_79 : HolLoopProg 64 :=
.mark loopBody676_78

def loopBody676_80 : HolLoopProg 64 :=
.seq loopBody676_79 loopBody676_1

def loopBody676_81 : HolLoopProg 64 :=
.mark loopBody676_80

def loopBody676_82 : HolLoopProg 64 :=
.seq loopBody676_75 loopBody676_81

def loopBody676_83 : HolLoopProg 64 :=
.mark loopBody676_82

def loopBody676_84 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_83

def loopBody676_85 : HolLoopProg 64 :=
.mark loopBody676_84

def loopBody676_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody676_87 : HolLoopProg 64 :=
.mark loopBody676_86

def loopBody676_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody676_89 : HolLoopProg 64 :=
.mark loopBody676_88

def loopBody676_90 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.RegImm.reg 11) loopBody676_69 loopBody676_65 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_91 : HolLoopProg 64 :=
.mark loopBody676_90

def loopBody676_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody676_93 : HolLoopProg 64 :=
.mark loopBody676_92

def loopBody676_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody676_95 : HolLoopProg 64 :=
.mark loopBody676_94

def loopBody676_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody676_97 : HolLoopProg 64 :=
.mark loopBody676_96

def loopBody676_98 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 736) ([10, 11]) (some (10, loopBody676_97, loopBody676_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody676_99 : HolLoopProg 64 :=
.mark loopBody676_98

def loopBody676_100 : HolLoopProg 64 :=
.seq loopBody676_99 loopBody676_1

def loopBody676_101 : HolLoopProg 64 :=
.mark loopBody676_100

def loopBody676_102 : HolLoopProg 64 :=
.seq loopBody676_95 loopBody676_101

def loopBody676_103 : HolLoopProg 64 :=
.mark loopBody676_102

def loopBody676_104 : HolLoopProg 64 :=
.seq loopBody676_93 loopBody676_103

def loopBody676_105 : HolLoopProg 64 :=
.mark loopBody676_104

def loopBody676_106 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_105

def loopBody676_107 : HolLoopProg 64 :=
.mark loopBody676_106

def loopBody676_108 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_107

def loopBody676_109 : HolLoopProg 64 :=
.mark loopBody676_108

def loopBody676_110 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody676_109 loopBody676_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_111 : HolLoopProg 64 :=
.mark loopBody676_110

def loopBody676_112 : HolLoopProg 64 :=
.seq loopBody676_111 loopBody676_1

def loopBody676_113 : HolLoopProg 64 :=
.mark loopBody676_112

def loopBody676_114 : HolLoopProg 64 :=
.seq loopBody676_73 loopBody676_113

def loopBody676_115 : HolLoopProg 64 :=
.mark loopBody676_114

def loopBody676_116 : HolLoopProg 64 :=
.seq loopBody676_91 loopBody676_115

def loopBody676_117 : HolLoopProg 64 :=
.mark loopBody676_116

def loopBody676_118 : HolLoopProg 64 :=
.seq loopBody676_89 loopBody676_117

def loopBody676_119 : HolLoopProg 64 :=
.mark loopBody676_118

def loopBody676_120 : HolLoopProg 64 :=
.seq loopBody676_87 loopBody676_119

def loopBody676_121 : HolLoopProg 64 :=
.mark loopBody676_120

def loopBody676_122 : HolLoopProg 64 :=
.seq loopBody676_85 loopBody676_121

def loopBody676_123 : HolLoopProg 64 :=
.mark loopBody676_122

def loopBody676_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 2,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 8)
                  (Flapjack.HolLoopExp.const 6#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 8, Flapjack.HolLoopExp.const 63#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody676_125 : HolLoopProg 64 :=
.mark loopBody676_124

def loopBody676_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody676_127 : HolLoopProg 64 :=
.mark loopBody676_126

def loopBody676_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody676_129 : HolLoopProg 64 :=
.mark loopBody676_128

def loopBody676_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody676_131 : HolLoopProg 64 :=
.mark loopBody676_130

def loopBody676_132 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody676_89 loopBody676_131 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_133 : HolLoopProg 64 :=
.mark loopBody676_132

def loopBody676_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody676_135 : HolLoopProg 64 :=
.mark loopBody676_134

def loopBody676_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody676_137 : HolLoopProg 64 :=
.mark loopBody676_136

def loopBody676_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 5)

def loopBody676_139 : HolLoopProg 64 :=
.mark loopBody676_138

def loopBody676_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody676_141 : HolLoopProg 64 :=
.mark loopBody676_140

def loopBody676_142 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 735) ([11, 12, 13]) (some (11, loopBody676_141, loopBody676_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody676_143 : HolLoopProg 64 :=
.mark loopBody676_142

def loopBody676_144 : HolLoopProg 64 :=
.seq loopBody676_143 loopBody676_1

def loopBody676_145 : HolLoopProg 64 :=
.mark loopBody676_144

def loopBody676_146 : HolLoopProg 64 :=
.seq loopBody676_139 loopBody676_145

def loopBody676_147 : HolLoopProg 64 :=
.mark loopBody676_146

def loopBody676_148 : HolLoopProg 64 :=
.seq loopBody676_137 loopBody676_147

def loopBody676_149 : HolLoopProg 64 :=
.mark loopBody676_148

def loopBody676_150 : HolLoopProg 64 :=
.seq loopBody676_95 loopBody676_149

def loopBody676_151 : HolLoopProg 64 :=
.mark loopBody676_150

def loopBody676_152 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_151

def loopBody676_153 : HolLoopProg 64 :=
.mark loopBody676_152

def loopBody676_154 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_153

def loopBody676_155 : HolLoopProg 64 :=
.mark loopBody676_154

def loopBody676_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody676_157 : HolLoopProg 64 :=
.mark loopBody676_156

def loopBody676_158 : HolLoopProg 64 :=
.seq loopBody676_157 loopBody676_1

def loopBody676_159 : HolLoopProg 64 :=
.mark loopBody676_158

def loopBody676_160 : HolLoopProg 64 :=
.seq loopBody676_159 loopBody676_1

def loopBody676_161 : HolLoopProg 64 :=
.mark loopBody676_160

def loopBody676_162 : HolLoopProg 64 :=
.seq loopBody676_155 loopBody676_161

def loopBody676_163 : HolLoopProg 64 :=
.mark loopBody676_162

def loopBody676_164 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody676_163 loopBody676_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_165 : HolLoopProg 64 :=
.mark loopBody676_164

def loopBody676_166 : HolLoopProg 64 :=
.seq loopBody676_165 loopBody676_1

def loopBody676_167 : HolLoopProg 64 :=
.mark loopBody676_166

def loopBody676_168 : HolLoopProg 64 :=
.seq loopBody676_135 loopBody676_167

def loopBody676_169 : HolLoopProg 64 :=
.mark loopBody676_168

def loopBody676_170 : HolLoopProg 64 :=
.seq loopBody676_133 loopBody676_169

def loopBody676_171 : HolLoopProg 64 :=
.mark loopBody676_170

def loopBody676_172 : HolLoopProg 64 :=
.seq loopBody676_129 loopBody676_171

def loopBody676_173 : HolLoopProg 64 :=
.mark loopBody676_172

def loopBody676_174 : HolLoopProg 64 :=
.seq loopBody676_127 loopBody676_173

def loopBody676_175 : HolLoopProg 64 :=
.mark loopBody676_174

def loopBody676_176 : HolLoopProg 64 :=
.seq loopBody676_125 loopBody676_175

def loopBody676_177 : HolLoopProg 64 :=
.mark loopBody676_176

def loopBody676_178 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_177

def loopBody676_179 : HolLoopProg 64 :=
.mark loopBody676_178

def loopBody676_180 : HolLoopProg 64 :=
.seq loopBody676_123 loopBody676_179

def loopBody676_181 : HolLoopProg 64 :=
.mark loopBody676_180

def loopBody676_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody676_183 : HolLoopProg 64 :=
.mark loopBody676_182

def loopBody676_184 : HolLoopProg 64 :=
.seq loopBody676_181 loopBody676_183

def loopBody676_185 : HolLoopProg 64 :=
.mark loopBody676_184

def loopBody676_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody676_187 : HolLoopProg 64 :=
.mark loopBody676_186

def loopBody676_188 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody676_185 loopBody676_187 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody676_189 : HolLoopProg 64 :=
.mark loopBody676_188

def loopBody676_190 : HolLoopProg 64 :=
.seq loopBody676_189 loopBody676_1

def loopBody676_191 : HolLoopProg 64 :=
.mark loopBody676_190

def loopBody676_192 : HolLoopProg 64 :=
.seq loopBody676_73 loopBody676_191

def loopBody676_193 : HolLoopProg 64 :=
.mark loopBody676_192

def loopBody676_194 : HolLoopProg 64 :=
.seq loopBody676_71 loopBody676_193

def loopBody676_195 : HolLoopProg 64 :=
.mark loopBody676_194

def loopBody676_196 : HolLoopProg 64 :=
.seq loopBody676_67 loopBody676_195

def loopBody676_197 : HolLoopProg 64 :=
.mark loopBody676_196

def loopBody676_198 : HolLoopProg 64 :=
.seq loopBody676_65 loopBody676_197

def loopBody676_199 : HolLoopProg 64 :=
.mark loopBody676_198

def loopBody676_200 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody676_199 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody676_201 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 0)

def loopBody676_202 : HolLoopProg 64 :=
.mark loopBody676_201

def loopBody676_203 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 725) ([10, 11]) (some (10, loopBody676_97, loopBody676_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody676_204 : HolLoopProg 64 :=
.mark loopBody676_203

def loopBody676_205 : HolLoopProg 64 :=
.seq loopBody676_204 loopBody676_1

def loopBody676_206 : HolLoopProg 64 :=
.mark loopBody676_205

def loopBody676_207 : HolLoopProg 64 :=
.seq loopBody676_95 loopBody676_206

def loopBody676_208 : HolLoopProg 64 :=
.mark loopBody676_207

def loopBody676_209 : HolLoopProg 64 :=
.seq loopBody676_202 loopBody676_208

def loopBody676_210 : HolLoopProg 64 :=
.mark loopBody676_209

def loopBody676_211 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_210

def loopBody676_212 : HolLoopProg 64 :=
.mark loopBody676_211

def loopBody676_213 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_212

def loopBody676_214 : HolLoopProg 64 :=
.mark loopBody676_213

def loopBody676_215 : HolLoopProg 64 :=
.seq loopBody676_200 loopBody676_214

def loopBody676_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody676_217 : HolLoopProg 64 :=
.mark loopBody676_216

def loopBody676_218 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 70) ([10]) (some (10, loopBody676_97, loopBody676_1, (Flapjack.Spt.ln)))

def loopBody676_219 : HolLoopProg 64 :=
.mark loopBody676_218

def loopBody676_220 : HolLoopProg 64 :=
.seq loopBody676_219 loopBody676_1

def loopBody676_221 : HolLoopProg 64 :=
.mark loopBody676_220

def loopBody676_222 : HolLoopProg 64 :=
.seq loopBody676_217 loopBody676_221

def loopBody676_223 : HolLoopProg 64 :=
.mark loopBody676_222

def loopBody676_224 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_223

def loopBody676_225 : HolLoopProg 64 :=
.mark loopBody676_224

def loopBody676_226 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_225

def loopBody676_227 : HolLoopProg 64 :=
.mark loopBody676_226

def loopBody676_228 : HolLoopProg 64 :=
.seq loopBody676_215 loopBody676_227

def loopBody676_229 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody676_230 : HolLoopProg 64 :=
.mark loopBody676_229

def loopBody676_231 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody676_232 : HolLoopProg 64 :=
.mark loopBody676_231

def loopBody676_233 : HolLoopProg 64 :=
.seq loopBody676_232 loopBody676_1

def loopBody676_234 : HolLoopProg 64 :=
.mark loopBody676_233

def loopBody676_235 : HolLoopProg 64 :=
.seq loopBody676_230 loopBody676_234

def loopBody676_236 : HolLoopProg 64 :=
.mark loopBody676_235

def loopBody676_237 : HolLoopProg 64 :=
.seq loopBody676_228 loopBody676_236

def loopBody676_238 : HolLoopProg 64 :=
.seq loopBody676_63 loopBody676_237

def loopBody676_239 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_238

def loopBody676_240 : HolLoopProg 64 :=
.seq loopBody676_61 loopBody676_239

def loopBody676_241 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_240

def loopBody676_242 : HolLoopProg 64 :=
.seq loopBody676_59 loopBody676_241

def loopBody676_243 : HolLoopProg 64 :=
.seq loopBody676_27 loopBody676_242

def loopBody676_244 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_243

def loopBody676_245 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_244

def loopBody676_246 : HolLoopProg 64 :=
.seq loopBody676_17 loopBody676_245

def loopBody676_247 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_246

def loopBody676_248 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_247

def loopBody676_249 : HolLoopProg 64 :=
.seq loopBody676_7 loopBody676_248

def loopBody676_250 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_249

def loopBody676_251 : HolLoopProg 64 :=
.seq loopBody676_1 loopBody676_250

def output676 : Nat × List Nat × HolLoopProg 64 :=
  (740, [0, 1, 2, 3], loopBody676_251)
end InitECandidate.Proofs.FrontendStages.Loop
