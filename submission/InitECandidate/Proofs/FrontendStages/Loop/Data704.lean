import InitECandidate.Proofs.FrontendStages.Loop.Translate688
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody704_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody704_1 : HolLoopProg 64 :=
.mark loopBody704_0

def loopBody704_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody704_3 : HolLoopProg 64 :=
.mark loopBody704_2

def loopBody704_4 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (5, loopBody704_3, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody704_5 : HolLoopProg 64 :=
.mark loopBody704_4

def loopBody704_6 : HolLoopProg 64 :=
.seq loopBody704_5 loopBody704_1

def loopBody704_7 : HolLoopProg 64 :=
.mark loopBody704_6

def loopBody704_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 144#64)

def loopBody704_9 : HolLoopProg 64 :=
.mark loopBody704_8

def loopBody704_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody704_11 : HolLoopProg 64 :=
.mark loopBody704_10

def loopBody704_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([6]) (some (6, loopBody704_11, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody704_13 : HolLoopProg 64 :=
.mark loopBody704_12

def loopBody704_14 : HolLoopProg 64 :=
.seq loopBody704_13 loopBody704_1

def loopBody704_15 : HolLoopProg 64 :=
.mark loopBody704_14

def loopBody704_16 : HolLoopProg 64 :=
.seq loopBody704_9 loopBody704_15

def loopBody704_17 : HolLoopProg 64 :=
.mark loopBody704_16

def loopBody704_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 144#64)

def loopBody704_19 : HolLoopProg 64 :=
.mark loopBody704_18

def loopBody704_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody704_21 : HolLoopProg 64 :=
.mark loopBody704_20

def loopBody704_22 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([7]) (some (7, loopBody704_21, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody704_23 : HolLoopProg 64 :=
.mark loopBody704_22

def loopBody704_24 : HolLoopProg 64 :=
.seq loopBody704_23 loopBody704_1

def loopBody704_25 : HolLoopProg 64 :=
.mark loopBody704_24

def loopBody704_26 : HolLoopProg 64 :=
.seq loopBody704_19 loopBody704_25

def loopBody704_27 : HolLoopProg 64 :=
.mark loopBody704_26

def loopBody704_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody704_29 : HolLoopProg 64 :=
.mark loopBody704_28

def loopBody704_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody704_31 : HolLoopProg 64 :=
.mark loopBody704_30

def loopBody704_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody704_33 : HolLoopProg 64 :=
.mark loopBody704_32

def loopBody704_34 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 764) ([8, 9]) (some (8, loopBody704_33, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody704_35 : HolLoopProg 64 :=
.mark loopBody704_34

def loopBody704_36 : HolLoopProg 64 :=
.seq loopBody704_35 loopBody704_1

def loopBody704_37 : HolLoopProg 64 :=
.mark loopBody704_36

def loopBody704_38 : HolLoopProg 64 :=
.seq loopBody704_31 loopBody704_37

def loopBody704_39 : HolLoopProg 64 :=
.mark loopBody704_38

def loopBody704_40 : HolLoopProg 64 :=
.seq loopBody704_29 loopBody704_39

def loopBody704_41 : HolLoopProg 64 :=
.mark loopBody704_40

def loopBody704_42 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_41

def loopBody704_43 : HolLoopProg 64 :=
.mark loopBody704_42

def loopBody704_44 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_43

def loopBody704_45 : HolLoopProg 64 :=
.mark loopBody704_44

def loopBody704_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody704_47 : HolLoopProg 64 :=
.mark loopBody704_46

def loopBody704_48 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 762) ([8]) (some (8, loopBody704_33, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody704_49 : HolLoopProg 64 :=
.mark loopBody704_48

def loopBody704_50 : HolLoopProg 64 :=
.seq loopBody704_49 loopBody704_1

def loopBody704_51 : HolLoopProg 64 :=
.mark loopBody704_50

def loopBody704_52 : HolLoopProg 64 :=
.seq loopBody704_47 loopBody704_51

def loopBody704_53 : HolLoopProg 64 :=
.mark loopBody704_52

def loopBody704_54 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_53

def loopBody704_55 : HolLoopProg 64 :=
.mark loopBody704_54

def loopBody704_56 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_55

def loopBody704_57 : HolLoopProg 64 :=
.mark loopBody704_56

def loopBody704_58 : HolLoopProg 64 :=
.seq loopBody704_45 loopBody704_57

def loopBody704_59 : HolLoopProg 64 :=
.mark loopBody704_58

def loopBody704_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 6#64))

def loopBody704_61 : HolLoopProg 64 :=
.mark loopBody704_60

def loopBody704_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody704_63 : HolLoopProg 64 :=
.mark loopBody704_62

def loopBody704_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody704_65 : HolLoopProg 64 :=
.mark loopBody704_64

def loopBody704_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody704_67 : HolLoopProg 64 :=
.mark loopBody704_66

def loopBody704_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody704_69 : HolLoopProg 64 :=
.mark loopBody704_68

def loopBody704_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.RegImm.reg 11) loopBody704_69 loopBody704_65 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_71 : HolLoopProg 64 :=
.mark loopBody704_70

def loopBody704_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody704_73 : HolLoopProg 64 :=
.mark loopBody704_72

def loopBody704_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody704_75 : HolLoopProg 64 :=
.mark loopBody704_74

def loopBody704_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 9)

def loopBody704_77 : HolLoopProg 64 :=
.mark loopBody704_76

def loopBody704_78 : HolLoopProg 64 :=
.seq loopBody704_77 loopBody704_1

def loopBody704_79 : HolLoopProg 64 :=
.mark loopBody704_78

def loopBody704_80 : HolLoopProg 64 :=
.seq loopBody704_79 loopBody704_1

def loopBody704_81 : HolLoopProg 64 :=
.mark loopBody704_80

def loopBody704_82 : HolLoopProg 64 :=
.seq loopBody704_75 loopBody704_81

def loopBody704_83 : HolLoopProg 64 :=
.mark loopBody704_82

def loopBody704_84 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_83

def loopBody704_85 : HolLoopProg 64 :=
.mark loopBody704_84

def loopBody704_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody704_87 : HolLoopProg 64 :=
.mark loopBody704_86

def loopBody704_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody704_89 : HolLoopProg 64 :=
.mark loopBody704_88

def loopBody704_90 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.RegImm.reg 11) loopBody704_69 loopBody704_65 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_91 : HolLoopProg 64 :=
.mark loopBody704_90

def loopBody704_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody704_93 : HolLoopProg 64 :=
.mark loopBody704_92

def loopBody704_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody704_95 : HolLoopProg 64 :=
.mark loopBody704_94

def loopBody704_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody704_97 : HolLoopProg 64 :=
.mark loopBody704_96

def loopBody704_98 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 766) ([10, 11]) (some (10, loopBody704_97, loopBody704_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody704_99 : HolLoopProg 64 :=
.mark loopBody704_98

def loopBody704_100 : HolLoopProg 64 :=
.seq loopBody704_99 loopBody704_1

def loopBody704_101 : HolLoopProg 64 :=
.mark loopBody704_100

def loopBody704_102 : HolLoopProg 64 :=
.seq loopBody704_95 loopBody704_101

def loopBody704_103 : HolLoopProg 64 :=
.mark loopBody704_102

def loopBody704_104 : HolLoopProg 64 :=
.seq loopBody704_93 loopBody704_103

def loopBody704_105 : HolLoopProg 64 :=
.mark loopBody704_104

def loopBody704_106 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_105

def loopBody704_107 : HolLoopProg 64 :=
.mark loopBody704_106

def loopBody704_108 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_107

def loopBody704_109 : HolLoopProg 64 :=
.mark loopBody704_108

def loopBody704_110 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody704_109 loopBody704_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_111 : HolLoopProg 64 :=
.mark loopBody704_110

def loopBody704_112 : HolLoopProg 64 :=
.seq loopBody704_111 loopBody704_1

def loopBody704_113 : HolLoopProg 64 :=
.mark loopBody704_112

def loopBody704_114 : HolLoopProg 64 :=
.seq loopBody704_73 loopBody704_113

def loopBody704_115 : HolLoopProg 64 :=
.mark loopBody704_114

def loopBody704_116 : HolLoopProg 64 :=
.seq loopBody704_91 loopBody704_115

def loopBody704_117 : HolLoopProg 64 :=
.mark loopBody704_116

def loopBody704_118 : HolLoopProg 64 :=
.seq loopBody704_89 loopBody704_117

def loopBody704_119 : HolLoopProg 64 :=
.mark loopBody704_118

def loopBody704_120 : HolLoopProg 64 :=
.seq loopBody704_87 loopBody704_119

def loopBody704_121 : HolLoopProg 64 :=
.mark loopBody704_120

def loopBody704_122 : HolLoopProg 64 :=
.seq loopBody704_85 loopBody704_121

def loopBody704_123 : HolLoopProg 64 :=
.mark loopBody704_122

def loopBody704_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 2,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 7)
                  (Flapjack.HolLoopExp.const 6#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 63#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody704_125 : HolLoopProg 64 :=
.mark loopBody704_124

def loopBody704_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody704_127 : HolLoopProg 64 :=
.mark loopBody704_126

def loopBody704_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody704_129 : HolLoopProg 64 :=
.mark loopBody704_128

def loopBody704_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody704_131 : HolLoopProg 64 :=
.mark loopBody704_130

def loopBody704_132 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody704_89 loopBody704_131 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_133 : HolLoopProg 64 :=
.mark loopBody704_132

def loopBody704_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody704_135 : HolLoopProg 64 :=
.mark loopBody704_134

def loopBody704_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 5)

def loopBody704_137 : HolLoopProg 64 :=
.mark loopBody704_136

def loopBody704_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 6)

def loopBody704_139 : HolLoopProg 64 :=
.mark loopBody704_138

def loopBody704_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody704_141 : HolLoopProg 64 :=
.mark loopBody704_140

def loopBody704_142 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 767) ([11, 12, 13]) (some (11, loopBody704_141, loopBody704_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody704_143 : HolLoopProg 64 :=
.mark loopBody704_142

def loopBody704_144 : HolLoopProg 64 :=
.seq loopBody704_143 loopBody704_1

def loopBody704_145 : HolLoopProg 64 :=
.mark loopBody704_144

def loopBody704_146 : HolLoopProg 64 :=
.seq loopBody704_139 loopBody704_145

def loopBody704_147 : HolLoopProg 64 :=
.mark loopBody704_146

def loopBody704_148 : HolLoopProg 64 :=
.seq loopBody704_137 loopBody704_147

def loopBody704_149 : HolLoopProg 64 :=
.mark loopBody704_148

def loopBody704_150 : HolLoopProg 64 :=
.seq loopBody704_95 loopBody704_149

def loopBody704_151 : HolLoopProg 64 :=
.mark loopBody704_150

def loopBody704_152 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_151

def loopBody704_153 : HolLoopProg 64 :=
.mark loopBody704_152

def loopBody704_154 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_153

def loopBody704_155 : HolLoopProg 64 :=
.mark loopBody704_154

def loopBody704_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody704_157 : HolLoopProg 64 :=
.mark loopBody704_156

def loopBody704_158 : HolLoopProg 64 :=
.seq loopBody704_157 loopBody704_1

def loopBody704_159 : HolLoopProg 64 :=
.mark loopBody704_158

def loopBody704_160 : HolLoopProg 64 :=
.seq loopBody704_159 loopBody704_1

def loopBody704_161 : HolLoopProg 64 :=
.mark loopBody704_160

def loopBody704_162 : HolLoopProg 64 :=
.seq loopBody704_155 loopBody704_161

def loopBody704_163 : HolLoopProg 64 :=
.mark loopBody704_162

def loopBody704_164 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody704_163 loopBody704_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_165 : HolLoopProg 64 :=
.mark loopBody704_164

def loopBody704_166 : HolLoopProg 64 :=
.seq loopBody704_165 loopBody704_1

def loopBody704_167 : HolLoopProg 64 :=
.mark loopBody704_166

def loopBody704_168 : HolLoopProg 64 :=
.seq loopBody704_135 loopBody704_167

def loopBody704_169 : HolLoopProg 64 :=
.mark loopBody704_168

def loopBody704_170 : HolLoopProg 64 :=
.seq loopBody704_133 loopBody704_169

def loopBody704_171 : HolLoopProg 64 :=
.mark loopBody704_170

def loopBody704_172 : HolLoopProg 64 :=
.seq loopBody704_129 loopBody704_171

def loopBody704_173 : HolLoopProg 64 :=
.mark loopBody704_172

def loopBody704_174 : HolLoopProg 64 :=
.seq loopBody704_127 loopBody704_173

def loopBody704_175 : HolLoopProg 64 :=
.mark loopBody704_174

def loopBody704_176 : HolLoopProg 64 :=
.seq loopBody704_125 loopBody704_175

def loopBody704_177 : HolLoopProg 64 :=
.mark loopBody704_176

def loopBody704_178 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_177

def loopBody704_179 : HolLoopProg 64 :=
.mark loopBody704_178

def loopBody704_180 : HolLoopProg 64 :=
.seq loopBody704_123 loopBody704_179

def loopBody704_181 : HolLoopProg 64 :=
.mark loopBody704_180

def loopBody704_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody704_183 : HolLoopProg 64 :=
.mark loopBody704_182

def loopBody704_184 : HolLoopProg 64 :=
.seq loopBody704_181 loopBody704_183

def loopBody704_185 : HolLoopProg 64 :=
.mark loopBody704_184

def loopBody704_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody704_187 : HolLoopProg 64 :=
.mark loopBody704_186

def loopBody704_188 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody704_185 loopBody704_187 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody704_189 : HolLoopProg 64 :=
.mark loopBody704_188

def loopBody704_190 : HolLoopProg 64 :=
.seq loopBody704_189 loopBody704_1

def loopBody704_191 : HolLoopProg 64 :=
.mark loopBody704_190

def loopBody704_192 : HolLoopProg 64 :=
.seq loopBody704_73 loopBody704_191

def loopBody704_193 : HolLoopProg 64 :=
.mark loopBody704_192

def loopBody704_194 : HolLoopProg 64 :=
.seq loopBody704_71 loopBody704_193

def loopBody704_195 : HolLoopProg 64 :=
.mark loopBody704_194

def loopBody704_196 : HolLoopProg 64 :=
.seq loopBody704_67 loopBody704_195

def loopBody704_197 : HolLoopProg 64 :=
.mark loopBody704_196

def loopBody704_198 : HolLoopProg 64 :=
.seq loopBody704_65 loopBody704_197

def loopBody704_199 : HolLoopProg 64 :=
.mark loopBody704_198

def loopBody704_200 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody704_199 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody704_201 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 0)

def loopBody704_202 : HolLoopProg 64 :=
.mark loopBody704_201

def loopBody704_203 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 764) ([10, 11]) (some (10, loopBody704_97, loopBody704_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody704_204 : HolLoopProg 64 :=
.mark loopBody704_203

def loopBody704_205 : HolLoopProg 64 :=
.seq loopBody704_204 loopBody704_1

def loopBody704_206 : HolLoopProg 64 :=
.mark loopBody704_205

def loopBody704_207 : HolLoopProg 64 :=
.seq loopBody704_95 loopBody704_206

def loopBody704_208 : HolLoopProg 64 :=
.mark loopBody704_207

def loopBody704_209 : HolLoopProg 64 :=
.seq loopBody704_202 loopBody704_208

def loopBody704_210 : HolLoopProg 64 :=
.mark loopBody704_209

def loopBody704_211 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_210

def loopBody704_212 : HolLoopProg 64 :=
.mark loopBody704_211

def loopBody704_213 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_212

def loopBody704_214 : HolLoopProg 64 :=
.mark loopBody704_213

def loopBody704_215 : HolLoopProg 64 :=
.seq loopBody704_200 loopBody704_214

def loopBody704_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody704_217 : HolLoopProg 64 :=
.mark loopBody704_216

def loopBody704_218 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 70) ([10]) (some (10, loopBody704_97, loopBody704_1, (Flapjack.Spt.ln)))

def loopBody704_219 : HolLoopProg 64 :=
.mark loopBody704_218

def loopBody704_220 : HolLoopProg 64 :=
.seq loopBody704_219 loopBody704_1

def loopBody704_221 : HolLoopProg 64 :=
.mark loopBody704_220

def loopBody704_222 : HolLoopProg 64 :=
.seq loopBody704_217 loopBody704_221

def loopBody704_223 : HolLoopProg 64 :=
.mark loopBody704_222

def loopBody704_224 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_223

def loopBody704_225 : HolLoopProg 64 :=
.mark loopBody704_224

def loopBody704_226 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_225

def loopBody704_227 : HolLoopProg 64 :=
.mark loopBody704_226

def loopBody704_228 : HolLoopProg 64 :=
.seq loopBody704_215 loopBody704_227

def loopBody704_229 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody704_230 : HolLoopProg 64 :=
.mark loopBody704_229

def loopBody704_231 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody704_232 : HolLoopProg 64 :=
.mark loopBody704_231

def loopBody704_233 : HolLoopProg 64 :=
.seq loopBody704_232 loopBody704_1

def loopBody704_234 : HolLoopProg 64 :=
.mark loopBody704_233

def loopBody704_235 : HolLoopProg 64 :=
.seq loopBody704_230 loopBody704_234

def loopBody704_236 : HolLoopProg 64 :=
.mark loopBody704_235

def loopBody704_237 : HolLoopProg 64 :=
.seq loopBody704_228 loopBody704_236

def loopBody704_238 : HolLoopProg 64 :=
.seq loopBody704_63 loopBody704_237

def loopBody704_239 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_238

def loopBody704_240 : HolLoopProg 64 :=
.seq loopBody704_61 loopBody704_239

def loopBody704_241 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_240

def loopBody704_242 : HolLoopProg 64 :=
.seq loopBody704_59 loopBody704_241

def loopBody704_243 : HolLoopProg 64 :=
.seq loopBody704_27 loopBody704_242

def loopBody704_244 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_243

def loopBody704_245 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_244

def loopBody704_246 : HolLoopProg 64 :=
.seq loopBody704_17 loopBody704_245

def loopBody704_247 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_246

def loopBody704_248 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_247

def loopBody704_249 : HolLoopProg 64 :=
.seq loopBody704_7 loopBody704_248

def loopBody704_250 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_249

def loopBody704_251 : HolLoopProg 64 :=
.seq loopBody704_1 loopBody704_250

def output704 : Nat × List Nat × HolLoopProg 64 :=
  (768, [0, 1, 2, 3], loopBody704_251)
end InitECandidate.Proofs.FrontendStages.Loop
