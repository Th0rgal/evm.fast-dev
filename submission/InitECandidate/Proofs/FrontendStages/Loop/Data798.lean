import InitECandidate.Proofs.FrontendStages.Loop.Translate782
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody798_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody798_1 : HolLoopProg 64 :=
.mark loopBody798_0

def loopBody798_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64])

def loopBody798_3 : HolLoopProg 64 :=
.mark loopBody798_2

def loopBody798_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody798_5 : HolLoopProg 64 :=
.mark loopBody798_4

def loopBody798_6 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody798_5, loopBody798_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody798_7 : HolLoopProg 64 :=
.mark loopBody798_6

def loopBody798_8 : HolLoopProg 64 :=
.seq loopBody798_7 loopBody798_1

def loopBody798_9 : HolLoopProg 64 :=
.mark loopBody798_8

def loopBody798_10 : HolLoopProg 64 :=
.seq loopBody798_3 loopBody798_9

def loopBody798_11 : HolLoopProg 64 :=
.mark loopBody798_10

def loopBody798_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody798_13 : HolLoopProg 64 :=
.mark loopBody798_12

def loopBody798_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody798_15 : HolLoopProg 64 :=
.mark loopBody798_14

def loopBody798_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 4 5

def loopBody798_17 : HolLoopProg 64 :=
.mark loopBody798_16

def loopBody798_18 : HolLoopProg 64 :=
.seq loopBody798_17 loopBody798_1

def loopBody798_19 : HolLoopProg 64 :=
.mark loopBody798_18

def loopBody798_20 : HolLoopProg 64 :=
.seq loopBody798_15 loopBody798_19

def loopBody798_21 : HolLoopProg 64 :=
.mark loopBody798_20

def loopBody798_22 : HolLoopProg 64 :=
.seq loopBody798_13 loopBody798_21

def loopBody798_23 : HolLoopProg 64 :=
.mark loopBody798_22

def loopBody798_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody798_25 : HolLoopProg 64 :=
.mark loopBody798_24

def loopBody798_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody798_27 : HolLoopProg 64 :=
.mark loopBody798_26

def loopBody798_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody798_29 : HolLoopProg 64 :=
.mark loopBody798_28

def loopBody798_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody798_31 : HolLoopProg 64 :=
.mark loopBody798_30

def loopBody798_32 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([5, 6, 7]) (some (5, loopBody798_31, loopBody798_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody798_33 : HolLoopProg 64 :=
.mark loopBody798_32

def loopBody798_34 : HolLoopProg 64 :=
.seq loopBody798_33 loopBody798_1

def loopBody798_35 : HolLoopProg 64 :=
.mark loopBody798_34

def loopBody798_36 : HolLoopProg 64 :=
.seq loopBody798_29 loopBody798_35

def loopBody798_37 : HolLoopProg 64 :=
.mark loopBody798_36

def loopBody798_38 : HolLoopProg 64 :=
.seq loopBody798_27 loopBody798_37

def loopBody798_39 : HolLoopProg 64 :=
.mark loopBody798_38

def loopBody798_40 : HolLoopProg 64 :=
.seq loopBody798_25 loopBody798_39

def loopBody798_41 : HolLoopProg 64 :=
.mark loopBody798_40

def loopBody798_42 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_41

def loopBody798_43 : HolLoopProg 64 :=
.mark loopBody798_42

def loopBody798_44 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_43

def loopBody798_45 : HolLoopProg 64 :=
.mark loopBody798_44

def loopBody798_46 : HolLoopProg 64 :=
.seq loopBody798_23 loopBody798_45

def loopBody798_47 : HolLoopProg 64 :=
.mark loopBody798_46

def loopBody798_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 416#64]),
        Flapjack.HolLoopExp.const 64#64]))

def loopBody798_49 : HolLoopProg 64 :=
.mark loopBody798_48

def loopBody798_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 416#64]),
            Flapjack.HolLoopExp.const 56#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64)])

def loopBody798_51 : HolLoopProg 64 :=
.mark loopBody798_50

def loopBody798_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody798_53 : HolLoopProg 64 :=
.mark loopBody798_52

def loopBody798_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody798_55 : HolLoopProg 64 :=
.mark loopBody798_54

def loopBody798_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody798_57 : HolLoopProg 64 :=
.mark loopBody798_56

def loopBody798_58 : HolLoopProg 64 :=
.seq loopBody798_57 loopBody798_1

def loopBody798_59 : HolLoopProg 64 :=
.mark loopBody798_58

def loopBody798_60 : HolLoopProg 64 :=
.seq loopBody798_55 loopBody798_59

def loopBody798_61 : HolLoopProg 64 :=
.mark loopBody798_60

def loopBody798_62 : HolLoopProg 64 :=
.seq loopBody798_61 loopBody798_1

def loopBody798_63 : HolLoopProg 64 :=
.mark loopBody798_62

def loopBody798_64 : HolLoopProg 64 :=
.seq loopBody798_53 loopBody798_63

def loopBody798_65 : HolLoopProg 64 :=
.mark loopBody798_64

def loopBody798_66 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_65

def loopBody798_67 : HolLoopProg 64 :=
.mark loopBody798_66

def loopBody798_68 : HolLoopProg 64 :=
.seq loopBody798_51 loopBody798_67

def loopBody798_69 : HolLoopProg 64 :=
.mark loopBody798_68

def loopBody798_70 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_69

def loopBody798_71 : HolLoopProg 64 :=
.mark loopBody798_70

def loopBody798_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 416#64]),
            Flapjack.HolLoopExp.const 56#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.const 8#64])

def loopBody798_73 : HolLoopProg 64 :=
.mark loopBody798_72

def loopBody798_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody798_75 : HolLoopProg 64 :=
.mark loopBody798_74

def loopBody798_76 : HolLoopProg 64 :=
.seq loopBody798_75 loopBody798_63

def loopBody798_77 : HolLoopProg 64 :=
.mark loopBody798_76

def loopBody798_78 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_77

def loopBody798_79 : HolLoopProg 64 :=
.mark loopBody798_78

def loopBody798_80 : HolLoopProg 64 :=
.seq loopBody798_73 loopBody798_79

def loopBody798_81 : HolLoopProg 64 :=
.mark loopBody798_80

def loopBody798_82 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_81

def loopBody798_83 : HolLoopProg 64 :=
.mark loopBody798_82

def loopBody798_84 : HolLoopProg 64 :=
.seq loopBody798_71 loopBody798_83

def loopBody798_85 : HolLoopProg 64 :=
.mark loopBody798_84

def loopBody798_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 416#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody798_87 : HolLoopProg 64 :=
.mark loopBody798_86

def loopBody798_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody798_89 : HolLoopProg 64 :=
.mark loopBody798_88

def loopBody798_90 : HolLoopProg 64 :=
.seq loopBody798_89 loopBody798_63

def loopBody798_91 : HolLoopProg 64 :=
.mark loopBody798_90

def loopBody798_92 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_91

def loopBody798_93 : HolLoopProg 64 :=
.mark loopBody798_92

def loopBody798_94 : HolLoopProg 64 :=
.seq loopBody798_87 loopBody798_93

def loopBody798_95 : HolLoopProg 64 :=
.mark loopBody798_94

def loopBody798_96 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_95

def loopBody798_97 : HolLoopProg 64 :=
.mark loopBody798_96

def loopBody798_98 : HolLoopProg 64 :=
.seq loopBody798_85 loopBody798_97

def loopBody798_99 : HolLoopProg 64 :=
.mark loopBody798_98

def loopBody798_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody798_101 : HolLoopProg 64 :=
.mark loopBody798_100

def loopBody798_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody798_103 : HolLoopProg 64 :=
.mark loopBody798_102

def loopBody798_104 : HolLoopProg 64 :=
.seq loopBody798_103 loopBody798_1

def loopBody798_105 : HolLoopProg 64 :=
.mark loopBody798_104

def loopBody798_106 : HolLoopProg 64 :=
.seq loopBody798_101 loopBody798_105

def loopBody798_107 : HolLoopProg 64 :=
.mark loopBody798_106

def loopBody798_108 : HolLoopProg 64 :=
.seq loopBody798_99 loopBody798_107

def loopBody798_109 : HolLoopProg 64 :=
.mark loopBody798_108

def loopBody798_110 : HolLoopProg 64 :=
.seq loopBody798_49 loopBody798_109

def loopBody798_111 : HolLoopProg 64 :=
.mark loopBody798_110

def loopBody798_112 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_111

def loopBody798_113 : HolLoopProg 64 :=
.mark loopBody798_112

def loopBody798_114 : HolLoopProg 64 :=
.seq loopBody798_47 loopBody798_113

def loopBody798_115 : HolLoopProg 64 :=
.mark loopBody798_114

def loopBody798_116 : HolLoopProg 64 :=
.seq loopBody798_11 loopBody798_115

def loopBody798_117 : HolLoopProg 64 :=
.mark loopBody798_116

def loopBody798_118 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_117

def loopBody798_119 : HolLoopProg 64 :=
.mark loopBody798_118

def loopBody798_120 : HolLoopProg 64 :=
.seq loopBody798_1 loopBody798_119

def loopBody798_121 : HolLoopProg 64 :=
.mark loopBody798_120

def output798 : Nat × List Nat × HolLoopProg 64 :=
  (862, [0, 1, 2], loopBody798_121)
end InitECandidate.Proofs.FrontendStages.Loop
