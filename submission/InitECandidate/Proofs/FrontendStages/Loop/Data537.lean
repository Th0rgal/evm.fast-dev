import InitECandidate.Proofs.FrontendStages.Loop.Translate521
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody537_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody537_1 : HolLoopProg 64 :=
.mark loopBody537_0

def loopBody537_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody537_3 : HolLoopProg 64 :=
.mark loopBody537_2

def loopBody537_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody537_5 : HolLoopProg 64 :=
.mark loopBody537_4

def loopBody537_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 152#64]))

def loopBody537_7 : HolLoopProg 64 :=
.mark loopBody537_6

def loopBody537_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody537_9 : HolLoopProg 64 :=
.mark loopBody537_8

def loopBody537_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody537_11 : HolLoopProg 64 :=
.mark loopBody537_10

def loopBody537_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody537_13 : HolLoopProg 64 :=
.mark loopBody537_12

def loopBody537_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody537_11 loopBody537_13 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody537_15 : HolLoopProg 64 :=
.mark loopBody537_14

def loopBody537_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody537_17 : HolLoopProg 64 :=
.mark loopBody537_16

def loopBody537_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody537_19 : HolLoopProg 64 :=
.mark loopBody537_18

def loopBody537_20 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 589) ([]) (some (4, loopBody537_19, loopBody537_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody537_21 : HolLoopProg 64 :=
.mark loopBody537_20

def loopBody537_22 : HolLoopProg 64 :=
.seq loopBody537_21 loopBody537_1

def loopBody537_23 : HolLoopProg 64 :=
.mark loopBody537_22

def loopBody537_24 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_23

def loopBody537_25 : HolLoopProg 64 :=
.mark loopBody537_24

def loopBody537_26 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_25

def loopBody537_27 : HolLoopProg 64 :=
.mark loopBody537_26

def loopBody537_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]))

def loopBody537_29 : HolLoopProg 64 :=
.mark loopBody537_28

def loopBody537_30 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 469) ([4]) (some (4, loopBody537_19, loopBody537_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody537_31 : HolLoopProg 64 :=
.mark loopBody537_30

def loopBody537_32 : HolLoopProg 64 :=
.seq loopBody537_31 loopBody537_1

def loopBody537_33 : HolLoopProg 64 :=
.mark loopBody537_32

def loopBody537_34 : HolLoopProg 64 :=
.seq loopBody537_29 loopBody537_33

def loopBody537_35 : HolLoopProg 64 :=
.mark loopBody537_34

def loopBody537_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 200#64])

def loopBody537_37 : HolLoopProg 64 :=
.mark loopBody537_36

def loopBody537_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody537_39 : HolLoopProg 64 :=
.mark loopBody537_38

def loopBody537_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody537_41 : HolLoopProg 64 :=
.mark loopBody537_40

def loopBody537_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody537_43 : HolLoopProg 64 :=
.mark loopBody537_42

def loopBody537_44 : HolLoopProg 64 :=
.seq loopBody537_43 loopBody537_1

def loopBody537_45 : HolLoopProg 64 :=
.mark loopBody537_44

def loopBody537_46 : HolLoopProg 64 :=
.seq loopBody537_41 loopBody537_45

def loopBody537_47 : HolLoopProg 64 :=
.mark loopBody537_46

def loopBody537_48 : HolLoopProg 64 :=
.seq loopBody537_47 loopBody537_1

def loopBody537_49 : HolLoopProg 64 :=
.mark loopBody537_48

def loopBody537_50 : HolLoopProg 64 :=
.seq loopBody537_39 loopBody537_49

def loopBody537_51 : HolLoopProg 64 :=
.mark loopBody537_50

def loopBody537_52 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_51

def loopBody537_53 : HolLoopProg 64 :=
.mark loopBody537_52

def loopBody537_54 : HolLoopProg 64 :=
.seq loopBody537_37 loopBody537_53

def loopBody537_55 : HolLoopProg 64 :=
.mark loopBody537_54

def loopBody537_56 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_55

def loopBody537_57 : HolLoopProg 64 :=
.mark loopBody537_56

def loopBody537_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64])

def loopBody537_59 : HolLoopProg 64 :=
.mark loopBody537_58

def loopBody537_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 72#64]))

def loopBody537_61 : HolLoopProg 64 :=
.mark loopBody537_60

def loopBody537_62 : HolLoopProg 64 :=
.seq loopBody537_61 loopBody537_49

def loopBody537_63 : HolLoopProg 64 :=
.mark loopBody537_62

def loopBody537_64 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_63

def loopBody537_65 : HolLoopProg 64 :=
.mark loopBody537_64

def loopBody537_66 : HolLoopProg 64 :=
.seq loopBody537_59 loopBody537_65

def loopBody537_67 : HolLoopProg 64 :=
.mark loopBody537_66

def loopBody537_68 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_67

def loopBody537_69 : HolLoopProg 64 :=
.mark loopBody537_68

def loopBody537_70 : HolLoopProg 64 :=
.seq loopBody537_57 loopBody537_69

def loopBody537_71 : HolLoopProg 64 :=
.mark loopBody537_70

def loopBody537_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 192#64])

def loopBody537_73 : HolLoopProg 64 :=
.mark loopBody537_72

def loopBody537_74 : HolLoopProg 64 :=
.seq loopBody537_9 loopBody537_49

def loopBody537_75 : HolLoopProg 64 :=
.mark loopBody537_74

def loopBody537_76 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_75

def loopBody537_77 : HolLoopProg 64 :=
.mark loopBody537_76

def loopBody537_78 : HolLoopProg 64 :=
.seq loopBody537_73 loopBody537_77

def loopBody537_79 : HolLoopProg 64 :=
.mark loopBody537_78

def loopBody537_80 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_79

def loopBody537_81 : HolLoopProg 64 :=
.mark loopBody537_80

def loopBody537_82 : HolLoopProg 64 :=
.seq loopBody537_71 loopBody537_81

def loopBody537_83 : HolLoopProg 64 :=
.mark loopBody537_82

def loopBody537_84 : HolLoopProg 64 :=
.seq loopBody537_35 loopBody537_83

def loopBody537_85 : HolLoopProg 64 :=
.mark loopBody537_84

def loopBody537_86 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_85

def loopBody537_87 : HolLoopProg 64 :=
.mark loopBody537_86

def loopBody537_88 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_87

def loopBody537_89 : HolLoopProg 64 :=
.mark loopBody537_88

def loopBody537_90 : HolLoopProg 64 :=
.seq loopBody537_27 loopBody537_89

def loopBody537_91 : HolLoopProg 64 :=
.mark loopBody537_90

def loopBody537_92 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody537_91 loopBody537_1 (Flapjack.Spt.ln)

def loopBody537_93 : HolLoopProg 64 :=
.mark loopBody537_92

def loopBody537_94 : HolLoopProg 64 :=
.seq loopBody537_93 loopBody537_1

def loopBody537_95 : HolLoopProg 64 :=
.mark loopBody537_94

def loopBody537_96 : HolLoopProg 64 :=
.seq loopBody537_17 loopBody537_95

def loopBody537_97 : HolLoopProg 64 :=
.mark loopBody537_96

def loopBody537_98 : HolLoopProg 64 :=
.seq loopBody537_15 loopBody537_97

def loopBody537_99 : HolLoopProg 64 :=
.mark loopBody537_98

def loopBody537_100 : HolLoopProg 64 :=
.seq loopBody537_9 loopBody537_99

def loopBody537_101 : HolLoopProg 64 :=
.mark loopBody537_100

def loopBody537_102 : HolLoopProg 64 :=
.seq loopBody537_7 loopBody537_101

def loopBody537_103 : HolLoopProg 64 :=
.mark loopBody537_102

def loopBody537_104 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 590) ([]) (some (4, loopBody537_19, loopBody537_1, (Flapjack.Spt.ln)))

def loopBody537_105 : HolLoopProg 64 :=
.mark loopBody537_104

def loopBody537_106 : HolLoopProg 64 :=
.seq loopBody537_105 loopBody537_1

def loopBody537_107 : HolLoopProg 64 :=
.mark loopBody537_106

def loopBody537_108 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_107

def loopBody537_109 : HolLoopProg 64 :=
.mark loopBody537_108

def loopBody537_110 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_109

def loopBody537_111 : HolLoopProg 64 :=
.mark loopBody537_110

def loopBody537_112 : HolLoopProg 64 :=
.seq loopBody537_103 loopBody537_111

def loopBody537_113 : HolLoopProg 64 :=
.mark loopBody537_112

def loopBody537_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody537_115 : HolLoopProg 64 :=
.mark loopBody537_114

def loopBody537_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody537_117 : HolLoopProg 64 :=
.mark loopBody537_116

def loopBody537_118 : HolLoopProg 64 :=
.seq loopBody537_117 loopBody537_1

def loopBody537_119 : HolLoopProg 64 :=
.mark loopBody537_118

def loopBody537_120 : HolLoopProg 64 :=
.seq loopBody537_115 loopBody537_119

def loopBody537_121 : HolLoopProg 64 :=
.mark loopBody537_120

def loopBody537_122 : HolLoopProg 64 :=
.seq loopBody537_113 loopBody537_121

def loopBody537_123 : HolLoopProg 64 :=
.mark loopBody537_122

def loopBody537_124 : HolLoopProg 64 :=
.seq loopBody537_5 loopBody537_123

def loopBody537_125 : HolLoopProg 64 :=
.mark loopBody537_124

def loopBody537_126 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_125

def loopBody537_127 : HolLoopProg 64 :=
.mark loopBody537_126

def loopBody537_128 : HolLoopProg 64 :=
.seq loopBody537_3 loopBody537_127

def loopBody537_129 : HolLoopProg 64 :=
.mark loopBody537_128

def loopBody537_130 : HolLoopProg 64 :=
.seq loopBody537_1 loopBody537_129

def loopBody537_131 : HolLoopProg 64 :=
.mark loopBody537_130

def output537 : Nat × List Nat × HolLoopProg 64 :=
  (601, [], loopBody537_131)
end InitECandidate.Proofs.FrontendStages.Loop
