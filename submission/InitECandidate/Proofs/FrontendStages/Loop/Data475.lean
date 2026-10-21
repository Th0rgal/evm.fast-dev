import InitECandidate.Proofs.FrontendStages.Loop.Translate459
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody475_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody475_1 : HolLoopProg 64 :=
.mark loopBody475_0

def loopBody475_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 3#64)

def loopBody475_3 : HolLoopProg 64 :=
.mark loopBody475_2

def loopBody475_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody475_5 : HolLoopProg 64 :=
.mark loopBody475_4

def loopBody475_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody475_5, loopBody475_1, (Flapjack.Spt.ln)))

def loopBody475_7 : HolLoopProg 64 :=
.mark loopBody475_6

def loopBody475_8 : HolLoopProg 64 :=
.seq loopBody475_7 loopBody475_1

def loopBody475_9 : HolLoopProg 64 :=
.mark loopBody475_8

def loopBody475_10 : HolLoopProg 64 :=
.seq loopBody475_3 loopBody475_9

def loopBody475_11 : HolLoopProg 64 :=
.mark loopBody475_10

def loopBody475_12 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_11

def loopBody475_13 : HolLoopProg 64 :=
.mark loopBody475_12

def loopBody475_14 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_13

def loopBody475_15 : HolLoopProg 64 :=
.mark loopBody475_14

def loopBody475_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 536) ([]) (some (2, loopBody475_5, loopBody475_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody475_17 : HolLoopProg 64 :=
.mark loopBody475_16

def loopBody475_18 : HolLoopProg 64 :=
.seq loopBody475_17 loopBody475_1

def loopBody475_19 : HolLoopProg 64 :=
.mark loopBody475_18

def loopBody475_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody475_21 : HolLoopProg 64 :=
.mark loopBody475_20

def loopBody475_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody475_23 : HolLoopProg 64 :=
.mark loopBody475_22

def loopBody475_24 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 537) ([3]) (some (3, loopBody475_23, loopBody475_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody475_25 : HolLoopProg 64 :=
.mark loopBody475_24

def loopBody475_26 : HolLoopProg 64 :=
.seq loopBody475_25 loopBody475_1

def loopBody475_27 : HolLoopProg 64 :=
.mark loopBody475_26

def loopBody475_28 : HolLoopProg 64 :=
.seq loopBody475_21 loopBody475_27

def loopBody475_29 : HolLoopProg 64 :=
.mark loopBody475_28

def loopBody475_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody475_31 : HolLoopProg 64 :=
.mark loopBody475_30

def loopBody475_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody475_33 : HolLoopProg 64 :=
.mark loopBody475_32

def loopBody475_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody475_35 : HolLoopProg 64 :=
.mark loopBody475_34

def loopBody475_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody475_37 : HolLoopProg 64 :=
.mark loopBody475_36

def loopBody475_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody475_35 loopBody475_37 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody475_39 : HolLoopProg 64 :=
.mark loopBody475_38

def loopBody475_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody475_41 : HolLoopProg 64 :=
.mark loopBody475_40

def loopBody475_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 2#64)

def loopBody475_43 : HolLoopProg 64 :=
.mark loopBody475_42

def loopBody475_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody475_45 : HolLoopProg 64 :=
.mark loopBody475_44

def loopBody475_46 : HolLoopProg 64 :=
.seq loopBody475_45 loopBody475_1

def loopBody475_47 : HolLoopProg 64 :=
.mark loopBody475_46

def loopBody475_48 : HolLoopProg 64 :=
.seq loopBody475_47 loopBody475_1

def loopBody475_49 : HolLoopProg 64 :=
.mark loopBody475_48

def loopBody475_50 : HolLoopProg 64 :=
.seq loopBody475_43 loopBody475_49

def loopBody475_51 : HolLoopProg 64 :=
.mark loopBody475_50

def loopBody475_52 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_51

def loopBody475_53 : HolLoopProg 64 :=
.mark loopBody475_52

def loopBody475_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody475_55 : HolLoopProg 64 :=
.mark loopBody475_54

def loopBody475_56 : HolLoopProg 64 :=
.seq loopBody475_55 loopBody475_23

def loopBody475_57 : HolLoopProg 64 :=
.mark loopBody475_56

def loopBody475_58 : HolLoopProg 64 :=
.seq loopBody475_53 loopBody475_57

def loopBody475_59 : HolLoopProg 64 :=
.mark loopBody475_58

def loopBody475_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody475_59 loopBody475_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody475_61 : HolLoopProg 64 :=
.mark loopBody475_60

def loopBody475_62 : HolLoopProg 64 :=
.seq loopBody475_61 loopBody475_1

def loopBody475_63 : HolLoopProg 64 :=
.mark loopBody475_62

def loopBody475_64 : HolLoopProg 64 :=
.seq loopBody475_41 loopBody475_63

def loopBody475_65 : HolLoopProg 64 :=
.mark loopBody475_64

def loopBody475_66 : HolLoopProg 64 :=
.seq loopBody475_39 loopBody475_65

def loopBody475_67 : HolLoopProg 64 :=
.mark loopBody475_66

def loopBody475_68 : HolLoopProg 64 :=
.seq loopBody475_33 loopBody475_67

def loopBody475_69 : HolLoopProg 64 :=
.mark loopBody475_68

def loopBody475_70 : HolLoopProg 64 :=
.seq loopBody475_31 loopBody475_69

def loopBody475_71 : HolLoopProg 64 :=
.mark loopBody475_70

def loopBody475_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody475_73 : HolLoopProg 64 :=
.mark loopBody475_72

def loopBody475_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody475_75 : HolLoopProg 64 :=
.mark loopBody475_74

def loopBody475_76 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 534) ([4, 5]) (some (4, loopBody475_75, loopBody475_1, (Flapjack.Spt.ln)))

def loopBody475_77 : HolLoopProg 64 :=
.mark loopBody475_76

def loopBody475_78 : HolLoopProg 64 :=
.seq loopBody475_77 loopBody475_1

def loopBody475_79 : HolLoopProg 64 :=
.mark loopBody475_78

def loopBody475_80 : HolLoopProg 64 :=
.seq loopBody475_73 loopBody475_79

def loopBody475_81 : HolLoopProg 64 :=
.mark loopBody475_80

def loopBody475_82 : HolLoopProg 64 :=
.seq loopBody475_37 loopBody475_81

def loopBody475_83 : HolLoopProg 64 :=
.mark loopBody475_82

def loopBody475_84 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_83

def loopBody475_85 : HolLoopProg 64 :=
.mark loopBody475_84

def loopBody475_86 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_85

def loopBody475_87 : HolLoopProg 64 :=
.mark loopBody475_86

def loopBody475_88 : HolLoopProg 64 :=
.seq loopBody475_71 loopBody475_87

def loopBody475_89 : HolLoopProg 64 :=
.mark loopBody475_88

def loopBody475_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 2#64)

def loopBody475_91 : HolLoopProg 64 :=
.mark loopBody475_90

def loopBody475_92 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 486) ([4]) (some (4, loopBody475_75, loopBody475_1, (Flapjack.Spt.ln)))

def loopBody475_93 : HolLoopProg 64 :=
.mark loopBody475_92

def loopBody475_94 : HolLoopProg 64 :=
.seq loopBody475_93 loopBody475_1

def loopBody475_95 : HolLoopProg 64 :=
.mark loopBody475_94

def loopBody475_96 : HolLoopProg 64 :=
.seq loopBody475_91 loopBody475_95

def loopBody475_97 : HolLoopProg 64 :=
.mark loopBody475_96

def loopBody475_98 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_97

def loopBody475_99 : HolLoopProg 64 :=
.mark loopBody475_98

def loopBody475_100 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_99

def loopBody475_101 : HolLoopProg 64 :=
.mark loopBody475_100

def loopBody475_102 : HolLoopProg 64 :=
.seq loopBody475_89 loopBody475_101

def loopBody475_103 : HolLoopProg 64 :=
.mark loopBody475_102

def loopBody475_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody475_105 : HolLoopProg 64 :=
.mark loopBody475_104

def loopBody475_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody475_107 : HolLoopProg 64 :=
.mark loopBody475_106

def loopBody475_108 : HolLoopProg 64 :=
.seq loopBody475_107 loopBody475_1

def loopBody475_109 : HolLoopProg 64 :=
.mark loopBody475_108

def loopBody475_110 : HolLoopProg 64 :=
.seq loopBody475_105 loopBody475_109

def loopBody475_111 : HolLoopProg 64 :=
.mark loopBody475_110

def loopBody475_112 : HolLoopProg 64 :=
.seq loopBody475_103 loopBody475_111

def loopBody475_113 : HolLoopProg 64 :=
.mark loopBody475_112

def loopBody475_114 : HolLoopProg 64 :=
.seq loopBody475_29 loopBody475_113

def loopBody475_115 : HolLoopProg 64 :=
.mark loopBody475_114

def loopBody475_116 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_115

def loopBody475_117 : HolLoopProg 64 :=
.mark loopBody475_116

def loopBody475_118 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_117

def loopBody475_119 : HolLoopProg 64 :=
.mark loopBody475_118

def loopBody475_120 : HolLoopProg 64 :=
.seq loopBody475_19 loopBody475_119

def loopBody475_121 : HolLoopProg 64 :=
.mark loopBody475_120

def loopBody475_122 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_121

def loopBody475_123 : HolLoopProg 64 :=
.mark loopBody475_122

def loopBody475_124 : HolLoopProg 64 :=
.seq loopBody475_1 loopBody475_123

def loopBody475_125 : HolLoopProg 64 :=
.mark loopBody475_124

def loopBody475_126 : HolLoopProg 64 :=
.seq loopBody475_15 loopBody475_125

def loopBody475_127 : HolLoopProg 64 :=
.mark loopBody475_126

def output475 : Nat × List Nat × HolLoopProg 64 :=
  (539, [], loopBody475_127)
end InitECandidate.Proofs.FrontendStages.Loop
