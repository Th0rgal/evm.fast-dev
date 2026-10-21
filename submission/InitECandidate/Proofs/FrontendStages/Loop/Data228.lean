import InitECandidate.Proofs.FrontendStages.Loop.Translate212
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody228_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody228_1 : HolLoopProg 64 :=
.mark loopBody228_0

def loopBody228_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 64#64)

def loopBody228_3 : HolLoopProg 64 :=
.mark loopBody228_2

def loopBody228_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody228_5 : HolLoopProg 64 :=
.mark loopBody228_4

def loopBody228_6 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody228_5, loopBody228_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody228_7 : HolLoopProg 64 :=
.mark loopBody228_6

def loopBody228_8 : HolLoopProg 64 :=
.seq loopBody228_7 loopBody228_1

def loopBody228_9 : HolLoopProg 64 :=
.mark loopBody228_8

def loopBody228_10 : HolLoopProg 64 :=
.seq loopBody228_3 loopBody228_9

def loopBody228_11 : HolLoopProg 64 :=
.mark loopBody228_10

def loopBody228_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 0#64])

def loopBody228_13 : HolLoopProg 64 :=
.mark loopBody228_12

def loopBody228_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody228_15 : HolLoopProg 64 :=
.mark loopBody228_14

def loopBody228_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody228_17 : HolLoopProg 64 :=
.mark loopBody228_16

def loopBody228_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody228_19 : HolLoopProg 64 :=
.mark loopBody228_18

def loopBody228_20 : HolLoopProg 64 :=
.seq loopBody228_19 loopBody228_1

def loopBody228_21 : HolLoopProg 64 :=
.mark loopBody228_20

def loopBody228_22 : HolLoopProg 64 :=
.seq loopBody228_17 loopBody228_21

def loopBody228_23 : HolLoopProg 64 :=
.mark loopBody228_22

def loopBody228_24 : HolLoopProg 64 :=
.seq loopBody228_23 loopBody228_1

def loopBody228_25 : HolLoopProg 64 :=
.mark loopBody228_24

def loopBody228_26 : HolLoopProg 64 :=
.seq loopBody228_15 loopBody228_25

def loopBody228_27 : HolLoopProg 64 :=
.mark loopBody228_26

def loopBody228_28 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_27

def loopBody228_29 : HolLoopProg 64 :=
.mark loopBody228_28

def loopBody228_30 : HolLoopProg 64 :=
.seq loopBody228_13 loopBody228_29

def loopBody228_31 : HolLoopProg 64 :=
.mark loopBody228_30

def loopBody228_32 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_31

def loopBody228_33 : HolLoopProg 64 :=
.mark loopBody228_32

def loopBody228_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 8#64])

def loopBody228_35 : HolLoopProg 64 :=
.mark loopBody228_34

def loopBody228_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody228_37 : HolLoopProg 64 :=
.mark loopBody228_36

def loopBody228_38 : HolLoopProg 64 :=
.seq loopBody228_37 loopBody228_25

def loopBody228_39 : HolLoopProg 64 :=
.mark loopBody228_38

def loopBody228_40 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_39

def loopBody228_41 : HolLoopProg 64 :=
.mark loopBody228_40

def loopBody228_42 : HolLoopProg 64 :=
.seq loopBody228_35 loopBody228_41

def loopBody228_43 : HolLoopProg 64 :=
.mark loopBody228_42

def loopBody228_44 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_43

def loopBody228_45 : HolLoopProg 64 :=
.mark loopBody228_44

def loopBody228_46 : HolLoopProg 64 :=
.seq loopBody228_33 loopBody228_45

def loopBody228_47 : HolLoopProg 64 :=
.mark loopBody228_46

def loopBody228_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 16#64])

def loopBody228_49 : HolLoopProg 64 :=
.mark loopBody228_48

def loopBody228_50 : HolLoopProg 64 :=
.seq loopBody228_49 loopBody228_41

def loopBody228_51 : HolLoopProg 64 :=
.mark loopBody228_50

def loopBody228_52 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_51

def loopBody228_53 : HolLoopProg 64 :=
.mark loopBody228_52

def loopBody228_54 : HolLoopProg 64 :=
.seq loopBody228_47 loopBody228_53

def loopBody228_55 : HolLoopProg 64 :=
.mark loopBody228_54

def loopBody228_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64])

def loopBody228_57 : HolLoopProg 64 :=
.mark loopBody228_56

def loopBody228_58 : HolLoopProg 64 :=
.seq loopBody228_57 loopBody228_41

def loopBody228_59 : HolLoopProg 64 :=
.mark loopBody228_58

def loopBody228_60 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_59

def loopBody228_61 : HolLoopProg 64 :=
.mark loopBody228_60

def loopBody228_62 : HolLoopProg 64 :=
.seq loopBody228_55 loopBody228_61

def loopBody228_63 : HolLoopProg 64 :=
.mark loopBody228_62

def loopBody228_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 32#64])

def loopBody228_65 : HolLoopProg 64 :=
.mark loopBody228_64

def loopBody228_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody228_67 : HolLoopProg 64 :=
.mark loopBody228_66

def loopBody228_68 : HolLoopProg 64 :=
.seq loopBody228_67 loopBody228_25

def loopBody228_69 : HolLoopProg 64 :=
.mark loopBody228_68

def loopBody228_70 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_69

def loopBody228_71 : HolLoopProg 64 :=
.mark loopBody228_70

def loopBody228_72 : HolLoopProg 64 :=
.seq loopBody228_65 loopBody228_71

def loopBody228_73 : HolLoopProg 64 :=
.mark loopBody228_72

def loopBody228_74 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_73

def loopBody228_75 : HolLoopProg 64 :=
.mark loopBody228_74

def loopBody228_76 : HolLoopProg 64 :=
.seq loopBody228_63 loopBody228_75

def loopBody228_77 : HolLoopProg 64 :=
.mark loopBody228_76

def loopBody228_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 40#64])

def loopBody228_79 : HolLoopProg 64 :=
.mark loopBody228_78

def loopBody228_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody228_81 : HolLoopProg 64 :=
.mark loopBody228_80

def loopBody228_82 : HolLoopProg 64 :=
.seq loopBody228_81 loopBody228_25

def loopBody228_83 : HolLoopProg 64 :=
.mark loopBody228_82

def loopBody228_84 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_83

def loopBody228_85 : HolLoopProg 64 :=
.mark loopBody228_84

def loopBody228_86 : HolLoopProg 64 :=
.seq loopBody228_79 loopBody228_85

def loopBody228_87 : HolLoopProg 64 :=
.mark loopBody228_86

def loopBody228_88 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_87

def loopBody228_89 : HolLoopProg 64 :=
.mark loopBody228_88

def loopBody228_90 : HolLoopProg 64 :=
.seq loopBody228_77 loopBody228_89

def loopBody228_91 : HolLoopProg 64 :=
.mark loopBody228_90

def loopBody228_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 48#64])

def loopBody228_93 : HolLoopProg 64 :=
.mark loopBody228_92

def loopBody228_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody228_95 : HolLoopProg 64 :=
.mark loopBody228_94

def loopBody228_96 : HolLoopProg 64 :=
.seq loopBody228_95 loopBody228_25

def loopBody228_97 : HolLoopProg 64 :=
.mark loopBody228_96

def loopBody228_98 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_97

def loopBody228_99 : HolLoopProg 64 :=
.mark loopBody228_98

def loopBody228_100 : HolLoopProg 64 :=
.seq loopBody228_93 loopBody228_99

def loopBody228_101 : HolLoopProg 64 :=
.mark loopBody228_100

def loopBody228_102 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_101

def loopBody228_103 : HolLoopProg 64 :=
.mark loopBody228_102

def loopBody228_104 : HolLoopProg 64 :=
.seq loopBody228_91 loopBody228_103

def loopBody228_105 : HolLoopProg 64 :=
.mark loopBody228_104

def loopBody228_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 56#64])

def loopBody228_107 : HolLoopProg 64 :=
.mark loopBody228_106

def loopBody228_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody228_109 : HolLoopProg 64 :=
.mark loopBody228_108

def loopBody228_110 : HolLoopProg 64 :=
.seq loopBody228_109 loopBody228_25

def loopBody228_111 : HolLoopProg 64 :=
.mark loopBody228_110

def loopBody228_112 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_111

def loopBody228_113 : HolLoopProg 64 :=
.mark loopBody228_112

def loopBody228_114 : HolLoopProg 64 :=
.seq loopBody228_107 loopBody228_113

def loopBody228_115 : HolLoopProg 64 :=
.mark loopBody228_114

def loopBody228_116 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_115

def loopBody228_117 : HolLoopProg 64 :=
.mark loopBody228_116

def loopBody228_118 : HolLoopProg 64 :=
.seq loopBody228_105 loopBody228_117

def loopBody228_119 : HolLoopProg 64 :=
.mark loopBody228_118

def loopBody228_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody228_121 : HolLoopProg 64 :=
.mark loopBody228_120

def loopBody228_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody228_123 : HolLoopProg 64 :=
.mark loopBody228_122

def loopBody228_124 : HolLoopProg 64 :=
.seq loopBody228_123 loopBody228_1

def loopBody228_125 : HolLoopProg 64 :=
.mark loopBody228_124

def loopBody228_126 : HolLoopProg 64 :=
.seq loopBody228_121 loopBody228_125

def loopBody228_127 : HolLoopProg 64 :=
.mark loopBody228_126

def loopBody228_128 : HolLoopProg 64 :=
.seq loopBody228_119 loopBody228_127

def loopBody228_129 : HolLoopProg 64 :=
.mark loopBody228_128

def loopBody228_130 : HolLoopProg 64 :=
.seq loopBody228_11 loopBody228_129

def loopBody228_131 : HolLoopProg 64 :=
.mark loopBody228_130

def loopBody228_132 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_131

def loopBody228_133 : HolLoopProg 64 :=
.mark loopBody228_132

def loopBody228_134 : HolLoopProg 64 :=
.seq loopBody228_1 loopBody228_133

def loopBody228_135 : HolLoopProg 64 :=
.mark loopBody228_134

def output228 : Nat × List Nat × HolLoopProg 64 :=
  (292, [0, 1, 2, 3], loopBody228_135)
end InitECandidate.Proofs.FrontendStages.Loop
