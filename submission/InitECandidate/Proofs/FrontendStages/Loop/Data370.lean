import InitECandidate.Proofs.FrontendStages.Loop.Translate354
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody370_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody370_1 : HolLoopProg 64 :=
.mark loopBody370_0

def loopBody370_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 20#64)

def loopBody370_3 : HolLoopProg 64 :=
.mark loopBody370_2

def loopBody370_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 64#64)

def loopBody370_5 : HolLoopProg 64 :=
.mark loopBody370_4

def loopBody370_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody370_7 : HolLoopProg 64 :=
.mark loopBody370_6

def loopBody370_8 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 182) ([2, 3]) (some (2, loopBody370_7, loopBody370_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody370_9 : HolLoopProg 64 :=
.mark loopBody370_8

def loopBody370_10 : HolLoopProg 64 :=
.seq loopBody370_9 loopBody370_1

def loopBody370_11 : HolLoopProg 64 :=
.mark loopBody370_10

def loopBody370_12 : HolLoopProg 64 :=
.seq loopBody370_5 loopBody370_11

def loopBody370_13 : HolLoopProg 64 :=
.mark loopBody370_12

def loopBody370_14 : HolLoopProg 64 :=
.seq loopBody370_3 loopBody370_13

def loopBody370_15 : HolLoopProg 64 :=
.mark loopBody370_14

def loopBody370_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 216#64])

def loopBody370_17 : HolLoopProg 64 :=
.mark loopBody370_16

def loopBody370_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody370_19 : HolLoopProg 64 :=
.mark loopBody370_18

def loopBody370_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody370_21 : HolLoopProg 64 :=
.mark loopBody370_20

def loopBody370_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody370_23 : HolLoopProg 64 :=
.mark loopBody370_22

def loopBody370_24 : HolLoopProg 64 :=
.seq loopBody370_23 loopBody370_1

def loopBody370_25 : HolLoopProg 64 :=
.mark loopBody370_24

def loopBody370_26 : HolLoopProg 64 :=
.seq loopBody370_21 loopBody370_25

def loopBody370_27 : HolLoopProg 64 :=
.mark loopBody370_26

def loopBody370_28 : HolLoopProg 64 :=
.seq loopBody370_27 loopBody370_1

def loopBody370_29 : HolLoopProg 64 :=
.mark loopBody370_28

def loopBody370_30 : HolLoopProg 64 :=
.seq loopBody370_19 loopBody370_29

def loopBody370_31 : HolLoopProg 64 :=
.mark loopBody370_30

def loopBody370_32 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_31

def loopBody370_33 : HolLoopProg 64 :=
.mark loopBody370_32

def loopBody370_34 : HolLoopProg 64 :=
.seq loopBody370_17 loopBody370_33

def loopBody370_35 : HolLoopProg 64 :=
.mark loopBody370_34

def loopBody370_36 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_35

def loopBody370_37 : HolLoopProg 64 :=
.mark loopBody370_36

def loopBody370_38 : HolLoopProg 64 :=
.seq loopBody370_15 loopBody370_37

def loopBody370_39 : HolLoopProg 64 :=
.mark loopBody370_38

def loopBody370_40 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_39

def loopBody370_41 : HolLoopProg 64 :=
.mark loopBody370_40

def loopBody370_42 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_41

def loopBody370_43 : HolLoopProg 64 :=
.mark loopBody370_42

def loopBody370_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 28#64)

def loopBody370_45 : HolLoopProg 64 :=
.mark loopBody370_44

def loopBody370_46 : HolLoopProg 64 :=
.seq loopBody370_45 loopBody370_13

def loopBody370_47 : HolLoopProg 64 :=
.mark loopBody370_46

def loopBody370_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 232#64])

def loopBody370_49 : HolLoopProg 64 :=
.mark loopBody370_48

def loopBody370_50 : HolLoopProg 64 :=
.seq loopBody370_49 loopBody370_33

def loopBody370_51 : HolLoopProg 64 :=
.mark loopBody370_50

def loopBody370_52 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_51

def loopBody370_53 : HolLoopProg 64 :=
.mark loopBody370_52

def loopBody370_54 : HolLoopProg 64 :=
.seq loopBody370_47 loopBody370_53

def loopBody370_55 : HolLoopProg 64 :=
.mark loopBody370_54

def loopBody370_56 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_55

def loopBody370_57 : HolLoopProg 64 :=
.mark loopBody370_56

def loopBody370_58 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_57

def loopBody370_59 : HolLoopProg 64 :=
.mark loopBody370_58

def loopBody370_60 : HolLoopProg 64 :=
.seq loopBody370_43 loopBody370_59

def loopBody370_61 : HolLoopProg 64 :=
.mark loopBody370_60

def loopBody370_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 60#64)

def loopBody370_63 : HolLoopProg 64 :=
.mark loopBody370_62

def loopBody370_64 : HolLoopProg 64 :=
.seq loopBody370_63 loopBody370_13

def loopBody370_65 : HolLoopProg 64 :=
.mark loopBody370_64

def loopBody370_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 240#64])

def loopBody370_67 : HolLoopProg 64 :=
.mark loopBody370_66

def loopBody370_68 : HolLoopProg 64 :=
.seq loopBody370_67 loopBody370_33

def loopBody370_69 : HolLoopProg 64 :=
.mark loopBody370_68

def loopBody370_70 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_69

def loopBody370_71 : HolLoopProg 64 :=
.mark loopBody370_70

def loopBody370_72 : HolLoopProg 64 :=
.seq loopBody370_65 loopBody370_71

def loopBody370_73 : HolLoopProg 64 :=
.mark loopBody370_72

def loopBody370_74 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_73

def loopBody370_75 : HolLoopProg 64 :=
.mark loopBody370_74

def loopBody370_76 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_75

def loopBody370_77 : HolLoopProg 64 :=
.mark loopBody370_76

def loopBody370_78 : HolLoopProg 64 :=
.seq loopBody370_61 loopBody370_77

def loopBody370_79 : HolLoopProg 64 :=
.mark loopBody370_78

def loopBody370_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 64#64)

def loopBody370_81 : HolLoopProg 64 :=
.mark loopBody370_80

def loopBody370_82 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 68) ([2]) (some (2, loopBody370_7, loopBody370_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody370_83 : HolLoopProg 64 :=
.mark loopBody370_82

def loopBody370_84 : HolLoopProg 64 :=
.seq loopBody370_83 loopBody370_1

def loopBody370_85 : HolLoopProg 64 :=
.mark loopBody370_84

def loopBody370_86 : HolLoopProg 64 :=
.seq loopBody370_81 loopBody370_85

def loopBody370_87 : HolLoopProg 64 :=
.mark loopBody370_86

def loopBody370_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 248#64])

def loopBody370_89 : HolLoopProg 64 :=
.mark loopBody370_88

def loopBody370_90 : HolLoopProg 64 :=
.seq loopBody370_89 loopBody370_33

def loopBody370_91 : HolLoopProg 64 :=
.mark loopBody370_90

def loopBody370_92 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_91

def loopBody370_93 : HolLoopProg 64 :=
.mark loopBody370_92

def loopBody370_94 : HolLoopProg 64 :=
.seq loopBody370_87 loopBody370_93

def loopBody370_95 : HolLoopProg 64 :=
.mark loopBody370_94

def loopBody370_96 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_95

def loopBody370_97 : HolLoopProg 64 :=
.mark loopBody370_96

def loopBody370_98 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_97

def loopBody370_99 : HolLoopProg 64 :=
.mark loopBody370_98

def loopBody370_100 : HolLoopProg 64 :=
.seq loopBody370_79 loopBody370_99

def loopBody370_101 : HolLoopProg 64 :=
.mark loopBody370_100

def loopBody370_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 224#64])

def loopBody370_103 : HolLoopProg 64 :=
.mark loopBody370_102

def loopBody370_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody370_105 : HolLoopProg 64 :=
.mark loopBody370_104

def loopBody370_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody370_107 : HolLoopProg 64 :=
.mark loopBody370_106

def loopBody370_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody370_109 : HolLoopProg 64 :=
.mark loopBody370_108

def loopBody370_110 : HolLoopProg 64 :=
.seq loopBody370_109 loopBody370_1

def loopBody370_111 : HolLoopProg 64 :=
.mark loopBody370_110

def loopBody370_112 : HolLoopProg 64 :=
.seq loopBody370_107 loopBody370_111

def loopBody370_113 : HolLoopProg 64 :=
.mark loopBody370_112

def loopBody370_114 : HolLoopProg 64 :=
.seq loopBody370_113 loopBody370_1

def loopBody370_115 : HolLoopProg 64 :=
.mark loopBody370_114

def loopBody370_116 : HolLoopProg 64 :=
.seq loopBody370_105 loopBody370_115

def loopBody370_117 : HolLoopProg 64 :=
.mark loopBody370_116

def loopBody370_118 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_117

def loopBody370_119 : HolLoopProg 64 :=
.mark loopBody370_118

def loopBody370_120 : HolLoopProg 64 :=
.seq loopBody370_103 loopBody370_119

def loopBody370_121 : HolLoopProg 64 :=
.mark loopBody370_120

def loopBody370_122 : HolLoopProg 64 :=
.seq loopBody370_1 loopBody370_121

def loopBody370_123 : HolLoopProg 64 :=
.mark loopBody370_122

def loopBody370_124 : HolLoopProg 64 :=
.seq loopBody370_101 loopBody370_123

def loopBody370_125 : HolLoopProg 64 :=
.mark loopBody370_124

def loopBody370_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody370_127 : HolLoopProg 64 :=
.mark loopBody370_126

def loopBody370_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody370_129 : HolLoopProg 64 :=
.mark loopBody370_128

def loopBody370_130 : HolLoopProg 64 :=
.seq loopBody370_129 loopBody370_1

def loopBody370_131 : HolLoopProg 64 :=
.mark loopBody370_130

def loopBody370_132 : HolLoopProg 64 :=
.seq loopBody370_127 loopBody370_131

def loopBody370_133 : HolLoopProg 64 :=
.mark loopBody370_132

def loopBody370_134 : HolLoopProg 64 :=
.seq loopBody370_125 loopBody370_133

def loopBody370_135 : HolLoopProg 64 :=
.mark loopBody370_134

def output370 : Nat × List Nat × HolLoopProg 64 :=
  (434, [], loopBody370_135)
end InitECandidate.Proofs.FrontendStages.Loop
