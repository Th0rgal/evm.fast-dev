import InitECandidate.Proofs.FrontendStages.Loop.Translate213
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody229_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody229_1 : HolLoopProg 64 :=
.mark loopBody229_0

def loopBody229_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 56#64)

def loopBody229_3 : HolLoopProg 64 :=
.mark loopBody229_2

def loopBody229_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody229_5 : HolLoopProg 64 :=
.mark loopBody229_4

def loopBody229_6 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody229_5, loopBody229_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody229_7 : HolLoopProg 64 :=
.mark loopBody229_6

def loopBody229_8 : HolLoopProg 64 :=
.seq loopBody229_7 loopBody229_1

def loopBody229_9 : HolLoopProg 64 :=
.mark loopBody229_8

def loopBody229_10 : HolLoopProg 64 :=
.seq loopBody229_3 loopBody229_9

def loopBody229_11 : HolLoopProg 64 :=
.mark loopBody229_10

def loopBody229_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 0#64])

def loopBody229_13 : HolLoopProg 64 :=
.mark loopBody229_12

def loopBody229_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 2#64)

def loopBody229_15 : HolLoopProg 64 :=
.mark loopBody229_14

def loopBody229_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody229_17 : HolLoopProg 64 :=
.mark loopBody229_16

def loopBody229_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody229_19 : HolLoopProg 64 :=
.mark loopBody229_18

def loopBody229_20 : HolLoopProg 64 :=
.seq loopBody229_19 loopBody229_1

def loopBody229_21 : HolLoopProg 64 :=
.mark loopBody229_20

def loopBody229_22 : HolLoopProg 64 :=
.seq loopBody229_17 loopBody229_21

def loopBody229_23 : HolLoopProg 64 :=
.mark loopBody229_22

def loopBody229_24 : HolLoopProg 64 :=
.seq loopBody229_23 loopBody229_1

def loopBody229_25 : HolLoopProg 64 :=
.mark loopBody229_24

def loopBody229_26 : HolLoopProg 64 :=
.seq loopBody229_15 loopBody229_25

def loopBody229_27 : HolLoopProg 64 :=
.mark loopBody229_26

def loopBody229_28 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_27

def loopBody229_29 : HolLoopProg 64 :=
.mark loopBody229_28

def loopBody229_30 : HolLoopProg 64 :=
.seq loopBody229_13 loopBody229_29

def loopBody229_31 : HolLoopProg 64 :=
.mark loopBody229_30

def loopBody229_32 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_31

def loopBody229_33 : HolLoopProg 64 :=
.mark loopBody229_32

def loopBody229_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 8#64])

def loopBody229_35 : HolLoopProg 64 :=
.mark loopBody229_34

def loopBody229_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody229_37 : HolLoopProg 64 :=
.mark loopBody229_36

def loopBody229_38 : HolLoopProg 64 :=
.seq loopBody229_37 loopBody229_25

def loopBody229_39 : HolLoopProg 64 :=
.mark loopBody229_38

def loopBody229_40 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_39

def loopBody229_41 : HolLoopProg 64 :=
.mark loopBody229_40

def loopBody229_42 : HolLoopProg 64 :=
.seq loopBody229_35 loopBody229_41

def loopBody229_43 : HolLoopProg 64 :=
.mark loopBody229_42

def loopBody229_44 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_43

def loopBody229_45 : HolLoopProg 64 :=
.mark loopBody229_44

def loopBody229_46 : HolLoopProg 64 :=
.seq loopBody229_33 loopBody229_45

def loopBody229_47 : HolLoopProg 64 :=
.mark loopBody229_46

def loopBody229_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 16#64])

def loopBody229_49 : HolLoopProg 64 :=
.mark loopBody229_48

def loopBody229_50 : HolLoopProg 64 :=
.seq loopBody229_49 loopBody229_41

def loopBody229_51 : HolLoopProg 64 :=
.mark loopBody229_50

def loopBody229_52 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_51

def loopBody229_53 : HolLoopProg 64 :=
.mark loopBody229_52

def loopBody229_54 : HolLoopProg 64 :=
.seq loopBody229_47 loopBody229_53

def loopBody229_55 : HolLoopProg 64 :=
.mark loopBody229_54

def loopBody229_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 24#64])

def loopBody229_57 : HolLoopProg 64 :=
.mark loopBody229_56

def loopBody229_58 : HolLoopProg 64 :=
.seq loopBody229_57 loopBody229_41

def loopBody229_59 : HolLoopProg 64 :=
.mark loopBody229_58

def loopBody229_60 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_59

def loopBody229_61 : HolLoopProg 64 :=
.mark loopBody229_60

def loopBody229_62 : HolLoopProg 64 :=
.seq loopBody229_55 loopBody229_61

def loopBody229_63 : HolLoopProg 64 :=
.mark loopBody229_62

def loopBody229_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 32#64])

def loopBody229_65 : HolLoopProg 64 :=
.mark loopBody229_64

def loopBody229_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody229_67 : HolLoopProg 64 :=
.mark loopBody229_66

def loopBody229_68 : HolLoopProg 64 :=
.seq loopBody229_67 loopBody229_25

def loopBody229_69 : HolLoopProg 64 :=
.mark loopBody229_68

def loopBody229_70 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_69

def loopBody229_71 : HolLoopProg 64 :=
.mark loopBody229_70

def loopBody229_72 : HolLoopProg 64 :=
.seq loopBody229_65 loopBody229_71

def loopBody229_73 : HolLoopProg 64 :=
.mark loopBody229_72

def loopBody229_74 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_73

def loopBody229_75 : HolLoopProg 64 :=
.mark loopBody229_74

def loopBody229_76 : HolLoopProg 64 :=
.seq loopBody229_63 loopBody229_75

def loopBody229_77 : HolLoopProg 64 :=
.mark loopBody229_76

def loopBody229_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 40#64])

def loopBody229_79 : HolLoopProg 64 :=
.mark loopBody229_78

def loopBody229_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody229_81 : HolLoopProg 64 :=
.mark loopBody229_80

def loopBody229_82 : HolLoopProg 64 :=
.seq loopBody229_81 loopBody229_25

def loopBody229_83 : HolLoopProg 64 :=
.mark loopBody229_82

def loopBody229_84 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_83

def loopBody229_85 : HolLoopProg 64 :=
.mark loopBody229_84

def loopBody229_86 : HolLoopProg 64 :=
.seq loopBody229_79 loopBody229_85

def loopBody229_87 : HolLoopProg 64 :=
.mark loopBody229_86

def loopBody229_88 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_87

def loopBody229_89 : HolLoopProg 64 :=
.mark loopBody229_88

def loopBody229_90 : HolLoopProg 64 :=
.seq loopBody229_77 loopBody229_89

def loopBody229_91 : HolLoopProg 64 :=
.mark loopBody229_90

def loopBody229_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 48#64])

def loopBody229_93 : HolLoopProg 64 :=
.mark loopBody229_92

def loopBody229_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody229_95 : HolLoopProg 64 :=
.mark loopBody229_94

def loopBody229_96 : HolLoopProg 64 :=
.seq loopBody229_95 loopBody229_25

def loopBody229_97 : HolLoopProg 64 :=
.mark loopBody229_96

def loopBody229_98 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_97

def loopBody229_99 : HolLoopProg 64 :=
.mark loopBody229_98

def loopBody229_100 : HolLoopProg 64 :=
.seq loopBody229_93 loopBody229_99

def loopBody229_101 : HolLoopProg 64 :=
.mark loopBody229_100

def loopBody229_102 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_101

def loopBody229_103 : HolLoopProg 64 :=
.mark loopBody229_102

def loopBody229_104 : HolLoopProg 64 :=
.seq loopBody229_91 loopBody229_103

def loopBody229_105 : HolLoopProg 64 :=
.mark loopBody229_104

def loopBody229_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody229_107 : HolLoopProg 64 :=
.mark loopBody229_106

def loopBody229_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody229_109 : HolLoopProg 64 :=
.mark loopBody229_108

def loopBody229_110 : HolLoopProg 64 :=
.seq loopBody229_109 loopBody229_1

def loopBody229_111 : HolLoopProg 64 :=
.mark loopBody229_110

def loopBody229_112 : HolLoopProg 64 :=
.seq loopBody229_107 loopBody229_111

def loopBody229_113 : HolLoopProg 64 :=
.mark loopBody229_112

def loopBody229_114 : HolLoopProg 64 :=
.seq loopBody229_105 loopBody229_113

def loopBody229_115 : HolLoopProg 64 :=
.mark loopBody229_114

def loopBody229_116 : HolLoopProg 64 :=
.seq loopBody229_11 loopBody229_115

def loopBody229_117 : HolLoopProg 64 :=
.mark loopBody229_116

def loopBody229_118 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_117

def loopBody229_119 : HolLoopProg 64 :=
.mark loopBody229_118

def loopBody229_120 : HolLoopProg 64 :=
.seq loopBody229_1 loopBody229_119

def loopBody229_121 : HolLoopProg 64 :=
.mark loopBody229_120

def output229 : Nat × List Nat × HolLoopProg 64 :=
  (293, [0, 1, 2], loopBody229_121)
end InitECandidate.Proofs.FrontendStages.Loop
