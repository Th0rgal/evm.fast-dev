import InitECandidate.Proofs.FrontendStages.Loop.Translate773
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody789_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody789_1 : HolLoopProg 64 :=
.mark loopBody789_0

def loopBody789_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 0)

def loopBody789_3 : HolLoopProg 64 :=
.mark loopBody789_2

def loopBody789_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody789_5 : HolLoopProg 64 :=
.mark loopBody789_4

def loopBody789_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody789_7 : HolLoopProg 64 :=
.mark loopBody789_6

def loopBody789_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody789_9 : HolLoopProg 64 :=
.mark loopBody789_8

def loopBody789_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 1)

def loopBody789_11 : HolLoopProg 64 :=
.mark loopBody789_10

def loopBody789_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 2)

def loopBody789_13 : HolLoopProg 64 :=
.mark loopBody789_12

def loopBody789_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 3)

def loopBody789_15 : HolLoopProg 64 :=
.mark loopBody789_14

def loopBody789_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 4)

def loopBody789_17 : HolLoopProg 64 :=
.mark loopBody789_16

def loopBody789_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody789_19 : HolLoopProg 64 :=
.mark loopBody789_18

def loopBody789_20 : HolLoopProg 64 :=
.call (some ([5, 6, 7, 8, 9, 10, 11, 12], Flapjack.Spt.ln)) (some 121) ([13, 14, 15, 16, 17, 18, 19, 20]) (some (13, loopBody789_19, loopBody789_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))))

def loopBody789_21 : HolLoopProg 64 :=
.mark loopBody789_20

def loopBody789_22 : HolLoopProg 64 :=
.seq loopBody789_21 loopBody789_1

def loopBody789_23 : HolLoopProg 64 :=
.mark loopBody789_22

def loopBody789_24 : HolLoopProg 64 :=
.seq loopBody789_17 loopBody789_23

def loopBody789_25 : HolLoopProg 64 :=
.mark loopBody789_24

def loopBody789_26 : HolLoopProg 64 :=
.seq loopBody789_15 loopBody789_25

def loopBody789_27 : HolLoopProg 64 :=
.mark loopBody789_26

def loopBody789_28 : HolLoopProg 64 :=
.seq loopBody789_13 loopBody789_27

def loopBody789_29 : HolLoopProg 64 :=
.mark loopBody789_28

def loopBody789_30 : HolLoopProg 64 :=
.seq loopBody789_11 loopBody789_29

def loopBody789_31 : HolLoopProg 64 :=
.mark loopBody789_30

def loopBody789_32 : HolLoopProg 64 :=
.seq loopBody789_9 loopBody789_31

def loopBody789_33 : HolLoopProg 64 :=
.mark loopBody789_32

def loopBody789_34 : HolLoopProg 64 :=
.seq loopBody789_7 loopBody789_33

def loopBody789_35 : HolLoopProg 64 :=
.mark loopBody789_34

def loopBody789_36 : HolLoopProg 64 :=
.seq loopBody789_5 loopBody789_35

def loopBody789_37 : HolLoopProg 64 :=
.mark loopBody789_36

def loopBody789_38 : HolLoopProg 64 :=
.seq loopBody789_3 loopBody789_37

def loopBody789_39 : HolLoopProg 64 :=
.mark loopBody789_38

def loopBody789_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody789_41 : HolLoopProg 64 :=
.mark loopBody789_40

def loopBody789_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.var 12])

def loopBody789_43 : HolLoopProg 64 :=
.mark loopBody789_42

def loopBody789_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody789_45 : HolLoopProg 64 :=
.mark loopBody789_44

def loopBody789_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.reg 16) loopBody789_45 loopBody789_7 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody789_47 : HolLoopProg 64 :=
.mark loopBody789_46

def loopBody789_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 15)

def loopBody789_49 : HolLoopProg 64 :=
.mark loopBody789_48

def loopBody789_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody789_51 : HolLoopProg 64 :=
.mark loopBody789_50

def loopBody789_52 : HolLoopProg 64 :=
.seq loopBody789_51 loopBody789_1

def loopBody789_53 : HolLoopProg 64 :=
.mark loopBody789_52

def loopBody789_54 : HolLoopProg 64 :=
.seq loopBody789_53 loopBody789_1

def loopBody789_55 : HolLoopProg 64 :=
.mark loopBody789_54

def loopBody789_56 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 17 (Flapjack.RegImm.imm 0#64) loopBody789_55 loopBody789_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody789_57 : HolLoopProg 64 :=
.mark loopBody789_56

def loopBody789_58 : HolLoopProg 64 :=
.seq loopBody789_57 loopBody789_1

def loopBody789_59 : HolLoopProg 64 :=
.mark loopBody789_58

def loopBody789_60 : HolLoopProg 64 :=
.seq loopBody789_49 loopBody789_59

def loopBody789_61 : HolLoopProg 64 :=
.mark loopBody789_60

def loopBody789_62 : HolLoopProg 64 :=
.seq loopBody789_47 loopBody789_61

def loopBody789_63 : HolLoopProg 64 :=
.mark loopBody789_62

def loopBody789_64 : HolLoopProg 64 :=
.seq loopBody789_9 loopBody789_63

def loopBody789_65 : HolLoopProg 64 :=
.mark loopBody789_64

def loopBody789_66 : HolLoopProg 64 :=
.seq loopBody789_43 loopBody789_65

def loopBody789_67 : HolLoopProg 64 :=
.mark loopBody789_66

def loopBody789_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 13)

def loopBody789_69 : HolLoopProg 64 :=
.mark loopBody789_68

def loopBody789_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 5)

def loopBody789_71 : HolLoopProg 64 :=
.mark loopBody789_70

def loopBody789_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 6)

def loopBody789_73 : HolLoopProg 64 :=
.mark loopBody789_72

def loopBody789_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 7)

def loopBody789_75 : HolLoopProg 64 :=
.mark loopBody789_74

def loopBody789_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 8)

def loopBody789_77 : HolLoopProg 64 :=
.mark loopBody789_76

def loopBody789_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14, 15, 16, 17, 18]

def loopBody789_79 : HolLoopProg 64 :=
.mark loopBody789_78

def loopBody789_80 : HolLoopProg 64 :=
.seq loopBody789_79 loopBody789_1

def loopBody789_81 : HolLoopProg 64 :=
.mark loopBody789_80

def loopBody789_82 : HolLoopProg 64 :=
.seq loopBody789_77 loopBody789_81

def loopBody789_83 : HolLoopProg 64 :=
.mark loopBody789_82

def loopBody789_84 : HolLoopProg 64 :=
.seq loopBody789_75 loopBody789_83

def loopBody789_85 : HolLoopProg 64 :=
.mark loopBody789_84

def loopBody789_86 : HolLoopProg 64 :=
.seq loopBody789_73 loopBody789_85

def loopBody789_87 : HolLoopProg 64 :=
.mark loopBody789_86

def loopBody789_88 : HolLoopProg 64 :=
.seq loopBody789_71 loopBody789_87

def loopBody789_89 : HolLoopProg 64 :=
.mark loopBody789_88

def loopBody789_90 : HolLoopProg 64 :=
.seq loopBody789_69 loopBody789_89

def loopBody789_91 : HolLoopProg 64 :=
.mark loopBody789_90

def loopBody789_92 : HolLoopProg 64 :=
.seq loopBody789_67 loopBody789_91

def loopBody789_93 : HolLoopProg 64 :=
.mark loopBody789_92

def loopBody789_94 : HolLoopProg 64 :=
.seq loopBody789_41 loopBody789_93

def loopBody789_95 : HolLoopProg 64 :=
.mark loopBody789_94

def loopBody789_96 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_95

def loopBody789_97 : HolLoopProg 64 :=
.mark loopBody789_96

def loopBody789_98 : HolLoopProg 64 :=
.seq loopBody789_39 loopBody789_97

def loopBody789_99 : HolLoopProg 64 :=
.mark loopBody789_98

def loopBody789_100 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_99

def loopBody789_101 : HolLoopProg 64 :=
.mark loopBody789_100

def loopBody789_102 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_101

def loopBody789_103 : HolLoopProg 64 :=
.mark loopBody789_102

def loopBody789_104 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_103

def loopBody789_105 : HolLoopProg 64 :=
.mark loopBody789_104

def loopBody789_106 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_105

def loopBody789_107 : HolLoopProg 64 :=
.mark loopBody789_106

def loopBody789_108 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_107

def loopBody789_109 : HolLoopProg 64 :=
.mark loopBody789_108

def loopBody789_110 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_109

def loopBody789_111 : HolLoopProg 64 :=
.mark loopBody789_110

def loopBody789_112 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_111

def loopBody789_113 : HolLoopProg 64 :=
.mark loopBody789_112

def loopBody789_114 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_113

def loopBody789_115 : HolLoopProg 64 :=
.mark loopBody789_114

def loopBody789_116 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_115

def loopBody789_117 : HolLoopProg 64 :=
.mark loopBody789_116

def loopBody789_118 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_117

def loopBody789_119 : HolLoopProg 64 :=
.mark loopBody789_118

def loopBody789_120 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_119

def loopBody789_121 : HolLoopProg 64 :=
.mark loopBody789_120

def loopBody789_122 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_121

def loopBody789_123 : HolLoopProg 64 :=
.mark loopBody789_122

def loopBody789_124 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_123

def loopBody789_125 : HolLoopProg 64 :=
.mark loopBody789_124

def loopBody789_126 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_125

def loopBody789_127 : HolLoopProg 64 :=
.mark loopBody789_126

def loopBody789_128 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_127

def loopBody789_129 : HolLoopProg 64 :=
.mark loopBody789_128

def loopBody789_130 : HolLoopProg 64 :=
.seq loopBody789_1 loopBody789_129

def loopBody789_131 : HolLoopProg 64 :=
.mark loopBody789_130

def output789 : Nat × List Nat × HolLoopProg 64 :=
  (853, [0, 1, 2, 3, 4], loopBody789_131)
end InitECandidate.Proofs.FrontendStages.Loop
