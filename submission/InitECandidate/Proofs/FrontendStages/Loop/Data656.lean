import InitECandidate.Proofs.FrontendStages.Loop.Translate640
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody656_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody656_1 : HolLoopProg 64 :=
.mark loopBody656_0

def loopBody656_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody656_3 : HolLoopProg 64 :=
.mark loopBody656_2

def loopBody656_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody656_5 : HolLoopProg 64 :=
.mark loopBody656_4

def loopBody656_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody656_7 : HolLoopProg 64 :=
.mark loopBody656_6

def loopBody656_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody656_9 : HolLoopProg 64 :=
.mark loopBody656_8

def loopBody656_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody656_11 : HolLoopProg 64 :=
.mark loopBody656_10

def loopBody656_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody656_13 : HolLoopProg 64 :=
.mark loopBody656_12

def loopBody656_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody656_15 : HolLoopProg 64 :=
.mark loopBody656_14

def loopBody656_16 : HolLoopProg 64 :=
.call (some ([6, 7, 8, 9, 10, 11], Flapjack.Spt.ln)) (some 713) ([12, 13, 14, 15, 16, 17]) (some (12, loopBody656_15, loopBody656_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))))

def loopBody656_17 : HolLoopProg 64 :=
.mark loopBody656_16

def loopBody656_18 : HolLoopProg 64 :=
.seq loopBody656_17 loopBody656_1

def loopBody656_19 : HolLoopProg 64 :=
.mark loopBody656_18

def loopBody656_20 : HolLoopProg 64 :=
.seq loopBody656_13 loopBody656_19

def loopBody656_21 : HolLoopProg 64 :=
.mark loopBody656_20

def loopBody656_22 : HolLoopProg 64 :=
.seq loopBody656_11 loopBody656_21

def loopBody656_23 : HolLoopProg 64 :=
.mark loopBody656_22

def loopBody656_24 : HolLoopProg 64 :=
.seq loopBody656_9 loopBody656_23

def loopBody656_25 : HolLoopProg 64 :=
.mark loopBody656_24

def loopBody656_26 : HolLoopProg 64 :=
.seq loopBody656_7 loopBody656_25

def loopBody656_27 : HolLoopProg 64 :=
.mark loopBody656_26

def loopBody656_28 : HolLoopProg 64 :=
.seq loopBody656_5 loopBody656_27

def loopBody656_29 : HolLoopProg 64 :=
.mark loopBody656_28

def loopBody656_30 : HolLoopProg 64 :=
.seq loopBody656_3 loopBody656_29

def loopBody656_31 : HolLoopProg 64 :=
.mark loopBody656_30

def loopBody656_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 15924587544893707605#64)

def loopBody656_33 : HolLoopProg 64 :=
.mark loopBody656_32

def loopBody656_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1105070755758604287#64)

def loopBody656_35 : HolLoopProg 64 :=
.mark loopBody656_34

def loopBody656_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 12941209323636816658#64)

def loopBody656_37 : HolLoopProg 64 :=
.mark loopBody656_36

def loopBody656_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 12843041017062132063#64)

def loopBody656_39 : HolLoopProg 64 :=
.mark loopBody656_38

def loopBody656_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 2706051889235351147#64)

def loopBody656_41 : HolLoopProg 64 :=
.mark loopBody656_40

def loopBody656_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 936899308823769933#64)

def loopBody656_43 : HolLoopProg 64 :=
.mark loopBody656_42

def loopBody656_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 6)

def loopBody656_45 : HolLoopProg 64 :=
.mark loopBody656_44

def loopBody656_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 7)

def loopBody656_47 : HolLoopProg 64 :=
.mark loopBody656_46

def loopBody656_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 8)

def loopBody656_49 : HolLoopProg 64 :=
.mark loopBody656_48

def loopBody656_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 9)

def loopBody656_51 : HolLoopProg 64 :=
.mark loopBody656_50

def loopBody656_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.var 10)

def loopBody656_53 : HolLoopProg 64 :=
.mark loopBody656_52

def loopBody656_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 11)

def loopBody656_55 : HolLoopProg 64 :=
.mark loopBody656_54

def loopBody656_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody656_57 : HolLoopProg 64 :=
.mark loopBody656_56

def loopBody656_58 : HolLoopProg 64 :=
.call (some ([12], Flapjack.Spt.ln)) (some 703) ([13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]) (some (13, loopBody656_57, loopBody656_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  Flapjack.Spt.ln)))

def loopBody656_59 : HolLoopProg 64 :=
.mark loopBody656_58

def loopBody656_60 : HolLoopProg 64 :=
.seq loopBody656_59 loopBody656_1

def loopBody656_61 : HolLoopProg 64 :=
.mark loopBody656_60

def loopBody656_62 : HolLoopProg 64 :=
.seq loopBody656_55 loopBody656_61

def loopBody656_63 : HolLoopProg 64 :=
.mark loopBody656_62

def loopBody656_64 : HolLoopProg 64 :=
.seq loopBody656_53 loopBody656_63

def loopBody656_65 : HolLoopProg 64 :=
.mark loopBody656_64

def loopBody656_66 : HolLoopProg 64 :=
.seq loopBody656_51 loopBody656_65

def loopBody656_67 : HolLoopProg 64 :=
.mark loopBody656_66

def loopBody656_68 : HolLoopProg 64 :=
.seq loopBody656_49 loopBody656_67

def loopBody656_69 : HolLoopProg 64 :=
.mark loopBody656_68

def loopBody656_70 : HolLoopProg 64 :=
.seq loopBody656_47 loopBody656_69

def loopBody656_71 : HolLoopProg 64 :=
.mark loopBody656_70

def loopBody656_72 : HolLoopProg 64 :=
.seq loopBody656_45 loopBody656_71

def loopBody656_73 : HolLoopProg 64 :=
.mark loopBody656_72

def loopBody656_74 : HolLoopProg 64 :=
.seq loopBody656_43 loopBody656_73

def loopBody656_75 : HolLoopProg 64 :=
.mark loopBody656_74

def loopBody656_76 : HolLoopProg 64 :=
.seq loopBody656_41 loopBody656_75

def loopBody656_77 : HolLoopProg 64 :=
.mark loopBody656_76

def loopBody656_78 : HolLoopProg 64 :=
.seq loopBody656_39 loopBody656_77

def loopBody656_79 : HolLoopProg 64 :=
.mark loopBody656_78

def loopBody656_80 : HolLoopProg 64 :=
.seq loopBody656_37 loopBody656_79

def loopBody656_81 : HolLoopProg 64 :=
.mark loopBody656_80

def loopBody656_82 : HolLoopProg 64 :=
.seq loopBody656_35 loopBody656_81

def loopBody656_83 : HolLoopProg 64 :=
.mark loopBody656_82

def loopBody656_84 : HolLoopProg 64 :=
.seq loopBody656_33 loopBody656_83

def loopBody656_85 : HolLoopProg 64 :=
.mark loopBody656_84

def loopBody656_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 12)

def loopBody656_87 : HolLoopProg 64 :=
.mark loopBody656_86

def loopBody656_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13]

def loopBody656_89 : HolLoopProg 64 :=
.mark loopBody656_88

def loopBody656_90 : HolLoopProg 64 :=
.seq loopBody656_89 loopBody656_1

def loopBody656_91 : HolLoopProg 64 :=
.mark loopBody656_90

def loopBody656_92 : HolLoopProg 64 :=
.seq loopBody656_87 loopBody656_91

def loopBody656_93 : HolLoopProg 64 :=
.mark loopBody656_92

def loopBody656_94 : HolLoopProg 64 :=
.seq loopBody656_85 loopBody656_93

def loopBody656_95 : HolLoopProg 64 :=
.mark loopBody656_94

def loopBody656_96 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_95

def loopBody656_97 : HolLoopProg 64 :=
.mark loopBody656_96

def loopBody656_98 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_97

def loopBody656_99 : HolLoopProg 64 :=
.mark loopBody656_98

def loopBody656_100 : HolLoopProg 64 :=
.seq loopBody656_31 loopBody656_99

def loopBody656_101 : HolLoopProg 64 :=
.mark loopBody656_100

def loopBody656_102 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_101

def loopBody656_103 : HolLoopProg 64 :=
.mark loopBody656_102

def loopBody656_104 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_103

def loopBody656_105 : HolLoopProg 64 :=
.mark loopBody656_104

def loopBody656_106 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_105

def loopBody656_107 : HolLoopProg 64 :=
.mark loopBody656_106

def loopBody656_108 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_107

def loopBody656_109 : HolLoopProg 64 :=
.mark loopBody656_108

def loopBody656_110 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_109

def loopBody656_111 : HolLoopProg 64 :=
.mark loopBody656_110

def loopBody656_112 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_111

def loopBody656_113 : HolLoopProg 64 :=
.mark loopBody656_112

def loopBody656_114 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_113

def loopBody656_115 : HolLoopProg 64 :=
.mark loopBody656_114

def loopBody656_116 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_115

def loopBody656_117 : HolLoopProg 64 :=
.mark loopBody656_116

def loopBody656_118 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_117

def loopBody656_119 : HolLoopProg 64 :=
.mark loopBody656_118

def loopBody656_120 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_119

def loopBody656_121 : HolLoopProg 64 :=
.mark loopBody656_120

def loopBody656_122 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_121

def loopBody656_123 : HolLoopProg 64 :=
.mark loopBody656_122

def loopBody656_124 : HolLoopProg 64 :=
.seq loopBody656_1 loopBody656_123

def loopBody656_125 : HolLoopProg 64 :=
.mark loopBody656_124

def output656 : Nat × List Nat × HolLoopProg 64 :=
  (720, [0, 1, 2, 3, 4, 5], loopBody656_125)
end InitECandidate.Proofs.FrontendStages.Loop
