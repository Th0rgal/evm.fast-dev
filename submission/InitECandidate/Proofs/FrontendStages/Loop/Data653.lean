import InitECandidate.Proofs.FrontendStages.Loop.Translate637
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody653_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody653_1 : HolLoopProg 64 :=
.mark loopBody653_0

def loopBody653_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody653_3 : HolLoopProg 64 :=
.mark loopBody653_2

def loopBody653_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody653_5 : HolLoopProg 64 :=
.mark loopBody653_4

def loopBody653_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody653_7 : HolLoopProg 64 :=
.mark loopBody653_6

def loopBody653_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody653_9 : HolLoopProg 64 :=
.mark loopBody653_8

def loopBody653_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody653_11 : HolLoopProg 64 :=
.mark loopBody653_10

def loopBody653_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody653_13 : HolLoopProg 64 :=
.mark loopBody653_12

def loopBody653_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody653_15 : HolLoopProg 64 :=
.mark loopBody653_14

def loopBody653_16 : HolLoopProg 64 :=
.call (some ([6, 7, 8, 9, 10, 11], Flapjack.Spt.ln)) (some 716) ([12, 13, 14, 15, 16, 17]) (some (12, loopBody653_15, loopBody653_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))))

def loopBody653_17 : HolLoopProg 64 :=
.mark loopBody653_16

def loopBody653_18 : HolLoopProg 64 :=
.seq loopBody653_17 loopBody653_1

def loopBody653_19 : HolLoopProg 64 :=
.mark loopBody653_18

def loopBody653_20 : HolLoopProg 64 :=
.seq loopBody653_13 loopBody653_19

def loopBody653_21 : HolLoopProg 64 :=
.mark loopBody653_20

def loopBody653_22 : HolLoopProg 64 :=
.seq loopBody653_11 loopBody653_21

def loopBody653_23 : HolLoopProg 64 :=
.mark loopBody653_22

def loopBody653_24 : HolLoopProg 64 :=
.seq loopBody653_9 loopBody653_23

def loopBody653_25 : HolLoopProg 64 :=
.mark loopBody653_24

def loopBody653_26 : HolLoopProg 64 :=
.seq loopBody653_7 loopBody653_25

def loopBody653_27 : HolLoopProg 64 :=
.mark loopBody653_26

def loopBody653_28 : HolLoopProg 64 :=
.seq loopBody653_5 loopBody653_27

def loopBody653_29 : HolLoopProg 64 :=
.mark loopBody653_28

def loopBody653_30 : HolLoopProg 64 :=
.seq loopBody653_3 loopBody653_29

def loopBody653_31 : HolLoopProg 64 :=
.mark loopBody653_30

def loopBody653_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody653_33 : HolLoopProg 64 :=
.mark loopBody653_32

def loopBody653_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 7)

def loopBody653_35 : HolLoopProg 64 :=
.mark loopBody653_34

def loopBody653_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 8)

def loopBody653_37 : HolLoopProg 64 :=
.mark loopBody653_36

def loopBody653_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 9)

def loopBody653_39 : HolLoopProg 64 :=
.mark loopBody653_38

def loopBody653_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 10)

def loopBody653_41 : HolLoopProg 64 :=
.mark loopBody653_40

def loopBody653_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 11)

def loopBody653_43 : HolLoopProg 64 :=
.mark loopBody653_42

def loopBody653_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 17098105564519244256#64)

def loopBody653_45 : HolLoopProg 64 :=
.mark loopBody653_44

def loopBody653_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.const 3557706395579559416#64)

def loopBody653_47 : HolLoopProg 64 :=
.mark loopBody653_46

def loopBody653_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.const 11120290361046346205#64)

def loopBody653_49 : HolLoopProg 64 :=
.mark loopBody653_48

def loopBody653_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.const 3801124253586036577#64)

def loopBody653_51 : HolLoopProg 64 :=
.mark loopBody653_50

def loopBody653_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.const 2671430854784468776#64)

def loopBody653_53 : HolLoopProg 64 :=
.mark loopBody653_52

def loopBody653_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.const 767358375875140941#64)

def loopBody653_55 : HolLoopProg 64 :=
.mark loopBody653_54

def loopBody653_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 710) [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] none

def loopBody653_57 : HolLoopProg 64 :=
.mark loopBody653_56

def loopBody653_58 : HolLoopProg 64 :=
.seq loopBody653_57 loopBody653_1

def loopBody653_59 : HolLoopProg 64 :=
.mark loopBody653_58

def loopBody653_60 : HolLoopProg 64 :=
.seq loopBody653_55 loopBody653_59

def loopBody653_61 : HolLoopProg 64 :=
.mark loopBody653_60

def loopBody653_62 : HolLoopProg 64 :=
.seq loopBody653_53 loopBody653_61

def loopBody653_63 : HolLoopProg 64 :=
.mark loopBody653_62

def loopBody653_64 : HolLoopProg 64 :=
.seq loopBody653_51 loopBody653_63

def loopBody653_65 : HolLoopProg 64 :=
.mark loopBody653_64

def loopBody653_66 : HolLoopProg 64 :=
.seq loopBody653_49 loopBody653_65

def loopBody653_67 : HolLoopProg 64 :=
.mark loopBody653_66

def loopBody653_68 : HolLoopProg 64 :=
.seq loopBody653_47 loopBody653_67

def loopBody653_69 : HolLoopProg 64 :=
.mark loopBody653_68

def loopBody653_70 : HolLoopProg 64 :=
.seq loopBody653_45 loopBody653_69

def loopBody653_71 : HolLoopProg 64 :=
.mark loopBody653_70

def loopBody653_72 : HolLoopProg 64 :=
.seq loopBody653_43 loopBody653_71

def loopBody653_73 : HolLoopProg 64 :=
.mark loopBody653_72

def loopBody653_74 : HolLoopProg 64 :=
.seq loopBody653_41 loopBody653_73

def loopBody653_75 : HolLoopProg 64 :=
.mark loopBody653_74

def loopBody653_76 : HolLoopProg 64 :=
.seq loopBody653_39 loopBody653_75

def loopBody653_77 : HolLoopProg 64 :=
.mark loopBody653_76

def loopBody653_78 : HolLoopProg 64 :=
.seq loopBody653_37 loopBody653_77

def loopBody653_79 : HolLoopProg 64 :=
.mark loopBody653_78

def loopBody653_80 : HolLoopProg 64 :=
.seq loopBody653_35 loopBody653_79

def loopBody653_81 : HolLoopProg 64 :=
.mark loopBody653_80

def loopBody653_82 : HolLoopProg 64 :=
.seq loopBody653_33 loopBody653_81

def loopBody653_83 : HolLoopProg 64 :=
.mark loopBody653_82

def loopBody653_84 : HolLoopProg 64 :=
.seq loopBody653_31 loopBody653_83

def loopBody653_85 : HolLoopProg 64 :=
.mark loopBody653_84

def loopBody653_86 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_85

def loopBody653_87 : HolLoopProg 64 :=
.mark loopBody653_86

def loopBody653_88 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_87

def loopBody653_89 : HolLoopProg 64 :=
.mark loopBody653_88

def loopBody653_90 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_89

def loopBody653_91 : HolLoopProg 64 :=
.mark loopBody653_90

def loopBody653_92 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_91

def loopBody653_93 : HolLoopProg 64 :=
.mark loopBody653_92

def loopBody653_94 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_93

def loopBody653_95 : HolLoopProg 64 :=
.mark loopBody653_94

def loopBody653_96 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_95

def loopBody653_97 : HolLoopProg 64 :=
.mark loopBody653_96

def loopBody653_98 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_97

def loopBody653_99 : HolLoopProg 64 :=
.mark loopBody653_98

def loopBody653_100 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_99

def loopBody653_101 : HolLoopProg 64 :=
.mark loopBody653_100

def loopBody653_102 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_101

def loopBody653_103 : HolLoopProg 64 :=
.mark loopBody653_102

def loopBody653_104 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_103

def loopBody653_105 : HolLoopProg 64 :=
.mark loopBody653_104

def loopBody653_106 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_105

def loopBody653_107 : HolLoopProg 64 :=
.mark loopBody653_106

def loopBody653_108 : HolLoopProg 64 :=
.seq loopBody653_1 loopBody653_107

def loopBody653_109 : HolLoopProg 64 :=
.mark loopBody653_108

def output653 : Nat × List Nat × HolLoopProg 64 :=
  (717, [0, 1, 2, 3, 4, 5], loopBody653_109)
end InitECandidate.Proofs.FrontendStages.Loop
