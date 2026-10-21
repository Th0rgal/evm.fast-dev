import InitECandidate.Proofs.FrontendStages.Loop.Translate576
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody592_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody592_1 : HolLoopProg 64 :=
.mark loopBody592_0

def loopBody592_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody592_3 : HolLoopProg 64 :=
.mark loopBody592_2

def loopBody592_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody592_5 : HolLoopProg 64 :=
.mark loopBody592_4

def loopBody592_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody592_7 : HolLoopProg 64 :=
.mark loopBody592_6

def loopBody592_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody592_9 : HolLoopProg 64 :=
.mark loopBody592_8

def loopBody592_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody592_11 : HolLoopProg 64 :=
.mark loopBody592_10

def loopBody592_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 102) ([5, 6, 7, 8]) (some (5, loopBody592_11, loopBody592_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody592_13 : HolLoopProg 64 :=
.mark loopBody592_12

def loopBody592_14 : HolLoopProg 64 :=
.seq loopBody592_13 loopBody592_1

def loopBody592_15 : HolLoopProg 64 :=
.mark loopBody592_14

def loopBody592_16 : HolLoopProg 64 :=
.seq loopBody592_9 loopBody592_15

def loopBody592_17 : HolLoopProg 64 :=
.mark loopBody592_16

def loopBody592_18 : HolLoopProg 64 :=
.seq loopBody592_7 loopBody592_17

def loopBody592_19 : HolLoopProg 64 :=
.mark loopBody592_18

def loopBody592_20 : HolLoopProg 64 :=
.seq loopBody592_5 loopBody592_19

def loopBody592_21 : HolLoopProg 64 :=
.mark loopBody592_20

def loopBody592_22 : HolLoopProg 64 :=
.seq loopBody592_3 loopBody592_21

def loopBody592_23 : HolLoopProg 64 :=
.mark loopBody592_22

def loopBody592_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody592_25 : HolLoopProg 64 :=
.mark loopBody592_24

def loopBody592_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody592_27 : HolLoopProg 64 :=
.mark loopBody592_26

def loopBody592_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody592_29 : HolLoopProg 64 :=
.mark loopBody592_28

def loopBody592_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody592_31 : HolLoopProg 64 :=
.mark loopBody592_30

def loopBody592_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody592_29 loopBody592_31 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody592_33 : HolLoopProg 64 :=
.mark loopBody592_32

def loopBody592_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody592_35 : HolLoopProg 64 :=
.mark loopBody592_34

def loopBody592_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody592_37 : HolLoopProg 64 :=
.mark loopBody592_36

def loopBody592_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody592_39 : HolLoopProg 64 :=
.mark loopBody592_38

def loopBody592_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody592_41 : HolLoopProg 64 :=
.mark loopBody592_40

def loopBody592_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody592_43 : HolLoopProg 64 :=
.mark loopBody592_42

def loopBody592_44 : HolLoopProg 64 :=
.seq loopBody592_43 loopBody592_1

def loopBody592_45 : HolLoopProg 64 :=
.mark loopBody592_44

def loopBody592_46 : HolLoopProg 64 :=
.seq loopBody592_41 loopBody592_45

def loopBody592_47 : HolLoopProg 64 :=
.mark loopBody592_46

def loopBody592_48 : HolLoopProg 64 :=
.seq loopBody592_39 loopBody592_47

def loopBody592_49 : HolLoopProg 64 :=
.mark loopBody592_48

def loopBody592_50 : HolLoopProg 64 :=
.seq loopBody592_31 loopBody592_49

def loopBody592_51 : HolLoopProg 64 :=
.mark loopBody592_50

def loopBody592_52 : HolLoopProg 64 :=
.seq loopBody592_37 loopBody592_51

def loopBody592_53 : HolLoopProg 64 :=
.mark loopBody592_52

def loopBody592_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody592_53 loopBody592_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody592_55 : HolLoopProg 64 :=
.mark loopBody592_54

def loopBody592_56 : HolLoopProg 64 :=
.seq loopBody592_55 loopBody592_1

def loopBody592_57 : HolLoopProg 64 :=
.mark loopBody592_56

def loopBody592_58 : HolLoopProg 64 :=
.seq loopBody592_35 loopBody592_57

def loopBody592_59 : HolLoopProg 64 :=
.mark loopBody592_58

def loopBody592_60 : HolLoopProg 64 :=
.seq loopBody592_33 loopBody592_59

def loopBody592_61 : HolLoopProg 64 :=
.mark loopBody592_60

def loopBody592_62 : HolLoopProg 64 :=
.seq loopBody592_27 loopBody592_61

def loopBody592_63 : HolLoopProg 64 :=
.mark loopBody592_62

def loopBody592_64 : HolLoopProg 64 :=
.seq loopBody592_25 loopBody592_63

def loopBody592_65 : HolLoopProg 64 :=
.mark loopBody592_64

def loopBody592_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 4332616871279656263#64)

def loopBody592_67 : HolLoopProg 64 :=
.mark loopBody592_66

def loopBody592_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 10917124144477883021#64)

def loopBody592_69 : HolLoopProg 64 :=
.mark loopBody592_68

def loopBody592_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 13281191951274694749#64)

def loopBody592_71 : HolLoopProg 64 :=
.mark loopBody592_70

def loopBody592_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 3486998266802970665#64)

def loopBody592_73 : HolLoopProg 64 :=
.mark loopBody592_72

def loopBody592_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody592_75 : HolLoopProg 64 :=
.mark loopBody592_74

def loopBody592_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody592_77 : HolLoopProg 64 :=
.mark loopBody592_76

def loopBody592_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody592_79 : HolLoopProg 64 :=
.mark loopBody592_78

def loopBody592_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody592_81 : HolLoopProg 64 :=
.mark loopBody592_80

def loopBody592_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 117) [5, 6, 7, 8, 9, 10, 11, 12] none

def loopBody592_83 : HolLoopProg 64 :=
.mark loopBody592_82

def loopBody592_84 : HolLoopProg 64 :=
.seq loopBody592_83 loopBody592_1

def loopBody592_85 : HolLoopProg 64 :=
.mark loopBody592_84

def loopBody592_86 : HolLoopProg 64 :=
.seq loopBody592_81 loopBody592_85

def loopBody592_87 : HolLoopProg 64 :=
.mark loopBody592_86

def loopBody592_88 : HolLoopProg 64 :=
.seq loopBody592_79 loopBody592_87

def loopBody592_89 : HolLoopProg 64 :=
.mark loopBody592_88

def loopBody592_90 : HolLoopProg 64 :=
.seq loopBody592_77 loopBody592_89

def loopBody592_91 : HolLoopProg 64 :=
.mark loopBody592_90

def loopBody592_92 : HolLoopProg 64 :=
.seq loopBody592_75 loopBody592_91

def loopBody592_93 : HolLoopProg 64 :=
.mark loopBody592_92

def loopBody592_94 : HolLoopProg 64 :=
.seq loopBody592_73 loopBody592_93

def loopBody592_95 : HolLoopProg 64 :=
.mark loopBody592_94

def loopBody592_96 : HolLoopProg 64 :=
.seq loopBody592_71 loopBody592_95

def loopBody592_97 : HolLoopProg 64 :=
.mark loopBody592_96

def loopBody592_98 : HolLoopProg 64 :=
.seq loopBody592_69 loopBody592_97

def loopBody592_99 : HolLoopProg 64 :=
.mark loopBody592_98

def loopBody592_100 : HolLoopProg 64 :=
.seq loopBody592_67 loopBody592_99

def loopBody592_101 : HolLoopProg 64 :=
.mark loopBody592_100

def loopBody592_102 : HolLoopProg 64 :=
.seq loopBody592_65 loopBody592_101

def loopBody592_103 : HolLoopProg 64 :=
.mark loopBody592_102

def loopBody592_104 : HolLoopProg 64 :=
.seq loopBody592_23 loopBody592_103

def loopBody592_105 : HolLoopProg 64 :=
.mark loopBody592_104

def loopBody592_106 : HolLoopProg 64 :=
.seq loopBody592_1 loopBody592_105

def loopBody592_107 : HolLoopProg 64 :=
.mark loopBody592_106

def loopBody592_108 : HolLoopProg 64 :=
.seq loopBody592_1 loopBody592_107

def loopBody592_109 : HolLoopProg 64 :=
.mark loopBody592_108

def output592 : Nat × List Nat × HolLoopProg 64 :=
  (656, [0, 1, 2, 3], loopBody592_109)
end InitECandidate.Proofs.FrontendStages.Loop
