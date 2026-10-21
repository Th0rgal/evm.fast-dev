import InitECandidate.Proofs.FrontendStages.Loop.Translate605
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody621_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody621_1 : HolLoopProg 64 :=
.mark loopBody621_0

def loopBody621_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody621_3 : HolLoopProg 64 :=
.mark loopBody621_2

def loopBody621_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody621_5 : HolLoopProg 64 :=
.mark loopBody621_4

def loopBody621_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody621_7 : HolLoopProg 64 :=
.mark loopBody621_6

def loopBody621_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody621_9 : HolLoopProg 64 :=
.mark loopBody621_8

def loopBody621_10 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody621_9 loopBody621_5 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody621_11 : HolLoopProg 64 :=
.mark loopBody621_10

def loopBody621_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody621_13 : HolLoopProg 64 :=
.mark loopBody621_12

def loopBody621_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody621_15 : HolLoopProg 64 :=
.mark loopBody621_14

def loopBody621_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 3)

def loopBody621_17 : HolLoopProg 64 :=
.mark loopBody621_16

def loopBody621_18 : HolLoopProg 64 :=
.seq loopBody621_17 loopBody621_1

def loopBody621_19 : HolLoopProg 64 :=
.mark loopBody621_18

def loopBody621_20 : HolLoopProg 64 :=
.seq loopBody621_19 loopBody621_1

def loopBody621_21 : HolLoopProg 64 :=
.mark loopBody621_20

def loopBody621_22 : HolLoopProg 64 :=
.seq loopBody621_15 loopBody621_21

def loopBody621_23 : HolLoopProg 64 :=
.mark loopBody621_22

def loopBody621_24 : HolLoopProg 64 :=
.seq loopBody621_1 loopBody621_23

def loopBody621_25 : HolLoopProg 64 :=
.mark loopBody621_24

def loopBody621_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 5#64)])

def loopBody621_27 : HolLoopProg 64 :=
.mark loopBody621_26

def loopBody621_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody621_29 : HolLoopProg 64 :=
.mark loopBody621_28

def loopBody621_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody621_31 : HolLoopProg 64 :=
.mark loopBody621_30

def loopBody621_32 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 80) ([4, 5]) (some (4, loopBody621_31, loopBody621_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody621_33 : HolLoopProg 64 :=
.mark loopBody621_32

def loopBody621_34 : HolLoopProg 64 :=
.seq loopBody621_33 loopBody621_1

def loopBody621_35 : HolLoopProg 64 :=
.mark loopBody621_34

def loopBody621_36 : HolLoopProg 64 :=
.seq loopBody621_29 loopBody621_35

def loopBody621_37 : HolLoopProg 64 :=
.mark loopBody621_36

def loopBody621_38 : HolLoopProg 64 :=
.seq loopBody621_27 loopBody621_37

def loopBody621_39 : HolLoopProg 64 :=
.mark loopBody621_38

def loopBody621_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody621_41 : HolLoopProg 64 :=
.mark loopBody621_40

def loopBody621_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody621_43 : HolLoopProg 64 :=
.mark loopBody621_42

def loopBody621_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody621_45 : HolLoopProg 64 :=
.mark loopBody621_44

def loopBody621_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody621_47 : HolLoopProg 64 :=
.mark loopBody621_46

def loopBody621_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody621_45 loopBody621_47 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))

def loopBody621_49 : HolLoopProg 64 :=
.mark loopBody621_48

def loopBody621_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody621_51 : HolLoopProg 64 :=
.mark loopBody621_50

def loopBody621_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody621_53 : HolLoopProg 64 :=
.mark loopBody621_52

def loopBody621_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody621_55 : HolLoopProg 64 :=
.mark loopBody621_54

def loopBody621_56 : HolLoopProg 64 :=
.seq loopBody621_55 loopBody621_1

def loopBody621_57 : HolLoopProg 64 :=
.mark loopBody621_56

def loopBody621_58 : HolLoopProg 64 :=
.seq loopBody621_53 loopBody621_57

def loopBody621_59 : HolLoopProg 64 :=
.mark loopBody621_58

def loopBody621_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody621_59 loopBody621_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody621_61 : HolLoopProg 64 :=
.mark loopBody621_60

def loopBody621_62 : HolLoopProg 64 :=
.seq loopBody621_61 loopBody621_1

def loopBody621_63 : HolLoopProg 64 :=
.mark loopBody621_62

def loopBody621_64 : HolLoopProg 64 :=
.seq loopBody621_51 loopBody621_63

def loopBody621_65 : HolLoopProg 64 :=
.mark loopBody621_64

def loopBody621_66 : HolLoopProg 64 :=
.seq loopBody621_49 loopBody621_65

def loopBody621_67 : HolLoopProg 64 :=
.mark loopBody621_66

def loopBody621_68 : HolLoopProg 64 :=
.seq loopBody621_43 loopBody621_67

def loopBody621_69 : HolLoopProg 64 :=
.mark loopBody621_68

def loopBody621_70 : HolLoopProg 64 :=
.seq loopBody621_41 loopBody621_69

def loopBody621_71 : HolLoopProg 64 :=
.mark loopBody621_70

def loopBody621_72 : HolLoopProg 64 :=
.seq loopBody621_39 loopBody621_71

def loopBody621_73 : HolLoopProg 64 :=
.mark loopBody621_72

def loopBody621_74 : HolLoopProg 64 :=
.seq loopBody621_1 loopBody621_73

def loopBody621_75 : HolLoopProg 64 :=
.mark loopBody621_74

def loopBody621_76 : HolLoopProg 64 :=
.seq loopBody621_1 loopBody621_75

def loopBody621_77 : HolLoopProg 64 :=
.mark loopBody621_76

def loopBody621_78 : HolLoopProg 64 :=
.seq loopBody621_25 loopBody621_77

def loopBody621_79 : HolLoopProg 64 :=
.mark loopBody621_78

def loopBody621_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody621_81 : HolLoopProg 64 :=
.mark loopBody621_80

def loopBody621_82 : HolLoopProg 64 :=
.seq loopBody621_79 loopBody621_81

def loopBody621_83 : HolLoopProg 64 :=
.mark loopBody621_82

def loopBody621_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody621_85 : HolLoopProg 64 :=
.mark loopBody621_84

def loopBody621_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody621_83 loopBody621_85 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody621_87 : HolLoopProg 64 :=
.mark loopBody621_86

def loopBody621_88 : HolLoopProg 64 :=
.seq loopBody621_87 loopBody621_1

def loopBody621_89 : HolLoopProg 64 :=
.mark loopBody621_88

def loopBody621_90 : HolLoopProg 64 :=
.seq loopBody621_13 loopBody621_89

def loopBody621_91 : HolLoopProg 64 :=
.mark loopBody621_90

def loopBody621_92 : HolLoopProg 64 :=
.seq loopBody621_11 loopBody621_91

def loopBody621_93 : HolLoopProg 64 :=
.mark loopBody621_92

def loopBody621_94 : HolLoopProg 64 :=
.seq loopBody621_7 loopBody621_93

def loopBody621_95 : HolLoopProg 64 :=
.mark loopBody621_94

def loopBody621_96 : HolLoopProg 64 :=
.seq loopBody621_5 loopBody621_95

def loopBody621_97 : HolLoopProg 64 :=
.mark loopBody621_96

def loopBody621_98 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) loopBody621_97 (Flapjack.Spt.ln)

def loopBody621_99 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64])

def loopBody621_100 : HolLoopProg 64 :=
.mark loopBody621_99

def loopBody621_101 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody621_102 : HolLoopProg 64 :=
.mark loopBody621_101

def loopBody621_103 : HolLoopProg 64 :=
.seq loopBody621_102 loopBody621_1

def loopBody621_104 : HolLoopProg 64 :=
.mark loopBody621_103

def loopBody621_105 : HolLoopProg 64 :=
.seq loopBody621_100 loopBody621_104

def loopBody621_106 : HolLoopProg 64 :=
.mark loopBody621_105

def loopBody621_107 : HolLoopProg 64 :=
.seq loopBody621_98 loopBody621_106

def loopBody621_108 : HolLoopProg 64 :=
.seq loopBody621_3 loopBody621_107

def loopBody621_109 : HolLoopProg 64 :=
.seq loopBody621_1 loopBody621_108

def output621 : Nat × List Nat × HolLoopProg 64 :=
  (685, [0, 1], loopBody621_109)
end InitECandidate.Proofs.FrontendStages.Loop
