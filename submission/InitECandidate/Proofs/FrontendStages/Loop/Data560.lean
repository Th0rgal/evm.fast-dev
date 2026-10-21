import InitECandidate.Proofs.FrontendStages.Loop.Translate544
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody560_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody560_1 : HolLoopProg 64 :=
.mark loopBody560_0

def loopBody560_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 16#64)

def loopBody560_3 : HolLoopProg 64 :=
.mark loopBody560_2

def loopBody560_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody560_5 : HolLoopProg 64 :=
.mark loopBody560_4

def loopBody560_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody560_7 : HolLoopProg 64 :=
.mark loopBody560_6

def loopBody560_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody560_5 loopBody560_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody560_9 : HolLoopProg 64 :=
.mark loopBody560_8

def loopBody560_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody560_11 : HolLoopProg 64 :=
.mark loopBody560_10

def loopBody560_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody560_13 : HolLoopProg 64 :=
.mark loopBody560_12

def loopBody560_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody560_15 : HolLoopProg 64 :=
.mark loopBody560_14

def loopBody560_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody560_17 : HolLoopProg 64 :=
.mark loopBody560_16

def loopBody560_18 : HolLoopProg 64 :=
.seq loopBody560_15 loopBody560_17

def loopBody560_19 : HolLoopProg 64 :=
.mark loopBody560_18

def loopBody560_20 : HolLoopProg 64 :=
.seq loopBody560_13 loopBody560_19

def loopBody560_21 : HolLoopProg 64 :=
.mark loopBody560_20

def loopBody560_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody560_21 loopBody560_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody560_23 : HolLoopProg 64 :=
.mark loopBody560_22

def loopBody560_24 : HolLoopProg 64 :=
.seq loopBody560_23 loopBody560_17

def loopBody560_25 : HolLoopProg 64 :=
.mark loopBody560_24

def loopBody560_26 : HolLoopProg 64 :=
.seq loopBody560_11 loopBody560_25

def loopBody560_27 : HolLoopProg 64 :=
.mark loopBody560_26

def loopBody560_28 : HolLoopProg 64 :=
.seq loopBody560_9 loopBody560_27

def loopBody560_29 : HolLoopProg 64 :=
.mark loopBody560_28

def loopBody560_30 : HolLoopProg 64 :=
.seq loopBody560_3 loopBody560_29

def loopBody560_31 : HolLoopProg 64 :=
.mark loopBody560_30

def loopBody560_32 : HolLoopProg 64 :=
.seq loopBody560_1 loopBody560_31

def loopBody560_33 : HolLoopProg 64 :=
.mark loopBody560_32

def loopBody560_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 32#64)

def loopBody560_35 : HolLoopProg 64 :=
.mark loopBody560_34

def loopBody560_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1518500249#64)

def loopBody560_37 : HolLoopProg 64 :=
.mark loopBody560_36

def loopBody560_38 : HolLoopProg 64 :=
.seq loopBody560_37 loopBody560_19

def loopBody560_39 : HolLoopProg 64 :=
.mark loopBody560_38

def loopBody560_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody560_39 loopBody560_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody560_41 : HolLoopProg 64 :=
.mark loopBody560_40

def loopBody560_42 : HolLoopProg 64 :=
.seq loopBody560_41 loopBody560_17

def loopBody560_43 : HolLoopProg 64 :=
.mark loopBody560_42

def loopBody560_44 : HolLoopProg 64 :=
.seq loopBody560_11 loopBody560_43

def loopBody560_45 : HolLoopProg 64 :=
.mark loopBody560_44

def loopBody560_46 : HolLoopProg 64 :=
.seq loopBody560_9 loopBody560_45

def loopBody560_47 : HolLoopProg 64 :=
.mark loopBody560_46

def loopBody560_48 : HolLoopProg 64 :=
.seq loopBody560_35 loopBody560_47

def loopBody560_49 : HolLoopProg 64 :=
.mark loopBody560_48

def loopBody560_50 : HolLoopProg 64 :=
.seq loopBody560_1 loopBody560_49

def loopBody560_51 : HolLoopProg 64 :=
.mark loopBody560_50

def loopBody560_52 : HolLoopProg 64 :=
.seq loopBody560_33 loopBody560_51

def loopBody560_53 : HolLoopProg 64 :=
.mark loopBody560_52

def loopBody560_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 48#64)

def loopBody560_55 : HolLoopProg 64 :=
.mark loopBody560_54

def loopBody560_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1859775393#64)

def loopBody560_57 : HolLoopProg 64 :=
.mark loopBody560_56

def loopBody560_58 : HolLoopProg 64 :=
.seq loopBody560_57 loopBody560_19

def loopBody560_59 : HolLoopProg 64 :=
.mark loopBody560_58

def loopBody560_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody560_59 loopBody560_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody560_61 : HolLoopProg 64 :=
.mark loopBody560_60

def loopBody560_62 : HolLoopProg 64 :=
.seq loopBody560_61 loopBody560_17

def loopBody560_63 : HolLoopProg 64 :=
.mark loopBody560_62

def loopBody560_64 : HolLoopProg 64 :=
.seq loopBody560_11 loopBody560_63

def loopBody560_65 : HolLoopProg 64 :=
.mark loopBody560_64

def loopBody560_66 : HolLoopProg 64 :=
.seq loopBody560_9 loopBody560_65

def loopBody560_67 : HolLoopProg 64 :=
.mark loopBody560_66

def loopBody560_68 : HolLoopProg 64 :=
.seq loopBody560_55 loopBody560_67

def loopBody560_69 : HolLoopProg 64 :=
.mark loopBody560_68

def loopBody560_70 : HolLoopProg 64 :=
.seq loopBody560_1 loopBody560_69

def loopBody560_71 : HolLoopProg 64 :=
.mark loopBody560_70

def loopBody560_72 : HolLoopProg 64 :=
.seq loopBody560_53 loopBody560_71

def loopBody560_73 : HolLoopProg 64 :=
.mark loopBody560_72

def loopBody560_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 64#64)

def loopBody560_75 : HolLoopProg 64 :=
.mark loopBody560_74

def loopBody560_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody560_5 loopBody560_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody560_77 : HolLoopProg 64 :=
.mark loopBody560_76

def loopBody560_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 2400959708#64)

def loopBody560_79 : HolLoopProg 64 :=
.mark loopBody560_78

def loopBody560_80 : HolLoopProg 64 :=
.seq loopBody560_79 loopBody560_19

def loopBody560_81 : HolLoopProg 64 :=
.mark loopBody560_80

def loopBody560_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody560_81 loopBody560_17 (Flapjack.Spt.ln)

def loopBody560_83 : HolLoopProg 64 :=
.mark loopBody560_82

def loopBody560_84 : HolLoopProg 64 :=
.seq loopBody560_83 loopBody560_17

def loopBody560_85 : HolLoopProg 64 :=
.mark loopBody560_84

def loopBody560_86 : HolLoopProg 64 :=
.seq loopBody560_11 loopBody560_85

def loopBody560_87 : HolLoopProg 64 :=
.mark loopBody560_86

def loopBody560_88 : HolLoopProg 64 :=
.seq loopBody560_77 loopBody560_87

def loopBody560_89 : HolLoopProg 64 :=
.mark loopBody560_88

def loopBody560_90 : HolLoopProg 64 :=
.seq loopBody560_75 loopBody560_89

def loopBody560_91 : HolLoopProg 64 :=
.mark loopBody560_90

def loopBody560_92 : HolLoopProg 64 :=
.seq loopBody560_1 loopBody560_91

def loopBody560_93 : HolLoopProg 64 :=
.mark loopBody560_92

def loopBody560_94 : HolLoopProg 64 :=
.seq loopBody560_73 loopBody560_93

def loopBody560_95 : HolLoopProg 64 :=
.mark loopBody560_94

def loopBody560_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 2840853838#64)

def loopBody560_97 : HolLoopProg 64 :=
.mark loopBody560_96

def loopBody560_98 : HolLoopProg 64 :=
.seq loopBody560_97 loopBody560_19

def loopBody560_99 : HolLoopProg 64 :=
.mark loopBody560_98

def loopBody560_100 : HolLoopProg 64 :=
.seq loopBody560_95 loopBody560_99

def loopBody560_101 : HolLoopProg 64 :=
.mark loopBody560_100

def output560 : Nat × List Nat × HolLoopProg 64 :=
  (624, [0], loopBody560_101)
end InitECandidate.Proofs.FrontendStages.Loop
