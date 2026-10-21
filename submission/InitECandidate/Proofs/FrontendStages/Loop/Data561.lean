import InitECandidate.Proofs.FrontendStages.Loop.Translate545
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody561_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody561_1 : HolLoopProg 64 :=
.mark loopBody561_0

def loopBody561_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 16#64)

def loopBody561_3 : HolLoopProg 64 :=
.mark loopBody561_2

def loopBody561_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody561_5 : HolLoopProg 64 :=
.mark loopBody561_4

def loopBody561_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody561_7 : HolLoopProg 64 :=
.mark loopBody561_6

def loopBody561_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody561_5 loopBody561_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody561_9 : HolLoopProg 64 :=
.mark loopBody561_8

def loopBody561_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody561_11 : HolLoopProg 64 :=
.mark loopBody561_10

def loopBody561_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1352829926#64)

def loopBody561_13 : HolLoopProg 64 :=
.mark loopBody561_12

def loopBody561_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody561_15 : HolLoopProg 64 :=
.mark loopBody561_14

def loopBody561_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody561_17 : HolLoopProg 64 :=
.mark loopBody561_16

def loopBody561_18 : HolLoopProg 64 :=
.seq loopBody561_15 loopBody561_17

def loopBody561_19 : HolLoopProg 64 :=
.mark loopBody561_18

def loopBody561_20 : HolLoopProg 64 :=
.seq loopBody561_13 loopBody561_19

def loopBody561_21 : HolLoopProg 64 :=
.mark loopBody561_20

def loopBody561_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody561_21 loopBody561_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody561_23 : HolLoopProg 64 :=
.mark loopBody561_22

def loopBody561_24 : HolLoopProg 64 :=
.seq loopBody561_23 loopBody561_17

def loopBody561_25 : HolLoopProg 64 :=
.mark loopBody561_24

def loopBody561_26 : HolLoopProg 64 :=
.seq loopBody561_11 loopBody561_25

def loopBody561_27 : HolLoopProg 64 :=
.mark loopBody561_26

def loopBody561_28 : HolLoopProg 64 :=
.seq loopBody561_9 loopBody561_27

def loopBody561_29 : HolLoopProg 64 :=
.mark loopBody561_28

def loopBody561_30 : HolLoopProg 64 :=
.seq loopBody561_3 loopBody561_29

def loopBody561_31 : HolLoopProg 64 :=
.mark loopBody561_30

def loopBody561_32 : HolLoopProg 64 :=
.seq loopBody561_1 loopBody561_31

def loopBody561_33 : HolLoopProg 64 :=
.mark loopBody561_32

def loopBody561_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 32#64)

def loopBody561_35 : HolLoopProg 64 :=
.mark loopBody561_34

def loopBody561_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1548603684#64)

def loopBody561_37 : HolLoopProg 64 :=
.mark loopBody561_36

def loopBody561_38 : HolLoopProg 64 :=
.seq loopBody561_37 loopBody561_19

def loopBody561_39 : HolLoopProg 64 :=
.mark loopBody561_38

def loopBody561_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody561_39 loopBody561_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody561_41 : HolLoopProg 64 :=
.mark loopBody561_40

def loopBody561_42 : HolLoopProg 64 :=
.seq loopBody561_41 loopBody561_17

def loopBody561_43 : HolLoopProg 64 :=
.mark loopBody561_42

def loopBody561_44 : HolLoopProg 64 :=
.seq loopBody561_11 loopBody561_43

def loopBody561_45 : HolLoopProg 64 :=
.mark loopBody561_44

def loopBody561_46 : HolLoopProg 64 :=
.seq loopBody561_9 loopBody561_45

def loopBody561_47 : HolLoopProg 64 :=
.mark loopBody561_46

def loopBody561_48 : HolLoopProg 64 :=
.seq loopBody561_35 loopBody561_47

def loopBody561_49 : HolLoopProg 64 :=
.mark loopBody561_48

def loopBody561_50 : HolLoopProg 64 :=
.seq loopBody561_1 loopBody561_49

def loopBody561_51 : HolLoopProg 64 :=
.mark loopBody561_50

def loopBody561_52 : HolLoopProg 64 :=
.seq loopBody561_33 loopBody561_51

def loopBody561_53 : HolLoopProg 64 :=
.mark loopBody561_52

def loopBody561_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 48#64)

def loopBody561_55 : HolLoopProg 64 :=
.mark loopBody561_54

def loopBody561_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1836072691#64)

def loopBody561_57 : HolLoopProg 64 :=
.mark loopBody561_56

def loopBody561_58 : HolLoopProg 64 :=
.seq loopBody561_57 loopBody561_19

def loopBody561_59 : HolLoopProg 64 :=
.mark loopBody561_58

def loopBody561_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody561_59 loopBody561_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody561_61 : HolLoopProg 64 :=
.mark loopBody561_60

def loopBody561_62 : HolLoopProg 64 :=
.seq loopBody561_61 loopBody561_17

def loopBody561_63 : HolLoopProg 64 :=
.mark loopBody561_62

def loopBody561_64 : HolLoopProg 64 :=
.seq loopBody561_11 loopBody561_63

def loopBody561_65 : HolLoopProg 64 :=
.mark loopBody561_64

def loopBody561_66 : HolLoopProg 64 :=
.seq loopBody561_9 loopBody561_65

def loopBody561_67 : HolLoopProg 64 :=
.mark loopBody561_66

def loopBody561_68 : HolLoopProg 64 :=
.seq loopBody561_55 loopBody561_67

def loopBody561_69 : HolLoopProg 64 :=
.mark loopBody561_68

def loopBody561_70 : HolLoopProg 64 :=
.seq loopBody561_1 loopBody561_69

def loopBody561_71 : HolLoopProg 64 :=
.mark loopBody561_70

def loopBody561_72 : HolLoopProg 64 :=
.seq loopBody561_53 loopBody561_71

def loopBody561_73 : HolLoopProg 64 :=
.mark loopBody561_72

def loopBody561_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 64#64)

def loopBody561_75 : HolLoopProg 64 :=
.mark loopBody561_74

def loopBody561_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody561_5 loopBody561_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody561_77 : HolLoopProg 64 :=
.mark loopBody561_76

def loopBody561_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 2053994217#64)

def loopBody561_79 : HolLoopProg 64 :=
.mark loopBody561_78

def loopBody561_80 : HolLoopProg 64 :=
.seq loopBody561_79 loopBody561_19

def loopBody561_81 : HolLoopProg 64 :=
.mark loopBody561_80

def loopBody561_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody561_81 loopBody561_17 (Flapjack.Spt.ln)

def loopBody561_83 : HolLoopProg 64 :=
.mark loopBody561_82

def loopBody561_84 : HolLoopProg 64 :=
.seq loopBody561_83 loopBody561_17

def loopBody561_85 : HolLoopProg 64 :=
.mark loopBody561_84

def loopBody561_86 : HolLoopProg 64 :=
.seq loopBody561_11 loopBody561_85

def loopBody561_87 : HolLoopProg 64 :=
.mark loopBody561_86

def loopBody561_88 : HolLoopProg 64 :=
.seq loopBody561_77 loopBody561_87

def loopBody561_89 : HolLoopProg 64 :=
.mark loopBody561_88

def loopBody561_90 : HolLoopProg 64 :=
.seq loopBody561_75 loopBody561_89

def loopBody561_91 : HolLoopProg 64 :=
.mark loopBody561_90

def loopBody561_92 : HolLoopProg 64 :=
.seq loopBody561_1 loopBody561_91

def loopBody561_93 : HolLoopProg 64 :=
.mark loopBody561_92

def loopBody561_94 : HolLoopProg 64 :=
.seq loopBody561_73 loopBody561_93

def loopBody561_95 : HolLoopProg 64 :=
.mark loopBody561_94

def loopBody561_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody561_97 : HolLoopProg 64 :=
.mark loopBody561_96

def loopBody561_98 : HolLoopProg 64 :=
.seq loopBody561_97 loopBody561_19

def loopBody561_99 : HolLoopProg 64 :=
.mark loopBody561_98

def loopBody561_100 : HolLoopProg 64 :=
.seq loopBody561_95 loopBody561_99

def loopBody561_101 : HolLoopProg 64 :=
.mark loopBody561_100

def output561 : Nat × List Nat × HolLoopProg 64 :=
  (625, [0], loopBody561_101)
end InitECandidate.Proofs.FrontendStages.Loop
