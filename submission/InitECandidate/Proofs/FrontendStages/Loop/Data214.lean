import InitECandidate.Proofs.FrontendStages.Loop.Translate198
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody214_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody214_1 : HolLoopProg 64 :=
.mark loopBody214_0

def loopBody214_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody214_3 : HolLoopProg 64 :=
.mark loopBody214_2

def loopBody214_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1024#64)

def loopBody214_5 : HolLoopProg 64 :=
.mark loopBody214_4

def loopBody214_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody214_7 : HolLoopProg 64 :=
.mark loopBody214_6

def loopBody214_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 95) ([3, 4]) (some (3, loopBody214_7, loopBody214_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody214_9 : HolLoopProg 64 :=
.mark loopBody214_8

def loopBody214_10 : HolLoopProg 64 :=
.seq loopBody214_9 loopBody214_1

def loopBody214_11 : HolLoopProg 64 :=
.mark loopBody214_10

def loopBody214_12 : HolLoopProg 64 :=
.seq loopBody214_5 loopBody214_11

def loopBody214_13 : HolLoopProg 64 :=
.mark loopBody214_12

def loopBody214_14 : HolLoopProg 64 :=
.seq loopBody214_3 loopBody214_13

def loopBody214_15 : HolLoopProg 64 :=
.mark loopBody214_14

def loopBody214_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody214_17 : HolLoopProg 64 :=
.mark loopBody214_16

def loopBody214_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2])

def loopBody214_19 : HolLoopProg 64 :=
.mark loopBody214_18

def loopBody214_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody214_21 : HolLoopProg 64 :=
.mark loopBody214_20

def loopBody214_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody214_23 : HolLoopProg 64 :=
.mark loopBody214_22

def loopBody214_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 4 (Flapjack.RegImm.reg 5) loopBody214_21 loopBody214_23 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody214_25 : HolLoopProg 64 :=
.mark loopBody214_24

def loopBody214_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody214_27 : HolLoopProg 64 :=
.mark loopBody214_26

def loopBody214_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody214_29 : HolLoopProg 64 :=
.mark loopBody214_28

def loopBody214_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody214_31 : HolLoopProg 64 :=
.mark loopBody214_30

def loopBody214_32 : HolLoopProg 64 :=
.seq loopBody214_31 loopBody214_1

def loopBody214_33 : HolLoopProg 64 :=
.mark loopBody214_32

def loopBody214_34 : HolLoopProg 64 :=
.seq loopBody214_29 loopBody214_33

def loopBody214_35 : HolLoopProg 64 :=
.mark loopBody214_34

def loopBody214_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody214_35 loopBody214_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody214_37 : HolLoopProg 64 :=
.mark loopBody214_36

def loopBody214_38 : HolLoopProg 64 :=
.seq loopBody214_37 loopBody214_1

def loopBody214_39 : HolLoopProg 64 :=
.mark loopBody214_38

def loopBody214_40 : HolLoopProg 64 :=
.seq loopBody214_27 loopBody214_39

def loopBody214_41 : HolLoopProg 64 :=
.mark loopBody214_40

def loopBody214_42 : HolLoopProg 64 :=
.seq loopBody214_25 loopBody214_41

def loopBody214_43 : HolLoopProg 64 :=
.mark loopBody214_42

def loopBody214_44 : HolLoopProg 64 :=
.seq loopBody214_19 loopBody214_43

def loopBody214_45 : HolLoopProg 64 :=
.mark loopBody214_44

def loopBody214_46 : HolLoopProg 64 :=
.seq loopBody214_17 loopBody214_45

def loopBody214_47 : HolLoopProg 64 :=
.mark loopBody214_46

def loopBody214_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody214_49 : HolLoopProg 64 :=
.mark loopBody214_48

def loopBody214_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 2])

def loopBody214_51 : HolLoopProg 64 :=
.mark loopBody214_50

def loopBody214_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 4 (Flapjack.RegImm.reg 5) loopBody214_21 loopBody214_23 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody214_53 : HolLoopProg 64 :=
.mark loopBody214_52

def loopBody214_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody214_35 loopBody214_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody214_55 : HolLoopProg 64 :=
.mark loopBody214_54

def loopBody214_56 : HolLoopProg 64 :=
.seq loopBody214_55 loopBody214_1

def loopBody214_57 : HolLoopProg 64 :=
.mark loopBody214_56

def loopBody214_58 : HolLoopProg 64 :=
.seq loopBody214_27 loopBody214_57

def loopBody214_59 : HolLoopProg 64 :=
.mark loopBody214_58

def loopBody214_60 : HolLoopProg 64 :=
.seq loopBody214_53 loopBody214_59

def loopBody214_61 : HolLoopProg 64 :=
.mark loopBody214_60

def loopBody214_62 : HolLoopProg 64 :=
.seq loopBody214_51 loopBody214_61

def loopBody214_63 : HolLoopProg 64 :=
.mark loopBody214_62

def loopBody214_64 : HolLoopProg 64 :=
.seq loopBody214_49 loopBody214_63

def loopBody214_65 : HolLoopProg 64 :=
.mark loopBody214_64

def loopBody214_66 : HolLoopProg 64 :=
.seq loopBody214_47 loopBody214_65

def loopBody214_67 : HolLoopProg 64 :=
.mark loopBody214_66

def loopBody214_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 5000#64)

def loopBody214_69 : HolLoopProg 64 :=
.mark loopBody214_68

def loopBody214_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody214_21 loopBody214_23 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody214_71 : HolLoopProg 64 :=
.mark loopBody214_70

def loopBody214_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody214_35 loopBody214_1 (Flapjack.Spt.ln)

def loopBody214_73 : HolLoopProg 64 :=
.mark loopBody214_72

def loopBody214_74 : HolLoopProg 64 :=
.seq loopBody214_73 loopBody214_1

def loopBody214_75 : HolLoopProg 64 :=
.mark loopBody214_74

def loopBody214_76 : HolLoopProg 64 :=
.seq loopBody214_27 loopBody214_75

def loopBody214_77 : HolLoopProg 64 :=
.mark loopBody214_76

def loopBody214_78 : HolLoopProg 64 :=
.seq loopBody214_71 loopBody214_77

def loopBody214_79 : HolLoopProg 64 :=
.mark loopBody214_78

def loopBody214_80 : HolLoopProg 64 :=
.seq loopBody214_69 loopBody214_79

def loopBody214_81 : HolLoopProg 64 :=
.mark loopBody214_80

def loopBody214_82 : HolLoopProg 64 :=
.seq loopBody214_17 loopBody214_81

def loopBody214_83 : HolLoopProg 64 :=
.mark loopBody214_82

def loopBody214_84 : HolLoopProg 64 :=
.seq loopBody214_67 loopBody214_83

def loopBody214_85 : HolLoopProg 64 :=
.mark loopBody214_84

def loopBody214_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody214_87 : HolLoopProg 64 :=
.mark loopBody214_86

def loopBody214_88 : HolLoopProg 64 :=
.seq loopBody214_87 loopBody214_33

def loopBody214_89 : HolLoopProg 64 :=
.mark loopBody214_88

def loopBody214_90 : HolLoopProg 64 :=
.seq loopBody214_85 loopBody214_89

def loopBody214_91 : HolLoopProg 64 :=
.mark loopBody214_90

def loopBody214_92 : HolLoopProg 64 :=
.seq loopBody214_15 loopBody214_91

def loopBody214_93 : HolLoopProg 64 :=
.mark loopBody214_92

def loopBody214_94 : HolLoopProg 64 :=
.seq loopBody214_1 loopBody214_93

def loopBody214_95 : HolLoopProg 64 :=
.mark loopBody214_94

def loopBody214_96 : HolLoopProg 64 :=
.seq loopBody214_1 loopBody214_95

def loopBody214_97 : HolLoopProg 64 :=
.mark loopBody214_96

def output214 : Nat × List Nat × HolLoopProg 64 :=
  (278, [0, 1], loopBody214_97)
end InitECandidate.Proofs.FrontendStages.Loop
