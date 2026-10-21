import InitECandidate.Proofs.FrontendStages.Loop.Translate274
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody290_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody290_1 : HolLoopProg 64 :=
.mark loopBody290_0

def loopBody290_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody290_3 : HolLoopProg 64 :=
.mark loopBody290_2

def loopBody290_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody290_5 : HolLoopProg 64 :=
.mark loopBody290_4

def loopBody290_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody290_7 : HolLoopProg 64 :=
.mark loopBody290_6

def loopBody290_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody290_9 : HolLoopProg 64 :=
.mark loopBody290_8

def loopBody290_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody290_11 : HolLoopProg 64 :=
.mark loopBody290_10

def loopBody290_12 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ls PUnit.unit)) (some 139) ([5, 6, 7, 8]) (some (5, loopBody290_11, loopBody290_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))

def loopBody290_13 : HolLoopProg 64 :=
.mark loopBody290_12

def loopBody290_14 : HolLoopProg 64 :=
.seq loopBody290_13 loopBody290_1

def loopBody290_15 : HolLoopProg 64 :=
.mark loopBody290_14

def loopBody290_16 : HolLoopProg 64 :=
.seq loopBody290_9 loopBody290_15

def loopBody290_17 : HolLoopProg 64 :=
.mark loopBody290_16

def loopBody290_18 : HolLoopProg 64 :=
.seq loopBody290_7 loopBody290_17

def loopBody290_19 : HolLoopProg 64 :=
.mark loopBody290_18

def loopBody290_20 : HolLoopProg 64 :=
.seq loopBody290_5 loopBody290_19

def loopBody290_21 : HolLoopProg 64 :=
.mark loopBody290_20

def loopBody290_22 : HolLoopProg 64 :=
.seq loopBody290_3 loopBody290_21

def loopBody290_23 : HolLoopProg 64 :=
.mark loopBody290_22

def loopBody290_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody290_25 : HolLoopProg 64 :=
.mark loopBody290_24

def loopBody290_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody290_27 : HolLoopProg 64 :=
.mark loopBody290_26

def loopBody290_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody290_29 : HolLoopProg 64 :=
.mark loopBody290_28

def loopBody290_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody290_31 : HolLoopProg 64 :=
.mark loopBody290_30

def loopBody290_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody290_29 loopBody290_31 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody290_33 : HolLoopProg 64 :=
.mark loopBody290_32

def loopBody290_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody290_35 : HolLoopProg 64 :=
.mark loopBody290_34

def loopBody290_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody290_37 : HolLoopProg 64 :=
.mark loopBody290_36

def loopBody290_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody290_39 : HolLoopProg 64 :=
.mark loopBody290_38

def loopBody290_40 : HolLoopProg 64 :=
.seq loopBody290_39 loopBody290_1

def loopBody290_41 : HolLoopProg 64 :=
.mark loopBody290_40

def loopBody290_42 : HolLoopProg 64 :=
.seq loopBody290_37 loopBody290_41

def loopBody290_43 : HolLoopProg 64 :=
.mark loopBody290_42

def loopBody290_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody290_43 loopBody290_1 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody290_45 : HolLoopProg 64 :=
.mark loopBody290_44

def loopBody290_46 : HolLoopProg 64 :=
.seq loopBody290_45 loopBody290_1

def loopBody290_47 : HolLoopProg 64 :=
.mark loopBody290_46

def loopBody290_48 : HolLoopProg 64 :=
.seq loopBody290_35 loopBody290_47

def loopBody290_49 : HolLoopProg 64 :=
.mark loopBody290_48

def loopBody290_50 : HolLoopProg 64 :=
.seq loopBody290_33 loopBody290_49

def loopBody290_51 : HolLoopProg 64 :=
.mark loopBody290_50

def loopBody290_52 : HolLoopProg 64 :=
.seq loopBody290_27 loopBody290_51

def loopBody290_53 : HolLoopProg 64 :=
.mark loopBody290_52

def loopBody290_54 : HolLoopProg 64 :=
.seq loopBody290_25 loopBody290_53

def loopBody290_55 : HolLoopProg 64 :=
.mark loopBody290_54

def loopBody290_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody290_57 : HolLoopProg 64 :=
.mark loopBody290_56

def loopBody290_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody290_59 : HolLoopProg 64 :=
.mark loopBody290_58

def loopBody290_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 128#64)

def loopBody290_61 : HolLoopProg 64 :=
.mark loopBody290_60

def loopBody290_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody290_29 loopBody290_31 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody290_63 : HolLoopProg 64 :=
.mark loopBody290_62

def loopBody290_64 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody290_43 loopBody290_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody290_65 : HolLoopProg 64 :=
.mark loopBody290_64

def loopBody290_66 : HolLoopProg 64 :=
.seq loopBody290_65 loopBody290_1

def loopBody290_67 : HolLoopProg 64 :=
.mark loopBody290_66

def loopBody290_68 : HolLoopProg 64 :=
.seq loopBody290_35 loopBody290_67

def loopBody290_69 : HolLoopProg 64 :=
.mark loopBody290_68

def loopBody290_70 : HolLoopProg 64 :=
.seq loopBody290_63 loopBody290_69

def loopBody290_71 : HolLoopProg 64 :=
.mark loopBody290_70

def loopBody290_72 : HolLoopProg 64 :=
.seq loopBody290_61 loopBody290_71

def loopBody290_73 : HolLoopProg 64 :=
.mark loopBody290_72

def loopBody290_74 : HolLoopProg 64 :=
.seq loopBody290_59 loopBody290_73

def loopBody290_75 : HolLoopProg 64 :=
.mark loopBody290_74

def loopBody290_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody290_75 loopBody290_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody290_77 : HolLoopProg 64 :=
.mark loopBody290_76

def loopBody290_78 : HolLoopProg 64 :=
.seq loopBody290_77 loopBody290_1

def loopBody290_79 : HolLoopProg 64 :=
.mark loopBody290_78

def loopBody290_80 : HolLoopProg 64 :=
.seq loopBody290_35 loopBody290_79

def loopBody290_81 : HolLoopProg 64 :=
.mark loopBody290_80

def loopBody290_82 : HolLoopProg 64 :=
.seq loopBody290_33 loopBody290_81

def loopBody290_83 : HolLoopProg 64 :=
.mark loopBody290_82

def loopBody290_84 : HolLoopProg 64 :=
.seq loopBody290_57 loopBody290_83

def loopBody290_85 : HolLoopProg 64 :=
.mark loopBody290_84

def loopBody290_86 : HolLoopProg 64 :=
.seq loopBody290_25 loopBody290_85

def loopBody290_87 : HolLoopProg 64 :=
.mark loopBody290_86

def loopBody290_88 : HolLoopProg 64 :=
.seq loopBody290_55 loopBody290_87

def loopBody290_89 : HolLoopProg 64 :=
.mark loopBody290_88

def loopBody290_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 1#64, Flapjack.HolLoopExp.var 4])

def loopBody290_91 : HolLoopProg 64 :=
.mark loopBody290_90

def loopBody290_92 : HolLoopProg 64 :=
.seq loopBody290_91 loopBody290_41

def loopBody290_93 : HolLoopProg 64 :=
.mark loopBody290_92

def loopBody290_94 : HolLoopProg 64 :=
.seq loopBody290_89 loopBody290_93

def loopBody290_95 : HolLoopProg 64 :=
.mark loopBody290_94

def loopBody290_96 : HolLoopProg 64 :=
.seq loopBody290_23 loopBody290_95

def loopBody290_97 : HolLoopProg 64 :=
.mark loopBody290_96

def loopBody290_98 : HolLoopProg 64 :=
.seq loopBody290_1 loopBody290_97

def loopBody290_99 : HolLoopProg 64 :=
.mark loopBody290_98

def loopBody290_100 : HolLoopProg 64 :=
.seq loopBody290_1 loopBody290_99

def loopBody290_101 : HolLoopProg 64 :=
.mark loopBody290_100

def output290 : Nat × List Nat × HolLoopProg 64 :=
  (354, [0, 1, 2, 3], loopBody290_101)
end InitECandidate.Proofs.FrontendStages.Loop
