import InitECandidate.Proofs.FrontendStages.Loop.Translate241
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody257_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody257_1 : HolLoopProg 64 :=
.mark loopBody257_0

def loopBody257_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody257_3 : HolLoopProg 64 :=
.mark loopBody257_2

def loopBody257_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody257_5 : HolLoopProg 64 :=
.mark loopBody257_4

def loopBody257_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody257_7 : HolLoopProg 64 :=
.mark loopBody257_6

def loopBody257_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody257_9 : HolLoopProg 64 :=
.mark loopBody257_8

def loopBody257_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody257_11 : HolLoopProg 64 :=
.mark loopBody257_10

def loopBody257_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody257_9 loopBody257_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody257_13 : HolLoopProg 64 :=
.mark loopBody257_12

def loopBody257_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody257_15 : HolLoopProg 64 :=
.mark loopBody257_14

def loopBody257_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody257_17 : HolLoopProg 64 :=
.mark loopBody257_16

def loopBody257_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody257_19 : HolLoopProg 64 :=
.mark loopBody257_18

def loopBody257_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2, 3]

def loopBody257_21 : HolLoopProg 64 :=
.mark loopBody257_20

def loopBody257_22 : HolLoopProg 64 :=
.seq loopBody257_21 loopBody257_1

def loopBody257_23 : HolLoopProg 64 :=
.mark loopBody257_22

def loopBody257_24 : HolLoopProg 64 :=
.seq loopBody257_19 loopBody257_23

def loopBody257_25 : HolLoopProg 64 :=
.mark loopBody257_24

def loopBody257_26 : HolLoopProg 64 :=
.seq loopBody257_17 loopBody257_25

def loopBody257_27 : HolLoopProg 64 :=
.mark loopBody257_26

def loopBody257_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody257_27 loopBody257_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody257_29 : HolLoopProg 64 :=
.mark loopBody257_28

def loopBody257_30 : HolLoopProg 64 :=
.seq loopBody257_29 loopBody257_1

def loopBody257_31 : HolLoopProg 64 :=
.mark loopBody257_30

def loopBody257_32 : HolLoopProg 64 :=
.seq loopBody257_15 loopBody257_31

def loopBody257_33 : HolLoopProg 64 :=
.mark loopBody257_32

def loopBody257_34 : HolLoopProg 64 :=
.seq loopBody257_13 loopBody257_33

def loopBody257_35 : HolLoopProg 64 :=
.mark loopBody257_34

def loopBody257_36 : HolLoopProg 64 :=
.seq loopBody257_7 loopBody257_35

def loopBody257_37 : HolLoopProg 64 :=
.mark loopBody257_36

def loopBody257_38 : HolLoopProg 64 :=
.seq loopBody257_5 loopBody257_37

def loopBody257_39 : HolLoopProg 64 :=
.mark loopBody257_38

def loopBody257_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody257_41 : HolLoopProg 64 :=
.mark loopBody257_40

def loopBody257_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody257_9 loopBody257_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody257_43 : HolLoopProg 64 :=
.mark loopBody257_42

def loopBody257_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 2#64)

def loopBody257_45 : HolLoopProg 64 :=
.mark loopBody257_44

def loopBody257_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody257_47 : HolLoopProg 64 :=
.mark loopBody257_46

def loopBody257_48 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 282) ([3]) (some (3, loopBody257_47, loopBody257_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody257_49 : HolLoopProg 64 :=
.mark loopBody257_48

def loopBody257_50 : HolLoopProg 64 :=
.seq loopBody257_49 loopBody257_1

def loopBody257_51 : HolLoopProg 64 :=
.mark loopBody257_50

def loopBody257_52 : HolLoopProg 64 :=
.seq loopBody257_45 loopBody257_51

def loopBody257_53 : HolLoopProg 64 :=
.mark loopBody257_52

def loopBody257_54 : HolLoopProg 64 :=
.seq loopBody257_1 loopBody257_53

def loopBody257_55 : HolLoopProg 64 :=
.mark loopBody257_54

def loopBody257_56 : HolLoopProg 64 :=
.seq loopBody257_1 loopBody257_55

def loopBody257_57 : HolLoopProg 64 :=
.mark loopBody257_56

def loopBody257_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody257_57 loopBody257_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody257_59 : HolLoopProg 64 :=
.mark loopBody257_58

def loopBody257_60 : HolLoopProg 64 :=
.seq loopBody257_59 loopBody257_1

def loopBody257_61 : HolLoopProg 64 :=
.mark loopBody257_60

def loopBody257_62 : HolLoopProg 64 :=
.seq loopBody257_15 loopBody257_61

def loopBody257_63 : HolLoopProg 64 :=
.mark loopBody257_62

def loopBody257_64 : HolLoopProg 64 :=
.seq loopBody257_43 loopBody257_63

def loopBody257_65 : HolLoopProg 64 :=
.mark loopBody257_64

def loopBody257_66 : HolLoopProg 64 :=
.seq loopBody257_7 loopBody257_65

def loopBody257_67 : HolLoopProg 64 :=
.mark loopBody257_66

def loopBody257_68 : HolLoopProg 64 :=
.seq loopBody257_41 loopBody257_67

def loopBody257_69 : HolLoopProg 64 :=
.mark loopBody257_68

def loopBody257_70 : HolLoopProg 64 :=
.seq loopBody257_39 loopBody257_69

def loopBody257_71 : HolLoopProg 64 :=
.mark loopBody257_70

def loopBody257_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody257_73 : HolLoopProg 64 :=
.mark loopBody257_72

def loopBody257_74 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 320) ([3]) (some (3, loopBody257_47, loopBody257_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody257_75 : HolLoopProg 64 :=
.mark loopBody257_74

def loopBody257_76 : HolLoopProg 64 :=
.seq loopBody257_75 loopBody257_1

def loopBody257_77 : HolLoopProg 64 :=
.mark loopBody257_76

def loopBody257_78 : HolLoopProg 64 :=
.seq loopBody257_73 loopBody257_77

def loopBody257_79 : HolLoopProg 64 :=
.mark loopBody257_78

def loopBody257_80 : HolLoopProg 64 :=
.seq loopBody257_1 loopBody257_79

def loopBody257_81 : HolLoopProg 64 :=
.mark loopBody257_80

def loopBody257_82 : HolLoopProg 64 :=
.seq loopBody257_1 loopBody257_81

def loopBody257_83 : HolLoopProg 64 :=
.mark loopBody257_82

def loopBody257_84 : HolLoopProg 64 :=
.seq loopBody257_71 loopBody257_83

def loopBody257_85 : HolLoopProg 64 :=
.mark loopBody257_84

def loopBody257_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody257_87 : HolLoopProg 64 :=
.mark loopBody257_86

def loopBody257_88 : HolLoopProg 64 :=
.seq loopBody257_87 loopBody257_25

def loopBody257_89 : HolLoopProg 64 :=
.mark loopBody257_88

def loopBody257_90 : HolLoopProg 64 :=
.seq loopBody257_85 loopBody257_89

def loopBody257_91 : HolLoopProg 64 :=
.mark loopBody257_90

def loopBody257_92 : HolLoopProg 64 :=
.seq loopBody257_3 loopBody257_91

def loopBody257_93 : HolLoopProg 64 :=
.mark loopBody257_92

def loopBody257_94 : HolLoopProg 64 :=
.seq loopBody257_1 loopBody257_93

def loopBody257_95 : HolLoopProg 64 :=
.mark loopBody257_94

def output257 : Nat × List Nat × HolLoopProg 64 :=
  (321, [0], loopBody257_95)
end InitECandidate.Proofs.FrontendStages.Loop
