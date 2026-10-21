import InitECandidate.Proofs.FrontendStages.Loop.Translate515
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody531_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody531_1 : HolLoopProg 64 :=
.mark loopBody531_0

def loopBody531_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody531_3 : HolLoopProg 64 :=
.mark loopBody531_2

def loopBody531_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody531_5 : HolLoopProg 64 :=
.mark loopBody531_4

def loopBody531_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody531_7 : HolLoopProg 64 :=
.mark loopBody531_6

def loopBody531_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody531_9 : HolLoopProg 64 :=
.mark loopBody531_8

def loopBody531_10 : HolLoopProg 64 :=
.seq loopBody531_9 loopBody531_1

def loopBody531_11 : HolLoopProg 64 :=
.mark loopBody531_10

def loopBody531_12 : HolLoopProg 64 :=
.seq loopBody531_11 loopBody531_1

def loopBody531_13 : HolLoopProg 64 :=
.mark loopBody531_12

def loopBody531_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody531_15 : HolLoopProg 64 :=
.mark loopBody531_14

def loopBody531_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody531_17 : HolLoopProg 64 :=
.mark loopBody531_16

def loopBody531_18 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 593) ([4]) (some (4, loopBody531_17, loopBody531_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody531_19 : HolLoopProg 64 :=
.mark loopBody531_18

def loopBody531_20 : HolLoopProg 64 :=
.seq loopBody531_19 loopBody531_1

def loopBody531_21 : HolLoopProg 64 :=
.mark loopBody531_20

def loopBody531_22 : HolLoopProg 64 :=
.seq loopBody531_15 loopBody531_21

def loopBody531_23 : HolLoopProg 64 :=
.mark loopBody531_22

def loopBody531_24 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_23

def loopBody531_25 : HolLoopProg 64 :=
.mark loopBody531_24

def loopBody531_26 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_25

def loopBody531_27 : HolLoopProg 64 :=
.mark loopBody531_26

def loopBody531_28 : HolLoopProg 64 :=
.seq loopBody531_13 loopBody531_27

def loopBody531_29 : HolLoopProg 64 :=
.mark loopBody531_28

def loopBody531_30 : HolLoopProg 64 :=
.seq loopBody531_7 loopBody531_29

def loopBody531_31 : HolLoopProg 64 :=
.mark loopBody531_30

def loopBody531_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.imm 8#64) loopBody531_5 loopBody531_31 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody531_33 : HolLoopProg 64 :=
.mark loopBody531_32

def loopBody531_34 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 594) ([]) (some (3, loopBody531_33, loopBody531_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody531_35 : HolLoopProg 64 :=
.mark loopBody531_34

def loopBody531_36 : HolLoopProg 64 :=
.seq loopBody531_35 loopBody531_1

def loopBody531_37 : HolLoopProg 64 :=
.mark loopBody531_36

def loopBody531_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody531_39 : HolLoopProg 64 :=
.mark loopBody531_38

def loopBody531_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody531_41 : HolLoopProg 64 :=
.mark loopBody531_40

def loopBody531_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody531_43 : HolLoopProg 64 :=
.mark loopBody531_42

def loopBody531_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody531_45 : HolLoopProg 64 :=
.mark loopBody531_44

def loopBody531_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody531_43 loopBody531_45 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody531_47 : HolLoopProg 64 :=
.mark loopBody531_46

def loopBody531_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody531_49 : HolLoopProg 64 :=
.mark loopBody531_48

def loopBody531_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
      Flapjack.HolLoopExp.const 32#64])

def loopBody531_51 : HolLoopProg 64 :=
.mark loopBody531_50

def loopBody531_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody531_53 : HolLoopProg 64 :=
.mark loopBody531_52

def loopBody531_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody531_55 : HolLoopProg 64 :=
.mark loopBody531_54

def loopBody531_56 : HolLoopProg 64 :=
.seq loopBody531_55 loopBody531_1

def loopBody531_57 : HolLoopProg 64 :=
.mark loopBody531_56

def loopBody531_58 : HolLoopProg 64 :=
.seq loopBody531_53 loopBody531_57

def loopBody531_59 : HolLoopProg 64 :=
.mark loopBody531_58

def loopBody531_60 : HolLoopProg 64 :=
.seq loopBody531_59 loopBody531_1

def loopBody531_61 : HolLoopProg 64 :=
.mark loopBody531_60

def loopBody531_62 : HolLoopProg 64 :=
.seq loopBody531_43 loopBody531_61

def loopBody531_63 : HolLoopProg 64 :=
.mark loopBody531_62

def loopBody531_64 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_63

def loopBody531_65 : HolLoopProg 64 :=
.mark loopBody531_64

def loopBody531_66 : HolLoopProg 64 :=
.seq loopBody531_51 loopBody531_65

def loopBody531_67 : HolLoopProg 64 :=
.mark loopBody531_66

def loopBody531_68 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_67

def loopBody531_69 : HolLoopProg 64 :=
.mark loopBody531_68

def loopBody531_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody531_69 loopBody531_1 (Flapjack.Spt.ln)

def loopBody531_71 : HolLoopProg 64 :=
.mark loopBody531_70

def loopBody531_72 : HolLoopProg 64 :=
.seq loopBody531_71 loopBody531_1

def loopBody531_73 : HolLoopProg 64 :=
.mark loopBody531_72

def loopBody531_74 : HolLoopProg 64 :=
.seq loopBody531_49 loopBody531_73

def loopBody531_75 : HolLoopProg 64 :=
.mark loopBody531_74

def loopBody531_76 : HolLoopProg 64 :=
.seq loopBody531_47 loopBody531_75

def loopBody531_77 : HolLoopProg 64 :=
.mark loopBody531_76

def loopBody531_78 : HolLoopProg 64 :=
.seq loopBody531_41 loopBody531_77

def loopBody531_79 : HolLoopProg 64 :=
.mark loopBody531_78

def loopBody531_80 : HolLoopProg 64 :=
.seq loopBody531_39 loopBody531_79

def loopBody531_81 : HolLoopProg 64 :=
.mark loopBody531_80

def loopBody531_82 : HolLoopProg 64 :=
.seq loopBody531_37 loopBody531_81

def loopBody531_83 : HolLoopProg 64 :=
.mark loopBody531_82

def loopBody531_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody531_85 : HolLoopProg 64 :=
.mark loopBody531_84

def loopBody531_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody531_87 : HolLoopProg 64 :=
.mark loopBody531_86

def loopBody531_88 : HolLoopProg 64 :=
.seq loopBody531_87 loopBody531_1

def loopBody531_89 : HolLoopProg 64 :=
.mark loopBody531_88

def loopBody531_90 : HolLoopProg 64 :=
.seq loopBody531_85 loopBody531_89

def loopBody531_91 : HolLoopProg 64 :=
.mark loopBody531_90

def loopBody531_92 : HolLoopProg 64 :=
.seq loopBody531_83 loopBody531_91

def loopBody531_93 : HolLoopProg 64 :=
.mark loopBody531_92

def loopBody531_94 : HolLoopProg 64 :=
.seq loopBody531_3 loopBody531_93

def loopBody531_95 : HolLoopProg 64 :=
.mark loopBody531_94

def loopBody531_96 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_95

def loopBody531_97 : HolLoopProg 64 :=
.mark loopBody531_96

def loopBody531_98 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_97

def loopBody531_99 : HolLoopProg 64 :=
.mark loopBody531_98

def loopBody531_100 : HolLoopProg 64 :=
.seq loopBody531_1 loopBody531_99

def loopBody531_101 : HolLoopProg 64 :=
.mark loopBody531_100

def output531 : Nat × List Nat × HolLoopProg 64 :=
  (595, [], loopBody531_101)
end InitECandidate.Proofs.FrontendStages.Loop
