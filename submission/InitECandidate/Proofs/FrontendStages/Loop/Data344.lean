import InitECandidate.Proofs.FrontendStages.Loop.Translate328
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody344_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody344_1 : HolLoopProg 64 :=
.mark loopBody344_0

def loopBody344_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody344_3 : HolLoopProg 64 :=
.mark loopBody344_2

def loopBody344_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody344_5 : HolLoopProg 64 :=
.mark loopBody344_4

def loopBody344_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody344_7 : HolLoopProg 64 :=
.mark loopBody344_6

def loopBody344_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 388) ([3, 4]) (some (3, loopBody344_7, loopBody344_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody344_9 : HolLoopProg 64 :=
.mark loopBody344_8

def loopBody344_10 : HolLoopProg 64 :=
.seq loopBody344_9 loopBody344_1

def loopBody344_11 : HolLoopProg 64 :=
.mark loopBody344_10

def loopBody344_12 : HolLoopProg 64 :=
.seq loopBody344_5 loopBody344_11

def loopBody344_13 : HolLoopProg 64 :=
.mark loopBody344_12

def loopBody344_14 : HolLoopProg 64 :=
.seq loopBody344_3 loopBody344_13

def loopBody344_15 : HolLoopProg 64 :=
.mark loopBody344_14

def loopBody344_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 64#64]))

def loopBody344_17 : HolLoopProg 64 :=
.mark loopBody344_16

def loopBody344_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody344_19 : HolLoopProg 64 :=
.mark loopBody344_18

def loopBody344_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody344_21 : HolLoopProg 64 :=
.mark loopBody344_20

def loopBody344_22 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.ln)) (some 186) ([5, 6]) (some (5, loopBody344_21, loopBody344_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody344_23 : HolLoopProg 64 :=
.mark loopBody344_22

def loopBody344_24 : HolLoopProg 64 :=
.seq loopBody344_23 loopBody344_1

def loopBody344_25 : HolLoopProg 64 :=
.mark loopBody344_24

def loopBody344_26 : HolLoopProg 64 :=
.seq loopBody344_19 loopBody344_25

def loopBody344_27 : HolLoopProg 64 :=
.mark loopBody344_26

def loopBody344_28 : HolLoopProg 64 :=
.seq loopBody344_17 loopBody344_27

def loopBody344_29 : HolLoopProg 64 :=
.mark loopBody344_28

def loopBody344_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody344_31 : HolLoopProg 64 :=
.mark loopBody344_30

def loopBody344_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody344_33 : HolLoopProg 64 :=
.mark loopBody344_32

def loopBody344_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody344_35 : HolLoopProg 64 :=
.mark loopBody344_34

def loopBody344_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody344_37 : HolLoopProg 64 :=
.mark loopBody344_36

def loopBody344_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody344_35 loopBody344_37 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody344_39 : HolLoopProg 64 :=
.mark loopBody344_38

def loopBody344_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody344_41 : HolLoopProg 64 :=
.mark loopBody344_40

def loopBody344_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody344_43 : HolLoopProg 64 :=
.mark loopBody344_42

def loopBody344_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody344_45 : HolLoopProg 64 :=
.mark loopBody344_44

def loopBody344_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody344_47 : HolLoopProg 64 :=
.mark loopBody344_46

def loopBody344_48 : HolLoopProg 64 :=
.seq loopBody344_47 loopBody344_1

def loopBody344_49 : HolLoopProg 64 :=
.mark loopBody344_48

def loopBody344_50 : HolLoopProg 64 :=
.seq loopBody344_45 loopBody344_49

def loopBody344_51 : HolLoopProg 64 :=
.mark loopBody344_50

def loopBody344_52 : HolLoopProg 64 :=
.seq loopBody344_33 loopBody344_51

def loopBody344_53 : HolLoopProg 64 :=
.mark loopBody344_52

def loopBody344_54 : HolLoopProg 64 :=
.seq loopBody344_37 loopBody344_53

def loopBody344_55 : HolLoopProg 64 :=
.mark loopBody344_54

def loopBody344_56 : HolLoopProg 64 :=
.seq loopBody344_43 loopBody344_55

def loopBody344_57 : HolLoopProg 64 :=
.mark loopBody344_56

def loopBody344_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody344_57 loopBody344_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody344_59 : HolLoopProg 64 :=
.mark loopBody344_58

def loopBody344_60 : HolLoopProg 64 :=
.seq loopBody344_59 loopBody344_1

def loopBody344_61 : HolLoopProg 64 :=
.mark loopBody344_60

def loopBody344_62 : HolLoopProg 64 :=
.seq loopBody344_41 loopBody344_61

def loopBody344_63 : HolLoopProg 64 :=
.mark loopBody344_62

def loopBody344_64 : HolLoopProg 64 :=
.seq loopBody344_39 loopBody344_63

def loopBody344_65 : HolLoopProg 64 :=
.mark loopBody344_64

def loopBody344_66 : HolLoopProg 64 :=
.seq loopBody344_33 loopBody344_65

def loopBody344_67 : HolLoopProg 64 :=
.mark loopBody344_66

def loopBody344_68 : HolLoopProg 64 :=
.seq loopBody344_31 loopBody344_67

def loopBody344_69 : HolLoopProg 64 :=
.mark loopBody344_68

def loopBody344_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 4))

def loopBody344_71 : HolLoopProg 64 :=
.mark loopBody344_70

def loopBody344_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 8#64]))

def loopBody344_73 : HolLoopProg 64 :=
.mark loopBody344_72

def loopBody344_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 16#64]))

def loopBody344_75 : HolLoopProg 64 :=
.mark loopBody344_74

def loopBody344_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64]))

def loopBody344_77 : HolLoopProg 64 :=
.mark loopBody344_76

def loopBody344_78 : HolLoopProg 64 :=
.seq loopBody344_77 loopBody344_49

def loopBody344_79 : HolLoopProg 64 :=
.mark loopBody344_78

def loopBody344_80 : HolLoopProg 64 :=
.seq loopBody344_75 loopBody344_79

def loopBody344_81 : HolLoopProg 64 :=
.mark loopBody344_80

def loopBody344_82 : HolLoopProg 64 :=
.seq loopBody344_73 loopBody344_81

def loopBody344_83 : HolLoopProg 64 :=
.mark loopBody344_82

def loopBody344_84 : HolLoopProg 64 :=
.seq loopBody344_71 loopBody344_83

def loopBody344_85 : HolLoopProg 64 :=
.mark loopBody344_84

def loopBody344_86 : HolLoopProg 64 :=
.seq loopBody344_69 loopBody344_85

def loopBody344_87 : HolLoopProg 64 :=
.mark loopBody344_86

def loopBody344_88 : HolLoopProg 64 :=
.seq loopBody344_29 loopBody344_87

def loopBody344_89 : HolLoopProg 64 :=
.mark loopBody344_88

def loopBody344_90 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_89

def loopBody344_91 : HolLoopProg 64 :=
.mark loopBody344_90

def loopBody344_92 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_91

def loopBody344_93 : HolLoopProg 64 :=
.mark loopBody344_92

def loopBody344_94 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_93

def loopBody344_95 : HolLoopProg 64 :=
.mark loopBody344_94

def loopBody344_96 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_95

def loopBody344_97 : HolLoopProg 64 :=
.mark loopBody344_96

def loopBody344_98 : HolLoopProg 64 :=
.seq loopBody344_15 loopBody344_97

def loopBody344_99 : HolLoopProg 64 :=
.mark loopBody344_98

def loopBody344_100 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_99

def loopBody344_101 : HolLoopProg 64 :=
.mark loopBody344_100

def loopBody344_102 : HolLoopProg 64 :=
.seq loopBody344_1 loopBody344_101

def loopBody344_103 : HolLoopProg 64 :=
.mark loopBody344_102

def output344 : Nat × List Nat × HolLoopProg 64 :=
  (408, [0, 1], loopBody344_103)
end InitECandidate.Proofs.FrontendStages.Loop
