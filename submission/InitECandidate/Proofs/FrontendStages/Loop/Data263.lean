import InitECandidate.Proofs.FrontendStages.Loop.Translate247
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody263_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody263_1 : HolLoopProg 64 :=
.mark loopBody263_0

def loopBody263_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody263_3 : HolLoopProg 64 :=
.mark loopBody263_2

def loopBody263_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody263_5 : HolLoopProg 64 :=
.mark loopBody263_4

def loopBody263_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody263_7 : HolLoopProg 64 :=
.mark loopBody263_6

def loopBody263_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody263_9 : HolLoopProg 64 :=
.mark loopBody263_8

def loopBody263_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody263_11 : HolLoopProg 64 :=
.mark loopBody263_10

def loopBody263_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody263_9 loopBody263_11 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody263_13 : HolLoopProg 64 :=
.mark loopBody263_12

def loopBody263_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody263_15 : HolLoopProg 64 :=
.mark loopBody263_14

def loopBody263_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody263_17 : HolLoopProg 64 :=
.mark loopBody263_16

def loopBody263_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 128#64]))

def loopBody263_19 : HolLoopProg 64 :=
.mark loopBody263_18

def loopBody263_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody263_21 : HolLoopProg 64 :=
.mark loopBody263_20

def loopBody263_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody263_23 : HolLoopProg 64 :=
.mark loopBody263_22

def loopBody263_24 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 77) ([4, 5, 6]) (some (4, loopBody263_23, loopBody263_1, (Flapjack.Spt.ln)))

def loopBody263_25 : HolLoopProg 64 :=
.mark loopBody263_24

def loopBody263_26 : HolLoopProg 64 :=
.seq loopBody263_25 loopBody263_1

def loopBody263_27 : HolLoopProg 64 :=
.mark loopBody263_26

def loopBody263_28 : HolLoopProg 64 :=
.seq loopBody263_21 loopBody263_27

def loopBody263_29 : HolLoopProg 64 :=
.mark loopBody263_28

def loopBody263_30 : HolLoopProg 64 :=
.seq loopBody263_19 loopBody263_29

def loopBody263_31 : HolLoopProg 64 :=
.mark loopBody263_30

def loopBody263_32 : HolLoopProg 64 :=
.seq loopBody263_17 loopBody263_31

def loopBody263_33 : HolLoopProg 64 :=
.mark loopBody263_32

def loopBody263_34 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_33

def loopBody263_35 : HolLoopProg 64 :=
.mark loopBody263_34

def loopBody263_36 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_35

def loopBody263_37 : HolLoopProg 64 :=
.mark loopBody263_36

def loopBody263_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody263_39 : HolLoopProg 64 :=
.mark loopBody263_38

def loopBody263_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody263_41 : HolLoopProg 64 :=
.mark loopBody263_40

def loopBody263_42 : HolLoopProg 64 :=
.seq loopBody263_41 loopBody263_1

def loopBody263_43 : HolLoopProg 64 :=
.mark loopBody263_42

def loopBody263_44 : HolLoopProg 64 :=
.seq loopBody263_39 loopBody263_43

def loopBody263_45 : HolLoopProg 64 :=
.mark loopBody263_44

def loopBody263_46 : HolLoopProg 64 :=
.seq loopBody263_37 loopBody263_45

def loopBody263_47 : HolLoopProg 64 :=
.mark loopBody263_46

def loopBody263_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody263_47 loopBody263_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody263_49 : HolLoopProg 64 :=
.mark loopBody263_48

def loopBody263_50 : HolLoopProg 64 :=
.seq loopBody263_49 loopBody263_1

def loopBody263_51 : HolLoopProg 64 :=
.mark loopBody263_50

def loopBody263_52 : HolLoopProg 64 :=
.seq loopBody263_15 loopBody263_51

def loopBody263_53 : HolLoopProg 64 :=
.mark loopBody263_52

def loopBody263_54 : HolLoopProg 64 :=
.seq loopBody263_13 loopBody263_53

def loopBody263_55 : HolLoopProg 64 :=
.mark loopBody263_54

def loopBody263_56 : HolLoopProg 64 :=
.seq loopBody263_7 loopBody263_55

def loopBody263_57 : HolLoopProg 64 :=
.mark loopBody263_56

def loopBody263_58 : HolLoopProg 64 :=
.seq loopBody263_5 loopBody263_57

def loopBody263_59 : HolLoopProg 64 :=
.mark loopBody263_58

def loopBody263_60 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 326) ([4]) (some (4, loopBody263_23, loopBody263_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody263_61 : HolLoopProg 64 :=
.mark loopBody263_60

def loopBody263_62 : HolLoopProg 64 :=
.seq loopBody263_61 loopBody263_1

def loopBody263_63 : HolLoopProg 64 :=
.mark loopBody263_62

def loopBody263_64 : HolLoopProg 64 :=
.seq loopBody263_5 loopBody263_63

def loopBody263_65 : HolLoopProg 64 :=
.mark loopBody263_64

def loopBody263_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody263_67 : HolLoopProg 64 :=
.mark loopBody263_66

def loopBody263_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody263_69 : HolLoopProg 64 :=
.mark loopBody263_68

def loopBody263_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody263_71 : HolLoopProg 64 :=
.mark loopBody263_70

def loopBody263_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody263_73 : HolLoopProg 64 :=
.mark loopBody263_72

def loopBody263_74 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 77) ([5, 6, 7]) (some (5, loopBody263_73, loopBody263_1, (Flapjack.Spt.ln)))

def loopBody263_75 : HolLoopProg 64 :=
.mark loopBody263_74

def loopBody263_76 : HolLoopProg 64 :=
.seq loopBody263_75 loopBody263_1

def loopBody263_77 : HolLoopProg 64 :=
.mark loopBody263_76

def loopBody263_78 : HolLoopProg 64 :=
.seq loopBody263_71 loopBody263_77

def loopBody263_79 : HolLoopProg 64 :=
.mark loopBody263_78

def loopBody263_80 : HolLoopProg 64 :=
.seq loopBody263_69 loopBody263_79

def loopBody263_81 : HolLoopProg 64 :=
.mark loopBody263_80

def loopBody263_82 : HolLoopProg 64 :=
.seq loopBody263_67 loopBody263_81

def loopBody263_83 : HolLoopProg 64 :=
.mark loopBody263_82

def loopBody263_84 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_83

def loopBody263_85 : HolLoopProg 64 :=
.mark loopBody263_84

def loopBody263_86 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_85

def loopBody263_87 : HolLoopProg 64 :=
.mark loopBody263_86

def loopBody263_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody263_89 : HolLoopProg 64 :=
.mark loopBody263_88

def loopBody263_90 : HolLoopProg 64 :=
.seq loopBody263_89 loopBody263_1

def loopBody263_91 : HolLoopProg 64 :=
.mark loopBody263_90

def loopBody263_92 : HolLoopProg 64 :=
.seq loopBody263_11 loopBody263_91

def loopBody263_93 : HolLoopProg 64 :=
.mark loopBody263_92

def loopBody263_94 : HolLoopProg 64 :=
.seq loopBody263_87 loopBody263_93

def loopBody263_95 : HolLoopProg 64 :=
.mark loopBody263_94

def loopBody263_96 : HolLoopProg 64 :=
.seq loopBody263_65 loopBody263_95

def loopBody263_97 : HolLoopProg 64 :=
.mark loopBody263_96

def loopBody263_98 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_97

def loopBody263_99 : HolLoopProg 64 :=
.mark loopBody263_98

def loopBody263_100 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_99

def loopBody263_101 : HolLoopProg 64 :=
.mark loopBody263_100

def loopBody263_102 : HolLoopProg 64 :=
.seq loopBody263_59 loopBody263_101

def loopBody263_103 : HolLoopProg 64 :=
.mark loopBody263_102

def loopBody263_104 : HolLoopProg 64 :=
.seq loopBody263_3 loopBody263_103

def loopBody263_105 : HolLoopProg 64 :=
.mark loopBody263_104

def loopBody263_106 : HolLoopProg 64 :=
.seq loopBody263_1 loopBody263_105

def loopBody263_107 : HolLoopProg 64 :=
.mark loopBody263_106

def output263 : Nat × List Nat × HolLoopProg 64 :=
  (327, [0, 1], loopBody263_107)
end InitECandidate.Proofs.FrontendStages.Loop
