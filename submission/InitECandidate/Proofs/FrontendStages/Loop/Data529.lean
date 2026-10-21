import InitECandidate.Proofs.FrontendStages.Loop.Translate513
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody529_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody529_1 : HolLoopProg 64 :=
.mark loopBody529_0

def loopBody529_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody529_3 : HolLoopProg 64 :=
.mark loopBody529_2

def loopBody529_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 470) ([]) (some (2, loopBody529_3, loopBody529_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody529_5 : HolLoopProg 64 :=
.mark loopBody529_4

def loopBody529_6 : HolLoopProg 64 :=
.seq loopBody529_5 loopBody529_1

def loopBody529_7 : HolLoopProg 64 :=
.mark loopBody529_6

def loopBody529_8 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_7

def loopBody529_9 : HolLoopProg 64 :=
.mark loopBody529_8

def loopBody529_10 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_9

def loopBody529_11 : HolLoopProg 64 :=
.mark loopBody529_10

def loopBody529_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody529_13 : HolLoopProg 64 :=
.mark loopBody529_12

def loopBody529_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody529_15 : HolLoopProg 64 :=
.mark loopBody529_14

def loopBody529_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody529_17 : HolLoopProg 64 :=
.mark loopBody529_16

def loopBody529_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody529_19 : HolLoopProg 64 :=
.mark loopBody529_18

def loopBody529_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.RegImm.reg 3) loopBody529_17 loopBody529_19 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody529_21 : HolLoopProg 64 :=
.mark loopBody529_20

def loopBody529_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody529_23 : HolLoopProg 64 :=
.mark loopBody529_22

def loopBody529_24 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 600) ([2]) (some (2, loopBody529_3, loopBody529_1, (Flapjack.Spt.ln)))

def loopBody529_25 : HolLoopProg 64 :=
.mark loopBody529_24

def loopBody529_26 : HolLoopProg 64 :=
.seq loopBody529_25 loopBody529_1

def loopBody529_27 : HolLoopProg 64 :=
.mark loopBody529_26

def loopBody529_28 : HolLoopProg 64 :=
.seq loopBody529_13 loopBody529_27

def loopBody529_29 : HolLoopProg 64 :=
.mark loopBody529_28

def loopBody529_30 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_29

def loopBody529_31 : HolLoopProg 64 :=
.mark loopBody529_30

def loopBody529_32 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_31

def loopBody529_33 : HolLoopProg 64 :=
.mark loopBody529_32

def loopBody529_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody529_35 : HolLoopProg 64 :=
.mark loopBody529_34

def loopBody529_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 264#64]))

def loopBody529_37 : HolLoopProg 64 :=
.mark loopBody529_36

def loopBody529_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody529_39 : HolLoopProg 64 :=
.mark loopBody529_38

def loopBody529_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody529_41 : HolLoopProg 64 :=
.mark loopBody529_40

def loopBody529_42 : HolLoopProg 64 :=
.seq loopBody529_41 loopBody529_1

def loopBody529_43 : HolLoopProg 64 :=
.mark loopBody529_42

def loopBody529_44 : HolLoopProg 64 :=
.seq loopBody529_39 loopBody529_43

def loopBody529_45 : HolLoopProg 64 :=
.mark loopBody529_44

def loopBody529_46 : HolLoopProg 64 :=
.seq loopBody529_45 loopBody529_1

def loopBody529_47 : HolLoopProg 64 :=
.mark loopBody529_46

def loopBody529_48 : HolLoopProg 64 :=
.seq loopBody529_37 loopBody529_47

def loopBody529_49 : HolLoopProg 64 :=
.mark loopBody529_48

def loopBody529_50 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_49

def loopBody529_51 : HolLoopProg 64 :=
.mark loopBody529_50

def loopBody529_52 : HolLoopProg 64 :=
.seq loopBody529_35 loopBody529_51

def loopBody529_53 : HolLoopProg 64 :=
.mark loopBody529_52

def loopBody529_54 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_53

def loopBody529_55 : HolLoopProg 64 :=
.mark loopBody529_54

def loopBody529_56 : HolLoopProg 64 :=
.seq loopBody529_33 loopBody529_55

def loopBody529_57 : HolLoopProg 64 :=
.mark loopBody529_56

def loopBody529_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody529_59 : HolLoopProg 64 :=
.mark loopBody529_58

def loopBody529_60 : HolLoopProg 64 :=
.seq loopBody529_19 loopBody529_47

def loopBody529_61 : HolLoopProg 64 :=
.mark loopBody529_60

def loopBody529_62 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_61

def loopBody529_63 : HolLoopProg 64 :=
.mark loopBody529_62

def loopBody529_64 : HolLoopProg 64 :=
.seq loopBody529_59 loopBody529_63

def loopBody529_65 : HolLoopProg 64 :=
.mark loopBody529_64

def loopBody529_66 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_65

def loopBody529_67 : HolLoopProg 64 :=
.mark loopBody529_66

def loopBody529_68 : HolLoopProg 64 :=
.seq loopBody529_57 loopBody529_67

def loopBody529_69 : HolLoopProg 64 :=
.mark loopBody529_68

def loopBody529_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 160#64])

def loopBody529_71 : HolLoopProg 64 :=
.mark loopBody529_70

def loopBody529_72 : HolLoopProg 64 :=
.seq loopBody529_13 loopBody529_47

def loopBody529_73 : HolLoopProg 64 :=
.mark loopBody529_72

def loopBody529_74 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_73

def loopBody529_75 : HolLoopProg 64 :=
.mark loopBody529_74

def loopBody529_76 : HolLoopProg 64 :=
.seq loopBody529_71 loopBody529_75

def loopBody529_77 : HolLoopProg 64 :=
.mark loopBody529_76

def loopBody529_78 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_77

def loopBody529_79 : HolLoopProg 64 :=
.mark loopBody529_78

def loopBody529_80 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody529_69 loopBody529_79 (Flapjack.Spt.ln)

def loopBody529_81 : HolLoopProg 64 :=
.mark loopBody529_80

def loopBody529_82 : HolLoopProg 64 :=
.seq loopBody529_81 loopBody529_1

def loopBody529_83 : HolLoopProg 64 :=
.mark loopBody529_82

def loopBody529_84 : HolLoopProg 64 :=
.seq loopBody529_23 loopBody529_83

def loopBody529_85 : HolLoopProg 64 :=
.mark loopBody529_84

def loopBody529_86 : HolLoopProg 64 :=
.seq loopBody529_21 loopBody529_85

def loopBody529_87 : HolLoopProg 64 :=
.mark loopBody529_86

def loopBody529_88 : HolLoopProg 64 :=
.seq loopBody529_15 loopBody529_87

def loopBody529_89 : HolLoopProg 64 :=
.mark loopBody529_88

def loopBody529_90 : HolLoopProg 64 :=
.seq loopBody529_13 loopBody529_89

def loopBody529_91 : HolLoopProg 64 :=
.mark loopBody529_90

def loopBody529_92 : HolLoopProg 64 :=
.seq loopBody529_11 loopBody529_91

def loopBody529_93 : HolLoopProg 64 :=
.mark loopBody529_92

def loopBody529_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
      Flapjack.HolLoopExp.const 32#64])

def loopBody529_95 : HolLoopProg 64 :=
.mark loopBody529_94

def loopBody529_96 : HolLoopProg 64 :=
.seq loopBody529_17 loopBody529_47

def loopBody529_97 : HolLoopProg 64 :=
.mark loopBody529_96

def loopBody529_98 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_97

def loopBody529_99 : HolLoopProg 64 :=
.mark loopBody529_98

def loopBody529_100 : HolLoopProg 64 :=
.seq loopBody529_95 loopBody529_99

def loopBody529_101 : HolLoopProg 64 :=
.mark loopBody529_100

def loopBody529_102 : HolLoopProg 64 :=
.seq loopBody529_1 loopBody529_101

def loopBody529_103 : HolLoopProg 64 :=
.mark loopBody529_102

def loopBody529_104 : HolLoopProg 64 :=
.seq loopBody529_93 loopBody529_103

def loopBody529_105 : HolLoopProg 64 :=
.mark loopBody529_104

def loopBody529_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody529_107 : HolLoopProg 64 :=
.mark loopBody529_106

def loopBody529_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody529_109 : HolLoopProg 64 :=
.mark loopBody529_108

def loopBody529_110 : HolLoopProg 64 :=
.seq loopBody529_109 loopBody529_1

def loopBody529_111 : HolLoopProg 64 :=
.mark loopBody529_110

def loopBody529_112 : HolLoopProg 64 :=
.seq loopBody529_107 loopBody529_111

def loopBody529_113 : HolLoopProg 64 :=
.mark loopBody529_112

def loopBody529_114 : HolLoopProg 64 :=
.seq loopBody529_105 loopBody529_113

def loopBody529_115 : HolLoopProg 64 :=
.mark loopBody529_114

def output529 : Nat × List Nat × HolLoopProg 64 :=
  (593, [0], loopBody529_115)
end InitECandidate.Proofs.FrontendStages.Loop
