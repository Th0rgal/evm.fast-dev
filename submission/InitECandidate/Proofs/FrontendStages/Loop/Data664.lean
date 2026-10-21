import InitECandidate.Proofs.FrontendStages.Loop.Translate648
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody664_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody664_1 : HolLoopProg 64 :=
.mark loopBody664_0

def loopBody664_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 0))

def loopBody664_3 : HolLoopProg 64 :=
.mark loopBody664_2

def loopBody664_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody664_5 : HolLoopProg 64 :=
.mark loopBody664_4

def loopBody664_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody664_7 : HolLoopProg 64 :=
.mark loopBody664_6

def loopBody664_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64]))

def loopBody664_9 : HolLoopProg 64 :=
.mark loopBody664_8

def loopBody664_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody664_11 : HolLoopProg 64 :=
.mark loopBody664_10

def loopBody664_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody664_13 : HolLoopProg 64 :=
.mark loopBody664_12

def loopBody664_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody664_15 : HolLoopProg 64 :=
.mark loopBody664_14

def loopBody664_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody664_17 : HolLoopProg 64 :=
.mark loopBody664_16

def loopBody664_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody664_19 : HolLoopProg 64 :=
.mark loopBody664_18

def loopBody664_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody664_21 : HolLoopProg 64 :=
.mark loopBody664_20

def loopBody664_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 32#64]))

def loopBody664_23 : HolLoopProg 64 :=
.mark loopBody664_22

def loopBody664_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 40#64]))

def loopBody664_25 : HolLoopProg 64 :=
.mark loopBody664_24

def loopBody664_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 4,
      Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 8,
      Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.var 12])

def loopBody664_27 : HolLoopProg 64 :=
.mark loopBody664_26

def loopBody664_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody664_29 : HolLoopProg 64 :=
.mark loopBody664_28

def loopBody664_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody664_31 : HolLoopProg 64 :=
.mark loopBody664_30

def loopBody664_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody664_33 : HolLoopProg 64 :=
.mark loopBody664_32

def loopBody664_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.RegImm.reg 15) loopBody664_31 loopBody664_33 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
  Flapjack.Spt.ln)

def loopBody664_35 : HolLoopProg 64 :=
.mark loopBody664_34

def loopBody664_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody664_37 : HolLoopProg 64 :=
.mark loopBody664_36

def loopBody664_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody664_39 : HolLoopProg 64 :=
.mark loopBody664_38

def loopBody664_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13]

def loopBody664_41 : HolLoopProg 64 :=
.mark loopBody664_40

def loopBody664_42 : HolLoopProg 64 :=
.seq loopBody664_41 loopBody664_1

def loopBody664_43 : HolLoopProg 64 :=
.mark loopBody664_42

def loopBody664_44 : HolLoopProg 64 :=
.seq loopBody664_39 loopBody664_43

def loopBody664_45 : HolLoopProg 64 :=
.mark loopBody664_44

def loopBody664_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.RegImm.imm 0#64) loopBody664_45 loopBody664_1 (Flapjack.Spt.ln)

def loopBody664_47 : HolLoopProg 64 :=
.mark loopBody664_46

def loopBody664_48 : HolLoopProg 64 :=
.seq loopBody664_47 loopBody664_1

def loopBody664_49 : HolLoopProg 64 :=
.mark loopBody664_48

def loopBody664_50 : HolLoopProg 64 :=
.seq loopBody664_37 loopBody664_49

def loopBody664_51 : HolLoopProg 64 :=
.mark loopBody664_50

def loopBody664_52 : HolLoopProg 64 :=
.seq loopBody664_35 loopBody664_51

def loopBody664_53 : HolLoopProg 64 :=
.mark loopBody664_52

def loopBody664_54 : HolLoopProg 64 :=
.seq loopBody664_29 loopBody664_53

def loopBody664_55 : HolLoopProg 64 :=
.mark loopBody664_54

def loopBody664_56 : HolLoopProg 64 :=
.seq loopBody664_27 loopBody664_55

def loopBody664_57 : HolLoopProg 64 :=
.mark loopBody664_56

def loopBody664_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody664_59 : HolLoopProg 64 :=
.mark loopBody664_58

def loopBody664_60 : HolLoopProg 64 :=
.seq loopBody664_59 loopBody664_43

def loopBody664_61 : HolLoopProg 64 :=
.mark loopBody664_60

def loopBody664_62 : HolLoopProg 64 :=
.seq loopBody664_57 loopBody664_61

def loopBody664_63 : HolLoopProg 64 :=
.mark loopBody664_62

def loopBody664_64 : HolLoopProg 64 :=
.seq loopBody664_25 loopBody664_63

def loopBody664_65 : HolLoopProg 64 :=
.mark loopBody664_64

def loopBody664_66 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_65

def loopBody664_67 : HolLoopProg 64 :=
.mark loopBody664_66

def loopBody664_68 : HolLoopProg 64 :=
.seq loopBody664_23 loopBody664_67

def loopBody664_69 : HolLoopProg 64 :=
.mark loopBody664_68

def loopBody664_70 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_69

def loopBody664_71 : HolLoopProg 64 :=
.mark loopBody664_70

def loopBody664_72 : HolLoopProg 64 :=
.seq loopBody664_21 loopBody664_71

def loopBody664_73 : HolLoopProg 64 :=
.mark loopBody664_72

def loopBody664_74 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_73

def loopBody664_75 : HolLoopProg 64 :=
.mark loopBody664_74

def loopBody664_76 : HolLoopProg 64 :=
.seq loopBody664_19 loopBody664_75

def loopBody664_77 : HolLoopProg 64 :=
.mark loopBody664_76

def loopBody664_78 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_77

def loopBody664_79 : HolLoopProg 64 :=
.mark loopBody664_78

def loopBody664_80 : HolLoopProg 64 :=
.seq loopBody664_17 loopBody664_79

def loopBody664_81 : HolLoopProg 64 :=
.mark loopBody664_80

def loopBody664_82 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_81

def loopBody664_83 : HolLoopProg 64 :=
.mark loopBody664_82

def loopBody664_84 : HolLoopProg 64 :=
.seq loopBody664_15 loopBody664_83

def loopBody664_85 : HolLoopProg 64 :=
.mark loopBody664_84

def loopBody664_86 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_85

def loopBody664_87 : HolLoopProg 64 :=
.mark loopBody664_86

def loopBody664_88 : HolLoopProg 64 :=
.seq loopBody664_13 loopBody664_87

def loopBody664_89 : HolLoopProg 64 :=
.mark loopBody664_88

def loopBody664_90 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_89

def loopBody664_91 : HolLoopProg 64 :=
.mark loopBody664_90

def loopBody664_92 : HolLoopProg 64 :=
.seq loopBody664_11 loopBody664_91

def loopBody664_93 : HolLoopProg 64 :=
.mark loopBody664_92

def loopBody664_94 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_93

def loopBody664_95 : HolLoopProg 64 :=
.mark loopBody664_94

def loopBody664_96 : HolLoopProg 64 :=
.seq loopBody664_9 loopBody664_95

def loopBody664_97 : HolLoopProg 64 :=
.mark loopBody664_96

def loopBody664_98 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_97

def loopBody664_99 : HolLoopProg 64 :=
.mark loopBody664_98

def loopBody664_100 : HolLoopProg 64 :=
.seq loopBody664_7 loopBody664_99

def loopBody664_101 : HolLoopProg 64 :=
.mark loopBody664_100

def loopBody664_102 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_101

def loopBody664_103 : HolLoopProg 64 :=
.mark loopBody664_102

def loopBody664_104 : HolLoopProg 64 :=
.seq loopBody664_5 loopBody664_103

def loopBody664_105 : HolLoopProg 64 :=
.mark loopBody664_104

def loopBody664_106 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_105

def loopBody664_107 : HolLoopProg 64 :=
.mark loopBody664_106

def loopBody664_108 : HolLoopProg 64 :=
.seq loopBody664_3 loopBody664_107

def loopBody664_109 : HolLoopProg 64 :=
.mark loopBody664_108

def loopBody664_110 : HolLoopProg 64 :=
.seq loopBody664_1 loopBody664_109

def loopBody664_111 : HolLoopProg 64 :=
.mark loopBody664_110

def output664 : Nat × List Nat × HolLoopProg 64 :=
  (728, [0], loopBody664_111)
end InitECandidate.Proofs.FrontendStages.Loop
