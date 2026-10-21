import InitECandidate.Proofs.FrontendStages.Loop.Translate171
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody187_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody187_1 : HolLoopProg 64 :=
.mark loopBody187_0

def loopBody187_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody187_3 : HolLoopProg 64 :=
.mark loopBody187_2

def loopBody187_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody187_5 : HolLoopProg 64 :=
.mark loopBody187_4

def loopBody187_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody187_7 : HolLoopProg 64 :=
.mark loopBody187_6

def loopBody187_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody187_9 : HolLoopProg 64 :=
.mark loopBody187_8

def loopBody187_10 : HolLoopProg 64 :=
.call (some
  ([4, 5],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 247) ([6, 7, 8]) (some (6, loopBody187_9, loopBody187_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody187_11 : HolLoopProg 64 :=
.mark loopBody187_10

def loopBody187_12 : HolLoopProg 64 :=
.seq loopBody187_11 loopBody187_1

def loopBody187_13 : HolLoopProg 64 :=
.mark loopBody187_12

def loopBody187_14 : HolLoopProg 64 :=
.seq loopBody187_7 loopBody187_13

def loopBody187_15 : HolLoopProg 64 :=
.mark loopBody187_14

def loopBody187_16 : HolLoopProg 64 :=
.seq loopBody187_5 loopBody187_15

def loopBody187_17 : HolLoopProg 64 :=
.mark loopBody187_16

def loopBody187_18 : HolLoopProg 64 :=
.seq loopBody187_3 loopBody187_17

def loopBody187_19 : HolLoopProg 64 :=
.mark loopBody187_18

def loopBody187_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody187_21 : HolLoopProg 64 :=
.mark loopBody187_20

def loopBody187_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody187_23 : HolLoopProg 64 :=
.mark loopBody187_22

def loopBody187_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody187_25 : HolLoopProg 64 :=
.mark loopBody187_24

def loopBody187_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody187_27 : HolLoopProg 64 :=
.mark loopBody187_26

def loopBody187_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody187_29 : HolLoopProg 64 :=
.mark loopBody187_28

def loopBody187_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.RegImm.reg 9) loopBody187_27 loopBody187_29 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody187_31 : HolLoopProg 64 :=
.mark loopBody187_30

def loopBody187_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody187_33 : HolLoopProg 64 :=
.mark loopBody187_32

def loopBody187_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody187_35 : HolLoopProg 64 :=
.mark loopBody187_34

def loopBody187_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 4,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody187_37 : HolLoopProg 64 :=
.mark loopBody187_36

def loopBody187_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody187_27 loopBody187_29 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody187_39 : HolLoopProg 64 :=
.mark loopBody187_38

def loopBody187_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 70#64)

def loopBody187_41 : HolLoopProg 64 :=
.mark loopBody187_40

def loopBody187_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody187_43 : HolLoopProg 64 :=
.mark loopBody187_42

def loopBody187_44 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 245) ([8]) (some (8, loopBody187_43, loopBody187_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody187_45 : HolLoopProg 64 :=
.mark loopBody187_44

def loopBody187_46 : HolLoopProg 64 :=
.seq loopBody187_45 loopBody187_1

def loopBody187_47 : HolLoopProg 64 :=
.mark loopBody187_46

def loopBody187_48 : HolLoopProg 64 :=
.seq loopBody187_41 loopBody187_47

def loopBody187_49 : HolLoopProg 64 :=
.mark loopBody187_48

def loopBody187_50 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_49

def loopBody187_51 : HolLoopProg 64 :=
.mark loopBody187_50

def loopBody187_52 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_51

def loopBody187_53 : HolLoopProg 64 :=
.mark loopBody187_52

def loopBody187_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody187_53 loopBody187_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody187_55 : HolLoopProg 64 :=
.mark loopBody187_54

def loopBody187_56 : HolLoopProg 64 :=
.seq loopBody187_55 loopBody187_1

def loopBody187_57 : HolLoopProg 64 :=
.mark loopBody187_56

def loopBody187_58 : HolLoopProg 64 :=
.seq loopBody187_33 loopBody187_57

def loopBody187_59 : HolLoopProg 64 :=
.mark loopBody187_58

def loopBody187_60 : HolLoopProg 64 :=
.seq loopBody187_39 loopBody187_59

def loopBody187_61 : HolLoopProg 64 :=
.mark loopBody187_60

def loopBody187_62 : HolLoopProg 64 :=
.seq loopBody187_37 loopBody187_61

def loopBody187_63 : HolLoopProg 64 :=
.mark loopBody187_62

def loopBody187_64 : HolLoopProg 64 :=
.seq loopBody187_35 loopBody187_63

def loopBody187_65 : HolLoopProg 64 :=
.mark loopBody187_64

def loopBody187_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody187_67 : HolLoopProg 64 :=
.mark loopBody187_66

def loopBody187_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 7)

def loopBody187_69 : HolLoopProg 64 :=
.mark loopBody187_68

def loopBody187_70 : HolLoopProg 64 :=
.seq loopBody187_69 loopBody187_1

def loopBody187_71 : HolLoopProg 64 :=
.mark loopBody187_70

def loopBody187_72 : HolLoopProg 64 :=
.seq loopBody187_71 loopBody187_1

def loopBody187_73 : HolLoopProg 64 :=
.mark loopBody187_72

def loopBody187_74 : HolLoopProg 64 :=
.seq loopBody187_67 loopBody187_73

def loopBody187_75 : HolLoopProg 64 :=
.mark loopBody187_74

def loopBody187_76 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_75

def loopBody187_77 : HolLoopProg 64 :=
.mark loopBody187_76

def loopBody187_78 : HolLoopProg 64 :=
.seq loopBody187_65 loopBody187_77

def loopBody187_79 : HolLoopProg 64 :=
.mark loopBody187_78

def loopBody187_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody187_81 : HolLoopProg 64 :=
.mark loopBody187_80

def loopBody187_82 : HolLoopProg 64 :=
.seq loopBody187_79 loopBody187_81

def loopBody187_83 : HolLoopProg 64 :=
.mark loopBody187_82

def loopBody187_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody187_85 : HolLoopProg 64 :=
.mark loopBody187_84

def loopBody187_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody187_83 loopBody187_85 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody187_87 : HolLoopProg 64 :=
.mark loopBody187_86

def loopBody187_88 : HolLoopProg 64 :=
.seq loopBody187_87 loopBody187_1

def loopBody187_89 : HolLoopProg 64 :=
.mark loopBody187_88

def loopBody187_90 : HolLoopProg 64 :=
.seq loopBody187_33 loopBody187_89

def loopBody187_91 : HolLoopProg 64 :=
.mark loopBody187_90

def loopBody187_92 : HolLoopProg 64 :=
.seq loopBody187_31 loopBody187_91

def loopBody187_93 : HolLoopProg 64 :=
.mark loopBody187_92

def loopBody187_94 : HolLoopProg 64 :=
.seq loopBody187_25 loopBody187_93

def loopBody187_95 : HolLoopProg 64 :=
.mark loopBody187_94

def loopBody187_96 : HolLoopProg 64 :=
.seq loopBody187_23 loopBody187_95

def loopBody187_97 : HolLoopProg 64 :=
.mark loopBody187_96

def loopBody187_98 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody187_97 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody187_99 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody187_100 : HolLoopProg 64 :=
.mark loopBody187_99

def loopBody187_101 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody187_102 : HolLoopProg 64 :=
.mark loopBody187_101

def loopBody187_103 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7, 8]

def loopBody187_104 : HolLoopProg 64 :=
.mark loopBody187_103

def loopBody187_105 : HolLoopProg 64 :=
.seq loopBody187_104 loopBody187_1

def loopBody187_106 : HolLoopProg 64 :=
.mark loopBody187_105

def loopBody187_107 : HolLoopProg 64 :=
.seq loopBody187_102 loopBody187_106

def loopBody187_108 : HolLoopProg 64 :=
.mark loopBody187_107

def loopBody187_109 : HolLoopProg 64 :=
.seq loopBody187_100 loopBody187_108

def loopBody187_110 : HolLoopProg 64 :=
.mark loopBody187_109

def loopBody187_111 : HolLoopProg 64 :=
.seq loopBody187_98 loopBody187_110

def loopBody187_112 : HolLoopProg 64 :=
.seq loopBody187_21 loopBody187_111

def loopBody187_113 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_112

def loopBody187_114 : HolLoopProg 64 :=
.seq loopBody187_19 loopBody187_113

def loopBody187_115 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_114

def loopBody187_116 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_115

def loopBody187_117 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_116

def loopBody187_118 : HolLoopProg 64 :=
.seq loopBody187_1 loopBody187_117

def output187 : Nat × List Nat × HolLoopProg 64 :=
  (251, [0, 1, 2, 3], loopBody187_118)
end InitECandidate.Proofs.FrontendStages.Loop
